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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_usize_of_nat(lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_addImportedGlobals___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg(lean_object*);
lean_object* l_Lean_SMap_instInhabited___redArg();
lean_object* l_Lean_ScopedEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_quickLt(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___redArg(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_PersistentEnvExtension_getModuleEntries___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_findSortedByName_x3f___redArg(lean_object*, lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Environment_logDeclChange(lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_addCore___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
lean_object* l_Lean_Attribute_Builtin_ensureNoArgs(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_ConstantInfo_isDefinition(lean_object*);
lean_object* l_Lean_registerBuiltinAttribute(lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ReducibilityStatus_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_Lean_ReducibilityStatus_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__0_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2__spec__1___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2__spec__1___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2__spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2__spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2__spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__1___closed__0_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__1___closed__0_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__1___closed__0_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__1_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__1_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "reducibility attribute core extension"};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__2___closed__1_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__2___closed__1_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__2___closed__1_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__2___closed__2_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__2___closed__1_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2__value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__2___closed__2_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__2___closed__2_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__2___closed__3_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "number of local entries: "};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__2___closed__3_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__2___closed__3_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__2___closed__4_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__2___closed__3_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__2___closed__4_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__2___closed__4_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__2___closed__5_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__2___closed__2_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__2___closed__4_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__2___closed__5_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__2___closed__5_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__2_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2__spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2__spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__3_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__3_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__4_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__4_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__5_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__5_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__6_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__6_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__0_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2_, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__1_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__2_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2_, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__3_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2____boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__4_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__4_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__4_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__4_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "reducibilityCore"};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__6_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(95, 201, 42, 208, 53, 44, 245, 169)}};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__6_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__6_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__7_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__5_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))} };
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__7_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__7_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__8_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__6_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2____boxed, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))} };
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__8_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__8_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__9_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 3}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__9_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__9_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__10_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__10_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__10_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__11_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*8 + 8, .m_other = 8, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__6_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__7_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__8_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__9_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__10_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(0, 1, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__11_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__11_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__12_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__11_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__4_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__12_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__12_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2__spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2__spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2__spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2__spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_reducibilityCoreExt;
LEAN_EXPORT lean_object* l_Lean_SMap_switch___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2__spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_switch___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2__spec__0(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8_spec__10___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2__spec__1_spec__2_spec__5___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2__spec__1_spec__2_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2__spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__3_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2__spec__1_spec__1_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2__spec__1_spec__1_spec__2___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2__spec__1_spec__1_spec__2___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__4___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2__spec__1_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2__spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2__spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__0_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__1_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__1_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__2_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__2_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__3_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__3_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__4_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__4_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__0_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2_, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_SMap_switch___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2__spec__0___redArg, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__1_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__2_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__4_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__3_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2____boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__4_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__4_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "reducibilityExtra"};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__6_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(114, 61, 52, 173, 157, 234, 207, 193)}};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__6_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__6_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__7_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__7_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__8_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__8_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__9_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__9_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__10_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__10_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__11_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__11_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__12_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__12_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2_;
static const lean_ctor_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__13_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__13_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__13_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__14_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__14_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__15_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__15_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2__spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2__spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2__spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2__spec__1_spec__1_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2__spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2__spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2__spec__1_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2__spec__1_spec__2_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2__spec__1_spec__2_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__4(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8_spec__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_reducibilityExtraExt;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__0_spec__1___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__1_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_getReducibilityStatusCore___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getReducibilityStatusCore___closed__0;
LEAN_EXPORT uint8_t l_Lean_getReducibilityStatusCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatusCore___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__0_spec__1(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore___lam__0(lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "failed to set `[reducible]`, `"};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__0 = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__0_value;
static lean_once_cell_t l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__1;
static const lean_string_object l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "` is not currently `[semireducible]`, but `"};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__2 = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__2_value;
static lean_once_cell_t l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__3;
static const lean_string_object l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "failed to set `[semireducible]` for `"};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__4 = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__4_value;
static lean_once_cell_t l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__5;
static const lean_string_object l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "` because it already is `[semireducible]`"};
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
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0(uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___redArg___closed__0;
static lean_once_cell_t l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___redArg___closed__1;
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
LEAN_EXPORT lean_object* l_Lean_ReducibilityStatus_ctorIdx___impl(uint8_t v_x_1_){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_box(v_x_1_);
v___x_3_ = lean_obj_tag_nat(v___x_2_);
lean_dec(v___x_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l_Lean_ReducibilityStatus_ctorIdx___impl___boxed(lean_object* v_x_4_){
_start:
{
uint8_t v_x_4__boxed_5_; lean_object* v_res_6_; 
v_x_4__boxed_5_ = lean_unbox(v_x_4_);
v_res_6_ = l_Lean_ReducibilityStatus_ctorIdx___impl(v_x_4__boxed_5_);
return v_res_6_;
}
}
LEAN_EXPORT lean_object* l_Lean_ReducibilityStatus_ctorElim___redArg(lean_object* v_k_7_){
_start:
{
lean_inc(v_k_7_);
return v_k_7_;
}
}
LEAN_EXPORT lean_object* l_Lean_ReducibilityStatus_ctorElim___redArg___boxed(lean_object* v_k_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = l_Lean_ReducibilityStatus_ctorElim___redArg(v_k_8_);
lean_dec(v_k_8_);
return v_res_9_;
}
}
LEAN_EXPORT lean_object* l_Lean_ReducibilityStatus_ctorElim(lean_object* v_motive_10_, lean_object* v_ctorIdx_11_, uint8_t v_t_12_, lean_object* v_h_13_, lean_object* v_k_14_){
_start:
{
lean_inc(v_k_14_);
return v_k_14_;
}
}
LEAN_EXPORT lean_object* l_Lean_ReducibilityStatus_ctorElim___boxed(lean_object* v_motive_15_, lean_object* v_ctorIdx_16_, lean_object* v_t_17_, lean_object* v_h_18_, lean_object* v_k_19_){
_start:
{
uint8_t v_t_boxed_20_; lean_object* v_res_21_; 
v_t_boxed_20_ = lean_unbox(v_t_17_);
v_res_21_ = l_Lean_ReducibilityStatus_ctorElim(v_motive_15_, v_ctorIdx_16_, v_t_boxed_20_, v_h_18_, v_k_19_);
lean_dec(v_k_19_);
lean_dec(v_ctorIdx_16_);
return v_res_21_;
}
}
LEAN_EXPORT lean_object* l_Lean_ReducibilityStatus_reducible_elim___redArg(lean_object* v_reducible_22_){
_start:
{
lean_inc(v_reducible_22_);
return v_reducible_22_;
}
}
LEAN_EXPORT lean_object* l_Lean_ReducibilityStatus_reducible_elim___redArg___boxed(lean_object* v_reducible_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l_Lean_ReducibilityStatus_reducible_elim___redArg(v_reducible_23_);
lean_dec(v_reducible_23_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l_Lean_ReducibilityStatus_reducible_elim(lean_object* v_motive_25_, uint8_t v_t_26_, lean_object* v_h_27_, lean_object* v_reducible_28_){
_start:
{
lean_inc(v_reducible_28_);
return v_reducible_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_ReducibilityStatus_reducible_elim___boxed(lean_object* v_motive_29_, lean_object* v_t_30_, lean_object* v_h_31_, lean_object* v_reducible_32_){
_start:
{
uint8_t v_t_boxed_33_; lean_object* v_res_34_; 
v_t_boxed_33_ = lean_unbox(v_t_30_);
v_res_34_ = l_Lean_ReducibilityStatus_reducible_elim(v_motive_29_, v_t_boxed_33_, v_h_31_, v_reducible_32_);
lean_dec(v_reducible_32_);
return v_res_34_;
}
}
LEAN_EXPORT lean_object* l_Lean_ReducibilityStatus_semireducible_elim___redArg(lean_object* v_semireducible_35_){
_start:
{
lean_inc(v_semireducible_35_);
return v_semireducible_35_;
}
}
LEAN_EXPORT lean_object* l_Lean_ReducibilityStatus_semireducible_elim___redArg___boxed(lean_object* v_semireducible_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l_Lean_ReducibilityStatus_semireducible_elim___redArg(v_semireducible_36_);
lean_dec(v_semireducible_36_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_Lean_ReducibilityStatus_semireducible_elim(lean_object* v_motive_38_, uint8_t v_t_39_, lean_object* v_h_40_, lean_object* v_semireducible_41_){
_start:
{
lean_inc(v_semireducible_41_);
return v_semireducible_41_;
}
}
LEAN_EXPORT lean_object* l_Lean_ReducibilityStatus_semireducible_elim___boxed(lean_object* v_motive_42_, lean_object* v_t_43_, lean_object* v_h_44_, lean_object* v_semireducible_45_){
_start:
{
uint8_t v_t_boxed_46_; lean_object* v_res_47_; 
v_t_boxed_46_ = lean_unbox(v_t_43_);
v_res_47_ = l_Lean_ReducibilityStatus_semireducible_elim(v_motive_42_, v_t_boxed_46_, v_h_44_, v_semireducible_45_);
lean_dec(v_semireducible_45_);
return v_res_47_;
}
}
LEAN_EXPORT lean_object* l_Lean_ReducibilityStatus_irreducible_elim___redArg(lean_object* v_irreducible_48_){
_start:
{
lean_inc(v_irreducible_48_);
return v_irreducible_48_;
}
}
LEAN_EXPORT lean_object* l_Lean_ReducibilityStatus_irreducible_elim___redArg___boxed(lean_object* v_irreducible_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = l_Lean_ReducibilityStatus_irreducible_elim___redArg(v_irreducible_49_);
lean_dec(v_irreducible_49_);
return v_res_50_;
}
}
LEAN_EXPORT lean_object* l_Lean_ReducibilityStatus_irreducible_elim(lean_object* v_motive_51_, uint8_t v_t_52_, lean_object* v_h_53_, lean_object* v_irreducible_54_){
_start:
{
lean_inc(v_irreducible_54_);
return v_irreducible_54_;
}
}
LEAN_EXPORT lean_object* l_Lean_ReducibilityStatus_irreducible_elim___boxed(lean_object* v_motive_55_, lean_object* v_t_56_, lean_object* v_h_57_, lean_object* v_irreducible_58_){
_start:
{
uint8_t v_t_boxed_59_; lean_object* v_res_60_; 
v_t_boxed_59_ = lean_unbox(v_t_56_);
v_res_60_ = l_Lean_ReducibilityStatus_irreducible_elim(v_motive_55_, v_t_boxed_59_, v_h_57_, v_irreducible_58_);
lean_dec(v_irreducible_58_);
return v_res_60_;
}
}
LEAN_EXPORT lean_object* l_Lean_ReducibilityStatus_implicitReducible_elim___redArg(lean_object* v_implicitReducible_61_){
_start:
{
lean_inc(v_implicitReducible_61_);
return v_implicitReducible_61_;
}
}
LEAN_EXPORT lean_object* l_Lean_ReducibilityStatus_implicitReducible_elim___redArg___boxed(lean_object* v_implicitReducible_62_){
_start:
{
lean_object* v_res_63_; 
v_res_63_ = l_Lean_ReducibilityStatus_implicitReducible_elim___redArg(v_implicitReducible_62_);
lean_dec(v_implicitReducible_62_);
return v_res_63_;
}
}
LEAN_EXPORT lean_object* l_Lean_ReducibilityStatus_implicitReducible_elim(lean_object* v_motive_64_, uint8_t v_t_65_, lean_object* v_h_66_, lean_object* v_implicitReducible_67_){
_start:
{
lean_inc(v_implicitReducible_67_);
return v_implicitReducible_67_;
}
}
LEAN_EXPORT lean_object* l_Lean_ReducibilityStatus_implicitReducible_elim___boxed(lean_object* v_motive_68_, lean_object* v_t_69_, lean_object* v_h_70_, lean_object* v_implicitReducible_71_){
_start:
{
uint8_t v_t_boxed_72_; lean_object* v_res_73_; 
v_t_boxed_72_ = lean_unbox(v_t_69_);
v_res_73_ = l_Lean_ReducibilityStatus_implicitReducible_elim(v_motive_68_, v_t_boxed_72_, v_h_70_, v_implicitReducible_71_);
lean_dec(v_implicitReducible_71_);
return v_res_73_;
}
}
LEAN_EXPORT lean_object* l_Lean_ReducibilityStatus_instanceReducible_elim___redArg(lean_object* v_instanceReducible_74_){
_start:
{
lean_inc(v_instanceReducible_74_);
return v_instanceReducible_74_;
}
}
LEAN_EXPORT lean_object* l_Lean_ReducibilityStatus_instanceReducible_elim___redArg___boxed(lean_object* v_instanceReducible_75_){
_start:
{
lean_object* v_res_76_; 
v_res_76_ = l_Lean_ReducibilityStatus_instanceReducible_elim___redArg(v_instanceReducible_75_);
lean_dec(v_instanceReducible_75_);
return v_res_76_;
}
}
LEAN_EXPORT lean_object* l_Lean_ReducibilityStatus_instanceReducible_elim(lean_object* v_motive_77_, uint8_t v_t_78_, lean_object* v_h_79_, lean_object* v_instanceReducible_80_){
_start:
{
lean_inc(v_instanceReducible_80_);
return v_instanceReducible_80_;
}
}
LEAN_EXPORT lean_object* l_Lean_ReducibilityStatus_instanceReducible_elim___boxed(lean_object* v_motive_81_, lean_object* v_t_82_, lean_object* v_h_83_, lean_object* v_instanceReducible_84_){
_start:
{
uint8_t v_t_boxed_85_; lean_object* v_res_86_; 
v_t_boxed_85_ = lean_unbox(v_t_82_);
v_res_86_ = l_Lean_ReducibilityStatus_instanceReducible_elim(v_motive_81_, v_t_boxed_85_, v_h_83_, v_instanceReducible_84_);
lean_dec(v_instanceReducible_84_);
return v_res_86_;
}
}
static uint8_t _init_l_Lean_instInhabitedReducibilityStatus_default(void){
_start:
{
uint8_t v___x_87_; 
v___x_87_ = 0;
return v___x_87_;
}
}
static uint8_t _init_l_Lean_instInhabitedReducibilityStatus(void){
_start:
{
uint8_t v___x_88_; 
v___x_88_ = 0;
return v___x_88_;
}
}
static lean_object* _init_l_Lean_instReprReducibilityStatus_repr___closed__10(void){
_start:
{
lean_object* v___x_104_; lean_object* v___x_105_; 
v___x_104_ = lean_unsigned_to_nat(2u);
v___x_105_ = lean_nat_to_int(v___x_104_);
return v___x_105_;
}
}
static lean_object* _init_l_Lean_instReprReducibilityStatus_repr___closed__11(void){
_start:
{
lean_object* v___x_106_; lean_object* v___x_107_; 
v___x_106_ = lean_unsigned_to_nat(1u);
v___x_107_ = lean_nat_to_int(v___x_106_);
return v___x_107_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprReducibilityStatus_repr(uint8_t v_x_108_, lean_object* v_prec_109_){
_start:
{
lean_object* v___y_111_; lean_object* v___y_118_; lean_object* v___y_125_; lean_object* v___y_132_; lean_object* v___y_139_; 
switch(v_x_108_)
{
case 0:
{
lean_object* v___x_145_; uint8_t v___x_146_; 
v___x_145_ = lean_unsigned_to_nat(1024u);
v___x_146_ = lean_nat_dec_le(v___x_145_, v_prec_109_);
if (v___x_146_ == 0)
{
lean_object* v___x_147_; 
v___x_147_ = lean_obj_once(&l_Lean_instReprReducibilityStatus_repr___closed__10, &l_Lean_instReprReducibilityStatus_repr___closed__10_once, _init_l_Lean_instReprReducibilityStatus_repr___closed__10);
v___y_111_ = v___x_147_;
goto v___jp_110_;
}
else
{
lean_object* v___x_148_; 
v___x_148_ = lean_obj_once(&l_Lean_instReprReducibilityStatus_repr___closed__11, &l_Lean_instReprReducibilityStatus_repr___closed__11_once, _init_l_Lean_instReprReducibilityStatus_repr___closed__11);
v___y_111_ = v___x_148_;
goto v___jp_110_;
}
}
case 1:
{
lean_object* v___x_149_; uint8_t v___x_150_; 
v___x_149_ = lean_unsigned_to_nat(1024u);
v___x_150_ = lean_nat_dec_le(v___x_149_, v_prec_109_);
if (v___x_150_ == 0)
{
lean_object* v___x_151_; 
v___x_151_ = lean_obj_once(&l_Lean_instReprReducibilityStatus_repr___closed__10, &l_Lean_instReprReducibilityStatus_repr___closed__10_once, _init_l_Lean_instReprReducibilityStatus_repr___closed__10);
v___y_118_ = v___x_151_;
goto v___jp_117_;
}
else
{
lean_object* v___x_152_; 
v___x_152_ = lean_obj_once(&l_Lean_instReprReducibilityStatus_repr___closed__11, &l_Lean_instReprReducibilityStatus_repr___closed__11_once, _init_l_Lean_instReprReducibilityStatus_repr___closed__11);
v___y_118_ = v___x_152_;
goto v___jp_117_;
}
}
case 2:
{
lean_object* v___x_153_; uint8_t v___x_154_; 
v___x_153_ = lean_unsigned_to_nat(1024u);
v___x_154_ = lean_nat_dec_le(v___x_153_, v_prec_109_);
if (v___x_154_ == 0)
{
lean_object* v___x_155_; 
v___x_155_ = lean_obj_once(&l_Lean_instReprReducibilityStatus_repr___closed__10, &l_Lean_instReprReducibilityStatus_repr___closed__10_once, _init_l_Lean_instReprReducibilityStatus_repr___closed__10);
v___y_125_ = v___x_155_;
goto v___jp_124_;
}
else
{
lean_object* v___x_156_; 
v___x_156_ = lean_obj_once(&l_Lean_instReprReducibilityStatus_repr___closed__11, &l_Lean_instReprReducibilityStatus_repr___closed__11_once, _init_l_Lean_instReprReducibilityStatus_repr___closed__11);
v___y_125_ = v___x_156_;
goto v___jp_124_;
}
}
case 3:
{
lean_object* v___x_157_; uint8_t v___x_158_; 
v___x_157_ = lean_unsigned_to_nat(1024u);
v___x_158_ = lean_nat_dec_le(v___x_157_, v_prec_109_);
if (v___x_158_ == 0)
{
lean_object* v___x_159_; 
v___x_159_ = lean_obj_once(&l_Lean_instReprReducibilityStatus_repr___closed__10, &l_Lean_instReprReducibilityStatus_repr___closed__10_once, _init_l_Lean_instReprReducibilityStatus_repr___closed__10);
v___y_132_ = v___x_159_;
goto v___jp_131_;
}
else
{
lean_object* v___x_160_; 
v___x_160_ = lean_obj_once(&l_Lean_instReprReducibilityStatus_repr___closed__11, &l_Lean_instReprReducibilityStatus_repr___closed__11_once, _init_l_Lean_instReprReducibilityStatus_repr___closed__11);
v___y_132_ = v___x_160_;
goto v___jp_131_;
}
}
default: 
{
lean_object* v___x_161_; uint8_t v___x_162_; 
v___x_161_ = lean_unsigned_to_nat(1024u);
v___x_162_ = lean_nat_dec_le(v___x_161_, v_prec_109_);
if (v___x_162_ == 0)
{
lean_object* v___x_163_; 
v___x_163_ = lean_obj_once(&l_Lean_instReprReducibilityStatus_repr___closed__10, &l_Lean_instReprReducibilityStatus_repr___closed__10_once, _init_l_Lean_instReprReducibilityStatus_repr___closed__10);
v___y_139_ = v___x_163_;
goto v___jp_138_;
}
else
{
lean_object* v___x_164_; 
v___x_164_ = lean_obj_once(&l_Lean_instReprReducibilityStatus_repr___closed__11, &l_Lean_instReprReducibilityStatus_repr___closed__11_once, _init_l_Lean_instReprReducibilityStatus_repr___closed__11);
v___y_139_ = v___x_164_;
goto v___jp_138_;
}
}
}
v___jp_110_:
{
lean_object* v___x_112_; lean_object* v___x_113_; uint8_t v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; 
v___x_112_ = ((lean_object*)(l_Lean_instReprReducibilityStatus_repr___closed__1));
lean_inc(v___y_111_);
v___x_113_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_113_, 0, v___y_111_);
lean_ctor_set(v___x_113_, 1, v___x_112_);
v___x_114_ = 0;
v___x_115_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_115_, 0, v___x_113_);
lean_ctor_set_uint8(v___x_115_, sizeof(void*)*1, v___x_114_);
v___x_116_ = l_Repr_addAppParen(v___x_115_, v_prec_109_);
return v___x_116_;
}
v___jp_117_:
{
lean_object* v___x_119_; lean_object* v___x_120_; uint8_t v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; 
v___x_119_ = ((lean_object*)(l_Lean_instReprReducibilityStatus_repr___closed__3));
lean_inc(v___y_118_);
v___x_120_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_120_, 0, v___y_118_);
lean_ctor_set(v___x_120_, 1, v___x_119_);
v___x_121_ = 0;
v___x_122_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_122_, 0, v___x_120_);
lean_ctor_set_uint8(v___x_122_, sizeof(void*)*1, v___x_121_);
v___x_123_ = l_Repr_addAppParen(v___x_122_, v_prec_109_);
return v___x_123_;
}
v___jp_124_:
{
lean_object* v___x_126_; lean_object* v___x_127_; uint8_t v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; 
v___x_126_ = ((lean_object*)(l_Lean_instReprReducibilityStatus_repr___closed__5));
lean_inc(v___y_125_);
v___x_127_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_127_, 0, v___y_125_);
lean_ctor_set(v___x_127_, 1, v___x_126_);
v___x_128_ = 0;
v___x_129_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_129_, 0, v___x_127_);
lean_ctor_set_uint8(v___x_129_, sizeof(void*)*1, v___x_128_);
v___x_130_ = l_Repr_addAppParen(v___x_129_, v_prec_109_);
return v___x_130_;
}
v___jp_131_:
{
lean_object* v___x_133_; lean_object* v___x_134_; uint8_t v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; 
v___x_133_ = ((lean_object*)(l_Lean_instReprReducibilityStatus_repr___closed__7));
lean_inc(v___y_132_);
v___x_134_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_134_, 0, v___y_132_);
lean_ctor_set(v___x_134_, 1, v___x_133_);
v___x_135_ = 0;
v___x_136_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_136_, 0, v___x_134_);
lean_ctor_set_uint8(v___x_136_, sizeof(void*)*1, v___x_135_);
v___x_137_ = l_Repr_addAppParen(v___x_136_, v_prec_109_);
return v___x_137_;
}
v___jp_138_:
{
lean_object* v___x_140_; lean_object* v___x_141_; uint8_t v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; 
v___x_140_ = ((lean_object*)(l_Lean_instReprReducibilityStatus_repr___closed__9));
lean_inc(v___y_139_);
v___x_141_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_141_, 0, v___y_139_);
lean_ctor_set(v___x_141_, 1, v___x_140_);
v___x_142_ = 0;
v___x_143_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_143_, 0, v___x_141_);
lean_ctor_set_uint8(v___x_143_, sizeof(void*)*1, v___x_142_);
v___x_144_ = l_Repr_addAppParen(v___x_143_, v_prec_109_);
return v___x_144_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instReprReducibilityStatus_repr___boxed(lean_object* v_x_165_, lean_object* v_prec_166_){
_start:
{
uint8_t v_x_279__boxed_167_; lean_object* v_res_168_; 
v_x_279__boxed_167_ = lean_unbox(v_x_165_);
v_res_168_ = l_Lean_instReprReducibilityStatus_repr(v_x_279__boxed_167_, v_prec_166_);
lean_dec(v_prec_166_);
return v_res_168_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqReducibilityStatus_beq(uint8_t v_x_171_, uint8_t v_y_172_){
_start:
{
lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; uint8_t v___x_177_; 
v___x_173_ = lean_box(v_x_171_);
v___x_174_ = lean_obj_tag_nat(v___x_173_);
lean_dec(v___x_173_);
v___x_175_ = lean_box(v_y_172_);
v___x_176_ = lean_obj_tag_nat(v___x_175_);
lean_dec(v___x_175_);
v___x_177_ = lean_nat_dec_eq(v___x_174_, v___x_176_);
return v___x_177_;
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqReducibilityStatus_beq___boxed(lean_object* v_x_178_, lean_object* v_y_179_){
_start:
{
uint8_t v_x_24__boxed_180_; uint8_t v_y_25__boxed_181_; uint8_t v_res_182_; lean_object* v_r_183_; 
v_x_24__boxed_180_ = lean_unbox(v_x_178_);
v_y_25__boxed_181_ = lean_unbox(v_y_179_);
v_res_182_ = l_Lean_instBEqReducibilityStatus_beq(v_x_24__boxed_180_, v_y_25__boxed_181_);
v_r_183_ = lean_box(v_res_182_);
return v_r_183_;
}
}
LEAN_EXPORT lean_object* l_Lean_ReducibilityStatus_toAttrString(uint8_t v_x_191_){
_start:
{
switch(v_x_191_)
{
case 0:
{
lean_object* v___x_192_; 
v___x_192_ = ((lean_object*)(l_Lean_ReducibilityStatus_toAttrString___closed__0));
return v___x_192_;
}
case 1:
{
lean_object* v___x_193_; 
v___x_193_ = ((lean_object*)(l_Lean_ReducibilityStatus_toAttrString___closed__1));
return v___x_193_;
}
case 2:
{
lean_object* v___x_194_; 
v___x_194_ = ((lean_object*)(l_Lean_ReducibilityStatus_toAttrString___closed__2));
return v___x_194_;
}
case 3:
{
lean_object* v___x_195_; 
v___x_195_ = ((lean_object*)(l_Lean_ReducibilityStatus_toAttrString___closed__3));
return v___x_195_;
}
default: 
{
lean_object* v___x_196_; 
v___x_196_ = ((lean_object*)(l_Lean_ReducibilityStatus_toAttrString___closed__4));
return v___x_196_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ReducibilityStatus_toAttrString___boxed(lean_object* v_x_197_){
_start:
{
uint8_t v_x_49__boxed_198_; lean_object* v_res_199_; 
v_x_49__boxed_198_ = lean_unbox(v_x_197_);
v_res_199_ = l_Lean_ReducibilityStatus_toAttrString(v_x_49__boxed_198_);
return v_res_199_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__0_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2_(lean_object* v_s_200_, lean_object* v_p_201_){
_start:
{
lean_object* v_fst_202_; lean_object* v_snd_203_; lean_object* v___x_204_; 
v_fst_202_ = lean_ctor_get(v_p_201_, 0);
lean_inc(v_fst_202_);
v_snd_203_ = lean_ctor_get(v_p_201_, 1);
lean_inc(v_snd_203_);
lean_dec_ref(v_p_201_);
v___x_204_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_202_, v_snd_203_, v_s_200_);
return v___x_204_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_init_205_, lean_object* v_x_206_){
_start:
{
if (lean_obj_tag(v_x_206_) == 0)
{
lean_object* v_k_207_; lean_object* v_v_208_; lean_object* v_l_209_; lean_object* v_r_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; 
v_k_207_ = lean_ctor_get(v_x_206_, 1);
v_v_208_ = lean_ctor_get(v_x_206_, 2);
v_l_209_ = lean_ctor_get(v_x_206_, 3);
v_r_210_ = lean_ctor_get(v_x_206_, 4);
v___x_211_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2__spec__0_spec__0(v_init_205_, v_l_209_);
lean_inc(v_v_208_);
lean_inc(v_k_207_);
v___x_212_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_212_, 0, v_k_207_);
lean_ctor_set(v___x_212_, 1, v_v_208_);
v___x_213_ = lean_array_push(v___x_211_, v___x_212_);
v_init_205_ = v___x_213_;
v_x_206_ = v_r_210_;
goto _start;
}
else
{
return v_init_205_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_init_215_, lean_object* v_x_216_){
_start:
{
lean_object* v_res_217_; 
v_res_217_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2__spec__0_spec__0(v_init_215_, v_x_216_);
lean_dec(v_x_216_);
return v_res_217_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2__spec__1___redArg___lam__0(lean_object* v_a_218_, lean_object* v_b_219_){
_start:
{
lean_object* v_fst_220_; lean_object* v_fst_221_; uint8_t v___x_222_; 
v_fst_220_ = lean_ctor_get(v_a_218_, 0);
v_fst_221_ = lean_ctor_get(v_b_219_, 0);
v___x_222_ = l_Lean_Name_quickLt(v_fst_220_, v_fst_221_);
return v___x_222_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2__spec__1___redArg___lam__0___boxed(lean_object* v_a_223_, lean_object* v_b_224_){
_start:
{
uint8_t v_res_225_; lean_object* v_r_226_; 
v_res_225_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2__spec__1___redArg___lam__0(v_a_223_, v_b_224_);
lean_dec_ref(v_b_224_);
lean_dec_ref(v_a_223_);
v_r_226_ = lean_box(v_res_225_);
return v_r_226_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2__spec__1_spec__2___redArg(lean_object* v_hi_227_, lean_object* v_pivot_228_, lean_object* v_as_229_, lean_object* v_i_230_, lean_object* v_k_231_){
_start:
{
uint8_t v___x_232_; 
v___x_232_ = lean_nat_dec_lt(v_k_231_, v_hi_227_);
if (v___x_232_ == 0)
{
lean_object* v___x_233_; lean_object* v___x_234_; 
lean_dec(v_k_231_);
v___x_233_ = lean_array_fswap(v_as_229_, v_i_230_, v_hi_227_);
v___x_234_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_234_, 0, v_i_230_);
lean_ctor_set(v___x_234_, 1, v___x_233_);
return v___x_234_;
}
else
{
lean_object* v___x_235_; lean_object* v_fst_236_; lean_object* v_fst_237_; uint8_t v___x_238_; 
v___x_235_ = lean_array_fget_borrowed(v_as_229_, v_k_231_);
v_fst_236_ = lean_ctor_get(v___x_235_, 0);
v_fst_237_ = lean_ctor_get(v_pivot_228_, 0);
v___x_238_ = l_Lean_Name_quickLt(v_fst_236_, v_fst_237_);
if (v___x_238_ == 0)
{
lean_object* v___x_239_; lean_object* v___x_240_; 
v___x_239_ = lean_unsigned_to_nat(1u);
v___x_240_ = lean_nat_add(v_k_231_, v___x_239_);
lean_dec(v_k_231_);
v_k_231_ = v___x_240_;
goto _start;
}
else
{
lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; 
v___x_242_ = lean_array_fswap(v_as_229_, v_i_230_, v_k_231_);
v___x_243_ = lean_unsigned_to_nat(1u);
v___x_244_ = lean_nat_add(v_i_230_, v___x_243_);
lean_dec(v_i_230_);
v___x_245_ = lean_nat_add(v_k_231_, v___x_243_);
lean_dec(v_k_231_);
v_as_229_ = v___x_242_;
v_i_230_ = v___x_244_;
v_k_231_ = v___x_245_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2__spec__1_spec__2___redArg___boxed(lean_object* v_hi_247_, lean_object* v_pivot_248_, lean_object* v_as_249_, lean_object* v_i_250_, lean_object* v_k_251_){
_start:
{
lean_object* v_res_252_; 
v_res_252_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2__spec__1_spec__2___redArg(v_hi_247_, v_pivot_248_, v_as_249_, v_i_250_, v_k_251_);
lean_dec_ref(v_pivot_248_);
lean_dec(v_hi_247_);
return v_res_252_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2__spec__1___redArg(lean_object* v_n_253_, lean_object* v_as_254_, lean_object* v_lo_255_, lean_object* v_hi_256_){
_start:
{
lean_object* v___y_258_; uint8_t v___x_268_; 
v___x_268_ = lean_nat_dec_lt(v_lo_255_, v_hi_256_);
if (v___x_268_ == 0)
{
lean_dec(v_lo_255_);
return v_as_254_;
}
else
{
lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v_mid_271_; lean_object* v___y_273_; lean_object* v___y_279_; lean_object* v___x_284_; lean_object* v___x_285_; uint8_t v___x_286_; 
v___x_269_ = lean_nat_add(v_lo_255_, v_hi_256_);
v___x_270_ = lean_unsigned_to_nat(1u);
v_mid_271_ = lean_nat_shiftr(v___x_269_, v___x_270_);
lean_dec(v___x_269_);
v___x_284_ = lean_array_fget_borrowed(v_as_254_, v_mid_271_);
v___x_285_ = lean_array_fget_borrowed(v_as_254_, v_lo_255_);
v___x_286_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2__spec__1___redArg___lam__0(v___x_284_, v___x_285_);
if (v___x_286_ == 0)
{
v___y_279_ = v_as_254_;
goto v___jp_278_;
}
else
{
lean_object* v___x_287_; 
v___x_287_ = lean_array_fswap(v_as_254_, v_lo_255_, v_mid_271_);
v___y_279_ = v___x_287_;
goto v___jp_278_;
}
v___jp_272_:
{
lean_object* v___x_274_; lean_object* v___x_275_; uint8_t v___x_276_; 
v___x_274_ = lean_array_fget_borrowed(v___y_273_, v_mid_271_);
v___x_275_ = lean_array_fget_borrowed(v___y_273_, v_hi_256_);
v___x_276_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2__spec__1___redArg___lam__0(v___x_274_, v___x_275_);
if (v___x_276_ == 0)
{
lean_dec(v_mid_271_);
v___y_258_ = v___y_273_;
goto v___jp_257_;
}
else
{
lean_object* v___x_277_; 
v___x_277_ = lean_array_fswap(v___y_273_, v_mid_271_, v_hi_256_);
lean_dec(v_mid_271_);
v___y_258_ = v___x_277_;
goto v___jp_257_;
}
}
v___jp_278_:
{
lean_object* v___x_280_; lean_object* v___x_281_; uint8_t v___x_282_; 
v___x_280_ = lean_array_fget_borrowed(v___y_279_, v_hi_256_);
v___x_281_ = lean_array_fget_borrowed(v___y_279_, v_lo_255_);
v___x_282_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2__spec__1___redArg___lam__0(v___x_280_, v___x_281_);
if (v___x_282_ == 0)
{
v___y_273_ = v___y_279_;
goto v___jp_272_;
}
else
{
lean_object* v___x_283_; 
v___x_283_ = lean_array_fswap(v___y_279_, v_lo_255_, v_hi_256_);
v___y_273_ = v___x_283_;
goto v___jp_272_;
}
}
}
v___jp_257_:
{
lean_object* v_pivot_259_; lean_object* v___x_260_; lean_object* v_fst_261_; lean_object* v_snd_262_; uint8_t v___x_263_; 
v_pivot_259_ = lean_array_fget(v___y_258_, v_hi_256_);
lean_inc_n(v_lo_255_, 2);
v___x_260_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2__spec__1_spec__2___redArg(v_hi_256_, v_pivot_259_, v___y_258_, v_lo_255_, v_lo_255_);
lean_dec(v_pivot_259_);
v_fst_261_ = lean_ctor_get(v___x_260_, 0);
lean_inc(v_fst_261_);
v_snd_262_ = lean_ctor_get(v___x_260_, 1);
lean_inc(v_snd_262_);
lean_dec_ref(v___x_260_);
v___x_263_ = lean_nat_dec_le(v_hi_256_, v_fst_261_);
if (v___x_263_ == 0)
{
lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; 
v___x_264_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2__spec__1___redArg(v_n_253_, v_snd_262_, v_lo_255_, v_fst_261_);
v___x_265_ = lean_unsigned_to_nat(1u);
v___x_266_ = lean_nat_add(v_fst_261_, v___x_265_);
lean_dec(v_fst_261_);
v_as_254_ = v___x_264_;
v_lo_255_ = v___x_266_;
goto _start;
}
else
{
lean_dec(v_fst_261_);
lean_dec(v_lo_255_);
return v_snd_262_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object* v_n_288_, lean_object* v_as_289_, lean_object* v_lo_290_, lean_object* v_hi_291_){
_start:
{
lean_object* v_res_292_; 
v_res_292_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2__spec__1___redArg(v_n_288_, v_as_289_, v_lo_290_, v_hi_291_);
lean_dec(v_hi_291_);
lean_dec(v_n_288_);
return v_res_292_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__1_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2_(lean_object* v_x_295_, lean_object* v_s_296_){
_start:
{
lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v_r_299_; lean_object* v___x_300_; lean_object* v___y_302_; lean_object* v___y_303_; uint8_t v___x_306_; 
v___x_297_ = lean_unsigned_to_nat(0u);
v___x_298_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__1___closed__0_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2_));
v_r_299_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2__spec__0_spec__0(v___x_298_, v_s_296_);
v___x_300_ = lean_array_get_size(v_r_299_);
v___x_306_ = lean_nat_dec_eq(v___x_300_, v___x_297_);
if (v___x_306_ == 0)
{
lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___y_310_; uint8_t v___x_312_; 
v___x_307_ = lean_unsigned_to_nat(1u);
v___x_308_ = lean_nat_sub(v___x_300_, v___x_307_);
v___x_312_ = lean_nat_dec_le(v___x_297_, v___x_308_);
if (v___x_312_ == 0)
{
lean_inc(v___x_308_);
v___y_310_ = v___x_308_;
goto v___jp_309_;
}
else
{
v___y_310_ = v___x_297_;
goto v___jp_309_;
}
v___jp_309_:
{
uint8_t v___x_311_; 
v___x_311_ = lean_nat_dec_le(v___y_310_, v___x_308_);
if (v___x_311_ == 0)
{
lean_dec(v___x_308_);
lean_inc(v___y_310_);
v___y_302_ = v___y_310_;
v___y_303_ = v___y_310_;
goto v___jp_301_;
}
else
{
v___y_302_ = v___y_310_;
v___y_303_ = v___x_308_;
goto v___jp_301_;
}
}
}
else
{
lean_object* v___x_313_; 
lean_inc_ref_n(v_r_299_, 2);
v___x_313_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_313_, 0, v_r_299_);
lean_ctor_set(v___x_313_, 1, v_r_299_);
lean_ctor_set(v___x_313_, 2, v_r_299_);
return v___x_313_;
}
v___jp_301_:
{
lean_object* v___x_304_; lean_object* v___x_305_; 
v___x_304_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2__spec__1___redArg(v___x_300_, v_r_299_, v___y_302_, v___y_303_);
lean_dec(v___y_303_);
lean_inc_ref_n(v___x_304_, 2);
v___x_305_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_305_, 0, v___x_304_);
lean_ctor_set(v___x_305_, 1, v___x_304_);
lean_ctor_set(v___x_305_, 2, v___x_304_);
return v___x_305_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__1_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2____boxed(lean_object* v_x_314_, lean_object* v_s_315_){
_start:
{
lean_object* v_res_316_; 
v_res_316_ = l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__1_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2_(v_x_314_, v_s_315_);
lean_dec(v_s_315_);
lean_dec_ref(v_x_314_);
return v_res_316_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__2_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2_(lean_object* v_s_329_){
_start:
{
lean_object* v___x_330_; lean_object* v___y_332_; 
v___x_330_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__2___closed__5_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2_));
if (lean_obj_tag(v_s_329_) == 0)
{
lean_object* v_size_336_; 
v_size_336_ = lean_ctor_get(v_s_329_, 0);
lean_inc(v_size_336_);
lean_dec_ref_known(v_s_329_, 5);
v___y_332_ = v_size_336_;
goto v___jp_331_;
}
else
{
lean_object* v___x_337_; 
v___x_337_ = lean_unsigned_to_nat(0u);
v___y_332_ = v___x_337_;
goto v___jp_331_;
}
v___jp_331_:
{
lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; 
v___x_333_ = l_Nat_reprFast(v___y_332_);
v___x_334_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_334_, 0, v___x_333_);
v___x_335_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_335_, 0, v___x_330_);
lean_ctor_set(v___x_335_, 1, v___x_334_);
return v___x_335_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2__spec__2(lean_object* v_newState_338_, lean_object* v_x_339_, lean_object* v_x_340_){
_start:
{
if (lean_obj_tag(v_x_340_) == 0)
{
return v_x_339_;
}
else
{
lean_object* v_head_341_; lean_object* v_tail_342_; lean_object* v___x_343_; 
v_head_341_ = lean_ctor_get(v_x_340_, 0);
lean_inc(v_head_341_);
v_tail_342_ = lean_ctor_get(v_x_340_, 1);
lean_inc(v_tail_342_);
lean_dec_ref_known(v_x_340_, 2);
v___x_343_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_newState_338_, v_head_341_);
if (lean_obj_tag(v___x_343_) == 1)
{
lean_object* v_val_344_; lean_object* v___x_345_; 
v_val_344_ = lean_ctor_get(v___x_343_, 0);
lean_inc(v_val_344_);
lean_dec_ref_known(v___x_343_, 1);
v___x_345_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_head_341_, v_val_344_, v_x_339_);
v_x_339_ = v___x_345_;
v_x_340_ = v_tail_342_;
goto _start;
}
else
{
lean_dec(v___x_343_);
lean_dec(v_head_341_);
v_x_340_ = v_tail_342_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2__spec__2___boxed(lean_object* v_newState_348_, lean_object* v_x_349_, lean_object* v_x_350_){
_start:
{
lean_object* v_res_351_; 
v_res_351_ = l_List_foldl___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2__spec__2(v_newState_348_, v_x_349_, v_x_350_);
lean_dec(v_newState_348_);
return v_res_351_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__3_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2_(lean_object* v___oldState_352_, lean_object* v_newState_353_, lean_object* v_newItems_354_, lean_object* v_otherState_355_){
_start:
{
lean_object* v___x_356_; 
v___x_356_ = l_List_foldl___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2__spec__2(v_newState_353_, v_otherState_355_, v_newItems_354_);
return v___x_356_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__3_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2____boxed(lean_object* v___oldState_357_, lean_object* v_newState_358_, lean_object* v_newItems_359_, lean_object* v_otherState_360_){
_start:
{
lean_object* v_res_361_; 
v_res_361_ = l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__3_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2_(v___oldState_357_, v_newState_358_, v_newItems_359_, v_otherState_360_);
lean_dec(v_newState_358_);
lean_dec(v___oldState_357_);
return v_res_361_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__4_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2_(lean_object* v_m_362_){
_start:
{
lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v_r_365_; lean_object* v___x_366_; uint8_t v___x_367_; 
v___x_363_ = lean_unsigned_to_nat(0u);
v___x_364_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__1___closed__0_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2_));
v_r_365_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2__spec__0_spec__0(v___x_364_, v_m_362_);
v___x_366_ = lean_array_get_size(v_r_365_);
v___x_367_ = lean_nat_dec_eq(v___x_366_, v___x_363_);
if (v___x_367_ == 0)
{
lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___y_371_; uint8_t v___x_375_; 
v___x_368_ = lean_unsigned_to_nat(1u);
v___x_369_ = lean_nat_sub(v___x_366_, v___x_368_);
v___x_375_ = lean_nat_dec_le(v___x_363_, v___x_369_);
if (v___x_375_ == 0)
{
lean_inc(v___x_369_);
v___y_371_ = v___x_369_;
goto v___jp_370_;
}
else
{
v___y_371_ = v___x_363_;
goto v___jp_370_;
}
v___jp_370_:
{
uint8_t v___x_372_; 
v___x_372_ = lean_nat_dec_le(v___y_371_, v___x_369_);
if (v___x_372_ == 0)
{
lean_object* v___x_373_; 
lean_dec(v___x_369_);
lean_inc(v___y_371_);
v___x_373_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2__spec__1___redArg(v___x_366_, v_r_365_, v___y_371_, v___y_371_);
lean_dec(v___y_371_);
return v___x_373_;
}
else
{
lean_object* v___x_374_; 
v___x_374_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2__spec__1___redArg(v___x_366_, v_r_365_, v___y_371_, v___x_369_);
lean_dec(v___x_369_);
return v___x_374_;
}
}
}
else
{
return v_r_365_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__4_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2____boxed(lean_object* v_m_376_){
_start:
{
lean_object* v_res_377_; 
v_res_377_ = l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__4_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2_(v_m_376_);
lean_dec(v_m_376_);
return v_res_377_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__5_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2_(lean_object* v___x_378_){
_start:
{
lean_object* v___x_380_; 
v___x_380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_380_, 0, v___x_378_);
return v___x_380_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__5_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2____boxed(lean_object* v___x_381_, lean_object* v___y_382_){
_start:
{
lean_object* v_res_383_; 
v_res_383_ = l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__5_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2_(v___x_381_);
return v_res_383_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__6_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2_(lean_object* v___x_384_, lean_object* v_x_385_, lean_object* v_x_386_){
_start:
{
lean_object* v___x_388_; 
v___x_388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_388_, 0, v___x_384_);
return v___x_388_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__6_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2____boxed(lean_object* v___x_389_, lean_object* v_x_390_, lean_object* v_x_391_, lean_object* v___y_392_){
_start:
{
lean_object* v_res_393_; 
v_res_393_ = l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__6_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2_(v___x_389_, v_x_390_, v_x_391_);
lean_dec_ref(v_x_391_);
lean_dec_ref(v_x_390_);
return v_res_393_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_425_; lean_object* v___x_426_; 
v___x_425_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__12_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2_));
v___x_426_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_425_);
return v___x_426_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2____boxed(lean_object* v_a_427_){
_start:
{
lean_object* v_res_428_; 
v_res_428_ = l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2_();
return v_res_428_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2__spec__0(lean_object* v_init_429_, lean_object* v_t_430_){
_start:
{
lean_object* v___x_431_; 
v___x_431_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2__spec__0_spec__0(v_init_429_, v_t_430_);
return v___x_431_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2__spec__0___boxed(lean_object* v_init_432_, lean_object* v_t_433_){
_start:
{
lean_object* v_res_434_; 
v_res_434_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2__spec__0(v_init_432_, v_t_433_);
lean_dec(v_t_433_);
return v_res_434_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2__spec__1(lean_object* v_n_435_, lean_object* v_as_436_, lean_object* v_lo_437_, lean_object* v_hi_438_, lean_object* v_w_439_, lean_object* v_hlo_440_, lean_object* v_hhi_441_){
_start:
{
lean_object* v___x_442_; 
v___x_442_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2__spec__1___redArg(v_n_435_, v_as_436_, v_lo_437_, v_hi_438_);
return v___x_442_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2__spec__1___boxed(lean_object* v_n_443_, lean_object* v_as_444_, lean_object* v_lo_445_, lean_object* v_hi_446_, lean_object* v_w_447_, lean_object* v_hlo_448_, lean_object* v_hhi_449_){
_start:
{
lean_object* v_res_450_; 
v_res_450_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2__spec__1(v_n_443_, v_as_444_, v_lo_445_, v_hi_446_, v_w_447_, v_hlo_448_, v_hhi_449_);
lean_dec(v_hi_446_);
lean_dec(v_n_443_);
return v_res_450_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2__spec__1_spec__2(lean_object* v_n_451_, lean_object* v_lo_452_, lean_object* v_hi_453_, lean_object* v_hhi_454_, lean_object* v_pivot_455_, lean_object* v_as_456_, lean_object* v_i_457_, lean_object* v_k_458_, lean_object* v_ilo_459_, lean_object* v_ik_460_, lean_object* v_w_461_){
_start:
{
lean_object* v___x_462_; 
v___x_462_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2__spec__1_spec__2___redArg(v_hi_453_, v_pivot_455_, v_as_456_, v_i_457_, v_k_458_);
return v___x_462_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object* v_n_463_, lean_object* v_lo_464_, lean_object* v_hi_465_, lean_object* v_hhi_466_, lean_object* v_pivot_467_, lean_object* v_as_468_, lean_object* v_i_469_, lean_object* v_k_470_, lean_object* v_ilo_471_, lean_object* v_ik_472_, lean_object* v_w_473_){
_start:
{
lean_object* v_res_474_; 
v_res_474_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2__spec__1_spec__2(v_n_463_, v_lo_464_, v_hi_465_, v_hhi_466_, v_pivot_467_, v_as_468_, v_i_469_, v_k_470_, v_ilo_471_, v_ik_472_, v_w_473_);
lean_dec_ref(v_pivot_467_);
lean_dec(v_hi_465_);
lean_dec(v_lo_464_);
lean_dec(v_n_463_);
return v_res_474_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_switch___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2__spec__0___redArg(lean_object* v_m_475_){
_start:
{
uint8_t v_stage_u2081_476_; 
v_stage_u2081_476_ = lean_ctor_get_uint8(v_m_475_, sizeof(void*)*2);
if (v_stage_u2081_476_ == 0)
{
return v_m_475_;
}
else
{
lean_object* v_map_u2081_477_; lean_object* v_map_u2082_478_; lean_object* v___x_480_; uint8_t v_isShared_481_; uint8_t v_isSharedCheck_486_; 
v_map_u2081_477_ = lean_ctor_get(v_m_475_, 0);
v_map_u2082_478_ = lean_ctor_get(v_m_475_, 1);
v_isSharedCheck_486_ = !lean_is_exclusive(v_m_475_);
if (v_isSharedCheck_486_ == 0)
{
v___x_480_ = v_m_475_;
v_isShared_481_ = v_isSharedCheck_486_;
goto v_resetjp_479_;
}
else
{
lean_inc(v_map_u2082_478_);
lean_inc(v_map_u2081_477_);
lean_dec(v_m_475_);
v___x_480_ = lean_box(0);
v_isShared_481_ = v_isSharedCheck_486_;
goto v_resetjp_479_;
}
v_resetjp_479_:
{
uint8_t v___x_482_; lean_object* v___x_484_; 
v___x_482_ = 0;
if (v_isShared_481_ == 0)
{
v___x_484_ = v___x_480_;
goto v_reusejp_483_;
}
else
{
lean_object* v_reuseFailAlloc_485_; 
v_reuseFailAlloc_485_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_485_, 0, v_map_u2081_477_);
lean_ctor_set(v_reuseFailAlloc_485_, 1, v_map_u2082_478_);
v___x_484_ = v_reuseFailAlloc_485_;
goto v_reusejp_483_;
}
v_reusejp_483_:
{
lean_ctor_set_uint8(v___x_484_, sizeof(void*)*2, v___x_482_);
return v___x_484_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_switch___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b2_487_, lean_object* v_m_488_){
_start:
{
lean_object* v___x_489_; 
v___x_489_ = l_Lean_SMap_switch___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2__spec__0___redArg(v_m_488_);
return v___x_489_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg(lean_object* v_a_490_, lean_object* v_x_491_){
_start:
{
if (lean_obj_tag(v_x_491_) == 0)
{
uint8_t v___x_492_; 
v___x_492_ = 0;
return v___x_492_;
}
else
{
lean_object* v_key_493_; lean_object* v_tail_494_; uint8_t v___x_495_; 
v_key_493_ = lean_ctor_get(v_x_491_, 0);
v_tail_494_ = lean_ctor_get(v_x_491_, 2);
v___x_495_ = lean_name_eq(v_key_493_, v_a_490_);
if (v___x_495_ == 0)
{
v_x_491_ = v_tail_494_;
goto _start;
}
else
{
return v___x_495_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_a_497_, lean_object* v_x_498_){
_start:
{
uint8_t v_res_499_; lean_object* v_r_500_; 
v_res_499_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg(v_a_497_, v_x_498_);
lean_dec(v_x_498_);
lean_dec(v_a_497_);
v_r_500_ = lean_box(v_res_499_);
return v_r_500_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8_spec__10___redArg(lean_object* v_x_501_, lean_object* v_x_502_){
_start:
{
if (lean_obj_tag(v_x_502_) == 0)
{
return v_x_501_;
}
else
{
lean_object* v_key_503_; lean_object* v_value_504_; lean_object* v_tail_505_; lean_object* v___x_507_; uint8_t v_isShared_508_; uint8_t v_isSharedCheck_531_; 
v_key_503_ = lean_ctor_get(v_x_502_, 0);
v_value_504_ = lean_ctor_get(v_x_502_, 1);
v_tail_505_ = lean_ctor_get(v_x_502_, 2);
v_isSharedCheck_531_ = !lean_is_exclusive(v_x_502_);
if (v_isSharedCheck_531_ == 0)
{
v___x_507_ = v_x_502_;
v_isShared_508_ = v_isSharedCheck_531_;
goto v_resetjp_506_;
}
else
{
lean_inc(v_tail_505_);
lean_inc(v_value_504_);
lean_inc(v_key_503_);
lean_dec(v_x_502_);
v___x_507_ = lean_box(0);
v_isShared_508_ = v_isSharedCheck_531_;
goto v_resetjp_506_;
}
v_resetjp_506_:
{
lean_object* v___x_509_; uint64_t v___y_511_; 
v___x_509_ = lean_array_get_size(v_x_501_);
if (lean_obj_tag(v_key_503_) == 0)
{
uint64_t v___x_529_; 
v___x_529_ = 1723ULL;
v___y_511_ = v___x_529_;
goto v___jp_510_;
}
else
{
uint64_t v_hash_530_; 
v_hash_530_ = lean_ctor_get_uint64(v_key_503_, sizeof(void*)*2);
v___y_511_ = v_hash_530_;
goto v___jp_510_;
}
v___jp_510_:
{
uint64_t v___x_512_; uint64_t v___x_513_; uint64_t v_fold_514_; uint64_t v___x_515_; uint64_t v___x_516_; uint64_t v___x_517_; size_t v___x_518_; size_t v___x_519_; size_t v___x_520_; size_t v___x_521_; size_t v___x_522_; lean_object* v___x_523_; lean_object* v___x_525_; 
v___x_512_ = 32ULL;
v___x_513_ = lean_uint64_shift_right(v___y_511_, v___x_512_);
v_fold_514_ = lean_uint64_xor(v___y_511_, v___x_513_);
v___x_515_ = 16ULL;
v___x_516_ = lean_uint64_shift_right(v_fold_514_, v___x_515_);
v___x_517_ = lean_uint64_xor(v_fold_514_, v___x_516_);
v___x_518_ = lean_uint64_to_usize(v___x_517_);
v___x_519_ = lean_usize_of_nat(v___x_509_);
v___x_520_ = ((size_t)1ULL);
v___x_521_ = lean_usize_sub(v___x_519_, v___x_520_);
v___x_522_ = lean_usize_land(v___x_518_, v___x_521_);
v___x_523_ = lean_array_uget_borrowed(v_x_501_, v___x_522_);
lean_inc(v___x_523_);
if (v_isShared_508_ == 0)
{
lean_ctor_set(v___x_507_, 2, v___x_523_);
v___x_525_ = v___x_507_;
goto v_reusejp_524_;
}
else
{
lean_object* v_reuseFailAlloc_528_; 
v_reuseFailAlloc_528_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_528_, 0, v_key_503_);
lean_ctor_set(v_reuseFailAlloc_528_, 1, v_value_504_);
lean_ctor_set(v_reuseFailAlloc_528_, 2, v___x_523_);
v___x_525_ = v_reuseFailAlloc_528_;
goto v_reusejp_524_;
}
v_reusejp_524_:
{
lean_object* v___x_526_; 
v___x_526_ = lean_array_uset(v_x_501_, v___x_522_, v___x_525_);
v_x_501_ = v___x_526_;
v_x_502_ = v_tail_505_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8___redArg(lean_object* v_i_532_, lean_object* v_source_533_, lean_object* v_target_534_){
_start:
{
lean_object* v___x_535_; uint8_t v___x_536_; 
v___x_535_ = lean_array_get_size(v_source_533_);
v___x_536_ = lean_nat_dec_lt(v_i_532_, v___x_535_);
if (v___x_536_ == 0)
{
lean_dec_ref(v_source_533_);
lean_dec(v_i_532_);
return v_target_534_;
}
else
{
lean_object* v_es_537_; lean_object* v___x_538_; lean_object* v_source_539_; lean_object* v_target_540_; lean_object* v___x_541_; lean_object* v___x_542_; 
v_es_537_ = lean_array_fget(v_source_533_, v_i_532_);
v___x_538_ = lean_box(0);
v_source_539_ = lean_array_fset(v_source_533_, v_i_532_, v___x_538_);
v_target_540_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8_spec__10___redArg(v_target_534_, v_es_537_);
v___x_541_ = lean_unsigned_to_nat(1u);
v___x_542_ = lean_nat_add(v_i_532_, v___x_541_);
lean_dec(v_i_532_);
v_i_532_ = v___x_542_;
v_source_533_ = v_source_539_;
v_target_534_ = v_target_540_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2__spec__1_spec__2_spec__5___redArg(lean_object* v_data_544_){
_start:
{
lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v_nbuckets_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; 
v___x_545_ = lean_array_get_size(v_data_544_);
v___x_546_ = lean_unsigned_to_nat(2u);
v_nbuckets_547_ = lean_nat_mul(v___x_545_, v___x_546_);
v___x_548_ = lean_unsigned_to_nat(0u);
v___x_549_ = lean_box(0);
v___x_550_ = lean_mk_array(v_nbuckets_547_, v___x_549_);
v___x_551_ = lean_array_propagate_mark(v_data_544_, v___x_550_);
v___x_552_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8___redArg(v___x_548_, v_data_544_, v___x_551_);
return v___x_552_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2__spec__1_spec__2_spec__6___redArg(lean_object* v_a_553_, lean_object* v_b_554_, lean_object* v_x_555_){
_start:
{
if (lean_obj_tag(v_x_555_) == 0)
{
lean_dec(v_b_554_);
lean_dec(v_a_553_);
return v_x_555_;
}
else
{
lean_object* v_key_556_; lean_object* v_value_557_; lean_object* v_tail_558_; lean_object* v___x_560_; uint8_t v_isShared_561_; uint8_t v_isSharedCheck_570_; 
v_key_556_ = lean_ctor_get(v_x_555_, 0);
v_value_557_ = lean_ctor_get(v_x_555_, 1);
v_tail_558_ = lean_ctor_get(v_x_555_, 2);
v_isSharedCheck_570_ = !lean_is_exclusive(v_x_555_);
if (v_isSharedCheck_570_ == 0)
{
v___x_560_ = v_x_555_;
v_isShared_561_ = v_isSharedCheck_570_;
goto v_resetjp_559_;
}
else
{
lean_inc(v_tail_558_);
lean_inc(v_value_557_);
lean_inc(v_key_556_);
lean_dec(v_x_555_);
v___x_560_ = lean_box(0);
v_isShared_561_ = v_isSharedCheck_570_;
goto v_resetjp_559_;
}
v_resetjp_559_:
{
uint8_t v___x_562_; 
v___x_562_ = lean_name_eq(v_key_556_, v_a_553_);
if (v___x_562_ == 0)
{
lean_object* v___x_563_; lean_object* v___x_565_; 
v___x_563_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2__spec__1_spec__2_spec__6___redArg(v_a_553_, v_b_554_, v_tail_558_);
if (v_isShared_561_ == 0)
{
lean_ctor_set(v___x_560_, 2, v___x_563_);
v___x_565_ = v___x_560_;
goto v_reusejp_564_;
}
else
{
lean_object* v_reuseFailAlloc_566_; 
v_reuseFailAlloc_566_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_566_, 0, v_key_556_);
lean_ctor_set(v_reuseFailAlloc_566_, 1, v_value_557_);
lean_ctor_set(v_reuseFailAlloc_566_, 2, v___x_563_);
v___x_565_ = v_reuseFailAlloc_566_;
goto v_reusejp_564_;
}
v_reusejp_564_:
{
return v___x_565_;
}
}
else
{
lean_object* v___x_568_; 
lean_dec(v_value_557_);
lean_dec(v_key_556_);
if (v_isShared_561_ == 0)
{
lean_ctor_set(v___x_560_, 1, v_b_554_);
lean_ctor_set(v___x_560_, 0, v_a_553_);
v___x_568_ = v___x_560_;
goto v_reusejp_567_;
}
else
{
lean_object* v_reuseFailAlloc_569_; 
v_reuseFailAlloc_569_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_569_, 0, v_a_553_);
lean_ctor_set(v_reuseFailAlloc_569_, 1, v_b_554_);
lean_ctor_set(v_reuseFailAlloc_569_, 2, v_tail_558_);
v___x_568_ = v_reuseFailAlloc_569_;
goto v_reusejp_567_;
}
v_reusejp_567_:
{
return v___x_568_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2__spec__1_spec__2___redArg(lean_object* v_m_571_, lean_object* v_a_572_, lean_object* v_b_573_){
_start:
{
lean_object* v_size_574_; lean_object* v_buckets_575_; lean_object* v___x_577_; uint8_t v_isShared_578_; uint8_t v_isSharedCheck_621_; 
v_size_574_ = lean_ctor_get(v_m_571_, 0);
v_buckets_575_ = lean_ctor_get(v_m_571_, 1);
v_isSharedCheck_621_ = !lean_is_exclusive(v_m_571_);
if (v_isSharedCheck_621_ == 0)
{
v___x_577_ = v_m_571_;
v_isShared_578_ = v_isSharedCheck_621_;
goto v_resetjp_576_;
}
else
{
lean_inc(v_buckets_575_);
lean_inc(v_size_574_);
lean_dec(v_m_571_);
v___x_577_ = lean_box(0);
v_isShared_578_ = v_isSharedCheck_621_;
goto v_resetjp_576_;
}
v_resetjp_576_:
{
lean_object* v___x_579_; uint64_t v___y_581_; 
v___x_579_ = lean_array_get_size(v_buckets_575_);
if (lean_obj_tag(v_a_572_) == 0)
{
uint64_t v___x_619_; 
v___x_619_ = 1723ULL;
v___y_581_ = v___x_619_;
goto v___jp_580_;
}
else
{
uint64_t v_hash_620_; 
v_hash_620_ = lean_ctor_get_uint64(v_a_572_, sizeof(void*)*2);
v___y_581_ = v_hash_620_;
goto v___jp_580_;
}
v___jp_580_:
{
uint64_t v___x_582_; uint64_t v___x_583_; uint64_t v_fold_584_; uint64_t v___x_585_; uint64_t v___x_586_; uint64_t v___x_587_; size_t v___x_588_; size_t v___x_589_; size_t v___x_590_; size_t v___x_591_; size_t v___x_592_; lean_object* v_bkt_593_; uint8_t v___x_594_; 
v___x_582_ = 32ULL;
v___x_583_ = lean_uint64_shift_right(v___y_581_, v___x_582_);
v_fold_584_ = lean_uint64_xor(v___y_581_, v___x_583_);
v___x_585_ = 16ULL;
v___x_586_ = lean_uint64_shift_right(v_fold_584_, v___x_585_);
v___x_587_ = lean_uint64_xor(v_fold_584_, v___x_586_);
v___x_588_ = lean_uint64_to_usize(v___x_587_);
v___x_589_ = lean_usize_of_nat(v___x_579_);
v___x_590_ = ((size_t)1ULL);
v___x_591_ = lean_usize_sub(v___x_589_, v___x_590_);
v___x_592_ = lean_usize_land(v___x_588_, v___x_591_);
v_bkt_593_ = lean_array_uget_borrowed(v_buckets_575_, v___x_592_);
v___x_594_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg(v_a_572_, v_bkt_593_);
if (v___x_594_ == 0)
{
lean_object* v___x_595_; lean_object* v_size_x27_596_; lean_object* v___x_597_; lean_object* v_buckets_x27_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; uint8_t v___x_604_; 
v___x_595_ = lean_unsigned_to_nat(1u);
v_size_x27_596_ = lean_nat_add(v_size_574_, v___x_595_);
lean_dec(v_size_574_);
lean_inc(v_bkt_593_);
v___x_597_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_597_, 0, v_a_572_);
lean_ctor_set(v___x_597_, 1, v_b_573_);
lean_ctor_set(v___x_597_, 2, v_bkt_593_);
v_buckets_x27_598_ = lean_array_uset(v_buckets_575_, v___x_592_, v___x_597_);
v___x_599_ = lean_unsigned_to_nat(4u);
v___x_600_ = lean_nat_mul(v_size_x27_596_, v___x_599_);
v___x_601_ = lean_unsigned_to_nat(3u);
v___x_602_ = lean_nat_div(v___x_600_, v___x_601_);
lean_dec(v___x_600_);
v___x_603_ = lean_array_get_size(v_buckets_x27_598_);
v___x_604_ = lean_nat_dec_le(v___x_602_, v___x_603_);
lean_dec(v___x_602_);
if (v___x_604_ == 0)
{
lean_object* v_val_605_; lean_object* v___x_607_; 
v_val_605_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2__spec__1_spec__2_spec__5___redArg(v_buckets_x27_598_);
if (v_isShared_578_ == 0)
{
lean_ctor_set(v___x_577_, 1, v_val_605_);
lean_ctor_set(v___x_577_, 0, v_size_x27_596_);
v___x_607_ = v___x_577_;
goto v_reusejp_606_;
}
else
{
lean_object* v_reuseFailAlloc_608_; 
v_reuseFailAlloc_608_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_608_, 0, v_size_x27_596_);
lean_ctor_set(v_reuseFailAlloc_608_, 1, v_val_605_);
v___x_607_ = v_reuseFailAlloc_608_;
goto v_reusejp_606_;
}
v_reusejp_606_:
{
return v___x_607_;
}
}
else
{
lean_object* v___x_610_; 
if (v_isShared_578_ == 0)
{
lean_ctor_set(v___x_577_, 1, v_buckets_x27_598_);
lean_ctor_set(v___x_577_, 0, v_size_x27_596_);
v___x_610_ = v___x_577_;
goto v_reusejp_609_;
}
else
{
lean_object* v_reuseFailAlloc_611_; 
v_reuseFailAlloc_611_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_611_, 0, v_size_x27_596_);
lean_ctor_set(v_reuseFailAlloc_611_, 1, v_buckets_x27_598_);
v___x_610_ = v_reuseFailAlloc_611_;
goto v_reusejp_609_;
}
v_reusejp_609_:
{
return v___x_610_;
}
}
}
else
{
lean_object* v___x_612_; lean_object* v_buckets_x27_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_617_; 
lean_inc(v_bkt_593_);
v___x_612_ = lean_box(0);
v_buckets_x27_613_ = lean_array_uset(v_buckets_575_, v___x_592_, v___x_612_);
v___x_614_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2__spec__1_spec__2_spec__6___redArg(v_a_572_, v_b_573_, v_bkt_593_);
v___x_615_ = lean_array_uset(v_buckets_x27_613_, v___x_592_, v___x_614_);
if (v_isShared_578_ == 0)
{
lean_ctor_set(v___x_577_, 1, v___x_615_);
v___x_617_ = v___x_577_;
goto v_reusejp_616_;
}
else
{
lean_object* v_reuseFailAlloc_618_; 
v_reuseFailAlloc_618_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_618_, 0, v_size_574_);
lean_ctor_set(v_reuseFailAlloc_618_, 1, v___x_615_);
v___x_617_ = v_reuseFailAlloc_618_;
goto v_reusejp_616_;
}
v_reusejp_616_:
{
return v___x_617_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__3_spec__5___redArg(lean_object* v_x_622_, lean_object* v_x_623_, lean_object* v_x_624_, lean_object* v_x_625_){
_start:
{
lean_object* v_ks_626_; lean_object* v_vs_627_; lean_object* v___x_629_; uint8_t v_isShared_630_; uint8_t v_isSharedCheck_651_; 
v_ks_626_ = lean_ctor_get(v_x_622_, 0);
v_vs_627_ = lean_ctor_get(v_x_622_, 1);
v_isSharedCheck_651_ = !lean_is_exclusive(v_x_622_);
if (v_isSharedCheck_651_ == 0)
{
v___x_629_ = v_x_622_;
v_isShared_630_ = v_isSharedCheck_651_;
goto v_resetjp_628_;
}
else
{
lean_inc(v_vs_627_);
lean_inc(v_ks_626_);
lean_dec(v_x_622_);
v___x_629_ = lean_box(0);
v_isShared_630_ = v_isSharedCheck_651_;
goto v_resetjp_628_;
}
v_resetjp_628_:
{
lean_object* v___x_631_; uint8_t v___x_632_; 
v___x_631_ = lean_array_get_size(v_ks_626_);
v___x_632_ = lean_nat_dec_lt(v_x_623_, v___x_631_);
if (v___x_632_ == 0)
{
lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_636_; 
lean_dec(v_x_623_);
v___x_633_ = lean_array_push(v_ks_626_, v_x_624_);
v___x_634_ = lean_array_push(v_vs_627_, v_x_625_);
if (v_isShared_630_ == 0)
{
lean_ctor_set(v___x_629_, 1, v___x_634_);
lean_ctor_set(v___x_629_, 0, v___x_633_);
v___x_636_ = v___x_629_;
goto v_reusejp_635_;
}
else
{
lean_object* v_reuseFailAlloc_637_; 
v_reuseFailAlloc_637_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_637_, 0, v___x_633_);
lean_ctor_set(v_reuseFailAlloc_637_, 1, v___x_634_);
v___x_636_ = v_reuseFailAlloc_637_;
goto v_reusejp_635_;
}
v_reusejp_635_:
{
return v___x_636_;
}
}
else
{
lean_object* v_k_x27_638_; uint8_t v___x_639_; 
v_k_x27_638_ = lean_array_fget_borrowed(v_ks_626_, v_x_623_);
v___x_639_ = lean_name_eq(v_x_624_, v_k_x27_638_);
if (v___x_639_ == 0)
{
lean_object* v___x_641_; 
if (v_isShared_630_ == 0)
{
v___x_641_ = v___x_629_;
goto v_reusejp_640_;
}
else
{
lean_object* v_reuseFailAlloc_645_; 
v_reuseFailAlloc_645_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_645_, 0, v_ks_626_);
lean_ctor_set(v_reuseFailAlloc_645_, 1, v_vs_627_);
v___x_641_ = v_reuseFailAlloc_645_;
goto v_reusejp_640_;
}
v_reusejp_640_:
{
lean_object* v___x_642_; lean_object* v___x_643_; 
v___x_642_ = lean_unsigned_to_nat(1u);
v___x_643_ = lean_nat_add(v_x_623_, v___x_642_);
lean_dec(v_x_623_);
v_x_622_ = v___x_641_;
v_x_623_ = v___x_643_;
goto _start;
}
}
else
{
lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_649_; 
v___x_646_ = lean_array_fset(v_ks_626_, v_x_623_, v_x_624_);
v___x_647_ = lean_array_fset(v_vs_627_, v_x_623_, v_x_625_);
lean_dec(v_x_623_);
if (v_isShared_630_ == 0)
{
lean_ctor_set(v___x_629_, 1, v___x_647_);
lean_ctor_set(v___x_629_, 0, v___x_646_);
v___x_649_ = v___x_629_;
goto v_reusejp_648_;
}
else
{
lean_object* v_reuseFailAlloc_650_; 
v_reuseFailAlloc_650_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_650_, 0, v___x_646_);
lean_ctor_set(v_reuseFailAlloc_650_, 1, v___x_647_);
v___x_649_ = v_reuseFailAlloc_650_;
goto v_reusejp_648_;
}
v_reusejp_648_:
{
return v___x_649_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__3___redArg(lean_object* v_n_652_, lean_object* v_k_653_, lean_object* v_v_654_){
_start:
{
lean_object* v___x_655_; lean_object* v___x_656_; 
v___x_655_ = lean_unsigned_to_nat(0u);
v___x_656_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__3_spec__5___redArg(v_n_652_, v___x_655_, v_k_653_, v_v_654_);
return v___x_656_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2__spec__1_spec__1_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_657_; 
v___x_657_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_657_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2__spec__1_spec__1_spec__2___redArg(lean_object* v_x_658_, size_t v_x_659_, size_t v_x_660_, lean_object* v_x_661_, lean_object* v_x_662_){
_start:
{
if (lean_obj_tag(v_x_658_) == 0)
{
lean_object* v_es_663_; size_t v___x_664_; size_t v___x_665_; lean_object* v_j_666_; lean_object* v___x_667_; uint8_t v___x_668_; 
v_es_663_ = lean_ctor_get(v_x_658_, 0);
v___x_664_ = ((size_t)31ULL);
v___x_665_ = lean_usize_land(v_x_659_, v___x_664_);
v_j_666_ = lean_usize_to_nat(v___x_665_);
v___x_667_ = lean_array_get_size(v_es_663_);
v___x_668_ = lean_nat_dec_lt(v_j_666_, v___x_667_);
if (v___x_668_ == 0)
{
lean_dec(v_j_666_);
lean_dec(v_x_662_);
lean_dec(v_x_661_);
return v_x_658_;
}
else
{
lean_object* v___x_670_; uint8_t v_isShared_671_; uint8_t v_isSharedCheck_707_; 
lean_inc_ref(v_es_663_);
v_isSharedCheck_707_ = !lean_is_exclusive(v_x_658_);
if (v_isSharedCheck_707_ == 0)
{
lean_object* v_unused_708_; 
v_unused_708_ = lean_ctor_get(v_x_658_, 0);
lean_dec(v_unused_708_);
v___x_670_ = v_x_658_;
v_isShared_671_ = v_isSharedCheck_707_;
goto v_resetjp_669_;
}
else
{
lean_dec(v_x_658_);
v___x_670_ = lean_box(0);
v_isShared_671_ = v_isSharedCheck_707_;
goto v_resetjp_669_;
}
v_resetjp_669_:
{
lean_object* v_v_672_; lean_object* v___x_673_; lean_object* v_xs_x27_674_; lean_object* v___y_676_; 
v_v_672_ = lean_array_fget(v_es_663_, v_j_666_);
v___x_673_ = lean_box(0);
v_xs_x27_674_ = lean_array_fset(v_es_663_, v_j_666_, v___x_673_);
switch(lean_obj_tag(v_v_672_))
{
case 0:
{
lean_object* v_key_681_; lean_object* v_val_682_; lean_object* v___x_684_; uint8_t v_isShared_685_; uint8_t v_isSharedCheck_692_; 
v_key_681_ = lean_ctor_get(v_v_672_, 0);
v_val_682_ = lean_ctor_get(v_v_672_, 1);
v_isSharedCheck_692_ = !lean_is_exclusive(v_v_672_);
if (v_isSharedCheck_692_ == 0)
{
v___x_684_ = v_v_672_;
v_isShared_685_ = v_isSharedCheck_692_;
goto v_resetjp_683_;
}
else
{
lean_inc(v_val_682_);
lean_inc(v_key_681_);
lean_dec(v_v_672_);
v___x_684_ = lean_box(0);
v_isShared_685_ = v_isSharedCheck_692_;
goto v_resetjp_683_;
}
v_resetjp_683_:
{
uint8_t v___x_686_; 
v___x_686_ = lean_name_eq(v_x_661_, v_key_681_);
if (v___x_686_ == 0)
{
lean_object* v___x_687_; lean_object* v___x_688_; 
lean_del_object(v___x_684_);
v___x_687_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_681_, v_val_682_, v_x_661_, v_x_662_);
v___x_688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_688_, 0, v___x_687_);
v___y_676_ = v___x_688_;
goto v___jp_675_;
}
else
{
lean_object* v___x_690_; 
lean_dec(v_val_682_);
lean_dec(v_key_681_);
if (v_isShared_685_ == 0)
{
lean_ctor_set(v___x_684_, 1, v_x_662_);
lean_ctor_set(v___x_684_, 0, v_x_661_);
v___x_690_ = v___x_684_;
goto v_reusejp_689_;
}
else
{
lean_object* v_reuseFailAlloc_691_; 
v_reuseFailAlloc_691_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_691_, 0, v_x_661_);
lean_ctor_set(v_reuseFailAlloc_691_, 1, v_x_662_);
v___x_690_ = v_reuseFailAlloc_691_;
goto v_reusejp_689_;
}
v_reusejp_689_:
{
v___y_676_ = v___x_690_;
goto v___jp_675_;
}
}
}
}
case 1:
{
lean_object* v_node_693_; lean_object* v___x_695_; uint8_t v_isShared_696_; uint8_t v_isSharedCheck_705_; 
v_node_693_ = lean_ctor_get(v_v_672_, 0);
v_isSharedCheck_705_ = !lean_is_exclusive(v_v_672_);
if (v_isSharedCheck_705_ == 0)
{
v___x_695_ = v_v_672_;
v_isShared_696_ = v_isSharedCheck_705_;
goto v_resetjp_694_;
}
else
{
lean_inc(v_node_693_);
lean_dec(v_v_672_);
v___x_695_ = lean_box(0);
v_isShared_696_ = v_isSharedCheck_705_;
goto v_resetjp_694_;
}
v_resetjp_694_:
{
size_t v___x_697_; size_t v___x_698_; size_t v___x_699_; size_t v___x_700_; lean_object* v___x_701_; lean_object* v___x_703_; 
v___x_697_ = ((size_t)5ULL);
v___x_698_ = lean_usize_shift_right(v_x_659_, v___x_697_);
v___x_699_ = ((size_t)1ULL);
v___x_700_ = lean_usize_add(v_x_660_, v___x_699_);
v___x_701_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2__spec__1_spec__1_spec__2___redArg(v_node_693_, v___x_698_, v___x_700_, v_x_661_, v_x_662_);
if (v_isShared_696_ == 0)
{
lean_ctor_set(v___x_695_, 0, v___x_701_);
v___x_703_ = v___x_695_;
goto v_reusejp_702_;
}
else
{
lean_object* v_reuseFailAlloc_704_; 
v_reuseFailAlloc_704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_704_, 0, v___x_701_);
v___x_703_ = v_reuseFailAlloc_704_;
goto v_reusejp_702_;
}
v_reusejp_702_:
{
v___y_676_ = v___x_703_;
goto v___jp_675_;
}
}
}
default: 
{
lean_object* v___x_706_; 
v___x_706_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_706_, 0, v_x_661_);
lean_ctor_set(v___x_706_, 1, v_x_662_);
v___y_676_ = v___x_706_;
goto v___jp_675_;
}
}
v___jp_675_:
{
lean_object* v___x_677_; lean_object* v___x_679_; 
v___x_677_ = lean_array_fset(v_xs_x27_674_, v_j_666_, v___y_676_);
lean_dec(v_j_666_);
if (v_isShared_671_ == 0)
{
lean_ctor_set(v___x_670_, 0, v___x_677_);
v___x_679_ = v___x_670_;
goto v_reusejp_678_;
}
else
{
lean_object* v_reuseFailAlloc_680_; 
v_reuseFailAlloc_680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_680_, 0, v___x_677_);
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
}
else
{
lean_object* v_ks_709_; lean_object* v_vs_710_; lean_object* v___x_712_; uint8_t v_isShared_713_; uint8_t v_isSharedCheck_728_; 
v_ks_709_ = lean_ctor_get(v_x_658_, 0);
v_vs_710_ = lean_ctor_get(v_x_658_, 1);
v_isSharedCheck_728_ = !lean_is_exclusive(v_x_658_);
if (v_isSharedCheck_728_ == 0)
{
v___x_712_ = v_x_658_;
v_isShared_713_ = v_isSharedCheck_728_;
goto v_resetjp_711_;
}
else
{
lean_inc(v_vs_710_);
lean_inc(v_ks_709_);
lean_dec(v_x_658_);
v___x_712_ = lean_box(0);
v_isShared_713_ = v_isSharedCheck_728_;
goto v_resetjp_711_;
}
v_resetjp_711_:
{
lean_object* v___x_715_; 
if (v_isShared_713_ == 0)
{
v___x_715_ = v___x_712_;
goto v_reusejp_714_;
}
else
{
lean_object* v_reuseFailAlloc_727_; 
v_reuseFailAlloc_727_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_727_, 0, v_ks_709_);
lean_ctor_set(v_reuseFailAlloc_727_, 1, v_vs_710_);
v___x_715_ = v_reuseFailAlloc_727_;
goto v_reusejp_714_;
}
v_reusejp_714_:
{
lean_object* v_newNode_716_; size_t v___x_717_; uint8_t v___x_718_; 
v_newNode_716_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__3___redArg(v___x_715_, v_x_661_, v_x_662_);
v___x_717_ = ((size_t)7ULL);
v___x_718_ = lean_usize_dec_le(v___x_717_, v_x_660_);
if (v___x_718_ == 0)
{
lean_object* v___x_719_; lean_object* v___x_720_; uint8_t v___x_721_; 
v___x_719_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_716_);
v___x_720_ = lean_unsigned_to_nat(4u);
v___x_721_ = lean_nat_dec_lt(v___x_719_, v___x_720_);
lean_dec(v___x_719_);
if (v___x_721_ == 0)
{
lean_object* v_ks_722_; lean_object* v_vs_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; 
v_ks_722_ = lean_ctor_get(v_newNode_716_, 0);
lean_inc_ref(v_ks_722_);
v_vs_723_ = lean_ctor_get(v_newNode_716_, 1);
lean_inc_ref(v_vs_723_);
lean_dec_ref(v_newNode_716_);
v___x_724_ = lean_unsigned_to_nat(0u);
v___x_725_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2__spec__1_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2__spec__1_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2__spec__1_spec__1_spec__2___redArg___closed__0);
v___x_726_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__4___redArg(v_x_660_, v_ks_722_, v_vs_723_, v___x_724_, v___x_725_);
lean_dec_ref(v_vs_723_);
lean_dec_ref(v_ks_722_);
return v___x_726_;
}
else
{
return v_newNode_716_;
}
}
else
{
return v_newNode_716_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__4___redArg(size_t v_depth_729_, lean_object* v_keys_730_, lean_object* v_vals_731_, lean_object* v_i_732_, lean_object* v_entries_733_){
_start:
{
lean_object* v___x_734_; uint8_t v___x_735_; 
v___x_734_ = lean_array_get_size(v_keys_730_);
v___x_735_ = lean_nat_dec_lt(v_i_732_, v___x_734_);
if (v___x_735_ == 0)
{
lean_dec(v_i_732_);
return v_entries_733_;
}
else
{
lean_object* v_k_736_; lean_object* v_v_737_; uint64_t v___y_739_; 
v_k_736_ = lean_array_fget_borrowed(v_keys_730_, v_i_732_);
v_v_737_ = lean_array_fget_borrowed(v_vals_731_, v_i_732_);
if (lean_obj_tag(v_k_736_) == 0)
{
uint64_t v___x_750_; 
v___x_750_ = 1723ULL;
v___y_739_ = v___x_750_;
goto v___jp_738_;
}
else
{
uint64_t v_hash_751_; 
v_hash_751_ = lean_ctor_get_uint64(v_k_736_, sizeof(void*)*2);
v___y_739_ = v_hash_751_;
goto v___jp_738_;
}
v___jp_738_:
{
size_t v_h_740_; size_t v___x_741_; lean_object* v___x_742_; size_t v___x_743_; size_t v___x_744_; size_t v___x_745_; size_t v_h_746_; lean_object* v___x_747_; lean_object* v___x_748_; 
v_h_740_ = lean_uint64_to_usize(v___y_739_);
v___x_741_ = ((size_t)5ULL);
v___x_742_ = lean_unsigned_to_nat(1u);
v___x_743_ = ((size_t)1ULL);
v___x_744_ = lean_usize_sub(v_depth_729_, v___x_743_);
v___x_745_ = lean_usize_mul(v___x_741_, v___x_744_);
v_h_746_ = lean_usize_shift_right(v_h_740_, v___x_745_);
v___x_747_ = lean_nat_add(v_i_732_, v___x_742_);
lean_dec(v_i_732_);
lean_inc(v_v_737_);
lean_inc(v_k_736_);
v___x_748_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2__spec__1_spec__1_spec__2___redArg(v_entries_733_, v_h_746_, v_depth_729_, v_k_736_, v_v_737_);
v_i_732_ = v___x_747_;
v_entries_733_ = v___x_748_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_depth_752_, lean_object* v_keys_753_, lean_object* v_vals_754_, lean_object* v_i_755_, lean_object* v_entries_756_){
_start:
{
size_t v_depth_boxed_757_; lean_object* v_res_758_; 
v_depth_boxed_757_ = lean_unbox_usize(v_depth_752_);
lean_dec(v_depth_752_);
v_res_758_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__4___redArg(v_depth_boxed_757_, v_keys_753_, v_vals_754_, v_i_755_, v_entries_756_);
lean_dec_ref(v_vals_754_);
lean_dec_ref(v_keys_753_);
return v_res_758_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2__spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_x_759_, lean_object* v_x_760_, lean_object* v_x_761_, lean_object* v_x_762_, lean_object* v_x_763_){
_start:
{
size_t v_x_1194__boxed_764_; size_t v_x_1195__boxed_765_; lean_object* v_res_766_; 
v_x_1194__boxed_764_ = lean_unbox_usize(v_x_760_);
lean_dec(v_x_760_);
v_x_1195__boxed_765_ = lean_unbox_usize(v_x_761_);
lean_dec(v_x_761_);
v_res_766_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2__spec__1_spec__1_spec__2___redArg(v_x_759_, v_x_1194__boxed_764_, v_x_1195__boxed_765_, v_x_762_, v_x_763_);
return v_res_766_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2__spec__1_spec__1___redArg(lean_object* v_x_767_, lean_object* v_x_768_, lean_object* v_x_769_){
_start:
{
uint64_t v___y_771_; 
if (lean_obj_tag(v_x_768_) == 0)
{
uint64_t v___x_775_; 
v___x_775_ = 1723ULL;
v___y_771_ = v___x_775_;
goto v___jp_770_;
}
else
{
uint64_t v_hash_776_; 
v_hash_776_ = lean_ctor_get_uint64(v_x_768_, sizeof(void*)*2);
v___y_771_ = v_hash_776_;
goto v___jp_770_;
}
v___jp_770_:
{
size_t v___x_772_; size_t v___x_773_; lean_object* v___x_774_; 
v___x_772_ = lean_uint64_to_usize(v___y_771_);
v___x_773_ = ((size_t)1ULL);
v___x_774_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2__spec__1_spec__1_spec__2___redArg(v_x_767_, v___x_772_, v___x_773_, v_x_768_, v_x_769_);
return v___x_774_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2__spec__1___redArg(lean_object* v_x_777_, lean_object* v_x_778_, lean_object* v_x_779_){
_start:
{
uint8_t v_stage_u2081_780_; 
v_stage_u2081_780_ = lean_ctor_get_uint8(v_x_777_, sizeof(void*)*2);
if (v_stage_u2081_780_ == 0)
{
lean_object* v_map_u2081_781_; lean_object* v_map_u2082_782_; lean_object* v___x_784_; uint8_t v_isShared_785_; uint8_t v_isSharedCheck_790_; 
v_map_u2081_781_ = lean_ctor_get(v_x_777_, 0);
v_map_u2082_782_ = lean_ctor_get(v_x_777_, 1);
v_isSharedCheck_790_ = !lean_is_exclusive(v_x_777_);
if (v_isSharedCheck_790_ == 0)
{
v___x_784_ = v_x_777_;
v_isShared_785_ = v_isSharedCheck_790_;
goto v_resetjp_783_;
}
else
{
lean_inc(v_map_u2082_782_);
lean_inc(v_map_u2081_781_);
lean_dec(v_x_777_);
v___x_784_ = lean_box(0);
v_isShared_785_ = v_isSharedCheck_790_;
goto v_resetjp_783_;
}
v_resetjp_783_:
{
lean_object* v___x_786_; lean_object* v___x_788_; 
v___x_786_ = l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2__spec__1_spec__1___redArg(v_map_u2082_782_, v_x_778_, v_x_779_);
if (v_isShared_785_ == 0)
{
lean_ctor_set(v___x_784_, 1, v___x_786_);
v___x_788_ = v___x_784_;
goto v_reusejp_787_;
}
else
{
lean_object* v_reuseFailAlloc_789_; 
v_reuseFailAlloc_789_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_789_, 0, v_map_u2081_781_);
lean_ctor_set(v_reuseFailAlloc_789_, 1, v___x_786_);
lean_ctor_set_uint8(v_reuseFailAlloc_789_, sizeof(void*)*2, v_stage_u2081_780_);
v___x_788_ = v_reuseFailAlloc_789_;
goto v_reusejp_787_;
}
v_reusejp_787_:
{
return v___x_788_;
}
}
}
else
{
lean_object* v_map_u2081_791_; lean_object* v_map_u2082_792_; lean_object* v___x_794_; uint8_t v_isShared_795_; uint8_t v_isSharedCheck_800_; 
v_map_u2081_791_ = lean_ctor_get(v_x_777_, 0);
v_map_u2082_792_ = lean_ctor_get(v_x_777_, 1);
v_isSharedCheck_800_ = !lean_is_exclusive(v_x_777_);
if (v_isSharedCheck_800_ == 0)
{
v___x_794_ = v_x_777_;
v_isShared_795_ = v_isSharedCheck_800_;
goto v_resetjp_793_;
}
else
{
lean_inc(v_map_u2082_792_);
lean_inc(v_map_u2081_791_);
lean_dec(v_x_777_);
v___x_794_ = lean_box(0);
v_isShared_795_ = v_isSharedCheck_800_;
goto v_resetjp_793_;
}
v_resetjp_793_:
{
lean_object* v___x_796_; lean_object* v___x_798_; 
v___x_796_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2__spec__1_spec__2___redArg(v_map_u2081_791_, v_x_778_, v_x_779_);
if (v_isShared_795_ == 0)
{
lean_ctor_set(v___x_794_, 0, v___x_796_);
v___x_798_ = v___x_794_;
goto v_reusejp_797_;
}
else
{
lean_object* v_reuseFailAlloc_799_; 
v_reuseFailAlloc_799_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_799_, 0, v___x_796_);
lean_ctor_set(v_reuseFailAlloc_799_, 1, v_map_u2082_792_);
lean_ctor_set_uint8(v_reuseFailAlloc_799_, sizeof(void*)*2, v_stage_u2081_780_);
v___x_798_ = v_reuseFailAlloc_799_;
goto v_reusejp_797_;
}
v_reusejp_797_:
{
return v___x_798_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__0_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2_(lean_object* v_d_801_, lean_object* v_x_802_){
_start:
{
lean_object* v_fst_803_; lean_object* v_snd_804_; lean_object* v___x_805_; 
v_fst_803_ = lean_ctor_get(v_x_802_, 0);
lean_inc(v_fst_803_);
v_snd_804_ = lean_ctor_get(v_x_802_, 1);
lean_inc(v_snd_804_);
lean_dec_ref(v_x_802_);
v___x_805_ = l_Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2__spec__1___redArg(v_d_801_, v_fst_803_, v_snd_804_);
return v___x_805_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__1_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2_(lean_object* v_x_806_, lean_object* v_a_807_){
_start:
{
lean_object* v___x_808_; lean_object* v___x_809_; 
v___x_808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_808_, 0, v_a_807_);
lean_inc_ref_n(v___x_808_, 2);
v___x_809_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_809_, 0, v___x_808_);
lean_ctor_set(v___x_809_, 1, v___x_808_);
lean_ctor_set(v___x_809_, 2, v___x_808_);
return v___x_809_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__1_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2____boxed(lean_object* v_x_810_, lean_object* v_a_811_){
_start:
{
lean_object* v_res_812_; 
v_res_812_ = l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__1_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2_(v_x_810_, v_a_811_);
lean_dec_ref(v_x_810_);
return v_res_812_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__2_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2_(lean_object* v_x_813_){
_start:
{
lean_object* v_fst_814_; 
v_fst_814_ = lean_ctor_get(v_x_813_, 0);
lean_inc(v_fst_814_);
return v_fst_814_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__2_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2____boxed(lean_object* v_x_815_){
_start:
{
lean_object* v_res_816_; 
v_res_816_ = l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__2_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2_(v_x_815_);
lean_dec_ref(v_x_815_);
return v_res_816_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__3_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2_(lean_object* v_x_817_, lean_object* v_a_818_, lean_object* v___y_819_){
_start:
{
lean_object* v___x_821_; 
v___x_821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_821_, 0, v_a_818_);
return v___x_821_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__3_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2____boxed(lean_object* v_x_822_, lean_object* v_a_823_, lean_object* v___y_824_, lean_object* v___y_825_){
_start:
{
lean_object* v_res_826_; 
v_res_826_ = l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__3_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2_(v_x_822_, v_a_823_, v___y_824_);
lean_dec_ref(v___y_824_);
lean_dec_ref(v_x_822_);
return v_res_826_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__4_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2_(lean_object* v___x_827_){
_start:
{
lean_object* v___x_829_; 
v___x_829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_829_, 0, v___x_827_);
return v___x_829_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__4_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2____boxed(lean_object* v___x_830_, lean_object* v___y_831_){
_start:
{
lean_object* v_res_832_; 
v_res_832_ = l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__4_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2_(v___x_830_);
return v_res_832_;
}
}
static lean_object* _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__7_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; 
v___x_841_ = lean_box(0);
v___x_842_ = lean_unsigned_to_nat(16u);
v___x_843_ = lean_mk_array(v___x_842_, v___x_841_);
return v___x_843_;
}
}
static lean_object* _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__8_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; 
v___x_844_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__7_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2_, &l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__7_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2__once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__7_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2_);
v___x_845_ = lean_unsigned_to_nat(0u);
v___x_846_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_846_, 0, v___x_845_);
lean_ctor_set(v___x_846_, 1, v___x_844_);
return v___x_846_;
}
}
static lean_object* _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__9_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_847_; 
v___x_847_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_847_;
}
}
static lean_object* _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__10_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_848_; lean_object* v___x_849_; 
v___x_848_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__9_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2_, &l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__9_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2__once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__9_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2_);
v___x_849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_849_, 0, v___x_848_);
return v___x_849_;
}
}
static lean_object* _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__11_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_850_; lean_object* v___x_851_; uint8_t v___x_852_; lean_object* v___x_853_; 
v___x_850_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__10_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2_, &l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__10_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2__once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__10_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2_);
v___x_851_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__8_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2_, &l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__8_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2__once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__8_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2_);
v___x_852_ = 1;
v___x_853_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_853_, 0, v___x_851_);
lean_ctor_set(v___x_853_, 1, v___x_850_);
lean_ctor_set_uint8(v___x_853_, sizeof(void*)*2, v___x_852_);
return v___x_853_;
}
}
static lean_object* _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__12_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_854_; lean_object* v___f_855_; 
v___x_854_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__11_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2_, &l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__11_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2__once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__11_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2_);
v___f_855_ = lean_alloc_closure((void*)(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__4_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_855_, 0, v___x_854_);
return v___f_855_;
}
}
static lean_object* _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__14_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_858_; lean_object* v___f_859_; lean_object* v___f_860_; lean_object* v___x_861_; 
v___f_858_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2_));
v___f_859_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__4_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2_));
v___f_860_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__12_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2_, &l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__12_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2__once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__12_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2_);
v___x_861_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_addImportedGlobals___boxed), 9, 6);
lean_closure_set(v___x_861_, 0, lean_box(0));
lean_closure_set(v___x_861_, 1, lean_box(0));
lean_closure_set(v___x_861_, 2, lean_box(0));
lean_closure_set(v___x_861_, 3, v___f_860_);
lean_closure_set(v___x_861_, 4, v___f_859_);
lean_closure_set(v___x_861_, 5, v___f_858_);
return v___x_861_;
}
}
static lean_object* _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__15_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_862_; lean_object* v___x_863_; uint8_t v___x_864_; uint8_t v___x_865_; lean_object* v___f_866_; lean_object* v___f_867_; lean_object* v___x_868_; lean_object* v___f_869_; lean_object* v___x_870_; lean_object* v___x_871_; 
v___x_862_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__14_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2_, &l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__14_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2__once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__14_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2_);
v___x_863_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__13_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2_));
v___x_864_ = 1;
v___x_865_ = 0;
v___f_866_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2_));
v___f_867_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2_));
v___x_868_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__11_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2_, &l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__11_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2__once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__11_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2_);
v___f_869_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2_));
v___x_870_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__6_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2_));
v___x_871_ = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(v___x_871_, 0, v___x_870_);
lean_ctor_set(v___x_871_, 1, v___f_869_);
lean_ctor_set(v___x_871_, 2, v___f_869_);
lean_ctor_set(v___x_871_, 3, v___x_868_);
lean_ctor_set(v___x_871_, 4, v___f_867_);
lean_ctor_set(v___x_871_, 5, v___f_866_);
lean_ctor_set(v___x_871_, 6, v___x_863_);
lean_ctor_set(v___x_871_, 7, v___x_862_);
lean_ctor_set_uint8(v___x_871_, sizeof(void*)*8, v___x_865_);
lean_ctor_set_uint8(v___x_871_, sizeof(void*)*8 + 1, v___x_864_);
return v___x_871_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_873_; lean_object* v___x_874_; 
v___x_873_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__15_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2_, &l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__15_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2__once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__15_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2_);
v___x_874_ = l_Lean_registerSimpleScopedEnvExtension___redArg(v___x_873_);
return v___x_874_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2____boxed(lean_object* v_a_875_){
_start:
{
lean_object* v_res_876_; 
v_res_876_ = l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2_();
return v_res_876_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2__spec__1(lean_object* v_00_u03b2_877_, lean_object* v_x_878_, lean_object* v_x_879_, lean_object* v_x_880_){
_start:
{
lean_object* v___x_881_; 
v___x_881_ = l_Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2__spec__1___redArg(v_x_878_, v_x_879_, v_x_880_);
return v___x_881_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2__spec__1_spec__1(lean_object* v_00_u03b2_882_, lean_object* v_x_883_, lean_object* v_x_884_, lean_object* v_x_885_){
_start:
{
lean_object* v___x_886_; 
v___x_886_ = l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2__spec__1_spec__1___redArg(v_x_883_, v_x_884_, v_x_885_);
return v___x_886_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2__spec__1_spec__2(lean_object* v_00_u03b2_887_, lean_object* v_m_888_, lean_object* v_a_889_, lean_object* v_b_890_){
_start:
{
lean_object* v___x_891_; 
v___x_891_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2__spec__1_spec__2___redArg(v_m_888_, v_a_889_, v_b_890_);
return v___x_891_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2__spec__1_spec__1_spec__2(lean_object* v_00_u03b2_892_, lean_object* v_x_893_, size_t v_x_894_, size_t v_x_895_, lean_object* v_x_896_, lean_object* v_x_897_){
_start:
{
lean_object* v___x_898_; 
v___x_898_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2__spec__1_spec__1_spec__2___redArg(v_x_893_, v_x_894_, v_x_895_, v_x_896_, v_x_897_);
return v___x_898_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2__spec__1_spec__1_spec__2___boxed(lean_object* v_00_u03b2_899_, lean_object* v_x_900_, lean_object* v_x_901_, lean_object* v_x_902_, lean_object* v_x_903_, lean_object* v_x_904_){
_start:
{
size_t v_x_1595__boxed_905_; size_t v_x_1596__boxed_906_; lean_object* v_res_907_; 
v_x_1595__boxed_905_ = lean_unbox_usize(v_x_901_);
lean_dec(v_x_901_);
v_x_1596__boxed_906_ = lean_unbox_usize(v_x_902_);
lean_dec(v_x_902_);
v_res_907_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2__spec__1_spec__1_spec__2(v_00_u03b2_899_, v_x_900_, v_x_1595__boxed_905_, v_x_1596__boxed_906_, v_x_903_, v_x_904_);
return v_res_907_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2__spec__1_spec__2_spec__4(lean_object* v_00_u03b2_908_, lean_object* v_a_909_, lean_object* v_x_910_){
_start:
{
uint8_t v___x_911_; 
v___x_911_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg(v_a_909_, v_x_910_);
return v___x_911_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2__spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b2_912_, lean_object* v_a_913_, lean_object* v_x_914_){
_start:
{
uint8_t v_res_915_; lean_object* v_r_916_; 
v_res_915_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2__spec__1_spec__2_spec__4(v_00_u03b2_912_, v_a_913_, v_x_914_);
lean_dec(v_x_914_);
lean_dec(v_a_913_);
v_r_916_ = lean_box(v_res_915_);
return v_r_916_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2__spec__1_spec__2_spec__5(lean_object* v_00_u03b2_917_, lean_object* v_data_918_){
_start:
{
lean_object* v___x_919_; 
v___x_919_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2__spec__1_spec__2_spec__5___redArg(v_data_918_);
return v___x_919_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2__spec__1_spec__2_spec__6(lean_object* v_00_u03b2_920_, lean_object* v_a_921_, lean_object* v_b_922_, lean_object* v_x_923_){
_start:
{
lean_object* v___x_924_; 
v___x_924_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2__spec__1_spec__2_spec__6___redArg(v_a_921_, v_b_922_, v_x_923_);
return v___x_924_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_925_, lean_object* v_n_926_, lean_object* v_k_927_, lean_object* v_v_928_){
_start:
{
lean_object* v___x_929_; 
v___x_929_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__3___redArg(v_n_926_, v_k_927_, v_v_928_);
return v___x_929_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_930_, size_t v_depth_931_, lean_object* v_keys_932_, lean_object* v_vals_933_, lean_object* v_heq_934_, lean_object* v_i_935_, lean_object* v_entries_936_){
_start:
{
lean_object* v___x_937_; 
v___x_937_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__4___redArg(v_depth_931_, v_keys_932_, v_vals_933_, v_i_935_, v_entries_936_);
return v___x_937_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b2_938_, lean_object* v_depth_939_, lean_object* v_keys_940_, lean_object* v_vals_941_, lean_object* v_heq_942_, lean_object* v_i_943_, lean_object* v_entries_944_){
_start:
{
size_t v_depth_boxed_945_; lean_object* v_res_946_; 
v_depth_boxed_945_ = lean_unbox_usize(v_depth_939_);
lean_dec(v_depth_939_);
v_res_946_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__4(v_00_u03b2_938_, v_depth_boxed_945_, v_keys_940_, v_vals_941_, v_heq_942_, v_i_943_, v_entries_944_);
lean_dec_ref(v_vals_941_);
lean_dec_ref(v_keys_940_);
return v_res_946_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8(lean_object* v_00_u03b2_947_, lean_object* v_i_948_, lean_object* v_source_949_, lean_object* v_target_950_){
_start:
{
lean_object* v___x_951_; 
v___x_951_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8___redArg(v_i_948_, v_source_949_, v_target_950_);
return v___x_951_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__3_spec__5(lean_object* v_00_u03b2_952_, lean_object* v_x_953_, lean_object* v_x_954_, lean_object* v_x_955_, lean_object* v_x_956_){
_start:
{
lean_object* v___x_957_; 
v___x_957_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__3_spec__5___redArg(v_x_953_, v_x_954_, v_x_955_, v_x_956_);
return v___x_957_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8_spec__10(lean_object* v_00_u03b2_958_, lean_object* v_x_959_, lean_object* v_x_960_){
_start:
{
lean_object* v___x_961_; 
v___x_961_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8_spec__10___redArg(v_x_959_, v_x_960_);
return v___x_961_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_keys_962_, lean_object* v_vals_963_, lean_object* v_i_964_, lean_object* v_k_965_){
_start:
{
lean_object* v___x_966_; uint8_t v___x_967_; 
v___x_966_ = lean_array_get_size(v_keys_962_);
v___x_967_ = lean_nat_dec_lt(v_i_964_, v___x_966_);
if (v___x_967_ == 0)
{
lean_object* v___x_968_; 
lean_dec(v_i_964_);
v___x_968_ = lean_box(0);
return v___x_968_;
}
else
{
lean_object* v_k_x27_969_; uint8_t v___x_970_; 
v_k_x27_969_ = lean_array_fget_borrowed(v_keys_962_, v_i_964_);
v___x_970_ = lean_name_eq(v_k_965_, v_k_x27_969_);
if (v___x_970_ == 0)
{
lean_object* v___x_971_; lean_object* v___x_972_; 
v___x_971_ = lean_unsigned_to_nat(1u);
v___x_972_ = lean_nat_add(v_i_964_, v___x_971_);
lean_dec(v_i_964_);
v_i_964_ = v___x_972_;
goto _start;
}
else
{
lean_object* v___x_974_; lean_object* v___x_975_; 
v___x_974_ = lean_array_fget_borrowed(v_vals_963_, v_i_964_);
lean_dec(v_i_964_);
lean_inc(v___x_974_);
v___x_975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_975_, 0, v___x_974_);
return v___x_975_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_keys_976_, lean_object* v_vals_977_, lean_object* v_i_978_, lean_object* v_k_979_){
_start:
{
lean_object* v_res_980_; 
v_res_980_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__0_spec__1_spec__2___redArg(v_keys_976_, v_vals_977_, v_i_978_, v_k_979_);
lean_dec(v_k_979_);
lean_dec_ref(v_vals_977_);
lean_dec_ref(v_keys_976_);
return v_res_980_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__0_spec__1___redArg(lean_object* v_x_981_, size_t v_x_982_, lean_object* v_x_983_){
_start:
{
if (lean_obj_tag(v_x_981_) == 0)
{
lean_object* v_es_984_; lean_object* v___x_985_; size_t v___x_986_; size_t v___x_987_; lean_object* v_j_988_; lean_object* v___x_989_; 
v_es_984_ = lean_ctor_get(v_x_981_, 0);
v___x_985_ = lean_box(2);
v___x_986_ = ((size_t)31ULL);
v___x_987_ = lean_usize_land(v_x_982_, v___x_986_);
v_j_988_ = lean_usize_to_nat(v___x_987_);
v___x_989_ = lean_array_get_borrowed(v___x_985_, v_es_984_, v_j_988_);
lean_dec(v_j_988_);
switch(lean_obj_tag(v___x_989_))
{
case 0:
{
lean_object* v_key_990_; lean_object* v_val_991_; uint8_t v___x_992_; 
v_key_990_ = lean_ctor_get(v___x_989_, 0);
v_val_991_ = lean_ctor_get(v___x_989_, 1);
v___x_992_ = lean_name_eq(v_x_983_, v_key_990_);
if (v___x_992_ == 0)
{
lean_object* v___x_993_; 
v___x_993_ = lean_box(0);
return v___x_993_;
}
else
{
lean_object* v___x_994_; 
lean_inc(v_val_991_);
v___x_994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_994_, 0, v_val_991_);
return v___x_994_;
}
}
case 1:
{
lean_object* v_node_995_; size_t v___x_996_; size_t v___x_997_; 
v_node_995_ = lean_ctor_get(v___x_989_, 0);
v___x_996_ = ((size_t)5ULL);
v___x_997_ = lean_usize_shift_right(v_x_982_, v___x_996_);
v_x_981_ = v_node_995_;
v_x_982_ = v___x_997_;
goto _start;
}
default: 
{
lean_object* v___x_999_; 
v___x_999_ = lean_box(0);
return v___x_999_;
}
}
}
else
{
lean_object* v_ks_1000_; lean_object* v_vs_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; 
v_ks_1000_ = lean_ctor_get(v_x_981_, 0);
v_vs_1001_ = lean_ctor_get(v_x_981_, 1);
v___x_1002_ = lean_unsigned_to_nat(0u);
v___x_1003_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__0_spec__1_spec__2___redArg(v_ks_1000_, v_vs_1001_, v___x_1002_, v_x_983_);
return v___x_1003_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_1004_, lean_object* v_x_1005_, lean_object* v_x_1006_){
_start:
{
size_t v_x_365__boxed_1007_; lean_object* v_res_1008_; 
v_x_365__boxed_1007_ = lean_unbox_usize(v_x_1005_);
lean_dec(v_x_1005_);
v_res_1008_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__0_spec__1___redArg(v_x_1004_, v_x_365__boxed_1007_, v_x_1006_);
lean_dec(v_x_1006_);
lean_dec_ref(v_x_1004_);
return v_res_1008_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__0___redArg(lean_object* v_x_1009_, lean_object* v_x_1010_){
_start:
{
uint64_t v___y_1012_; 
if (lean_obj_tag(v_x_1010_) == 0)
{
uint64_t v___x_1015_; 
v___x_1015_ = 1723ULL;
v___y_1012_ = v___x_1015_;
goto v___jp_1011_;
}
else
{
uint64_t v_hash_1016_; 
v_hash_1016_ = lean_ctor_get_uint64(v_x_1010_, sizeof(void*)*2);
v___y_1012_ = v_hash_1016_;
goto v___jp_1011_;
}
v___jp_1011_:
{
size_t v___x_1013_; lean_object* v___x_1014_; 
v___x_1013_ = lean_uint64_to_usize(v___y_1012_);
v___x_1014_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__0_spec__1___redArg(v_x_1009_, v___x_1013_, v_x_1010_);
return v___x_1014_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__0___redArg___boxed(lean_object* v_x_1017_, lean_object* v_x_1018_){
_start:
{
lean_object* v_res_1019_; 
v_res_1019_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__0___redArg(v_x_1017_, v_x_1018_);
lean_dec(v_x_1018_);
lean_dec_ref(v_x_1017_);
return v_res_1019_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__1_spec__3___redArg(lean_object* v_a_1020_, lean_object* v_x_1021_){
_start:
{
if (lean_obj_tag(v_x_1021_) == 0)
{
lean_object* v___x_1022_; 
v___x_1022_ = lean_box(0);
return v___x_1022_;
}
else
{
lean_object* v_key_1023_; lean_object* v_value_1024_; lean_object* v_tail_1025_; uint8_t v___x_1026_; 
v_key_1023_ = lean_ctor_get(v_x_1021_, 0);
v_value_1024_ = lean_ctor_get(v_x_1021_, 1);
v_tail_1025_ = lean_ctor_get(v_x_1021_, 2);
v___x_1026_ = lean_name_eq(v_key_1023_, v_a_1020_);
if (v___x_1026_ == 0)
{
v_x_1021_ = v_tail_1025_;
goto _start;
}
else
{
lean_object* v___x_1028_; 
lean_inc(v_value_1024_);
v___x_1028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1028_, 0, v_value_1024_);
return v___x_1028_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_a_1029_, lean_object* v_x_1030_){
_start:
{
lean_object* v_res_1031_; 
v_res_1031_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__1_spec__3___redArg(v_a_1029_, v_x_1030_);
lean_dec(v_x_1030_);
lean_dec(v_a_1029_);
return v_res_1031_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__1___redArg(lean_object* v_m_1032_, lean_object* v_a_1033_){
_start:
{
lean_object* v_buckets_1034_; lean_object* v___x_1035_; uint64_t v___y_1037_; 
v_buckets_1034_ = lean_ctor_get(v_m_1032_, 1);
v___x_1035_ = lean_array_get_size(v_buckets_1034_);
if (lean_obj_tag(v_a_1033_) == 0)
{
uint64_t v___x_1051_; 
v___x_1051_ = 1723ULL;
v___y_1037_ = v___x_1051_;
goto v___jp_1036_;
}
else
{
uint64_t v_hash_1052_; 
v_hash_1052_ = lean_ctor_get_uint64(v_a_1033_, sizeof(void*)*2);
v___y_1037_ = v_hash_1052_;
goto v___jp_1036_;
}
v___jp_1036_:
{
uint64_t v___x_1038_; uint64_t v___x_1039_; uint64_t v_fold_1040_; uint64_t v___x_1041_; uint64_t v___x_1042_; uint64_t v___x_1043_; size_t v___x_1044_; size_t v___x_1045_; size_t v___x_1046_; size_t v___x_1047_; size_t v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; 
v___x_1038_ = 32ULL;
v___x_1039_ = lean_uint64_shift_right(v___y_1037_, v___x_1038_);
v_fold_1040_ = lean_uint64_xor(v___y_1037_, v___x_1039_);
v___x_1041_ = 16ULL;
v___x_1042_ = lean_uint64_shift_right(v_fold_1040_, v___x_1041_);
v___x_1043_ = lean_uint64_xor(v_fold_1040_, v___x_1042_);
v___x_1044_ = lean_uint64_to_usize(v___x_1043_);
v___x_1045_ = lean_usize_of_nat(v___x_1035_);
v___x_1046_ = ((size_t)1ULL);
v___x_1047_ = lean_usize_sub(v___x_1045_, v___x_1046_);
v___x_1048_ = lean_usize_land(v___x_1044_, v___x_1047_);
v___x_1049_ = lean_array_uget_borrowed(v_buckets_1034_, v___x_1048_);
v___x_1050_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__1_spec__3___redArg(v_a_1033_, v___x_1049_);
return v___x_1050_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__1___redArg___boxed(lean_object* v_m_1053_, lean_object* v_a_1054_){
_start:
{
lean_object* v_res_1055_; 
v_res_1055_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__1___redArg(v_m_1053_, v_a_1054_);
lean_dec(v_a_1054_);
lean_dec_ref(v_m_1053_);
return v_res_1055_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0___redArg(lean_object* v_x_1056_, lean_object* v_x_1057_){
_start:
{
uint8_t v_stage_u2081_1058_; 
v_stage_u2081_1058_ = lean_ctor_get_uint8(v_x_1056_, sizeof(void*)*2);
if (v_stage_u2081_1058_ == 0)
{
lean_object* v_map_u2081_1059_; lean_object* v_map_u2082_1060_; lean_object* v___x_1061_; 
v_map_u2081_1059_ = lean_ctor_get(v_x_1056_, 0);
v_map_u2082_1060_ = lean_ctor_get(v_x_1056_, 1);
v___x_1061_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__0___redArg(v_map_u2082_1060_, v_x_1057_);
if (lean_obj_tag(v___x_1061_) == 0)
{
lean_object* v___x_1062_; 
v___x_1062_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__1___redArg(v_map_u2081_1059_, v_x_1057_);
return v___x_1062_;
}
else
{
return v___x_1061_;
}
}
else
{
lean_object* v_map_u2081_1063_; lean_object* v___x_1064_; 
v_map_u2081_1063_ = lean_ctor_get(v_x_1056_, 0);
v___x_1064_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__1___redArg(v_map_u2081_1063_, v_x_1057_);
return v___x_1064_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0___redArg___boxed(lean_object* v_x_1065_, lean_object* v_x_1066_){
_start:
{
lean_object* v_res_1067_; 
v_res_1067_ = l_Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0___redArg(v_x_1065_, v_x_1066_);
lean_dec(v_x_1066_);
lean_dec_ref(v_x_1065_);
return v_res_1067_;
}
}
static lean_object* _init_l_Lean_getReducibilityStatusCore___closed__0(void){
_start:
{
lean_object* v___x_1068_; 
v___x_1068_ = l_Lean_SMap_instInhabited___redArg();
return v___x_1068_;
}
}
LEAN_EXPORT uint8_t l_Lean_getReducibilityStatusCore(lean_object* v_env_1069_, lean_object* v_declName_1070_){
_start:
{
lean_object* v___x_1071_; lean_object* v_ext_1072_; lean_object* v_toEnvExtension_1073_; lean_object* v_asyncMode_1074_; lean_object* v___x_1075_; uint8_t v___x_1076_; lean_object* v_m_1077_; lean_object* v___x_1078_; 
v___x_1071_ = l_Lean_reducibilityExtraExt;
v_ext_1072_ = lean_ctor_get(v___x_1071_, 1);
v_toEnvExtension_1073_ = lean_ctor_get(v_ext_1072_, 0);
v_asyncMode_1074_ = lean_ctor_get(v_toEnvExtension_1073_, 2);
v___x_1075_ = lean_obj_once(&l_Lean_getReducibilityStatusCore___closed__0, &l_Lean_getReducibilityStatusCore___closed__0_once, _init_l_Lean_getReducibilityStatusCore___closed__0);
v___x_1076_ = 0;
lean_inc_ref(v_env_1069_);
v_m_1077_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_1075_, v___x_1071_, v_env_1069_, v_asyncMode_1074_, v___x_1076_);
v___x_1078_ = l_Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0___redArg(v_m_1077_, v_declName_1070_);
lean_dec(v_m_1077_);
if (lean_obj_tag(v___x_1078_) == 1)
{
lean_object* v_val_1079_; uint8_t v___x_1080_; 
lean_dec(v_declName_1070_);
lean_dec_ref(v_env_1069_);
v_val_1079_ = lean_ctor_get(v___x_1078_, 0);
lean_inc(v_val_1079_);
lean_dec_ref_known(v___x_1078_, 1);
v___x_1080_ = lean_unbox(v_val_1079_);
lean_dec(v_val_1079_);
return v___x_1080_;
}
else
{
lean_object* v___x_1081_; lean_object* v___x_1082_; 
lean_dec(v___x_1078_);
v___x_1081_ = lean_box(1);
v___x_1082_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1069_, v_declName_1070_);
if (lean_obj_tag(v___x_1082_) == 0)
{
lean_object* v___x_1083_; lean_object* v_toEnvExtension_1084_; lean_object* v_asyncMode_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; 
v___x_1083_ = l_Lean_reducibilityCoreExt;
v_toEnvExtension_1084_ = lean_ctor_get(v___x_1083_, 0);
v_asyncMode_1085_ = lean_ctor_get(v_toEnvExtension_1084_, 2);
lean_inc(v_declName_1070_);
v___x_1086_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1081_, v___x_1083_, v_env_1069_, v_asyncMode_1085_, v_declName_1070_, v___x_1076_);
v___x_1087_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_1086_, v_declName_1070_);
lean_dec(v_declName_1070_);
lean_dec(v___x_1086_);
if (lean_obj_tag(v___x_1087_) == 0)
{
uint8_t v___x_1088_; 
v___x_1088_ = 1;
return v___x_1088_;
}
else
{
lean_object* v_val_1089_; uint8_t v___x_1090_; 
v_val_1089_ = lean_ctor_get(v___x_1087_, 0);
lean_inc(v_val_1089_);
lean_dec_ref_known(v___x_1087_, 1);
v___x_1090_ = lean_unbox(v_val_1089_);
lean_dec(v_val_1089_);
return v___x_1090_;
}
}
else
{
lean_object* v_val_1091_; lean_object* v___x_1092_; uint8_t v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; 
v_val_1091_ = lean_ctor_get(v___x_1082_, 0);
lean_inc(v_val_1091_);
lean_dec_ref_known(v___x_1082_, 1);
v___x_1092_ = l_Lean_reducibilityCoreExt;
v___x_1093_ = 0;
v___x_1094_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_1081_, v___x_1092_, v_env_1069_, v_val_1091_, v___x_1093_);
lean_dec(v_val_1091_);
lean_dec_ref(v_env_1069_);
v___x_1095_ = l_Lean_findSortedByName_x3f___redArg(v___x_1094_, v_declName_1070_);
lean_dec(v_declName_1070_);
lean_dec_ref(v___x_1094_);
if (lean_obj_tag(v___x_1095_) == 0)
{
uint8_t v___x_1096_; 
v___x_1096_ = 1;
return v___x_1096_;
}
else
{
lean_object* v_val_1097_; lean_object* v_snd_1098_; uint8_t v___x_1099_; 
v_val_1097_ = lean_ctor_get(v___x_1095_, 0);
lean_inc(v_val_1097_);
lean_dec_ref_known(v___x_1095_, 1);
v_snd_1098_ = lean_ctor_get(v_val_1097_, 1);
lean_inc(v_snd_1098_);
lean_dec(v_val_1097_);
v___x_1099_ = lean_unbox(v_snd_1098_);
lean_dec(v_snd_1098_);
return v___x_1099_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatusCore___boxed(lean_object* v_env_1100_, lean_object* v_declName_1101_){
_start:
{
uint8_t v_res_1102_; lean_object* v_r_1103_; 
v_res_1102_ = l_Lean_getReducibilityStatusCore(v_env_1100_, v_declName_1101_);
v_r_1103_ = lean_box(v_res_1102_);
return v_r_1103_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0(lean_object* v_00_u03b2_1104_, lean_object* v_x_1105_, lean_object* v_x_1106_){
_start:
{
lean_object* v___x_1107_; 
v___x_1107_ = l_Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0___redArg(v_x_1105_, v_x_1106_);
return v___x_1107_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0___boxed(lean_object* v_00_u03b2_1108_, lean_object* v_x_1109_, lean_object* v_x_1110_){
_start:
{
lean_object* v_res_1111_; 
v_res_1111_ = l_Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0(v_00_u03b2_1108_, v_x_1109_, v_x_1110_);
lean_dec(v_x_1110_);
lean_dec_ref(v_x_1109_);
return v_res_1111_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__0(lean_object* v_00_u03b2_1112_, lean_object* v_x_1113_, lean_object* v_x_1114_){
_start:
{
lean_object* v___x_1115_; 
v___x_1115_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__0___redArg(v_x_1113_, v_x_1114_);
return v___x_1115_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1116_, lean_object* v_x_1117_, lean_object* v_x_1118_){
_start:
{
lean_object* v_res_1119_; 
v_res_1119_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__0(v_00_u03b2_1116_, v_x_1117_, v_x_1118_);
lean_dec(v_x_1118_);
lean_dec_ref(v_x_1117_);
return v_res_1119_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__1(lean_object* v_00_u03b2_1120_, lean_object* v_m_1121_, lean_object* v_a_1122_){
_start:
{
lean_object* v___x_1123_; 
v___x_1123_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__1___redArg(v_m_1121_, v_a_1122_);
return v___x_1123_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1124_, lean_object* v_m_1125_, lean_object* v_a_1126_){
_start:
{
lean_object* v_res_1127_; 
v_res_1127_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__1(v_00_u03b2_1124_, v_m_1125_, v_a_1126_);
lean_dec(v_a_1126_);
lean_dec_ref(v_m_1125_);
return v_res_1127_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1128_, lean_object* v_x_1129_, size_t v_x_1130_, lean_object* v_x_1131_){
_start:
{
lean_object* v___x_1132_; 
v___x_1132_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__0_spec__1___redArg(v_x_1129_, v_x_1130_, v_x_1131_);
return v___x_1132_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1133_, lean_object* v_x_1134_, lean_object* v_x_1135_, lean_object* v_x_1136_){
_start:
{
size_t v_x_569__boxed_1137_; lean_object* v_res_1138_; 
v_x_569__boxed_1137_ = lean_unbox_usize(v_x_1135_);
lean_dec(v_x_1135_);
v_res_1138_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__0_spec__1(v_00_u03b2_1133_, v_x_1134_, v_x_569__boxed_1137_, v_x_1136_);
lean_dec(v_x_1136_);
lean_dec_ref(v_x_1134_);
return v_res_1138_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_1139_, lean_object* v_a_1140_, lean_object* v_x_1141_){
_start:
{
lean_object* v___x_1142_; 
v___x_1142_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__1_spec__3___redArg(v_a_1140_, v_x_1141_);
return v___x_1142_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_1143_, lean_object* v_a_1144_, lean_object* v_x_1145_){
_start:
{
lean_object* v_res_1146_; 
v_res_1146_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__1_spec__3(v_00_u03b2_1143_, v_a_1144_, v_x_1145_);
lean_dec(v_x_1145_);
lean_dec(v_a_1144_);
return v_res_1146_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_1147_, lean_object* v_keys_1148_, lean_object* v_vals_1149_, lean_object* v_heq_1150_, lean_object* v_i_1151_, lean_object* v_k_1152_){
_start:
{
lean_object* v___x_1153_; 
v___x_1153_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__0_spec__1_spec__2___redArg(v_keys_1148_, v_vals_1149_, v_i_1151_, v_k_1152_);
return v___x_1153_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1154_, lean_object* v_keys_1155_, lean_object* v_vals_1156_, lean_object* v_heq_1157_, lean_object* v_i_1158_, lean_object* v_k_1159_){
_start:
{
lean_object* v_res_1160_; 
v_res_1160_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__0_spec__1_spec__2(v_00_u03b2_1154_, v_keys_1155_, v_vals_1156_, v_heq_1157_, v_i_1158_, v_k_1159_);
lean_dec(v_k_1159_);
lean_dec_ref(v_vals_1156_);
lean_dec_ref(v_keys_1155_);
return v_res_1160_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore___lam__0(lean_object* v_addEntryFn_1161_, lean_object* v___x_1162_, lean_object* v_s_1163_){
_start:
{
lean_object* v_importedEntries_1164_; lean_object* v_state_1165_; lean_object* v___x_1167_; uint8_t v_isShared_1168_; uint8_t v_isSharedCheck_1173_; 
v_importedEntries_1164_ = lean_ctor_get(v_s_1163_, 0);
v_state_1165_ = lean_ctor_get(v_s_1163_, 1);
v_isSharedCheck_1173_ = !lean_is_exclusive(v_s_1163_);
if (v_isSharedCheck_1173_ == 0)
{
v___x_1167_ = v_s_1163_;
v_isShared_1168_ = v_isSharedCheck_1173_;
goto v_resetjp_1166_;
}
else
{
lean_inc(v_state_1165_);
lean_inc(v_importedEntries_1164_);
lean_dec(v_s_1163_);
v___x_1167_ = lean_box(0);
v_isShared_1168_ = v_isSharedCheck_1173_;
goto v_resetjp_1166_;
}
v_resetjp_1166_:
{
lean_object* v_state_1169_; lean_object* v___x_1171_; 
v_state_1169_ = lean_apply_2(v_addEntryFn_1161_, v_state_1165_, v___x_1162_);
if (v_isShared_1168_ == 0)
{
lean_ctor_set(v___x_1167_, 1, v_state_1169_);
v___x_1171_ = v___x_1167_;
goto v_reusejp_1170_;
}
else
{
lean_object* v_reuseFailAlloc_1172_; 
v_reuseFailAlloc_1172_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1172_, 0, v_importedEntries_1164_);
lean_ctor_set(v_reuseFailAlloc_1172_, 1, v_state_1169_);
v___x_1171_ = v_reuseFailAlloc_1172_;
goto v_reusejp_1170_;
}
v_reusejp_1170_:
{
return v___x_1171_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(lean_object* v_env_1174_, lean_object* v_declName_1175_, uint8_t v_status_1176_, uint8_t v_attrKind_1177_, lean_object* v_currNamespace_1178_){
_start:
{
if (v_attrKind_1177_ == 0)
{
lean_object* v___x_1179_; 
lean_dec(v_currNamespace_1178_);
v___x_1179_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1174_, v_declName_1175_);
if (lean_obj_tag(v___x_1179_) == 0)
{
lean_object* v___x_1180_; lean_object* v_toEnvExtension_1181_; lean_object* v_addEntryFn_1182_; lean_object* v_asyncMode_1183_; uint8_t v_logWrites_1184_; uint8_t v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___f_1188_; 
v___x_1180_ = l_Lean_reducibilityCoreExt;
v_toEnvExtension_1181_ = lean_ctor_get(v___x_1180_, 0);
v_addEntryFn_1182_ = lean_ctor_get(v___x_1180_, 3);
v_asyncMode_1183_ = lean_ctor_get(v_toEnvExtension_1181_, 2);
v_logWrites_1184_ = lean_ctor_get_uint8(v_toEnvExtension_1181_, sizeof(void*)*6);
v___x_1185_ = 1;
v___x_1186_ = lean_box(v_status_1176_);
lean_inc(v_declName_1175_);
v___x_1187_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1187_, 0, v_declName_1175_);
lean_ctor_set(v___x_1187_, 1, v___x_1186_);
lean_inc(v_addEntryFn_1182_);
v___f_1188_ = lean_alloc_closure((void*)(l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore___lam__0), 3, 2);
lean_closure_set(v___f_1188_, 0, v_addEntryFn_1182_);
lean_closure_set(v___f_1188_, 1, v___x_1187_);
if (v_logWrites_1184_ == 0)
{
lean_object* v___x_1189_; 
lean_inc_ref(v_toEnvExtension_1181_);
v___x_1189_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1181_, v_env_1174_, v___f_1188_, v_asyncMode_1183_, v_declName_1175_, v___x_1185_);
return v___x_1189_;
}
else
{
lean_object* v___x_1190_; lean_object* v___x_1191_; 
lean_inc(v_declName_1175_);
v___x_1190_ = l_Lean_Environment_logDeclChange(v_env_1174_, v_declName_1175_);
lean_inc_ref(v_toEnvExtension_1181_);
v___x_1191_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1181_, v___x_1190_, v___f_1188_, v_asyncMode_1183_, v_declName_1175_, v___x_1185_);
return v___x_1191_;
}
}
else
{
lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; 
lean_dec_ref_known(v___x_1179_, 1);
v___x_1192_ = l_Lean_reducibilityExtraExt;
v___x_1193_ = lean_box(v_status_1176_);
v___x_1194_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1194_, 0, v_declName_1175_);
lean_ctor_set(v___x_1194_, 1, v___x_1193_);
v___x_1195_ = l_Lean_ScopedEnvExtension_addEntry___redArg(v___x_1192_, v_env_1174_, v___x_1194_);
return v___x_1195_;
}
}
else
{
lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; 
v___x_1196_ = l_Lean_reducibilityExtraExt;
v___x_1197_ = lean_box(v_status_1176_);
v___x_1198_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1198_, 0, v_declName_1175_);
lean_ctor_set(v___x_1198_, 1, v___x_1197_);
v___x_1199_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_env_1174_, v___x_1196_, v___x_1198_, v_attrKind_1177_, v_currNamespace_1178_);
return v___x_1199_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore___boxed(lean_object* v_env_1200_, lean_object* v_declName_1201_, lean_object* v_status_1202_, lean_object* v_attrKind_1203_, lean_object* v_currNamespace_1204_){
_start:
{
uint8_t v_status_boxed_1205_; uint8_t v_attrKind_boxed_1206_; lean_object* v_res_1207_; 
v_status_boxed_1205_ = lean_unbox(v_status_1202_);
v_attrKind_boxed_1206_ = lean_unbox(v_attrKind_1203_);
v_res_1207_ = l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(v_env_1200_, v_declName_1201_, v_status_boxed_1205_, v_attrKind_boxed_1206_, v_currNamespace_1204_);
return v_res_1207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4__spec__0(lean_object* v_name_1208_, lean_object* v_decl_1209_, lean_object* v_ref_1210_){
_start:
{
lean_object* v_defValue_1212_; lean_object* v_descr_1213_; lean_object* v_deprecation_x3f_1214_; lean_object* v___x_1215_; uint8_t v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; 
v_defValue_1212_ = lean_ctor_get(v_decl_1209_, 0);
v_descr_1213_ = lean_ctor_get(v_decl_1209_, 1);
v_deprecation_x3f_1214_ = lean_ctor_get(v_decl_1209_, 2);
v___x_1215_ = lean_alloc_ctor(1, 0, 1);
v___x_1216_ = lean_unbox(v_defValue_1212_);
lean_ctor_set_uint8(v___x_1215_, 0, v___x_1216_);
lean_inc(v_deprecation_x3f_1214_);
lean_inc_ref(v_descr_1213_);
lean_inc_n(v_name_1208_, 2);
v___x_1217_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1217_, 0, v_name_1208_);
lean_ctor_set(v___x_1217_, 1, v_ref_1210_);
lean_ctor_set(v___x_1217_, 2, v___x_1215_);
lean_ctor_set(v___x_1217_, 3, v_descr_1213_);
lean_ctor_set(v___x_1217_, 4, v_deprecation_x3f_1214_);
v___x_1218_ = lean_register_option(v_name_1208_, v___x_1217_);
if (lean_obj_tag(v___x_1218_) == 0)
{
lean_object* v___x_1220_; uint8_t v_isShared_1221_; uint8_t v_isSharedCheck_1226_; 
v_isSharedCheck_1226_ = !lean_is_exclusive(v___x_1218_);
if (v_isSharedCheck_1226_ == 0)
{
lean_object* v_unused_1227_; 
v_unused_1227_ = lean_ctor_get(v___x_1218_, 0);
lean_dec(v_unused_1227_);
v___x_1220_ = v___x_1218_;
v_isShared_1221_ = v_isSharedCheck_1226_;
goto v_resetjp_1219_;
}
else
{
lean_dec(v___x_1218_);
v___x_1220_ = lean_box(0);
v_isShared_1221_ = v_isSharedCheck_1226_;
goto v_resetjp_1219_;
}
v_resetjp_1219_:
{
lean_object* v___x_1222_; lean_object* v___x_1224_; 
lean_inc(v_defValue_1212_);
v___x_1222_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1222_, 0, v_name_1208_);
lean_ctor_set(v___x_1222_, 1, v_defValue_1212_);
if (v_isShared_1221_ == 0)
{
lean_ctor_set(v___x_1220_, 0, v___x_1222_);
v___x_1224_ = v___x_1220_;
goto v_reusejp_1223_;
}
else
{
lean_object* v_reuseFailAlloc_1225_; 
v_reuseFailAlloc_1225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1225_, 0, v___x_1222_);
v___x_1224_ = v_reuseFailAlloc_1225_;
goto v_reusejp_1223_;
}
v_reusejp_1223_:
{
return v___x_1224_;
}
}
}
else
{
lean_object* v_a_1228_; lean_object* v___x_1230_; uint8_t v_isShared_1231_; uint8_t v_isSharedCheck_1235_; 
lean_dec(v_name_1208_);
v_a_1228_ = lean_ctor_get(v___x_1218_, 0);
v_isSharedCheck_1235_ = !lean_is_exclusive(v___x_1218_);
if (v_isSharedCheck_1235_ == 0)
{
v___x_1230_ = v___x_1218_;
v_isShared_1231_ = v_isSharedCheck_1235_;
goto v_resetjp_1229_;
}
else
{
lean_inc(v_a_1228_);
lean_dec(v___x_1218_);
v___x_1230_ = lean_box(0);
v_isShared_1231_ = v_isSharedCheck_1235_;
goto v_resetjp_1229_;
}
v_resetjp_1229_:
{
lean_object* v___x_1233_; 
if (v_isShared_1231_ == 0)
{
v___x_1233_ = v___x_1230_;
goto v_reusejp_1232_;
}
else
{
lean_object* v_reuseFailAlloc_1234_; 
v_reuseFailAlloc_1234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1234_, 0, v_a_1228_);
v___x_1233_ = v_reuseFailAlloc_1234_;
goto v_reusejp_1232_;
}
v_reusejp_1232_:
{
return v___x_1233_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_1236_, lean_object* v_decl_1237_, lean_object* v_ref_1238_, lean_object* v_a_1239_){
_start:
{
lean_object* v_res_1240_; 
v_res_1240_ = l_Lean_Option_register___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4__spec__0(v_name_1236_, v_decl_1237_, v_ref_1238_);
lean_dec_ref(v_decl_1237_);
return v_res_1240_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; 
v___x_1255_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4_));
v___x_1256_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4_));
v___x_1257_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4_));
v___x_1258_ = l_Lean_Option_register___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4__spec__0(v___x_1255_, v___x_1256_, v___x_1257_);
return v___x_1258_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4____boxed(lean_object* v_a_1259_){
_start:
{
lean_object* v_res_1260_; 
v_res_1260_ = l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4_();
return v_res_1260_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__0(lean_object* v_opts_1261_, lean_object* v_opt_1262_){
_start:
{
lean_object* v_name_1263_; lean_object* v_defValue_1264_; lean_object* v_map_1265_; lean_object* v___x_1266_; 
v_name_1263_ = lean_ctor_get(v_opt_1262_, 0);
v_defValue_1264_ = lean_ctor_get(v_opt_1262_, 1);
v_map_1265_ = lean_ctor_get(v_opts_1261_, 0);
v___x_1266_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1265_, v_name_1263_);
if (lean_obj_tag(v___x_1266_) == 0)
{
uint8_t v___x_1267_; 
v___x_1267_ = lean_unbox(v_defValue_1264_);
return v___x_1267_;
}
else
{
lean_object* v_val_1268_; 
v_val_1268_ = lean_ctor_get(v___x_1266_, 0);
lean_inc(v_val_1268_);
lean_dec_ref_known(v___x_1266_, 1);
if (lean_obj_tag(v_val_1268_) == 1)
{
uint8_t v_v_1269_; 
v_v_1269_ = lean_ctor_get_uint8(v_val_1268_, 0);
lean_dec_ref_known(v_val_1268_, 0);
return v_v_1269_;
}
else
{
uint8_t v___x_1270_; 
lean_dec(v_val_1268_);
v___x_1270_ = lean_unbox(v_defValue_1264_);
return v___x_1270_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__0___boxed(lean_object* v_opts_1271_, lean_object* v_opt_1272_){
_start:
{
uint8_t v_res_1273_; lean_object* v_r_1274_; 
v_res_1273_ = l_Lean_Option_get___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__0(v_opts_1271_, v_opt_1272_);
lean_dec_ref(v_opt_1272_);
lean_dec_ref(v_opts_1271_);
v_r_1274_ = lean_box(v_res_1273_);
return v_r_1274_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1275_; lean_object* v___x_1276_; 
v___x_1275_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__9_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2_, &l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__9_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2__once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__9_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2_);
v___x_1276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1276_, 0, v___x_1275_);
return v___x_1276_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__1(void){
_start:
{
lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; 
v___x_1277_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__0);
v___x_1278_ = lean_unsigned_to_nat(0u);
v___x_1279_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_1279_, 0, v___x_1278_);
lean_ctor_set(v___x_1279_, 1, v___x_1278_);
lean_ctor_set(v___x_1279_, 2, v___x_1278_);
lean_ctor_set(v___x_1279_, 3, v___x_1278_);
lean_ctor_set(v___x_1279_, 4, v___x_1277_);
lean_ctor_set(v___x_1279_, 5, v___x_1277_);
lean_ctor_set(v___x_1279_, 6, v___x_1277_);
lean_ctor_set(v___x_1279_, 7, v___x_1277_);
lean_ctor_set(v___x_1279_, 8, v___x_1277_);
lean_ctor_set(v___x_1279_, 9, v___x_1277_);
lean_ctor_set(v___x_1279_, 10, v___x_1277_);
return v___x_1279_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__2(void){
_start:
{
lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; 
v___x_1280_ = lean_unsigned_to_nat(32u);
v___x_1281_ = lean_mk_empty_array_with_capacity(v___x_1280_);
v___x_1282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1282_, 0, v___x_1281_);
return v___x_1282_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__3(void){
_start:
{
size_t v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; 
v___x_1283_ = ((size_t)5ULL);
v___x_1284_ = lean_unsigned_to_nat(0u);
v___x_1285_ = lean_unsigned_to_nat(32u);
v___x_1286_ = lean_mk_empty_array_with_capacity(v___x_1285_);
v___x_1287_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__2);
v___x_1288_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1288_, 0, v___x_1287_);
lean_ctor_set(v___x_1288_, 1, v___x_1286_);
lean_ctor_set(v___x_1288_, 2, v___x_1284_);
lean_ctor_set(v___x_1288_, 3, v___x_1284_);
lean_ctor_set_usize(v___x_1288_, 4, v___x_1283_);
return v___x_1288_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__4(void){
_start:
{
lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; 
v___x_1289_ = lean_box(1);
v___x_1290_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__3);
v___x_1291_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__0);
v___x_1292_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1292_, 0, v___x_1291_);
lean_ctor_set(v___x_1292_, 1, v___x_1290_);
lean_ctor_set(v___x_1292_, 2, v___x_1289_);
return v___x_1292_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1(lean_object* v_msgData_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_){
_start:
{
lean_object* v___x_1297_; lean_object* v_toCold_1298_; lean_object* v_env_1299_; lean_object* v_options_1300_; uint8_t v___x_1301_; lean_object* v_env_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; 
v___x_1297_ = lean_st_ref_get(v___y_1295_);
v_toCold_1298_ = lean_ctor_get(v___y_1294_, 0);
v_env_1299_ = lean_ctor_get(v___x_1297_, 0);
lean_inc_ref(v_env_1299_);
lean_dec(v___x_1297_);
v_options_1300_ = lean_ctor_get(v_toCold_1298_, 2);
v___x_1301_ = 0;
v_env_1302_ = l_Lean_Environment_setRecordingDeps(v_env_1299_, v___x_1301_);
v___x_1303_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__1);
v___x_1304_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__4);
lean_inc_ref(v_options_1300_);
v___x_1305_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1305_, 0, v_env_1302_);
lean_ctor_set(v___x_1305_, 1, v___x_1303_);
lean_ctor_set(v___x_1305_, 2, v___x_1304_);
lean_ctor_set(v___x_1305_, 3, v_options_1300_);
v___x_1306_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1306_, 0, v___x_1305_);
lean_ctor_set(v___x_1306_, 1, v_msgData_1293_);
v___x_1307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1307_, 0, v___x_1306_);
return v___x_1307_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___boxed(lean_object* v_msgData_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_){
_start:
{
lean_object* v_res_1312_; 
v_res_1312_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1(v_msgData_1308_, v___y_1309_, v___y_1310_);
lean_dec(v___y_1310_);
lean_dec_ref(v___y_1309_);
return v_res_1312_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1___redArg(lean_object* v_msg_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_){
_start:
{
lean_object* v_ref_1317_; lean_object* v___x_1318_; lean_object* v_a_1319_; lean_object* v___x_1321_; uint8_t v_isShared_1322_; uint8_t v_isSharedCheck_1327_; 
v_ref_1317_ = lean_ctor_get(v___y_1314_, 2);
v___x_1318_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1(v_msg_1313_, v___y_1314_, v___y_1315_);
v_a_1319_ = lean_ctor_get(v___x_1318_, 0);
v_isSharedCheck_1327_ = !lean_is_exclusive(v___x_1318_);
if (v_isSharedCheck_1327_ == 0)
{
v___x_1321_ = v___x_1318_;
v_isShared_1322_ = v_isSharedCheck_1327_;
goto v_resetjp_1320_;
}
else
{
lean_inc(v_a_1319_);
lean_dec(v___x_1318_);
v___x_1321_ = lean_box(0);
v_isShared_1322_ = v_isSharedCheck_1327_;
goto v_resetjp_1320_;
}
v_resetjp_1320_:
{
lean_object* v___x_1323_; lean_object* v___x_1325_; 
lean_inc(v_ref_1317_);
v___x_1323_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1323_, 0, v_ref_1317_);
lean_ctor_set(v___x_1323_, 1, v_a_1319_);
if (v_isShared_1322_ == 0)
{
lean_ctor_set_tag(v___x_1321_, 1);
lean_ctor_set(v___x_1321_, 0, v___x_1323_);
v___x_1325_ = v___x_1321_;
goto v_reusejp_1324_;
}
else
{
lean_object* v_reuseFailAlloc_1326_; 
v_reuseFailAlloc_1326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1326_, 0, v___x_1323_);
v___x_1325_ = v_reuseFailAlloc_1326_;
goto v_reusejp_1324_;
}
v_reusejp_1324_:
{
return v___x_1325_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1___redArg___boxed(lean_object* v_msg_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_){
_start:
{
lean_object* v_res_1332_; 
v_res_1332_ = l_Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1___redArg(v_msg_1328_, v___y_1329_, v___y_1330_);
lean_dec(v___y_1330_);
lean_dec_ref(v___y_1329_);
return v_res_1332_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__9___redArg(lean_object* v_ref_1333_, lean_object* v_msg_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_){
_start:
{
lean_object* v_toCold_1338_; lean_object* v_currRecDepth_1339_; lean_object* v_ref_1340_; uint16_t v_optionFlags_1341_; uint8_t v_suppressElabErrors_1342_; uint8_t v_checkDeprecated_1343_; uint8_t v_isRecordingDeps_1344_; lean_object* v_ref_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; 
v_toCold_1338_ = lean_ctor_get(v___y_1335_, 0);
v_currRecDepth_1339_ = lean_ctor_get(v___y_1335_, 1);
v_ref_1340_ = lean_ctor_get(v___y_1335_, 2);
v_optionFlags_1341_ = lean_ctor_get_uint16(v___y_1335_, sizeof(void*)*3);
v_suppressElabErrors_1342_ = lean_ctor_get_uint8(v___y_1335_, sizeof(void*)*3 + 2);
v_checkDeprecated_1343_ = lean_ctor_get_uint8(v___y_1335_, sizeof(void*)*3 + 3);
v_isRecordingDeps_1344_ = lean_ctor_get_uint8(v___y_1335_, sizeof(void*)*3 + 4);
v_ref_1345_ = l_Lean_replaceRef(v_ref_1333_, v_ref_1340_);
lean_inc(v_currRecDepth_1339_);
lean_inc_ref(v_toCold_1338_);
v___x_1346_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_1346_, 0, v_toCold_1338_);
lean_ctor_set(v___x_1346_, 1, v_currRecDepth_1339_);
lean_ctor_set(v___x_1346_, 2, v_ref_1345_);
lean_ctor_set_uint16(v___x_1346_, sizeof(void*)*3, v_optionFlags_1341_);
lean_ctor_set_uint8(v___x_1346_, sizeof(void*)*3 + 2, v_suppressElabErrors_1342_);
lean_ctor_set_uint8(v___x_1346_, sizeof(void*)*3 + 3, v_checkDeprecated_1343_);
lean_ctor_set_uint8(v___x_1346_, sizeof(void*)*3 + 4, v_isRecordingDeps_1344_);
v___x_1347_ = l_Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1___redArg(v_msg_1334_, v___x_1346_, v___y_1336_);
lean_dec_ref_known(v___x_1346_, 3);
return v___x_1347_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__9___redArg___boxed(lean_object* v_ref_1348_, lean_object* v_msg_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_){
_start:
{
lean_object* v_res_1353_; 
v_res_1353_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__9___redArg(v_ref_1348_, v_msg_1349_, v___y_1350_, v___y_1351_);
lean_dec(v___y_1351_);
lean_dec_ref(v___y_1350_);
lean_dec(v_ref_1348_);
return v_res_1353_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__1(void){
_start:
{
lean_object* v___x_1355_; lean_object* v___x_1356_; 
v___x_1355_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__0));
v___x_1356_ = l_Lean_stringToMessageData(v___x_1355_);
return v___x_1356_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__3(void){
_start:
{
lean_object* v___x_1358_; lean_object* v___x_1359_; 
v___x_1358_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__2));
v___x_1359_ = l_Lean_stringToMessageData(v___x_1358_);
return v___x_1359_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__5(void){
_start:
{
lean_object* v___x_1361_; lean_object* v___x_1362_; 
v___x_1361_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__4));
v___x_1362_ = l_Lean_stringToMessageData(v___x_1361_);
return v___x_1362_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__7(void){
_start:
{
lean_object* v___x_1364_; lean_object* v___x_1365_; 
v___x_1364_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__6));
v___x_1365_ = l_Lean_stringToMessageData(v___x_1364_);
return v___x_1365_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__9(void){
_start:
{
lean_object* v___x_1367_; lean_object* v___x_1368_; 
v___x_1367_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__8));
v___x_1368_ = l_Lean_stringToMessageData(v___x_1367_);
return v___x_1368_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__11(void){
_start:
{
lean_object* v___x_1370_; lean_object* v___x_1371_; 
v___x_1370_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__10));
v___x_1371_ = l_Lean_stringToMessageData(v___x_1370_);
return v___x_1371_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__13(void){
_start:
{
lean_object* v___x_1373_; lean_object* v___x_1374_; 
v___x_1373_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__12));
v___x_1374_ = l_Lean_stringToMessageData(v___x_1373_);
return v___x_1374_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg(lean_object* v_msg_1375_, lean_object* v_declHint_1376_, lean_object* v___y_1377_){
_start:
{
lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v_env_1381_; uint8_t v___x_1382_; 
v___x_1379_ = lean_box(0);
v___x_1380_ = lean_st_ref_get(v___y_1377_);
v_env_1381_ = lean_ctor_get(v___x_1380_, 0);
lean_inc_ref(v_env_1381_);
lean_dec(v___x_1380_);
v___x_1382_ = l_Lean_Name_isAnonymous(v_declHint_1376_);
if (v___x_1382_ == 0)
{
uint8_t v_isExporting_1383_; 
v_isExporting_1383_ = lean_ctor_get_uint8(v_env_1381_, sizeof(void*)*13);
if (v_isExporting_1383_ == 0)
{
lean_object* v___x_1384_; 
lean_dec_ref(v_env_1381_);
lean_dec(v_declHint_1376_);
v___x_1384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1384_, 0, v_msg_1375_);
return v___x_1384_;
}
else
{
lean_object* v___x_1385_; uint8_t v___x_1386_; 
lean_inc_ref(v_env_1381_);
v___x_1385_ = l_Lean_Environment_setExporting(v_env_1381_, v___x_1382_);
lean_inc(v_declHint_1376_);
lean_inc_ref(v___x_1385_);
v___x_1386_ = l_Lean_Environment_contains(v___x_1385_, v_declHint_1376_, v_isExporting_1383_);
if (v___x_1386_ == 0)
{
lean_object* v___x_1387_; 
lean_dec_ref(v___x_1385_);
lean_dec_ref(v_env_1381_);
lean_dec(v_declHint_1376_);
v___x_1387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1387_, 0, v_msg_1375_);
return v___x_1387_;
}
else
{
lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v_c_1393_; lean_object* v___x_1394_; 
v___x_1388_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__1);
v___x_1389_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__4);
v___x_1390_ = l_Lean_Options_empty;
lean_inc_ref(v___x_1385_);
v___x_1391_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1391_, 0, v___x_1385_);
lean_ctor_set(v___x_1391_, 1, v___x_1388_);
lean_ctor_set(v___x_1391_, 2, v___x_1389_);
lean_ctor_set(v___x_1391_, 3, v___x_1390_);
lean_inc(v_declHint_1376_);
v___x_1392_ = l_Lean_MessageData_ofConstName(v_declHint_1376_, v___x_1382_);
v_c_1393_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1393_, 0, v___x_1391_);
lean_ctor_set(v_c_1393_, 1, v___x_1392_);
v___x_1394_ = l_Lean_Environment_getModuleIdxFor_x3f(v___x_1385_, v_declHint_1376_);
lean_dec_ref(v___x_1385_);
if (lean_obj_tag(v___x_1394_) == 0)
{
lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; 
lean_dec_ref(v_env_1381_);
lean_dec(v_declHint_1376_);
v___x_1395_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__1);
v___x_1396_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1396_, 0, v___x_1395_);
lean_ctor_set(v___x_1396_, 1, v_c_1393_);
v___x_1397_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__3);
v___x_1398_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1398_, 0, v___x_1396_);
lean_ctor_set(v___x_1398_, 1, v___x_1397_);
v___x_1399_ = l_Lean_MessageData_note(v___x_1398_);
v___x_1400_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1400_, 0, v_msg_1375_);
lean_ctor_set(v___x_1400_, 1, v___x_1399_);
v___x_1401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1401_, 0, v___x_1400_);
return v___x_1401_;
}
else
{
lean_object* v_val_1402_; lean_object* v___x_1404_; uint8_t v_isShared_1405_; uint8_t v_isSharedCheck_1436_; 
v_val_1402_ = lean_ctor_get(v___x_1394_, 0);
v_isSharedCheck_1436_ = !lean_is_exclusive(v___x_1394_);
if (v_isSharedCheck_1436_ == 0)
{
v___x_1404_ = v___x_1394_;
v_isShared_1405_ = v_isSharedCheck_1436_;
goto v_resetjp_1403_;
}
else
{
lean_inc(v_val_1402_);
lean_dec(v___x_1394_);
v___x_1404_ = lean_box(0);
v_isShared_1405_ = v_isSharedCheck_1436_;
goto v_resetjp_1403_;
}
v_resetjp_1403_:
{
lean_object* v___x_1406_; lean_object* v_moduleNames_1407_; lean_object* v_mod_1408_; uint8_t v___x_1409_; 
v___x_1406_ = l_Lean_Environment_header(v_env_1381_);
lean_dec_ref(v_env_1381_);
v_moduleNames_1407_ = lean_ctor_get(v___x_1406_, 4);
lean_inc_ref(v_moduleNames_1407_);
lean_dec_ref(v___x_1406_);
v_mod_1408_ = lean_array_get(v___x_1379_, v_moduleNames_1407_, v_val_1402_);
lean_dec(v_val_1402_);
lean_dec_ref(v_moduleNames_1407_);
v___x_1409_ = l_Lean_isPrivateName(v_declHint_1376_);
lean_dec(v_declHint_1376_);
if (v___x_1409_ == 0)
{
lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1421_; 
v___x_1410_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__5);
v___x_1411_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1411_, 0, v___x_1410_);
lean_ctor_set(v___x_1411_, 1, v_c_1393_);
v___x_1412_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__7);
v___x_1413_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1413_, 0, v___x_1411_);
lean_ctor_set(v___x_1413_, 1, v___x_1412_);
v___x_1414_ = l_Lean_MessageData_ofName(v_mod_1408_);
v___x_1415_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1415_, 0, v___x_1413_);
lean_ctor_set(v___x_1415_, 1, v___x_1414_);
v___x_1416_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__9);
v___x_1417_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1417_, 0, v___x_1415_);
lean_ctor_set(v___x_1417_, 1, v___x_1416_);
v___x_1418_ = l_Lean_MessageData_note(v___x_1417_);
v___x_1419_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1419_, 0, v_msg_1375_);
lean_ctor_set(v___x_1419_, 1, v___x_1418_);
if (v_isShared_1405_ == 0)
{
lean_ctor_set_tag(v___x_1404_, 0);
lean_ctor_set(v___x_1404_, 0, v___x_1419_);
v___x_1421_ = v___x_1404_;
goto v_reusejp_1420_;
}
else
{
lean_object* v_reuseFailAlloc_1422_; 
v_reuseFailAlloc_1422_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1422_, 0, v___x_1419_);
v___x_1421_ = v_reuseFailAlloc_1422_;
goto v_reusejp_1420_;
}
v_reusejp_1420_:
{
return v___x_1421_;
}
}
else
{
lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1434_; 
v___x_1423_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__1);
v___x_1424_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1424_, 0, v___x_1423_);
lean_ctor_set(v___x_1424_, 1, v_c_1393_);
v___x_1425_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__11);
v___x_1426_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1426_, 0, v___x_1424_);
lean_ctor_set(v___x_1426_, 1, v___x_1425_);
v___x_1427_ = l_Lean_MessageData_ofName(v_mod_1408_);
v___x_1428_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1428_, 0, v___x_1426_);
lean_ctor_set(v___x_1428_, 1, v___x_1427_);
v___x_1429_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__13);
v___x_1430_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1430_, 0, v___x_1428_);
lean_ctor_set(v___x_1430_, 1, v___x_1429_);
v___x_1431_ = l_Lean_MessageData_note(v___x_1430_);
v___x_1432_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1432_, 0, v_msg_1375_);
lean_ctor_set(v___x_1432_, 1, v___x_1431_);
if (v_isShared_1405_ == 0)
{
lean_ctor_set_tag(v___x_1404_, 0);
lean_ctor_set(v___x_1404_, 0, v___x_1432_);
v___x_1434_ = v___x_1404_;
goto v_reusejp_1433_;
}
else
{
lean_object* v_reuseFailAlloc_1435_; 
v_reuseFailAlloc_1435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1435_, 0, v___x_1432_);
v___x_1434_ = v_reuseFailAlloc_1435_;
goto v_reusejp_1433_;
}
v_reusejp_1433_:
{
return v___x_1434_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1437_; 
lean_dec_ref(v_env_1381_);
lean_dec(v_declHint_1376_);
v___x_1437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1437_, 0, v_msg_1375_);
return v___x_1437_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___boxed(lean_object* v_msg_1438_, lean_object* v_declHint_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_){
_start:
{
lean_object* v_res_1442_; 
v_res_1442_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg(v_msg_1438_, v_declHint_1439_, v___y_1440_);
lean_dec(v___y_1440_);
return v_res_1442_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8(lean_object* v_msg_1443_, lean_object* v_declHint_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_){
_start:
{
lean_object* v___x_1448_; lean_object* v_a_1449_; lean_object* v___x_1451_; uint8_t v_isShared_1452_; uint8_t v_isSharedCheck_1458_; 
v___x_1448_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg(v_msg_1443_, v_declHint_1444_, v___y_1446_);
v_a_1449_ = lean_ctor_get(v___x_1448_, 0);
v_isSharedCheck_1458_ = !lean_is_exclusive(v___x_1448_);
if (v_isSharedCheck_1458_ == 0)
{
v___x_1451_ = v___x_1448_;
v_isShared_1452_ = v_isSharedCheck_1458_;
goto v_resetjp_1450_;
}
else
{
lean_inc(v_a_1449_);
lean_dec(v___x_1448_);
v___x_1451_ = lean_box(0);
v_isShared_1452_ = v_isSharedCheck_1458_;
goto v_resetjp_1450_;
}
v_resetjp_1450_:
{
lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1456_; 
v___x_1453_ = l_Lean_unknownIdentifierMessageTag;
v___x_1454_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1454_, 0, v___x_1453_);
lean_ctor_set(v___x_1454_, 1, v_a_1449_);
if (v_isShared_1452_ == 0)
{
lean_ctor_set(v___x_1451_, 0, v___x_1454_);
v___x_1456_ = v___x_1451_;
goto v_reusejp_1455_;
}
else
{
lean_object* v_reuseFailAlloc_1457_; 
v_reuseFailAlloc_1457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1457_, 0, v___x_1454_);
v___x_1456_ = v_reuseFailAlloc_1457_;
goto v_reusejp_1455_;
}
v_reusejp_1455_:
{
return v___x_1456_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8___boxed(lean_object* v_msg_1459_, lean_object* v_declHint_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_){
_start:
{
lean_object* v_res_1464_; 
v_res_1464_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8(v_msg_1459_, v_declHint_1460_, v___y_1461_, v___y_1462_);
lean_dec(v___y_1462_);
lean_dec_ref(v___y_1461_);
return v_res_1464_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7___redArg(lean_object* v_ref_1465_, lean_object* v_msg_1466_, lean_object* v_declHint_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_){
_start:
{
lean_object* v___x_1471_; lean_object* v_a_1472_; lean_object* v___x_1473_; 
v___x_1471_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8(v_msg_1466_, v_declHint_1467_, v___y_1468_, v___y_1469_);
v_a_1472_ = lean_ctor_get(v___x_1471_, 0);
lean_inc(v_a_1472_);
lean_dec_ref(v___x_1471_);
v___x_1473_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__9___redArg(v_ref_1465_, v_a_1472_, v___y_1468_, v___y_1469_);
return v___x_1473_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7___redArg___boxed(lean_object* v_ref_1474_, lean_object* v_msg_1475_, lean_object* v_declHint_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_){
_start:
{
lean_object* v_res_1480_; 
v_res_1480_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7___redArg(v_ref_1474_, v_msg_1475_, v_declHint_1476_, v___y_1477_, v___y_1478_);
lean_dec(v___y_1478_);
lean_dec_ref(v___y_1477_);
lean_dec(v_ref_1474_);
return v_res_1480_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_1482_; lean_object* v___x_1483_; 
v___x_1482_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg___closed__0));
v___x_1483_ = l_Lean_stringToMessageData(v___x_1482_);
return v___x_1483_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_1485_; lean_object* v___x_1486_; 
v___x_1485_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg___closed__2));
v___x_1486_ = l_Lean_stringToMessageData(v___x_1485_);
return v___x_1486_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg(lean_object* v_ref_1487_, lean_object* v_constName_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_){
_start:
{
lean_object* v___x_1492_; uint8_t v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; 
v___x_1492_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg___closed__1);
v___x_1493_ = 0;
lean_inc(v_constName_1488_);
v___x_1494_ = l_Lean_MessageData_ofConstName(v_constName_1488_, v___x_1493_);
v___x_1495_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1495_, 0, v___x_1492_);
lean_ctor_set(v___x_1495_, 1, v___x_1494_);
v___x_1496_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg___closed__3);
v___x_1497_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1497_, 0, v___x_1495_);
lean_ctor_set(v___x_1497_, 1, v___x_1496_);
v___x_1498_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7___redArg(v_ref_1487_, v___x_1497_, v_constName_1488_, v___y_1489_, v___y_1490_);
return v___x_1498_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg___boxed(lean_object* v_ref_1499_, lean_object* v_constName_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_){
_start:
{
lean_object* v_res_1504_; 
v_res_1504_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg(v_ref_1499_, v_constName_1500_, v___y_1501_, v___y_1502_);
lean_dec(v___y_1502_);
lean_dec_ref(v___y_1501_);
lean_dec(v_ref_1499_);
return v_res_1504_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3___redArg(lean_object* v_constName_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_){
_start:
{
lean_object* v_ref_1509_; lean_object* v___x_1510_; 
v_ref_1509_ = lean_ctor_get(v___y_1506_, 2);
v___x_1510_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg(v_ref_1509_, v_constName_1505_, v___y_1506_, v___y_1507_);
return v___x_1510_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3___redArg___boxed(lean_object* v_constName_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_){
_start:
{
lean_object* v_res_1515_; 
v_res_1515_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3___redArg(v_constName_1511_, v___y_1512_, v___y_1513_);
lean_dec(v___y_1513_);
lean_dec_ref(v___y_1512_);
return v_res_1515_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2(lean_object* v_constName_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_){
_start:
{
lean_object* v___x_1520_; lean_object* v_env_1521_; uint8_t v___x_1522_; lean_object* v___x_1523_; 
v___x_1520_ = lean_st_ref_get(v___y_1518_);
v_env_1521_ = lean_ctor_get(v___x_1520_, 0);
lean_inc_ref(v_env_1521_);
lean_dec(v___x_1520_);
v___x_1522_ = 0;
lean_inc(v_constName_1516_);
v___x_1523_ = l_Lean_Environment_find_x3f(v_env_1521_, v_constName_1516_, v___x_1522_);
if (lean_obj_tag(v___x_1523_) == 0)
{
lean_object* v___x_1524_; 
v___x_1524_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3___redArg(v_constName_1516_, v___y_1517_, v___y_1518_);
return v___x_1524_;
}
else
{
lean_object* v_val_1525_; lean_object* v___x_1527_; uint8_t v_isShared_1528_; uint8_t v_isSharedCheck_1532_; 
lean_dec(v_constName_1516_);
v_val_1525_ = lean_ctor_get(v___x_1523_, 0);
v_isSharedCheck_1532_ = !lean_is_exclusive(v___x_1523_);
if (v_isSharedCheck_1532_ == 0)
{
v___x_1527_ = v___x_1523_;
v_isShared_1528_ = v_isSharedCheck_1532_;
goto v_resetjp_1526_;
}
else
{
lean_inc(v_val_1525_);
lean_dec(v___x_1523_);
v___x_1527_ = lean_box(0);
v_isShared_1528_ = v_isSharedCheck_1532_;
goto v_resetjp_1526_;
}
v_resetjp_1526_:
{
lean_object* v___x_1530_; 
if (v_isShared_1528_ == 0)
{
lean_ctor_set_tag(v___x_1527_, 0);
v___x_1530_ = v___x_1527_;
goto v_reusejp_1529_;
}
else
{
lean_object* v_reuseFailAlloc_1531_; 
v_reuseFailAlloc_1531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1531_, 0, v_val_1525_);
v___x_1530_ = v_reuseFailAlloc_1531_;
goto v_reusejp_1529_;
}
v_reusejp_1529_:
{
return v___x_1530_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2___boxed(lean_object* v_constName_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_){
_start:
{
lean_object* v_res_1537_; 
v_res_1537_ = l_Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2(v_constName_1533_, v___y_1534_, v___y_1535_);
lean_dec(v___y_1535_);
lean_dec_ref(v___y_1534_);
return v_res_1537_;
}
}
static lean_object* _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1539_; lean_object* v___x_1540_; 
v___x_1539_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__0));
v___x_1540_ = l_Lean_stringToMessageData(v___x_1539_);
return v___x_1540_;
}
}
static lean_object* _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1542_; lean_object* v___x_1543_; 
v___x_1542_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__2));
v___x_1543_ = l_Lean_stringToMessageData(v___x_1542_);
return v___x_1543_;
}
}
static lean_object* _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__5(void){
_start:
{
lean_object* v___x_1545_; lean_object* v___x_1546_; 
v___x_1545_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__4));
v___x_1546_ = l_Lean_stringToMessageData(v___x_1545_);
return v___x_1546_;
}
}
static lean_object* _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__7(void){
_start:
{
lean_object* v___x_1548_; lean_object* v___x_1549_; 
v___x_1548_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__6));
v___x_1549_ = l_Lean_stringToMessageData(v___x_1548_);
return v___x_1549_;
}
}
static lean_object* _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__9(void){
_start:
{
lean_object* v___x_1551_; lean_object* v___x_1552_; 
v___x_1551_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__8));
v___x_1552_ = l_Lean_stringToMessageData(v___x_1551_);
return v___x_1552_;
}
}
static lean_object* _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__11(void){
_start:
{
lean_object* v___x_1554_; lean_object* v___x_1555_; 
v___x_1554_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__10));
v___x_1555_ = l_Lean_stringToMessageData(v___x_1554_);
return v___x_1555_;
}
}
static lean_object* _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__13(void){
_start:
{
lean_object* v___x_1557_; lean_object* v___x_1558_; 
v___x_1557_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__12));
v___x_1558_ = l_Lean_stringToMessageData(v___x_1557_);
return v___x_1558_;
}
}
static lean_object* _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__15(void){
_start:
{
lean_object* v___x_1560_; lean_object* v___x_1561_; 
v___x_1560_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__14));
v___x_1561_ = l_Lean_stringToMessageData(v___x_1560_);
return v___x_1561_;
}
}
static lean_object* _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__17(void){
_start:
{
lean_object* v___x_1563_; lean_object* v___x_1564_; 
v___x_1563_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__16));
v___x_1564_ = l_Lean_stringToMessageData(v___x_1563_);
return v___x_1564_;
}
}
static lean_object* _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__19(void){
_start:
{
lean_object* v___x_1566_; lean_object* v___x_1567_; 
v___x_1566_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__18));
v___x_1567_ = l_Lean_stringToMessageData(v___x_1566_);
return v___x_1567_;
}
}
static lean_object* _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__21(void){
_start:
{
lean_object* v___x_1569_; lean_object* v___x_1570_; 
v___x_1569_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__20));
v___x_1570_ = l_Lean_stringToMessageData(v___x_1569_);
return v___x_1570_;
}
}
static lean_object* _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__23(void){
_start:
{
lean_object* v___x_1572_; lean_object* v___x_1573_; 
v___x_1572_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__22));
v___x_1573_ = l_Lean_stringToMessageData(v___x_1572_);
return v___x_1573_;
}
}
static lean_object* _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__25(void){
_start:
{
lean_object* v___x_1575_; lean_object* v___x_1576_; 
v___x_1575_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__24));
v___x_1576_ = l_Lean_stringToMessageData(v___x_1575_);
return v___x_1576_;
}
}
static lean_object* _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__27(void){
_start:
{
lean_object* v___x_1578_; lean_object* v___x_1579_; 
v___x_1578_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__26));
v___x_1579_ = l_Lean_stringToMessageData(v___x_1578_);
return v___x_1579_;
}
}
static lean_object* _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__29(void){
_start:
{
lean_object* v___x_1581_; lean_object* v___x_1582_; 
v___x_1581_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__28));
v___x_1582_ = l_Lean_stringToMessageData(v___x_1581_);
return v___x_1582_;
}
}
static lean_object* _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__31(void){
_start:
{
lean_object* v___x_1584_; lean_object* v___x_1585_; 
v___x_1584_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__30));
v___x_1585_ = l_Lean_stringToMessageData(v___x_1584_);
return v___x_1585_;
}
}
static lean_object* _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__33(void){
_start:
{
lean_object* v___x_1587_; lean_object* v___x_1588_; 
v___x_1587_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__32));
v___x_1588_ = l_Lean_stringToMessageData(v___x_1587_);
return v___x_1588_;
}
}
static lean_object* _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__35(void){
_start:
{
lean_object* v___x_1590_; lean_object* v___x_1591_; 
v___x_1590_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__34));
v___x_1591_ = l_Lean_stringToMessageData(v___x_1590_);
return v___x_1591_;
}
}
static lean_object* _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__37(void){
_start:
{
lean_object* v___x_1593_; lean_object* v___x_1594_; 
v___x_1593_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__36));
v___x_1594_ = l_Lean_stringToMessageData(v___x_1593_);
return v___x_1594_;
}
}
static lean_object* _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__39(void){
_start:
{
lean_object* v___x_1596_; lean_object* v___x_1597_; 
v___x_1596_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__38));
v___x_1597_ = l_Lean_stringToMessageData(v___x_1596_);
return v___x_1597_;
}
}
static lean_object* _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__41(void){
_start:
{
lean_object* v___x_1599_; lean_object* v___x_1600_; 
v___x_1599_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__40));
v___x_1600_ = l_Lean_stringToMessageData(v___x_1599_);
return v___x_1600_;
}
}
static lean_object* _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__43(void){
_start:
{
lean_object* v___x_1602_; lean_object* v___x_1603_; 
v___x_1602_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__42));
v___x_1603_ = l_Lean_stringToMessageData(v___x_1602_);
return v___x_1603_;
}
}
static lean_object* _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__45(void){
_start:
{
lean_object* v___x_1605_; lean_object* v___x_1606_; 
v___x_1605_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__44));
v___x_1606_ = l_Lean_stringToMessageData(v___x_1605_);
return v___x_1606_;
}
}
static lean_object* _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__47(void){
_start:
{
lean_object* v___x_1608_; lean_object* v___x_1609_; 
v___x_1608_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__46));
v___x_1609_ = l_Lean_stringToMessageData(v___x_1608_);
return v___x_1609_;
}
}
static lean_object* _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__49(void){
_start:
{
lean_object* v___x_1611_; lean_object* v___x_1612_; 
v___x_1611_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__48));
v___x_1612_ = l_Lean_stringToMessageData(v___x_1611_);
return v___x_1612_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0(uint8_t v_status_1613_, lean_object* v_declName_1614_, lean_object* v_suffix_1615_, uint8_t v_attrKind_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_){
_start:
{
lean_object* v___x_1632_; lean_object* v___x_1633_; uint8_t v___x_1634_; uint8_t v___y_1636_; lean_object* v___y_1637_; lean_object* v___y_1638_; lean_object* v___y_1706_; lean_object* v___y_1707_; 
v___x_1632_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1617_);
v___x_1633_ = l_Lean_allowUnsafeReducibility;
v___x_1634_ = l_Lean_Option_get___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__0(v___x_1632_, v___x_1633_);
lean_dec_ref(v___x_1632_);
if (v___x_1634_ == 0)
{
lean_object* v___x_1787_; 
lean_inc(v_declName_1614_);
v___x_1787_ = l_Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2(v_declName_1614_, v___y_1617_, v___y_1618_);
if (lean_obj_tag(v___x_1787_) == 0)
{
lean_object* v_a_1788_; uint8_t v___x_1789_; 
v_a_1788_ = lean_ctor_get(v___x_1787_, 0);
lean_inc(v_a_1788_);
lean_dec_ref_known(v___x_1787_, 1);
v___x_1789_ = l_Lean_ConstantInfo_isDefinition(v_a_1788_);
lean_dec(v_a_1788_);
if (v___x_1789_ == 0)
{
lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; 
v___x_1790_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__19, &l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__19_once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__19);
v___x_1791_ = l_Lean_MessageData_ofConstName(v_declName_1614_, v___x_1789_);
v___x_1792_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1792_, 0, v___x_1790_);
lean_ctor_set(v___x_1792_, 1, v___x_1791_);
v___x_1793_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__49, &l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__49_once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__49);
v___x_1794_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1794_, 0, v___x_1792_);
lean_ctor_set(v___x_1794_, 1, v___x_1793_);
v___x_1795_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1795_, 0, v___x_1794_);
lean_ctor_set(v___x_1795_, 1, v_suffix_1615_);
v___x_1796_ = l_Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1___redArg(v___x_1795_, v___y_1617_, v___y_1618_);
return v___x_1796_;
}
else
{
v___y_1706_ = v___y_1617_;
v___y_1707_ = v___y_1618_;
goto v___jp_1705_;
}
}
else
{
lean_object* v_a_1797_; lean_object* v___x_1799_; uint8_t v_isShared_1800_; uint8_t v_isSharedCheck_1804_; 
lean_dec_ref(v_suffix_1615_);
lean_dec(v_declName_1614_);
v_a_1797_ = lean_ctor_get(v___x_1787_, 0);
v_isSharedCheck_1804_ = !lean_is_exclusive(v___x_1787_);
if (v_isSharedCheck_1804_ == 0)
{
v___x_1799_ = v___x_1787_;
v_isShared_1800_ = v_isSharedCheck_1804_;
goto v_resetjp_1798_;
}
else
{
lean_inc(v_a_1797_);
lean_dec(v___x_1787_);
v___x_1799_ = lean_box(0);
v_isShared_1800_ = v_isSharedCheck_1804_;
goto v_resetjp_1798_;
}
v_resetjp_1798_:
{
lean_object* v___x_1802_; 
if (v_isShared_1800_ == 0)
{
v___x_1802_ = v___x_1799_;
goto v_reusejp_1801_;
}
else
{
lean_object* v_reuseFailAlloc_1803_; 
v_reuseFailAlloc_1803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1803_, 0, v_a_1797_);
v___x_1802_ = v_reuseFailAlloc_1803_;
goto v_reusejp_1801_;
}
v_reusejp_1801_:
{
return v___x_1802_;
}
}
}
}
else
{
lean_object* v___x_1805_; lean_object* v___x_1806_; 
lean_dec_ref(v_suffix_1615_);
lean_dec(v_declName_1614_);
v___x_1805_ = lean_box(0);
v___x_1806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1806_, 0, v___x_1805_);
return v___x_1806_;
}
v___jp_1620_:
{
lean_object* v___x_1621_; lean_object* v___x_1622_; 
v___x_1621_ = lean_box(0);
v___x_1622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1622_, 0, v___x_1621_);
return v___x_1622_;
}
v___jp_1623_:
{
lean_object* v___x_1624_; lean_object* v___x_1625_; 
v___x_1624_ = lean_box(0);
v___x_1625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1625_, 0, v___x_1624_);
return v___x_1625_;
}
v___jp_1626_:
{
lean_object* v___x_1627_; lean_object* v___x_1628_; 
v___x_1627_ = lean_box(0);
v___x_1628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1628_, 0, v___x_1627_);
return v___x_1628_;
}
v___jp_1629_:
{
lean_object* v___x_1630_; lean_object* v___x_1631_; 
v___x_1630_ = lean_box(0);
v___x_1631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1631_, 0, v___x_1630_);
return v___x_1631_;
}
v___jp_1635_:
{
switch(v_status_1613_)
{
case 0:
{
if (v___y_1636_ == 1)
{
lean_object* v___x_1639_; lean_object* v___x_1640_; 
lean_dec_ref(v_suffix_1615_);
lean_dec(v_declName_1614_);
v___x_1639_ = lean_box(0);
v___x_1640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1640_, 0, v___x_1639_);
return v___x_1640_;
}
else
{
lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; 
v___x_1641_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__1, &l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__1_once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__1);
v___x_1642_ = l_Lean_MessageData_ofConstName(v_declName_1614_, v___x_1634_);
v___x_1643_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1643_, 0, v___x_1641_);
lean_ctor_set(v___x_1643_, 1, v___x_1642_);
v___x_1644_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__3, &l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__3_once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__3);
v___x_1645_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1645_, 0, v___x_1643_);
lean_ctor_set(v___x_1645_, 1, v___x_1644_);
v___x_1646_ = l_Lean_ReducibilityStatus_toAttrString(v___y_1636_);
v___x_1647_ = l_Lean_stringToMessageData(v___x_1646_);
v___x_1648_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1648_, 0, v___x_1645_);
lean_ctor_set(v___x_1648_, 1, v___x_1647_);
v___x_1649_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg___closed__3);
v___x_1650_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1650_, 0, v___x_1648_);
lean_ctor_set(v___x_1650_, 1, v___x_1649_);
v___x_1651_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1651_, 0, v___x_1650_);
lean_ctor_set(v___x_1651_, 1, v_suffix_1615_);
v___x_1652_ = l_Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1___redArg(v___x_1651_, v___y_1637_, v___y_1638_);
return v___x_1652_;
}
}
case 1:
{
if (v___y_1636_ == 1)
{
lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; 
v___x_1653_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__5, &l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__5_once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__5);
v___x_1654_ = l_Lean_MessageData_ofConstName(v_declName_1614_, v___x_1634_);
v___x_1655_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1655_, 0, v___x_1653_);
lean_ctor_set(v___x_1655_, 1, v___x_1654_);
v___x_1656_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__7, &l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__7_once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__7);
v___x_1657_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1657_, 0, v___x_1655_);
lean_ctor_set(v___x_1657_, 1, v___x_1656_);
v___x_1658_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1658_, 0, v___x_1657_);
lean_ctor_set(v___x_1658_, 1, v_suffix_1615_);
v___x_1659_ = l_Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1___redArg(v___x_1658_, v___y_1637_, v___y_1638_);
return v___x_1659_;
}
else
{
lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; 
v___x_1660_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__5, &l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__5_once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__5);
v___x_1661_ = l_Lean_MessageData_ofConstName(v_declName_1614_, v___x_1634_);
v___x_1662_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1662_, 0, v___x_1660_);
lean_ctor_set(v___x_1662_, 1, v___x_1661_);
v___x_1663_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg___closed__3);
v___x_1664_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1664_, 0, v___x_1662_);
lean_ctor_set(v___x_1664_, 1, v___x_1663_);
v___x_1665_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1665_, 0, v___x_1664_);
lean_ctor_set(v___x_1665_, 1, v_suffix_1615_);
v___x_1666_ = l_Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1___redArg(v___x_1665_, v___y_1637_, v___y_1638_);
return v___x_1666_;
}
}
case 2:
{
switch(v___y_1636_)
{
case 1:
{
lean_dec_ref(v_suffix_1615_);
lean_dec(v_declName_1614_);
goto v___jp_1629_;
}
case 3:
{
lean_dec_ref(v_suffix_1615_);
lean_dec(v_declName_1614_);
goto v___jp_1629_;
}
case 4:
{
lean_dec_ref(v_suffix_1615_);
lean_dec(v_declName_1614_);
goto v___jp_1629_;
}
default: 
{
lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; 
v___x_1667_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__9, &l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__9_once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__9);
v___x_1668_ = l_Lean_MessageData_ofConstName(v_declName_1614_, v___x_1634_);
v___x_1669_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1669_, 0, v___x_1667_);
lean_ctor_set(v___x_1669_, 1, v___x_1668_);
v___x_1670_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__11, &l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__11_once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__11);
v___x_1671_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1671_, 0, v___x_1669_);
lean_ctor_set(v___x_1671_, 1, v___x_1670_);
v___x_1672_ = l_Lean_ReducibilityStatus_toAttrString(v___y_1636_);
v___x_1673_ = l_Lean_stringToMessageData(v___x_1672_);
v___x_1674_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1674_, 0, v___x_1671_);
lean_ctor_set(v___x_1674_, 1, v___x_1673_);
v___x_1675_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg___closed__3);
v___x_1676_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1676_, 0, v___x_1674_);
lean_ctor_set(v___x_1676_, 1, v___x_1675_);
v___x_1677_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1677_, 0, v___x_1676_);
lean_ctor_set(v___x_1677_, 1, v_suffix_1615_);
v___x_1678_ = l_Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1___redArg(v___x_1677_, v___y_1637_, v___y_1638_);
return v___x_1678_;
}
}
}
case 3:
{
switch(v___y_1636_)
{
case 1:
{
lean_dec_ref(v_suffix_1615_);
lean_dec(v_declName_1614_);
goto v___jp_1626_;
}
case 4:
{
lean_dec_ref(v_suffix_1615_);
lean_dec(v_declName_1614_);
goto v___jp_1626_;
}
default: 
{
lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; 
v___x_1679_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__13, &l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__13_once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__13);
v___x_1680_ = l_Lean_MessageData_ofConstName(v_declName_1614_, v___x_1634_);
v___x_1681_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1681_, 0, v___x_1679_);
lean_ctor_set(v___x_1681_, 1, v___x_1680_);
v___x_1682_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__15, &l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__15_once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__15);
v___x_1683_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1683_, 0, v___x_1681_);
lean_ctor_set(v___x_1683_, 1, v___x_1682_);
v___x_1684_ = l_Lean_ReducibilityStatus_toAttrString(v___y_1636_);
v___x_1685_ = l_Lean_stringToMessageData(v___x_1684_);
v___x_1686_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1686_, 0, v___x_1683_);
lean_ctor_set(v___x_1686_, 1, v___x_1685_);
v___x_1687_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg___closed__3);
v___x_1688_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1688_, 0, v___x_1686_);
lean_ctor_set(v___x_1688_, 1, v___x_1687_);
v___x_1689_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1689_, 0, v___x_1688_);
lean_ctor_set(v___x_1689_, 1, v_suffix_1615_);
v___x_1690_ = l_Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1___redArg(v___x_1689_, v___y_1637_, v___y_1638_);
return v___x_1690_;
}
}
}
default: 
{
if (v___y_1636_ == 1)
{
lean_object* v___x_1691_; lean_object* v___x_1692_; 
lean_dec_ref(v_suffix_1615_);
lean_dec(v_declName_1614_);
v___x_1691_ = lean_box(0);
v___x_1692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1692_, 0, v___x_1691_);
return v___x_1692_;
}
else
{
lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; 
v___x_1693_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__17, &l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__17_once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__17);
v___x_1694_ = l_Lean_MessageData_ofConstName(v_declName_1614_, v___x_1634_);
v___x_1695_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1695_, 0, v___x_1693_);
lean_ctor_set(v___x_1695_, 1, v___x_1694_);
v___x_1696_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__3, &l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__3_once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__3);
v___x_1697_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1697_, 0, v___x_1695_);
lean_ctor_set(v___x_1697_, 1, v___x_1696_);
v___x_1698_ = l_Lean_ReducibilityStatus_toAttrString(v___y_1636_);
v___x_1699_ = l_Lean_stringToMessageData(v___x_1698_);
v___x_1700_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1700_, 0, v___x_1697_);
lean_ctor_set(v___x_1700_, 1, v___x_1699_);
v___x_1701_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg___closed__3);
v___x_1702_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1702_, 0, v___x_1700_);
lean_ctor_set(v___x_1702_, 1, v___x_1701_);
v___x_1703_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1703_, 0, v___x_1702_);
lean_ctor_set(v___x_1703_, 1, v_suffix_1615_);
v___x_1704_ = l_Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1___redArg(v___x_1703_, v___y_1637_, v___y_1638_);
return v___x_1704_;
}
}
}
}
v___jp_1705_:
{
lean_object* v___x_1708_; lean_object* v_env_1709_; uint8_t v___x_1710_; 
v___x_1708_ = lean_st_ref_get(v___y_1707_);
v_env_1709_ = lean_ctor_get(v___x_1708_, 0);
lean_inc_ref(v_env_1709_);
lean_dec(v___x_1708_);
lean_inc(v_declName_1614_);
v___x_1710_ = l_Lean_getReducibilityStatusCore(v_env_1709_, v_declName_1614_);
switch(v_attrKind_1616_)
{
case 0:
{
lean_object* v___x_1711_; lean_object* v_env_1712_; lean_object* v___x_1713_; 
v___x_1711_ = lean_st_ref_get(v___y_1707_);
v_env_1712_ = lean_ctor_get(v___x_1711_, 0);
lean_inc_ref(v_env_1712_);
lean_dec(v___x_1711_);
v___x_1713_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1712_, v_declName_1614_);
lean_dec_ref(v_env_1712_);
if (lean_obj_tag(v___x_1713_) == 1)
{
lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; 
lean_dec_ref_known(v___x_1713_, 1);
v___x_1714_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__19, &l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__19_once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__19);
v___x_1715_ = l_Lean_MessageData_ofConstName(v_declName_1614_, v___x_1634_);
v___x_1716_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1716_, 0, v___x_1714_);
lean_ctor_set(v___x_1716_, 1, v___x_1715_);
v___x_1717_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__21, &l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__21_once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__21);
v___x_1718_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1718_, 0, v___x_1716_);
lean_ctor_set(v___x_1718_, 1, v___x_1717_);
v___x_1719_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1719_, 0, v___x_1718_);
lean_ctor_set(v___x_1719_, 1, v_suffix_1615_);
v___x_1720_ = l_Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1___redArg(v___x_1719_, v___y_1706_, v___y_1707_);
return v___x_1720_;
}
else
{
lean_dec(v___x_1713_);
v___y_1636_ = v___x_1710_;
v___y_1637_ = v___y_1706_;
v___y_1638_ = v___y_1707_;
goto v___jp_1635_;
}
}
case 1:
{
switch(v_status_1613_)
{
case 0:
{
lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; 
v___x_1721_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__23, &l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__23_once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__23);
v___x_1722_ = l_Lean_MessageData_ofConstName(v_declName_1614_, v___x_1634_);
v___x_1723_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1723_, 0, v___x_1721_);
lean_ctor_set(v___x_1723_, 1, v___x_1722_);
v___x_1724_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__25, &l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__25_once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__25);
v___x_1725_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1725_, 0, v___x_1723_);
lean_ctor_set(v___x_1725_, 1, v___x_1724_);
v___x_1726_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1726_, 0, v___x_1725_);
lean_ctor_set(v___x_1726_, 1, v_suffix_1615_);
v___x_1727_ = l_Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1___redArg(v___x_1726_, v___y_1706_, v___y_1707_);
return v___x_1727_;
}
case 1:
{
if (v___x_1710_ == 2)
{
lean_object* v___x_1728_; lean_object* v___x_1729_; 
lean_dec_ref(v_suffix_1615_);
lean_dec(v_declName_1614_);
v___x_1728_ = lean_box(0);
v___x_1729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1729_, 0, v___x_1728_);
return v___x_1729_;
}
else
{
lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; 
v___x_1730_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__27, &l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__27_once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__27);
v___x_1731_ = l_Lean_MessageData_ofConstName(v_declName_1614_, v___x_1634_);
v___x_1732_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1732_, 0, v___x_1730_);
lean_ctor_set(v___x_1732_, 1, v___x_1731_);
v___x_1733_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__29, &l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__29_once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__29);
v___x_1734_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1734_, 0, v___x_1732_);
lean_ctor_set(v___x_1734_, 1, v___x_1733_);
v___x_1735_ = l_Lean_ReducibilityStatus_toAttrString(v___x_1710_);
v___x_1736_ = l_Lean_stringToMessageData(v___x_1735_);
v___x_1737_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1737_, 0, v___x_1734_);
lean_ctor_set(v___x_1737_, 1, v___x_1736_);
v___x_1738_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__31, &l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__31_once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__31);
v___x_1739_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1739_, 0, v___x_1737_);
lean_ctor_set(v___x_1739_, 1, v___x_1738_);
v___x_1740_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1740_, 0, v___x_1739_);
lean_ctor_set(v___x_1740_, 1, v_suffix_1615_);
v___x_1741_ = l_Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1___redArg(v___x_1740_, v___y_1706_, v___y_1707_);
return v___x_1741_;
}
}
case 2:
{
switch(v___x_1710_)
{
case 1:
{
lean_dec_ref(v_suffix_1615_);
lean_dec(v_declName_1614_);
goto v___jp_1620_;
}
case 3:
{
lean_dec_ref(v_suffix_1615_);
lean_dec(v_declName_1614_);
goto v___jp_1620_;
}
case 4:
{
lean_dec_ref(v_suffix_1615_);
lean_dec(v_declName_1614_);
goto v___jp_1620_;
}
default: 
{
lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; 
v___x_1742_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__33, &l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__33_once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__33);
v___x_1743_ = l_Lean_MessageData_ofConstName(v_declName_1614_, v___x_1634_);
v___x_1744_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1744_, 0, v___x_1742_);
lean_ctor_set(v___x_1744_, 1, v___x_1743_);
v___x_1745_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__29, &l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__29_once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__29);
v___x_1746_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1746_, 0, v___x_1744_);
lean_ctor_set(v___x_1746_, 1, v___x_1745_);
v___x_1747_ = l_Lean_ReducibilityStatus_toAttrString(v___x_1710_);
v___x_1748_ = l_Lean_stringToMessageData(v___x_1747_);
v___x_1749_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1749_, 0, v___x_1746_);
lean_ctor_set(v___x_1749_, 1, v___x_1748_);
v___x_1750_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__35, &l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__35_once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__35);
v___x_1751_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1751_, 0, v___x_1749_);
lean_ctor_set(v___x_1751_, 1, v___x_1750_);
v___x_1752_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1752_, 0, v___x_1751_);
lean_ctor_set(v___x_1752_, 1, v_suffix_1615_);
v___x_1753_ = l_Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1___redArg(v___x_1752_, v___y_1706_, v___y_1707_);
return v___x_1753_;
}
}
}
case 3:
{
switch(v___x_1710_)
{
case 1:
{
lean_dec_ref(v_suffix_1615_);
lean_dec(v_declName_1614_);
goto v___jp_1623_;
}
case 4:
{
lean_dec_ref(v_suffix_1615_);
lean_dec(v_declName_1614_);
goto v___jp_1623_;
}
default: 
{
lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; 
v___x_1754_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__37, &l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__37_once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__37);
v___x_1755_ = l_Lean_MessageData_ofConstName(v_declName_1614_, v___x_1634_);
v___x_1756_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1756_, 0, v___x_1754_);
lean_ctor_set(v___x_1756_, 1, v___x_1755_);
v___x_1757_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__29, &l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__29_once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__29);
v___x_1758_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1758_, 0, v___x_1756_);
lean_ctor_set(v___x_1758_, 1, v___x_1757_);
v___x_1759_ = l_Lean_ReducibilityStatus_toAttrString(v___x_1710_);
v___x_1760_ = l_Lean_stringToMessageData(v___x_1759_);
v___x_1761_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1761_, 0, v___x_1758_);
lean_ctor_set(v___x_1761_, 1, v___x_1760_);
v___x_1762_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__39, &l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__39_once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__39);
v___x_1763_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1763_, 0, v___x_1761_);
lean_ctor_set(v___x_1763_, 1, v___x_1762_);
v___x_1764_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1764_, 0, v___x_1763_);
lean_ctor_set(v___x_1764_, 1, v_suffix_1615_);
v___x_1765_ = l_Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1___redArg(v___x_1764_, v___y_1706_, v___y_1707_);
return v___x_1765_;
}
}
}
default: 
{
if (v___x_1710_ == 1)
{
lean_object* v___x_1766_; lean_object* v___x_1767_; 
lean_dec_ref(v_suffix_1615_);
lean_dec(v_declName_1614_);
v___x_1766_ = lean_box(0);
v___x_1767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1767_, 0, v___x_1766_);
return v___x_1767_;
}
else
{
lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; 
v___x_1768_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__41, &l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__41_once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__41);
v___x_1769_ = l_Lean_MessageData_ofConstName(v_declName_1614_, v___x_1634_);
v___x_1770_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1770_, 0, v___x_1768_);
lean_ctor_set(v___x_1770_, 1, v___x_1769_);
v___x_1771_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__29, &l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__29_once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__29);
v___x_1772_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1772_, 0, v___x_1770_);
lean_ctor_set(v___x_1772_, 1, v___x_1771_);
v___x_1773_ = l_Lean_ReducibilityStatus_toAttrString(v___x_1710_);
v___x_1774_ = l_Lean_stringToMessageData(v___x_1773_);
v___x_1775_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1775_, 0, v___x_1772_);
lean_ctor_set(v___x_1775_, 1, v___x_1774_);
v___x_1776_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__43, &l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__43_once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__43);
v___x_1777_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1777_, 0, v___x_1775_);
lean_ctor_set(v___x_1777_, 1, v___x_1776_);
v___x_1778_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1778_, 0, v___x_1777_);
lean_ctor_set(v___x_1778_, 1, v_suffix_1615_);
v___x_1779_ = l_Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1___redArg(v___x_1778_, v___y_1706_, v___y_1707_);
return v___x_1779_;
}
}
}
}
default: 
{
lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; 
v___x_1780_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__45, &l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__45_once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__45);
v___x_1781_ = l_Lean_MessageData_ofConstName(v_declName_1614_, v___x_1634_);
v___x_1782_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1782_, 0, v___x_1780_);
lean_ctor_set(v___x_1782_, 1, v___x_1781_);
v___x_1783_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__47, &l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__47_once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__47);
v___x_1784_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1784_, 0, v___x_1782_);
lean_ctor_set(v___x_1784_, 1, v___x_1783_);
v___x_1785_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1785_, 0, v___x_1784_);
lean_ctor_set(v___x_1785_, 1, v_suffix_1615_);
v___x_1786_ = l_Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1___redArg(v___x_1785_, v___y_1706_, v___y_1707_);
return v___x_1786_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___boxed(lean_object* v_status_1807_, lean_object* v_declName_1808_, lean_object* v_suffix_1809_, lean_object* v_attrKind_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_){
_start:
{
uint8_t v_status_boxed_1814_; uint8_t v_attrKind_boxed_1815_; lean_object* v_res_1816_; 
v_status_boxed_1814_ = lean_unbox(v_status_1807_);
v_attrKind_boxed_1815_ = lean_unbox(v_attrKind_1810_);
v_res_1816_ = l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0(v_status_boxed_1814_, v_declName_1808_, v_suffix_1809_, v_attrKind_boxed_1815_, v___y_1811_, v___y_1812_);
lean_dec(v___y_1812_);
lean_dec_ref(v___y_1811_);
return v_res_1816_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___redArg___lam__0(lean_object* v___y_1817_, uint8_t v_isExporting_1818_, lean_object* v___x_1819_, lean_object* v_a_x3f_1820_){
_start:
{
lean_object* v___x_1822_; lean_object* v_env_1823_; lean_object* v_nextMacroScope_1824_; lean_object* v_ngen_1825_; lean_object* v_auxDeclNGen_1826_; lean_object* v_traceState_1827_; lean_object* v_recordedDeps_1828_; lean_object* v_messages_1829_; lean_object* v_infoState_1830_; lean_object* v_snapshotTasks_1831_; lean_object* v___x_1833_; uint8_t v_isShared_1834_; uint8_t v_isSharedCheck_1842_; 
v___x_1822_ = lean_st_ref_take(v___y_1817_);
v_env_1823_ = lean_ctor_get(v___x_1822_, 0);
v_nextMacroScope_1824_ = lean_ctor_get(v___x_1822_, 1);
v_ngen_1825_ = lean_ctor_get(v___x_1822_, 2);
v_auxDeclNGen_1826_ = lean_ctor_get(v___x_1822_, 3);
v_traceState_1827_ = lean_ctor_get(v___x_1822_, 4);
v_recordedDeps_1828_ = lean_ctor_get(v___x_1822_, 6);
v_messages_1829_ = lean_ctor_get(v___x_1822_, 7);
v_infoState_1830_ = lean_ctor_get(v___x_1822_, 8);
v_snapshotTasks_1831_ = lean_ctor_get(v___x_1822_, 9);
v_isSharedCheck_1842_ = !lean_is_exclusive(v___x_1822_);
if (v_isSharedCheck_1842_ == 0)
{
lean_object* v_unused_1843_; 
v_unused_1843_ = lean_ctor_get(v___x_1822_, 5);
lean_dec(v_unused_1843_);
v___x_1833_ = v___x_1822_;
v_isShared_1834_ = v_isSharedCheck_1842_;
goto v_resetjp_1832_;
}
else
{
lean_inc(v_snapshotTasks_1831_);
lean_inc(v_infoState_1830_);
lean_inc(v_messages_1829_);
lean_inc(v_recordedDeps_1828_);
lean_inc(v_traceState_1827_);
lean_inc(v_auxDeclNGen_1826_);
lean_inc(v_ngen_1825_);
lean_inc(v_nextMacroScope_1824_);
lean_inc(v_env_1823_);
lean_dec(v___x_1822_);
v___x_1833_ = lean_box(0);
v_isShared_1834_ = v_isSharedCheck_1842_;
goto v_resetjp_1832_;
}
v_resetjp_1832_:
{
lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1838_; 
v___x_1835_ = lean_box(0);
v___x_1836_ = l_Lean_Environment_setExporting(v_env_1823_, v_isExporting_1818_);
if (v_isShared_1834_ == 0)
{
lean_ctor_set(v___x_1833_, 5, v___x_1819_);
lean_ctor_set(v___x_1833_, 0, v___x_1836_);
v___x_1838_ = v___x_1833_;
goto v_reusejp_1837_;
}
else
{
lean_object* v_reuseFailAlloc_1841_; 
v_reuseFailAlloc_1841_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1841_, 0, v___x_1836_);
lean_ctor_set(v_reuseFailAlloc_1841_, 1, v_nextMacroScope_1824_);
lean_ctor_set(v_reuseFailAlloc_1841_, 2, v_ngen_1825_);
lean_ctor_set(v_reuseFailAlloc_1841_, 3, v_auxDeclNGen_1826_);
lean_ctor_set(v_reuseFailAlloc_1841_, 4, v_traceState_1827_);
lean_ctor_set(v_reuseFailAlloc_1841_, 5, v___x_1819_);
lean_ctor_set(v_reuseFailAlloc_1841_, 6, v_recordedDeps_1828_);
lean_ctor_set(v_reuseFailAlloc_1841_, 7, v_messages_1829_);
lean_ctor_set(v_reuseFailAlloc_1841_, 8, v_infoState_1830_);
lean_ctor_set(v_reuseFailAlloc_1841_, 9, v_snapshotTasks_1831_);
v___x_1838_ = v_reuseFailAlloc_1841_;
goto v_reusejp_1837_;
}
v_reusejp_1837_:
{
lean_object* v___x_1839_; lean_object* v___x_1840_; 
v___x_1839_ = lean_st_ref_put(v___y_1817_, v___x_1838_);
v___x_1840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1840_, 0, v___x_1835_);
return v___x_1840_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___redArg___lam__0___boxed(lean_object* v___y_1844_, lean_object* v_isExporting_1845_, lean_object* v___x_1846_, lean_object* v_a_x3f_1847_, lean_object* v___y_1848_){
_start:
{
uint8_t v_isExporting_boxed_1849_; lean_object* v_res_1850_; 
v_isExporting_boxed_1849_ = lean_unbox(v_isExporting_1845_);
v_res_1850_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___redArg___lam__0(v___y_1844_, v_isExporting_boxed_1849_, v___x_1846_, v_a_x3f_1847_);
lean_dec(v_a_x3f_1847_);
lean_dec(v___y_1844_);
return v_res_1850_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_1851_; lean_object* v___x_1852_; 
v___x_1851_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__9_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2_, &l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__9_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2__once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__9_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2_);
v___x_1852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1852_, 0, v___x_1851_);
return v___x_1852_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_1853_; lean_object* v___x_1854_; 
v___x_1853_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___redArg___closed__0, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___redArg___closed__0);
v___x_1854_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1854_, 0, v___x_1853_);
lean_ctor_set(v___x_1854_, 1, v___x_1853_);
return v___x_1854_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___redArg(lean_object* v_x_1855_, uint8_t v_isExporting_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_){
_start:
{
lean_object* v___x_1860_; lean_object* v_env_1861_; lean_object* v___x_1862_; uint8_t v_isModule_1863_; 
v___x_1860_ = lean_st_ref_get(v___y_1858_);
v_env_1861_ = lean_ctor_get(v___x_1860_, 0);
lean_inc_ref(v_env_1861_);
lean_dec(v___x_1860_);
v___x_1862_ = l_Lean_Environment_header(v_env_1861_);
v_isModule_1863_ = lean_ctor_get_uint8(v___x_1862_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_1862_);
if (v_isModule_1863_ == 0)
{
lean_object* v___x_1864_; 
lean_dec_ref(v_env_1861_);
lean_inc(v___y_1858_);
lean_inc_ref(v___y_1857_);
v___x_1864_ = lean_apply_3(v_x_1855_, v___y_1857_, v___y_1858_, lean_box(0));
return v___x_1864_;
}
else
{
uint8_t v_isExporting_1865_; 
v_isExporting_1865_ = lean_ctor_get_uint8(v_env_1861_, sizeof(void*)*13);
lean_dec_ref(v_env_1861_);
if (v_isExporting_1856_ == 0)
{
if (v_isExporting_1865_ == 0)
{
lean_object* v___x_1917_; 
lean_inc(v___y_1858_);
lean_inc_ref(v___y_1857_);
v___x_1917_ = lean_apply_3(v_x_1855_, v___y_1857_, v___y_1858_, lean_box(0));
return v___x_1917_;
}
else
{
goto v___jp_1866_;
}
}
else
{
if (v_isExporting_1865_ == 0)
{
goto v___jp_1866_;
}
else
{
lean_object* v___x_1918_; 
lean_inc(v___y_1858_);
lean_inc_ref(v___y_1857_);
v___x_1918_ = lean_apply_3(v_x_1855_, v___y_1857_, v___y_1858_, lean_box(0));
return v___x_1918_;
}
}
v___jp_1866_:
{
lean_object* v___x_1867_; lean_object* v_env_1868_; lean_object* v_nextMacroScope_1869_; lean_object* v_ngen_1870_; lean_object* v_auxDeclNGen_1871_; lean_object* v_traceState_1872_; lean_object* v_recordedDeps_1873_; lean_object* v_messages_1874_; lean_object* v_infoState_1875_; lean_object* v_snapshotTasks_1876_; lean_object* v___x_1878_; uint8_t v_isShared_1879_; uint8_t v_isSharedCheck_1915_; 
v___x_1867_ = lean_st_ref_take(v___y_1858_);
v_env_1868_ = lean_ctor_get(v___x_1867_, 0);
v_nextMacroScope_1869_ = lean_ctor_get(v___x_1867_, 1);
v_ngen_1870_ = lean_ctor_get(v___x_1867_, 2);
v_auxDeclNGen_1871_ = lean_ctor_get(v___x_1867_, 3);
v_traceState_1872_ = lean_ctor_get(v___x_1867_, 4);
v_recordedDeps_1873_ = lean_ctor_get(v___x_1867_, 6);
v_messages_1874_ = lean_ctor_get(v___x_1867_, 7);
v_infoState_1875_ = lean_ctor_get(v___x_1867_, 8);
v_snapshotTasks_1876_ = lean_ctor_get(v___x_1867_, 9);
v_isSharedCheck_1915_ = !lean_is_exclusive(v___x_1867_);
if (v_isSharedCheck_1915_ == 0)
{
lean_object* v_unused_1916_; 
v_unused_1916_ = lean_ctor_get(v___x_1867_, 5);
lean_dec(v_unused_1916_);
v___x_1878_ = v___x_1867_;
v_isShared_1879_ = v_isSharedCheck_1915_;
goto v_resetjp_1877_;
}
else
{
lean_inc(v_snapshotTasks_1876_);
lean_inc(v_infoState_1875_);
lean_inc(v_messages_1874_);
lean_inc(v_recordedDeps_1873_);
lean_inc(v_traceState_1872_);
lean_inc(v_auxDeclNGen_1871_);
lean_inc(v_ngen_1870_);
lean_inc(v_nextMacroScope_1869_);
lean_inc(v_env_1868_);
lean_dec(v___x_1867_);
v___x_1878_ = lean_box(0);
v_isShared_1879_ = v_isSharedCheck_1915_;
goto v_resetjp_1877_;
}
v_resetjp_1877_:
{
lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1883_; 
v___x_1880_ = l_Lean_Environment_setExporting(v_env_1868_, v_isExporting_1856_);
v___x_1881_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___redArg___closed__1, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___redArg___closed__1);
if (v_isShared_1879_ == 0)
{
lean_ctor_set(v___x_1878_, 5, v___x_1881_);
lean_ctor_set(v___x_1878_, 0, v___x_1880_);
v___x_1883_ = v___x_1878_;
goto v_reusejp_1882_;
}
else
{
lean_object* v_reuseFailAlloc_1914_; 
v_reuseFailAlloc_1914_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1914_, 0, v___x_1880_);
lean_ctor_set(v_reuseFailAlloc_1914_, 1, v_nextMacroScope_1869_);
lean_ctor_set(v_reuseFailAlloc_1914_, 2, v_ngen_1870_);
lean_ctor_set(v_reuseFailAlloc_1914_, 3, v_auxDeclNGen_1871_);
lean_ctor_set(v_reuseFailAlloc_1914_, 4, v_traceState_1872_);
lean_ctor_set(v_reuseFailAlloc_1914_, 5, v___x_1881_);
lean_ctor_set(v_reuseFailAlloc_1914_, 6, v_recordedDeps_1873_);
lean_ctor_set(v_reuseFailAlloc_1914_, 7, v_messages_1874_);
lean_ctor_set(v_reuseFailAlloc_1914_, 8, v_infoState_1875_);
lean_ctor_set(v_reuseFailAlloc_1914_, 9, v_snapshotTasks_1876_);
v___x_1883_ = v_reuseFailAlloc_1914_;
goto v_reusejp_1882_;
}
v_reusejp_1882_:
{
lean_object* v___x_1884_; lean_object* v_r_1885_; 
v___x_1884_ = lean_st_ref_put(v___y_1858_, v___x_1883_);
lean_inc(v___y_1858_);
lean_inc_ref(v___y_1857_);
v_r_1885_ = lean_apply_3(v_x_1855_, v___y_1857_, v___y_1858_, lean_box(0));
if (lean_obj_tag(v_r_1885_) == 0)
{
lean_object* v_a_1886_; lean_object* v___x_1888_; uint8_t v_isShared_1889_; uint8_t v_isSharedCheck_1902_; 
v_a_1886_ = lean_ctor_get(v_r_1885_, 0);
v_isSharedCheck_1902_ = !lean_is_exclusive(v_r_1885_);
if (v_isSharedCheck_1902_ == 0)
{
v___x_1888_ = v_r_1885_;
v_isShared_1889_ = v_isSharedCheck_1902_;
goto v_resetjp_1887_;
}
else
{
lean_inc(v_a_1886_);
lean_dec(v_r_1885_);
v___x_1888_ = lean_box(0);
v_isShared_1889_ = v_isSharedCheck_1902_;
goto v_resetjp_1887_;
}
v_resetjp_1887_:
{
lean_object* v___x_1891_; 
lean_inc(v_a_1886_);
if (v_isShared_1889_ == 0)
{
lean_ctor_set_tag(v___x_1888_, 1);
v___x_1891_ = v___x_1888_;
goto v_reusejp_1890_;
}
else
{
lean_object* v_reuseFailAlloc_1901_; 
v_reuseFailAlloc_1901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1901_, 0, v_a_1886_);
v___x_1891_ = v_reuseFailAlloc_1901_;
goto v_reusejp_1890_;
}
v_reusejp_1890_:
{
lean_object* v___x_1892_; lean_object* v___x_1894_; uint8_t v_isShared_1895_; uint8_t v_isSharedCheck_1899_; 
v___x_1892_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___redArg___lam__0(v___y_1858_, v_isExporting_1865_, v___x_1881_, v___x_1891_);
lean_dec_ref(v___x_1891_);
v_isSharedCheck_1899_ = !lean_is_exclusive(v___x_1892_);
if (v_isSharedCheck_1899_ == 0)
{
lean_object* v_unused_1900_; 
v_unused_1900_ = lean_ctor_get(v___x_1892_, 0);
lean_dec(v_unused_1900_);
v___x_1894_ = v___x_1892_;
v_isShared_1895_ = v_isSharedCheck_1899_;
goto v_resetjp_1893_;
}
else
{
lean_dec(v___x_1892_);
v___x_1894_ = lean_box(0);
v_isShared_1895_ = v_isSharedCheck_1899_;
goto v_resetjp_1893_;
}
v_resetjp_1893_:
{
lean_object* v___x_1897_; 
if (v_isShared_1895_ == 0)
{
lean_ctor_set(v___x_1894_, 0, v_a_1886_);
v___x_1897_ = v___x_1894_;
goto v_reusejp_1896_;
}
else
{
lean_object* v_reuseFailAlloc_1898_; 
v_reuseFailAlloc_1898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1898_, 0, v_a_1886_);
v___x_1897_ = v_reuseFailAlloc_1898_;
goto v_reusejp_1896_;
}
v_reusejp_1896_:
{
return v___x_1897_;
}
}
}
}
}
else
{
lean_object* v_a_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1907_; uint8_t v_isShared_1908_; uint8_t v_isSharedCheck_1912_; 
v_a_1903_ = lean_ctor_get(v_r_1885_, 0);
lean_inc(v_a_1903_);
lean_dec_ref_known(v_r_1885_, 1);
v___x_1904_ = lean_box(0);
v___x_1905_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___redArg___lam__0(v___y_1858_, v_isExporting_1865_, v___x_1881_, v___x_1904_);
v_isSharedCheck_1912_ = !lean_is_exclusive(v___x_1905_);
if (v_isSharedCheck_1912_ == 0)
{
lean_object* v_unused_1913_; 
v_unused_1913_ = lean_ctor_get(v___x_1905_, 0);
lean_dec(v_unused_1913_);
v___x_1907_ = v___x_1905_;
v_isShared_1908_ = v_isSharedCheck_1912_;
goto v_resetjp_1906_;
}
else
{
lean_dec(v___x_1905_);
v___x_1907_ = lean_box(0);
v_isShared_1908_ = v_isSharedCheck_1912_;
goto v_resetjp_1906_;
}
v_resetjp_1906_:
{
lean_object* v___x_1910_; 
if (v_isShared_1908_ == 0)
{
lean_ctor_set_tag(v___x_1907_, 1);
lean_ctor_set(v___x_1907_, 0, v_a_1903_);
v___x_1910_ = v___x_1907_;
goto v_reusejp_1909_;
}
else
{
lean_object* v_reuseFailAlloc_1911_; 
v_reuseFailAlloc_1911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1911_, 0, v_a_1903_);
v___x_1910_ = v_reuseFailAlloc_1911_;
goto v_reusejp_1909_;
}
v_reusejp_1909_:
{
return v___x_1910_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___redArg___boxed(lean_object* v_x_1919_, lean_object* v_isExporting_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_){
_start:
{
uint8_t v_isExporting_boxed_1924_; lean_object* v_res_1925_; 
v_isExporting_boxed_1924_ = lean_unbox(v_isExporting_1920_);
v_res_1925_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___redArg(v_x_1919_, v_isExporting_boxed_1924_, v___y_1921_, v___y_1922_);
lean_dec(v___y_1922_);
lean_dec_ref(v___y_1921_);
return v_res_1925_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3___redArg(lean_object* v_x_1926_, uint8_t v_when_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_){
_start:
{
if (v_when_1927_ == 0)
{
lean_object* v___x_1931_; 
lean_inc(v___y_1929_);
lean_inc_ref(v___y_1928_);
v___x_1931_ = lean_apply_3(v_x_1926_, v___y_1928_, v___y_1929_, lean_box(0));
return v___x_1931_;
}
else
{
uint8_t v___x_1932_; lean_object* v___x_1933_; 
v___x_1932_ = 0;
v___x_1933_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___redArg(v_x_1926_, v___x_1932_, v___y_1928_, v___y_1929_);
return v___x_1933_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3___redArg___boxed(lean_object* v_x_1934_, lean_object* v_when_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_){
_start:
{
uint8_t v_when_boxed_1939_; lean_object* v_res_1940_; 
v_when_boxed_1939_ = lean_unbox(v_when_1935_);
v_res_1940_ = l_Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3___redArg(v_x_1934_, v_when_boxed_1939_, v___y_1936_, v___y_1937_);
lean_dec(v___y_1937_);
lean_dec_ref(v___y_1936_);
return v_res_1940_;
}
}
static lean_object* _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___closed__2(void){
_start:
{
lean_object* v___x_1944_; lean_object* v___x_1945_; 
v___x_1944_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_validate___closed__1));
v___x_1945_ = l_Lean_MessageData_ofFormat(v___x_1944_);
return v___x_1945_;
}
}
static lean_object* _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___closed__3(void){
_start:
{
lean_object* v___x_1946_; lean_object* v_suffix_1947_; 
v___x_1946_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_validate___closed__2, &l___private_Lean_ReducibilityAttrs_0__Lean_validate___closed__2_once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___closed__2);
v_suffix_1947_ = l_Lean_MessageData_note(v___x_1946_);
return v_suffix_1947_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_validate(lean_object* v_declName_1948_, uint8_t v_status_1949_, uint8_t v_attrKind_1950_, lean_object* v_a_1951_, lean_object* v_a_1952_){
_start:
{
lean_object* v_suffix_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___f_1957_; uint8_t v___x_1958_; lean_object* v___x_1959_; 
v_suffix_1954_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_validate___closed__3, &l___private_Lean_ReducibilityAttrs_0__Lean_validate___closed__3_once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___closed__3);
v___x_1955_ = lean_box(v_status_1949_);
v___x_1956_ = lean_box(v_attrKind_1950_);
v___f_1957_ = lean_alloc_closure((void*)(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___boxed), 7, 4);
lean_closure_set(v___f_1957_, 0, v___x_1955_);
lean_closure_set(v___f_1957_, 1, v_declName_1948_);
lean_closure_set(v___f_1957_, 2, v_suffix_1954_);
lean_closure_set(v___f_1957_, 3, v___x_1956_);
v___x_1958_ = 1;
v___x_1959_ = l_Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3___redArg(v___f_1957_, v___x_1958_, v_a_1951_, v_a_1952_);
return v___x_1959_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_validate___boxed(lean_object* v_declName_1960_, lean_object* v_status_1961_, lean_object* v_attrKind_1962_, lean_object* v_a_1963_, lean_object* v_a_1964_, lean_object* v_a_1965_){
_start:
{
uint8_t v_status_boxed_1966_; uint8_t v_attrKind_boxed_1967_; lean_object* v_res_1968_; 
v_status_boxed_1966_ = lean_unbox(v_status_1961_);
v_attrKind_boxed_1967_ = lean_unbox(v_attrKind_1962_);
v_res_1968_ = l___private_Lean_ReducibilityAttrs_0__Lean_validate(v_declName_1960_, v_status_boxed_1966_, v_attrKind_boxed_1967_, v_a_1963_, v_a_1964_);
lean_dec(v_a_1964_);
lean_dec_ref(v_a_1963_);
return v_res_1968_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1(lean_object* v_00_u03b1_1969_, lean_object* v_msg_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_){
_start:
{
lean_object* v___x_1974_; 
v___x_1974_ = l_Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1___redArg(v_msg_1970_, v___y_1971_, v___y_1972_);
return v___x_1974_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1___boxed(lean_object* v_00_u03b1_1975_, lean_object* v_msg_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_){
_start:
{
lean_object* v_res_1980_; 
v_res_1980_ = l_Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1(v_00_u03b1_1975_, v_msg_1976_, v___y_1977_, v___y_1978_);
lean_dec(v___y_1978_);
lean_dec_ref(v___y_1977_);
return v_res_1980_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5(lean_object* v_00_u03b1_1981_, lean_object* v_x_1982_, uint8_t v_isExporting_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_){
_start:
{
lean_object* v___x_1987_; 
v___x_1987_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___redArg(v_x_1982_, v_isExporting_1983_, v___y_1984_, v___y_1985_);
return v___x_1987_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___boxed(lean_object* v_00_u03b1_1988_, lean_object* v_x_1989_, lean_object* v_isExporting_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_){
_start:
{
uint8_t v_isExporting_boxed_1994_; lean_object* v_res_1995_; 
v_isExporting_boxed_1994_ = lean_unbox(v_isExporting_1990_);
v_res_1995_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5(v_00_u03b1_1988_, v_x_1989_, v_isExporting_boxed_1994_, v___y_1991_, v___y_1992_);
lean_dec(v___y_1992_);
lean_dec_ref(v___y_1991_);
return v_res_1995_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3(lean_object* v_00_u03b1_1996_, lean_object* v_x_1997_, uint8_t v_when_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_){
_start:
{
lean_object* v___x_2002_; 
v___x_2002_ = l_Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3___redArg(v_x_1997_, v_when_1998_, v___y_1999_, v___y_2000_);
return v___x_2002_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3___boxed(lean_object* v_00_u03b1_2003_, lean_object* v_x_2004_, lean_object* v_when_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_){
_start:
{
uint8_t v_when_boxed_2009_; lean_object* v_res_2010_; 
v_when_boxed_2009_ = lean_unbox(v_when_2005_);
v_res_2010_ = l_Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3(v_00_u03b1_2003_, v_x_2004_, v_when_boxed_2009_, v___y_2006_, v___y_2007_);
lean_dec(v___y_2007_);
lean_dec_ref(v___y_2006_);
return v_res_2010_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3(lean_object* v_00_u03b1_2011_, lean_object* v_constName_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_){
_start:
{
lean_object* v___x_2016_; 
v___x_2016_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3___redArg(v_constName_2012_, v___y_2013_, v___y_2014_);
return v___x_2016_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3___boxed(lean_object* v_00_u03b1_2017_, lean_object* v_constName_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_){
_start:
{
lean_object* v_res_2022_; 
v_res_2022_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3(v_00_u03b1_2017_, v_constName_2018_, v___y_2019_, v___y_2020_);
lean_dec(v___y_2020_);
lean_dec_ref(v___y_2019_);
return v_res_2022_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4(lean_object* v_00_u03b1_2023_, lean_object* v_ref_2024_, lean_object* v_constName_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_){
_start:
{
lean_object* v___x_2029_; 
v___x_2029_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg(v_ref_2024_, v_constName_2025_, v___y_2026_, v___y_2027_);
return v___x_2029_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___boxed(lean_object* v_00_u03b1_2030_, lean_object* v_ref_2031_, lean_object* v_constName_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_){
_start:
{
lean_object* v_res_2036_; 
v_res_2036_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4(v_00_u03b1_2030_, v_ref_2031_, v_constName_2032_, v___y_2033_, v___y_2034_);
lean_dec(v___y_2034_);
lean_dec_ref(v___y_2033_);
lean_dec(v_ref_2031_);
return v_res_2036_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7(lean_object* v_00_u03b1_2037_, lean_object* v_ref_2038_, lean_object* v_msg_2039_, lean_object* v_declHint_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_){
_start:
{
lean_object* v___x_2044_; 
v___x_2044_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7___redArg(v_ref_2038_, v_msg_2039_, v_declHint_2040_, v___y_2041_, v___y_2042_);
return v___x_2044_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7___boxed(lean_object* v_00_u03b1_2045_, lean_object* v_ref_2046_, lean_object* v_msg_2047_, lean_object* v_declHint_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_){
_start:
{
lean_object* v_res_2052_; 
v_res_2052_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7(v_00_u03b1_2045_, v_ref_2046_, v_msg_2047_, v_declHint_2048_, v___y_2049_, v___y_2050_);
lean_dec(v___y_2050_);
lean_dec_ref(v___y_2049_);
lean_dec(v_ref_2046_);
return v_res_2052_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9(lean_object* v_msg_2053_, lean_object* v_declHint_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_){
_start:
{
lean_object* v___x_2058_; 
v___x_2058_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg(v_msg_2053_, v_declHint_2054_, v___y_2056_);
return v___x_2058_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___boxed(lean_object* v_msg_2059_, lean_object* v_declHint_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_){
_start:
{
lean_object* v_res_2064_; 
v_res_2064_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9(v_msg_2059_, v_declHint_2060_, v___y_2061_, v___y_2062_);
lean_dec(v___y_2062_);
lean_dec_ref(v___y_2061_);
return v_res_2064_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__9(lean_object* v_00_u03b1_2065_, lean_object* v_ref_2066_, lean_object* v_msg_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_){
_start:
{
lean_object* v___x_2071_; 
v___x_2071_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__9___redArg(v_ref_2066_, v_msg_2067_, v___y_2068_, v___y_2069_);
return v___x_2071_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__9___boxed(lean_object* v_00_u03b1_2072_, lean_object* v_ref_2073_, lean_object* v_msg_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_){
_start:
{
lean_object* v_res_2078_; 
v_res_2078_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__9(v_00_u03b1_2072_, v_ref_2073_, v_msg_2074_, v___y_2075_, v___y_2076_);
lean_dec(v___y_2076_);
lean_dec_ref(v___y_2075_);
lean_dec(v_ref_2073_);
return v_res_2078_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_addAttr(uint8_t v_status_2079_, lean_object* v_declName_2080_, lean_object* v_stx_2081_, uint8_t v_attrKind_2082_, lean_object* v_a_2083_, lean_object* v_a_2084_){
_start:
{
lean_object* v___x_2086_; 
v___x_2086_ = l_Lean_Attribute_Builtin_ensureNoArgs(v_stx_2081_, v_a_2083_, v_a_2084_);
if (lean_obj_tag(v___x_2086_) == 0)
{
lean_object* v___x_2087_; 
lean_dec_ref_known(v___x_2086_, 1);
lean_inc(v_declName_2080_);
v___x_2087_ = l___private_Lean_ReducibilityAttrs_0__Lean_validate(v_declName_2080_, v_status_2079_, v_attrKind_2082_, v_a_2083_, v_a_2084_);
if (lean_obj_tag(v___x_2087_) == 0)
{
lean_object* v___x_2089_; uint8_t v_isShared_2090_; uint8_t v_isSharedCheck_2118_; 
v_isSharedCheck_2118_ = !lean_is_exclusive(v___x_2087_);
if (v_isSharedCheck_2118_ == 0)
{
lean_object* v_unused_2119_; 
v_unused_2119_ = lean_ctor_get(v___x_2087_, 0);
lean_dec(v_unused_2119_);
v___x_2089_ = v___x_2087_;
v_isShared_2090_ = v_isSharedCheck_2118_;
goto v_resetjp_2088_;
}
else
{
lean_dec(v___x_2087_);
v___x_2089_ = lean_box(0);
v_isShared_2090_ = v_isSharedCheck_2118_;
goto v_resetjp_2088_;
}
v_resetjp_2088_:
{
lean_object* v_toCold_2091_; lean_object* v_currNamespace_2092_; lean_object* v___x_2093_; lean_object* v_env_2094_; lean_object* v_nextMacroScope_2095_; lean_object* v_ngen_2096_; lean_object* v_auxDeclNGen_2097_; lean_object* v_traceState_2098_; lean_object* v_recordedDeps_2099_; lean_object* v_messages_2100_; lean_object* v_infoState_2101_; lean_object* v_snapshotTasks_2102_; lean_object* v___x_2104_; uint8_t v_isShared_2105_; uint8_t v_isSharedCheck_2116_; 
v_toCold_2091_ = lean_ctor_get(v_a_2083_, 0);
v_currNamespace_2092_ = lean_ctor_get(v_toCold_2091_, 4);
v___x_2093_ = lean_st_ref_take(v_a_2084_);
v_env_2094_ = lean_ctor_get(v___x_2093_, 0);
v_nextMacroScope_2095_ = lean_ctor_get(v___x_2093_, 1);
v_ngen_2096_ = lean_ctor_get(v___x_2093_, 2);
v_auxDeclNGen_2097_ = lean_ctor_get(v___x_2093_, 3);
v_traceState_2098_ = lean_ctor_get(v___x_2093_, 4);
v_recordedDeps_2099_ = lean_ctor_get(v___x_2093_, 6);
v_messages_2100_ = lean_ctor_get(v___x_2093_, 7);
v_infoState_2101_ = lean_ctor_get(v___x_2093_, 8);
v_snapshotTasks_2102_ = lean_ctor_get(v___x_2093_, 9);
v_isSharedCheck_2116_ = !lean_is_exclusive(v___x_2093_);
if (v_isSharedCheck_2116_ == 0)
{
lean_object* v_unused_2117_; 
v_unused_2117_ = lean_ctor_get(v___x_2093_, 5);
lean_dec(v_unused_2117_);
v___x_2104_ = v___x_2093_;
v_isShared_2105_ = v_isSharedCheck_2116_;
goto v_resetjp_2103_;
}
else
{
lean_inc(v_snapshotTasks_2102_);
lean_inc(v_infoState_2101_);
lean_inc(v_messages_2100_);
lean_inc(v_recordedDeps_2099_);
lean_inc(v_traceState_2098_);
lean_inc(v_auxDeclNGen_2097_);
lean_inc(v_ngen_2096_);
lean_inc(v_nextMacroScope_2095_);
lean_inc(v_env_2094_);
lean_dec(v___x_2093_);
v___x_2104_ = lean_box(0);
v_isShared_2105_ = v_isSharedCheck_2116_;
goto v_resetjp_2103_;
}
v_resetjp_2103_:
{
lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2110_; 
v___x_2106_ = lean_box(0);
lean_inc(v_currNamespace_2092_);
v___x_2107_ = l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(v_env_2094_, v_declName_2080_, v_status_2079_, v_attrKind_2082_, v_currNamespace_2092_);
v___x_2108_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___redArg___closed__1, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___redArg___closed__1);
if (v_isShared_2105_ == 0)
{
lean_ctor_set(v___x_2104_, 5, v___x_2108_);
lean_ctor_set(v___x_2104_, 0, v___x_2107_);
v___x_2110_ = v___x_2104_;
goto v_reusejp_2109_;
}
else
{
lean_object* v_reuseFailAlloc_2115_; 
v_reuseFailAlloc_2115_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2115_, 0, v___x_2107_);
lean_ctor_set(v_reuseFailAlloc_2115_, 1, v_nextMacroScope_2095_);
lean_ctor_set(v_reuseFailAlloc_2115_, 2, v_ngen_2096_);
lean_ctor_set(v_reuseFailAlloc_2115_, 3, v_auxDeclNGen_2097_);
lean_ctor_set(v_reuseFailAlloc_2115_, 4, v_traceState_2098_);
lean_ctor_set(v_reuseFailAlloc_2115_, 5, v___x_2108_);
lean_ctor_set(v_reuseFailAlloc_2115_, 6, v_recordedDeps_2099_);
lean_ctor_set(v_reuseFailAlloc_2115_, 7, v_messages_2100_);
lean_ctor_set(v_reuseFailAlloc_2115_, 8, v_infoState_2101_);
lean_ctor_set(v_reuseFailAlloc_2115_, 9, v_snapshotTasks_2102_);
v___x_2110_ = v_reuseFailAlloc_2115_;
goto v_reusejp_2109_;
}
v_reusejp_2109_:
{
lean_object* v___x_2111_; lean_object* v___x_2113_; 
v___x_2111_ = lean_st_ref_put(v_a_2084_, v___x_2110_);
if (v_isShared_2090_ == 0)
{
lean_ctor_set(v___x_2089_, 0, v___x_2106_);
v___x_2113_ = v___x_2089_;
goto v_reusejp_2112_;
}
else
{
lean_object* v_reuseFailAlloc_2114_; 
v_reuseFailAlloc_2114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2114_, 0, v___x_2106_);
v___x_2113_ = v_reuseFailAlloc_2114_;
goto v_reusejp_2112_;
}
v_reusejp_2112_:
{
return v___x_2113_;
}
}
}
}
}
else
{
lean_dec(v_declName_2080_);
return v___x_2087_;
}
}
else
{
lean_dec(v_declName_2080_);
return v___x_2086_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_addAttr___boxed(lean_object* v_status_2120_, lean_object* v_declName_2121_, lean_object* v_stx_2122_, lean_object* v_attrKind_2123_, lean_object* v_a_2124_, lean_object* v_a_2125_, lean_object* v_a_2126_){
_start:
{
uint8_t v_status_boxed_2127_; uint8_t v_attrKind_boxed_2128_; lean_object* v_res_2129_; 
v_status_boxed_2127_ = lean_unbox(v_status_2120_);
v_attrKind_boxed_2128_ = lean_unbox(v_attrKind_2123_);
v_res_2129_ = l___private_Lean_ReducibilityAttrs_0__Lean_addAttr(v_status_boxed_2127_, v_declName_2121_, v_stx_2122_, v_attrKind_boxed_2128_, v_a_2124_, v_a_2125_);
lean_dec(v_a_2125_);
lean_dec_ref(v_a_2124_);
return v_res_2129_;
}
}
static lean_object* _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2131_; lean_object* v___x_2132_; 
v___x_2131_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_));
v___x_2132_ = l_Lean_stringToMessageData(v___x_2131_);
return v___x_2132_;
}
}
static lean_object* _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__0___closed__3_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2134_; lean_object* v___x_2135_; 
v___x_2134_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__0___closed__2_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_));
v___x_2135_ = l_Lean_stringToMessageData(v___x_2134_);
return v___x_2135_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__0_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_(lean_object* v___x_2136_, lean_object* v_decl_2137_, lean_object* v___y_2138_, lean_object* v___y_2139_){
_start:
{
lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; 
v___x_2141_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_, &l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_);
v___x_2142_ = l_Lean_MessageData_ofName(v___x_2136_);
v___x_2143_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2143_, 0, v___x_2141_);
lean_ctor_set(v___x_2143_, 1, v___x_2142_);
v___x_2144_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__0___closed__3_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_, &l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__0___closed__3_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__0___closed__3_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_);
v___x_2145_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2145_, 0, v___x_2143_);
lean_ctor_set(v___x_2145_, 1, v___x_2144_);
v___x_2146_ = l_Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1___redArg(v___x_2145_, v___y_2138_, v___y_2139_);
return v___x_2146_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__0_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2____boxed(lean_object* v___x_2147_, lean_object* v_decl_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_){
_start:
{
lean_object* v_res_2152_; 
v_res_2152_ = l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__0_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_(v___x_2147_, v_decl_2148_, v___y_2149_, v___y_2150_);
lean_dec(v___y_2150_);
lean_dec_ref(v___y_2149_);
lean_dec(v_decl_2148_);
return v_res_2152_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2217_; lean_object* v___x_2218_; 
v___x_2217_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__25_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_));
v___x_2218_ = l_Lean_registerBuiltinAttribute(v___x_2217_);
return v___x_2218_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2____boxed(lean_object* v_a_2219_){
_start:
{
lean_object* v_res_2220_; 
v_res_2220_ = l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_();
return v_res_2220_;
}
}
static lean_object* _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; 
v___x_2221_ = lean_unsigned_to_nat(4118757939u);
v___x_2222_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__12_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_));
v___x_2223_ = l_Lean_Name_num___override(v___x_2222_, v___x_2221_);
return v___x_2223_;
}
}
static lean_object* _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; 
v___x_2224_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__14_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_));
v___x_2225_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_, &l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2__once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_);
v___x_2226_ = l_Lean_Name_str___override(v___x_2225_, v___x_2224_);
return v___x_2226_;
}
}
static lean_object* _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; 
v___x_2227_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__16_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_));
v___x_2228_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_, &l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2__once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_);
v___x_2229_ = l_Lean_Name_str___override(v___x_2228_, v___x_2227_);
return v___x_2229_;
}
}
static lean_object* _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; 
v___x_2230_ = lean_unsigned_to_nat(2u);
v___x_2231_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_, &l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2__once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_);
v___x_2232_ = l_Lean_Name_num___override(v___x_2231_, v___x_2230_);
return v___x_2232_;
}
}
static lean_object* _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__8_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_(void){
_start:
{
uint8_t v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; 
v___x_2239_ = 0;
v___x_2240_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__7_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_));
v___x_2241_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_));
v___x_2242_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_, &l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2__once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_);
v___x_2243_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2243_, 0, v___x_2242_);
lean_ctor_set(v___x_2243_, 1, v___x_2241_);
lean_ctor_set(v___x_2243_, 2, v___x_2240_);
lean_ctor_set_uint8(v___x_2243_, sizeof(void*)*3, v___x_2239_);
return v___x_2243_;
}
}
static lean_object* _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__10_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; 
v___f_2247_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__6_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_));
v___x_2248_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__9_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_));
v___x_2249_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__8_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_, &l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__8_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2__once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__8_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_);
v___x_2250_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2250_, 0, v___x_2249_);
lean_ctor_set(v___x_2250_, 1, v___x_2248_);
lean_ctor_set(v___x_2250_, 2, v___f_2247_);
return v___x_2250_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2252_; lean_object* v___x_2253_; 
v___x_2252_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__10_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_, &l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__10_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2__once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__10_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_);
v___x_2253_ = l_Lean_registerBuiltinAttribute(v___x_2252_);
return v___x_2253_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2____boxed(lean_object* v_a_2254_){
_start:
{
lean_object* v_res_2255_; 
v_res_2255_ = l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_();
return v_res_2255_;
}
}
static lean_object* _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; 
v___x_2256_ = lean_unsigned_to_nat(2994861043u);
v___x_2257_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__12_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_));
v___x_2258_ = l_Lean_Name_num___override(v___x_2257_, v___x_2256_);
return v___x_2258_;
}
}
static lean_object* _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; 
v___x_2259_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__14_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_));
v___x_2260_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_, &l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2__once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_);
v___x_2261_ = l_Lean_Name_str___override(v___x_2260_, v___x_2259_);
return v___x_2261_;
}
}
static lean_object* _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; 
v___x_2262_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__16_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_));
v___x_2263_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_, &l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2__once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_);
v___x_2264_ = l_Lean_Name_str___override(v___x_2263_, v___x_2262_);
return v___x_2264_;
}
}
static lean_object* _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; 
v___x_2265_ = lean_unsigned_to_nat(2u);
v___x_2266_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_, &l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2__once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_);
v___x_2267_ = l_Lean_Name_num___override(v___x_2266_, v___x_2265_);
return v___x_2267_;
}
}
static lean_object* _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__8_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_(void){
_start:
{
uint8_t v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; 
v___x_2274_ = 0;
v___x_2275_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__7_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_));
v___x_2276_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_));
v___x_2277_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_, &l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2__once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_);
v___x_2278_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2278_, 0, v___x_2277_);
lean_ctor_set(v___x_2278_, 1, v___x_2276_);
lean_ctor_set(v___x_2278_, 2, v___x_2275_);
lean_ctor_set_uint8(v___x_2278_, sizeof(void*)*3, v___x_2274_);
return v___x_2278_;
}
}
static lean_object* _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__10_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; 
v___f_2282_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__6_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_));
v___x_2283_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__9_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_));
v___x_2284_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__8_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_, &l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__8_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2__once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__8_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_);
v___x_2285_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2285_, 0, v___x_2284_);
lean_ctor_set(v___x_2285_, 1, v___x_2283_);
lean_ctor_set(v___x_2285_, 2, v___f_2282_);
return v___x_2285_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2287_; lean_object* v___x_2288_; 
v___x_2287_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__10_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_, &l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__10_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2__once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__10_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_);
v___x_2288_ = l_Lean_registerBuiltinAttribute(v___x_2287_);
return v___x_2288_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2____boxed(lean_object* v_a_2289_){
_start:
{
lean_object* v_res_2290_; 
v_res_2290_ = l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_();
return v_res_2290_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_82891871____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2322_; lean_object* v___x_2323_; 
v___x_2322_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__10_00___x40_Lean_ReducibilityAttrs_82891871____hygCtx___hyg_2_));
v___x_2323_ = l_Lean_registerBuiltinAttribute(v___x_2322_);
return v___x_2323_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_82891871____hygCtx___hyg_2____boxed(lean_object* v_a_2324_){
_start:
{
lean_object* v_res_2325_; 
v_res_2325_ = l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_82891871____hygCtx___hyg_2_();
return v_res_2325_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_2104212786____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2357_; lean_object* v___x_2358_; 
v___x_2357_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__10_00___x40_Lean_ReducibilityAttrs_2104212786____hygCtx___hyg_2_));
v___x_2358_ = l_Lean_registerBuiltinAttribute(v___x_2357_);
return v___x_2358_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_2104212786____hygCtx___hyg_2____boxed(lean_object* v_a_2359_){
_start:
{
lean_object* v_res_2360_; 
v_res_2360_ = l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_2104212786____hygCtx___hyg_2_();
return v_res_2360_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___redArg___lam__0(lean_object* v_declName_2361_, lean_object* v_toPure_2362_, lean_object* v_____do__lift_2363_){
_start:
{
uint8_t v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; 
v___x_2364_ = l_Lean_getReducibilityStatusCore(v_____do__lift_2363_, v_declName_2361_);
v___x_2365_ = lean_box(v___x_2364_);
v___x_2366_ = lean_apply_2(v_toPure_2362_, lean_box(0), v___x_2365_);
return v___x_2366_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___redArg(lean_object* v_inst_2367_, lean_object* v_inst_2368_, lean_object* v_declName_2369_){
_start:
{
lean_object* v_toApplicative_2370_; lean_object* v_toBind_2371_; lean_object* v_getEnv_2372_; lean_object* v_toPure_2373_; lean_object* v___f_2374_; lean_object* v___x_2375_; 
v_toApplicative_2370_ = lean_ctor_get(v_inst_2367_, 0);
lean_inc_ref(v_toApplicative_2370_);
v_toBind_2371_ = lean_ctor_get(v_inst_2367_, 1);
lean_inc(v_toBind_2371_);
lean_dec_ref(v_inst_2367_);
v_getEnv_2372_ = lean_ctor_get(v_inst_2368_, 0);
lean_inc(v_getEnv_2372_);
lean_dec_ref(v_inst_2368_);
v_toPure_2373_ = lean_ctor_get(v_toApplicative_2370_, 1);
lean_inc(v_toPure_2373_);
lean_dec_ref(v_toApplicative_2370_);
v___f_2374_ = lean_alloc_closure((void*)(l_Lean_getReducibilityStatus___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2374_, 0, v_declName_2369_);
lean_closure_set(v___f_2374_, 1, v_toPure_2373_);
v___x_2375_ = lean_apply_4(v_toBind_2371_, lean_box(0), lean_box(0), v_getEnv_2372_, v___f_2374_);
return v___x_2375_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus(lean_object* v_m_2376_, lean_object* v_inst_2377_, lean_object* v_inst_2378_, lean_object* v_declName_2379_){
_start:
{
lean_object* v___x_2380_; 
v___x_2380_ = l_Lean_getReducibilityStatus___redArg(v_inst_2377_, v_inst_2378_, v_declName_2379_);
return v___x_2380_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___redArg___lam__0(lean_object* v_declName_2381_, uint8_t v_s_2382_, lean_object* v_env_2383_){
_start:
{
uint8_t v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; 
v___x_2384_ = 0;
v___x_2385_ = lean_box(0);
v___x_2386_ = l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(v_env_2383_, v_declName_2381_, v_s_2382_, v___x_2384_, v___x_2385_);
return v___x_2386_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___redArg___lam__0___boxed(lean_object* v_declName_2387_, lean_object* v_s_2388_, lean_object* v_env_2389_){
_start:
{
uint8_t v_s_boxed_2390_; lean_object* v_res_2391_; 
v_s_boxed_2390_ = lean_unbox(v_s_2388_);
v_res_2391_ = l_Lean_setReducibilityStatus___redArg___lam__0(v_declName_2387_, v_s_boxed_2390_, v_env_2389_);
return v_res_2391_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___redArg(lean_object* v_inst_2392_, lean_object* v_declName_2393_, uint8_t v_s_2394_){
_start:
{
lean_object* v_modifyEnv_2395_; lean_object* v___x_2396_; lean_object* v___f_2397_; lean_object* v___x_2398_; 
v_modifyEnv_2395_ = lean_ctor_get(v_inst_2392_, 1);
lean_inc(v_modifyEnv_2395_);
lean_dec_ref(v_inst_2392_);
v___x_2396_ = lean_box(v_s_2394_);
v___f_2397_ = lean_alloc_closure((void*)(l_Lean_setReducibilityStatus___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2397_, 0, v_declName_2393_);
lean_closure_set(v___f_2397_, 1, v___x_2396_);
v___x_2398_ = lean_apply_1(v_modifyEnv_2395_, v___f_2397_);
return v___x_2398_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___redArg___boxed(lean_object* v_inst_2399_, lean_object* v_declName_2400_, lean_object* v_s_2401_){
_start:
{
uint8_t v_s_boxed_2402_; lean_object* v_res_2403_; 
v_s_boxed_2402_ = lean_unbox(v_s_2401_);
v_res_2403_ = l_Lean_setReducibilityStatus___redArg(v_inst_2399_, v_declName_2400_, v_s_boxed_2402_);
return v_res_2403_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus(lean_object* v_m_2404_, lean_object* v_inst_2405_, lean_object* v_declName_2406_, uint8_t v_s_2407_){
_start:
{
lean_object* v___x_2408_; 
v___x_2408_ = l_Lean_setReducibilityStatus___redArg(v_inst_2405_, v_declName_2406_, v_s_2407_);
return v___x_2408_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___boxed(lean_object* v_m_2409_, lean_object* v_inst_2410_, lean_object* v_declName_2411_, lean_object* v_s_2412_){
_start:
{
uint8_t v_s_boxed_2413_; lean_object* v_res_2414_; 
v_s_boxed_2413_ = lean_unbox(v_s_2412_);
v_res_2414_ = l_Lean_setReducibilityStatus(v_m_2409_, v_inst_2410_, v_declName_2411_, v_s_boxed_2413_);
return v_res_2414_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___redArg(lean_object* v_inst_2415_, lean_object* v_declName_2416_){
_start:
{
uint8_t v___x_2417_; lean_object* v___x_2418_; 
v___x_2417_ = 0;
v___x_2418_ = l_Lean_setReducibilityStatus___redArg(v_inst_2415_, v_declName_2416_, v___x_2417_);
return v___x_2418_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute(lean_object* v_m_2419_, lean_object* v_inst_2420_, lean_object* v_declName_2421_){
_start:
{
lean_object* v___x_2422_; 
v___x_2422_ = l_Lean_setReducibleAttribute___redArg(v_inst_2420_, v_declName_2421_);
return v___x_2422_;
}
}
LEAN_EXPORT lean_object* l_Lean_isReducible___redArg___lam__0(lean_object* v_toPure_2423_, uint8_t v_____do__lift_2424_){
_start:
{
if (v_____do__lift_2424_ == 0)
{
uint8_t v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; 
v___x_2425_ = 1;
v___x_2426_ = lean_box(v___x_2425_);
v___x_2427_ = lean_apply_2(v_toPure_2423_, lean_box(0), v___x_2426_);
return v___x_2427_;
}
else
{
uint8_t v___x_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; 
v___x_2428_ = 0;
v___x_2429_ = lean_box(v___x_2428_);
v___x_2430_ = lean_apply_2(v_toPure_2423_, lean_box(0), v___x_2429_);
return v___x_2430_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isReducible___redArg___lam__0___boxed(lean_object* v_toPure_2431_, lean_object* v_____do__lift_2432_){
_start:
{
uint8_t v_____do__lift_48__boxed_2433_; lean_object* v_res_2434_; 
v_____do__lift_48__boxed_2433_ = lean_unbox(v_____do__lift_2432_);
v_res_2434_ = l_Lean_isReducible___redArg___lam__0(v_toPure_2431_, v_____do__lift_48__boxed_2433_);
return v_res_2434_;
}
}
LEAN_EXPORT lean_object* l_Lean_isReducible___redArg(lean_object* v_inst_2435_, lean_object* v_inst_2436_, lean_object* v_declName_2437_){
_start:
{
lean_object* v_toApplicative_2438_; lean_object* v_toBind_2439_; lean_object* v_toPure_2440_; lean_object* v___x_2441_; lean_object* v___f_2442_; lean_object* v___x_2443_; 
v_toApplicative_2438_ = lean_ctor_get(v_inst_2435_, 0);
v_toBind_2439_ = lean_ctor_get(v_inst_2435_, 1);
lean_inc(v_toBind_2439_);
v_toPure_2440_ = lean_ctor_get(v_toApplicative_2438_, 1);
lean_inc(v_toPure_2440_);
v___x_2441_ = l_Lean_getReducibilityStatus___redArg(v_inst_2435_, v_inst_2436_, v_declName_2437_);
v___f_2442_ = lean_alloc_closure((void*)(l_Lean_isReducible___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2442_, 0, v_toPure_2440_);
v___x_2443_ = lean_apply_4(v_toBind_2439_, lean_box(0), lean_box(0), v___x_2441_, v___f_2442_);
return v___x_2443_;
}
}
LEAN_EXPORT lean_object* l_Lean_isReducible(lean_object* v_m_2444_, lean_object* v_inst_2445_, lean_object* v_inst_2446_, lean_object* v_declName_2447_){
_start:
{
lean_object* v___x_2448_; 
v___x_2448_ = l_Lean_isReducible___redArg(v_inst_2445_, v_inst_2446_, v_declName_2447_);
return v___x_2448_;
}
}
LEAN_EXPORT lean_object* l_Lean_isIrreducible___redArg___lam__0(lean_object* v_toPure_2449_, uint8_t v_____do__lift_2450_){
_start:
{
if (v_____do__lift_2450_ == 2)
{
uint8_t v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; 
v___x_2451_ = 1;
v___x_2452_ = lean_box(v___x_2451_);
v___x_2453_ = lean_apply_2(v_toPure_2449_, lean_box(0), v___x_2452_);
return v___x_2453_;
}
else
{
uint8_t v___x_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; 
v___x_2454_ = 0;
v___x_2455_ = lean_box(v___x_2454_);
v___x_2456_ = lean_apply_2(v_toPure_2449_, lean_box(0), v___x_2455_);
return v___x_2456_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isIrreducible___redArg___lam__0___boxed(lean_object* v_toPure_2457_, lean_object* v_____do__lift_2458_){
_start:
{
uint8_t v_____do__lift_48__boxed_2459_; lean_object* v_res_2460_; 
v_____do__lift_48__boxed_2459_ = lean_unbox(v_____do__lift_2458_);
v_res_2460_ = l_Lean_isIrreducible___redArg___lam__0(v_toPure_2457_, v_____do__lift_48__boxed_2459_);
return v_res_2460_;
}
}
LEAN_EXPORT lean_object* l_Lean_isIrreducible___redArg(lean_object* v_inst_2461_, lean_object* v_inst_2462_, lean_object* v_declName_2463_){
_start:
{
lean_object* v_toApplicative_2464_; lean_object* v_toBind_2465_; lean_object* v_toPure_2466_; lean_object* v___x_2467_; lean_object* v___f_2468_; lean_object* v___x_2469_; 
v_toApplicative_2464_ = lean_ctor_get(v_inst_2461_, 0);
v_toBind_2465_ = lean_ctor_get(v_inst_2461_, 1);
lean_inc(v_toBind_2465_);
v_toPure_2466_ = lean_ctor_get(v_toApplicative_2464_, 1);
lean_inc(v_toPure_2466_);
v___x_2467_ = l_Lean_getReducibilityStatus___redArg(v_inst_2461_, v_inst_2462_, v_declName_2463_);
v___f_2468_ = lean_alloc_closure((void*)(l_Lean_isIrreducible___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2468_, 0, v_toPure_2466_);
v___x_2469_ = lean_apply_4(v_toBind_2465_, lean_box(0), lean_box(0), v___x_2467_, v___f_2468_);
return v___x_2469_;
}
}
LEAN_EXPORT lean_object* l_Lean_isIrreducible(lean_object* v_m_2470_, lean_object* v_inst_2471_, lean_object* v_inst_2472_, lean_object* v_declName_2473_){
_start:
{
lean_object* v___x_2474_; 
v___x_2474_ = l_Lean_isIrreducible___redArg(v_inst_2471_, v_inst_2472_, v_declName_2473_);
return v___x_2474_;
}
}
LEAN_EXPORT uint8_t l_Lean_isImplicitReducibleCore(lean_object* v_env_2475_, lean_object* v_declName_2476_){
_start:
{
uint8_t v___x_2477_; 
v___x_2477_ = l_Lean_getReducibilityStatusCore(v_env_2475_, v_declName_2476_);
if (v___x_2477_ == 3)
{
uint8_t v___x_2478_; 
v___x_2478_ = 1;
return v___x_2478_;
}
else
{
uint8_t v___x_2479_; 
v___x_2479_ = 0;
return v___x_2479_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isImplicitReducibleCore___boxed(lean_object* v_env_2480_, lean_object* v_declName_2481_){
_start:
{
uint8_t v_res_2482_; lean_object* v_r_2483_; 
v_res_2482_ = l_Lean_isImplicitReducibleCore(v_env_2480_, v_declName_2481_);
v_r_2483_ = lean_box(v_res_2482_);
return v_r_2483_;
}
}
LEAN_EXPORT lean_object* l_Lean_isImplicitReducible___redArg___lam__0(lean_object* v_declName_2484_, lean_object* v_toPure_2485_, lean_object* v_____do__lift_2486_){
_start:
{
uint8_t v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; 
v___x_2487_ = l_Lean_isImplicitReducibleCore(v_____do__lift_2486_, v_declName_2484_);
v___x_2488_ = lean_box(v___x_2487_);
v___x_2489_ = lean_apply_2(v_toPure_2485_, lean_box(0), v___x_2488_);
return v___x_2489_;
}
}
LEAN_EXPORT lean_object* l_Lean_isImplicitReducible___redArg(lean_object* v_inst_2490_, lean_object* v_inst_2491_, lean_object* v_declName_2492_){
_start:
{
lean_object* v_toApplicative_2493_; lean_object* v_toBind_2494_; lean_object* v_getEnv_2495_; lean_object* v_toPure_2496_; lean_object* v___f_2497_; lean_object* v___x_2498_; 
v_toApplicative_2493_ = lean_ctor_get(v_inst_2490_, 0);
lean_inc_ref(v_toApplicative_2493_);
v_toBind_2494_ = lean_ctor_get(v_inst_2490_, 1);
lean_inc(v_toBind_2494_);
lean_dec_ref(v_inst_2490_);
v_getEnv_2495_ = lean_ctor_get(v_inst_2491_, 0);
lean_inc(v_getEnv_2495_);
lean_dec_ref(v_inst_2491_);
v_toPure_2496_ = lean_ctor_get(v_toApplicative_2493_, 1);
lean_inc(v_toPure_2496_);
lean_dec_ref(v_toApplicative_2493_);
v___f_2497_ = lean_alloc_closure((void*)(l_Lean_isImplicitReducible___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2497_, 0, v_declName_2492_);
lean_closure_set(v___f_2497_, 1, v_toPure_2496_);
v___x_2498_ = lean_apply_4(v_toBind_2494_, lean_box(0), lean_box(0), v_getEnv_2495_, v___f_2497_);
return v___x_2498_;
}
}
LEAN_EXPORT lean_object* l_Lean_isImplicitReducible(lean_object* v_m_2499_, lean_object* v_inst_2500_, lean_object* v_inst_2501_, lean_object* v_declName_2502_){
_start:
{
lean_object* v___x_2503_; 
v___x_2503_ = l_Lean_isImplicitReducible___redArg(v_inst_2500_, v_inst_2501_, v_declName_2502_);
return v___x_2503_;
}
}
LEAN_EXPORT uint8_t l_Lean_isInstanceReducibleCore(lean_object* v_env_2504_, lean_object* v_declName_2505_){
_start:
{
uint8_t v___x_2506_; 
v___x_2506_ = l_Lean_getReducibilityStatusCore(v_env_2504_, v_declName_2505_);
if (v___x_2506_ == 4)
{
uint8_t v___x_2507_; 
v___x_2507_ = 1;
return v___x_2507_;
}
else
{
uint8_t v___x_2508_; 
v___x_2508_ = 0;
return v___x_2508_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isInstanceReducibleCore___boxed(lean_object* v_env_2509_, lean_object* v_declName_2510_){
_start:
{
uint8_t v_res_2511_; lean_object* v_r_2512_; 
v_res_2511_ = l_Lean_isInstanceReducibleCore(v_env_2509_, v_declName_2510_);
v_r_2512_ = lean_box(v_res_2511_);
return v_r_2512_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInstanceReducible___redArg___lam__0(lean_object* v_declName_2513_, lean_object* v_toPure_2514_, lean_object* v_____do__lift_2515_){
_start:
{
uint8_t v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; 
v___x_2516_ = l_Lean_isInstanceReducibleCore(v_____do__lift_2515_, v_declName_2513_);
v___x_2517_ = lean_box(v___x_2516_);
v___x_2518_ = lean_apply_2(v_toPure_2514_, lean_box(0), v___x_2517_);
return v___x_2518_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInstanceReducible___redArg(lean_object* v_inst_2519_, lean_object* v_inst_2520_, lean_object* v_declName_2521_){
_start:
{
lean_object* v_toApplicative_2522_; lean_object* v_toBind_2523_; lean_object* v_getEnv_2524_; lean_object* v_toPure_2525_; lean_object* v___f_2526_; lean_object* v___x_2527_; 
v_toApplicative_2522_ = lean_ctor_get(v_inst_2519_, 0);
lean_inc_ref(v_toApplicative_2522_);
v_toBind_2523_ = lean_ctor_get(v_inst_2519_, 1);
lean_inc(v_toBind_2523_);
lean_dec_ref(v_inst_2519_);
v_getEnv_2524_ = lean_ctor_get(v_inst_2520_, 0);
lean_inc(v_getEnv_2524_);
lean_dec_ref(v_inst_2520_);
v_toPure_2525_ = lean_ctor_get(v_toApplicative_2522_, 1);
lean_inc(v_toPure_2525_);
lean_dec_ref(v_toApplicative_2522_);
v___f_2526_ = lean_alloc_closure((void*)(l_Lean_isInstanceReducible___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2526_, 0, v_declName_2521_);
lean_closure_set(v___f_2526_, 1, v_toPure_2525_);
v___x_2527_ = lean_apply_4(v_toBind_2523_, lean_box(0), lean_box(0), v_getEnv_2524_, v___f_2526_);
return v___x_2527_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInstanceReducible(lean_object* v_m_2528_, lean_object* v_inst_2529_, lean_object* v_inst_2530_, lean_object* v_declName_2531_){
_start:
{
lean_object* v___x_2532_; 
v___x_2532_ = l_Lean_isInstanceReducible___redArg(v_inst_2529_, v_inst_2530_, v_declName_2531_);
return v___x_2532_;
}
}
LEAN_EXPORT lean_object* l_Lean_setIrreducibleAttribute___redArg(lean_object* v_inst_2533_, lean_object* v_declName_2534_){
_start:
{
uint8_t v___x_2535_; lean_object* v___x_2536_; 
v___x_2535_ = 2;
v___x_2536_ = l_Lean_setReducibilityStatus___redArg(v_inst_2533_, v_declName_2534_, v___x_2535_);
return v___x_2536_;
}
}
LEAN_EXPORT lean_object* l_Lean_setIrreducibleAttribute(lean_object* v_m_2537_, lean_object* v_inst_2538_, lean_object* v_declName_2539_){
_start:
{
lean_object* v___x_2540_; 
v___x_2540_ = l_Lean_setIrreducibleAttribute___redArg(v_inst_2538_, v_declName_2539_);
return v___x_2540_;
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
res = l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_599401733____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_reducibilityCoreExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_reducibilityCoreExt);
lean_dec_ref(res);
res = l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3383261721____hygCtx___hyg_2_();
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
