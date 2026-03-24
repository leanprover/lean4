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
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
uint64_t lean_uint64_of_nat(lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_usize_of_nat(lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg(lean_object*);
lean_object* l_Lean_Name_hash___override___boxed(lean_object*);
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_SMap_instInhabited(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t l_Lean_Name_quickLt(lean_object*, lean_object*);
lean_object* l_Array_qpartition___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___redArg(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getModuleEntries___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_addCore___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Attribute_Builtin_ensureNoArgs(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_ConstantInfo_isDefinition(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_registerBuiltinAttribute(lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ReducibilityStatus_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_ReducibilityStatus_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ReducibilityStatus_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_ReducibilityStatus_toCtorIdx___boxed(lean_object*);
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
static lean_once_cell_t l_Lean_instReprReducibilityStatus_repr___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instReprReducibilityStatus_repr___closed__8;
static lean_once_cell_t l_Lean_instReprReducibilityStatus_repr___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instReprReducibilityStatus_repr___closed__9;
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
LEAN_EXPORT lean_object* l_Lean_ReducibilityStatus_toAttrString(uint8_t);
LEAN_EXPORT lean_object* l_Lean_ReducibilityStatus_toAttrString___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__1___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__1___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__1___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__1___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__1___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*);
static const lean_array_object l_Lean_initFn___lam__1___closed__0_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_initFn___lam__1___closed__0_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___lam__1___closed__0_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l_Lean_initFn___lam__1_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_initFn___lam__1_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_initFn___lam__2___closed__0_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "reducibility attribute core extension"};
static const lean_object* l_Lean_initFn___lam__2___closed__0_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___lam__2___closed__0_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_initFn___lam__2___closed__1_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_initFn___lam__2___closed__0_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value)}};
static const lean_object* l_Lean_initFn___lam__2___closed__1_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___lam__2___closed__1_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_initFn___lam__2___closed__2_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_initFn___lam__2___closed__1_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_initFn___lam__2___closed__2_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___lam__2___closed__2_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_initFn___lam__2___closed__3_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "number of local entries: "};
static const lean_object* l_Lean_initFn___lam__2___closed__3_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___lam__2___closed__3_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_initFn___lam__2___closed__4_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_initFn___lam__2___closed__3_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value)}};
static const lean_object* l_Lean_initFn___lam__2___closed__4_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___lam__2___closed__4_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_initFn___lam__2___closed__5_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_initFn___lam__2___closed__2_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value),((lean_object*)&l_Lean_initFn___lam__2___closed__4_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value)}};
static const lean_object* l_Lean_initFn___lam__2___closed__5_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___lam__2___closed__5_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l_Lean_initFn___lam__2_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn___lam__3_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn___lam__3_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn___lam__4_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn___lam__4_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn___lam__5_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn___lam__5_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn___lam__6_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn___lam__6_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_initFn___lam__0_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_initFn___lam__1_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2____boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_initFn___lam__2_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_initFn___lam__3_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2____boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_initFn___closed__4_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_initFn___lam__4_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_initFn___closed__4_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__4_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "reducibilityCore"};
static const lean_object* l_Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_initFn___closed__6_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(95, 201, 42, 208, 53, 44, 245, 169)}};
static const lean_object* l_Lean_initFn___closed__6_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__6_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_initFn___closed__7_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_initFn___lam__5_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))} };
static const lean_object* l_Lean_initFn___closed__7_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__7_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_initFn___closed__8_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_initFn___lam__6_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2____boxed, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))} };
static const lean_object* l_Lean_initFn___closed__8_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__8_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_initFn___closed__9_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 3}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_initFn___closed__9_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__9_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_initFn___closed__10_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value)}};
static const lean_object* l_Lean_initFn___closed__10_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__10_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_initFn___closed__11_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*8 + 0, .m_other = 8, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_initFn___closed__6_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value),((lean_object*)&l_Lean_initFn___closed__7_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value),((lean_object*)&l_Lean_initFn___closed__8_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value),((lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value),((lean_object*)&l_Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value),((lean_object*)&l_Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value),((lean_object*)&l_Lean_initFn___closed__9_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value),((lean_object*)&l_Lean_initFn___closed__10_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value)}};
static const lean_object* l_Lean_initFn___closed__11_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__11_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_initFn___closed__12_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_initFn___closed__11_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value),((lean_object*)&l_Lean_initFn___closed__4_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value)}};
static const lean_object* l_Lean_initFn___closed__12_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__12_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_reducibilityCoreExt;
LEAN_EXPORT lean_object* l_Lean_SMap_switch___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_switch___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8_spec__10___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8_spec__10___redArg___closed__0;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8_spec__10___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__5___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__3_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2___redArg___closed__1;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__4___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn___lam__1_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_(lean_object*, lean_object*);
static const lean_closure_object l_Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_initFn___lam__0_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_SMap_switch___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__0___redArg, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_initFn___lam__1_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "reducibilityExtra"};
static const lean_object* l_Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_initFn___closed__4_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(114, 61, 52, 173, 157, 234, 207, 193)}};
static const lean_object* l_Lean_initFn___closed__4_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__4_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__value;
static lean_once_cell_t l_Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_;
static lean_once_cell_t l_Lean_initFn___closed__6_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_initFn___closed__6_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_;
static lean_once_cell_t l_Lean_initFn___closed__7_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_initFn___closed__7_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_;
static lean_once_cell_t l_Lean_initFn___closed__8_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_initFn___closed__8_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_;
static lean_once_cell_t l_Lean_initFn___closed__9_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_initFn___closed__9_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_;
static lean_once_cell_t l_Lean_initFn___closed__10_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_initFn___closed__10_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__4(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8_spec__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_reducibilityExtraExt;
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_getReducibilityStatusCore_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_getReducibilityStatusCore_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__0_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_closure_object l_Lean_getReducibilityStatusCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_getReducibilityStatusCore___closed__0 = (const lean_object*)&l_Lean_getReducibilityStatusCore___closed__0_value;
static const lean_closure_object l_Lean_getReducibilityStatusCore___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_hash___override___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_getReducibilityStatusCore___closed__1 = (const lean_object*)&l_Lean_getReducibilityStatusCore___closed__1_value;
static lean_once_cell_t l_Lean_getReducibilityStatusCore___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getReducibilityStatusCore___closed__2;
LEAN_EXPORT uint8_t lean_get_reducibility_status(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_set_reducibility_status(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusImp___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "allowUnsafeReducibility"};
static const lean_object* l_Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(43, 3, 217, 246, 47, 128, 204, 22)}};
static const lean_object* l_Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 235, .m_capacity = 235, .m_length = 234, .m_data = "enables users to modify the reducibility settings for declarations even when such changes are deemed potentially hazardous. For example, `simp` and type class resolution maintain term indices where reducible declarations are expanded."};
static const lean_object* l_Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4__value)}};
static const lean_object* l_Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_initFn___closed__4_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_initFn___closed__4_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__4_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_initFn___closed__4_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(106, 158, 85, 56, 211, 107, 118, 9)}};
static const lean_object* l_Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4____boxed(lean_object*);
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
static const lean_string_object l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 49, .m_capacity = 49, .m_length = 48, .m_data = "`, declarations are `[semireducible]` by default"};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__6 = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__6_value;
static lean_once_cell_t l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__7;
static const lean_string_object l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "failed to set `[irreducible]`, `"};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__8 = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__8_value;
static lean_once_cell_t l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__9;
static const lean_string_object l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 71, .m_capacity = 71, .m_length = 70, .m_data = "` is not currently `[semireducible]` nor `[implicit_reducible]`, but `"};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__10 = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__10_value;
static lean_once_cell_t l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__11;
static const lean_string_object l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "failed to set `[implicit_reducible]`, `"};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__12 = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__12_value;
static lean_once_cell_t l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__13;
static const lean_string_object l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "failed to set reducibility status, `"};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__14 = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__14_value;
static lean_once_cell_t l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__15;
static const lean_string_object l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 73, .m_capacity = 73, .m_length = 72, .m_data = "` has not been defined in this file, consider using the `local` modifier"};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__16 = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__16_value;
static lean_once_cell_t l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__17;
static const lean_string_object l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "failed to set `[local reducible]` for `"};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__18 = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__18_value;
static lean_once_cell_t l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__19;
static const lean_string_object l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 111, .m_capacity = 111, .m_length = 110, .m_data = "`, recall that `[reducible]` affects the term indexing datastructures used by `simp` and type class resolution"};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__20 = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__20_value;
static lean_once_cell_t l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__21;
static const lean_string_object l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "failed to set `[local semireducible]`, `"};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__22 = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__22_value;
static lean_once_cell_t l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__23;
static const lean_string_object l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "` is currently `"};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__24 = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__24_value;
static lean_once_cell_t l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__25;
static const lean_string_object l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "`, `[irreducible]` expected"};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__26 = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__26_value;
static lean_once_cell_t l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__27;
static const lean_string_object l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "failed to set `[local irreducible]`, `"};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__28 = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__28_value;
static lean_once_cell_t l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__29_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__29;
static const lean_string_object l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 57, .m_capacity = 57, .m_length = 56, .m_data = "`, `[semireducible]` nor `[implicit_reducible]` expected"};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__30 = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__30_value;
static lean_once_cell_t l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__31;
static const lean_string_object l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = "failed to set `[local implicit_reducible]`, `"};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__32 = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__32_value;
static lean_once_cell_t l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__33_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__33;
static const lean_string_object l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "`, `[semireducible]` expected"};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__34 = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__34_value;
static lean_once_cell_t l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__35_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__35;
static const lean_string_object l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "failed to set reducibility status for `"};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__36 = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__36_value;
static lean_once_cell_t l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__37_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__37;
static const lean_string_object l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 71, .m_capacity = 71, .m_length = 70, .m_data = "`, the `scoped` modifier is not recommended for this kind of attribute"};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__38 = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__38_value;
static lean_once_cell_t l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__39_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__39;
static const lean_string_object l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "` is not a definition"};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__40 = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__40_value;
static lean_once_cell_t l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__41_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__41;
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0(lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*);
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
static const lean_ctor_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value),((lean_object*)&l_Lean_initFn___closed__4_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "ReducibilityAttrs"};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__4_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(253, 243, 132, 119, 102, 176, 104, 231)}};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__4_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__4_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__4_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(136, 6, 121, 201, 161, 138, 59, 119)}};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__6_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value),((lean_object*)&l_Lean_initFn___closed__4_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(97, 62, 6, 154, 126, 194, 108, 7)}};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__6_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__6_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__7_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__7_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__7_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__8_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__6_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__7_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(152, 228, 198, 151, 110, 175, 120, 179)}};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__8_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__8_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__9_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__9_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__9_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__10_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__8_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__9_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(105, 11, 210, 221, 39, 72, 148, 16)}};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__10_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__10_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__11_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__10_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value),((lean_object*)&l_Lean_initFn___closed__4_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(44, 11, 42, 155, 183, 228, 253, 121)}};
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
static const lean_ctor_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__12_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value),((lean_object*)(((size_t)(448179520) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 198, 205, 193, 232, 47, 231, 115)}};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__14_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(215, 103, 212, 74, 221, 101, 148, 94)}};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__16_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(63, 101, 95, 202, 234, 22, 138, 248)}};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(122, 149, 83, 76, 39, 245, 77, 136)}};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__4_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "implicit_reducible"};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__4_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__4_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__4_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(138, 100, 121, 167, 26, 160, 176, 156)}};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__6_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__0_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2____boxed, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2__value)} };
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__6_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__6_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__7_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "implicit reducible declaration"};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__7_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__7_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__8_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 8, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__7_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__8_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__8_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__9_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_ReducibilityAttrs_0__Lean_addAttr___boxed, .m_arity = 7, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(3) << 1) | 1))} };
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__9_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__9_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__10_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__8_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__9_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__6_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__10_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__10_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2____boxed(lean_object*);
static const lean_ctor_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_598760241____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__12_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value),((lean_object*)(((size_t)(598760241) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(203, 31, 124, 35, 202, 125, 149, 183)}};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_598760241____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_598760241____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_598760241____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_598760241____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__14_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(48, 246, 192, 136, 91, 195, 24, 249)}};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_598760241____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_598760241____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_598760241____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_598760241____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__16_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(52, 129, 8, 210, 22, 75, 42, 139)}};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_598760241____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_598760241____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_598760241____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_598760241____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(141, 132, 253, 75, 111, 151, 182, 152)}};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_598760241____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_598760241____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__4_00___x40_Lean_ReducibilityAttrs_598760241____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "instance_reducible"};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__4_00___x40_Lean_ReducibilityAttrs_598760241____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__4_00___x40_Lean_ReducibilityAttrs_598760241____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_598760241____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__4_00___x40_Lean_ReducibilityAttrs_598760241____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(125, 180, 213, 185, 56, 77, 23, 14)}};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_598760241____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_598760241____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__6_00___x40_Lean_ReducibilityAttrs_598760241____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__0_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2____boxed, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_598760241____hygCtx___hyg_2__value)} };
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__6_00___x40_Lean_ReducibilityAttrs_598760241____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__6_00___x40_Lean_ReducibilityAttrs_598760241____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__7_00___x40_Lean_ReducibilityAttrs_598760241____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "alias for implicit_reducible"};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__7_00___x40_Lean_ReducibilityAttrs_598760241____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__7_00___x40_Lean_ReducibilityAttrs_598760241____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__8_00___x40_Lean_ReducibilityAttrs_598760241____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 8, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_598760241____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_598760241____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__7_00___x40_Lean_ReducibilityAttrs_598760241____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__8_00___x40_Lean_ReducibilityAttrs_598760241____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__8_00___x40_Lean_ReducibilityAttrs_598760241____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__9_00___x40_Lean_ReducibilityAttrs_598760241____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__8_00___x40_Lean_ReducibilityAttrs_598760241____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__9_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__6_00___x40_Lean_ReducibilityAttrs_598760241____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__9_00___x40_Lean_ReducibilityAttrs_598760241____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__9_00___x40_Lean_ReducibilityAttrs_598760241____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_598760241____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_598760241____hygCtx___hyg_2____boxed(lean_object*);
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
default: 
{
lean_object* v___x_5_; 
v___x_5_ = lean_unsigned_to_nat(3u);
return v___x_5_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ReducibilityStatus_ctorIdx___boxed(lean_object* v_x_6_){
_start:
{
uint8_t v_x_boxed_7_; lean_object* v_res_8_; 
v_x_boxed_7_ = lean_unbox(v_x_6_);
v_res_8_ = l_Lean_ReducibilityStatus_ctorIdx(v_x_boxed_7_);
return v_res_8_;
}
}
LEAN_EXPORT lean_object* l_Lean_ReducibilityStatus_toCtorIdx(uint8_t v_x_9_){
_start:
{
lean_object* v___x_10_; 
v___x_10_ = l_Lean_ReducibilityStatus_ctorIdx(v_x_9_);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* l_Lean_ReducibilityStatus_toCtorIdx___boxed(lean_object* v_x_11_){
_start:
{
uint8_t v_x_4__boxed_12_; lean_object* v_res_13_; 
v_x_4__boxed_12_ = lean_unbox(v_x_11_);
v_res_13_ = l_Lean_ReducibilityStatus_toCtorIdx(v_x_4__boxed_12_);
return v_res_13_;
}
}
LEAN_EXPORT lean_object* l_Lean_ReducibilityStatus_ctorElim___redArg(lean_object* v_k_14_){
_start:
{
lean_inc(v_k_14_);
return v_k_14_;
}
}
LEAN_EXPORT lean_object* l_Lean_ReducibilityStatus_ctorElim___redArg___boxed(lean_object* v_k_15_){
_start:
{
lean_object* v_res_16_; 
v_res_16_ = l_Lean_ReducibilityStatus_ctorElim___redArg(v_k_15_);
lean_dec(v_k_15_);
return v_res_16_;
}
}
LEAN_EXPORT lean_object* l_Lean_ReducibilityStatus_ctorElim(lean_object* v_motive_17_, lean_object* v_ctorIdx_18_, uint8_t v_t_19_, lean_object* v_h_20_, lean_object* v_k_21_){
_start:
{
lean_inc(v_k_21_);
return v_k_21_;
}
}
LEAN_EXPORT lean_object* l_Lean_ReducibilityStatus_ctorElim___boxed(lean_object* v_motive_22_, lean_object* v_ctorIdx_23_, lean_object* v_t_24_, lean_object* v_h_25_, lean_object* v_k_26_){
_start:
{
uint8_t v_t_boxed_27_; lean_object* v_res_28_; 
v_t_boxed_27_ = lean_unbox(v_t_24_);
v_res_28_ = l_Lean_ReducibilityStatus_ctorElim(v_motive_22_, v_ctorIdx_23_, v_t_boxed_27_, v_h_25_, v_k_26_);
lean_dec(v_k_26_);
lean_dec(v_ctorIdx_23_);
return v_res_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_ReducibilityStatus_reducible_elim___redArg(lean_object* v_reducible_29_){
_start:
{
lean_inc(v_reducible_29_);
return v_reducible_29_;
}
}
LEAN_EXPORT lean_object* l_Lean_ReducibilityStatus_reducible_elim___redArg___boxed(lean_object* v_reducible_30_){
_start:
{
lean_object* v_res_31_; 
v_res_31_ = l_Lean_ReducibilityStatus_reducible_elim___redArg(v_reducible_30_);
lean_dec(v_reducible_30_);
return v_res_31_;
}
}
LEAN_EXPORT lean_object* l_Lean_ReducibilityStatus_reducible_elim(lean_object* v_motive_32_, uint8_t v_t_33_, lean_object* v_h_34_, lean_object* v_reducible_35_){
_start:
{
lean_inc(v_reducible_35_);
return v_reducible_35_;
}
}
LEAN_EXPORT lean_object* l_Lean_ReducibilityStatus_reducible_elim___boxed(lean_object* v_motive_36_, lean_object* v_t_37_, lean_object* v_h_38_, lean_object* v_reducible_39_){
_start:
{
uint8_t v_t_boxed_40_; lean_object* v_res_41_; 
v_t_boxed_40_ = lean_unbox(v_t_37_);
v_res_41_ = l_Lean_ReducibilityStatus_reducible_elim(v_motive_36_, v_t_boxed_40_, v_h_38_, v_reducible_39_);
lean_dec(v_reducible_39_);
return v_res_41_;
}
}
LEAN_EXPORT lean_object* l_Lean_ReducibilityStatus_semireducible_elim___redArg(lean_object* v_semireducible_42_){
_start:
{
lean_inc(v_semireducible_42_);
return v_semireducible_42_;
}
}
LEAN_EXPORT lean_object* l_Lean_ReducibilityStatus_semireducible_elim___redArg___boxed(lean_object* v_semireducible_43_){
_start:
{
lean_object* v_res_44_; 
v_res_44_ = l_Lean_ReducibilityStatus_semireducible_elim___redArg(v_semireducible_43_);
lean_dec(v_semireducible_43_);
return v_res_44_;
}
}
LEAN_EXPORT lean_object* l_Lean_ReducibilityStatus_semireducible_elim(lean_object* v_motive_45_, uint8_t v_t_46_, lean_object* v_h_47_, lean_object* v_semireducible_48_){
_start:
{
lean_inc(v_semireducible_48_);
return v_semireducible_48_;
}
}
LEAN_EXPORT lean_object* l_Lean_ReducibilityStatus_semireducible_elim___boxed(lean_object* v_motive_49_, lean_object* v_t_50_, lean_object* v_h_51_, lean_object* v_semireducible_52_){
_start:
{
uint8_t v_t_boxed_53_; lean_object* v_res_54_; 
v_t_boxed_53_ = lean_unbox(v_t_50_);
v_res_54_ = l_Lean_ReducibilityStatus_semireducible_elim(v_motive_49_, v_t_boxed_53_, v_h_51_, v_semireducible_52_);
lean_dec(v_semireducible_52_);
return v_res_54_;
}
}
LEAN_EXPORT lean_object* l_Lean_ReducibilityStatus_irreducible_elim___redArg(lean_object* v_irreducible_55_){
_start:
{
lean_inc(v_irreducible_55_);
return v_irreducible_55_;
}
}
LEAN_EXPORT lean_object* l_Lean_ReducibilityStatus_irreducible_elim___redArg___boxed(lean_object* v_irreducible_56_){
_start:
{
lean_object* v_res_57_; 
v_res_57_ = l_Lean_ReducibilityStatus_irreducible_elim___redArg(v_irreducible_56_);
lean_dec(v_irreducible_56_);
return v_res_57_;
}
}
LEAN_EXPORT lean_object* l_Lean_ReducibilityStatus_irreducible_elim(lean_object* v_motive_58_, uint8_t v_t_59_, lean_object* v_h_60_, lean_object* v_irreducible_61_){
_start:
{
lean_inc(v_irreducible_61_);
return v_irreducible_61_;
}
}
LEAN_EXPORT lean_object* l_Lean_ReducibilityStatus_irreducible_elim___boxed(lean_object* v_motive_62_, lean_object* v_t_63_, lean_object* v_h_64_, lean_object* v_irreducible_65_){
_start:
{
uint8_t v_t_boxed_66_; lean_object* v_res_67_; 
v_t_boxed_66_ = lean_unbox(v_t_63_);
v_res_67_ = l_Lean_ReducibilityStatus_irreducible_elim(v_motive_62_, v_t_boxed_66_, v_h_64_, v_irreducible_65_);
lean_dec(v_irreducible_65_);
return v_res_67_;
}
}
LEAN_EXPORT lean_object* l_Lean_ReducibilityStatus_implicitReducible_elim___redArg(lean_object* v_implicitReducible_68_){
_start:
{
lean_inc(v_implicitReducible_68_);
return v_implicitReducible_68_;
}
}
LEAN_EXPORT lean_object* l_Lean_ReducibilityStatus_implicitReducible_elim___redArg___boxed(lean_object* v_implicitReducible_69_){
_start:
{
lean_object* v_res_70_; 
v_res_70_ = l_Lean_ReducibilityStatus_implicitReducible_elim___redArg(v_implicitReducible_69_);
lean_dec(v_implicitReducible_69_);
return v_res_70_;
}
}
LEAN_EXPORT lean_object* l_Lean_ReducibilityStatus_implicitReducible_elim(lean_object* v_motive_71_, uint8_t v_t_72_, lean_object* v_h_73_, lean_object* v_implicitReducible_74_){
_start:
{
lean_inc(v_implicitReducible_74_);
return v_implicitReducible_74_;
}
}
LEAN_EXPORT lean_object* l_Lean_ReducibilityStatus_implicitReducible_elim___boxed(lean_object* v_motive_75_, lean_object* v_t_76_, lean_object* v_h_77_, lean_object* v_implicitReducible_78_){
_start:
{
uint8_t v_t_boxed_79_; lean_object* v_res_80_; 
v_t_boxed_79_ = lean_unbox(v_t_76_);
v_res_80_ = l_Lean_ReducibilityStatus_implicitReducible_elim(v_motive_75_, v_t_boxed_79_, v_h_77_, v_implicitReducible_78_);
lean_dec(v_implicitReducible_78_);
return v_res_80_;
}
}
static uint8_t _init_l_Lean_instInhabitedReducibilityStatus_default(void){
_start:
{
uint8_t v___x_81_; 
v___x_81_ = 0;
return v___x_81_;
}
}
static uint8_t _init_l_Lean_instInhabitedReducibilityStatus(void){
_start:
{
uint8_t v___x_82_; 
v___x_82_ = 0;
return v___x_82_;
}
}
static lean_object* _init_l_Lean_instReprReducibilityStatus_repr___closed__8(void){
_start:
{
lean_object* v___x_95_; lean_object* v___x_96_; 
v___x_95_ = lean_unsigned_to_nat(2u);
v___x_96_ = lean_nat_to_int(v___x_95_);
return v___x_96_;
}
}
static lean_object* _init_l_Lean_instReprReducibilityStatus_repr___closed__9(void){
_start:
{
lean_object* v___x_97_; lean_object* v___x_98_; 
v___x_97_ = lean_unsigned_to_nat(1u);
v___x_98_ = lean_nat_to_int(v___x_97_);
return v___x_98_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprReducibilityStatus_repr(uint8_t v_x_99_, lean_object* v_prec_100_){
_start:
{
lean_object* v___y_102_; lean_object* v___y_109_; lean_object* v___y_116_; lean_object* v___y_123_; 
switch(v_x_99_)
{
case 0:
{
lean_object* v___x_129_; uint8_t v___x_130_; 
v___x_129_ = lean_unsigned_to_nat(1024u);
v___x_130_ = lean_nat_dec_le(v___x_129_, v_prec_100_);
if (v___x_130_ == 0)
{
lean_object* v___x_131_; 
v___x_131_ = lean_obj_once(&l_Lean_instReprReducibilityStatus_repr___closed__8, &l_Lean_instReprReducibilityStatus_repr___closed__8_once, _init_l_Lean_instReprReducibilityStatus_repr___closed__8);
v___y_102_ = v___x_131_;
goto v___jp_101_;
}
else
{
lean_object* v___x_132_; 
v___x_132_ = lean_obj_once(&l_Lean_instReprReducibilityStatus_repr___closed__9, &l_Lean_instReprReducibilityStatus_repr___closed__9_once, _init_l_Lean_instReprReducibilityStatus_repr___closed__9);
v___y_102_ = v___x_132_;
goto v___jp_101_;
}
}
case 1:
{
lean_object* v___x_133_; uint8_t v___x_134_; 
v___x_133_ = lean_unsigned_to_nat(1024u);
v___x_134_ = lean_nat_dec_le(v___x_133_, v_prec_100_);
if (v___x_134_ == 0)
{
lean_object* v___x_135_; 
v___x_135_ = lean_obj_once(&l_Lean_instReprReducibilityStatus_repr___closed__8, &l_Lean_instReprReducibilityStatus_repr___closed__8_once, _init_l_Lean_instReprReducibilityStatus_repr___closed__8);
v___y_109_ = v___x_135_;
goto v___jp_108_;
}
else
{
lean_object* v___x_136_; 
v___x_136_ = lean_obj_once(&l_Lean_instReprReducibilityStatus_repr___closed__9, &l_Lean_instReprReducibilityStatus_repr___closed__9_once, _init_l_Lean_instReprReducibilityStatus_repr___closed__9);
v___y_109_ = v___x_136_;
goto v___jp_108_;
}
}
case 2:
{
lean_object* v___x_137_; uint8_t v___x_138_; 
v___x_137_ = lean_unsigned_to_nat(1024u);
v___x_138_ = lean_nat_dec_le(v___x_137_, v_prec_100_);
if (v___x_138_ == 0)
{
lean_object* v___x_139_; 
v___x_139_ = lean_obj_once(&l_Lean_instReprReducibilityStatus_repr___closed__8, &l_Lean_instReprReducibilityStatus_repr___closed__8_once, _init_l_Lean_instReprReducibilityStatus_repr___closed__8);
v___y_116_ = v___x_139_;
goto v___jp_115_;
}
else
{
lean_object* v___x_140_; 
v___x_140_ = lean_obj_once(&l_Lean_instReprReducibilityStatus_repr___closed__9, &l_Lean_instReprReducibilityStatus_repr___closed__9_once, _init_l_Lean_instReprReducibilityStatus_repr___closed__9);
v___y_116_ = v___x_140_;
goto v___jp_115_;
}
}
default: 
{
lean_object* v___x_141_; uint8_t v___x_142_; 
v___x_141_ = lean_unsigned_to_nat(1024u);
v___x_142_ = lean_nat_dec_le(v___x_141_, v_prec_100_);
if (v___x_142_ == 0)
{
lean_object* v___x_143_; 
v___x_143_ = lean_obj_once(&l_Lean_instReprReducibilityStatus_repr___closed__8, &l_Lean_instReprReducibilityStatus_repr___closed__8_once, _init_l_Lean_instReprReducibilityStatus_repr___closed__8);
v___y_123_ = v___x_143_;
goto v___jp_122_;
}
else
{
lean_object* v___x_144_; 
v___x_144_ = lean_obj_once(&l_Lean_instReprReducibilityStatus_repr___closed__9, &l_Lean_instReprReducibilityStatus_repr___closed__9_once, _init_l_Lean_instReprReducibilityStatus_repr___closed__9);
v___y_123_ = v___x_144_;
goto v___jp_122_;
}
}
}
v___jp_101_:
{
lean_object* v___x_103_; lean_object* v___x_104_; uint8_t v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; 
v___x_103_ = ((lean_object*)(l_Lean_instReprReducibilityStatus_repr___closed__1));
v___x_104_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_104_, 0, v___y_102_);
lean_ctor_set(v___x_104_, 1, v___x_103_);
v___x_105_ = 0;
v___x_106_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_106_, 0, v___x_104_);
lean_ctor_set_uint8(v___x_106_, sizeof(void*)*1, v___x_105_);
v___x_107_ = l_Repr_addAppParen(v___x_106_, v_prec_100_);
return v___x_107_;
}
v___jp_108_:
{
lean_object* v___x_110_; lean_object* v___x_111_; uint8_t v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; 
v___x_110_ = ((lean_object*)(l_Lean_instReprReducibilityStatus_repr___closed__3));
v___x_111_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_111_, 0, v___y_109_);
lean_ctor_set(v___x_111_, 1, v___x_110_);
v___x_112_ = 0;
v___x_113_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_113_, 0, v___x_111_);
lean_ctor_set_uint8(v___x_113_, sizeof(void*)*1, v___x_112_);
v___x_114_ = l_Repr_addAppParen(v___x_113_, v_prec_100_);
return v___x_114_;
}
v___jp_115_:
{
lean_object* v___x_117_; lean_object* v___x_118_; uint8_t v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; 
v___x_117_ = ((lean_object*)(l_Lean_instReprReducibilityStatus_repr___closed__5));
v___x_118_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_118_, 0, v___y_116_);
lean_ctor_set(v___x_118_, 1, v___x_117_);
v___x_119_ = 0;
v___x_120_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_120_, 0, v___x_118_);
lean_ctor_set_uint8(v___x_120_, sizeof(void*)*1, v___x_119_);
v___x_121_ = l_Repr_addAppParen(v___x_120_, v_prec_100_);
return v___x_121_;
}
v___jp_122_:
{
lean_object* v___x_124_; lean_object* v___x_125_; uint8_t v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; 
v___x_124_ = ((lean_object*)(l_Lean_instReprReducibilityStatus_repr___closed__7));
v___x_125_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_125_, 0, v___y_123_);
lean_ctor_set(v___x_125_, 1, v___x_124_);
v___x_126_ = 0;
v___x_127_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_127_, 0, v___x_125_);
lean_ctor_set_uint8(v___x_127_, sizeof(void*)*1, v___x_126_);
v___x_128_ = l_Repr_addAppParen(v___x_127_, v_prec_100_);
return v___x_128_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instReprReducibilityStatus_repr___boxed(lean_object* v_x_145_, lean_object* v_prec_146_){
_start:
{
uint8_t v_x_233__boxed_147_; lean_object* v_res_148_; 
v_x_233__boxed_147_ = lean_unbox(v_x_145_);
v_res_148_ = l_Lean_instReprReducibilityStatus_repr(v_x_233__boxed_147_, v_prec_146_);
lean_dec(v_prec_146_);
return v_res_148_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqReducibilityStatus_beq(uint8_t v_x_151_, uint8_t v_y_152_){
_start:
{
lean_object* v___x_153_; lean_object* v___x_154_; uint8_t v___x_155_; 
v___x_153_ = l_Lean_ReducibilityStatus_ctorIdx(v_x_151_);
v___x_154_ = l_Lean_ReducibilityStatus_ctorIdx(v_y_152_);
v___x_155_ = lean_nat_dec_eq(v___x_153_, v___x_154_);
lean_dec(v___x_154_);
lean_dec(v___x_153_);
return v___x_155_;
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqReducibilityStatus_beq___boxed(lean_object* v_x_156_, lean_object* v_y_157_){
_start:
{
uint8_t v_x_17__boxed_158_; uint8_t v_y_18__boxed_159_; uint8_t v_res_160_; lean_object* v_r_161_; 
v_x_17__boxed_158_ = lean_unbox(v_x_156_);
v_y_18__boxed_159_ = lean_unbox(v_y_157_);
v_res_160_ = l_Lean_instBEqReducibilityStatus_beq(v_x_17__boxed_158_, v_y_18__boxed_159_);
v_r_161_ = lean_box(v_res_160_);
return v_r_161_;
}
}
LEAN_EXPORT lean_object* l_Lean_ReducibilityStatus_toAttrString(uint8_t v_x_168_){
_start:
{
switch(v_x_168_)
{
case 0:
{
lean_object* v___x_169_; 
v___x_169_ = ((lean_object*)(l_Lean_ReducibilityStatus_toAttrString___closed__0));
return v___x_169_;
}
case 1:
{
lean_object* v___x_170_; 
v___x_170_ = ((lean_object*)(l_Lean_ReducibilityStatus_toAttrString___closed__1));
return v___x_170_;
}
case 2:
{
lean_object* v___x_171_; 
v___x_171_ = ((lean_object*)(l_Lean_ReducibilityStatus_toAttrString___closed__2));
return v___x_171_;
}
default: 
{
lean_object* v___x_172_; 
v___x_172_ = ((lean_object*)(l_Lean_ReducibilityStatus_toAttrString___closed__3));
return v___x_172_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ReducibilityStatus_toAttrString___boxed(lean_object* v_x_173_){
_start:
{
uint8_t v_x_40__boxed_174_; lean_object* v_res_175_; 
v_x_40__boxed_174_ = lean_unbox(v_x_173_);
v_res_175_ = l_Lean_ReducibilityStatus_toAttrString(v_x_40__boxed_174_);
return v_res_175_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_(lean_object* v_s_176_, lean_object* v_p_177_){
_start:
{
lean_object* v_fst_178_; lean_object* v_snd_179_; lean_object* v___x_180_; 
v_fst_178_ = lean_ctor_get(v_p_177_, 0);
lean_inc(v_fst_178_);
v_snd_179_ = lean_ctor_get(v_p_177_, 1);
lean_inc(v_snd_179_);
lean_dec_ref(v_p_177_);
v___x_180_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_178_, v_snd_179_, v_s_176_);
return v___x_180_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__1___redArg___lam__0(lean_object* v_a_181_, lean_object* v_b_182_){
_start:
{
lean_object* v_fst_183_; lean_object* v_fst_184_; uint8_t v___x_185_; 
v_fst_183_ = lean_ctor_get(v_a_181_, 0);
v_fst_184_ = lean_ctor_get(v_b_182_, 0);
v___x_185_ = l_Lean_Name_quickLt(v_fst_183_, v_fst_184_);
return v___x_185_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__1___redArg___lam__0___boxed(lean_object* v_a_186_, lean_object* v_b_187_){
_start:
{
uint8_t v_res_188_; lean_object* v_r_189_; 
v_res_188_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__1___redArg___lam__0(v_a_186_, v_b_187_);
lean_dec_ref(v_b_187_);
lean_dec_ref(v_a_186_);
v_r_189_ = lean_box(v_res_188_);
return v_r_189_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__1___redArg(lean_object* v_as_191_, lean_object* v_lo_192_, lean_object* v_hi_193_){
_start:
{
uint8_t v___x_194_; 
v___x_194_ = lean_nat_dec_lt(v_lo_192_, v_hi_193_);
if (v___x_194_ == 0)
{
lean_dec(v_lo_192_);
return v_as_191_;
}
else
{
lean_object* v___f_195_; lean_object* v___x_196_; lean_object* v_fst_197_; lean_object* v_snd_198_; uint8_t v___x_199_; 
v___f_195_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__1___redArg___closed__0));
lean_inc(v_lo_192_);
v___x_196_ = l_Array_qpartition___redArg(v_as_191_, v___f_195_, v_lo_192_, v_hi_193_);
v_fst_197_ = lean_ctor_get(v___x_196_, 0);
lean_inc(v_fst_197_);
v_snd_198_ = lean_ctor_get(v___x_196_, 1);
lean_inc(v_snd_198_);
lean_dec_ref(v___x_196_);
v___x_199_ = lean_nat_dec_le(v_hi_193_, v_fst_197_);
if (v___x_199_ == 0)
{
lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; 
v___x_200_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__1___redArg(v_snd_198_, v_lo_192_, v_fst_197_);
v___x_201_ = lean_unsigned_to_nat(1u);
v___x_202_ = lean_nat_add(v_fst_197_, v___x_201_);
lean_dec(v_fst_197_);
v_as_191_ = v___x_200_;
v_lo_192_ = v___x_202_;
goto _start;
}
else
{
lean_dec(v_fst_197_);
lean_dec(v_lo_192_);
return v_snd_198_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object* v_as_204_, lean_object* v_lo_205_, lean_object* v_hi_206_){
_start:
{
lean_object* v_res_207_; 
v_res_207_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__1___redArg(v_as_204_, v_lo_205_, v_hi_206_);
lean_dec(v_hi_206_);
return v_res_207_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_init_208_, lean_object* v_x_209_){
_start:
{
if (lean_obj_tag(v_x_209_) == 0)
{
lean_object* v_k_210_; lean_object* v_v_211_; lean_object* v_l_212_; lean_object* v_r_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; 
v_k_210_ = lean_ctor_get(v_x_209_, 1);
v_v_211_ = lean_ctor_get(v_x_209_, 2);
v_l_212_ = lean_ctor_get(v_x_209_, 3);
v_r_213_ = lean_ctor_get(v_x_209_, 4);
v___x_214_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__0_spec__0(v_init_208_, v_l_212_);
lean_inc(v_v_211_);
lean_inc(v_k_210_);
v___x_215_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_215_, 0, v_k_210_);
lean_ctor_set(v___x_215_, 1, v_v_211_);
v___x_216_ = lean_array_push(v___x_214_, v___x_215_);
v_init_208_ = v___x_216_;
v_x_209_ = v_r_213_;
goto _start;
}
else
{
return v_init_208_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_init_218_, lean_object* v_x_219_){
_start:
{
lean_object* v_res_220_; 
v_res_220_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__0_spec__0(v_init_218_, v_x_219_);
lean_dec(v_x_219_);
return v_res_220_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__1_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_(lean_object* v_x_223_, lean_object* v_s_224_, uint8_t v_x_225_){
_start:
{
lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v_r_228_; lean_object* v___x_229_; uint8_t v___x_230_; 
v___x_226_ = lean_unsigned_to_nat(0u);
v___x_227_ = ((lean_object*)(l_Lean_initFn___lam__1___closed__0_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_));
v_r_228_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__0_spec__0(v___x_227_, v_s_224_);
v___x_229_ = lean_array_get_size(v_r_228_);
v___x_230_ = lean_nat_dec_eq(v___x_229_, v___x_226_);
if (v___x_230_ == 0)
{
lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___y_234_; uint8_t v___x_238_; 
v___x_231_ = lean_unsigned_to_nat(1u);
v___x_232_ = lean_nat_sub(v___x_229_, v___x_231_);
v___x_238_ = lean_nat_dec_le(v___x_226_, v___x_232_);
if (v___x_238_ == 0)
{
lean_inc(v___x_232_);
v___y_234_ = v___x_232_;
goto v___jp_233_;
}
else
{
v___y_234_ = v___x_226_;
goto v___jp_233_;
}
v___jp_233_:
{
uint8_t v___x_235_; 
v___x_235_ = lean_nat_dec_le(v___y_234_, v___x_232_);
if (v___x_235_ == 0)
{
lean_object* v___x_236_; 
lean_dec(v___x_232_);
lean_inc(v___y_234_);
v___x_236_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__1___redArg(v_r_228_, v___y_234_, v___y_234_);
lean_dec(v___y_234_);
return v___x_236_;
}
else
{
lean_object* v___x_237_; 
v___x_237_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__1___redArg(v_r_228_, v___y_234_, v___x_232_);
lean_dec(v___x_232_);
return v___x_237_;
}
}
}
else
{
return v_r_228_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__1_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2____boxed(lean_object* v_x_239_, lean_object* v_s_240_, lean_object* v_x_241_){
_start:
{
uint8_t v_x_687__boxed_242_; lean_object* v_res_243_; 
v_x_687__boxed_242_ = lean_unbox(v_x_241_);
v_res_243_ = l_Lean_initFn___lam__1_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_(v_x_239_, v_s_240_, v_x_687__boxed_242_);
lean_dec(v_s_240_);
lean_dec_ref(v_x_239_);
return v_res_243_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__2_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_(lean_object* v_s_256_){
_start:
{
lean_object* v___x_257_; lean_object* v___y_259_; 
v___x_257_ = ((lean_object*)(l_Lean_initFn___lam__2___closed__5_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_));
if (lean_obj_tag(v_s_256_) == 0)
{
lean_object* v_size_263_; 
v_size_263_ = lean_ctor_get(v_s_256_, 0);
lean_inc(v_size_263_);
lean_dec_ref(v_s_256_);
v___y_259_ = v_size_263_;
goto v___jp_258_;
}
else
{
lean_object* v___x_264_; 
v___x_264_ = lean_unsigned_to_nat(0u);
v___y_259_ = v___x_264_;
goto v___jp_258_;
}
v___jp_258_:
{
lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; 
v___x_260_ = l_Nat_reprFast(v___y_259_);
v___x_261_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_261_, 0, v___x_260_);
v___x_262_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_262_, 0, v___x_257_);
lean_ctor_set(v___x_262_, 1, v___x_261_);
return v___x_262_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__2(lean_object* v_newState_265_, lean_object* v_x_266_, lean_object* v_x_267_){
_start:
{
if (lean_obj_tag(v_x_267_) == 0)
{
return v_x_266_;
}
else
{
lean_object* v_head_268_; lean_object* v_tail_269_; lean_object* v___x_270_; 
v_head_268_ = lean_ctor_get(v_x_267_, 0);
lean_inc(v_head_268_);
v_tail_269_ = lean_ctor_get(v_x_267_, 1);
lean_inc(v_tail_269_);
lean_dec_ref(v_x_267_);
v___x_270_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_newState_265_, v_head_268_);
if (lean_obj_tag(v___x_270_) == 1)
{
lean_object* v_val_271_; lean_object* v___x_272_; 
v_val_271_ = lean_ctor_get(v___x_270_, 0);
lean_inc(v_val_271_);
lean_dec_ref(v___x_270_);
v___x_272_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_head_268_, v_val_271_, v_x_266_);
v_x_266_ = v___x_272_;
v_x_267_ = v_tail_269_;
goto _start;
}
else
{
lean_dec(v___x_270_);
lean_dec(v_head_268_);
v_x_267_ = v_tail_269_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__2___boxed(lean_object* v_newState_275_, lean_object* v_x_276_, lean_object* v_x_277_){
_start:
{
lean_object* v_res_278_; 
v_res_278_ = l_List_foldl___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__2(v_newState_275_, v_x_276_, v_x_277_);
lean_dec(v_newState_275_);
return v_res_278_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__3_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_(lean_object* v___oldState_279_, lean_object* v_newState_280_, lean_object* v_newItems_281_, lean_object* v_otherState_282_){
_start:
{
lean_object* v___x_283_; 
v___x_283_ = l_List_foldl___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__2(v_newState_280_, v_otherState_282_, v_newItems_281_);
return v___x_283_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__3_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2____boxed(lean_object* v___oldState_284_, lean_object* v_newState_285_, lean_object* v_newItems_286_, lean_object* v_otherState_287_){
_start:
{
lean_object* v_res_288_; 
v_res_288_ = l_Lean_initFn___lam__3_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_(v___oldState_284_, v_newState_285_, v_newItems_286_, v_otherState_287_);
lean_dec(v_newState_285_);
lean_dec(v___oldState_284_);
return v_res_288_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__4_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_(lean_object* v_m_289_){
_start:
{
lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v_r_292_; lean_object* v___x_293_; uint8_t v___x_294_; 
v___x_290_ = lean_unsigned_to_nat(0u);
v___x_291_ = ((lean_object*)(l_Lean_initFn___lam__1___closed__0_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_));
v_r_292_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__0_spec__0(v___x_291_, v_m_289_);
v___x_293_ = lean_array_get_size(v_r_292_);
v___x_294_ = lean_nat_dec_eq(v___x_293_, v___x_290_);
if (v___x_294_ == 0)
{
lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___y_298_; uint8_t v___x_302_; 
v___x_295_ = lean_unsigned_to_nat(1u);
v___x_296_ = lean_nat_sub(v___x_293_, v___x_295_);
v___x_302_ = lean_nat_dec_le(v___x_290_, v___x_296_);
if (v___x_302_ == 0)
{
lean_inc(v___x_296_);
v___y_298_ = v___x_296_;
goto v___jp_297_;
}
else
{
v___y_298_ = v___x_290_;
goto v___jp_297_;
}
v___jp_297_:
{
uint8_t v___x_299_; 
v___x_299_ = lean_nat_dec_le(v___y_298_, v___x_296_);
if (v___x_299_ == 0)
{
lean_object* v___x_300_; 
lean_dec(v___x_296_);
lean_inc(v___y_298_);
v___x_300_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__1___redArg(v_r_292_, v___y_298_, v___y_298_);
lean_dec(v___y_298_);
return v___x_300_;
}
else
{
lean_object* v___x_301_; 
v___x_301_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__1___redArg(v_r_292_, v___y_298_, v___x_296_);
lean_dec(v___x_296_);
return v___x_301_;
}
}
}
else
{
return v_r_292_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__4_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2____boxed(lean_object* v_m_303_){
_start:
{
lean_object* v_res_304_; 
v_res_304_ = l_Lean_initFn___lam__4_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_(v_m_303_);
lean_dec(v_m_303_);
return v_res_304_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__5_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_(lean_object* v___x_305_){
_start:
{
lean_object* v___x_307_; 
v___x_307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_307_, 0, v___x_305_);
return v___x_307_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__5_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2____boxed(lean_object* v___x_308_, lean_object* v___y_309_){
_start:
{
lean_object* v_res_310_; 
v_res_310_ = l_Lean_initFn___lam__5_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_(v___x_308_);
return v_res_310_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__6_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_(lean_object* v___x_311_, lean_object* v_x_312_, lean_object* v_x_313_){
_start:
{
lean_object* v___x_315_; 
v___x_315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_315_, 0, v___x_311_);
return v___x_315_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__6_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2____boxed(lean_object* v___x_316_, lean_object* v_x_317_, lean_object* v_x_318_, lean_object* v___y_319_){
_start:
{
lean_object* v_res_320_; 
v_res_320_ = l_Lean_initFn___lam__6_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_(v___x_316_, v_x_317_, v_x_318_);
lean_dec_ref(v_x_318_);
lean_dec_ref(v_x_317_);
return v_res_320_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_350_; lean_object* v___x_351_; 
v___x_350_ = ((lean_object*)(l_Lean_initFn___closed__12_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_));
v___x_351_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_350_);
return v___x_351_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2____boxed(lean_object* v_a_352_){
_start:
{
lean_object* v_res_353_; 
v_res_353_ = l_Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_();
return v_res_353_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__0(lean_object* v_init_354_, lean_object* v_t_355_){
_start:
{
lean_object* v___x_356_; 
v___x_356_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__0_spec__0(v_init_354_, v_t_355_);
return v___x_356_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__0___boxed(lean_object* v_init_357_, lean_object* v_t_358_){
_start:
{
lean_object* v_res_359_; 
v_res_359_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__0(v_init_357_, v_t_358_);
lean_dec(v_t_358_);
return v_res_359_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__1(lean_object* v_n_360_, lean_object* v_as_361_, lean_object* v_lo_362_, lean_object* v_hi_363_, lean_object* v_w_364_, lean_object* v_hlo_365_, lean_object* v_hhi_366_){
_start:
{
lean_object* v___x_367_; 
v___x_367_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__1___redArg(v_as_361_, v_lo_362_, v_hi_363_);
return v___x_367_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__1___boxed(lean_object* v_n_368_, lean_object* v_as_369_, lean_object* v_lo_370_, lean_object* v_hi_371_, lean_object* v_w_372_, lean_object* v_hlo_373_, lean_object* v_hhi_374_){
_start:
{
lean_object* v_res_375_; 
v_res_375_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__1(v_n_368_, v_as_369_, v_lo_370_, v_hi_371_, v_w_372_, v_hlo_373_, v_hhi_374_);
lean_dec(v_hi_371_);
lean_dec(v_n_368_);
return v_res_375_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_switch___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__0___redArg(lean_object* v_m_376_){
_start:
{
uint8_t v_stage_u2081_377_; 
v_stage_u2081_377_ = lean_ctor_get_uint8(v_m_376_, sizeof(void*)*2);
if (v_stage_u2081_377_ == 0)
{
return v_m_376_;
}
else
{
lean_object* v_map_u2081_378_; lean_object* v_map_u2082_379_; lean_object* v___x_381_; uint8_t v_isShared_382_; uint8_t v_isSharedCheck_387_; 
v_map_u2081_378_ = lean_ctor_get(v_m_376_, 0);
v_map_u2082_379_ = lean_ctor_get(v_m_376_, 1);
v_isSharedCheck_387_ = !lean_is_exclusive(v_m_376_);
if (v_isSharedCheck_387_ == 0)
{
v___x_381_ = v_m_376_;
v_isShared_382_ = v_isSharedCheck_387_;
goto v_resetjp_380_;
}
else
{
lean_inc(v_map_u2082_379_);
lean_inc(v_map_u2081_378_);
lean_dec(v_m_376_);
v___x_381_ = lean_box(0);
v_isShared_382_ = v_isSharedCheck_387_;
goto v_resetjp_380_;
}
v_resetjp_380_:
{
uint8_t v___x_383_; lean_object* v___x_385_; 
v___x_383_ = 0;
if (v_isShared_382_ == 0)
{
v___x_385_ = v___x_381_;
goto v_reusejp_384_;
}
else
{
lean_object* v_reuseFailAlloc_386_; 
v_reuseFailAlloc_386_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_386_, 0, v_map_u2081_378_);
lean_ctor_set(v_reuseFailAlloc_386_, 1, v_map_u2082_379_);
v___x_385_ = v_reuseFailAlloc_386_;
goto v_reusejp_384_;
}
v_reusejp_384_:
{
lean_ctor_set_uint8(v___x_385_, sizeof(void*)*2, v___x_383_);
return v___x_385_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_switch___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b2_388_, lean_object* v_m_389_){
_start:
{
lean_object* v___x_390_; 
v___x_390_ = l_Lean_SMap_switch___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__0___redArg(v_m_389_);
return v___x_390_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_(uint8_t v_x_391_, lean_object* v___y_392_){
_start:
{
lean_object* v___x_393_; 
v___x_393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_393_, 0, v___y_392_);
return v___x_393_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2____boxed(lean_object* v_x_394_, lean_object* v___y_395_){
_start:
{
uint8_t v_x_788__boxed_396_; lean_object* v_res_397_; 
v_x_788__boxed_396_ = lean_unbox(v_x_394_);
v_res_397_ = l_Lean_initFn___lam__0_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_(v_x_788__boxed_396_, v___y_395_);
return v_res_397_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__6___redArg(lean_object* v_a_398_, lean_object* v_b_399_, lean_object* v_x_400_){
_start:
{
if (lean_obj_tag(v_x_400_) == 0)
{
lean_dec(v_b_399_);
lean_dec(v_a_398_);
return v_x_400_;
}
else
{
lean_object* v_key_401_; lean_object* v_value_402_; lean_object* v_tail_403_; lean_object* v___x_405_; uint8_t v_isShared_406_; uint8_t v_isSharedCheck_415_; 
v_key_401_ = lean_ctor_get(v_x_400_, 0);
v_value_402_ = lean_ctor_get(v_x_400_, 1);
v_tail_403_ = lean_ctor_get(v_x_400_, 2);
v_isSharedCheck_415_ = !lean_is_exclusive(v_x_400_);
if (v_isSharedCheck_415_ == 0)
{
v___x_405_ = v_x_400_;
v_isShared_406_ = v_isSharedCheck_415_;
goto v_resetjp_404_;
}
else
{
lean_inc(v_tail_403_);
lean_inc(v_value_402_);
lean_inc(v_key_401_);
lean_dec(v_x_400_);
v___x_405_ = lean_box(0);
v_isShared_406_ = v_isSharedCheck_415_;
goto v_resetjp_404_;
}
v_resetjp_404_:
{
uint8_t v___x_407_; 
v___x_407_ = lean_name_eq(v_key_401_, v_a_398_);
if (v___x_407_ == 0)
{
lean_object* v___x_408_; lean_object* v___x_410_; 
v___x_408_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__6___redArg(v_a_398_, v_b_399_, v_tail_403_);
if (v_isShared_406_ == 0)
{
lean_ctor_set(v___x_405_, 2, v___x_408_);
v___x_410_ = v___x_405_;
goto v_reusejp_409_;
}
else
{
lean_object* v_reuseFailAlloc_411_; 
v_reuseFailAlloc_411_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_411_, 0, v_key_401_);
lean_ctor_set(v_reuseFailAlloc_411_, 1, v_value_402_);
lean_ctor_set(v_reuseFailAlloc_411_, 2, v___x_408_);
v___x_410_ = v_reuseFailAlloc_411_;
goto v_reusejp_409_;
}
v_reusejp_409_:
{
return v___x_410_;
}
}
else
{
lean_object* v___x_413_; 
lean_dec(v_value_402_);
lean_dec(v_key_401_);
if (v_isShared_406_ == 0)
{
lean_ctor_set(v___x_405_, 1, v_b_399_);
lean_ctor_set(v___x_405_, 0, v_a_398_);
v___x_413_ = v___x_405_;
goto v_reusejp_412_;
}
else
{
lean_object* v_reuseFailAlloc_414_; 
v_reuseFailAlloc_414_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_414_, 0, v_a_398_);
lean_ctor_set(v_reuseFailAlloc_414_, 1, v_b_399_);
lean_ctor_set(v_reuseFailAlloc_414_, 2, v_tail_403_);
v___x_413_ = v_reuseFailAlloc_414_;
goto v_reusejp_412_;
}
v_reusejp_412_:
{
return v___x_413_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg(lean_object* v_a_416_, lean_object* v_x_417_){
_start:
{
if (lean_obj_tag(v_x_417_) == 0)
{
uint8_t v___x_418_; 
v___x_418_ = 0;
return v___x_418_;
}
else
{
lean_object* v_key_419_; lean_object* v_tail_420_; uint8_t v___x_421_; 
v_key_419_ = lean_ctor_get(v_x_417_, 0);
v_tail_420_ = lean_ctor_get(v_x_417_, 2);
v___x_421_ = lean_name_eq(v_key_419_, v_a_416_);
if (v___x_421_ == 0)
{
v_x_417_ = v_tail_420_;
goto _start;
}
else
{
return v___x_421_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_a_423_, lean_object* v_x_424_){
_start:
{
uint8_t v_res_425_; lean_object* v_r_426_; 
v_res_425_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg(v_a_423_, v_x_424_);
lean_dec(v_x_424_);
lean_dec(v_a_423_);
v_r_426_ = lean_box(v_res_425_);
return v_r_426_;
}
}
static uint64_t _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8_spec__10___redArg___closed__0(void){
_start:
{
lean_object* v___x_427_; uint64_t v___x_428_; 
v___x_427_ = lean_unsigned_to_nat(1723u);
v___x_428_ = lean_uint64_of_nat(v___x_427_);
return v___x_428_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8_spec__10___redArg(lean_object* v_x_429_, lean_object* v_x_430_){
_start:
{
if (lean_obj_tag(v_x_430_) == 0)
{
return v_x_429_;
}
else
{
lean_object* v_key_431_; lean_object* v_value_432_; lean_object* v_tail_433_; lean_object* v___x_435_; uint8_t v_isShared_436_; uint8_t v_isSharedCheck_459_; 
v_key_431_ = lean_ctor_get(v_x_430_, 0);
v_value_432_ = lean_ctor_get(v_x_430_, 1);
v_tail_433_ = lean_ctor_get(v_x_430_, 2);
v_isSharedCheck_459_ = !lean_is_exclusive(v_x_430_);
if (v_isSharedCheck_459_ == 0)
{
v___x_435_ = v_x_430_;
v_isShared_436_ = v_isSharedCheck_459_;
goto v_resetjp_434_;
}
else
{
lean_inc(v_tail_433_);
lean_inc(v_value_432_);
lean_inc(v_key_431_);
lean_dec(v_x_430_);
v___x_435_ = lean_box(0);
v_isShared_436_ = v_isSharedCheck_459_;
goto v_resetjp_434_;
}
v_resetjp_434_:
{
lean_object* v___x_437_; uint64_t v___y_439_; 
v___x_437_ = lean_array_get_size(v_x_429_);
if (lean_obj_tag(v_key_431_) == 0)
{
uint64_t v___x_457_; 
v___x_457_ = lean_uint64_once(&l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8_spec__10___redArg___closed__0, &l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8_spec__10___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8_spec__10___redArg___closed__0);
v___y_439_ = v___x_457_;
goto v___jp_438_;
}
else
{
uint64_t v_hash_458_; 
v_hash_458_ = lean_ctor_get_uint64(v_key_431_, sizeof(void*)*2);
v___y_439_ = v_hash_458_;
goto v___jp_438_;
}
v___jp_438_:
{
uint64_t v___x_440_; uint64_t v___x_441_; uint64_t v_fold_442_; uint64_t v___x_443_; uint64_t v___x_444_; uint64_t v___x_445_; size_t v___x_446_; size_t v___x_447_; size_t v___x_448_; size_t v___x_449_; size_t v___x_450_; lean_object* v___x_451_; lean_object* v___x_453_; 
v___x_440_ = 32ULL;
v___x_441_ = lean_uint64_shift_right(v___y_439_, v___x_440_);
v_fold_442_ = lean_uint64_xor(v___y_439_, v___x_441_);
v___x_443_ = 16ULL;
v___x_444_ = lean_uint64_shift_right(v_fold_442_, v___x_443_);
v___x_445_ = lean_uint64_xor(v_fold_442_, v___x_444_);
v___x_446_ = lean_uint64_to_usize(v___x_445_);
v___x_447_ = lean_usize_of_nat(v___x_437_);
v___x_448_ = ((size_t)1ULL);
v___x_449_ = lean_usize_sub(v___x_447_, v___x_448_);
v___x_450_ = lean_usize_land(v___x_446_, v___x_449_);
v___x_451_ = lean_array_uget_borrowed(v_x_429_, v___x_450_);
lean_inc(v___x_451_);
if (v_isShared_436_ == 0)
{
lean_ctor_set(v___x_435_, 2, v___x_451_);
v___x_453_ = v___x_435_;
goto v_reusejp_452_;
}
else
{
lean_object* v_reuseFailAlloc_456_; 
v_reuseFailAlloc_456_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_456_, 0, v_key_431_);
lean_ctor_set(v_reuseFailAlloc_456_, 1, v_value_432_);
lean_ctor_set(v_reuseFailAlloc_456_, 2, v___x_451_);
v___x_453_ = v_reuseFailAlloc_456_;
goto v_reusejp_452_;
}
v_reusejp_452_:
{
lean_object* v___x_454_; 
v___x_454_ = lean_array_uset(v_x_429_, v___x_450_, v___x_453_);
v_x_429_ = v___x_454_;
v_x_430_ = v_tail_433_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8___redArg(lean_object* v_i_460_, lean_object* v_source_461_, lean_object* v_target_462_){
_start:
{
lean_object* v___x_463_; uint8_t v___x_464_; 
v___x_463_ = lean_array_get_size(v_source_461_);
v___x_464_ = lean_nat_dec_lt(v_i_460_, v___x_463_);
if (v___x_464_ == 0)
{
lean_dec_ref(v_source_461_);
lean_dec(v_i_460_);
return v_target_462_;
}
else
{
lean_object* v_es_465_; lean_object* v___x_466_; lean_object* v_source_467_; lean_object* v_target_468_; lean_object* v___x_469_; lean_object* v___x_470_; 
v_es_465_ = lean_array_fget(v_source_461_, v_i_460_);
v___x_466_ = lean_box(0);
v_source_467_ = lean_array_fset(v_source_461_, v_i_460_, v___x_466_);
v_target_468_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8_spec__10___redArg(v_target_462_, v_es_465_);
v___x_469_ = lean_unsigned_to_nat(1u);
v___x_470_ = lean_nat_add(v_i_460_, v___x_469_);
lean_dec(v_i_460_);
v_i_460_ = v___x_470_;
v_source_461_ = v_source_467_;
v_target_462_ = v_target_468_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__5___redArg(lean_object* v_data_472_){
_start:
{
lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v_nbuckets_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; 
v___x_473_ = lean_array_get_size(v_data_472_);
v___x_474_ = lean_unsigned_to_nat(2u);
v_nbuckets_475_ = lean_nat_mul(v___x_473_, v___x_474_);
v___x_476_ = lean_unsigned_to_nat(0u);
v___x_477_ = lean_box(0);
v___x_478_ = lean_mk_array(v_nbuckets_475_, v___x_477_);
v___x_479_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8___redArg(v___x_476_, v_data_472_, v___x_478_);
return v___x_479_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2___redArg(lean_object* v_m_480_, lean_object* v_a_481_, lean_object* v_b_482_){
_start:
{
lean_object* v_size_483_; lean_object* v_buckets_484_; lean_object* v___x_486_; uint8_t v_isShared_487_; uint8_t v_isSharedCheck_530_; 
v_size_483_ = lean_ctor_get(v_m_480_, 0);
v_buckets_484_ = lean_ctor_get(v_m_480_, 1);
v_isSharedCheck_530_ = !lean_is_exclusive(v_m_480_);
if (v_isSharedCheck_530_ == 0)
{
v___x_486_ = v_m_480_;
v_isShared_487_ = v_isSharedCheck_530_;
goto v_resetjp_485_;
}
else
{
lean_inc(v_buckets_484_);
lean_inc(v_size_483_);
lean_dec(v_m_480_);
v___x_486_ = lean_box(0);
v_isShared_487_ = v_isSharedCheck_530_;
goto v_resetjp_485_;
}
v_resetjp_485_:
{
lean_object* v___x_488_; uint64_t v___y_490_; 
v___x_488_ = lean_array_get_size(v_buckets_484_);
if (lean_obj_tag(v_a_481_) == 0)
{
uint64_t v___x_528_; 
v___x_528_ = lean_uint64_once(&l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8_spec__10___redArg___closed__0, &l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8_spec__10___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8_spec__10___redArg___closed__0);
v___y_490_ = v___x_528_;
goto v___jp_489_;
}
else
{
uint64_t v_hash_529_; 
v_hash_529_ = lean_ctor_get_uint64(v_a_481_, sizeof(void*)*2);
v___y_490_ = v_hash_529_;
goto v___jp_489_;
}
v___jp_489_:
{
uint64_t v___x_491_; uint64_t v___x_492_; uint64_t v_fold_493_; uint64_t v___x_494_; uint64_t v___x_495_; uint64_t v___x_496_; size_t v___x_497_; size_t v___x_498_; size_t v___x_499_; size_t v___x_500_; size_t v___x_501_; lean_object* v_bkt_502_; uint8_t v___x_503_; 
v___x_491_ = 32ULL;
v___x_492_ = lean_uint64_shift_right(v___y_490_, v___x_491_);
v_fold_493_ = lean_uint64_xor(v___y_490_, v___x_492_);
v___x_494_ = 16ULL;
v___x_495_ = lean_uint64_shift_right(v_fold_493_, v___x_494_);
v___x_496_ = lean_uint64_xor(v_fold_493_, v___x_495_);
v___x_497_ = lean_uint64_to_usize(v___x_496_);
v___x_498_ = lean_usize_of_nat(v___x_488_);
v___x_499_ = ((size_t)1ULL);
v___x_500_ = lean_usize_sub(v___x_498_, v___x_499_);
v___x_501_ = lean_usize_land(v___x_497_, v___x_500_);
v_bkt_502_ = lean_array_uget_borrowed(v_buckets_484_, v___x_501_);
v___x_503_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg(v_a_481_, v_bkt_502_);
if (v___x_503_ == 0)
{
lean_object* v___x_504_; lean_object* v_size_x27_505_; lean_object* v___x_506_; lean_object* v_buckets_x27_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; uint8_t v___x_513_; 
v___x_504_ = lean_unsigned_to_nat(1u);
v_size_x27_505_ = lean_nat_add(v_size_483_, v___x_504_);
lean_dec(v_size_483_);
lean_inc(v_bkt_502_);
v___x_506_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_506_, 0, v_a_481_);
lean_ctor_set(v___x_506_, 1, v_b_482_);
lean_ctor_set(v___x_506_, 2, v_bkt_502_);
v_buckets_x27_507_ = lean_array_uset(v_buckets_484_, v___x_501_, v___x_506_);
v___x_508_ = lean_unsigned_to_nat(4u);
v___x_509_ = lean_nat_mul(v_size_x27_505_, v___x_508_);
v___x_510_ = lean_unsigned_to_nat(3u);
v___x_511_ = lean_nat_div(v___x_509_, v___x_510_);
lean_dec(v___x_509_);
v___x_512_ = lean_array_get_size(v_buckets_x27_507_);
v___x_513_ = lean_nat_dec_le(v___x_511_, v___x_512_);
lean_dec(v___x_511_);
if (v___x_513_ == 0)
{
lean_object* v_val_514_; lean_object* v___x_516_; 
v_val_514_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__5___redArg(v_buckets_x27_507_);
if (v_isShared_487_ == 0)
{
lean_ctor_set(v___x_486_, 1, v_val_514_);
lean_ctor_set(v___x_486_, 0, v_size_x27_505_);
v___x_516_ = v___x_486_;
goto v_reusejp_515_;
}
else
{
lean_object* v_reuseFailAlloc_517_; 
v_reuseFailAlloc_517_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_517_, 0, v_size_x27_505_);
lean_ctor_set(v_reuseFailAlloc_517_, 1, v_val_514_);
v___x_516_ = v_reuseFailAlloc_517_;
goto v_reusejp_515_;
}
v_reusejp_515_:
{
return v___x_516_;
}
}
else
{
lean_object* v___x_519_; 
if (v_isShared_487_ == 0)
{
lean_ctor_set(v___x_486_, 1, v_buckets_x27_507_);
lean_ctor_set(v___x_486_, 0, v_size_x27_505_);
v___x_519_ = v___x_486_;
goto v_reusejp_518_;
}
else
{
lean_object* v_reuseFailAlloc_520_; 
v_reuseFailAlloc_520_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_520_, 0, v_size_x27_505_);
lean_ctor_set(v_reuseFailAlloc_520_, 1, v_buckets_x27_507_);
v___x_519_ = v_reuseFailAlloc_520_;
goto v_reusejp_518_;
}
v_reusejp_518_:
{
return v___x_519_;
}
}
}
else
{
lean_object* v___x_521_; lean_object* v_buckets_x27_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_526_; 
lean_inc(v_bkt_502_);
v___x_521_ = lean_box(0);
v_buckets_x27_522_ = lean_array_uset(v_buckets_484_, v___x_501_, v___x_521_);
v___x_523_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__6___redArg(v_a_481_, v_b_482_, v_bkt_502_);
v___x_524_ = lean_array_uset(v_buckets_x27_522_, v___x_501_, v___x_523_);
if (v_isShared_487_ == 0)
{
lean_ctor_set(v___x_486_, 1, v___x_524_);
v___x_526_ = v___x_486_;
goto v_reusejp_525_;
}
else
{
lean_object* v_reuseFailAlloc_527_; 
v_reuseFailAlloc_527_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_527_, 0, v_size_483_);
lean_ctor_set(v_reuseFailAlloc_527_, 1, v___x_524_);
v___x_526_ = v_reuseFailAlloc_527_;
goto v_reusejp_525_;
}
v_reusejp_525_:
{
return v___x_526_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__3_spec__5___redArg(lean_object* v_x_531_, lean_object* v_x_532_, lean_object* v_x_533_, lean_object* v_x_534_){
_start:
{
lean_object* v_ks_535_; lean_object* v_vs_536_; lean_object* v___x_538_; uint8_t v_isShared_539_; uint8_t v_isSharedCheck_560_; 
v_ks_535_ = lean_ctor_get(v_x_531_, 0);
v_vs_536_ = lean_ctor_get(v_x_531_, 1);
v_isSharedCheck_560_ = !lean_is_exclusive(v_x_531_);
if (v_isSharedCheck_560_ == 0)
{
v___x_538_ = v_x_531_;
v_isShared_539_ = v_isSharedCheck_560_;
goto v_resetjp_537_;
}
else
{
lean_inc(v_vs_536_);
lean_inc(v_ks_535_);
lean_dec(v_x_531_);
v___x_538_ = lean_box(0);
v_isShared_539_ = v_isSharedCheck_560_;
goto v_resetjp_537_;
}
v_resetjp_537_:
{
lean_object* v___x_540_; uint8_t v___x_541_; 
v___x_540_ = lean_array_get_size(v_ks_535_);
v___x_541_ = lean_nat_dec_lt(v_x_532_, v___x_540_);
if (v___x_541_ == 0)
{
lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_545_; 
lean_dec(v_x_532_);
v___x_542_ = lean_array_push(v_ks_535_, v_x_533_);
v___x_543_ = lean_array_push(v_vs_536_, v_x_534_);
if (v_isShared_539_ == 0)
{
lean_ctor_set(v___x_538_, 1, v___x_543_);
lean_ctor_set(v___x_538_, 0, v___x_542_);
v___x_545_ = v___x_538_;
goto v_reusejp_544_;
}
else
{
lean_object* v_reuseFailAlloc_546_; 
v_reuseFailAlloc_546_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_546_, 0, v___x_542_);
lean_ctor_set(v_reuseFailAlloc_546_, 1, v___x_543_);
v___x_545_ = v_reuseFailAlloc_546_;
goto v_reusejp_544_;
}
v_reusejp_544_:
{
return v___x_545_;
}
}
else
{
lean_object* v_k_x27_547_; uint8_t v___x_548_; 
v_k_x27_547_ = lean_array_fget_borrowed(v_ks_535_, v_x_532_);
v___x_548_ = lean_name_eq(v_x_533_, v_k_x27_547_);
if (v___x_548_ == 0)
{
lean_object* v___x_550_; 
if (v_isShared_539_ == 0)
{
v___x_550_ = v___x_538_;
goto v_reusejp_549_;
}
else
{
lean_object* v_reuseFailAlloc_554_; 
v_reuseFailAlloc_554_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_554_, 0, v_ks_535_);
lean_ctor_set(v_reuseFailAlloc_554_, 1, v_vs_536_);
v___x_550_ = v_reuseFailAlloc_554_;
goto v_reusejp_549_;
}
v_reusejp_549_:
{
lean_object* v___x_551_; lean_object* v___x_552_; 
v___x_551_ = lean_unsigned_to_nat(1u);
v___x_552_ = lean_nat_add(v_x_532_, v___x_551_);
lean_dec(v_x_532_);
v_x_531_ = v___x_550_;
v_x_532_ = v___x_552_;
goto _start;
}
}
else
{
lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_558_; 
v___x_555_ = lean_array_fset(v_ks_535_, v_x_532_, v_x_533_);
v___x_556_ = lean_array_fset(v_vs_536_, v_x_532_, v_x_534_);
lean_dec(v_x_532_);
if (v_isShared_539_ == 0)
{
lean_ctor_set(v___x_538_, 1, v___x_556_);
lean_ctor_set(v___x_538_, 0, v___x_555_);
v___x_558_ = v___x_538_;
goto v_reusejp_557_;
}
else
{
lean_object* v_reuseFailAlloc_559_; 
v_reuseFailAlloc_559_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_559_, 0, v___x_555_);
lean_ctor_set(v_reuseFailAlloc_559_, 1, v___x_556_);
v___x_558_ = v_reuseFailAlloc_559_;
goto v_reusejp_557_;
}
v_reusejp_557_:
{
return v___x_558_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__3___redArg(lean_object* v_n_561_, lean_object* v_k_562_, lean_object* v_v_563_){
_start:
{
lean_object* v___x_564_; lean_object* v___x_565_; 
v___x_564_ = lean_unsigned_to_nat(0u);
v___x_565_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__3_spec__5___redArg(v_n_561_, v___x_564_, v_k_562_, v_v_563_);
return v___x_565_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2___redArg___closed__0(void){
_start:
{
size_t v___x_566_; size_t v___x_567_; size_t v___x_568_; 
v___x_566_ = ((size_t)5ULL);
v___x_567_ = ((size_t)1ULL);
v___x_568_ = lean_usize_shift_left(v___x_567_, v___x_566_);
return v___x_568_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2___redArg___closed__1(void){
_start:
{
size_t v___x_569_; size_t v___x_570_; size_t v___x_571_; 
v___x_569_ = ((size_t)1ULL);
v___x_570_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2___redArg___closed__0);
v___x_571_ = lean_usize_sub(v___x_570_, v___x_569_);
return v___x_571_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_572_; 
v___x_572_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_572_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2___redArg(lean_object* v_x_573_, size_t v_x_574_, size_t v_x_575_, lean_object* v_x_576_, lean_object* v_x_577_){
_start:
{
if (lean_obj_tag(v_x_573_) == 0)
{
lean_object* v_es_578_; size_t v___x_579_; size_t v___x_580_; size_t v___x_581_; size_t v___x_582_; lean_object* v_j_583_; lean_object* v___x_584_; uint8_t v___x_585_; 
v_es_578_ = lean_ctor_get(v_x_573_, 0);
v___x_579_ = ((size_t)5ULL);
v___x_580_ = ((size_t)1ULL);
v___x_581_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2___redArg___closed__1);
v___x_582_ = lean_usize_land(v_x_574_, v___x_581_);
v_j_583_ = lean_usize_to_nat(v___x_582_);
v___x_584_ = lean_array_get_size(v_es_578_);
v___x_585_ = lean_nat_dec_lt(v_j_583_, v___x_584_);
if (v___x_585_ == 0)
{
lean_dec(v_j_583_);
lean_dec(v_x_577_);
lean_dec(v_x_576_);
return v_x_573_;
}
else
{
lean_object* v___x_587_; uint8_t v_isShared_588_; uint8_t v_isSharedCheck_622_; 
lean_inc_ref(v_es_578_);
v_isSharedCheck_622_ = !lean_is_exclusive(v_x_573_);
if (v_isSharedCheck_622_ == 0)
{
lean_object* v_unused_623_; 
v_unused_623_ = lean_ctor_get(v_x_573_, 0);
lean_dec(v_unused_623_);
v___x_587_ = v_x_573_;
v_isShared_588_ = v_isSharedCheck_622_;
goto v_resetjp_586_;
}
else
{
lean_dec(v_x_573_);
v___x_587_ = lean_box(0);
v_isShared_588_ = v_isSharedCheck_622_;
goto v_resetjp_586_;
}
v_resetjp_586_:
{
lean_object* v_v_589_; lean_object* v___x_590_; lean_object* v_xs_x27_591_; lean_object* v___y_593_; 
v_v_589_ = lean_array_fget(v_es_578_, v_j_583_);
v___x_590_ = lean_box(0);
v_xs_x27_591_ = lean_array_fset(v_es_578_, v_j_583_, v___x_590_);
switch(lean_obj_tag(v_v_589_))
{
case 0:
{
lean_object* v_key_598_; lean_object* v_val_599_; lean_object* v___x_601_; uint8_t v_isShared_602_; uint8_t v_isSharedCheck_609_; 
v_key_598_ = lean_ctor_get(v_v_589_, 0);
v_val_599_ = lean_ctor_get(v_v_589_, 1);
v_isSharedCheck_609_ = !lean_is_exclusive(v_v_589_);
if (v_isSharedCheck_609_ == 0)
{
v___x_601_ = v_v_589_;
v_isShared_602_ = v_isSharedCheck_609_;
goto v_resetjp_600_;
}
else
{
lean_inc(v_val_599_);
lean_inc(v_key_598_);
lean_dec(v_v_589_);
v___x_601_ = lean_box(0);
v_isShared_602_ = v_isSharedCheck_609_;
goto v_resetjp_600_;
}
v_resetjp_600_:
{
uint8_t v___x_603_; 
v___x_603_ = lean_name_eq(v_x_576_, v_key_598_);
if (v___x_603_ == 0)
{
lean_object* v___x_604_; lean_object* v___x_605_; 
lean_del_object(v___x_601_);
v___x_604_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_598_, v_val_599_, v_x_576_, v_x_577_);
v___x_605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_605_, 0, v___x_604_);
v___y_593_ = v___x_605_;
goto v___jp_592_;
}
else
{
lean_object* v___x_607_; 
lean_dec(v_val_599_);
lean_dec(v_key_598_);
if (v_isShared_602_ == 0)
{
lean_ctor_set(v___x_601_, 1, v_x_577_);
lean_ctor_set(v___x_601_, 0, v_x_576_);
v___x_607_ = v___x_601_;
goto v_reusejp_606_;
}
else
{
lean_object* v_reuseFailAlloc_608_; 
v_reuseFailAlloc_608_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_608_, 0, v_x_576_);
lean_ctor_set(v_reuseFailAlloc_608_, 1, v_x_577_);
v___x_607_ = v_reuseFailAlloc_608_;
goto v_reusejp_606_;
}
v_reusejp_606_:
{
v___y_593_ = v___x_607_;
goto v___jp_592_;
}
}
}
}
case 1:
{
lean_object* v_node_610_; lean_object* v___x_612_; uint8_t v_isShared_613_; uint8_t v_isSharedCheck_620_; 
v_node_610_ = lean_ctor_get(v_v_589_, 0);
v_isSharedCheck_620_ = !lean_is_exclusive(v_v_589_);
if (v_isSharedCheck_620_ == 0)
{
v___x_612_ = v_v_589_;
v_isShared_613_ = v_isSharedCheck_620_;
goto v_resetjp_611_;
}
else
{
lean_inc(v_node_610_);
lean_dec(v_v_589_);
v___x_612_ = lean_box(0);
v_isShared_613_ = v_isSharedCheck_620_;
goto v_resetjp_611_;
}
v_resetjp_611_:
{
size_t v___x_614_; size_t v___x_615_; lean_object* v___x_616_; lean_object* v___x_618_; 
v___x_614_ = lean_usize_shift_right(v_x_574_, v___x_579_);
v___x_615_ = lean_usize_add(v_x_575_, v___x_580_);
v___x_616_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2___redArg(v_node_610_, v___x_614_, v___x_615_, v_x_576_, v_x_577_);
if (v_isShared_613_ == 0)
{
lean_ctor_set(v___x_612_, 0, v___x_616_);
v___x_618_ = v___x_612_;
goto v_reusejp_617_;
}
else
{
lean_object* v_reuseFailAlloc_619_; 
v_reuseFailAlloc_619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_619_, 0, v___x_616_);
v___x_618_ = v_reuseFailAlloc_619_;
goto v_reusejp_617_;
}
v_reusejp_617_:
{
v___y_593_ = v___x_618_;
goto v___jp_592_;
}
}
}
default: 
{
lean_object* v___x_621_; 
v___x_621_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_621_, 0, v_x_576_);
lean_ctor_set(v___x_621_, 1, v_x_577_);
v___y_593_ = v___x_621_;
goto v___jp_592_;
}
}
v___jp_592_:
{
lean_object* v___x_594_; lean_object* v___x_596_; 
v___x_594_ = lean_array_fset(v_xs_x27_591_, v_j_583_, v___y_593_);
lean_dec(v_j_583_);
if (v_isShared_588_ == 0)
{
lean_ctor_set(v___x_587_, 0, v___x_594_);
v___x_596_ = v___x_587_;
goto v_reusejp_595_;
}
else
{
lean_object* v_reuseFailAlloc_597_; 
v_reuseFailAlloc_597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_597_, 0, v___x_594_);
v___x_596_ = v_reuseFailAlloc_597_;
goto v_reusejp_595_;
}
v_reusejp_595_:
{
return v___x_596_;
}
}
}
}
}
else
{
lean_object* v_ks_624_; lean_object* v_vs_625_; lean_object* v___x_627_; uint8_t v_isShared_628_; uint8_t v_isSharedCheck_645_; 
v_ks_624_ = lean_ctor_get(v_x_573_, 0);
v_vs_625_ = lean_ctor_get(v_x_573_, 1);
v_isSharedCheck_645_ = !lean_is_exclusive(v_x_573_);
if (v_isSharedCheck_645_ == 0)
{
v___x_627_ = v_x_573_;
v_isShared_628_ = v_isSharedCheck_645_;
goto v_resetjp_626_;
}
else
{
lean_inc(v_vs_625_);
lean_inc(v_ks_624_);
lean_dec(v_x_573_);
v___x_627_ = lean_box(0);
v_isShared_628_ = v_isSharedCheck_645_;
goto v_resetjp_626_;
}
v_resetjp_626_:
{
lean_object* v___x_630_; 
if (v_isShared_628_ == 0)
{
v___x_630_ = v___x_627_;
goto v_reusejp_629_;
}
else
{
lean_object* v_reuseFailAlloc_644_; 
v_reuseFailAlloc_644_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_644_, 0, v_ks_624_);
lean_ctor_set(v_reuseFailAlloc_644_, 1, v_vs_625_);
v___x_630_ = v_reuseFailAlloc_644_;
goto v_reusejp_629_;
}
v_reusejp_629_:
{
lean_object* v_newNode_631_; uint8_t v___y_633_; size_t v___x_639_; uint8_t v___x_640_; 
v_newNode_631_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__3___redArg(v___x_630_, v_x_576_, v_x_577_);
v___x_639_ = ((size_t)7ULL);
v___x_640_ = lean_usize_dec_le(v___x_639_, v_x_575_);
if (v___x_640_ == 0)
{
lean_object* v___x_641_; lean_object* v___x_642_; uint8_t v___x_643_; 
v___x_641_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_631_);
v___x_642_ = lean_unsigned_to_nat(4u);
v___x_643_ = lean_nat_dec_lt(v___x_641_, v___x_642_);
lean_dec(v___x_641_);
v___y_633_ = v___x_643_;
goto v___jp_632_;
}
else
{
v___y_633_ = v___x_640_;
goto v___jp_632_;
}
v___jp_632_:
{
if (v___y_633_ == 0)
{
lean_object* v_ks_634_; lean_object* v_vs_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; 
v_ks_634_ = lean_ctor_get(v_newNode_631_, 0);
lean_inc_ref(v_ks_634_);
v_vs_635_ = lean_ctor_get(v_newNode_631_, 1);
lean_inc_ref(v_vs_635_);
lean_dec_ref(v_newNode_631_);
v___x_636_ = lean_unsigned_to_nat(0u);
v___x_637_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2___redArg___closed__2);
v___x_638_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__4___redArg(v_x_575_, v_ks_634_, v_vs_635_, v___x_636_, v___x_637_);
lean_dec_ref(v_vs_635_);
lean_dec_ref(v_ks_634_);
return v___x_638_;
}
else
{
return v_newNode_631_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__4___redArg(size_t v_depth_646_, lean_object* v_keys_647_, lean_object* v_vals_648_, lean_object* v_i_649_, lean_object* v_entries_650_){
_start:
{
lean_object* v___x_651_; uint8_t v___x_652_; 
v___x_651_ = lean_array_get_size(v_keys_647_);
v___x_652_ = lean_nat_dec_lt(v_i_649_, v___x_651_);
if (v___x_652_ == 0)
{
lean_dec(v_i_649_);
return v_entries_650_;
}
else
{
lean_object* v_k_653_; lean_object* v_v_654_; uint64_t v___y_656_; 
v_k_653_ = lean_array_fget_borrowed(v_keys_647_, v_i_649_);
v_v_654_ = lean_array_fget_borrowed(v_vals_648_, v_i_649_);
if (lean_obj_tag(v_k_653_) == 0)
{
uint64_t v___x_667_; 
v___x_667_ = lean_uint64_once(&l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8_spec__10___redArg___closed__0, &l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8_spec__10___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8_spec__10___redArg___closed__0);
v___y_656_ = v___x_667_;
goto v___jp_655_;
}
else
{
uint64_t v_hash_668_; 
v_hash_668_ = lean_ctor_get_uint64(v_k_653_, sizeof(void*)*2);
v___y_656_ = v_hash_668_;
goto v___jp_655_;
}
v___jp_655_:
{
size_t v_h_657_; size_t v___x_658_; lean_object* v___x_659_; size_t v___x_660_; size_t v___x_661_; size_t v___x_662_; size_t v_h_663_; lean_object* v___x_664_; lean_object* v___x_665_; 
v_h_657_ = lean_uint64_to_usize(v___y_656_);
v___x_658_ = ((size_t)5ULL);
v___x_659_ = lean_unsigned_to_nat(1u);
v___x_660_ = ((size_t)1ULL);
v___x_661_ = lean_usize_sub(v_depth_646_, v___x_660_);
v___x_662_ = lean_usize_mul(v___x_658_, v___x_661_);
v_h_663_ = lean_usize_shift_right(v_h_657_, v___x_662_);
v___x_664_ = lean_nat_add(v_i_649_, v___x_659_);
lean_dec(v_i_649_);
lean_inc(v_v_654_);
lean_inc(v_k_653_);
v___x_665_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2___redArg(v_entries_650_, v_h_663_, v_depth_646_, v_k_653_, v_v_654_);
v_i_649_ = v___x_664_;
v_entries_650_ = v___x_665_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_depth_669_, lean_object* v_keys_670_, lean_object* v_vals_671_, lean_object* v_i_672_, lean_object* v_entries_673_){
_start:
{
size_t v_depth_boxed_674_; lean_object* v_res_675_; 
v_depth_boxed_674_ = lean_unbox_usize(v_depth_669_);
lean_dec(v_depth_669_);
v_res_675_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__4___redArg(v_depth_boxed_674_, v_keys_670_, v_vals_671_, v_i_672_, v_entries_673_);
lean_dec_ref(v_vals_671_);
lean_dec_ref(v_keys_670_);
return v_res_675_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_x_676_, lean_object* v_x_677_, lean_object* v_x_678_, lean_object* v_x_679_, lean_object* v_x_680_){
_start:
{
size_t v_x_1111__boxed_681_; size_t v_x_1112__boxed_682_; lean_object* v_res_683_; 
v_x_1111__boxed_681_ = lean_unbox_usize(v_x_677_);
lean_dec(v_x_677_);
v_x_1112__boxed_682_ = lean_unbox_usize(v_x_678_);
lean_dec(v_x_678_);
v_res_683_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2___redArg(v_x_676_, v_x_1111__boxed_681_, v_x_1112__boxed_682_, v_x_679_, v_x_680_);
return v_res_683_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1___redArg(lean_object* v_x_684_, lean_object* v_x_685_, lean_object* v_x_686_){
_start:
{
uint64_t v___y_688_; 
if (lean_obj_tag(v_x_685_) == 0)
{
uint64_t v___x_692_; 
v___x_692_ = lean_uint64_once(&l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8_spec__10___redArg___closed__0, &l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8_spec__10___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8_spec__10___redArg___closed__0);
v___y_688_ = v___x_692_;
goto v___jp_687_;
}
else
{
uint64_t v_hash_693_; 
v_hash_693_ = lean_ctor_get_uint64(v_x_685_, sizeof(void*)*2);
v___y_688_ = v_hash_693_;
goto v___jp_687_;
}
v___jp_687_:
{
size_t v___x_689_; size_t v___x_690_; lean_object* v___x_691_; 
v___x_689_ = lean_uint64_to_usize(v___y_688_);
v___x_690_ = ((size_t)1ULL);
v___x_691_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2___redArg(v_x_684_, v___x_689_, v___x_690_, v_x_685_, v_x_686_);
return v___x_691_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1___redArg(lean_object* v_x_694_, lean_object* v_x_695_, lean_object* v_x_696_){
_start:
{
uint8_t v_stage_u2081_697_; 
v_stage_u2081_697_ = lean_ctor_get_uint8(v_x_694_, sizeof(void*)*2);
if (v_stage_u2081_697_ == 0)
{
lean_object* v_map_u2081_698_; lean_object* v_map_u2082_699_; lean_object* v___x_701_; uint8_t v_isShared_702_; uint8_t v_isSharedCheck_707_; 
v_map_u2081_698_ = lean_ctor_get(v_x_694_, 0);
v_map_u2082_699_ = lean_ctor_get(v_x_694_, 1);
v_isSharedCheck_707_ = !lean_is_exclusive(v_x_694_);
if (v_isSharedCheck_707_ == 0)
{
v___x_701_ = v_x_694_;
v_isShared_702_ = v_isSharedCheck_707_;
goto v_resetjp_700_;
}
else
{
lean_inc(v_map_u2082_699_);
lean_inc(v_map_u2081_698_);
lean_dec(v_x_694_);
v___x_701_ = lean_box(0);
v_isShared_702_ = v_isSharedCheck_707_;
goto v_resetjp_700_;
}
v_resetjp_700_:
{
lean_object* v___x_703_; lean_object* v___x_705_; 
v___x_703_ = l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1___redArg(v_map_u2082_699_, v_x_695_, v_x_696_);
if (v_isShared_702_ == 0)
{
lean_ctor_set(v___x_701_, 1, v___x_703_);
v___x_705_ = v___x_701_;
goto v_reusejp_704_;
}
else
{
lean_object* v_reuseFailAlloc_706_; 
v_reuseFailAlloc_706_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_706_, 0, v_map_u2081_698_);
lean_ctor_set(v_reuseFailAlloc_706_, 1, v___x_703_);
lean_ctor_set_uint8(v_reuseFailAlloc_706_, sizeof(void*)*2, v_stage_u2081_697_);
v___x_705_ = v_reuseFailAlloc_706_;
goto v_reusejp_704_;
}
v_reusejp_704_:
{
return v___x_705_;
}
}
}
else
{
lean_object* v_map_u2081_708_; lean_object* v_map_u2082_709_; lean_object* v___x_711_; uint8_t v_isShared_712_; uint8_t v_isSharedCheck_717_; 
v_map_u2081_708_ = lean_ctor_get(v_x_694_, 0);
v_map_u2082_709_ = lean_ctor_get(v_x_694_, 1);
v_isSharedCheck_717_ = !lean_is_exclusive(v_x_694_);
if (v_isSharedCheck_717_ == 0)
{
v___x_711_ = v_x_694_;
v_isShared_712_ = v_isSharedCheck_717_;
goto v_resetjp_710_;
}
else
{
lean_inc(v_map_u2082_709_);
lean_inc(v_map_u2081_708_);
lean_dec(v_x_694_);
v___x_711_ = lean_box(0);
v_isShared_712_ = v_isSharedCheck_717_;
goto v_resetjp_710_;
}
v_resetjp_710_:
{
lean_object* v___x_713_; lean_object* v___x_715_; 
v___x_713_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2___redArg(v_map_u2081_708_, v_x_695_, v_x_696_);
if (v_isShared_712_ == 0)
{
lean_ctor_set(v___x_711_, 0, v___x_713_);
v___x_715_ = v___x_711_;
goto v_reusejp_714_;
}
else
{
lean_object* v_reuseFailAlloc_716_; 
v_reuseFailAlloc_716_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_716_, 0, v___x_713_);
lean_ctor_set(v_reuseFailAlloc_716_, 1, v_map_u2082_709_);
lean_ctor_set_uint8(v_reuseFailAlloc_716_, sizeof(void*)*2, v_stage_u2081_697_);
v___x_715_ = v_reuseFailAlloc_716_;
goto v_reusejp_714_;
}
v_reusejp_714_:
{
return v___x_715_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__1_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_(lean_object* v_d_718_, lean_object* v_x_719_){
_start:
{
lean_object* v_fst_720_; lean_object* v_snd_721_; lean_object* v___x_722_; 
v_fst_720_ = lean_ctor_get(v_x_719_, 0);
lean_inc(v_fst_720_);
v_snd_721_ = lean_ctor_get(v_x_719_, 1);
lean_inc(v_snd_721_);
lean_dec_ref(v_x_719_);
v___x_722_ = l_Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1___redArg(v_d_718_, v_fst_720_, v_snd_721_);
return v___x_722_;
}
}
static lean_object* _init_l_Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; 
v___x_729_ = lean_box(0);
v___x_730_ = lean_unsigned_to_nat(16u);
v___x_731_ = lean_mk_array(v___x_730_, v___x_729_);
return v___x_731_;
}
}
static lean_object* _init_l_Lean_initFn___closed__6_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; 
v___x_732_ = lean_obj_once(&l_Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_, &l_Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__once, _init_l_Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_);
v___x_733_ = lean_unsigned_to_nat(0u);
v___x_734_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_734_, 0, v___x_733_);
lean_ctor_set(v___x_734_, 1, v___x_732_);
return v___x_734_;
}
}
static lean_object* _init_l_Lean_initFn___closed__7_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_735_; 
v___x_735_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_735_;
}
}
static lean_object* _init_l_Lean_initFn___closed__8_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_736_; lean_object* v___x_737_; 
v___x_736_ = lean_obj_once(&l_Lean_initFn___closed__7_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_, &l_Lean_initFn___closed__7_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__once, _init_l_Lean_initFn___closed__7_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_);
v___x_737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_737_, 0, v___x_736_);
return v___x_737_;
}
}
static lean_object* _init_l_Lean_initFn___closed__9_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_738_; lean_object* v___x_739_; uint8_t v___x_740_; lean_object* v___x_741_; 
v___x_738_ = lean_obj_once(&l_Lean_initFn___closed__8_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_, &l_Lean_initFn___closed__8_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__once, _init_l_Lean_initFn___closed__8_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_);
v___x_739_ = lean_obj_once(&l_Lean_initFn___closed__6_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_, &l_Lean_initFn___closed__6_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__once, _init_l_Lean_initFn___closed__6_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_);
v___x_740_ = 1;
v___x_741_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_741_, 0, v___x_739_);
lean_ctor_set(v___x_741_, 1, v___x_738_);
lean_ctor_set_uint8(v___x_741_, sizeof(void*)*2, v___x_740_);
return v___x_741_;
}
}
static lean_object* _init_l_Lean_initFn___closed__10_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_742_; lean_object* v___f_743_; lean_object* v___x_744_; lean_object* v___f_745_; lean_object* v___x_746_; lean_object* v___x_747_; 
v___f_742_ = ((lean_object*)(l_Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_));
v___f_743_ = ((lean_object*)(l_Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_));
v___x_744_ = lean_obj_once(&l_Lean_initFn___closed__9_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_, &l_Lean_initFn___closed__9_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__once, _init_l_Lean_initFn___closed__9_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_);
v___f_745_ = ((lean_object*)(l_Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_));
v___x_746_ = ((lean_object*)(l_Lean_initFn___closed__4_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_));
v___x_747_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_747_, 0, v___x_746_);
lean_ctor_set(v___x_747_, 1, v___f_745_);
lean_ctor_set(v___x_747_, 2, v___x_744_);
lean_ctor_set(v___x_747_, 3, v___f_743_);
lean_ctor_set(v___x_747_, 4, v___f_742_);
return v___x_747_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_749_; lean_object* v___x_750_; 
v___x_749_ = lean_obj_once(&l_Lean_initFn___closed__10_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_, &l_Lean_initFn___closed__10_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__once, _init_l_Lean_initFn___closed__10_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_);
v___x_750_ = l_Lean_registerSimpleScopedEnvExtension___redArg(v___x_749_);
return v___x_750_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2____boxed(lean_object* v_a_751_){
_start:
{
lean_object* v_res_752_; 
v_res_752_ = l_Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_();
return v_res_752_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1(lean_object* v_00_u03b2_753_, lean_object* v_x_754_, lean_object* v_x_755_, lean_object* v_x_756_){
_start:
{
lean_object* v___x_757_; 
v___x_757_ = l_Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1___redArg(v_x_754_, v_x_755_, v_x_756_);
return v___x_757_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1(lean_object* v_00_u03b2_758_, lean_object* v_x_759_, lean_object* v_x_760_, lean_object* v_x_761_){
_start:
{
lean_object* v___x_762_; 
v___x_762_ = l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1___redArg(v_x_759_, v_x_760_, v_x_761_);
return v___x_762_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2(lean_object* v_00_u03b2_763_, lean_object* v_m_764_, lean_object* v_a_765_, lean_object* v_b_766_){
_start:
{
lean_object* v___x_767_; 
v___x_767_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2___redArg(v_m_764_, v_a_765_, v_b_766_);
return v___x_767_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2(lean_object* v_00_u03b2_768_, lean_object* v_x_769_, size_t v_x_770_, size_t v_x_771_, lean_object* v_x_772_, lean_object* v_x_773_){
_start:
{
lean_object* v___x_774_; 
v___x_774_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2___redArg(v_x_769_, v_x_770_, v_x_771_, v_x_772_, v_x_773_);
return v___x_774_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2___boxed(lean_object* v_00_u03b2_775_, lean_object* v_x_776_, lean_object* v_x_777_, lean_object* v_x_778_, lean_object* v_x_779_, lean_object* v_x_780_){
_start:
{
size_t v_x_1452__boxed_781_; size_t v_x_1453__boxed_782_; lean_object* v_res_783_; 
v_x_1452__boxed_781_ = lean_unbox_usize(v_x_777_);
lean_dec(v_x_777_);
v_x_1453__boxed_782_ = lean_unbox_usize(v_x_778_);
lean_dec(v_x_778_);
v_res_783_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2(v_00_u03b2_775_, v_x_776_, v_x_1452__boxed_781_, v_x_1453__boxed_782_, v_x_779_, v_x_780_);
return v_res_783_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__4(lean_object* v_00_u03b2_784_, lean_object* v_a_785_, lean_object* v_x_786_){
_start:
{
uint8_t v___x_787_; 
v___x_787_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg(v_a_785_, v_x_786_);
return v___x_787_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b2_788_, lean_object* v_a_789_, lean_object* v_x_790_){
_start:
{
uint8_t v_res_791_; lean_object* v_r_792_; 
v_res_791_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__4(v_00_u03b2_788_, v_a_789_, v_x_790_);
lean_dec(v_x_790_);
lean_dec(v_a_789_);
v_r_792_ = lean_box(v_res_791_);
return v_r_792_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__5(lean_object* v_00_u03b2_793_, lean_object* v_data_794_){
_start:
{
lean_object* v___x_795_; 
v___x_795_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__5___redArg(v_data_794_);
return v___x_795_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__6(lean_object* v_00_u03b2_796_, lean_object* v_a_797_, lean_object* v_b_798_, lean_object* v_x_799_){
_start:
{
lean_object* v___x_800_; 
v___x_800_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__6___redArg(v_a_797_, v_b_798_, v_x_799_);
return v___x_800_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_801_, lean_object* v_n_802_, lean_object* v_k_803_, lean_object* v_v_804_){
_start:
{
lean_object* v___x_805_; 
v___x_805_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__3___redArg(v_n_802_, v_k_803_, v_v_804_);
return v___x_805_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_806_, size_t v_depth_807_, lean_object* v_keys_808_, lean_object* v_vals_809_, lean_object* v_heq_810_, lean_object* v_i_811_, lean_object* v_entries_812_){
_start:
{
lean_object* v___x_813_; 
v___x_813_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__4___redArg(v_depth_807_, v_keys_808_, v_vals_809_, v_i_811_, v_entries_812_);
return v___x_813_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b2_814_, lean_object* v_depth_815_, lean_object* v_keys_816_, lean_object* v_vals_817_, lean_object* v_heq_818_, lean_object* v_i_819_, lean_object* v_entries_820_){
_start:
{
size_t v_depth_boxed_821_; lean_object* v_res_822_; 
v_depth_boxed_821_ = lean_unbox_usize(v_depth_815_);
lean_dec(v_depth_815_);
v_res_822_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__4(v_00_u03b2_814_, v_depth_boxed_821_, v_keys_816_, v_vals_817_, v_heq_818_, v_i_819_, v_entries_820_);
lean_dec_ref(v_vals_817_);
lean_dec_ref(v_keys_816_);
return v_res_822_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8(lean_object* v_00_u03b2_823_, lean_object* v_i_824_, lean_object* v_source_825_, lean_object* v_target_826_){
_start:
{
lean_object* v___x_827_; 
v___x_827_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8___redArg(v_i_824_, v_source_825_, v_target_826_);
return v___x_827_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__3_spec__5(lean_object* v_00_u03b2_828_, lean_object* v_x_829_, lean_object* v_x_830_, lean_object* v_x_831_, lean_object* v_x_832_){
_start:
{
lean_object* v___x_833_; 
v___x_833_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__3_spec__5___redArg(v_x_829_, v_x_830_, v_x_831_, v_x_832_);
return v___x_833_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8_spec__10(lean_object* v_00_u03b2_834_, lean_object* v_x_835_, lean_object* v_x_836_){
_start:
{
lean_object* v___x_837_; 
v___x_837_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8_spec__10___redArg(v_x_835_, v_x_836_);
return v___x_837_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_getReducibilityStatusCore_spec__1___redArg(lean_object* v_as_838_, lean_object* v_k_839_, lean_object* v_x_840_, lean_object* v_x_841_){
_start:
{
lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v_m_844_; lean_object* v_a_845_; uint8_t v___x_846_; 
v___x_842_ = lean_nat_add(v_x_840_, v_x_841_);
v___x_843_ = lean_unsigned_to_nat(1u);
v_m_844_ = lean_nat_shiftr(v___x_842_, v___x_843_);
lean_dec(v___x_842_);
v_a_845_ = lean_array_fget_borrowed(v_as_838_, v_m_844_);
v___x_846_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__1___redArg___lam__0(v_a_845_, v_k_839_);
if (v___x_846_ == 0)
{
uint8_t v___x_847_; 
lean_dec(v_x_841_);
v___x_847_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__1___redArg___lam__0(v_k_839_, v_a_845_);
if (v___x_847_ == 0)
{
lean_object* v___x_848_; 
lean_dec(v_m_844_);
lean_dec(v_x_840_);
lean_inc(v_a_845_);
v___x_848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_848_, 0, v_a_845_);
return v___x_848_;
}
else
{
lean_object* v___x_849_; uint8_t v___x_850_; 
v___x_849_ = lean_unsigned_to_nat(0u);
v___x_850_ = lean_nat_dec_eq(v_m_844_, v___x_849_);
if (v___x_850_ == 0)
{
lean_object* v___x_851_; uint8_t v___x_852_; 
v___x_851_ = lean_nat_sub(v_m_844_, v___x_843_);
lean_dec(v_m_844_);
v___x_852_ = lean_nat_dec_lt(v___x_851_, v_x_840_);
if (v___x_852_ == 0)
{
v_x_841_ = v___x_851_;
goto _start;
}
else
{
lean_object* v___x_854_; 
lean_dec(v___x_851_);
lean_dec(v_x_840_);
v___x_854_ = lean_box(0);
return v___x_854_;
}
}
else
{
lean_object* v___x_855_; 
lean_dec(v_m_844_);
lean_dec(v_x_840_);
v___x_855_ = lean_box(0);
return v___x_855_;
}
}
}
else
{
lean_object* v___x_856_; uint8_t v___x_857_; 
lean_dec(v_x_840_);
v___x_856_ = lean_nat_add(v_m_844_, v___x_843_);
lean_dec(v_m_844_);
v___x_857_ = lean_nat_dec_le(v___x_856_, v_x_841_);
if (v___x_857_ == 0)
{
lean_object* v___x_858_; 
lean_dec(v___x_856_);
lean_dec(v_x_841_);
v___x_858_ = lean_box(0);
return v___x_858_;
}
else
{
v_x_840_ = v___x_856_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_getReducibilityStatusCore_spec__1___redArg___boxed(lean_object* v_as_860_, lean_object* v_k_861_, lean_object* v_x_862_, lean_object* v_x_863_){
_start:
{
lean_object* v_res_864_; 
v_res_864_ = l_Array_binSearchAux___at___00Lean_getReducibilityStatusCore_spec__1___redArg(v_as_860_, v_k_861_, v_x_862_, v_x_863_);
lean_dec_ref(v_k_861_);
lean_dec_ref(v_as_860_);
return v_res_864_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_keys_865_, lean_object* v_vals_866_, lean_object* v_i_867_, lean_object* v_k_868_){
_start:
{
lean_object* v___x_869_; uint8_t v___x_870_; 
v___x_869_ = lean_array_get_size(v_keys_865_);
v___x_870_ = lean_nat_dec_lt(v_i_867_, v___x_869_);
if (v___x_870_ == 0)
{
lean_object* v___x_871_; 
lean_dec(v_i_867_);
v___x_871_ = lean_box(0);
return v___x_871_;
}
else
{
lean_object* v_k_x27_872_; uint8_t v___x_873_; 
v_k_x27_872_ = lean_array_fget_borrowed(v_keys_865_, v_i_867_);
v___x_873_ = lean_name_eq(v_k_868_, v_k_x27_872_);
if (v___x_873_ == 0)
{
lean_object* v___x_874_; lean_object* v___x_875_; 
v___x_874_ = lean_unsigned_to_nat(1u);
v___x_875_ = lean_nat_add(v_i_867_, v___x_874_);
lean_dec(v_i_867_);
v_i_867_ = v___x_875_;
goto _start;
}
else
{
lean_object* v___x_877_; lean_object* v___x_878_; 
v___x_877_ = lean_array_fget_borrowed(v_vals_866_, v_i_867_);
lean_dec(v_i_867_);
lean_inc(v___x_877_);
v___x_878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_878_, 0, v___x_877_);
return v___x_878_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_keys_879_, lean_object* v_vals_880_, lean_object* v_i_881_, lean_object* v_k_882_){
_start:
{
lean_object* v_res_883_; 
v_res_883_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__0_spec__1_spec__3___redArg(v_keys_879_, v_vals_880_, v_i_881_, v_k_882_);
lean_dec(v_k_882_);
lean_dec_ref(v_vals_880_);
lean_dec_ref(v_keys_879_);
return v_res_883_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__0_spec__1___redArg(lean_object* v_x_884_, size_t v_x_885_, lean_object* v_x_886_){
_start:
{
if (lean_obj_tag(v_x_884_) == 0)
{
lean_object* v_es_887_; lean_object* v___x_889_; uint8_t v_isShared_890_; uint8_t v_isSharedCheck_908_; 
v_es_887_ = lean_ctor_get(v_x_884_, 0);
v_isSharedCheck_908_ = !lean_is_exclusive(v_x_884_);
if (v_isSharedCheck_908_ == 0)
{
v___x_889_ = v_x_884_;
v_isShared_890_ = v_isSharedCheck_908_;
goto v_resetjp_888_;
}
else
{
lean_inc(v_es_887_);
lean_dec(v_x_884_);
v___x_889_ = lean_box(0);
v_isShared_890_ = v_isSharedCheck_908_;
goto v_resetjp_888_;
}
v_resetjp_888_:
{
lean_object* v___x_891_; size_t v___x_892_; size_t v___x_893_; size_t v___x_894_; lean_object* v_j_895_; lean_object* v___x_896_; 
v___x_891_ = lean_box(2);
v___x_892_ = ((size_t)5ULL);
v___x_893_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2___redArg___closed__1);
v___x_894_ = lean_usize_land(v_x_885_, v___x_893_);
v_j_895_ = lean_usize_to_nat(v___x_894_);
v___x_896_ = lean_array_get(v___x_891_, v_es_887_, v_j_895_);
lean_dec(v_j_895_);
lean_dec_ref(v_es_887_);
switch(lean_obj_tag(v___x_896_))
{
case 0:
{
lean_object* v_key_897_; lean_object* v_val_898_; uint8_t v___x_899_; 
v_key_897_ = lean_ctor_get(v___x_896_, 0);
lean_inc(v_key_897_);
v_val_898_ = lean_ctor_get(v___x_896_, 1);
lean_inc(v_val_898_);
lean_dec_ref(v___x_896_);
v___x_899_ = lean_name_eq(v_x_886_, v_key_897_);
lean_dec(v_key_897_);
if (v___x_899_ == 0)
{
lean_object* v___x_900_; 
lean_dec(v_val_898_);
lean_del_object(v___x_889_);
v___x_900_ = lean_box(0);
return v___x_900_;
}
else
{
lean_object* v___x_902_; 
if (v_isShared_890_ == 0)
{
lean_ctor_set_tag(v___x_889_, 1);
lean_ctor_set(v___x_889_, 0, v_val_898_);
v___x_902_ = v___x_889_;
goto v_reusejp_901_;
}
else
{
lean_object* v_reuseFailAlloc_903_; 
v_reuseFailAlloc_903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_903_, 0, v_val_898_);
v___x_902_ = v_reuseFailAlloc_903_;
goto v_reusejp_901_;
}
v_reusejp_901_:
{
return v___x_902_;
}
}
}
case 1:
{
lean_object* v_node_904_; size_t v___x_905_; 
lean_del_object(v___x_889_);
v_node_904_ = lean_ctor_get(v___x_896_, 0);
lean_inc(v_node_904_);
lean_dec_ref(v___x_896_);
v___x_905_ = lean_usize_shift_right(v_x_885_, v___x_892_);
v_x_884_ = v_node_904_;
v_x_885_ = v___x_905_;
goto _start;
}
default: 
{
lean_object* v___x_907_; 
lean_del_object(v___x_889_);
v___x_907_ = lean_box(0);
return v___x_907_;
}
}
}
}
else
{
lean_object* v_ks_909_; lean_object* v_vs_910_; lean_object* v___x_911_; lean_object* v___x_912_; 
v_ks_909_ = lean_ctor_get(v_x_884_, 0);
lean_inc_ref(v_ks_909_);
v_vs_910_ = lean_ctor_get(v_x_884_, 1);
lean_inc_ref(v_vs_910_);
lean_dec_ref(v_x_884_);
v___x_911_ = lean_unsigned_to_nat(0u);
v___x_912_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__0_spec__1_spec__3___redArg(v_ks_909_, v_vs_910_, v___x_911_, v_x_886_);
lean_dec_ref(v_vs_910_);
lean_dec_ref(v_ks_909_);
return v___x_912_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_913_, lean_object* v_x_914_, lean_object* v_x_915_){
_start:
{
size_t v_x_615__boxed_916_; lean_object* v_res_917_; 
v_x_615__boxed_916_ = lean_unbox_usize(v_x_914_);
lean_dec(v_x_914_);
v_res_917_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__0_spec__1___redArg(v_x_913_, v_x_615__boxed_916_, v_x_915_);
lean_dec(v_x_915_);
return v_res_917_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__0___redArg(lean_object* v_x_918_, lean_object* v_x_919_){
_start:
{
uint64_t v___y_921_; 
if (lean_obj_tag(v_x_919_) == 0)
{
uint64_t v___x_924_; 
v___x_924_ = lean_uint64_once(&l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8_spec__10___redArg___closed__0, &l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8_spec__10___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8_spec__10___redArg___closed__0);
v___y_921_ = v___x_924_;
goto v___jp_920_;
}
else
{
uint64_t v_hash_925_; 
v_hash_925_ = lean_ctor_get_uint64(v_x_919_, sizeof(void*)*2);
v___y_921_ = v_hash_925_;
goto v___jp_920_;
}
v___jp_920_:
{
size_t v___x_922_; lean_object* v___x_923_; 
v___x_922_ = lean_uint64_to_usize(v___y_921_);
v___x_923_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__0_spec__1___redArg(v_x_918_, v___x_922_, v_x_919_);
return v___x_923_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__0___redArg___boxed(lean_object* v_x_926_, lean_object* v_x_927_){
_start:
{
lean_object* v_res_928_; 
v_res_928_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__0___redArg(v_x_926_, v_x_927_);
lean_dec(v_x_927_);
return v_res_928_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__1_spec__3___redArg(lean_object* v_a_929_, lean_object* v_x_930_){
_start:
{
if (lean_obj_tag(v_x_930_) == 0)
{
lean_object* v___x_931_; 
v___x_931_ = lean_box(0);
return v___x_931_;
}
else
{
lean_object* v_key_932_; lean_object* v_value_933_; lean_object* v_tail_934_; uint8_t v___x_935_; 
v_key_932_ = lean_ctor_get(v_x_930_, 0);
v_value_933_ = lean_ctor_get(v_x_930_, 1);
v_tail_934_ = lean_ctor_get(v_x_930_, 2);
v___x_935_ = lean_name_eq(v_key_932_, v_a_929_);
if (v___x_935_ == 0)
{
v_x_930_ = v_tail_934_;
goto _start;
}
else
{
lean_object* v___x_937_; 
lean_inc(v_value_933_);
v___x_937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_937_, 0, v_value_933_);
return v___x_937_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_a_938_, lean_object* v_x_939_){
_start:
{
lean_object* v_res_940_; 
v_res_940_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__1_spec__3___redArg(v_a_938_, v_x_939_);
lean_dec(v_x_939_);
lean_dec(v_a_938_);
return v_res_940_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__1___redArg(lean_object* v_m_941_, lean_object* v_a_942_){
_start:
{
lean_object* v_buckets_943_; lean_object* v___x_944_; uint64_t v___y_946_; 
v_buckets_943_ = lean_ctor_get(v_m_941_, 1);
v___x_944_ = lean_array_get_size(v_buckets_943_);
if (lean_obj_tag(v_a_942_) == 0)
{
uint64_t v___x_960_; 
v___x_960_ = lean_uint64_once(&l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8_spec__10___redArg___closed__0, &l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8_spec__10___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8_spec__10___redArg___closed__0);
v___y_946_ = v___x_960_;
goto v___jp_945_;
}
else
{
uint64_t v_hash_961_; 
v_hash_961_ = lean_ctor_get_uint64(v_a_942_, sizeof(void*)*2);
v___y_946_ = v_hash_961_;
goto v___jp_945_;
}
v___jp_945_:
{
uint64_t v___x_947_; uint64_t v___x_948_; uint64_t v_fold_949_; uint64_t v___x_950_; uint64_t v___x_951_; uint64_t v___x_952_; size_t v___x_953_; size_t v___x_954_; size_t v___x_955_; size_t v___x_956_; size_t v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; 
v___x_947_ = 32ULL;
v___x_948_ = lean_uint64_shift_right(v___y_946_, v___x_947_);
v_fold_949_ = lean_uint64_xor(v___y_946_, v___x_948_);
v___x_950_ = 16ULL;
v___x_951_ = lean_uint64_shift_right(v_fold_949_, v___x_950_);
v___x_952_ = lean_uint64_xor(v_fold_949_, v___x_951_);
v___x_953_ = lean_uint64_to_usize(v___x_952_);
v___x_954_ = lean_usize_of_nat(v___x_944_);
v___x_955_ = ((size_t)1ULL);
v___x_956_ = lean_usize_sub(v___x_954_, v___x_955_);
v___x_957_ = lean_usize_land(v___x_953_, v___x_956_);
v___x_958_ = lean_array_uget_borrowed(v_buckets_943_, v___x_957_);
v___x_959_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__1_spec__3___redArg(v_a_942_, v___x_958_);
return v___x_959_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__1___redArg___boxed(lean_object* v_m_962_, lean_object* v_a_963_){
_start:
{
lean_object* v_res_964_; 
v_res_964_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__1___redArg(v_m_962_, v_a_963_);
lean_dec(v_a_963_);
lean_dec_ref(v_m_962_);
return v_res_964_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0___redArg(lean_object* v_x_965_, lean_object* v_x_966_){
_start:
{
uint8_t v_stage_u2081_967_; 
v_stage_u2081_967_ = lean_ctor_get_uint8(v_x_965_, sizeof(void*)*2);
if (v_stage_u2081_967_ == 0)
{
lean_object* v_map_u2081_968_; lean_object* v_map_u2082_969_; lean_object* v___x_970_; 
v_map_u2081_968_ = lean_ctor_get(v_x_965_, 0);
lean_inc_ref(v_map_u2081_968_);
v_map_u2082_969_ = lean_ctor_get(v_x_965_, 1);
lean_inc_ref(v_map_u2082_969_);
lean_dec_ref(v_x_965_);
v___x_970_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__0___redArg(v_map_u2082_969_, v_x_966_);
if (lean_obj_tag(v___x_970_) == 0)
{
lean_object* v___x_971_; 
v___x_971_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__1___redArg(v_map_u2081_968_, v_x_966_);
lean_dec_ref(v_map_u2081_968_);
return v___x_971_;
}
else
{
lean_dec_ref(v_map_u2081_968_);
return v___x_970_;
}
}
else
{
lean_object* v_map_u2081_972_; lean_object* v___x_973_; 
v_map_u2081_972_ = lean_ctor_get(v_x_965_, 0);
lean_inc_ref(v_map_u2081_972_);
lean_dec_ref(v_x_965_);
v___x_973_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__1___redArg(v_map_u2081_972_, v_x_966_);
lean_dec_ref(v_map_u2081_972_);
return v___x_973_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0___redArg___boxed(lean_object* v_x_974_, lean_object* v_x_975_){
_start:
{
lean_object* v_res_976_; 
v_res_976_ = l_Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0___redArg(v_x_974_, v_x_975_);
lean_dec(v_x_975_);
return v_res_976_;
}
}
static lean_object* _init_l_Lean_getReducibilityStatusCore___closed__2(void){
_start:
{
lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; 
v___x_979_ = ((lean_object*)(l_Lean_getReducibilityStatusCore___closed__1));
v___x_980_ = ((lean_object*)(l_Lean_getReducibilityStatusCore___closed__0));
v___x_981_ = l_Lean_SMap_instInhabited(lean_box(0), lean_box(0), v___x_980_, v___x_979_);
return v___x_981_;
}
}
LEAN_EXPORT uint8_t lean_get_reducibility_status(lean_object* v_env_982_, lean_object* v_declName_983_){
_start:
{
lean_object* v___x_984_; lean_object* v_ext_985_; lean_object* v_toEnvExtension_986_; lean_object* v_asyncMode_987_; lean_object* v___x_988_; lean_object* v_m_989_; lean_object* v___x_991_; uint8_t v_isShared_992_; uint8_t v_isSharedCheck_1026_; 
v___x_984_ = l_Lean_reducibilityExtraExt;
v_ext_985_ = lean_ctor_get(v___x_984_, 1);
lean_inc_ref(v_ext_985_);
v_toEnvExtension_986_ = lean_ctor_get(v_ext_985_, 0);
lean_inc_ref(v_toEnvExtension_986_);
lean_dec_ref(v_ext_985_);
v_asyncMode_987_ = lean_ctor_get(v_toEnvExtension_986_, 2);
lean_inc(v_asyncMode_987_);
lean_dec_ref(v_toEnvExtension_986_);
v___x_988_ = lean_obj_once(&l_Lean_getReducibilityStatusCore___closed__2, &l_Lean_getReducibilityStatusCore___closed__2_once, _init_l_Lean_getReducibilityStatusCore___closed__2);
lean_inc_ref(v_env_982_);
v_m_989_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_988_, v___x_984_, v_env_982_, v_asyncMode_987_);
lean_dec(v_asyncMode_987_);
v_isSharedCheck_1026_ = !lean_is_exclusive(v___x_984_);
if (v_isSharedCheck_1026_ == 0)
{
lean_object* v_unused_1027_; lean_object* v_unused_1028_; 
v_unused_1027_ = lean_ctor_get(v___x_984_, 1);
lean_dec(v_unused_1027_);
v_unused_1028_ = lean_ctor_get(v___x_984_, 0);
lean_dec(v_unused_1028_);
v___x_991_ = v___x_984_;
v_isShared_992_ = v_isSharedCheck_1026_;
goto v_resetjp_990_;
}
else
{
lean_dec(v___x_984_);
v___x_991_ = lean_box(0);
v_isShared_992_ = v_isSharedCheck_1026_;
goto v_resetjp_990_;
}
v_resetjp_990_:
{
lean_object* v___x_993_; 
v___x_993_ = l_Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0___redArg(v_m_989_, v_declName_983_);
if (lean_obj_tag(v___x_993_) == 1)
{
lean_object* v_val_994_; uint8_t v___x_995_; 
lean_del_object(v___x_991_);
lean_dec(v_declName_983_);
lean_dec_ref(v_env_982_);
v_val_994_ = lean_ctor_get(v___x_993_, 0);
lean_inc(v_val_994_);
lean_dec_ref(v___x_993_);
v___x_995_ = lean_unbox(v_val_994_);
lean_dec(v_val_994_);
return v___x_995_;
}
else
{
lean_object* v___x_996_; lean_object* v___x_997_; 
lean_dec(v___x_993_);
v___x_996_ = lean_box(1);
v___x_997_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_982_, v_declName_983_);
if (lean_obj_tag(v___x_997_) == 0)
{
lean_object* v___x_998_; lean_object* v_toEnvExtension_999_; lean_object* v_asyncMode_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; 
lean_del_object(v___x_991_);
v___x_998_ = l_Lean_reducibilityCoreExt;
v_toEnvExtension_999_ = lean_ctor_get(v___x_998_, 0);
lean_inc_ref(v_toEnvExtension_999_);
v_asyncMode_1000_ = lean_ctor_get(v_toEnvExtension_999_, 2);
lean_inc(v_asyncMode_1000_);
lean_dec_ref(v_toEnvExtension_999_);
lean_inc(v_declName_983_);
v___x_1001_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_996_, v___x_998_, v_env_982_, v_asyncMode_1000_, v_declName_983_);
lean_dec(v_asyncMode_1000_);
v___x_1002_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_1001_, v_declName_983_);
lean_dec(v_declName_983_);
lean_dec(v___x_1001_);
if (lean_obj_tag(v___x_1002_) == 0)
{
uint8_t v___x_1003_; 
v___x_1003_ = 1;
return v___x_1003_;
}
else
{
lean_object* v_val_1004_; uint8_t v___x_1005_; 
v_val_1004_ = lean_ctor_get(v___x_1002_, 0);
lean_inc(v_val_1004_);
lean_dec_ref(v___x_1002_);
v___x_1005_ = lean_unbox(v_val_1004_);
lean_dec(v_val_1004_);
return v___x_1005_;
}
}
else
{
lean_object* v_val_1006_; lean_object* v___x_1007_; uint8_t v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; uint8_t v___x_1012_; 
v_val_1006_ = lean_ctor_get(v___x_997_, 0);
lean_inc(v_val_1006_);
lean_dec_ref(v___x_997_);
v___x_1007_ = l_Lean_reducibilityCoreExt;
v___x_1008_ = 0;
v___x_1009_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_996_, v___x_1007_, v_env_982_, v_val_1006_, v___x_1008_);
lean_dec(v_val_1006_);
lean_dec_ref(v_env_982_);
v___x_1010_ = lean_unsigned_to_nat(0u);
v___x_1011_ = lean_array_get_size(v___x_1009_);
v___x_1012_ = lean_nat_dec_lt(v___x_1010_, v___x_1011_);
if (v___x_1012_ == 0)
{
uint8_t v___x_1013_; 
lean_dec_ref(v___x_1009_);
lean_del_object(v___x_991_);
lean_dec(v_declName_983_);
v___x_1013_ = 1;
return v___x_1013_;
}
else
{
uint8_t v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; uint8_t v___x_1017_; 
v___x_1014_ = 1;
v___x_1015_ = lean_unsigned_to_nat(1u);
v___x_1016_ = lean_nat_sub(v___x_1011_, v___x_1015_);
v___x_1017_ = lean_nat_dec_le(v___x_1010_, v___x_1016_);
if (v___x_1017_ == 0)
{
lean_dec(v___x_1016_);
lean_dec_ref(v___x_1009_);
lean_del_object(v___x_991_);
lean_dec(v_declName_983_);
return v___x_1014_;
}
else
{
lean_object* v___x_1018_; lean_object* v___x_1020_; 
v___x_1018_ = lean_box(v___x_1014_);
if (v_isShared_992_ == 0)
{
lean_ctor_set(v___x_991_, 1, v___x_1018_);
lean_ctor_set(v___x_991_, 0, v_declName_983_);
v___x_1020_ = v___x_991_;
goto v_reusejp_1019_;
}
else
{
lean_object* v_reuseFailAlloc_1025_; 
v_reuseFailAlloc_1025_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1025_, 0, v_declName_983_);
lean_ctor_set(v_reuseFailAlloc_1025_, 1, v___x_1018_);
v___x_1020_ = v_reuseFailAlloc_1025_;
goto v_reusejp_1019_;
}
v_reusejp_1019_:
{
lean_object* v___x_1021_; 
v___x_1021_ = l_Array_binSearchAux___at___00Lean_getReducibilityStatusCore_spec__1___redArg(v___x_1009_, v___x_1020_, v___x_1010_, v___x_1016_);
lean_dec_ref(v___x_1020_);
lean_dec_ref(v___x_1009_);
if (lean_obj_tag(v___x_1021_) == 0)
{
return v___x_1014_;
}
else
{
lean_object* v_val_1022_; lean_object* v_snd_1023_; uint8_t v___x_1024_; 
v_val_1022_ = lean_ctor_get(v___x_1021_, 0);
lean_inc(v_val_1022_);
lean_dec_ref(v___x_1021_);
v_snd_1023_ = lean_ctor_get(v_val_1022_, 1);
lean_inc(v_snd_1023_);
lean_dec(v_val_1022_);
v___x_1024_ = lean_unbox(v_snd_1023_);
lean_dec(v_snd_1023_);
return v___x_1024_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatusCore___boxed(lean_object* v_env_1029_, lean_object* v_declName_1030_){
_start:
{
uint8_t v_res_1031_; lean_object* v_r_1032_; 
v_res_1031_ = lean_get_reducibility_status(v_env_1029_, v_declName_1030_);
v_r_1032_ = lean_box(v_res_1031_);
return v_r_1032_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0(lean_object* v_00_u03b2_1033_, lean_object* v_x_1034_, lean_object* v_x_1035_){
_start:
{
lean_object* v___x_1036_; 
v___x_1036_ = l_Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0___redArg(v_x_1034_, v_x_1035_);
return v___x_1036_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0___boxed(lean_object* v_00_u03b2_1037_, lean_object* v_x_1038_, lean_object* v_x_1039_){
_start:
{
lean_object* v_res_1040_; 
v_res_1040_ = l_Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0(v_00_u03b2_1037_, v_x_1038_, v_x_1039_);
lean_dec(v_x_1039_);
return v_res_1040_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_getReducibilityStatusCore_spec__1(lean_object* v_as_1041_, lean_object* v_k_1042_, lean_object* v_x_1043_, lean_object* v_x_1044_, lean_object* v_x_1045_){
_start:
{
lean_object* v___x_1046_; 
v___x_1046_ = l_Array_binSearchAux___at___00Lean_getReducibilityStatusCore_spec__1___redArg(v_as_1041_, v_k_1042_, v_x_1043_, v_x_1044_);
return v___x_1046_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_getReducibilityStatusCore_spec__1___boxed(lean_object* v_as_1047_, lean_object* v_k_1048_, lean_object* v_x_1049_, lean_object* v_x_1050_, lean_object* v_x_1051_){
_start:
{
lean_object* v_res_1052_; 
v_res_1052_ = l_Array_binSearchAux___at___00Lean_getReducibilityStatusCore_spec__1(v_as_1047_, v_k_1048_, v_x_1049_, v_x_1050_, v_x_1051_);
lean_dec_ref(v_k_1048_);
lean_dec_ref(v_as_1047_);
return v_res_1052_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__0(lean_object* v_00_u03b2_1053_, lean_object* v_x_1054_, lean_object* v_x_1055_){
_start:
{
lean_object* v___x_1056_; 
v___x_1056_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__0___redArg(v_x_1054_, v_x_1055_);
return v___x_1056_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1057_, lean_object* v_x_1058_, lean_object* v_x_1059_){
_start:
{
lean_object* v_res_1060_; 
v_res_1060_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__0(v_00_u03b2_1057_, v_x_1058_, v_x_1059_);
lean_dec(v_x_1059_);
return v_res_1060_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__1(lean_object* v_00_u03b2_1061_, lean_object* v_m_1062_, lean_object* v_a_1063_){
_start:
{
lean_object* v___x_1064_; 
v___x_1064_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__1___redArg(v_m_1062_, v_a_1063_);
return v___x_1064_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1065_, lean_object* v_m_1066_, lean_object* v_a_1067_){
_start:
{
lean_object* v_res_1068_; 
v_res_1068_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__1(v_00_u03b2_1065_, v_m_1066_, v_a_1067_);
lean_dec(v_a_1067_);
lean_dec_ref(v_m_1066_);
return v_res_1068_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1069_, lean_object* v_x_1070_, size_t v_x_1071_, lean_object* v_x_1072_){
_start:
{
lean_object* v___x_1073_; 
v___x_1073_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__0_spec__1___redArg(v_x_1070_, v_x_1071_, v_x_1072_);
return v___x_1073_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1074_, lean_object* v_x_1075_, lean_object* v_x_1076_, lean_object* v_x_1077_){
_start:
{
size_t v_x_894__boxed_1078_; lean_object* v_res_1079_; 
v_x_894__boxed_1078_ = lean_unbox_usize(v_x_1076_);
lean_dec(v_x_1076_);
v_res_1079_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__0_spec__1(v_00_u03b2_1074_, v_x_1075_, v_x_894__boxed_1078_, v_x_1077_);
lean_dec(v_x_1077_);
return v_res_1079_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_1080_, lean_object* v_a_1081_, lean_object* v_x_1082_){
_start:
{
lean_object* v___x_1083_; 
v___x_1083_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__1_spec__3___redArg(v_a_1081_, v_x_1082_);
return v___x_1083_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_1084_, lean_object* v_a_1085_, lean_object* v_x_1086_){
_start:
{
lean_object* v_res_1087_; 
v_res_1087_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__1_spec__3(v_00_u03b2_1084_, v_a_1085_, v_x_1086_);
lean_dec(v_x_1086_);
lean_dec(v_a_1085_);
return v_res_1087_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_1088_, lean_object* v_keys_1089_, lean_object* v_vals_1090_, lean_object* v_heq_1091_, lean_object* v_i_1092_, lean_object* v_k_1093_){
_start:
{
lean_object* v___x_1094_; 
v___x_1094_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__0_spec__1_spec__3___redArg(v_keys_1089_, v_vals_1090_, v_i_1092_, v_k_1093_);
return v___x_1094_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_1095_, lean_object* v_keys_1096_, lean_object* v_vals_1097_, lean_object* v_heq_1098_, lean_object* v_i_1099_, lean_object* v_k_1100_){
_start:
{
lean_object* v_res_1101_; 
v_res_1101_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_1095_, v_keys_1096_, v_vals_1097_, v_heq_1098_, v_i_1099_, v_k_1100_);
lean_dec(v_k_1100_);
lean_dec_ref(v_vals_1097_);
lean_dec_ref(v_keys_1096_);
return v_res_1101_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(lean_object* v_env_1102_, lean_object* v_declName_1103_, uint8_t v_status_1104_, uint8_t v_attrKind_1105_, lean_object* v_currNamespace_1106_){
_start:
{
if (v_attrKind_1105_ == 0)
{
lean_object* v___x_1107_; 
lean_dec(v_currNamespace_1106_);
v___x_1107_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1102_, v_declName_1103_);
if (lean_obj_tag(v___x_1107_) == 0)
{
lean_object* v___x_1108_; lean_object* v_toEnvExtension_1109_; lean_object* v_asyncMode_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; 
v___x_1108_ = l_Lean_reducibilityCoreExt;
v_toEnvExtension_1109_ = lean_ctor_get(v___x_1108_, 0);
lean_inc_ref(v_toEnvExtension_1109_);
v_asyncMode_1110_ = lean_ctor_get(v_toEnvExtension_1109_, 2);
lean_inc(v_asyncMode_1110_);
lean_dec_ref(v_toEnvExtension_1109_);
v___x_1111_ = lean_box(v_status_1104_);
lean_inc(v_declName_1103_);
v___x_1112_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1112_, 0, v_declName_1103_);
lean_ctor_set(v___x_1112_, 1, v___x_1111_);
v___x_1113_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_1108_, v_env_1102_, v___x_1112_, v_asyncMode_1110_, v_declName_1103_);
lean_dec(v_asyncMode_1110_);
return v___x_1113_;
}
else
{
lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; 
lean_dec_ref(v___x_1107_);
v___x_1114_ = l_Lean_reducibilityExtraExt;
v___x_1115_ = lean_box(v_status_1104_);
v___x_1116_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1116_, 0, v_declName_1103_);
lean_ctor_set(v___x_1116_, 1, v___x_1115_);
v___x_1117_ = l_Lean_ScopedEnvExtension_addEntry___redArg(v___x_1114_, v_env_1102_, v___x_1116_);
return v___x_1117_;
}
}
else
{
lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; 
v___x_1118_ = l_Lean_reducibilityExtraExt;
v___x_1119_ = lean_box(v_status_1104_);
v___x_1120_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1120_, 0, v_declName_1103_);
lean_ctor_set(v___x_1120_, 1, v___x_1119_);
v___x_1121_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_env_1102_, v___x_1118_, v___x_1120_, v_attrKind_1105_, v_currNamespace_1106_);
return v___x_1121_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore___boxed(lean_object* v_env_1122_, lean_object* v_declName_1123_, lean_object* v_status_1124_, lean_object* v_attrKind_1125_, lean_object* v_currNamespace_1126_){
_start:
{
uint8_t v_status_boxed_1127_; uint8_t v_attrKind_boxed_1128_; lean_object* v_res_1129_; 
v_status_boxed_1127_ = lean_unbox(v_status_1124_);
v_attrKind_boxed_1128_ = lean_unbox(v_attrKind_1125_);
v_res_1129_ = l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(v_env_1122_, v_declName_1123_, v_status_boxed_1127_, v_attrKind_boxed_1128_, v_currNamespace_1126_);
return v_res_1129_;
}
}
LEAN_EXPORT lean_object* lean_set_reducibility_status(lean_object* v_env_1130_, lean_object* v_declName_1131_, uint8_t v_status_1132_){
_start:
{
uint8_t v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; 
v___x_1133_ = 0;
v___x_1134_ = lean_box(0);
v___x_1135_ = l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(v_env_1130_, v_declName_1131_, v_status_1132_, v___x_1133_, v___x_1134_);
return v___x_1135_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusImp___boxed(lean_object* v_env_1136_, lean_object* v_declName_1137_, lean_object* v_status_1138_){
_start:
{
uint8_t v_status_boxed_1139_; lean_object* v_res_1140_; 
v_status_boxed_1139_ = lean_unbox(v_status_1138_);
v_res_1140_ = lean_set_reducibility_status(v_env_1136_, v_declName_1137_, v_status_boxed_1139_);
return v_res_1140_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4__spec__0(lean_object* v_name_1141_, lean_object* v_decl_1142_, lean_object* v_ref_1143_){
_start:
{
lean_object* v_defValue_1145_; lean_object* v_descr_1146_; lean_object* v___x_1148_; uint8_t v_isShared_1149_; uint8_t v_isSharedCheck_1173_; 
v_defValue_1145_ = lean_ctor_get(v_decl_1142_, 0);
v_descr_1146_ = lean_ctor_get(v_decl_1142_, 1);
v_isSharedCheck_1173_ = !lean_is_exclusive(v_decl_1142_);
if (v_isSharedCheck_1173_ == 0)
{
v___x_1148_ = v_decl_1142_;
v_isShared_1149_ = v_isSharedCheck_1173_;
goto v_resetjp_1147_;
}
else
{
lean_inc(v_descr_1146_);
lean_inc(v_defValue_1145_);
lean_dec(v_decl_1142_);
v___x_1148_ = lean_box(0);
v_isShared_1149_ = v_isSharedCheck_1173_;
goto v_resetjp_1147_;
}
v_resetjp_1147_:
{
lean_object* v___x_1150_; uint8_t v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; 
v___x_1150_ = lean_alloc_ctor(1, 0, 1);
v___x_1151_ = lean_unbox(v_defValue_1145_);
lean_ctor_set_uint8(v___x_1150_, 0, v___x_1151_);
lean_inc(v_name_1141_);
v___x_1152_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1152_, 0, v_name_1141_);
lean_ctor_set(v___x_1152_, 1, v_ref_1143_);
lean_ctor_set(v___x_1152_, 2, v___x_1150_);
lean_ctor_set(v___x_1152_, 3, v_descr_1146_);
lean_inc(v_name_1141_);
v___x_1153_ = lean_register_option(v_name_1141_, v___x_1152_);
if (lean_obj_tag(v___x_1153_) == 0)
{
lean_object* v___x_1155_; uint8_t v_isShared_1156_; uint8_t v_isSharedCheck_1163_; 
v_isSharedCheck_1163_ = !lean_is_exclusive(v___x_1153_);
if (v_isSharedCheck_1163_ == 0)
{
lean_object* v_unused_1164_; 
v_unused_1164_ = lean_ctor_get(v___x_1153_, 0);
lean_dec(v_unused_1164_);
v___x_1155_ = v___x_1153_;
v_isShared_1156_ = v_isSharedCheck_1163_;
goto v_resetjp_1154_;
}
else
{
lean_dec(v___x_1153_);
v___x_1155_ = lean_box(0);
v_isShared_1156_ = v_isSharedCheck_1163_;
goto v_resetjp_1154_;
}
v_resetjp_1154_:
{
lean_object* v___x_1158_; 
if (v_isShared_1149_ == 0)
{
lean_ctor_set(v___x_1148_, 1, v_defValue_1145_);
lean_ctor_set(v___x_1148_, 0, v_name_1141_);
v___x_1158_ = v___x_1148_;
goto v_reusejp_1157_;
}
else
{
lean_object* v_reuseFailAlloc_1162_; 
v_reuseFailAlloc_1162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1162_, 0, v_name_1141_);
lean_ctor_set(v_reuseFailAlloc_1162_, 1, v_defValue_1145_);
v___x_1158_ = v_reuseFailAlloc_1162_;
goto v_reusejp_1157_;
}
v_reusejp_1157_:
{
lean_object* v___x_1160_; 
if (v_isShared_1156_ == 0)
{
lean_ctor_set(v___x_1155_, 0, v___x_1158_);
v___x_1160_ = v___x_1155_;
goto v_reusejp_1159_;
}
else
{
lean_object* v_reuseFailAlloc_1161_; 
v_reuseFailAlloc_1161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1161_, 0, v___x_1158_);
v___x_1160_ = v_reuseFailAlloc_1161_;
goto v_reusejp_1159_;
}
v_reusejp_1159_:
{
return v___x_1160_;
}
}
}
}
else
{
lean_object* v_a_1165_; lean_object* v___x_1167_; uint8_t v_isShared_1168_; uint8_t v_isSharedCheck_1172_; 
lean_del_object(v___x_1148_);
lean_dec(v_defValue_1145_);
lean_dec(v_name_1141_);
v_a_1165_ = lean_ctor_get(v___x_1153_, 0);
v_isSharedCheck_1172_ = !lean_is_exclusive(v___x_1153_);
if (v_isSharedCheck_1172_ == 0)
{
v___x_1167_ = v___x_1153_;
v_isShared_1168_ = v_isSharedCheck_1172_;
goto v_resetjp_1166_;
}
else
{
lean_inc(v_a_1165_);
lean_dec(v___x_1153_);
v___x_1167_ = lean_box(0);
v_isShared_1168_ = v_isSharedCheck_1172_;
goto v_resetjp_1166_;
}
v_resetjp_1166_:
{
lean_object* v___x_1170_; 
if (v_isShared_1168_ == 0)
{
v___x_1170_ = v___x_1167_;
goto v_reusejp_1169_;
}
else
{
lean_object* v_reuseFailAlloc_1171_; 
v_reuseFailAlloc_1171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1171_, 0, v_a_1165_);
v___x_1170_ = v_reuseFailAlloc_1171_;
goto v_reusejp_1169_;
}
v_reusejp_1169_:
{
return v___x_1170_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_1174_, lean_object* v_decl_1175_, lean_object* v_ref_1176_, lean_object* v_a_1177_){
_start:
{
lean_object* v_res_1178_; 
v_res_1178_ = l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4__spec__0(v_name_1174_, v_decl_1175_, v_ref_1176_);
return v_res_1178_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; 
v___x_1192_ = ((lean_object*)(l_Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4_));
v___x_1193_ = ((lean_object*)(l_Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4_));
v___x_1194_ = ((lean_object*)(l_Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4_));
v___x_1195_ = l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4__spec__0(v___x_1192_, v___x_1193_, v___x_1194_);
return v___x_1195_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4____boxed(lean_object* v_a_1196_){
_start:
{
lean_object* v_res_1197_; 
v_res_1197_ = l_Lean_initFn_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4_();
return v_res_1197_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__0(lean_object* v_opts_1198_, lean_object* v_opt_1199_){
_start:
{
lean_object* v_name_1200_; lean_object* v_defValue_1201_; lean_object* v_map_1202_; lean_object* v___x_1203_; 
v_name_1200_ = lean_ctor_get(v_opt_1199_, 0);
v_defValue_1201_ = lean_ctor_get(v_opt_1199_, 1);
v_map_1202_ = lean_ctor_get(v_opts_1198_, 0);
v___x_1203_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1202_, v_name_1200_);
if (lean_obj_tag(v___x_1203_) == 0)
{
uint8_t v___x_1204_; 
v___x_1204_ = lean_unbox(v_defValue_1201_);
return v___x_1204_;
}
else
{
lean_object* v_val_1205_; 
v_val_1205_ = lean_ctor_get(v___x_1203_, 0);
lean_inc(v_val_1205_);
lean_dec_ref(v___x_1203_);
if (lean_obj_tag(v_val_1205_) == 1)
{
uint8_t v_v_1206_; 
v_v_1206_ = lean_ctor_get_uint8(v_val_1205_, 0);
lean_dec_ref(v_val_1205_);
return v_v_1206_;
}
else
{
uint8_t v___x_1207_; 
lean_dec(v_val_1205_);
v___x_1207_ = lean_unbox(v_defValue_1201_);
return v___x_1207_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__0___boxed(lean_object* v_opts_1208_, lean_object* v_opt_1209_){
_start:
{
uint8_t v_res_1210_; lean_object* v_r_1211_; 
v_res_1210_ = l_Lean_Option_get___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__0(v_opts_1208_, v_opt_1209_);
lean_dec_ref(v_opt_1209_);
lean_dec_ref(v_opts_1208_);
v_r_1211_ = lean_box(v_res_1210_);
return v_r_1211_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1212_; 
v___x_1212_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1212_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__1(void){
_start:
{
lean_object* v___x_1213_; lean_object* v___x_1214_; 
v___x_1213_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__0);
v___x_1214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1214_, 0, v___x_1213_);
return v___x_1214_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__2(void){
_start:
{
lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; 
v___x_1215_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__1);
v___x_1216_ = lean_unsigned_to_nat(0u);
v___x_1217_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_1217_, 0, v___x_1216_);
lean_ctor_set(v___x_1217_, 1, v___x_1216_);
lean_ctor_set(v___x_1217_, 2, v___x_1216_);
lean_ctor_set(v___x_1217_, 3, v___x_1215_);
lean_ctor_set(v___x_1217_, 4, v___x_1215_);
lean_ctor_set(v___x_1217_, 5, v___x_1215_);
lean_ctor_set(v___x_1217_, 6, v___x_1215_);
lean_ctor_set(v___x_1217_, 7, v___x_1215_);
lean_ctor_set(v___x_1217_, 8, v___x_1215_);
return v___x_1217_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__3(void){
_start:
{
lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; 
v___x_1218_ = lean_unsigned_to_nat(32u);
v___x_1219_ = lean_mk_empty_array_with_capacity(v___x_1218_);
v___x_1220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1220_, 0, v___x_1219_);
return v___x_1220_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__4(void){
_start:
{
size_t v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; 
v___x_1221_ = ((size_t)5ULL);
v___x_1222_ = lean_unsigned_to_nat(0u);
v___x_1223_ = lean_unsigned_to_nat(32u);
v___x_1224_ = lean_mk_empty_array_with_capacity(v___x_1223_);
v___x_1225_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__3);
v___x_1226_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1226_, 0, v___x_1225_);
lean_ctor_set(v___x_1226_, 1, v___x_1224_);
lean_ctor_set(v___x_1226_, 2, v___x_1222_);
lean_ctor_set(v___x_1226_, 3, v___x_1222_);
lean_ctor_set_usize(v___x_1226_, 4, v___x_1221_);
return v___x_1226_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__5(void){
_start:
{
lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; 
v___x_1227_ = lean_box(1);
v___x_1228_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__4);
v___x_1229_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__1);
v___x_1230_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1230_, 0, v___x_1229_);
lean_ctor_set(v___x_1230_, 1, v___x_1228_);
lean_ctor_set(v___x_1230_, 2, v___x_1227_);
return v___x_1230_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1(lean_object* v_msgData_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_){
_start:
{
lean_object* v___x_1235_; lean_object* v_env_1236_; lean_object* v_options_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; 
v___x_1235_ = lean_st_ref_get(v___y_1233_);
v_env_1236_ = lean_ctor_get(v___x_1235_, 0);
lean_inc_ref(v_env_1236_);
lean_dec(v___x_1235_);
v_options_1237_ = lean_ctor_get(v___y_1232_, 2);
v___x_1238_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__2);
v___x_1239_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__5);
lean_inc_ref(v_options_1237_);
v___x_1240_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1240_, 0, v_env_1236_);
lean_ctor_set(v___x_1240_, 1, v___x_1238_);
lean_ctor_set(v___x_1240_, 2, v___x_1239_);
lean_ctor_set(v___x_1240_, 3, v_options_1237_);
v___x_1241_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1241_, 0, v___x_1240_);
lean_ctor_set(v___x_1241_, 1, v_msgData_1231_);
v___x_1242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1242_, 0, v___x_1241_);
return v___x_1242_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___boxed(lean_object* v_msgData_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_){
_start:
{
lean_object* v_res_1247_; 
v_res_1247_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1(v_msgData_1243_, v___y_1244_, v___y_1245_);
lean_dec(v___y_1245_);
lean_dec_ref(v___y_1244_);
return v_res_1247_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1___redArg(lean_object* v_msg_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_){
_start:
{
lean_object* v_ref_1252_; lean_object* v___x_1253_; lean_object* v_a_1254_; lean_object* v___x_1256_; uint8_t v_isShared_1257_; uint8_t v_isSharedCheck_1262_; 
v_ref_1252_ = lean_ctor_get(v___y_1249_, 5);
v___x_1253_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1(v_msg_1248_, v___y_1249_, v___y_1250_);
v_a_1254_ = lean_ctor_get(v___x_1253_, 0);
v_isSharedCheck_1262_ = !lean_is_exclusive(v___x_1253_);
if (v_isSharedCheck_1262_ == 0)
{
v___x_1256_ = v___x_1253_;
v_isShared_1257_ = v_isSharedCheck_1262_;
goto v_resetjp_1255_;
}
else
{
lean_inc(v_a_1254_);
lean_dec(v___x_1253_);
v___x_1256_ = lean_box(0);
v_isShared_1257_ = v_isSharedCheck_1262_;
goto v_resetjp_1255_;
}
v_resetjp_1255_:
{
lean_object* v___x_1258_; lean_object* v___x_1260_; 
lean_inc(v_ref_1252_);
v___x_1258_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1258_, 0, v_ref_1252_);
lean_ctor_set(v___x_1258_, 1, v_a_1254_);
if (v_isShared_1257_ == 0)
{
lean_ctor_set_tag(v___x_1256_, 1);
lean_ctor_set(v___x_1256_, 0, v___x_1258_);
v___x_1260_ = v___x_1256_;
goto v_reusejp_1259_;
}
else
{
lean_object* v_reuseFailAlloc_1261_; 
v_reuseFailAlloc_1261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1261_, 0, v___x_1258_);
v___x_1260_ = v_reuseFailAlloc_1261_;
goto v_reusejp_1259_;
}
v_reusejp_1259_:
{
return v___x_1260_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1___redArg___boxed(lean_object* v_msg_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_){
_start:
{
lean_object* v_res_1267_; 
v_res_1267_ = l_Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1___redArg(v_msg_1263_, v___y_1264_, v___y_1265_);
lean_dec(v___y_1265_);
lean_dec_ref(v___y_1264_);
return v_res_1267_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__9___redArg(lean_object* v_ref_1268_, lean_object* v_msg_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_){
_start:
{
lean_object* v_fileName_1273_; lean_object* v_fileMap_1274_; lean_object* v_options_1275_; lean_object* v_currRecDepth_1276_; lean_object* v_maxRecDepth_1277_; lean_object* v_ref_1278_; lean_object* v_currNamespace_1279_; lean_object* v_openDecls_1280_; lean_object* v_initHeartbeats_1281_; lean_object* v_maxHeartbeats_1282_; lean_object* v_quotContext_1283_; lean_object* v_currMacroScope_1284_; uint8_t v_diag_1285_; lean_object* v_cancelTk_x3f_1286_; uint8_t v_suppressElabErrors_1287_; lean_object* v_inheritedTraceOptions_1288_; lean_object* v___x_1290_; uint8_t v_isShared_1291_; uint8_t v_isSharedCheck_1297_; 
v_fileName_1273_ = lean_ctor_get(v___y_1270_, 0);
v_fileMap_1274_ = lean_ctor_get(v___y_1270_, 1);
v_options_1275_ = lean_ctor_get(v___y_1270_, 2);
v_currRecDepth_1276_ = lean_ctor_get(v___y_1270_, 3);
v_maxRecDepth_1277_ = lean_ctor_get(v___y_1270_, 4);
v_ref_1278_ = lean_ctor_get(v___y_1270_, 5);
v_currNamespace_1279_ = lean_ctor_get(v___y_1270_, 6);
v_openDecls_1280_ = lean_ctor_get(v___y_1270_, 7);
v_initHeartbeats_1281_ = lean_ctor_get(v___y_1270_, 8);
v_maxHeartbeats_1282_ = lean_ctor_get(v___y_1270_, 9);
v_quotContext_1283_ = lean_ctor_get(v___y_1270_, 10);
v_currMacroScope_1284_ = lean_ctor_get(v___y_1270_, 11);
v_diag_1285_ = lean_ctor_get_uint8(v___y_1270_, sizeof(void*)*14);
v_cancelTk_x3f_1286_ = lean_ctor_get(v___y_1270_, 12);
v_suppressElabErrors_1287_ = lean_ctor_get_uint8(v___y_1270_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1288_ = lean_ctor_get(v___y_1270_, 13);
v_isSharedCheck_1297_ = !lean_is_exclusive(v___y_1270_);
if (v_isSharedCheck_1297_ == 0)
{
v___x_1290_ = v___y_1270_;
v_isShared_1291_ = v_isSharedCheck_1297_;
goto v_resetjp_1289_;
}
else
{
lean_inc(v_inheritedTraceOptions_1288_);
lean_inc(v_cancelTk_x3f_1286_);
lean_inc(v_currMacroScope_1284_);
lean_inc(v_quotContext_1283_);
lean_inc(v_maxHeartbeats_1282_);
lean_inc(v_initHeartbeats_1281_);
lean_inc(v_openDecls_1280_);
lean_inc(v_currNamespace_1279_);
lean_inc(v_ref_1278_);
lean_inc(v_maxRecDepth_1277_);
lean_inc(v_currRecDepth_1276_);
lean_inc(v_options_1275_);
lean_inc(v_fileMap_1274_);
lean_inc(v_fileName_1273_);
lean_dec(v___y_1270_);
v___x_1290_ = lean_box(0);
v_isShared_1291_ = v_isSharedCheck_1297_;
goto v_resetjp_1289_;
}
v_resetjp_1289_:
{
lean_object* v_ref_1292_; lean_object* v___x_1294_; 
v_ref_1292_ = l_Lean_replaceRef(v_ref_1268_, v_ref_1278_);
lean_dec(v_ref_1278_);
if (v_isShared_1291_ == 0)
{
lean_ctor_set(v___x_1290_, 5, v_ref_1292_);
v___x_1294_ = v___x_1290_;
goto v_reusejp_1293_;
}
else
{
lean_object* v_reuseFailAlloc_1296_; 
v_reuseFailAlloc_1296_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_1296_, 0, v_fileName_1273_);
lean_ctor_set(v_reuseFailAlloc_1296_, 1, v_fileMap_1274_);
lean_ctor_set(v_reuseFailAlloc_1296_, 2, v_options_1275_);
lean_ctor_set(v_reuseFailAlloc_1296_, 3, v_currRecDepth_1276_);
lean_ctor_set(v_reuseFailAlloc_1296_, 4, v_maxRecDepth_1277_);
lean_ctor_set(v_reuseFailAlloc_1296_, 5, v_ref_1292_);
lean_ctor_set(v_reuseFailAlloc_1296_, 6, v_currNamespace_1279_);
lean_ctor_set(v_reuseFailAlloc_1296_, 7, v_openDecls_1280_);
lean_ctor_set(v_reuseFailAlloc_1296_, 8, v_initHeartbeats_1281_);
lean_ctor_set(v_reuseFailAlloc_1296_, 9, v_maxHeartbeats_1282_);
lean_ctor_set(v_reuseFailAlloc_1296_, 10, v_quotContext_1283_);
lean_ctor_set(v_reuseFailAlloc_1296_, 11, v_currMacroScope_1284_);
lean_ctor_set(v_reuseFailAlloc_1296_, 12, v_cancelTk_x3f_1286_);
lean_ctor_set(v_reuseFailAlloc_1296_, 13, v_inheritedTraceOptions_1288_);
lean_ctor_set_uint8(v_reuseFailAlloc_1296_, sizeof(void*)*14, v_diag_1285_);
lean_ctor_set_uint8(v_reuseFailAlloc_1296_, sizeof(void*)*14 + 1, v_suppressElabErrors_1287_);
v___x_1294_ = v_reuseFailAlloc_1296_;
goto v_reusejp_1293_;
}
v_reusejp_1293_:
{
lean_object* v___x_1295_; 
v___x_1295_ = l_Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1___redArg(v_msg_1269_, v___x_1294_, v___y_1271_);
lean_dec_ref(v___x_1294_);
return v___x_1295_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__9___redArg___boxed(lean_object* v_ref_1298_, lean_object* v_msg_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_){
_start:
{
lean_object* v_res_1303_; 
v_res_1303_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__9___redArg(v_ref_1298_, v_msg_1299_, v___y_1300_, v___y_1301_);
lean_dec(v___y_1301_);
lean_dec(v_ref_1298_);
return v_res_1303_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__1(void){
_start:
{
lean_object* v___x_1305_; lean_object* v___x_1306_; 
v___x_1305_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__0));
v___x_1306_ = l_Lean_stringToMessageData(v___x_1305_);
return v___x_1306_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__3(void){
_start:
{
lean_object* v___x_1308_; lean_object* v___x_1309_; 
v___x_1308_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__2));
v___x_1309_ = l_Lean_stringToMessageData(v___x_1308_);
return v___x_1309_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__5(void){
_start:
{
lean_object* v___x_1311_; lean_object* v___x_1312_; 
v___x_1311_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__4));
v___x_1312_ = l_Lean_stringToMessageData(v___x_1311_);
return v___x_1312_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__7(void){
_start:
{
lean_object* v___x_1314_; lean_object* v___x_1315_; 
v___x_1314_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__6));
v___x_1315_ = l_Lean_stringToMessageData(v___x_1314_);
return v___x_1315_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__9(void){
_start:
{
lean_object* v___x_1317_; lean_object* v___x_1318_; 
v___x_1317_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__8));
v___x_1318_ = l_Lean_stringToMessageData(v___x_1317_);
return v___x_1318_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__11(void){
_start:
{
lean_object* v___x_1320_; lean_object* v___x_1321_; 
v___x_1320_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__10));
v___x_1321_ = l_Lean_stringToMessageData(v___x_1320_);
return v___x_1321_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__13(void){
_start:
{
lean_object* v___x_1323_; lean_object* v___x_1324_; 
v___x_1323_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__12));
v___x_1324_ = l_Lean_stringToMessageData(v___x_1323_);
return v___x_1324_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg(lean_object* v_msg_1325_, lean_object* v_declHint_1326_, lean_object* v___y_1327_){
_start:
{
lean_object* v___x_1329_; lean_object* v_env_1330_; uint8_t v___x_1331_; 
v___x_1329_ = lean_st_ref_get(v___y_1327_);
v_env_1330_ = lean_ctor_get(v___x_1329_, 0);
lean_inc_ref(v_env_1330_);
lean_dec(v___x_1329_);
v___x_1331_ = l_Lean_Name_isAnonymous(v_declHint_1326_);
if (v___x_1331_ == 0)
{
uint8_t v_isExporting_1332_; 
v_isExporting_1332_ = lean_ctor_get_uint8(v_env_1330_, sizeof(void*)*8);
if (v_isExporting_1332_ == 0)
{
lean_object* v___x_1333_; 
lean_dec_ref(v_env_1330_);
lean_dec(v_declHint_1326_);
v___x_1333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1333_, 0, v_msg_1325_);
return v___x_1333_;
}
else
{
lean_object* v___x_1334_; uint8_t v___x_1335_; 
lean_inc_ref(v_env_1330_);
v___x_1334_ = l_Lean_Environment_setExporting(v_env_1330_, v___x_1331_);
lean_inc(v_declHint_1326_);
lean_inc_ref(v___x_1334_);
v___x_1335_ = l_Lean_Environment_contains(v___x_1334_, v_declHint_1326_, v_isExporting_1332_);
if (v___x_1335_ == 0)
{
lean_object* v___x_1336_; 
lean_dec_ref(v___x_1334_);
lean_dec_ref(v_env_1330_);
lean_dec(v_declHint_1326_);
v___x_1336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1336_, 0, v_msg_1325_);
return v___x_1336_;
}
else
{
lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v_c_1342_; lean_object* v___x_1343_; 
v___x_1337_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__2);
v___x_1338_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__5);
v___x_1339_ = l_Lean_Options_empty;
v___x_1340_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1340_, 0, v___x_1334_);
lean_ctor_set(v___x_1340_, 1, v___x_1337_);
lean_ctor_set(v___x_1340_, 2, v___x_1338_);
lean_ctor_set(v___x_1340_, 3, v___x_1339_);
lean_inc(v_declHint_1326_);
v___x_1341_ = l_Lean_MessageData_ofConstName(v_declHint_1326_, v___x_1331_);
v_c_1342_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1342_, 0, v___x_1340_);
lean_ctor_set(v_c_1342_, 1, v___x_1341_);
v___x_1343_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1330_, v_declHint_1326_);
if (lean_obj_tag(v___x_1343_) == 0)
{
lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; 
lean_dec_ref(v_env_1330_);
lean_dec(v_declHint_1326_);
v___x_1344_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__1);
v___x_1345_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1345_, 0, v___x_1344_);
lean_ctor_set(v___x_1345_, 1, v_c_1342_);
v___x_1346_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__3);
v___x_1347_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1347_, 0, v___x_1345_);
lean_ctor_set(v___x_1347_, 1, v___x_1346_);
v___x_1348_ = l_Lean_MessageData_note(v___x_1347_);
v___x_1349_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1349_, 0, v_msg_1325_);
lean_ctor_set(v___x_1349_, 1, v___x_1348_);
v___x_1350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1350_, 0, v___x_1349_);
return v___x_1350_;
}
else
{
lean_object* v_val_1351_; lean_object* v___x_1353_; uint8_t v_isShared_1354_; uint8_t v_isSharedCheck_1386_; 
v_val_1351_ = lean_ctor_get(v___x_1343_, 0);
v_isSharedCheck_1386_ = !lean_is_exclusive(v___x_1343_);
if (v_isSharedCheck_1386_ == 0)
{
v___x_1353_ = v___x_1343_;
v_isShared_1354_ = v_isSharedCheck_1386_;
goto v_resetjp_1352_;
}
else
{
lean_inc(v_val_1351_);
lean_dec(v___x_1343_);
v___x_1353_ = lean_box(0);
v_isShared_1354_ = v_isSharedCheck_1386_;
goto v_resetjp_1352_;
}
v_resetjp_1352_:
{
lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v_mod_1358_; uint8_t v___x_1359_; 
v___x_1355_ = lean_box(0);
v___x_1356_ = l_Lean_Environment_header(v_env_1330_);
lean_dec_ref(v_env_1330_);
v___x_1357_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1356_);
v_mod_1358_ = lean_array_get(v___x_1355_, v___x_1357_, v_val_1351_);
lean_dec(v_val_1351_);
lean_dec_ref(v___x_1357_);
v___x_1359_ = l_Lean_isPrivateName(v_declHint_1326_);
lean_dec(v_declHint_1326_);
if (v___x_1359_ == 0)
{
lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1371_; 
v___x_1360_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__5);
v___x_1361_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1361_, 0, v___x_1360_);
lean_ctor_set(v___x_1361_, 1, v_c_1342_);
v___x_1362_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__7);
v___x_1363_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1363_, 0, v___x_1361_);
lean_ctor_set(v___x_1363_, 1, v___x_1362_);
v___x_1364_ = l_Lean_MessageData_ofName(v_mod_1358_);
v___x_1365_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1365_, 0, v___x_1363_);
lean_ctor_set(v___x_1365_, 1, v___x_1364_);
v___x_1366_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__9);
v___x_1367_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1367_, 0, v___x_1365_);
lean_ctor_set(v___x_1367_, 1, v___x_1366_);
v___x_1368_ = l_Lean_MessageData_note(v___x_1367_);
v___x_1369_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1369_, 0, v_msg_1325_);
lean_ctor_set(v___x_1369_, 1, v___x_1368_);
if (v_isShared_1354_ == 0)
{
lean_ctor_set_tag(v___x_1353_, 0);
lean_ctor_set(v___x_1353_, 0, v___x_1369_);
v___x_1371_ = v___x_1353_;
goto v_reusejp_1370_;
}
else
{
lean_object* v_reuseFailAlloc_1372_; 
v_reuseFailAlloc_1372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1372_, 0, v___x_1369_);
v___x_1371_ = v_reuseFailAlloc_1372_;
goto v_reusejp_1370_;
}
v_reusejp_1370_:
{
return v___x_1371_;
}
}
else
{
lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1384_; 
v___x_1373_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__1);
v___x_1374_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1374_, 0, v___x_1373_);
lean_ctor_set(v___x_1374_, 1, v_c_1342_);
v___x_1375_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__11);
v___x_1376_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1376_, 0, v___x_1374_);
lean_ctor_set(v___x_1376_, 1, v___x_1375_);
v___x_1377_ = l_Lean_MessageData_ofName(v_mod_1358_);
v___x_1378_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1378_, 0, v___x_1376_);
lean_ctor_set(v___x_1378_, 1, v___x_1377_);
v___x_1379_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__13);
v___x_1380_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1380_, 0, v___x_1378_);
lean_ctor_set(v___x_1380_, 1, v___x_1379_);
v___x_1381_ = l_Lean_MessageData_note(v___x_1380_);
v___x_1382_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1382_, 0, v_msg_1325_);
lean_ctor_set(v___x_1382_, 1, v___x_1381_);
if (v_isShared_1354_ == 0)
{
lean_ctor_set_tag(v___x_1353_, 0);
lean_ctor_set(v___x_1353_, 0, v___x_1382_);
v___x_1384_ = v___x_1353_;
goto v_reusejp_1383_;
}
else
{
lean_object* v_reuseFailAlloc_1385_; 
v_reuseFailAlloc_1385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1385_, 0, v___x_1382_);
v___x_1384_ = v_reuseFailAlloc_1385_;
goto v_reusejp_1383_;
}
v_reusejp_1383_:
{
return v___x_1384_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1387_; 
lean_dec_ref(v_env_1330_);
lean_dec(v_declHint_1326_);
v___x_1387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1387_, 0, v_msg_1325_);
return v___x_1387_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___boxed(lean_object* v_msg_1388_, lean_object* v_declHint_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_){
_start:
{
lean_object* v_res_1392_; 
v_res_1392_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg(v_msg_1388_, v_declHint_1389_, v___y_1390_);
lean_dec(v___y_1390_);
return v_res_1392_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8(lean_object* v_msg_1393_, lean_object* v_declHint_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_){
_start:
{
lean_object* v___x_1398_; lean_object* v_a_1399_; lean_object* v___x_1401_; uint8_t v_isShared_1402_; uint8_t v_isSharedCheck_1408_; 
v___x_1398_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg(v_msg_1393_, v_declHint_1394_, v___y_1396_);
v_a_1399_ = lean_ctor_get(v___x_1398_, 0);
v_isSharedCheck_1408_ = !lean_is_exclusive(v___x_1398_);
if (v_isSharedCheck_1408_ == 0)
{
v___x_1401_ = v___x_1398_;
v_isShared_1402_ = v_isSharedCheck_1408_;
goto v_resetjp_1400_;
}
else
{
lean_inc(v_a_1399_);
lean_dec(v___x_1398_);
v___x_1401_ = lean_box(0);
v_isShared_1402_ = v_isSharedCheck_1408_;
goto v_resetjp_1400_;
}
v_resetjp_1400_:
{
lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1406_; 
v___x_1403_ = l_Lean_unknownIdentifierMessageTag;
v___x_1404_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1404_, 0, v___x_1403_);
lean_ctor_set(v___x_1404_, 1, v_a_1399_);
if (v_isShared_1402_ == 0)
{
lean_ctor_set(v___x_1401_, 0, v___x_1404_);
v___x_1406_ = v___x_1401_;
goto v_reusejp_1405_;
}
else
{
lean_object* v_reuseFailAlloc_1407_; 
v_reuseFailAlloc_1407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1407_, 0, v___x_1404_);
v___x_1406_ = v_reuseFailAlloc_1407_;
goto v_reusejp_1405_;
}
v_reusejp_1405_:
{
return v___x_1406_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8___boxed(lean_object* v_msg_1409_, lean_object* v_declHint_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_){
_start:
{
lean_object* v_res_1414_; 
v_res_1414_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8(v_msg_1409_, v_declHint_1410_, v___y_1411_, v___y_1412_);
lean_dec(v___y_1412_);
lean_dec_ref(v___y_1411_);
return v_res_1414_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7___redArg(lean_object* v_ref_1415_, lean_object* v_msg_1416_, lean_object* v_declHint_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_){
_start:
{
lean_object* v___x_1421_; lean_object* v_a_1422_; lean_object* v___x_1423_; 
v___x_1421_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8(v_msg_1416_, v_declHint_1417_, v___y_1418_, v___y_1419_);
v_a_1422_ = lean_ctor_get(v___x_1421_, 0);
lean_inc(v_a_1422_);
lean_dec_ref(v___x_1421_);
v___x_1423_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__9___redArg(v_ref_1415_, v_a_1422_, v___y_1418_, v___y_1419_);
return v___x_1423_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7___redArg___boxed(lean_object* v_ref_1424_, lean_object* v_msg_1425_, lean_object* v_declHint_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_){
_start:
{
lean_object* v_res_1430_; 
v_res_1430_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7___redArg(v_ref_1424_, v_msg_1425_, v_declHint_1426_, v___y_1427_, v___y_1428_);
lean_dec(v___y_1428_);
lean_dec(v_ref_1424_);
return v_res_1430_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_1432_; lean_object* v___x_1433_; 
v___x_1432_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg___closed__0));
v___x_1433_ = l_Lean_stringToMessageData(v___x_1432_);
return v___x_1433_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_1435_; lean_object* v___x_1436_; 
v___x_1435_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg___closed__2));
v___x_1436_ = l_Lean_stringToMessageData(v___x_1435_);
return v___x_1436_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg(lean_object* v_ref_1437_, lean_object* v_constName_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_){
_start:
{
lean_object* v___x_1442_; uint8_t v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; 
v___x_1442_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg___closed__1);
v___x_1443_ = 0;
lean_inc(v_constName_1438_);
v___x_1444_ = l_Lean_MessageData_ofConstName(v_constName_1438_, v___x_1443_);
v___x_1445_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1445_, 0, v___x_1442_);
lean_ctor_set(v___x_1445_, 1, v___x_1444_);
v___x_1446_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg___closed__3);
v___x_1447_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1447_, 0, v___x_1445_);
lean_ctor_set(v___x_1447_, 1, v___x_1446_);
v___x_1448_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7___redArg(v_ref_1437_, v___x_1447_, v_constName_1438_, v___y_1439_, v___y_1440_);
return v___x_1448_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg___boxed(lean_object* v_ref_1449_, lean_object* v_constName_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_){
_start:
{
lean_object* v_res_1454_; 
v_res_1454_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg(v_ref_1449_, v_constName_1450_, v___y_1451_, v___y_1452_);
lean_dec(v___y_1452_);
lean_dec(v_ref_1449_);
return v_res_1454_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3___redArg(lean_object* v_constName_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_){
_start:
{
lean_object* v_ref_1459_; lean_object* v___x_1460_; 
v_ref_1459_ = lean_ctor_get(v___y_1456_, 5);
lean_inc(v_ref_1459_);
v___x_1460_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg(v_ref_1459_, v_constName_1455_, v___y_1456_, v___y_1457_);
lean_dec(v_ref_1459_);
return v___x_1460_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3___redArg___boxed(lean_object* v_constName_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_){
_start:
{
lean_object* v_res_1465_; 
v_res_1465_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3___redArg(v_constName_1461_, v___y_1462_, v___y_1463_);
lean_dec(v___y_1463_);
return v_res_1465_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2(lean_object* v_constName_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_){
_start:
{
lean_object* v___x_1470_; lean_object* v_env_1471_; uint8_t v___x_1472_; lean_object* v___x_1473_; 
v___x_1470_ = lean_st_ref_get(v___y_1468_);
v_env_1471_ = lean_ctor_get(v___x_1470_, 0);
lean_inc_ref(v_env_1471_);
lean_dec(v___x_1470_);
v___x_1472_ = 0;
lean_inc(v_constName_1466_);
v___x_1473_ = l_Lean_Environment_find_x3f(v_env_1471_, v_constName_1466_, v___x_1472_);
if (lean_obj_tag(v___x_1473_) == 0)
{
lean_object* v___x_1474_; 
v___x_1474_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3___redArg(v_constName_1466_, v___y_1467_, v___y_1468_);
return v___x_1474_;
}
else
{
lean_object* v_val_1475_; lean_object* v___x_1477_; uint8_t v_isShared_1478_; uint8_t v_isSharedCheck_1482_; 
lean_dec_ref(v___y_1467_);
lean_dec(v_constName_1466_);
v_val_1475_ = lean_ctor_get(v___x_1473_, 0);
v_isSharedCheck_1482_ = !lean_is_exclusive(v___x_1473_);
if (v_isSharedCheck_1482_ == 0)
{
v___x_1477_ = v___x_1473_;
v_isShared_1478_ = v_isSharedCheck_1482_;
goto v_resetjp_1476_;
}
else
{
lean_inc(v_val_1475_);
lean_dec(v___x_1473_);
v___x_1477_ = lean_box(0);
v_isShared_1478_ = v_isSharedCheck_1482_;
goto v_resetjp_1476_;
}
v_resetjp_1476_:
{
lean_object* v___x_1480_; 
if (v_isShared_1478_ == 0)
{
lean_ctor_set_tag(v___x_1477_, 0);
v___x_1480_ = v___x_1477_;
goto v_reusejp_1479_;
}
else
{
lean_object* v_reuseFailAlloc_1481_; 
v_reuseFailAlloc_1481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1481_, 0, v_val_1475_);
v___x_1480_ = v_reuseFailAlloc_1481_;
goto v_reusejp_1479_;
}
v_reusejp_1479_:
{
return v___x_1480_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2___boxed(lean_object* v_constName_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_){
_start:
{
lean_object* v_res_1487_; 
v_res_1487_ = l_Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2(v_constName_1483_, v___y_1484_, v___y_1485_);
lean_dec(v___y_1485_);
return v_res_1487_;
}
}
static lean_object* _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1489_; lean_object* v___x_1490_; 
v___x_1489_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__0));
v___x_1490_ = l_Lean_stringToMessageData(v___x_1489_);
return v___x_1490_;
}
}
static lean_object* _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1492_; lean_object* v___x_1493_; 
v___x_1492_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__2));
v___x_1493_ = l_Lean_stringToMessageData(v___x_1492_);
return v___x_1493_;
}
}
static lean_object* _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__5(void){
_start:
{
lean_object* v___x_1495_; lean_object* v___x_1496_; 
v___x_1495_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__4));
v___x_1496_ = l_Lean_stringToMessageData(v___x_1495_);
return v___x_1496_;
}
}
static lean_object* _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__7(void){
_start:
{
lean_object* v___x_1498_; lean_object* v___x_1499_; 
v___x_1498_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__6));
v___x_1499_ = l_Lean_stringToMessageData(v___x_1498_);
return v___x_1499_;
}
}
static lean_object* _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__9(void){
_start:
{
lean_object* v___x_1501_; lean_object* v___x_1502_; 
v___x_1501_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__8));
v___x_1502_ = l_Lean_stringToMessageData(v___x_1501_);
return v___x_1502_;
}
}
static lean_object* _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__11(void){
_start:
{
lean_object* v___x_1504_; lean_object* v___x_1505_; 
v___x_1504_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__10));
v___x_1505_ = l_Lean_stringToMessageData(v___x_1504_);
return v___x_1505_;
}
}
static lean_object* _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__13(void){
_start:
{
lean_object* v___x_1507_; lean_object* v___x_1508_; 
v___x_1507_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__12));
v___x_1508_ = l_Lean_stringToMessageData(v___x_1507_);
return v___x_1508_;
}
}
static lean_object* _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__15(void){
_start:
{
lean_object* v___x_1510_; lean_object* v___x_1511_; 
v___x_1510_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__14));
v___x_1511_ = l_Lean_stringToMessageData(v___x_1510_);
return v___x_1511_;
}
}
static lean_object* _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__17(void){
_start:
{
lean_object* v___x_1513_; lean_object* v___x_1514_; 
v___x_1513_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__16));
v___x_1514_ = l_Lean_stringToMessageData(v___x_1513_);
return v___x_1514_;
}
}
static lean_object* _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__19(void){
_start:
{
lean_object* v___x_1516_; lean_object* v___x_1517_; 
v___x_1516_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__18));
v___x_1517_ = l_Lean_stringToMessageData(v___x_1516_);
return v___x_1517_;
}
}
static lean_object* _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__21(void){
_start:
{
lean_object* v___x_1519_; lean_object* v___x_1520_; 
v___x_1519_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__20));
v___x_1520_ = l_Lean_stringToMessageData(v___x_1519_);
return v___x_1520_;
}
}
static lean_object* _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__23(void){
_start:
{
lean_object* v___x_1522_; lean_object* v___x_1523_; 
v___x_1522_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__22));
v___x_1523_ = l_Lean_stringToMessageData(v___x_1522_);
return v___x_1523_;
}
}
static lean_object* _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__25(void){
_start:
{
lean_object* v___x_1525_; lean_object* v___x_1526_; 
v___x_1525_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__24));
v___x_1526_ = l_Lean_stringToMessageData(v___x_1525_);
return v___x_1526_;
}
}
static lean_object* _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__27(void){
_start:
{
lean_object* v___x_1528_; lean_object* v___x_1529_; 
v___x_1528_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__26));
v___x_1529_ = l_Lean_stringToMessageData(v___x_1528_);
return v___x_1529_;
}
}
static lean_object* _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__29(void){
_start:
{
lean_object* v___x_1531_; lean_object* v___x_1532_; 
v___x_1531_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__28));
v___x_1532_ = l_Lean_stringToMessageData(v___x_1531_);
return v___x_1532_;
}
}
static lean_object* _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__31(void){
_start:
{
lean_object* v___x_1534_; lean_object* v___x_1535_; 
v___x_1534_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__30));
v___x_1535_ = l_Lean_stringToMessageData(v___x_1534_);
return v___x_1535_;
}
}
static lean_object* _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__33(void){
_start:
{
lean_object* v___x_1537_; lean_object* v___x_1538_; 
v___x_1537_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__32));
v___x_1538_ = l_Lean_stringToMessageData(v___x_1537_);
return v___x_1538_;
}
}
static lean_object* _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__35(void){
_start:
{
lean_object* v___x_1540_; lean_object* v___x_1541_; 
v___x_1540_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__34));
v___x_1541_ = l_Lean_stringToMessageData(v___x_1540_);
return v___x_1541_;
}
}
static lean_object* _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__37(void){
_start:
{
lean_object* v___x_1543_; lean_object* v___x_1544_; 
v___x_1543_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__36));
v___x_1544_ = l_Lean_stringToMessageData(v___x_1543_);
return v___x_1544_;
}
}
static lean_object* _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__39(void){
_start:
{
lean_object* v___x_1546_; lean_object* v___x_1547_; 
v___x_1546_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__38));
v___x_1547_ = l_Lean_stringToMessageData(v___x_1546_);
return v___x_1547_;
}
}
static lean_object* _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__41(void){
_start:
{
lean_object* v___x_1549_; lean_object* v___x_1550_; 
v___x_1549_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__40));
v___x_1550_ = l_Lean_stringToMessageData(v___x_1549_);
return v___x_1550_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0(lean_object* v_declName_1551_, uint8_t v_status_1552_, lean_object* v_suffix_1553_, uint8_t v_attrKind_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_){
_start:
{
lean_object* v_options_1576_; lean_object* v___x_1577_; uint8_t v___x_1578_; uint8_t v___y_1580_; lean_object* v___y_1581_; lean_object* v___y_1582_; lean_object* v___y_1627_; lean_object* v___y_1628_; uint8_t v___y_1629_; lean_object* v___y_1638_; lean_object* v___y_1639_; 
v_options_1576_ = lean_ctor_get(v___y_1555_, 2);
v___x_1577_ = l_Lean_allowUnsafeReducibility;
v___x_1578_ = l_Lean_Option_get___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__0(v_options_1576_, v___x_1577_);
if (v___x_1578_ == 0)
{
lean_object* v___x_1696_; 
lean_inc_ref(v___y_1555_);
lean_inc(v_declName_1551_);
v___x_1696_ = l_Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2(v_declName_1551_, v___y_1555_, v___y_1556_);
if (lean_obj_tag(v___x_1696_) == 0)
{
lean_object* v_a_1697_; uint8_t v___x_1698_; 
v_a_1697_ = lean_ctor_get(v___x_1696_, 0);
lean_inc(v_a_1697_);
lean_dec_ref(v___x_1696_);
v___x_1698_ = l_Lean_ConstantInfo_isDefinition(v_a_1697_);
lean_dec(v_a_1697_);
if (v___x_1698_ == 0)
{
lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; 
v___x_1699_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__15, &l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__15_once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__15);
v___x_1700_ = l_Lean_MessageData_ofConstName(v_declName_1551_, v___x_1698_);
v___x_1701_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1701_, 0, v___x_1699_);
lean_ctor_set(v___x_1701_, 1, v___x_1700_);
v___x_1702_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__41, &l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__41_once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__41);
v___x_1703_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1703_, 0, v___x_1701_);
lean_ctor_set(v___x_1703_, 1, v___x_1702_);
v___x_1704_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1704_, 0, v___x_1703_);
lean_ctor_set(v___x_1704_, 1, v_suffix_1553_);
v___x_1705_ = l_Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1___redArg(v___x_1704_, v___y_1555_, v___y_1556_);
lean_dec_ref(v___y_1555_);
return v___x_1705_;
}
else
{
v___y_1638_ = v___y_1555_;
v___y_1639_ = v___y_1556_;
goto v___jp_1637_;
}
}
else
{
lean_object* v_a_1706_; lean_object* v___x_1708_; uint8_t v_isShared_1709_; uint8_t v_isSharedCheck_1713_; 
lean_dec_ref(v___y_1555_);
lean_dec_ref(v_suffix_1553_);
lean_dec(v_declName_1551_);
v_a_1706_ = lean_ctor_get(v___x_1696_, 0);
v_isSharedCheck_1713_ = !lean_is_exclusive(v___x_1696_);
if (v_isSharedCheck_1713_ == 0)
{
v___x_1708_ = v___x_1696_;
v_isShared_1709_ = v_isSharedCheck_1713_;
goto v_resetjp_1707_;
}
else
{
lean_inc(v_a_1706_);
lean_dec(v___x_1696_);
v___x_1708_ = lean_box(0);
v_isShared_1709_ = v_isSharedCheck_1713_;
goto v_resetjp_1707_;
}
v_resetjp_1707_:
{
lean_object* v___x_1711_; 
if (v_isShared_1709_ == 0)
{
v___x_1711_ = v___x_1708_;
goto v_reusejp_1710_;
}
else
{
lean_object* v_reuseFailAlloc_1712_; 
v_reuseFailAlloc_1712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1712_, 0, v_a_1706_);
v___x_1711_ = v_reuseFailAlloc_1712_;
goto v_reusejp_1710_;
}
v_reusejp_1710_:
{
return v___x_1711_;
}
}
}
}
else
{
lean_object* v___x_1714_; lean_object* v___x_1715_; 
lean_dec_ref(v___y_1555_);
lean_dec_ref(v_suffix_1553_);
lean_dec(v_declName_1551_);
v___x_1714_ = lean_box(0);
v___x_1715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1715_, 0, v___x_1714_);
return v___x_1715_;
}
v___jp_1558_:
{
lean_object* v___x_1559_; lean_object* v___x_1560_; 
v___x_1559_ = lean_box(0);
v___x_1560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1560_, 0, v___x_1559_);
return v___x_1560_;
}
v___jp_1561_:
{
lean_object* v___x_1562_; lean_object* v___x_1563_; 
v___x_1562_ = lean_box(0);
v___x_1563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1563_, 0, v___x_1562_);
return v___x_1563_;
}
v___jp_1564_:
{
lean_object* v___x_1565_; lean_object* v___x_1566_; 
v___x_1565_ = lean_box(0);
v___x_1566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1566_, 0, v___x_1565_);
return v___x_1566_;
}
v___jp_1567_:
{
lean_object* v___x_1568_; lean_object* v___x_1569_; 
v___x_1568_ = lean_box(0);
v___x_1569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1569_, 0, v___x_1568_);
return v___x_1569_;
}
v___jp_1570_:
{
lean_object* v___x_1571_; lean_object* v___x_1572_; 
v___x_1571_ = lean_box(0);
v___x_1572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1572_, 0, v___x_1571_);
return v___x_1572_;
}
v___jp_1573_:
{
lean_object* v___x_1574_; lean_object* v___x_1575_; 
v___x_1574_ = lean_box(0);
v___x_1575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1575_, 0, v___x_1574_);
return v___x_1575_;
}
v___jp_1579_:
{
switch(v_status_1552_)
{
case 0:
{
if (v___y_1580_ == 1)
{
lean_dec_ref(v___y_1581_);
lean_dec_ref(v_suffix_1553_);
lean_dec(v_declName_1551_);
goto v___jp_1573_;
}
else
{
if (v___x_1578_ == 0)
{
lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; 
v___x_1583_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__1, &l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__1_once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__1);
v___x_1584_ = l_Lean_MessageData_ofConstName(v_declName_1551_, v___x_1578_);
v___x_1585_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1585_, 0, v___x_1583_);
lean_ctor_set(v___x_1585_, 1, v___x_1584_);
v___x_1586_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__3, &l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__3_once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__3);
v___x_1587_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1587_, 0, v___x_1585_);
lean_ctor_set(v___x_1587_, 1, v___x_1586_);
v___x_1588_ = l_Lean_ReducibilityStatus_toAttrString(v___y_1580_);
v___x_1589_ = l_Lean_stringToMessageData(v___x_1588_);
v___x_1590_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1590_, 0, v___x_1587_);
lean_ctor_set(v___x_1590_, 1, v___x_1589_);
v___x_1591_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg___closed__3);
v___x_1592_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1592_, 0, v___x_1590_);
lean_ctor_set(v___x_1592_, 1, v___x_1591_);
v___x_1593_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1593_, 0, v___x_1592_);
lean_ctor_set(v___x_1593_, 1, v_suffix_1553_);
v___x_1594_ = l_Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1___redArg(v___x_1593_, v___y_1581_, v___y_1582_);
lean_dec_ref(v___y_1581_);
return v___x_1594_;
}
else
{
lean_dec_ref(v___y_1581_);
lean_dec_ref(v_suffix_1553_);
lean_dec(v_declName_1551_);
goto v___jp_1573_;
}
}
}
case 1:
{
lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; 
v___x_1595_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__5, &l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__5_once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__5);
v___x_1596_ = l_Lean_MessageData_ofConstName(v_declName_1551_, v___x_1578_);
v___x_1597_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1597_, 0, v___x_1595_);
lean_ctor_set(v___x_1597_, 1, v___x_1596_);
v___x_1598_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__7, &l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__7_once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__7);
v___x_1599_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1599_, 0, v___x_1597_);
lean_ctor_set(v___x_1599_, 1, v___x_1598_);
v___x_1600_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1600_, 0, v___x_1599_);
lean_ctor_set(v___x_1600_, 1, v_suffix_1553_);
v___x_1601_ = l_Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1___redArg(v___x_1600_, v___y_1581_, v___y_1582_);
lean_dec_ref(v___y_1581_);
return v___x_1601_;
}
case 2:
{
switch(v___y_1580_)
{
case 1:
{
lean_dec_ref(v___y_1581_);
lean_dec_ref(v_suffix_1553_);
lean_dec(v_declName_1551_);
goto v___jp_1570_;
}
case 3:
{
lean_dec_ref(v___y_1581_);
lean_dec_ref(v_suffix_1553_);
lean_dec(v_declName_1551_);
goto v___jp_1570_;
}
default: 
{
if (v___x_1578_ == 0)
{
lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; 
v___x_1602_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__9, &l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__9_once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__9);
v___x_1603_ = l_Lean_MessageData_ofConstName(v_declName_1551_, v___x_1578_);
v___x_1604_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1604_, 0, v___x_1602_);
lean_ctor_set(v___x_1604_, 1, v___x_1603_);
v___x_1605_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__11, &l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__11_once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__11);
v___x_1606_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1606_, 0, v___x_1604_);
lean_ctor_set(v___x_1606_, 1, v___x_1605_);
v___x_1607_ = l_Lean_ReducibilityStatus_toAttrString(v___y_1580_);
v___x_1608_ = l_Lean_stringToMessageData(v___x_1607_);
v___x_1609_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1609_, 0, v___x_1606_);
lean_ctor_set(v___x_1609_, 1, v___x_1608_);
v___x_1610_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg___closed__3);
v___x_1611_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1611_, 0, v___x_1609_);
lean_ctor_set(v___x_1611_, 1, v___x_1610_);
v___x_1612_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1612_, 0, v___x_1611_);
lean_ctor_set(v___x_1612_, 1, v_suffix_1553_);
v___x_1613_ = l_Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1___redArg(v___x_1612_, v___y_1581_, v___y_1582_);
lean_dec_ref(v___y_1581_);
return v___x_1613_;
}
else
{
lean_dec_ref(v___y_1581_);
lean_dec_ref(v_suffix_1553_);
lean_dec(v_declName_1551_);
goto v___jp_1570_;
}
}
}
}
default: 
{
if (v___y_1580_ == 1)
{
lean_dec_ref(v___y_1581_);
lean_dec_ref(v_suffix_1553_);
lean_dec(v_declName_1551_);
goto v___jp_1567_;
}
else
{
if (v___x_1578_ == 0)
{
lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; 
v___x_1614_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__13, &l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__13_once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__13);
v___x_1615_ = l_Lean_MessageData_ofConstName(v_declName_1551_, v___x_1578_);
v___x_1616_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1616_, 0, v___x_1614_);
lean_ctor_set(v___x_1616_, 1, v___x_1615_);
v___x_1617_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__3, &l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__3_once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__3);
v___x_1618_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1618_, 0, v___x_1616_);
lean_ctor_set(v___x_1618_, 1, v___x_1617_);
v___x_1619_ = l_Lean_ReducibilityStatus_toAttrString(v___y_1580_);
v___x_1620_ = l_Lean_stringToMessageData(v___x_1619_);
v___x_1621_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1621_, 0, v___x_1618_);
lean_ctor_set(v___x_1621_, 1, v___x_1620_);
v___x_1622_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg___closed__3);
v___x_1623_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1623_, 0, v___x_1621_);
lean_ctor_set(v___x_1623_, 1, v___x_1622_);
v___x_1624_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1624_, 0, v___x_1623_);
lean_ctor_set(v___x_1624_, 1, v_suffix_1553_);
v___x_1625_ = l_Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1___redArg(v___x_1624_, v___y_1581_, v___y_1582_);
lean_dec_ref(v___y_1581_);
return v___x_1625_;
}
else
{
lean_dec_ref(v___y_1581_);
lean_dec_ref(v_suffix_1553_);
lean_dec(v_declName_1551_);
goto v___jp_1567_;
}
}
}
}
}
v___jp_1626_:
{
lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; 
v___x_1630_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__15, &l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__15_once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__15);
v___x_1631_ = l_Lean_MessageData_ofConstName(v_declName_1551_, v___x_1578_);
v___x_1632_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1632_, 0, v___x_1630_);
lean_ctor_set(v___x_1632_, 1, v___x_1631_);
v___x_1633_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__17, &l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__17_once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__17);
v___x_1634_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1634_, 0, v___x_1632_);
lean_ctor_set(v___x_1634_, 1, v___x_1633_);
v___x_1635_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1635_, 0, v___x_1634_);
lean_ctor_set(v___x_1635_, 1, v_suffix_1553_);
v___x_1636_ = l_Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1___redArg(v___x_1635_, v___y_1628_, v___y_1627_);
lean_dec_ref(v___y_1628_);
return v___x_1636_;
}
v___jp_1637_:
{
lean_object* v___x_1640_; lean_object* v_env_1641_; uint8_t v___x_1642_; 
v___x_1640_ = lean_st_ref_get(v___y_1639_);
v_env_1641_ = lean_ctor_get(v___x_1640_, 0);
lean_inc_ref(v_env_1641_);
lean_dec(v___x_1640_);
lean_inc(v_declName_1551_);
v___x_1642_ = lean_get_reducibility_status(v_env_1641_, v_declName_1551_);
switch(v_attrKind_1554_)
{
case 0:
{
lean_object* v___x_1643_; lean_object* v_env_1644_; lean_object* v___x_1645_; 
v___x_1643_ = lean_st_ref_get(v___y_1639_);
v_env_1644_ = lean_ctor_get(v___x_1643_, 0);
lean_inc_ref(v_env_1644_);
lean_dec(v___x_1643_);
v___x_1645_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1644_, v_declName_1551_);
lean_dec_ref(v_env_1644_);
if (lean_obj_tag(v___x_1645_) == 1)
{
lean_dec_ref(v___x_1645_);
v___y_1627_ = v___y_1639_;
v___y_1628_ = v___y_1638_;
v___y_1629_ = v___x_1642_;
goto v___jp_1626_;
}
else
{
lean_dec(v___x_1645_);
if (v___x_1578_ == 0)
{
v___y_1580_ = v___x_1642_;
v___y_1581_ = v___y_1638_;
v___y_1582_ = v___y_1639_;
goto v___jp_1579_;
}
else
{
v___y_1627_ = v___y_1639_;
v___y_1628_ = v___y_1638_;
v___y_1629_ = v___x_1642_;
goto v___jp_1626_;
}
}
}
case 1:
{
switch(v_status_1552_)
{
case 0:
{
lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; 
v___x_1646_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__19, &l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__19_once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__19);
v___x_1647_ = l_Lean_MessageData_ofConstName(v_declName_1551_, v___x_1578_);
v___x_1648_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1648_, 0, v___x_1646_);
lean_ctor_set(v___x_1648_, 1, v___x_1647_);
v___x_1649_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__21, &l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__21_once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__21);
v___x_1650_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1650_, 0, v___x_1648_);
lean_ctor_set(v___x_1650_, 1, v___x_1649_);
v___x_1651_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1651_, 0, v___x_1650_);
lean_ctor_set(v___x_1651_, 1, v_suffix_1553_);
v___x_1652_ = l_Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1___redArg(v___x_1651_, v___y_1638_, v___y_1639_);
lean_dec_ref(v___y_1638_);
return v___x_1652_;
}
case 1:
{
if (v___x_1642_ == 2)
{
lean_dec_ref(v___y_1638_);
lean_dec_ref(v_suffix_1553_);
lean_dec(v_declName_1551_);
goto v___jp_1558_;
}
else
{
if (v___x_1578_ == 0)
{
lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; 
v___x_1653_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__23, &l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__23_once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__23);
v___x_1654_ = l_Lean_MessageData_ofConstName(v_declName_1551_, v___x_1578_);
v___x_1655_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1655_, 0, v___x_1653_);
lean_ctor_set(v___x_1655_, 1, v___x_1654_);
v___x_1656_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__25, &l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__25_once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__25);
v___x_1657_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1657_, 0, v___x_1655_);
lean_ctor_set(v___x_1657_, 1, v___x_1656_);
v___x_1658_ = l_Lean_ReducibilityStatus_toAttrString(v___x_1642_);
v___x_1659_ = l_Lean_stringToMessageData(v___x_1658_);
v___x_1660_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1660_, 0, v___x_1657_);
lean_ctor_set(v___x_1660_, 1, v___x_1659_);
v___x_1661_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__27, &l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__27_once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__27);
v___x_1662_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1662_, 0, v___x_1660_);
lean_ctor_set(v___x_1662_, 1, v___x_1661_);
v___x_1663_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1663_, 0, v___x_1662_);
lean_ctor_set(v___x_1663_, 1, v_suffix_1553_);
v___x_1664_ = l_Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1___redArg(v___x_1663_, v___y_1638_, v___y_1639_);
lean_dec_ref(v___y_1638_);
return v___x_1664_;
}
else
{
lean_dec_ref(v___y_1638_);
lean_dec_ref(v_suffix_1553_);
lean_dec(v_declName_1551_);
goto v___jp_1558_;
}
}
}
case 2:
{
switch(v___x_1642_)
{
case 1:
{
lean_dec_ref(v___y_1638_);
lean_dec_ref(v_suffix_1553_);
lean_dec(v_declName_1551_);
goto v___jp_1561_;
}
case 3:
{
lean_dec_ref(v___y_1638_);
lean_dec_ref(v_suffix_1553_);
lean_dec(v_declName_1551_);
goto v___jp_1561_;
}
default: 
{
if (v___x_1578_ == 0)
{
lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; 
v___x_1665_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__29, &l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__29_once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__29);
v___x_1666_ = l_Lean_MessageData_ofConstName(v_declName_1551_, v___x_1578_);
v___x_1667_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1667_, 0, v___x_1665_);
lean_ctor_set(v___x_1667_, 1, v___x_1666_);
v___x_1668_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__25, &l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__25_once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__25);
v___x_1669_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1669_, 0, v___x_1667_);
lean_ctor_set(v___x_1669_, 1, v___x_1668_);
v___x_1670_ = l_Lean_ReducibilityStatus_toAttrString(v___x_1642_);
v___x_1671_ = l_Lean_stringToMessageData(v___x_1670_);
v___x_1672_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1672_, 0, v___x_1669_);
lean_ctor_set(v___x_1672_, 1, v___x_1671_);
v___x_1673_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__31, &l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__31_once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__31);
v___x_1674_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1674_, 0, v___x_1672_);
lean_ctor_set(v___x_1674_, 1, v___x_1673_);
v___x_1675_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1675_, 0, v___x_1674_);
lean_ctor_set(v___x_1675_, 1, v_suffix_1553_);
v___x_1676_ = l_Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1___redArg(v___x_1675_, v___y_1638_, v___y_1639_);
lean_dec_ref(v___y_1638_);
return v___x_1676_;
}
else
{
lean_dec_ref(v___y_1638_);
lean_dec_ref(v_suffix_1553_);
lean_dec(v_declName_1551_);
goto v___jp_1561_;
}
}
}
}
default: 
{
if (v___x_1642_ == 1)
{
lean_dec_ref(v___y_1638_);
lean_dec_ref(v_suffix_1553_);
lean_dec(v_declName_1551_);
goto v___jp_1564_;
}
else
{
if (v___x_1578_ == 0)
{
lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; 
v___x_1677_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__33, &l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__33_once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__33);
v___x_1678_ = l_Lean_MessageData_ofConstName(v_declName_1551_, v___x_1578_);
v___x_1679_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1679_, 0, v___x_1677_);
lean_ctor_set(v___x_1679_, 1, v___x_1678_);
v___x_1680_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__25, &l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__25_once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__25);
v___x_1681_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1681_, 0, v___x_1679_);
lean_ctor_set(v___x_1681_, 1, v___x_1680_);
v___x_1682_ = l_Lean_ReducibilityStatus_toAttrString(v___x_1642_);
v___x_1683_ = l_Lean_stringToMessageData(v___x_1682_);
v___x_1684_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1684_, 0, v___x_1681_);
lean_ctor_set(v___x_1684_, 1, v___x_1683_);
v___x_1685_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__35, &l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__35_once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__35);
v___x_1686_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1686_, 0, v___x_1684_);
lean_ctor_set(v___x_1686_, 1, v___x_1685_);
v___x_1687_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1687_, 0, v___x_1686_);
lean_ctor_set(v___x_1687_, 1, v_suffix_1553_);
v___x_1688_ = l_Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1___redArg(v___x_1687_, v___y_1638_, v___y_1639_);
lean_dec_ref(v___y_1638_);
return v___x_1688_;
}
else
{
lean_dec_ref(v___y_1638_);
lean_dec_ref(v_suffix_1553_);
lean_dec(v_declName_1551_);
goto v___jp_1564_;
}
}
}
}
}
default: 
{
lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; 
v___x_1689_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__37, &l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__37_once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__37);
v___x_1690_ = l_Lean_MessageData_ofConstName(v_declName_1551_, v___x_1578_);
v___x_1691_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1691_, 0, v___x_1689_);
lean_ctor_set(v___x_1691_, 1, v___x_1690_);
v___x_1692_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__39, &l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__39_once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__39);
v___x_1693_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1693_, 0, v___x_1691_);
lean_ctor_set(v___x_1693_, 1, v___x_1692_);
v___x_1694_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1694_, 0, v___x_1693_);
lean_ctor_set(v___x_1694_, 1, v_suffix_1553_);
v___x_1695_ = l_Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1___redArg(v___x_1694_, v___y_1638_, v___y_1639_);
lean_dec_ref(v___y_1638_);
return v___x_1695_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___boxed(lean_object* v_declName_1716_, lean_object* v_status_1717_, lean_object* v_suffix_1718_, lean_object* v_attrKind_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_){
_start:
{
uint8_t v_status_boxed_1723_; uint8_t v_attrKind_boxed_1724_; lean_object* v_res_1725_; 
v_status_boxed_1723_ = lean_unbox(v_status_1717_);
v_attrKind_boxed_1724_ = lean_unbox(v_attrKind_1719_);
v_res_1725_ = l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0(v_declName_1716_, v_status_boxed_1723_, v_suffix_1718_, v_attrKind_boxed_1724_, v___y_1720_, v___y_1721_);
lean_dec(v___y_1721_);
return v_res_1725_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___redArg___lam__0(lean_object* v___y_1726_, uint8_t v_isExporting_1727_, lean_object* v___x_1728_, lean_object* v_a_x3f_1729_){
_start:
{
lean_object* v___x_1731_; lean_object* v_env_1732_; lean_object* v_nextMacroScope_1733_; lean_object* v_ngen_1734_; lean_object* v_auxDeclNGen_1735_; lean_object* v_traceState_1736_; lean_object* v_messages_1737_; lean_object* v_infoState_1738_; lean_object* v_snapshotTasks_1739_; lean_object* v___x_1741_; uint8_t v_isShared_1742_; uint8_t v_isSharedCheck_1750_; 
v___x_1731_ = lean_st_ref_take(v___y_1726_);
v_env_1732_ = lean_ctor_get(v___x_1731_, 0);
v_nextMacroScope_1733_ = lean_ctor_get(v___x_1731_, 1);
v_ngen_1734_ = lean_ctor_get(v___x_1731_, 2);
v_auxDeclNGen_1735_ = lean_ctor_get(v___x_1731_, 3);
v_traceState_1736_ = lean_ctor_get(v___x_1731_, 4);
v_messages_1737_ = lean_ctor_get(v___x_1731_, 6);
v_infoState_1738_ = lean_ctor_get(v___x_1731_, 7);
v_snapshotTasks_1739_ = lean_ctor_get(v___x_1731_, 8);
v_isSharedCheck_1750_ = !lean_is_exclusive(v___x_1731_);
if (v_isSharedCheck_1750_ == 0)
{
lean_object* v_unused_1751_; 
v_unused_1751_ = lean_ctor_get(v___x_1731_, 5);
lean_dec(v_unused_1751_);
v___x_1741_ = v___x_1731_;
v_isShared_1742_ = v_isSharedCheck_1750_;
goto v_resetjp_1740_;
}
else
{
lean_inc(v_snapshotTasks_1739_);
lean_inc(v_infoState_1738_);
lean_inc(v_messages_1737_);
lean_inc(v_traceState_1736_);
lean_inc(v_auxDeclNGen_1735_);
lean_inc(v_ngen_1734_);
lean_inc(v_nextMacroScope_1733_);
lean_inc(v_env_1732_);
lean_dec(v___x_1731_);
v___x_1741_ = lean_box(0);
v_isShared_1742_ = v_isSharedCheck_1750_;
goto v_resetjp_1740_;
}
v_resetjp_1740_:
{
lean_object* v___x_1743_; lean_object* v___x_1745_; 
v___x_1743_ = l_Lean_Environment_setExporting(v_env_1732_, v_isExporting_1727_);
if (v_isShared_1742_ == 0)
{
lean_ctor_set(v___x_1741_, 5, v___x_1728_);
lean_ctor_set(v___x_1741_, 0, v___x_1743_);
v___x_1745_ = v___x_1741_;
goto v_reusejp_1744_;
}
else
{
lean_object* v_reuseFailAlloc_1749_; 
v_reuseFailAlloc_1749_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1749_, 0, v___x_1743_);
lean_ctor_set(v_reuseFailAlloc_1749_, 1, v_nextMacroScope_1733_);
lean_ctor_set(v_reuseFailAlloc_1749_, 2, v_ngen_1734_);
lean_ctor_set(v_reuseFailAlloc_1749_, 3, v_auxDeclNGen_1735_);
lean_ctor_set(v_reuseFailAlloc_1749_, 4, v_traceState_1736_);
lean_ctor_set(v_reuseFailAlloc_1749_, 5, v___x_1728_);
lean_ctor_set(v_reuseFailAlloc_1749_, 6, v_messages_1737_);
lean_ctor_set(v_reuseFailAlloc_1749_, 7, v_infoState_1738_);
lean_ctor_set(v_reuseFailAlloc_1749_, 8, v_snapshotTasks_1739_);
v___x_1745_ = v_reuseFailAlloc_1749_;
goto v_reusejp_1744_;
}
v_reusejp_1744_:
{
lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; 
v___x_1746_ = lean_st_ref_set(v___y_1726_, v___x_1745_);
v___x_1747_ = lean_box(0);
v___x_1748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1748_, 0, v___x_1747_);
return v___x_1748_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___redArg___lam__0___boxed(lean_object* v___y_1752_, lean_object* v_isExporting_1753_, lean_object* v___x_1754_, lean_object* v_a_x3f_1755_, lean_object* v___y_1756_){
_start:
{
uint8_t v_isExporting_boxed_1757_; lean_object* v_res_1758_; 
v_isExporting_boxed_1757_ = lean_unbox(v_isExporting_1753_);
v_res_1758_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___redArg___lam__0(v___y_1752_, v_isExporting_boxed_1757_, v___x_1754_, v_a_x3f_1755_);
lean_dec(v_a_x3f_1755_);
lean_dec(v___y_1752_);
return v_res_1758_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_1759_; 
v___x_1759_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1759_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_1760_; lean_object* v___x_1761_; 
v___x_1760_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___redArg___closed__0, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___redArg___closed__0);
v___x_1761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1761_, 0, v___x_1760_);
return v___x_1761_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___redArg___closed__2(void){
_start:
{
lean_object* v___x_1762_; lean_object* v___x_1763_; 
v___x_1762_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___redArg___closed__1, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___redArg___closed__1);
v___x_1763_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1763_, 0, v___x_1762_);
lean_ctor_set(v___x_1763_, 1, v___x_1762_);
return v___x_1763_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___redArg(lean_object* v_x_1764_, uint8_t v_isExporting_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_){
_start:
{
lean_object* v___x_1769_; lean_object* v_env_1770_; uint8_t v_isExporting_1771_; lean_object* v___x_1772_; lean_object* v_env_1773_; lean_object* v_nextMacroScope_1774_; lean_object* v_ngen_1775_; lean_object* v_auxDeclNGen_1776_; lean_object* v_traceState_1777_; lean_object* v_messages_1778_; lean_object* v_infoState_1779_; lean_object* v_snapshotTasks_1780_; lean_object* v___x_1782_; uint8_t v_isShared_1783_; uint8_t v_isSharedCheck_1819_; 
v___x_1769_ = lean_st_ref_get(v___y_1767_);
v_env_1770_ = lean_ctor_get(v___x_1769_, 0);
lean_inc_ref(v_env_1770_);
lean_dec(v___x_1769_);
v_isExporting_1771_ = lean_ctor_get_uint8(v_env_1770_, sizeof(void*)*8);
lean_dec_ref(v_env_1770_);
v___x_1772_ = lean_st_ref_take(v___y_1767_);
v_env_1773_ = lean_ctor_get(v___x_1772_, 0);
v_nextMacroScope_1774_ = lean_ctor_get(v___x_1772_, 1);
v_ngen_1775_ = lean_ctor_get(v___x_1772_, 2);
v_auxDeclNGen_1776_ = lean_ctor_get(v___x_1772_, 3);
v_traceState_1777_ = lean_ctor_get(v___x_1772_, 4);
v_messages_1778_ = lean_ctor_get(v___x_1772_, 6);
v_infoState_1779_ = lean_ctor_get(v___x_1772_, 7);
v_snapshotTasks_1780_ = lean_ctor_get(v___x_1772_, 8);
v_isSharedCheck_1819_ = !lean_is_exclusive(v___x_1772_);
if (v_isSharedCheck_1819_ == 0)
{
lean_object* v_unused_1820_; 
v_unused_1820_ = lean_ctor_get(v___x_1772_, 5);
lean_dec(v_unused_1820_);
v___x_1782_ = v___x_1772_;
v_isShared_1783_ = v_isSharedCheck_1819_;
goto v_resetjp_1781_;
}
else
{
lean_inc(v_snapshotTasks_1780_);
lean_inc(v_infoState_1779_);
lean_inc(v_messages_1778_);
lean_inc(v_traceState_1777_);
lean_inc(v_auxDeclNGen_1776_);
lean_inc(v_ngen_1775_);
lean_inc(v_nextMacroScope_1774_);
lean_inc(v_env_1773_);
lean_dec(v___x_1772_);
v___x_1782_ = lean_box(0);
v_isShared_1783_ = v_isSharedCheck_1819_;
goto v_resetjp_1781_;
}
v_resetjp_1781_:
{
lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1787_; 
v___x_1784_ = l_Lean_Environment_setExporting(v_env_1773_, v_isExporting_1765_);
v___x_1785_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___redArg___closed__2, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___redArg___closed__2);
if (v_isShared_1783_ == 0)
{
lean_ctor_set(v___x_1782_, 5, v___x_1785_);
lean_ctor_set(v___x_1782_, 0, v___x_1784_);
v___x_1787_ = v___x_1782_;
goto v_reusejp_1786_;
}
else
{
lean_object* v_reuseFailAlloc_1818_; 
v_reuseFailAlloc_1818_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1818_, 0, v___x_1784_);
lean_ctor_set(v_reuseFailAlloc_1818_, 1, v_nextMacroScope_1774_);
lean_ctor_set(v_reuseFailAlloc_1818_, 2, v_ngen_1775_);
lean_ctor_set(v_reuseFailAlloc_1818_, 3, v_auxDeclNGen_1776_);
lean_ctor_set(v_reuseFailAlloc_1818_, 4, v_traceState_1777_);
lean_ctor_set(v_reuseFailAlloc_1818_, 5, v___x_1785_);
lean_ctor_set(v_reuseFailAlloc_1818_, 6, v_messages_1778_);
lean_ctor_set(v_reuseFailAlloc_1818_, 7, v_infoState_1779_);
lean_ctor_set(v_reuseFailAlloc_1818_, 8, v_snapshotTasks_1780_);
v___x_1787_ = v_reuseFailAlloc_1818_;
goto v_reusejp_1786_;
}
v_reusejp_1786_:
{
lean_object* v___x_1788_; lean_object* v_r_1789_; 
v___x_1788_ = lean_st_ref_set(v___y_1767_, v___x_1787_);
lean_inc(v___y_1767_);
v_r_1789_ = lean_apply_3(v_x_1764_, v___y_1766_, v___y_1767_, lean_box(0));
if (lean_obj_tag(v_r_1789_) == 0)
{
lean_object* v_a_1790_; lean_object* v___x_1792_; uint8_t v_isShared_1793_; uint8_t v_isSharedCheck_1806_; 
v_a_1790_ = lean_ctor_get(v_r_1789_, 0);
v_isSharedCheck_1806_ = !lean_is_exclusive(v_r_1789_);
if (v_isSharedCheck_1806_ == 0)
{
v___x_1792_ = v_r_1789_;
v_isShared_1793_ = v_isSharedCheck_1806_;
goto v_resetjp_1791_;
}
else
{
lean_inc(v_a_1790_);
lean_dec(v_r_1789_);
v___x_1792_ = lean_box(0);
v_isShared_1793_ = v_isSharedCheck_1806_;
goto v_resetjp_1791_;
}
v_resetjp_1791_:
{
lean_object* v___x_1795_; 
lean_inc(v_a_1790_);
if (v_isShared_1793_ == 0)
{
lean_ctor_set_tag(v___x_1792_, 1);
v___x_1795_ = v___x_1792_;
goto v_reusejp_1794_;
}
else
{
lean_object* v_reuseFailAlloc_1805_; 
v_reuseFailAlloc_1805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1805_, 0, v_a_1790_);
v___x_1795_ = v_reuseFailAlloc_1805_;
goto v_reusejp_1794_;
}
v_reusejp_1794_:
{
lean_object* v___x_1796_; lean_object* v___x_1798_; uint8_t v_isShared_1799_; uint8_t v_isSharedCheck_1803_; 
v___x_1796_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___redArg___lam__0(v___y_1767_, v_isExporting_1771_, v___x_1785_, v___x_1795_);
lean_dec_ref(v___x_1795_);
lean_dec(v___y_1767_);
v_isSharedCheck_1803_ = !lean_is_exclusive(v___x_1796_);
if (v_isSharedCheck_1803_ == 0)
{
lean_object* v_unused_1804_; 
v_unused_1804_ = lean_ctor_get(v___x_1796_, 0);
lean_dec(v_unused_1804_);
v___x_1798_ = v___x_1796_;
v_isShared_1799_ = v_isSharedCheck_1803_;
goto v_resetjp_1797_;
}
else
{
lean_dec(v___x_1796_);
v___x_1798_ = lean_box(0);
v_isShared_1799_ = v_isSharedCheck_1803_;
goto v_resetjp_1797_;
}
v_resetjp_1797_:
{
lean_object* v___x_1801_; 
if (v_isShared_1799_ == 0)
{
lean_ctor_set(v___x_1798_, 0, v_a_1790_);
v___x_1801_ = v___x_1798_;
goto v_reusejp_1800_;
}
else
{
lean_object* v_reuseFailAlloc_1802_; 
v_reuseFailAlloc_1802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1802_, 0, v_a_1790_);
v___x_1801_ = v_reuseFailAlloc_1802_;
goto v_reusejp_1800_;
}
v_reusejp_1800_:
{
return v___x_1801_;
}
}
}
}
}
else
{
lean_object* v_a_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1811_; uint8_t v_isShared_1812_; uint8_t v_isSharedCheck_1816_; 
v_a_1807_ = lean_ctor_get(v_r_1789_, 0);
lean_inc(v_a_1807_);
lean_dec_ref(v_r_1789_);
v___x_1808_ = lean_box(0);
v___x_1809_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___redArg___lam__0(v___y_1767_, v_isExporting_1771_, v___x_1785_, v___x_1808_);
lean_dec(v___y_1767_);
v_isSharedCheck_1816_ = !lean_is_exclusive(v___x_1809_);
if (v_isSharedCheck_1816_ == 0)
{
lean_object* v_unused_1817_; 
v_unused_1817_ = lean_ctor_get(v___x_1809_, 0);
lean_dec(v_unused_1817_);
v___x_1811_ = v___x_1809_;
v_isShared_1812_ = v_isSharedCheck_1816_;
goto v_resetjp_1810_;
}
else
{
lean_dec(v___x_1809_);
v___x_1811_ = lean_box(0);
v_isShared_1812_ = v_isSharedCheck_1816_;
goto v_resetjp_1810_;
}
v_resetjp_1810_:
{
lean_object* v___x_1814_; 
if (v_isShared_1812_ == 0)
{
lean_ctor_set_tag(v___x_1811_, 1);
lean_ctor_set(v___x_1811_, 0, v_a_1807_);
v___x_1814_ = v___x_1811_;
goto v_reusejp_1813_;
}
else
{
lean_object* v_reuseFailAlloc_1815_; 
v_reuseFailAlloc_1815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1815_, 0, v_a_1807_);
v___x_1814_ = v_reuseFailAlloc_1815_;
goto v_reusejp_1813_;
}
v_reusejp_1813_:
{
return v___x_1814_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___redArg___boxed(lean_object* v_x_1821_, lean_object* v_isExporting_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_){
_start:
{
uint8_t v_isExporting_boxed_1826_; lean_object* v_res_1827_; 
v_isExporting_boxed_1826_ = lean_unbox(v_isExporting_1822_);
v_res_1827_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___redArg(v_x_1821_, v_isExporting_boxed_1826_, v___y_1823_, v___y_1824_);
return v_res_1827_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3___redArg(lean_object* v_x_1828_, uint8_t v_when_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_){
_start:
{
if (v_when_1829_ == 0)
{
lean_object* v___x_1833_; 
v___x_1833_ = lean_apply_3(v_x_1828_, v___y_1830_, v___y_1831_, lean_box(0));
return v___x_1833_;
}
else
{
uint8_t v___x_1834_; lean_object* v___x_1835_; 
v___x_1834_ = 0;
v___x_1835_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___redArg(v_x_1828_, v___x_1834_, v___y_1830_, v___y_1831_);
return v___x_1835_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3___redArg___boxed(lean_object* v_x_1836_, lean_object* v_when_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_){
_start:
{
uint8_t v_when_boxed_1841_; lean_object* v_res_1842_; 
v_when_boxed_1841_ = lean_unbox(v_when_1837_);
v_res_1842_ = l_Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3___redArg(v_x_1836_, v_when_boxed_1841_, v___y_1838_, v___y_1839_);
return v_res_1842_;
}
}
static lean_object* _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___closed__2(void){
_start:
{
lean_object* v___x_1846_; lean_object* v___x_1847_; 
v___x_1846_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_validate___closed__1));
v___x_1847_ = l_Lean_MessageData_ofFormat(v___x_1846_);
return v___x_1847_;
}
}
static lean_object* _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___closed__3(void){
_start:
{
lean_object* v___x_1848_; lean_object* v_suffix_1849_; 
v___x_1848_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_validate___closed__2, &l___private_Lean_ReducibilityAttrs_0__Lean_validate___closed__2_once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___closed__2);
v_suffix_1849_ = l_Lean_MessageData_note(v___x_1848_);
return v_suffix_1849_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_validate(lean_object* v_declName_1850_, uint8_t v_status_1851_, uint8_t v_attrKind_1852_, lean_object* v_a_1853_, lean_object* v_a_1854_){
_start:
{
lean_object* v_suffix_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___f_1859_; uint8_t v___x_1860_; lean_object* v___x_1861_; 
v_suffix_1856_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_validate___closed__3, &l___private_Lean_ReducibilityAttrs_0__Lean_validate___closed__3_once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___closed__3);
v___x_1857_ = lean_box(v_status_1851_);
v___x_1858_ = lean_box(v_attrKind_1852_);
v___f_1859_ = lean_alloc_closure((void*)(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___boxed), 7, 4);
lean_closure_set(v___f_1859_, 0, v_declName_1850_);
lean_closure_set(v___f_1859_, 1, v___x_1857_);
lean_closure_set(v___f_1859_, 2, v_suffix_1856_);
lean_closure_set(v___f_1859_, 3, v___x_1858_);
v___x_1860_ = 1;
v___x_1861_ = l_Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3___redArg(v___f_1859_, v___x_1860_, v_a_1853_, v_a_1854_);
return v___x_1861_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_validate___boxed(lean_object* v_declName_1862_, lean_object* v_status_1863_, lean_object* v_attrKind_1864_, lean_object* v_a_1865_, lean_object* v_a_1866_, lean_object* v_a_1867_){
_start:
{
uint8_t v_status_boxed_1868_; uint8_t v_attrKind_boxed_1869_; lean_object* v_res_1870_; 
v_status_boxed_1868_ = lean_unbox(v_status_1863_);
v_attrKind_boxed_1869_ = lean_unbox(v_attrKind_1864_);
v_res_1870_ = l___private_Lean_ReducibilityAttrs_0__Lean_validate(v_declName_1862_, v_status_boxed_1868_, v_attrKind_boxed_1869_, v_a_1865_, v_a_1866_);
return v_res_1870_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1(lean_object* v_00_u03b1_1871_, lean_object* v_msg_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_){
_start:
{
lean_object* v___x_1876_; 
v___x_1876_ = l_Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1___redArg(v_msg_1872_, v___y_1873_, v___y_1874_);
return v___x_1876_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1___boxed(lean_object* v_00_u03b1_1877_, lean_object* v_msg_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_){
_start:
{
lean_object* v_res_1882_; 
v_res_1882_ = l_Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1(v_00_u03b1_1877_, v_msg_1878_, v___y_1879_, v___y_1880_);
lean_dec(v___y_1880_);
lean_dec_ref(v___y_1879_);
return v_res_1882_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5(lean_object* v_00_u03b1_1883_, lean_object* v_x_1884_, uint8_t v_isExporting_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_){
_start:
{
lean_object* v___x_1889_; 
v___x_1889_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___redArg(v_x_1884_, v_isExporting_1885_, v___y_1886_, v___y_1887_);
return v___x_1889_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___boxed(lean_object* v_00_u03b1_1890_, lean_object* v_x_1891_, lean_object* v_isExporting_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_){
_start:
{
uint8_t v_isExporting_boxed_1896_; lean_object* v_res_1897_; 
v_isExporting_boxed_1896_ = lean_unbox(v_isExporting_1892_);
v_res_1897_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5(v_00_u03b1_1890_, v_x_1891_, v_isExporting_boxed_1896_, v___y_1893_, v___y_1894_);
return v_res_1897_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3(lean_object* v_00_u03b1_1898_, lean_object* v_x_1899_, uint8_t v_when_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_){
_start:
{
lean_object* v___x_1904_; 
v___x_1904_ = l_Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3___redArg(v_x_1899_, v_when_1900_, v___y_1901_, v___y_1902_);
return v___x_1904_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3___boxed(lean_object* v_00_u03b1_1905_, lean_object* v_x_1906_, lean_object* v_when_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_){
_start:
{
uint8_t v_when_boxed_1911_; lean_object* v_res_1912_; 
v_when_boxed_1911_ = lean_unbox(v_when_1907_);
v_res_1912_ = l_Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3(v_00_u03b1_1905_, v_x_1906_, v_when_boxed_1911_, v___y_1908_, v___y_1909_);
return v_res_1912_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3(lean_object* v_00_u03b1_1913_, lean_object* v_constName_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_){
_start:
{
lean_object* v___x_1918_; 
v___x_1918_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3___redArg(v_constName_1914_, v___y_1915_, v___y_1916_);
return v___x_1918_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3___boxed(lean_object* v_00_u03b1_1919_, lean_object* v_constName_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_){
_start:
{
lean_object* v_res_1924_; 
v_res_1924_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3(v_00_u03b1_1919_, v_constName_1920_, v___y_1921_, v___y_1922_);
lean_dec(v___y_1922_);
return v_res_1924_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4(lean_object* v_00_u03b1_1925_, lean_object* v_ref_1926_, lean_object* v_constName_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_){
_start:
{
lean_object* v___x_1931_; 
v___x_1931_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg(v_ref_1926_, v_constName_1927_, v___y_1928_, v___y_1929_);
return v___x_1931_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___boxed(lean_object* v_00_u03b1_1932_, lean_object* v_ref_1933_, lean_object* v_constName_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_){
_start:
{
lean_object* v_res_1938_; 
v_res_1938_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4(v_00_u03b1_1932_, v_ref_1933_, v_constName_1934_, v___y_1935_, v___y_1936_);
lean_dec(v___y_1936_);
lean_dec(v_ref_1933_);
return v_res_1938_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7(lean_object* v_00_u03b1_1939_, lean_object* v_ref_1940_, lean_object* v_msg_1941_, lean_object* v_declHint_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_){
_start:
{
lean_object* v___x_1946_; 
v___x_1946_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7___redArg(v_ref_1940_, v_msg_1941_, v_declHint_1942_, v___y_1943_, v___y_1944_);
return v___x_1946_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7___boxed(lean_object* v_00_u03b1_1947_, lean_object* v_ref_1948_, lean_object* v_msg_1949_, lean_object* v_declHint_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_){
_start:
{
lean_object* v_res_1954_; 
v_res_1954_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7(v_00_u03b1_1947_, v_ref_1948_, v_msg_1949_, v_declHint_1950_, v___y_1951_, v___y_1952_);
lean_dec(v___y_1952_);
lean_dec(v_ref_1948_);
return v_res_1954_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9(lean_object* v_msg_1955_, lean_object* v_declHint_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_){
_start:
{
lean_object* v___x_1960_; 
v___x_1960_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg(v_msg_1955_, v_declHint_1956_, v___y_1958_);
return v___x_1960_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___boxed(lean_object* v_msg_1961_, lean_object* v_declHint_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_){
_start:
{
lean_object* v_res_1966_; 
v_res_1966_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9(v_msg_1961_, v_declHint_1962_, v___y_1963_, v___y_1964_);
lean_dec(v___y_1964_);
lean_dec_ref(v___y_1963_);
return v_res_1966_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__9(lean_object* v_00_u03b1_1967_, lean_object* v_ref_1968_, lean_object* v_msg_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_){
_start:
{
lean_object* v___x_1973_; 
v___x_1973_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__9___redArg(v_ref_1968_, v_msg_1969_, v___y_1970_, v___y_1971_);
return v___x_1973_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__9___boxed(lean_object* v_00_u03b1_1974_, lean_object* v_ref_1975_, lean_object* v_msg_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_){
_start:
{
lean_object* v_res_1980_; 
v_res_1980_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__9(v_00_u03b1_1974_, v_ref_1975_, v_msg_1976_, v___y_1977_, v___y_1978_);
lean_dec(v___y_1978_);
lean_dec(v_ref_1975_);
return v_res_1980_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_addAttr(uint8_t v_status_1981_, lean_object* v_declName_1982_, lean_object* v_stx_1983_, uint8_t v_attrKind_1984_, lean_object* v_a_1985_, lean_object* v_a_1986_){
_start:
{
lean_object* v___x_1988_; 
lean_inc_ref(v_a_1985_);
v___x_1988_ = l_Lean_Attribute_Builtin_ensureNoArgs(v_stx_1983_, v_a_1985_, v_a_1986_);
if (lean_obj_tag(v___x_1988_) == 0)
{
lean_object* v___x_1989_; 
lean_dec_ref(v___x_1988_);
lean_inc(v_a_1986_);
lean_inc_ref(v_a_1985_);
lean_inc(v_declName_1982_);
v___x_1989_ = l___private_Lean_ReducibilityAttrs_0__Lean_validate(v_declName_1982_, v_status_1981_, v_attrKind_1984_, v_a_1985_, v_a_1986_);
if (lean_obj_tag(v___x_1989_) == 0)
{
lean_object* v___x_1991_; uint8_t v_isShared_1992_; uint8_t v_isSharedCheck_2018_; 
v_isSharedCheck_2018_ = !lean_is_exclusive(v___x_1989_);
if (v_isSharedCheck_2018_ == 0)
{
lean_object* v_unused_2019_; 
v_unused_2019_ = lean_ctor_get(v___x_1989_, 0);
lean_dec(v_unused_2019_);
v___x_1991_ = v___x_1989_;
v_isShared_1992_ = v_isSharedCheck_2018_;
goto v_resetjp_1990_;
}
else
{
lean_dec(v___x_1989_);
v___x_1991_ = lean_box(0);
v_isShared_1992_ = v_isSharedCheck_2018_;
goto v_resetjp_1990_;
}
v_resetjp_1990_:
{
lean_object* v___x_1993_; lean_object* v_currNamespace_1994_; lean_object* v_env_1995_; lean_object* v_nextMacroScope_1996_; lean_object* v_ngen_1997_; lean_object* v_auxDeclNGen_1998_; lean_object* v_traceState_1999_; lean_object* v_messages_2000_; lean_object* v_infoState_2001_; lean_object* v_snapshotTasks_2002_; lean_object* v___x_2004_; uint8_t v_isShared_2005_; uint8_t v_isSharedCheck_2016_; 
v___x_1993_ = lean_st_ref_take(v_a_1986_);
v_currNamespace_1994_ = lean_ctor_get(v_a_1985_, 6);
lean_inc(v_currNamespace_1994_);
lean_dec_ref(v_a_1985_);
v_env_1995_ = lean_ctor_get(v___x_1993_, 0);
v_nextMacroScope_1996_ = lean_ctor_get(v___x_1993_, 1);
v_ngen_1997_ = lean_ctor_get(v___x_1993_, 2);
v_auxDeclNGen_1998_ = lean_ctor_get(v___x_1993_, 3);
v_traceState_1999_ = lean_ctor_get(v___x_1993_, 4);
v_messages_2000_ = lean_ctor_get(v___x_1993_, 6);
v_infoState_2001_ = lean_ctor_get(v___x_1993_, 7);
v_snapshotTasks_2002_ = lean_ctor_get(v___x_1993_, 8);
v_isSharedCheck_2016_ = !lean_is_exclusive(v___x_1993_);
if (v_isSharedCheck_2016_ == 0)
{
lean_object* v_unused_2017_; 
v_unused_2017_ = lean_ctor_get(v___x_1993_, 5);
lean_dec(v_unused_2017_);
v___x_2004_ = v___x_1993_;
v_isShared_2005_ = v_isSharedCheck_2016_;
goto v_resetjp_2003_;
}
else
{
lean_inc(v_snapshotTasks_2002_);
lean_inc(v_infoState_2001_);
lean_inc(v_messages_2000_);
lean_inc(v_traceState_1999_);
lean_inc(v_auxDeclNGen_1998_);
lean_inc(v_ngen_1997_);
lean_inc(v_nextMacroScope_1996_);
lean_inc(v_env_1995_);
lean_dec(v___x_1993_);
v___x_2004_ = lean_box(0);
v_isShared_2005_ = v_isSharedCheck_2016_;
goto v_resetjp_2003_;
}
v_resetjp_2003_:
{
lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2009_; 
v___x_2006_ = l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(v_env_1995_, v_declName_1982_, v_status_1981_, v_attrKind_1984_, v_currNamespace_1994_);
v___x_2007_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___redArg___closed__2, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___redArg___closed__2);
if (v_isShared_2005_ == 0)
{
lean_ctor_set(v___x_2004_, 5, v___x_2007_);
lean_ctor_set(v___x_2004_, 0, v___x_2006_);
v___x_2009_ = v___x_2004_;
goto v_reusejp_2008_;
}
else
{
lean_object* v_reuseFailAlloc_2015_; 
v_reuseFailAlloc_2015_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2015_, 0, v___x_2006_);
lean_ctor_set(v_reuseFailAlloc_2015_, 1, v_nextMacroScope_1996_);
lean_ctor_set(v_reuseFailAlloc_2015_, 2, v_ngen_1997_);
lean_ctor_set(v_reuseFailAlloc_2015_, 3, v_auxDeclNGen_1998_);
lean_ctor_set(v_reuseFailAlloc_2015_, 4, v_traceState_1999_);
lean_ctor_set(v_reuseFailAlloc_2015_, 5, v___x_2007_);
lean_ctor_set(v_reuseFailAlloc_2015_, 6, v_messages_2000_);
lean_ctor_set(v_reuseFailAlloc_2015_, 7, v_infoState_2001_);
lean_ctor_set(v_reuseFailAlloc_2015_, 8, v_snapshotTasks_2002_);
v___x_2009_ = v_reuseFailAlloc_2015_;
goto v_reusejp_2008_;
}
v_reusejp_2008_:
{
lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2013_; 
v___x_2010_ = lean_st_ref_set(v_a_1986_, v___x_2009_);
lean_dec(v_a_1986_);
v___x_2011_ = lean_box(0);
if (v_isShared_1992_ == 0)
{
lean_ctor_set(v___x_1991_, 0, v___x_2011_);
v___x_2013_ = v___x_1991_;
goto v_reusejp_2012_;
}
else
{
lean_object* v_reuseFailAlloc_2014_; 
v_reuseFailAlloc_2014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2014_, 0, v___x_2011_);
v___x_2013_ = v_reuseFailAlloc_2014_;
goto v_reusejp_2012_;
}
v_reusejp_2012_:
{
return v___x_2013_;
}
}
}
}
}
else
{
lean_dec(v_a_1986_);
lean_dec_ref(v_a_1985_);
lean_dec(v_declName_1982_);
return v___x_1989_;
}
}
else
{
lean_dec(v_a_1986_);
lean_dec_ref(v_a_1985_);
lean_dec(v_declName_1982_);
return v___x_1988_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_addAttr___boxed(lean_object* v_status_2020_, lean_object* v_declName_2021_, lean_object* v_stx_2022_, lean_object* v_attrKind_2023_, lean_object* v_a_2024_, lean_object* v_a_2025_, lean_object* v_a_2026_){
_start:
{
uint8_t v_status_boxed_2027_; uint8_t v_attrKind_boxed_2028_; lean_object* v_res_2029_; 
v_status_boxed_2027_ = lean_unbox(v_status_2020_);
v_attrKind_boxed_2028_ = lean_unbox(v_attrKind_2023_);
v_res_2029_ = l___private_Lean_ReducibilityAttrs_0__Lean_addAttr(v_status_boxed_2027_, v_declName_2021_, v_stx_2022_, v_attrKind_boxed_2028_, v_a_2024_, v_a_2025_);
return v_res_2029_;
}
}
static lean_object* _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2031_; lean_object* v___x_2032_; 
v___x_2031_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_));
v___x_2032_ = l_Lean_stringToMessageData(v___x_2031_);
return v___x_2032_;
}
}
static lean_object* _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__0___closed__3_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2034_; lean_object* v___x_2035_; 
v___x_2034_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__0___closed__2_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_));
v___x_2035_ = l_Lean_stringToMessageData(v___x_2034_);
return v___x_2035_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__0_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_(lean_object* v___x_2036_, lean_object* v_decl_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_){
_start:
{
lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; 
v___x_2041_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_, &l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_);
v___x_2042_ = l_Lean_MessageData_ofName(v___x_2036_);
v___x_2043_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2043_, 0, v___x_2041_);
lean_ctor_set(v___x_2043_, 1, v___x_2042_);
v___x_2044_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__0___closed__3_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_, &l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__0___closed__3_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__0___closed__3_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_);
v___x_2045_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2045_, 0, v___x_2043_);
lean_ctor_set(v___x_2045_, 1, v___x_2044_);
v___x_2046_ = l_Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1___redArg(v___x_2045_, v___y_2038_, v___y_2039_);
return v___x_2046_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__0_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2____boxed(lean_object* v___x_2047_, lean_object* v_decl_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_){
_start:
{
lean_object* v_res_2052_; 
v_res_2052_ = l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__0_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_(v___x_2047_, v_decl_2048_, v___y_2049_, v___y_2050_);
lean_dec(v___y_2050_);
lean_dec_ref(v___y_2049_);
lean_dec(v_decl_2048_);
return v_res_2052_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2117_; lean_object* v___x_2118_; 
v___x_2117_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__25_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_));
v___x_2118_ = l_Lean_registerBuiltinAttribute(v___x_2117_);
return v___x_2118_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2____boxed(lean_object* v_a_2119_){
_start:
{
lean_object* v_res_2120_; 
v_res_2120_ = l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_();
return v_res_2120_;
}
}
static lean_object* _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; 
v___x_2121_ = lean_unsigned_to_nat(4118757939u);
v___x_2122_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__12_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_));
v___x_2123_ = l_Lean_Name_num___override(v___x_2122_, v___x_2121_);
return v___x_2123_;
}
}
static lean_object* _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; 
v___x_2124_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__14_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_));
v___x_2125_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_, &l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2__once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_);
v___x_2126_ = l_Lean_Name_str___override(v___x_2125_, v___x_2124_);
return v___x_2126_;
}
}
static lean_object* _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; 
v___x_2127_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__16_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_));
v___x_2128_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_, &l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2__once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_);
v___x_2129_ = l_Lean_Name_str___override(v___x_2128_, v___x_2127_);
return v___x_2129_;
}
}
static lean_object* _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; 
v___x_2130_ = lean_unsigned_to_nat(2u);
v___x_2131_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_, &l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2__once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_);
v___x_2132_ = l_Lean_Name_num___override(v___x_2131_, v___x_2130_);
return v___x_2132_;
}
}
static lean_object* _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__8_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_(void){
_start:
{
uint8_t v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; 
v___x_2139_ = 0;
v___x_2140_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__7_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_));
v___x_2141_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_));
v___x_2142_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_, &l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2__once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_);
v___x_2143_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2143_, 0, v___x_2142_);
lean_ctor_set(v___x_2143_, 1, v___x_2141_);
lean_ctor_set(v___x_2143_, 2, v___x_2140_);
lean_ctor_set_uint8(v___x_2143_, sizeof(void*)*3, v___x_2139_);
return v___x_2143_;
}
}
static lean_object* _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__10_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; 
v___f_2147_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__6_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_));
v___x_2148_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__9_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_));
v___x_2149_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__8_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_, &l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__8_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2__once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__8_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_);
v___x_2150_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2150_, 0, v___x_2149_);
lean_ctor_set(v___x_2150_, 1, v___x_2148_);
lean_ctor_set(v___x_2150_, 2, v___f_2147_);
return v___x_2150_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2152_; lean_object* v___x_2153_; 
v___x_2152_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__10_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_, &l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__10_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2__once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__10_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_);
v___x_2153_ = l_Lean_registerBuiltinAttribute(v___x_2152_);
return v___x_2153_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2____boxed(lean_object* v_a_2154_){
_start:
{
lean_object* v_res_2155_; 
v_res_2155_ = l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_();
return v_res_2155_;
}
}
static lean_object* _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; 
v___x_2156_ = lean_unsigned_to_nat(2994861043u);
v___x_2157_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__12_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_));
v___x_2158_ = l_Lean_Name_num___override(v___x_2157_, v___x_2156_);
return v___x_2158_;
}
}
static lean_object* _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; 
v___x_2159_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__14_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_));
v___x_2160_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_, &l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2__once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_);
v___x_2161_ = l_Lean_Name_str___override(v___x_2160_, v___x_2159_);
return v___x_2161_;
}
}
static lean_object* _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; 
v___x_2162_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__16_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_));
v___x_2163_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_, &l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2__once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_);
v___x_2164_ = l_Lean_Name_str___override(v___x_2163_, v___x_2162_);
return v___x_2164_;
}
}
static lean_object* _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; 
v___x_2165_ = lean_unsigned_to_nat(2u);
v___x_2166_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_, &l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2__once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_);
v___x_2167_ = l_Lean_Name_num___override(v___x_2166_, v___x_2165_);
return v___x_2167_;
}
}
static lean_object* _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__8_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_(void){
_start:
{
uint8_t v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; 
v___x_2174_ = 0;
v___x_2175_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__7_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_));
v___x_2176_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_));
v___x_2177_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_, &l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2__once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_);
v___x_2178_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2178_, 0, v___x_2177_);
lean_ctor_set(v___x_2178_, 1, v___x_2176_);
lean_ctor_set(v___x_2178_, 2, v___x_2175_);
lean_ctor_set_uint8(v___x_2178_, sizeof(void*)*3, v___x_2174_);
return v___x_2178_;
}
}
static lean_object* _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__10_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; 
v___f_2182_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__6_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_));
v___x_2183_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__9_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_));
v___x_2184_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__8_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_, &l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__8_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2__once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__8_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_);
v___x_2185_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2185_, 0, v___x_2184_);
lean_ctor_set(v___x_2185_, 1, v___x_2183_);
lean_ctor_set(v___x_2185_, 2, v___f_2182_);
return v___x_2185_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2187_; lean_object* v___x_2188_; 
v___x_2187_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__10_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_, &l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__10_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2__once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__10_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_);
v___x_2188_ = l_Lean_registerBuiltinAttribute(v___x_2187_);
return v___x_2188_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2____boxed(lean_object* v_a_2189_){
_start:
{
lean_object* v_res_2190_; 
v_res_2190_ = l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_();
return v_res_2190_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2222_; lean_object* v___x_2223_; 
v___x_2222_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__10_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2_));
v___x_2223_ = l_Lean_registerBuiltinAttribute(v___x_2222_);
return v___x_2223_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2____boxed(lean_object* v_a_2224_){
_start:
{
lean_object* v_res_2225_; 
v_res_2225_ = l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2_();
return v_res_2225_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_598760241____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2254_; lean_object* v___x_2255_; 
v___x_2254_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__9_00___x40_Lean_ReducibilityAttrs_598760241____hygCtx___hyg_2_));
v___x_2255_ = l_Lean_registerBuiltinAttribute(v___x_2254_);
return v___x_2255_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_598760241____hygCtx___hyg_2____boxed(lean_object* v_a_2256_){
_start:
{
lean_object* v_res_2257_; 
v_res_2257_ = l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_598760241____hygCtx___hyg_2_();
return v_res_2257_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___redArg___lam__0(lean_object* v_declName_2258_, lean_object* v_toPure_2259_, lean_object* v_____do__lift_2260_){
_start:
{
uint8_t v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; 
v___x_2261_ = lean_get_reducibility_status(v_____do__lift_2260_, v_declName_2258_);
v___x_2262_ = lean_box(v___x_2261_);
v___x_2263_ = lean_apply_2(v_toPure_2259_, lean_box(0), v___x_2262_);
return v___x_2263_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___redArg(lean_object* v_inst_2264_, lean_object* v_inst_2265_, lean_object* v_declName_2266_){
_start:
{
lean_object* v_toApplicative_2267_; lean_object* v_toBind_2268_; lean_object* v_getEnv_2269_; lean_object* v_toPure_2270_; lean_object* v___f_2271_; lean_object* v___x_2272_; 
v_toApplicative_2267_ = lean_ctor_get(v_inst_2264_, 0);
lean_inc_ref(v_toApplicative_2267_);
v_toBind_2268_ = lean_ctor_get(v_inst_2264_, 1);
lean_inc(v_toBind_2268_);
lean_dec_ref(v_inst_2264_);
v_getEnv_2269_ = lean_ctor_get(v_inst_2265_, 0);
lean_inc(v_getEnv_2269_);
lean_dec_ref(v_inst_2265_);
v_toPure_2270_ = lean_ctor_get(v_toApplicative_2267_, 1);
lean_inc(v_toPure_2270_);
lean_dec_ref(v_toApplicative_2267_);
v___f_2271_ = lean_alloc_closure((void*)(l_Lean_getReducibilityStatus___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2271_, 0, v_declName_2266_);
lean_closure_set(v___f_2271_, 1, v_toPure_2270_);
v___x_2272_ = lean_apply_4(v_toBind_2268_, lean_box(0), lean_box(0), v_getEnv_2269_, v___f_2271_);
return v___x_2272_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus(lean_object* v_m_2273_, lean_object* v_inst_2274_, lean_object* v_inst_2275_, lean_object* v_declName_2276_){
_start:
{
lean_object* v___x_2277_; 
v___x_2277_ = l_Lean_getReducibilityStatus___redArg(v_inst_2274_, v_inst_2275_, v_declName_2276_);
return v___x_2277_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___redArg___lam__0(lean_object* v_declName_2278_, uint8_t v_s_2279_, lean_object* v_env_2280_){
_start:
{
uint8_t v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; 
v___x_2281_ = 0;
v___x_2282_ = lean_box(0);
v___x_2283_ = l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(v_env_2280_, v_declName_2278_, v_s_2279_, v___x_2281_, v___x_2282_);
return v___x_2283_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___redArg___lam__0___boxed(lean_object* v_declName_2284_, lean_object* v_s_2285_, lean_object* v_env_2286_){
_start:
{
uint8_t v_s_boxed_2287_; lean_object* v_res_2288_; 
v_s_boxed_2287_ = lean_unbox(v_s_2285_);
v_res_2288_ = l_Lean_setReducibilityStatus___redArg___lam__0(v_declName_2284_, v_s_boxed_2287_, v_env_2286_);
return v_res_2288_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___redArg(lean_object* v_inst_2289_, lean_object* v_declName_2290_, uint8_t v_s_2291_){
_start:
{
lean_object* v_modifyEnv_2292_; lean_object* v___x_2293_; lean_object* v___f_2294_; lean_object* v___x_2295_; 
v_modifyEnv_2292_ = lean_ctor_get(v_inst_2289_, 1);
lean_inc(v_modifyEnv_2292_);
lean_dec_ref(v_inst_2289_);
v___x_2293_ = lean_box(v_s_2291_);
v___f_2294_ = lean_alloc_closure((void*)(l_Lean_setReducibilityStatus___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2294_, 0, v_declName_2290_);
lean_closure_set(v___f_2294_, 1, v___x_2293_);
v___x_2295_ = lean_apply_1(v_modifyEnv_2292_, v___f_2294_);
return v___x_2295_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___redArg___boxed(lean_object* v_inst_2296_, lean_object* v_declName_2297_, lean_object* v_s_2298_){
_start:
{
uint8_t v_s_boxed_2299_; lean_object* v_res_2300_; 
v_s_boxed_2299_ = lean_unbox(v_s_2298_);
v_res_2300_ = l_Lean_setReducibilityStatus___redArg(v_inst_2296_, v_declName_2297_, v_s_boxed_2299_);
return v_res_2300_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus(lean_object* v_m_2301_, lean_object* v_inst_2302_, lean_object* v_declName_2303_, uint8_t v_s_2304_){
_start:
{
lean_object* v___x_2305_; 
v___x_2305_ = l_Lean_setReducibilityStatus___redArg(v_inst_2302_, v_declName_2303_, v_s_2304_);
return v___x_2305_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___boxed(lean_object* v_m_2306_, lean_object* v_inst_2307_, lean_object* v_declName_2308_, lean_object* v_s_2309_){
_start:
{
uint8_t v_s_boxed_2310_; lean_object* v_res_2311_; 
v_s_boxed_2310_ = lean_unbox(v_s_2309_);
v_res_2311_ = l_Lean_setReducibilityStatus(v_m_2306_, v_inst_2307_, v_declName_2308_, v_s_boxed_2310_);
return v_res_2311_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___redArg(lean_object* v_inst_2312_, lean_object* v_declName_2313_){
_start:
{
uint8_t v___x_2314_; lean_object* v___x_2315_; 
v___x_2314_ = 0;
v___x_2315_ = l_Lean_setReducibilityStatus___redArg(v_inst_2312_, v_declName_2313_, v___x_2314_);
return v___x_2315_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute(lean_object* v_m_2316_, lean_object* v_inst_2317_, lean_object* v_declName_2318_){
_start:
{
lean_object* v___x_2319_; 
v___x_2319_ = l_Lean_setReducibleAttribute___redArg(v_inst_2317_, v_declName_2318_);
return v___x_2319_;
}
}
LEAN_EXPORT lean_object* l_Lean_isReducible___redArg___lam__0(lean_object* v_toPure_2320_, uint8_t v_____do__lift_2321_){
_start:
{
if (v_____do__lift_2321_ == 0)
{
uint8_t v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; 
v___x_2322_ = 1;
v___x_2323_ = lean_box(v___x_2322_);
v___x_2324_ = lean_apply_2(v_toPure_2320_, lean_box(0), v___x_2323_);
return v___x_2324_;
}
else
{
uint8_t v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; 
v___x_2325_ = 0;
v___x_2326_ = lean_box(v___x_2325_);
v___x_2327_ = lean_apply_2(v_toPure_2320_, lean_box(0), v___x_2326_);
return v___x_2327_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isReducible___redArg___lam__0___boxed(lean_object* v_toPure_2328_, lean_object* v_____do__lift_2329_){
_start:
{
uint8_t v_____do__lift_47__boxed_2330_; lean_object* v_res_2331_; 
v_____do__lift_47__boxed_2330_ = lean_unbox(v_____do__lift_2329_);
v_res_2331_ = l_Lean_isReducible___redArg___lam__0(v_toPure_2328_, v_____do__lift_47__boxed_2330_);
return v_res_2331_;
}
}
LEAN_EXPORT lean_object* l_Lean_isReducible___redArg(lean_object* v_inst_2332_, lean_object* v_inst_2333_, lean_object* v_declName_2334_){
_start:
{
lean_object* v_toApplicative_2335_; lean_object* v_toBind_2336_; lean_object* v_toPure_2337_; lean_object* v___x_2338_; lean_object* v___f_2339_; lean_object* v___x_2340_; 
v_toApplicative_2335_ = lean_ctor_get(v_inst_2332_, 0);
v_toBind_2336_ = lean_ctor_get(v_inst_2332_, 1);
lean_inc(v_toBind_2336_);
v_toPure_2337_ = lean_ctor_get(v_toApplicative_2335_, 1);
lean_inc(v_toPure_2337_);
v___x_2338_ = l_Lean_getReducibilityStatus___redArg(v_inst_2332_, v_inst_2333_, v_declName_2334_);
v___f_2339_ = lean_alloc_closure((void*)(l_Lean_isReducible___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2339_, 0, v_toPure_2337_);
v___x_2340_ = lean_apply_4(v_toBind_2336_, lean_box(0), lean_box(0), v___x_2338_, v___f_2339_);
return v___x_2340_;
}
}
LEAN_EXPORT lean_object* l_Lean_isReducible(lean_object* v_m_2341_, lean_object* v_inst_2342_, lean_object* v_inst_2343_, lean_object* v_declName_2344_){
_start:
{
lean_object* v___x_2345_; 
v___x_2345_ = l_Lean_isReducible___redArg(v_inst_2342_, v_inst_2343_, v_declName_2344_);
return v___x_2345_;
}
}
LEAN_EXPORT lean_object* l_Lean_isIrreducible___redArg___lam__0(lean_object* v_toPure_2346_, uint8_t v_____do__lift_2347_){
_start:
{
if (v_____do__lift_2347_ == 2)
{
uint8_t v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; 
v___x_2348_ = 1;
v___x_2349_ = lean_box(v___x_2348_);
v___x_2350_ = lean_apply_2(v_toPure_2346_, lean_box(0), v___x_2349_);
return v___x_2350_;
}
else
{
uint8_t v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; 
v___x_2351_ = 0;
v___x_2352_ = lean_box(v___x_2351_);
v___x_2353_ = lean_apply_2(v_toPure_2346_, lean_box(0), v___x_2352_);
return v___x_2353_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isIrreducible___redArg___lam__0___boxed(lean_object* v_toPure_2354_, lean_object* v_____do__lift_2355_){
_start:
{
uint8_t v_____do__lift_47__boxed_2356_; lean_object* v_res_2357_; 
v_____do__lift_47__boxed_2356_ = lean_unbox(v_____do__lift_2355_);
v_res_2357_ = l_Lean_isIrreducible___redArg___lam__0(v_toPure_2354_, v_____do__lift_47__boxed_2356_);
return v_res_2357_;
}
}
LEAN_EXPORT lean_object* l_Lean_isIrreducible___redArg(lean_object* v_inst_2358_, lean_object* v_inst_2359_, lean_object* v_declName_2360_){
_start:
{
lean_object* v_toApplicative_2361_; lean_object* v_toBind_2362_; lean_object* v_toPure_2363_; lean_object* v___x_2364_; lean_object* v___f_2365_; lean_object* v___x_2366_; 
v_toApplicative_2361_ = lean_ctor_get(v_inst_2358_, 0);
v_toBind_2362_ = lean_ctor_get(v_inst_2358_, 1);
lean_inc(v_toBind_2362_);
v_toPure_2363_ = lean_ctor_get(v_toApplicative_2361_, 1);
lean_inc(v_toPure_2363_);
v___x_2364_ = l_Lean_getReducibilityStatus___redArg(v_inst_2358_, v_inst_2359_, v_declName_2360_);
v___f_2365_ = lean_alloc_closure((void*)(l_Lean_isIrreducible___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2365_, 0, v_toPure_2363_);
v___x_2366_ = lean_apply_4(v_toBind_2362_, lean_box(0), lean_box(0), v___x_2364_, v___f_2365_);
return v___x_2366_;
}
}
LEAN_EXPORT lean_object* l_Lean_isIrreducible(lean_object* v_m_2367_, lean_object* v_inst_2368_, lean_object* v_inst_2369_, lean_object* v_declName_2370_){
_start:
{
lean_object* v___x_2371_; 
v___x_2371_ = l_Lean_isIrreducible___redArg(v_inst_2368_, v_inst_2369_, v_declName_2370_);
return v___x_2371_;
}
}
LEAN_EXPORT uint8_t l_Lean_isImplicitReducibleCore(lean_object* v_env_2372_, lean_object* v_declName_2373_){
_start:
{
uint8_t v___x_2374_; 
v___x_2374_ = lean_get_reducibility_status(v_env_2372_, v_declName_2373_);
if (v___x_2374_ == 3)
{
uint8_t v___x_2375_; 
v___x_2375_ = 1;
return v___x_2375_;
}
else
{
uint8_t v___x_2376_; 
v___x_2376_ = 0;
return v___x_2376_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isImplicitReducibleCore___boxed(lean_object* v_env_2377_, lean_object* v_declName_2378_){
_start:
{
uint8_t v_res_2379_; lean_object* v_r_2380_; 
v_res_2379_ = l_Lean_isImplicitReducibleCore(v_env_2377_, v_declName_2378_);
v_r_2380_ = lean_box(v_res_2379_);
return v_r_2380_;
}
}
LEAN_EXPORT lean_object* l_Lean_isImplicitReducible___redArg___lam__0(lean_object* v_declName_2381_, lean_object* v_toPure_2382_, lean_object* v_____do__lift_2383_){
_start:
{
uint8_t v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; 
v___x_2384_ = l_Lean_isImplicitReducibleCore(v_____do__lift_2383_, v_declName_2381_);
v___x_2385_ = lean_box(v___x_2384_);
v___x_2386_ = lean_apply_2(v_toPure_2382_, lean_box(0), v___x_2385_);
return v___x_2386_;
}
}
LEAN_EXPORT lean_object* l_Lean_isImplicitReducible___redArg(lean_object* v_inst_2387_, lean_object* v_inst_2388_, lean_object* v_declName_2389_){
_start:
{
lean_object* v_toApplicative_2390_; lean_object* v_toBind_2391_; lean_object* v_getEnv_2392_; lean_object* v_toPure_2393_; lean_object* v___f_2394_; lean_object* v___x_2395_; 
v_toApplicative_2390_ = lean_ctor_get(v_inst_2387_, 0);
lean_inc_ref(v_toApplicative_2390_);
v_toBind_2391_ = lean_ctor_get(v_inst_2387_, 1);
lean_inc(v_toBind_2391_);
lean_dec_ref(v_inst_2387_);
v_getEnv_2392_ = lean_ctor_get(v_inst_2388_, 0);
lean_inc(v_getEnv_2392_);
lean_dec_ref(v_inst_2388_);
v_toPure_2393_ = lean_ctor_get(v_toApplicative_2390_, 1);
lean_inc(v_toPure_2393_);
lean_dec_ref(v_toApplicative_2390_);
v___f_2394_ = lean_alloc_closure((void*)(l_Lean_isImplicitReducible___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2394_, 0, v_declName_2389_);
lean_closure_set(v___f_2394_, 1, v_toPure_2393_);
v___x_2395_ = lean_apply_4(v_toBind_2391_, lean_box(0), lean_box(0), v_getEnv_2392_, v___f_2394_);
return v___x_2395_;
}
}
LEAN_EXPORT lean_object* l_Lean_isImplicitReducible(lean_object* v_m_2396_, lean_object* v_inst_2397_, lean_object* v_inst_2398_, lean_object* v_declName_2399_){
_start:
{
lean_object* v___x_2400_; 
v___x_2400_ = l_Lean_isImplicitReducible___redArg(v_inst_2397_, v_inst_2398_, v_declName_2399_);
return v___x_2400_;
}
}
LEAN_EXPORT uint8_t l_Lean_isInstanceReducibleCore(lean_object* v_env_2401_, lean_object* v_declName_2402_){
_start:
{
uint8_t v___x_2403_; 
v___x_2403_ = l_Lean_isImplicitReducibleCore(v_env_2401_, v_declName_2402_);
return v___x_2403_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInstanceReducibleCore___boxed(lean_object* v_env_2404_, lean_object* v_declName_2405_){
_start:
{
uint8_t v_res_2406_; lean_object* v_r_2407_; 
v_res_2406_ = l_Lean_isInstanceReducibleCore(v_env_2404_, v_declName_2405_);
v_r_2407_ = lean_box(v_res_2406_);
return v_r_2407_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInstanceReducible___redArg(lean_object* v_inst_2408_, lean_object* v_inst_2409_, lean_object* v_declName_2410_){
_start:
{
lean_object* v___x_2411_; 
v___x_2411_ = l_Lean_isImplicitReducible___redArg(v_inst_2408_, v_inst_2409_, v_declName_2410_);
return v___x_2411_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInstanceReducible(lean_object* v_m_2412_, lean_object* v_inst_2413_, lean_object* v_inst_2414_, lean_object* v_declName_2415_){
_start:
{
lean_object* v___x_2416_; 
v___x_2416_ = l_Lean_isImplicitReducible___redArg(v_inst_2413_, v_inst_2414_, v_declName_2415_);
return v___x_2416_;
}
}
LEAN_EXPORT lean_object* l_Lean_setIrreducibleAttribute___redArg(lean_object* v_inst_2417_, lean_object* v_declName_2418_){
_start:
{
uint8_t v___x_2419_; lean_object* v___x_2420_; 
v___x_2419_ = 2;
v___x_2420_ = l_Lean_setReducibilityStatus___redArg(v_inst_2417_, v_declName_2418_, v___x_2419_);
return v___x_2420_;
}
}
LEAN_EXPORT lean_object* l_Lean_setIrreducibleAttribute(lean_object* v_m_2421_, lean_object* v_inst_2422_, lean_object* v_declName_2423_){
_start:
{
lean_object* v___x_2424_; 
v___x_2424_ = l_Lean_setIrreducibleAttribute___redArg(v_inst_2422_, v_declName_2423_);
return v___x_2424_;
}
}
lean_object* runtime_initialize_Lean_ScopedEnvExtension(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_ReducibilityAttrs(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_ScopedEnvExtension(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_instInhabitedReducibilityStatus_default = _init_l_Lean_instInhabitedReducibilityStatus_default();
l_Lean_instInhabitedReducibilityStatus = _init_l_Lean_instInhabitedReducibilityStatus();
res = l_Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_reducibilityCoreExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_reducibilityCoreExt);
lean_dec_ref(res);
res = l_Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_reducibilityExtraExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_reducibilityExtraExt);
lean_dec_ref(res);
res = l_Lean_initFn_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4_();
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
res = l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_598760241____hygCtx___hyg_2_();
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
