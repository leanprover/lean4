// Lean compiler output
// Module: Lean.Level
// Imports: public import Init.Data.Array.QSort public import Lean.Data.PersistentHashSet public import Lean.Hygiene public import Init.Data.Option.Coe import Init.Data.Nat.Internal.Linear
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
lean_object* lean_string_length(lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint32_t lean_uint64_to_uint32(uint64_t);
uint64_t lean_uint32_to_uint64(uint32_t);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* l_Nat_reprFast(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint8_t lean_bool_not(uint8_t);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_replacePrefix(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkIdent(lean_object*);
lean_object* l_Lean_Syntax_mkNumLit(lean_object*, lean_object*);
lean_object* l_Array_mkArray0(lean_object*);
lean_object* lean_array_mk(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
lean_object* lean_uint32_to_nat(uint32_t);
uint64_t lean_uint64_land(uint64_t, uint64_t);
uint8_t lean_uint64_dec_eq(uint64_t, uint64_t);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_lt(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Name_reprPrec(lean_object*, lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_uint64_to_nat(uint64_t);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* l_Lean_Name_reprPrec___boxed(lean_object*, lean_object*);
lean_object* l_UInt64_decEq___boxed(lean_object*, lean_object*);
extern lean_object* l_Std_Format_defWidth;
lean_object* l_Std_Format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Nat_imax(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Nat_imax___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_instInhabitedData___aux__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lean_instInhabitedData___aux__1___closed__0;
LEAN_EXPORT uint64_t l_Lean_instInhabitedData___aux__1;
LEAN_EXPORT uint64_t l_Lean_instInhabitedData;
LEAN_EXPORT uint64_t l_Lean_Level_Data_hash(uint64_t);
LEAN_EXPORT lean_object* l_Lean_Level_Data_hash___boxed(lean_object*);
static const lean_closure_object l_Lean_instBEqData___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt64_decEq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instBEqData___closed__0 = (const lean_object*)&l_Lean_instBEqData___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instBEqData = (const lean_object*)&l_Lean_instBEqData___closed__0_value;
LEAN_EXPORT uint32_t l_Lean_Level_Data_depth(uint64_t);
LEAN_EXPORT lean_object* l_Lean_Level_Data_depth___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Level_Data_hasMVar(uint64_t);
LEAN_EXPORT lean_object* l_Lean_Level_Data_hasMVar___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Level_Data_hasParam(uint64_t);
LEAN_EXPORT lean_object* l_Lean_Level_Data_hasParam___boxed(lean_object*);
uint64_t lean_level_mk_data(uint64_t, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Level_mkData___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_instReprData___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_Lean_instReprData___lam__0___closed__0 = (const lean_object*)&l_Lean_instReprData___lam__0___closed__0_value;
static const lean_string_object l_Lean_instReprData___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = " (hasParam := "};
static const lean_object* l_Lean_instReprData___lam__0___closed__1 = (const lean_object*)&l_Lean_instReprData___lam__0___closed__1_value;
static const lean_string_object l_Lean_instReprData___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l_Lean_instReprData___lam__0___closed__2 = (const lean_object*)&l_Lean_instReprData___lam__0___closed__2_value;
static const lean_string_object l_Lean_instReprData___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l_Lean_instReprData___lam__0___closed__3 = (const lean_object*)&l_Lean_instReprData___lam__0___closed__3_value;
static const lean_string_object l_Lean_instReprData___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = " (hasMVar := "};
static const lean_object* l_Lean_instReprData___lam__0___closed__4 = (const lean_object*)&l_Lean_instReprData___lam__0___closed__4_value;
static const lean_string_object l_Lean_instReprData___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Level.mkData "};
static const lean_object* l_Lean_instReprData___lam__0___closed__5 = (const lean_object*)&l_Lean_instReprData___lam__0___closed__5_value;
static const lean_string_object l_Lean_instReprData___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = " (depth := "};
static const lean_object* l_Lean_instReprData___lam__0___closed__6 = (const lean_object*)&l_Lean_instReprData___lam__0___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_instReprData___lam__0(uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instReprData___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_instReprData___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instReprData___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instReprData___closed__0 = (const lean_object*)&l_Lean_instReprData___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instReprData = (const lean_object*)&l_Lean_instReprData___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_instInhabitedLevelMVarId_default;
LEAN_EXPORT lean_object* l_Lean_instInhabitedLevelMVarId;
LEAN_EXPORT uint8_t l_Lean_instBEqLevelMVarId_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instBEqLevelMVarId_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_instBEqLevelMVarId___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqLevelMVarId_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instBEqLevelMVarId___closed__0 = (const lean_object*)&l_Lean_instBEqLevelMVarId___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instBEqLevelMVarId = (const lean_object*)&l_Lean_instBEqLevelMVarId___closed__0_value;
static lean_once_cell_t l_Lean_instHashableLevelMVarId_hash___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lean_instHashableLevelMVarId_hash___closed__0;
static lean_once_cell_t l_Lean_instHashableLevelMVarId_hash___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lean_instHashableLevelMVarId_hash___closed__1;
LEAN_EXPORT uint64_t l_Lean_instHashableLevelMVarId_hash(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instHashableLevelMVarId_hash___boxed(lean_object*);
static const lean_closure_object l_Lean_instHashableLevelMVarId___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instHashableLevelMVarId_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instHashableLevelMVarId___closed__0 = (const lean_object*)&l_Lean_instHashableLevelMVarId___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instHashableLevelMVarId = (const lean_object*)&l_Lean_instHashableLevelMVarId___closed__0_value;
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_instReprLevelMVarId_repr_spec__0(lean_object*);
static const lean_string_object l_Lean_instReprLevelMVarId_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "{ "};
static const lean_object* l_Lean_instReprLevelMVarId_repr___redArg___closed__0 = (const lean_object*)&l_Lean_instReprLevelMVarId_repr___redArg___closed__0_value;
static const lean_string_object l_Lean_instReprLevelMVarId_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "name"};
static const lean_object* l_Lean_instReprLevelMVarId_repr___redArg___closed__1 = (const lean_object*)&l_Lean_instReprLevelMVarId_repr___redArg___closed__1_value;
static const lean_ctor_object l_Lean_instReprLevelMVarId_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprLevelMVarId_repr___redArg___closed__1_value)}};
static const lean_object* l_Lean_instReprLevelMVarId_repr___redArg___closed__2 = (const lean_object*)&l_Lean_instReprLevelMVarId_repr___redArg___closed__2_value;
static const lean_ctor_object l_Lean_instReprLevelMVarId_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instReprLevelMVarId_repr___redArg___closed__2_value)}};
static const lean_object* l_Lean_instReprLevelMVarId_repr___redArg___closed__3 = (const lean_object*)&l_Lean_instReprLevelMVarId_repr___redArg___closed__3_value;
static const lean_string_object l_Lean_instReprLevelMVarId_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l_Lean_instReprLevelMVarId_repr___redArg___closed__4 = (const lean_object*)&l_Lean_instReprLevelMVarId_repr___redArg___closed__4_value;
static const lean_ctor_object l_Lean_instReprLevelMVarId_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprLevelMVarId_repr___redArg___closed__4_value)}};
static const lean_object* l_Lean_instReprLevelMVarId_repr___redArg___closed__5 = (const lean_object*)&l_Lean_instReprLevelMVarId_repr___redArg___closed__5_value;
static const lean_ctor_object l_Lean_instReprLevelMVarId_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_instReprLevelMVarId_repr___redArg___closed__3_value),((lean_object*)&l_Lean_instReprLevelMVarId_repr___redArg___closed__5_value)}};
static const lean_object* l_Lean_instReprLevelMVarId_repr___redArg___closed__6 = (const lean_object*)&l_Lean_instReprLevelMVarId_repr___redArg___closed__6_value;
static lean_once_cell_t l_Lean_instReprLevelMVarId_repr___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instReprLevelMVarId_repr___redArg___closed__7;
static const lean_string_object l_Lean_instReprLevelMVarId_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " }"};
static const lean_object* l_Lean_instReprLevelMVarId_repr___redArg___closed__8 = (const lean_object*)&l_Lean_instReprLevelMVarId_repr___redArg___closed__8_value;
static lean_once_cell_t l_Lean_instReprLevelMVarId_repr___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instReprLevelMVarId_repr___redArg___closed__9;
static lean_once_cell_t l_Lean_instReprLevelMVarId_repr___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instReprLevelMVarId_repr___redArg___closed__10;
static const lean_ctor_object l_Lean_instReprLevelMVarId_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprLevelMVarId_repr___redArg___closed__0_value)}};
static const lean_object* l_Lean_instReprLevelMVarId_repr___redArg___closed__11 = (const lean_object*)&l_Lean_instReprLevelMVarId_repr___redArg___closed__11_value;
static const lean_ctor_object l_Lean_instReprLevelMVarId_repr___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprLevelMVarId_repr___redArg___closed__8_value)}};
static const lean_object* l_Lean_instReprLevelMVarId_repr___redArg___closed__12 = (const lean_object*)&l_Lean_instReprLevelMVarId_repr___redArg___closed__12_value;
LEAN_EXPORT lean_object* l_Lean_instReprLevelMVarId_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instReprLevelMVarId_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instReprLevelMVarId_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_instReprLevelMVarId___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instReprLevelMVarId_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instReprLevelMVarId___closed__0 = (const lean_object*)&l_Lean_instReprLevelMVarId___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instReprLevelMVarId = (const lean_object*)&l_Lean_instReprLevelMVarId___closed__0_value;
static const lean_closure_object l_Lean_instReprLMVarId___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_reprPrec___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instReprLMVarId___closed__0 = (const lean_object*)&l_Lean_instReprLMVarId___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instReprLMVarId = (const lean_object*)&l_Lean_instReprLMVarId___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_instInhabitedLMVarIdSet___aux__1;
LEAN_EXPORT lean_object* l_Lean_instInhabitedLMVarIdSet;
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionLMVarIdSet___aux__1;
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionLMVarIdSet;
LEAN_EXPORT lean_object* l_Lean_instForInLMVarIdSetLMVarIdOfMonad___aux__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instForInLMVarIdSetLMVarIdOfMonad___aux__1___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instForInLMVarIdSetLMVarIdOfMonad___aux__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instForInLMVarIdSetLMVarIdOfMonad___aux__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instForInLMVarIdSetLMVarIdOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instForInLMVarIdSetLMVarIdOfMonad(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionLMVarIdMap___aux__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionLMVarIdMap(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instForInLMVarIdMapProdLMVarIdOfMonad___aux__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instForInLMVarIdMapProdLMVarIdOfMonad___aux__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instForInLMVarIdMapProdLMVarIdOfMonad___aux__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instForInLMVarIdMapProdLMVarIdOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instForInLMVarIdMapProdLMVarIdOfMonad(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedLMVarIdMap(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_zero_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_zero_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_succ_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_succ_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_max_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_max_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_imax_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_imax_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_param_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_param_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_mvar_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_mvar_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_casesOn___override___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_casesOn___override___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_casesOn___override(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_casesOn___override___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_zero___override;
static lean_once_cell_t l_Lean_Level_data___override___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lean_Level_data___override___closed__0;
LEAN_EXPORT uint64_t l_Lean_Level_data___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_data___override___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_succ___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_max___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_imax___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_param___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_mvar___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedLevel_default;
LEAN_EXPORT lean_object* l_Lean_instInhabitedLevel;
static const lean_string_object l_Lean_instReprLevel_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "Lean.Level.zero"};
static const lean_object* l_Lean_instReprLevel_repr___closed__0 = (const lean_object*)&l_Lean_instReprLevel_repr___closed__0_value;
static const lean_ctor_object l_Lean_instReprLevel_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprLevel_repr___closed__0_value)}};
static const lean_object* l_Lean_instReprLevel_repr___closed__1 = (const lean_object*)&l_Lean_instReprLevel_repr___closed__1_value;
static lean_once_cell_t l_Lean_instReprLevel_repr___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instReprLevel_repr___closed__2;
static lean_once_cell_t l_Lean_instReprLevel_repr___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instReprLevel_repr___closed__3;
static const lean_string_object l_Lean_instReprLevel_repr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "Lean.Level.succ"};
static const lean_object* l_Lean_instReprLevel_repr___closed__4 = (const lean_object*)&l_Lean_instReprLevel_repr___closed__4_value;
static const lean_ctor_object l_Lean_instReprLevel_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprLevel_repr___closed__4_value)}};
static const lean_object* l_Lean_instReprLevel_repr___closed__5 = (const lean_object*)&l_Lean_instReprLevel_repr___closed__5_value;
static const lean_ctor_object l_Lean_instReprLevel_repr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_instReprLevel_repr___closed__5_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_instReprLevel_repr___closed__6 = (const lean_object*)&l_Lean_instReprLevel_repr___closed__6_value;
static const lean_string_object l_Lean_instReprLevel_repr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "Lean.Level.max"};
static const lean_object* l_Lean_instReprLevel_repr___closed__7 = (const lean_object*)&l_Lean_instReprLevel_repr___closed__7_value;
static const lean_ctor_object l_Lean_instReprLevel_repr___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprLevel_repr___closed__7_value)}};
static const lean_object* l_Lean_instReprLevel_repr___closed__8 = (const lean_object*)&l_Lean_instReprLevel_repr___closed__8_value;
static const lean_ctor_object l_Lean_instReprLevel_repr___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_instReprLevel_repr___closed__8_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_instReprLevel_repr___closed__9 = (const lean_object*)&l_Lean_instReprLevel_repr___closed__9_value;
static const lean_string_object l_Lean_instReprLevel_repr___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "Lean.Level.imax"};
static const lean_object* l_Lean_instReprLevel_repr___closed__10 = (const lean_object*)&l_Lean_instReprLevel_repr___closed__10_value;
static const lean_ctor_object l_Lean_instReprLevel_repr___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprLevel_repr___closed__10_value)}};
static const lean_object* l_Lean_instReprLevel_repr___closed__11 = (const lean_object*)&l_Lean_instReprLevel_repr___closed__11_value;
static const lean_ctor_object l_Lean_instReprLevel_repr___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_instReprLevel_repr___closed__11_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_instReprLevel_repr___closed__12 = (const lean_object*)&l_Lean_instReprLevel_repr___closed__12_value;
static const lean_string_object l_Lean_instReprLevel_repr___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "Lean.Level.param"};
static const lean_object* l_Lean_instReprLevel_repr___closed__13 = (const lean_object*)&l_Lean_instReprLevel_repr___closed__13_value;
static const lean_ctor_object l_Lean_instReprLevel_repr___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprLevel_repr___closed__13_value)}};
static const lean_object* l_Lean_instReprLevel_repr___closed__14 = (const lean_object*)&l_Lean_instReprLevel_repr___closed__14_value;
static const lean_ctor_object l_Lean_instReprLevel_repr___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_instReprLevel_repr___closed__14_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_instReprLevel_repr___closed__15 = (const lean_object*)&l_Lean_instReprLevel_repr___closed__15_value;
static const lean_string_object l_Lean_instReprLevel_repr___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "Lean.Level.mvar"};
static const lean_object* l_Lean_instReprLevel_repr___closed__16 = (const lean_object*)&l_Lean_instReprLevel_repr___closed__16_value;
static const lean_ctor_object l_Lean_instReprLevel_repr___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprLevel_repr___closed__16_value)}};
static const lean_object* l_Lean_instReprLevel_repr___closed__17 = (const lean_object*)&l_Lean_instReprLevel_repr___closed__17_value;
static const lean_ctor_object l_Lean_instReprLevel_repr___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_instReprLevel_repr___closed__17_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_instReprLevel_repr___closed__18 = (const lean_object*)&l_Lean_instReprLevel_repr___closed__18_value;
LEAN_EXPORT lean_object* l_Lean_instReprLevel_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instReprLevel_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_instReprLevel___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instReprLevel_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instReprLevel___closed__0 = (const lean_object*)&l_Lean_instReprLevel___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instReprLevel = (const lean_object*)&l_Lean_instReprLevel___closed__0_value;
LEAN_EXPORT uint64_t l_Lean_Level_hash(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_hash___boxed(lean_object*);
static const lean_closure_object l_Lean_Level_instHashable___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Level_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Level_instHashable___closed__0 = (const lean_object*)&l_Lean_Level_instHashable___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Level_instHashable = (const lean_object*)&l_Lean_Level_instHashable___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Level_depth(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_depth___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Level_hasMVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_hasMVar___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Level_hasParam(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_hasParam___boxed(lean_object*);
LEAN_EXPORT uint32_t lean_level_hash(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_hashEx___boxed(lean_object*);
LEAN_EXPORT uint8_t lean_level_has_mvar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_hasMVarEx___boxed(lean_object*);
LEAN_EXPORT uint8_t lean_level_has_param(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_hasParamEx___boxed(lean_object*);
LEAN_EXPORT uint32_t lean_level_depth(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_depthEx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_levelZero;
LEAN_EXPORT lean_object* l_Lean_mkLevelMVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkLevelParam(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkLevelSucc(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkLevelMax(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkLevelIMax(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Level_one___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Level_one___closed__0;
LEAN_EXPORT lean_object* l_Lean_Level_one;
LEAN_EXPORT lean_object* l_Lean_levelOne;
LEAN_EXPORT lean_object* lean_level_mk_zero(lean_object*);
LEAN_EXPORT lean_object* lean_level_mk_succ(lean_object*);
LEAN_EXPORT lean_object* lean_level_mk_mvar(lean_object*);
LEAN_EXPORT lean_object* lean_level_mk_param(lean_object*);
LEAN_EXPORT lean_object* lean_level_mk_max(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_level_mk_imax(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Level_isZero(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_isZero___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Level_isSucc(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_isSucc___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Level_isMax(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_isMax___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Level_isIMax(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_isIMax___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Level_isMaxIMax(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_isMaxIMax___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Level_isParam(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_isParam___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Level_isMVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_isMVar___boxed(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Level_mvarId_x21_spec__0(lean_object*);
static const lean_string_object l_Lean_Level_mvarId_x21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "Lean.Level"};
static const lean_object* l_Lean_Level_mvarId_x21___closed__0 = (const lean_object*)&l_Lean_Level_mvarId_x21___closed__0_value;
static const lean_string_object l_Lean_Level_mvarId_x21___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Lean.Level.mvarId!"};
static const lean_object* l_Lean_Level_mvarId_x21___closed__1 = (const lean_object*)&l_Lean_Level_mvarId_x21___closed__1_value;
static const lean_string_object l_Lean_Level_mvarId_x21___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "metavariable expected"};
static const lean_object* l_Lean_Level_mvarId_x21___closed__2 = (const lean_object*)&l_Lean_Level_mvarId_x21___closed__2_value;
static lean_once_cell_t l_Lean_Level_mvarId_x21___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Level_mvarId_x21___closed__3;
LEAN_EXPORT lean_object* l_Lean_Level_mvarId_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_mvarId_x21___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Level_isNeverZero(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_isNeverZero___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Level_isAlwaysZero(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_isAlwaysZero___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_ofNat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_ofNat___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_instOfNat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_instOfNat___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_addOffsetAux(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_addOffset(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Level_isExplicit(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_isExplicit___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_getOffsetAux(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_getOffsetAux___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_getOffset(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_getOffset___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_getLevelOffset(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_getLevelOffset___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_toNat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_toNat___boxed(lean_object*);
uint8_t lean_level_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Level_instBEq___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Level_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Level_instBEq___closed__0 = (const lean_object*)&l_Lean_Level_instBEq___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Level_instBEq = (const lean_object*)&l_Lean_Level_instBEq___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Level_occurs(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_occurs___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_ctorToNat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_ctorToNat___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Level_normLtAux(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_normLtAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_normLtAux_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_normLtAux_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Level_normLt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_normLt___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Level_isAlreadyNormalizedCheap(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_isAlreadyNormalizedCheap___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_mkIMaxAux(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_getMaxArgsAux(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_getMaxArgsAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_accMax(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_mkMaxAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_mkMaxAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_skipExplicit(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_skipExplicit___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Level_0__Lean_Level_isExplicitSubsumedAux(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_isExplicitSubsumedAux___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Level_0__Lean_Level_isExplicitSubsumed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_isExplicitSubsumed___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Level_normalize_spec__2(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Level_normalize___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Level_normalize___closed__0 = (const lean_object*)&l_Lean_Level_normalize___closed__0_value;
static const lean_string_object l_Lean_Level_normalize___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_Lean_Level_normalize___closed__2 = (const lean_object*)&l_Lean_Level_normalize___closed__2_value;
static const lean_string_object l_Lean_Level_normalize___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Lean.Level.normalize"};
static const lean_object* l_Lean_Level_normalize___closed__1 = (const lean_object*)&l_Lean_Level_normalize___closed__1_value;
static lean_once_cell_t l_Lean_Level_normalize___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Level_normalize___closed__3;
LEAN_EXPORT lean_object* l_Lean_Level_normalize(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_getMaxArgsAux___at___00Lean_Level_normalize_spec__0(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_getMaxArgsAux___at___00Lean_Level_normalize_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_normalize___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Level_isEquiv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_isEquiv___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_dec(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_dec___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_leaf_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_leaf_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_num_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_num_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_offset_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_offset_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_maxNode_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_maxNode_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_imaxNode_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_imaxNode_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_succ(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_max(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_imax(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Level_PP_toResult___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Level_PP_toResult___closed__0 = (const lean_object*)&l_Lean_Level_PP_toResult___closed__0_value;
static const lean_string_object l_Lean_Level_PP_toResult___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "\?u"};
static const lean_object* l_Lean_Level_PP_toResult___closed__1 = (const lean_object*)&l_Lean_Level_PP_toResult___closed__1_value;
static const lean_ctor_object l_Lean_Level_PP_toResult___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Level_PP_toResult___closed__1_value),LEAN_SCALAR_PTR_LITERAL(228, 117, 157, 98, 226, 186, 76, 191)}};
static const lean_object* l_Lean_Level_PP_toResult___closed__2 = (const lean_object*)&l_Lean_Level_PP_toResult___closed__2_value;
static const lean_string_object l_Lean_Level_PP_toResult___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "_uniq"};
static const lean_object* l_Lean_Level_PP_toResult___closed__3 = (const lean_object*)&l_Lean_Level_PP_toResult___closed__3_value;
static const lean_ctor_object l_Lean_Level_PP_toResult___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Level_PP_toResult___closed__3_value),LEAN_SCALAR_PTR_LITERAL(237, 141, 162, 170, 202, 74, 55, 55)}};
static const lean_object* l_Lean_Level_PP_toResult___closed__4 = (const lean_object*)&l_Lean_Level_PP_toResult___closed__4_value;
static const lean_string_object l_Lean_Level_PP_toResult___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "\?_mvar"};
static const lean_object* l_Lean_Level_PP_toResult___closed__5 = (const lean_object*)&l_Lean_Level_PP_toResult___closed__5_value;
static const lean_ctor_object l_Lean_Level_PP_toResult___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Level_PP_toResult___closed__5_value),LEAN_SCALAR_PTR_LITERAL(49, 72, 57, 220, 81, 200, 89, 8)}};
static const lean_object* l_Lean_Level_PP_toResult___closed__6 = (const lean_object*)&l_Lean_Level_PP_toResult___closed__6_value;
static const lean_string_object l_Lean_Level_PP_toResult___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "_"};
static const lean_object* l_Lean_Level_PP_toResult___closed__7 = (const lean_object*)&l_Lean_Level_PP_toResult___closed__7_value;
static const lean_ctor_object l_Lean_Level_PP_toResult___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Level_PP_toResult___closed__7_value),LEAN_SCALAR_PTR_LITERAL(168, 60, 211, 188, 58, 220, 100, 184)}};
static const lean_object* l_Lean_Level_PP_toResult___closed__8 = (const lean_object*)&l_Lean_Level_PP_toResult___closed__8_value;
static const lean_ctor_object l_Lean_Level_PP_toResult___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Level_PP_toResult___closed__8_value)}};
static const lean_object* l_Lean_Level_PP_toResult___closed__9 = (const lean_object*)&l_Lean_Level_PP_toResult___closed__9_value;
LEAN_EXPORT lean_object* l_Lean_Level_PP_toResult(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_PP_toResult___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__0 = (const lean_object*)&l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__0_value;
static lean_once_cell_t l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__1;
static lean_once_cell_t l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__2;
static const lean_ctor_object l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__0_value)}};
static const lean_object* l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__3 = (const lean_object*)&l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__3_value;
static const lean_ctor_object l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprData___lam__0___closed__0_value)}};
static const lean_object* l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__4 = (const lean_object*)&l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__4_value;
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Level_PP_Result_format___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " + "};
static const lean_object* l_Lean_Level_PP_Result_format___closed__0 = (const lean_object*)&l_Lean_Level_PP_Result_format___closed__0_value;
static const lean_ctor_object l_Lean_Level_PP_Result_format___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Level_PP_Result_format___closed__0_value)}};
static const lean_object* l_Lean_Level_PP_Result_format___closed__1 = (const lean_object*)&l_Lean_Level_PP_Result_format___closed__1_value;
static const lean_string_object l_Lean_Level_PP_Result_format___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "max"};
static const lean_object* l_Lean_Level_PP_Result_format___closed__2 = (const lean_object*)&l_Lean_Level_PP_Result_format___closed__2_value;
static const lean_ctor_object l_Lean_Level_PP_Result_format___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Level_PP_Result_format___closed__2_value)}};
static const lean_object* l_Lean_Level_PP_Result_format___closed__3 = (const lean_object*)&l_Lean_Level_PP_Result_format___closed__3_value;
static const lean_string_object l_Lean_Level_PP_Result_format___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "imax"};
static const lean_object* l_Lean_Level_PP_Result_format___closed__4 = (const lean_object*)&l_Lean_Level_PP_Result_format___closed__4_value;
static const lean_ctor_object l_Lean_Level_PP_Result_format___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Level_PP_Result_format___closed__4_value)}};
static const lean_object* l_Lean_Level_PP_Result_format___closed__5 = (const lean_object*)&l_Lean_Level_PP_Result_format___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_format(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_PP_Result_formatLst(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_format___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Level_PP_Result_quote___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Level_PP_Result_quote___closed__0;
static const lean_string_object l_Lean_Level_PP_Result_quote___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "paren"};
static const lean_object* l_Lean_Level_PP_Result_quote___closed__4 = (const lean_object*)&l_Lean_Level_PP_Result_quote___closed__4_value;
static const lean_string_object l_Lean_Level_PP_Result_quote___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Level"};
static const lean_object* l_Lean_Level_PP_Result_quote___closed__3 = (const lean_object*)&l_Lean_Level_PP_Result_quote___closed__3_value;
static const lean_string_object l_Lean_Level_PP_Result_quote___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Level_PP_Result_quote___closed__2 = (const lean_object*)&l_Lean_Level_PP_Result_quote___closed__2_value;
static const lean_string_object l_Lean_Level_PP_Result_quote___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Level_PP_Result_quote___closed__1 = (const lean_object*)&l_Lean_Level_PP_Result_quote___closed__1_value;
static const lean_ctor_object l_Lean_Level_PP_Result_quote___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Level_PP_Result_quote___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Level_PP_Result_quote___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Level_PP_Result_quote___closed__5_value_aux_0),((lean_object*)&l_Lean_Level_PP_Result_quote___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Level_PP_Result_quote___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Level_PP_Result_quote___closed__5_value_aux_1),((lean_object*)&l_Lean_Level_PP_Result_quote___closed__3_value),LEAN_SCALAR_PTR_LITERAL(176, 210, 143, 23, 235, 250, 136, 158)}};
static const lean_ctor_object l_Lean_Level_PP_Result_quote___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Level_PP_Result_quote___closed__5_value_aux_2),((lean_object*)&l_Lean_Level_PP_Result_quote___closed__4_value),LEAN_SCALAR_PTR_LITERAL(67, 200, 57, 231, 14, 244, 115, 229)}};
static const lean_object* l_Lean_Level_PP_Result_quote___closed__5 = (const lean_object*)&l_Lean_Level_PP_Result_quote___closed__5_value;
static lean_once_cell_t l_Lean_Level_PP_Result_quote___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Level_PP_Result_quote___closed__6;
static lean_once_cell_t l_Lean_Level_PP_Result_quote___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Level_PP_Result_quote___closed__7;
static const lean_string_object l_Lean_Level_PP_Result_quote___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "addLit"};
static const lean_object* l_Lean_Level_PP_Result_quote___closed__8 = (const lean_object*)&l_Lean_Level_PP_Result_quote___closed__8_value;
static const lean_ctor_object l_Lean_Level_PP_Result_quote___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Level_PP_Result_quote___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Level_PP_Result_quote___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Level_PP_Result_quote___closed__9_value_aux_0),((lean_object*)&l_Lean_Level_PP_Result_quote___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Level_PP_Result_quote___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Level_PP_Result_quote___closed__9_value_aux_1),((lean_object*)&l_Lean_Level_PP_Result_quote___closed__3_value),LEAN_SCALAR_PTR_LITERAL(176, 210, 143, 23, 235, 250, 136, 158)}};
static const lean_ctor_object l_Lean_Level_PP_Result_quote___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Level_PP_Result_quote___closed__9_value_aux_2),((lean_object*)&l_Lean_Level_PP_Result_quote___closed__8_value),LEAN_SCALAR_PTR_LITERAL(53, 243, 225, 2, 30, 243, 80, 174)}};
static const lean_object* l_Lean_Level_PP_Result_quote___closed__9 = (const lean_object*)&l_Lean_Level_PP_Result_quote___closed__9_value;
static const lean_string_object l_Lean_Level_PP_Result_quote___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "+"};
static const lean_object* l_Lean_Level_PP_Result_quote___closed__10 = (const lean_object*)&l_Lean_Level_PP_Result_quote___closed__10_value;
static const lean_ctor_object l_Lean_Level_PP_Result_quote___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Level_PP_Result_quote___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Level_PP_Result_quote___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Level_PP_Result_quote___closed__11_value_aux_0),((lean_object*)&l_Lean_Level_PP_Result_quote___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Level_PP_Result_quote___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Level_PP_Result_quote___closed__11_value_aux_1),((lean_object*)&l_Lean_Level_PP_Result_quote___closed__3_value),LEAN_SCALAR_PTR_LITERAL(176, 210, 143, 23, 235, 250, 136, 158)}};
static const lean_ctor_object l_Lean_Level_PP_Result_quote___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Level_PP_Result_quote___closed__11_value_aux_2),((lean_object*)&l_Lean_Level_PP_Result_format___closed__2_value),LEAN_SCALAR_PTR_LITERAL(106, 181, 1, 145, 170, 142, 100, 97)}};
static const lean_object* l_Lean_Level_PP_Result_quote___closed__11 = (const lean_object*)&l_Lean_Level_PP_Result_quote___closed__11_value;
static lean_once_cell_t l_Lean_Level_PP_Result_quote___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Level_PP_Result_quote___closed__12;
static const lean_string_object l_Lean_Level_PP_Result_quote___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_Level_PP_Result_quote___closed__13 = (const lean_object*)&l_Lean_Level_PP_Result_quote___closed__13_value;
static const lean_ctor_object l_Lean_Level_PP_Result_quote___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Level_PP_Result_quote___closed__13_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean_Level_PP_Result_quote___closed__14 = (const lean_object*)&l_Lean_Level_PP_Result_quote___closed__14_value;
static lean_once_cell_t l_Lean_Level_PP_Result_quote___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Level_PP_Result_quote___closed__15;
static const lean_ctor_object l_Lean_Level_PP_Result_quote___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Level_PP_Result_quote___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Level_PP_Result_quote___closed__16_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Level_PP_Result_quote___closed__16_value_aux_0),((lean_object*)&l_Lean_Level_PP_Result_quote___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Level_PP_Result_quote___closed__16_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Level_PP_Result_quote___closed__16_value_aux_1),((lean_object*)&l_Lean_Level_PP_Result_quote___closed__3_value),LEAN_SCALAR_PTR_LITERAL(176, 210, 143, 23, 235, 250, 136, 158)}};
static const lean_ctor_object l_Lean_Level_PP_Result_quote___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Level_PP_Result_quote___closed__16_value_aux_2),((lean_object*)&l_Lean_Level_PP_Result_format___closed__4_value),LEAN_SCALAR_PTR_LITERAL(124, 169, 176, 27, 219, 169, 119, 28)}};
static const lean_object* l_Lean_Level_PP_Result_quote___closed__16 = (const lean_object*)&l_Lean_Level_PP_Result_quote___closed__16_value;
static lean_once_cell_t l_Lean_Level_PP_Result_quote___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Level_PP_Result_quote___closed__17;
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_quote(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Level_PP_Result_quote_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Level_PP_Result_quote_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_quote___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_format(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_format___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_instToFormat___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_instToFormat___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_instToFormat___lam__1(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Level_instToFormat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Level_instToFormat___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Level_instToFormat___closed__0 = (const lean_object*)&l_Lean_Level_instToFormat___closed__0_value;
static const lean_closure_object l_Lean_Level_instToFormat___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Level_instToFormat___lam__1, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Level_instToFormat___closed__0_value)} };
static const lean_object* l_Lean_Level_instToFormat___closed__1 = (const lean_object*)&l_Lean_Level_instToFormat___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Level_instToFormat = (const lean_object*)&l_Lean_Level_instToFormat___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Level_instToString___lam__1(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Level_instToString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Level_instToString___lam__1, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Level_instToFormat___closed__0_value)} };
static const lean_object* l_Lean_Level_instToString___closed__0 = (const lean_object*)&l_Lean_Level_instToString___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Level_instToString = (const lean_object*)&l_Lean_Level_instToString___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Level_quote(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_quote___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_instQuoteMkStr1___lam__1(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Level_instQuoteMkStr1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Level_instQuoteMkStr1___lam__1, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Level_instToFormat___closed__0_value)} };
static const lean_object* l_Lean_Level_instQuoteMkStr1___closed__0 = (const lean_object*)&l_Lean_Level_instQuoteMkStr1___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Level_instQuoteMkStr1 = (const lean_object*)&l_Lean_Level_instQuoteMkStr1___closed__0_value;
LEAN_EXPORT uint8_t l___private_Lean_Level_0__Lean_mkLevelMaxCore___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_mkLevelMaxCore___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_mkLevelMaxCore(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_mkLevelMaxCore___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkLevelMax_x27(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_simpLevelMax_x27(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_simpLevelMax_x27___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_mkLevelIMaxCore(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkLevelIMax_x27(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_simpLevelIMax_x27(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_simpLevelIMax_x27___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 49, .m_capacity = 49, .m_length = 48, .m_data = "_private.Lean.Level.0.Lean.Level.updateSucc!Impl"};
static const lean_object* l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl___closed__0 = (const lean_object*)&l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl___closed__0_value;
static const lean_string_object l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "succ level expected"};
static const lean_object* l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl___closed__1 = (const lean_object*)&l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl___closed__1_value;
static lean_once_cell_t l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 48, .m_capacity = 48, .m_length = 47, .m_data = "_private.Lean.Level.0.Lean.Level.updateMax!Impl"};
static const lean_object* l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl___closed__0 = (const lean_object*)&l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl___closed__0_value;
static const lean_string_object l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "max level expected"};
static const lean_object* l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl___closed__1 = (const lean_object*)&l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl___closed__1_value;
static lean_once_cell_t l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 49, .m_capacity = 49, .m_length = 48, .m_data = "_private.Lean.Level.0.Lean.Level.updateIMax!Impl"};
static const lean_object* l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl___closed__0 = (const lean_object*)&l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl___closed__0_value;
static const lean_string_object l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "imax level expected"};
static const lean_object* l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl___closed__1 = (const lean_object*)&l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl___closed__1_value;
static lean_once_cell_t l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_mkNaryMax(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_substParams_go(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_substParams(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_getParamSubst(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_getParamSubst___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_instantiateParams(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Level_0__Lean_Level_geq_go(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_geq_go___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_geq_go_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_geq_go_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_isIMax_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_isIMax_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Level_geq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_geq___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Level_collectMVars_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Level_collectMVars_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Level_collectMVars_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_collectMVars(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Level_collectMVars_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Level_collectMVars_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Level_collectMVars_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_find_x3f_visit(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_find_x3f(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Level_any(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_any___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Nat_toLevel(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Nat_toLevel___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Nat_imax(lean_object* v_n_1_, lean_object* v_m_2_){
_start:
{
lean_object* v___x_3_; uint8_t v___x_4_; 
v___x_3_ = lean_unsigned_to_nat(0u);
v___x_4_ = lean_nat_dec_eq(v_m_2_, v___x_3_);
if (v___x_4_ == 0)
{
uint8_t v___x_5_; 
v___x_5_ = lean_nat_dec_le(v_n_1_, v_m_2_);
if (v___x_5_ == 0)
{
lean_inc(v_n_1_);
return v_n_1_;
}
else
{
lean_inc(v_m_2_);
return v_m_2_;
}
}
else
{
return v___x_3_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Nat_imax___boxed(lean_object* v_n_6_, lean_object* v_m_7_){
_start:
{
lean_object* v_res_8_; 
v_res_8_ = l_Lean_Nat_imax(v_n_6_, v_m_7_);
lean_dec(v_m_7_);
lean_dec(v_n_6_);
return v_res_8_;
}
}
static uint64_t _init_l_Lean_instInhabitedData___aux__1___closed__0(void){
_start:
{
lean_object* v___x_9_; uint64_t v___x_10_; 
v___x_9_ = lean_unsigned_to_nat(0u);
v___x_10_ = lean_uint64_of_nat(v___x_9_);
return v___x_10_;
}
}
static uint64_t _init_l_Lean_instInhabitedData___aux__1(void){
_start:
{
uint64_t v___x_11_; 
v___x_11_ = lean_uint64_once(&l_Lean_instInhabitedData___aux__1___closed__0, &l_Lean_instInhabitedData___aux__1___closed__0_once, _init_l_Lean_instInhabitedData___aux__1___closed__0);
return v___x_11_;
}
}
static uint64_t _init_l_Lean_instInhabitedData(void){
_start:
{
uint64_t v___x_12_; 
v___x_12_ = lean_uint64_once(&l_Lean_instInhabitedData___aux__1___closed__0, &l_Lean_instInhabitedData___aux__1___closed__0_once, _init_l_Lean_instInhabitedData___aux__1___closed__0);
return v___x_12_;
}
}
LEAN_EXPORT uint64_t l_Lean_Level_Data_hash(uint64_t v_c_13_){
_start:
{
uint32_t v___x_14_; uint64_t v___x_15_; 
v___x_14_ = lean_uint64_to_uint32(v_c_13_);
v___x_15_ = lean_uint32_to_uint64(v___x_14_);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_Data_hash___boxed(lean_object* v_c_16_){
_start:
{
uint64_t v_c_boxed_17_; uint64_t v_res_18_; lean_object* v_r_19_; 
v_c_boxed_17_ = lean_unbox_uint64(v_c_16_);
lean_dec_ref(v_c_16_);
v_res_18_ = l_Lean_Level_Data_hash(v_c_boxed_17_);
v_r_19_ = lean_box_uint64(v_res_18_);
return v_r_19_;
}
}
LEAN_EXPORT uint32_t l_Lean_Level_Data_depth(uint64_t v_c_22_){
_start:
{
uint64_t v___x_23_; uint64_t v___x_24_; uint32_t v___x_25_; 
v___x_23_ = 40ULL;
v___x_24_ = lean_uint64_shift_right(v_c_22_, v___x_23_);
v___x_25_ = lean_uint64_to_uint32(v___x_24_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_Data_depth___boxed(lean_object* v_c_26_){
_start:
{
uint64_t v_c_boxed_27_; uint32_t v_res_28_; lean_object* v_r_29_; 
v_c_boxed_27_ = lean_unbox_uint64(v_c_26_);
lean_dec_ref(v_c_26_);
v_res_28_ = l_Lean_Level_Data_depth(v_c_boxed_27_);
v_r_29_ = lean_box_uint32(v_res_28_);
return v_r_29_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_Data_hasMVar(uint64_t v_c_30_){
_start:
{
uint64_t v___x_31_; uint64_t v___x_32_; uint64_t v___x_33_; uint64_t v___x_34_; uint8_t v___x_35_; 
v___x_31_ = 32ULL;
v___x_32_ = lean_uint64_shift_right(v_c_30_, v___x_31_);
v___x_33_ = 1ULL;
v___x_34_ = lean_uint64_land(v___x_32_, v___x_33_);
v___x_35_ = lean_uint64_dec_eq(v___x_34_, v___x_33_);
return v___x_35_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_Data_hasMVar___boxed(lean_object* v_c_36_){
_start:
{
uint64_t v_c_boxed_37_; uint8_t v_res_38_; lean_object* v_r_39_; 
v_c_boxed_37_ = lean_unbox_uint64(v_c_36_);
lean_dec_ref(v_c_36_);
v_res_38_ = l_Lean_Level_Data_hasMVar(v_c_boxed_37_);
v_r_39_ = lean_box(v_res_38_);
return v_r_39_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_Data_hasParam(uint64_t v_c_40_){
_start:
{
uint64_t v___x_41_; uint64_t v___x_42_; uint64_t v___x_43_; uint64_t v___x_44_; uint8_t v___x_45_; 
v___x_41_ = 33ULL;
v___x_42_ = lean_uint64_shift_right(v_c_40_, v___x_41_);
v___x_43_ = 1ULL;
v___x_44_ = lean_uint64_land(v___x_42_, v___x_43_);
v___x_45_ = lean_uint64_dec_eq(v___x_44_, v___x_43_);
return v___x_45_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_Data_hasParam___boxed(lean_object* v_c_46_){
_start:
{
uint64_t v_c_boxed_47_; uint8_t v_res_48_; lean_object* v_r_49_; 
v_c_boxed_47_ = lean_unbox_uint64(v_c_46_);
lean_dec_ref(v_c_46_);
v_res_48_ = l_Lean_Level_Data_hasParam(v_c_boxed_47_);
v_r_49_ = lean_box(v_res_48_);
return v_r_49_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_mkData___boxed(lean_object* v_h_54_, lean_object* v_depth_55_, lean_object* v_hasMVar_56_, lean_object* v_hasParam_57_){
_start:
{
uint64_t v_h_boxed_58_; uint8_t v_hasMVar_boxed_59_; uint8_t v_hasParam_boxed_60_; uint64_t v_res_61_; lean_object* v_r_62_; 
v_h_boxed_58_ = lean_unbox_uint64(v_h_54_);
lean_dec_ref(v_h_54_);
v_hasMVar_boxed_59_ = lean_unbox(v_hasMVar_56_);
v_hasParam_boxed_60_ = lean_unbox(v_hasParam_57_);
v_res_61_ = lean_level_mk_data(v_h_boxed_58_, v_depth_55_, v_hasMVar_boxed_59_, v_hasParam_boxed_60_);
v_r_62_ = lean_box_uint64(v_res_61_);
return v_r_62_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprData___lam__0(uint64_t v_v_70_, lean_object* v_prec_71_){
_start:
{
lean_object* v_r_73_; lean_object* v___y_77_; lean_object* v___y_78_; lean_object* v_r_83_; lean_object* v___y_90_; lean_object* v___y_91_; lean_object* v_r_96_; lean_object* v___x_102_; uint64_t v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v_r_106_; uint32_t v___x_107_; uint32_t v___x_108_; uint8_t v___x_109_; uint8_t v___x_110_; 
v___x_102_ = ((lean_object*)(l_Lean_instReprData___lam__0___closed__5));
v___x_103_ = l_Lean_Level_Data_hash(v_v_70_);
v___x_104_ = lean_uint64_to_nat(v___x_103_);
v___x_105_ = l_Nat_reprFast(v___x_104_);
v_r_106_ = lean_string_append(v___x_102_, v___x_105_);
lean_dec_ref(v___x_105_);
v___x_107_ = l_Lean_Level_Data_depth(v_v_70_);
v___x_108_ = 0;
v___x_109_ = lean_uint32_dec_eq(v___x_107_, v___x_108_);
v___x_110_ = lean_bool_not(v___x_109_);
if (v___x_110_ == 0)
{
v_r_96_ = v_r_106_;
goto v___jp_95_;
}
else
{
lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v_r_117_; 
v___x_111_ = ((lean_object*)(l_Lean_instReprData___lam__0___closed__6));
v___x_112_ = lean_string_append(v_r_106_, v___x_111_);
v___x_113_ = lean_uint32_to_nat(v___x_107_);
v___x_114_ = l_Nat_reprFast(v___x_113_);
v___x_115_ = lean_string_append(v___x_112_, v___x_114_);
lean_dec_ref(v___x_114_);
v___x_116_ = ((lean_object*)(l_Lean_instReprData___lam__0___closed__0));
v_r_117_ = lean_string_append(v___x_115_, v___x_116_);
v_r_96_ = v_r_117_;
goto v___jp_95_;
}
v___jp_72_:
{
lean_object* v___x_74_; lean_object* v___x_75_; 
v___x_74_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_74_, 0, v_r_73_);
v___x_75_ = l_Repr_addAppParen(v___x_74_, v_prec_71_);
return v___x_75_;
}
v___jp_76_:
{
lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v_r_81_; 
v___x_79_ = lean_string_append(v___y_77_, v___y_78_);
v___x_80_ = ((lean_object*)(l_Lean_instReprData___lam__0___closed__0));
v_r_81_ = lean_string_append(v___x_79_, v___x_80_);
v_r_73_ = v_r_81_;
goto v___jp_72_;
}
v___jp_82_:
{
uint8_t v___x_84_; 
v___x_84_ = l_Lean_Level_Data_hasParam(v_v_70_);
if (v___x_84_ == 0)
{
v_r_73_ = v_r_83_;
goto v___jp_72_;
}
else
{
lean_object* v___x_85_; lean_object* v___x_86_; 
v___x_85_ = ((lean_object*)(l_Lean_instReprData___lam__0___closed__1));
v___x_86_ = lean_string_append(v_r_83_, v___x_85_);
if (v___x_84_ == 0)
{
lean_object* v___x_87_; 
v___x_87_ = ((lean_object*)(l_Lean_instReprData___lam__0___closed__2));
v___y_77_ = v___x_86_;
v___y_78_ = v___x_87_;
goto v___jp_76_;
}
else
{
lean_object* v___x_88_; 
v___x_88_ = ((lean_object*)(l_Lean_instReprData___lam__0___closed__3));
v___y_77_ = v___x_86_;
v___y_78_ = v___x_88_;
goto v___jp_76_;
}
}
}
v___jp_89_:
{
lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v_r_94_; 
v___x_92_ = lean_string_append(v___y_90_, v___y_91_);
v___x_93_ = ((lean_object*)(l_Lean_instReprData___lam__0___closed__0));
v_r_94_ = lean_string_append(v___x_92_, v___x_93_);
v_r_83_ = v_r_94_;
goto v___jp_82_;
}
v___jp_95_:
{
uint8_t v___x_97_; 
v___x_97_ = l_Lean_Level_Data_hasMVar(v_v_70_);
if (v___x_97_ == 0)
{
v_r_83_ = v_r_96_;
goto v___jp_82_;
}
else
{
lean_object* v___x_98_; lean_object* v___x_99_; 
v___x_98_ = ((lean_object*)(l_Lean_instReprData___lam__0___closed__4));
v___x_99_ = lean_string_append(v_r_96_, v___x_98_);
if (v___x_97_ == 0)
{
lean_object* v___x_100_; 
v___x_100_ = ((lean_object*)(l_Lean_instReprData___lam__0___closed__2));
v___y_90_ = v___x_99_;
v___y_91_ = v___x_100_;
goto v___jp_89_;
}
else
{
lean_object* v___x_101_; 
v___x_101_ = ((lean_object*)(l_Lean_instReprData___lam__0___closed__3));
v___y_90_ = v___x_99_;
v___y_91_ = v___x_101_;
goto v___jp_89_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instReprData___lam__0___boxed(lean_object* v_v_118_, lean_object* v_prec_119_){
_start:
{
uint64_t v_v_boxed_120_; lean_object* v_res_121_; 
v_v_boxed_120_ = lean_unbox_uint64(v_v_118_);
lean_dec_ref(v_v_118_);
v_res_121_ = l_Lean_instReprData___lam__0(v_v_boxed_120_, v_prec_119_);
lean_dec(v_prec_119_);
return v_res_121_;
}
}
static lean_object* _init_l_Lean_instInhabitedLevelMVarId_default(void){
_start:
{
lean_object* v___x_124_; 
v___x_124_ = lean_box(0);
return v___x_124_;
}
}
static lean_object* _init_l_Lean_instInhabitedLevelMVarId(void){
_start:
{
lean_object* v___x_125_; 
v___x_125_ = lean_box(0);
return v___x_125_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqLevelMVarId_beq(lean_object* v_x_126_, lean_object* v_x_127_){
_start:
{
uint8_t v___x_128_; 
v___x_128_ = lean_name_eq(v_x_126_, v_x_127_);
return v___x_128_;
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqLevelMVarId_beq___boxed(lean_object* v_x_129_, lean_object* v_x_130_){
_start:
{
uint8_t v_res_131_; lean_object* v_r_132_; 
v_res_131_ = l_Lean_instBEqLevelMVarId_beq(v_x_129_, v_x_130_);
lean_dec(v_x_130_);
lean_dec(v_x_129_);
v_r_132_ = lean_box(v_res_131_);
return v_r_132_;
}
}
static uint64_t _init_l_Lean_instHashableLevelMVarId_hash___closed__0(void){
_start:
{
lean_object* v___x_135_; uint64_t v___x_136_; 
v___x_135_ = lean_unsigned_to_nat(1723u);
v___x_136_ = lean_uint64_of_nat(v___x_135_);
return v___x_136_;
}
}
static uint64_t _init_l_Lean_instHashableLevelMVarId_hash___closed__1(void){
_start:
{
uint64_t v___x_137_; uint64_t v___x_138_; uint64_t v___x_139_; 
v___x_137_ = lean_uint64_once(&l_Lean_instHashableLevelMVarId_hash___closed__0, &l_Lean_instHashableLevelMVarId_hash___closed__0_once, _init_l_Lean_instHashableLevelMVarId_hash___closed__0);
v___x_138_ = 0ULL;
v___x_139_ = lean_uint64_mix_hash(v___x_138_, v___x_137_);
return v___x_139_;
}
}
LEAN_EXPORT uint64_t l_Lean_instHashableLevelMVarId_hash(lean_object* v_x_140_){
_start:
{
uint64_t v___x_141_; 
v___x_141_ = 0ULL;
if (lean_obj_tag(v_x_140_) == 0)
{
uint64_t v___x_142_; 
v___x_142_ = lean_uint64_once(&l_Lean_instHashableLevelMVarId_hash___closed__1, &l_Lean_instHashableLevelMVarId_hash___closed__1_once, _init_l_Lean_instHashableLevelMVarId_hash___closed__1);
return v___x_142_;
}
else
{
uint64_t v_hash_143_; uint64_t v___x_144_; 
v_hash_143_ = lean_ctor_get_uint64(v_x_140_, sizeof(void*)*2);
v___x_144_ = lean_uint64_mix_hash(v___x_141_, v_hash_143_);
return v___x_144_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instHashableLevelMVarId_hash___boxed(lean_object* v_x_145_){
_start:
{
uint64_t v_res_146_; lean_object* v_r_147_; 
v_res_146_ = l_Lean_instHashableLevelMVarId_hash(v_x_145_);
lean_dec(v_x_145_);
v_r_147_ = lean_box_uint64(v_res_146_);
return v_r_147_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_instReprLevelMVarId_repr_spec__0(lean_object* v_a_150_){
_start:
{
lean_object* v___x_151_; 
v___x_151_ = lean_nat_to_int(v_a_150_);
return v___x_151_;
}
}
static lean_object* _init_l_Lean_instReprLevelMVarId_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_165_; lean_object* v___x_166_; 
v___x_165_ = lean_unsigned_to_nat(8u);
v___x_166_ = lean_nat_to_int(v___x_165_);
return v___x_166_;
}
}
static lean_object* _init_l_Lean_instReprLevelMVarId_repr___redArg___closed__9(void){
_start:
{
lean_object* v___x_168_; lean_object* v___x_169_; 
v___x_168_ = ((lean_object*)(l_Lean_instReprLevelMVarId_repr___redArg___closed__0));
v___x_169_ = lean_string_length(v___x_168_);
return v___x_169_;
}
}
static lean_object* _init_l_Lean_instReprLevelMVarId_repr___redArg___closed__10(void){
_start:
{
lean_object* v___x_170_; lean_object* v___x_171_; 
v___x_170_ = lean_obj_once(&l_Lean_instReprLevelMVarId_repr___redArg___closed__9, &l_Lean_instReprLevelMVarId_repr___redArg___closed__9_once, _init_l_Lean_instReprLevelMVarId_repr___redArg___closed__9);
v___x_171_ = lean_nat_to_int(v___x_170_);
return v___x_171_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprLevelMVarId_repr___redArg(lean_object* v_x_176_){
_start:
{
lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; uint8_t v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; 
v___x_177_ = ((lean_object*)(l_Lean_instReprLevelMVarId_repr___redArg___closed__6));
v___x_178_ = lean_obj_once(&l_Lean_instReprLevelMVarId_repr___redArg___closed__7, &l_Lean_instReprLevelMVarId_repr___redArg___closed__7_once, _init_l_Lean_instReprLevelMVarId_repr___redArg___closed__7);
v___x_179_ = lean_unsigned_to_nat(0u);
v___x_180_ = l_Lean_Name_reprPrec(v_x_176_, v___x_179_);
v___x_181_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_181_, 0, v___x_178_);
lean_ctor_set(v___x_181_, 1, v___x_180_);
v___x_182_ = 0;
v___x_183_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_183_, 0, v___x_181_);
lean_ctor_set_uint8(v___x_183_, sizeof(void*)*1, v___x_182_);
v___x_184_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_184_, 0, v___x_177_);
lean_ctor_set(v___x_184_, 1, v___x_183_);
v___x_185_ = lean_obj_once(&l_Lean_instReprLevelMVarId_repr___redArg___closed__10, &l_Lean_instReprLevelMVarId_repr___redArg___closed__10_once, _init_l_Lean_instReprLevelMVarId_repr___redArg___closed__10);
v___x_186_ = ((lean_object*)(l_Lean_instReprLevelMVarId_repr___redArg___closed__11));
v___x_187_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_187_, 0, v___x_186_);
lean_ctor_set(v___x_187_, 1, v___x_184_);
v___x_188_ = ((lean_object*)(l_Lean_instReprLevelMVarId_repr___redArg___closed__12));
v___x_189_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_189_, 0, v___x_187_);
lean_ctor_set(v___x_189_, 1, v___x_188_);
v___x_190_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_190_, 0, v___x_185_);
lean_ctor_set(v___x_190_, 1, v___x_189_);
v___x_191_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_191_, 0, v___x_190_);
lean_ctor_set_uint8(v___x_191_, sizeof(void*)*1, v___x_182_);
return v___x_191_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprLevelMVarId_repr(lean_object* v_x_192_, lean_object* v_prec_193_){
_start:
{
lean_object* v___x_194_; 
v___x_194_ = l_Lean_instReprLevelMVarId_repr___redArg(v_x_192_);
return v___x_194_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprLevelMVarId_repr___boxed(lean_object* v_x_195_, lean_object* v_prec_196_){
_start:
{
lean_object* v_res_197_; 
v_res_197_ = l_Lean_instReprLevelMVarId_repr(v_x_195_, v_prec_196_);
lean_dec(v_prec_196_);
return v_res_197_;
}
}
static lean_object* _init_l_Lean_instInhabitedLMVarIdSet___aux__1(void){
_start:
{
lean_object* v___x_202_; 
v___x_202_ = lean_box(1);
return v___x_202_;
}
}
static lean_object* _init_l_Lean_instInhabitedLMVarIdSet(void){
_start:
{
lean_object* v___x_203_; 
v___x_203_ = lean_box(1);
return v___x_203_;
}
}
static lean_object* _init_l_Lean_instEmptyCollectionLMVarIdSet___aux__1(void){
_start:
{
lean_object* v___x_204_; 
v___x_204_ = lean_box(1);
return v___x_204_;
}
}
static lean_object* _init_l_Lean_instEmptyCollectionLMVarIdSet(void){
_start:
{
lean_object* v___x_205_; 
v___x_205_ = lean_box(1);
return v___x_205_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInLMVarIdSetLMVarIdOfMonad___aux__1___redArg___lam__0(lean_object* v_f_206_, lean_object* v_a_207_, lean_object* v_b_208_, lean_object* v_c_209_){
_start:
{
lean_object* v___x_210_; 
v___x_210_ = lean_apply_2(v_f_206_, v_a_207_, v_c_209_);
return v___x_210_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInLMVarIdSetLMVarIdOfMonad___aux__1___redArg___lam__1(lean_object* v_toPure_211_, lean_object* v_____do__lift_212_){
_start:
{
lean_object* v_a_213_; lean_object* v___x_214_; 
v_a_213_ = lean_ctor_get(v_____do__lift_212_, 0);
lean_inc(v_a_213_);
lean_dec_ref(v_____do__lift_212_);
v___x_214_ = lean_apply_2(v_toPure_211_, lean_box(0), v_a_213_);
return v___x_214_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInLMVarIdSetLMVarIdOfMonad___aux__1___redArg(lean_object* v_inst_215_, lean_object* v_m_216_, lean_object* v_init_217_, lean_object* v_f_218_){
_start:
{
lean_object* v_toApplicative_219_; lean_object* v_toBind_220_; lean_object* v_toPure_221_; lean_object* v___f_222_; lean_object* v___x_223_; lean_object* v___f_224_; lean_object* v___x_225_; 
v_toApplicative_219_ = lean_ctor_get(v_inst_215_, 0);
v_toBind_220_ = lean_ctor_get(v_inst_215_, 1);
lean_inc(v_toBind_220_);
v_toPure_221_ = lean_ctor_get(v_toApplicative_219_, 1);
lean_inc(v_toPure_221_);
v___f_222_ = lean_alloc_closure((void*)(l_Lean_instForInLMVarIdSetLMVarIdOfMonad___aux__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_222_, 0, v_f_218_);
v___x_223_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_215_, v___f_222_, v_init_217_, v_m_216_);
v___f_224_ = lean_alloc_closure((void*)(l_Lean_instForInLMVarIdSetLMVarIdOfMonad___aux__1___redArg___lam__1), 2, 1);
lean_closure_set(v___f_224_, 0, v_toPure_221_);
v___x_225_ = lean_apply_4(v_toBind_220_, lean_box(0), lean_box(0), v___x_223_, v___f_224_);
return v___x_225_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInLMVarIdSetLMVarIdOfMonad___aux__1(lean_object* v_m_226_, lean_object* v_inst_227_, lean_object* v_00_u03b2_228_, lean_object* v_m_229_, lean_object* v_init_230_, lean_object* v_f_231_){
_start:
{
lean_object* v_toApplicative_232_; lean_object* v_toBind_233_; lean_object* v_toPure_234_; lean_object* v___f_235_; lean_object* v___x_236_; lean_object* v___f_237_; lean_object* v___x_238_; 
v_toApplicative_232_ = lean_ctor_get(v_inst_227_, 0);
v_toBind_233_ = lean_ctor_get(v_inst_227_, 1);
lean_inc(v_toBind_233_);
v_toPure_234_ = lean_ctor_get(v_toApplicative_232_, 1);
lean_inc(v_toPure_234_);
v___f_235_ = lean_alloc_closure((void*)(l_Lean_instForInLMVarIdSetLMVarIdOfMonad___aux__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_235_, 0, v_f_231_);
v___x_236_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_227_, v___f_235_, v_init_230_, v_m_229_);
v___f_237_ = lean_alloc_closure((void*)(l_Lean_instForInLMVarIdSetLMVarIdOfMonad___aux__1___redArg___lam__1), 2, 1);
lean_closure_set(v___f_237_, 0, v_toPure_234_);
v___x_238_ = lean_apply_4(v_toBind_233_, lean_box(0), lean_box(0), v___x_236_, v___f_237_);
return v___x_238_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInLMVarIdSetLMVarIdOfMonad___redArg(lean_object* v_inst_239_){
_start:
{
lean_object* v___x_240_; 
v___x_240_ = lean_alloc_closure((void*)(l_Lean_instForInLMVarIdSetLMVarIdOfMonad___aux__1), 6, 2);
lean_closure_set(v___x_240_, 0, lean_box(0));
lean_closure_set(v___x_240_, 1, v_inst_239_);
return v___x_240_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInLMVarIdSetLMVarIdOfMonad(lean_object* v_m_241_, lean_object* v_inst_242_){
_start:
{
lean_object* v___x_243_; 
v___x_243_ = lean_alloc_closure((void*)(l_Lean_instForInLMVarIdSetLMVarIdOfMonad___aux__1), 6, 2);
lean_closure_set(v___x_243_, 0, lean_box(0));
lean_closure_set(v___x_243_, 1, v_inst_242_);
return v___x_243_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionLMVarIdMap___aux__1(lean_object* v_00_u03b1_244_){
_start:
{
lean_object* v___x_245_; 
v___x_245_ = lean_box(1);
return v___x_245_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionLMVarIdMap(lean_object* v_00_u03b1_246_){
_start:
{
lean_object* v___x_247_; 
v___x_247_ = lean_box(1);
return v___x_247_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInLMVarIdMapProdLMVarIdOfMonad___aux__1___redArg___lam__0(lean_object* v_f_248_, lean_object* v_a_249_, lean_object* v_b_250_, lean_object* v_c_251_){
_start:
{
lean_object* v___x_252_; lean_object* v___x_253_; 
v___x_252_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_252_, 0, v_a_249_);
lean_ctor_set(v___x_252_, 1, v_b_250_);
v___x_253_ = lean_apply_2(v_f_248_, v___x_252_, v_c_251_);
return v___x_253_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInLMVarIdMapProdLMVarIdOfMonad___aux__1___redArg(lean_object* v_inst_254_, lean_object* v_m_255_, lean_object* v_init_256_, lean_object* v_f_257_){
_start:
{
lean_object* v_toApplicative_258_; lean_object* v_toBind_259_; lean_object* v_toPure_260_; lean_object* v___f_261_; lean_object* v___x_262_; lean_object* v___f_263_; lean_object* v___x_264_; 
v_toApplicative_258_ = lean_ctor_get(v_inst_254_, 0);
v_toBind_259_ = lean_ctor_get(v_inst_254_, 1);
lean_inc(v_toBind_259_);
v_toPure_260_ = lean_ctor_get(v_toApplicative_258_, 1);
lean_inc(v_toPure_260_);
v___f_261_ = lean_alloc_closure((void*)(l_Lean_instForInLMVarIdMapProdLMVarIdOfMonad___aux__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_261_, 0, v_f_257_);
v___x_262_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_254_, v___f_261_, v_init_256_, v_m_255_);
v___f_263_ = lean_alloc_closure((void*)(l_Lean_instForInLMVarIdSetLMVarIdOfMonad___aux__1___redArg___lam__1), 2, 1);
lean_closure_set(v___f_263_, 0, v_toPure_260_);
v___x_264_ = lean_apply_4(v_toBind_259_, lean_box(0), lean_box(0), v___x_262_, v___f_263_);
return v___x_264_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInLMVarIdMapProdLMVarIdOfMonad___aux__1(lean_object* v_m_265_, lean_object* v_00_u03b1_266_, lean_object* v_inst_267_, lean_object* v_00_u03b2_268_, lean_object* v_m_269_, lean_object* v_init_270_, lean_object* v_f_271_){
_start:
{
lean_object* v_toApplicative_272_; lean_object* v_toBind_273_; lean_object* v_toPure_274_; lean_object* v___f_275_; lean_object* v___x_276_; lean_object* v___f_277_; lean_object* v___x_278_; 
v_toApplicative_272_ = lean_ctor_get(v_inst_267_, 0);
v_toBind_273_ = lean_ctor_get(v_inst_267_, 1);
lean_inc(v_toBind_273_);
v_toPure_274_ = lean_ctor_get(v_toApplicative_272_, 1);
lean_inc(v_toPure_274_);
v___f_275_ = lean_alloc_closure((void*)(l_Lean_instForInLMVarIdMapProdLMVarIdOfMonad___aux__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_275_, 0, v_f_271_);
v___x_276_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_267_, v___f_275_, v_init_270_, v_m_269_);
v___f_277_ = lean_alloc_closure((void*)(l_Lean_instForInLMVarIdSetLMVarIdOfMonad___aux__1___redArg___lam__1), 2, 1);
lean_closure_set(v___f_277_, 0, v_toPure_274_);
v___x_278_ = lean_apply_4(v_toBind_273_, lean_box(0), lean_box(0), v___x_276_, v___f_277_);
return v___x_278_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInLMVarIdMapProdLMVarIdOfMonad___redArg(lean_object* v_inst_279_){
_start:
{
lean_object* v___x_280_; 
v___x_280_ = lean_alloc_closure((void*)(l_Lean_instForInLMVarIdMapProdLMVarIdOfMonad___aux__1), 7, 3);
lean_closure_set(v___x_280_, 0, lean_box(0));
lean_closure_set(v___x_280_, 1, lean_box(0));
lean_closure_set(v___x_280_, 2, v_inst_279_);
return v___x_280_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInLMVarIdMapProdLMVarIdOfMonad(lean_object* v_m_281_, lean_object* v_00_u03b1_282_, lean_object* v_inst_283_){
_start:
{
lean_object* v___x_284_; 
v___x_284_ = lean_alloc_closure((void*)(l_Lean_instForInLMVarIdMapProdLMVarIdOfMonad___aux__1), 7, 3);
lean_closure_set(v___x_284_, 0, lean_box(0));
lean_closure_set(v___x_284_, 1, lean_box(0));
lean_closure_set(v___x_284_, 2, v_inst_283_);
return v___x_284_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedLMVarIdMap(lean_object* v_00_u03b1_285_){
_start:
{
lean_object* v___x_286_; 
v___x_286_ = lean_box(1);
return v___x_286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_ctorIdx(lean_object* v_x_287_){
_start:
{
switch(lean_obj_tag(v_x_287_))
{
case 0:
{
lean_object* v___x_288_; 
v___x_288_ = lean_unsigned_to_nat(0u);
return v___x_288_;
}
case 1:
{
lean_object* v___x_289_; 
v___x_289_ = lean_unsigned_to_nat(1u);
return v___x_289_;
}
case 2:
{
lean_object* v___x_290_; 
v___x_290_ = lean_unsigned_to_nat(2u);
return v___x_290_;
}
case 3:
{
lean_object* v___x_291_; 
v___x_291_ = lean_unsigned_to_nat(3u);
return v___x_291_;
}
case 4:
{
lean_object* v___x_292_; 
v___x_292_ = lean_unsigned_to_nat(4u);
return v___x_292_;
}
default: 
{
lean_object* v___x_293_; 
v___x_293_ = lean_unsigned_to_nat(5u);
return v___x_293_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_ctorIdx___boxed(lean_object* v_x_294_){
_start:
{
lean_object* v_res_295_; 
v_res_295_ = l_Lean_Level_ctorIdx(v_x_294_);
lean_dec(v_x_294_);
return v_res_295_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_ctorElim___redArg(lean_object* v_t_296_, lean_object* v_k_297_){
_start:
{
switch(lean_obj_tag(v_t_296_))
{
case 0:
{
return v_k_297_;
}
case 2:
{
lean_object* v_a_298_; lean_object* v_a_299_; lean_object* v___x_300_; 
v_a_298_ = lean_ctor_get(v_t_296_, 0);
lean_inc(v_a_298_);
v_a_299_ = lean_ctor_get(v_t_296_, 1);
lean_inc(v_a_299_);
lean_dec_ref_known(v_t_296_, 2);
v___x_300_ = lean_apply_2(v_k_297_, v_a_298_, v_a_299_);
return v___x_300_;
}
case 3:
{
lean_object* v_a_301_; lean_object* v_a_302_; lean_object* v___x_303_; 
v_a_301_ = lean_ctor_get(v_t_296_, 0);
lean_inc(v_a_301_);
v_a_302_ = lean_ctor_get(v_t_296_, 1);
lean_inc(v_a_302_);
lean_dec_ref_known(v_t_296_, 2);
v___x_303_ = lean_apply_2(v_k_297_, v_a_301_, v_a_302_);
return v___x_303_;
}
default: 
{
lean_object* v_a_304_; lean_object* v___x_305_; 
v_a_304_ = lean_ctor_get(v_t_296_, 0);
lean_inc(v_a_304_);
lean_dec(v_t_296_);
v___x_305_ = lean_apply_1(v_k_297_, v_a_304_);
return v___x_305_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_ctorElim(lean_object* v_motive_306_, lean_object* v_ctorIdx_307_, lean_object* v_t_308_, lean_object* v_h_309_, lean_object* v_k_310_){
_start:
{
lean_object* v___x_311_; 
v___x_311_ = l_Lean_Level_ctorElim___redArg(v_t_308_, v_k_310_);
return v___x_311_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_ctorElim___boxed(lean_object* v_motive_312_, lean_object* v_ctorIdx_313_, lean_object* v_t_314_, lean_object* v_h_315_, lean_object* v_k_316_){
_start:
{
lean_object* v_res_317_; 
v_res_317_ = l_Lean_Level_ctorElim(v_motive_312_, v_ctorIdx_313_, v_t_314_, v_h_315_, v_k_316_);
lean_dec(v_ctorIdx_313_);
return v_res_317_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_zero_elim___redArg(lean_object* v_t_318_, lean_object* v_zero_319_){
_start:
{
lean_object* v___x_320_; 
v___x_320_ = l_Lean_Level_ctorElim___redArg(v_t_318_, v_zero_319_);
return v___x_320_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_zero_elim(lean_object* v_motive_321_, lean_object* v_t_322_, lean_object* v_h_323_, lean_object* v_zero_324_){
_start:
{
lean_object* v___x_325_; 
v___x_325_ = l_Lean_Level_ctorElim___redArg(v_t_322_, v_zero_324_);
return v___x_325_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_succ_elim___redArg(lean_object* v_t_326_, lean_object* v_succ_327_){
_start:
{
lean_object* v___x_328_; 
v___x_328_ = l_Lean_Level_ctorElim___redArg(v_t_326_, v_succ_327_);
return v___x_328_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_succ_elim(lean_object* v_motive_329_, lean_object* v_t_330_, lean_object* v_h_331_, lean_object* v_succ_332_){
_start:
{
lean_object* v___x_333_; 
v___x_333_ = l_Lean_Level_ctorElim___redArg(v_t_330_, v_succ_332_);
return v___x_333_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_max_elim___redArg(lean_object* v_t_334_, lean_object* v_max_335_){
_start:
{
lean_object* v___x_336_; 
v___x_336_ = l_Lean_Level_ctorElim___redArg(v_t_334_, v_max_335_);
return v___x_336_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_max_elim(lean_object* v_motive_337_, lean_object* v_t_338_, lean_object* v_h_339_, lean_object* v_max_340_){
_start:
{
lean_object* v___x_341_; 
v___x_341_ = l_Lean_Level_ctorElim___redArg(v_t_338_, v_max_340_);
return v___x_341_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_imax_elim___redArg(lean_object* v_t_342_, lean_object* v_imax_343_){
_start:
{
lean_object* v___x_344_; 
v___x_344_ = l_Lean_Level_ctorElim___redArg(v_t_342_, v_imax_343_);
return v___x_344_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_imax_elim(lean_object* v_motive_345_, lean_object* v_t_346_, lean_object* v_h_347_, lean_object* v_imax_348_){
_start:
{
lean_object* v___x_349_; 
v___x_349_ = l_Lean_Level_ctorElim___redArg(v_t_346_, v_imax_348_);
return v___x_349_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_param_elim___redArg(lean_object* v_t_350_, lean_object* v_param_351_){
_start:
{
lean_object* v___x_352_; 
v___x_352_ = l_Lean_Level_ctorElim___redArg(v_t_350_, v_param_351_);
return v___x_352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_param_elim(lean_object* v_motive_353_, lean_object* v_t_354_, lean_object* v_h_355_, lean_object* v_param_356_){
_start:
{
lean_object* v___x_357_; 
v___x_357_ = l_Lean_Level_ctorElim___redArg(v_t_354_, v_param_356_);
return v___x_357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_mvar_elim___redArg(lean_object* v_t_358_, lean_object* v_mvar_359_){
_start:
{
lean_object* v___x_360_; 
v___x_360_ = l_Lean_Level_ctorElim___redArg(v_t_358_, v_mvar_359_);
return v___x_360_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_mvar_elim(lean_object* v_motive_361_, lean_object* v_t_362_, lean_object* v_h_363_, lean_object* v_mvar_364_){
_start:
{
lean_object* v___x_365_; 
v___x_365_ = l_Lean_Level_ctorElim___redArg(v_t_362_, v_mvar_364_);
return v___x_365_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_casesOn___override___redArg(lean_object* v_t_366_, lean_object* v_zero_367_, lean_object* v_succ_368_, lean_object* v_max_369_, lean_object* v_imax_370_, lean_object* v_param_371_, lean_object* v_mvar_372_){
_start:
{
switch(lean_obj_tag(v_t_366_))
{
case 0:
{
lean_dec(v_mvar_372_);
lean_dec(v_param_371_);
lean_dec(v_imax_370_);
lean_dec(v_max_369_);
lean_dec(v_succ_368_);
lean_inc(v_zero_367_);
return v_zero_367_;
}
case 1:
{
lean_object* v_a_373_; lean_object* v___x_374_; 
lean_dec(v_mvar_372_);
lean_dec(v_param_371_);
lean_dec(v_imax_370_);
lean_dec(v_max_369_);
v_a_373_ = lean_ctor_get(v_t_366_, 0);
lean_inc(v_a_373_);
lean_dec_ref_known(v_t_366_, 1);
v___x_374_ = lean_apply_1(v_succ_368_, v_a_373_);
return v___x_374_;
}
case 2:
{
lean_object* v_a_375_; lean_object* v_a_376_; lean_object* v___x_377_; 
lean_dec(v_mvar_372_);
lean_dec(v_param_371_);
lean_dec(v_imax_370_);
lean_dec(v_succ_368_);
v_a_375_ = lean_ctor_get(v_t_366_, 0);
lean_inc(v_a_375_);
v_a_376_ = lean_ctor_get(v_t_366_, 1);
lean_inc(v_a_376_);
lean_dec_ref_known(v_t_366_, 2);
v___x_377_ = lean_apply_2(v_max_369_, v_a_375_, v_a_376_);
return v___x_377_;
}
case 3:
{
lean_object* v_a_378_; lean_object* v_a_379_; lean_object* v___x_380_; 
lean_dec(v_mvar_372_);
lean_dec(v_param_371_);
lean_dec(v_max_369_);
lean_dec(v_succ_368_);
v_a_378_ = lean_ctor_get(v_t_366_, 0);
lean_inc(v_a_378_);
v_a_379_ = lean_ctor_get(v_t_366_, 1);
lean_inc(v_a_379_);
lean_dec_ref_known(v_t_366_, 2);
v___x_380_ = lean_apply_2(v_imax_370_, v_a_378_, v_a_379_);
return v___x_380_;
}
case 4:
{
lean_object* v_a_381_; lean_object* v___x_382_; 
lean_dec(v_mvar_372_);
lean_dec(v_imax_370_);
lean_dec(v_max_369_);
lean_dec(v_succ_368_);
v_a_381_ = lean_ctor_get(v_t_366_, 0);
lean_inc(v_a_381_);
lean_dec_ref_known(v_t_366_, 1);
v___x_382_ = lean_apply_1(v_param_371_, v_a_381_);
return v___x_382_;
}
default: 
{
lean_object* v_a_383_; lean_object* v___x_384_; 
lean_dec(v_param_371_);
lean_dec(v_imax_370_);
lean_dec(v_max_369_);
lean_dec(v_succ_368_);
v_a_383_ = lean_ctor_get(v_t_366_, 0);
lean_inc(v_a_383_);
lean_dec_ref_known(v_t_366_, 1);
v___x_384_ = lean_apply_1(v_mvar_372_, v_a_383_);
return v___x_384_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_casesOn___override___redArg___boxed(lean_object* v_t_385_, lean_object* v_zero_386_, lean_object* v_succ_387_, lean_object* v_max_388_, lean_object* v_imax_389_, lean_object* v_param_390_, lean_object* v_mvar_391_){
_start:
{
lean_object* v_res_392_; 
v_res_392_ = l_Lean_Level_casesOn___override___redArg(v_t_385_, v_zero_386_, v_succ_387_, v_max_388_, v_imax_389_, v_param_390_, v_mvar_391_);
lean_dec(v_zero_386_);
return v_res_392_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_casesOn___override(lean_object* v_motive_393_, lean_object* v_t_394_, lean_object* v_zero_395_, lean_object* v_succ_396_, lean_object* v_max_397_, lean_object* v_imax_398_, lean_object* v_param_399_, lean_object* v_mvar_400_){
_start:
{
switch(lean_obj_tag(v_t_394_))
{
case 0:
{
lean_dec(v_mvar_400_);
lean_dec(v_param_399_);
lean_dec(v_imax_398_);
lean_dec(v_max_397_);
lean_dec(v_succ_396_);
lean_inc(v_zero_395_);
return v_zero_395_;
}
case 1:
{
lean_object* v_a_401_; lean_object* v___x_402_; 
lean_dec(v_mvar_400_);
lean_dec(v_param_399_);
lean_dec(v_imax_398_);
lean_dec(v_max_397_);
v_a_401_ = lean_ctor_get(v_t_394_, 0);
lean_inc(v_a_401_);
lean_dec_ref_known(v_t_394_, 1);
v___x_402_ = lean_apply_1(v_succ_396_, v_a_401_);
return v___x_402_;
}
case 2:
{
lean_object* v_a_403_; lean_object* v_a_404_; lean_object* v___x_405_; 
lean_dec(v_mvar_400_);
lean_dec(v_param_399_);
lean_dec(v_imax_398_);
lean_dec(v_succ_396_);
v_a_403_ = lean_ctor_get(v_t_394_, 0);
lean_inc(v_a_403_);
v_a_404_ = lean_ctor_get(v_t_394_, 1);
lean_inc(v_a_404_);
lean_dec_ref_known(v_t_394_, 2);
v___x_405_ = lean_apply_2(v_max_397_, v_a_403_, v_a_404_);
return v___x_405_;
}
case 3:
{
lean_object* v_a_406_; lean_object* v_a_407_; lean_object* v___x_408_; 
lean_dec(v_mvar_400_);
lean_dec(v_param_399_);
lean_dec(v_max_397_);
lean_dec(v_succ_396_);
v_a_406_ = lean_ctor_get(v_t_394_, 0);
lean_inc(v_a_406_);
v_a_407_ = lean_ctor_get(v_t_394_, 1);
lean_inc(v_a_407_);
lean_dec_ref_known(v_t_394_, 2);
v___x_408_ = lean_apply_2(v_imax_398_, v_a_406_, v_a_407_);
return v___x_408_;
}
case 4:
{
lean_object* v_a_409_; lean_object* v___x_410_; 
lean_dec(v_mvar_400_);
lean_dec(v_imax_398_);
lean_dec(v_max_397_);
lean_dec(v_succ_396_);
v_a_409_ = lean_ctor_get(v_t_394_, 0);
lean_inc(v_a_409_);
lean_dec_ref_known(v_t_394_, 1);
v___x_410_ = lean_apply_1(v_param_399_, v_a_409_);
return v___x_410_;
}
default: 
{
lean_object* v_a_411_; lean_object* v___x_412_; 
lean_dec(v_param_399_);
lean_dec(v_imax_398_);
lean_dec(v_max_397_);
lean_dec(v_succ_396_);
v_a_411_ = lean_ctor_get(v_t_394_, 0);
lean_inc(v_a_411_);
lean_dec_ref_known(v_t_394_, 1);
v___x_412_ = lean_apply_1(v_mvar_400_, v_a_411_);
return v___x_412_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_casesOn___override___boxed(lean_object* v_motive_413_, lean_object* v_t_414_, lean_object* v_zero_415_, lean_object* v_succ_416_, lean_object* v_max_417_, lean_object* v_imax_418_, lean_object* v_param_419_, lean_object* v_mvar_420_){
_start:
{
lean_object* v_res_421_; 
v_res_421_ = l_Lean_Level_casesOn___override(v_motive_413_, v_t_414_, v_zero_415_, v_succ_416_, v_max_417_, v_imax_418_, v_param_419_, v_mvar_420_);
lean_dec(v_zero_415_);
return v_res_421_;
}
}
static lean_object* _init_l_Lean_Level_zero___override(void){
_start:
{
lean_object* v___x_422_; 
v___x_422_ = lean_box(0);
return v___x_422_;
}
}
static uint64_t _init_l_Lean_Level_data___override___closed__0(void){
_start:
{
uint8_t v___x_423_; lean_object* v___x_424_; uint64_t v___x_425_; uint64_t v___x_426_; 
v___x_423_ = 0;
v___x_424_ = lean_unsigned_to_nat(0u);
v___x_425_ = 2221ULL;
v___x_426_ = lean_level_mk_data(v___x_425_, v___x_424_, v___x_423_, v___x_423_);
return v___x_426_;
}
}
LEAN_EXPORT uint64_t l_Lean_Level_data___override(lean_object* v_x_427_){
_start:
{
switch(lean_obj_tag(v_x_427_))
{
case 0:
{
uint64_t v___x_428_; 
v___x_428_ = lean_uint64_once(&l_Lean_Level_data___override___closed__0, &l_Lean_Level_data___override___closed__0_once, _init_l_Lean_Level_data___override___closed__0);
return v___x_428_;
}
case 2:
{
uint64_t v_data_429_; 
v_data_429_ = lean_ctor_get_uint64(v_x_427_, sizeof(void*)*2);
return v_data_429_;
}
case 3:
{
uint64_t v_data_430_; 
v_data_430_ = lean_ctor_get_uint64(v_x_427_, sizeof(void*)*2);
return v_data_430_;
}
default: 
{
uint64_t v_data_431_; 
v_data_431_ = lean_ctor_get_uint64(v_x_427_, sizeof(void*)*1);
return v_data_431_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_data___override___boxed(lean_object* v_x_432_){
_start:
{
uint64_t v_res_433_; lean_object* v_r_434_; 
v_res_433_ = l_Lean_Level_data___override(v_x_432_);
lean_dec(v_x_432_);
v_r_434_ = lean_box_uint64(v_res_433_);
return v_r_434_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_succ___override(lean_object* v_a_435_){
_start:
{
uint64_t v___x_436_; uint64_t v___x_437_; uint64_t v___x_438_; uint64_t v___x_439_; uint32_t v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; uint8_t v___x_444_; uint8_t v___x_445_; uint64_t v___x_446_; lean_object* v___x_447_; 
v___x_436_ = 2243ULL;
v___x_437_ = l_Lean_Level_data___override(v_a_435_);
v___x_438_ = l_Lean_Level_Data_hash(v___x_437_);
v___x_439_ = lean_uint64_mix_hash(v___x_436_, v___x_438_);
v___x_440_ = l_Lean_Level_Data_depth(v___x_437_);
v___x_441_ = lean_uint32_to_nat(v___x_440_);
v___x_442_ = lean_unsigned_to_nat(1u);
v___x_443_ = lean_nat_add(v___x_441_, v___x_442_);
lean_dec(v___x_441_);
v___x_444_ = l_Lean_Level_Data_hasMVar(v___x_437_);
v___x_445_ = l_Lean_Level_Data_hasParam(v___x_437_);
v___x_446_ = lean_level_mk_data(v___x_439_, v___x_443_, v___x_444_, v___x_445_);
v___x_447_ = lean_alloc_ctor(1, 1, 8);
lean_ctor_set(v___x_447_, 0, v_a_435_);
lean_ctor_set_uint64(v___x_447_, sizeof(void*)*1, v___x_446_);
return v___x_447_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_max___override(lean_object* v_a_448_, lean_object* v_a_449_){
_start:
{
uint64_t v___x_450_; uint64_t v___x_451_; uint64_t v___x_452_; uint64_t v___x_453_; uint64_t v___x_454_; uint64_t v___x_455_; uint64_t v___x_456_; uint8_t v___y_458_; lean_object* v___y_459_; uint8_t v___y_460_; lean_object* v___y_464_; uint8_t v___y_465_; lean_object* v___y_469_; uint32_t v___x_474_; lean_object* v___x_475_; uint32_t v___x_476_; lean_object* v___x_477_; uint8_t v___x_478_; 
v___x_450_ = 2251ULL;
v___x_451_ = l_Lean_Level_data___override(v_a_448_);
v___x_452_ = l_Lean_Level_Data_hash(v___x_451_);
v___x_453_ = l_Lean_Level_data___override(v_a_449_);
v___x_454_ = l_Lean_Level_Data_hash(v___x_453_);
v___x_455_ = lean_uint64_mix_hash(v___x_452_, v___x_454_);
v___x_456_ = lean_uint64_mix_hash(v___x_450_, v___x_455_);
v___x_474_ = l_Lean_Level_Data_depth(v___x_451_);
v___x_475_ = lean_uint32_to_nat(v___x_474_);
v___x_476_ = l_Lean_Level_Data_depth(v___x_453_);
v___x_477_ = lean_uint32_to_nat(v___x_476_);
v___x_478_ = lean_nat_dec_le(v___x_475_, v___x_477_);
if (v___x_478_ == 0)
{
lean_dec(v___x_477_);
v___y_469_ = v___x_475_;
goto v___jp_468_;
}
else
{
lean_dec(v___x_475_);
v___y_469_ = v___x_477_;
goto v___jp_468_;
}
v___jp_457_:
{
uint64_t v___x_461_; lean_object* v___x_462_; 
v___x_461_ = lean_level_mk_data(v___x_456_, v___y_459_, v___y_458_, v___y_460_);
v___x_462_ = lean_alloc_ctor(2, 2, 8);
lean_ctor_set(v___x_462_, 0, v_a_448_);
lean_ctor_set(v___x_462_, 1, v_a_449_);
lean_ctor_set_uint64(v___x_462_, sizeof(void*)*2, v___x_461_);
return v___x_462_;
}
v___jp_463_:
{
uint8_t v___x_466_; 
v___x_466_ = l_Lean_Level_Data_hasParam(v___x_451_);
if (v___x_466_ == 0)
{
uint8_t v___x_467_; 
v___x_467_ = l_Lean_Level_Data_hasParam(v___x_453_);
v___y_458_ = v___y_465_;
v___y_459_ = v___y_464_;
v___y_460_ = v___x_467_;
goto v___jp_457_;
}
else
{
v___y_458_ = v___y_465_;
v___y_459_ = v___y_464_;
v___y_460_ = v___x_466_;
goto v___jp_457_;
}
}
v___jp_468_:
{
lean_object* v___x_470_; lean_object* v___x_471_; uint8_t v___x_472_; 
v___x_470_ = lean_unsigned_to_nat(1u);
v___x_471_ = lean_nat_add(v___y_469_, v___x_470_);
lean_dec(v___y_469_);
v___x_472_ = l_Lean_Level_Data_hasMVar(v___x_451_);
if (v___x_472_ == 0)
{
uint8_t v___x_473_; 
v___x_473_ = l_Lean_Level_Data_hasMVar(v___x_453_);
v___y_464_ = v___x_471_;
v___y_465_ = v___x_473_;
goto v___jp_463_;
}
else
{
v___y_464_ = v___x_471_;
v___y_465_ = v___x_472_;
goto v___jp_463_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_imax___override(lean_object* v_a_479_, lean_object* v_a_480_){
_start:
{
uint64_t v___x_481_; uint64_t v___x_482_; uint64_t v___x_483_; uint64_t v___x_484_; uint64_t v___x_485_; uint64_t v___x_486_; uint64_t v___x_487_; lean_object* v___y_489_; uint8_t v___y_490_; uint8_t v___y_491_; lean_object* v___y_495_; uint8_t v___y_496_; lean_object* v___y_500_; uint32_t v___x_505_; lean_object* v___x_506_; uint32_t v___x_507_; lean_object* v___x_508_; uint8_t v___x_509_; 
v___x_481_ = 2267ULL;
v___x_482_ = l_Lean_Level_data___override(v_a_479_);
v___x_483_ = l_Lean_Level_Data_hash(v___x_482_);
v___x_484_ = l_Lean_Level_data___override(v_a_480_);
v___x_485_ = l_Lean_Level_Data_hash(v___x_484_);
v___x_486_ = lean_uint64_mix_hash(v___x_483_, v___x_485_);
v___x_487_ = lean_uint64_mix_hash(v___x_481_, v___x_486_);
v___x_505_ = l_Lean_Level_Data_depth(v___x_482_);
v___x_506_ = lean_uint32_to_nat(v___x_505_);
v___x_507_ = l_Lean_Level_Data_depth(v___x_484_);
v___x_508_ = lean_uint32_to_nat(v___x_507_);
v___x_509_ = lean_nat_dec_le(v___x_506_, v___x_508_);
if (v___x_509_ == 0)
{
lean_dec(v___x_508_);
v___y_500_ = v___x_506_;
goto v___jp_499_;
}
else
{
lean_dec(v___x_506_);
v___y_500_ = v___x_508_;
goto v___jp_499_;
}
v___jp_488_:
{
uint64_t v___x_492_; lean_object* v___x_493_; 
v___x_492_ = lean_level_mk_data(v___x_487_, v___y_489_, v___y_490_, v___y_491_);
v___x_493_ = lean_alloc_ctor(3, 2, 8);
lean_ctor_set(v___x_493_, 0, v_a_479_);
lean_ctor_set(v___x_493_, 1, v_a_480_);
lean_ctor_set_uint64(v___x_493_, sizeof(void*)*2, v___x_492_);
return v___x_493_;
}
v___jp_494_:
{
uint8_t v___x_497_; 
v___x_497_ = l_Lean_Level_Data_hasParam(v___x_482_);
if (v___x_497_ == 0)
{
uint8_t v___x_498_; 
v___x_498_ = l_Lean_Level_Data_hasParam(v___x_484_);
v___y_489_ = v___y_495_;
v___y_490_ = v___y_496_;
v___y_491_ = v___x_498_;
goto v___jp_488_;
}
else
{
v___y_489_ = v___y_495_;
v___y_490_ = v___y_496_;
v___y_491_ = v___x_497_;
goto v___jp_488_;
}
}
v___jp_499_:
{
lean_object* v___x_501_; lean_object* v___x_502_; uint8_t v___x_503_; 
v___x_501_ = lean_unsigned_to_nat(1u);
v___x_502_ = lean_nat_add(v___y_500_, v___x_501_);
lean_dec(v___y_500_);
v___x_503_ = l_Lean_Level_Data_hasMVar(v___x_482_);
if (v___x_503_ == 0)
{
uint8_t v___x_504_; 
v___x_504_ = l_Lean_Level_Data_hasMVar(v___x_484_);
v___y_495_ = v___x_502_;
v___y_496_ = v___x_504_;
goto v___jp_494_;
}
else
{
v___y_495_ = v___x_502_;
v___y_496_ = v___x_503_;
goto v___jp_494_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_param___override(lean_object* v_a_510_){
_start:
{
uint64_t v___x_511_; uint64_t v___y_513_; 
v___x_511_ = 2239ULL;
if (lean_obj_tag(v_a_510_) == 0)
{
uint64_t v___x_520_; 
v___x_520_ = lean_uint64_once(&l_Lean_instHashableLevelMVarId_hash___closed__0, &l_Lean_instHashableLevelMVarId_hash___closed__0_once, _init_l_Lean_instHashableLevelMVarId_hash___closed__0);
v___y_513_ = v___x_520_;
goto v___jp_512_;
}
else
{
uint64_t v_hash_521_; 
v_hash_521_ = lean_ctor_get_uint64(v_a_510_, sizeof(void*)*2);
v___y_513_ = v_hash_521_;
goto v___jp_512_;
}
v___jp_512_:
{
uint64_t v___x_514_; lean_object* v___x_515_; uint8_t v___x_516_; uint8_t v___x_517_; uint64_t v___x_518_; lean_object* v___x_519_; 
v___x_514_ = lean_uint64_mix_hash(v___x_511_, v___y_513_);
v___x_515_ = lean_unsigned_to_nat(0u);
v___x_516_ = 0;
v___x_517_ = 1;
v___x_518_ = lean_level_mk_data(v___x_514_, v___x_515_, v___x_516_, v___x_517_);
v___x_519_ = lean_alloc_ctor(4, 1, 8);
lean_ctor_set(v___x_519_, 0, v_a_510_);
lean_ctor_set_uint64(v___x_519_, sizeof(void*)*1, v___x_518_);
return v___x_519_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_mvar___override(lean_object* v_a_522_){
_start:
{
uint64_t v___x_523_; uint64_t v___x_524_; uint64_t v___x_525_; lean_object* v___x_526_; uint8_t v___x_527_; uint8_t v___x_528_; uint64_t v___x_529_; lean_object* v___x_530_; 
v___x_523_ = 2237ULL;
v___x_524_ = l_Lean_instHashableLevelMVarId_hash(v_a_522_);
v___x_525_ = lean_uint64_mix_hash(v___x_523_, v___x_524_);
v___x_526_ = lean_unsigned_to_nat(0u);
v___x_527_ = 1;
v___x_528_ = 0;
v___x_529_ = lean_level_mk_data(v___x_525_, v___x_526_, v___x_527_, v___x_528_);
v___x_530_ = lean_alloc_ctor(5, 1, 8);
lean_ctor_set(v___x_530_, 0, v_a_522_);
lean_ctor_set_uint64(v___x_530_, sizeof(void*)*1, v___x_529_);
return v___x_530_;
}
}
static lean_object* _init_l_Lean_instInhabitedLevel_default(void){
_start:
{
lean_object* v___x_531_; 
v___x_531_ = lean_box(0);
return v___x_531_;
}
}
static lean_object* _init_l_Lean_instInhabitedLevel(void){
_start:
{
lean_object* v___x_532_; 
v___x_532_ = lean_box(0);
return v___x_532_;
}
}
static lean_object* _init_l_Lean_instReprLevel_repr___closed__2(void){
_start:
{
lean_object* v___x_536_; lean_object* v___x_537_; 
v___x_536_ = lean_unsigned_to_nat(2u);
v___x_537_ = lean_nat_to_int(v___x_536_);
return v___x_537_;
}
}
static lean_object* _init_l_Lean_instReprLevel_repr___closed__3(void){
_start:
{
lean_object* v___x_538_; lean_object* v___x_539_; 
v___x_538_ = lean_unsigned_to_nat(1u);
v___x_539_ = lean_nat_to_int(v___x_538_);
return v___x_539_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprLevel_repr(lean_object* v_x_570_, lean_object* v_prec_571_){
_start:
{
lean_object* v___y_573_; 
switch(lean_obj_tag(v_x_570_))
{
case 0:
{
lean_object* v___x_579_; uint8_t v___x_580_; 
v___x_579_ = lean_unsigned_to_nat(1024u);
v___x_580_ = lean_nat_dec_le(v___x_579_, v_prec_571_);
if (v___x_580_ == 0)
{
lean_object* v___x_581_; 
v___x_581_ = lean_obj_once(&l_Lean_instReprLevel_repr___closed__2, &l_Lean_instReprLevel_repr___closed__2_once, _init_l_Lean_instReprLevel_repr___closed__2);
v___y_573_ = v___x_581_;
goto v___jp_572_;
}
else
{
lean_object* v___x_582_; 
v___x_582_ = lean_obj_once(&l_Lean_instReprLevel_repr___closed__3, &l_Lean_instReprLevel_repr___closed__3_once, _init_l_Lean_instReprLevel_repr___closed__3);
v___y_573_ = v___x_582_;
goto v___jp_572_;
}
}
case 1:
{
lean_object* v_a_583_; lean_object* v___x_584_; lean_object* v___y_586_; uint8_t v___x_594_; 
v_a_583_ = lean_ctor_get(v_x_570_, 0);
lean_inc(v_a_583_);
lean_dec_ref_known(v_x_570_, 1);
v___x_584_ = lean_unsigned_to_nat(1024u);
v___x_594_ = lean_nat_dec_le(v___x_584_, v_prec_571_);
if (v___x_594_ == 0)
{
lean_object* v___x_595_; 
v___x_595_ = lean_obj_once(&l_Lean_instReprLevel_repr___closed__2, &l_Lean_instReprLevel_repr___closed__2_once, _init_l_Lean_instReprLevel_repr___closed__2);
v___y_586_ = v___x_595_;
goto v___jp_585_;
}
else
{
lean_object* v___x_596_; 
v___x_596_ = lean_obj_once(&l_Lean_instReprLevel_repr___closed__3, &l_Lean_instReprLevel_repr___closed__3_once, _init_l_Lean_instReprLevel_repr___closed__3);
v___y_586_ = v___x_596_;
goto v___jp_585_;
}
v___jp_585_:
{
lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; uint8_t v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; 
v___x_587_ = ((lean_object*)(l_Lean_instReprLevel_repr___closed__6));
v___x_588_ = l_Lean_instReprLevel_repr(v_a_583_, v___x_584_);
v___x_589_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_589_, 0, v___x_587_);
lean_ctor_set(v___x_589_, 1, v___x_588_);
lean_inc(v___y_586_);
v___x_590_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_590_, 0, v___y_586_);
lean_ctor_set(v___x_590_, 1, v___x_589_);
v___x_591_ = 0;
v___x_592_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_592_, 0, v___x_590_);
lean_ctor_set_uint8(v___x_592_, sizeof(void*)*1, v___x_591_);
v___x_593_ = l_Repr_addAppParen(v___x_592_, v_prec_571_);
return v___x_593_;
}
}
case 2:
{
lean_object* v_a_597_; lean_object* v_a_598_; lean_object* v___x_599_; lean_object* v___y_601_; uint8_t v___x_613_; 
v_a_597_ = lean_ctor_get(v_x_570_, 0);
lean_inc(v_a_597_);
v_a_598_ = lean_ctor_get(v_x_570_, 1);
lean_inc(v_a_598_);
lean_dec_ref_known(v_x_570_, 2);
v___x_599_ = lean_unsigned_to_nat(1024u);
v___x_613_ = lean_nat_dec_le(v___x_599_, v_prec_571_);
if (v___x_613_ == 0)
{
lean_object* v___x_614_; 
v___x_614_ = lean_obj_once(&l_Lean_instReprLevel_repr___closed__2, &l_Lean_instReprLevel_repr___closed__2_once, _init_l_Lean_instReprLevel_repr___closed__2);
v___y_601_ = v___x_614_;
goto v___jp_600_;
}
else
{
lean_object* v___x_615_; 
v___x_615_ = lean_obj_once(&l_Lean_instReprLevel_repr___closed__3, &l_Lean_instReprLevel_repr___closed__3_once, _init_l_Lean_instReprLevel_repr___closed__3);
v___y_601_ = v___x_615_;
goto v___jp_600_;
}
v___jp_600_:
{
lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; uint8_t v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; 
v___x_602_ = lean_box(1);
v___x_603_ = ((lean_object*)(l_Lean_instReprLevel_repr___closed__9));
v___x_604_ = l_Lean_instReprLevel_repr(v_a_597_, v___x_599_);
v___x_605_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_605_, 0, v___x_603_);
lean_ctor_set(v___x_605_, 1, v___x_604_);
v___x_606_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_606_, 0, v___x_605_);
lean_ctor_set(v___x_606_, 1, v___x_602_);
v___x_607_ = l_Lean_instReprLevel_repr(v_a_598_, v___x_599_);
v___x_608_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_608_, 0, v___x_606_);
lean_ctor_set(v___x_608_, 1, v___x_607_);
lean_inc(v___y_601_);
v___x_609_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_609_, 0, v___y_601_);
lean_ctor_set(v___x_609_, 1, v___x_608_);
v___x_610_ = 0;
v___x_611_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_611_, 0, v___x_609_);
lean_ctor_set_uint8(v___x_611_, sizeof(void*)*1, v___x_610_);
v___x_612_ = l_Repr_addAppParen(v___x_611_, v_prec_571_);
return v___x_612_;
}
}
case 3:
{
lean_object* v_a_616_; lean_object* v_a_617_; lean_object* v___x_618_; lean_object* v___y_620_; uint8_t v___x_632_; 
v_a_616_ = lean_ctor_get(v_x_570_, 0);
lean_inc(v_a_616_);
v_a_617_ = lean_ctor_get(v_x_570_, 1);
lean_inc(v_a_617_);
lean_dec_ref_known(v_x_570_, 2);
v___x_618_ = lean_unsigned_to_nat(1024u);
v___x_632_ = lean_nat_dec_le(v___x_618_, v_prec_571_);
if (v___x_632_ == 0)
{
lean_object* v___x_633_; 
v___x_633_ = lean_obj_once(&l_Lean_instReprLevel_repr___closed__2, &l_Lean_instReprLevel_repr___closed__2_once, _init_l_Lean_instReprLevel_repr___closed__2);
v___y_620_ = v___x_633_;
goto v___jp_619_;
}
else
{
lean_object* v___x_634_; 
v___x_634_ = lean_obj_once(&l_Lean_instReprLevel_repr___closed__3, &l_Lean_instReprLevel_repr___closed__3_once, _init_l_Lean_instReprLevel_repr___closed__3);
v___y_620_ = v___x_634_;
goto v___jp_619_;
}
v___jp_619_:
{
lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; uint8_t v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; 
v___x_621_ = lean_box(1);
v___x_622_ = ((lean_object*)(l_Lean_instReprLevel_repr___closed__12));
v___x_623_ = l_Lean_instReprLevel_repr(v_a_616_, v___x_618_);
v___x_624_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_624_, 0, v___x_622_);
lean_ctor_set(v___x_624_, 1, v___x_623_);
v___x_625_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_625_, 0, v___x_624_);
lean_ctor_set(v___x_625_, 1, v___x_621_);
v___x_626_ = l_Lean_instReprLevel_repr(v_a_617_, v___x_618_);
v___x_627_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_627_, 0, v___x_625_);
lean_ctor_set(v___x_627_, 1, v___x_626_);
lean_inc(v___y_620_);
v___x_628_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_628_, 0, v___y_620_);
lean_ctor_set(v___x_628_, 1, v___x_627_);
v___x_629_ = 0;
v___x_630_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_630_, 0, v___x_628_);
lean_ctor_set_uint8(v___x_630_, sizeof(void*)*1, v___x_629_);
v___x_631_ = l_Repr_addAppParen(v___x_630_, v_prec_571_);
return v___x_631_;
}
}
case 4:
{
lean_object* v_a_635_; lean_object* v___y_637_; lean_object* v___x_646_; uint8_t v___x_647_; 
v_a_635_ = lean_ctor_get(v_x_570_, 0);
lean_inc(v_a_635_);
lean_dec_ref_known(v_x_570_, 1);
v___x_646_ = lean_unsigned_to_nat(1024u);
v___x_647_ = lean_nat_dec_le(v___x_646_, v_prec_571_);
if (v___x_647_ == 0)
{
lean_object* v___x_648_; 
v___x_648_ = lean_obj_once(&l_Lean_instReprLevel_repr___closed__2, &l_Lean_instReprLevel_repr___closed__2_once, _init_l_Lean_instReprLevel_repr___closed__2);
v___y_637_ = v___x_648_;
goto v___jp_636_;
}
else
{
lean_object* v___x_649_; 
v___x_649_ = lean_obj_once(&l_Lean_instReprLevel_repr___closed__3, &l_Lean_instReprLevel_repr___closed__3_once, _init_l_Lean_instReprLevel_repr___closed__3);
v___y_637_ = v___x_649_;
goto v___jp_636_;
}
v___jp_636_:
{
lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; uint8_t v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; 
v___x_638_ = ((lean_object*)(l_Lean_instReprLevel_repr___closed__15));
v___x_639_ = lean_unsigned_to_nat(1024u);
v___x_640_ = l_Lean_Name_reprPrec(v_a_635_, v___x_639_);
v___x_641_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_641_, 0, v___x_638_);
lean_ctor_set(v___x_641_, 1, v___x_640_);
lean_inc(v___y_637_);
v___x_642_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_642_, 0, v___y_637_);
lean_ctor_set(v___x_642_, 1, v___x_641_);
v___x_643_ = 0;
v___x_644_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_644_, 0, v___x_642_);
lean_ctor_set_uint8(v___x_644_, sizeof(void*)*1, v___x_643_);
v___x_645_ = l_Repr_addAppParen(v___x_644_, v_prec_571_);
return v___x_645_;
}
}
default: 
{
lean_object* v_a_650_; lean_object* v___y_652_; lean_object* v___x_661_; uint8_t v___x_662_; 
v_a_650_ = lean_ctor_get(v_x_570_, 0);
lean_inc(v_a_650_);
lean_dec_ref_known(v_x_570_, 1);
v___x_661_ = lean_unsigned_to_nat(1024u);
v___x_662_ = lean_nat_dec_le(v___x_661_, v_prec_571_);
if (v___x_662_ == 0)
{
lean_object* v___x_663_; 
v___x_663_ = lean_obj_once(&l_Lean_instReprLevel_repr___closed__2, &l_Lean_instReprLevel_repr___closed__2_once, _init_l_Lean_instReprLevel_repr___closed__2);
v___y_652_ = v___x_663_;
goto v___jp_651_;
}
else
{
lean_object* v___x_664_; 
v___x_664_ = lean_obj_once(&l_Lean_instReprLevel_repr___closed__3, &l_Lean_instReprLevel_repr___closed__3_once, _init_l_Lean_instReprLevel_repr___closed__3);
v___y_652_ = v___x_664_;
goto v___jp_651_;
}
v___jp_651_:
{
lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; uint8_t v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; 
v___x_653_ = ((lean_object*)(l_Lean_instReprLevel_repr___closed__18));
v___x_654_ = lean_unsigned_to_nat(1024u);
v___x_655_ = l_Lean_Name_reprPrec(v_a_650_, v___x_654_);
v___x_656_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_656_, 0, v___x_653_);
lean_ctor_set(v___x_656_, 1, v___x_655_);
lean_inc(v___y_652_);
v___x_657_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_657_, 0, v___y_652_);
lean_ctor_set(v___x_657_, 1, v___x_656_);
v___x_658_ = 0;
v___x_659_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_659_, 0, v___x_657_);
lean_ctor_set_uint8(v___x_659_, sizeof(void*)*1, v___x_658_);
v___x_660_ = l_Repr_addAppParen(v___x_659_, v_prec_571_);
return v___x_660_;
}
}
}
v___jp_572_:
{
lean_object* v___x_574_; lean_object* v___x_575_; uint8_t v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; 
v___x_574_ = ((lean_object*)(l_Lean_instReprLevel_repr___closed__1));
lean_inc(v___y_573_);
v___x_575_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_575_, 0, v___y_573_);
lean_ctor_set(v___x_575_, 1, v___x_574_);
v___x_576_ = 0;
v___x_577_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_577_, 0, v___x_575_);
lean_ctor_set_uint8(v___x_577_, sizeof(void*)*1, v___x_576_);
v___x_578_ = l_Repr_addAppParen(v___x_577_, v_prec_571_);
return v___x_578_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instReprLevel_repr___boxed(lean_object* v_x_665_, lean_object* v_prec_666_){
_start:
{
lean_object* v_res_667_; 
v_res_667_ = l_Lean_instReprLevel_repr(v_x_665_, v_prec_666_);
lean_dec(v_prec_666_);
return v_res_667_;
}
}
LEAN_EXPORT uint64_t l_Lean_Level_hash(lean_object* v_u_670_){
_start:
{
uint64_t v___x_671_; uint64_t v___x_672_; 
v___x_671_ = l_Lean_Level_data___override(v_u_670_);
v___x_672_ = l_Lean_Level_Data_hash(v___x_671_);
return v___x_672_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_hash___boxed(lean_object* v_u_673_){
_start:
{
uint64_t v_res_674_; lean_object* v_r_675_; 
v_res_674_ = l_Lean_Level_hash(v_u_673_);
lean_dec(v_u_673_);
v_r_675_ = lean_box_uint64(v_res_674_);
return v_r_675_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_depth(lean_object* v_u_678_){
_start:
{
uint64_t v___x_679_; uint32_t v___x_680_; lean_object* v___x_681_; 
v___x_679_ = l_Lean_Level_data___override(v_u_678_);
v___x_680_ = l_Lean_Level_Data_depth(v___x_679_);
v___x_681_ = lean_uint32_to_nat(v___x_680_);
return v___x_681_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_depth___boxed(lean_object* v_u_682_){
_start:
{
lean_object* v_res_683_; 
v_res_683_ = l_Lean_Level_depth(v_u_682_);
lean_dec(v_u_682_);
return v_res_683_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_hasMVar(lean_object* v_u_684_){
_start:
{
uint64_t v___x_685_; uint8_t v___x_686_; 
v___x_685_ = l_Lean_Level_data___override(v_u_684_);
v___x_686_ = l_Lean_Level_Data_hasMVar(v___x_685_);
return v___x_686_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_hasMVar___boxed(lean_object* v_u_687_){
_start:
{
uint8_t v_res_688_; lean_object* v_r_689_; 
v_res_688_ = l_Lean_Level_hasMVar(v_u_687_);
lean_dec(v_u_687_);
v_r_689_ = lean_box(v_res_688_);
return v_r_689_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_hasParam(lean_object* v_u_690_){
_start:
{
uint64_t v___x_691_; uint8_t v___x_692_; 
v___x_691_ = l_Lean_Level_data___override(v_u_690_);
v___x_692_ = l_Lean_Level_Data_hasParam(v___x_691_);
return v___x_692_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_hasParam___boxed(lean_object* v_u_693_){
_start:
{
uint8_t v_res_694_; lean_object* v_r_695_; 
v_res_694_ = l_Lean_Level_hasParam(v_u_693_);
lean_dec(v_u_693_);
v_r_695_ = lean_box(v_res_694_);
return v_r_695_;
}
}
LEAN_EXPORT uint32_t lean_level_hash(lean_object* v_u_696_){
_start:
{
uint64_t v___x_697_; uint32_t v___x_698_; 
v___x_697_ = l_Lean_Level_hash(v_u_696_);
lean_dec(v_u_696_);
v___x_698_ = lean_uint64_to_uint32(v___x_697_);
return v___x_698_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_hashEx___boxed(lean_object* v_u_699_){
_start:
{
uint32_t v_res_700_; lean_object* v_r_701_; 
v_res_700_ = lean_level_hash(v_u_699_);
v_r_701_ = lean_box_uint32(v_res_700_);
return v_r_701_;
}
}
LEAN_EXPORT uint8_t lean_level_has_mvar(lean_object* v_u_702_){
_start:
{
uint8_t v___x_703_; 
v___x_703_ = l_Lean_Level_hasMVar(v_u_702_);
lean_dec(v_u_702_);
return v___x_703_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_hasMVarEx___boxed(lean_object* v_u_704_){
_start:
{
uint8_t v_res_705_; lean_object* v_r_706_; 
v_res_705_ = lean_level_has_mvar(v_u_704_);
v_r_706_ = lean_box(v_res_705_);
return v_r_706_;
}
}
LEAN_EXPORT uint8_t lean_level_has_param(lean_object* v_u_707_){
_start:
{
uint8_t v___x_708_; 
v___x_708_ = l_Lean_Level_hasParam(v_u_707_);
lean_dec(v_u_707_);
return v___x_708_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_hasParamEx___boxed(lean_object* v_u_709_){
_start:
{
uint8_t v_res_710_; lean_object* v_r_711_; 
v_res_710_ = lean_level_has_param(v_u_709_);
v_r_711_ = lean_box(v_res_710_);
return v_r_711_;
}
}
LEAN_EXPORT uint32_t lean_level_depth(lean_object* v_u_712_){
_start:
{
uint64_t v___x_713_; uint32_t v___x_714_; 
v___x_713_ = l_Lean_Level_data___override(v_u_712_);
lean_dec(v_u_712_);
v___x_714_ = l_Lean_Level_Data_depth(v___x_713_);
return v___x_714_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_depthEx___boxed(lean_object* v_u_715_){
_start:
{
uint32_t v_res_716_; lean_object* v_r_717_; 
v_res_716_ = lean_level_depth(v_u_715_);
v_r_717_ = lean_box_uint32(v_res_716_);
return v_r_717_;
}
}
static lean_object* _init_l_Lean_levelZero(void){
_start:
{
lean_object* v___x_718_; 
v___x_718_ = lean_box(0);
return v___x_718_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLevelMVar(lean_object* v_mvarId_719_){
_start:
{
lean_object* v___x_720_; 
v___x_720_ = l_Lean_Level_mvar___override(v_mvarId_719_);
return v___x_720_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLevelParam(lean_object* v_name_721_){
_start:
{
lean_object* v___x_722_; 
v___x_722_ = l_Lean_Level_param___override(v_name_721_);
return v___x_722_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLevelSucc(lean_object* v_u_723_){
_start:
{
lean_object* v___x_724_; 
v___x_724_ = l_Lean_Level_succ___override(v_u_723_);
return v___x_724_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLevelMax(lean_object* v_u_725_, lean_object* v_v_726_){
_start:
{
lean_object* v___x_727_; 
v___x_727_ = l_Lean_Level_max___override(v_u_725_, v_v_726_);
return v___x_727_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLevelIMax(lean_object* v_u_728_, lean_object* v_v_729_){
_start:
{
lean_object* v___x_730_; 
v___x_730_ = l_Lean_Level_imax___override(v_u_728_, v_v_729_);
return v___x_730_;
}
}
static lean_object* _init_l_Lean_Level_one___closed__0(void){
_start:
{
lean_object* v___x_731_; lean_object* v___x_732_; 
v___x_731_ = lean_box(0);
v___x_732_ = l_Lean_Level_succ___override(v___x_731_);
return v___x_732_;
}
}
static lean_object* _init_l_Lean_Level_one(void){
_start:
{
lean_object* v___x_733_; 
v___x_733_ = lean_obj_once(&l_Lean_Level_one___closed__0, &l_Lean_Level_one___closed__0_once, _init_l_Lean_Level_one___closed__0);
return v___x_733_;
}
}
static lean_object* _init_l_Lean_levelOne(void){
_start:
{
lean_object* v___x_734_; 
v___x_734_ = lean_obj_once(&l_Lean_Level_one___closed__0, &l_Lean_Level_one___closed__0_once, _init_l_Lean_Level_one___closed__0);
return v___x_734_;
}
}
LEAN_EXPORT lean_object* lean_level_mk_zero(lean_object* v_x_735_){
_start:
{
lean_object* v___x_736_; 
v___x_736_ = lean_box(0);
return v___x_736_;
}
}
LEAN_EXPORT lean_object* lean_level_mk_succ(lean_object* v_u_737_){
_start:
{
lean_object* v___x_738_; 
v___x_738_ = l_Lean_Level_succ___override(v_u_737_);
return v___x_738_;
}
}
LEAN_EXPORT lean_object* lean_level_mk_mvar(lean_object* v_mvarId_739_){
_start:
{
lean_object* v___x_740_; 
v___x_740_ = l_Lean_Level_mvar___override(v_mvarId_739_);
return v___x_740_;
}
}
LEAN_EXPORT lean_object* lean_level_mk_param(lean_object* v_name_741_){
_start:
{
lean_object* v___x_742_; 
v___x_742_ = l_Lean_Level_param___override(v_name_741_);
return v___x_742_;
}
}
LEAN_EXPORT lean_object* lean_level_mk_max(lean_object* v_u_743_, lean_object* v_v_744_){
_start:
{
lean_object* v___x_745_; 
v___x_745_ = l_Lean_Level_max___override(v_u_743_, v_v_744_);
return v___x_745_;
}
}
LEAN_EXPORT lean_object* lean_level_mk_imax(lean_object* v_u_746_, lean_object* v_v_747_){
_start:
{
lean_object* v___x_748_; 
v___x_748_ = l_Lean_Level_imax___override(v_u_746_, v_v_747_);
return v___x_748_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_isZero(lean_object* v_x_749_){
_start:
{
if (lean_obj_tag(v_x_749_) == 0)
{
uint8_t v___x_750_; 
v___x_750_ = 1;
return v___x_750_;
}
else
{
uint8_t v___x_751_; 
v___x_751_ = 0;
return v___x_751_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_isZero___boxed(lean_object* v_x_752_){
_start:
{
uint8_t v_res_753_; lean_object* v_r_754_; 
v_res_753_ = l_Lean_Level_isZero(v_x_752_);
lean_dec(v_x_752_);
v_r_754_ = lean_box(v_res_753_);
return v_r_754_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_isSucc(lean_object* v_x_755_){
_start:
{
if (lean_obj_tag(v_x_755_) == 1)
{
uint8_t v___x_756_; 
v___x_756_ = 1;
return v___x_756_;
}
else
{
uint8_t v___x_757_; 
v___x_757_ = 0;
return v___x_757_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_isSucc___boxed(lean_object* v_x_758_){
_start:
{
uint8_t v_res_759_; lean_object* v_r_760_; 
v_res_759_ = l_Lean_Level_isSucc(v_x_758_);
lean_dec(v_x_758_);
v_r_760_ = lean_box(v_res_759_);
return v_r_760_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_isMax(lean_object* v_x_761_){
_start:
{
if (lean_obj_tag(v_x_761_) == 2)
{
uint8_t v___x_762_; 
v___x_762_ = 1;
return v___x_762_;
}
else
{
uint8_t v___x_763_; 
v___x_763_ = 0;
return v___x_763_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_isMax___boxed(lean_object* v_x_764_){
_start:
{
uint8_t v_res_765_; lean_object* v_r_766_; 
v_res_765_ = l_Lean_Level_isMax(v_x_764_);
lean_dec(v_x_764_);
v_r_766_ = lean_box(v_res_765_);
return v_r_766_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_isIMax(lean_object* v_x_767_){
_start:
{
if (lean_obj_tag(v_x_767_) == 3)
{
uint8_t v___x_768_; 
v___x_768_ = 1;
return v___x_768_;
}
else
{
uint8_t v___x_769_; 
v___x_769_ = 0;
return v___x_769_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_isIMax___boxed(lean_object* v_x_770_){
_start:
{
uint8_t v_res_771_; lean_object* v_r_772_; 
v_res_771_ = l_Lean_Level_isIMax(v_x_770_);
lean_dec(v_x_770_);
v_r_772_ = lean_box(v_res_771_);
return v_r_772_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_isMaxIMax(lean_object* v_x_773_){
_start:
{
switch(lean_obj_tag(v_x_773_))
{
case 2:
{
uint8_t v___x_774_; 
v___x_774_ = 1;
return v___x_774_;
}
case 3:
{
uint8_t v___x_775_; 
v___x_775_ = 1;
return v___x_775_;
}
default: 
{
uint8_t v___x_776_; 
v___x_776_ = 0;
return v___x_776_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_isMaxIMax___boxed(lean_object* v_x_777_){
_start:
{
uint8_t v_res_778_; lean_object* v_r_779_; 
v_res_778_ = l_Lean_Level_isMaxIMax(v_x_777_);
lean_dec(v_x_777_);
v_r_779_ = lean_box(v_res_778_);
return v_r_779_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_isParam(lean_object* v_x_780_){
_start:
{
if (lean_obj_tag(v_x_780_) == 4)
{
uint8_t v___x_781_; 
v___x_781_ = 1;
return v___x_781_;
}
else
{
uint8_t v___x_782_; 
v___x_782_ = 0;
return v___x_782_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_isParam___boxed(lean_object* v_x_783_){
_start:
{
uint8_t v_res_784_; lean_object* v_r_785_; 
v_res_784_ = l_Lean_Level_isParam(v_x_783_);
lean_dec(v_x_783_);
v_r_785_ = lean_box(v_res_784_);
return v_r_785_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_isMVar(lean_object* v_x_786_){
_start:
{
if (lean_obj_tag(v_x_786_) == 5)
{
uint8_t v___x_787_; 
v___x_787_ = 1;
return v___x_787_;
}
else
{
uint8_t v___x_788_; 
v___x_788_ = 0;
return v___x_788_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_isMVar___boxed(lean_object* v_x_789_){
_start:
{
uint8_t v_res_790_; lean_object* v_r_791_; 
v_res_790_ = l_Lean_Level_isMVar(v_x_789_);
lean_dec(v_x_789_);
v_r_791_ = lean_box(v_res_790_);
return v_r_791_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Level_mvarId_x21_spec__0(lean_object* v_msg_792_){
_start:
{
lean_object* v___x_793_; lean_object* v___x_794_; 
v___x_793_ = lean_box(0);
v___x_794_ = lean_panic_fn_borrowed(v___x_793_, v_msg_792_);
return v___x_794_;
}
}
static lean_object* _init_l_Lean_Level_mvarId_x21___closed__3(void){
_start:
{
lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; 
v___x_798_ = ((lean_object*)(l_Lean_Level_mvarId_x21___closed__2));
v___x_799_ = lean_unsigned_to_nat(19u);
v___x_800_ = lean_unsigned_to_nat(196u);
v___x_801_ = ((lean_object*)(l_Lean_Level_mvarId_x21___closed__1));
v___x_802_ = ((lean_object*)(l_Lean_Level_mvarId_x21___closed__0));
v___x_803_ = l_mkPanicMessageWithDecl(v___x_802_, v___x_801_, v___x_800_, v___x_799_, v___x_798_);
return v___x_803_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_mvarId_x21(lean_object* v_x_804_){
_start:
{
if (lean_obj_tag(v_x_804_) == 5)
{
lean_object* v_a_805_; 
v_a_805_ = lean_ctor_get(v_x_804_, 0);
lean_inc(v_a_805_);
return v_a_805_;
}
else
{
lean_object* v___x_806_; lean_object* v___x_807_; 
v___x_806_ = lean_obj_once(&l_Lean_Level_mvarId_x21___closed__3, &l_Lean_Level_mvarId_x21___closed__3_once, _init_l_Lean_Level_mvarId_x21___closed__3);
v___x_807_ = l_panic___at___00Lean_Level_mvarId_x21_spec__0(v___x_806_);
return v___x_807_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_mvarId_x21___boxed(lean_object* v_x_808_){
_start:
{
lean_object* v_res_809_; 
v_res_809_ = l_Lean_Level_mvarId_x21(v_x_808_);
lean_dec(v_x_808_);
return v_res_809_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_isNeverZero(lean_object* v_x_810_){
_start:
{
switch(lean_obj_tag(v_x_810_))
{
case 0:
{
uint8_t v___x_811_; 
v___x_811_ = 0;
return v___x_811_;
}
case 1:
{
uint8_t v___x_812_; 
v___x_812_ = 1;
return v___x_812_;
}
case 2:
{
lean_object* v_a_813_; lean_object* v_a_814_; uint8_t v___x_815_; 
v_a_813_ = lean_ctor_get(v_x_810_, 0);
v_a_814_ = lean_ctor_get(v_x_810_, 1);
v___x_815_ = l_Lean_Level_isNeverZero(v_a_813_);
if (v___x_815_ == 0)
{
v_x_810_ = v_a_814_;
goto _start;
}
else
{
return v___x_815_;
}
}
case 3:
{
lean_object* v_a_817_; 
v_a_817_ = lean_ctor_get(v_x_810_, 1);
v_x_810_ = v_a_817_;
goto _start;
}
default: 
{
uint8_t v___x_819_; 
v___x_819_ = 0;
return v___x_819_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_isNeverZero___boxed(lean_object* v_x_820_){
_start:
{
uint8_t v_res_821_; lean_object* v_r_822_; 
v_res_821_ = l_Lean_Level_isNeverZero(v_x_820_);
lean_dec(v_x_820_);
v_r_822_ = lean_box(v_res_821_);
return v_r_822_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_isAlwaysZero(lean_object* v_x_823_){
_start:
{
switch(lean_obj_tag(v_x_823_))
{
case 0:
{
uint8_t v___x_824_; 
v___x_824_ = 1;
return v___x_824_;
}
case 2:
{
lean_object* v_a_825_; lean_object* v_a_826_; uint8_t v___x_827_; 
v_a_825_ = lean_ctor_get(v_x_823_, 0);
v_a_826_ = lean_ctor_get(v_x_823_, 1);
v___x_827_ = l_Lean_Level_isAlwaysZero(v_a_825_);
if (v___x_827_ == 0)
{
return v___x_827_;
}
else
{
v_x_823_ = v_a_826_;
goto _start;
}
}
case 3:
{
lean_object* v_a_829_; 
v_a_829_ = lean_ctor_get(v_x_823_, 1);
v_x_823_ = v_a_829_;
goto _start;
}
default: 
{
uint8_t v___x_831_; 
v___x_831_ = 0;
return v___x_831_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_isAlwaysZero___boxed(lean_object* v_x_832_){
_start:
{
uint8_t v_res_833_; lean_object* v_r_834_; 
v_res_833_ = l_Lean_Level_isAlwaysZero(v_x_832_);
lean_dec(v_x_832_);
v_r_834_ = lean_box(v_res_833_);
return v_r_834_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_ofNat(lean_object* v_x_835_){
_start:
{
lean_object* v_zero_836_; uint8_t v_isZero_837_; 
v_zero_836_ = lean_unsigned_to_nat(0u);
v_isZero_837_ = lean_nat_dec_eq(v_x_835_, v_zero_836_);
if (v_isZero_837_ == 1)
{
lean_object* v___x_838_; 
v___x_838_ = lean_box(0);
return v___x_838_;
}
else
{
lean_object* v_one_839_; lean_object* v_n_840_; lean_object* v___x_841_; lean_object* v___x_842_; 
v_one_839_ = lean_unsigned_to_nat(1u);
v_n_840_ = lean_nat_sub(v_x_835_, v_one_839_);
v___x_841_ = l_Lean_Level_ofNat(v_n_840_);
lean_dec(v_n_840_);
v___x_842_ = l_Lean_Level_succ___override(v___x_841_);
return v___x_842_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_ofNat___boxed(lean_object* v_x_843_){
_start:
{
lean_object* v_res_844_; 
v_res_844_ = l_Lean_Level_ofNat(v_x_843_);
lean_dec(v_x_843_);
return v_res_844_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_instOfNat(lean_object* v_n_845_){
_start:
{
lean_object* v___x_846_; 
v___x_846_ = l_Lean_Level_ofNat(v_n_845_);
return v___x_846_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_instOfNat___boxed(lean_object* v_n_847_){
_start:
{
lean_object* v_res_848_; 
v_res_848_ = l_Lean_Level_instOfNat(v_n_847_);
lean_dec(v_n_847_);
return v_res_848_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_addOffsetAux(lean_object* v_x_849_, lean_object* v_x_850_){
_start:
{
lean_object* v_zero_851_; uint8_t v_isZero_852_; 
v_zero_851_ = lean_unsigned_to_nat(0u);
v_isZero_852_ = lean_nat_dec_eq(v_x_849_, v_zero_851_);
if (v_isZero_852_ == 1)
{
lean_dec(v_x_849_);
return v_x_850_;
}
else
{
lean_object* v_one_853_; lean_object* v_n_854_; lean_object* v___x_855_; 
v_one_853_ = lean_unsigned_to_nat(1u);
v_n_854_ = lean_nat_sub(v_x_849_, v_one_853_);
lean_dec(v_x_849_);
v___x_855_ = l_Lean_Level_succ___override(v_x_850_);
v_x_849_ = v_n_854_;
v_x_850_ = v___x_855_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_addOffset(lean_object* v_u_857_, lean_object* v_n_858_){
_start:
{
lean_object* v___x_859_; 
v___x_859_ = l_Lean_Level_addOffsetAux(v_n_858_, v_u_857_);
return v___x_859_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_isExplicit(lean_object* v_x_860_){
_start:
{
switch(lean_obj_tag(v_x_860_))
{
case 0:
{
uint8_t v___x_861_; 
v___x_861_ = 1;
return v___x_861_;
}
case 1:
{
lean_object* v_a_862_; uint8_t v___y_864_; uint8_t v___x_866_; uint8_t v___x_867_; 
v_a_862_ = lean_ctor_get(v_x_860_, 0);
v___x_866_ = l_Lean_Level_hasMVar(v_a_862_);
v___x_867_ = lean_bool_not(v___x_866_);
if (v___x_867_ == 0)
{
v___y_864_ = v___x_867_;
goto v___jp_863_;
}
else
{
uint8_t v___x_868_; uint8_t v___x_869_; 
v___x_868_ = l_Lean_Level_hasParam(v_a_862_);
v___x_869_ = lean_bool_not(v___x_868_);
v___y_864_ = v___x_869_;
goto v___jp_863_;
}
v___jp_863_:
{
if (v___y_864_ == 0)
{
return v___y_864_;
}
else
{
v_x_860_ = v_a_862_;
goto _start;
}
}
}
default: 
{
uint8_t v___x_870_; 
v___x_870_ = 0;
return v___x_870_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_isExplicit___boxed(lean_object* v_x_871_){
_start:
{
uint8_t v_res_872_; lean_object* v_r_873_; 
v_res_872_ = l_Lean_Level_isExplicit(v_x_871_);
lean_dec(v_x_871_);
v_r_873_ = lean_box(v_res_872_);
return v_r_873_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_getOffsetAux(lean_object* v_x_874_, lean_object* v_x_875_){
_start:
{
if (lean_obj_tag(v_x_874_) == 1)
{
lean_object* v_a_876_; lean_object* v___x_877_; lean_object* v___x_878_; 
v_a_876_ = lean_ctor_get(v_x_874_, 0);
v___x_877_ = lean_unsigned_to_nat(1u);
v___x_878_ = lean_nat_add(v_x_875_, v___x_877_);
lean_dec(v_x_875_);
v_x_874_ = v_a_876_;
v_x_875_ = v___x_878_;
goto _start;
}
else
{
return v_x_875_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_getOffsetAux___boxed(lean_object* v_x_880_, lean_object* v_x_881_){
_start:
{
lean_object* v_res_882_; 
v_res_882_ = l_Lean_Level_getOffsetAux(v_x_880_, v_x_881_);
lean_dec(v_x_880_);
return v_res_882_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_getOffset(lean_object* v_lvl_883_){
_start:
{
lean_object* v___x_884_; lean_object* v___x_885_; 
v___x_884_ = lean_unsigned_to_nat(0u);
v___x_885_ = l_Lean_Level_getOffsetAux(v_lvl_883_, v___x_884_);
return v___x_885_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_getOffset___boxed(lean_object* v_lvl_886_){
_start:
{
lean_object* v_res_887_; 
v_res_887_ = l_Lean_Level_getOffset(v_lvl_886_);
lean_dec(v_lvl_886_);
return v_res_887_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_getLevelOffset(lean_object* v_x_888_){
_start:
{
if (lean_obj_tag(v_x_888_) == 1)
{
lean_object* v_a_889_; 
v_a_889_ = lean_ctor_get(v_x_888_, 0);
v_x_888_ = v_a_889_;
goto _start;
}
else
{
lean_inc(v_x_888_);
return v_x_888_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_getLevelOffset___boxed(lean_object* v_x_891_){
_start:
{
lean_object* v_res_892_; 
v_res_892_ = l_Lean_Level_getLevelOffset(v_x_891_);
lean_dec(v_x_891_);
return v_res_892_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_toNat(lean_object* v_lvl_893_){
_start:
{
lean_object* v___x_894_; 
v___x_894_ = l_Lean_Level_getLevelOffset(v_lvl_893_);
if (lean_obj_tag(v___x_894_) == 0)
{
lean_object* v___x_895_; lean_object* v___x_896_; 
v___x_895_ = l_Lean_Level_getOffset(v_lvl_893_);
v___x_896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_896_, 0, v___x_895_);
return v___x_896_;
}
else
{
lean_object* v___x_897_; 
lean_dec(v___x_894_);
v___x_897_ = lean_box(0);
return v___x_897_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_toNat___boxed(lean_object* v_lvl_898_){
_start:
{
lean_object* v_res_899_; 
v_res_899_ = l_Lean_Level_toNat(v_lvl_898_);
lean_dec(v_lvl_898_);
return v_res_899_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_beq___boxed(lean_object* v_a_902_, lean_object* v_b_903_){
_start:
{
uint8_t v_res_904_; lean_object* v_r_905_; 
v_res_904_ = lean_level_eq(v_a_902_, v_b_903_);
lean_dec(v_b_903_);
lean_dec(v_a_902_);
v_r_905_ = lean_box(v_res_904_);
return v_r_905_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_occurs(lean_object* v_x_908_, lean_object* v_x_909_){
_start:
{
switch(lean_obj_tag(v_x_909_))
{
case 1:
{
lean_object* v_a_910_; uint8_t v___x_911_; 
v_a_910_ = lean_ctor_get(v_x_909_, 0);
v___x_911_ = lean_level_eq(v_x_908_, v_x_909_);
if (v___x_911_ == 0)
{
v_x_909_ = v_a_910_;
goto _start;
}
else
{
return v___x_911_;
}
}
case 2:
{
lean_object* v_a_913_; lean_object* v_a_914_; uint8_t v___y_916_; uint8_t v___x_918_; 
v_a_913_ = lean_ctor_get(v_x_909_, 0);
v_a_914_ = lean_ctor_get(v_x_909_, 1);
v___x_918_ = lean_level_eq(v_x_908_, v_x_909_);
if (v___x_918_ == 0)
{
uint8_t v___x_919_; 
v___x_919_ = l_Lean_Level_occurs(v_x_908_, v_a_913_);
v___y_916_ = v___x_919_;
goto v___jp_915_;
}
else
{
v___y_916_ = v___x_918_;
goto v___jp_915_;
}
v___jp_915_:
{
if (v___y_916_ == 0)
{
v_x_909_ = v_a_914_;
goto _start;
}
else
{
return v___y_916_;
}
}
}
case 3:
{
lean_object* v_a_920_; lean_object* v_a_921_; uint8_t v___y_923_; uint8_t v___x_925_; 
v_a_920_ = lean_ctor_get(v_x_909_, 0);
v_a_921_ = lean_ctor_get(v_x_909_, 1);
v___x_925_ = lean_level_eq(v_x_908_, v_x_909_);
if (v___x_925_ == 0)
{
uint8_t v___x_926_; 
v___x_926_ = l_Lean_Level_occurs(v_x_908_, v_a_920_);
v___y_923_ = v___x_926_;
goto v___jp_922_;
}
else
{
v___y_923_ = v___x_925_;
goto v___jp_922_;
}
v___jp_922_:
{
if (v___y_923_ == 0)
{
v_x_909_ = v_a_921_;
goto _start;
}
else
{
return v___y_923_;
}
}
}
default: 
{
uint8_t v___x_927_; 
v___x_927_ = lean_level_eq(v_x_908_, v_x_909_);
return v___x_927_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_occurs___boxed(lean_object* v_x_928_, lean_object* v_x_929_){
_start:
{
uint8_t v_res_930_; lean_object* v_r_931_; 
v_res_930_ = l_Lean_Level_occurs(v_x_928_, v_x_929_);
lean_dec(v_x_929_);
lean_dec(v_x_928_);
v_r_931_ = lean_box(v_res_930_);
return v_r_931_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_ctorToNat(lean_object* v_x_932_){
_start:
{
switch(lean_obj_tag(v_x_932_))
{
case 0:
{
lean_object* v___x_933_; 
v___x_933_ = lean_unsigned_to_nat(0u);
return v___x_933_;
}
case 1:
{
lean_object* v___x_934_; 
v___x_934_ = lean_unsigned_to_nat(3u);
return v___x_934_;
}
case 2:
{
lean_object* v___x_935_; 
v___x_935_ = lean_unsigned_to_nat(4u);
return v___x_935_;
}
case 3:
{
lean_object* v___x_936_; 
v___x_936_ = lean_unsigned_to_nat(5u);
return v___x_936_;
}
case 4:
{
lean_object* v___x_937_; 
v___x_937_ = lean_unsigned_to_nat(1u);
return v___x_937_;
}
default: 
{
lean_object* v___x_938_; 
v___x_938_ = lean_unsigned_to_nat(2u);
return v___x_938_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_ctorToNat___boxed(lean_object* v_x_939_){
_start:
{
lean_object* v_res_940_; 
v_res_940_ = l_Lean_Level_ctorToNat(v_x_939_);
lean_dec(v_x_939_);
return v_res_940_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_normLtAux(lean_object* v_x_941_, lean_object* v_x_942_, lean_object* v_x_943_, lean_object* v_x_944_){
_start:
{
lean_object* v_l_u2081_946_; lean_object* v_k_u2081_947_; lean_object* v_l_u2082_948_; lean_object* v_k_u2082_949_; lean_object* v_l_u2081_954_; lean_object* v_k_u2081_955_; lean_object* v_l_u2082_956_; lean_object* v_k_u2082_957_; 
switch(lean_obj_tag(v_x_941_))
{
case 1:
{
lean_object* v_a_963_; lean_object* v___x_964_; lean_object* v___x_965_; 
v_a_963_ = lean_ctor_get(v_x_941_, 0);
v___x_964_ = lean_unsigned_to_nat(1u);
v___x_965_ = lean_nat_add(v_x_942_, v___x_964_);
lean_dec(v_x_942_);
v_x_941_ = v_a_963_;
v_x_942_ = v___x_965_;
goto _start;
}
case 2:
{
switch(lean_obj_tag(v_x_943_))
{
case 1:
{
lean_object* v_a_967_; 
v_a_967_ = lean_ctor_get(v_x_943_, 0);
v_l_u2081_946_ = v_x_941_;
v_k_u2081_947_ = v_x_942_;
v_l_u2082_948_ = v_a_967_;
v_k_u2082_949_ = v_x_944_;
goto v___jp_945_;
}
case 2:
{
lean_object* v_a_968_; lean_object* v_a_969_; lean_object* v_a_970_; lean_object* v_a_971_; uint8_t v___x_972_; 
v_a_968_ = lean_ctor_get(v_x_941_, 0);
v_a_969_ = lean_ctor_get(v_x_941_, 1);
v_a_970_ = lean_ctor_get(v_x_943_, 0);
v_a_971_ = lean_ctor_get(v_x_943_, 1);
v___x_972_ = lean_level_eq(v_x_941_, v_x_943_);
if (v___x_972_ == 0)
{
uint8_t v___x_973_; uint8_t v___x_974_; 
lean_dec(v_x_944_);
lean_dec(v_x_942_);
v___x_973_ = lean_level_eq(v_a_968_, v_a_970_);
v___x_974_ = lean_bool_not(v___x_973_);
if (v___x_974_ == 0)
{
lean_object* v___x_975_; 
v___x_975_ = lean_unsigned_to_nat(0u);
v_x_941_ = v_a_969_;
v_x_942_ = v___x_975_;
v_x_943_ = v_a_971_;
v_x_944_ = v___x_975_;
goto _start;
}
else
{
lean_object* v___x_977_; 
v___x_977_ = lean_unsigned_to_nat(0u);
v_x_941_ = v_a_968_;
v_x_942_ = v___x_977_;
v_x_943_ = v_a_970_;
v_x_944_ = v___x_977_;
goto _start;
}
}
else
{
uint8_t v___x_979_; 
v___x_979_ = lean_nat_dec_lt(v_x_942_, v_x_944_);
lean_dec(v_x_944_);
lean_dec(v_x_942_);
return v___x_979_;
}
}
default: 
{
v_l_u2081_954_ = v_x_941_;
v_k_u2081_955_ = v_x_942_;
v_l_u2082_956_ = v_x_943_;
v_k_u2082_957_ = v_x_944_;
goto v___jp_953_;
}
}
}
case 3:
{
switch(lean_obj_tag(v_x_943_))
{
case 1:
{
lean_object* v_a_980_; 
v_a_980_ = lean_ctor_get(v_x_943_, 0);
v_l_u2081_946_ = v_x_941_;
v_k_u2081_947_ = v_x_942_;
v_l_u2082_948_ = v_a_980_;
v_k_u2082_949_ = v_x_944_;
goto v___jp_945_;
}
case 3:
{
lean_object* v_a_981_; lean_object* v_a_982_; lean_object* v_a_983_; lean_object* v_a_984_; uint8_t v___x_985_; 
v_a_981_ = lean_ctor_get(v_x_941_, 0);
v_a_982_ = lean_ctor_get(v_x_941_, 1);
v_a_983_ = lean_ctor_get(v_x_943_, 0);
v_a_984_ = lean_ctor_get(v_x_943_, 1);
v___x_985_ = lean_level_eq(v_x_941_, v_x_943_);
if (v___x_985_ == 0)
{
uint8_t v___x_986_; uint8_t v___x_987_; 
lean_dec(v_x_944_);
lean_dec(v_x_942_);
v___x_986_ = lean_level_eq(v_a_981_, v_a_983_);
v___x_987_ = lean_bool_not(v___x_986_);
if (v___x_987_ == 0)
{
lean_object* v___x_988_; 
v___x_988_ = lean_unsigned_to_nat(0u);
v_x_941_ = v_a_982_;
v_x_942_ = v___x_988_;
v_x_943_ = v_a_984_;
v_x_944_ = v___x_988_;
goto _start;
}
else
{
lean_object* v___x_990_; 
v___x_990_ = lean_unsigned_to_nat(0u);
v_x_941_ = v_a_981_;
v_x_942_ = v___x_990_;
v_x_943_ = v_a_983_;
v_x_944_ = v___x_990_;
goto _start;
}
}
else
{
uint8_t v___x_992_; 
v___x_992_ = lean_nat_dec_lt(v_x_942_, v_x_944_);
lean_dec(v_x_944_);
lean_dec(v_x_942_);
return v___x_992_;
}
}
default: 
{
v_l_u2081_954_ = v_x_941_;
v_k_u2081_955_ = v_x_942_;
v_l_u2082_956_ = v_x_943_;
v_k_u2082_957_ = v_x_944_;
goto v___jp_953_;
}
}
}
case 4:
{
switch(lean_obj_tag(v_x_943_))
{
case 1:
{
lean_object* v_a_993_; 
v_a_993_ = lean_ctor_get(v_x_943_, 0);
v_l_u2081_946_ = v_x_941_;
v_k_u2081_947_ = v_x_942_;
v_l_u2082_948_ = v_a_993_;
v_k_u2082_949_ = v_x_944_;
goto v___jp_945_;
}
case 4:
{
lean_object* v_a_994_; lean_object* v_a_995_; uint8_t v___x_996_; 
v_a_994_ = lean_ctor_get(v_x_941_, 0);
v_a_995_ = lean_ctor_get(v_x_943_, 0);
v___x_996_ = lean_name_eq(v_a_994_, v_a_995_);
if (v___x_996_ == 0)
{
uint8_t v___x_997_; 
lean_dec(v_x_944_);
lean_dec(v_x_942_);
v___x_997_ = l_Lean_Name_lt(v_a_994_, v_a_995_);
return v___x_997_;
}
else
{
uint8_t v___x_998_; 
v___x_998_ = lean_nat_dec_lt(v_x_942_, v_x_944_);
lean_dec(v_x_944_);
lean_dec(v_x_942_);
return v___x_998_;
}
}
default: 
{
v_l_u2081_954_ = v_x_941_;
v_k_u2081_955_ = v_x_942_;
v_l_u2082_956_ = v_x_943_;
v_k_u2082_957_ = v_x_944_;
goto v___jp_953_;
}
}
}
case 5:
{
switch(lean_obj_tag(v_x_943_))
{
case 1:
{
lean_object* v_a_999_; 
v_a_999_ = lean_ctor_get(v_x_943_, 0);
v_l_u2081_946_ = v_x_941_;
v_k_u2081_947_ = v_x_942_;
v_l_u2082_948_ = v_a_999_;
v_k_u2082_949_ = v_x_944_;
goto v___jp_945_;
}
case 5:
{
lean_object* v_a_1000_; lean_object* v_a_1001_; uint8_t v___x_1002_; 
v_a_1000_ = lean_ctor_get(v_x_941_, 0);
v_a_1001_ = lean_ctor_get(v_x_943_, 0);
v___x_1002_ = lean_name_eq(v_a_1000_, v_a_1001_);
if (v___x_1002_ == 0)
{
uint8_t v___x_1003_; 
lean_dec(v_x_944_);
lean_dec(v_x_942_);
v___x_1003_ = l_Lean_Name_lt(v_a_1000_, v_a_1001_);
return v___x_1003_;
}
else
{
uint8_t v___x_1004_; 
v___x_1004_ = lean_nat_dec_lt(v_x_942_, v_x_944_);
lean_dec(v_x_944_);
lean_dec(v_x_942_);
return v___x_1004_;
}
}
default: 
{
v_l_u2081_954_ = v_x_941_;
v_k_u2081_955_ = v_x_942_;
v_l_u2082_956_ = v_x_943_;
v_k_u2082_957_ = v_x_944_;
goto v___jp_953_;
}
}
}
default: 
{
if (lean_obj_tag(v_x_943_) == 1)
{
lean_object* v_a_1005_; 
v_a_1005_ = lean_ctor_get(v_x_943_, 0);
v_l_u2081_946_ = v_x_941_;
v_k_u2081_947_ = v_x_942_;
v_l_u2082_948_ = v_a_1005_;
v_k_u2082_949_ = v_x_944_;
goto v___jp_945_;
}
else
{
v_l_u2081_954_ = v_x_941_;
v_k_u2081_955_ = v_x_942_;
v_l_u2082_956_ = v_x_943_;
v_k_u2082_957_ = v_x_944_;
goto v___jp_953_;
}
}
}
v___jp_945_:
{
lean_object* v___x_950_; lean_object* v___x_951_; 
v___x_950_ = lean_unsigned_to_nat(1u);
v___x_951_ = lean_nat_add(v_k_u2082_949_, v___x_950_);
lean_dec(v_k_u2082_949_);
v_x_941_ = v_l_u2081_946_;
v_x_942_ = v_k_u2081_947_;
v_x_943_ = v_l_u2082_948_;
v_x_944_ = v___x_951_;
goto _start;
}
v___jp_953_:
{
uint8_t v___x_958_; 
v___x_958_ = lean_level_eq(v_l_u2081_954_, v_l_u2082_956_);
if (v___x_958_ == 0)
{
lean_object* v___x_959_; lean_object* v___x_960_; uint8_t v___x_961_; 
lean_dec(v_k_u2082_957_);
lean_dec(v_k_u2081_955_);
v___x_959_ = l_Lean_Level_ctorToNat(v_l_u2081_954_);
v___x_960_ = l_Lean_Level_ctorToNat(v_l_u2082_956_);
v___x_961_ = lean_nat_dec_lt(v___x_959_, v___x_960_);
lean_dec(v___x_960_);
lean_dec(v___x_959_);
return v___x_961_;
}
else
{
uint8_t v___x_962_; 
v___x_962_ = lean_nat_dec_lt(v_k_u2081_955_, v_k_u2082_957_);
lean_dec(v_k_u2082_957_);
lean_dec(v_k_u2081_955_);
return v___x_962_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_normLtAux___boxed(lean_object* v_x_1006_, lean_object* v_x_1007_, lean_object* v_x_1008_, lean_object* v_x_1009_){
_start:
{
uint8_t v_res_1010_; lean_object* v_r_1011_; 
v_res_1010_ = l_Lean_Level_normLtAux(v_x_1006_, v_x_1007_, v_x_1008_, v_x_1009_);
lean_dec(v_x_1008_);
lean_dec(v_x_1006_);
v_r_1011_ = lean_box(v_res_1010_);
return v_r_1011_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_normLtAux_match__1_splitter___redArg(lean_object* v_x_1012_, lean_object* v_x_1013_, lean_object* v_x_1014_, lean_object* v_x_1015_, lean_object* v_h__1_1016_, lean_object* v_h__2_1017_, lean_object* v_h__3_1018_, lean_object* v_h__4_1019_, lean_object* v_h__5_1020_, lean_object* v_h__6_1021_, lean_object* v_h__7_1022_){
_start:
{
switch(lean_obj_tag(v_x_1012_))
{
case 1:
{
lean_object* v_a_1023_; lean_object* v___x_1024_; 
lean_dec(v_h__7_1022_);
lean_dec(v_h__6_1021_);
lean_dec(v_h__5_1020_);
lean_dec(v_h__4_1019_);
lean_dec(v_h__3_1018_);
lean_dec(v_h__2_1017_);
v_a_1023_ = lean_ctor_get(v_x_1012_, 0);
lean_inc(v_a_1023_);
lean_dec_ref_known(v_x_1012_, 1);
v___x_1024_ = lean_apply_4(v_h__1_1016_, v_a_1023_, v_x_1013_, v_x_1014_, v_x_1015_);
return v___x_1024_;
}
case 2:
{
lean_dec(v_h__6_1021_);
lean_dec(v_h__5_1020_);
lean_dec(v_h__4_1019_);
lean_dec(v_h__1_1016_);
switch(lean_obj_tag(v_x_1014_))
{
case 1:
{
lean_object* v_a_1025_; lean_object* v___x_1026_; 
lean_dec(v_h__7_1022_);
lean_dec(v_h__3_1018_);
v_a_1025_ = lean_ctor_get(v_x_1014_, 0);
lean_inc(v_a_1025_);
lean_dec_ref_known(v_x_1014_, 1);
v___x_1026_ = lean_apply_5(v_h__2_1017_, v_x_1012_, v_x_1013_, v_a_1025_, v_x_1015_, lean_box(0));
return v___x_1026_;
}
case 2:
{
lean_object* v_a_1027_; lean_object* v_a_1028_; lean_object* v_a_1029_; lean_object* v_a_1030_; lean_object* v___x_1031_; 
lean_dec(v_h__7_1022_);
lean_dec(v_h__2_1017_);
v_a_1027_ = lean_ctor_get(v_x_1012_, 0);
lean_inc(v_a_1027_);
v_a_1028_ = lean_ctor_get(v_x_1012_, 1);
lean_inc(v_a_1028_);
lean_dec_ref_known(v_x_1012_, 2);
v_a_1029_ = lean_ctor_get(v_x_1014_, 0);
lean_inc(v_a_1029_);
v_a_1030_ = lean_ctor_get(v_x_1014_, 1);
lean_inc(v_a_1030_);
lean_dec_ref_known(v_x_1014_, 2);
v___x_1031_ = lean_apply_6(v_h__3_1018_, v_a_1027_, v_a_1028_, v_x_1013_, v_a_1029_, v_a_1030_, v_x_1015_);
return v___x_1031_;
}
default: 
{
lean_object* v___x_1032_; 
lean_dec(v_h__3_1018_);
lean_dec(v_h__2_1017_);
v___x_1032_ = lean_apply_10(v_h__7_1022_, v_x_1012_, v_x_1013_, v_x_1014_, v_x_1015_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_1032_;
}
}
}
case 3:
{
lean_dec(v_h__6_1021_);
lean_dec(v_h__5_1020_);
lean_dec(v_h__3_1018_);
lean_dec(v_h__1_1016_);
switch(lean_obj_tag(v_x_1014_))
{
case 1:
{
lean_object* v_a_1033_; lean_object* v___x_1034_; 
lean_dec(v_h__7_1022_);
lean_dec(v_h__4_1019_);
v_a_1033_ = lean_ctor_get(v_x_1014_, 0);
lean_inc(v_a_1033_);
lean_dec_ref_known(v_x_1014_, 1);
v___x_1034_ = lean_apply_5(v_h__2_1017_, v_x_1012_, v_x_1013_, v_a_1033_, v_x_1015_, lean_box(0));
return v___x_1034_;
}
case 3:
{
lean_object* v_a_1035_; lean_object* v_a_1036_; lean_object* v_a_1037_; lean_object* v_a_1038_; lean_object* v___x_1039_; 
lean_dec(v_h__7_1022_);
lean_dec(v_h__2_1017_);
v_a_1035_ = lean_ctor_get(v_x_1012_, 0);
lean_inc(v_a_1035_);
v_a_1036_ = lean_ctor_get(v_x_1012_, 1);
lean_inc(v_a_1036_);
lean_dec_ref_known(v_x_1012_, 2);
v_a_1037_ = lean_ctor_get(v_x_1014_, 0);
lean_inc(v_a_1037_);
v_a_1038_ = lean_ctor_get(v_x_1014_, 1);
lean_inc(v_a_1038_);
lean_dec_ref_known(v_x_1014_, 2);
v___x_1039_ = lean_apply_6(v_h__4_1019_, v_a_1035_, v_a_1036_, v_x_1013_, v_a_1037_, v_a_1038_, v_x_1015_);
return v___x_1039_;
}
default: 
{
lean_object* v___x_1040_; 
lean_dec(v_h__4_1019_);
lean_dec(v_h__2_1017_);
v___x_1040_ = lean_apply_10(v_h__7_1022_, v_x_1012_, v_x_1013_, v_x_1014_, v_x_1015_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_1040_;
}
}
}
case 4:
{
lean_dec(v_h__6_1021_);
lean_dec(v_h__4_1019_);
lean_dec(v_h__3_1018_);
lean_dec(v_h__1_1016_);
switch(lean_obj_tag(v_x_1014_))
{
case 1:
{
lean_object* v_a_1041_; lean_object* v___x_1042_; 
lean_dec(v_h__7_1022_);
lean_dec(v_h__5_1020_);
v_a_1041_ = lean_ctor_get(v_x_1014_, 0);
lean_inc(v_a_1041_);
lean_dec_ref_known(v_x_1014_, 1);
v___x_1042_ = lean_apply_5(v_h__2_1017_, v_x_1012_, v_x_1013_, v_a_1041_, v_x_1015_, lean_box(0));
return v___x_1042_;
}
case 4:
{
lean_object* v_a_1043_; lean_object* v_a_1044_; lean_object* v___x_1045_; 
lean_dec(v_h__7_1022_);
lean_dec(v_h__2_1017_);
v_a_1043_ = lean_ctor_get(v_x_1012_, 0);
lean_inc(v_a_1043_);
lean_dec_ref_known(v_x_1012_, 1);
v_a_1044_ = lean_ctor_get(v_x_1014_, 0);
lean_inc(v_a_1044_);
lean_dec_ref_known(v_x_1014_, 1);
v___x_1045_ = lean_apply_4(v_h__5_1020_, v_a_1043_, v_x_1013_, v_a_1044_, v_x_1015_);
return v___x_1045_;
}
default: 
{
lean_object* v___x_1046_; 
lean_dec(v_h__5_1020_);
lean_dec(v_h__2_1017_);
v___x_1046_ = lean_apply_10(v_h__7_1022_, v_x_1012_, v_x_1013_, v_x_1014_, v_x_1015_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_1046_;
}
}
}
case 5:
{
lean_dec(v_h__5_1020_);
lean_dec(v_h__4_1019_);
lean_dec(v_h__3_1018_);
lean_dec(v_h__1_1016_);
switch(lean_obj_tag(v_x_1014_))
{
case 1:
{
lean_object* v_a_1047_; lean_object* v___x_1048_; 
lean_dec(v_h__7_1022_);
lean_dec(v_h__6_1021_);
v_a_1047_ = lean_ctor_get(v_x_1014_, 0);
lean_inc(v_a_1047_);
lean_dec_ref_known(v_x_1014_, 1);
v___x_1048_ = lean_apply_5(v_h__2_1017_, v_x_1012_, v_x_1013_, v_a_1047_, v_x_1015_, lean_box(0));
return v___x_1048_;
}
case 5:
{
lean_object* v_a_1049_; lean_object* v_a_1050_; lean_object* v___x_1051_; 
lean_dec(v_h__7_1022_);
lean_dec(v_h__2_1017_);
v_a_1049_ = lean_ctor_get(v_x_1012_, 0);
lean_inc(v_a_1049_);
lean_dec_ref_known(v_x_1012_, 1);
v_a_1050_ = lean_ctor_get(v_x_1014_, 0);
lean_inc(v_a_1050_);
lean_dec_ref_known(v_x_1014_, 1);
v___x_1051_ = lean_apply_4(v_h__6_1021_, v_a_1049_, v_x_1013_, v_a_1050_, v_x_1015_);
return v___x_1051_;
}
default: 
{
lean_object* v___x_1052_; 
lean_dec(v_h__6_1021_);
lean_dec(v_h__2_1017_);
v___x_1052_ = lean_apply_10(v_h__7_1022_, v_x_1012_, v_x_1013_, v_x_1014_, v_x_1015_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_1052_;
}
}
}
default: 
{
lean_dec(v_h__6_1021_);
lean_dec(v_h__5_1020_);
lean_dec(v_h__4_1019_);
lean_dec(v_h__3_1018_);
lean_dec(v_h__1_1016_);
if (lean_obj_tag(v_x_1014_) == 1)
{
lean_object* v_a_1053_; lean_object* v___x_1054_; 
lean_dec(v_h__7_1022_);
v_a_1053_ = lean_ctor_get(v_x_1014_, 0);
lean_inc(v_a_1053_);
lean_dec_ref_known(v_x_1014_, 1);
v___x_1054_ = lean_apply_5(v_h__2_1017_, v_x_1012_, v_x_1013_, v_a_1053_, v_x_1015_, lean_box(0));
return v___x_1054_;
}
else
{
lean_object* v___x_1055_; 
lean_dec(v_h__2_1017_);
v___x_1055_ = lean_apply_10(v_h__7_1022_, v_x_1012_, v_x_1013_, v_x_1014_, v_x_1015_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_1055_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_normLtAux_match__1_splitter(lean_object* v_motive_1056_, lean_object* v_x_1057_, lean_object* v_x_1058_, lean_object* v_x_1059_, lean_object* v_x_1060_, lean_object* v_h__1_1061_, lean_object* v_h__2_1062_, lean_object* v_h__3_1063_, lean_object* v_h__4_1064_, lean_object* v_h__5_1065_, lean_object* v_h__6_1066_, lean_object* v_h__7_1067_){
_start:
{
switch(lean_obj_tag(v_x_1057_))
{
case 1:
{
lean_object* v_a_1068_; lean_object* v___x_1069_; 
lean_dec(v_h__7_1067_);
lean_dec(v_h__6_1066_);
lean_dec(v_h__5_1065_);
lean_dec(v_h__4_1064_);
lean_dec(v_h__3_1063_);
lean_dec(v_h__2_1062_);
v_a_1068_ = lean_ctor_get(v_x_1057_, 0);
lean_inc(v_a_1068_);
lean_dec_ref_known(v_x_1057_, 1);
v___x_1069_ = lean_apply_4(v_h__1_1061_, v_a_1068_, v_x_1058_, v_x_1059_, v_x_1060_);
return v___x_1069_;
}
case 2:
{
lean_dec(v_h__6_1066_);
lean_dec(v_h__5_1065_);
lean_dec(v_h__4_1064_);
lean_dec(v_h__1_1061_);
switch(lean_obj_tag(v_x_1059_))
{
case 1:
{
lean_object* v_a_1070_; lean_object* v___x_1071_; 
lean_dec(v_h__7_1067_);
lean_dec(v_h__3_1063_);
v_a_1070_ = lean_ctor_get(v_x_1059_, 0);
lean_inc(v_a_1070_);
lean_dec_ref_known(v_x_1059_, 1);
v___x_1071_ = lean_apply_5(v_h__2_1062_, v_x_1057_, v_x_1058_, v_a_1070_, v_x_1060_, lean_box(0));
return v___x_1071_;
}
case 2:
{
lean_object* v_a_1072_; lean_object* v_a_1073_; lean_object* v_a_1074_; lean_object* v_a_1075_; lean_object* v___x_1076_; 
lean_dec(v_h__7_1067_);
lean_dec(v_h__2_1062_);
v_a_1072_ = lean_ctor_get(v_x_1057_, 0);
lean_inc(v_a_1072_);
v_a_1073_ = lean_ctor_get(v_x_1057_, 1);
lean_inc(v_a_1073_);
lean_dec_ref_known(v_x_1057_, 2);
v_a_1074_ = lean_ctor_get(v_x_1059_, 0);
lean_inc(v_a_1074_);
v_a_1075_ = lean_ctor_get(v_x_1059_, 1);
lean_inc(v_a_1075_);
lean_dec_ref_known(v_x_1059_, 2);
v___x_1076_ = lean_apply_6(v_h__3_1063_, v_a_1072_, v_a_1073_, v_x_1058_, v_a_1074_, v_a_1075_, v_x_1060_);
return v___x_1076_;
}
default: 
{
lean_object* v___x_1077_; 
lean_dec(v_h__3_1063_);
lean_dec(v_h__2_1062_);
v___x_1077_ = lean_apply_10(v_h__7_1067_, v_x_1057_, v_x_1058_, v_x_1059_, v_x_1060_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_1077_;
}
}
}
case 3:
{
lean_dec(v_h__6_1066_);
lean_dec(v_h__5_1065_);
lean_dec(v_h__3_1063_);
lean_dec(v_h__1_1061_);
switch(lean_obj_tag(v_x_1059_))
{
case 1:
{
lean_object* v_a_1078_; lean_object* v___x_1079_; 
lean_dec(v_h__7_1067_);
lean_dec(v_h__4_1064_);
v_a_1078_ = lean_ctor_get(v_x_1059_, 0);
lean_inc(v_a_1078_);
lean_dec_ref_known(v_x_1059_, 1);
v___x_1079_ = lean_apply_5(v_h__2_1062_, v_x_1057_, v_x_1058_, v_a_1078_, v_x_1060_, lean_box(0));
return v___x_1079_;
}
case 3:
{
lean_object* v_a_1080_; lean_object* v_a_1081_; lean_object* v_a_1082_; lean_object* v_a_1083_; lean_object* v___x_1084_; 
lean_dec(v_h__7_1067_);
lean_dec(v_h__2_1062_);
v_a_1080_ = lean_ctor_get(v_x_1057_, 0);
lean_inc(v_a_1080_);
v_a_1081_ = lean_ctor_get(v_x_1057_, 1);
lean_inc(v_a_1081_);
lean_dec_ref_known(v_x_1057_, 2);
v_a_1082_ = lean_ctor_get(v_x_1059_, 0);
lean_inc(v_a_1082_);
v_a_1083_ = lean_ctor_get(v_x_1059_, 1);
lean_inc(v_a_1083_);
lean_dec_ref_known(v_x_1059_, 2);
v___x_1084_ = lean_apply_6(v_h__4_1064_, v_a_1080_, v_a_1081_, v_x_1058_, v_a_1082_, v_a_1083_, v_x_1060_);
return v___x_1084_;
}
default: 
{
lean_object* v___x_1085_; 
lean_dec(v_h__4_1064_);
lean_dec(v_h__2_1062_);
v___x_1085_ = lean_apply_10(v_h__7_1067_, v_x_1057_, v_x_1058_, v_x_1059_, v_x_1060_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_1085_;
}
}
}
case 4:
{
lean_dec(v_h__6_1066_);
lean_dec(v_h__4_1064_);
lean_dec(v_h__3_1063_);
lean_dec(v_h__1_1061_);
switch(lean_obj_tag(v_x_1059_))
{
case 1:
{
lean_object* v_a_1086_; lean_object* v___x_1087_; 
lean_dec(v_h__7_1067_);
lean_dec(v_h__5_1065_);
v_a_1086_ = lean_ctor_get(v_x_1059_, 0);
lean_inc(v_a_1086_);
lean_dec_ref_known(v_x_1059_, 1);
v___x_1087_ = lean_apply_5(v_h__2_1062_, v_x_1057_, v_x_1058_, v_a_1086_, v_x_1060_, lean_box(0));
return v___x_1087_;
}
case 4:
{
lean_object* v_a_1088_; lean_object* v_a_1089_; lean_object* v___x_1090_; 
lean_dec(v_h__7_1067_);
lean_dec(v_h__2_1062_);
v_a_1088_ = lean_ctor_get(v_x_1057_, 0);
lean_inc(v_a_1088_);
lean_dec_ref_known(v_x_1057_, 1);
v_a_1089_ = lean_ctor_get(v_x_1059_, 0);
lean_inc(v_a_1089_);
lean_dec_ref_known(v_x_1059_, 1);
v___x_1090_ = lean_apply_4(v_h__5_1065_, v_a_1088_, v_x_1058_, v_a_1089_, v_x_1060_);
return v___x_1090_;
}
default: 
{
lean_object* v___x_1091_; 
lean_dec(v_h__5_1065_);
lean_dec(v_h__2_1062_);
v___x_1091_ = lean_apply_10(v_h__7_1067_, v_x_1057_, v_x_1058_, v_x_1059_, v_x_1060_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_1091_;
}
}
}
case 5:
{
lean_dec(v_h__5_1065_);
lean_dec(v_h__4_1064_);
lean_dec(v_h__3_1063_);
lean_dec(v_h__1_1061_);
switch(lean_obj_tag(v_x_1059_))
{
case 1:
{
lean_object* v_a_1092_; lean_object* v___x_1093_; 
lean_dec(v_h__7_1067_);
lean_dec(v_h__6_1066_);
v_a_1092_ = lean_ctor_get(v_x_1059_, 0);
lean_inc(v_a_1092_);
lean_dec_ref_known(v_x_1059_, 1);
v___x_1093_ = lean_apply_5(v_h__2_1062_, v_x_1057_, v_x_1058_, v_a_1092_, v_x_1060_, lean_box(0));
return v___x_1093_;
}
case 5:
{
lean_object* v_a_1094_; lean_object* v_a_1095_; lean_object* v___x_1096_; 
lean_dec(v_h__7_1067_);
lean_dec(v_h__2_1062_);
v_a_1094_ = lean_ctor_get(v_x_1057_, 0);
lean_inc(v_a_1094_);
lean_dec_ref_known(v_x_1057_, 1);
v_a_1095_ = lean_ctor_get(v_x_1059_, 0);
lean_inc(v_a_1095_);
lean_dec_ref_known(v_x_1059_, 1);
v___x_1096_ = lean_apply_4(v_h__6_1066_, v_a_1094_, v_x_1058_, v_a_1095_, v_x_1060_);
return v___x_1096_;
}
default: 
{
lean_object* v___x_1097_; 
lean_dec(v_h__6_1066_);
lean_dec(v_h__2_1062_);
v___x_1097_ = lean_apply_10(v_h__7_1067_, v_x_1057_, v_x_1058_, v_x_1059_, v_x_1060_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_1097_;
}
}
}
default: 
{
lean_dec(v_h__6_1066_);
lean_dec(v_h__5_1065_);
lean_dec(v_h__4_1064_);
lean_dec(v_h__3_1063_);
lean_dec(v_h__1_1061_);
if (lean_obj_tag(v_x_1059_) == 1)
{
lean_object* v_a_1098_; lean_object* v___x_1099_; 
lean_dec(v_h__7_1067_);
v_a_1098_ = lean_ctor_get(v_x_1059_, 0);
lean_inc(v_a_1098_);
lean_dec_ref_known(v_x_1059_, 1);
v___x_1099_ = lean_apply_5(v_h__2_1062_, v_x_1057_, v_x_1058_, v_a_1098_, v_x_1060_, lean_box(0));
return v___x_1099_;
}
else
{
lean_object* v___x_1100_; 
lean_dec(v_h__2_1062_);
v___x_1100_ = lean_apply_10(v_h__7_1067_, v_x_1057_, v_x_1058_, v_x_1059_, v_x_1060_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_1100_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Level_normLt(lean_object* v_l_u2081_1101_, lean_object* v_l_u2082_1102_){
_start:
{
lean_object* v___x_1103_; uint8_t v___x_1104_; 
v___x_1103_ = lean_unsigned_to_nat(0u);
v___x_1104_ = l_Lean_Level_normLtAux(v_l_u2081_1101_, v___x_1103_, v_l_u2082_1102_, v___x_1103_);
return v___x_1104_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_normLt___boxed(lean_object* v_l_u2081_1105_, lean_object* v_l_u2082_1106_){
_start:
{
uint8_t v_res_1107_; lean_object* v_r_1108_; 
v_res_1107_ = l_Lean_Level_normLt(v_l_u2081_1105_, v_l_u2082_1106_);
lean_dec(v_l_u2082_1106_);
lean_dec(v_l_u2081_1105_);
v_r_1108_ = lean_box(v_res_1107_);
return v_r_1108_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_isAlreadyNormalizedCheap(lean_object* v_x_1109_){
_start:
{
switch(lean_obj_tag(v_x_1109_))
{
case 0:
{
uint8_t v___x_1110_; 
v___x_1110_ = 1;
return v___x_1110_;
}
case 4:
{
uint8_t v___x_1111_; 
v___x_1111_ = 1;
return v___x_1111_;
}
case 5:
{
uint8_t v___x_1112_; 
v___x_1112_ = 1;
return v___x_1112_;
}
case 1:
{
lean_object* v_a_1113_; 
v_a_1113_ = lean_ctor_get(v_x_1109_, 0);
v_x_1109_ = v_a_1113_;
goto _start;
}
default: 
{
uint8_t v___x_1115_; 
v___x_1115_ = 0;
return v___x_1115_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_isAlreadyNormalizedCheap___boxed(lean_object* v_x_1116_){
_start:
{
uint8_t v_res_1117_; lean_object* v_r_1118_; 
v_res_1117_ = l_Lean_Level_isAlreadyNormalizedCheap(v_x_1116_);
lean_dec(v_x_1116_);
v_r_1118_ = lean_box(v_res_1117_);
return v_r_1118_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_mkIMaxAux(lean_object* v_x_1119_, lean_object* v_x_1120_){
_start:
{
lean_object* v_u_u2081_1122_; lean_object* v_u_u2082_1123_; 
if (lean_obj_tag(v_x_1120_) == 0)
{
lean_dec(v_x_1119_);
return v_x_1120_;
}
else
{
switch(lean_obj_tag(v_x_1119_))
{
case 0:
{
return v_x_1120_;
}
case 1:
{
lean_object* v_a_1126_; 
v_a_1126_ = lean_ctor_get(v_x_1119_, 0);
if (lean_obj_tag(v_a_1126_) == 0)
{
lean_dec_ref_known(v_x_1119_, 1);
return v_x_1120_;
}
else
{
v_u_u2081_1122_ = v_x_1119_;
v_u_u2082_1123_ = v_x_1120_;
goto v___jp_1121_;
}
}
default: 
{
v_u_u2081_1122_ = v_x_1119_;
v_u_u2082_1123_ = v_x_1120_;
goto v___jp_1121_;
}
}
}
v___jp_1121_:
{
uint8_t v___x_1124_; 
v___x_1124_ = lean_level_eq(v_u_u2081_1122_, v_u_u2082_1123_);
if (v___x_1124_ == 0)
{
lean_object* v___x_1125_; 
v___x_1125_ = l_Lean_Level_imax___override(v_u_u2081_1122_, v_u_u2082_1123_);
return v___x_1125_;
}
else
{
lean_dec(v_u_u2082_1123_);
return v_u_u2081_1122_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_getMaxArgsAux(lean_object* v_normalize_1127_, lean_object* v_x_1128_, uint8_t v_x_1129_, lean_object* v_x_1130_){
_start:
{
if (lean_obj_tag(v_x_1128_) == 2)
{
lean_object* v_a_1131_; lean_object* v_a_1132_; lean_object* v___x_1133_; 
v_a_1131_ = lean_ctor_get(v_x_1128_, 0);
lean_inc(v_a_1131_);
v_a_1132_ = lean_ctor_get(v_x_1128_, 1);
lean_inc(v_a_1132_);
lean_dec_ref_known(v_x_1128_, 2);
lean_inc_ref(v_normalize_1127_);
v___x_1133_ = l___private_Lean_Level_0__Lean_Level_getMaxArgsAux(v_normalize_1127_, v_a_1131_, v_x_1129_, v_x_1130_);
v_x_1128_ = v_a_1132_;
v_x_1130_ = v___x_1133_;
goto _start;
}
else
{
if (v_x_1129_ == 0)
{
lean_object* v___x_1135_; uint8_t v___x_1136_; 
lean_inc_ref(v_normalize_1127_);
v___x_1135_ = lean_apply_1(v_normalize_1127_, v_x_1128_);
v___x_1136_ = 1;
v_x_1128_ = v___x_1135_;
v_x_1129_ = v___x_1136_;
goto _start;
}
else
{
lean_object* v___x_1138_; 
lean_dec_ref(v_normalize_1127_);
v___x_1138_ = lean_array_push(v_x_1130_, v_x_1128_);
return v___x_1138_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_getMaxArgsAux___boxed(lean_object* v_normalize_1139_, lean_object* v_x_1140_, lean_object* v_x_1141_, lean_object* v_x_1142_){
_start:
{
uint8_t v_x_36__boxed_1143_; lean_object* v_res_1144_; 
v_x_36__boxed_1143_ = lean_unbox(v_x_1141_);
v_res_1144_ = l___private_Lean_Level_0__Lean_Level_getMaxArgsAux(v_normalize_1139_, v_x_1140_, v_x_36__boxed_1143_, v_x_1142_);
return v_res_1144_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_accMax(lean_object* v_result_1145_, lean_object* v_prev_1146_, lean_object* v_offset_1147_){
_start:
{
uint8_t v___x_1148_; 
v___x_1148_ = l_Lean_Level_isZero(v_result_1145_);
if (v___x_1148_ == 0)
{
lean_object* v___x_1149_; lean_object* v___x_1150_; 
v___x_1149_ = l_Lean_Level_addOffsetAux(v_offset_1147_, v_prev_1146_);
v___x_1150_ = l_Lean_Level_max___override(v_result_1145_, v___x_1149_);
return v___x_1150_;
}
else
{
lean_object* v___x_1151_; 
lean_dec(v_result_1145_);
v___x_1151_ = l_Lean_Level_addOffsetAux(v_offset_1147_, v_prev_1146_);
return v___x_1151_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_mkMaxAux(lean_object* v_lvls_1152_, lean_object* v_extraK_1153_, lean_object* v_i_1154_, lean_object* v_prev_1155_, lean_object* v_prevK_1156_, lean_object* v_result_1157_){
_start:
{
lean_object* v___x_1158_; uint8_t v___x_1159_; 
v___x_1158_ = lean_array_get_size(v_lvls_1152_);
v___x_1159_ = lean_nat_dec_lt(v_i_1154_, v___x_1158_);
if (v___x_1159_ == 0)
{
lean_object* v___x_1160_; lean_object* v___x_1161_; 
lean_dec(v_i_1154_);
v___x_1160_ = lean_nat_add(v_extraK_1153_, v_prevK_1156_);
lean_dec(v_prevK_1156_);
v___x_1161_ = l___private_Lean_Level_0__Lean_Level_accMax(v_result_1157_, v_prev_1155_, v___x_1160_);
return v___x_1161_;
}
else
{
lean_object* v_lvl_1162_; lean_object* v_curr_1163_; lean_object* v_currK_1164_; uint8_t v___x_1165_; 
v_lvl_1162_ = lean_array_fget_borrowed(v_lvls_1152_, v_i_1154_);
v_curr_1163_ = l_Lean_Level_getLevelOffset(v_lvl_1162_);
v_currK_1164_ = l_Lean_Level_getOffset(v_lvl_1162_);
v___x_1165_ = lean_level_eq(v_curr_1163_, v_prev_1155_);
if (v___x_1165_ == 0)
{
lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; 
v___x_1166_ = lean_unsigned_to_nat(1u);
v___x_1167_ = lean_nat_add(v_i_1154_, v___x_1166_);
lean_dec(v_i_1154_);
v___x_1168_ = lean_nat_add(v_extraK_1153_, v_prevK_1156_);
lean_dec(v_prevK_1156_);
v___x_1169_ = l___private_Lean_Level_0__Lean_Level_accMax(v_result_1157_, v_prev_1155_, v___x_1168_);
v_i_1154_ = v___x_1167_;
v_prev_1155_ = v_curr_1163_;
v_prevK_1156_ = v_currK_1164_;
v_result_1157_ = v___x_1169_;
goto _start;
}
else
{
lean_object* v___x_1171_; lean_object* v___x_1172_; 
lean_dec(v_prevK_1156_);
lean_dec(v_prev_1155_);
v___x_1171_ = lean_unsigned_to_nat(1u);
v___x_1172_ = lean_nat_add(v_i_1154_, v___x_1171_);
lean_dec(v_i_1154_);
v_i_1154_ = v___x_1172_;
v_prev_1155_ = v_curr_1163_;
v_prevK_1156_ = v_currK_1164_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_mkMaxAux___boxed(lean_object* v_lvls_1174_, lean_object* v_extraK_1175_, lean_object* v_i_1176_, lean_object* v_prev_1177_, lean_object* v_prevK_1178_, lean_object* v_result_1179_){
_start:
{
lean_object* v_res_1180_; 
v_res_1180_ = l___private_Lean_Level_0__Lean_Level_mkMaxAux(v_lvls_1174_, v_extraK_1175_, v_i_1176_, v_prev_1177_, v_prevK_1178_, v_result_1179_);
lean_dec(v_extraK_1175_);
lean_dec_ref(v_lvls_1174_);
return v_res_1180_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_skipExplicit(lean_object* v_lvls_1181_, lean_object* v_i_1182_){
_start:
{
lean_object* v___x_1183_; uint8_t v___x_1184_; 
v___x_1183_ = lean_array_get_size(v_lvls_1181_);
v___x_1184_ = lean_nat_dec_lt(v_i_1182_, v___x_1183_);
if (v___x_1184_ == 0)
{
return v_i_1182_;
}
else
{
lean_object* v_lvl_1185_; lean_object* v___x_1186_; uint8_t v___x_1187_; 
v_lvl_1185_ = lean_array_fget_borrowed(v_lvls_1181_, v_i_1182_);
v___x_1186_ = l_Lean_Level_getLevelOffset(v_lvl_1185_);
v___x_1187_ = l_Lean_Level_isZero(v___x_1186_);
lean_dec(v___x_1186_);
if (v___x_1187_ == 0)
{
return v_i_1182_;
}
else
{
lean_object* v___x_1188_; lean_object* v___x_1189_; 
v___x_1188_ = lean_unsigned_to_nat(1u);
v___x_1189_ = lean_nat_add(v_i_1182_, v___x_1188_);
lean_dec(v_i_1182_);
v_i_1182_ = v___x_1189_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_skipExplicit___boxed(lean_object* v_lvls_1191_, lean_object* v_i_1192_){
_start:
{
lean_object* v_res_1193_; 
v_res_1193_ = l___private_Lean_Level_0__Lean_Level_skipExplicit(v_lvls_1191_, v_i_1192_);
lean_dec_ref(v_lvls_1191_);
return v_res_1193_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Level_0__Lean_Level_isExplicitSubsumedAux(lean_object* v_lvls_1194_, lean_object* v_maxExplicit_1195_, lean_object* v_i_1196_){
_start:
{
lean_object* v___x_1197_; uint8_t v___x_1198_; 
v___x_1197_ = lean_array_get_size(v_lvls_1194_);
v___x_1198_ = lean_nat_dec_lt(v_i_1196_, v___x_1197_);
if (v___x_1198_ == 0)
{
lean_dec(v_i_1196_);
return v___x_1198_;
}
else
{
lean_object* v_lvl_1199_; lean_object* v___x_1200_; uint8_t v___x_1201_; 
v_lvl_1199_ = lean_array_fget_borrowed(v_lvls_1194_, v_i_1196_);
v___x_1200_ = l_Lean_Level_getOffset(v_lvl_1199_);
v___x_1201_ = lean_nat_dec_le(v_maxExplicit_1195_, v___x_1200_);
lean_dec(v___x_1200_);
if (v___x_1201_ == 0)
{
lean_object* v___x_1202_; lean_object* v___x_1203_; 
v___x_1202_ = lean_unsigned_to_nat(1u);
v___x_1203_ = lean_nat_add(v_i_1196_, v___x_1202_);
lean_dec(v_i_1196_);
v_i_1196_ = v___x_1203_;
goto _start;
}
else
{
lean_dec(v_i_1196_);
return v___x_1201_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_isExplicitSubsumedAux___boxed(lean_object* v_lvls_1205_, lean_object* v_maxExplicit_1206_, lean_object* v_i_1207_){
_start:
{
uint8_t v_res_1208_; lean_object* v_r_1209_; 
v_res_1208_ = l___private_Lean_Level_0__Lean_Level_isExplicitSubsumedAux(v_lvls_1205_, v_maxExplicit_1206_, v_i_1207_);
lean_dec(v_maxExplicit_1206_);
lean_dec_ref(v_lvls_1205_);
v_r_1209_ = lean_box(v_res_1208_);
return v_r_1209_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Level_0__Lean_Level_isExplicitSubsumed(lean_object* v_lvls_1210_, lean_object* v_firstNonExplicit_1211_){
_start:
{
lean_object* v___x_1212_; uint8_t v___x_1213_; 
v___x_1212_ = lean_unsigned_to_nat(0u);
v___x_1213_ = lean_nat_dec_eq(v_firstNonExplicit_1211_, v___x_1212_);
if (v___x_1213_ == 0)
{
lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v_max_1218_; uint8_t v___x_1219_; 
v___x_1214_ = lean_box(0);
v___x_1215_ = lean_unsigned_to_nat(1u);
v___x_1216_ = lean_nat_sub(v_firstNonExplicit_1211_, v___x_1215_);
v___x_1217_ = lean_array_get_borrowed(v___x_1214_, v_lvls_1210_, v___x_1216_);
lean_dec(v___x_1216_);
v_max_1218_ = l_Lean_Level_getOffset(v___x_1217_);
v___x_1219_ = l___private_Lean_Level_0__Lean_Level_isExplicitSubsumedAux(v_lvls_1210_, v_max_1218_, v_firstNonExplicit_1211_);
lean_dec(v_max_1218_);
return v___x_1219_;
}
else
{
uint8_t v___x_1220_; 
lean_dec(v_firstNonExplicit_1211_);
v___x_1220_ = 0;
return v___x_1220_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_isExplicitSubsumed___boxed(lean_object* v_lvls_1221_, lean_object* v_firstNonExplicit_1222_){
_start:
{
uint8_t v_res_1223_; lean_object* v_r_1224_; 
v_res_1223_ = l___private_Lean_Level_0__Lean_Level_isExplicitSubsumed(v_lvls_1221_, v_firstNonExplicit_1222_);
lean_dec_ref(v_lvls_1221_);
v_r_1224_ = lean_box(v_res_1223_);
return v_r_1224_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Level_normalize_spec__2(lean_object* v_msg_1225_){
_start:
{
lean_object* v___x_1226_; lean_object* v___x_1227_; 
v___x_1226_ = lean_box(0);
v___x_1227_ = lean_panic_fn_borrowed(v___x_1226_, v_msg_1225_);
return v___x_1227_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1_spec__1___redArg(lean_object* v_hi_1228_, lean_object* v_pivot_1229_, lean_object* v_as_1230_, lean_object* v_i_1231_, lean_object* v_k_1232_){
_start:
{
uint8_t v___x_1233_; 
v___x_1233_ = lean_nat_dec_lt(v_k_1232_, v_hi_1228_);
if (v___x_1233_ == 0)
{
lean_object* v___x_1234_; lean_object* v___x_1235_; 
lean_dec(v_k_1232_);
v___x_1234_ = lean_array_fswap(v_as_1230_, v_i_1231_, v_hi_1228_);
v___x_1235_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1235_, 0, v_i_1231_);
lean_ctor_set(v___x_1235_, 1, v___x_1234_);
return v___x_1235_;
}
else
{
lean_object* v___x_1236_; uint8_t v___x_1237_; 
v___x_1236_ = lean_array_fget_borrowed(v_as_1230_, v_k_1232_);
v___x_1237_ = l_Lean_Level_normLt(v___x_1236_, v_pivot_1229_);
if (v___x_1237_ == 0)
{
lean_object* v___x_1238_; lean_object* v___x_1239_; 
v___x_1238_ = lean_unsigned_to_nat(1u);
v___x_1239_ = lean_nat_add(v_k_1232_, v___x_1238_);
lean_dec(v_k_1232_);
v_k_1232_ = v___x_1239_;
goto _start;
}
else
{
lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; 
v___x_1241_ = lean_array_fswap(v_as_1230_, v_i_1231_, v_k_1232_);
v___x_1242_ = lean_unsigned_to_nat(1u);
v___x_1243_ = lean_nat_add(v_i_1231_, v___x_1242_);
lean_dec(v_i_1231_);
v___x_1244_ = lean_nat_add(v_k_1232_, v___x_1242_);
lean_dec(v_k_1232_);
v_as_1230_ = v___x_1241_;
v_i_1231_ = v___x_1243_;
v_k_1232_ = v___x_1244_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1_spec__1___redArg___boxed(lean_object* v_hi_1246_, lean_object* v_pivot_1247_, lean_object* v_as_1248_, lean_object* v_i_1249_, lean_object* v_k_1250_){
_start:
{
lean_object* v_res_1251_; 
v_res_1251_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1_spec__1___redArg(v_hi_1246_, v_pivot_1247_, v_as_1248_, v_i_1249_, v_k_1250_);
lean_dec(v_pivot_1247_);
lean_dec(v_hi_1246_);
return v_res_1251_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1___redArg(lean_object* v_n_1252_, lean_object* v_as_1253_, lean_object* v_lo_1254_, lean_object* v_hi_1255_){
_start:
{
lean_object* v___y_1257_; uint8_t v___x_1267_; 
v___x_1267_ = lean_nat_dec_lt(v_lo_1254_, v_hi_1255_);
if (v___x_1267_ == 0)
{
lean_dec(v_lo_1254_);
return v_as_1253_;
}
else
{
lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v_mid_1270_; lean_object* v___y_1272_; lean_object* v___y_1278_; lean_object* v___x_1283_; lean_object* v___x_1284_; uint8_t v___x_1285_; 
v___x_1268_ = lean_nat_add(v_lo_1254_, v_hi_1255_);
v___x_1269_ = lean_unsigned_to_nat(1u);
v_mid_1270_ = lean_nat_shiftr(v___x_1268_, v___x_1269_);
lean_dec(v___x_1268_);
v___x_1283_ = lean_array_fget_borrowed(v_as_1253_, v_mid_1270_);
v___x_1284_ = lean_array_fget_borrowed(v_as_1253_, v_lo_1254_);
v___x_1285_ = l_Lean_Level_normLt(v___x_1283_, v___x_1284_);
if (v___x_1285_ == 0)
{
v___y_1278_ = v_as_1253_;
goto v___jp_1277_;
}
else
{
lean_object* v___x_1286_; 
v___x_1286_ = lean_array_fswap(v_as_1253_, v_lo_1254_, v_mid_1270_);
v___y_1278_ = v___x_1286_;
goto v___jp_1277_;
}
v___jp_1271_:
{
lean_object* v___x_1273_; lean_object* v___x_1274_; uint8_t v___x_1275_; 
v___x_1273_ = lean_array_fget_borrowed(v___y_1272_, v_mid_1270_);
v___x_1274_ = lean_array_fget_borrowed(v___y_1272_, v_hi_1255_);
v___x_1275_ = l_Lean_Level_normLt(v___x_1273_, v___x_1274_);
if (v___x_1275_ == 0)
{
lean_dec(v_mid_1270_);
v___y_1257_ = v___y_1272_;
goto v___jp_1256_;
}
else
{
lean_object* v___x_1276_; 
v___x_1276_ = lean_array_fswap(v___y_1272_, v_mid_1270_, v_hi_1255_);
lean_dec(v_mid_1270_);
v___y_1257_ = v___x_1276_;
goto v___jp_1256_;
}
}
v___jp_1277_:
{
lean_object* v___x_1279_; lean_object* v___x_1280_; uint8_t v___x_1281_; 
v___x_1279_ = lean_array_fget_borrowed(v___y_1278_, v_hi_1255_);
v___x_1280_ = lean_array_fget_borrowed(v___y_1278_, v_lo_1254_);
v___x_1281_ = l_Lean_Level_normLt(v___x_1279_, v___x_1280_);
if (v___x_1281_ == 0)
{
v___y_1272_ = v___y_1278_;
goto v___jp_1271_;
}
else
{
lean_object* v___x_1282_; 
v___x_1282_ = lean_array_fswap(v___y_1278_, v_lo_1254_, v_hi_1255_);
v___y_1272_ = v___x_1282_;
goto v___jp_1271_;
}
}
}
v___jp_1256_:
{
lean_object* v_pivot_1258_; lean_object* v___x_1259_; lean_object* v_fst_1260_; lean_object* v_snd_1261_; uint8_t v___x_1262_; 
v_pivot_1258_ = lean_array_fget(v___y_1257_, v_hi_1255_);
lean_inc_n(v_lo_1254_, 2);
v___x_1259_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1_spec__1___redArg(v_hi_1255_, v_pivot_1258_, v___y_1257_, v_lo_1254_, v_lo_1254_);
lean_dec(v_pivot_1258_);
v_fst_1260_ = lean_ctor_get(v___x_1259_, 0);
lean_inc(v_fst_1260_);
v_snd_1261_ = lean_ctor_get(v___x_1259_, 1);
lean_inc(v_snd_1261_);
lean_dec_ref(v___x_1259_);
v___x_1262_ = lean_nat_dec_le(v_hi_1255_, v_fst_1260_);
if (v___x_1262_ == 0)
{
lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; 
v___x_1263_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1___redArg(v_n_1252_, v_snd_1261_, v_lo_1254_, v_fst_1260_);
v___x_1264_ = lean_unsigned_to_nat(1u);
v___x_1265_ = lean_nat_add(v_fst_1260_, v___x_1264_);
lean_dec(v_fst_1260_);
v_as_1253_ = v___x_1263_;
v_lo_1254_ = v___x_1265_;
goto _start;
}
else
{
lean_dec(v_fst_1260_);
lean_dec(v_lo_1254_);
return v_snd_1261_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1___redArg___boxed(lean_object* v_n_1287_, lean_object* v_as_1288_, lean_object* v_lo_1289_, lean_object* v_hi_1290_){
_start:
{
lean_object* v_res_1291_; 
v_res_1291_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1___redArg(v_n_1287_, v_as_1288_, v_lo_1289_, v_hi_1290_);
lean_dec(v_hi_1290_);
lean_dec(v_n_1287_);
return v_res_1291_;
}
}
static lean_object* _init_l_Lean_Level_normalize___closed__3(void){
_start:
{
lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; 
v___x_1296_ = ((lean_object*)(l_Lean_Level_normalize___closed__2));
v___x_1297_ = lean_unsigned_to_nat(11u);
v___x_1298_ = lean_unsigned_to_nat(404u);
v___x_1299_ = ((lean_object*)(l_Lean_Level_normalize___closed__1));
v___x_1300_ = ((lean_object*)(l_Lean_Level_mvarId_x21___closed__0));
v___x_1301_ = l_mkPanicMessageWithDecl(v___x_1300_, v___x_1299_, v___x_1298_, v___x_1297_, v___x_1296_);
return v___x_1301_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_normalize(lean_object* v_l_1302_){
_start:
{
uint8_t v___x_1303_; 
v___x_1303_ = l_Lean_Level_isAlreadyNormalizedCheap(v_l_1302_);
if (v___x_1303_ == 0)
{
lean_object* v_k_1304_; lean_object* v_u_1305_; 
v_k_1304_ = l_Lean_Level_getOffset(v_l_1302_);
v_u_1305_ = l_Lean_Level_getLevelOffset(v_l_1302_);
switch(lean_obj_tag(v_u_1305_))
{
case 2:
{
lean_object* v_a_1306_; lean_object* v_a_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v_lvls_1310_; lean_object* v_lvls_1311_; lean_object* v___x_1312_; lean_object* v___y_1314_; lean_object* v___y_1315_; lean_object* v___y_1323_; lean_object* v___x_1327_; lean_object* v___y_1329_; lean_object* v___y_1330_; uint8_t v___x_1332_; 
v_a_1306_ = lean_ctor_get(v_u_1305_, 0);
lean_inc(v_a_1306_);
v_a_1307_ = lean_ctor_get(v_u_1305_, 1);
lean_inc(v_a_1307_);
lean_dec_ref_known(v_u_1305_, 2);
v___x_1308_ = lean_unsigned_to_nat(0u);
v___x_1309_ = ((lean_object*)(l_Lean_Level_normalize___closed__0));
v_lvls_1310_ = l___private_Lean_Level_0__Lean_Level_getMaxArgsAux___at___00Lean_Level_normalize_spec__0(v_a_1306_, v___x_1303_, v___x_1309_);
v_lvls_1311_ = l___private_Lean_Level_0__Lean_Level_getMaxArgsAux___at___00Lean_Level_normalize_spec__0(v_a_1307_, v___x_1303_, v_lvls_1310_);
v___x_1312_ = lean_unsigned_to_nat(1u);
v___x_1327_ = lean_array_get_size(v_lvls_1311_);
v___x_1332_ = lean_nat_dec_eq(v___x_1327_, v___x_1308_);
if (v___x_1332_ == 0)
{
lean_object* v___x_1333_; lean_object* v___y_1335_; uint8_t v___x_1337_; 
v___x_1333_ = lean_nat_sub(v___x_1327_, v___x_1312_);
v___x_1337_ = lean_nat_dec_le(v___x_1308_, v___x_1333_);
if (v___x_1337_ == 0)
{
lean_inc(v___x_1333_);
v___y_1335_ = v___x_1333_;
goto v___jp_1334_;
}
else
{
v___y_1335_ = v___x_1308_;
goto v___jp_1334_;
}
v___jp_1334_:
{
uint8_t v___x_1336_; 
v___x_1336_ = lean_nat_dec_le(v___y_1335_, v___x_1333_);
if (v___x_1336_ == 0)
{
lean_dec(v___x_1333_);
lean_inc(v___y_1335_);
v___y_1329_ = v___y_1335_;
v___y_1330_ = v___y_1335_;
goto v___jp_1328_;
}
else
{
v___y_1329_ = v___y_1335_;
v___y_1330_ = v___x_1333_;
goto v___jp_1328_;
}
}
}
else
{
v___y_1323_ = v_lvls_1311_;
goto v___jp_1322_;
}
v___jp_1313_:
{
lean_object* v___x_1316_; lean_object* v_lvl_u2081_1317_; lean_object* v_prev_1318_; lean_object* v_prevK_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; 
v___x_1316_ = lean_box(0);
v_lvl_u2081_1317_ = lean_array_get_borrowed(v___x_1316_, v___y_1314_, v___y_1315_);
v_prev_1318_ = l_Lean_Level_getLevelOffset(v_lvl_u2081_1317_);
v_prevK_1319_ = l_Lean_Level_getOffset(v_lvl_u2081_1317_);
v___x_1320_ = lean_nat_add(v___y_1315_, v___x_1312_);
lean_dec(v___y_1315_);
v___x_1321_ = l___private_Lean_Level_0__Lean_Level_mkMaxAux(v___y_1314_, v_k_1304_, v___x_1320_, v_prev_1318_, v_prevK_1319_, v___x_1316_);
lean_dec(v_k_1304_);
lean_dec_ref(v___y_1314_);
return v___x_1321_;
}
v___jp_1322_:
{
lean_object* v_firstNonExplicit_1324_; uint8_t v___x_1325_; 
v_firstNonExplicit_1324_ = l___private_Lean_Level_0__Lean_Level_skipExplicit(v___y_1323_, v___x_1308_);
lean_inc(v_firstNonExplicit_1324_);
v___x_1325_ = l___private_Lean_Level_0__Lean_Level_isExplicitSubsumed(v___y_1323_, v_firstNonExplicit_1324_);
if (v___x_1325_ == 0)
{
lean_object* v___x_1326_; 
v___x_1326_ = lean_nat_sub(v_firstNonExplicit_1324_, v___x_1312_);
lean_dec(v_firstNonExplicit_1324_);
v___y_1314_ = v___y_1323_;
v___y_1315_ = v___x_1326_;
goto v___jp_1313_;
}
else
{
v___y_1314_ = v___y_1323_;
v___y_1315_ = v_firstNonExplicit_1324_;
goto v___jp_1313_;
}
}
v___jp_1328_:
{
lean_object* v___x_1331_; 
v___x_1331_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1___redArg(v___x_1327_, v_lvls_1311_, v___y_1329_, v___y_1330_);
lean_dec(v___y_1330_);
v___y_1323_ = v___x_1331_;
goto v___jp_1322_;
}
}
case 3:
{
lean_object* v_a_1338_; lean_object* v_a_1339_; uint8_t v___x_1340_; 
v_a_1338_ = lean_ctor_get(v_u_1305_, 0);
lean_inc(v_a_1338_);
v_a_1339_ = lean_ctor_get(v_u_1305_, 1);
lean_inc(v_a_1339_);
lean_dec_ref_known(v_u_1305_, 2);
v___x_1340_ = l_Lean_Level_isNeverZero(v_a_1339_);
if (v___x_1340_ == 0)
{
lean_object* v_l_u2081_1341_; lean_object* v_l_u2082_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; 
v_l_u2081_1341_ = l_Lean_Level_normalize(v_a_1338_);
lean_dec(v_a_1338_);
v_l_u2082_1342_ = l_Lean_Level_normalize(v_a_1339_);
lean_dec(v_a_1339_);
v___x_1343_ = l___private_Lean_Level_0__Lean_Level_mkIMaxAux(v_l_u2081_1341_, v_l_u2082_1342_);
v___x_1344_ = l_Lean_Level_addOffsetAux(v_k_1304_, v___x_1343_);
return v___x_1344_;
}
else
{
lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; 
v___x_1345_ = l_Lean_Level_max___override(v_a_1338_, v_a_1339_);
v___x_1346_ = l_Lean_Level_normalize(v___x_1345_);
lean_dec(v___x_1345_);
v___x_1347_ = l_Lean_Level_addOffsetAux(v_k_1304_, v___x_1346_);
return v___x_1347_;
}
}
default: 
{
lean_object* v___x_1348_; lean_object* v___x_1349_; 
lean_dec(v_u_1305_);
lean_dec(v_k_1304_);
v___x_1348_ = lean_obj_once(&l_Lean_Level_normalize___closed__3, &l_Lean_Level_normalize___closed__3_once, _init_l_Lean_Level_normalize___closed__3);
v___x_1349_ = l_panic___at___00Lean_Level_normalize_spec__2(v___x_1348_);
return v___x_1349_;
}
}
}
else
{
lean_inc(v_l_1302_);
return v_l_1302_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_getMaxArgsAux___at___00Lean_Level_normalize_spec__0(lean_object* v_x_1350_, uint8_t v_x_1351_, lean_object* v_x_1352_){
_start:
{
if (lean_obj_tag(v_x_1350_) == 2)
{
lean_object* v_a_1353_; lean_object* v_a_1354_; lean_object* v___x_1355_; 
v_a_1353_ = lean_ctor_get(v_x_1350_, 0);
lean_inc(v_a_1353_);
v_a_1354_ = lean_ctor_get(v_x_1350_, 1);
lean_inc(v_a_1354_);
lean_dec_ref_known(v_x_1350_, 2);
v___x_1355_ = l___private_Lean_Level_0__Lean_Level_getMaxArgsAux___at___00Lean_Level_normalize_spec__0(v_a_1353_, v_x_1351_, v_x_1352_);
v_x_1350_ = v_a_1354_;
v_x_1352_ = v___x_1355_;
goto _start;
}
else
{
if (v_x_1351_ == 0)
{
lean_object* v___x_1357_; uint8_t v___x_1358_; 
v___x_1357_ = l_Lean_Level_normalize(v_x_1350_);
lean_dec(v_x_1350_);
v___x_1358_ = 1;
v_x_1350_ = v___x_1357_;
v_x_1351_ = v___x_1358_;
goto _start;
}
else
{
lean_object* v___x_1360_; 
v___x_1360_ = lean_array_push(v_x_1352_, v_x_1350_);
return v___x_1360_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_getMaxArgsAux___at___00Lean_Level_normalize_spec__0___boxed(lean_object* v_x_1361_, lean_object* v_x_1362_, lean_object* v_x_1363_){
_start:
{
uint8_t v_x_676__boxed_1364_; lean_object* v_res_1365_; 
v_x_676__boxed_1364_ = lean_unbox(v_x_1362_);
v_res_1365_ = l___private_Lean_Level_0__Lean_Level_getMaxArgsAux___at___00Lean_Level_normalize_spec__0(v_x_1361_, v_x_676__boxed_1364_, v_x_1363_);
return v_res_1365_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_normalize___boxed(lean_object* v_l_1366_){
_start:
{
lean_object* v_res_1367_; 
v_res_1367_ = l_Lean_Level_normalize(v_l_1366_);
lean_dec(v_l_1366_);
return v_res_1367_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1(lean_object* v_n_1368_, lean_object* v_as_1369_, lean_object* v_lo_1370_, lean_object* v_hi_1371_, lean_object* v_w_1372_, lean_object* v_hlo_1373_, lean_object* v_hhi_1374_){
_start:
{
lean_object* v___x_1375_; 
v___x_1375_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1___redArg(v_n_1368_, v_as_1369_, v_lo_1370_, v_hi_1371_);
return v___x_1375_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1___boxed(lean_object* v_n_1376_, lean_object* v_as_1377_, lean_object* v_lo_1378_, lean_object* v_hi_1379_, lean_object* v_w_1380_, lean_object* v_hlo_1381_, lean_object* v_hhi_1382_){
_start:
{
lean_object* v_res_1383_; 
v_res_1383_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1(v_n_1376_, v_as_1377_, v_lo_1378_, v_hi_1379_, v_w_1380_, v_hlo_1381_, v_hhi_1382_);
lean_dec(v_hi_1379_);
lean_dec(v_n_1376_);
return v_res_1383_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1_spec__1(lean_object* v_n_1384_, lean_object* v_lo_1385_, lean_object* v_hi_1386_, lean_object* v_hhi_1387_, lean_object* v_pivot_1388_, lean_object* v_as_1389_, lean_object* v_i_1390_, lean_object* v_k_1391_, lean_object* v_ilo_1392_, lean_object* v_ik_1393_, lean_object* v_w_1394_){
_start:
{
lean_object* v___x_1395_; 
v___x_1395_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1_spec__1___redArg(v_hi_1386_, v_pivot_1388_, v_as_1389_, v_i_1390_, v_k_1391_);
return v___x_1395_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1_spec__1___boxed(lean_object* v_n_1396_, lean_object* v_lo_1397_, lean_object* v_hi_1398_, lean_object* v_hhi_1399_, lean_object* v_pivot_1400_, lean_object* v_as_1401_, lean_object* v_i_1402_, lean_object* v_k_1403_, lean_object* v_ilo_1404_, lean_object* v_ik_1405_, lean_object* v_w_1406_){
_start:
{
lean_object* v_res_1407_; 
v_res_1407_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1_spec__1(v_n_1396_, v_lo_1397_, v_hi_1398_, v_hhi_1399_, v_pivot_1400_, v_as_1401_, v_i_1402_, v_k_1403_, v_ilo_1404_, v_ik_1405_, v_w_1406_);
lean_dec(v_pivot_1400_);
lean_dec(v_hi_1398_);
lean_dec(v_lo_1397_);
lean_dec(v_n_1396_);
return v_res_1407_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_isEquiv(lean_object* v_u_1408_, lean_object* v_v_1409_){
_start:
{
uint8_t v___x_1410_; 
v___x_1410_ = lean_level_eq(v_u_1408_, v_v_1409_);
if (v___x_1410_ == 0)
{
lean_object* v___x_1411_; lean_object* v___x_1412_; uint8_t v___x_1413_; 
v___x_1411_ = l_Lean_Level_normalize(v_u_1408_);
v___x_1412_ = l_Lean_Level_normalize(v_v_1409_);
v___x_1413_ = lean_level_eq(v___x_1411_, v___x_1412_);
lean_dec(v___x_1412_);
lean_dec(v___x_1411_);
return v___x_1413_;
}
else
{
return v___x_1410_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_isEquiv___boxed(lean_object* v_u_1414_, lean_object* v_v_1415_){
_start:
{
uint8_t v_res_1416_; lean_object* v_r_1417_; 
v_res_1416_ = l_Lean_Level_isEquiv(v_u_1414_, v_v_1415_);
lean_dec(v_v_1415_);
lean_dec(v_u_1414_);
v_r_1417_ = lean_box(v_res_1416_);
return v_r_1417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_dec(lean_object* v_x_1418_){
_start:
{
lean_object* v_l_u2081_1420_; lean_object* v_l_u2082_1421_; 
switch(lean_obj_tag(v_x_1418_))
{
case 0:
{
lean_object* v___x_1434_; 
v___x_1434_ = lean_box(0);
return v___x_1434_;
}
case 1:
{
lean_object* v_a_1435_; lean_object* v___x_1436_; 
v_a_1435_ = lean_ctor_get(v_x_1418_, 0);
lean_inc(v_a_1435_);
v___x_1436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1436_, 0, v_a_1435_);
return v___x_1436_;
}
case 2:
{
lean_object* v_a_1437_; lean_object* v_a_1438_; 
v_a_1437_ = lean_ctor_get(v_x_1418_, 0);
v_a_1438_ = lean_ctor_get(v_x_1418_, 1);
v_l_u2081_1420_ = v_a_1437_;
v_l_u2082_1421_ = v_a_1438_;
goto v___jp_1419_;
}
case 3:
{
lean_object* v_a_1439_; lean_object* v_a_1440_; 
v_a_1439_ = lean_ctor_get(v_x_1418_, 0);
v_a_1440_ = lean_ctor_get(v_x_1418_, 1);
v_l_u2081_1420_ = v_a_1439_;
v_l_u2082_1421_ = v_a_1440_;
goto v___jp_1419_;
}
default: 
{
lean_object* v___x_1441_; 
v___x_1441_ = lean_box(0);
return v___x_1441_;
}
}
v___jp_1419_:
{
lean_object* v___x_1422_; 
v___x_1422_ = l_Lean_Level_dec(v_l_u2081_1420_);
if (lean_obj_tag(v___x_1422_) == 0)
{
return v___x_1422_;
}
else
{
lean_object* v_val_1423_; lean_object* v___x_1424_; 
v_val_1423_ = lean_ctor_get(v___x_1422_, 0);
lean_inc(v_val_1423_);
lean_dec_ref_known(v___x_1422_, 1);
v___x_1424_ = l_Lean_Level_dec(v_l_u2082_1421_);
if (lean_obj_tag(v___x_1424_) == 0)
{
lean_dec(v_val_1423_);
return v___x_1424_;
}
else
{
lean_object* v_val_1425_; lean_object* v___x_1427_; uint8_t v_isShared_1428_; uint8_t v_isSharedCheck_1433_; 
v_val_1425_ = lean_ctor_get(v___x_1424_, 0);
v_isSharedCheck_1433_ = !lean_is_exclusive(v___x_1424_);
if (v_isSharedCheck_1433_ == 0)
{
v___x_1427_ = v___x_1424_;
v_isShared_1428_ = v_isSharedCheck_1433_;
goto v_resetjp_1426_;
}
else
{
lean_inc(v_val_1425_);
lean_dec(v___x_1424_);
v___x_1427_ = lean_box(0);
v_isShared_1428_ = v_isSharedCheck_1433_;
goto v_resetjp_1426_;
}
v_resetjp_1426_:
{
lean_object* v___x_1429_; lean_object* v___x_1431_; 
v___x_1429_ = l_Lean_Level_max___override(v_val_1423_, v_val_1425_);
if (v_isShared_1428_ == 0)
{
lean_ctor_set(v___x_1427_, 0, v___x_1429_);
v___x_1431_ = v___x_1427_;
goto v_reusejp_1430_;
}
else
{
lean_object* v_reuseFailAlloc_1432_; 
v_reuseFailAlloc_1432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1432_, 0, v___x_1429_);
v___x_1431_ = v_reuseFailAlloc_1432_;
goto v_reusejp_1430_;
}
v_reusejp_1430_:
{
return v___x_1431_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_dec___boxed(lean_object* v_x_1442_){
_start:
{
lean_object* v_res_1443_; 
v_res_1443_ = l_Lean_Level_dec(v_x_1442_);
lean_dec(v_x_1442_);
return v_res_1443_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_ctorIdx(lean_object* v_x_1444_){
_start:
{
switch(lean_obj_tag(v_x_1444_))
{
case 0:
{
lean_object* v___x_1445_; 
v___x_1445_ = lean_unsigned_to_nat(0u);
return v___x_1445_;
}
case 1:
{
lean_object* v___x_1446_; 
v___x_1446_ = lean_unsigned_to_nat(1u);
return v___x_1446_;
}
case 2:
{
lean_object* v___x_1447_; 
v___x_1447_ = lean_unsigned_to_nat(2u);
return v___x_1447_;
}
case 3:
{
lean_object* v___x_1448_; 
v___x_1448_ = lean_unsigned_to_nat(3u);
return v___x_1448_;
}
default: 
{
lean_object* v___x_1449_; 
v___x_1449_ = lean_unsigned_to_nat(4u);
return v___x_1449_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_ctorIdx___boxed(lean_object* v_x_1450_){
_start:
{
lean_object* v_res_1451_; 
v_res_1451_ = l_Lean_Level_PP_Result_ctorIdx(v_x_1450_);
lean_dec_ref(v_x_1450_);
return v_res_1451_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_ctorElim___redArg(lean_object* v_t_1452_, lean_object* v_k_1453_){
_start:
{
if (lean_obj_tag(v_t_1452_) == 2)
{
lean_object* v_a_1454_; lean_object* v_a_1455_; lean_object* v___x_1456_; 
v_a_1454_ = lean_ctor_get(v_t_1452_, 0);
lean_inc_ref(v_a_1454_);
v_a_1455_ = lean_ctor_get(v_t_1452_, 1);
lean_inc(v_a_1455_);
lean_dec_ref_known(v_t_1452_, 2);
v___x_1456_ = lean_apply_2(v_k_1453_, v_a_1454_, v_a_1455_);
return v___x_1456_;
}
else
{
lean_object* v_a_1457_; lean_object* v___x_1458_; 
v_a_1457_ = lean_ctor_get(v_t_1452_, 0);
lean_inc(v_a_1457_);
lean_dec_ref(v_t_1452_);
v___x_1458_ = lean_apply_1(v_k_1453_, v_a_1457_);
return v___x_1458_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_ctorElim(lean_object* v_motive__1_1459_, lean_object* v_ctorIdx_1460_, lean_object* v_t_1461_, lean_object* v_h_1462_, lean_object* v_k_1463_){
_start:
{
lean_object* v___x_1464_; 
v___x_1464_ = l_Lean_Level_PP_Result_ctorElim___redArg(v_t_1461_, v_k_1463_);
return v___x_1464_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_ctorElim___boxed(lean_object* v_motive__1_1465_, lean_object* v_ctorIdx_1466_, lean_object* v_t_1467_, lean_object* v_h_1468_, lean_object* v_k_1469_){
_start:
{
lean_object* v_res_1470_; 
v_res_1470_ = l_Lean_Level_PP_Result_ctorElim(v_motive__1_1465_, v_ctorIdx_1466_, v_t_1467_, v_h_1468_, v_k_1469_);
lean_dec(v_ctorIdx_1466_);
return v_res_1470_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_leaf_elim___redArg(lean_object* v_t_1471_, lean_object* v_leaf_1472_){
_start:
{
lean_object* v___x_1473_; 
v___x_1473_ = l_Lean_Level_PP_Result_ctorElim___redArg(v_t_1471_, v_leaf_1472_);
return v___x_1473_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_leaf_elim(lean_object* v_motive__1_1474_, lean_object* v_t_1475_, lean_object* v_h_1476_, lean_object* v_leaf_1477_){
_start:
{
lean_object* v___x_1478_; 
v___x_1478_ = l_Lean_Level_PP_Result_ctorElim___redArg(v_t_1475_, v_leaf_1477_);
return v___x_1478_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_num_elim___redArg(lean_object* v_t_1479_, lean_object* v_num_1480_){
_start:
{
lean_object* v___x_1481_; 
v___x_1481_ = l_Lean_Level_PP_Result_ctorElim___redArg(v_t_1479_, v_num_1480_);
return v___x_1481_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_num_elim(lean_object* v_motive__1_1482_, lean_object* v_t_1483_, lean_object* v_h_1484_, lean_object* v_num_1485_){
_start:
{
lean_object* v___x_1486_; 
v___x_1486_ = l_Lean_Level_PP_Result_ctorElim___redArg(v_t_1483_, v_num_1485_);
return v___x_1486_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_offset_elim___redArg(lean_object* v_t_1487_, lean_object* v_offset_1488_){
_start:
{
lean_object* v___x_1489_; 
v___x_1489_ = l_Lean_Level_PP_Result_ctorElim___redArg(v_t_1487_, v_offset_1488_);
return v___x_1489_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_offset_elim(lean_object* v_motive__1_1490_, lean_object* v_t_1491_, lean_object* v_h_1492_, lean_object* v_offset_1493_){
_start:
{
lean_object* v___x_1494_; 
v___x_1494_ = l_Lean_Level_PP_Result_ctorElim___redArg(v_t_1491_, v_offset_1493_);
return v___x_1494_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_maxNode_elim___redArg(lean_object* v_t_1495_, lean_object* v_maxNode_1496_){
_start:
{
lean_object* v___x_1497_; 
v___x_1497_ = l_Lean_Level_PP_Result_ctorElim___redArg(v_t_1495_, v_maxNode_1496_);
return v___x_1497_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_maxNode_elim(lean_object* v_motive__1_1498_, lean_object* v_t_1499_, lean_object* v_h_1500_, lean_object* v_maxNode_1501_){
_start:
{
lean_object* v___x_1502_; 
v___x_1502_ = l_Lean_Level_PP_Result_ctorElim___redArg(v_t_1499_, v_maxNode_1501_);
return v___x_1502_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_imaxNode_elim___redArg(lean_object* v_t_1503_, lean_object* v_imaxNode_1504_){
_start:
{
lean_object* v___x_1505_; 
v___x_1505_ = l_Lean_Level_PP_Result_ctorElim___redArg(v_t_1503_, v_imaxNode_1504_);
return v___x_1505_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_imaxNode_elim(lean_object* v_motive__1_1506_, lean_object* v_t_1507_, lean_object* v_h_1508_, lean_object* v_imaxNode_1509_){
_start:
{
lean_object* v___x_1510_; 
v___x_1510_ = l_Lean_Level_PP_Result_ctorElim___redArg(v_t_1507_, v_imaxNode_1509_);
return v___x_1510_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_succ(lean_object* v_x_1511_){
_start:
{
switch(lean_obj_tag(v_x_1511_))
{
case 2:
{
lean_object* v_a_1512_; lean_object* v_a_1513_; lean_object* v___x_1515_; uint8_t v_isShared_1516_; uint8_t v_isSharedCheck_1522_; 
v_a_1512_ = lean_ctor_get(v_x_1511_, 0);
v_a_1513_ = lean_ctor_get(v_x_1511_, 1);
v_isSharedCheck_1522_ = !lean_is_exclusive(v_x_1511_);
if (v_isSharedCheck_1522_ == 0)
{
v___x_1515_ = v_x_1511_;
v_isShared_1516_ = v_isSharedCheck_1522_;
goto v_resetjp_1514_;
}
else
{
lean_inc(v_a_1513_);
lean_inc(v_a_1512_);
lean_dec(v_x_1511_);
v___x_1515_ = lean_box(0);
v_isShared_1516_ = v_isSharedCheck_1522_;
goto v_resetjp_1514_;
}
v_resetjp_1514_:
{
lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1520_; 
v___x_1517_ = lean_unsigned_to_nat(1u);
v___x_1518_ = lean_nat_add(v_a_1513_, v___x_1517_);
lean_dec(v_a_1513_);
if (v_isShared_1516_ == 0)
{
lean_ctor_set(v___x_1515_, 1, v___x_1518_);
v___x_1520_ = v___x_1515_;
goto v_reusejp_1519_;
}
else
{
lean_object* v_reuseFailAlloc_1521_; 
v_reuseFailAlloc_1521_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1521_, 0, v_a_1512_);
lean_ctor_set(v_reuseFailAlloc_1521_, 1, v___x_1518_);
v___x_1520_ = v_reuseFailAlloc_1521_;
goto v_reusejp_1519_;
}
v_reusejp_1519_:
{
return v___x_1520_;
}
}
}
case 1:
{
lean_object* v_a_1523_; lean_object* v___x_1525_; uint8_t v_isShared_1526_; uint8_t v_isSharedCheck_1532_; 
v_a_1523_ = lean_ctor_get(v_x_1511_, 0);
v_isSharedCheck_1532_ = !lean_is_exclusive(v_x_1511_);
if (v_isSharedCheck_1532_ == 0)
{
v___x_1525_ = v_x_1511_;
v_isShared_1526_ = v_isSharedCheck_1532_;
goto v_resetjp_1524_;
}
else
{
lean_inc(v_a_1523_);
lean_dec(v_x_1511_);
v___x_1525_ = lean_box(0);
v_isShared_1526_ = v_isSharedCheck_1532_;
goto v_resetjp_1524_;
}
v_resetjp_1524_:
{
lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1530_; 
v___x_1527_ = lean_unsigned_to_nat(1u);
v___x_1528_ = lean_nat_add(v_a_1523_, v___x_1527_);
lean_dec(v_a_1523_);
if (v_isShared_1526_ == 0)
{
lean_ctor_set(v___x_1525_, 0, v___x_1528_);
v___x_1530_ = v___x_1525_;
goto v_reusejp_1529_;
}
else
{
lean_object* v_reuseFailAlloc_1531_; 
v_reuseFailAlloc_1531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1531_, 0, v___x_1528_);
v___x_1530_ = v_reuseFailAlloc_1531_;
goto v_reusejp_1529_;
}
v_reusejp_1529_:
{
return v___x_1530_;
}
}
}
default: 
{
lean_object* v___x_1533_; lean_object* v___x_1534_; 
v___x_1533_ = lean_unsigned_to_nat(1u);
v___x_1534_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1534_, 0, v_x_1511_);
lean_ctor_set(v___x_1534_, 1, v___x_1533_);
return v___x_1534_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_max(lean_object* v_x_1535_, lean_object* v_x_1536_){
_start:
{
if (lean_obj_tag(v_x_1536_) == 3)
{
lean_object* v_a_1537_; lean_object* v___x_1539_; uint8_t v_isShared_1540_; uint8_t v_isSharedCheck_1545_; 
v_a_1537_ = lean_ctor_get(v_x_1536_, 0);
v_isSharedCheck_1545_ = !lean_is_exclusive(v_x_1536_);
if (v_isSharedCheck_1545_ == 0)
{
v___x_1539_ = v_x_1536_;
v_isShared_1540_ = v_isSharedCheck_1545_;
goto v_resetjp_1538_;
}
else
{
lean_inc(v_a_1537_);
lean_dec(v_x_1536_);
v___x_1539_ = lean_box(0);
v_isShared_1540_ = v_isSharedCheck_1545_;
goto v_resetjp_1538_;
}
v_resetjp_1538_:
{
lean_object* v___x_1541_; lean_object* v___x_1543_; 
v___x_1541_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1541_, 0, v_x_1535_);
lean_ctor_set(v___x_1541_, 1, v_a_1537_);
if (v_isShared_1540_ == 0)
{
lean_ctor_set(v___x_1539_, 0, v___x_1541_);
v___x_1543_ = v___x_1539_;
goto v_reusejp_1542_;
}
else
{
lean_object* v_reuseFailAlloc_1544_; 
v_reuseFailAlloc_1544_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1544_, 0, v___x_1541_);
v___x_1543_ = v_reuseFailAlloc_1544_;
goto v_reusejp_1542_;
}
v_reusejp_1542_:
{
return v___x_1543_;
}
}
}
else
{
lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; 
v___x_1546_ = lean_box(0);
v___x_1547_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1547_, 0, v_x_1536_);
lean_ctor_set(v___x_1547_, 1, v___x_1546_);
v___x_1548_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1548_, 0, v_x_1535_);
lean_ctor_set(v___x_1548_, 1, v___x_1547_);
v___x_1549_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1549_, 0, v___x_1548_);
return v___x_1549_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_imax(lean_object* v_x_1550_, lean_object* v_x_1551_){
_start:
{
if (lean_obj_tag(v_x_1551_) == 4)
{
lean_object* v_a_1552_; lean_object* v___x_1554_; uint8_t v_isShared_1555_; uint8_t v_isSharedCheck_1560_; 
v_a_1552_ = lean_ctor_get(v_x_1551_, 0);
v_isSharedCheck_1560_ = !lean_is_exclusive(v_x_1551_);
if (v_isSharedCheck_1560_ == 0)
{
v___x_1554_ = v_x_1551_;
v_isShared_1555_ = v_isSharedCheck_1560_;
goto v_resetjp_1553_;
}
else
{
lean_inc(v_a_1552_);
lean_dec(v_x_1551_);
v___x_1554_ = lean_box(0);
v_isShared_1555_ = v_isSharedCheck_1560_;
goto v_resetjp_1553_;
}
v_resetjp_1553_:
{
lean_object* v___x_1556_; lean_object* v___x_1558_; 
v___x_1556_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1556_, 0, v_x_1550_);
lean_ctor_set(v___x_1556_, 1, v_a_1552_);
if (v_isShared_1555_ == 0)
{
lean_ctor_set(v___x_1554_, 0, v___x_1556_);
v___x_1558_ = v___x_1554_;
goto v_reusejp_1557_;
}
else
{
lean_object* v_reuseFailAlloc_1559_; 
v_reuseFailAlloc_1559_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1559_, 0, v___x_1556_);
v___x_1558_ = v_reuseFailAlloc_1559_;
goto v_reusejp_1557_;
}
v_reusejp_1557_:
{
return v___x_1558_;
}
}
}
else
{
lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; 
v___x_1561_ = lean_box(0);
v___x_1562_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1562_, 0, v_x_1551_);
lean_ctor_set(v___x_1562_, 1, v___x_1561_);
v___x_1563_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1563_, 0, v_x_1550_);
lean_ctor_set(v___x_1563_, 1, v___x_1562_);
v___x_1564_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1564_, 0, v___x_1563_);
return v___x_1564_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_toResult(lean_object* v_l_1583_, lean_object* v_a_1584_){
_start:
{
switch(lean_obj_tag(v_l_1583_))
{
case 0:
{
lean_object* v___x_1585_; 
v___x_1585_ = ((lean_object*)(l_Lean_Level_PP_toResult___closed__0));
return v___x_1585_;
}
case 1:
{
lean_object* v_a_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; 
v_a_1586_ = lean_ctor_get(v_l_1583_, 0);
lean_inc(v_a_1586_);
lean_dec_ref_known(v_l_1583_, 1);
v___x_1587_ = l_Lean_Level_PP_toResult(v_a_1586_, v_a_1584_);
v___x_1588_ = l_Lean_Level_PP_Result_succ(v___x_1587_);
return v___x_1588_;
}
case 2:
{
lean_object* v_a_1589_; lean_object* v_a_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; 
v_a_1589_ = lean_ctor_get(v_l_1583_, 0);
lean_inc(v_a_1589_);
v_a_1590_ = lean_ctor_get(v_l_1583_, 1);
lean_inc(v_a_1590_);
lean_dec_ref_known(v_l_1583_, 2);
v___x_1591_ = l_Lean_Level_PP_toResult(v_a_1589_, v_a_1584_);
v___x_1592_ = l_Lean_Level_PP_toResult(v_a_1590_, v_a_1584_);
v___x_1593_ = l_Lean_Level_PP_Result_max(v___x_1591_, v___x_1592_);
return v___x_1593_;
}
case 3:
{
lean_object* v_a_1594_; lean_object* v_a_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; 
v_a_1594_ = lean_ctor_get(v_l_1583_, 0);
lean_inc(v_a_1594_);
v_a_1595_ = lean_ctor_get(v_l_1583_, 1);
lean_inc(v_a_1595_);
lean_dec_ref_known(v_l_1583_, 2);
v___x_1596_ = l_Lean_Level_PP_toResult(v_a_1594_, v_a_1584_);
v___x_1597_ = l_Lean_Level_PP_toResult(v_a_1595_, v_a_1584_);
v___x_1598_ = l_Lean_Level_PP_Result_imax(v___x_1596_, v___x_1597_);
return v___x_1598_;
}
case 4:
{
lean_object* v_a_1599_; lean_object* v___x_1600_; 
v_a_1599_ = lean_ctor_get(v_l_1583_, 0);
lean_inc(v_a_1599_);
lean_dec_ref_known(v_l_1583_, 1);
v___x_1600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1600_, 0, v_a_1599_);
return v___x_1600_;
}
default: 
{
lean_object* v_a_1601_; uint8_t v_mvars_1602_; lean_object* v_lIndex_x3f_1603_; uint8_t v___x_1604_; 
v_a_1601_ = lean_ctor_get(v_l_1583_, 0);
lean_inc(v_a_1601_);
lean_dec_ref_known(v_l_1583_, 1);
v_mvars_1602_ = lean_ctor_get_uint8(v_a_1584_, sizeof(void*)*1);
v_lIndex_x3f_1603_ = lean_ctor_get(v_a_1584_, 0);
v___x_1604_ = lean_bool_not(v_mvars_1602_);
if (v___x_1604_ == 0)
{
lean_object* v___x_1605_; 
lean_inc_ref(v_lIndex_x3f_1603_);
lean_inc(v_a_1601_);
v___x_1605_ = lean_apply_1(v_lIndex_x3f_1603_, v_a_1601_);
if (lean_obj_tag(v___x_1605_) == 1)
{
lean_object* v_val_1606_; lean_object* v___x_1608_; uint8_t v_isShared_1609_; uint8_t v_isSharedCheck_1617_; 
lean_dec(v_a_1601_);
v_val_1606_ = lean_ctor_get(v___x_1605_, 0);
v_isSharedCheck_1617_ = !lean_is_exclusive(v___x_1605_);
if (v_isSharedCheck_1617_ == 0)
{
v___x_1608_ = v___x_1605_;
v_isShared_1609_ = v_isSharedCheck_1617_;
goto v_resetjp_1607_;
}
else
{
lean_inc(v_val_1606_);
lean_dec(v___x_1605_);
v___x_1608_ = lean_box(0);
v_isShared_1609_ = v_isSharedCheck_1617_;
goto v_resetjp_1607_;
}
v_resetjp_1607_:
{
lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1615_; 
v___x_1610_ = ((lean_object*)(l_Lean_Level_PP_toResult___closed__2));
v___x_1611_ = lean_unsigned_to_nat(1u);
v___x_1612_ = lean_nat_add(v_val_1606_, v___x_1611_);
lean_dec(v_val_1606_);
v___x_1613_ = l_Lean_Name_num___override(v___x_1610_, v___x_1612_);
if (v_isShared_1609_ == 0)
{
lean_ctor_set_tag(v___x_1608_, 0);
lean_ctor_set(v___x_1608_, 0, v___x_1613_);
v___x_1615_ = v___x_1608_;
goto v_reusejp_1614_;
}
else
{
lean_object* v_reuseFailAlloc_1616_; 
v_reuseFailAlloc_1616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1616_, 0, v___x_1613_);
v___x_1615_ = v_reuseFailAlloc_1616_;
goto v_reusejp_1614_;
}
v_reusejp_1614_:
{
return v___x_1615_;
}
}
}
else
{
lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; 
lean_dec(v___x_1605_);
v___x_1618_ = ((lean_object*)(l_Lean_Level_PP_toResult___closed__4));
v___x_1619_ = ((lean_object*)(l_Lean_Level_PP_toResult___closed__6));
v___x_1620_ = l_Lean_Name_replacePrefix(v_a_1601_, v___x_1618_, v___x_1619_);
v___x_1621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1621_, 0, v___x_1620_);
return v___x_1621_;
}
}
else
{
lean_object* v___x_1622_; 
lean_dec(v_a_1601_);
v___x_1622_ = ((lean_object*)(l_Lean_Level_PP_toResult___closed__9));
return v___x_1622_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_toResult___boxed(lean_object* v_l_1623_, lean_object* v_a_1624_){
_start:
{
lean_object* v_res_1625_; 
v_res_1625_ = l_Lean_Level_PP_toResult(v_l_1623_, v_a_1624_);
lean_dec_ref(v_a_1624_);
return v_res_1625_;
}
}
static lean_object* _init_l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__1(void){
_start:
{
lean_object* v___x_1627_; lean_object* v___x_1628_; 
v___x_1627_ = ((lean_object*)(l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__0));
v___x_1628_ = lean_string_length(v___x_1627_);
return v___x_1628_;
}
}
static lean_object* _init_l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__2(void){
_start:
{
lean_object* v___x_1629_; lean_object* v___x_1630_; 
v___x_1629_ = lean_obj_once(&l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__1, &l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__1_once, _init_l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__1);
v___x_1630_ = lean_nat_to_int(v___x_1629_);
return v___x_1630_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse(lean_object* v_x_1635_, uint8_t v_x_1636_){
_start:
{
if (v_x_1636_ == 0)
{
lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; uint8_t v___x_1643_; lean_object* v___x_1644_; 
v___x_1637_ = lean_obj_once(&l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__2, &l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__2_once, _init_l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__2);
v___x_1638_ = ((lean_object*)(l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__3));
v___x_1639_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1639_, 0, v___x_1638_);
lean_ctor_set(v___x_1639_, 1, v_x_1635_);
v___x_1640_ = ((lean_object*)(l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__4));
v___x_1641_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1641_, 0, v___x_1639_);
lean_ctor_set(v___x_1641_, 1, v___x_1640_);
v___x_1642_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1642_, 0, v___x_1637_);
lean_ctor_set(v___x_1642_, 1, v___x_1641_);
v___x_1643_ = 0;
v___x_1644_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1644_, 0, v___x_1642_);
lean_ctor_set_uint8(v___x_1644_, sizeof(void*)*1, v___x_1643_);
return v___x_1644_;
}
else
{
return v_x_1635_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___boxed(lean_object* v_x_1645_, lean_object* v_x_1646_){
_start:
{
uint8_t v_x_57__boxed_1647_; lean_object* v_res_1648_; 
v_x_57__boxed_1647_ = lean_unbox(v_x_1646_);
v_res_1648_ = l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse(v_x_1645_, v_x_57__boxed_1647_);
return v_res_1648_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_format(lean_object* v_x_1658_, uint8_t v_x_1659_){
_start:
{
switch(lean_obj_tag(v_x_1658_))
{
case 0:
{
lean_object* v_a_1660_; lean_object* v___x_1662_; uint8_t v_isShared_1663_; uint8_t v_isSharedCheck_1669_; 
v_a_1660_ = lean_ctor_get(v_x_1658_, 0);
v_isSharedCheck_1669_ = !lean_is_exclusive(v_x_1658_);
if (v_isSharedCheck_1669_ == 0)
{
v___x_1662_ = v_x_1658_;
v_isShared_1663_ = v_isSharedCheck_1669_;
goto v_resetjp_1661_;
}
else
{
lean_inc(v_a_1660_);
lean_dec(v_x_1658_);
v___x_1662_ = lean_box(0);
v_isShared_1663_ = v_isSharedCheck_1669_;
goto v_resetjp_1661_;
}
v_resetjp_1661_:
{
uint8_t v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1667_; 
v___x_1664_ = 1;
v___x_1665_ = l_Lean_Name_toString(v_a_1660_, v___x_1664_);
if (v_isShared_1663_ == 0)
{
lean_ctor_set_tag(v___x_1662_, 3);
lean_ctor_set(v___x_1662_, 0, v___x_1665_);
v___x_1667_ = v___x_1662_;
goto v_reusejp_1666_;
}
else
{
lean_object* v_reuseFailAlloc_1668_; 
v_reuseFailAlloc_1668_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1668_, 0, v___x_1665_);
v___x_1667_ = v_reuseFailAlloc_1668_;
goto v_reusejp_1666_;
}
v_reusejp_1666_:
{
return v___x_1667_;
}
}
}
case 1:
{
lean_object* v_a_1670_; lean_object* v___x_1672_; uint8_t v_isShared_1673_; uint8_t v_isSharedCheck_1678_; 
v_a_1670_ = lean_ctor_get(v_x_1658_, 0);
v_isSharedCheck_1678_ = !lean_is_exclusive(v_x_1658_);
if (v_isSharedCheck_1678_ == 0)
{
v___x_1672_ = v_x_1658_;
v_isShared_1673_ = v_isSharedCheck_1678_;
goto v_resetjp_1671_;
}
else
{
lean_inc(v_a_1670_);
lean_dec(v_x_1658_);
v___x_1672_ = lean_box(0);
v_isShared_1673_ = v_isSharedCheck_1678_;
goto v_resetjp_1671_;
}
v_resetjp_1671_:
{
lean_object* v___x_1674_; lean_object* v___x_1676_; 
v___x_1674_ = l_Nat_reprFast(v_a_1670_);
if (v_isShared_1673_ == 0)
{
lean_ctor_set_tag(v___x_1672_, 3);
lean_ctor_set(v___x_1672_, 0, v___x_1674_);
v___x_1676_ = v___x_1672_;
goto v_reusejp_1675_;
}
else
{
lean_object* v_reuseFailAlloc_1677_; 
v_reuseFailAlloc_1677_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1677_, 0, v___x_1674_);
v___x_1676_ = v_reuseFailAlloc_1677_;
goto v_reusejp_1675_;
}
v_reusejp_1675_:
{
return v___x_1676_;
}
}
}
case 2:
{
lean_object* v_a_1679_; lean_object* v_a_1680_; lean_object* v___x_1682_; uint8_t v_isShared_1683_; uint8_t v_isSharedCheck_1699_; 
v_a_1679_ = lean_ctor_get(v_x_1658_, 0);
v_a_1680_ = lean_ctor_get(v_x_1658_, 1);
v_isSharedCheck_1699_ = !lean_is_exclusive(v_x_1658_);
if (v_isSharedCheck_1699_ == 0)
{
v___x_1682_ = v_x_1658_;
v_isShared_1683_ = v_isSharedCheck_1699_;
goto v_resetjp_1681_;
}
else
{
lean_inc(v_a_1680_);
lean_inc(v_a_1679_);
lean_dec(v_x_1658_);
v___x_1682_ = lean_box(0);
v_isShared_1683_ = v_isSharedCheck_1699_;
goto v_resetjp_1681_;
}
v_resetjp_1681_:
{
lean_object* v_zero_1684_; uint8_t v_isZero_1685_; 
v_zero_1684_ = lean_unsigned_to_nat(0u);
v_isZero_1685_ = lean_nat_dec_eq(v_a_1680_, v_zero_1684_);
if (v_isZero_1685_ == 1)
{
lean_del_object(v___x_1682_);
lean_dec(v_a_1680_);
v_x_1658_ = v_a_1679_;
goto _start;
}
else
{
lean_object* v_one_1687_; lean_object* v_n_1688_; lean_object* v_f_x27_1689_; lean_object* v___x_1690_; lean_object* v___x_1692_; 
v_one_1687_ = lean_unsigned_to_nat(1u);
v_n_1688_ = lean_nat_sub(v_a_1680_, v_one_1687_);
lean_dec(v_a_1680_);
v_f_x27_1689_ = l_Lean_Level_PP_Result_format(v_a_1679_, v_isZero_1685_);
v___x_1690_ = ((lean_object*)(l_Lean_Level_PP_Result_format___closed__1));
if (v_isShared_1683_ == 0)
{
lean_ctor_set_tag(v___x_1682_, 5);
lean_ctor_set(v___x_1682_, 1, v___x_1690_);
lean_ctor_set(v___x_1682_, 0, v_f_x27_1689_);
v___x_1692_ = v___x_1682_;
goto v_reusejp_1691_;
}
else
{
lean_object* v_reuseFailAlloc_1698_; 
v_reuseFailAlloc_1698_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1698_, 0, v_f_x27_1689_);
lean_ctor_set(v_reuseFailAlloc_1698_, 1, v___x_1690_);
v___x_1692_ = v_reuseFailAlloc_1698_;
goto v_reusejp_1691_;
}
v_reusejp_1691_:
{
lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; 
v___x_1693_ = lean_nat_add(v_n_1688_, v_one_1687_);
lean_dec(v_n_1688_);
v___x_1694_ = l_Nat_reprFast(v___x_1693_);
v___x_1695_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1695_, 0, v___x_1694_);
v___x_1696_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1696_, 0, v___x_1692_);
lean_ctor_set(v___x_1696_, 1, v___x_1695_);
v___x_1697_ = l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse(v___x_1696_, v_x_1659_);
return v___x_1697_;
}
}
}
}
case 3:
{
lean_object* v_a_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; uint8_t v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; 
v_a_1700_ = lean_ctor_get(v_x_1658_, 0);
lean_inc(v_a_1700_);
lean_dec_ref_known(v_x_1658_, 1);
v___x_1701_ = ((lean_object*)(l_Lean_Level_PP_Result_format___closed__3));
v___x_1702_ = l___private_Lean_Level_0__Lean_Level_PP_Result_formatLst(v_a_1700_);
v___x_1703_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1703_, 0, v___x_1701_);
lean_ctor_set(v___x_1703_, 1, v___x_1702_);
v___x_1704_ = 0;
v___x_1705_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1705_, 0, v___x_1703_);
lean_ctor_set_uint8(v___x_1705_, sizeof(void*)*1, v___x_1704_);
v___x_1706_ = l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse(v___x_1705_, v_x_1659_);
return v___x_1706_;
}
default: 
{
lean_object* v_a_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; uint8_t v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; 
v_a_1707_ = lean_ctor_get(v_x_1658_, 0);
lean_inc(v_a_1707_);
lean_dec_ref_known(v_x_1658_, 1);
v___x_1708_ = ((lean_object*)(l_Lean_Level_PP_Result_format___closed__5));
v___x_1709_ = l___private_Lean_Level_0__Lean_Level_PP_Result_formatLst(v_a_1707_);
v___x_1710_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1710_, 0, v___x_1708_);
lean_ctor_set(v___x_1710_, 1, v___x_1709_);
v___x_1711_ = 0;
v___x_1712_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1712_, 0, v___x_1710_);
lean_ctor_set_uint8(v___x_1712_, sizeof(void*)*1, v___x_1711_);
v___x_1713_ = l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse(v___x_1712_, v_x_1659_);
return v___x_1713_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_PP_Result_formatLst(lean_object* v_x_1714_){
_start:
{
if (lean_obj_tag(v_x_1714_) == 0)
{
lean_object* v___x_1715_; 
v___x_1715_ = lean_box(0);
return v___x_1715_;
}
else
{
lean_object* v_head_1716_; lean_object* v_tail_1717_; lean_object* v___x_1719_; uint8_t v_isShared_1720_; uint8_t v_isSharedCheck_1729_; 
v_head_1716_ = lean_ctor_get(v_x_1714_, 0);
v_tail_1717_ = lean_ctor_get(v_x_1714_, 1);
v_isSharedCheck_1729_ = !lean_is_exclusive(v_x_1714_);
if (v_isSharedCheck_1729_ == 0)
{
v___x_1719_ = v_x_1714_;
v_isShared_1720_ = v_isSharedCheck_1729_;
goto v_resetjp_1718_;
}
else
{
lean_inc(v_tail_1717_);
lean_inc(v_head_1716_);
lean_dec(v_x_1714_);
v___x_1719_ = lean_box(0);
v_isShared_1720_ = v_isSharedCheck_1729_;
goto v_resetjp_1718_;
}
v_resetjp_1718_:
{
lean_object* v___x_1721_; uint8_t v___x_1722_; lean_object* v___x_1723_; lean_object* v___x_1725_; 
v___x_1721_ = lean_box(1);
v___x_1722_ = 0;
v___x_1723_ = l_Lean_Level_PP_Result_format(v_head_1716_, v___x_1722_);
if (v_isShared_1720_ == 0)
{
lean_ctor_set_tag(v___x_1719_, 5);
lean_ctor_set(v___x_1719_, 1, v___x_1723_);
lean_ctor_set(v___x_1719_, 0, v___x_1721_);
v___x_1725_ = v___x_1719_;
goto v_reusejp_1724_;
}
else
{
lean_object* v_reuseFailAlloc_1728_; 
v_reuseFailAlloc_1728_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1728_, 0, v___x_1721_);
lean_ctor_set(v_reuseFailAlloc_1728_, 1, v___x_1723_);
v___x_1725_ = v_reuseFailAlloc_1728_;
goto v_reusejp_1724_;
}
v_reusejp_1724_:
{
lean_object* v___x_1726_; lean_object* v___x_1727_; 
v___x_1726_ = l___private_Lean_Level_0__Lean_Level_PP_Result_formatLst(v_tail_1717_);
v___x_1727_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1727_, 0, v___x_1725_);
lean_ctor_set(v___x_1727_, 1, v___x_1726_);
return v___x_1727_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_format___boxed(lean_object* v_x_1730_, lean_object* v_x_1731_){
_start:
{
uint8_t v_x_270__boxed_1732_; lean_object* v_res_1733_; 
v_x_270__boxed_1732_ = lean_unbox(v_x_1731_);
v_res_1733_ = l_Lean_Level_PP_Result_format(v_x_1730_, v_x_270__boxed_1732_);
return v_res_1733_;
}
}
static lean_object* _init_l_Lean_Level_PP_Result_quote___closed__0(void){
_start:
{
uint8_t v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; 
v___x_1734_ = 0;
v___x_1735_ = lean_box(0);
v___x_1736_ = l_Lean_SourceInfo_fromRef(v___x_1735_, v___x_1734_);
return v___x_1736_;
}
}
static lean_object* _init_l_Lean_Level_PP_Result_quote___closed__6(void){
_start:
{
lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; 
v___x_1746_ = ((lean_object*)(l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__0));
v___x_1747_ = lean_obj_once(&l_Lean_Level_PP_Result_quote___closed__0, &l_Lean_Level_PP_Result_quote___closed__0_once, _init_l_Lean_Level_PP_Result_quote___closed__0);
v___x_1748_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1748_, 0, v___x_1747_);
lean_ctor_set(v___x_1748_, 1, v___x_1746_);
return v___x_1748_;
}
}
static lean_object* _init_l_Lean_Level_PP_Result_quote___closed__7(void){
_start:
{
lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; 
v___x_1749_ = ((lean_object*)(l_Lean_instReprData___lam__0___closed__0));
v___x_1750_ = lean_obj_once(&l_Lean_Level_PP_Result_quote___closed__0, &l_Lean_Level_PP_Result_quote___closed__0_once, _init_l_Lean_Level_PP_Result_quote___closed__0);
v___x_1751_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1751_, 0, v___x_1750_);
lean_ctor_set(v___x_1751_, 1, v___x_1749_);
return v___x_1751_;
}
}
static lean_object* _init_l_Lean_Level_PP_Result_quote___closed__12(void){
_start:
{
lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; 
v___x_1764_ = ((lean_object*)(l_Lean_Level_PP_Result_format___closed__2));
v___x_1765_ = lean_obj_once(&l_Lean_Level_PP_Result_quote___closed__0, &l_Lean_Level_PP_Result_quote___closed__0_once, _init_l_Lean_Level_PP_Result_quote___closed__0);
v___x_1766_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1766_, 0, v___x_1765_);
lean_ctor_set(v___x_1766_, 1, v___x_1764_);
return v___x_1766_;
}
}
static lean_object* _init_l_Lean_Level_PP_Result_quote___closed__15(void){
_start:
{
lean_object* v___x_1770_; 
v___x_1770_ = l_Array_mkArray0(lean_box(0));
return v___x_1770_;
}
}
static lean_object* _init_l_Lean_Level_PP_Result_quote___closed__17(void){
_start:
{
lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; 
v___x_1776_ = ((lean_object*)(l_Lean_Level_PP_Result_format___closed__4));
v___x_1777_ = lean_obj_once(&l_Lean_Level_PP_Result_quote___closed__0, &l_Lean_Level_PP_Result_quote___closed__0_once, _init_l_Lean_Level_PP_Result_quote___closed__0);
v___x_1778_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1778_, 0, v___x_1777_);
lean_ctor_set(v___x_1778_, 1, v___x_1776_);
return v___x_1778_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_quote(lean_object* v_r_1779_, lean_object* v_prec_1780_){
_start:
{
lean_object* v_s_1782_; 
switch(lean_obj_tag(v_r_1779_))
{
case 0:
{
lean_object* v_a_1790_; lean_object* v___x_1791_; 
v_a_1790_ = lean_ctor_get(v_r_1779_, 0);
lean_inc(v_a_1790_);
lean_dec_ref_known(v_r_1779_, 1);
v___x_1791_ = l_Lean_mkIdent(v_a_1790_);
return v___x_1791_;
}
case 1:
{
lean_object* v_a_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; 
v_a_1792_ = lean_ctor_get(v_r_1779_, 0);
lean_inc(v_a_1792_);
lean_dec_ref_known(v_r_1779_, 1);
v___x_1793_ = l_Nat_reprFast(v_a_1792_);
v___x_1794_ = lean_box(2);
v___x_1795_ = l_Lean_Syntax_mkNumLit(v___x_1793_, v___x_1794_);
return v___x_1795_;
}
case 2:
{
lean_object* v_a_1796_; lean_object* v_a_1797_; lean_object* v___x_1799_; uint8_t v_isShared_1800_; uint8_t v_isSharedCheck_1820_; 
v_a_1796_ = lean_ctor_get(v_r_1779_, 0);
v_a_1797_ = lean_ctor_get(v_r_1779_, 1);
v_isSharedCheck_1820_ = !lean_is_exclusive(v_r_1779_);
if (v_isSharedCheck_1820_ == 0)
{
v___x_1799_ = v_r_1779_;
v_isShared_1800_ = v_isSharedCheck_1820_;
goto v_resetjp_1798_;
}
else
{
lean_inc(v_a_1797_);
lean_inc(v_a_1796_);
lean_dec(v_r_1779_);
v___x_1799_ = lean_box(0);
v_isShared_1800_ = v_isSharedCheck_1820_;
goto v_resetjp_1798_;
}
v_resetjp_1798_:
{
lean_object* v_zero_1801_; uint8_t v_isZero_1802_; 
v_zero_1801_ = lean_unsigned_to_nat(0u);
v_isZero_1802_ = lean_nat_dec_eq(v_a_1797_, v_zero_1801_);
if (v_isZero_1802_ == 1)
{
lean_del_object(v___x_1799_);
lean_dec(v_a_1797_);
v_r_1779_ = v_a_1796_;
goto _start;
}
else
{
lean_object* v_one_1804_; lean_object* v_n_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1813_; 
v_one_1804_ = lean_unsigned_to_nat(1u);
v_n_1805_ = lean_nat_sub(v_a_1797_, v_one_1804_);
lean_dec(v_a_1797_);
v___x_1806_ = lean_box(0);
v___x_1807_ = l_Lean_SourceInfo_fromRef(v___x_1806_, v_isZero_1802_);
v___x_1808_ = ((lean_object*)(l_Lean_Level_PP_Result_quote___closed__9));
v___x_1809_ = lean_unsigned_to_nat(65u);
v___x_1810_ = l_Lean_Level_PP_Result_quote(v_a_1796_, v___x_1809_);
v___x_1811_ = ((lean_object*)(l_Lean_Level_PP_Result_quote___closed__10));
lean_inc(v___x_1807_);
if (v_isShared_1800_ == 0)
{
lean_ctor_set(v___x_1799_, 1, v___x_1811_);
lean_ctor_set(v___x_1799_, 0, v___x_1807_);
v___x_1813_ = v___x_1799_;
goto v_reusejp_1812_;
}
else
{
lean_object* v_reuseFailAlloc_1819_; 
v_reuseFailAlloc_1819_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1819_, 0, v___x_1807_);
lean_ctor_set(v_reuseFailAlloc_1819_, 1, v___x_1811_);
v___x_1813_ = v_reuseFailAlloc_1819_;
goto v_reusejp_1812_;
}
v_reusejp_1812_:
{
lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; 
v___x_1814_ = lean_nat_add(v_n_1805_, v_one_1804_);
lean_dec(v_n_1805_);
v___x_1815_ = l_Nat_reprFast(v___x_1814_);
v___x_1816_ = lean_box(2);
v___x_1817_ = l_Lean_Syntax_mkNumLit(v___x_1815_, v___x_1816_);
v___x_1818_ = l_Lean_Syntax_node3(v___x_1807_, v___x_1808_, v___x_1810_, v___x_1813_, v___x_1817_);
v_s_1782_ = v___x_1818_;
goto v___jp_1781_;
}
}
}
}
case 3:
{
lean_object* v_a_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; size_t v_sz_1828_; size_t v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; 
v_a_1821_ = lean_ctor_get(v_r_1779_, 0);
lean_inc(v_a_1821_);
lean_dec_ref_known(v_r_1779_, 1);
v___x_1822_ = lean_obj_once(&l_Lean_Level_PP_Result_quote___closed__0, &l_Lean_Level_PP_Result_quote___closed__0_once, _init_l_Lean_Level_PP_Result_quote___closed__0);
v___x_1823_ = ((lean_object*)(l_Lean_Level_PP_Result_quote___closed__11));
v___x_1824_ = lean_obj_once(&l_Lean_Level_PP_Result_quote___closed__12, &l_Lean_Level_PP_Result_quote___closed__12_once, _init_l_Lean_Level_PP_Result_quote___closed__12);
v___x_1825_ = ((lean_object*)(l_Lean_Level_PP_Result_quote___closed__14));
v___x_1826_ = lean_obj_once(&l_Lean_Level_PP_Result_quote___closed__15, &l_Lean_Level_PP_Result_quote___closed__15_once, _init_l_Lean_Level_PP_Result_quote___closed__15);
v___x_1827_ = lean_array_mk(v_a_1821_);
v_sz_1828_ = lean_array_size(v___x_1827_);
v___x_1829_ = ((size_t)0ULL);
v___x_1830_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Level_PP_Result_quote_spec__0(v_sz_1828_, v___x_1829_, v___x_1827_);
v___x_1831_ = l_Array_append___redArg(v___x_1826_, v___x_1830_);
lean_dec_ref(v___x_1830_);
v___x_1832_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1832_, 0, v___x_1822_);
lean_ctor_set(v___x_1832_, 1, v___x_1825_);
lean_ctor_set(v___x_1832_, 2, v___x_1831_);
v___x_1833_ = l_Lean_Syntax_node2(v___x_1822_, v___x_1823_, v___x_1824_, v___x_1832_);
v_s_1782_ = v___x_1833_;
goto v___jp_1781_;
}
default: 
{
lean_object* v_a_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; size_t v_sz_1841_; size_t v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; 
v_a_1834_ = lean_ctor_get(v_r_1779_, 0);
lean_inc(v_a_1834_);
lean_dec_ref_known(v_r_1779_, 1);
v___x_1835_ = lean_obj_once(&l_Lean_Level_PP_Result_quote___closed__0, &l_Lean_Level_PP_Result_quote___closed__0_once, _init_l_Lean_Level_PP_Result_quote___closed__0);
v___x_1836_ = ((lean_object*)(l_Lean_Level_PP_Result_quote___closed__16));
v___x_1837_ = lean_obj_once(&l_Lean_Level_PP_Result_quote___closed__17, &l_Lean_Level_PP_Result_quote___closed__17_once, _init_l_Lean_Level_PP_Result_quote___closed__17);
v___x_1838_ = ((lean_object*)(l_Lean_Level_PP_Result_quote___closed__14));
v___x_1839_ = lean_obj_once(&l_Lean_Level_PP_Result_quote___closed__15, &l_Lean_Level_PP_Result_quote___closed__15_once, _init_l_Lean_Level_PP_Result_quote___closed__15);
v___x_1840_ = lean_array_mk(v_a_1834_);
v_sz_1841_ = lean_array_size(v___x_1840_);
v___x_1842_ = ((size_t)0ULL);
v___x_1843_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Level_PP_Result_quote_spec__0(v_sz_1841_, v___x_1842_, v___x_1840_);
v___x_1844_ = l_Array_append___redArg(v___x_1839_, v___x_1843_);
lean_dec_ref(v___x_1843_);
v___x_1845_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1845_, 0, v___x_1835_);
lean_ctor_set(v___x_1845_, 1, v___x_1838_);
lean_ctor_set(v___x_1845_, 2, v___x_1844_);
v___x_1846_ = l_Lean_Syntax_node2(v___x_1835_, v___x_1836_, v___x_1837_, v___x_1845_);
v_s_1782_ = v___x_1846_;
goto v___jp_1781_;
}
}
v___jp_1781_:
{
lean_object* v___x_1783_; uint8_t v___x_1784_; 
v___x_1783_ = lean_unsigned_to_nat(0u);
v___x_1784_ = lean_nat_dec_lt(v___x_1783_, v_prec_1780_);
if (v___x_1784_ == 0)
{
return v_s_1782_;
}
else
{
lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; 
v___x_1785_ = lean_obj_once(&l_Lean_Level_PP_Result_quote___closed__0, &l_Lean_Level_PP_Result_quote___closed__0_once, _init_l_Lean_Level_PP_Result_quote___closed__0);
v___x_1786_ = ((lean_object*)(l_Lean_Level_PP_Result_quote___closed__5));
v___x_1787_ = lean_obj_once(&l_Lean_Level_PP_Result_quote___closed__6, &l_Lean_Level_PP_Result_quote___closed__6_once, _init_l_Lean_Level_PP_Result_quote___closed__6);
v___x_1788_ = lean_obj_once(&l_Lean_Level_PP_Result_quote___closed__7, &l_Lean_Level_PP_Result_quote___closed__7_once, _init_l_Lean_Level_PP_Result_quote___closed__7);
v___x_1789_ = l_Lean_Syntax_node3(v___x_1785_, v___x_1786_, v___x_1787_, v_s_1782_, v___x_1788_);
return v___x_1789_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Level_PP_Result_quote_spec__0(size_t v_sz_1847_, size_t v_i_1848_, lean_object* v_bs_1849_){
_start:
{
uint8_t v___x_1850_; 
v___x_1850_ = lean_usize_dec_lt(v_i_1848_, v_sz_1847_);
if (v___x_1850_ == 0)
{
return v_bs_1849_;
}
else
{
lean_object* v_v_1851_; lean_object* v___x_1852_; lean_object* v_bs_x27_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; size_t v___x_1856_; size_t v___x_1857_; lean_object* v___x_1858_; 
v_v_1851_ = lean_array_uget(v_bs_1849_, v_i_1848_);
v___x_1852_ = lean_unsigned_to_nat(0u);
v_bs_x27_1853_ = lean_array_uset(v_bs_1849_, v_i_1848_, v___x_1852_);
v___x_1854_ = lean_unsigned_to_nat(1024u);
v___x_1855_ = l_Lean_Level_PP_Result_quote(v_v_1851_, v___x_1854_);
v___x_1856_ = ((size_t)1ULL);
v___x_1857_ = lean_usize_add(v_i_1848_, v___x_1856_);
v___x_1858_ = lean_array_uset(v_bs_x27_1853_, v_i_1848_, v___x_1855_);
v_i_1848_ = v___x_1857_;
v_bs_1849_ = v___x_1858_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Level_PP_Result_quote_spec__0___boxed(lean_object* v_sz_1860_, lean_object* v_i_1861_, lean_object* v_bs_1862_){
_start:
{
size_t v_sz_boxed_1863_; size_t v_i_boxed_1864_; lean_object* v_res_1865_; 
v_sz_boxed_1863_ = lean_unbox_usize(v_sz_1860_);
lean_dec(v_sz_1860_);
v_i_boxed_1864_ = lean_unbox_usize(v_i_1861_);
lean_dec(v_i_1861_);
v_res_1865_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Level_PP_Result_quote_spec__0(v_sz_boxed_1863_, v_i_boxed_1864_, v_bs_1862_);
return v_res_1865_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_quote___boxed(lean_object* v_r_1866_, lean_object* v_prec_1867_){
_start:
{
lean_object* v_res_1868_; 
v_res_1868_ = l_Lean_Level_PP_Result_quote(v_r_1866_, v_prec_1867_);
lean_dec(v_prec_1867_);
return v_res_1868_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_format(lean_object* v_u_1869_, uint8_t v_mvars_1870_, lean_object* v_lIndex_x3f_1871_){
_start:
{
lean_object* v___x_1872_; lean_object* v___x_1873_; uint8_t v___x_1874_; lean_object* v___x_1875_; 
v___x_1872_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1872_, 0, v_lIndex_x3f_1871_);
lean_ctor_set_uint8(v___x_1872_, sizeof(void*)*1, v_mvars_1870_);
v___x_1873_ = l_Lean_Level_PP_toResult(v_u_1869_, v___x_1872_);
lean_dec_ref_known(v___x_1872_, 1);
v___x_1874_ = 1;
v___x_1875_ = l_Lean_Level_PP_Result_format(v___x_1873_, v___x_1874_);
return v___x_1875_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_format___boxed(lean_object* v_u_1876_, lean_object* v_mvars_1877_, lean_object* v_lIndex_x3f_1878_){
_start:
{
uint8_t v_mvars_boxed_1879_; lean_object* v_res_1880_; 
v_mvars_boxed_1879_ = lean_unbox(v_mvars_1877_);
v_res_1880_ = l_Lean_Level_format(v_u_1876_, v_mvars_boxed_1879_, v_lIndex_x3f_1878_);
return v_res_1880_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_instToFormat___lam__0(lean_object* v_x_1881_){
_start:
{
lean_object* v___x_1882_; 
v___x_1882_ = lean_box(0);
return v___x_1882_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_instToFormat___lam__0___boxed(lean_object* v_x_1883_){
_start:
{
lean_object* v_res_1884_; 
v_res_1884_ = l_Lean_Level_instToFormat___lam__0(v_x_1883_);
lean_dec(v_x_1883_);
return v_res_1884_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_instToFormat___lam__1(lean_object* v___f_1885_, lean_object* v_u_1886_){
_start:
{
uint8_t v___x_1887_; lean_object* v___x_1888_; 
v___x_1887_ = 1;
v___x_1888_ = l_Lean_Level_format(v_u_1886_, v___x_1887_, v___f_1885_);
return v___x_1888_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_instToString___lam__1(lean_object* v___f_1893_, lean_object* v_u_1894_){
_start:
{
uint8_t v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; 
v___x_1895_ = 1;
v___x_1896_ = l_Lean_Level_format(v_u_1894_, v___x_1895_, v___f_1893_);
v___x_1897_ = l_Std_Format_defWidth;
v___x_1898_ = lean_unsigned_to_nat(0u);
v___x_1899_ = l_Std_Format_pretty(v___x_1896_, v___x_1897_, v___x_1898_, v___x_1898_);
return v___x_1899_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_quote(lean_object* v_u_1903_, lean_object* v_prec_1904_, uint8_t v_mvars_1905_, lean_object* v_lIndex_x3f_1906_){
_start:
{
lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; 
v___x_1907_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1907_, 0, v_lIndex_x3f_1906_);
lean_ctor_set_uint8(v___x_1907_, sizeof(void*)*1, v_mvars_1905_);
v___x_1908_ = l_Lean_Level_PP_toResult(v_u_1903_, v___x_1907_);
lean_dec_ref_known(v___x_1907_, 1);
v___x_1909_ = l_Lean_Level_PP_Result_quote(v___x_1908_, v_prec_1904_);
return v___x_1909_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_quote___boxed(lean_object* v_u_1910_, lean_object* v_prec_1911_, lean_object* v_mvars_1912_, lean_object* v_lIndex_x3f_1913_){
_start:
{
uint8_t v_mvars_boxed_1914_; lean_object* v_res_1915_; 
v_mvars_boxed_1914_ = lean_unbox(v_mvars_1912_);
v_res_1915_ = l_Lean_Level_quote(v_u_1910_, v_prec_1911_, v_mvars_boxed_1914_, v_lIndex_x3f_1913_);
lean_dec(v_prec_1911_);
return v_res_1915_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_instQuoteMkStr1___lam__1(lean_object* v___f_1916_, lean_object* v_u_1917_){
_start:
{
lean_object* v___x_1918_; uint8_t v___x_1919_; lean_object* v___x_1920_; 
v___x_1918_ = lean_unsigned_to_nat(0u);
v___x_1919_ = 1;
v___x_1920_ = l_Lean_Level_quote(v_u_1917_, v___x_1918_, v___x_1919_, v___f_1916_);
return v___x_1920_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Level_0__Lean_mkLevelMaxCore___lam__0(lean_object* v_u_1924_, lean_object* v_v_1925_){
_start:
{
uint8_t v___y_1927_; uint8_t v___x_1933_; 
v___x_1933_ = l_Lean_Level_isExplicit(v_v_1925_);
if (v___x_1933_ == 0)
{
v___y_1927_ = v___x_1933_;
goto v___jp_1926_;
}
else
{
lean_object* v___x_1934_; lean_object* v___x_1935_; uint8_t v___x_1936_; 
v___x_1934_ = l_Lean_Level_getOffset(v_v_1925_);
v___x_1935_ = l_Lean_Level_getOffset(v_u_1924_);
v___x_1936_ = lean_nat_dec_le(v___x_1934_, v___x_1935_);
lean_dec(v___x_1935_);
lean_dec(v___x_1934_);
v___y_1927_ = v___x_1936_;
goto v___jp_1926_;
}
v___jp_1926_:
{
uint8_t v___x_1928_; 
v___x_1928_ = 1;
if (v___y_1927_ == 0)
{
if (lean_obj_tag(v_u_1924_) == 2)
{
lean_object* v_a_1929_; lean_object* v_a_1930_; uint8_t v___x_1931_; 
v_a_1929_ = lean_ctor_get(v_u_1924_, 0);
v_a_1930_ = lean_ctor_get(v_u_1924_, 1);
v___x_1931_ = lean_level_eq(v_v_1925_, v_a_1929_);
if (v___x_1931_ == 0)
{
uint8_t v___x_1932_; 
v___x_1932_ = lean_level_eq(v_v_1925_, v_a_1930_);
return v___x_1932_;
}
else
{
return v___x_1928_;
}
}
else
{
return v___y_1927_;
}
}
else
{
return v___x_1928_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_mkLevelMaxCore___lam__0___boxed(lean_object* v_u_1937_, lean_object* v_v_1938_){
_start:
{
uint8_t v_res_1939_; lean_object* v_r_1940_; 
v_res_1939_ = l___private_Lean_Level_0__Lean_mkLevelMaxCore___lam__0(v_u_1937_, v_v_1938_);
lean_dec(v_v_1938_);
lean_dec(v_u_1937_);
v_r_1940_ = lean_box(v_res_1939_);
return v_r_1940_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_mkLevelMaxCore(lean_object* v_u_1941_, lean_object* v_v_1942_, lean_object* v_elseK_1943_){
_start:
{
uint8_t v___x_1944_; 
v___x_1944_ = lean_level_eq(v_u_1941_, v_v_1942_);
if (v___x_1944_ == 0)
{
uint8_t v___x_1945_; 
v___x_1945_ = l_Lean_Level_isZero(v_u_1941_);
if (v___x_1945_ == 0)
{
uint8_t v___x_1946_; 
v___x_1946_ = l_Lean_Level_isZero(v_v_1942_);
if (v___x_1946_ == 0)
{
uint8_t v___x_1947_; 
v___x_1947_ = l___private_Lean_Level_0__Lean_mkLevelMaxCore___lam__0(v_u_1941_, v_v_1942_);
if (v___x_1947_ == 0)
{
uint8_t v___x_1948_; 
v___x_1948_ = l___private_Lean_Level_0__Lean_mkLevelMaxCore___lam__0(v_v_1942_, v_u_1941_);
if (v___x_1948_ == 0)
{
lean_object* v___x_1949_; lean_object* v___x_1950_; uint8_t v___x_1951_; 
v___x_1949_ = l_Lean_Level_getLevelOffset(v_u_1941_);
v___x_1950_ = l_Lean_Level_getLevelOffset(v_v_1942_);
v___x_1951_ = lean_level_eq(v___x_1949_, v___x_1950_);
lean_dec(v___x_1950_);
lean_dec(v___x_1949_);
if (v___x_1951_ == 0)
{
lean_object* v___x_1952_; lean_object* v___x_1953_; 
v___x_1952_ = lean_box(0);
v___x_1953_ = lean_apply_1(v_elseK_1943_, v___x_1952_);
return v___x_1953_;
}
else
{
lean_object* v___x_1954_; lean_object* v___x_1955_; uint8_t v___x_1956_; 
lean_dec_ref(v_elseK_1943_);
v___x_1954_ = l_Lean_Level_getOffset(v_v_1942_);
v___x_1955_ = l_Lean_Level_getOffset(v_u_1941_);
v___x_1956_ = lean_nat_dec_le(v___x_1954_, v___x_1955_);
lean_dec(v___x_1955_);
lean_dec(v___x_1954_);
if (v___x_1956_ == 0)
{
lean_inc(v_v_1942_);
return v_v_1942_;
}
else
{
lean_inc(v_u_1941_);
return v_u_1941_;
}
}
}
else
{
lean_dec_ref(v_elseK_1943_);
lean_inc(v_v_1942_);
return v_v_1942_;
}
}
else
{
lean_dec_ref(v_elseK_1943_);
lean_inc(v_u_1941_);
return v_u_1941_;
}
}
else
{
lean_dec_ref(v_elseK_1943_);
lean_inc(v_u_1941_);
return v_u_1941_;
}
}
else
{
lean_dec_ref(v_elseK_1943_);
lean_inc(v_v_1942_);
return v_v_1942_;
}
}
else
{
lean_dec_ref(v_elseK_1943_);
lean_inc(v_u_1941_);
return v_u_1941_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_mkLevelMaxCore___boxed(lean_object* v_u_1957_, lean_object* v_v_1958_, lean_object* v_elseK_1959_){
_start:
{
lean_object* v_res_1960_; 
v_res_1960_ = l___private_Lean_Level_0__Lean_mkLevelMaxCore(v_u_1957_, v_v_1958_, v_elseK_1959_);
lean_dec(v_v_1958_);
lean_dec(v_u_1957_);
return v_res_1960_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLevelMax_x27(lean_object* v_u_1961_, lean_object* v_v_1962_){
_start:
{
uint8_t v___x_1963_; 
v___x_1963_ = lean_level_eq(v_u_1961_, v_v_1962_);
if (v___x_1963_ == 0)
{
uint8_t v___x_1964_; 
v___x_1964_ = l_Lean_Level_isZero(v_u_1961_);
if (v___x_1964_ == 0)
{
uint8_t v___x_1965_; 
v___x_1965_ = l_Lean_Level_isZero(v_v_1962_);
if (v___x_1965_ == 0)
{
uint8_t v___x_1966_; 
v___x_1966_ = l___private_Lean_Level_0__Lean_mkLevelMaxCore___lam__0(v_u_1961_, v_v_1962_);
if (v___x_1966_ == 0)
{
uint8_t v___x_1967_; 
v___x_1967_ = l___private_Lean_Level_0__Lean_mkLevelMaxCore___lam__0(v_v_1962_, v_u_1961_);
if (v___x_1967_ == 0)
{
lean_object* v___x_1968_; lean_object* v___x_1969_; uint8_t v___x_1970_; 
v___x_1968_ = l_Lean_Level_getLevelOffset(v_u_1961_);
v___x_1969_ = l_Lean_Level_getLevelOffset(v_v_1962_);
v___x_1970_ = lean_level_eq(v___x_1968_, v___x_1969_);
lean_dec(v___x_1969_);
lean_dec(v___x_1968_);
if (v___x_1970_ == 0)
{
lean_object* v___x_1971_; 
v___x_1971_ = l_Lean_Level_max___override(v_u_1961_, v_v_1962_);
return v___x_1971_;
}
else
{
lean_object* v___x_1972_; lean_object* v___x_1973_; uint8_t v___x_1974_; 
v___x_1972_ = l_Lean_Level_getOffset(v_v_1962_);
v___x_1973_ = l_Lean_Level_getOffset(v_u_1961_);
v___x_1974_ = lean_nat_dec_le(v___x_1972_, v___x_1973_);
lean_dec(v___x_1973_);
lean_dec(v___x_1972_);
if (v___x_1974_ == 0)
{
lean_dec(v_u_1961_);
return v_v_1962_;
}
else
{
lean_dec(v_v_1962_);
return v_u_1961_;
}
}
}
else
{
lean_dec(v_u_1961_);
return v_v_1962_;
}
}
else
{
lean_dec(v_v_1962_);
return v_u_1961_;
}
}
else
{
lean_dec(v_v_1962_);
return v_u_1961_;
}
}
else
{
lean_dec(v_u_1961_);
return v_v_1962_;
}
}
else
{
lean_dec(v_v_1962_);
return v_u_1961_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_simpLevelMax_x27(lean_object* v_u_1975_, lean_object* v_v_1976_, lean_object* v_d_1977_){
_start:
{
uint8_t v___x_1978_; 
v___x_1978_ = lean_level_eq(v_u_1975_, v_v_1976_);
if (v___x_1978_ == 0)
{
uint8_t v___x_1979_; 
v___x_1979_ = l_Lean_Level_isZero(v_u_1975_);
if (v___x_1979_ == 0)
{
uint8_t v___x_1980_; 
v___x_1980_ = l_Lean_Level_isZero(v_v_1976_);
if (v___x_1980_ == 0)
{
uint8_t v___x_1981_; 
v___x_1981_ = l___private_Lean_Level_0__Lean_mkLevelMaxCore___lam__0(v_u_1975_, v_v_1976_);
if (v___x_1981_ == 0)
{
uint8_t v___x_1982_; 
v___x_1982_ = l___private_Lean_Level_0__Lean_mkLevelMaxCore___lam__0(v_v_1976_, v_u_1975_);
if (v___x_1982_ == 0)
{
lean_object* v___x_1983_; lean_object* v___x_1984_; uint8_t v___x_1985_; 
v___x_1983_ = l_Lean_Level_getLevelOffset(v_u_1975_);
v___x_1984_ = l_Lean_Level_getLevelOffset(v_v_1976_);
v___x_1985_ = lean_level_eq(v___x_1983_, v___x_1984_);
lean_dec(v___x_1984_);
lean_dec(v___x_1983_);
if (v___x_1985_ == 0)
{
lean_inc(v_d_1977_);
return v_d_1977_;
}
else
{
lean_object* v___x_1986_; lean_object* v___x_1987_; uint8_t v___x_1988_; 
v___x_1986_ = l_Lean_Level_getOffset(v_v_1976_);
v___x_1987_ = l_Lean_Level_getOffset(v_u_1975_);
v___x_1988_ = lean_nat_dec_le(v___x_1986_, v___x_1987_);
lean_dec(v___x_1987_);
lean_dec(v___x_1986_);
if (v___x_1988_ == 0)
{
lean_inc(v_v_1976_);
return v_v_1976_;
}
else
{
lean_inc(v_u_1975_);
return v_u_1975_;
}
}
}
else
{
lean_inc(v_v_1976_);
return v_v_1976_;
}
}
else
{
lean_inc(v_u_1975_);
return v_u_1975_;
}
}
else
{
lean_inc(v_u_1975_);
return v_u_1975_;
}
}
else
{
lean_inc(v_v_1976_);
return v_v_1976_;
}
}
else
{
lean_inc(v_u_1975_);
return v_u_1975_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_simpLevelMax_x27___boxed(lean_object* v_u_1989_, lean_object* v_v_1990_, lean_object* v_d_1991_){
_start:
{
lean_object* v_res_1992_; 
v_res_1992_ = l_Lean_simpLevelMax_x27(v_u_1989_, v_v_1990_, v_d_1991_);
lean_dec(v_d_1991_);
lean_dec(v_v_1990_);
lean_dec(v_u_1989_);
return v_res_1992_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_mkLevelIMaxCore(lean_object* v_u_1993_, lean_object* v_v_1994_, lean_object* v_elseK_1995_){
_start:
{
uint8_t v___x_1996_; 
v___x_1996_ = l_Lean_Level_isNeverZero(v_v_1994_);
if (v___x_1996_ == 0)
{
uint8_t v___x_1997_; 
v___x_1997_ = l_Lean_Level_isZero(v_v_1994_);
if (v___x_1997_ == 0)
{
uint8_t v___x_1998_; 
v___x_1998_ = l_Lean_Level_isZero(v_u_1993_);
if (v___x_1998_ == 0)
{
uint8_t v___x_1999_; 
v___x_1999_ = lean_level_eq(v_u_1993_, v_v_1994_);
lean_dec(v_v_1994_);
if (v___x_1999_ == 0)
{
lean_object* v___x_2000_; lean_object* v___x_2001_; 
lean_dec(v_u_1993_);
v___x_2000_ = lean_box(0);
v___x_2001_ = lean_apply_1(v_elseK_1995_, v___x_2000_);
return v___x_2001_;
}
else
{
lean_dec_ref(v_elseK_1995_);
return v_u_1993_;
}
}
else
{
lean_dec_ref(v_elseK_1995_);
lean_dec(v_u_1993_);
return v_v_1994_;
}
}
else
{
lean_dec_ref(v_elseK_1995_);
lean_dec(v_u_1993_);
return v_v_1994_;
}
}
else
{
lean_object* v___x_2002_; 
lean_dec_ref(v_elseK_1995_);
v___x_2002_ = l_Lean_mkLevelMax_x27(v_u_1993_, v_v_1994_);
return v___x_2002_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkLevelIMax_x27(lean_object* v_u_2003_, lean_object* v_v_2004_){
_start:
{
uint8_t v___x_2005_; 
v___x_2005_ = l_Lean_Level_isNeverZero(v_v_2004_);
if (v___x_2005_ == 0)
{
uint8_t v___x_2006_; 
v___x_2006_ = l_Lean_Level_isZero(v_v_2004_);
if (v___x_2006_ == 0)
{
uint8_t v___x_2007_; 
v___x_2007_ = l_Lean_Level_isZero(v_u_2003_);
if (v___x_2007_ == 0)
{
uint8_t v___x_2008_; 
v___x_2008_ = lean_level_eq(v_u_2003_, v_v_2004_);
if (v___x_2008_ == 0)
{
lean_object* v___x_2009_; 
v___x_2009_ = l_Lean_Level_imax___override(v_u_2003_, v_v_2004_);
return v___x_2009_;
}
else
{
lean_dec(v_v_2004_);
return v_u_2003_;
}
}
else
{
lean_dec(v_u_2003_);
return v_v_2004_;
}
}
else
{
lean_dec(v_u_2003_);
return v_v_2004_;
}
}
else
{
lean_object* v___x_2010_; 
v___x_2010_ = l_Lean_mkLevelMax_x27(v_u_2003_, v_v_2004_);
return v___x_2010_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_simpLevelIMax_x27(lean_object* v_u_2011_, lean_object* v_v_2012_, lean_object* v_d_2013_){
_start:
{
uint8_t v___x_2014_; 
v___x_2014_ = l_Lean_Level_isNeverZero(v_v_2012_);
if (v___x_2014_ == 0)
{
uint8_t v___x_2015_; 
v___x_2015_ = l_Lean_Level_isZero(v_v_2012_);
if (v___x_2015_ == 0)
{
uint8_t v___x_2016_; 
v___x_2016_ = l_Lean_Level_isZero(v_u_2011_);
if (v___x_2016_ == 0)
{
uint8_t v___x_2017_; 
v___x_2017_ = lean_level_eq(v_u_2011_, v_v_2012_);
lean_dec(v_v_2012_);
if (v___x_2017_ == 0)
{
lean_dec(v_u_2011_);
lean_inc(v_d_2013_);
return v_d_2013_;
}
else
{
return v_u_2011_;
}
}
else
{
lean_dec(v_u_2011_);
return v_v_2012_;
}
}
else
{
lean_dec(v_u_2011_);
return v_v_2012_;
}
}
else
{
lean_object* v___x_2018_; 
v___x_2018_ = l_Lean_mkLevelMax_x27(v_u_2011_, v_v_2012_);
return v___x_2018_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_simpLevelIMax_x27___boxed(lean_object* v_u_2019_, lean_object* v_v_2020_, lean_object* v_d_2021_){
_start:
{
lean_object* v_res_2022_; 
v_res_2022_ = l_Lean_simpLevelIMax_x27(v_u_2019_, v_v_2020_, v_d_2021_);
lean_dec(v_d_2021_);
return v_res_2022_;
}
}
static lean_object* _init_l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl___closed__2(void){
_start:
{
lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; 
v___x_2025_ = ((lean_object*)(l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl___closed__1));
v___x_2026_ = lean_unsigned_to_nat(14u);
v___x_2027_ = lean_unsigned_to_nat(567u);
v___x_2028_ = ((lean_object*)(l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl___closed__0));
v___x_2029_ = ((lean_object*)(l_Lean_Level_mvarId_x21___closed__0));
v___x_2030_ = l_mkPanicMessageWithDecl(v___x_2029_, v___x_2028_, v___x_2027_, v___x_2026_, v___x_2025_);
return v___x_2030_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl(lean_object* v_lvl_2031_, lean_object* v_newLvl_2032_){
_start:
{
if (lean_obj_tag(v_lvl_2031_) == 1)
{
lean_object* v_a_2033_; size_t v___x_2034_; size_t v___x_2035_; uint8_t v___x_2036_; 
v_a_2033_ = lean_ctor_get(v_lvl_2031_, 0);
v___x_2034_ = lean_ptr_addr(v_a_2033_);
v___x_2035_ = lean_ptr_addr(v_newLvl_2032_);
v___x_2036_ = lean_usize_dec_eq(v___x_2034_, v___x_2035_);
if (v___x_2036_ == 0)
{
lean_object* v___x_2037_; 
v___x_2037_ = l_Lean_Level_succ___override(v_newLvl_2032_);
return v___x_2037_;
}
else
{
lean_dec(v_newLvl_2032_);
lean_inc_ref(v_lvl_2031_);
return v_lvl_2031_;
}
}
else
{
lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; 
lean_dec(v_newLvl_2032_);
v___x_2038_ = lean_box(0);
v___x_2039_ = lean_obj_once(&l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl___closed__2, &l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl___closed__2_once, _init_l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl___closed__2);
v___x_2040_ = l_panic___redArg(v___x_2038_, v___x_2039_);
return v___x_2040_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl___boxed(lean_object* v_lvl_2041_, lean_object* v_newLvl_2042_){
_start:
{
lean_object* v_res_2043_; 
v_res_2043_ = l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl(v_lvl_2041_, v_newLvl_2042_);
lean_dec(v_lvl_2041_);
return v_res_2043_;
}
}
static lean_object* _init_l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl___closed__2(void){
_start:
{
lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; 
v___x_2046_ = ((lean_object*)(l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl___closed__1));
v___x_2047_ = lean_unsigned_to_nat(19u);
v___x_2048_ = lean_unsigned_to_nat(578u);
v___x_2049_ = ((lean_object*)(l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl___closed__0));
v___x_2050_ = ((lean_object*)(l_Lean_Level_mvarId_x21___closed__0));
v___x_2051_ = l_mkPanicMessageWithDecl(v___x_2050_, v___x_2049_, v___x_2048_, v___x_2047_, v___x_2046_);
return v___x_2051_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl(lean_object* v_lvl_2052_, lean_object* v_newLhs_2053_, lean_object* v_newRhs_2054_){
_start:
{
uint8_t v___y_2056_; 
if (lean_obj_tag(v_lvl_2052_) == 2)
{
lean_object* v_a_2059_; lean_object* v_a_2060_; size_t v___x_2061_; size_t v___x_2062_; uint8_t v___x_2063_; 
v_a_2059_ = lean_ctor_get(v_lvl_2052_, 0);
v_a_2060_ = lean_ctor_get(v_lvl_2052_, 1);
v___x_2061_ = lean_ptr_addr(v_a_2059_);
v___x_2062_ = lean_ptr_addr(v_newLhs_2053_);
v___x_2063_ = lean_usize_dec_eq(v___x_2061_, v___x_2062_);
if (v___x_2063_ == 0)
{
v___y_2056_ = v___x_2063_;
goto v___jp_2055_;
}
else
{
size_t v___x_2064_; size_t v___x_2065_; uint8_t v___x_2066_; 
v___x_2064_ = lean_ptr_addr(v_a_2060_);
v___x_2065_ = lean_ptr_addr(v_newRhs_2054_);
v___x_2066_ = lean_usize_dec_eq(v___x_2064_, v___x_2065_);
v___y_2056_ = v___x_2066_;
goto v___jp_2055_;
}
}
else
{
lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; 
lean_dec(v_newRhs_2054_);
lean_dec(v_newLhs_2053_);
v___x_2067_ = lean_box(0);
v___x_2068_ = lean_obj_once(&l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl___closed__2, &l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl___closed__2_once, _init_l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl___closed__2);
v___x_2069_ = l_panic___redArg(v___x_2067_, v___x_2068_);
return v___x_2069_;
}
v___jp_2055_:
{
if (v___y_2056_ == 0)
{
lean_object* v___x_2057_; 
v___x_2057_ = l_Lean_mkLevelMax_x27(v_newLhs_2053_, v_newRhs_2054_);
return v___x_2057_;
}
else
{
lean_object* v___x_2058_; 
v___x_2058_ = l_Lean_simpLevelMax_x27(v_newLhs_2053_, v_newRhs_2054_, v_lvl_2052_);
lean_dec(v_newRhs_2054_);
lean_dec(v_newLhs_2053_);
return v___x_2058_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl___boxed(lean_object* v_lvl_2070_, lean_object* v_newLhs_2071_, lean_object* v_newRhs_2072_){
_start:
{
lean_object* v_res_2073_; 
v_res_2073_ = l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl(v_lvl_2070_, v_newLhs_2071_, v_newRhs_2072_);
lean_dec(v_lvl_2070_);
return v_res_2073_;
}
}
static lean_object* _init_l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl___closed__2(void){
_start:
{
lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; 
v___x_2076_ = ((lean_object*)(l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl___closed__1));
v___x_2077_ = lean_unsigned_to_nat(20u);
v___x_2078_ = lean_unsigned_to_nat(589u);
v___x_2079_ = ((lean_object*)(l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl___closed__0));
v___x_2080_ = ((lean_object*)(l_Lean_Level_mvarId_x21___closed__0));
v___x_2081_ = l_mkPanicMessageWithDecl(v___x_2080_, v___x_2079_, v___x_2078_, v___x_2077_, v___x_2076_);
return v___x_2081_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl(lean_object* v_lvl_2082_, lean_object* v_newLhs_2083_, lean_object* v_newRhs_2084_){
_start:
{
uint8_t v___y_2086_; 
if (lean_obj_tag(v_lvl_2082_) == 3)
{
lean_object* v_a_2089_; lean_object* v_a_2090_; size_t v___x_2091_; size_t v___x_2092_; uint8_t v___x_2093_; 
v_a_2089_ = lean_ctor_get(v_lvl_2082_, 0);
v_a_2090_ = lean_ctor_get(v_lvl_2082_, 1);
v___x_2091_ = lean_ptr_addr(v_a_2089_);
v___x_2092_ = lean_ptr_addr(v_newLhs_2083_);
v___x_2093_ = lean_usize_dec_eq(v___x_2091_, v___x_2092_);
if (v___x_2093_ == 0)
{
v___y_2086_ = v___x_2093_;
goto v___jp_2085_;
}
else
{
size_t v___x_2094_; size_t v___x_2095_; uint8_t v___x_2096_; 
v___x_2094_ = lean_ptr_addr(v_a_2090_);
v___x_2095_ = lean_ptr_addr(v_newRhs_2084_);
v___x_2096_ = lean_usize_dec_eq(v___x_2094_, v___x_2095_);
v___y_2086_ = v___x_2096_;
goto v___jp_2085_;
}
}
else
{
lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; 
lean_dec(v_newRhs_2084_);
lean_dec(v_newLhs_2083_);
v___x_2097_ = lean_box(0);
v___x_2098_ = lean_obj_once(&l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl___closed__2, &l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl___closed__2_once, _init_l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl___closed__2);
v___x_2099_ = l_panic___redArg(v___x_2097_, v___x_2098_);
return v___x_2099_;
}
v___jp_2085_:
{
if (v___y_2086_ == 0)
{
lean_object* v___x_2087_; 
v___x_2087_ = l_Lean_mkLevelIMax_x27(v_newLhs_2083_, v_newRhs_2084_);
return v___x_2087_;
}
else
{
lean_object* v___x_2088_; 
v___x_2088_ = l_Lean_simpLevelIMax_x27(v_newLhs_2083_, v_newRhs_2084_, v_lvl_2082_);
return v___x_2088_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl___boxed(lean_object* v_lvl_2100_, lean_object* v_newLhs_2101_, lean_object* v_newRhs_2102_){
_start:
{
lean_object* v_res_2103_; 
v_res_2103_ = l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl(v_lvl_2100_, v_newLhs_2101_, v_newRhs_2102_);
lean_dec(v_lvl_2100_);
return v_res_2103_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_mkNaryMax(lean_object* v_x_2104_){
_start:
{
if (lean_obj_tag(v_x_2104_) == 0)
{
lean_object* v___x_2105_; 
v___x_2105_ = lean_box(0);
return v___x_2105_;
}
else
{
lean_object* v_tail_2106_; 
v_tail_2106_ = lean_ctor_get(v_x_2104_, 1);
if (lean_obj_tag(v_tail_2106_) == 0)
{
lean_object* v_head_2107_; 
v_head_2107_ = lean_ctor_get(v_x_2104_, 0);
lean_inc(v_head_2107_);
lean_dec_ref_known(v_x_2104_, 2);
return v_head_2107_;
}
else
{
lean_object* v_head_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; 
lean_inc(v_tail_2106_);
v_head_2108_ = lean_ctor_get(v_x_2104_, 0);
lean_inc(v_head_2108_);
lean_dec_ref_known(v_x_2104_, 2);
v___x_2109_ = l_Lean_Level_mkNaryMax(v_tail_2106_);
v___x_2110_ = l_Lean_mkLevelMax_x27(v_head_2108_, v___x_2109_);
return v___x_2110_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_substParams_go(lean_object* v_s_2111_, lean_object* v_u_2112_){
_start:
{
switch(lean_obj_tag(v_u_2112_))
{
case 0:
{
lean_dec_ref(v_s_2111_);
return v_u_2112_;
}
case 1:
{
lean_object* v_a_2113_; uint8_t v___x_2114_; 
v_a_2113_ = lean_ctor_get(v_u_2112_, 0);
v___x_2114_ = l_Lean_Level_hasParam(v_u_2112_);
if (v___x_2114_ == 0)
{
lean_dec_ref(v_s_2111_);
return v_u_2112_;
}
else
{
lean_object* v___x_2115_; size_t v___x_2116_; size_t v___x_2117_; uint8_t v___x_2118_; 
lean_inc(v_a_2113_);
v___x_2115_ = l___private_Lean_Level_0__Lean_Level_substParams_go(v_s_2111_, v_a_2113_);
v___x_2116_ = lean_ptr_addr(v_a_2113_);
v___x_2117_ = lean_ptr_addr(v___x_2115_);
v___x_2118_ = lean_usize_dec_eq(v___x_2116_, v___x_2117_);
if (v___x_2118_ == 0)
{
lean_object* v___x_2119_; 
lean_dec_ref_known(v_u_2112_, 1);
v___x_2119_ = l_Lean_Level_succ___override(v___x_2115_);
return v___x_2119_;
}
else
{
lean_dec(v___x_2115_);
return v_u_2112_;
}
}
}
case 2:
{
lean_object* v_a_2120_; lean_object* v_a_2121_; uint8_t v___x_2122_; 
v_a_2120_ = lean_ctor_get(v_u_2112_, 0);
v_a_2121_ = lean_ctor_get(v_u_2112_, 1);
v___x_2122_ = l_Lean_Level_hasParam(v_u_2112_);
if (v___x_2122_ == 0)
{
lean_dec_ref(v_s_2111_);
return v_u_2112_;
}
else
{
lean_object* v___x_2123_; lean_object* v___x_2124_; uint8_t v___y_2126_; size_t v___x_2129_; size_t v___x_2130_; uint8_t v___x_2131_; 
lean_inc(v_a_2120_);
lean_inc_ref(v_s_2111_);
v___x_2123_ = l___private_Lean_Level_0__Lean_Level_substParams_go(v_s_2111_, v_a_2120_);
lean_inc(v_a_2121_);
v___x_2124_ = l___private_Lean_Level_0__Lean_Level_substParams_go(v_s_2111_, v_a_2121_);
v___x_2129_ = lean_ptr_addr(v_a_2120_);
v___x_2130_ = lean_ptr_addr(v___x_2123_);
v___x_2131_ = lean_usize_dec_eq(v___x_2129_, v___x_2130_);
if (v___x_2131_ == 0)
{
v___y_2126_ = v___x_2131_;
goto v___jp_2125_;
}
else
{
size_t v___x_2132_; size_t v___x_2133_; uint8_t v___x_2134_; 
v___x_2132_ = lean_ptr_addr(v_a_2121_);
v___x_2133_ = lean_ptr_addr(v___x_2124_);
v___x_2134_ = lean_usize_dec_eq(v___x_2132_, v___x_2133_);
v___y_2126_ = v___x_2134_;
goto v___jp_2125_;
}
v___jp_2125_:
{
if (v___y_2126_ == 0)
{
lean_object* v___x_2127_; 
lean_dec_ref_known(v_u_2112_, 2);
v___x_2127_ = l_Lean_mkLevelMax_x27(v___x_2123_, v___x_2124_);
return v___x_2127_;
}
else
{
lean_object* v___x_2128_; 
v___x_2128_ = l_Lean_simpLevelMax_x27(v___x_2123_, v___x_2124_, v_u_2112_);
lean_dec_ref_known(v_u_2112_, 2);
lean_dec(v___x_2124_);
lean_dec(v___x_2123_);
return v___x_2128_;
}
}
}
}
case 3:
{
lean_object* v_a_2135_; lean_object* v_a_2136_; uint8_t v___x_2137_; 
v_a_2135_ = lean_ctor_get(v_u_2112_, 0);
v_a_2136_ = lean_ctor_get(v_u_2112_, 1);
v___x_2137_ = l_Lean_Level_hasParam(v_u_2112_);
if (v___x_2137_ == 0)
{
lean_dec_ref(v_s_2111_);
return v_u_2112_;
}
else
{
lean_object* v___x_2138_; lean_object* v___x_2139_; uint8_t v___y_2141_; size_t v___x_2144_; size_t v___x_2145_; uint8_t v___x_2146_; 
lean_inc(v_a_2135_);
lean_inc_ref(v_s_2111_);
v___x_2138_ = l___private_Lean_Level_0__Lean_Level_substParams_go(v_s_2111_, v_a_2135_);
lean_inc(v_a_2136_);
v___x_2139_ = l___private_Lean_Level_0__Lean_Level_substParams_go(v_s_2111_, v_a_2136_);
v___x_2144_ = lean_ptr_addr(v_a_2135_);
v___x_2145_ = lean_ptr_addr(v___x_2138_);
v___x_2146_ = lean_usize_dec_eq(v___x_2144_, v___x_2145_);
if (v___x_2146_ == 0)
{
v___y_2141_ = v___x_2146_;
goto v___jp_2140_;
}
else
{
size_t v___x_2147_; size_t v___x_2148_; uint8_t v___x_2149_; 
v___x_2147_ = lean_ptr_addr(v_a_2136_);
v___x_2148_ = lean_ptr_addr(v___x_2139_);
v___x_2149_ = lean_usize_dec_eq(v___x_2147_, v___x_2148_);
v___y_2141_ = v___x_2149_;
goto v___jp_2140_;
}
v___jp_2140_:
{
if (v___y_2141_ == 0)
{
lean_object* v___x_2142_; 
lean_dec_ref_known(v_u_2112_, 2);
v___x_2142_ = l_Lean_mkLevelIMax_x27(v___x_2138_, v___x_2139_);
return v___x_2142_;
}
else
{
lean_object* v___x_2143_; 
v___x_2143_ = l_Lean_simpLevelIMax_x27(v___x_2138_, v___x_2139_, v_u_2112_);
lean_dec_ref_known(v_u_2112_, 2);
return v___x_2143_;
}
}
}
}
case 4:
{
lean_object* v_a_2150_; lean_object* v___x_2151_; 
v_a_2150_ = lean_ctor_get(v_u_2112_, 0);
lean_inc(v_a_2150_);
v___x_2151_ = lean_apply_1(v_s_2111_, v_a_2150_);
if (lean_obj_tag(v___x_2151_) == 0)
{
return v_u_2112_;
}
else
{
lean_object* v_val_2152_; 
lean_dec_ref_known(v_u_2112_, 1);
v_val_2152_ = lean_ctor_get(v___x_2151_, 0);
lean_inc(v_val_2152_);
lean_dec_ref_known(v___x_2151_, 1);
return v_val_2152_;
}
}
default: 
{
lean_dec_ref(v_s_2111_);
return v_u_2112_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_substParams(lean_object* v_u_2153_, lean_object* v_s_2154_){
_start:
{
lean_object* v___x_2155_; 
v___x_2155_ = l___private_Lean_Level_0__Lean_Level_substParams_go(v_s_2154_, v_u_2153_);
return v___x_2155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_getParamSubst(lean_object* v_x_2156_, lean_object* v_x_2157_, lean_object* v_x_2158_){
_start:
{
if (lean_obj_tag(v_x_2156_) == 1)
{
if (lean_obj_tag(v_x_2157_) == 1)
{
lean_object* v_head_2159_; lean_object* v_tail_2160_; lean_object* v_head_2161_; lean_object* v_tail_2162_; uint8_t v___x_2163_; 
v_head_2159_ = lean_ctor_get(v_x_2156_, 0);
v_tail_2160_ = lean_ctor_get(v_x_2156_, 1);
v_head_2161_ = lean_ctor_get(v_x_2157_, 0);
v_tail_2162_ = lean_ctor_get(v_x_2157_, 1);
v___x_2163_ = lean_name_eq(v_head_2159_, v_x_2158_);
if (v___x_2163_ == 0)
{
v_x_2156_ = v_tail_2160_;
v_x_2157_ = v_tail_2162_;
goto _start;
}
else
{
lean_object* v___x_2165_; 
lean_inc(v_head_2161_);
v___x_2165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2165_, 0, v_head_2161_);
return v___x_2165_;
}
}
else
{
lean_object* v___x_2166_; 
v___x_2166_ = lean_box(0);
return v___x_2166_;
}
}
else
{
lean_object* v___x_2167_; 
v___x_2167_ = lean_box(0);
return v___x_2167_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_getParamSubst___boxed(lean_object* v_x_2168_, lean_object* v_x_2169_, lean_object* v_x_2170_){
_start:
{
lean_object* v_res_2171_; 
v_res_2171_ = l_Lean_Level_getParamSubst(v_x_2168_, v_x_2169_, v_x_2170_);
lean_dec(v_x_2170_);
lean_dec(v_x_2169_);
lean_dec(v_x_2168_);
return v_res_2171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_instantiateParams(lean_object* v_u_2172_, lean_object* v_paramNames_2173_, lean_object* v_vs_2174_){
_start:
{
lean_object* v___x_2175_; lean_object* v___x_2176_; 
v___x_2175_ = lean_alloc_closure((void*)(l_Lean_Level_getParamSubst___boxed), 3, 2);
lean_closure_set(v___x_2175_, 0, v_paramNames_2173_);
lean_closure_set(v___x_2175_, 1, v_vs_2174_);
v___x_2176_ = l___private_Lean_Level_0__Lean_Level_substParams_go(v___x_2175_, v_u_2172_);
return v___x_2176_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Level_0__Lean_Level_geq_go(lean_object* v_u_2177_, lean_object* v_v_2178_){
_start:
{
uint8_t v___y_2180_; uint8_t v___y_2194_; lean_object* v_u_u2081_2196_; lean_object* v_u_u2082_2197_; lean_object* v_v_2198_; uint8_t v___x_2201_; 
v___x_2201_ = lean_level_eq(v_u_2177_, v_v_2178_);
if (v___x_2201_ == 0)
{
switch(lean_obj_tag(v_v_2178_))
{
case 0:
{
uint8_t v___x_2202_; 
v___x_2202_ = 1;
return v___x_2202_;
}
case 2:
{
lean_object* v_a_2203_; lean_object* v_a_2204_; uint8_t v___x_2205_; 
v_a_2203_ = lean_ctor_get(v_v_2178_, 0);
v_a_2204_ = lean_ctor_get(v_v_2178_, 1);
v___x_2205_ = l___private_Lean_Level_0__Lean_Level_geq_go(v_u_2177_, v_a_2203_);
if (v___x_2205_ == 0)
{
return v___x_2205_;
}
else
{
v_v_2178_ = v_a_2204_;
goto _start;
}
}
case 1:
{
switch(lean_obj_tag(v_u_2177_))
{
case 2:
{
lean_object* v_a_2207_; lean_object* v_a_2208_; 
v_a_2207_ = lean_ctor_get(v_u_2177_, 0);
v_a_2208_ = lean_ctor_get(v_u_2177_, 1);
v_u_u2081_2196_ = v_a_2207_;
v_u_u2082_2197_ = v_a_2208_;
v_v_2198_ = v_v_2178_;
goto v___jp_2195_;
}
case 3:
{
lean_object* v_a_2209_; 
v_a_2209_ = lean_ctor_get(v_u_2177_, 1);
v_u_2177_ = v_a_2209_;
goto _start;
}
case 1:
{
lean_object* v_a_2211_; lean_object* v_a_2212_; 
v_a_2211_ = lean_ctor_get(v_v_2178_, 0);
v_a_2212_ = lean_ctor_get(v_u_2177_, 0);
v_u_2177_ = v_a_2212_;
v_v_2178_ = v_a_2211_;
goto _start;
}
default: 
{
goto v___jp_2184_;
}
}
}
default: 
{
switch(lean_obj_tag(v_u_2177_))
{
case 2:
{
lean_object* v_a_2214_; lean_object* v_a_2215_; 
v_a_2214_ = lean_ctor_get(v_u_2177_, 0);
v_a_2215_ = lean_ctor_get(v_u_2177_, 1);
v_u_u2081_2196_ = v_a_2214_;
v_u_u2082_2197_ = v_a_2215_;
v_v_2198_ = v_v_2178_;
goto v___jp_2195_;
}
case 3:
{
lean_object* v_a_2216_; 
v_a_2216_ = lean_ctor_get(v_u_2177_, 1);
v_u_2177_ = v_a_2216_;
goto _start;
}
default: 
{
goto v___jp_2184_;
}
}
}
}
}
else
{
return v___x_2201_;
}
v___jp_2179_:
{
if (v___y_2180_ == 0)
{
return v___y_2180_;
}
else
{
lean_object* v___x_2181_; lean_object* v___x_2182_; uint8_t v___x_2183_; 
v___x_2181_ = l_Lean_Level_getOffset(v_v_2178_);
v___x_2182_ = l_Lean_Level_getOffset(v_u_2177_);
v___x_2183_ = lean_nat_dec_le(v___x_2181_, v___x_2182_);
lean_dec(v___x_2182_);
lean_dec(v___x_2181_);
return v___x_2183_;
}
}
v___jp_2184_:
{
if (lean_obj_tag(v_v_2178_) == 3)
{
lean_object* v_a_2185_; lean_object* v_a_2186_; uint8_t v___x_2187_; 
v_a_2185_ = lean_ctor_get(v_v_2178_, 0);
v_a_2186_ = lean_ctor_get(v_v_2178_, 1);
v___x_2187_ = l___private_Lean_Level_0__Lean_Level_geq_go(v_u_2177_, v_a_2185_);
if (v___x_2187_ == 0)
{
return v___x_2187_;
}
else
{
v_v_2178_ = v_a_2186_;
goto _start;
}
}
else
{
lean_object* v_v_x27_2189_; lean_object* v___x_2190_; uint8_t v___x_2191_; 
v_v_x27_2189_ = l_Lean_Level_getLevelOffset(v_v_2178_);
v___x_2190_ = l_Lean_Level_getLevelOffset(v_u_2177_);
v___x_2191_ = lean_level_eq(v___x_2190_, v_v_x27_2189_);
lean_dec(v___x_2190_);
if (v___x_2191_ == 0)
{
uint8_t v___x_2192_; 
v___x_2192_ = l_Lean_Level_isZero(v_v_x27_2189_);
lean_dec(v_v_x27_2189_);
v___y_2180_ = v___x_2192_;
goto v___jp_2179_;
}
else
{
lean_dec(v_v_x27_2189_);
v___y_2180_ = v___x_2191_;
goto v___jp_2179_;
}
}
}
v___jp_2193_:
{
if (v___y_2194_ == 0)
{
goto v___jp_2184_;
}
else
{
return v___y_2194_;
}
}
v___jp_2195_:
{
uint8_t v___x_2199_; 
v___x_2199_ = l___private_Lean_Level_0__Lean_Level_geq_go(v_u_u2081_2196_, v_v_2198_);
if (v___x_2199_ == 0)
{
uint8_t v___x_2200_; 
v___x_2200_ = l___private_Lean_Level_0__Lean_Level_geq_go(v_u_u2082_2197_, v_v_2198_);
v___y_2194_ = v___x_2200_;
goto v___jp_2193_;
}
else
{
v___y_2194_ = v___x_2199_;
goto v___jp_2193_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_geq_go___boxed(lean_object* v_u_2218_, lean_object* v_v_2219_){
_start:
{
uint8_t v_res_2220_; lean_object* v_r_2221_; 
v_res_2220_ = l___private_Lean_Level_0__Lean_Level_geq_go(v_u_2218_, v_v_2219_);
lean_dec(v_v_2219_);
lean_dec(v_u_2218_);
v_r_2221_ = lean_box(v_res_2220_);
return v_r_2221_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_geq_go_match__1_splitter___redArg(lean_object* v_u_2222_, lean_object* v_v_2223_, lean_object* v_h__1_2224_, lean_object* v_h__2_2225_, lean_object* v_h__3_2226_, lean_object* v_h__4_2227_, lean_object* v_h__5_2228_, lean_object* v_h__6_2229_){
_start:
{
switch(lean_obj_tag(v_v_2223_))
{
case 0:
{
lean_object* v___x_2230_; 
lean_dec(v_h__6_2229_);
lean_dec(v_h__5_2228_);
lean_dec(v_h__4_2227_);
lean_dec(v_h__3_2226_);
lean_dec(v_h__2_2225_);
v___x_2230_ = lean_apply_1(v_h__1_2224_, v_u_2222_);
return v___x_2230_;
}
case 2:
{
lean_object* v_a_2231_; lean_object* v_a_2232_; lean_object* v___x_2233_; 
lean_dec(v_h__6_2229_);
lean_dec(v_h__5_2228_);
lean_dec(v_h__4_2227_);
lean_dec(v_h__3_2226_);
lean_dec(v_h__1_2224_);
v_a_2231_ = lean_ctor_get(v_v_2223_, 0);
lean_inc(v_a_2231_);
v_a_2232_ = lean_ctor_get(v_v_2223_, 1);
lean_inc(v_a_2232_);
lean_dec_ref_known(v_v_2223_, 2);
v___x_2233_ = lean_apply_3(v_h__2_2225_, v_u_2222_, v_a_2231_, v_a_2232_);
return v___x_2233_;
}
case 1:
{
lean_dec(v_h__2_2225_);
lean_dec(v_h__1_2224_);
switch(lean_obj_tag(v_u_2222_))
{
case 2:
{
lean_object* v_a_2234_; lean_object* v_a_2235_; lean_object* v___x_2236_; 
lean_dec(v_h__6_2229_);
lean_dec(v_h__5_2228_);
lean_dec(v_h__4_2227_);
v_a_2234_ = lean_ctor_get(v_u_2222_, 0);
lean_inc(v_a_2234_);
v_a_2235_ = lean_ctor_get(v_u_2222_, 1);
lean_inc(v_a_2235_);
lean_dec_ref_known(v_u_2222_, 2);
v___x_2236_ = lean_apply_5(v_h__3_2226_, v_a_2234_, v_a_2235_, v_v_2223_, lean_box(0), lean_box(0));
return v___x_2236_;
}
case 3:
{
lean_object* v_a_2237_; lean_object* v_a_2238_; lean_object* v___x_2239_; 
lean_dec(v_h__6_2229_);
lean_dec(v_h__5_2228_);
lean_dec(v_h__3_2226_);
v_a_2237_ = lean_ctor_get(v_u_2222_, 0);
lean_inc(v_a_2237_);
v_a_2238_ = lean_ctor_get(v_u_2222_, 1);
lean_inc(v_a_2238_);
lean_dec_ref_known(v_u_2222_, 2);
v___x_2239_ = lean_apply_5(v_h__4_2227_, v_a_2237_, v_a_2238_, v_v_2223_, lean_box(0), lean_box(0));
return v___x_2239_;
}
case 1:
{
lean_object* v_a_2240_; lean_object* v_a_2241_; lean_object* v___x_2242_; 
lean_dec(v_h__6_2229_);
lean_dec(v_h__4_2227_);
lean_dec(v_h__3_2226_);
v_a_2240_ = lean_ctor_get(v_v_2223_, 0);
lean_inc(v_a_2240_);
lean_dec_ref_known(v_v_2223_, 1);
v_a_2241_ = lean_ctor_get(v_u_2222_, 0);
lean_inc(v_a_2241_);
lean_dec_ref_known(v_u_2222_, 1);
v___x_2242_ = lean_apply_2(v_h__5_2228_, v_a_2241_, v_a_2240_);
return v___x_2242_;
}
default: 
{
lean_object* v___x_2243_; 
lean_dec(v_h__5_2228_);
lean_dec(v_h__4_2227_);
lean_dec(v_h__3_2226_);
v___x_2243_ = lean_apply_7(v_h__6_2229_, v_u_2222_, v_v_2223_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_2243_;
}
}
}
default: 
{
lean_dec(v_h__5_2228_);
lean_dec(v_h__2_2225_);
lean_dec(v_h__1_2224_);
switch(lean_obj_tag(v_u_2222_))
{
case 2:
{
lean_object* v_a_2244_; lean_object* v_a_2245_; lean_object* v___x_2246_; 
lean_dec(v_h__6_2229_);
lean_dec(v_h__4_2227_);
v_a_2244_ = lean_ctor_get(v_u_2222_, 0);
lean_inc(v_a_2244_);
v_a_2245_ = lean_ctor_get(v_u_2222_, 1);
lean_inc(v_a_2245_);
lean_dec_ref_known(v_u_2222_, 2);
v___x_2246_ = lean_apply_5(v_h__3_2226_, v_a_2244_, v_a_2245_, v_v_2223_, lean_box(0), lean_box(0));
return v___x_2246_;
}
case 3:
{
lean_object* v_a_2247_; lean_object* v_a_2248_; lean_object* v___x_2249_; 
lean_dec(v_h__6_2229_);
lean_dec(v_h__3_2226_);
v_a_2247_ = lean_ctor_get(v_u_2222_, 0);
lean_inc(v_a_2247_);
v_a_2248_ = lean_ctor_get(v_u_2222_, 1);
lean_inc(v_a_2248_);
lean_dec_ref_known(v_u_2222_, 2);
v___x_2249_ = lean_apply_5(v_h__4_2227_, v_a_2247_, v_a_2248_, v_v_2223_, lean_box(0), lean_box(0));
return v___x_2249_;
}
default: 
{
lean_object* v___x_2250_; 
lean_dec(v_h__4_2227_);
lean_dec(v_h__3_2226_);
v___x_2250_ = lean_apply_7(v_h__6_2229_, v_u_2222_, v_v_2223_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_2250_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_geq_go_match__1_splitter(lean_object* v_motive_2251_, lean_object* v_u_2252_, lean_object* v_v_2253_, lean_object* v_h__1_2254_, lean_object* v_h__2_2255_, lean_object* v_h__3_2256_, lean_object* v_h__4_2257_, lean_object* v_h__5_2258_, lean_object* v_h__6_2259_){
_start:
{
switch(lean_obj_tag(v_v_2253_))
{
case 0:
{
lean_object* v___x_2260_; 
lean_dec(v_h__6_2259_);
lean_dec(v_h__5_2258_);
lean_dec(v_h__4_2257_);
lean_dec(v_h__3_2256_);
lean_dec(v_h__2_2255_);
v___x_2260_ = lean_apply_1(v_h__1_2254_, v_u_2252_);
return v___x_2260_;
}
case 2:
{
lean_object* v_a_2261_; lean_object* v_a_2262_; lean_object* v___x_2263_; 
lean_dec(v_h__6_2259_);
lean_dec(v_h__5_2258_);
lean_dec(v_h__4_2257_);
lean_dec(v_h__3_2256_);
lean_dec(v_h__1_2254_);
v_a_2261_ = lean_ctor_get(v_v_2253_, 0);
lean_inc(v_a_2261_);
v_a_2262_ = lean_ctor_get(v_v_2253_, 1);
lean_inc(v_a_2262_);
lean_dec_ref_known(v_v_2253_, 2);
v___x_2263_ = lean_apply_3(v_h__2_2255_, v_u_2252_, v_a_2261_, v_a_2262_);
return v___x_2263_;
}
case 1:
{
lean_dec(v_h__2_2255_);
lean_dec(v_h__1_2254_);
switch(lean_obj_tag(v_u_2252_))
{
case 2:
{
lean_object* v_a_2264_; lean_object* v_a_2265_; lean_object* v___x_2266_; 
lean_dec(v_h__6_2259_);
lean_dec(v_h__5_2258_);
lean_dec(v_h__4_2257_);
v_a_2264_ = lean_ctor_get(v_u_2252_, 0);
lean_inc(v_a_2264_);
v_a_2265_ = lean_ctor_get(v_u_2252_, 1);
lean_inc(v_a_2265_);
lean_dec_ref_known(v_u_2252_, 2);
v___x_2266_ = lean_apply_5(v_h__3_2256_, v_a_2264_, v_a_2265_, v_v_2253_, lean_box(0), lean_box(0));
return v___x_2266_;
}
case 3:
{
lean_object* v_a_2267_; lean_object* v_a_2268_; lean_object* v___x_2269_; 
lean_dec(v_h__6_2259_);
lean_dec(v_h__5_2258_);
lean_dec(v_h__3_2256_);
v_a_2267_ = lean_ctor_get(v_u_2252_, 0);
lean_inc(v_a_2267_);
v_a_2268_ = lean_ctor_get(v_u_2252_, 1);
lean_inc(v_a_2268_);
lean_dec_ref_known(v_u_2252_, 2);
v___x_2269_ = lean_apply_5(v_h__4_2257_, v_a_2267_, v_a_2268_, v_v_2253_, lean_box(0), lean_box(0));
return v___x_2269_;
}
case 1:
{
lean_object* v_a_2270_; lean_object* v_a_2271_; lean_object* v___x_2272_; 
lean_dec(v_h__6_2259_);
lean_dec(v_h__4_2257_);
lean_dec(v_h__3_2256_);
v_a_2270_ = lean_ctor_get(v_v_2253_, 0);
lean_inc(v_a_2270_);
lean_dec_ref_known(v_v_2253_, 1);
v_a_2271_ = lean_ctor_get(v_u_2252_, 0);
lean_inc(v_a_2271_);
lean_dec_ref_known(v_u_2252_, 1);
v___x_2272_ = lean_apply_2(v_h__5_2258_, v_a_2271_, v_a_2270_);
return v___x_2272_;
}
default: 
{
lean_object* v___x_2273_; 
lean_dec(v_h__5_2258_);
lean_dec(v_h__4_2257_);
lean_dec(v_h__3_2256_);
v___x_2273_ = lean_apply_7(v_h__6_2259_, v_u_2252_, v_v_2253_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_2273_;
}
}
}
default: 
{
lean_dec(v_h__5_2258_);
lean_dec(v_h__2_2255_);
lean_dec(v_h__1_2254_);
switch(lean_obj_tag(v_u_2252_))
{
case 2:
{
lean_object* v_a_2274_; lean_object* v_a_2275_; lean_object* v___x_2276_; 
lean_dec(v_h__6_2259_);
lean_dec(v_h__4_2257_);
v_a_2274_ = lean_ctor_get(v_u_2252_, 0);
lean_inc(v_a_2274_);
v_a_2275_ = lean_ctor_get(v_u_2252_, 1);
lean_inc(v_a_2275_);
lean_dec_ref_known(v_u_2252_, 2);
v___x_2276_ = lean_apply_5(v_h__3_2256_, v_a_2274_, v_a_2275_, v_v_2253_, lean_box(0), lean_box(0));
return v___x_2276_;
}
case 3:
{
lean_object* v_a_2277_; lean_object* v_a_2278_; lean_object* v___x_2279_; 
lean_dec(v_h__6_2259_);
lean_dec(v_h__3_2256_);
v_a_2277_ = lean_ctor_get(v_u_2252_, 0);
lean_inc(v_a_2277_);
v_a_2278_ = lean_ctor_get(v_u_2252_, 1);
lean_inc(v_a_2278_);
lean_dec_ref_known(v_u_2252_, 2);
v___x_2279_ = lean_apply_5(v_h__4_2257_, v_a_2277_, v_a_2278_, v_v_2253_, lean_box(0), lean_box(0));
return v___x_2279_;
}
default: 
{
lean_object* v___x_2280_; 
lean_dec(v_h__4_2257_);
lean_dec(v_h__3_2256_);
v___x_2280_ = lean_apply_7(v_h__6_2259_, v_u_2252_, v_v_2253_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_2280_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_isIMax_match__1_splitter___redArg(lean_object* v_x_2281_, lean_object* v_h__1_2282_, lean_object* v_h__2_2283_){
_start:
{
if (lean_obj_tag(v_x_2281_) == 3)
{
lean_object* v_a_2284_; lean_object* v_a_2285_; lean_object* v___x_2286_; 
lean_dec(v_h__2_2283_);
v_a_2284_ = lean_ctor_get(v_x_2281_, 0);
lean_inc(v_a_2284_);
v_a_2285_ = lean_ctor_get(v_x_2281_, 1);
lean_inc(v_a_2285_);
lean_dec_ref_known(v_x_2281_, 2);
v___x_2286_ = lean_apply_2(v_h__1_2282_, v_a_2284_, v_a_2285_);
return v___x_2286_;
}
else
{
lean_object* v___x_2287_; 
lean_dec(v_h__1_2282_);
v___x_2287_ = lean_apply_2(v_h__2_2283_, v_x_2281_, lean_box(0));
return v___x_2287_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_isIMax_match__1_splitter(lean_object* v_motive_2288_, lean_object* v_x_2289_, lean_object* v_h__1_2290_, lean_object* v_h__2_2291_){
_start:
{
if (lean_obj_tag(v_x_2289_) == 3)
{
lean_object* v_a_2292_; lean_object* v_a_2293_; lean_object* v___x_2294_; 
lean_dec(v_h__2_2291_);
v_a_2292_ = lean_ctor_get(v_x_2289_, 0);
lean_inc(v_a_2292_);
v_a_2293_ = lean_ctor_get(v_x_2289_, 1);
lean_inc(v_a_2293_);
lean_dec_ref_known(v_x_2289_, 2);
v___x_2294_ = lean_apply_2(v_h__1_2290_, v_a_2292_, v_a_2293_);
return v___x_2294_;
}
else
{
lean_object* v___x_2295_; 
lean_dec(v_h__1_2290_);
v___x_2295_ = lean_apply_2(v_h__2_2291_, v_x_2289_, lean_box(0));
return v___x_2295_;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Level_geq(lean_object* v_u_2296_, lean_object* v_v_2297_){
_start:
{
lean_object* v___x_2298_; lean_object* v___x_2299_; uint8_t v___x_2300_; 
v___x_2298_ = l_Lean_Level_normalize(v_u_2296_);
v___x_2299_ = l_Lean_Level_normalize(v_v_2297_);
v___x_2300_ = l___private_Lean_Level_0__Lean_Level_geq_go(v___x_2298_, v___x_2299_);
lean_dec(v___x_2299_);
lean_dec(v___x_2298_);
return v___x_2300_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_geq___boxed(lean_object* v_u_2301_, lean_object* v_v_2302_){
_start:
{
uint8_t v_res_2303_; lean_object* v_r_2304_; 
v_res_2303_ = l_Lean_Level_geq(v_u_2301_, v_v_2302_);
lean_dec(v_v_2302_);
lean_dec(v_u_2301_);
v_r_2304_ = lean_box(v_res_2303_);
return v_r_2304_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Level_collectMVars_spec__1___redArg(lean_object* v_k_2305_, lean_object* v_v_2306_, lean_object* v_t_2307_){
_start:
{
if (lean_obj_tag(v_t_2307_) == 0)
{
lean_object* v_size_2308_; lean_object* v_k_2309_; lean_object* v_v_2310_; lean_object* v_l_2311_; lean_object* v_r_2312_; lean_object* v___x_2314_; uint8_t v_isShared_2315_; uint8_t v_isSharedCheck_2592_; 
v_size_2308_ = lean_ctor_get(v_t_2307_, 0);
v_k_2309_ = lean_ctor_get(v_t_2307_, 1);
v_v_2310_ = lean_ctor_get(v_t_2307_, 2);
v_l_2311_ = lean_ctor_get(v_t_2307_, 3);
v_r_2312_ = lean_ctor_get(v_t_2307_, 4);
v_isSharedCheck_2592_ = !lean_is_exclusive(v_t_2307_);
if (v_isSharedCheck_2592_ == 0)
{
v___x_2314_ = v_t_2307_;
v_isShared_2315_ = v_isSharedCheck_2592_;
goto v_resetjp_2313_;
}
else
{
lean_inc(v_r_2312_);
lean_inc(v_l_2311_);
lean_inc(v_v_2310_);
lean_inc(v_k_2309_);
lean_inc(v_size_2308_);
lean_dec(v_t_2307_);
v___x_2314_ = lean_box(0);
v_isShared_2315_ = v_isSharedCheck_2592_;
goto v_resetjp_2313_;
}
v_resetjp_2313_:
{
uint8_t v___x_2316_; 
v___x_2316_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2305_, v_k_2309_);
switch(v___x_2316_)
{
case 0:
{
lean_object* v_impl_2317_; lean_object* v___x_2318_; 
lean_dec(v_size_2308_);
v_impl_2317_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Level_collectMVars_spec__1___redArg(v_k_2305_, v_v_2306_, v_l_2311_);
v___x_2318_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_2312_) == 0)
{
lean_object* v_size_2319_; lean_object* v_size_2320_; lean_object* v_k_2321_; lean_object* v_v_2322_; lean_object* v_l_2323_; lean_object* v_r_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; uint8_t v___x_2327_; 
v_size_2319_ = lean_ctor_get(v_r_2312_, 0);
v_size_2320_ = lean_ctor_get(v_impl_2317_, 0);
lean_inc(v_size_2320_);
v_k_2321_ = lean_ctor_get(v_impl_2317_, 1);
lean_inc(v_k_2321_);
v_v_2322_ = lean_ctor_get(v_impl_2317_, 2);
lean_inc(v_v_2322_);
v_l_2323_ = lean_ctor_get(v_impl_2317_, 3);
lean_inc(v_l_2323_);
v_r_2324_ = lean_ctor_get(v_impl_2317_, 4);
lean_inc(v_r_2324_);
v___x_2325_ = lean_unsigned_to_nat(3u);
v___x_2326_ = lean_nat_mul(v___x_2325_, v_size_2319_);
v___x_2327_ = lean_nat_dec_lt(v___x_2326_, v_size_2320_);
lean_dec(v___x_2326_);
if (v___x_2327_ == 0)
{
lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2331_; 
lean_dec(v_r_2324_);
lean_dec(v_l_2323_);
lean_dec(v_v_2322_);
lean_dec(v_k_2321_);
v___x_2328_ = lean_nat_add(v___x_2318_, v_size_2320_);
lean_dec(v_size_2320_);
v___x_2329_ = lean_nat_add(v___x_2328_, v_size_2319_);
lean_dec(v___x_2328_);
if (v_isShared_2315_ == 0)
{
lean_ctor_set(v___x_2314_, 3, v_impl_2317_);
lean_ctor_set(v___x_2314_, 0, v___x_2329_);
v___x_2331_ = v___x_2314_;
goto v_reusejp_2330_;
}
else
{
lean_object* v_reuseFailAlloc_2332_; 
v_reuseFailAlloc_2332_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2332_, 0, v___x_2329_);
lean_ctor_set(v_reuseFailAlloc_2332_, 1, v_k_2309_);
lean_ctor_set(v_reuseFailAlloc_2332_, 2, v_v_2310_);
lean_ctor_set(v_reuseFailAlloc_2332_, 3, v_impl_2317_);
lean_ctor_set(v_reuseFailAlloc_2332_, 4, v_r_2312_);
v___x_2331_ = v_reuseFailAlloc_2332_;
goto v_reusejp_2330_;
}
v_reusejp_2330_:
{
return v___x_2331_;
}
}
else
{
lean_object* v___x_2334_; uint8_t v_isShared_2335_; uint8_t v_isSharedCheck_2398_; 
v_isSharedCheck_2398_ = !lean_is_exclusive(v_impl_2317_);
if (v_isSharedCheck_2398_ == 0)
{
lean_object* v_unused_2399_; lean_object* v_unused_2400_; lean_object* v_unused_2401_; lean_object* v_unused_2402_; lean_object* v_unused_2403_; 
v_unused_2399_ = lean_ctor_get(v_impl_2317_, 4);
lean_dec(v_unused_2399_);
v_unused_2400_ = lean_ctor_get(v_impl_2317_, 3);
lean_dec(v_unused_2400_);
v_unused_2401_ = lean_ctor_get(v_impl_2317_, 2);
lean_dec(v_unused_2401_);
v_unused_2402_ = lean_ctor_get(v_impl_2317_, 1);
lean_dec(v_unused_2402_);
v_unused_2403_ = lean_ctor_get(v_impl_2317_, 0);
lean_dec(v_unused_2403_);
v___x_2334_ = v_impl_2317_;
v_isShared_2335_ = v_isSharedCheck_2398_;
goto v_resetjp_2333_;
}
else
{
lean_dec(v_impl_2317_);
v___x_2334_ = lean_box(0);
v_isShared_2335_ = v_isSharedCheck_2398_;
goto v_resetjp_2333_;
}
v_resetjp_2333_:
{
lean_object* v_size_2336_; lean_object* v_size_2337_; lean_object* v_k_2338_; lean_object* v_v_2339_; lean_object* v_l_2340_; lean_object* v_r_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; uint8_t v___x_2344_; 
v_size_2336_ = lean_ctor_get(v_l_2323_, 0);
v_size_2337_ = lean_ctor_get(v_r_2324_, 0);
v_k_2338_ = lean_ctor_get(v_r_2324_, 1);
v_v_2339_ = lean_ctor_get(v_r_2324_, 2);
v_l_2340_ = lean_ctor_get(v_r_2324_, 3);
v_r_2341_ = lean_ctor_get(v_r_2324_, 4);
v___x_2342_ = lean_unsigned_to_nat(2u);
v___x_2343_ = lean_nat_mul(v___x_2342_, v_size_2336_);
v___x_2344_ = lean_nat_dec_lt(v_size_2337_, v___x_2343_);
lean_dec(v___x_2343_);
if (v___x_2344_ == 0)
{
lean_object* v___x_2346_; uint8_t v_isShared_2347_; uint8_t v_isSharedCheck_2373_; 
lean_inc(v_r_2341_);
lean_inc(v_l_2340_);
lean_inc(v_v_2339_);
lean_inc(v_k_2338_);
v_isSharedCheck_2373_ = !lean_is_exclusive(v_r_2324_);
if (v_isSharedCheck_2373_ == 0)
{
lean_object* v_unused_2374_; lean_object* v_unused_2375_; lean_object* v_unused_2376_; lean_object* v_unused_2377_; lean_object* v_unused_2378_; 
v_unused_2374_ = lean_ctor_get(v_r_2324_, 4);
lean_dec(v_unused_2374_);
v_unused_2375_ = lean_ctor_get(v_r_2324_, 3);
lean_dec(v_unused_2375_);
v_unused_2376_ = lean_ctor_get(v_r_2324_, 2);
lean_dec(v_unused_2376_);
v_unused_2377_ = lean_ctor_get(v_r_2324_, 1);
lean_dec(v_unused_2377_);
v_unused_2378_ = lean_ctor_get(v_r_2324_, 0);
lean_dec(v_unused_2378_);
v___x_2346_ = v_r_2324_;
v_isShared_2347_ = v_isSharedCheck_2373_;
goto v_resetjp_2345_;
}
else
{
lean_dec(v_r_2324_);
v___x_2346_ = lean_box(0);
v_isShared_2347_ = v_isSharedCheck_2373_;
goto v_resetjp_2345_;
}
v_resetjp_2345_:
{
lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___y_2351_; lean_object* v___y_2352_; lean_object* v___y_2353_; lean_object* v___x_2361_; lean_object* v___y_2363_; 
v___x_2348_ = lean_nat_add(v___x_2318_, v_size_2320_);
lean_dec(v_size_2320_);
v___x_2349_ = lean_nat_add(v___x_2348_, v_size_2319_);
lean_dec(v___x_2348_);
v___x_2361_ = lean_nat_add(v___x_2318_, v_size_2336_);
if (lean_obj_tag(v_l_2340_) == 0)
{
lean_object* v_size_2371_; 
v_size_2371_ = lean_ctor_get(v_l_2340_, 0);
lean_inc(v_size_2371_);
v___y_2363_ = v_size_2371_;
goto v___jp_2362_;
}
else
{
lean_object* v___x_2372_; 
v___x_2372_ = lean_unsigned_to_nat(0u);
v___y_2363_ = v___x_2372_;
goto v___jp_2362_;
}
v___jp_2350_:
{
lean_object* v___x_2354_; lean_object* v___x_2356_; 
v___x_2354_ = lean_nat_add(v___y_2352_, v___y_2353_);
lean_dec(v___y_2353_);
lean_dec(v___y_2352_);
if (v_isShared_2347_ == 0)
{
lean_ctor_set(v___x_2346_, 4, v_r_2312_);
lean_ctor_set(v___x_2346_, 3, v_r_2341_);
lean_ctor_set(v___x_2346_, 2, v_v_2310_);
lean_ctor_set(v___x_2346_, 1, v_k_2309_);
lean_ctor_set(v___x_2346_, 0, v___x_2354_);
v___x_2356_ = v___x_2346_;
goto v_reusejp_2355_;
}
else
{
lean_object* v_reuseFailAlloc_2360_; 
v_reuseFailAlloc_2360_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2360_, 0, v___x_2354_);
lean_ctor_set(v_reuseFailAlloc_2360_, 1, v_k_2309_);
lean_ctor_set(v_reuseFailAlloc_2360_, 2, v_v_2310_);
lean_ctor_set(v_reuseFailAlloc_2360_, 3, v_r_2341_);
lean_ctor_set(v_reuseFailAlloc_2360_, 4, v_r_2312_);
v___x_2356_ = v_reuseFailAlloc_2360_;
goto v_reusejp_2355_;
}
v_reusejp_2355_:
{
lean_object* v___x_2358_; 
if (v_isShared_2335_ == 0)
{
lean_ctor_set(v___x_2334_, 4, v___x_2356_);
lean_ctor_set(v___x_2334_, 3, v___y_2351_);
lean_ctor_set(v___x_2334_, 2, v_v_2339_);
lean_ctor_set(v___x_2334_, 1, v_k_2338_);
lean_ctor_set(v___x_2334_, 0, v___x_2349_);
v___x_2358_ = v___x_2334_;
goto v_reusejp_2357_;
}
else
{
lean_object* v_reuseFailAlloc_2359_; 
v_reuseFailAlloc_2359_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2359_, 0, v___x_2349_);
lean_ctor_set(v_reuseFailAlloc_2359_, 1, v_k_2338_);
lean_ctor_set(v_reuseFailAlloc_2359_, 2, v_v_2339_);
lean_ctor_set(v_reuseFailAlloc_2359_, 3, v___y_2351_);
lean_ctor_set(v_reuseFailAlloc_2359_, 4, v___x_2356_);
v___x_2358_ = v_reuseFailAlloc_2359_;
goto v_reusejp_2357_;
}
v_reusejp_2357_:
{
return v___x_2358_;
}
}
}
v___jp_2362_:
{
lean_object* v___x_2364_; lean_object* v___x_2366_; 
v___x_2364_ = lean_nat_add(v___x_2361_, v___y_2363_);
lean_dec(v___y_2363_);
lean_dec(v___x_2361_);
if (v_isShared_2315_ == 0)
{
lean_ctor_set(v___x_2314_, 4, v_l_2340_);
lean_ctor_set(v___x_2314_, 3, v_l_2323_);
lean_ctor_set(v___x_2314_, 2, v_v_2322_);
lean_ctor_set(v___x_2314_, 1, v_k_2321_);
lean_ctor_set(v___x_2314_, 0, v___x_2364_);
v___x_2366_ = v___x_2314_;
goto v_reusejp_2365_;
}
else
{
lean_object* v_reuseFailAlloc_2370_; 
v_reuseFailAlloc_2370_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2370_, 0, v___x_2364_);
lean_ctor_set(v_reuseFailAlloc_2370_, 1, v_k_2321_);
lean_ctor_set(v_reuseFailAlloc_2370_, 2, v_v_2322_);
lean_ctor_set(v_reuseFailAlloc_2370_, 3, v_l_2323_);
lean_ctor_set(v_reuseFailAlloc_2370_, 4, v_l_2340_);
v___x_2366_ = v_reuseFailAlloc_2370_;
goto v_reusejp_2365_;
}
v_reusejp_2365_:
{
lean_object* v___x_2367_; 
v___x_2367_ = lean_nat_add(v___x_2318_, v_size_2319_);
if (lean_obj_tag(v_r_2341_) == 0)
{
lean_object* v_size_2368_; 
v_size_2368_ = lean_ctor_get(v_r_2341_, 0);
lean_inc(v_size_2368_);
v___y_2351_ = v___x_2366_;
v___y_2352_ = v___x_2367_;
v___y_2353_ = v_size_2368_;
goto v___jp_2350_;
}
else
{
lean_object* v___x_2369_; 
v___x_2369_ = lean_unsigned_to_nat(0u);
v___y_2351_ = v___x_2366_;
v___y_2352_ = v___x_2367_;
v___y_2353_ = v___x_2369_;
goto v___jp_2350_;
}
}
}
}
}
else
{
lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2384_; 
lean_del_object(v___x_2314_);
v___x_2379_ = lean_nat_add(v___x_2318_, v_size_2320_);
lean_dec(v_size_2320_);
v___x_2380_ = lean_nat_add(v___x_2379_, v_size_2319_);
lean_dec(v___x_2379_);
v___x_2381_ = lean_nat_add(v___x_2318_, v_size_2319_);
v___x_2382_ = lean_nat_add(v___x_2381_, v_size_2337_);
lean_dec(v___x_2381_);
lean_inc_ref(v_r_2312_);
if (v_isShared_2335_ == 0)
{
lean_ctor_set(v___x_2334_, 4, v_r_2312_);
lean_ctor_set(v___x_2334_, 3, v_r_2324_);
lean_ctor_set(v___x_2334_, 2, v_v_2310_);
lean_ctor_set(v___x_2334_, 1, v_k_2309_);
lean_ctor_set(v___x_2334_, 0, v___x_2382_);
v___x_2384_ = v___x_2334_;
goto v_reusejp_2383_;
}
else
{
lean_object* v_reuseFailAlloc_2397_; 
v_reuseFailAlloc_2397_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2397_, 0, v___x_2382_);
lean_ctor_set(v_reuseFailAlloc_2397_, 1, v_k_2309_);
lean_ctor_set(v_reuseFailAlloc_2397_, 2, v_v_2310_);
lean_ctor_set(v_reuseFailAlloc_2397_, 3, v_r_2324_);
lean_ctor_set(v_reuseFailAlloc_2397_, 4, v_r_2312_);
v___x_2384_ = v_reuseFailAlloc_2397_;
goto v_reusejp_2383_;
}
v_reusejp_2383_:
{
lean_object* v___x_2386_; uint8_t v_isShared_2387_; uint8_t v_isSharedCheck_2391_; 
v_isSharedCheck_2391_ = !lean_is_exclusive(v_r_2312_);
if (v_isSharedCheck_2391_ == 0)
{
lean_object* v_unused_2392_; lean_object* v_unused_2393_; lean_object* v_unused_2394_; lean_object* v_unused_2395_; lean_object* v_unused_2396_; 
v_unused_2392_ = lean_ctor_get(v_r_2312_, 4);
lean_dec(v_unused_2392_);
v_unused_2393_ = lean_ctor_get(v_r_2312_, 3);
lean_dec(v_unused_2393_);
v_unused_2394_ = lean_ctor_get(v_r_2312_, 2);
lean_dec(v_unused_2394_);
v_unused_2395_ = lean_ctor_get(v_r_2312_, 1);
lean_dec(v_unused_2395_);
v_unused_2396_ = lean_ctor_get(v_r_2312_, 0);
lean_dec(v_unused_2396_);
v___x_2386_ = v_r_2312_;
v_isShared_2387_ = v_isSharedCheck_2391_;
goto v_resetjp_2385_;
}
else
{
lean_dec(v_r_2312_);
v___x_2386_ = lean_box(0);
v_isShared_2387_ = v_isSharedCheck_2391_;
goto v_resetjp_2385_;
}
v_resetjp_2385_:
{
lean_object* v___x_2389_; 
if (v_isShared_2387_ == 0)
{
lean_ctor_set(v___x_2386_, 4, v___x_2384_);
lean_ctor_set(v___x_2386_, 3, v_l_2323_);
lean_ctor_set(v___x_2386_, 2, v_v_2322_);
lean_ctor_set(v___x_2386_, 1, v_k_2321_);
lean_ctor_set(v___x_2386_, 0, v___x_2380_);
v___x_2389_ = v___x_2386_;
goto v_reusejp_2388_;
}
else
{
lean_object* v_reuseFailAlloc_2390_; 
v_reuseFailAlloc_2390_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2390_, 0, v___x_2380_);
lean_ctor_set(v_reuseFailAlloc_2390_, 1, v_k_2321_);
lean_ctor_set(v_reuseFailAlloc_2390_, 2, v_v_2322_);
lean_ctor_set(v_reuseFailAlloc_2390_, 3, v_l_2323_);
lean_ctor_set(v_reuseFailAlloc_2390_, 4, v___x_2384_);
v___x_2389_ = v_reuseFailAlloc_2390_;
goto v_reusejp_2388_;
}
v_reusejp_2388_:
{
return v___x_2389_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_2404_; 
v_l_2404_ = lean_ctor_get(v_impl_2317_, 3);
lean_inc(v_l_2404_);
if (lean_obj_tag(v_l_2404_) == 0)
{
lean_object* v_r_2405_; lean_object* v_k_2406_; lean_object* v_v_2407_; lean_object* v___x_2409_; uint8_t v_isShared_2410_; uint8_t v_isSharedCheck_2418_; 
v_r_2405_ = lean_ctor_get(v_impl_2317_, 4);
v_k_2406_ = lean_ctor_get(v_impl_2317_, 1);
v_v_2407_ = lean_ctor_get(v_impl_2317_, 2);
v_isSharedCheck_2418_ = !lean_is_exclusive(v_impl_2317_);
if (v_isSharedCheck_2418_ == 0)
{
lean_object* v_unused_2419_; lean_object* v_unused_2420_; 
v_unused_2419_ = lean_ctor_get(v_impl_2317_, 3);
lean_dec(v_unused_2419_);
v_unused_2420_ = lean_ctor_get(v_impl_2317_, 0);
lean_dec(v_unused_2420_);
v___x_2409_ = v_impl_2317_;
v_isShared_2410_ = v_isSharedCheck_2418_;
goto v_resetjp_2408_;
}
else
{
lean_inc(v_r_2405_);
lean_inc(v_v_2407_);
lean_inc(v_k_2406_);
lean_dec(v_impl_2317_);
v___x_2409_ = lean_box(0);
v_isShared_2410_ = v_isSharedCheck_2418_;
goto v_resetjp_2408_;
}
v_resetjp_2408_:
{
lean_object* v___x_2411_; lean_object* v___x_2413_; 
v___x_2411_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_2405_);
if (v_isShared_2410_ == 0)
{
lean_ctor_set(v___x_2409_, 3, v_r_2405_);
lean_ctor_set(v___x_2409_, 2, v_v_2310_);
lean_ctor_set(v___x_2409_, 1, v_k_2309_);
lean_ctor_set(v___x_2409_, 0, v___x_2318_);
v___x_2413_ = v___x_2409_;
goto v_reusejp_2412_;
}
else
{
lean_object* v_reuseFailAlloc_2417_; 
v_reuseFailAlloc_2417_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2417_, 0, v___x_2318_);
lean_ctor_set(v_reuseFailAlloc_2417_, 1, v_k_2309_);
lean_ctor_set(v_reuseFailAlloc_2417_, 2, v_v_2310_);
lean_ctor_set(v_reuseFailAlloc_2417_, 3, v_r_2405_);
lean_ctor_set(v_reuseFailAlloc_2417_, 4, v_r_2405_);
v___x_2413_ = v_reuseFailAlloc_2417_;
goto v_reusejp_2412_;
}
v_reusejp_2412_:
{
lean_object* v___x_2415_; 
if (v_isShared_2315_ == 0)
{
lean_ctor_set(v___x_2314_, 4, v___x_2413_);
lean_ctor_set(v___x_2314_, 3, v_l_2404_);
lean_ctor_set(v___x_2314_, 2, v_v_2407_);
lean_ctor_set(v___x_2314_, 1, v_k_2406_);
lean_ctor_set(v___x_2314_, 0, v___x_2411_);
v___x_2415_ = v___x_2314_;
goto v_reusejp_2414_;
}
else
{
lean_object* v_reuseFailAlloc_2416_; 
v_reuseFailAlloc_2416_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2416_, 0, v___x_2411_);
lean_ctor_set(v_reuseFailAlloc_2416_, 1, v_k_2406_);
lean_ctor_set(v_reuseFailAlloc_2416_, 2, v_v_2407_);
lean_ctor_set(v_reuseFailAlloc_2416_, 3, v_l_2404_);
lean_ctor_set(v_reuseFailAlloc_2416_, 4, v___x_2413_);
v___x_2415_ = v_reuseFailAlloc_2416_;
goto v_reusejp_2414_;
}
v_reusejp_2414_:
{
return v___x_2415_;
}
}
}
}
else
{
lean_object* v_r_2421_; 
v_r_2421_ = lean_ctor_get(v_impl_2317_, 4);
lean_inc(v_r_2421_);
if (lean_obj_tag(v_r_2421_) == 0)
{
lean_object* v_k_2422_; lean_object* v_v_2423_; lean_object* v___x_2425_; uint8_t v_isShared_2426_; uint8_t v_isSharedCheck_2446_; 
v_k_2422_ = lean_ctor_get(v_impl_2317_, 1);
v_v_2423_ = lean_ctor_get(v_impl_2317_, 2);
v_isSharedCheck_2446_ = !lean_is_exclusive(v_impl_2317_);
if (v_isSharedCheck_2446_ == 0)
{
lean_object* v_unused_2447_; lean_object* v_unused_2448_; lean_object* v_unused_2449_; 
v_unused_2447_ = lean_ctor_get(v_impl_2317_, 4);
lean_dec(v_unused_2447_);
v_unused_2448_ = lean_ctor_get(v_impl_2317_, 3);
lean_dec(v_unused_2448_);
v_unused_2449_ = lean_ctor_get(v_impl_2317_, 0);
lean_dec(v_unused_2449_);
v___x_2425_ = v_impl_2317_;
v_isShared_2426_ = v_isSharedCheck_2446_;
goto v_resetjp_2424_;
}
else
{
lean_inc(v_v_2423_);
lean_inc(v_k_2422_);
lean_dec(v_impl_2317_);
v___x_2425_ = lean_box(0);
v_isShared_2426_ = v_isSharedCheck_2446_;
goto v_resetjp_2424_;
}
v_resetjp_2424_:
{
lean_object* v_k_2427_; lean_object* v_v_2428_; lean_object* v___x_2430_; uint8_t v_isShared_2431_; uint8_t v_isSharedCheck_2442_; 
v_k_2427_ = lean_ctor_get(v_r_2421_, 1);
v_v_2428_ = lean_ctor_get(v_r_2421_, 2);
v_isSharedCheck_2442_ = !lean_is_exclusive(v_r_2421_);
if (v_isSharedCheck_2442_ == 0)
{
lean_object* v_unused_2443_; lean_object* v_unused_2444_; lean_object* v_unused_2445_; 
v_unused_2443_ = lean_ctor_get(v_r_2421_, 4);
lean_dec(v_unused_2443_);
v_unused_2444_ = lean_ctor_get(v_r_2421_, 3);
lean_dec(v_unused_2444_);
v_unused_2445_ = lean_ctor_get(v_r_2421_, 0);
lean_dec(v_unused_2445_);
v___x_2430_ = v_r_2421_;
v_isShared_2431_ = v_isSharedCheck_2442_;
goto v_resetjp_2429_;
}
else
{
lean_inc(v_v_2428_);
lean_inc(v_k_2427_);
lean_dec(v_r_2421_);
v___x_2430_ = lean_box(0);
v_isShared_2431_ = v_isSharedCheck_2442_;
goto v_resetjp_2429_;
}
v_resetjp_2429_:
{
lean_object* v___x_2432_; lean_object* v___x_2434_; 
v___x_2432_ = lean_unsigned_to_nat(3u);
if (v_isShared_2431_ == 0)
{
lean_ctor_set(v___x_2430_, 4, v_l_2404_);
lean_ctor_set(v___x_2430_, 3, v_l_2404_);
lean_ctor_set(v___x_2430_, 2, v_v_2423_);
lean_ctor_set(v___x_2430_, 1, v_k_2422_);
lean_ctor_set(v___x_2430_, 0, v___x_2318_);
v___x_2434_ = v___x_2430_;
goto v_reusejp_2433_;
}
else
{
lean_object* v_reuseFailAlloc_2441_; 
v_reuseFailAlloc_2441_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2441_, 0, v___x_2318_);
lean_ctor_set(v_reuseFailAlloc_2441_, 1, v_k_2422_);
lean_ctor_set(v_reuseFailAlloc_2441_, 2, v_v_2423_);
lean_ctor_set(v_reuseFailAlloc_2441_, 3, v_l_2404_);
lean_ctor_set(v_reuseFailAlloc_2441_, 4, v_l_2404_);
v___x_2434_ = v_reuseFailAlloc_2441_;
goto v_reusejp_2433_;
}
v_reusejp_2433_:
{
lean_object* v___x_2436_; 
if (v_isShared_2426_ == 0)
{
lean_ctor_set(v___x_2425_, 4, v_l_2404_);
lean_ctor_set(v___x_2425_, 2, v_v_2310_);
lean_ctor_set(v___x_2425_, 1, v_k_2309_);
lean_ctor_set(v___x_2425_, 0, v___x_2318_);
v___x_2436_ = v___x_2425_;
goto v_reusejp_2435_;
}
else
{
lean_object* v_reuseFailAlloc_2440_; 
v_reuseFailAlloc_2440_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2440_, 0, v___x_2318_);
lean_ctor_set(v_reuseFailAlloc_2440_, 1, v_k_2309_);
lean_ctor_set(v_reuseFailAlloc_2440_, 2, v_v_2310_);
lean_ctor_set(v_reuseFailAlloc_2440_, 3, v_l_2404_);
lean_ctor_set(v_reuseFailAlloc_2440_, 4, v_l_2404_);
v___x_2436_ = v_reuseFailAlloc_2440_;
goto v_reusejp_2435_;
}
v_reusejp_2435_:
{
lean_object* v___x_2438_; 
if (v_isShared_2315_ == 0)
{
lean_ctor_set(v___x_2314_, 4, v___x_2436_);
lean_ctor_set(v___x_2314_, 3, v___x_2434_);
lean_ctor_set(v___x_2314_, 2, v_v_2428_);
lean_ctor_set(v___x_2314_, 1, v_k_2427_);
lean_ctor_set(v___x_2314_, 0, v___x_2432_);
v___x_2438_ = v___x_2314_;
goto v_reusejp_2437_;
}
else
{
lean_object* v_reuseFailAlloc_2439_; 
v_reuseFailAlloc_2439_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2439_, 0, v___x_2432_);
lean_ctor_set(v_reuseFailAlloc_2439_, 1, v_k_2427_);
lean_ctor_set(v_reuseFailAlloc_2439_, 2, v_v_2428_);
lean_ctor_set(v_reuseFailAlloc_2439_, 3, v___x_2434_);
lean_ctor_set(v_reuseFailAlloc_2439_, 4, v___x_2436_);
v___x_2438_ = v_reuseFailAlloc_2439_;
goto v_reusejp_2437_;
}
v_reusejp_2437_:
{
return v___x_2438_;
}
}
}
}
}
}
else
{
lean_object* v___x_2450_; lean_object* v___x_2452_; 
v___x_2450_ = lean_unsigned_to_nat(2u);
if (v_isShared_2315_ == 0)
{
lean_ctor_set(v___x_2314_, 4, v_r_2421_);
lean_ctor_set(v___x_2314_, 3, v_impl_2317_);
lean_ctor_set(v___x_2314_, 0, v___x_2450_);
v___x_2452_ = v___x_2314_;
goto v_reusejp_2451_;
}
else
{
lean_object* v_reuseFailAlloc_2453_; 
v_reuseFailAlloc_2453_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2453_, 0, v___x_2450_);
lean_ctor_set(v_reuseFailAlloc_2453_, 1, v_k_2309_);
lean_ctor_set(v_reuseFailAlloc_2453_, 2, v_v_2310_);
lean_ctor_set(v_reuseFailAlloc_2453_, 3, v_impl_2317_);
lean_ctor_set(v_reuseFailAlloc_2453_, 4, v_r_2421_);
v___x_2452_ = v_reuseFailAlloc_2453_;
goto v_reusejp_2451_;
}
v_reusejp_2451_:
{
return v___x_2452_;
}
}
}
}
}
case 1:
{
lean_object* v___x_2455_; 
lean_dec(v_v_2310_);
lean_dec(v_k_2309_);
if (v_isShared_2315_ == 0)
{
lean_ctor_set(v___x_2314_, 2, v_v_2306_);
lean_ctor_set(v___x_2314_, 1, v_k_2305_);
v___x_2455_ = v___x_2314_;
goto v_reusejp_2454_;
}
else
{
lean_object* v_reuseFailAlloc_2456_; 
v_reuseFailAlloc_2456_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2456_, 0, v_size_2308_);
lean_ctor_set(v_reuseFailAlloc_2456_, 1, v_k_2305_);
lean_ctor_set(v_reuseFailAlloc_2456_, 2, v_v_2306_);
lean_ctor_set(v_reuseFailAlloc_2456_, 3, v_l_2311_);
lean_ctor_set(v_reuseFailAlloc_2456_, 4, v_r_2312_);
v___x_2455_ = v_reuseFailAlloc_2456_;
goto v_reusejp_2454_;
}
v_reusejp_2454_:
{
return v___x_2455_;
}
}
default: 
{
lean_object* v_impl_2457_; lean_object* v___x_2458_; 
lean_dec(v_size_2308_);
v_impl_2457_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Level_collectMVars_spec__1___redArg(v_k_2305_, v_v_2306_, v_r_2312_);
v___x_2458_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_2311_) == 0)
{
lean_object* v_size_2459_; lean_object* v_size_2460_; lean_object* v_k_2461_; lean_object* v_v_2462_; lean_object* v_l_2463_; lean_object* v_r_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; uint8_t v___x_2467_; 
v_size_2459_ = lean_ctor_get(v_l_2311_, 0);
v_size_2460_ = lean_ctor_get(v_impl_2457_, 0);
lean_inc(v_size_2460_);
v_k_2461_ = lean_ctor_get(v_impl_2457_, 1);
lean_inc(v_k_2461_);
v_v_2462_ = lean_ctor_get(v_impl_2457_, 2);
lean_inc(v_v_2462_);
v_l_2463_ = lean_ctor_get(v_impl_2457_, 3);
lean_inc(v_l_2463_);
v_r_2464_ = lean_ctor_get(v_impl_2457_, 4);
lean_inc(v_r_2464_);
v___x_2465_ = lean_unsigned_to_nat(3u);
v___x_2466_ = lean_nat_mul(v___x_2465_, v_size_2459_);
v___x_2467_ = lean_nat_dec_lt(v___x_2466_, v_size_2460_);
lean_dec(v___x_2466_);
if (v___x_2467_ == 0)
{
lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2471_; 
lean_dec(v_r_2464_);
lean_dec(v_l_2463_);
lean_dec(v_v_2462_);
lean_dec(v_k_2461_);
v___x_2468_ = lean_nat_add(v___x_2458_, v_size_2459_);
v___x_2469_ = lean_nat_add(v___x_2468_, v_size_2460_);
lean_dec(v_size_2460_);
lean_dec(v___x_2468_);
if (v_isShared_2315_ == 0)
{
lean_ctor_set(v___x_2314_, 4, v_impl_2457_);
lean_ctor_set(v___x_2314_, 0, v___x_2469_);
v___x_2471_ = v___x_2314_;
goto v_reusejp_2470_;
}
else
{
lean_object* v_reuseFailAlloc_2472_; 
v_reuseFailAlloc_2472_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2472_, 0, v___x_2469_);
lean_ctor_set(v_reuseFailAlloc_2472_, 1, v_k_2309_);
lean_ctor_set(v_reuseFailAlloc_2472_, 2, v_v_2310_);
lean_ctor_set(v_reuseFailAlloc_2472_, 3, v_l_2311_);
lean_ctor_set(v_reuseFailAlloc_2472_, 4, v_impl_2457_);
v___x_2471_ = v_reuseFailAlloc_2472_;
goto v_reusejp_2470_;
}
v_reusejp_2470_:
{
return v___x_2471_;
}
}
else
{
lean_object* v___x_2474_; uint8_t v_isShared_2475_; uint8_t v_isSharedCheck_2536_; 
v_isSharedCheck_2536_ = !lean_is_exclusive(v_impl_2457_);
if (v_isSharedCheck_2536_ == 0)
{
lean_object* v_unused_2537_; lean_object* v_unused_2538_; lean_object* v_unused_2539_; lean_object* v_unused_2540_; lean_object* v_unused_2541_; 
v_unused_2537_ = lean_ctor_get(v_impl_2457_, 4);
lean_dec(v_unused_2537_);
v_unused_2538_ = lean_ctor_get(v_impl_2457_, 3);
lean_dec(v_unused_2538_);
v_unused_2539_ = lean_ctor_get(v_impl_2457_, 2);
lean_dec(v_unused_2539_);
v_unused_2540_ = lean_ctor_get(v_impl_2457_, 1);
lean_dec(v_unused_2540_);
v_unused_2541_ = lean_ctor_get(v_impl_2457_, 0);
lean_dec(v_unused_2541_);
v___x_2474_ = v_impl_2457_;
v_isShared_2475_ = v_isSharedCheck_2536_;
goto v_resetjp_2473_;
}
else
{
lean_dec(v_impl_2457_);
v___x_2474_ = lean_box(0);
v_isShared_2475_ = v_isSharedCheck_2536_;
goto v_resetjp_2473_;
}
v_resetjp_2473_:
{
lean_object* v_size_2476_; lean_object* v_k_2477_; lean_object* v_v_2478_; lean_object* v_l_2479_; lean_object* v_r_2480_; lean_object* v_size_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; uint8_t v___x_2484_; 
v_size_2476_ = lean_ctor_get(v_l_2463_, 0);
v_k_2477_ = lean_ctor_get(v_l_2463_, 1);
v_v_2478_ = lean_ctor_get(v_l_2463_, 2);
v_l_2479_ = lean_ctor_get(v_l_2463_, 3);
v_r_2480_ = lean_ctor_get(v_l_2463_, 4);
v_size_2481_ = lean_ctor_get(v_r_2464_, 0);
v___x_2482_ = lean_unsigned_to_nat(2u);
v___x_2483_ = lean_nat_mul(v___x_2482_, v_size_2481_);
v___x_2484_ = lean_nat_dec_lt(v_size_2476_, v___x_2483_);
lean_dec(v___x_2483_);
if (v___x_2484_ == 0)
{
lean_object* v___x_2486_; uint8_t v_isShared_2487_; uint8_t v_isSharedCheck_2512_; 
lean_inc(v_r_2480_);
lean_inc(v_l_2479_);
lean_inc(v_v_2478_);
lean_inc(v_k_2477_);
v_isSharedCheck_2512_ = !lean_is_exclusive(v_l_2463_);
if (v_isSharedCheck_2512_ == 0)
{
lean_object* v_unused_2513_; lean_object* v_unused_2514_; lean_object* v_unused_2515_; lean_object* v_unused_2516_; lean_object* v_unused_2517_; 
v_unused_2513_ = lean_ctor_get(v_l_2463_, 4);
lean_dec(v_unused_2513_);
v_unused_2514_ = lean_ctor_get(v_l_2463_, 3);
lean_dec(v_unused_2514_);
v_unused_2515_ = lean_ctor_get(v_l_2463_, 2);
lean_dec(v_unused_2515_);
v_unused_2516_ = lean_ctor_get(v_l_2463_, 1);
lean_dec(v_unused_2516_);
v_unused_2517_ = lean_ctor_get(v_l_2463_, 0);
lean_dec(v_unused_2517_);
v___x_2486_ = v_l_2463_;
v_isShared_2487_ = v_isSharedCheck_2512_;
goto v_resetjp_2485_;
}
else
{
lean_dec(v_l_2463_);
v___x_2486_ = lean_box(0);
v_isShared_2487_ = v_isSharedCheck_2512_;
goto v_resetjp_2485_;
}
v_resetjp_2485_:
{
lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___y_2491_; lean_object* v___y_2492_; lean_object* v___y_2493_; lean_object* v___y_2502_; 
v___x_2488_ = lean_nat_add(v___x_2458_, v_size_2459_);
v___x_2489_ = lean_nat_add(v___x_2488_, v_size_2460_);
lean_dec(v_size_2460_);
if (lean_obj_tag(v_l_2479_) == 0)
{
lean_object* v_size_2510_; 
v_size_2510_ = lean_ctor_get(v_l_2479_, 0);
lean_inc(v_size_2510_);
v___y_2502_ = v_size_2510_;
goto v___jp_2501_;
}
else
{
lean_object* v___x_2511_; 
v___x_2511_ = lean_unsigned_to_nat(0u);
v___y_2502_ = v___x_2511_;
goto v___jp_2501_;
}
v___jp_2490_:
{
lean_object* v___x_2494_; lean_object* v___x_2496_; 
v___x_2494_ = lean_nat_add(v___y_2491_, v___y_2493_);
lean_dec(v___y_2493_);
lean_dec(v___y_2491_);
if (v_isShared_2487_ == 0)
{
lean_ctor_set(v___x_2486_, 4, v_r_2464_);
lean_ctor_set(v___x_2486_, 3, v_r_2480_);
lean_ctor_set(v___x_2486_, 2, v_v_2462_);
lean_ctor_set(v___x_2486_, 1, v_k_2461_);
lean_ctor_set(v___x_2486_, 0, v___x_2494_);
v___x_2496_ = v___x_2486_;
goto v_reusejp_2495_;
}
else
{
lean_object* v_reuseFailAlloc_2500_; 
v_reuseFailAlloc_2500_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2500_, 0, v___x_2494_);
lean_ctor_set(v_reuseFailAlloc_2500_, 1, v_k_2461_);
lean_ctor_set(v_reuseFailAlloc_2500_, 2, v_v_2462_);
lean_ctor_set(v_reuseFailAlloc_2500_, 3, v_r_2480_);
lean_ctor_set(v_reuseFailAlloc_2500_, 4, v_r_2464_);
v___x_2496_ = v_reuseFailAlloc_2500_;
goto v_reusejp_2495_;
}
v_reusejp_2495_:
{
lean_object* v___x_2498_; 
if (v_isShared_2475_ == 0)
{
lean_ctor_set(v___x_2474_, 4, v___x_2496_);
lean_ctor_set(v___x_2474_, 3, v___y_2492_);
lean_ctor_set(v___x_2474_, 2, v_v_2478_);
lean_ctor_set(v___x_2474_, 1, v_k_2477_);
lean_ctor_set(v___x_2474_, 0, v___x_2489_);
v___x_2498_ = v___x_2474_;
goto v_reusejp_2497_;
}
else
{
lean_object* v_reuseFailAlloc_2499_; 
v_reuseFailAlloc_2499_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2499_, 0, v___x_2489_);
lean_ctor_set(v_reuseFailAlloc_2499_, 1, v_k_2477_);
lean_ctor_set(v_reuseFailAlloc_2499_, 2, v_v_2478_);
lean_ctor_set(v_reuseFailAlloc_2499_, 3, v___y_2492_);
lean_ctor_set(v_reuseFailAlloc_2499_, 4, v___x_2496_);
v___x_2498_ = v_reuseFailAlloc_2499_;
goto v_reusejp_2497_;
}
v_reusejp_2497_:
{
return v___x_2498_;
}
}
}
v___jp_2501_:
{
lean_object* v___x_2503_; lean_object* v___x_2505_; 
v___x_2503_ = lean_nat_add(v___x_2488_, v___y_2502_);
lean_dec(v___y_2502_);
lean_dec(v___x_2488_);
if (v_isShared_2315_ == 0)
{
lean_ctor_set(v___x_2314_, 4, v_l_2479_);
lean_ctor_set(v___x_2314_, 0, v___x_2503_);
v___x_2505_ = v___x_2314_;
goto v_reusejp_2504_;
}
else
{
lean_object* v_reuseFailAlloc_2509_; 
v_reuseFailAlloc_2509_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2509_, 0, v___x_2503_);
lean_ctor_set(v_reuseFailAlloc_2509_, 1, v_k_2309_);
lean_ctor_set(v_reuseFailAlloc_2509_, 2, v_v_2310_);
lean_ctor_set(v_reuseFailAlloc_2509_, 3, v_l_2311_);
lean_ctor_set(v_reuseFailAlloc_2509_, 4, v_l_2479_);
v___x_2505_ = v_reuseFailAlloc_2509_;
goto v_reusejp_2504_;
}
v_reusejp_2504_:
{
lean_object* v___x_2506_; 
v___x_2506_ = lean_nat_add(v___x_2458_, v_size_2481_);
if (lean_obj_tag(v_r_2480_) == 0)
{
lean_object* v_size_2507_; 
v_size_2507_ = lean_ctor_get(v_r_2480_, 0);
lean_inc(v_size_2507_);
v___y_2491_ = v___x_2506_;
v___y_2492_ = v___x_2505_;
v___y_2493_ = v_size_2507_;
goto v___jp_2490_;
}
else
{
lean_object* v___x_2508_; 
v___x_2508_ = lean_unsigned_to_nat(0u);
v___y_2491_ = v___x_2506_;
v___y_2492_ = v___x_2505_;
v___y_2493_ = v___x_2508_;
goto v___jp_2490_;
}
}
}
}
}
else
{
lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2522_; 
lean_del_object(v___x_2314_);
v___x_2518_ = lean_nat_add(v___x_2458_, v_size_2459_);
v___x_2519_ = lean_nat_add(v___x_2518_, v_size_2460_);
lean_dec(v_size_2460_);
v___x_2520_ = lean_nat_add(v___x_2518_, v_size_2476_);
lean_dec(v___x_2518_);
lean_inc_ref(v_l_2311_);
if (v_isShared_2475_ == 0)
{
lean_ctor_set(v___x_2474_, 4, v_l_2463_);
lean_ctor_set(v___x_2474_, 3, v_l_2311_);
lean_ctor_set(v___x_2474_, 2, v_v_2310_);
lean_ctor_set(v___x_2474_, 1, v_k_2309_);
lean_ctor_set(v___x_2474_, 0, v___x_2520_);
v___x_2522_ = v___x_2474_;
goto v_reusejp_2521_;
}
else
{
lean_object* v_reuseFailAlloc_2535_; 
v_reuseFailAlloc_2535_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2535_, 0, v___x_2520_);
lean_ctor_set(v_reuseFailAlloc_2535_, 1, v_k_2309_);
lean_ctor_set(v_reuseFailAlloc_2535_, 2, v_v_2310_);
lean_ctor_set(v_reuseFailAlloc_2535_, 3, v_l_2311_);
lean_ctor_set(v_reuseFailAlloc_2535_, 4, v_l_2463_);
v___x_2522_ = v_reuseFailAlloc_2535_;
goto v_reusejp_2521_;
}
v_reusejp_2521_:
{
lean_object* v___x_2524_; uint8_t v_isShared_2525_; uint8_t v_isSharedCheck_2529_; 
v_isSharedCheck_2529_ = !lean_is_exclusive(v_l_2311_);
if (v_isSharedCheck_2529_ == 0)
{
lean_object* v_unused_2530_; lean_object* v_unused_2531_; lean_object* v_unused_2532_; lean_object* v_unused_2533_; lean_object* v_unused_2534_; 
v_unused_2530_ = lean_ctor_get(v_l_2311_, 4);
lean_dec(v_unused_2530_);
v_unused_2531_ = lean_ctor_get(v_l_2311_, 3);
lean_dec(v_unused_2531_);
v_unused_2532_ = lean_ctor_get(v_l_2311_, 2);
lean_dec(v_unused_2532_);
v_unused_2533_ = lean_ctor_get(v_l_2311_, 1);
lean_dec(v_unused_2533_);
v_unused_2534_ = lean_ctor_get(v_l_2311_, 0);
lean_dec(v_unused_2534_);
v___x_2524_ = v_l_2311_;
v_isShared_2525_ = v_isSharedCheck_2529_;
goto v_resetjp_2523_;
}
else
{
lean_dec(v_l_2311_);
v___x_2524_ = lean_box(0);
v_isShared_2525_ = v_isSharedCheck_2529_;
goto v_resetjp_2523_;
}
v_resetjp_2523_:
{
lean_object* v___x_2527_; 
if (v_isShared_2525_ == 0)
{
lean_ctor_set(v___x_2524_, 4, v_r_2464_);
lean_ctor_set(v___x_2524_, 3, v___x_2522_);
lean_ctor_set(v___x_2524_, 2, v_v_2462_);
lean_ctor_set(v___x_2524_, 1, v_k_2461_);
lean_ctor_set(v___x_2524_, 0, v___x_2519_);
v___x_2527_ = v___x_2524_;
goto v_reusejp_2526_;
}
else
{
lean_object* v_reuseFailAlloc_2528_; 
v_reuseFailAlloc_2528_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2528_, 0, v___x_2519_);
lean_ctor_set(v_reuseFailAlloc_2528_, 1, v_k_2461_);
lean_ctor_set(v_reuseFailAlloc_2528_, 2, v_v_2462_);
lean_ctor_set(v_reuseFailAlloc_2528_, 3, v___x_2522_);
lean_ctor_set(v_reuseFailAlloc_2528_, 4, v_r_2464_);
v___x_2527_ = v_reuseFailAlloc_2528_;
goto v_reusejp_2526_;
}
v_reusejp_2526_:
{
return v___x_2527_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_2542_; 
v_l_2542_ = lean_ctor_get(v_impl_2457_, 3);
lean_inc(v_l_2542_);
if (lean_obj_tag(v_l_2542_) == 0)
{
lean_object* v_r_2543_; lean_object* v_k_2544_; lean_object* v_v_2545_; lean_object* v___x_2547_; uint8_t v_isShared_2548_; uint8_t v_isSharedCheck_2568_; 
v_r_2543_ = lean_ctor_get(v_impl_2457_, 4);
v_k_2544_ = lean_ctor_get(v_impl_2457_, 1);
v_v_2545_ = lean_ctor_get(v_impl_2457_, 2);
v_isSharedCheck_2568_ = !lean_is_exclusive(v_impl_2457_);
if (v_isSharedCheck_2568_ == 0)
{
lean_object* v_unused_2569_; lean_object* v_unused_2570_; 
v_unused_2569_ = lean_ctor_get(v_impl_2457_, 3);
lean_dec(v_unused_2569_);
v_unused_2570_ = lean_ctor_get(v_impl_2457_, 0);
lean_dec(v_unused_2570_);
v___x_2547_ = v_impl_2457_;
v_isShared_2548_ = v_isSharedCheck_2568_;
goto v_resetjp_2546_;
}
else
{
lean_inc(v_r_2543_);
lean_inc(v_v_2545_);
lean_inc(v_k_2544_);
lean_dec(v_impl_2457_);
v___x_2547_ = lean_box(0);
v_isShared_2548_ = v_isSharedCheck_2568_;
goto v_resetjp_2546_;
}
v_resetjp_2546_:
{
lean_object* v_k_2549_; lean_object* v_v_2550_; lean_object* v___x_2552_; uint8_t v_isShared_2553_; uint8_t v_isSharedCheck_2564_; 
v_k_2549_ = lean_ctor_get(v_l_2542_, 1);
v_v_2550_ = lean_ctor_get(v_l_2542_, 2);
v_isSharedCheck_2564_ = !lean_is_exclusive(v_l_2542_);
if (v_isSharedCheck_2564_ == 0)
{
lean_object* v_unused_2565_; lean_object* v_unused_2566_; lean_object* v_unused_2567_; 
v_unused_2565_ = lean_ctor_get(v_l_2542_, 4);
lean_dec(v_unused_2565_);
v_unused_2566_ = lean_ctor_get(v_l_2542_, 3);
lean_dec(v_unused_2566_);
v_unused_2567_ = lean_ctor_get(v_l_2542_, 0);
lean_dec(v_unused_2567_);
v___x_2552_ = v_l_2542_;
v_isShared_2553_ = v_isSharedCheck_2564_;
goto v_resetjp_2551_;
}
else
{
lean_inc(v_v_2550_);
lean_inc(v_k_2549_);
lean_dec(v_l_2542_);
v___x_2552_ = lean_box(0);
v_isShared_2553_ = v_isSharedCheck_2564_;
goto v_resetjp_2551_;
}
v_resetjp_2551_:
{
lean_object* v___x_2554_; lean_object* v___x_2556_; 
v___x_2554_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_2543_, 2);
if (v_isShared_2553_ == 0)
{
lean_ctor_set(v___x_2552_, 4, v_r_2543_);
lean_ctor_set(v___x_2552_, 3, v_r_2543_);
lean_ctor_set(v___x_2552_, 2, v_v_2310_);
lean_ctor_set(v___x_2552_, 1, v_k_2309_);
lean_ctor_set(v___x_2552_, 0, v___x_2458_);
v___x_2556_ = v___x_2552_;
goto v_reusejp_2555_;
}
else
{
lean_object* v_reuseFailAlloc_2563_; 
v_reuseFailAlloc_2563_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2563_, 0, v___x_2458_);
lean_ctor_set(v_reuseFailAlloc_2563_, 1, v_k_2309_);
lean_ctor_set(v_reuseFailAlloc_2563_, 2, v_v_2310_);
lean_ctor_set(v_reuseFailAlloc_2563_, 3, v_r_2543_);
lean_ctor_set(v_reuseFailAlloc_2563_, 4, v_r_2543_);
v___x_2556_ = v_reuseFailAlloc_2563_;
goto v_reusejp_2555_;
}
v_reusejp_2555_:
{
lean_object* v___x_2558_; 
lean_inc(v_r_2543_);
if (v_isShared_2548_ == 0)
{
lean_ctor_set(v___x_2547_, 3, v_r_2543_);
lean_ctor_set(v___x_2547_, 0, v___x_2458_);
v___x_2558_ = v___x_2547_;
goto v_reusejp_2557_;
}
else
{
lean_object* v_reuseFailAlloc_2562_; 
v_reuseFailAlloc_2562_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2562_, 0, v___x_2458_);
lean_ctor_set(v_reuseFailAlloc_2562_, 1, v_k_2544_);
lean_ctor_set(v_reuseFailAlloc_2562_, 2, v_v_2545_);
lean_ctor_set(v_reuseFailAlloc_2562_, 3, v_r_2543_);
lean_ctor_set(v_reuseFailAlloc_2562_, 4, v_r_2543_);
v___x_2558_ = v_reuseFailAlloc_2562_;
goto v_reusejp_2557_;
}
v_reusejp_2557_:
{
lean_object* v___x_2560_; 
if (v_isShared_2315_ == 0)
{
lean_ctor_set(v___x_2314_, 4, v___x_2558_);
lean_ctor_set(v___x_2314_, 3, v___x_2556_);
lean_ctor_set(v___x_2314_, 2, v_v_2550_);
lean_ctor_set(v___x_2314_, 1, v_k_2549_);
lean_ctor_set(v___x_2314_, 0, v___x_2554_);
v___x_2560_ = v___x_2314_;
goto v_reusejp_2559_;
}
else
{
lean_object* v_reuseFailAlloc_2561_; 
v_reuseFailAlloc_2561_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2561_, 0, v___x_2554_);
lean_ctor_set(v_reuseFailAlloc_2561_, 1, v_k_2549_);
lean_ctor_set(v_reuseFailAlloc_2561_, 2, v_v_2550_);
lean_ctor_set(v_reuseFailAlloc_2561_, 3, v___x_2556_);
lean_ctor_set(v_reuseFailAlloc_2561_, 4, v___x_2558_);
v___x_2560_ = v_reuseFailAlloc_2561_;
goto v_reusejp_2559_;
}
v_reusejp_2559_:
{
return v___x_2560_;
}
}
}
}
}
}
else
{
lean_object* v_r_2571_; 
v_r_2571_ = lean_ctor_get(v_impl_2457_, 4);
lean_inc(v_r_2571_);
if (lean_obj_tag(v_r_2571_) == 0)
{
lean_object* v_k_2572_; lean_object* v_v_2573_; lean_object* v___x_2575_; uint8_t v_isShared_2576_; uint8_t v_isSharedCheck_2584_; 
v_k_2572_ = lean_ctor_get(v_impl_2457_, 1);
v_v_2573_ = lean_ctor_get(v_impl_2457_, 2);
v_isSharedCheck_2584_ = !lean_is_exclusive(v_impl_2457_);
if (v_isSharedCheck_2584_ == 0)
{
lean_object* v_unused_2585_; lean_object* v_unused_2586_; lean_object* v_unused_2587_; 
v_unused_2585_ = lean_ctor_get(v_impl_2457_, 4);
lean_dec(v_unused_2585_);
v_unused_2586_ = lean_ctor_get(v_impl_2457_, 3);
lean_dec(v_unused_2586_);
v_unused_2587_ = lean_ctor_get(v_impl_2457_, 0);
lean_dec(v_unused_2587_);
v___x_2575_ = v_impl_2457_;
v_isShared_2576_ = v_isSharedCheck_2584_;
goto v_resetjp_2574_;
}
else
{
lean_inc(v_v_2573_);
lean_inc(v_k_2572_);
lean_dec(v_impl_2457_);
v___x_2575_ = lean_box(0);
v_isShared_2576_ = v_isSharedCheck_2584_;
goto v_resetjp_2574_;
}
v_resetjp_2574_:
{
lean_object* v___x_2577_; lean_object* v___x_2579_; 
v___x_2577_ = lean_unsigned_to_nat(3u);
if (v_isShared_2576_ == 0)
{
lean_ctor_set(v___x_2575_, 4, v_l_2542_);
lean_ctor_set(v___x_2575_, 2, v_v_2310_);
lean_ctor_set(v___x_2575_, 1, v_k_2309_);
lean_ctor_set(v___x_2575_, 0, v___x_2458_);
v___x_2579_ = v___x_2575_;
goto v_reusejp_2578_;
}
else
{
lean_object* v_reuseFailAlloc_2583_; 
v_reuseFailAlloc_2583_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2583_, 0, v___x_2458_);
lean_ctor_set(v_reuseFailAlloc_2583_, 1, v_k_2309_);
lean_ctor_set(v_reuseFailAlloc_2583_, 2, v_v_2310_);
lean_ctor_set(v_reuseFailAlloc_2583_, 3, v_l_2542_);
lean_ctor_set(v_reuseFailAlloc_2583_, 4, v_l_2542_);
v___x_2579_ = v_reuseFailAlloc_2583_;
goto v_reusejp_2578_;
}
v_reusejp_2578_:
{
lean_object* v___x_2581_; 
if (v_isShared_2315_ == 0)
{
lean_ctor_set(v___x_2314_, 4, v_r_2571_);
lean_ctor_set(v___x_2314_, 3, v___x_2579_);
lean_ctor_set(v___x_2314_, 2, v_v_2573_);
lean_ctor_set(v___x_2314_, 1, v_k_2572_);
lean_ctor_set(v___x_2314_, 0, v___x_2577_);
v___x_2581_ = v___x_2314_;
goto v_reusejp_2580_;
}
else
{
lean_object* v_reuseFailAlloc_2582_; 
v_reuseFailAlloc_2582_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2582_, 0, v___x_2577_);
lean_ctor_set(v_reuseFailAlloc_2582_, 1, v_k_2572_);
lean_ctor_set(v_reuseFailAlloc_2582_, 2, v_v_2573_);
lean_ctor_set(v_reuseFailAlloc_2582_, 3, v___x_2579_);
lean_ctor_set(v_reuseFailAlloc_2582_, 4, v_r_2571_);
v___x_2581_ = v_reuseFailAlloc_2582_;
goto v_reusejp_2580_;
}
v_reusejp_2580_:
{
return v___x_2581_;
}
}
}
}
else
{
lean_object* v___x_2588_; lean_object* v___x_2590_; 
v___x_2588_ = lean_unsigned_to_nat(2u);
if (v_isShared_2315_ == 0)
{
lean_ctor_set(v___x_2314_, 4, v_impl_2457_);
lean_ctor_set(v___x_2314_, 3, v_r_2571_);
lean_ctor_set(v___x_2314_, 0, v___x_2588_);
v___x_2590_ = v___x_2314_;
goto v_reusejp_2589_;
}
else
{
lean_object* v_reuseFailAlloc_2591_; 
v_reuseFailAlloc_2591_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2591_, 0, v___x_2588_);
lean_ctor_set(v_reuseFailAlloc_2591_, 1, v_k_2309_);
lean_ctor_set(v_reuseFailAlloc_2591_, 2, v_v_2310_);
lean_ctor_set(v_reuseFailAlloc_2591_, 3, v_r_2571_);
lean_ctor_set(v_reuseFailAlloc_2591_, 4, v_impl_2457_);
v___x_2590_ = v_reuseFailAlloc_2591_;
goto v_reusejp_2589_;
}
v_reusejp_2589_:
{
return v___x_2590_;
}
}
}
}
}
}
}
}
else
{
lean_object* v___x_2593_; lean_object* v___x_2594_; 
v___x_2593_ = lean_unsigned_to_nat(1u);
v___x_2594_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2594_, 0, v___x_2593_);
lean_ctor_set(v___x_2594_, 1, v_k_2305_);
lean_ctor_set(v___x_2594_, 2, v_v_2306_);
lean_ctor_set(v___x_2594_, 3, v_t_2307_);
lean_ctor_set(v___x_2594_, 4, v_t_2307_);
return v___x_2594_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Level_collectMVars_spec__0___redArg(lean_object* v_k_2595_, lean_object* v_t_2596_){
_start:
{
if (lean_obj_tag(v_t_2596_) == 0)
{
lean_object* v_k_2597_; lean_object* v_l_2598_; lean_object* v_r_2599_; uint8_t v___x_2600_; 
v_k_2597_ = lean_ctor_get(v_t_2596_, 1);
v_l_2598_ = lean_ctor_get(v_t_2596_, 3);
v_r_2599_ = lean_ctor_get(v_t_2596_, 4);
v___x_2600_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2595_, v_k_2597_);
switch(v___x_2600_)
{
case 0:
{
v_t_2596_ = v_l_2598_;
goto _start;
}
case 1:
{
uint8_t v___x_2602_; 
v___x_2602_ = 1;
return v___x_2602_;
}
default: 
{
v_t_2596_ = v_r_2599_;
goto _start;
}
}
}
else
{
uint8_t v___x_2604_; 
v___x_2604_ = 0;
return v___x_2604_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Level_collectMVars_spec__0___redArg___boxed(lean_object* v_k_2605_, lean_object* v_t_2606_){
_start:
{
uint8_t v_res_2607_; lean_object* v_r_2608_; 
v_res_2607_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Level_collectMVars_spec__0___redArg(v_k_2605_, v_t_2606_);
lean_dec(v_t_2606_);
lean_dec(v_k_2605_);
v_r_2608_ = lean_box(v_res_2607_);
return v_r_2608_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_collectMVars(lean_object* v_u_2609_, lean_object* v_s_2610_){
_start:
{
lean_object* v_u_2612_; lean_object* v_v_2613_; 
switch(lean_obj_tag(v_u_2609_))
{
case 1:
{
lean_object* v_a_2616_; 
v_a_2616_ = lean_ctor_get(v_u_2609_, 0);
lean_inc(v_a_2616_);
lean_dec_ref_known(v_u_2609_, 1);
v_u_2609_ = v_a_2616_;
goto _start;
}
case 2:
{
lean_object* v_a_2618_; lean_object* v_a_2619_; 
v_a_2618_ = lean_ctor_get(v_u_2609_, 0);
lean_inc(v_a_2618_);
v_a_2619_ = lean_ctor_get(v_u_2609_, 1);
lean_inc(v_a_2619_);
lean_dec_ref_known(v_u_2609_, 2);
v_u_2612_ = v_a_2618_;
v_v_2613_ = v_a_2619_;
goto v___jp_2611_;
}
case 3:
{
lean_object* v_a_2620_; lean_object* v_a_2621_; 
v_a_2620_ = lean_ctor_get(v_u_2609_, 0);
lean_inc(v_a_2620_);
v_a_2621_ = lean_ctor_get(v_u_2609_, 1);
lean_inc(v_a_2621_);
lean_dec_ref_known(v_u_2609_, 2);
v_u_2612_ = v_a_2620_;
v_v_2613_ = v_a_2621_;
goto v___jp_2611_;
}
case 5:
{
lean_object* v_a_2622_; uint8_t v___x_2623_; 
v_a_2622_ = lean_ctor_get(v_u_2609_, 0);
lean_inc(v_a_2622_);
lean_dec_ref_known(v_u_2609_, 1);
v___x_2623_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Level_collectMVars_spec__0___redArg(v_a_2622_, v_s_2610_);
if (v___x_2623_ == 0)
{
lean_object* v___x_2624_; lean_object* v___x_2625_; 
v___x_2624_ = lean_box(0);
v___x_2625_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Level_collectMVars_spec__1___redArg(v_a_2622_, v___x_2624_, v_s_2610_);
return v___x_2625_;
}
else
{
lean_dec(v_a_2622_);
return v_s_2610_;
}
}
default: 
{
lean_dec(v_u_2609_);
return v_s_2610_;
}
}
v___jp_2611_:
{
lean_object* v___x_2614_; 
v___x_2614_ = l_Lean_Level_collectMVars(v_v_2613_, v_s_2610_);
v_u_2609_ = v_u_2612_;
v_s_2610_ = v___x_2614_;
goto _start;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Level_collectMVars_spec__0(lean_object* v_00_u03b2_2626_, lean_object* v_k_2627_, lean_object* v_t_2628_){
_start:
{
uint8_t v___x_2629_; 
v___x_2629_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Level_collectMVars_spec__0___redArg(v_k_2627_, v_t_2628_);
return v___x_2629_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Level_collectMVars_spec__0___boxed(lean_object* v_00_u03b2_2630_, lean_object* v_k_2631_, lean_object* v_t_2632_){
_start:
{
uint8_t v_res_2633_; lean_object* v_r_2634_; 
v_res_2633_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Level_collectMVars_spec__0(v_00_u03b2_2630_, v_k_2631_, v_t_2632_);
lean_dec(v_t_2632_);
lean_dec(v_k_2631_);
v_r_2634_ = lean_box(v_res_2633_);
return v_r_2634_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Level_collectMVars_spec__1(lean_object* v_00_u03b2_2635_, lean_object* v_k_2636_, lean_object* v_v_2637_, lean_object* v_t_2638_, lean_object* v_hl_2639_){
_start:
{
lean_object* v___x_2640_; 
v___x_2640_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Level_collectMVars_spec__1___redArg(v_k_2636_, v_v_2637_, v_t_2638_);
return v___x_2640_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_find_x3f_visit(lean_object* v_p_2641_, lean_object* v_u_2642_){
_start:
{
lean_object* v_u_2644_; lean_object* v_v_2645_; lean_object* v___x_2648_; uint8_t v___x_2649_; 
lean_inc_ref(v_p_2641_);
lean_inc(v_u_2642_);
v___x_2648_ = lean_apply_1(v_p_2641_, v_u_2642_);
v___x_2649_ = lean_unbox(v___x_2648_);
if (v___x_2649_ == 0)
{
switch(lean_obj_tag(v_u_2642_))
{
case 1:
{
lean_object* v_a_2650_; 
v_a_2650_ = lean_ctor_get(v_u_2642_, 0);
lean_inc(v_a_2650_);
lean_dec_ref_known(v_u_2642_, 1);
v_u_2642_ = v_a_2650_;
goto _start;
}
case 2:
{
lean_object* v_a_2652_; lean_object* v_a_2653_; 
v_a_2652_ = lean_ctor_get(v_u_2642_, 0);
lean_inc(v_a_2652_);
v_a_2653_ = lean_ctor_get(v_u_2642_, 1);
lean_inc(v_a_2653_);
lean_dec_ref_known(v_u_2642_, 2);
v_u_2644_ = v_a_2652_;
v_v_2645_ = v_a_2653_;
goto v___jp_2643_;
}
case 3:
{
lean_object* v_a_2654_; lean_object* v_a_2655_; 
v_a_2654_ = lean_ctor_get(v_u_2642_, 0);
lean_inc(v_a_2654_);
v_a_2655_ = lean_ctor_get(v_u_2642_, 1);
lean_inc(v_a_2655_);
lean_dec_ref_known(v_u_2642_, 2);
v_u_2644_ = v_a_2654_;
v_v_2645_ = v_a_2655_;
goto v___jp_2643_;
}
default: 
{
lean_object* v___x_2656_; 
lean_dec(v_u_2642_);
lean_dec_ref(v_p_2641_);
v___x_2656_ = lean_box(0);
return v___x_2656_;
}
}
}
else
{
lean_object* v___x_2657_; 
lean_dec_ref(v_p_2641_);
v___x_2657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2657_, 0, v_u_2642_);
return v___x_2657_;
}
v___jp_2643_:
{
lean_object* v___x_2646_; 
lean_inc_ref(v_p_2641_);
v___x_2646_ = l___private_Lean_Level_0__Lean_Level_find_x3f_visit(v_p_2641_, v_u_2644_);
if (lean_obj_tag(v___x_2646_) == 0)
{
v_u_2642_ = v_v_2645_;
goto _start;
}
else
{
lean_dec(v_v_2645_);
lean_dec_ref(v_p_2641_);
return v___x_2646_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_find_x3f(lean_object* v_u_2658_, lean_object* v_p_2659_){
_start:
{
lean_object* v___x_2660_; 
v___x_2660_ = l___private_Lean_Level_0__Lean_Level_find_x3f_visit(v_p_2659_, v_u_2658_);
return v___x_2660_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_any(lean_object* v_u_2661_, lean_object* v_p_2662_){
_start:
{
lean_object* v___x_2663_; 
v___x_2663_ = l___private_Lean_Level_0__Lean_Level_find_x3f_visit(v_p_2662_, v_u_2661_);
if (lean_obj_tag(v___x_2663_) == 0)
{
uint8_t v___x_2664_; 
v___x_2664_ = 0;
return v___x_2664_;
}
else
{
uint8_t v___x_2665_; 
lean_dec_ref_known(v___x_2663_, 1);
v___x_2665_ = 1;
return v___x_2665_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_any___boxed(lean_object* v_u_2666_, lean_object* v_p_2667_){
_start:
{
uint8_t v_res_2668_; lean_object* v_r_2669_; 
v_res_2668_ = l_Lean_Level_any(v_u_2666_, v_p_2667_);
v_r_2669_ = lean_box(v_res_2668_);
return v_r_2669_;
}
}
LEAN_EXPORT lean_object* l_Lean_Nat_toLevel(lean_object* v_n_2670_){
_start:
{
lean_object* v___x_2671_; 
v___x_2671_ = l_Lean_Level_ofNat(v_n_2670_);
return v___x_2671_;
}
}
LEAN_EXPORT lean_object* l_Lean_Nat_toLevel___boxed(lean_object* v_n_2672_){
_start:
{
lean_object* v_res_2673_; 
v_res_2673_ = l_Lean_Nat_toLevel(v_n_2672_);
lean_dec(v_n_2672_);
return v_res_2673_;
}
}
lean_object* runtime_initialize_Init_Data_Array_QSort(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_PersistentHashSet(uint8_t builtin);
lean_object* runtime_initialize_Lean_Hygiene(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Option_Coe(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Internal_Linear(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Level(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Array_QSort(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_PersistentHashSet(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Hygiene(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Option_Coe(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Internal_Linear(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_instInhabitedData___aux__1 = _init_l_Lean_instInhabitedData___aux__1();
l_Lean_instInhabitedData = _init_l_Lean_instInhabitedData();
l_Lean_instInhabitedLevelMVarId_default = _init_l_Lean_instInhabitedLevelMVarId_default();
lean_mark_persistent(l_Lean_instInhabitedLevelMVarId_default);
l_Lean_instInhabitedLevelMVarId = _init_l_Lean_instInhabitedLevelMVarId();
lean_mark_persistent(l_Lean_instInhabitedLevelMVarId);
l_Lean_instInhabitedLMVarIdSet___aux__1 = _init_l_Lean_instInhabitedLMVarIdSet___aux__1();
lean_mark_persistent(l_Lean_instInhabitedLMVarIdSet___aux__1);
l_Lean_instInhabitedLMVarIdSet = _init_l_Lean_instInhabitedLMVarIdSet();
lean_mark_persistent(l_Lean_instInhabitedLMVarIdSet);
l_Lean_instEmptyCollectionLMVarIdSet___aux__1 = _init_l_Lean_instEmptyCollectionLMVarIdSet___aux__1();
lean_mark_persistent(l_Lean_instEmptyCollectionLMVarIdSet___aux__1);
l_Lean_instEmptyCollectionLMVarIdSet = _init_l_Lean_instEmptyCollectionLMVarIdSet();
lean_mark_persistent(l_Lean_instEmptyCollectionLMVarIdSet);
l_Lean_Level_zero___override = _init_l_Lean_Level_zero___override();
lean_mark_persistent(l_Lean_Level_zero___override);
l_Lean_instInhabitedLevel_default = _init_l_Lean_instInhabitedLevel_default();
lean_mark_persistent(l_Lean_instInhabitedLevel_default);
l_Lean_instInhabitedLevel = _init_l_Lean_instInhabitedLevel();
lean_mark_persistent(l_Lean_instInhabitedLevel);
l_Lean_levelZero = _init_l_Lean_levelZero();
lean_mark_persistent(l_Lean_levelZero);
l_Lean_Level_one = _init_l_Lean_Level_one();
lean_mark_persistent(l_Lean_Level_one);
l_Lean_levelOne = _init_l_Lean_levelOne();
lean_mark_persistent(l_Lean_levelOne);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Level(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Array_QSort(uint8_t builtin);
lean_object* initialize_Lean_Data_PersistentHashSet(uint8_t builtin);
lean_object* initialize_Lean_Hygiene(uint8_t builtin);
lean_object* initialize_Init_Data_Option_Coe(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Internal_Linear(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Level(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Array_QSort(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_PersistentHashSet(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Hygiene(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Option_Coe(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Internal_Linear(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Level(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Level(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Level(builtin);
}
#ifdef __cplusplus
}
#endif
