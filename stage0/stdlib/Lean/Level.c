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
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
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
static const lean_string_object l_Lean_Level_PP_toResult___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "_"};
static const lean_object* l_Lean_Level_PP_toResult___closed__1 = (const lean_object*)&l_Lean_Level_PP_toResult___closed__1_value;
static const lean_ctor_object l_Lean_Level_PP_toResult___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Level_PP_toResult___closed__1_value),LEAN_SCALAR_PTR_LITERAL(168, 60, 211, 188, 58, 220, 100, 184)}};
static const lean_object* l_Lean_Level_PP_toResult___closed__2 = (const lean_object*)&l_Lean_Level_PP_toResult___closed__2_value;
static const lean_ctor_object l_Lean_Level_PP_toResult___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Level_PP_toResult___closed__2_value)}};
static const lean_object* l_Lean_Level_PP_toResult___closed__3 = (const lean_object*)&l_Lean_Level_PP_toResult___closed__3_value;
static const lean_string_object l_Lean_Level_PP_toResult___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "\?u"};
static const lean_object* l_Lean_Level_PP_toResult___closed__4 = (const lean_object*)&l_Lean_Level_PP_toResult___closed__4_value;
static const lean_ctor_object l_Lean_Level_PP_toResult___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Level_PP_toResult___closed__4_value),LEAN_SCALAR_PTR_LITERAL(228, 117, 157, 98, 226, 186, 76, 191)}};
static const lean_object* l_Lean_Level_PP_toResult___closed__5 = (const lean_object*)&l_Lean_Level_PP_toResult___closed__5_value;
static const lean_string_object l_Lean_Level_PP_toResult___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "_uniq"};
static const lean_object* l_Lean_Level_PP_toResult___closed__6 = (const lean_object*)&l_Lean_Level_PP_toResult___closed__6_value;
static const lean_ctor_object l_Lean_Level_PP_toResult___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Level_PP_toResult___closed__6_value),LEAN_SCALAR_PTR_LITERAL(237, 141, 162, 170, 202, 74, 55, 55)}};
static const lean_object* l_Lean_Level_PP_toResult___closed__7 = (const lean_object*)&l_Lean_Level_PP_toResult___closed__7_value;
static const lean_string_object l_Lean_Level_PP_toResult___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "\?_mvar"};
static const lean_object* l_Lean_Level_PP_toResult___closed__8 = (const lean_object*)&l_Lean_Level_PP_toResult___closed__8_value;
static const lean_ctor_object l_Lean_Level_PP_toResult___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Level_PP_toResult___closed__8_value),LEAN_SCALAR_PTR_LITERAL(49, 72, 57, 220, 81, 200, 89, 8)}};
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
static uint64_t _init_l_Lean_instInhabitedData___aux__1(void){
_start:
{
uint64_t v___x_9_; 
v___x_9_ = 0ULL;
return v___x_9_;
}
}
static uint64_t _init_l_Lean_instInhabitedData(void){
_start:
{
uint64_t v___x_10_; 
v___x_10_ = 0ULL;
return v___x_10_;
}
}
LEAN_EXPORT uint64_t l_Lean_Level_Data_hash(uint64_t v_c_11_){
_start:
{
uint32_t v___x_12_; uint64_t v___x_13_; 
v___x_12_ = lean_uint64_to_uint32(v_c_11_);
v___x_13_ = lean_uint32_to_uint64(v___x_12_);
return v___x_13_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_Data_hash___boxed(lean_object* v_c_14_){
_start:
{
uint64_t v_c_boxed_15_; uint64_t v_res_16_; lean_object* v_r_17_; 
v_c_boxed_15_ = lean_unbox_uint64(v_c_14_);
lean_dec_ref(v_c_14_);
v_res_16_ = l_Lean_Level_Data_hash(v_c_boxed_15_);
v_r_17_ = lean_box_uint64(v_res_16_);
return v_r_17_;
}
}
LEAN_EXPORT uint32_t l_Lean_Level_Data_depth(uint64_t v_c_20_){
_start:
{
uint64_t v___x_21_; uint64_t v___x_22_; uint32_t v___x_23_; 
v___x_21_ = 40ULL;
v___x_22_ = lean_uint64_shift_right(v_c_20_, v___x_21_);
v___x_23_ = lean_uint64_to_uint32(v___x_22_);
return v___x_23_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_Data_depth___boxed(lean_object* v_c_24_){
_start:
{
uint64_t v_c_boxed_25_; uint32_t v_res_26_; lean_object* v_r_27_; 
v_c_boxed_25_ = lean_unbox_uint64(v_c_24_);
lean_dec_ref(v_c_24_);
v_res_26_ = l_Lean_Level_Data_depth(v_c_boxed_25_);
v_r_27_ = lean_box_uint32(v_res_26_);
return v_r_27_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_Data_hasMVar(uint64_t v_c_28_){
_start:
{
uint64_t v___x_29_; uint64_t v___x_30_; uint64_t v___x_31_; uint64_t v___x_32_; uint8_t v___x_33_; 
v___x_29_ = 32ULL;
v___x_30_ = lean_uint64_shift_right(v_c_28_, v___x_29_);
v___x_31_ = 1ULL;
v___x_32_ = lean_uint64_land(v___x_30_, v___x_31_);
v___x_33_ = lean_uint64_dec_eq(v___x_32_, v___x_31_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_Data_hasMVar___boxed(lean_object* v_c_34_){
_start:
{
uint64_t v_c_boxed_35_; uint8_t v_res_36_; lean_object* v_r_37_; 
v_c_boxed_35_ = lean_unbox_uint64(v_c_34_);
lean_dec_ref(v_c_34_);
v_res_36_ = l_Lean_Level_Data_hasMVar(v_c_boxed_35_);
v_r_37_ = lean_box(v_res_36_);
return v_r_37_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_Data_hasParam(uint64_t v_c_38_){
_start:
{
uint64_t v___x_39_; uint64_t v___x_40_; uint64_t v___x_41_; uint64_t v___x_42_; uint8_t v___x_43_; 
v___x_39_ = 33ULL;
v___x_40_ = lean_uint64_shift_right(v_c_38_, v___x_39_);
v___x_41_ = 1ULL;
v___x_42_ = lean_uint64_land(v___x_40_, v___x_41_);
v___x_43_ = lean_uint64_dec_eq(v___x_42_, v___x_41_);
return v___x_43_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_Data_hasParam___boxed(lean_object* v_c_44_){
_start:
{
uint64_t v_c_boxed_45_; uint8_t v_res_46_; lean_object* v_r_47_; 
v_c_boxed_45_ = lean_unbox_uint64(v_c_44_);
lean_dec_ref(v_c_44_);
v_res_46_ = l_Lean_Level_Data_hasParam(v_c_boxed_45_);
v_r_47_ = lean_box(v_res_46_);
return v_r_47_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_mkData___boxed(lean_object* v_h_52_, lean_object* v_depth_53_, lean_object* v_hasMVar_54_, lean_object* v_hasParam_55_){
_start:
{
uint64_t v_h_boxed_56_; uint8_t v_hasMVar_boxed_57_; uint8_t v_hasParam_boxed_58_; uint64_t v_res_59_; lean_object* v_r_60_; 
v_h_boxed_56_ = lean_unbox_uint64(v_h_52_);
lean_dec_ref(v_h_52_);
v_hasMVar_boxed_57_ = lean_unbox(v_hasMVar_54_);
v_hasParam_boxed_58_ = lean_unbox(v_hasParam_55_);
v_res_59_ = lean_level_mk_data(v_h_boxed_56_, v_depth_53_, v_hasMVar_boxed_57_, v_hasParam_boxed_58_);
v_r_60_ = lean_box_uint64(v_res_59_);
return v_r_60_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprData___lam__0(uint64_t v_v_68_, lean_object* v_prec_69_){
_start:
{
lean_object* v_r_71_; lean_object* v___y_75_; lean_object* v___y_76_; lean_object* v_r_81_; lean_object* v___y_88_; lean_object* v___y_89_; lean_object* v_r_94_; lean_object* v___x_100_; uint64_t v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v_r_104_; uint32_t v___x_105_; uint32_t v___x_106_; uint8_t v___x_107_; 
v___x_100_ = ((lean_object*)(l_Lean_instReprData___lam__0___closed__5));
v___x_101_ = l_Lean_Level_Data_hash(v_v_68_);
v___x_102_ = lean_uint64_to_nat(v___x_101_);
v___x_103_ = l_Nat_reprFast(v___x_102_);
v_r_104_ = lean_string_append(v___x_100_, v___x_103_);
lean_dec_ref(v___x_103_);
v___x_105_ = l_Lean_Level_Data_depth(v_v_68_);
v___x_106_ = 0;
v___x_107_ = lean_uint32_dec_eq(v___x_105_, v___x_106_);
if (v___x_107_ == 0)
{
lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v_r_114_; 
v___x_108_ = ((lean_object*)(l_Lean_instReprData___lam__0___closed__6));
v___x_109_ = lean_string_append(v_r_104_, v___x_108_);
v___x_110_ = lean_uint32_to_nat(v___x_105_);
v___x_111_ = l_Nat_reprFast(v___x_110_);
v___x_112_ = lean_string_append(v___x_109_, v___x_111_);
lean_dec_ref(v___x_111_);
v___x_113_ = ((lean_object*)(l_Lean_instReprData___lam__0___closed__0));
v_r_114_ = lean_string_append(v___x_112_, v___x_113_);
v_r_94_ = v_r_114_;
goto v___jp_93_;
}
else
{
v_r_94_ = v_r_104_;
goto v___jp_93_;
}
v___jp_70_:
{
lean_object* v___x_72_; lean_object* v___x_73_; 
v___x_72_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_72_, 0, v_r_71_);
v___x_73_ = l_Repr_addAppParen(v___x_72_, v_prec_69_);
return v___x_73_;
}
v___jp_74_:
{
lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v_r_79_; 
v___x_77_ = lean_string_append(v___y_75_, v___y_76_);
v___x_78_ = ((lean_object*)(l_Lean_instReprData___lam__0___closed__0));
v_r_79_ = lean_string_append(v___x_77_, v___x_78_);
v_r_71_ = v_r_79_;
goto v___jp_70_;
}
v___jp_80_:
{
uint8_t v___x_82_; 
v___x_82_ = l_Lean_Level_Data_hasParam(v_v_68_);
if (v___x_82_ == 0)
{
v_r_71_ = v_r_81_;
goto v___jp_70_;
}
else
{
lean_object* v___x_83_; lean_object* v___x_84_; 
v___x_83_ = ((lean_object*)(l_Lean_instReprData___lam__0___closed__1));
v___x_84_ = lean_string_append(v_r_81_, v___x_83_);
if (v___x_82_ == 0)
{
lean_object* v___x_85_; 
v___x_85_ = ((lean_object*)(l_Lean_instReprData___lam__0___closed__2));
v___y_75_ = v___x_84_;
v___y_76_ = v___x_85_;
goto v___jp_74_;
}
else
{
lean_object* v___x_86_; 
v___x_86_ = ((lean_object*)(l_Lean_instReprData___lam__0___closed__3));
v___y_75_ = v___x_84_;
v___y_76_ = v___x_86_;
goto v___jp_74_;
}
}
}
v___jp_87_:
{
lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v_r_92_; 
v___x_90_ = lean_string_append(v___y_88_, v___y_89_);
v___x_91_ = ((lean_object*)(l_Lean_instReprData___lam__0___closed__0));
v_r_92_ = lean_string_append(v___x_90_, v___x_91_);
v_r_81_ = v_r_92_;
goto v___jp_80_;
}
v___jp_93_:
{
uint8_t v___x_95_; 
v___x_95_ = l_Lean_Level_Data_hasMVar(v_v_68_);
if (v___x_95_ == 0)
{
v_r_81_ = v_r_94_;
goto v___jp_80_;
}
else
{
lean_object* v___x_96_; lean_object* v___x_97_; 
v___x_96_ = ((lean_object*)(l_Lean_instReprData___lam__0___closed__4));
v___x_97_ = lean_string_append(v_r_94_, v___x_96_);
if (v___x_95_ == 0)
{
lean_object* v___x_98_; 
v___x_98_ = ((lean_object*)(l_Lean_instReprData___lam__0___closed__2));
v___y_88_ = v___x_97_;
v___y_89_ = v___x_98_;
goto v___jp_87_;
}
else
{
lean_object* v___x_99_; 
v___x_99_ = ((lean_object*)(l_Lean_instReprData___lam__0___closed__3));
v___y_88_ = v___x_97_;
v___y_89_ = v___x_99_;
goto v___jp_87_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instReprData___lam__0___boxed(lean_object* v_v_115_, lean_object* v_prec_116_){
_start:
{
uint64_t v_v_boxed_117_; lean_object* v_res_118_; 
v_v_boxed_117_ = lean_unbox_uint64(v_v_115_);
lean_dec_ref(v_v_115_);
v_res_118_ = l_Lean_instReprData___lam__0(v_v_boxed_117_, v_prec_116_);
lean_dec(v_prec_116_);
return v_res_118_;
}
}
static lean_object* _init_l_Lean_instInhabitedLevelMVarId_default(void){
_start:
{
lean_object* v___x_121_; 
v___x_121_ = lean_box(0);
return v___x_121_;
}
}
static lean_object* _init_l_Lean_instInhabitedLevelMVarId(void){
_start:
{
lean_object* v___x_122_; 
v___x_122_ = lean_box(0);
return v___x_122_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqLevelMVarId_beq(lean_object* v_x_123_, lean_object* v_x_124_){
_start:
{
uint8_t v___x_125_; 
v___x_125_ = lean_name_eq(v_x_123_, v_x_124_);
return v___x_125_;
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqLevelMVarId_beq___boxed(lean_object* v_x_126_, lean_object* v_x_127_){
_start:
{
uint8_t v_res_128_; lean_object* v_r_129_; 
v_res_128_ = l_Lean_instBEqLevelMVarId_beq(v_x_126_, v_x_127_);
lean_dec(v_x_127_);
lean_dec(v_x_126_);
v_r_129_ = lean_box(v_res_128_);
return v_r_129_;
}
}
static uint64_t _init_l_Lean_instHashableLevelMVarId_hash___closed__0(void){
_start:
{
uint64_t v___x_132_; uint64_t v___x_133_; uint64_t v___x_134_; 
v___x_132_ = 1723ULL;
v___x_133_ = 0ULL;
v___x_134_ = lean_uint64_mix_hash(v___x_133_, v___x_132_);
return v___x_134_;
}
}
LEAN_EXPORT uint64_t l_Lean_instHashableLevelMVarId_hash(lean_object* v_x_135_){
_start:
{
uint64_t v___x_136_; 
v___x_136_ = 0ULL;
if (lean_obj_tag(v_x_135_) == 0)
{
uint64_t v___x_137_; 
v___x_137_ = lean_uint64_once(&l_Lean_instHashableLevelMVarId_hash___closed__0, &l_Lean_instHashableLevelMVarId_hash___closed__0_once, _init_l_Lean_instHashableLevelMVarId_hash___closed__0);
return v___x_137_;
}
else
{
uint64_t v_hash_138_; uint64_t v___x_139_; 
v_hash_138_ = lean_ctor_get_uint64(v_x_135_, sizeof(void*)*2);
v___x_139_ = lean_uint64_mix_hash(v___x_136_, v_hash_138_);
return v___x_139_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instHashableLevelMVarId_hash___boxed(lean_object* v_x_140_){
_start:
{
uint64_t v_res_141_; lean_object* v_r_142_; 
v_res_141_ = l_Lean_instHashableLevelMVarId_hash(v_x_140_);
lean_dec(v_x_140_);
v_r_142_ = lean_box_uint64(v_res_141_);
return v_r_142_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_instReprLevelMVarId_repr_spec__0(lean_object* v_a_145_){
_start:
{
lean_object* v___x_146_; 
v___x_146_ = lean_nat_to_int(v_a_145_);
return v___x_146_;
}
}
static lean_object* _init_l_Lean_instReprLevelMVarId_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_160_; lean_object* v___x_161_; 
v___x_160_ = lean_unsigned_to_nat(8u);
v___x_161_ = lean_nat_to_int(v___x_160_);
return v___x_161_;
}
}
static lean_object* _init_l_Lean_instReprLevelMVarId_repr___redArg___closed__9(void){
_start:
{
lean_object* v___x_163_; lean_object* v___x_164_; 
v___x_163_ = ((lean_object*)(l_Lean_instReprLevelMVarId_repr___redArg___closed__0));
v___x_164_ = lean_string_length(v___x_163_);
return v___x_164_;
}
}
static lean_object* _init_l_Lean_instReprLevelMVarId_repr___redArg___closed__10(void){
_start:
{
lean_object* v___x_165_; lean_object* v___x_166_; 
v___x_165_ = lean_obj_once(&l_Lean_instReprLevelMVarId_repr___redArg___closed__9, &l_Lean_instReprLevelMVarId_repr___redArg___closed__9_once, _init_l_Lean_instReprLevelMVarId_repr___redArg___closed__9);
v___x_166_ = lean_nat_to_int(v___x_165_);
return v___x_166_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprLevelMVarId_repr___redArg(lean_object* v_x_171_){
_start:
{
lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; uint8_t v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; 
v___x_172_ = ((lean_object*)(l_Lean_instReprLevelMVarId_repr___redArg___closed__6));
v___x_173_ = lean_obj_once(&l_Lean_instReprLevelMVarId_repr___redArg___closed__7, &l_Lean_instReprLevelMVarId_repr___redArg___closed__7_once, _init_l_Lean_instReprLevelMVarId_repr___redArg___closed__7);
v___x_174_ = lean_unsigned_to_nat(0u);
v___x_175_ = l_Lean_Name_reprPrec(v_x_171_, v___x_174_);
v___x_176_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_176_, 0, v___x_173_);
lean_ctor_set(v___x_176_, 1, v___x_175_);
v___x_177_ = 0;
v___x_178_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_178_, 0, v___x_176_);
lean_ctor_set_uint8(v___x_178_, sizeof(void*)*1, v___x_177_);
v___x_179_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_179_, 0, v___x_172_);
lean_ctor_set(v___x_179_, 1, v___x_178_);
v___x_180_ = lean_obj_once(&l_Lean_instReprLevelMVarId_repr___redArg___closed__10, &l_Lean_instReprLevelMVarId_repr___redArg___closed__10_once, _init_l_Lean_instReprLevelMVarId_repr___redArg___closed__10);
v___x_181_ = ((lean_object*)(l_Lean_instReprLevelMVarId_repr___redArg___closed__11));
v___x_182_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_182_, 0, v___x_181_);
lean_ctor_set(v___x_182_, 1, v___x_179_);
v___x_183_ = ((lean_object*)(l_Lean_instReprLevelMVarId_repr___redArg___closed__12));
v___x_184_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_184_, 0, v___x_182_);
lean_ctor_set(v___x_184_, 1, v___x_183_);
v___x_185_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_185_, 0, v___x_180_);
lean_ctor_set(v___x_185_, 1, v___x_184_);
v___x_186_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_186_, 0, v___x_185_);
lean_ctor_set_uint8(v___x_186_, sizeof(void*)*1, v___x_177_);
return v___x_186_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprLevelMVarId_repr(lean_object* v_x_187_, lean_object* v_prec_188_){
_start:
{
lean_object* v___x_189_; 
v___x_189_ = l_Lean_instReprLevelMVarId_repr___redArg(v_x_187_);
return v___x_189_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprLevelMVarId_repr___boxed(lean_object* v_x_190_, lean_object* v_prec_191_){
_start:
{
lean_object* v_res_192_; 
v_res_192_ = l_Lean_instReprLevelMVarId_repr(v_x_190_, v_prec_191_);
lean_dec(v_prec_191_);
return v_res_192_;
}
}
static lean_object* _init_l_Lean_instInhabitedLMVarIdSet___aux__1(void){
_start:
{
lean_object* v___x_197_; 
v___x_197_ = lean_box(1);
return v___x_197_;
}
}
static lean_object* _init_l_Lean_instInhabitedLMVarIdSet(void){
_start:
{
lean_object* v___x_198_; 
v___x_198_ = lean_box(1);
return v___x_198_;
}
}
static lean_object* _init_l_Lean_instEmptyCollectionLMVarIdSet___aux__1(void){
_start:
{
lean_object* v___x_199_; 
v___x_199_ = lean_box(1);
return v___x_199_;
}
}
static lean_object* _init_l_Lean_instEmptyCollectionLMVarIdSet(void){
_start:
{
lean_object* v___x_200_; 
v___x_200_ = lean_box(1);
return v___x_200_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInLMVarIdSetLMVarIdOfMonad___aux__1___redArg___lam__0(lean_object* v_f_201_, lean_object* v_a_202_, lean_object* v_b_203_, lean_object* v_c_204_){
_start:
{
lean_object* v___x_205_; 
v___x_205_ = lean_apply_2(v_f_201_, v_a_202_, v_c_204_);
return v___x_205_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInLMVarIdSetLMVarIdOfMonad___aux__1___redArg___lam__1(lean_object* v_toPure_206_, lean_object* v_____do__lift_207_){
_start:
{
lean_object* v_a_208_; lean_object* v___x_209_; 
v_a_208_ = lean_ctor_get(v_____do__lift_207_, 0);
lean_inc(v_a_208_);
lean_dec_ref(v_____do__lift_207_);
v___x_209_ = lean_apply_2(v_toPure_206_, lean_box(0), v_a_208_);
return v___x_209_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInLMVarIdSetLMVarIdOfMonad___aux__1___redArg(lean_object* v_inst_210_, lean_object* v_m_211_, lean_object* v_init_212_, lean_object* v_f_213_){
_start:
{
lean_object* v_toApplicative_214_; lean_object* v_toBind_215_; lean_object* v_toPure_216_; lean_object* v___f_217_; lean_object* v___x_218_; lean_object* v___f_219_; lean_object* v___x_220_; 
v_toApplicative_214_ = lean_ctor_get(v_inst_210_, 0);
v_toBind_215_ = lean_ctor_get(v_inst_210_, 1);
lean_inc(v_toBind_215_);
v_toPure_216_ = lean_ctor_get(v_toApplicative_214_, 1);
lean_inc(v_toPure_216_);
v___f_217_ = lean_alloc_closure((void*)(l_Lean_instForInLMVarIdSetLMVarIdOfMonad___aux__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_217_, 0, v_f_213_);
v___x_218_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_210_, v___f_217_, v_init_212_, v_m_211_);
v___f_219_ = lean_alloc_closure((void*)(l_Lean_instForInLMVarIdSetLMVarIdOfMonad___aux__1___redArg___lam__1), 2, 1);
lean_closure_set(v___f_219_, 0, v_toPure_216_);
v___x_220_ = lean_apply_4(v_toBind_215_, lean_box(0), lean_box(0), v___x_218_, v___f_219_);
return v___x_220_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInLMVarIdSetLMVarIdOfMonad___aux__1(lean_object* v_m_221_, lean_object* v_inst_222_, lean_object* v_00_u03b2_223_, lean_object* v_m_224_, lean_object* v_init_225_, lean_object* v_f_226_){
_start:
{
lean_object* v_toApplicative_227_; lean_object* v_toBind_228_; lean_object* v_toPure_229_; lean_object* v___f_230_; lean_object* v___x_231_; lean_object* v___f_232_; lean_object* v___x_233_; 
v_toApplicative_227_ = lean_ctor_get(v_inst_222_, 0);
v_toBind_228_ = lean_ctor_get(v_inst_222_, 1);
lean_inc(v_toBind_228_);
v_toPure_229_ = lean_ctor_get(v_toApplicative_227_, 1);
lean_inc(v_toPure_229_);
v___f_230_ = lean_alloc_closure((void*)(l_Lean_instForInLMVarIdSetLMVarIdOfMonad___aux__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_230_, 0, v_f_226_);
v___x_231_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_222_, v___f_230_, v_init_225_, v_m_224_);
v___f_232_ = lean_alloc_closure((void*)(l_Lean_instForInLMVarIdSetLMVarIdOfMonad___aux__1___redArg___lam__1), 2, 1);
lean_closure_set(v___f_232_, 0, v_toPure_229_);
v___x_233_ = lean_apply_4(v_toBind_228_, lean_box(0), lean_box(0), v___x_231_, v___f_232_);
return v___x_233_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInLMVarIdSetLMVarIdOfMonad___redArg(lean_object* v_inst_234_){
_start:
{
lean_object* v___x_235_; 
v___x_235_ = lean_alloc_closure((void*)(l_Lean_instForInLMVarIdSetLMVarIdOfMonad___aux__1), 6, 2);
lean_closure_set(v___x_235_, 0, lean_box(0));
lean_closure_set(v___x_235_, 1, v_inst_234_);
return v___x_235_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInLMVarIdSetLMVarIdOfMonad(lean_object* v_m_236_, lean_object* v_inst_237_){
_start:
{
lean_object* v___x_238_; 
v___x_238_ = lean_alloc_closure((void*)(l_Lean_instForInLMVarIdSetLMVarIdOfMonad___aux__1), 6, 2);
lean_closure_set(v___x_238_, 0, lean_box(0));
lean_closure_set(v___x_238_, 1, v_inst_237_);
return v___x_238_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionLMVarIdMap___aux__1(lean_object* v_00_u03b1_239_){
_start:
{
lean_object* v___x_240_; 
v___x_240_ = lean_box(1);
return v___x_240_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionLMVarIdMap(lean_object* v_00_u03b1_241_){
_start:
{
lean_object* v___x_242_; 
v___x_242_ = lean_box(1);
return v___x_242_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInLMVarIdMapProdLMVarIdOfMonad___aux__1___redArg___lam__0(lean_object* v_f_243_, lean_object* v_a_244_, lean_object* v_b_245_, lean_object* v_c_246_){
_start:
{
lean_object* v___x_247_; lean_object* v___x_248_; 
v___x_247_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_247_, 0, v_a_244_);
lean_ctor_set(v___x_247_, 1, v_b_245_);
v___x_248_ = lean_apply_2(v_f_243_, v___x_247_, v_c_246_);
return v___x_248_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInLMVarIdMapProdLMVarIdOfMonad___aux__1___redArg(lean_object* v_inst_249_, lean_object* v_m_250_, lean_object* v_init_251_, lean_object* v_f_252_){
_start:
{
lean_object* v_toApplicative_253_; lean_object* v_toBind_254_; lean_object* v_toPure_255_; lean_object* v___f_256_; lean_object* v___x_257_; lean_object* v___f_258_; lean_object* v___x_259_; 
v_toApplicative_253_ = lean_ctor_get(v_inst_249_, 0);
v_toBind_254_ = lean_ctor_get(v_inst_249_, 1);
lean_inc(v_toBind_254_);
v_toPure_255_ = lean_ctor_get(v_toApplicative_253_, 1);
lean_inc(v_toPure_255_);
v___f_256_ = lean_alloc_closure((void*)(l_Lean_instForInLMVarIdMapProdLMVarIdOfMonad___aux__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_256_, 0, v_f_252_);
v___x_257_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_249_, v___f_256_, v_init_251_, v_m_250_);
v___f_258_ = lean_alloc_closure((void*)(l_Lean_instForInLMVarIdSetLMVarIdOfMonad___aux__1___redArg___lam__1), 2, 1);
lean_closure_set(v___f_258_, 0, v_toPure_255_);
v___x_259_ = lean_apply_4(v_toBind_254_, lean_box(0), lean_box(0), v___x_257_, v___f_258_);
return v___x_259_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInLMVarIdMapProdLMVarIdOfMonad___aux__1(lean_object* v_m_260_, lean_object* v_00_u03b1_261_, lean_object* v_inst_262_, lean_object* v_00_u03b2_263_, lean_object* v_m_264_, lean_object* v_init_265_, lean_object* v_f_266_){
_start:
{
lean_object* v_toApplicative_267_; lean_object* v_toBind_268_; lean_object* v_toPure_269_; lean_object* v___f_270_; lean_object* v___x_271_; lean_object* v___f_272_; lean_object* v___x_273_; 
v_toApplicative_267_ = lean_ctor_get(v_inst_262_, 0);
v_toBind_268_ = lean_ctor_get(v_inst_262_, 1);
lean_inc(v_toBind_268_);
v_toPure_269_ = lean_ctor_get(v_toApplicative_267_, 1);
lean_inc(v_toPure_269_);
v___f_270_ = lean_alloc_closure((void*)(l_Lean_instForInLMVarIdMapProdLMVarIdOfMonad___aux__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_270_, 0, v_f_266_);
v___x_271_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_262_, v___f_270_, v_init_265_, v_m_264_);
v___f_272_ = lean_alloc_closure((void*)(l_Lean_instForInLMVarIdSetLMVarIdOfMonad___aux__1___redArg___lam__1), 2, 1);
lean_closure_set(v___f_272_, 0, v_toPure_269_);
v___x_273_ = lean_apply_4(v_toBind_268_, lean_box(0), lean_box(0), v___x_271_, v___f_272_);
return v___x_273_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInLMVarIdMapProdLMVarIdOfMonad___redArg(lean_object* v_inst_274_){
_start:
{
lean_object* v___x_275_; 
v___x_275_ = lean_alloc_closure((void*)(l_Lean_instForInLMVarIdMapProdLMVarIdOfMonad___aux__1), 7, 3);
lean_closure_set(v___x_275_, 0, lean_box(0));
lean_closure_set(v___x_275_, 1, lean_box(0));
lean_closure_set(v___x_275_, 2, v_inst_274_);
return v___x_275_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInLMVarIdMapProdLMVarIdOfMonad(lean_object* v_m_276_, lean_object* v_00_u03b1_277_, lean_object* v_inst_278_){
_start:
{
lean_object* v___x_279_; 
v___x_279_ = lean_alloc_closure((void*)(l_Lean_instForInLMVarIdMapProdLMVarIdOfMonad___aux__1), 7, 3);
lean_closure_set(v___x_279_, 0, lean_box(0));
lean_closure_set(v___x_279_, 1, lean_box(0));
lean_closure_set(v___x_279_, 2, v_inst_278_);
return v___x_279_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedLMVarIdMap(lean_object* v_00_u03b1_280_){
_start:
{
lean_object* v___x_281_; 
v___x_281_ = lean_box(1);
return v___x_281_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_ctorIdx(lean_object* v_x_282_){
_start:
{
switch(lean_obj_tag(v_x_282_))
{
case 0:
{
lean_object* v___x_283_; 
v___x_283_ = lean_unsigned_to_nat(0u);
return v___x_283_;
}
case 1:
{
lean_object* v___x_284_; 
v___x_284_ = lean_unsigned_to_nat(1u);
return v___x_284_;
}
case 2:
{
lean_object* v___x_285_; 
v___x_285_ = lean_unsigned_to_nat(2u);
return v___x_285_;
}
case 3:
{
lean_object* v___x_286_; 
v___x_286_ = lean_unsigned_to_nat(3u);
return v___x_286_;
}
case 4:
{
lean_object* v___x_287_; 
v___x_287_ = lean_unsigned_to_nat(4u);
return v___x_287_;
}
default: 
{
lean_object* v___x_288_; 
v___x_288_ = lean_unsigned_to_nat(5u);
return v___x_288_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_ctorIdx___boxed(lean_object* v_x_289_){
_start:
{
lean_object* v_res_290_; 
v_res_290_ = l_Lean_Level_ctorIdx(v_x_289_);
lean_dec(v_x_289_);
return v_res_290_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_ctorElim___redArg(lean_object* v_t_291_, lean_object* v_k_292_){
_start:
{
switch(lean_obj_tag(v_t_291_))
{
case 0:
{
return v_k_292_;
}
case 2:
{
lean_object* v_a_293_; lean_object* v_a_294_; lean_object* v___x_295_; 
v_a_293_ = lean_ctor_get(v_t_291_, 0);
lean_inc(v_a_293_);
v_a_294_ = lean_ctor_get(v_t_291_, 1);
lean_inc(v_a_294_);
lean_dec_ref_known(v_t_291_, 2);
v___x_295_ = lean_apply_2(v_k_292_, v_a_293_, v_a_294_);
return v___x_295_;
}
case 3:
{
lean_object* v_a_296_; lean_object* v_a_297_; lean_object* v___x_298_; 
v_a_296_ = lean_ctor_get(v_t_291_, 0);
lean_inc(v_a_296_);
v_a_297_ = lean_ctor_get(v_t_291_, 1);
lean_inc(v_a_297_);
lean_dec_ref_known(v_t_291_, 2);
v___x_298_ = lean_apply_2(v_k_292_, v_a_296_, v_a_297_);
return v___x_298_;
}
default: 
{
lean_object* v_a_299_; lean_object* v___x_300_; 
v_a_299_ = lean_ctor_get(v_t_291_, 0);
lean_inc(v_a_299_);
lean_dec(v_t_291_);
v___x_300_ = lean_apply_1(v_k_292_, v_a_299_);
return v___x_300_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_ctorElim(lean_object* v_motive_301_, lean_object* v_ctorIdx_302_, lean_object* v_t_303_, lean_object* v_h_304_, lean_object* v_k_305_){
_start:
{
lean_object* v___x_306_; 
v___x_306_ = l_Lean_Level_ctorElim___redArg(v_t_303_, v_k_305_);
return v___x_306_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_ctorElim___boxed(lean_object* v_motive_307_, lean_object* v_ctorIdx_308_, lean_object* v_t_309_, lean_object* v_h_310_, lean_object* v_k_311_){
_start:
{
lean_object* v_res_312_; 
v_res_312_ = l_Lean_Level_ctorElim(v_motive_307_, v_ctorIdx_308_, v_t_309_, v_h_310_, v_k_311_);
lean_dec(v_ctorIdx_308_);
return v_res_312_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_zero_elim___redArg(lean_object* v_t_313_, lean_object* v_zero_314_){
_start:
{
lean_object* v___x_315_; 
v___x_315_ = l_Lean_Level_ctorElim___redArg(v_t_313_, v_zero_314_);
return v___x_315_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_zero_elim(lean_object* v_motive_316_, lean_object* v_t_317_, lean_object* v_h_318_, lean_object* v_zero_319_){
_start:
{
lean_object* v___x_320_; 
v___x_320_ = l_Lean_Level_ctorElim___redArg(v_t_317_, v_zero_319_);
return v___x_320_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_succ_elim___redArg(lean_object* v_t_321_, lean_object* v_succ_322_){
_start:
{
lean_object* v___x_323_; 
v___x_323_ = l_Lean_Level_ctorElim___redArg(v_t_321_, v_succ_322_);
return v___x_323_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_succ_elim(lean_object* v_motive_324_, lean_object* v_t_325_, lean_object* v_h_326_, lean_object* v_succ_327_){
_start:
{
lean_object* v___x_328_; 
v___x_328_ = l_Lean_Level_ctorElim___redArg(v_t_325_, v_succ_327_);
return v___x_328_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_max_elim___redArg(lean_object* v_t_329_, lean_object* v_max_330_){
_start:
{
lean_object* v___x_331_; 
v___x_331_ = l_Lean_Level_ctorElim___redArg(v_t_329_, v_max_330_);
return v___x_331_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_max_elim(lean_object* v_motive_332_, lean_object* v_t_333_, lean_object* v_h_334_, lean_object* v_max_335_){
_start:
{
lean_object* v___x_336_; 
v___x_336_ = l_Lean_Level_ctorElim___redArg(v_t_333_, v_max_335_);
return v___x_336_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_imax_elim___redArg(lean_object* v_t_337_, lean_object* v_imax_338_){
_start:
{
lean_object* v___x_339_; 
v___x_339_ = l_Lean_Level_ctorElim___redArg(v_t_337_, v_imax_338_);
return v___x_339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_imax_elim(lean_object* v_motive_340_, lean_object* v_t_341_, lean_object* v_h_342_, lean_object* v_imax_343_){
_start:
{
lean_object* v___x_344_; 
v___x_344_ = l_Lean_Level_ctorElim___redArg(v_t_341_, v_imax_343_);
return v___x_344_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_param_elim___redArg(lean_object* v_t_345_, lean_object* v_param_346_){
_start:
{
lean_object* v___x_347_; 
v___x_347_ = l_Lean_Level_ctorElim___redArg(v_t_345_, v_param_346_);
return v___x_347_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_param_elim(lean_object* v_motive_348_, lean_object* v_t_349_, lean_object* v_h_350_, lean_object* v_param_351_){
_start:
{
lean_object* v___x_352_; 
v___x_352_ = l_Lean_Level_ctorElim___redArg(v_t_349_, v_param_351_);
return v___x_352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_mvar_elim___redArg(lean_object* v_t_353_, lean_object* v_mvar_354_){
_start:
{
lean_object* v___x_355_; 
v___x_355_ = l_Lean_Level_ctorElim___redArg(v_t_353_, v_mvar_354_);
return v___x_355_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_mvar_elim(lean_object* v_motive_356_, lean_object* v_t_357_, lean_object* v_h_358_, lean_object* v_mvar_359_){
_start:
{
lean_object* v___x_360_; 
v___x_360_ = l_Lean_Level_ctorElim___redArg(v_t_357_, v_mvar_359_);
return v___x_360_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_casesOn___override___redArg(lean_object* v_t_361_, lean_object* v_zero_362_, lean_object* v_succ_363_, lean_object* v_max_364_, lean_object* v_imax_365_, lean_object* v_param_366_, lean_object* v_mvar_367_){
_start:
{
switch(lean_obj_tag(v_t_361_))
{
case 0:
{
lean_dec(v_mvar_367_);
lean_dec(v_param_366_);
lean_dec(v_imax_365_);
lean_dec(v_max_364_);
lean_dec(v_succ_363_);
lean_inc(v_zero_362_);
return v_zero_362_;
}
case 1:
{
lean_object* v_a_368_; lean_object* v___x_369_; 
lean_dec(v_mvar_367_);
lean_dec(v_param_366_);
lean_dec(v_imax_365_);
lean_dec(v_max_364_);
v_a_368_ = lean_ctor_get(v_t_361_, 0);
lean_inc(v_a_368_);
lean_dec_ref_known(v_t_361_, 1);
v___x_369_ = lean_apply_1(v_succ_363_, v_a_368_);
return v___x_369_;
}
case 2:
{
lean_object* v_a_370_; lean_object* v_a_371_; lean_object* v___x_372_; 
lean_dec(v_mvar_367_);
lean_dec(v_param_366_);
lean_dec(v_imax_365_);
lean_dec(v_succ_363_);
v_a_370_ = lean_ctor_get(v_t_361_, 0);
lean_inc(v_a_370_);
v_a_371_ = lean_ctor_get(v_t_361_, 1);
lean_inc(v_a_371_);
lean_dec_ref_known(v_t_361_, 2);
v___x_372_ = lean_apply_2(v_max_364_, v_a_370_, v_a_371_);
return v___x_372_;
}
case 3:
{
lean_object* v_a_373_; lean_object* v_a_374_; lean_object* v___x_375_; 
lean_dec(v_mvar_367_);
lean_dec(v_param_366_);
lean_dec(v_max_364_);
lean_dec(v_succ_363_);
v_a_373_ = lean_ctor_get(v_t_361_, 0);
lean_inc(v_a_373_);
v_a_374_ = lean_ctor_get(v_t_361_, 1);
lean_inc(v_a_374_);
lean_dec_ref_known(v_t_361_, 2);
v___x_375_ = lean_apply_2(v_imax_365_, v_a_373_, v_a_374_);
return v___x_375_;
}
case 4:
{
lean_object* v_a_376_; lean_object* v___x_377_; 
lean_dec(v_mvar_367_);
lean_dec(v_imax_365_);
lean_dec(v_max_364_);
lean_dec(v_succ_363_);
v_a_376_ = lean_ctor_get(v_t_361_, 0);
lean_inc(v_a_376_);
lean_dec_ref_known(v_t_361_, 1);
v___x_377_ = lean_apply_1(v_param_366_, v_a_376_);
return v___x_377_;
}
default: 
{
lean_object* v_a_378_; lean_object* v___x_379_; 
lean_dec(v_param_366_);
lean_dec(v_imax_365_);
lean_dec(v_max_364_);
lean_dec(v_succ_363_);
v_a_378_ = lean_ctor_get(v_t_361_, 0);
lean_inc(v_a_378_);
lean_dec_ref_known(v_t_361_, 1);
v___x_379_ = lean_apply_1(v_mvar_367_, v_a_378_);
return v___x_379_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_casesOn___override___redArg___boxed(lean_object* v_t_380_, lean_object* v_zero_381_, lean_object* v_succ_382_, lean_object* v_max_383_, lean_object* v_imax_384_, lean_object* v_param_385_, lean_object* v_mvar_386_){
_start:
{
lean_object* v_res_387_; 
v_res_387_ = l_Lean_Level_casesOn___override___redArg(v_t_380_, v_zero_381_, v_succ_382_, v_max_383_, v_imax_384_, v_param_385_, v_mvar_386_);
lean_dec(v_zero_381_);
return v_res_387_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_casesOn___override(lean_object* v_motive_388_, lean_object* v_t_389_, lean_object* v_zero_390_, lean_object* v_succ_391_, lean_object* v_max_392_, lean_object* v_imax_393_, lean_object* v_param_394_, lean_object* v_mvar_395_){
_start:
{
switch(lean_obj_tag(v_t_389_))
{
case 0:
{
lean_dec(v_mvar_395_);
lean_dec(v_param_394_);
lean_dec(v_imax_393_);
lean_dec(v_max_392_);
lean_dec(v_succ_391_);
lean_inc(v_zero_390_);
return v_zero_390_;
}
case 1:
{
lean_object* v_a_396_; lean_object* v___x_397_; 
lean_dec(v_mvar_395_);
lean_dec(v_param_394_);
lean_dec(v_imax_393_);
lean_dec(v_max_392_);
v_a_396_ = lean_ctor_get(v_t_389_, 0);
lean_inc(v_a_396_);
lean_dec_ref_known(v_t_389_, 1);
v___x_397_ = lean_apply_1(v_succ_391_, v_a_396_);
return v___x_397_;
}
case 2:
{
lean_object* v_a_398_; lean_object* v_a_399_; lean_object* v___x_400_; 
lean_dec(v_mvar_395_);
lean_dec(v_param_394_);
lean_dec(v_imax_393_);
lean_dec(v_succ_391_);
v_a_398_ = lean_ctor_get(v_t_389_, 0);
lean_inc(v_a_398_);
v_a_399_ = lean_ctor_get(v_t_389_, 1);
lean_inc(v_a_399_);
lean_dec_ref_known(v_t_389_, 2);
v___x_400_ = lean_apply_2(v_max_392_, v_a_398_, v_a_399_);
return v___x_400_;
}
case 3:
{
lean_object* v_a_401_; lean_object* v_a_402_; lean_object* v___x_403_; 
lean_dec(v_mvar_395_);
lean_dec(v_param_394_);
lean_dec(v_max_392_);
lean_dec(v_succ_391_);
v_a_401_ = lean_ctor_get(v_t_389_, 0);
lean_inc(v_a_401_);
v_a_402_ = lean_ctor_get(v_t_389_, 1);
lean_inc(v_a_402_);
lean_dec_ref_known(v_t_389_, 2);
v___x_403_ = lean_apply_2(v_imax_393_, v_a_401_, v_a_402_);
return v___x_403_;
}
case 4:
{
lean_object* v_a_404_; lean_object* v___x_405_; 
lean_dec(v_mvar_395_);
lean_dec(v_imax_393_);
lean_dec(v_max_392_);
lean_dec(v_succ_391_);
v_a_404_ = lean_ctor_get(v_t_389_, 0);
lean_inc(v_a_404_);
lean_dec_ref_known(v_t_389_, 1);
v___x_405_ = lean_apply_1(v_param_394_, v_a_404_);
return v___x_405_;
}
default: 
{
lean_object* v_a_406_; lean_object* v___x_407_; 
lean_dec(v_param_394_);
lean_dec(v_imax_393_);
lean_dec(v_max_392_);
lean_dec(v_succ_391_);
v_a_406_ = lean_ctor_get(v_t_389_, 0);
lean_inc(v_a_406_);
lean_dec_ref_known(v_t_389_, 1);
v___x_407_ = lean_apply_1(v_mvar_395_, v_a_406_);
return v___x_407_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_casesOn___override___boxed(lean_object* v_motive_408_, lean_object* v_t_409_, lean_object* v_zero_410_, lean_object* v_succ_411_, lean_object* v_max_412_, lean_object* v_imax_413_, lean_object* v_param_414_, lean_object* v_mvar_415_){
_start:
{
lean_object* v_res_416_; 
v_res_416_ = l_Lean_Level_casesOn___override(v_motive_408_, v_t_409_, v_zero_410_, v_succ_411_, v_max_412_, v_imax_413_, v_param_414_, v_mvar_415_);
lean_dec(v_zero_410_);
return v_res_416_;
}
}
static lean_object* _init_l_Lean_Level_zero___override(void){
_start:
{
lean_object* v___x_417_; 
v___x_417_ = lean_box(0);
return v___x_417_;
}
}
static uint64_t _init_l_Lean_Level_data___override___closed__0(void){
_start:
{
uint8_t v___x_418_; lean_object* v___x_419_; uint64_t v___x_420_; uint64_t v___x_421_; 
v___x_418_ = 0;
v___x_419_ = lean_unsigned_to_nat(0u);
v___x_420_ = 2221ULL;
v___x_421_ = lean_level_mk_data(v___x_420_, v___x_419_, v___x_418_, v___x_418_);
return v___x_421_;
}
}
LEAN_EXPORT uint64_t l_Lean_Level_data___override(lean_object* v_x_422_){
_start:
{
switch(lean_obj_tag(v_x_422_))
{
case 0:
{
uint64_t v___x_423_; 
v___x_423_ = lean_uint64_once(&l_Lean_Level_data___override___closed__0, &l_Lean_Level_data___override___closed__0_once, _init_l_Lean_Level_data___override___closed__0);
return v___x_423_;
}
case 2:
{
uint64_t v_data_424_; 
v_data_424_ = lean_ctor_get_uint64(v_x_422_, sizeof(void*)*2);
return v_data_424_;
}
case 3:
{
uint64_t v_data_425_; 
v_data_425_ = lean_ctor_get_uint64(v_x_422_, sizeof(void*)*2);
return v_data_425_;
}
default: 
{
uint64_t v_data_426_; 
v_data_426_ = lean_ctor_get_uint64(v_x_422_, sizeof(void*)*1);
return v_data_426_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_data___override___boxed(lean_object* v_x_427_){
_start:
{
uint64_t v_res_428_; lean_object* v_r_429_; 
v_res_428_ = l_Lean_Level_data___override(v_x_427_);
lean_dec(v_x_427_);
v_r_429_ = lean_box_uint64(v_res_428_);
return v_r_429_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_succ___override(lean_object* v_a_430_){
_start:
{
uint64_t v___x_431_; uint64_t v___x_432_; uint64_t v___x_433_; uint64_t v___x_434_; uint32_t v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; uint8_t v___x_439_; uint8_t v___x_440_; uint64_t v___x_441_; lean_object* v___x_442_; 
v___x_431_ = 2243ULL;
v___x_432_ = l_Lean_Level_data___override(v_a_430_);
v___x_433_ = l_Lean_Level_Data_hash(v___x_432_);
v___x_434_ = lean_uint64_mix_hash(v___x_431_, v___x_433_);
v___x_435_ = l_Lean_Level_Data_depth(v___x_432_);
v___x_436_ = lean_uint32_to_nat(v___x_435_);
v___x_437_ = lean_unsigned_to_nat(1u);
v___x_438_ = lean_nat_add(v___x_436_, v___x_437_);
lean_dec(v___x_436_);
v___x_439_ = l_Lean_Level_Data_hasMVar(v___x_432_);
v___x_440_ = l_Lean_Level_Data_hasParam(v___x_432_);
v___x_441_ = lean_level_mk_data(v___x_434_, v___x_438_, v___x_439_, v___x_440_);
v___x_442_ = lean_alloc_ctor(1, 1, 8);
lean_ctor_set(v___x_442_, 0, v_a_430_);
lean_ctor_set_uint64(v___x_442_, sizeof(void*)*1, v___x_441_);
return v___x_442_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_max___override(lean_object* v_a_443_, lean_object* v_a_444_){
_start:
{
uint64_t v___x_445_; uint64_t v___x_446_; uint64_t v___x_447_; uint64_t v___x_448_; uint64_t v___x_449_; uint64_t v___x_450_; uint64_t v___x_451_; uint8_t v___y_453_; lean_object* v___y_454_; uint8_t v___y_455_; lean_object* v___y_459_; uint8_t v___y_460_; lean_object* v___y_464_; uint32_t v___x_469_; lean_object* v___x_470_; uint32_t v___x_471_; lean_object* v___x_472_; uint8_t v___x_473_; 
v___x_445_ = 2251ULL;
v___x_446_ = l_Lean_Level_data___override(v_a_443_);
v___x_447_ = l_Lean_Level_Data_hash(v___x_446_);
v___x_448_ = l_Lean_Level_data___override(v_a_444_);
v___x_449_ = l_Lean_Level_Data_hash(v___x_448_);
v___x_450_ = lean_uint64_mix_hash(v___x_447_, v___x_449_);
v___x_451_ = lean_uint64_mix_hash(v___x_445_, v___x_450_);
v___x_469_ = l_Lean_Level_Data_depth(v___x_446_);
v___x_470_ = lean_uint32_to_nat(v___x_469_);
v___x_471_ = l_Lean_Level_Data_depth(v___x_448_);
v___x_472_ = lean_uint32_to_nat(v___x_471_);
v___x_473_ = lean_nat_dec_le(v___x_470_, v___x_472_);
if (v___x_473_ == 0)
{
lean_dec(v___x_472_);
v___y_464_ = v___x_470_;
goto v___jp_463_;
}
else
{
lean_dec(v___x_470_);
v___y_464_ = v___x_472_;
goto v___jp_463_;
}
v___jp_452_:
{
uint64_t v___x_456_; lean_object* v___x_457_; 
v___x_456_ = lean_level_mk_data(v___x_451_, v___y_454_, v___y_453_, v___y_455_);
v___x_457_ = lean_alloc_ctor(2, 2, 8);
lean_ctor_set(v___x_457_, 0, v_a_443_);
lean_ctor_set(v___x_457_, 1, v_a_444_);
lean_ctor_set_uint64(v___x_457_, sizeof(void*)*2, v___x_456_);
return v___x_457_;
}
v___jp_458_:
{
uint8_t v___x_461_; 
v___x_461_ = l_Lean_Level_Data_hasParam(v___x_446_);
if (v___x_461_ == 0)
{
uint8_t v___x_462_; 
v___x_462_ = l_Lean_Level_Data_hasParam(v___x_448_);
v___y_453_ = v___y_460_;
v___y_454_ = v___y_459_;
v___y_455_ = v___x_462_;
goto v___jp_452_;
}
else
{
v___y_453_ = v___y_460_;
v___y_454_ = v___y_459_;
v___y_455_ = v___x_461_;
goto v___jp_452_;
}
}
v___jp_463_:
{
lean_object* v___x_465_; lean_object* v___x_466_; uint8_t v___x_467_; 
v___x_465_ = lean_unsigned_to_nat(1u);
v___x_466_ = lean_nat_add(v___y_464_, v___x_465_);
lean_dec(v___y_464_);
v___x_467_ = l_Lean_Level_Data_hasMVar(v___x_446_);
if (v___x_467_ == 0)
{
uint8_t v___x_468_; 
v___x_468_ = l_Lean_Level_Data_hasMVar(v___x_448_);
v___y_459_ = v___x_466_;
v___y_460_ = v___x_468_;
goto v___jp_458_;
}
else
{
v___y_459_ = v___x_466_;
v___y_460_ = v___x_467_;
goto v___jp_458_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_imax___override(lean_object* v_a_474_, lean_object* v_a_475_){
_start:
{
uint64_t v___x_476_; uint64_t v___x_477_; uint64_t v___x_478_; uint64_t v___x_479_; uint64_t v___x_480_; uint64_t v___x_481_; uint64_t v___x_482_; uint8_t v___y_484_; lean_object* v___y_485_; uint8_t v___y_486_; lean_object* v___y_490_; uint8_t v___y_491_; lean_object* v___y_495_; uint32_t v___x_500_; lean_object* v___x_501_; uint32_t v___x_502_; lean_object* v___x_503_; uint8_t v___x_504_; 
v___x_476_ = 2267ULL;
v___x_477_ = l_Lean_Level_data___override(v_a_474_);
v___x_478_ = l_Lean_Level_Data_hash(v___x_477_);
v___x_479_ = l_Lean_Level_data___override(v_a_475_);
v___x_480_ = l_Lean_Level_Data_hash(v___x_479_);
v___x_481_ = lean_uint64_mix_hash(v___x_478_, v___x_480_);
v___x_482_ = lean_uint64_mix_hash(v___x_476_, v___x_481_);
v___x_500_ = l_Lean_Level_Data_depth(v___x_477_);
v___x_501_ = lean_uint32_to_nat(v___x_500_);
v___x_502_ = l_Lean_Level_Data_depth(v___x_479_);
v___x_503_ = lean_uint32_to_nat(v___x_502_);
v___x_504_ = lean_nat_dec_le(v___x_501_, v___x_503_);
if (v___x_504_ == 0)
{
lean_dec(v___x_503_);
v___y_495_ = v___x_501_;
goto v___jp_494_;
}
else
{
lean_dec(v___x_501_);
v___y_495_ = v___x_503_;
goto v___jp_494_;
}
v___jp_483_:
{
uint64_t v___x_487_; lean_object* v___x_488_; 
v___x_487_ = lean_level_mk_data(v___x_482_, v___y_485_, v___y_484_, v___y_486_);
v___x_488_ = lean_alloc_ctor(3, 2, 8);
lean_ctor_set(v___x_488_, 0, v_a_474_);
lean_ctor_set(v___x_488_, 1, v_a_475_);
lean_ctor_set_uint64(v___x_488_, sizeof(void*)*2, v___x_487_);
return v___x_488_;
}
v___jp_489_:
{
uint8_t v___x_492_; 
v___x_492_ = l_Lean_Level_Data_hasParam(v___x_477_);
if (v___x_492_ == 0)
{
uint8_t v___x_493_; 
v___x_493_ = l_Lean_Level_Data_hasParam(v___x_479_);
v___y_484_ = v___y_491_;
v___y_485_ = v___y_490_;
v___y_486_ = v___x_493_;
goto v___jp_483_;
}
else
{
v___y_484_ = v___y_491_;
v___y_485_ = v___y_490_;
v___y_486_ = v___x_492_;
goto v___jp_483_;
}
}
v___jp_494_:
{
lean_object* v___x_496_; lean_object* v___x_497_; uint8_t v___x_498_; 
v___x_496_ = lean_unsigned_to_nat(1u);
v___x_497_ = lean_nat_add(v___y_495_, v___x_496_);
lean_dec(v___y_495_);
v___x_498_ = l_Lean_Level_Data_hasMVar(v___x_477_);
if (v___x_498_ == 0)
{
uint8_t v___x_499_; 
v___x_499_ = l_Lean_Level_Data_hasMVar(v___x_479_);
v___y_490_ = v___x_497_;
v___y_491_ = v___x_499_;
goto v___jp_489_;
}
else
{
v___y_490_ = v___x_497_;
v___y_491_ = v___x_498_;
goto v___jp_489_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_param___override(lean_object* v_a_505_){
_start:
{
uint64_t v___x_506_; uint64_t v___y_508_; 
v___x_506_ = 2239ULL;
if (lean_obj_tag(v_a_505_) == 0)
{
uint64_t v___x_515_; 
v___x_515_ = 1723ULL;
v___y_508_ = v___x_515_;
goto v___jp_507_;
}
else
{
uint64_t v_hash_516_; 
v_hash_516_ = lean_ctor_get_uint64(v_a_505_, sizeof(void*)*2);
v___y_508_ = v_hash_516_;
goto v___jp_507_;
}
v___jp_507_:
{
uint64_t v___x_509_; lean_object* v___x_510_; uint8_t v___x_511_; uint8_t v___x_512_; uint64_t v___x_513_; lean_object* v___x_514_; 
v___x_509_ = lean_uint64_mix_hash(v___x_506_, v___y_508_);
v___x_510_ = lean_unsigned_to_nat(0u);
v___x_511_ = 0;
v___x_512_ = 1;
v___x_513_ = lean_level_mk_data(v___x_509_, v___x_510_, v___x_511_, v___x_512_);
v___x_514_ = lean_alloc_ctor(4, 1, 8);
lean_ctor_set(v___x_514_, 0, v_a_505_);
lean_ctor_set_uint64(v___x_514_, sizeof(void*)*1, v___x_513_);
return v___x_514_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_mvar___override(lean_object* v_a_517_){
_start:
{
uint64_t v___x_518_; uint64_t v___x_519_; uint64_t v___x_520_; lean_object* v___x_521_; uint8_t v___x_522_; uint8_t v___x_523_; uint64_t v___x_524_; lean_object* v___x_525_; 
v___x_518_ = 2237ULL;
v___x_519_ = l_Lean_instHashableLevelMVarId_hash(v_a_517_);
v___x_520_ = lean_uint64_mix_hash(v___x_518_, v___x_519_);
v___x_521_ = lean_unsigned_to_nat(0u);
v___x_522_ = 1;
v___x_523_ = 0;
v___x_524_ = lean_level_mk_data(v___x_520_, v___x_521_, v___x_522_, v___x_523_);
v___x_525_ = lean_alloc_ctor(5, 1, 8);
lean_ctor_set(v___x_525_, 0, v_a_517_);
lean_ctor_set_uint64(v___x_525_, sizeof(void*)*1, v___x_524_);
return v___x_525_;
}
}
static lean_object* _init_l_Lean_instInhabitedLevel_default(void){
_start:
{
lean_object* v___x_526_; 
v___x_526_ = lean_box(0);
return v___x_526_;
}
}
static lean_object* _init_l_Lean_instInhabitedLevel(void){
_start:
{
lean_object* v___x_527_; 
v___x_527_ = lean_box(0);
return v___x_527_;
}
}
static lean_object* _init_l_Lean_instReprLevel_repr___closed__2(void){
_start:
{
lean_object* v___x_531_; lean_object* v___x_532_; 
v___x_531_ = lean_unsigned_to_nat(2u);
v___x_532_ = lean_nat_to_int(v___x_531_);
return v___x_532_;
}
}
static lean_object* _init_l_Lean_instReprLevel_repr___closed__3(void){
_start:
{
lean_object* v___x_533_; lean_object* v___x_534_; 
v___x_533_ = lean_unsigned_to_nat(1u);
v___x_534_ = lean_nat_to_int(v___x_533_);
return v___x_534_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprLevel_repr(lean_object* v_x_565_, lean_object* v_prec_566_){
_start:
{
lean_object* v___y_568_; 
switch(lean_obj_tag(v_x_565_))
{
case 0:
{
lean_object* v___x_574_; uint8_t v___x_575_; 
v___x_574_ = lean_unsigned_to_nat(1024u);
v___x_575_ = lean_nat_dec_le(v___x_574_, v_prec_566_);
if (v___x_575_ == 0)
{
lean_object* v___x_576_; 
v___x_576_ = lean_obj_once(&l_Lean_instReprLevel_repr___closed__2, &l_Lean_instReprLevel_repr___closed__2_once, _init_l_Lean_instReprLevel_repr___closed__2);
v___y_568_ = v___x_576_;
goto v___jp_567_;
}
else
{
lean_object* v___x_577_; 
v___x_577_ = lean_obj_once(&l_Lean_instReprLevel_repr___closed__3, &l_Lean_instReprLevel_repr___closed__3_once, _init_l_Lean_instReprLevel_repr___closed__3);
v___y_568_ = v___x_577_;
goto v___jp_567_;
}
}
case 1:
{
lean_object* v_a_578_; lean_object* v___x_579_; lean_object* v___y_581_; uint8_t v___x_589_; 
v_a_578_ = lean_ctor_get(v_x_565_, 0);
lean_inc(v_a_578_);
lean_dec_ref_known(v_x_565_, 1);
v___x_579_ = lean_unsigned_to_nat(1024u);
v___x_589_ = lean_nat_dec_le(v___x_579_, v_prec_566_);
if (v___x_589_ == 0)
{
lean_object* v___x_590_; 
v___x_590_ = lean_obj_once(&l_Lean_instReprLevel_repr___closed__2, &l_Lean_instReprLevel_repr___closed__2_once, _init_l_Lean_instReprLevel_repr___closed__2);
v___y_581_ = v___x_590_;
goto v___jp_580_;
}
else
{
lean_object* v___x_591_; 
v___x_591_ = lean_obj_once(&l_Lean_instReprLevel_repr___closed__3, &l_Lean_instReprLevel_repr___closed__3_once, _init_l_Lean_instReprLevel_repr___closed__3);
v___y_581_ = v___x_591_;
goto v___jp_580_;
}
v___jp_580_:
{
lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; uint8_t v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; 
v___x_582_ = ((lean_object*)(l_Lean_instReprLevel_repr___closed__6));
v___x_583_ = l_Lean_instReprLevel_repr(v_a_578_, v___x_579_);
v___x_584_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_584_, 0, v___x_582_);
lean_ctor_set(v___x_584_, 1, v___x_583_);
lean_inc(v___y_581_);
v___x_585_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_585_, 0, v___y_581_);
lean_ctor_set(v___x_585_, 1, v___x_584_);
v___x_586_ = 0;
v___x_587_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_587_, 0, v___x_585_);
lean_ctor_set_uint8(v___x_587_, sizeof(void*)*1, v___x_586_);
v___x_588_ = l_Repr_addAppParen(v___x_587_, v_prec_566_);
return v___x_588_;
}
}
case 2:
{
lean_object* v_a_592_; lean_object* v_a_593_; lean_object* v___x_594_; lean_object* v___y_596_; uint8_t v___x_608_; 
v_a_592_ = lean_ctor_get(v_x_565_, 0);
lean_inc(v_a_592_);
v_a_593_ = lean_ctor_get(v_x_565_, 1);
lean_inc(v_a_593_);
lean_dec_ref_known(v_x_565_, 2);
v___x_594_ = lean_unsigned_to_nat(1024u);
v___x_608_ = lean_nat_dec_le(v___x_594_, v_prec_566_);
if (v___x_608_ == 0)
{
lean_object* v___x_609_; 
v___x_609_ = lean_obj_once(&l_Lean_instReprLevel_repr___closed__2, &l_Lean_instReprLevel_repr___closed__2_once, _init_l_Lean_instReprLevel_repr___closed__2);
v___y_596_ = v___x_609_;
goto v___jp_595_;
}
else
{
lean_object* v___x_610_; 
v___x_610_ = lean_obj_once(&l_Lean_instReprLevel_repr___closed__3, &l_Lean_instReprLevel_repr___closed__3_once, _init_l_Lean_instReprLevel_repr___closed__3);
v___y_596_ = v___x_610_;
goto v___jp_595_;
}
v___jp_595_:
{
lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; uint8_t v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; 
v___x_597_ = lean_box(1);
v___x_598_ = ((lean_object*)(l_Lean_instReprLevel_repr___closed__9));
v___x_599_ = l_Lean_instReprLevel_repr(v_a_592_, v___x_594_);
v___x_600_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_600_, 0, v___x_598_);
lean_ctor_set(v___x_600_, 1, v___x_599_);
v___x_601_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_601_, 0, v___x_600_);
lean_ctor_set(v___x_601_, 1, v___x_597_);
v___x_602_ = l_Lean_instReprLevel_repr(v_a_593_, v___x_594_);
v___x_603_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_603_, 0, v___x_601_);
lean_ctor_set(v___x_603_, 1, v___x_602_);
lean_inc(v___y_596_);
v___x_604_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_604_, 0, v___y_596_);
lean_ctor_set(v___x_604_, 1, v___x_603_);
v___x_605_ = 0;
v___x_606_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_606_, 0, v___x_604_);
lean_ctor_set_uint8(v___x_606_, sizeof(void*)*1, v___x_605_);
v___x_607_ = l_Repr_addAppParen(v___x_606_, v_prec_566_);
return v___x_607_;
}
}
case 3:
{
lean_object* v_a_611_; lean_object* v_a_612_; lean_object* v___x_613_; lean_object* v___y_615_; uint8_t v___x_627_; 
v_a_611_ = lean_ctor_get(v_x_565_, 0);
lean_inc(v_a_611_);
v_a_612_ = lean_ctor_get(v_x_565_, 1);
lean_inc(v_a_612_);
lean_dec_ref_known(v_x_565_, 2);
v___x_613_ = lean_unsigned_to_nat(1024u);
v___x_627_ = lean_nat_dec_le(v___x_613_, v_prec_566_);
if (v___x_627_ == 0)
{
lean_object* v___x_628_; 
v___x_628_ = lean_obj_once(&l_Lean_instReprLevel_repr___closed__2, &l_Lean_instReprLevel_repr___closed__2_once, _init_l_Lean_instReprLevel_repr___closed__2);
v___y_615_ = v___x_628_;
goto v___jp_614_;
}
else
{
lean_object* v___x_629_; 
v___x_629_ = lean_obj_once(&l_Lean_instReprLevel_repr___closed__3, &l_Lean_instReprLevel_repr___closed__3_once, _init_l_Lean_instReprLevel_repr___closed__3);
v___y_615_ = v___x_629_;
goto v___jp_614_;
}
v___jp_614_:
{
lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; uint8_t v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; 
v___x_616_ = lean_box(1);
v___x_617_ = ((lean_object*)(l_Lean_instReprLevel_repr___closed__12));
v___x_618_ = l_Lean_instReprLevel_repr(v_a_611_, v___x_613_);
v___x_619_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_619_, 0, v___x_617_);
lean_ctor_set(v___x_619_, 1, v___x_618_);
v___x_620_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_620_, 0, v___x_619_);
lean_ctor_set(v___x_620_, 1, v___x_616_);
v___x_621_ = l_Lean_instReprLevel_repr(v_a_612_, v___x_613_);
v___x_622_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_622_, 0, v___x_620_);
lean_ctor_set(v___x_622_, 1, v___x_621_);
lean_inc(v___y_615_);
v___x_623_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_623_, 0, v___y_615_);
lean_ctor_set(v___x_623_, 1, v___x_622_);
v___x_624_ = 0;
v___x_625_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_625_, 0, v___x_623_);
lean_ctor_set_uint8(v___x_625_, sizeof(void*)*1, v___x_624_);
v___x_626_ = l_Repr_addAppParen(v___x_625_, v_prec_566_);
return v___x_626_;
}
}
case 4:
{
lean_object* v_a_630_; lean_object* v___y_632_; lean_object* v___x_641_; uint8_t v___x_642_; 
v_a_630_ = lean_ctor_get(v_x_565_, 0);
lean_inc(v_a_630_);
lean_dec_ref_known(v_x_565_, 1);
v___x_641_ = lean_unsigned_to_nat(1024u);
v___x_642_ = lean_nat_dec_le(v___x_641_, v_prec_566_);
if (v___x_642_ == 0)
{
lean_object* v___x_643_; 
v___x_643_ = lean_obj_once(&l_Lean_instReprLevel_repr___closed__2, &l_Lean_instReprLevel_repr___closed__2_once, _init_l_Lean_instReprLevel_repr___closed__2);
v___y_632_ = v___x_643_;
goto v___jp_631_;
}
else
{
lean_object* v___x_644_; 
v___x_644_ = lean_obj_once(&l_Lean_instReprLevel_repr___closed__3, &l_Lean_instReprLevel_repr___closed__3_once, _init_l_Lean_instReprLevel_repr___closed__3);
v___y_632_ = v___x_644_;
goto v___jp_631_;
}
v___jp_631_:
{
lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; uint8_t v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; 
v___x_633_ = ((lean_object*)(l_Lean_instReprLevel_repr___closed__15));
v___x_634_ = lean_unsigned_to_nat(1024u);
v___x_635_ = l_Lean_Name_reprPrec(v_a_630_, v___x_634_);
v___x_636_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_636_, 0, v___x_633_);
lean_ctor_set(v___x_636_, 1, v___x_635_);
lean_inc(v___y_632_);
v___x_637_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_637_, 0, v___y_632_);
lean_ctor_set(v___x_637_, 1, v___x_636_);
v___x_638_ = 0;
v___x_639_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_639_, 0, v___x_637_);
lean_ctor_set_uint8(v___x_639_, sizeof(void*)*1, v___x_638_);
v___x_640_ = l_Repr_addAppParen(v___x_639_, v_prec_566_);
return v___x_640_;
}
}
default: 
{
lean_object* v_a_645_; lean_object* v___y_647_; lean_object* v___x_656_; uint8_t v___x_657_; 
v_a_645_ = lean_ctor_get(v_x_565_, 0);
lean_inc(v_a_645_);
lean_dec_ref_known(v_x_565_, 1);
v___x_656_ = lean_unsigned_to_nat(1024u);
v___x_657_ = lean_nat_dec_le(v___x_656_, v_prec_566_);
if (v___x_657_ == 0)
{
lean_object* v___x_658_; 
v___x_658_ = lean_obj_once(&l_Lean_instReprLevel_repr___closed__2, &l_Lean_instReprLevel_repr___closed__2_once, _init_l_Lean_instReprLevel_repr___closed__2);
v___y_647_ = v___x_658_;
goto v___jp_646_;
}
else
{
lean_object* v___x_659_; 
v___x_659_ = lean_obj_once(&l_Lean_instReprLevel_repr___closed__3, &l_Lean_instReprLevel_repr___closed__3_once, _init_l_Lean_instReprLevel_repr___closed__3);
v___y_647_ = v___x_659_;
goto v___jp_646_;
}
v___jp_646_:
{
lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; uint8_t v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; 
v___x_648_ = ((lean_object*)(l_Lean_instReprLevel_repr___closed__18));
v___x_649_ = lean_unsigned_to_nat(1024u);
v___x_650_ = l_Lean_Name_reprPrec(v_a_645_, v___x_649_);
v___x_651_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_651_, 0, v___x_648_);
lean_ctor_set(v___x_651_, 1, v___x_650_);
lean_inc(v___y_647_);
v___x_652_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_652_, 0, v___y_647_);
lean_ctor_set(v___x_652_, 1, v___x_651_);
v___x_653_ = 0;
v___x_654_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_654_, 0, v___x_652_);
lean_ctor_set_uint8(v___x_654_, sizeof(void*)*1, v___x_653_);
v___x_655_ = l_Repr_addAppParen(v___x_654_, v_prec_566_);
return v___x_655_;
}
}
}
v___jp_567_:
{
lean_object* v___x_569_; lean_object* v___x_570_; uint8_t v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; 
v___x_569_ = ((lean_object*)(l_Lean_instReprLevel_repr___closed__1));
lean_inc(v___y_568_);
v___x_570_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_570_, 0, v___y_568_);
lean_ctor_set(v___x_570_, 1, v___x_569_);
v___x_571_ = 0;
v___x_572_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_572_, 0, v___x_570_);
lean_ctor_set_uint8(v___x_572_, sizeof(void*)*1, v___x_571_);
v___x_573_ = l_Repr_addAppParen(v___x_572_, v_prec_566_);
return v___x_573_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instReprLevel_repr___boxed(lean_object* v_x_660_, lean_object* v_prec_661_){
_start:
{
lean_object* v_res_662_; 
v_res_662_ = l_Lean_instReprLevel_repr(v_x_660_, v_prec_661_);
lean_dec(v_prec_661_);
return v_res_662_;
}
}
LEAN_EXPORT uint64_t l_Lean_Level_hash(lean_object* v_u_665_){
_start:
{
uint64_t v___x_666_; uint64_t v___x_667_; 
v___x_666_ = l_Lean_Level_data___override(v_u_665_);
v___x_667_ = l_Lean_Level_Data_hash(v___x_666_);
return v___x_667_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_hash___boxed(lean_object* v_u_668_){
_start:
{
uint64_t v_res_669_; lean_object* v_r_670_; 
v_res_669_ = l_Lean_Level_hash(v_u_668_);
lean_dec(v_u_668_);
v_r_670_ = lean_box_uint64(v_res_669_);
return v_r_670_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_depth(lean_object* v_u_673_){
_start:
{
uint64_t v___x_674_; uint32_t v___x_675_; lean_object* v___x_676_; 
v___x_674_ = l_Lean_Level_data___override(v_u_673_);
v___x_675_ = l_Lean_Level_Data_depth(v___x_674_);
v___x_676_ = lean_uint32_to_nat(v___x_675_);
return v___x_676_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_depth___boxed(lean_object* v_u_677_){
_start:
{
lean_object* v_res_678_; 
v_res_678_ = l_Lean_Level_depth(v_u_677_);
lean_dec(v_u_677_);
return v_res_678_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_hasMVar(lean_object* v_u_679_){
_start:
{
uint64_t v___x_680_; uint8_t v___x_681_; 
v___x_680_ = l_Lean_Level_data___override(v_u_679_);
v___x_681_ = l_Lean_Level_Data_hasMVar(v___x_680_);
return v___x_681_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_hasMVar___boxed(lean_object* v_u_682_){
_start:
{
uint8_t v_res_683_; lean_object* v_r_684_; 
v_res_683_ = l_Lean_Level_hasMVar(v_u_682_);
lean_dec(v_u_682_);
v_r_684_ = lean_box(v_res_683_);
return v_r_684_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_hasParam(lean_object* v_u_685_){
_start:
{
uint64_t v___x_686_; uint8_t v___x_687_; 
v___x_686_ = l_Lean_Level_data___override(v_u_685_);
v___x_687_ = l_Lean_Level_Data_hasParam(v___x_686_);
return v___x_687_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_hasParam___boxed(lean_object* v_u_688_){
_start:
{
uint8_t v_res_689_; lean_object* v_r_690_; 
v_res_689_ = l_Lean_Level_hasParam(v_u_688_);
lean_dec(v_u_688_);
v_r_690_ = lean_box(v_res_689_);
return v_r_690_;
}
}
LEAN_EXPORT uint32_t lean_level_hash(lean_object* v_u_691_){
_start:
{
uint64_t v___x_692_; uint32_t v___x_693_; 
v___x_692_ = l_Lean_Level_hash(v_u_691_);
lean_dec(v_u_691_);
v___x_693_ = lean_uint64_to_uint32(v___x_692_);
return v___x_693_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_hashEx___boxed(lean_object* v_u_694_){
_start:
{
uint32_t v_res_695_; lean_object* v_r_696_; 
v_res_695_ = lean_level_hash(v_u_694_);
v_r_696_ = lean_box_uint32(v_res_695_);
return v_r_696_;
}
}
LEAN_EXPORT uint8_t lean_level_has_mvar(lean_object* v_u_697_){
_start:
{
uint8_t v___x_698_; 
v___x_698_ = l_Lean_Level_hasMVar(v_u_697_);
lean_dec(v_u_697_);
return v___x_698_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_hasMVarEx___boxed(lean_object* v_u_699_){
_start:
{
uint8_t v_res_700_; lean_object* v_r_701_; 
v_res_700_ = lean_level_has_mvar(v_u_699_);
v_r_701_ = lean_box(v_res_700_);
return v_r_701_;
}
}
LEAN_EXPORT uint8_t lean_level_has_param(lean_object* v_u_702_){
_start:
{
uint8_t v___x_703_; 
v___x_703_ = l_Lean_Level_hasParam(v_u_702_);
lean_dec(v_u_702_);
return v___x_703_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_hasParamEx___boxed(lean_object* v_u_704_){
_start:
{
uint8_t v_res_705_; lean_object* v_r_706_; 
v_res_705_ = lean_level_has_param(v_u_704_);
v_r_706_ = lean_box(v_res_705_);
return v_r_706_;
}
}
LEAN_EXPORT uint32_t lean_level_depth(lean_object* v_u_707_){
_start:
{
uint64_t v___x_708_; uint32_t v___x_709_; 
v___x_708_ = l_Lean_Level_data___override(v_u_707_);
lean_dec(v_u_707_);
v___x_709_ = l_Lean_Level_Data_depth(v___x_708_);
return v___x_709_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_depthEx___boxed(lean_object* v_u_710_){
_start:
{
uint32_t v_res_711_; lean_object* v_r_712_; 
v_res_711_ = lean_level_depth(v_u_710_);
v_r_712_ = lean_box_uint32(v_res_711_);
return v_r_712_;
}
}
static lean_object* _init_l_Lean_levelZero(void){
_start:
{
lean_object* v___x_713_; 
v___x_713_ = lean_box(0);
return v___x_713_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLevelMVar(lean_object* v_mvarId_714_){
_start:
{
lean_object* v___x_715_; 
v___x_715_ = l_Lean_Level_mvar___override(v_mvarId_714_);
return v___x_715_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLevelParam(lean_object* v_name_716_){
_start:
{
lean_object* v___x_717_; 
v___x_717_ = l_Lean_Level_param___override(v_name_716_);
return v___x_717_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLevelSucc(lean_object* v_u_718_){
_start:
{
lean_object* v___x_719_; 
v___x_719_ = l_Lean_Level_succ___override(v_u_718_);
return v___x_719_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLevelMax(lean_object* v_u_720_, lean_object* v_v_721_){
_start:
{
lean_object* v___x_722_; 
v___x_722_ = l_Lean_Level_max___override(v_u_720_, v_v_721_);
return v___x_722_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLevelIMax(lean_object* v_u_723_, lean_object* v_v_724_){
_start:
{
lean_object* v___x_725_; 
v___x_725_ = l_Lean_Level_imax___override(v_u_723_, v_v_724_);
return v___x_725_;
}
}
static lean_object* _init_l_Lean_Level_one___closed__0(void){
_start:
{
lean_object* v___x_726_; lean_object* v___x_727_; 
v___x_726_ = lean_box(0);
v___x_727_ = l_Lean_Level_succ___override(v___x_726_);
return v___x_727_;
}
}
static lean_object* _init_l_Lean_Level_one(void){
_start:
{
lean_object* v___x_728_; 
v___x_728_ = lean_obj_once(&l_Lean_Level_one___closed__0, &l_Lean_Level_one___closed__0_once, _init_l_Lean_Level_one___closed__0);
return v___x_728_;
}
}
static lean_object* _init_l_Lean_levelOne(void){
_start:
{
lean_object* v___x_729_; 
v___x_729_ = lean_obj_once(&l_Lean_Level_one___closed__0, &l_Lean_Level_one___closed__0_once, _init_l_Lean_Level_one___closed__0);
return v___x_729_;
}
}
LEAN_EXPORT lean_object* lean_level_mk_zero(lean_object* v_x_730_){
_start:
{
lean_object* v___x_731_; 
v___x_731_ = lean_box(0);
return v___x_731_;
}
}
LEAN_EXPORT lean_object* lean_level_mk_succ(lean_object* v_u_732_){
_start:
{
lean_object* v___x_733_; 
v___x_733_ = l_Lean_Level_succ___override(v_u_732_);
return v___x_733_;
}
}
LEAN_EXPORT lean_object* lean_level_mk_mvar(lean_object* v_mvarId_734_){
_start:
{
lean_object* v___x_735_; 
v___x_735_ = l_Lean_Level_mvar___override(v_mvarId_734_);
return v___x_735_;
}
}
LEAN_EXPORT lean_object* lean_level_mk_param(lean_object* v_name_736_){
_start:
{
lean_object* v___x_737_; 
v___x_737_ = l_Lean_Level_param___override(v_name_736_);
return v___x_737_;
}
}
LEAN_EXPORT lean_object* lean_level_mk_max(lean_object* v_u_738_, lean_object* v_v_739_){
_start:
{
lean_object* v___x_740_; 
v___x_740_ = l_Lean_Level_max___override(v_u_738_, v_v_739_);
return v___x_740_;
}
}
LEAN_EXPORT lean_object* lean_level_mk_imax(lean_object* v_u_741_, lean_object* v_v_742_){
_start:
{
lean_object* v___x_743_; 
v___x_743_ = l_Lean_Level_imax___override(v_u_741_, v_v_742_);
return v___x_743_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_isZero(lean_object* v_x_744_){
_start:
{
if (lean_obj_tag(v_x_744_) == 0)
{
uint8_t v___x_745_; 
v___x_745_ = 1;
return v___x_745_;
}
else
{
uint8_t v___x_746_; 
v___x_746_ = 0;
return v___x_746_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_isZero___boxed(lean_object* v_x_747_){
_start:
{
uint8_t v_res_748_; lean_object* v_r_749_; 
v_res_748_ = l_Lean_Level_isZero(v_x_747_);
lean_dec(v_x_747_);
v_r_749_ = lean_box(v_res_748_);
return v_r_749_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_isSucc(lean_object* v_x_750_){
_start:
{
if (lean_obj_tag(v_x_750_) == 1)
{
uint8_t v___x_751_; 
v___x_751_ = 1;
return v___x_751_;
}
else
{
uint8_t v___x_752_; 
v___x_752_ = 0;
return v___x_752_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_isSucc___boxed(lean_object* v_x_753_){
_start:
{
uint8_t v_res_754_; lean_object* v_r_755_; 
v_res_754_ = l_Lean_Level_isSucc(v_x_753_);
lean_dec(v_x_753_);
v_r_755_ = lean_box(v_res_754_);
return v_r_755_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_isMax(lean_object* v_x_756_){
_start:
{
if (lean_obj_tag(v_x_756_) == 2)
{
uint8_t v___x_757_; 
v___x_757_ = 1;
return v___x_757_;
}
else
{
uint8_t v___x_758_; 
v___x_758_ = 0;
return v___x_758_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_isMax___boxed(lean_object* v_x_759_){
_start:
{
uint8_t v_res_760_; lean_object* v_r_761_; 
v_res_760_ = l_Lean_Level_isMax(v_x_759_);
lean_dec(v_x_759_);
v_r_761_ = lean_box(v_res_760_);
return v_r_761_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_isIMax(lean_object* v_x_762_){
_start:
{
if (lean_obj_tag(v_x_762_) == 3)
{
uint8_t v___x_763_; 
v___x_763_ = 1;
return v___x_763_;
}
else
{
uint8_t v___x_764_; 
v___x_764_ = 0;
return v___x_764_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_isIMax___boxed(lean_object* v_x_765_){
_start:
{
uint8_t v_res_766_; lean_object* v_r_767_; 
v_res_766_ = l_Lean_Level_isIMax(v_x_765_);
lean_dec(v_x_765_);
v_r_767_ = lean_box(v_res_766_);
return v_r_767_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_isMaxIMax(lean_object* v_x_768_){
_start:
{
switch(lean_obj_tag(v_x_768_))
{
case 2:
{
uint8_t v___x_769_; 
v___x_769_ = 1;
return v___x_769_;
}
case 3:
{
uint8_t v___x_770_; 
v___x_770_ = 1;
return v___x_770_;
}
default: 
{
uint8_t v___x_771_; 
v___x_771_ = 0;
return v___x_771_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_isMaxIMax___boxed(lean_object* v_x_772_){
_start:
{
uint8_t v_res_773_; lean_object* v_r_774_; 
v_res_773_ = l_Lean_Level_isMaxIMax(v_x_772_);
lean_dec(v_x_772_);
v_r_774_ = lean_box(v_res_773_);
return v_r_774_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_isParam(lean_object* v_x_775_){
_start:
{
if (lean_obj_tag(v_x_775_) == 4)
{
uint8_t v___x_776_; 
v___x_776_ = 1;
return v___x_776_;
}
else
{
uint8_t v___x_777_; 
v___x_777_ = 0;
return v___x_777_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_isParam___boxed(lean_object* v_x_778_){
_start:
{
uint8_t v_res_779_; lean_object* v_r_780_; 
v_res_779_ = l_Lean_Level_isParam(v_x_778_);
lean_dec(v_x_778_);
v_r_780_ = lean_box(v_res_779_);
return v_r_780_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_isMVar(lean_object* v_x_781_){
_start:
{
if (lean_obj_tag(v_x_781_) == 5)
{
uint8_t v___x_782_; 
v___x_782_ = 1;
return v___x_782_;
}
else
{
uint8_t v___x_783_; 
v___x_783_ = 0;
return v___x_783_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_isMVar___boxed(lean_object* v_x_784_){
_start:
{
uint8_t v_res_785_; lean_object* v_r_786_; 
v_res_785_ = l_Lean_Level_isMVar(v_x_784_);
lean_dec(v_x_784_);
v_r_786_ = lean_box(v_res_785_);
return v_r_786_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Level_mvarId_x21_spec__0(lean_object* v_msg_787_){
_start:
{
lean_object* v___x_788_; lean_object* v___x_789_; 
v___x_788_ = lean_box(0);
v___x_789_ = lean_panic_fn_borrowed(v___x_788_, v_msg_787_);
return v___x_789_;
}
}
static lean_object* _init_l_Lean_Level_mvarId_x21___closed__3(void){
_start:
{
lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; 
v___x_793_ = ((lean_object*)(l_Lean_Level_mvarId_x21___closed__2));
v___x_794_ = lean_unsigned_to_nat(19u);
v___x_795_ = lean_unsigned_to_nat(196u);
v___x_796_ = ((lean_object*)(l_Lean_Level_mvarId_x21___closed__1));
v___x_797_ = ((lean_object*)(l_Lean_Level_mvarId_x21___closed__0));
v___x_798_ = l_mkPanicMessageWithDecl(v___x_797_, v___x_796_, v___x_795_, v___x_794_, v___x_793_);
return v___x_798_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_mvarId_x21(lean_object* v_x_799_){
_start:
{
if (lean_obj_tag(v_x_799_) == 5)
{
lean_object* v_a_800_; 
v_a_800_ = lean_ctor_get(v_x_799_, 0);
lean_inc(v_a_800_);
return v_a_800_;
}
else
{
lean_object* v___x_801_; lean_object* v___x_802_; 
v___x_801_ = lean_obj_once(&l_Lean_Level_mvarId_x21___closed__3, &l_Lean_Level_mvarId_x21___closed__3_once, _init_l_Lean_Level_mvarId_x21___closed__3);
v___x_802_ = l_panic___at___00Lean_Level_mvarId_x21_spec__0(v___x_801_);
return v___x_802_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_mvarId_x21___boxed(lean_object* v_x_803_){
_start:
{
lean_object* v_res_804_; 
v_res_804_ = l_Lean_Level_mvarId_x21(v_x_803_);
lean_dec(v_x_803_);
return v_res_804_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_isNeverZero(lean_object* v_x_805_){
_start:
{
switch(lean_obj_tag(v_x_805_))
{
case 0:
{
uint8_t v___x_806_; 
v___x_806_ = 0;
return v___x_806_;
}
case 1:
{
uint8_t v___x_807_; 
v___x_807_ = 1;
return v___x_807_;
}
case 2:
{
lean_object* v_a_808_; lean_object* v_a_809_; uint8_t v___x_810_; 
v_a_808_ = lean_ctor_get(v_x_805_, 0);
v_a_809_ = lean_ctor_get(v_x_805_, 1);
v___x_810_ = l_Lean_Level_isNeverZero(v_a_808_);
if (v___x_810_ == 0)
{
v_x_805_ = v_a_809_;
goto _start;
}
else
{
return v___x_810_;
}
}
case 3:
{
lean_object* v_a_812_; 
v_a_812_ = lean_ctor_get(v_x_805_, 1);
v_x_805_ = v_a_812_;
goto _start;
}
default: 
{
uint8_t v___x_814_; 
v___x_814_ = 0;
return v___x_814_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_isNeverZero___boxed(lean_object* v_x_815_){
_start:
{
uint8_t v_res_816_; lean_object* v_r_817_; 
v_res_816_ = l_Lean_Level_isNeverZero(v_x_815_);
lean_dec(v_x_815_);
v_r_817_ = lean_box(v_res_816_);
return v_r_817_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_isAlwaysZero(lean_object* v_x_818_){
_start:
{
switch(lean_obj_tag(v_x_818_))
{
case 0:
{
uint8_t v___x_819_; 
v___x_819_ = 1;
return v___x_819_;
}
case 2:
{
lean_object* v_a_820_; lean_object* v_a_821_; uint8_t v___x_822_; 
v_a_820_ = lean_ctor_get(v_x_818_, 0);
v_a_821_ = lean_ctor_get(v_x_818_, 1);
v___x_822_ = l_Lean_Level_isAlwaysZero(v_a_820_);
if (v___x_822_ == 0)
{
return v___x_822_;
}
else
{
v_x_818_ = v_a_821_;
goto _start;
}
}
case 3:
{
lean_object* v_a_824_; 
v_a_824_ = lean_ctor_get(v_x_818_, 1);
v_x_818_ = v_a_824_;
goto _start;
}
default: 
{
uint8_t v___x_826_; 
v___x_826_ = 0;
return v___x_826_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_isAlwaysZero___boxed(lean_object* v_x_827_){
_start:
{
uint8_t v_res_828_; lean_object* v_r_829_; 
v_res_828_ = l_Lean_Level_isAlwaysZero(v_x_827_);
lean_dec(v_x_827_);
v_r_829_ = lean_box(v_res_828_);
return v_r_829_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_ofNat(lean_object* v_x_830_){
_start:
{
lean_object* v_zero_831_; uint8_t v_isZero_832_; 
v_zero_831_ = lean_unsigned_to_nat(0u);
v_isZero_832_ = lean_nat_dec_eq(v_x_830_, v_zero_831_);
if (v_isZero_832_ == 1)
{
lean_object* v___x_833_; 
v___x_833_ = lean_box(0);
return v___x_833_;
}
else
{
lean_object* v_one_834_; lean_object* v_n_835_; lean_object* v___x_836_; lean_object* v___x_837_; 
v_one_834_ = lean_unsigned_to_nat(1u);
v_n_835_ = lean_nat_sub(v_x_830_, v_one_834_);
v___x_836_ = l_Lean_Level_ofNat(v_n_835_);
lean_dec(v_n_835_);
v___x_837_ = l_Lean_Level_succ___override(v___x_836_);
return v___x_837_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_ofNat___boxed(lean_object* v_x_838_){
_start:
{
lean_object* v_res_839_; 
v_res_839_ = l_Lean_Level_ofNat(v_x_838_);
lean_dec(v_x_838_);
return v_res_839_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_instOfNat(lean_object* v_n_840_){
_start:
{
lean_object* v___x_841_; 
v___x_841_ = l_Lean_Level_ofNat(v_n_840_);
return v___x_841_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_instOfNat___boxed(lean_object* v_n_842_){
_start:
{
lean_object* v_res_843_; 
v_res_843_ = l_Lean_Level_instOfNat(v_n_842_);
lean_dec(v_n_842_);
return v_res_843_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_addOffsetAux(lean_object* v_x_844_, lean_object* v_x_845_){
_start:
{
lean_object* v_zero_846_; uint8_t v_isZero_847_; 
v_zero_846_ = lean_unsigned_to_nat(0u);
v_isZero_847_ = lean_nat_dec_eq(v_x_844_, v_zero_846_);
if (v_isZero_847_ == 1)
{
lean_dec(v_x_844_);
return v_x_845_;
}
else
{
lean_object* v_one_848_; lean_object* v_n_849_; lean_object* v___x_850_; 
v_one_848_ = lean_unsigned_to_nat(1u);
v_n_849_ = lean_nat_sub(v_x_844_, v_one_848_);
lean_dec(v_x_844_);
v___x_850_ = l_Lean_Level_succ___override(v_x_845_);
v_x_844_ = v_n_849_;
v_x_845_ = v___x_850_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_addOffset(lean_object* v_u_852_, lean_object* v_n_853_){
_start:
{
lean_object* v___x_854_; 
v___x_854_ = l_Lean_Level_addOffsetAux(v_n_853_, v_u_852_);
return v___x_854_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_isExplicit(lean_object* v_x_855_){
_start:
{
switch(lean_obj_tag(v_x_855_))
{
case 0:
{
uint8_t v___x_856_; 
v___x_856_ = 1;
return v___x_856_;
}
case 1:
{
lean_object* v_a_857_; uint8_t v___x_858_; 
v_a_857_ = lean_ctor_get(v_x_855_, 0);
v___x_858_ = l_Lean_Level_hasMVar(v_a_857_);
if (v___x_858_ == 0)
{
uint8_t v___x_859_; 
v___x_859_ = l_Lean_Level_hasParam(v_a_857_);
if (v___x_859_ == 0)
{
v_x_855_ = v_a_857_;
goto _start;
}
else
{
return v___x_858_;
}
}
else
{
uint8_t v___x_861_; 
v___x_861_ = 0;
return v___x_861_;
}
}
default: 
{
uint8_t v___x_862_; 
v___x_862_ = 0;
return v___x_862_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_isExplicit___boxed(lean_object* v_x_863_){
_start:
{
uint8_t v_res_864_; lean_object* v_r_865_; 
v_res_864_ = l_Lean_Level_isExplicit(v_x_863_);
lean_dec(v_x_863_);
v_r_865_ = lean_box(v_res_864_);
return v_r_865_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_getOffsetAux(lean_object* v_x_866_, lean_object* v_x_867_){
_start:
{
if (lean_obj_tag(v_x_866_) == 1)
{
lean_object* v_a_868_; lean_object* v___x_869_; lean_object* v___x_870_; 
v_a_868_ = lean_ctor_get(v_x_866_, 0);
v___x_869_ = lean_unsigned_to_nat(1u);
v___x_870_ = lean_nat_add(v_x_867_, v___x_869_);
lean_dec(v_x_867_);
v_x_866_ = v_a_868_;
v_x_867_ = v___x_870_;
goto _start;
}
else
{
return v_x_867_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_getOffsetAux___boxed(lean_object* v_x_872_, lean_object* v_x_873_){
_start:
{
lean_object* v_res_874_; 
v_res_874_ = l_Lean_Level_getOffsetAux(v_x_872_, v_x_873_);
lean_dec(v_x_872_);
return v_res_874_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_getOffset(lean_object* v_lvl_875_){
_start:
{
lean_object* v___x_876_; lean_object* v___x_877_; 
v___x_876_ = lean_unsigned_to_nat(0u);
v___x_877_ = l_Lean_Level_getOffsetAux(v_lvl_875_, v___x_876_);
return v___x_877_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_getOffset___boxed(lean_object* v_lvl_878_){
_start:
{
lean_object* v_res_879_; 
v_res_879_ = l_Lean_Level_getOffset(v_lvl_878_);
lean_dec(v_lvl_878_);
return v_res_879_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_getLevelOffset(lean_object* v_x_880_){
_start:
{
if (lean_obj_tag(v_x_880_) == 1)
{
lean_object* v_a_881_; 
v_a_881_ = lean_ctor_get(v_x_880_, 0);
v_x_880_ = v_a_881_;
goto _start;
}
else
{
lean_inc(v_x_880_);
return v_x_880_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_getLevelOffset___boxed(lean_object* v_x_883_){
_start:
{
lean_object* v_res_884_; 
v_res_884_ = l_Lean_Level_getLevelOffset(v_x_883_);
lean_dec(v_x_883_);
return v_res_884_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_toNat(lean_object* v_lvl_885_){
_start:
{
lean_object* v___x_886_; 
v___x_886_ = l_Lean_Level_getLevelOffset(v_lvl_885_);
if (lean_obj_tag(v___x_886_) == 0)
{
lean_object* v___x_887_; lean_object* v___x_888_; 
v___x_887_ = l_Lean_Level_getOffset(v_lvl_885_);
v___x_888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_888_, 0, v___x_887_);
return v___x_888_;
}
else
{
lean_object* v___x_889_; 
lean_dec(v___x_886_);
v___x_889_ = lean_box(0);
return v___x_889_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_toNat___boxed(lean_object* v_lvl_890_){
_start:
{
lean_object* v_res_891_; 
v_res_891_ = l_Lean_Level_toNat(v_lvl_890_);
lean_dec(v_lvl_890_);
return v_res_891_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_beq___boxed(lean_object* v_a_894_, lean_object* v_b_895_){
_start:
{
uint8_t v_res_896_; lean_object* v_r_897_; 
v_res_896_ = lean_level_eq(v_a_894_, v_b_895_);
lean_dec(v_b_895_);
lean_dec(v_a_894_);
v_r_897_ = lean_box(v_res_896_);
return v_r_897_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_occurs(lean_object* v_x_900_, lean_object* v_x_901_){
_start:
{
switch(lean_obj_tag(v_x_901_))
{
case 1:
{
lean_object* v_a_902_; uint8_t v___x_903_; 
v_a_902_ = lean_ctor_get(v_x_901_, 0);
v___x_903_ = lean_level_eq(v_x_900_, v_x_901_);
if (v___x_903_ == 0)
{
v_x_901_ = v_a_902_;
goto _start;
}
else
{
return v___x_903_;
}
}
case 2:
{
lean_object* v_a_905_; lean_object* v_a_906_; uint8_t v___y_908_; uint8_t v___x_910_; 
v_a_905_ = lean_ctor_get(v_x_901_, 0);
v_a_906_ = lean_ctor_get(v_x_901_, 1);
v___x_910_ = lean_level_eq(v_x_900_, v_x_901_);
if (v___x_910_ == 0)
{
uint8_t v___x_911_; 
v___x_911_ = l_Lean_Level_occurs(v_x_900_, v_a_905_);
v___y_908_ = v___x_911_;
goto v___jp_907_;
}
else
{
v___y_908_ = v___x_910_;
goto v___jp_907_;
}
v___jp_907_:
{
if (v___y_908_ == 0)
{
v_x_901_ = v_a_906_;
goto _start;
}
else
{
return v___y_908_;
}
}
}
case 3:
{
lean_object* v_a_912_; lean_object* v_a_913_; uint8_t v___y_915_; uint8_t v___x_917_; 
v_a_912_ = lean_ctor_get(v_x_901_, 0);
v_a_913_ = lean_ctor_get(v_x_901_, 1);
v___x_917_ = lean_level_eq(v_x_900_, v_x_901_);
if (v___x_917_ == 0)
{
uint8_t v___x_918_; 
v___x_918_ = l_Lean_Level_occurs(v_x_900_, v_a_912_);
v___y_915_ = v___x_918_;
goto v___jp_914_;
}
else
{
v___y_915_ = v___x_917_;
goto v___jp_914_;
}
v___jp_914_:
{
if (v___y_915_ == 0)
{
v_x_901_ = v_a_913_;
goto _start;
}
else
{
return v___y_915_;
}
}
}
default: 
{
uint8_t v___x_919_; 
v___x_919_ = lean_level_eq(v_x_900_, v_x_901_);
return v___x_919_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_occurs___boxed(lean_object* v_x_920_, lean_object* v_x_921_){
_start:
{
uint8_t v_res_922_; lean_object* v_r_923_; 
v_res_922_ = l_Lean_Level_occurs(v_x_920_, v_x_921_);
lean_dec(v_x_921_);
lean_dec(v_x_920_);
v_r_923_ = lean_box(v_res_922_);
return v_r_923_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_ctorToNat(lean_object* v_x_924_){
_start:
{
switch(lean_obj_tag(v_x_924_))
{
case 0:
{
lean_object* v___x_925_; 
v___x_925_ = lean_unsigned_to_nat(0u);
return v___x_925_;
}
case 1:
{
lean_object* v___x_926_; 
v___x_926_ = lean_unsigned_to_nat(3u);
return v___x_926_;
}
case 2:
{
lean_object* v___x_927_; 
v___x_927_ = lean_unsigned_to_nat(4u);
return v___x_927_;
}
case 3:
{
lean_object* v___x_928_; 
v___x_928_ = lean_unsigned_to_nat(5u);
return v___x_928_;
}
case 4:
{
lean_object* v___x_929_; 
v___x_929_ = lean_unsigned_to_nat(1u);
return v___x_929_;
}
default: 
{
lean_object* v___x_930_; 
v___x_930_ = lean_unsigned_to_nat(2u);
return v___x_930_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_ctorToNat___boxed(lean_object* v_x_931_){
_start:
{
lean_object* v_res_932_; 
v_res_932_ = l_Lean_Level_ctorToNat(v_x_931_);
lean_dec(v_x_931_);
return v_res_932_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_normLtAux(lean_object* v_x_933_, lean_object* v_x_934_, lean_object* v_x_935_, lean_object* v_x_936_){
_start:
{
lean_object* v_l_u2081_938_; lean_object* v_k_u2081_939_; lean_object* v_l_u2082_940_; lean_object* v_k_u2082_941_; lean_object* v_l_u2081_946_; lean_object* v_k_u2081_947_; lean_object* v_l_u2082_948_; lean_object* v_k_u2082_949_; 
switch(lean_obj_tag(v_x_933_))
{
case 1:
{
lean_object* v_a_955_; lean_object* v___x_956_; lean_object* v___x_957_; 
v_a_955_ = lean_ctor_get(v_x_933_, 0);
v___x_956_ = lean_unsigned_to_nat(1u);
v___x_957_ = lean_nat_add(v_x_934_, v___x_956_);
lean_dec(v_x_934_);
v_x_933_ = v_a_955_;
v_x_934_ = v___x_957_;
goto _start;
}
case 2:
{
switch(lean_obj_tag(v_x_935_))
{
case 1:
{
lean_object* v_a_959_; 
v_a_959_ = lean_ctor_get(v_x_935_, 0);
v_l_u2081_938_ = v_x_933_;
v_k_u2081_939_ = v_x_934_;
v_l_u2082_940_ = v_a_959_;
v_k_u2082_941_ = v_x_936_;
goto v___jp_937_;
}
case 2:
{
lean_object* v_a_960_; lean_object* v_a_961_; lean_object* v_a_962_; lean_object* v_a_963_; uint8_t v___x_967_; 
v_a_960_ = lean_ctor_get(v_x_933_, 0);
v_a_961_ = lean_ctor_get(v_x_933_, 1);
v_a_962_ = lean_ctor_get(v_x_935_, 0);
v_a_963_ = lean_ctor_get(v_x_935_, 1);
v___x_967_ = lean_level_eq(v_x_933_, v_x_935_);
if (v___x_967_ == 0)
{
uint8_t v___x_968_; 
lean_dec(v_x_936_);
lean_dec(v_x_934_);
v___x_968_ = lean_level_eq(v_a_960_, v_a_962_);
if (v___x_968_ == 0)
{
goto v___jp_964_;
}
else
{
if (v___x_967_ == 0)
{
lean_object* v___x_969_; 
v___x_969_ = lean_unsigned_to_nat(0u);
v_x_933_ = v_a_961_;
v_x_934_ = v___x_969_;
v_x_935_ = v_a_963_;
v_x_936_ = v___x_969_;
goto _start;
}
else
{
goto v___jp_964_;
}
}
}
else
{
uint8_t v___x_971_; 
v___x_971_ = lean_nat_dec_lt(v_x_934_, v_x_936_);
lean_dec(v_x_936_);
lean_dec(v_x_934_);
return v___x_971_;
}
v___jp_964_:
{
lean_object* v___x_965_; 
v___x_965_ = lean_unsigned_to_nat(0u);
v_x_933_ = v_a_960_;
v_x_934_ = v___x_965_;
v_x_935_ = v_a_962_;
v_x_936_ = v___x_965_;
goto _start;
}
}
default: 
{
v_l_u2081_946_ = v_x_933_;
v_k_u2081_947_ = v_x_934_;
v_l_u2082_948_ = v_x_935_;
v_k_u2082_949_ = v_x_936_;
goto v___jp_945_;
}
}
}
case 3:
{
switch(lean_obj_tag(v_x_935_))
{
case 1:
{
lean_object* v_a_972_; 
v_a_972_ = lean_ctor_get(v_x_935_, 0);
v_l_u2081_938_ = v_x_933_;
v_k_u2081_939_ = v_x_934_;
v_l_u2082_940_ = v_a_972_;
v_k_u2082_941_ = v_x_936_;
goto v___jp_937_;
}
case 3:
{
lean_object* v_a_973_; lean_object* v_a_974_; lean_object* v_a_975_; lean_object* v_a_976_; uint8_t v___x_980_; 
v_a_973_ = lean_ctor_get(v_x_933_, 0);
v_a_974_ = lean_ctor_get(v_x_933_, 1);
v_a_975_ = lean_ctor_get(v_x_935_, 0);
v_a_976_ = lean_ctor_get(v_x_935_, 1);
v___x_980_ = lean_level_eq(v_x_933_, v_x_935_);
if (v___x_980_ == 0)
{
uint8_t v___x_981_; 
lean_dec(v_x_936_);
lean_dec(v_x_934_);
v___x_981_ = lean_level_eq(v_a_973_, v_a_975_);
if (v___x_981_ == 0)
{
goto v___jp_977_;
}
else
{
if (v___x_980_ == 0)
{
lean_object* v___x_982_; 
v___x_982_ = lean_unsigned_to_nat(0u);
v_x_933_ = v_a_974_;
v_x_934_ = v___x_982_;
v_x_935_ = v_a_976_;
v_x_936_ = v___x_982_;
goto _start;
}
else
{
goto v___jp_977_;
}
}
}
else
{
uint8_t v___x_984_; 
v___x_984_ = lean_nat_dec_lt(v_x_934_, v_x_936_);
lean_dec(v_x_936_);
lean_dec(v_x_934_);
return v___x_984_;
}
v___jp_977_:
{
lean_object* v___x_978_; 
v___x_978_ = lean_unsigned_to_nat(0u);
v_x_933_ = v_a_973_;
v_x_934_ = v___x_978_;
v_x_935_ = v_a_975_;
v_x_936_ = v___x_978_;
goto _start;
}
}
default: 
{
v_l_u2081_946_ = v_x_933_;
v_k_u2081_947_ = v_x_934_;
v_l_u2082_948_ = v_x_935_;
v_k_u2082_949_ = v_x_936_;
goto v___jp_945_;
}
}
}
case 4:
{
switch(lean_obj_tag(v_x_935_))
{
case 1:
{
lean_object* v_a_985_; 
v_a_985_ = lean_ctor_get(v_x_935_, 0);
v_l_u2081_938_ = v_x_933_;
v_k_u2081_939_ = v_x_934_;
v_l_u2082_940_ = v_a_985_;
v_k_u2082_941_ = v_x_936_;
goto v___jp_937_;
}
case 4:
{
lean_object* v_a_986_; lean_object* v_a_987_; uint8_t v___x_988_; 
v_a_986_ = lean_ctor_get(v_x_933_, 0);
v_a_987_ = lean_ctor_get(v_x_935_, 0);
v___x_988_ = lean_name_eq(v_a_986_, v_a_987_);
if (v___x_988_ == 0)
{
uint8_t v___x_989_; 
lean_dec(v_x_936_);
lean_dec(v_x_934_);
v___x_989_ = l_Lean_Name_lt(v_a_986_, v_a_987_);
return v___x_989_;
}
else
{
uint8_t v___x_990_; 
v___x_990_ = lean_nat_dec_lt(v_x_934_, v_x_936_);
lean_dec(v_x_936_);
lean_dec(v_x_934_);
return v___x_990_;
}
}
default: 
{
v_l_u2081_946_ = v_x_933_;
v_k_u2081_947_ = v_x_934_;
v_l_u2082_948_ = v_x_935_;
v_k_u2082_949_ = v_x_936_;
goto v___jp_945_;
}
}
}
case 5:
{
switch(lean_obj_tag(v_x_935_))
{
case 1:
{
lean_object* v_a_991_; 
v_a_991_ = lean_ctor_get(v_x_935_, 0);
v_l_u2081_938_ = v_x_933_;
v_k_u2081_939_ = v_x_934_;
v_l_u2082_940_ = v_a_991_;
v_k_u2082_941_ = v_x_936_;
goto v___jp_937_;
}
case 5:
{
lean_object* v_a_992_; lean_object* v_a_993_; uint8_t v___x_994_; 
v_a_992_ = lean_ctor_get(v_x_933_, 0);
v_a_993_ = lean_ctor_get(v_x_935_, 0);
v___x_994_ = lean_name_eq(v_a_992_, v_a_993_);
if (v___x_994_ == 0)
{
uint8_t v___x_995_; 
lean_dec(v_x_936_);
lean_dec(v_x_934_);
v___x_995_ = l_Lean_Name_lt(v_a_992_, v_a_993_);
return v___x_995_;
}
else
{
uint8_t v___x_996_; 
v___x_996_ = lean_nat_dec_lt(v_x_934_, v_x_936_);
lean_dec(v_x_936_);
lean_dec(v_x_934_);
return v___x_996_;
}
}
default: 
{
v_l_u2081_946_ = v_x_933_;
v_k_u2081_947_ = v_x_934_;
v_l_u2082_948_ = v_x_935_;
v_k_u2082_949_ = v_x_936_;
goto v___jp_945_;
}
}
}
default: 
{
if (lean_obj_tag(v_x_935_) == 1)
{
lean_object* v_a_997_; 
v_a_997_ = lean_ctor_get(v_x_935_, 0);
v_l_u2081_938_ = v_x_933_;
v_k_u2081_939_ = v_x_934_;
v_l_u2082_940_ = v_a_997_;
v_k_u2082_941_ = v_x_936_;
goto v___jp_937_;
}
else
{
v_l_u2081_946_ = v_x_933_;
v_k_u2081_947_ = v_x_934_;
v_l_u2082_948_ = v_x_935_;
v_k_u2082_949_ = v_x_936_;
goto v___jp_945_;
}
}
}
v___jp_937_:
{
lean_object* v___x_942_; lean_object* v___x_943_; 
v___x_942_ = lean_unsigned_to_nat(1u);
v___x_943_ = lean_nat_add(v_k_u2082_941_, v___x_942_);
lean_dec(v_k_u2082_941_);
v_x_933_ = v_l_u2081_938_;
v_x_934_ = v_k_u2081_939_;
v_x_935_ = v_l_u2082_940_;
v_x_936_ = v___x_943_;
goto _start;
}
v___jp_945_:
{
uint8_t v___x_950_; 
v___x_950_ = lean_level_eq(v_l_u2081_946_, v_l_u2082_948_);
if (v___x_950_ == 0)
{
lean_object* v___x_951_; lean_object* v___x_952_; uint8_t v___x_953_; 
lean_dec(v_k_u2082_949_);
lean_dec(v_k_u2081_947_);
v___x_951_ = l_Lean_Level_ctorToNat(v_l_u2081_946_);
v___x_952_ = l_Lean_Level_ctorToNat(v_l_u2082_948_);
v___x_953_ = lean_nat_dec_lt(v___x_951_, v___x_952_);
lean_dec(v___x_952_);
lean_dec(v___x_951_);
return v___x_953_;
}
else
{
uint8_t v___x_954_; 
v___x_954_ = lean_nat_dec_lt(v_k_u2081_947_, v_k_u2082_949_);
lean_dec(v_k_u2082_949_);
lean_dec(v_k_u2081_947_);
return v___x_954_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_normLtAux___boxed(lean_object* v_x_998_, lean_object* v_x_999_, lean_object* v_x_1000_, lean_object* v_x_1001_){
_start:
{
uint8_t v_res_1002_; lean_object* v_r_1003_; 
v_res_1002_ = l_Lean_Level_normLtAux(v_x_998_, v_x_999_, v_x_1000_, v_x_1001_);
lean_dec(v_x_1000_);
lean_dec(v_x_998_);
v_r_1003_ = lean_box(v_res_1002_);
return v_r_1003_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_normLtAux_match__1_splitter___redArg(lean_object* v_x_1004_, lean_object* v_x_1005_, lean_object* v_x_1006_, lean_object* v_x_1007_, lean_object* v_h__1_1008_, lean_object* v_h__2_1009_, lean_object* v_h__3_1010_, lean_object* v_h__4_1011_, lean_object* v_h__5_1012_, lean_object* v_h__6_1013_, lean_object* v_h__7_1014_){
_start:
{
switch(lean_obj_tag(v_x_1004_))
{
case 1:
{
lean_object* v_a_1015_; lean_object* v___x_1016_; 
lean_dec(v_h__7_1014_);
lean_dec(v_h__6_1013_);
lean_dec(v_h__5_1012_);
lean_dec(v_h__4_1011_);
lean_dec(v_h__3_1010_);
lean_dec(v_h__2_1009_);
v_a_1015_ = lean_ctor_get(v_x_1004_, 0);
lean_inc(v_a_1015_);
lean_dec_ref_known(v_x_1004_, 1);
v___x_1016_ = lean_apply_4(v_h__1_1008_, v_a_1015_, v_x_1005_, v_x_1006_, v_x_1007_);
return v___x_1016_;
}
case 2:
{
lean_dec(v_h__6_1013_);
lean_dec(v_h__5_1012_);
lean_dec(v_h__4_1011_);
lean_dec(v_h__1_1008_);
switch(lean_obj_tag(v_x_1006_))
{
case 1:
{
lean_object* v_a_1017_; lean_object* v___x_1018_; 
lean_dec(v_h__7_1014_);
lean_dec(v_h__3_1010_);
v_a_1017_ = lean_ctor_get(v_x_1006_, 0);
lean_inc(v_a_1017_);
lean_dec_ref_known(v_x_1006_, 1);
v___x_1018_ = lean_apply_5(v_h__2_1009_, v_x_1004_, v_x_1005_, v_a_1017_, v_x_1007_, lean_box(0));
return v___x_1018_;
}
case 2:
{
lean_object* v_a_1019_; lean_object* v_a_1020_; lean_object* v_a_1021_; lean_object* v_a_1022_; lean_object* v___x_1023_; 
lean_dec(v_h__7_1014_);
lean_dec(v_h__2_1009_);
v_a_1019_ = lean_ctor_get(v_x_1004_, 0);
lean_inc(v_a_1019_);
v_a_1020_ = lean_ctor_get(v_x_1004_, 1);
lean_inc(v_a_1020_);
lean_dec_ref_known(v_x_1004_, 2);
v_a_1021_ = lean_ctor_get(v_x_1006_, 0);
lean_inc(v_a_1021_);
v_a_1022_ = lean_ctor_get(v_x_1006_, 1);
lean_inc(v_a_1022_);
lean_dec_ref_known(v_x_1006_, 2);
v___x_1023_ = lean_apply_6(v_h__3_1010_, v_a_1019_, v_a_1020_, v_x_1005_, v_a_1021_, v_a_1022_, v_x_1007_);
return v___x_1023_;
}
default: 
{
lean_object* v___x_1024_; 
lean_dec(v_h__3_1010_);
lean_dec(v_h__2_1009_);
v___x_1024_ = lean_apply_10(v_h__7_1014_, v_x_1004_, v_x_1005_, v_x_1006_, v_x_1007_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_1024_;
}
}
}
case 3:
{
lean_dec(v_h__6_1013_);
lean_dec(v_h__5_1012_);
lean_dec(v_h__3_1010_);
lean_dec(v_h__1_1008_);
switch(lean_obj_tag(v_x_1006_))
{
case 1:
{
lean_object* v_a_1025_; lean_object* v___x_1026_; 
lean_dec(v_h__7_1014_);
lean_dec(v_h__4_1011_);
v_a_1025_ = lean_ctor_get(v_x_1006_, 0);
lean_inc(v_a_1025_);
lean_dec_ref_known(v_x_1006_, 1);
v___x_1026_ = lean_apply_5(v_h__2_1009_, v_x_1004_, v_x_1005_, v_a_1025_, v_x_1007_, lean_box(0));
return v___x_1026_;
}
case 3:
{
lean_object* v_a_1027_; lean_object* v_a_1028_; lean_object* v_a_1029_; lean_object* v_a_1030_; lean_object* v___x_1031_; 
lean_dec(v_h__7_1014_);
lean_dec(v_h__2_1009_);
v_a_1027_ = lean_ctor_get(v_x_1004_, 0);
lean_inc(v_a_1027_);
v_a_1028_ = lean_ctor_get(v_x_1004_, 1);
lean_inc(v_a_1028_);
lean_dec_ref_known(v_x_1004_, 2);
v_a_1029_ = lean_ctor_get(v_x_1006_, 0);
lean_inc(v_a_1029_);
v_a_1030_ = lean_ctor_get(v_x_1006_, 1);
lean_inc(v_a_1030_);
lean_dec_ref_known(v_x_1006_, 2);
v___x_1031_ = lean_apply_6(v_h__4_1011_, v_a_1027_, v_a_1028_, v_x_1005_, v_a_1029_, v_a_1030_, v_x_1007_);
return v___x_1031_;
}
default: 
{
lean_object* v___x_1032_; 
lean_dec(v_h__4_1011_);
lean_dec(v_h__2_1009_);
v___x_1032_ = lean_apply_10(v_h__7_1014_, v_x_1004_, v_x_1005_, v_x_1006_, v_x_1007_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_1032_;
}
}
}
case 4:
{
lean_dec(v_h__6_1013_);
lean_dec(v_h__4_1011_);
lean_dec(v_h__3_1010_);
lean_dec(v_h__1_1008_);
switch(lean_obj_tag(v_x_1006_))
{
case 1:
{
lean_object* v_a_1033_; lean_object* v___x_1034_; 
lean_dec(v_h__7_1014_);
lean_dec(v_h__5_1012_);
v_a_1033_ = lean_ctor_get(v_x_1006_, 0);
lean_inc(v_a_1033_);
lean_dec_ref_known(v_x_1006_, 1);
v___x_1034_ = lean_apply_5(v_h__2_1009_, v_x_1004_, v_x_1005_, v_a_1033_, v_x_1007_, lean_box(0));
return v___x_1034_;
}
case 4:
{
lean_object* v_a_1035_; lean_object* v_a_1036_; lean_object* v___x_1037_; 
lean_dec(v_h__7_1014_);
lean_dec(v_h__2_1009_);
v_a_1035_ = lean_ctor_get(v_x_1004_, 0);
lean_inc(v_a_1035_);
lean_dec_ref_known(v_x_1004_, 1);
v_a_1036_ = lean_ctor_get(v_x_1006_, 0);
lean_inc(v_a_1036_);
lean_dec_ref_known(v_x_1006_, 1);
v___x_1037_ = lean_apply_4(v_h__5_1012_, v_a_1035_, v_x_1005_, v_a_1036_, v_x_1007_);
return v___x_1037_;
}
default: 
{
lean_object* v___x_1038_; 
lean_dec(v_h__5_1012_);
lean_dec(v_h__2_1009_);
v___x_1038_ = lean_apply_10(v_h__7_1014_, v_x_1004_, v_x_1005_, v_x_1006_, v_x_1007_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_1038_;
}
}
}
case 5:
{
lean_dec(v_h__5_1012_);
lean_dec(v_h__4_1011_);
lean_dec(v_h__3_1010_);
lean_dec(v_h__1_1008_);
switch(lean_obj_tag(v_x_1006_))
{
case 1:
{
lean_object* v_a_1039_; lean_object* v___x_1040_; 
lean_dec(v_h__7_1014_);
lean_dec(v_h__6_1013_);
v_a_1039_ = lean_ctor_get(v_x_1006_, 0);
lean_inc(v_a_1039_);
lean_dec_ref_known(v_x_1006_, 1);
v___x_1040_ = lean_apply_5(v_h__2_1009_, v_x_1004_, v_x_1005_, v_a_1039_, v_x_1007_, lean_box(0));
return v___x_1040_;
}
case 5:
{
lean_object* v_a_1041_; lean_object* v_a_1042_; lean_object* v___x_1043_; 
lean_dec(v_h__7_1014_);
lean_dec(v_h__2_1009_);
v_a_1041_ = lean_ctor_get(v_x_1004_, 0);
lean_inc(v_a_1041_);
lean_dec_ref_known(v_x_1004_, 1);
v_a_1042_ = lean_ctor_get(v_x_1006_, 0);
lean_inc(v_a_1042_);
lean_dec_ref_known(v_x_1006_, 1);
v___x_1043_ = lean_apply_4(v_h__6_1013_, v_a_1041_, v_x_1005_, v_a_1042_, v_x_1007_);
return v___x_1043_;
}
default: 
{
lean_object* v___x_1044_; 
lean_dec(v_h__6_1013_);
lean_dec(v_h__2_1009_);
v___x_1044_ = lean_apply_10(v_h__7_1014_, v_x_1004_, v_x_1005_, v_x_1006_, v_x_1007_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_1044_;
}
}
}
default: 
{
lean_dec(v_h__6_1013_);
lean_dec(v_h__5_1012_);
lean_dec(v_h__4_1011_);
lean_dec(v_h__3_1010_);
lean_dec(v_h__1_1008_);
if (lean_obj_tag(v_x_1006_) == 1)
{
lean_object* v_a_1045_; lean_object* v___x_1046_; 
lean_dec(v_h__7_1014_);
v_a_1045_ = lean_ctor_get(v_x_1006_, 0);
lean_inc(v_a_1045_);
lean_dec_ref_known(v_x_1006_, 1);
v___x_1046_ = lean_apply_5(v_h__2_1009_, v_x_1004_, v_x_1005_, v_a_1045_, v_x_1007_, lean_box(0));
return v___x_1046_;
}
else
{
lean_object* v___x_1047_; 
lean_dec(v_h__2_1009_);
v___x_1047_ = lean_apply_10(v_h__7_1014_, v_x_1004_, v_x_1005_, v_x_1006_, v_x_1007_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_1047_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_normLtAux_match__1_splitter(lean_object* v_motive_1048_, lean_object* v_x_1049_, lean_object* v_x_1050_, lean_object* v_x_1051_, lean_object* v_x_1052_, lean_object* v_h__1_1053_, lean_object* v_h__2_1054_, lean_object* v_h__3_1055_, lean_object* v_h__4_1056_, lean_object* v_h__5_1057_, lean_object* v_h__6_1058_, lean_object* v_h__7_1059_){
_start:
{
switch(lean_obj_tag(v_x_1049_))
{
case 1:
{
lean_object* v_a_1060_; lean_object* v___x_1061_; 
lean_dec(v_h__7_1059_);
lean_dec(v_h__6_1058_);
lean_dec(v_h__5_1057_);
lean_dec(v_h__4_1056_);
lean_dec(v_h__3_1055_);
lean_dec(v_h__2_1054_);
v_a_1060_ = lean_ctor_get(v_x_1049_, 0);
lean_inc(v_a_1060_);
lean_dec_ref_known(v_x_1049_, 1);
v___x_1061_ = lean_apply_4(v_h__1_1053_, v_a_1060_, v_x_1050_, v_x_1051_, v_x_1052_);
return v___x_1061_;
}
case 2:
{
lean_dec(v_h__6_1058_);
lean_dec(v_h__5_1057_);
lean_dec(v_h__4_1056_);
lean_dec(v_h__1_1053_);
switch(lean_obj_tag(v_x_1051_))
{
case 1:
{
lean_object* v_a_1062_; lean_object* v___x_1063_; 
lean_dec(v_h__7_1059_);
lean_dec(v_h__3_1055_);
v_a_1062_ = lean_ctor_get(v_x_1051_, 0);
lean_inc(v_a_1062_);
lean_dec_ref_known(v_x_1051_, 1);
v___x_1063_ = lean_apply_5(v_h__2_1054_, v_x_1049_, v_x_1050_, v_a_1062_, v_x_1052_, lean_box(0));
return v___x_1063_;
}
case 2:
{
lean_object* v_a_1064_; lean_object* v_a_1065_; lean_object* v_a_1066_; lean_object* v_a_1067_; lean_object* v___x_1068_; 
lean_dec(v_h__7_1059_);
lean_dec(v_h__2_1054_);
v_a_1064_ = lean_ctor_get(v_x_1049_, 0);
lean_inc(v_a_1064_);
v_a_1065_ = lean_ctor_get(v_x_1049_, 1);
lean_inc(v_a_1065_);
lean_dec_ref_known(v_x_1049_, 2);
v_a_1066_ = lean_ctor_get(v_x_1051_, 0);
lean_inc(v_a_1066_);
v_a_1067_ = lean_ctor_get(v_x_1051_, 1);
lean_inc(v_a_1067_);
lean_dec_ref_known(v_x_1051_, 2);
v___x_1068_ = lean_apply_6(v_h__3_1055_, v_a_1064_, v_a_1065_, v_x_1050_, v_a_1066_, v_a_1067_, v_x_1052_);
return v___x_1068_;
}
default: 
{
lean_object* v___x_1069_; 
lean_dec(v_h__3_1055_);
lean_dec(v_h__2_1054_);
v___x_1069_ = lean_apply_10(v_h__7_1059_, v_x_1049_, v_x_1050_, v_x_1051_, v_x_1052_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_1069_;
}
}
}
case 3:
{
lean_dec(v_h__6_1058_);
lean_dec(v_h__5_1057_);
lean_dec(v_h__3_1055_);
lean_dec(v_h__1_1053_);
switch(lean_obj_tag(v_x_1051_))
{
case 1:
{
lean_object* v_a_1070_; lean_object* v___x_1071_; 
lean_dec(v_h__7_1059_);
lean_dec(v_h__4_1056_);
v_a_1070_ = lean_ctor_get(v_x_1051_, 0);
lean_inc(v_a_1070_);
lean_dec_ref_known(v_x_1051_, 1);
v___x_1071_ = lean_apply_5(v_h__2_1054_, v_x_1049_, v_x_1050_, v_a_1070_, v_x_1052_, lean_box(0));
return v___x_1071_;
}
case 3:
{
lean_object* v_a_1072_; lean_object* v_a_1073_; lean_object* v_a_1074_; lean_object* v_a_1075_; lean_object* v___x_1076_; 
lean_dec(v_h__7_1059_);
lean_dec(v_h__2_1054_);
v_a_1072_ = lean_ctor_get(v_x_1049_, 0);
lean_inc(v_a_1072_);
v_a_1073_ = lean_ctor_get(v_x_1049_, 1);
lean_inc(v_a_1073_);
lean_dec_ref_known(v_x_1049_, 2);
v_a_1074_ = lean_ctor_get(v_x_1051_, 0);
lean_inc(v_a_1074_);
v_a_1075_ = lean_ctor_get(v_x_1051_, 1);
lean_inc(v_a_1075_);
lean_dec_ref_known(v_x_1051_, 2);
v___x_1076_ = lean_apply_6(v_h__4_1056_, v_a_1072_, v_a_1073_, v_x_1050_, v_a_1074_, v_a_1075_, v_x_1052_);
return v___x_1076_;
}
default: 
{
lean_object* v___x_1077_; 
lean_dec(v_h__4_1056_);
lean_dec(v_h__2_1054_);
v___x_1077_ = lean_apply_10(v_h__7_1059_, v_x_1049_, v_x_1050_, v_x_1051_, v_x_1052_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_1077_;
}
}
}
case 4:
{
lean_dec(v_h__6_1058_);
lean_dec(v_h__4_1056_);
lean_dec(v_h__3_1055_);
lean_dec(v_h__1_1053_);
switch(lean_obj_tag(v_x_1051_))
{
case 1:
{
lean_object* v_a_1078_; lean_object* v___x_1079_; 
lean_dec(v_h__7_1059_);
lean_dec(v_h__5_1057_);
v_a_1078_ = lean_ctor_get(v_x_1051_, 0);
lean_inc(v_a_1078_);
lean_dec_ref_known(v_x_1051_, 1);
v___x_1079_ = lean_apply_5(v_h__2_1054_, v_x_1049_, v_x_1050_, v_a_1078_, v_x_1052_, lean_box(0));
return v___x_1079_;
}
case 4:
{
lean_object* v_a_1080_; lean_object* v_a_1081_; lean_object* v___x_1082_; 
lean_dec(v_h__7_1059_);
lean_dec(v_h__2_1054_);
v_a_1080_ = lean_ctor_get(v_x_1049_, 0);
lean_inc(v_a_1080_);
lean_dec_ref_known(v_x_1049_, 1);
v_a_1081_ = lean_ctor_get(v_x_1051_, 0);
lean_inc(v_a_1081_);
lean_dec_ref_known(v_x_1051_, 1);
v___x_1082_ = lean_apply_4(v_h__5_1057_, v_a_1080_, v_x_1050_, v_a_1081_, v_x_1052_);
return v___x_1082_;
}
default: 
{
lean_object* v___x_1083_; 
lean_dec(v_h__5_1057_);
lean_dec(v_h__2_1054_);
v___x_1083_ = lean_apply_10(v_h__7_1059_, v_x_1049_, v_x_1050_, v_x_1051_, v_x_1052_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_1083_;
}
}
}
case 5:
{
lean_dec(v_h__5_1057_);
lean_dec(v_h__4_1056_);
lean_dec(v_h__3_1055_);
lean_dec(v_h__1_1053_);
switch(lean_obj_tag(v_x_1051_))
{
case 1:
{
lean_object* v_a_1084_; lean_object* v___x_1085_; 
lean_dec(v_h__7_1059_);
lean_dec(v_h__6_1058_);
v_a_1084_ = lean_ctor_get(v_x_1051_, 0);
lean_inc(v_a_1084_);
lean_dec_ref_known(v_x_1051_, 1);
v___x_1085_ = lean_apply_5(v_h__2_1054_, v_x_1049_, v_x_1050_, v_a_1084_, v_x_1052_, lean_box(0));
return v___x_1085_;
}
case 5:
{
lean_object* v_a_1086_; lean_object* v_a_1087_; lean_object* v___x_1088_; 
lean_dec(v_h__7_1059_);
lean_dec(v_h__2_1054_);
v_a_1086_ = lean_ctor_get(v_x_1049_, 0);
lean_inc(v_a_1086_);
lean_dec_ref_known(v_x_1049_, 1);
v_a_1087_ = lean_ctor_get(v_x_1051_, 0);
lean_inc(v_a_1087_);
lean_dec_ref_known(v_x_1051_, 1);
v___x_1088_ = lean_apply_4(v_h__6_1058_, v_a_1086_, v_x_1050_, v_a_1087_, v_x_1052_);
return v___x_1088_;
}
default: 
{
lean_object* v___x_1089_; 
lean_dec(v_h__6_1058_);
lean_dec(v_h__2_1054_);
v___x_1089_ = lean_apply_10(v_h__7_1059_, v_x_1049_, v_x_1050_, v_x_1051_, v_x_1052_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_1089_;
}
}
}
default: 
{
lean_dec(v_h__6_1058_);
lean_dec(v_h__5_1057_);
lean_dec(v_h__4_1056_);
lean_dec(v_h__3_1055_);
lean_dec(v_h__1_1053_);
if (lean_obj_tag(v_x_1051_) == 1)
{
lean_object* v_a_1090_; lean_object* v___x_1091_; 
lean_dec(v_h__7_1059_);
v_a_1090_ = lean_ctor_get(v_x_1051_, 0);
lean_inc(v_a_1090_);
lean_dec_ref_known(v_x_1051_, 1);
v___x_1091_ = lean_apply_5(v_h__2_1054_, v_x_1049_, v_x_1050_, v_a_1090_, v_x_1052_, lean_box(0));
return v___x_1091_;
}
else
{
lean_object* v___x_1092_; 
lean_dec(v_h__2_1054_);
v___x_1092_ = lean_apply_10(v_h__7_1059_, v_x_1049_, v_x_1050_, v_x_1051_, v_x_1052_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_1092_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Level_normLt(lean_object* v_l_u2081_1093_, lean_object* v_l_u2082_1094_){
_start:
{
lean_object* v___x_1095_; uint8_t v___x_1096_; 
v___x_1095_ = lean_unsigned_to_nat(0u);
v___x_1096_ = l_Lean_Level_normLtAux(v_l_u2081_1093_, v___x_1095_, v_l_u2082_1094_, v___x_1095_);
return v___x_1096_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_normLt___boxed(lean_object* v_l_u2081_1097_, lean_object* v_l_u2082_1098_){
_start:
{
uint8_t v_res_1099_; lean_object* v_r_1100_; 
v_res_1099_ = l_Lean_Level_normLt(v_l_u2081_1097_, v_l_u2082_1098_);
lean_dec(v_l_u2082_1098_);
lean_dec(v_l_u2081_1097_);
v_r_1100_ = lean_box(v_res_1099_);
return v_r_1100_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_isAlreadyNormalizedCheap(lean_object* v_x_1101_){
_start:
{
switch(lean_obj_tag(v_x_1101_))
{
case 0:
{
uint8_t v___x_1102_; 
v___x_1102_ = 1;
return v___x_1102_;
}
case 4:
{
uint8_t v___x_1103_; 
v___x_1103_ = 1;
return v___x_1103_;
}
case 5:
{
uint8_t v___x_1104_; 
v___x_1104_ = 1;
return v___x_1104_;
}
case 1:
{
lean_object* v_a_1105_; 
v_a_1105_ = lean_ctor_get(v_x_1101_, 0);
v_x_1101_ = v_a_1105_;
goto _start;
}
default: 
{
uint8_t v___x_1107_; 
v___x_1107_ = 0;
return v___x_1107_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_isAlreadyNormalizedCheap___boxed(lean_object* v_x_1108_){
_start:
{
uint8_t v_res_1109_; lean_object* v_r_1110_; 
v_res_1109_ = l_Lean_Level_isAlreadyNormalizedCheap(v_x_1108_);
lean_dec(v_x_1108_);
v_r_1110_ = lean_box(v_res_1109_);
return v_r_1110_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_mkIMaxAux(lean_object* v_x_1111_, lean_object* v_x_1112_){
_start:
{
lean_object* v_u_u2081_1114_; lean_object* v_u_u2082_1115_; 
if (lean_obj_tag(v_x_1112_) == 0)
{
lean_dec(v_x_1111_);
return v_x_1112_;
}
else
{
switch(lean_obj_tag(v_x_1111_))
{
case 0:
{
return v_x_1112_;
}
case 1:
{
lean_object* v_a_1118_; 
v_a_1118_ = lean_ctor_get(v_x_1111_, 0);
if (lean_obj_tag(v_a_1118_) == 0)
{
lean_dec_ref_known(v_x_1111_, 1);
return v_x_1112_;
}
else
{
v_u_u2081_1114_ = v_x_1111_;
v_u_u2082_1115_ = v_x_1112_;
goto v___jp_1113_;
}
}
default: 
{
v_u_u2081_1114_ = v_x_1111_;
v_u_u2082_1115_ = v_x_1112_;
goto v___jp_1113_;
}
}
}
v___jp_1113_:
{
uint8_t v___x_1116_; 
v___x_1116_ = lean_level_eq(v_u_u2081_1114_, v_u_u2082_1115_);
if (v___x_1116_ == 0)
{
lean_object* v___x_1117_; 
v___x_1117_ = l_Lean_Level_imax___override(v_u_u2081_1114_, v_u_u2082_1115_);
return v___x_1117_;
}
else
{
lean_dec(v_u_u2082_1115_);
return v_u_u2081_1114_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_getMaxArgsAux(lean_object* v_normalize_1119_, lean_object* v_x_1120_, uint8_t v_x_1121_, lean_object* v_x_1122_){
_start:
{
if (lean_obj_tag(v_x_1120_) == 2)
{
lean_object* v_a_1123_; lean_object* v_a_1124_; lean_object* v___x_1125_; 
v_a_1123_ = lean_ctor_get(v_x_1120_, 0);
lean_inc(v_a_1123_);
v_a_1124_ = lean_ctor_get(v_x_1120_, 1);
lean_inc(v_a_1124_);
lean_dec_ref_known(v_x_1120_, 2);
lean_inc_ref(v_normalize_1119_);
v___x_1125_ = l___private_Lean_Level_0__Lean_Level_getMaxArgsAux(v_normalize_1119_, v_a_1123_, v_x_1121_, v_x_1122_);
v_x_1120_ = v_a_1124_;
v_x_1122_ = v___x_1125_;
goto _start;
}
else
{
if (v_x_1121_ == 0)
{
lean_object* v___x_1127_; uint8_t v___x_1128_; 
lean_inc_ref(v_normalize_1119_);
v___x_1127_ = lean_apply_1(v_normalize_1119_, v_x_1120_);
v___x_1128_ = 1;
v_x_1120_ = v___x_1127_;
v_x_1121_ = v___x_1128_;
goto _start;
}
else
{
lean_object* v___x_1130_; 
lean_dec_ref(v_normalize_1119_);
v___x_1130_ = lean_array_push(v_x_1122_, v_x_1120_);
return v___x_1130_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_getMaxArgsAux___boxed(lean_object* v_normalize_1131_, lean_object* v_x_1132_, lean_object* v_x_1133_, lean_object* v_x_1134_){
_start:
{
uint8_t v_x_36__boxed_1135_; lean_object* v_res_1136_; 
v_x_36__boxed_1135_ = lean_unbox(v_x_1133_);
v_res_1136_ = l___private_Lean_Level_0__Lean_Level_getMaxArgsAux(v_normalize_1131_, v_x_1132_, v_x_36__boxed_1135_, v_x_1134_);
return v_res_1136_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_accMax(lean_object* v_result_1137_, lean_object* v_prev_1138_, lean_object* v_offset_1139_){
_start:
{
uint8_t v___x_1140_; 
v___x_1140_ = l_Lean_Level_isZero(v_result_1137_);
if (v___x_1140_ == 0)
{
lean_object* v___x_1141_; lean_object* v___x_1142_; 
v___x_1141_ = l_Lean_Level_addOffsetAux(v_offset_1139_, v_prev_1138_);
v___x_1142_ = l_Lean_Level_max___override(v_result_1137_, v___x_1141_);
return v___x_1142_;
}
else
{
lean_object* v___x_1143_; 
lean_dec(v_result_1137_);
v___x_1143_ = l_Lean_Level_addOffsetAux(v_offset_1139_, v_prev_1138_);
return v___x_1143_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_mkMaxAux(lean_object* v_lvls_1144_, lean_object* v_extraK_1145_, lean_object* v_i_1146_, lean_object* v_prev_1147_, lean_object* v_prevK_1148_, lean_object* v_result_1149_){
_start:
{
lean_object* v___x_1150_; uint8_t v___x_1151_; 
v___x_1150_ = lean_array_get_size(v_lvls_1144_);
v___x_1151_ = lean_nat_dec_lt(v_i_1146_, v___x_1150_);
if (v___x_1151_ == 0)
{
lean_object* v___x_1152_; lean_object* v___x_1153_; 
lean_dec(v_i_1146_);
v___x_1152_ = lean_nat_add(v_extraK_1145_, v_prevK_1148_);
lean_dec(v_prevK_1148_);
v___x_1153_ = l___private_Lean_Level_0__Lean_Level_accMax(v_result_1149_, v_prev_1147_, v___x_1152_);
return v___x_1153_;
}
else
{
lean_object* v_lvl_1154_; lean_object* v_curr_1155_; lean_object* v_currK_1156_; uint8_t v___x_1157_; 
v_lvl_1154_ = lean_array_fget_borrowed(v_lvls_1144_, v_i_1146_);
v_curr_1155_ = l_Lean_Level_getLevelOffset(v_lvl_1154_);
v_currK_1156_ = l_Lean_Level_getOffset(v_lvl_1154_);
v___x_1157_ = lean_level_eq(v_curr_1155_, v_prev_1147_);
if (v___x_1157_ == 0)
{
lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; 
v___x_1158_ = lean_unsigned_to_nat(1u);
v___x_1159_ = lean_nat_add(v_i_1146_, v___x_1158_);
lean_dec(v_i_1146_);
v___x_1160_ = lean_nat_add(v_extraK_1145_, v_prevK_1148_);
lean_dec(v_prevK_1148_);
v___x_1161_ = l___private_Lean_Level_0__Lean_Level_accMax(v_result_1149_, v_prev_1147_, v___x_1160_);
v_i_1146_ = v___x_1159_;
v_prev_1147_ = v_curr_1155_;
v_prevK_1148_ = v_currK_1156_;
v_result_1149_ = v___x_1161_;
goto _start;
}
else
{
lean_object* v___x_1163_; lean_object* v___x_1164_; 
lean_dec(v_prevK_1148_);
lean_dec(v_prev_1147_);
v___x_1163_ = lean_unsigned_to_nat(1u);
v___x_1164_ = lean_nat_add(v_i_1146_, v___x_1163_);
lean_dec(v_i_1146_);
v_i_1146_ = v___x_1164_;
v_prev_1147_ = v_curr_1155_;
v_prevK_1148_ = v_currK_1156_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_mkMaxAux___boxed(lean_object* v_lvls_1166_, lean_object* v_extraK_1167_, lean_object* v_i_1168_, lean_object* v_prev_1169_, lean_object* v_prevK_1170_, lean_object* v_result_1171_){
_start:
{
lean_object* v_res_1172_; 
v_res_1172_ = l___private_Lean_Level_0__Lean_Level_mkMaxAux(v_lvls_1166_, v_extraK_1167_, v_i_1168_, v_prev_1169_, v_prevK_1170_, v_result_1171_);
lean_dec(v_extraK_1167_);
lean_dec_ref(v_lvls_1166_);
return v_res_1172_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_skipExplicit(lean_object* v_lvls_1173_, lean_object* v_i_1174_){
_start:
{
lean_object* v___x_1175_; uint8_t v___x_1176_; 
v___x_1175_ = lean_array_get_size(v_lvls_1173_);
v___x_1176_ = lean_nat_dec_lt(v_i_1174_, v___x_1175_);
if (v___x_1176_ == 0)
{
return v_i_1174_;
}
else
{
lean_object* v_lvl_1177_; lean_object* v___x_1178_; uint8_t v___x_1179_; 
v_lvl_1177_ = lean_array_fget_borrowed(v_lvls_1173_, v_i_1174_);
v___x_1178_ = l_Lean_Level_getLevelOffset(v_lvl_1177_);
v___x_1179_ = l_Lean_Level_isZero(v___x_1178_);
lean_dec(v___x_1178_);
if (v___x_1179_ == 0)
{
return v_i_1174_;
}
else
{
lean_object* v___x_1180_; lean_object* v___x_1181_; 
v___x_1180_ = lean_unsigned_to_nat(1u);
v___x_1181_ = lean_nat_add(v_i_1174_, v___x_1180_);
lean_dec(v_i_1174_);
v_i_1174_ = v___x_1181_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_skipExplicit___boxed(lean_object* v_lvls_1183_, lean_object* v_i_1184_){
_start:
{
lean_object* v_res_1185_; 
v_res_1185_ = l___private_Lean_Level_0__Lean_Level_skipExplicit(v_lvls_1183_, v_i_1184_);
lean_dec_ref(v_lvls_1183_);
return v_res_1185_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Level_0__Lean_Level_isExplicitSubsumedAux(lean_object* v_lvls_1186_, lean_object* v_maxExplicit_1187_, lean_object* v_i_1188_){
_start:
{
lean_object* v___x_1189_; uint8_t v___x_1190_; 
v___x_1189_ = lean_array_get_size(v_lvls_1186_);
v___x_1190_ = lean_nat_dec_lt(v_i_1188_, v___x_1189_);
if (v___x_1190_ == 0)
{
lean_dec(v_i_1188_);
return v___x_1190_;
}
else
{
lean_object* v_lvl_1191_; lean_object* v___x_1192_; uint8_t v___x_1193_; 
v_lvl_1191_ = lean_array_fget_borrowed(v_lvls_1186_, v_i_1188_);
v___x_1192_ = l_Lean_Level_getOffset(v_lvl_1191_);
v___x_1193_ = lean_nat_dec_le(v_maxExplicit_1187_, v___x_1192_);
lean_dec(v___x_1192_);
if (v___x_1193_ == 0)
{
lean_object* v___x_1194_; lean_object* v___x_1195_; 
v___x_1194_ = lean_unsigned_to_nat(1u);
v___x_1195_ = lean_nat_add(v_i_1188_, v___x_1194_);
lean_dec(v_i_1188_);
v_i_1188_ = v___x_1195_;
goto _start;
}
else
{
lean_dec(v_i_1188_);
return v___x_1193_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_isExplicitSubsumedAux___boxed(lean_object* v_lvls_1197_, lean_object* v_maxExplicit_1198_, lean_object* v_i_1199_){
_start:
{
uint8_t v_res_1200_; lean_object* v_r_1201_; 
v_res_1200_ = l___private_Lean_Level_0__Lean_Level_isExplicitSubsumedAux(v_lvls_1197_, v_maxExplicit_1198_, v_i_1199_);
lean_dec(v_maxExplicit_1198_);
lean_dec_ref(v_lvls_1197_);
v_r_1201_ = lean_box(v_res_1200_);
return v_r_1201_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Level_0__Lean_Level_isExplicitSubsumed(lean_object* v_lvls_1202_, lean_object* v_firstNonExplicit_1203_){
_start:
{
lean_object* v___x_1204_; uint8_t v___x_1205_; 
v___x_1204_ = lean_unsigned_to_nat(0u);
v___x_1205_ = lean_nat_dec_eq(v_firstNonExplicit_1203_, v___x_1204_);
if (v___x_1205_ == 0)
{
lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v_max_1210_; uint8_t v___x_1211_; 
v___x_1206_ = lean_box(0);
v___x_1207_ = lean_unsigned_to_nat(1u);
v___x_1208_ = lean_nat_sub(v_firstNonExplicit_1203_, v___x_1207_);
v___x_1209_ = lean_array_get_borrowed(v___x_1206_, v_lvls_1202_, v___x_1208_);
lean_dec(v___x_1208_);
v_max_1210_ = l_Lean_Level_getOffset(v___x_1209_);
v___x_1211_ = l___private_Lean_Level_0__Lean_Level_isExplicitSubsumedAux(v_lvls_1202_, v_max_1210_, v_firstNonExplicit_1203_);
lean_dec(v_max_1210_);
return v___x_1211_;
}
else
{
uint8_t v___x_1212_; 
lean_dec(v_firstNonExplicit_1203_);
v___x_1212_ = 0;
return v___x_1212_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_isExplicitSubsumed___boxed(lean_object* v_lvls_1213_, lean_object* v_firstNonExplicit_1214_){
_start:
{
uint8_t v_res_1215_; lean_object* v_r_1216_; 
v_res_1215_ = l___private_Lean_Level_0__Lean_Level_isExplicitSubsumed(v_lvls_1213_, v_firstNonExplicit_1214_);
lean_dec_ref(v_lvls_1213_);
v_r_1216_ = lean_box(v_res_1215_);
return v_r_1216_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Level_normalize_spec__2(lean_object* v_msg_1217_){
_start:
{
lean_object* v___x_1218_; lean_object* v___x_1219_; 
v___x_1218_ = lean_box(0);
v___x_1219_ = lean_panic_fn_borrowed(v___x_1218_, v_msg_1217_);
return v___x_1219_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1_spec__1___redArg(lean_object* v_hi_1220_, lean_object* v_pivot_1221_, lean_object* v_as_1222_, lean_object* v_i_1223_, lean_object* v_k_1224_){
_start:
{
uint8_t v___x_1225_; 
v___x_1225_ = lean_nat_dec_lt(v_k_1224_, v_hi_1220_);
if (v___x_1225_ == 0)
{
lean_object* v___x_1226_; lean_object* v___x_1227_; 
lean_dec(v_k_1224_);
v___x_1226_ = lean_array_fswap(v_as_1222_, v_i_1223_, v_hi_1220_);
v___x_1227_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1227_, 0, v_i_1223_);
lean_ctor_set(v___x_1227_, 1, v___x_1226_);
return v___x_1227_;
}
else
{
lean_object* v___x_1228_; uint8_t v___x_1229_; 
v___x_1228_ = lean_array_fget_borrowed(v_as_1222_, v_k_1224_);
v___x_1229_ = l_Lean_Level_normLt(v___x_1228_, v_pivot_1221_);
if (v___x_1229_ == 0)
{
lean_object* v___x_1230_; lean_object* v___x_1231_; 
v___x_1230_ = lean_unsigned_to_nat(1u);
v___x_1231_ = lean_nat_add(v_k_1224_, v___x_1230_);
lean_dec(v_k_1224_);
v_k_1224_ = v___x_1231_;
goto _start;
}
else
{
lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; 
v___x_1233_ = lean_array_fswap(v_as_1222_, v_i_1223_, v_k_1224_);
v___x_1234_ = lean_unsigned_to_nat(1u);
v___x_1235_ = lean_nat_add(v_i_1223_, v___x_1234_);
lean_dec(v_i_1223_);
v___x_1236_ = lean_nat_add(v_k_1224_, v___x_1234_);
lean_dec(v_k_1224_);
v_as_1222_ = v___x_1233_;
v_i_1223_ = v___x_1235_;
v_k_1224_ = v___x_1236_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1_spec__1___redArg___boxed(lean_object* v_hi_1238_, lean_object* v_pivot_1239_, lean_object* v_as_1240_, lean_object* v_i_1241_, lean_object* v_k_1242_){
_start:
{
lean_object* v_res_1243_; 
v_res_1243_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1_spec__1___redArg(v_hi_1238_, v_pivot_1239_, v_as_1240_, v_i_1241_, v_k_1242_);
lean_dec(v_pivot_1239_);
lean_dec(v_hi_1238_);
return v_res_1243_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1___redArg(lean_object* v_n_1244_, lean_object* v_as_1245_, lean_object* v_lo_1246_, lean_object* v_hi_1247_){
_start:
{
lean_object* v___y_1249_; uint8_t v___x_1259_; 
v___x_1259_ = lean_nat_dec_lt(v_lo_1246_, v_hi_1247_);
if (v___x_1259_ == 0)
{
lean_dec(v_lo_1246_);
return v_as_1245_;
}
else
{
lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v_mid_1262_; lean_object* v___y_1264_; lean_object* v___y_1270_; lean_object* v___x_1275_; lean_object* v___x_1276_; uint8_t v___x_1277_; 
v___x_1260_ = lean_nat_add(v_lo_1246_, v_hi_1247_);
v___x_1261_ = lean_unsigned_to_nat(1u);
v_mid_1262_ = lean_nat_shiftr(v___x_1260_, v___x_1261_);
lean_dec(v___x_1260_);
v___x_1275_ = lean_array_fget_borrowed(v_as_1245_, v_mid_1262_);
v___x_1276_ = lean_array_fget_borrowed(v_as_1245_, v_lo_1246_);
v___x_1277_ = l_Lean_Level_normLt(v___x_1275_, v___x_1276_);
if (v___x_1277_ == 0)
{
v___y_1270_ = v_as_1245_;
goto v___jp_1269_;
}
else
{
lean_object* v___x_1278_; 
v___x_1278_ = lean_array_fswap(v_as_1245_, v_lo_1246_, v_mid_1262_);
v___y_1270_ = v___x_1278_;
goto v___jp_1269_;
}
v___jp_1263_:
{
lean_object* v___x_1265_; lean_object* v___x_1266_; uint8_t v___x_1267_; 
v___x_1265_ = lean_array_fget_borrowed(v___y_1264_, v_mid_1262_);
v___x_1266_ = lean_array_fget_borrowed(v___y_1264_, v_hi_1247_);
v___x_1267_ = l_Lean_Level_normLt(v___x_1265_, v___x_1266_);
if (v___x_1267_ == 0)
{
lean_dec(v_mid_1262_);
v___y_1249_ = v___y_1264_;
goto v___jp_1248_;
}
else
{
lean_object* v___x_1268_; 
v___x_1268_ = lean_array_fswap(v___y_1264_, v_mid_1262_, v_hi_1247_);
lean_dec(v_mid_1262_);
v___y_1249_ = v___x_1268_;
goto v___jp_1248_;
}
}
v___jp_1269_:
{
lean_object* v___x_1271_; lean_object* v___x_1272_; uint8_t v___x_1273_; 
v___x_1271_ = lean_array_fget_borrowed(v___y_1270_, v_hi_1247_);
v___x_1272_ = lean_array_fget_borrowed(v___y_1270_, v_lo_1246_);
v___x_1273_ = l_Lean_Level_normLt(v___x_1271_, v___x_1272_);
if (v___x_1273_ == 0)
{
v___y_1264_ = v___y_1270_;
goto v___jp_1263_;
}
else
{
lean_object* v___x_1274_; 
v___x_1274_ = lean_array_fswap(v___y_1270_, v_lo_1246_, v_hi_1247_);
v___y_1264_ = v___x_1274_;
goto v___jp_1263_;
}
}
}
v___jp_1248_:
{
lean_object* v_pivot_1250_; lean_object* v___x_1251_; lean_object* v_fst_1252_; lean_object* v_snd_1253_; uint8_t v___x_1254_; 
v_pivot_1250_ = lean_array_fget(v___y_1249_, v_hi_1247_);
lean_inc_n(v_lo_1246_, 2);
v___x_1251_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1_spec__1___redArg(v_hi_1247_, v_pivot_1250_, v___y_1249_, v_lo_1246_, v_lo_1246_);
lean_dec(v_pivot_1250_);
v_fst_1252_ = lean_ctor_get(v___x_1251_, 0);
lean_inc(v_fst_1252_);
v_snd_1253_ = lean_ctor_get(v___x_1251_, 1);
lean_inc(v_snd_1253_);
lean_dec_ref(v___x_1251_);
v___x_1254_ = lean_nat_dec_le(v_hi_1247_, v_fst_1252_);
if (v___x_1254_ == 0)
{
lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; 
v___x_1255_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1___redArg(v_n_1244_, v_snd_1253_, v_lo_1246_, v_fst_1252_);
v___x_1256_ = lean_unsigned_to_nat(1u);
v___x_1257_ = lean_nat_add(v_fst_1252_, v___x_1256_);
lean_dec(v_fst_1252_);
v_as_1245_ = v___x_1255_;
v_lo_1246_ = v___x_1257_;
goto _start;
}
else
{
lean_dec(v_fst_1252_);
lean_dec(v_lo_1246_);
return v_snd_1253_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1___redArg___boxed(lean_object* v_n_1279_, lean_object* v_as_1280_, lean_object* v_lo_1281_, lean_object* v_hi_1282_){
_start:
{
lean_object* v_res_1283_; 
v_res_1283_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1___redArg(v_n_1279_, v_as_1280_, v_lo_1281_, v_hi_1282_);
lean_dec(v_hi_1282_);
lean_dec(v_n_1279_);
return v_res_1283_;
}
}
static lean_object* _init_l_Lean_Level_normalize___closed__3(void){
_start:
{
lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; 
v___x_1288_ = ((lean_object*)(l_Lean_Level_normalize___closed__2));
v___x_1289_ = lean_unsigned_to_nat(11u);
v___x_1290_ = lean_unsigned_to_nat(404u);
v___x_1291_ = ((lean_object*)(l_Lean_Level_normalize___closed__1));
v___x_1292_ = ((lean_object*)(l_Lean_Level_mvarId_x21___closed__0));
v___x_1293_ = l_mkPanicMessageWithDecl(v___x_1292_, v___x_1291_, v___x_1290_, v___x_1289_, v___x_1288_);
return v___x_1293_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_normalize(lean_object* v_l_1294_){
_start:
{
uint8_t v___x_1295_; 
v___x_1295_ = l_Lean_Level_isAlreadyNormalizedCheap(v_l_1294_);
if (v___x_1295_ == 0)
{
lean_object* v_k_1296_; lean_object* v_u_1297_; 
v_k_1296_ = l_Lean_Level_getOffset(v_l_1294_);
v_u_1297_ = l_Lean_Level_getLevelOffset(v_l_1294_);
switch(lean_obj_tag(v_u_1297_))
{
case 2:
{
lean_object* v_a_1298_; lean_object* v_a_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v_lvls_1302_; lean_object* v_lvls_1303_; lean_object* v___x_1304_; lean_object* v___y_1306_; lean_object* v___y_1307_; lean_object* v___y_1315_; lean_object* v___x_1319_; lean_object* v___y_1321_; lean_object* v___y_1322_; uint8_t v___x_1324_; 
v_a_1298_ = lean_ctor_get(v_u_1297_, 0);
lean_inc(v_a_1298_);
v_a_1299_ = lean_ctor_get(v_u_1297_, 1);
lean_inc(v_a_1299_);
lean_dec_ref_known(v_u_1297_, 2);
v___x_1300_ = lean_unsigned_to_nat(0u);
v___x_1301_ = ((lean_object*)(l_Lean_Level_normalize___closed__0));
v_lvls_1302_ = l___private_Lean_Level_0__Lean_Level_getMaxArgsAux___at___00Lean_Level_normalize_spec__0(v_a_1298_, v___x_1295_, v___x_1301_);
v_lvls_1303_ = l___private_Lean_Level_0__Lean_Level_getMaxArgsAux___at___00Lean_Level_normalize_spec__0(v_a_1299_, v___x_1295_, v_lvls_1302_);
v___x_1304_ = lean_unsigned_to_nat(1u);
v___x_1319_ = lean_array_get_size(v_lvls_1303_);
v___x_1324_ = lean_nat_dec_eq(v___x_1319_, v___x_1300_);
if (v___x_1324_ == 0)
{
lean_object* v___x_1325_; lean_object* v___y_1327_; uint8_t v___x_1329_; 
v___x_1325_ = lean_nat_sub(v___x_1319_, v___x_1304_);
v___x_1329_ = lean_nat_dec_le(v___x_1300_, v___x_1325_);
if (v___x_1329_ == 0)
{
lean_inc(v___x_1325_);
v___y_1327_ = v___x_1325_;
goto v___jp_1326_;
}
else
{
v___y_1327_ = v___x_1300_;
goto v___jp_1326_;
}
v___jp_1326_:
{
uint8_t v___x_1328_; 
v___x_1328_ = lean_nat_dec_le(v___y_1327_, v___x_1325_);
if (v___x_1328_ == 0)
{
lean_dec(v___x_1325_);
lean_inc(v___y_1327_);
v___y_1321_ = v___y_1327_;
v___y_1322_ = v___y_1327_;
goto v___jp_1320_;
}
else
{
v___y_1321_ = v___y_1327_;
v___y_1322_ = v___x_1325_;
goto v___jp_1320_;
}
}
}
else
{
v___y_1315_ = v_lvls_1303_;
goto v___jp_1314_;
}
v___jp_1305_:
{
lean_object* v___x_1308_; lean_object* v_lvl_u2081_1309_; lean_object* v_prev_1310_; lean_object* v_prevK_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; 
v___x_1308_ = lean_box(0);
v_lvl_u2081_1309_ = lean_array_get_borrowed(v___x_1308_, v___y_1306_, v___y_1307_);
v_prev_1310_ = l_Lean_Level_getLevelOffset(v_lvl_u2081_1309_);
v_prevK_1311_ = l_Lean_Level_getOffset(v_lvl_u2081_1309_);
v___x_1312_ = lean_nat_add(v___y_1307_, v___x_1304_);
lean_dec(v___y_1307_);
v___x_1313_ = l___private_Lean_Level_0__Lean_Level_mkMaxAux(v___y_1306_, v_k_1296_, v___x_1312_, v_prev_1310_, v_prevK_1311_, v___x_1308_);
lean_dec(v_k_1296_);
lean_dec_ref(v___y_1306_);
return v___x_1313_;
}
v___jp_1314_:
{
lean_object* v_firstNonExplicit_1316_; uint8_t v___x_1317_; 
v_firstNonExplicit_1316_ = l___private_Lean_Level_0__Lean_Level_skipExplicit(v___y_1315_, v___x_1300_);
lean_inc(v_firstNonExplicit_1316_);
v___x_1317_ = l___private_Lean_Level_0__Lean_Level_isExplicitSubsumed(v___y_1315_, v_firstNonExplicit_1316_);
if (v___x_1317_ == 0)
{
lean_object* v___x_1318_; 
v___x_1318_ = lean_nat_sub(v_firstNonExplicit_1316_, v___x_1304_);
lean_dec(v_firstNonExplicit_1316_);
v___y_1306_ = v___y_1315_;
v___y_1307_ = v___x_1318_;
goto v___jp_1305_;
}
else
{
v___y_1306_ = v___y_1315_;
v___y_1307_ = v_firstNonExplicit_1316_;
goto v___jp_1305_;
}
}
v___jp_1320_:
{
lean_object* v___x_1323_; 
v___x_1323_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1___redArg(v___x_1319_, v_lvls_1303_, v___y_1321_, v___y_1322_);
lean_dec(v___y_1322_);
v___y_1315_ = v___x_1323_;
goto v___jp_1314_;
}
}
case 3:
{
lean_object* v_a_1330_; lean_object* v_a_1331_; uint8_t v___x_1332_; 
v_a_1330_ = lean_ctor_get(v_u_1297_, 0);
lean_inc(v_a_1330_);
v_a_1331_ = lean_ctor_get(v_u_1297_, 1);
lean_inc(v_a_1331_);
lean_dec_ref_known(v_u_1297_, 2);
v___x_1332_ = l_Lean_Level_isNeverZero(v_a_1331_);
if (v___x_1332_ == 0)
{
lean_object* v_l_u2081_1333_; lean_object* v_l_u2082_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; 
v_l_u2081_1333_ = l_Lean_Level_normalize(v_a_1330_);
lean_dec(v_a_1330_);
v_l_u2082_1334_ = l_Lean_Level_normalize(v_a_1331_);
lean_dec(v_a_1331_);
v___x_1335_ = l___private_Lean_Level_0__Lean_Level_mkIMaxAux(v_l_u2081_1333_, v_l_u2082_1334_);
v___x_1336_ = l_Lean_Level_addOffsetAux(v_k_1296_, v___x_1335_);
return v___x_1336_;
}
else
{
lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; 
v___x_1337_ = l_Lean_Level_max___override(v_a_1330_, v_a_1331_);
v___x_1338_ = l_Lean_Level_normalize(v___x_1337_);
lean_dec(v___x_1337_);
v___x_1339_ = l_Lean_Level_addOffsetAux(v_k_1296_, v___x_1338_);
return v___x_1339_;
}
}
default: 
{
lean_object* v___x_1340_; lean_object* v___x_1341_; 
lean_dec(v_u_1297_);
lean_dec(v_k_1296_);
v___x_1340_ = lean_obj_once(&l_Lean_Level_normalize___closed__3, &l_Lean_Level_normalize___closed__3_once, _init_l_Lean_Level_normalize___closed__3);
v___x_1341_ = l_panic___at___00Lean_Level_normalize_spec__2(v___x_1340_);
return v___x_1341_;
}
}
}
else
{
lean_inc(v_l_1294_);
return v_l_1294_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_getMaxArgsAux___at___00Lean_Level_normalize_spec__0(lean_object* v_x_1342_, uint8_t v_x_1343_, lean_object* v_x_1344_){
_start:
{
if (lean_obj_tag(v_x_1342_) == 2)
{
lean_object* v_a_1345_; lean_object* v_a_1346_; lean_object* v___x_1347_; 
v_a_1345_ = lean_ctor_get(v_x_1342_, 0);
lean_inc(v_a_1345_);
v_a_1346_ = lean_ctor_get(v_x_1342_, 1);
lean_inc(v_a_1346_);
lean_dec_ref_known(v_x_1342_, 2);
v___x_1347_ = l___private_Lean_Level_0__Lean_Level_getMaxArgsAux___at___00Lean_Level_normalize_spec__0(v_a_1345_, v_x_1343_, v_x_1344_);
v_x_1342_ = v_a_1346_;
v_x_1344_ = v___x_1347_;
goto _start;
}
else
{
if (v_x_1343_ == 0)
{
lean_object* v___x_1349_; uint8_t v___x_1350_; 
v___x_1349_ = l_Lean_Level_normalize(v_x_1342_);
lean_dec(v_x_1342_);
v___x_1350_ = 1;
v_x_1342_ = v___x_1349_;
v_x_1343_ = v___x_1350_;
goto _start;
}
else
{
lean_object* v___x_1352_; 
v___x_1352_ = lean_array_push(v_x_1344_, v_x_1342_);
return v___x_1352_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_getMaxArgsAux___at___00Lean_Level_normalize_spec__0___boxed(lean_object* v_x_1353_, lean_object* v_x_1354_, lean_object* v_x_1355_){
_start:
{
uint8_t v_x_676__boxed_1356_; lean_object* v_res_1357_; 
v_x_676__boxed_1356_ = lean_unbox(v_x_1354_);
v_res_1357_ = l___private_Lean_Level_0__Lean_Level_getMaxArgsAux___at___00Lean_Level_normalize_spec__0(v_x_1353_, v_x_676__boxed_1356_, v_x_1355_);
return v_res_1357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_normalize___boxed(lean_object* v_l_1358_){
_start:
{
lean_object* v_res_1359_; 
v_res_1359_ = l_Lean_Level_normalize(v_l_1358_);
lean_dec(v_l_1358_);
return v_res_1359_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1(lean_object* v_n_1360_, lean_object* v_as_1361_, lean_object* v_lo_1362_, lean_object* v_hi_1363_, lean_object* v_w_1364_, lean_object* v_hlo_1365_, lean_object* v_hhi_1366_){
_start:
{
lean_object* v___x_1367_; 
v___x_1367_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1___redArg(v_n_1360_, v_as_1361_, v_lo_1362_, v_hi_1363_);
return v___x_1367_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1___boxed(lean_object* v_n_1368_, lean_object* v_as_1369_, lean_object* v_lo_1370_, lean_object* v_hi_1371_, lean_object* v_w_1372_, lean_object* v_hlo_1373_, lean_object* v_hhi_1374_){
_start:
{
lean_object* v_res_1375_; 
v_res_1375_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1(v_n_1368_, v_as_1369_, v_lo_1370_, v_hi_1371_, v_w_1372_, v_hlo_1373_, v_hhi_1374_);
lean_dec(v_hi_1371_);
lean_dec(v_n_1368_);
return v_res_1375_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1_spec__1(lean_object* v_n_1376_, lean_object* v_lo_1377_, lean_object* v_hi_1378_, lean_object* v_hhi_1379_, lean_object* v_pivot_1380_, lean_object* v_as_1381_, lean_object* v_i_1382_, lean_object* v_k_1383_, lean_object* v_ilo_1384_, lean_object* v_ik_1385_, lean_object* v_w_1386_){
_start:
{
lean_object* v___x_1387_; 
v___x_1387_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1_spec__1___redArg(v_hi_1378_, v_pivot_1380_, v_as_1381_, v_i_1382_, v_k_1383_);
return v___x_1387_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1_spec__1___boxed(lean_object* v_n_1388_, lean_object* v_lo_1389_, lean_object* v_hi_1390_, lean_object* v_hhi_1391_, lean_object* v_pivot_1392_, lean_object* v_as_1393_, lean_object* v_i_1394_, lean_object* v_k_1395_, lean_object* v_ilo_1396_, lean_object* v_ik_1397_, lean_object* v_w_1398_){
_start:
{
lean_object* v_res_1399_; 
v_res_1399_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1_spec__1(v_n_1388_, v_lo_1389_, v_hi_1390_, v_hhi_1391_, v_pivot_1392_, v_as_1393_, v_i_1394_, v_k_1395_, v_ilo_1396_, v_ik_1397_, v_w_1398_);
lean_dec(v_pivot_1392_);
lean_dec(v_hi_1390_);
lean_dec(v_lo_1389_);
lean_dec(v_n_1388_);
return v_res_1399_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_isEquiv(lean_object* v_u_1400_, lean_object* v_v_1401_){
_start:
{
uint8_t v___x_1402_; 
v___x_1402_ = lean_level_eq(v_u_1400_, v_v_1401_);
if (v___x_1402_ == 0)
{
lean_object* v___x_1403_; lean_object* v___x_1404_; uint8_t v___x_1405_; 
v___x_1403_ = l_Lean_Level_normalize(v_u_1400_);
v___x_1404_ = l_Lean_Level_normalize(v_v_1401_);
v___x_1405_ = lean_level_eq(v___x_1403_, v___x_1404_);
lean_dec(v___x_1404_);
lean_dec(v___x_1403_);
return v___x_1405_;
}
else
{
return v___x_1402_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_isEquiv___boxed(lean_object* v_u_1406_, lean_object* v_v_1407_){
_start:
{
uint8_t v_res_1408_; lean_object* v_r_1409_; 
v_res_1408_ = l_Lean_Level_isEquiv(v_u_1406_, v_v_1407_);
lean_dec(v_v_1407_);
lean_dec(v_u_1406_);
v_r_1409_ = lean_box(v_res_1408_);
return v_r_1409_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_dec(lean_object* v_x_1410_){
_start:
{
lean_object* v_l_u2081_1412_; lean_object* v_l_u2082_1413_; 
switch(lean_obj_tag(v_x_1410_))
{
case 0:
{
lean_object* v___x_1426_; 
v___x_1426_ = lean_box(0);
return v___x_1426_;
}
case 1:
{
lean_object* v_a_1427_; lean_object* v___x_1428_; 
v_a_1427_ = lean_ctor_get(v_x_1410_, 0);
lean_inc(v_a_1427_);
v___x_1428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1428_, 0, v_a_1427_);
return v___x_1428_;
}
case 2:
{
lean_object* v_a_1429_; lean_object* v_a_1430_; 
v_a_1429_ = lean_ctor_get(v_x_1410_, 0);
v_a_1430_ = lean_ctor_get(v_x_1410_, 1);
v_l_u2081_1412_ = v_a_1429_;
v_l_u2082_1413_ = v_a_1430_;
goto v___jp_1411_;
}
case 3:
{
lean_object* v_a_1431_; lean_object* v_a_1432_; 
v_a_1431_ = lean_ctor_get(v_x_1410_, 0);
v_a_1432_ = lean_ctor_get(v_x_1410_, 1);
v_l_u2081_1412_ = v_a_1431_;
v_l_u2082_1413_ = v_a_1432_;
goto v___jp_1411_;
}
default: 
{
lean_object* v___x_1433_; 
v___x_1433_ = lean_box(0);
return v___x_1433_;
}
}
v___jp_1411_:
{
lean_object* v___x_1414_; 
v___x_1414_ = l_Lean_Level_dec(v_l_u2081_1412_);
if (lean_obj_tag(v___x_1414_) == 0)
{
return v___x_1414_;
}
else
{
lean_object* v_val_1415_; lean_object* v___x_1416_; 
v_val_1415_ = lean_ctor_get(v___x_1414_, 0);
lean_inc(v_val_1415_);
lean_dec_ref_known(v___x_1414_, 1);
v___x_1416_ = l_Lean_Level_dec(v_l_u2082_1413_);
if (lean_obj_tag(v___x_1416_) == 0)
{
lean_dec(v_val_1415_);
return v___x_1416_;
}
else
{
lean_object* v_val_1417_; lean_object* v___x_1419_; uint8_t v_isShared_1420_; uint8_t v_isSharedCheck_1425_; 
v_val_1417_ = lean_ctor_get(v___x_1416_, 0);
v_isSharedCheck_1425_ = !lean_is_exclusive(v___x_1416_);
if (v_isSharedCheck_1425_ == 0)
{
v___x_1419_ = v___x_1416_;
v_isShared_1420_ = v_isSharedCheck_1425_;
goto v_resetjp_1418_;
}
else
{
lean_inc(v_val_1417_);
lean_dec(v___x_1416_);
v___x_1419_ = lean_box(0);
v_isShared_1420_ = v_isSharedCheck_1425_;
goto v_resetjp_1418_;
}
v_resetjp_1418_:
{
lean_object* v___x_1421_; lean_object* v___x_1423_; 
v___x_1421_ = l_Lean_Level_max___override(v_val_1415_, v_val_1417_);
if (v_isShared_1420_ == 0)
{
lean_ctor_set(v___x_1419_, 0, v___x_1421_);
v___x_1423_ = v___x_1419_;
goto v_reusejp_1422_;
}
else
{
lean_object* v_reuseFailAlloc_1424_; 
v_reuseFailAlloc_1424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1424_, 0, v___x_1421_);
v___x_1423_ = v_reuseFailAlloc_1424_;
goto v_reusejp_1422_;
}
v_reusejp_1422_:
{
return v___x_1423_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_dec___boxed(lean_object* v_x_1434_){
_start:
{
lean_object* v_res_1435_; 
v_res_1435_ = l_Lean_Level_dec(v_x_1434_);
lean_dec(v_x_1434_);
return v_res_1435_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_ctorIdx(lean_object* v_x_1436_){
_start:
{
switch(lean_obj_tag(v_x_1436_))
{
case 0:
{
lean_object* v___x_1437_; 
v___x_1437_ = lean_unsigned_to_nat(0u);
return v___x_1437_;
}
case 1:
{
lean_object* v___x_1438_; 
v___x_1438_ = lean_unsigned_to_nat(1u);
return v___x_1438_;
}
case 2:
{
lean_object* v___x_1439_; 
v___x_1439_ = lean_unsigned_to_nat(2u);
return v___x_1439_;
}
case 3:
{
lean_object* v___x_1440_; 
v___x_1440_ = lean_unsigned_to_nat(3u);
return v___x_1440_;
}
default: 
{
lean_object* v___x_1441_; 
v___x_1441_ = lean_unsigned_to_nat(4u);
return v___x_1441_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_ctorIdx___boxed(lean_object* v_x_1442_){
_start:
{
lean_object* v_res_1443_; 
v_res_1443_ = l_Lean_Level_PP_Result_ctorIdx(v_x_1442_);
lean_dec_ref(v_x_1442_);
return v_res_1443_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_ctorElim___redArg(lean_object* v_t_1444_, lean_object* v_k_1445_){
_start:
{
if (lean_obj_tag(v_t_1444_) == 2)
{
lean_object* v_a_1446_; lean_object* v_a_1447_; lean_object* v___x_1448_; 
v_a_1446_ = lean_ctor_get(v_t_1444_, 0);
lean_inc_ref(v_a_1446_);
v_a_1447_ = lean_ctor_get(v_t_1444_, 1);
lean_inc(v_a_1447_);
lean_dec_ref_known(v_t_1444_, 2);
v___x_1448_ = lean_apply_2(v_k_1445_, v_a_1446_, v_a_1447_);
return v___x_1448_;
}
else
{
lean_object* v_a_1449_; lean_object* v___x_1450_; 
v_a_1449_ = lean_ctor_get(v_t_1444_, 0);
lean_inc(v_a_1449_);
lean_dec_ref(v_t_1444_);
v___x_1450_ = lean_apply_1(v_k_1445_, v_a_1449_);
return v___x_1450_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_ctorElim(lean_object* v_motive__1_1451_, lean_object* v_ctorIdx_1452_, lean_object* v_t_1453_, lean_object* v_h_1454_, lean_object* v_k_1455_){
_start:
{
lean_object* v___x_1456_; 
v___x_1456_ = l_Lean_Level_PP_Result_ctorElim___redArg(v_t_1453_, v_k_1455_);
return v___x_1456_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_ctorElim___boxed(lean_object* v_motive__1_1457_, lean_object* v_ctorIdx_1458_, lean_object* v_t_1459_, lean_object* v_h_1460_, lean_object* v_k_1461_){
_start:
{
lean_object* v_res_1462_; 
v_res_1462_ = l_Lean_Level_PP_Result_ctorElim(v_motive__1_1457_, v_ctorIdx_1458_, v_t_1459_, v_h_1460_, v_k_1461_);
lean_dec(v_ctorIdx_1458_);
return v_res_1462_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_leaf_elim___redArg(lean_object* v_t_1463_, lean_object* v_leaf_1464_){
_start:
{
lean_object* v___x_1465_; 
v___x_1465_ = l_Lean_Level_PP_Result_ctorElim___redArg(v_t_1463_, v_leaf_1464_);
return v___x_1465_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_leaf_elim(lean_object* v_motive__1_1466_, lean_object* v_t_1467_, lean_object* v_h_1468_, lean_object* v_leaf_1469_){
_start:
{
lean_object* v___x_1470_; 
v___x_1470_ = l_Lean_Level_PP_Result_ctorElim___redArg(v_t_1467_, v_leaf_1469_);
return v___x_1470_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_num_elim___redArg(lean_object* v_t_1471_, lean_object* v_num_1472_){
_start:
{
lean_object* v___x_1473_; 
v___x_1473_ = l_Lean_Level_PP_Result_ctorElim___redArg(v_t_1471_, v_num_1472_);
return v___x_1473_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_num_elim(lean_object* v_motive__1_1474_, lean_object* v_t_1475_, lean_object* v_h_1476_, lean_object* v_num_1477_){
_start:
{
lean_object* v___x_1478_; 
v___x_1478_ = l_Lean_Level_PP_Result_ctorElim___redArg(v_t_1475_, v_num_1477_);
return v___x_1478_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_offset_elim___redArg(lean_object* v_t_1479_, lean_object* v_offset_1480_){
_start:
{
lean_object* v___x_1481_; 
v___x_1481_ = l_Lean_Level_PP_Result_ctorElim___redArg(v_t_1479_, v_offset_1480_);
return v___x_1481_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_offset_elim(lean_object* v_motive__1_1482_, lean_object* v_t_1483_, lean_object* v_h_1484_, lean_object* v_offset_1485_){
_start:
{
lean_object* v___x_1486_; 
v___x_1486_ = l_Lean_Level_PP_Result_ctorElim___redArg(v_t_1483_, v_offset_1485_);
return v___x_1486_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_maxNode_elim___redArg(lean_object* v_t_1487_, lean_object* v_maxNode_1488_){
_start:
{
lean_object* v___x_1489_; 
v___x_1489_ = l_Lean_Level_PP_Result_ctorElim___redArg(v_t_1487_, v_maxNode_1488_);
return v___x_1489_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_maxNode_elim(lean_object* v_motive__1_1490_, lean_object* v_t_1491_, lean_object* v_h_1492_, lean_object* v_maxNode_1493_){
_start:
{
lean_object* v___x_1494_; 
v___x_1494_ = l_Lean_Level_PP_Result_ctorElim___redArg(v_t_1491_, v_maxNode_1493_);
return v___x_1494_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_imaxNode_elim___redArg(lean_object* v_t_1495_, lean_object* v_imaxNode_1496_){
_start:
{
lean_object* v___x_1497_; 
v___x_1497_ = l_Lean_Level_PP_Result_ctorElim___redArg(v_t_1495_, v_imaxNode_1496_);
return v___x_1497_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_imaxNode_elim(lean_object* v_motive__1_1498_, lean_object* v_t_1499_, lean_object* v_h_1500_, lean_object* v_imaxNode_1501_){
_start:
{
lean_object* v___x_1502_; 
v___x_1502_ = l_Lean_Level_PP_Result_ctorElim___redArg(v_t_1499_, v_imaxNode_1501_);
return v___x_1502_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_succ(lean_object* v_x_1503_){
_start:
{
switch(lean_obj_tag(v_x_1503_))
{
case 2:
{
lean_object* v_a_1504_; lean_object* v_a_1505_; lean_object* v___x_1507_; uint8_t v_isShared_1508_; uint8_t v_isSharedCheck_1514_; 
v_a_1504_ = lean_ctor_get(v_x_1503_, 0);
v_a_1505_ = lean_ctor_get(v_x_1503_, 1);
v_isSharedCheck_1514_ = !lean_is_exclusive(v_x_1503_);
if (v_isSharedCheck_1514_ == 0)
{
v___x_1507_ = v_x_1503_;
v_isShared_1508_ = v_isSharedCheck_1514_;
goto v_resetjp_1506_;
}
else
{
lean_inc(v_a_1505_);
lean_inc(v_a_1504_);
lean_dec(v_x_1503_);
v___x_1507_ = lean_box(0);
v_isShared_1508_ = v_isSharedCheck_1514_;
goto v_resetjp_1506_;
}
v_resetjp_1506_:
{
lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1512_; 
v___x_1509_ = lean_unsigned_to_nat(1u);
v___x_1510_ = lean_nat_add(v_a_1505_, v___x_1509_);
lean_dec(v_a_1505_);
if (v_isShared_1508_ == 0)
{
lean_ctor_set(v___x_1507_, 1, v___x_1510_);
v___x_1512_ = v___x_1507_;
goto v_reusejp_1511_;
}
else
{
lean_object* v_reuseFailAlloc_1513_; 
v_reuseFailAlloc_1513_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1513_, 0, v_a_1504_);
lean_ctor_set(v_reuseFailAlloc_1513_, 1, v___x_1510_);
v___x_1512_ = v_reuseFailAlloc_1513_;
goto v_reusejp_1511_;
}
v_reusejp_1511_:
{
return v___x_1512_;
}
}
}
case 1:
{
lean_object* v_a_1515_; lean_object* v___x_1517_; uint8_t v_isShared_1518_; uint8_t v_isSharedCheck_1524_; 
v_a_1515_ = lean_ctor_get(v_x_1503_, 0);
v_isSharedCheck_1524_ = !lean_is_exclusive(v_x_1503_);
if (v_isSharedCheck_1524_ == 0)
{
v___x_1517_ = v_x_1503_;
v_isShared_1518_ = v_isSharedCheck_1524_;
goto v_resetjp_1516_;
}
else
{
lean_inc(v_a_1515_);
lean_dec(v_x_1503_);
v___x_1517_ = lean_box(0);
v_isShared_1518_ = v_isSharedCheck_1524_;
goto v_resetjp_1516_;
}
v_resetjp_1516_:
{
lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1522_; 
v___x_1519_ = lean_unsigned_to_nat(1u);
v___x_1520_ = lean_nat_add(v_a_1515_, v___x_1519_);
lean_dec(v_a_1515_);
if (v_isShared_1518_ == 0)
{
lean_ctor_set(v___x_1517_, 0, v___x_1520_);
v___x_1522_ = v___x_1517_;
goto v_reusejp_1521_;
}
else
{
lean_object* v_reuseFailAlloc_1523_; 
v_reuseFailAlloc_1523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1523_, 0, v___x_1520_);
v___x_1522_ = v_reuseFailAlloc_1523_;
goto v_reusejp_1521_;
}
v_reusejp_1521_:
{
return v___x_1522_;
}
}
}
default: 
{
lean_object* v___x_1525_; lean_object* v___x_1526_; 
v___x_1525_ = lean_unsigned_to_nat(1u);
v___x_1526_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1526_, 0, v_x_1503_);
lean_ctor_set(v___x_1526_, 1, v___x_1525_);
return v___x_1526_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_max(lean_object* v_x_1527_, lean_object* v_x_1528_){
_start:
{
if (lean_obj_tag(v_x_1528_) == 3)
{
lean_object* v_a_1529_; lean_object* v___x_1531_; uint8_t v_isShared_1532_; uint8_t v_isSharedCheck_1537_; 
v_a_1529_ = lean_ctor_get(v_x_1528_, 0);
v_isSharedCheck_1537_ = !lean_is_exclusive(v_x_1528_);
if (v_isSharedCheck_1537_ == 0)
{
v___x_1531_ = v_x_1528_;
v_isShared_1532_ = v_isSharedCheck_1537_;
goto v_resetjp_1530_;
}
else
{
lean_inc(v_a_1529_);
lean_dec(v_x_1528_);
v___x_1531_ = lean_box(0);
v_isShared_1532_ = v_isSharedCheck_1537_;
goto v_resetjp_1530_;
}
v_resetjp_1530_:
{
lean_object* v___x_1533_; lean_object* v___x_1535_; 
v___x_1533_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1533_, 0, v_x_1527_);
lean_ctor_set(v___x_1533_, 1, v_a_1529_);
if (v_isShared_1532_ == 0)
{
lean_ctor_set(v___x_1531_, 0, v___x_1533_);
v___x_1535_ = v___x_1531_;
goto v_reusejp_1534_;
}
else
{
lean_object* v_reuseFailAlloc_1536_; 
v_reuseFailAlloc_1536_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1536_, 0, v___x_1533_);
v___x_1535_ = v_reuseFailAlloc_1536_;
goto v_reusejp_1534_;
}
v_reusejp_1534_:
{
return v___x_1535_;
}
}
}
else
{
lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; 
v___x_1538_ = lean_box(0);
v___x_1539_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1539_, 0, v_x_1528_);
lean_ctor_set(v___x_1539_, 1, v___x_1538_);
v___x_1540_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1540_, 0, v_x_1527_);
lean_ctor_set(v___x_1540_, 1, v___x_1539_);
v___x_1541_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1541_, 0, v___x_1540_);
return v___x_1541_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_imax(lean_object* v_x_1542_, lean_object* v_x_1543_){
_start:
{
if (lean_obj_tag(v_x_1543_) == 4)
{
lean_object* v_a_1544_; lean_object* v___x_1546_; uint8_t v_isShared_1547_; uint8_t v_isSharedCheck_1552_; 
v_a_1544_ = lean_ctor_get(v_x_1543_, 0);
v_isSharedCheck_1552_ = !lean_is_exclusive(v_x_1543_);
if (v_isSharedCheck_1552_ == 0)
{
v___x_1546_ = v_x_1543_;
v_isShared_1547_ = v_isSharedCheck_1552_;
goto v_resetjp_1545_;
}
else
{
lean_inc(v_a_1544_);
lean_dec(v_x_1543_);
v___x_1546_ = lean_box(0);
v_isShared_1547_ = v_isSharedCheck_1552_;
goto v_resetjp_1545_;
}
v_resetjp_1545_:
{
lean_object* v___x_1548_; lean_object* v___x_1550_; 
v___x_1548_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1548_, 0, v_x_1542_);
lean_ctor_set(v___x_1548_, 1, v_a_1544_);
if (v_isShared_1547_ == 0)
{
lean_ctor_set(v___x_1546_, 0, v___x_1548_);
v___x_1550_ = v___x_1546_;
goto v_reusejp_1549_;
}
else
{
lean_object* v_reuseFailAlloc_1551_; 
v_reuseFailAlloc_1551_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1551_, 0, v___x_1548_);
v___x_1550_ = v_reuseFailAlloc_1551_;
goto v_reusejp_1549_;
}
v_reusejp_1549_:
{
return v___x_1550_;
}
}
}
else
{
lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; 
v___x_1553_ = lean_box(0);
v___x_1554_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1554_, 0, v_x_1543_);
lean_ctor_set(v___x_1554_, 1, v___x_1553_);
v___x_1555_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1555_, 0, v_x_1542_);
lean_ctor_set(v___x_1555_, 1, v___x_1554_);
v___x_1556_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1556_, 0, v___x_1555_);
return v___x_1556_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_toResult(lean_object* v_l_1575_, lean_object* v_a_1576_){
_start:
{
switch(lean_obj_tag(v_l_1575_))
{
case 0:
{
lean_object* v___x_1577_; 
v___x_1577_ = ((lean_object*)(l_Lean_Level_PP_toResult___closed__0));
return v___x_1577_;
}
case 1:
{
lean_object* v_a_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; 
v_a_1578_ = lean_ctor_get(v_l_1575_, 0);
lean_inc(v_a_1578_);
lean_dec_ref_known(v_l_1575_, 1);
v___x_1579_ = l_Lean_Level_PP_toResult(v_a_1578_, v_a_1576_);
v___x_1580_ = l_Lean_Level_PP_Result_succ(v___x_1579_);
return v___x_1580_;
}
case 2:
{
lean_object* v_a_1581_; lean_object* v_a_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; 
v_a_1581_ = lean_ctor_get(v_l_1575_, 0);
lean_inc(v_a_1581_);
v_a_1582_ = lean_ctor_get(v_l_1575_, 1);
lean_inc(v_a_1582_);
lean_dec_ref_known(v_l_1575_, 2);
v___x_1583_ = l_Lean_Level_PP_toResult(v_a_1581_, v_a_1576_);
v___x_1584_ = l_Lean_Level_PP_toResult(v_a_1582_, v_a_1576_);
v___x_1585_ = l_Lean_Level_PP_Result_max(v___x_1583_, v___x_1584_);
return v___x_1585_;
}
case 3:
{
lean_object* v_a_1586_; lean_object* v_a_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; 
v_a_1586_ = lean_ctor_get(v_l_1575_, 0);
lean_inc(v_a_1586_);
v_a_1587_ = lean_ctor_get(v_l_1575_, 1);
lean_inc(v_a_1587_);
lean_dec_ref_known(v_l_1575_, 2);
v___x_1588_ = l_Lean_Level_PP_toResult(v_a_1586_, v_a_1576_);
v___x_1589_ = l_Lean_Level_PP_toResult(v_a_1587_, v_a_1576_);
v___x_1590_ = l_Lean_Level_PP_Result_imax(v___x_1588_, v___x_1589_);
return v___x_1590_;
}
case 4:
{
lean_object* v_a_1591_; lean_object* v___x_1592_; 
v_a_1591_ = lean_ctor_get(v_l_1575_, 0);
lean_inc(v_a_1591_);
lean_dec_ref_known(v_l_1575_, 1);
v___x_1592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1592_, 0, v_a_1591_);
return v___x_1592_;
}
default: 
{
uint8_t v_mvars_1593_; 
v_mvars_1593_ = lean_ctor_get_uint8(v_a_1576_, sizeof(void*)*1);
if (v_mvars_1593_ == 0)
{
lean_object* v___x_1594_; 
lean_dec_ref_known(v_l_1575_, 1);
v___x_1594_ = ((lean_object*)(l_Lean_Level_PP_toResult___closed__3));
return v___x_1594_;
}
else
{
lean_object* v_a_1595_; lean_object* v_lIndex_x3f_1596_; lean_object* v___x_1597_; 
v_a_1595_ = lean_ctor_get(v_l_1575_, 0);
lean_inc_n(v_a_1595_, 2);
lean_dec_ref_known(v_l_1575_, 1);
v_lIndex_x3f_1596_ = lean_ctor_get(v_a_1576_, 0);
lean_inc_ref(v_lIndex_x3f_1596_);
v___x_1597_ = lean_apply_1(v_lIndex_x3f_1596_, v_a_1595_);
if (lean_obj_tag(v___x_1597_) == 1)
{
lean_object* v_val_1598_; lean_object* v___x_1600_; uint8_t v_isShared_1601_; uint8_t v_isSharedCheck_1609_; 
lean_dec(v_a_1595_);
v_val_1598_ = lean_ctor_get(v___x_1597_, 0);
v_isSharedCheck_1609_ = !lean_is_exclusive(v___x_1597_);
if (v_isSharedCheck_1609_ == 0)
{
v___x_1600_ = v___x_1597_;
v_isShared_1601_ = v_isSharedCheck_1609_;
goto v_resetjp_1599_;
}
else
{
lean_inc(v_val_1598_);
lean_dec(v___x_1597_);
v___x_1600_ = lean_box(0);
v_isShared_1601_ = v_isSharedCheck_1609_;
goto v_resetjp_1599_;
}
v_resetjp_1599_:
{
lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1607_; 
v___x_1602_ = ((lean_object*)(l_Lean_Level_PP_toResult___closed__5));
v___x_1603_ = lean_unsigned_to_nat(1u);
v___x_1604_ = lean_nat_add(v_val_1598_, v___x_1603_);
lean_dec(v_val_1598_);
v___x_1605_ = l_Lean_Name_num___override(v___x_1602_, v___x_1604_);
if (v_isShared_1601_ == 0)
{
lean_ctor_set_tag(v___x_1600_, 0);
lean_ctor_set(v___x_1600_, 0, v___x_1605_);
v___x_1607_ = v___x_1600_;
goto v_reusejp_1606_;
}
else
{
lean_object* v_reuseFailAlloc_1608_; 
v_reuseFailAlloc_1608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1608_, 0, v___x_1605_);
v___x_1607_ = v_reuseFailAlloc_1608_;
goto v_reusejp_1606_;
}
v_reusejp_1606_:
{
return v___x_1607_;
}
}
}
else
{
lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; 
lean_dec(v___x_1597_);
v___x_1610_ = ((lean_object*)(l_Lean_Level_PP_toResult___closed__7));
v___x_1611_ = ((lean_object*)(l_Lean_Level_PP_toResult___closed__9));
v___x_1612_ = l_Lean_Name_replacePrefix(v_a_1595_, v___x_1610_, v___x_1611_);
v___x_1613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1613_, 0, v___x_1612_);
return v___x_1613_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_toResult___boxed(lean_object* v_l_1614_, lean_object* v_a_1615_){
_start:
{
lean_object* v_res_1616_; 
v_res_1616_ = l_Lean_Level_PP_toResult(v_l_1614_, v_a_1615_);
lean_dec_ref(v_a_1615_);
return v_res_1616_;
}
}
static lean_object* _init_l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__1(void){
_start:
{
lean_object* v___x_1618_; lean_object* v___x_1619_; 
v___x_1618_ = ((lean_object*)(l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__0));
v___x_1619_ = lean_string_length(v___x_1618_);
return v___x_1619_;
}
}
static lean_object* _init_l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__2(void){
_start:
{
lean_object* v___x_1620_; lean_object* v___x_1621_; 
v___x_1620_ = lean_obj_once(&l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__1, &l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__1_once, _init_l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__1);
v___x_1621_ = lean_nat_to_int(v___x_1620_);
return v___x_1621_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse(lean_object* v_x_1626_, uint8_t v_x_1627_){
_start:
{
if (v_x_1627_ == 0)
{
lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; uint8_t v___x_1634_; lean_object* v___x_1635_; 
v___x_1628_ = lean_obj_once(&l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__2, &l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__2_once, _init_l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__2);
v___x_1629_ = ((lean_object*)(l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__3));
v___x_1630_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1630_, 0, v___x_1629_);
lean_ctor_set(v___x_1630_, 1, v_x_1626_);
v___x_1631_ = ((lean_object*)(l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__4));
v___x_1632_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1632_, 0, v___x_1630_);
lean_ctor_set(v___x_1632_, 1, v___x_1631_);
v___x_1633_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1633_, 0, v___x_1628_);
lean_ctor_set(v___x_1633_, 1, v___x_1632_);
v___x_1634_ = 0;
v___x_1635_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1635_, 0, v___x_1633_);
lean_ctor_set_uint8(v___x_1635_, sizeof(void*)*1, v___x_1634_);
return v___x_1635_;
}
else
{
return v_x_1626_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___boxed(lean_object* v_x_1636_, lean_object* v_x_1637_){
_start:
{
uint8_t v_x_57__boxed_1638_; lean_object* v_res_1639_; 
v_x_57__boxed_1638_ = lean_unbox(v_x_1637_);
v_res_1639_ = l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse(v_x_1636_, v_x_57__boxed_1638_);
return v_res_1639_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_format(lean_object* v_x_1649_, uint8_t v_x_1650_){
_start:
{
switch(lean_obj_tag(v_x_1649_))
{
case 0:
{
lean_object* v_a_1651_; lean_object* v___x_1653_; uint8_t v_isShared_1654_; uint8_t v_isSharedCheck_1660_; 
v_a_1651_ = lean_ctor_get(v_x_1649_, 0);
v_isSharedCheck_1660_ = !lean_is_exclusive(v_x_1649_);
if (v_isSharedCheck_1660_ == 0)
{
v___x_1653_ = v_x_1649_;
v_isShared_1654_ = v_isSharedCheck_1660_;
goto v_resetjp_1652_;
}
else
{
lean_inc(v_a_1651_);
lean_dec(v_x_1649_);
v___x_1653_ = lean_box(0);
v_isShared_1654_ = v_isSharedCheck_1660_;
goto v_resetjp_1652_;
}
v_resetjp_1652_:
{
uint8_t v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1658_; 
v___x_1655_ = 1;
v___x_1656_ = l_Lean_Name_toString(v_a_1651_, v___x_1655_);
if (v_isShared_1654_ == 0)
{
lean_ctor_set_tag(v___x_1653_, 3);
lean_ctor_set(v___x_1653_, 0, v___x_1656_);
v___x_1658_ = v___x_1653_;
goto v_reusejp_1657_;
}
else
{
lean_object* v_reuseFailAlloc_1659_; 
v_reuseFailAlloc_1659_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1659_, 0, v___x_1656_);
v___x_1658_ = v_reuseFailAlloc_1659_;
goto v_reusejp_1657_;
}
v_reusejp_1657_:
{
return v___x_1658_;
}
}
}
case 1:
{
lean_object* v_a_1661_; lean_object* v___x_1663_; uint8_t v_isShared_1664_; uint8_t v_isSharedCheck_1669_; 
v_a_1661_ = lean_ctor_get(v_x_1649_, 0);
v_isSharedCheck_1669_ = !lean_is_exclusive(v_x_1649_);
if (v_isSharedCheck_1669_ == 0)
{
v___x_1663_ = v_x_1649_;
v_isShared_1664_ = v_isSharedCheck_1669_;
goto v_resetjp_1662_;
}
else
{
lean_inc(v_a_1661_);
lean_dec(v_x_1649_);
v___x_1663_ = lean_box(0);
v_isShared_1664_ = v_isSharedCheck_1669_;
goto v_resetjp_1662_;
}
v_resetjp_1662_:
{
lean_object* v___x_1665_; lean_object* v___x_1667_; 
v___x_1665_ = l_Nat_reprFast(v_a_1661_);
if (v_isShared_1664_ == 0)
{
lean_ctor_set_tag(v___x_1663_, 3);
lean_ctor_set(v___x_1663_, 0, v___x_1665_);
v___x_1667_ = v___x_1663_;
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
case 2:
{
lean_object* v_a_1670_; lean_object* v_a_1671_; lean_object* v___x_1673_; uint8_t v_isShared_1674_; uint8_t v_isSharedCheck_1690_; 
v_a_1670_ = lean_ctor_get(v_x_1649_, 0);
v_a_1671_ = lean_ctor_get(v_x_1649_, 1);
v_isSharedCheck_1690_ = !lean_is_exclusive(v_x_1649_);
if (v_isSharedCheck_1690_ == 0)
{
v___x_1673_ = v_x_1649_;
v_isShared_1674_ = v_isSharedCheck_1690_;
goto v_resetjp_1672_;
}
else
{
lean_inc(v_a_1671_);
lean_inc(v_a_1670_);
lean_dec(v_x_1649_);
v___x_1673_ = lean_box(0);
v_isShared_1674_ = v_isSharedCheck_1690_;
goto v_resetjp_1672_;
}
v_resetjp_1672_:
{
lean_object* v_zero_1675_; uint8_t v_isZero_1676_; 
v_zero_1675_ = lean_unsigned_to_nat(0u);
v_isZero_1676_ = lean_nat_dec_eq(v_a_1671_, v_zero_1675_);
if (v_isZero_1676_ == 1)
{
lean_del_object(v___x_1673_);
lean_dec(v_a_1671_);
v_x_1649_ = v_a_1670_;
goto _start;
}
else
{
lean_object* v_one_1678_; lean_object* v_n_1679_; lean_object* v_f_x27_1680_; lean_object* v___x_1681_; lean_object* v___x_1683_; 
v_one_1678_ = lean_unsigned_to_nat(1u);
v_n_1679_ = lean_nat_sub(v_a_1671_, v_one_1678_);
lean_dec(v_a_1671_);
v_f_x27_1680_ = l_Lean_Level_PP_Result_format(v_a_1670_, v_isZero_1676_);
v___x_1681_ = ((lean_object*)(l_Lean_Level_PP_Result_format___closed__1));
if (v_isShared_1674_ == 0)
{
lean_ctor_set_tag(v___x_1673_, 5);
lean_ctor_set(v___x_1673_, 1, v___x_1681_);
lean_ctor_set(v___x_1673_, 0, v_f_x27_1680_);
v___x_1683_ = v___x_1673_;
goto v_reusejp_1682_;
}
else
{
lean_object* v_reuseFailAlloc_1689_; 
v_reuseFailAlloc_1689_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1689_, 0, v_f_x27_1680_);
lean_ctor_set(v_reuseFailAlloc_1689_, 1, v___x_1681_);
v___x_1683_ = v_reuseFailAlloc_1689_;
goto v_reusejp_1682_;
}
v_reusejp_1682_:
{
lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; 
v___x_1684_ = lean_nat_add(v_n_1679_, v_one_1678_);
lean_dec(v_n_1679_);
v___x_1685_ = l_Nat_reprFast(v___x_1684_);
v___x_1686_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1686_, 0, v___x_1685_);
v___x_1687_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1687_, 0, v___x_1683_);
lean_ctor_set(v___x_1687_, 1, v___x_1686_);
v___x_1688_ = l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse(v___x_1687_, v_x_1650_);
return v___x_1688_;
}
}
}
}
case 3:
{
lean_object* v_a_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; uint8_t v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; 
v_a_1691_ = lean_ctor_get(v_x_1649_, 0);
lean_inc(v_a_1691_);
lean_dec_ref_known(v_x_1649_, 1);
v___x_1692_ = ((lean_object*)(l_Lean_Level_PP_Result_format___closed__3));
v___x_1693_ = l___private_Lean_Level_0__Lean_Level_PP_Result_formatLst(v_a_1691_);
v___x_1694_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1694_, 0, v___x_1692_);
lean_ctor_set(v___x_1694_, 1, v___x_1693_);
v___x_1695_ = 0;
v___x_1696_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1696_, 0, v___x_1694_);
lean_ctor_set_uint8(v___x_1696_, sizeof(void*)*1, v___x_1695_);
v___x_1697_ = l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse(v___x_1696_, v_x_1650_);
return v___x_1697_;
}
default: 
{
lean_object* v_a_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; uint8_t v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; 
v_a_1698_ = lean_ctor_get(v_x_1649_, 0);
lean_inc(v_a_1698_);
lean_dec_ref_known(v_x_1649_, 1);
v___x_1699_ = ((lean_object*)(l_Lean_Level_PP_Result_format___closed__5));
v___x_1700_ = l___private_Lean_Level_0__Lean_Level_PP_Result_formatLst(v_a_1698_);
v___x_1701_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1701_, 0, v___x_1699_);
lean_ctor_set(v___x_1701_, 1, v___x_1700_);
v___x_1702_ = 0;
v___x_1703_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1703_, 0, v___x_1701_);
lean_ctor_set_uint8(v___x_1703_, sizeof(void*)*1, v___x_1702_);
v___x_1704_ = l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse(v___x_1703_, v_x_1650_);
return v___x_1704_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_PP_Result_formatLst(lean_object* v_x_1705_){
_start:
{
if (lean_obj_tag(v_x_1705_) == 0)
{
lean_object* v___x_1706_; 
v___x_1706_ = lean_box(0);
return v___x_1706_;
}
else
{
lean_object* v_head_1707_; lean_object* v_tail_1708_; lean_object* v___x_1710_; uint8_t v_isShared_1711_; uint8_t v_isSharedCheck_1720_; 
v_head_1707_ = lean_ctor_get(v_x_1705_, 0);
v_tail_1708_ = lean_ctor_get(v_x_1705_, 1);
v_isSharedCheck_1720_ = !lean_is_exclusive(v_x_1705_);
if (v_isSharedCheck_1720_ == 0)
{
v___x_1710_ = v_x_1705_;
v_isShared_1711_ = v_isSharedCheck_1720_;
goto v_resetjp_1709_;
}
else
{
lean_inc(v_tail_1708_);
lean_inc(v_head_1707_);
lean_dec(v_x_1705_);
v___x_1710_ = lean_box(0);
v_isShared_1711_ = v_isSharedCheck_1720_;
goto v_resetjp_1709_;
}
v_resetjp_1709_:
{
lean_object* v___x_1712_; uint8_t v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1716_; 
v___x_1712_ = lean_box(1);
v___x_1713_ = 0;
v___x_1714_ = l_Lean_Level_PP_Result_format(v_head_1707_, v___x_1713_);
if (v_isShared_1711_ == 0)
{
lean_ctor_set_tag(v___x_1710_, 5);
lean_ctor_set(v___x_1710_, 1, v___x_1714_);
lean_ctor_set(v___x_1710_, 0, v___x_1712_);
v___x_1716_ = v___x_1710_;
goto v_reusejp_1715_;
}
else
{
lean_object* v_reuseFailAlloc_1719_; 
v_reuseFailAlloc_1719_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1719_, 0, v___x_1712_);
lean_ctor_set(v_reuseFailAlloc_1719_, 1, v___x_1714_);
v___x_1716_ = v_reuseFailAlloc_1719_;
goto v_reusejp_1715_;
}
v_reusejp_1715_:
{
lean_object* v___x_1717_; lean_object* v___x_1718_; 
v___x_1717_ = l___private_Lean_Level_0__Lean_Level_PP_Result_formatLst(v_tail_1708_);
v___x_1718_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1718_, 0, v___x_1716_);
lean_ctor_set(v___x_1718_, 1, v___x_1717_);
return v___x_1718_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_format___boxed(lean_object* v_x_1721_, lean_object* v_x_1722_){
_start:
{
uint8_t v_x_270__boxed_1723_; lean_object* v_res_1724_; 
v_x_270__boxed_1723_ = lean_unbox(v_x_1722_);
v_res_1724_ = l_Lean_Level_PP_Result_format(v_x_1721_, v_x_270__boxed_1723_);
return v_res_1724_;
}
}
static lean_object* _init_l_Lean_Level_PP_Result_quote___closed__0(void){
_start:
{
uint8_t v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; 
v___x_1725_ = 0;
v___x_1726_ = lean_box(0);
v___x_1727_ = l_Lean_SourceInfo_fromRef(v___x_1726_, v___x_1725_);
return v___x_1727_;
}
}
static lean_object* _init_l_Lean_Level_PP_Result_quote___closed__6(void){
_start:
{
lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; 
v___x_1737_ = ((lean_object*)(l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__0));
v___x_1738_ = lean_obj_once(&l_Lean_Level_PP_Result_quote___closed__0, &l_Lean_Level_PP_Result_quote___closed__0_once, _init_l_Lean_Level_PP_Result_quote___closed__0);
v___x_1739_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1739_, 0, v___x_1738_);
lean_ctor_set(v___x_1739_, 1, v___x_1737_);
return v___x_1739_;
}
}
static lean_object* _init_l_Lean_Level_PP_Result_quote___closed__7(void){
_start:
{
lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; 
v___x_1740_ = ((lean_object*)(l_Lean_instReprData___lam__0___closed__0));
v___x_1741_ = lean_obj_once(&l_Lean_Level_PP_Result_quote___closed__0, &l_Lean_Level_PP_Result_quote___closed__0_once, _init_l_Lean_Level_PP_Result_quote___closed__0);
v___x_1742_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1742_, 0, v___x_1741_);
lean_ctor_set(v___x_1742_, 1, v___x_1740_);
return v___x_1742_;
}
}
static lean_object* _init_l_Lean_Level_PP_Result_quote___closed__12(void){
_start:
{
lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; 
v___x_1755_ = ((lean_object*)(l_Lean_Level_PP_Result_format___closed__2));
v___x_1756_ = lean_obj_once(&l_Lean_Level_PP_Result_quote___closed__0, &l_Lean_Level_PP_Result_quote___closed__0_once, _init_l_Lean_Level_PP_Result_quote___closed__0);
v___x_1757_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1757_, 0, v___x_1756_);
lean_ctor_set(v___x_1757_, 1, v___x_1755_);
return v___x_1757_;
}
}
static lean_object* _init_l_Lean_Level_PP_Result_quote___closed__15(void){
_start:
{
lean_object* v___x_1761_; 
v___x_1761_ = l_Array_mkArray0(lean_box(0));
return v___x_1761_;
}
}
static lean_object* _init_l_Lean_Level_PP_Result_quote___closed__17(void){
_start:
{
lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; 
v___x_1767_ = ((lean_object*)(l_Lean_Level_PP_Result_format___closed__4));
v___x_1768_ = lean_obj_once(&l_Lean_Level_PP_Result_quote___closed__0, &l_Lean_Level_PP_Result_quote___closed__0_once, _init_l_Lean_Level_PP_Result_quote___closed__0);
v___x_1769_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1769_, 0, v___x_1768_);
lean_ctor_set(v___x_1769_, 1, v___x_1767_);
return v___x_1769_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_quote(lean_object* v_r_1770_, lean_object* v_prec_1771_){
_start:
{
lean_object* v_s_1773_; 
switch(lean_obj_tag(v_r_1770_))
{
case 0:
{
lean_object* v_a_1781_; lean_object* v___x_1782_; 
v_a_1781_ = lean_ctor_get(v_r_1770_, 0);
lean_inc(v_a_1781_);
lean_dec_ref_known(v_r_1770_, 1);
v___x_1782_ = l_Lean_mkIdent(v_a_1781_);
return v___x_1782_;
}
case 1:
{
lean_object* v_a_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; 
v_a_1783_ = lean_ctor_get(v_r_1770_, 0);
lean_inc(v_a_1783_);
lean_dec_ref_known(v_r_1770_, 1);
v___x_1784_ = l_Nat_reprFast(v_a_1783_);
v___x_1785_ = lean_box(2);
v___x_1786_ = l_Lean_Syntax_mkNumLit(v___x_1784_, v___x_1785_);
return v___x_1786_;
}
case 2:
{
lean_object* v_a_1787_; lean_object* v_a_1788_; lean_object* v___x_1790_; uint8_t v_isShared_1791_; uint8_t v_isSharedCheck_1811_; 
v_a_1787_ = lean_ctor_get(v_r_1770_, 0);
v_a_1788_ = lean_ctor_get(v_r_1770_, 1);
v_isSharedCheck_1811_ = !lean_is_exclusive(v_r_1770_);
if (v_isSharedCheck_1811_ == 0)
{
v___x_1790_ = v_r_1770_;
v_isShared_1791_ = v_isSharedCheck_1811_;
goto v_resetjp_1789_;
}
else
{
lean_inc(v_a_1788_);
lean_inc(v_a_1787_);
lean_dec(v_r_1770_);
v___x_1790_ = lean_box(0);
v_isShared_1791_ = v_isSharedCheck_1811_;
goto v_resetjp_1789_;
}
v_resetjp_1789_:
{
lean_object* v_zero_1792_; uint8_t v_isZero_1793_; 
v_zero_1792_ = lean_unsigned_to_nat(0u);
v_isZero_1793_ = lean_nat_dec_eq(v_a_1788_, v_zero_1792_);
if (v_isZero_1793_ == 1)
{
lean_del_object(v___x_1790_);
lean_dec(v_a_1788_);
v_r_1770_ = v_a_1787_;
goto _start;
}
else
{
lean_object* v_one_1795_; lean_object* v_n_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1804_; 
v_one_1795_ = lean_unsigned_to_nat(1u);
v_n_1796_ = lean_nat_sub(v_a_1788_, v_one_1795_);
lean_dec(v_a_1788_);
v___x_1797_ = lean_box(0);
v___x_1798_ = l_Lean_SourceInfo_fromRef(v___x_1797_, v_isZero_1793_);
v___x_1799_ = ((lean_object*)(l_Lean_Level_PP_Result_quote___closed__9));
v___x_1800_ = lean_unsigned_to_nat(65u);
v___x_1801_ = l_Lean_Level_PP_Result_quote(v_a_1787_, v___x_1800_);
v___x_1802_ = ((lean_object*)(l_Lean_Level_PP_Result_quote___closed__10));
lean_inc(v___x_1798_);
if (v_isShared_1791_ == 0)
{
lean_ctor_set(v___x_1790_, 1, v___x_1802_);
lean_ctor_set(v___x_1790_, 0, v___x_1798_);
v___x_1804_ = v___x_1790_;
goto v_reusejp_1803_;
}
else
{
lean_object* v_reuseFailAlloc_1810_; 
v_reuseFailAlloc_1810_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1810_, 0, v___x_1798_);
lean_ctor_set(v_reuseFailAlloc_1810_, 1, v___x_1802_);
v___x_1804_ = v_reuseFailAlloc_1810_;
goto v_reusejp_1803_;
}
v_reusejp_1803_:
{
lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; 
v___x_1805_ = lean_nat_add(v_n_1796_, v_one_1795_);
lean_dec(v_n_1796_);
v___x_1806_ = l_Nat_reprFast(v___x_1805_);
v___x_1807_ = lean_box(2);
v___x_1808_ = l_Lean_Syntax_mkNumLit(v___x_1806_, v___x_1807_);
v___x_1809_ = l_Lean_Syntax_node3(v___x_1798_, v___x_1799_, v___x_1801_, v___x_1804_, v___x_1808_);
v_s_1773_ = v___x_1809_;
goto v___jp_1772_;
}
}
}
}
case 3:
{
lean_object* v_a_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; size_t v_sz_1819_; size_t v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; 
v_a_1812_ = lean_ctor_get(v_r_1770_, 0);
lean_inc(v_a_1812_);
lean_dec_ref_known(v_r_1770_, 1);
v___x_1813_ = lean_obj_once(&l_Lean_Level_PP_Result_quote___closed__0, &l_Lean_Level_PP_Result_quote___closed__0_once, _init_l_Lean_Level_PP_Result_quote___closed__0);
v___x_1814_ = ((lean_object*)(l_Lean_Level_PP_Result_quote___closed__11));
v___x_1815_ = lean_obj_once(&l_Lean_Level_PP_Result_quote___closed__12, &l_Lean_Level_PP_Result_quote___closed__12_once, _init_l_Lean_Level_PP_Result_quote___closed__12);
v___x_1816_ = ((lean_object*)(l_Lean_Level_PP_Result_quote___closed__14));
v___x_1817_ = lean_obj_once(&l_Lean_Level_PP_Result_quote___closed__15, &l_Lean_Level_PP_Result_quote___closed__15_once, _init_l_Lean_Level_PP_Result_quote___closed__15);
v___x_1818_ = lean_array_mk(v_a_1812_);
v_sz_1819_ = lean_array_size(v___x_1818_);
v___x_1820_ = ((size_t)0ULL);
v___x_1821_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Level_PP_Result_quote_spec__0(v_sz_1819_, v___x_1820_, v___x_1818_);
v___x_1822_ = l_Array_append___redArg(v___x_1817_, v___x_1821_);
lean_dec_ref(v___x_1821_);
v___x_1823_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1823_, 0, v___x_1813_);
lean_ctor_set(v___x_1823_, 1, v___x_1816_);
lean_ctor_set(v___x_1823_, 2, v___x_1822_);
v___x_1824_ = l_Lean_Syntax_node2(v___x_1813_, v___x_1814_, v___x_1815_, v___x_1823_);
v_s_1773_ = v___x_1824_;
goto v___jp_1772_;
}
default: 
{
lean_object* v_a_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; size_t v_sz_1832_; size_t v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; 
v_a_1825_ = lean_ctor_get(v_r_1770_, 0);
lean_inc(v_a_1825_);
lean_dec_ref_known(v_r_1770_, 1);
v___x_1826_ = lean_obj_once(&l_Lean_Level_PP_Result_quote___closed__0, &l_Lean_Level_PP_Result_quote___closed__0_once, _init_l_Lean_Level_PP_Result_quote___closed__0);
v___x_1827_ = ((lean_object*)(l_Lean_Level_PP_Result_quote___closed__16));
v___x_1828_ = lean_obj_once(&l_Lean_Level_PP_Result_quote___closed__17, &l_Lean_Level_PP_Result_quote___closed__17_once, _init_l_Lean_Level_PP_Result_quote___closed__17);
v___x_1829_ = ((lean_object*)(l_Lean_Level_PP_Result_quote___closed__14));
v___x_1830_ = lean_obj_once(&l_Lean_Level_PP_Result_quote___closed__15, &l_Lean_Level_PP_Result_quote___closed__15_once, _init_l_Lean_Level_PP_Result_quote___closed__15);
v___x_1831_ = lean_array_mk(v_a_1825_);
v_sz_1832_ = lean_array_size(v___x_1831_);
v___x_1833_ = ((size_t)0ULL);
v___x_1834_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Level_PP_Result_quote_spec__0(v_sz_1832_, v___x_1833_, v___x_1831_);
v___x_1835_ = l_Array_append___redArg(v___x_1830_, v___x_1834_);
lean_dec_ref(v___x_1834_);
v___x_1836_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1836_, 0, v___x_1826_);
lean_ctor_set(v___x_1836_, 1, v___x_1829_);
lean_ctor_set(v___x_1836_, 2, v___x_1835_);
v___x_1837_ = l_Lean_Syntax_node2(v___x_1826_, v___x_1827_, v___x_1828_, v___x_1836_);
v_s_1773_ = v___x_1837_;
goto v___jp_1772_;
}
}
v___jp_1772_:
{
lean_object* v___x_1774_; uint8_t v___x_1775_; 
v___x_1774_ = lean_unsigned_to_nat(0u);
v___x_1775_ = lean_nat_dec_lt(v___x_1774_, v_prec_1771_);
if (v___x_1775_ == 0)
{
return v_s_1773_;
}
else
{
lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; 
v___x_1776_ = lean_obj_once(&l_Lean_Level_PP_Result_quote___closed__0, &l_Lean_Level_PP_Result_quote___closed__0_once, _init_l_Lean_Level_PP_Result_quote___closed__0);
v___x_1777_ = ((lean_object*)(l_Lean_Level_PP_Result_quote___closed__5));
v___x_1778_ = lean_obj_once(&l_Lean_Level_PP_Result_quote___closed__6, &l_Lean_Level_PP_Result_quote___closed__6_once, _init_l_Lean_Level_PP_Result_quote___closed__6);
v___x_1779_ = lean_obj_once(&l_Lean_Level_PP_Result_quote___closed__7, &l_Lean_Level_PP_Result_quote___closed__7_once, _init_l_Lean_Level_PP_Result_quote___closed__7);
v___x_1780_ = l_Lean_Syntax_node3(v___x_1776_, v___x_1777_, v___x_1778_, v_s_1773_, v___x_1779_);
return v___x_1780_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Level_PP_Result_quote_spec__0(size_t v_sz_1838_, size_t v_i_1839_, lean_object* v_bs_1840_){
_start:
{
uint8_t v___x_1841_; 
v___x_1841_ = lean_usize_dec_lt(v_i_1839_, v_sz_1838_);
if (v___x_1841_ == 0)
{
return v_bs_1840_;
}
else
{
lean_object* v_v_1842_; lean_object* v___x_1843_; lean_object* v_bs_x27_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; size_t v___x_1847_; size_t v___x_1848_; lean_object* v___x_1849_; 
v_v_1842_ = lean_array_uget(v_bs_1840_, v_i_1839_);
v___x_1843_ = lean_unsigned_to_nat(0u);
v_bs_x27_1844_ = lean_array_uset(v_bs_1840_, v_i_1839_, v___x_1843_);
v___x_1845_ = lean_unsigned_to_nat(1024u);
v___x_1846_ = l_Lean_Level_PP_Result_quote(v_v_1842_, v___x_1845_);
v___x_1847_ = ((size_t)1ULL);
v___x_1848_ = lean_usize_add(v_i_1839_, v___x_1847_);
v___x_1849_ = lean_array_uset(v_bs_x27_1844_, v_i_1839_, v___x_1846_);
v_i_1839_ = v___x_1848_;
v_bs_1840_ = v___x_1849_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Level_PP_Result_quote_spec__0___boxed(lean_object* v_sz_1851_, lean_object* v_i_1852_, lean_object* v_bs_1853_){
_start:
{
size_t v_sz_boxed_1854_; size_t v_i_boxed_1855_; lean_object* v_res_1856_; 
v_sz_boxed_1854_ = lean_unbox_usize(v_sz_1851_);
lean_dec(v_sz_1851_);
v_i_boxed_1855_ = lean_unbox_usize(v_i_1852_);
lean_dec(v_i_1852_);
v_res_1856_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Level_PP_Result_quote_spec__0(v_sz_boxed_1854_, v_i_boxed_1855_, v_bs_1853_);
return v_res_1856_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_quote___boxed(lean_object* v_r_1857_, lean_object* v_prec_1858_){
_start:
{
lean_object* v_res_1859_; 
v_res_1859_ = l_Lean_Level_PP_Result_quote(v_r_1857_, v_prec_1858_);
lean_dec(v_prec_1858_);
return v_res_1859_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_format(lean_object* v_u_1860_, uint8_t v_mvars_1861_, lean_object* v_lIndex_x3f_1862_){
_start:
{
lean_object* v___x_1863_; lean_object* v___x_1864_; uint8_t v___x_1865_; lean_object* v___x_1866_; 
v___x_1863_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1863_, 0, v_lIndex_x3f_1862_);
lean_ctor_set_uint8(v___x_1863_, sizeof(void*)*1, v_mvars_1861_);
v___x_1864_ = l_Lean_Level_PP_toResult(v_u_1860_, v___x_1863_);
lean_dec_ref_known(v___x_1863_, 1);
v___x_1865_ = 1;
v___x_1866_ = l_Lean_Level_PP_Result_format(v___x_1864_, v___x_1865_);
return v___x_1866_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_format___boxed(lean_object* v_u_1867_, lean_object* v_mvars_1868_, lean_object* v_lIndex_x3f_1869_){
_start:
{
uint8_t v_mvars_boxed_1870_; lean_object* v_res_1871_; 
v_mvars_boxed_1870_ = lean_unbox(v_mvars_1868_);
v_res_1871_ = l_Lean_Level_format(v_u_1867_, v_mvars_boxed_1870_, v_lIndex_x3f_1869_);
return v_res_1871_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_instToFormat___lam__0(lean_object* v_x_1872_){
_start:
{
lean_object* v___x_1873_; 
v___x_1873_ = lean_box(0);
return v___x_1873_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_instToFormat___lam__0___boxed(lean_object* v_x_1874_){
_start:
{
lean_object* v_res_1875_; 
v_res_1875_ = l_Lean_Level_instToFormat___lam__0(v_x_1874_);
lean_dec(v_x_1874_);
return v_res_1875_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_instToFormat___lam__1(lean_object* v___f_1876_, lean_object* v_u_1877_){
_start:
{
uint8_t v___x_1878_; lean_object* v___x_1879_; 
v___x_1878_ = 1;
v___x_1879_ = l_Lean_Level_format(v_u_1877_, v___x_1878_, v___f_1876_);
return v___x_1879_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_instToString___lam__1(lean_object* v___f_1884_, lean_object* v_u_1885_){
_start:
{
uint8_t v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; 
v___x_1886_ = 1;
v___x_1887_ = l_Lean_Level_format(v_u_1885_, v___x_1886_, v___f_1884_);
v___x_1888_ = l_Std_Format_defWidth;
v___x_1889_ = lean_unsigned_to_nat(0u);
v___x_1890_ = l_Std_Format_pretty(v___x_1887_, v___x_1888_, v___x_1889_, v___x_1889_);
return v___x_1890_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_quote(lean_object* v_u_1894_, lean_object* v_prec_1895_, uint8_t v_mvars_1896_, lean_object* v_lIndex_x3f_1897_){
_start:
{
lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; 
v___x_1898_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1898_, 0, v_lIndex_x3f_1897_);
lean_ctor_set_uint8(v___x_1898_, sizeof(void*)*1, v_mvars_1896_);
v___x_1899_ = l_Lean_Level_PP_toResult(v_u_1894_, v___x_1898_);
lean_dec_ref_known(v___x_1898_, 1);
v___x_1900_ = l_Lean_Level_PP_Result_quote(v___x_1899_, v_prec_1895_);
return v___x_1900_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_quote___boxed(lean_object* v_u_1901_, lean_object* v_prec_1902_, lean_object* v_mvars_1903_, lean_object* v_lIndex_x3f_1904_){
_start:
{
uint8_t v_mvars_boxed_1905_; lean_object* v_res_1906_; 
v_mvars_boxed_1905_ = lean_unbox(v_mvars_1903_);
v_res_1906_ = l_Lean_Level_quote(v_u_1901_, v_prec_1902_, v_mvars_boxed_1905_, v_lIndex_x3f_1904_);
lean_dec(v_prec_1902_);
return v_res_1906_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_instQuoteMkStr1___lam__1(lean_object* v___f_1907_, lean_object* v_u_1908_){
_start:
{
lean_object* v___x_1909_; uint8_t v___x_1910_; lean_object* v___x_1911_; 
v___x_1909_ = lean_unsigned_to_nat(0u);
v___x_1910_ = 1;
v___x_1911_ = l_Lean_Level_quote(v_u_1908_, v___x_1909_, v___x_1910_, v___f_1907_);
return v___x_1911_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Level_0__Lean_mkLevelMaxCore___lam__0(lean_object* v_u_1915_, lean_object* v_v_1916_){
_start:
{
uint8_t v___y_1918_; uint8_t v___x_1924_; 
v___x_1924_ = l_Lean_Level_isExplicit(v_v_1916_);
if (v___x_1924_ == 0)
{
v___y_1918_ = v___x_1924_;
goto v___jp_1917_;
}
else
{
lean_object* v___x_1925_; lean_object* v___x_1926_; uint8_t v___x_1927_; 
v___x_1925_ = l_Lean_Level_getOffset(v_v_1916_);
v___x_1926_ = l_Lean_Level_getOffset(v_u_1915_);
v___x_1927_ = lean_nat_dec_le(v___x_1925_, v___x_1926_);
lean_dec(v___x_1926_);
lean_dec(v___x_1925_);
v___y_1918_ = v___x_1927_;
goto v___jp_1917_;
}
v___jp_1917_:
{
uint8_t v___x_1919_; 
v___x_1919_ = 1;
if (v___y_1918_ == 0)
{
if (lean_obj_tag(v_u_1915_) == 2)
{
lean_object* v_a_1920_; lean_object* v_a_1921_; uint8_t v___x_1922_; 
v_a_1920_ = lean_ctor_get(v_u_1915_, 0);
v_a_1921_ = lean_ctor_get(v_u_1915_, 1);
v___x_1922_ = lean_level_eq(v_v_1916_, v_a_1920_);
if (v___x_1922_ == 0)
{
uint8_t v___x_1923_; 
v___x_1923_ = lean_level_eq(v_v_1916_, v_a_1921_);
return v___x_1923_;
}
else
{
return v___x_1919_;
}
}
else
{
return v___y_1918_;
}
}
else
{
return v___x_1919_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_mkLevelMaxCore___lam__0___boxed(lean_object* v_u_1928_, lean_object* v_v_1929_){
_start:
{
uint8_t v_res_1930_; lean_object* v_r_1931_; 
v_res_1930_ = l___private_Lean_Level_0__Lean_mkLevelMaxCore___lam__0(v_u_1928_, v_v_1929_);
lean_dec(v_v_1929_);
lean_dec(v_u_1928_);
v_r_1931_ = lean_box(v_res_1930_);
return v_r_1931_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_mkLevelMaxCore(lean_object* v_u_1932_, lean_object* v_v_1933_, lean_object* v_elseK_1934_){
_start:
{
uint8_t v___x_1935_; 
v___x_1935_ = lean_level_eq(v_u_1932_, v_v_1933_);
if (v___x_1935_ == 0)
{
uint8_t v___x_1936_; 
v___x_1936_ = l_Lean_Level_isZero(v_u_1932_);
if (v___x_1936_ == 0)
{
uint8_t v___x_1937_; 
v___x_1937_ = l_Lean_Level_isZero(v_v_1933_);
if (v___x_1937_ == 0)
{
uint8_t v___x_1938_; 
v___x_1938_ = l___private_Lean_Level_0__Lean_mkLevelMaxCore___lam__0(v_u_1932_, v_v_1933_);
if (v___x_1938_ == 0)
{
uint8_t v___x_1939_; 
v___x_1939_ = l___private_Lean_Level_0__Lean_mkLevelMaxCore___lam__0(v_v_1933_, v_u_1932_);
if (v___x_1939_ == 0)
{
lean_object* v___x_1940_; lean_object* v___x_1941_; uint8_t v___x_1942_; 
v___x_1940_ = l_Lean_Level_getLevelOffset(v_u_1932_);
v___x_1941_ = l_Lean_Level_getLevelOffset(v_v_1933_);
v___x_1942_ = lean_level_eq(v___x_1940_, v___x_1941_);
lean_dec(v___x_1941_);
lean_dec(v___x_1940_);
if (v___x_1942_ == 0)
{
lean_object* v___x_1943_; lean_object* v___x_1944_; 
v___x_1943_ = lean_box(0);
v___x_1944_ = lean_apply_1(v_elseK_1934_, v___x_1943_);
return v___x_1944_;
}
else
{
lean_object* v___x_1945_; lean_object* v___x_1946_; uint8_t v___x_1947_; 
lean_dec_ref(v_elseK_1934_);
v___x_1945_ = l_Lean_Level_getOffset(v_v_1933_);
v___x_1946_ = l_Lean_Level_getOffset(v_u_1932_);
v___x_1947_ = lean_nat_dec_le(v___x_1945_, v___x_1946_);
lean_dec(v___x_1946_);
lean_dec(v___x_1945_);
if (v___x_1947_ == 0)
{
lean_inc(v_v_1933_);
return v_v_1933_;
}
else
{
lean_inc(v_u_1932_);
return v_u_1932_;
}
}
}
else
{
lean_dec_ref(v_elseK_1934_);
lean_inc(v_v_1933_);
return v_v_1933_;
}
}
else
{
lean_dec_ref(v_elseK_1934_);
lean_inc(v_u_1932_);
return v_u_1932_;
}
}
else
{
lean_dec_ref(v_elseK_1934_);
lean_inc(v_u_1932_);
return v_u_1932_;
}
}
else
{
lean_dec_ref(v_elseK_1934_);
lean_inc(v_v_1933_);
return v_v_1933_;
}
}
else
{
lean_dec_ref(v_elseK_1934_);
lean_inc(v_u_1932_);
return v_u_1932_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_mkLevelMaxCore___boxed(lean_object* v_u_1948_, lean_object* v_v_1949_, lean_object* v_elseK_1950_){
_start:
{
lean_object* v_res_1951_; 
v_res_1951_ = l___private_Lean_Level_0__Lean_mkLevelMaxCore(v_u_1948_, v_v_1949_, v_elseK_1950_);
lean_dec(v_v_1949_);
lean_dec(v_u_1948_);
return v_res_1951_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLevelMax_x27(lean_object* v_u_1952_, lean_object* v_v_1953_){
_start:
{
uint8_t v___x_1954_; 
v___x_1954_ = lean_level_eq(v_u_1952_, v_v_1953_);
if (v___x_1954_ == 0)
{
uint8_t v___x_1955_; 
v___x_1955_ = l_Lean_Level_isZero(v_u_1952_);
if (v___x_1955_ == 0)
{
uint8_t v___x_1956_; 
v___x_1956_ = l_Lean_Level_isZero(v_v_1953_);
if (v___x_1956_ == 0)
{
uint8_t v___x_1957_; 
v___x_1957_ = l___private_Lean_Level_0__Lean_mkLevelMaxCore___lam__0(v_u_1952_, v_v_1953_);
if (v___x_1957_ == 0)
{
uint8_t v___x_1958_; 
v___x_1958_ = l___private_Lean_Level_0__Lean_mkLevelMaxCore___lam__0(v_v_1953_, v_u_1952_);
if (v___x_1958_ == 0)
{
lean_object* v___x_1959_; lean_object* v___x_1960_; uint8_t v___x_1961_; 
v___x_1959_ = l_Lean_Level_getLevelOffset(v_u_1952_);
v___x_1960_ = l_Lean_Level_getLevelOffset(v_v_1953_);
v___x_1961_ = lean_level_eq(v___x_1959_, v___x_1960_);
lean_dec(v___x_1960_);
lean_dec(v___x_1959_);
if (v___x_1961_ == 0)
{
lean_object* v___x_1962_; 
v___x_1962_ = l_Lean_Level_max___override(v_u_1952_, v_v_1953_);
return v___x_1962_;
}
else
{
lean_object* v___x_1963_; lean_object* v___x_1964_; uint8_t v___x_1965_; 
v___x_1963_ = l_Lean_Level_getOffset(v_v_1953_);
v___x_1964_ = l_Lean_Level_getOffset(v_u_1952_);
v___x_1965_ = lean_nat_dec_le(v___x_1963_, v___x_1964_);
lean_dec(v___x_1964_);
lean_dec(v___x_1963_);
if (v___x_1965_ == 0)
{
lean_dec(v_u_1952_);
return v_v_1953_;
}
else
{
lean_dec(v_v_1953_);
return v_u_1952_;
}
}
}
else
{
lean_dec(v_u_1952_);
return v_v_1953_;
}
}
else
{
lean_dec(v_v_1953_);
return v_u_1952_;
}
}
else
{
lean_dec(v_v_1953_);
return v_u_1952_;
}
}
else
{
lean_dec(v_u_1952_);
return v_v_1953_;
}
}
else
{
lean_dec(v_v_1953_);
return v_u_1952_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_simpLevelMax_x27(lean_object* v_u_1966_, lean_object* v_v_1967_, lean_object* v_d_1968_){
_start:
{
uint8_t v___x_1969_; 
v___x_1969_ = lean_level_eq(v_u_1966_, v_v_1967_);
if (v___x_1969_ == 0)
{
uint8_t v___x_1970_; 
v___x_1970_ = l_Lean_Level_isZero(v_u_1966_);
if (v___x_1970_ == 0)
{
uint8_t v___x_1971_; 
v___x_1971_ = l_Lean_Level_isZero(v_v_1967_);
if (v___x_1971_ == 0)
{
uint8_t v___x_1972_; 
v___x_1972_ = l___private_Lean_Level_0__Lean_mkLevelMaxCore___lam__0(v_u_1966_, v_v_1967_);
if (v___x_1972_ == 0)
{
uint8_t v___x_1973_; 
v___x_1973_ = l___private_Lean_Level_0__Lean_mkLevelMaxCore___lam__0(v_v_1967_, v_u_1966_);
if (v___x_1973_ == 0)
{
lean_object* v___x_1974_; lean_object* v___x_1975_; uint8_t v___x_1976_; 
v___x_1974_ = l_Lean_Level_getLevelOffset(v_u_1966_);
v___x_1975_ = l_Lean_Level_getLevelOffset(v_v_1967_);
v___x_1976_ = lean_level_eq(v___x_1974_, v___x_1975_);
lean_dec(v___x_1975_);
lean_dec(v___x_1974_);
if (v___x_1976_ == 0)
{
lean_inc(v_d_1968_);
return v_d_1968_;
}
else
{
lean_object* v___x_1977_; lean_object* v___x_1978_; uint8_t v___x_1979_; 
v___x_1977_ = l_Lean_Level_getOffset(v_v_1967_);
v___x_1978_ = l_Lean_Level_getOffset(v_u_1966_);
v___x_1979_ = lean_nat_dec_le(v___x_1977_, v___x_1978_);
lean_dec(v___x_1978_);
lean_dec(v___x_1977_);
if (v___x_1979_ == 0)
{
lean_inc(v_v_1967_);
return v_v_1967_;
}
else
{
lean_inc(v_u_1966_);
return v_u_1966_;
}
}
}
else
{
lean_inc(v_v_1967_);
return v_v_1967_;
}
}
else
{
lean_inc(v_u_1966_);
return v_u_1966_;
}
}
else
{
lean_inc(v_u_1966_);
return v_u_1966_;
}
}
else
{
lean_inc(v_v_1967_);
return v_v_1967_;
}
}
else
{
lean_inc(v_u_1966_);
return v_u_1966_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_simpLevelMax_x27___boxed(lean_object* v_u_1980_, lean_object* v_v_1981_, lean_object* v_d_1982_){
_start:
{
lean_object* v_res_1983_; 
v_res_1983_ = l_Lean_simpLevelMax_x27(v_u_1980_, v_v_1981_, v_d_1982_);
lean_dec(v_d_1982_);
lean_dec(v_v_1981_);
lean_dec(v_u_1980_);
return v_res_1983_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_mkLevelIMaxCore(lean_object* v_u_1984_, lean_object* v_v_1985_, lean_object* v_elseK_1986_){
_start:
{
uint8_t v___x_1987_; 
v___x_1987_ = l_Lean_Level_isNeverZero(v_v_1985_);
if (v___x_1987_ == 0)
{
uint8_t v___x_1988_; 
v___x_1988_ = l_Lean_Level_isZero(v_v_1985_);
if (v___x_1988_ == 0)
{
uint8_t v___x_1989_; 
v___x_1989_ = l_Lean_Level_isZero(v_u_1984_);
if (v___x_1989_ == 0)
{
uint8_t v___x_1990_; 
v___x_1990_ = lean_level_eq(v_u_1984_, v_v_1985_);
lean_dec(v_v_1985_);
if (v___x_1990_ == 0)
{
lean_object* v___x_1991_; lean_object* v___x_1992_; 
lean_dec(v_u_1984_);
v___x_1991_ = lean_box(0);
v___x_1992_ = lean_apply_1(v_elseK_1986_, v___x_1991_);
return v___x_1992_;
}
else
{
lean_dec_ref(v_elseK_1986_);
return v_u_1984_;
}
}
else
{
lean_dec_ref(v_elseK_1986_);
lean_dec(v_u_1984_);
return v_v_1985_;
}
}
else
{
lean_dec_ref(v_elseK_1986_);
lean_dec(v_u_1984_);
return v_v_1985_;
}
}
else
{
lean_object* v___x_1993_; 
lean_dec_ref(v_elseK_1986_);
v___x_1993_ = l_Lean_mkLevelMax_x27(v_u_1984_, v_v_1985_);
return v___x_1993_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkLevelIMax_x27(lean_object* v_u_1994_, lean_object* v_v_1995_){
_start:
{
uint8_t v___x_1996_; 
v___x_1996_ = l_Lean_Level_isNeverZero(v_v_1995_);
if (v___x_1996_ == 0)
{
uint8_t v___x_1997_; 
v___x_1997_ = l_Lean_Level_isZero(v_v_1995_);
if (v___x_1997_ == 0)
{
uint8_t v___x_1998_; 
v___x_1998_ = l_Lean_Level_isZero(v_u_1994_);
if (v___x_1998_ == 0)
{
uint8_t v___x_1999_; 
v___x_1999_ = lean_level_eq(v_u_1994_, v_v_1995_);
if (v___x_1999_ == 0)
{
lean_object* v___x_2000_; 
v___x_2000_ = l_Lean_Level_imax___override(v_u_1994_, v_v_1995_);
return v___x_2000_;
}
else
{
lean_dec(v_v_1995_);
return v_u_1994_;
}
}
else
{
lean_dec(v_u_1994_);
return v_v_1995_;
}
}
else
{
lean_dec(v_u_1994_);
return v_v_1995_;
}
}
else
{
lean_object* v___x_2001_; 
v___x_2001_ = l_Lean_mkLevelMax_x27(v_u_1994_, v_v_1995_);
return v___x_2001_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_simpLevelIMax_x27(lean_object* v_u_2002_, lean_object* v_v_2003_, lean_object* v_d_2004_){
_start:
{
uint8_t v___x_2005_; 
v___x_2005_ = l_Lean_Level_isNeverZero(v_v_2003_);
if (v___x_2005_ == 0)
{
uint8_t v___x_2006_; 
v___x_2006_ = l_Lean_Level_isZero(v_v_2003_);
if (v___x_2006_ == 0)
{
uint8_t v___x_2007_; 
v___x_2007_ = l_Lean_Level_isZero(v_u_2002_);
if (v___x_2007_ == 0)
{
uint8_t v___x_2008_; 
v___x_2008_ = lean_level_eq(v_u_2002_, v_v_2003_);
lean_dec(v_v_2003_);
if (v___x_2008_ == 0)
{
lean_dec(v_u_2002_);
lean_inc(v_d_2004_);
return v_d_2004_;
}
else
{
return v_u_2002_;
}
}
else
{
lean_dec(v_u_2002_);
return v_v_2003_;
}
}
else
{
lean_dec(v_u_2002_);
return v_v_2003_;
}
}
else
{
lean_object* v___x_2009_; 
v___x_2009_ = l_Lean_mkLevelMax_x27(v_u_2002_, v_v_2003_);
return v___x_2009_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_simpLevelIMax_x27___boxed(lean_object* v_u_2010_, lean_object* v_v_2011_, lean_object* v_d_2012_){
_start:
{
lean_object* v_res_2013_; 
v_res_2013_ = l_Lean_simpLevelIMax_x27(v_u_2010_, v_v_2011_, v_d_2012_);
lean_dec(v_d_2012_);
return v_res_2013_;
}
}
static lean_object* _init_l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl___closed__2(void){
_start:
{
lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; 
v___x_2016_ = ((lean_object*)(l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl___closed__1));
v___x_2017_ = lean_unsigned_to_nat(14u);
v___x_2018_ = lean_unsigned_to_nat(567u);
v___x_2019_ = ((lean_object*)(l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl___closed__0));
v___x_2020_ = ((lean_object*)(l_Lean_Level_mvarId_x21___closed__0));
v___x_2021_ = l_mkPanicMessageWithDecl(v___x_2020_, v___x_2019_, v___x_2018_, v___x_2017_, v___x_2016_);
return v___x_2021_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl(lean_object* v_lvl_2022_, lean_object* v_newLvl_2023_){
_start:
{
if (lean_obj_tag(v_lvl_2022_) == 1)
{
lean_object* v_a_2024_; size_t v___x_2025_; size_t v___x_2026_; uint8_t v___x_2027_; 
v_a_2024_ = lean_ctor_get(v_lvl_2022_, 0);
v___x_2025_ = lean_ptr_addr(v_a_2024_);
v___x_2026_ = lean_ptr_addr(v_newLvl_2023_);
v___x_2027_ = lean_usize_dec_eq(v___x_2025_, v___x_2026_);
if (v___x_2027_ == 0)
{
lean_object* v___x_2028_; 
v___x_2028_ = l_Lean_Level_succ___override(v_newLvl_2023_);
return v___x_2028_;
}
else
{
lean_dec(v_newLvl_2023_);
lean_inc_ref(v_lvl_2022_);
return v_lvl_2022_;
}
}
else
{
lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; 
lean_dec(v_newLvl_2023_);
v___x_2029_ = lean_box(0);
v___x_2030_ = lean_obj_once(&l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl___closed__2, &l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl___closed__2_once, _init_l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl___closed__2);
v___x_2031_ = l_panic___redArg(v___x_2029_, v___x_2030_);
return v___x_2031_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl___boxed(lean_object* v_lvl_2032_, lean_object* v_newLvl_2033_){
_start:
{
lean_object* v_res_2034_; 
v_res_2034_ = l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl(v_lvl_2032_, v_newLvl_2033_);
lean_dec(v_lvl_2032_);
return v_res_2034_;
}
}
static lean_object* _init_l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl___closed__2(void){
_start:
{
lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; 
v___x_2037_ = ((lean_object*)(l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl___closed__1));
v___x_2038_ = lean_unsigned_to_nat(19u);
v___x_2039_ = lean_unsigned_to_nat(578u);
v___x_2040_ = ((lean_object*)(l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl___closed__0));
v___x_2041_ = ((lean_object*)(l_Lean_Level_mvarId_x21___closed__0));
v___x_2042_ = l_mkPanicMessageWithDecl(v___x_2041_, v___x_2040_, v___x_2039_, v___x_2038_, v___x_2037_);
return v___x_2042_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl(lean_object* v_lvl_2043_, lean_object* v_newLhs_2044_, lean_object* v_newRhs_2045_){
_start:
{
uint8_t v___y_2047_; 
if (lean_obj_tag(v_lvl_2043_) == 2)
{
lean_object* v_a_2050_; lean_object* v_a_2051_; size_t v___x_2052_; size_t v___x_2053_; uint8_t v___x_2054_; 
v_a_2050_ = lean_ctor_get(v_lvl_2043_, 0);
v_a_2051_ = lean_ctor_get(v_lvl_2043_, 1);
v___x_2052_ = lean_ptr_addr(v_a_2050_);
v___x_2053_ = lean_ptr_addr(v_newLhs_2044_);
v___x_2054_ = lean_usize_dec_eq(v___x_2052_, v___x_2053_);
if (v___x_2054_ == 0)
{
v___y_2047_ = v___x_2054_;
goto v___jp_2046_;
}
else
{
size_t v___x_2055_; size_t v___x_2056_; uint8_t v___x_2057_; 
v___x_2055_ = lean_ptr_addr(v_a_2051_);
v___x_2056_ = lean_ptr_addr(v_newRhs_2045_);
v___x_2057_ = lean_usize_dec_eq(v___x_2055_, v___x_2056_);
v___y_2047_ = v___x_2057_;
goto v___jp_2046_;
}
}
else
{
lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; 
lean_dec(v_newRhs_2045_);
lean_dec(v_newLhs_2044_);
v___x_2058_ = lean_box(0);
v___x_2059_ = lean_obj_once(&l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl___closed__2, &l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl___closed__2_once, _init_l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl___closed__2);
v___x_2060_ = l_panic___redArg(v___x_2058_, v___x_2059_);
return v___x_2060_;
}
v___jp_2046_:
{
if (v___y_2047_ == 0)
{
lean_object* v___x_2048_; 
v___x_2048_ = l_Lean_mkLevelMax_x27(v_newLhs_2044_, v_newRhs_2045_);
return v___x_2048_;
}
else
{
lean_object* v___x_2049_; 
v___x_2049_ = l_Lean_simpLevelMax_x27(v_newLhs_2044_, v_newRhs_2045_, v_lvl_2043_);
lean_dec(v_newRhs_2045_);
lean_dec(v_newLhs_2044_);
return v___x_2049_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl___boxed(lean_object* v_lvl_2061_, lean_object* v_newLhs_2062_, lean_object* v_newRhs_2063_){
_start:
{
lean_object* v_res_2064_; 
v_res_2064_ = l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl(v_lvl_2061_, v_newLhs_2062_, v_newRhs_2063_);
lean_dec(v_lvl_2061_);
return v_res_2064_;
}
}
static lean_object* _init_l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl___closed__2(void){
_start:
{
lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; 
v___x_2067_ = ((lean_object*)(l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl___closed__1));
v___x_2068_ = lean_unsigned_to_nat(20u);
v___x_2069_ = lean_unsigned_to_nat(589u);
v___x_2070_ = ((lean_object*)(l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl___closed__0));
v___x_2071_ = ((lean_object*)(l_Lean_Level_mvarId_x21___closed__0));
v___x_2072_ = l_mkPanicMessageWithDecl(v___x_2071_, v___x_2070_, v___x_2069_, v___x_2068_, v___x_2067_);
return v___x_2072_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl(lean_object* v_lvl_2073_, lean_object* v_newLhs_2074_, lean_object* v_newRhs_2075_){
_start:
{
uint8_t v___y_2077_; 
if (lean_obj_tag(v_lvl_2073_) == 3)
{
lean_object* v_a_2080_; lean_object* v_a_2081_; size_t v___x_2082_; size_t v___x_2083_; uint8_t v___x_2084_; 
v_a_2080_ = lean_ctor_get(v_lvl_2073_, 0);
v_a_2081_ = lean_ctor_get(v_lvl_2073_, 1);
v___x_2082_ = lean_ptr_addr(v_a_2080_);
v___x_2083_ = lean_ptr_addr(v_newLhs_2074_);
v___x_2084_ = lean_usize_dec_eq(v___x_2082_, v___x_2083_);
if (v___x_2084_ == 0)
{
v___y_2077_ = v___x_2084_;
goto v___jp_2076_;
}
else
{
size_t v___x_2085_; size_t v___x_2086_; uint8_t v___x_2087_; 
v___x_2085_ = lean_ptr_addr(v_a_2081_);
v___x_2086_ = lean_ptr_addr(v_newRhs_2075_);
v___x_2087_ = lean_usize_dec_eq(v___x_2085_, v___x_2086_);
v___y_2077_ = v___x_2087_;
goto v___jp_2076_;
}
}
else
{
lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; 
lean_dec(v_newRhs_2075_);
lean_dec(v_newLhs_2074_);
v___x_2088_ = lean_box(0);
v___x_2089_ = lean_obj_once(&l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl___closed__2, &l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl___closed__2_once, _init_l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl___closed__2);
v___x_2090_ = l_panic___redArg(v___x_2088_, v___x_2089_);
return v___x_2090_;
}
v___jp_2076_:
{
if (v___y_2077_ == 0)
{
lean_object* v___x_2078_; 
v___x_2078_ = l_Lean_mkLevelIMax_x27(v_newLhs_2074_, v_newRhs_2075_);
return v___x_2078_;
}
else
{
lean_object* v___x_2079_; 
v___x_2079_ = l_Lean_simpLevelIMax_x27(v_newLhs_2074_, v_newRhs_2075_, v_lvl_2073_);
return v___x_2079_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl___boxed(lean_object* v_lvl_2091_, lean_object* v_newLhs_2092_, lean_object* v_newRhs_2093_){
_start:
{
lean_object* v_res_2094_; 
v_res_2094_ = l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl(v_lvl_2091_, v_newLhs_2092_, v_newRhs_2093_);
lean_dec(v_lvl_2091_);
return v_res_2094_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_mkNaryMax(lean_object* v_x_2095_){
_start:
{
if (lean_obj_tag(v_x_2095_) == 0)
{
lean_object* v___x_2096_; 
v___x_2096_ = lean_box(0);
return v___x_2096_;
}
else
{
lean_object* v_tail_2097_; 
v_tail_2097_ = lean_ctor_get(v_x_2095_, 1);
if (lean_obj_tag(v_tail_2097_) == 0)
{
lean_object* v_head_2098_; 
v_head_2098_ = lean_ctor_get(v_x_2095_, 0);
lean_inc(v_head_2098_);
lean_dec_ref_known(v_x_2095_, 2);
return v_head_2098_;
}
else
{
lean_object* v_head_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; 
lean_inc(v_tail_2097_);
v_head_2099_ = lean_ctor_get(v_x_2095_, 0);
lean_inc(v_head_2099_);
lean_dec_ref_known(v_x_2095_, 2);
v___x_2100_ = l_Lean_Level_mkNaryMax(v_tail_2097_);
v___x_2101_ = l_Lean_mkLevelMax_x27(v_head_2099_, v___x_2100_);
return v___x_2101_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_substParams_go(lean_object* v_s_2102_, lean_object* v_u_2103_){
_start:
{
switch(lean_obj_tag(v_u_2103_))
{
case 0:
{
lean_dec_ref(v_s_2102_);
return v_u_2103_;
}
case 1:
{
lean_object* v_a_2104_; uint8_t v___x_2105_; 
v_a_2104_ = lean_ctor_get(v_u_2103_, 0);
v___x_2105_ = l_Lean_Level_hasParam(v_u_2103_);
if (v___x_2105_ == 0)
{
lean_dec_ref(v_s_2102_);
return v_u_2103_;
}
else
{
lean_object* v___x_2106_; size_t v___x_2107_; size_t v___x_2108_; uint8_t v___x_2109_; 
lean_inc(v_a_2104_);
v___x_2106_ = l___private_Lean_Level_0__Lean_Level_substParams_go(v_s_2102_, v_a_2104_);
v___x_2107_ = lean_ptr_addr(v_a_2104_);
v___x_2108_ = lean_ptr_addr(v___x_2106_);
v___x_2109_ = lean_usize_dec_eq(v___x_2107_, v___x_2108_);
if (v___x_2109_ == 0)
{
lean_object* v___x_2110_; 
lean_dec_ref_known(v_u_2103_, 1);
v___x_2110_ = l_Lean_Level_succ___override(v___x_2106_);
return v___x_2110_;
}
else
{
lean_dec(v___x_2106_);
return v_u_2103_;
}
}
}
case 2:
{
lean_object* v_a_2111_; lean_object* v_a_2112_; uint8_t v___x_2113_; 
v_a_2111_ = lean_ctor_get(v_u_2103_, 0);
v_a_2112_ = lean_ctor_get(v_u_2103_, 1);
v___x_2113_ = l_Lean_Level_hasParam(v_u_2103_);
if (v___x_2113_ == 0)
{
lean_dec_ref(v_s_2102_);
return v_u_2103_;
}
else
{
lean_object* v___x_2114_; lean_object* v___x_2115_; uint8_t v___y_2117_; size_t v___x_2120_; size_t v___x_2121_; uint8_t v___x_2122_; 
lean_inc(v_a_2111_);
lean_inc_ref(v_s_2102_);
v___x_2114_ = l___private_Lean_Level_0__Lean_Level_substParams_go(v_s_2102_, v_a_2111_);
lean_inc(v_a_2112_);
v___x_2115_ = l___private_Lean_Level_0__Lean_Level_substParams_go(v_s_2102_, v_a_2112_);
v___x_2120_ = lean_ptr_addr(v_a_2111_);
v___x_2121_ = lean_ptr_addr(v___x_2114_);
v___x_2122_ = lean_usize_dec_eq(v___x_2120_, v___x_2121_);
if (v___x_2122_ == 0)
{
v___y_2117_ = v___x_2122_;
goto v___jp_2116_;
}
else
{
size_t v___x_2123_; size_t v___x_2124_; uint8_t v___x_2125_; 
v___x_2123_ = lean_ptr_addr(v_a_2112_);
v___x_2124_ = lean_ptr_addr(v___x_2115_);
v___x_2125_ = lean_usize_dec_eq(v___x_2123_, v___x_2124_);
v___y_2117_ = v___x_2125_;
goto v___jp_2116_;
}
v___jp_2116_:
{
if (v___y_2117_ == 0)
{
lean_object* v___x_2118_; 
lean_dec_ref_known(v_u_2103_, 2);
v___x_2118_ = l_Lean_mkLevelMax_x27(v___x_2114_, v___x_2115_);
return v___x_2118_;
}
else
{
lean_object* v___x_2119_; 
v___x_2119_ = l_Lean_simpLevelMax_x27(v___x_2114_, v___x_2115_, v_u_2103_);
lean_dec_ref_known(v_u_2103_, 2);
lean_dec(v___x_2115_);
lean_dec(v___x_2114_);
return v___x_2119_;
}
}
}
}
case 3:
{
lean_object* v_a_2126_; lean_object* v_a_2127_; uint8_t v___x_2128_; 
v_a_2126_ = lean_ctor_get(v_u_2103_, 0);
v_a_2127_ = lean_ctor_get(v_u_2103_, 1);
v___x_2128_ = l_Lean_Level_hasParam(v_u_2103_);
if (v___x_2128_ == 0)
{
lean_dec_ref(v_s_2102_);
return v_u_2103_;
}
else
{
lean_object* v___x_2129_; lean_object* v___x_2130_; uint8_t v___y_2132_; size_t v___x_2135_; size_t v___x_2136_; uint8_t v___x_2137_; 
lean_inc(v_a_2126_);
lean_inc_ref(v_s_2102_);
v___x_2129_ = l___private_Lean_Level_0__Lean_Level_substParams_go(v_s_2102_, v_a_2126_);
lean_inc(v_a_2127_);
v___x_2130_ = l___private_Lean_Level_0__Lean_Level_substParams_go(v_s_2102_, v_a_2127_);
v___x_2135_ = lean_ptr_addr(v_a_2126_);
v___x_2136_ = lean_ptr_addr(v___x_2129_);
v___x_2137_ = lean_usize_dec_eq(v___x_2135_, v___x_2136_);
if (v___x_2137_ == 0)
{
v___y_2132_ = v___x_2137_;
goto v___jp_2131_;
}
else
{
size_t v___x_2138_; size_t v___x_2139_; uint8_t v___x_2140_; 
v___x_2138_ = lean_ptr_addr(v_a_2127_);
v___x_2139_ = lean_ptr_addr(v___x_2130_);
v___x_2140_ = lean_usize_dec_eq(v___x_2138_, v___x_2139_);
v___y_2132_ = v___x_2140_;
goto v___jp_2131_;
}
v___jp_2131_:
{
if (v___y_2132_ == 0)
{
lean_object* v___x_2133_; 
lean_dec_ref_known(v_u_2103_, 2);
v___x_2133_ = l_Lean_mkLevelIMax_x27(v___x_2129_, v___x_2130_);
return v___x_2133_;
}
else
{
lean_object* v___x_2134_; 
v___x_2134_ = l_Lean_simpLevelIMax_x27(v___x_2129_, v___x_2130_, v_u_2103_);
lean_dec_ref_known(v_u_2103_, 2);
return v___x_2134_;
}
}
}
}
case 4:
{
lean_object* v_a_2141_; lean_object* v___x_2142_; 
v_a_2141_ = lean_ctor_get(v_u_2103_, 0);
lean_inc(v_a_2141_);
v___x_2142_ = lean_apply_1(v_s_2102_, v_a_2141_);
if (lean_obj_tag(v___x_2142_) == 0)
{
return v_u_2103_;
}
else
{
lean_object* v_val_2143_; 
lean_dec_ref_known(v_u_2103_, 1);
v_val_2143_ = lean_ctor_get(v___x_2142_, 0);
lean_inc(v_val_2143_);
lean_dec_ref_known(v___x_2142_, 1);
return v_val_2143_;
}
}
default: 
{
lean_dec_ref(v_s_2102_);
return v_u_2103_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_substParams(lean_object* v_u_2144_, lean_object* v_s_2145_){
_start:
{
lean_object* v___x_2146_; 
v___x_2146_ = l___private_Lean_Level_0__Lean_Level_substParams_go(v_s_2145_, v_u_2144_);
return v___x_2146_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_getParamSubst(lean_object* v_x_2147_, lean_object* v_x_2148_, lean_object* v_x_2149_){
_start:
{
if (lean_obj_tag(v_x_2147_) == 1)
{
if (lean_obj_tag(v_x_2148_) == 1)
{
lean_object* v_head_2150_; lean_object* v_tail_2151_; lean_object* v_head_2152_; lean_object* v_tail_2153_; uint8_t v___x_2154_; 
v_head_2150_ = lean_ctor_get(v_x_2147_, 0);
v_tail_2151_ = lean_ctor_get(v_x_2147_, 1);
v_head_2152_ = lean_ctor_get(v_x_2148_, 0);
v_tail_2153_ = lean_ctor_get(v_x_2148_, 1);
v___x_2154_ = lean_name_eq(v_head_2150_, v_x_2149_);
if (v___x_2154_ == 0)
{
v_x_2147_ = v_tail_2151_;
v_x_2148_ = v_tail_2153_;
goto _start;
}
else
{
lean_object* v___x_2156_; 
lean_inc(v_head_2152_);
v___x_2156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2156_, 0, v_head_2152_);
return v___x_2156_;
}
}
else
{
lean_object* v___x_2157_; 
v___x_2157_ = lean_box(0);
return v___x_2157_;
}
}
else
{
lean_object* v___x_2158_; 
v___x_2158_ = lean_box(0);
return v___x_2158_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_getParamSubst___boxed(lean_object* v_x_2159_, lean_object* v_x_2160_, lean_object* v_x_2161_){
_start:
{
lean_object* v_res_2162_; 
v_res_2162_ = l_Lean_Level_getParamSubst(v_x_2159_, v_x_2160_, v_x_2161_);
lean_dec(v_x_2161_);
lean_dec(v_x_2160_);
lean_dec(v_x_2159_);
return v_res_2162_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_instantiateParams(lean_object* v_u_2163_, lean_object* v_paramNames_2164_, lean_object* v_vs_2165_){
_start:
{
lean_object* v___x_2166_; lean_object* v___x_2167_; 
v___x_2166_ = lean_alloc_closure((void*)(l_Lean_Level_getParamSubst___boxed), 3, 2);
lean_closure_set(v___x_2166_, 0, v_paramNames_2164_);
lean_closure_set(v___x_2166_, 1, v_vs_2165_);
v___x_2167_ = l___private_Lean_Level_0__Lean_Level_substParams_go(v___x_2166_, v_u_2163_);
return v___x_2167_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Level_0__Lean_Level_geq_go(lean_object* v_u_2168_, lean_object* v_v_2169_){
_start:
{
uint8_t v___y_2171_; uint8_t v___y_2185_; lean_object* v_u_u2081_2187_; lean_object* v_u_u2082_2188_; lean_object* v_v_2189_; uint8_t v___x_2192_; 
v___x_2192_ = lean_level_eq(v_u_2168_, v_v_2169_);
if (v___x_2192_ == 0)
{
switch(lean_obj_tag(v_v_2169_))
{
case 0:
{
uint8_t v___x_2193_; 
v___x_2193_ = 1;
return v___x_2193_;
}
case 2:
{
lean_object* v_a_2194_; lean_object* v_a_2195_; uint8_t v___x_2196_; 
v_a_2194_ = lean_ctor_get(v_v_2169_, 0);
v_a_2195_ = lean_ctor_get(v_v_2169_, 1);
v___x_2196_ = l___private_Lean_Level_0__Lean_Level_geq_go(v_u_2168_, v_a_2194_);
if (v___x_2196_ == 0)
{
return v___x_2196_;
}
else
{
v_v_2169_ = v_a_2195_;
goto _start;
}
}
case 1:
{
switch(lean_obj_tag(v_u_2168_))
{
case 2:
{
lean_object* v_a_2198_; lean_object* v_a_2199_; 
v_a_2198_ = lean_ctor_get(v_u_2168_, 0);
v_a_2199_ = lean_ctor_get(v_u_2168_, 1);
v_u_u2081_2187_ = v_a_2198_;
v_u_u2082_2188_ = v_a_2199_;
v_v_2189_ = v_v_2169_;
goto v___jp_2186_;
}
case 3:
{
lean_object* v_a_2200_; 
v_a_2200_ = lean_ctor_get(v_u_2168_, 1);
v_u_2168_ = v_a_2200_;
goto _start;
}
case 1:
{
lean_object* v_a_2202_; lean_object* v_a_2203_; 
v_a_2202_ = lean_ctor_get(v_v_2169_, 0);
v_a_2203_ = lean_ctor_get(v_u_2168_, 0);
v_u_2168_ = v_a_2203_;
v_v_2169_ = v_a_2202_;
goto _start;
}
default: 
{
goto v___jp_2175_;
}
}
}
default: 
{
switch(lean_obj_tag(v_u_2168_))
{
case 2:
{
lean_object* v_a_2205_; lean_object* v_a_2206_; 
v_a_2205_ = lean_ctor_get(v_u_2168_, 0);
v_a_2206_ = lean_ctor_get(v_u_2168_, 1);
v_u_u2081_2187_ = v_a_2205_;
v_u_u2082_2188_ = v_a_2206_;
v_v_2189_ = v_v_2169_;
goto v___jp_2186_;
}
case 3:
{
lean_object* v_a_2207_; 
v_a_2207_ = lean_ctor_get(v_u_2168_, 1);
v_u_2168_ = v_a_2207_;
goto _start;
}
default: 
{
goto v___jp_2175_;
}
}
}
}
}
else
{
return v___x_2192_;
}
v___jp_2170_:
{
if (v___y_2171_ == 0)
{
return v___y_2171_;
}
else
{
lean_object* v___x_2172_; lean_object* v___x_2173_; uint8_t v___x_2174_; 
v___x_2172_ = l_Lean_Level_getOffset(v_v_2169_);
v___x_2173_ = l_Lean_Level_getOffset(v_u_2168_);
v___x_2174_ = lean_nat_dec_le(v___x_2172_, v___x_2173_);
lean_dec(v___x_2173_);
lean_dec(v___x_2172_);
return v___x_2174_;
}
}
v___jp_2175_:
{
if (lean_obj_tag(v_v_2169_) == 3)
{
lean_object* v_a_2176_; lean_object* v_a_2177_; uint8_t v___x_2178_; 
v_a_2176_ = lean_ctor_get(v_v_2169_, 0);
v_a_2177_ = lean_ctor_get(v_v_2169_, 1);
v___x_2178_ = l___private_Lean_Level_0__Lean_Level_geq_go(v_u_2168_, v_a_2176_);
if (v___x_2178_ == 0)
{
return v___x_2178_;
}
else
{
v_v_2169_ = v_a_2177_;
goto _start;
}
}
else
{
lean_object* v_v_x27_2180_; lean_object* v___x_2181_; uint8_t v___x_2182_; 
v_v_x27_2180_ = l_Lean_Level_getLevelOffset(v_v_2169_);
v___x_2181_ = l_Lean_Level_getLevelOffset(v_u_2168_);
v___x_2182_ = lean_level_eq(v___x_2181_, v_v_x27_2180_);
lean_dec(v___x_2181_);
if (v___x_2182_ == 0)
{
uint8_t v___x_2183_; 
v___x_2183_ = l_Lean_Level_isZero(v_v_x27_2180_);
lean_dec(v_v_x27_2180_);
v___y_2171_ = v___x_2183_;
goto v___jp_2170_;
}
else
{
lean_dec(v_v_x27_2180_);
v___y_2171_ = v___x_2182_;
goto v___jp_2170_;
}
}
}
v___jp_2184_:
{
if (v___y_2185_ == 0)
{
goto v___jp_2175_;
}
else
{
return v___y_2185_;
}
}
v___jp_2186_:
{
uint8_t v___x_2190_; 
v___x_2190_ = l___private_Lean_Level_0__Lean_Level_geq_go(v_u_u2081_2187_, v_v_2189_);
if (v___x_2190_ == 0)
{
uint8_t v___x_2191_; 
v___x_2191_ = l___private_Lean_Level_0__Lean_Level_geq_go(v_u_u2082_2188_, v_v_2189_);
v___y_2185_ = v___x_2191_;
goto v___jp_2184_;
}
else
{
v___y_2185_ = v___x_2190_;
goto v___jp_2184_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_geq_go___boxed(lean_object* v_u_2209_, lean_object* v_v_2210_){
_start:
{
uint8_t v_res_2211_; lean_object* v_r_2212_; 
v_res_2211_ = l___private_Lean_Level_0__Lean_Level_geq_go(v_u_2209_, v_v_2210_);
lean_dec(v_v_2210_);
lean_dec(v_u_2209_);
v_r_2212_ = lean_box(v_res_2211_);
return v_r_2212_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_geq_go_match__1_splitter___redArg(lean_object* v_u_2213_, lean_object* v_v_2214_, lean_object* v_h__1_2215_, lean_object* v_h__2_2216_, lean_object* v_h__3_2217_, lean_object* v_h__4_2218_, lean_object* v_h__5_2219_, lean_object* v_h__6_2220_){
_start:
{
switch(lean_obj_tag(v_v_2214_))
{
case 0:
{
lean_object* v___x_2221_; 
lean_dec(v_h__6_2220_);
lean_dec(v_h__5_2219_);
lean_dec(v_h__4_2218_);
lean_dec(v_h__3_2217_);
lean_dec(v_h__2_2216_);
v___x_2221_ = lean_apply_1(v_h__1_2215_, v_u_2213_);
return v___x_2221_;
}
case 2:
{
lean_object* v_a_2222_; lean_object* v_a_2223_; lean_object* v___x_2224_; 
lean_dec(v_h__6_2220_);
lean_dec(v_h__5_2219_);
lean_dec(v_h__4_2218_);
lean_dec(v_h__3_2217_);
lean_dec(v_h__1_2215_);
v_a_2222_ = lean_ctor_get(v_v_2214_, 0);
lean_inc(v_a_2222_);
v_a_2223_ = lean_ctor_get(v_v_2214_, 1);
lean_inc(v_a_2223_);
lean_dec_ref_known(v_v_2214_, 2);
v___x_2224_ = lean_apply_3(v_h__2_2216_, v_u_2213_, v_a_2222_, v_a_2223_);
return v___x_2224_;
}
case 1:
{
lean_dec(v_h__2_2216_);
lean_dec(v_h__1_2215_);
switch(lean_obj_tag(v_u_2213_))
{
case 2:
{
lean_object* v_a_2225_; lean_object* v_a_2226_; lean_object* v___x_2227_; 
lean_dec(v_h__6_2220_);
lean_dec(v_h__5_2219_);
lean_dec(v_h__4_2218_);
v_a_2225_ = lean_ctor_get(v_u_2213_, 0);
lean_inc(v_a_2225_);
v_a_2226_ = lean_ctor_get(v_u_2213_, 1);
lean_inc(v_a_2226_);
lean_dec_ref_known(v_u_2213_, 2);
v___x_2227_ = lean_apply_5(v_h__3_2217_, v_a_2225_, v_a_2226_, v_v_2214_, lean_box(0), lean_box(0));
return v___x_2227_;
}
case 3:
{
lean_object* v_a_2228_; lean_object* v_a_2229_; lean_object* v___x_2230_; 
lean_dec(v_h__6_2220_);
lean_dec(v_h__5_2219_);
lean_dec(v_h__3_2217_);
v_a_2228_ = lean_ctor_get(v_u_2213_, 0);
lean_inc(v_a_2228_);
v_a_2229_ = lean_ctor_get(v_u_2213_, 1);
lean_inc(v_a_2229_);
lean_dec_ref_known(v_u_2213_, 2);
v___x_2230_ = lean_apply_5(v_h__4_2218_, v_a_2228_, v_a_2229_, v_v_2214_, lean_box(0), lean_box(0));
return v___x_2230_;
}
case 1:
{
lean_object* v_a_2231_; lean_object* v_a_2232_; lean_object* v___x_2233_; 
lean_dec(v_h__6_2220_);
lean_dec(v_h__4_2218_);
lean_dec(v_h__3_2217_);
v_a_2231_ = lean_ctor_get(v_v_2214_, 0);
lean_inc(v_a_2231_);
lean_dec_ref_known(v_v_2214_, 1);
v_a_2232_ = lean_ctor_get(v_u_2213_, 0);
lean_inc(v_a_2232_);
lean_dec_ref_known(v_u_2213_, 1);
v___x_2233_ = lean_apply_2(v_h__5_2219_, v_a_2232_, v_a_2231_);
return v___x_2233_;
}
default: 
{
lean_object* v___x_2234_; 
lean_dec(v_h__5_2219_);
lean_dec(v_h__4_2218_);
lean_dec(v_h__3_2217_);
v___x_2234_ = lean_apply_7(v_h__6_2220_, v_u_2213_, v_v_2214_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_2234_;
}
}
}
default: 
{
lean_dec(v_h__5_2219_);
lean_dec(v_h__2_2216_);
lean_dec(v_h__1_2215_);
switch(lean_obj_tag(v_u_2213_))
{
case 2:
{
lean_object* v_a_2235_; lean_object* v_a_2236_; lean_object* v___x_2237_; 
lean_dec(v_h__6_2220_);
lean_dec(v_h__4_2218_);
v_a_2235_ = lean_ctor_get(v_u_2213_, 0);
lean_inc(v_a_2235_);
v_a_2236_ = lean_ctor_get(v_u_2213_, 1);
lean_inc(v_a_2236_);
lean_dec_ref_known(v_u_2213_, 2);
v___x_2237_ = lean_apply_5(v_h__3_2217_, v_a_2235_, v_a_2236_, v_v_2214_, lean_box(0), lean_box(0));
return v___x_2237_;
}
case 3:
{
lean_object* v_a_2238_; lean_object* v_a_2239_; lean_object* v___x_2240_; 
lean_dec(v_h__6_2220_);
lean_dec(v_h__3_2217_);
v_a_2238_ = lean_ctor_get(v_u_2213_, 0);
lean_inc(v_a_2238_);
v_a_2239_ = lean_ctor_get(v_u_2213_, 1);
lean_inc(v_a_2239_);
lean_dec_ref_known(v_u_2213_, 2);
v___x_2240_ = lean_apply_5(v_h__4_2218_, v_a_2238_, v_a_2239_, v_v_2214_, lean_box(0), lean_box(0));
return v___x_2240_;
}
default: 
{
lean_object* v___x_2241_; 
lean_dec(v_h__4_2218_);
lean_dec(v_h__3_2217_);
v___x_2241_ = lean_apply_7(v_h__6_2220_, v_u_2213_, v_v_2214_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_2241_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_geq_go_match__1_splitter(lean_object* v_motive_2242_, lean_object* v_u_2243_, lean_object* v_v_2244_, lean_object* v_h__1_2245_, lean_object* v_h__2_2246_, lean_object* v_h__3_2247_, lean_object* v_h__4_2248_, lean_object* v_h__5_2249_, lean_object* v_h__6_2250_){
_start:
{
switch(lean_obj_tag(v_v_2244_))
{
case 0:
{
lean_object* v___x_2251_; 
lean_dec(v_h__6_2250_);
lean_dec(v_h__5_2249_);
lean_dec(v_h__4_2248_);
lean_dec(v_h__3_2247_);
lean_dec(v_h__2_2246_);
v___x_2251_ = lean_apply_1(v_h__1_2245_, v_u_2243_);
return v___x_2251_;
}
case 2:
{
lean_object* v_a_2252_; lean_object* v_a_2253_; lean_object* v___x_2254_; 
lean_dec(v_h__6_2250_);
lean_dec(v_h__5_2249_);
lean_dec(v_h__4_2248_);
lean_dec(v_h__3_2247_);
lean_dec(v_h__1_2245_);
v_a_2252_ = lean_ctor_get(v_v_2244_, 0);
lean_inc(v_a_2252_);
v_a_2253_ = lean_ctor_get(v_v_2244_, 1);
lean_inc(v_a_2253_);
lean_dec_ref_known(v_v_2244_, 2);
v___x_2254_ = lean_apply_3(v_h__2_2246_, v_u_2243_, v_a_2252_, v_a_2253_);
return v___x_2254_;
}
case 1:
{
lean_dec(v_h__2_2246_);
lean_dec(v_h__1_2245_);
switch(lean_obj_tag(v_u_2243_))
{
case 2:
{
lean_object* v_a_2255_; lean_object* v_a_2256_; lean_object* v___x_2257_; 
lean_dec(v_h__6_2250_);
lean_dec(v_h__5_2249_);
lean_dec(v_h__4_2248_);
v_a_2255_ = lean_ctor_get(v_u_2243_, 0);
lean_inc(v_a_2255_);
v_a_2256_ = lean_ctor_get(v_u_2243_, 1);
lean_inc(v_a_2256_);
lean_dec_ref_known(v_u_2243_, 2);
v___x_2257_ = lean_apply_5(v_h__3_2247_, v_a_2255_, v_a_2256_, v_v_2244_, lean_box(0), lean_box(0));
return v___x_2257_;
}
case 3:
{
lean_object* v_a_2258_; lean_object* v_a_2259_; lean_object* v___x_2260_; 
lean_dec(v_h__6_2250_);
lean_dec(v_h__5_2249_);
lean_dec(v_h__3_2247_);
v_a_2258_ = lean_ctor_get(v_u_2243_, 0);
lean_inc(v_a_2258_);
v_a_2259_ = lean_ctor_get(v_u_2243_, 1);
lean_inc(v_a_2259_);
lean_dec_ref_known(v_u_2243_, 2);
v___x_2260_ = lean_apply_5(v_h__4_2248_, v_a_2258_, v_a_2259_, v_v_2244_, lean_box(0), lean_box(0));
return v___x_2260_;
}
case 1:
{
lean_object* v_a_2261_; lean_object* v_a_2262_; lean_object* v___x_2263_; 
lean_dec(v_h__6_2250_);
lean_dec(v_h__4_2248_);
lean_dec(v_h__3_2247_);
v_a_2261_ = lean_ctor_get(v_v_2244_, 0);
lean_inc(v_a_2261_);
lean_dec_ref_known(v_v_2244_, 1);
v_a_2262_ = lean_ctor_get(v_u_2243_, 0);
lean_inc(v_a_2262_);
lean_dec_ref_known(v_u_2243_, 1);
v___x_2263_ = lean_apply_2(v_h__5_2249_, v_a_2262_, v_a_2261_);
return v___x_2263_;
}
default: 
{
lean_object* v___x_2264_; 
lean_dec(v_h__5_2249_);
lean_dec(v_h__4_2248_);
lean_dec(v_h__3_2247_);
v___x_2264_ = lean_apply_7(v_h__6_2250_, v_u_2243_, v_v_2244_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_2264_;
}
}
}
default: 
{
lean_dec(v_h__5_2249_);
lean_dec(v_h__2_2246_);
lean_dec(v_h__1_2245_);
switch(lean_obj_tag(v_u_2243_))
{
case 2:
{
lean_object* v_a_2265_; lean_object* v_a_2266_; lean_object* v___x_2267_; 
lean_dec(v_h__6_2250_);
lean_dec(v_h__4_2248_);
v_a_2265_ = lean_ctor_get(v_u_2243_, 0);
lean_inc(v_a_2265_);
v_a_2266_ = lean_ctor_get(v_u_2243_, 1);
lean_inc(v_a_2266_);
lean_dec_ref_known(v_u_2243_, 2);
v___x_2267_ = lean_apply_5(v_h__3_2247_, v_a_2265_, v_a_2266_, v_v_2244_, lean_box(0), lean_box(0));
return v___x_2267_;
}
case 3:
{
lean_object* v_a_2268_; lean_object* v_a_2269_; lean_object* v___x_2270_; 
lean_dec(v_h__6_2250_);
lean_dec(v_h__3_2247_);
v_a_2268_ = lean_ctor_get(v_u_2243_, 0);
lean_inc(v_a_2268_);
v_a_2269_ = lean_ctor_get(v_u_2243_, 1);
lean_inc(v_a_2269_);
lean_dec_ref_known(v_u_2243_, 2);
v___x_2270_ = lean_apply_5(v_h__4_2248_, v_a_2268_, v_a_2269_, v_v_2244_, lean_box(0), lean_box(0));
return v___x_2270_;
}
default: 
{
lean_object* v___x_2271_; 
lean_dec(v_h__4_2248_);
lean_dec(v_h__3_2247_);
v___x_2271_ = lean_apply_7(v_h__6_2250_, v_u_2243_, v_v_2244_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_2271_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_isIMax_match__1_splitter___redArg(lean_object* v_x_2272_, lean_object* v_h__1_2273_, lean_object* v_h__2_2274_){
_start:
{
if (lean_obj_tag(v_x_2272_) == 3)
{
lean_object* v_a_2275_; lean_object* v_a_2276_; lean_object* v___x_2277_; 
lean_dec(v_h__2_2274_);
v_a_2275_ = lean_ctor_get(v_x_2272_, 0);
lean_inc(v_a_2275_);
v_a_2276_ = lean_ctor_get(v_x_2272_, 1);
lean_inc(v_a_2276_);
lean_dec_ref_known(v_x_2272_, 2);
v___x_2277_ = lean_apply_2(v_h__1_2273_, v_a_2275_, v_a_2276_);
return v___x_2277_;
}
else
{
lean_object* v___x_2278_; 
lean_dec(v_h__1_2273_);
v___x_2278_ = lean_apply_2(v_h__2_2274_, v_x_2272_, lean_box(0));
return v___x_2278_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_isIMax_match__1_splitter(lean_object* v_motive_2279_, lean_object* v_x_2280_, lean_object* v_h__1_2281_, lean_object* v_h__2_2282_){
_start:
{
if (lean_obj_tag(v_x_2280_) == 3)
{
lean_object* v_a_2283_; lean_object* v_a_2284_; lean_object* v___x_2285_; 
lean_dec(v_h__2_2282_);
v_a_2283_ = lean_ctor_get(v_x_2280_, 0);
lean_inc(v_a_2283_);
v_a_2284_ = lean_ctor_get(v_x_2280_, 1);
lean_inc(v_a_2284_);
lean_dec_ref_known(v_x_2280_, 2);
v___x_2285_ = lean_apply_2(v_h__1_2281_, v_a_2283_, v_a_2284_);
return v___x_2285_;
}
else
{
lean_object* v___x_2286_; 
lean_dec(v_h__1_2281_);
v___x_2286_ = lean_apply_2(v_h__2_2282_, v_x_2280_, lean_box(0));
return v___x_2286_;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Level_geq(lean_object* v_u_2287_, lean_object* v_v_2288_){
_start:
{
lean_object* v___x_2289_; lean_object* v___x_2290_; uint8_t v___x_2291_; 
v___x_2289_ = l_Lean_Level_normalize(v_u_2287_);
v___x_2290_ = l_Lean_Level_normalize(v_v_2288_);
v___x_2291_ = l___private_Lean_Level_0__Lean_Level_geq_go(v___x_2289_, v___x_2290_);
lean_dec(v___x_2290_);
lean_dec(v___x_2289_);
return v___x_2291_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_geq___boxed(lean_object* v_u_2292_, lean_object* v_v_2293_){
_start:
{
uint8_t v_res_2294_; lean_object* v_r_2295_; 
v_res_2294_ = l_Lean_Level_geq(v_u_2292_, v_v_2293_);
lean_dec(v_v_2293_);
lean_dec(v_u_2292_);
v_r_2295_ = lean_box(v_res_2294_);
return v_r_2295_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Level_collectMVars_spec__1___redArg(lean_object* v_k_2296_, lean_object* v_v_2297_, lean_object* v_t_2298_){
_start:
{
if (lean_obj_tag(v_t_2298_) == 0)
{
lean_object* v_size_2299_; lean_object* v_k_2300_; lean_object* v_v_2301_; lean_object* v_l_2302_; lean_object* v_r_2303_; lean_object* v___x_2305_; uint8_t v_isShared_2306_; uint8_t v_isSharedCheck_2583_; 
v_size_2299_ = lean_ctor_get(v_t_2298_, 0);
v_k_2300_ = lean_ctor_get(v_t_2298_, 1);
v_v_2301_ = lean_ctor_get(v_t_2298_, 2);
v_l_2302_ = lean_ctor_get(v_t_2298_, 3);
v_r_2303_ = lean_ctor_get(v_t_2298_, 4);
v_isSharedCheck_2583_ = !lean_is_exclusive(v_t_2298_);
if (v_isSharedCheck_2583_ == 0)
{
v___x_2305_ = v_t_2298_;
v_isShared_2306_ = v_isSharedCheck_2583_;
goto v_resetjp_2304_;
}
else
{
lean_inc(v_r_2303_);
lean_inc(v_l_2302_);
lean_inc(v_v_2301_);
lean_inc(v_k_2300_);
lean_inc(v_size_2299_);
lean_dec(v_t_2298_);
v___x_2305_ = lean_box(0);
v_isShared_2306_ = v_isSharedCheck_2583_;
goto v_resetjp_2304_;
}
v_resetjp_2304_:
{
uint8_t v___x_2307_; 
v___x_2307_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2296_, v_k_2300_);
switch(v___x_2307_)
{
case 0:
{
lean_object* v_impl_2308_; lean_object* v___x_2309_; 
lean_dec(v_size_2299_);
v_impl_2308_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Level_collectMVars_spec__1___redArg(v_k_2296_, v_v_2297_, v_l_2302_);
v___x_2309_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_2303_) == 0)
{
lean_object* v_size_2310_; lean_object* v_size_2311_; lean_object* v_k_2312_; lean_object* v_v_2313_; lean_object* v_l_2314_; lean_object* v_r_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; uint8_t v___x_2318_; 
v_size_2310_ = lean_ctor_get(v_r_2303_, 0);
v_size_2311_ = lean_ctor_get(v_impl_2308_, 0);
lean_inc(v_size_2311_);
v_k_2312_ = lean_ctor_get(v_impl_2308_, 1);
lean_inc(v_k_2312_);
v_v_2313_ = lean_ctor_get(v_impl_2308_, 2);
lean_inc(v_v_2313_);
v_l_2314_ = lean_ctor_get(v_impl_2308_, 3);
lean_inc(v_l_2314_);
v_r_2315_ = lean_ctor_get(v_impl_2308_, 4);
lean_inc(v_r_2315_);
v___x_2316_ = lean_unsigned_to_nat(3u);
v___x_2317_ = lean_nat_mul(v___x_2316_, v_size_2310_);
v___x_2318_ = lean_nat_dec_lt(v___x_2317_, v_size_2311_);
lean_dec(v___x_2317_);
if (v___x_2318_ == 0)
{
lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2322_; 
lean_dec(v_r_2315_);
lean_dec(v_l_2314_);
lean_dec(v_v_2313_);
lean_dec(v_k_2312_);
v___x_2319_ = lean_nat_add(v___x_2309_, v_size_2311_);
lean_dec(v_size_2311_);
v___x_2320_ = lean_nat_add(v___x_2319_, v_size_2310_);
lean_dec(v___x_2319_);
if (v_isShared_2306_ == 0)
{
lean_ctor_set(v___x_2305_, 3, v_impl_2308_);
lean_ctor_set(v___x_2305_, 0, v___x_2320_);
v___x_2322_ = v___x_2305_;
goto v_reusejp_2321_;
}
else
{
lean_object* v_reuseFailAlloc_2323_; 
v_reuseFailAlloc_2323_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2323_, 0, v___x_2320_);
lean_ctor_set(v_reuseFailAlloc_2323_, 1, v_k_2300_);
lean_ctor_set(v_reuseFailAlloc_2323_, 2, v_v_2301_);
lean_ctor_set(v_reuseFailAlloc_2323_, 3, v_impl_2308_);
lean_ctor_set(v_reuseFailAlloc_2323_, 4, v_r_2303_);
v___x_2322_ = v_reuseFailAlloc_2323_;
goto v_reusejp_2321_;
}
v_reusejp_2321_:
{
return v___x_2322_;
}
}
else
{
lean_object* v___x_2325_; uint8_t v_isShared_2326_; uint8_t v_isSharedCheck_2389_; 
v_isSharedCheck_2389_ = !lean_is_exclusive(v_impl_2308_);
if (v_isSharedCheck_2389_ == 0)
{
lean_object* v_unused_2390_; lean_object* v_unused_2391_; lean_object* v_unused_2392_; lean_object* v_unused_2393_; lean_object* v_unused_2394_; 
v_unused_2390_ = lean_ctor_get(v_impl_2308_, 4);
lean_dec(v_unused_2390_);
v_unused_2391_ = lean_ctor_get(v_impl_2308_, 3);
lean_dec(v_unused_2391_);
v_unused_2392_ = lean_ctor_get(v_impl_2308_, 2);
lean_dec(v_unused_2392_);
v_unused_2393_ = lean_ctor_get(v_impl_2308_, 1);
lean_dec(v_unused_2393_);
v_unused_2394_ = lean_ctor_get(v_impl_2308_, 0);
lean_dec(v_unused_2394_);
v___x_2325_ = v_impl_2308_;
v_isShared_2326_ = v_isSharedCheck_2389_;
goto v_resetjp_2324_;
}
else
{
lean_dec(v_impl_2308_);
v___x_2325_ = lean_box(0);
v_isShared_2326_ = v_isSharedCheck_2389_;
goto v_resetjp_2324_;
}
v_resetjp_2324_:
{
lean_object* v_size_2327_; lean_object* v_size_2328_; lean_object* v_k_2329_; lean_object* v_v_2330_; lean_object* v_l_2331_; lean_object* v_r_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; uint8_t v___x_2335_; 
v_size_2327_ = lean_ctor_get(v_l_2314_, 0);
v_size_2328_ = lean_ctor_get(v_r_2315_, 0);
v_k_2329_ = lean_ctor_get(v_r_2315_, 1);
v_v_2330_ = lean_ctor_get(v_r_2315_, 2);
v_l_2331_ = lean_ctor_get(v_r_2315_, 3);
v_r_2332_ = lean_ctor_get(v_r_2315_, 4);
v___x_2333_ = lean_unsigned_to_nat(2u);
v___x_2334_ = lean_nat_mul(v___x_2333_, v_size_2327_);
v___x_2335_ = lean_nat_dec_lt(v_size_2328_, v___x_2334_);
lean_dec(v___x_2334_);
if (v___x_2335_ == 0)
{
lean_object* v___x_2337_; uint8_t v_isShared_2338_; uint8_t v_isSharedCheck_2364_; 
lean_inc(v_r_2332_);
lean_inc(v_l_2331_);
lean_inc(v_v_2330_);
lean_inc(v_k_2329_);
v_isSharedCheck_2364_ = !lean_is_exclusive(v_r_2315_);
if (v_isSharedCheck_2364_ == 0)
{
lean_object* v_unused_2365_; lean_object* v_unused_2366_; lean_object* v_unused_2367_; lean_object* v_unused_2368_; lean_object* v_unused_2369_; 
v_unused_2365_ = lean_ctor_get(v_r_2315_, 4);
lean_dec(v_unused_2365_);
v_unused_2366_ = lean_ctor_get(v_r_2315_, 3);
lean_dec(v_unused_2366_);
v_unused_2367_ = lean_ctor_get(v_r_2315_, 2);
lean_dec(v_unused_2367_);
v_unused_2368_ = lean_ctor_get(v_r_2315_, 1);
lean_dec(v_unused_2368_);
v_unused_2369_ = lean_ctor_get(v_r_2315_, 0);
lean_dec(v_unused_2369_);
v___x_2337_ = v_r_2315_;
v_isShared_2338_ = v_isSharedCheck_2364_;
goto v_resetjp_2336_;
}
else
{
lean_dec(v_r_2315_);
v___x_2337_ = lean_box(0);
v_isShared_2338_ = v_isSharedCheck_2364_;
goto v_resetjp_2336_;
}
v_resetjp_2336_:
{
lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___y_2342_; lean_object* v___y_2343_; lean_object* v___y_2344_; lean_object* v___x_2352_; lean_object* v___y_2354_; 
v___x_2339_ = lean_nat_add(v___x_2309_, v_size_2311_);
lean_dec(v_size_2311_);
v___x_2340_ = lean_nat_add(v___x_2339_, v_size_2310_);
lean_dec(v___x_2339_);
v___x_2352_ = lean_nat_add(v___x_2309_, v_size_2327_);
if (lean_obj_tag(v_l_2331_) == 0)
{
lean_object* v_size_2362_; 
v_size_2362_ = lean_ctor_get(v_l_2331_, 0);
lean_inc(v_size_2362_);
v___y_2354_ = v_size_2362_;
goto v___jp_2353_;
}
else
{
lean_object* v___x_2363_; 
v___x_2363_ = lean_unsigned_to_nat(0u);
v___y_2354_ = v___x_2363_;
goto v___jp_2353_;
}
v___jp_2341_:
{
lean_object* v___x_2345_; lean_object* v___x_2347_; 
v___x_2345_ = lean_nat_add(v___y_2343_, v___y_2344_);
lean_dec(v___y_2344_);
lean_dec(v___y_2343_);
if (v_isShared_2338_ == 0)
{
lean_ctor_set(v___x_2337_, 4, v_r_2303_);
lean_ctor_set(v___x_2337_, 3, v_r_2332_);
lean_ctor_set(v___x_2337_, 2, v_v_2301_);
lean_ctor_set(v___x_2337_, 1, v_k_2300_);
lean_ctor_set(v___x_2337_, 0, v___x_2345_);
v___x_2347_ = v___x_2337_;
goto v_reusejp_2346_;
}
else
{
lean_object* v_reuseFailAlloc_2351_; 
v_reuseFailAlloc_2351_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2351_, 0, v___x_2345_);
lean_ctor_set(v_reuseFailAlloc_2351_, 1, v_k_2300_);
lean_ctor_set(v_reuseFailAlloc_2351_, 2, v_v_2301_);
lean_ctor_set(v_reuseFailAlloc_2351_, 3, v_r_2332_);
lean_ctor_set(v_reuseFailAlloc_2351_, 4, v_r_2303_);
v___x_2347_ = v_reuseFailAlloc_2351_;
goto v_reusejp_2346_;
}
v_reusejp_2346_:
{
lean_object* v___x_2349_; 
if (v_isShared_2326_ == 0)
{
lean_ctor_set(v___x_2325_, 4, v___x_2347_);
lean_ctor_set(v___x_2325_, 3, v___y_2342_);
lean_ctor_set(v___x_2325_, 2, v_v_2330_);
lean_ctor_set(v___x_2325_, 1, v_k_2329_);
lean_ctor_set(v___x_2325_, 0, v___x_2340_);
v___x_2349_ = v___x_2325_;
goto v_reusejp_2348_;
}
else
{
lean_object* v_reuseFailAlloc_2350_; 
v_reuseFailAlloc_2350_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2350_, 0, v___x_2340_);
lean_ctor_set(v_reuseFailAlloc_2350_, 1, v_k_2329_);
lean_ctor_set(v_reuseFailAlloc_2350_, 2, v_v_2330_);
lean_ctor_set(v_reuseFailAlloc_2350_, 3, v___y_2342_);
lean_ctor_set(v_reuseFailAlloc_2350_, 4, v___x_2347_);
v___x_2349_ = v_reuseFailAlloc_2350_;
goto v_reusejp_2348_;
}
v_reusejp_2348_:
{
return v___x_2349_;
}
}
}
v___jp_2353_:
{
lean_object* v___x_2355_; lean_object* v___x_2357_; 
v___x_2355_ = lean_nat_add(v___x_2352_, v___y_2354_);
lean_dec(v___y_2354_);
lean_dec(v___x_2352_);
if (v_isShared_2306_ == 0)
{
lean_ctor_set(v___x_2305_, 4, v_l_2331_);
lean_ctor_set(v___x_2305_, 3, v_l_2314_);
lean_ctor_set(v___x_2305_, 2, v_v_2313_);
lean_ctor_set(v___x_2305_, 1, v_k_2312_);
lean_ctor_set(v___x_2305_, 0, v___x_2355_);
v___x_2357_ = v___x_2305_;
goto v_reusejp_2356_;
}
else
{
lean_object* v_reuseFailAlloc_2361_; 
v_reuseFailAlloc_2361_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2361_, 0, v___x_2355_);
lean_ctor_set(v_reuseFailAlloc_2361_, 1, v_k_2312_);
lean_ctor_set(v_reuseFailAlloc_2361_, 2, v_v_2313_);
lean_ctor_set(v_reuseFailAlloc_2361_, 3, v_l_2314_);
lean_ctor_set(v_reuseFailAlloc_2361_, 4, v_l_2331_);
v___x_2357_ = v_reuseFailAlloc_2361_;
goto v_reusejp_2356_;
}
v_reusejp_2356_:
{
lean_object* v___x_2358_; 
v___x_2358_ = lean_nat_add(v___x_2309_, v_size_2310_);
if (lean_obj_tag(v_r_2332_) == 0)
{
lean_object* v_size_2359_; 
v_size_2359_ = lean_ctor_get(v_r_2332_, 0);
lean_inc(v_size_2359_);
v___y_2342_ = v___x_2357_;
v___y_2343_ = v___x_2358_;
v___y_2344_ = v_size_2359_;
goto v___jp_2341_;
}
else
{
lean_object* v___x_2360_; 
v___x_2360_ = lean_unsigned_to_nat(0u);
v___y_2342_ = v___x_2357_;
v___y_2343_ = v___x_2358_;
v___y_2344_ = v___x_2360_;
goto v___jp_2341_;
}
}
}
}
}
else
{
lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2375_; 
lean_del_object(v___x_2305_);
v___x_2370_ = lean_nat_add(v___x_2309_, v_size_2311_);
lean_dec(v_size_2311_);
v___x_2371_ = lean_nat_add(v___x_2370_, v_size_2310_);
lean_dec(v___x_2370_);
v___x_2372_ = lean_nat_add(v___x_2309_, v_size_2310_);
v___x_2373_ = lean_nat_add(v___x_2372_, v_size_2328_);
lean_dec(v___x_2372_);
lean_inc_ref(v_r_2303_);
if (v_isShared_2326_ == 0)
{
lean_ctor_set(v___x_2325_, 4, v_r_2303_);
lean_ctor_set(v___x_2325_, 3, v_r_2315_);
lean_ctor_set(v___x_2325_, 2, v_v_2301_);
lean_ctor_set(v___x_2325_, 1, v_k_2300_);
lean_ctor_set(v___x_2325_, 0, v___x_2373_);
v___x_2375_ = v___x_2325_;
goto v_reusejp_2374_;
}
else
{
lean_object* v_reuseFailAlloc_2388_; 
v_reuseFailAlloc_2388_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2388_, 0, v___x_2373_);
lean_ctor_set(v_reuseFailAlloc_2388_, 1, v_k_2300_);
lean_ctor_set(v_reuseFailAlloc_2388_, 2, v_v_2301_);
lean_ctor_set(v_reuseFailAlloc_2388_, 3, v_r_2315_);
lean_ctor_set(v_reuseFailAlloc_2388_, 4, v_r_2303_);
v___x_2375_ = v_reuseFailAlloc_2388_;
goto v_reusejp_2374_;
}
v_reusejp_2374_:
{
lean_object* v___x_2377_; uint8_t v_isShared_2378_; uint8_t v_isSharedCheck_2382_; 
v_isSharedCheck_2382_ = !lean_is_exclusive(v_r_2303_);
if (v_isSharedCheck_2382_ == 0)
{
lean_object* v_unused_2383_; lean_object* v_unused_2384_; lean_object* v_unused_2385_; lean_object* v_unused_2386_; lean_object* v_unused_2387_; 
v_unused_2383_ = lean_ctor_get(v_r_2303_, 4);
lean_dec(v_unused_2383_);
v_unused_2384_ = lean_ctor_get(v_r_2303_, 3);
lean_dec(v_unused_2384_);
v_unused_2385_ = lean_ctor_get(v_r_2303_, 2);
lean_dec(v_unused_2385_);
v_unused_2386_ = lean_ctor_get(v_r_2303_, 1);
lean_dec(v_unused_2386_);
v_unused_2387_ = lean_ctor_get(v_r_2303_, 0);
lean_dec(v_unused_2387_);
v___x_2377_ = v_r_2303_;
v_isShared_2378_ = v_isSharedCheck_2382_;
goto v_resetjp_2376_;
}
else
{
lean_dec(v_r_2303_);
v___x_2377_ = lean_box(0);
v_isShared_2378_ = v_isSharedCheck_2382_;
goto v_resetjp_2376_;
}
v_resetjp_2376_:
{
lean_object* v___x_2380_; 
if (v_isShared_2378_ == 0)
{
lean_ctor_set(v___x_2377_, 4, v___x_2375_);
lean_ctor_set(v___x_2377_, 3, v_l_2314_);
lean_ctor_set(v___x_2377_, 2, v_v_2313_);
lean_ctor_set(v___x_2377_, 1, v_k_2312_);
lean_ctor_set(v___x_2377_, 0, v___x_2371_);
v___x_2380_ = v___x_2377_;
goto v_reusejp_2379_;
}
else
{
lean_object* v_reuseFailAlloc_2381_; 
v_reuseFailAlloc_2381_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2381_, 0, v___x_2371_);
lean_ctor_set(v_reuseFailAlloc_2381_, 1, v_k_2312_);
lean_ctor_set(v_reuseFailAlloc_2381_, 2, v_v_2313_);
lean_ctor_set(v_reuseFailAlloc_2381_, 3, v_l_2314_);
lean_ctor_set(v_reuseFailAlloc_2381_, 4, v___x_2375_);
v___x_2380_ = v_reuseFailAlloc_2381_;
goto v_reusejp_2379_;
}
v_reusejp_2379_:
{
return v___x_2380_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_2395_; 
v_l_2395_ = lean_ctor_get(v_impl_2308_, 3);
lean_inc(v_l_2395_);
if (lean_obj_tag(v_l_2395_) == 0)
{
lean_object* v_r_2396_; lean_object* v_k_2397_; lean_object* v_v_2398_; lean_object* v___x_2400_; uint8_t v_isShared_2401_; uint8_t v_isSharedCheck_2409_; 
v_r_2396_ = lean_ctor_get(v_impl_2308_, 4);
v_k_2397_ = lean_ctor_get(v_impl_2308_, 1);
v_v_2398_ = lean_ctor_get(v_impl_2308_, 2);
v_isSharedCheck_2409_ = !lean_is_exclusive(v_impl_2308_);
if (v_isSharedCheck_2409_ == 0)
{
lean_object* v_unused_2410_; lean_object* v_unused_2411_; 
v_unused_2410_ = lean_ctor_get(v_impl_2308_, 3);
lean_dec(v_unused_2410_);
v_unused_2411_ = lean_ctor_get(v_impl_2308_, 0);
lean_dec(v_unused_2411_);
v___x_2400_ = v_impl_2308_;
v_isShared_2401_ = v_isSharedCheck_2409_;
goto v_resetjp_2399_;
}
else
{
lean_inc(v_r_2396_);
lean_inc(v_v_2398_);
lean_inc(v_k_2397_);
lean_dec(v_impl_2308_);
v___x_2400_ = lean_box(0);
v_isShared_2401_ = v_isSharedCheck_2409_;
goto v_resetjp_2399_;
}
v_resetjp_2399_:
{
lean_object* v___x_2402_; lean_object* v___x_2404_; 
v___x_2402_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_2396_);
if (v_isShared_2401_ == 0)
{
lean_ctor_set(v___x_2400_, 3, v_r_2396_);
lean_ctor_set(v___x_2400_, 2, v_v_2301_);
lean_ctor_set(v___x_2400_, 1, v_k_2300_);
lean_ctor_set(v___x_2400_, 0, v___x_2309_);
v___x_2404_ = v___x_2400_;
goto v_reusejp_2403_;
}
else
{
lean_object* v_reuseFailAlloc_2408_; 
v_reuseFailAlloc_2408_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2408_, 0, v___x_2309_);
lean_ctor_set(v_reuseFailAlloc_2408_, 1, v_k_2300_);
lean_ctor_set(v_reuseFailAlloc_2408_, 2, v_v_2301_);
lean_ctor_set(v_reuseFailAlloc_2408_, 3, v_r_2396_);
lean_ctor_set(v_reuseFailAlloc_2408_, 4, v_r_2396_);
v___x_2404_ = v_reuseFailAlloc_2408_;
goto v_reusejp_2403_;
}
v_reusejp_2403_:
{
lean_object* v___x_2406_; 
if (v_isShared_2306_ == 0)
{
lean_ctor_set(v___x_2305_, 4, v___x_2404_);
lean_ctor_set(v___x_2305_, 3, v_l_2395_);
lean_ctor_set(v___x_2305_, 2, v_v_2398_);
lean_ctor_set(v___x_2305_, 1, v_k_2397_);
lean_ctor_set(v___x_2305_, 0, v___x_2402_);
v___x_2406_ = v___x_2305_;
goto v_reusejp_2405_;
}
else
{
lean_object* v_reuseFailAlloc_2407_; 
v_reuseFailAlloc_2407_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2407_, 0, v___x_2402_);
lean_ctor_set(v_reuseFailAlloc_2407_, 1, v_k_2397_);
lean_ctor_set(v_reuseFailAlloc_2407_, 2, v_v_2398_);
lean_ctor_set(v_reuseFailAlloc_2407_, 3, v_l_2395_);
lean_ctor_set(v_reuseFailAlloc_2407_, 4, v___x_2404_);
v___x_2406_ = v_reuseFailAlloc_2407_;
goto v_reusejp_2405_;
}
v_reusejp_2405_:
{
return v___x_2406_;
}
}
}
}
else
{
lean_object* v_r_2412_; 
v_r_2412_ = lean_ctor_get(v_impl_2308_, 4);
lean_inc(v_r_2412_);
if (lean_obj_tag(v_r_2412_) == 0)
{
lean_object* v_k_2413_; lean_object* v_v_2414_; lean_object* v___x_2416_; uint8_t v_isShared_2417_; uint8_t v_isSharedCheck_2437_; 
v_k_2413_ = lean_ctor_get(v_impl_2308_, 1);
v_v_2414_ = lean_ctor_get(v_impl_2308_, 2);
v_isSharedCheck_2437_ = !lean_is_exclusive(v_impl_2308_);
if (v_isSharedCheck_2437_ == 0)
{
lean_object* v_unused_2438_; lean_object* v_unused_2439_; lean_object* v_unused_2440_; 
v_unused_2438_ = lean_ctor_get(v_impl_2308_, 4);
lean_dec(v_unused_2438_);
v_unused_2439_ = lean_ctor_get(v_impl_2308_, 3);
lean_dec(v_unused_2439_);
v_unused_2440_ = lean_ctor_get(v_impl_2308_, 0);
lean_dec(v_unused_2440_);
v___x_2416_ = v_impl_2308_;
v_isShared_2417_ = v_isSharedCheck_2437_;
goto v_resetjp_2415_;
}
else
{
lean_inc(v_v_2414_);
lean_inc(v_k_2413_);
lean_dec(v_impl_2308_);
v___x_2416_ = lean_box(0);
v_isShared_2417_ = v_isSharedCheck_2437_;
goto v_resetjp_2415_;
}
v_resetjp_2415_:
{
lean_object* v_k_2418_; lean_object* v_v_2419_; lean_object* v___x_2421_; uint8_t v_isShared_2422_; uint8_t v_isSharedCheck_2433_; 
v_k_2418_ = lean_ctor_get(v_r_2412_, 1);
v_v_2419_ = lean_ctor_get(v_r_2412_, 2);
v_isSharedCheck_2433_ = !lean_is_exclusive(v_r_2412_);
if (v_isSharedCheck_2433_ == 0)
{
lean_object* v_unused_2434_; lean_object* v_unused_2435_; lean_object* v_unused_2436_; 
v_unused_2434_ = lean_ctor_get(v_r_2412_, 4);
lean_dec(v_unused_2434_);
v_unused_2435_ = lean_ctor_get(v_r_2412_, 3);
lean_dec(v_unused_2435_);
v_unused_2436_ = lean_ctor_get(v_r_2412_, 0);
lean_dec(v_unused_2436_);
v___x_2421_ = v_r_2412_;
v_isShared_2422_ = v_isSharedCheck_2433_;
goto v_resetjp_2420_;
}
else
{
lean_inc(v_v_2419_);
lean_inc(v_k_2418_);
lean_dec(v_r_2412_);
v___x_2421_ = lean_box(0);
v_isShared_2422_ = v_isSharedCheck_2433_;
goto v_resetjp_2420_;
}
v_resetjp_2420_:
{
lean_object* v___x_2423_; lean_object* v___x_2425_; 
v___x_2423_ = lean_unsigned_to_nat(3u);
if (v_isShared_2422_ == 0)
{
lean_ctor_set(v___x_2421_, 4, v_l_2395_);
lean_ctor_set(v___x_2421_, 3, v_l_2395_);
lean_ctor_set(v___x_2421_, 2, v_v_2414_);
lean_ctor_set(v___x_2421_, 1, v_k_2413_);
lean_ctor_set(v___x_2421_, 0, v___x_2309_);
v___x_2425_ = v___x_2421_;
goto v_reusejp_2424_;
}
else
{
lean_object* v_reuseFailAlloc_2432_; 
v_reuseFailAlloc_2432_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2432_, 0, v___x_2309_);
lean_ctor_set(v_reuseFailAlloc_2432_, 1, v_k_2413_);
lean_ctor_set(v_reuseFailAlloc_2432_, 2, v_v_2414_);
lean_ctor_set(v_reuseFailAlloc_2432_, 3, v_l_2395_);
lean_ctor_set(v_reuseFailAlloc_2432_, 4, v_l_2395_);
v___x_2425_ = v_reuseFailAlloc_2432_;
goto v_reusejp_2424_;
}
v_reusejp_2424_:
{
lean_object* v___x_2427_; 
if (v_isShared_2417_ == 0)
{
lean_ctor_set(v___x_2416_, 4, v_l_2395_);
lean_ctor_set(v___x_2416_, 2, v_v_2301_);
lean_ctor_set(v___x_2416_, 1, v_k_2300_);
lean_ctor_set(v___x_2416_, 0, v___x_2309_);
v___x_2427_ = v___x_2416_;
goto v_reusejp_2426_;
}
else
{
lean_object* v_reuseFailAlloc_2431_; 
v_reuseFailAlloc_2431_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2431_, 0, v___x_2309_);
lean_ctor_set(v_reuseFailAlloc_2431_, 1, v_k_2300_);
lean_ctor_set(v_reuseFailAlloc_2431_, 2, v_v_2301_);
lean_ctor_set(v_reuseFailAlloc_2431_, 3, v_l_2395_);
lean_ctor_set(v_reuseFailAlloc_2431_, 4, v_l_2395_);
v___x_2427_ = v_reuseFailAlloc_2431_;
goto v_reusejp_2426_;
}
v_reusejp_2426_:
{
lean_object* v___x_2429_; 
if (v_isShared_2306_ == 0)
{
lean_ctor_set(v___x_2305_, 4, v___x_2427_);
lean_ctor_set(v___x_2305_, 3, v___x_2425_);
lean_ctor_set(v___x_2305_, 2, v_v_2419_);
lean_ctor_set(v___x_2305_, 1, v_k_2418_);
lean_ctor_set(v___x_2305_, 0, v___x_2423_);
v___x_2429_ = v___x_2305_;
goto v_reusejp_2428_;
}
else
{
lean_object* v_reuseFailAlloc_2430_; 
v_reuseFailAlloc_2430_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2430_, 0, v___x_2423_);
lean_ctor_set(v_reuseFailAlloc_2430_, 1, v_k_2418_);
lean_ctor_set(v_reuseFailAlloc_2430_, 2, v_v_2419_);
lean_ctor_set(v_reuseFailAlloc_2430_, 3, v___x_2425_);
lean_ctor_set(v_reuseFailAlloc_2430_, 4, v___x_2427_);
v___x_2429_ = v_reuseFailAlloc_2430_;
goto v_reusejp_2428_;
}
v_reusejp_2428_:
{
return v___x_2429_;
}
}
}
}
}
}
else
{
lean_object* v___x_2441_; lean_object* v___x_2443_; 
v___x_2441_ = lean_unsigned_to_nat(2u);
if (v_isShared_2306_ == 0)
{
lean_ctor_set(v___x_2305_, 4, v_r_2412_);
lean_ctor_set(v___x_2305_, 3, v_impl_2308_);
lean_ctor_set(v___x_2305_, 0, v___x_2441_);
v___x_2443_ = v___x_2305_;
goto v_reusejp_2442_;
}
else
{
lean_object* v_reuseFailAlloc_2444_; 
v_reuseFailAlloc_2444_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2444_, 0, v___x_2441_);
lean_ctor_set(v_reuseFailAlloc_2444_, 1, v_k_2300_);
lean_ctor_set(v_reuseFailAlloc_2444_, 2, v_v_2301_);
lean_ctor_set(v_reuseFailAlloc_2444_, 3, v_impl_2308_);
lean_ctor_set(v_reuseFailAlloc_2444_, 4, v_r_2412_);
v___x_2443_ = v_reuseFailAlloc_2444_;
goto v_reusejp_2442_;
}
v_reusejp_2442_:
{
return v___x_2443_;
}
}
}
}
}
case 1:
{
lean_object* v___x_2446_; 
lean_dec(v_v_2301_);
lean_dec(v_k_2300_);
if (v_isShared_2306_ == 0)
{
lean_ctor_set(v___x_2305_, 2, v_v_2297_);
lean_ctor_set(v___x_2305_, 1, v_k_2296_);
v___x_2446_ = v___x_2305_;
goto v_reusejp_2445_;
}
else
{
lean_object* v_reuseFailAlloc_2447_; 
v_reuseFailAlloc_2447_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2447_, 0, v_size_2299_);
lean_ctor_set(v_reuseFailAlloc_2447_, 1, v_k_2296_);
lean_ctor_set(v_reuseFailAlloc_2447_, 2, v_v_2297_);
lean_ctor_set(v_reuseFailAlloc_2447_, 3, v_l_2302_);
lean_ctor_set(v_reuseFailAlloc_2447_, 4, v_r_2303_);
v___x_2446_ = v_reuseFailAlloc_2447_;
goto v_reusejp_2445_;
}
v_reusejp_2445_:
{
return v___x_2446_;
}
}
default: 
{
lean_object* v_impl_2448_; lean_object* v___x_2449_; 
lean_dec(v_size_2299_);
v_impl_2448_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Level_collectMVars_spec__1___redArg(v_k_2296_, v_v_2297_, v_r_2303_);
v___x_2449_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_2302_) == 0)
{
lean_object* v_size_2450_; lean_object* v_size_2451_; lean_object* v_k_2452_; lean_object* v_v_2453_; lean_object* v_l_2454_; lean_object* v_r_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; uint8_t v___x_2458_; 
v_size_2450_ = lean_ctor_get(v_l_2302_, 0);
v_size_2451_ = lean_ctor_get(v_impl_2448_, 0);
lean_inc(v_size_2451_);
v_k_2452_ = lean_ctor_get(v_impl_2448_, 1);
lean_inc(v_k_2452_);
v_v_2453_ = lean_ctor_get(v_impl_2448_, 2);
lean_inc(v_v_2453_);
v_l_2454_ = lean_ctor_get(v_impl_2448_, 3);
lean_inc(v_l_2454_);
v_r_2455_ = lean_ctor_get(v_impl_2448_, 4);
lean_inc(v_r_2455_);
v___x_2456_ = lean_unsigned_to_nat(3u);
v___x_2457_ = lean_nat_mul(v___x_2456_, v_size_2450_);
v___x_2458_ = lean_nat_dec_lt(v___x_2457_, v_size_2451_);
lean_dec(v___x_2457_);
if (v___x_2458_ == 0)
{
lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2462_; 
lean_dec(v_r_2455_);
lean_dec(v_l_2454_);
lean_dec(v_v_2453_);
lean_dec(v_k_2452_);
v___x_2459_ = lean_nat_add(v___x_2449_, v_size_2450_);
v___x_2460_ = lean_nat_add(v___x_2459_, v_size_2451_);
lean_dec(v_size_2451_);
lean_dec(v___x_2459_);
if (v_isShared_2306_ == 0)
{
lean_ctor_set(v___x_2305_, 4, v_impl_2448_);
lean_ctor_set(v___x_2305_, 0, v___x_2460_);
v___x_2462_ = v___x_2305_;
goto v_reusejp_2461_;
}
else
{
lean_object* v_reuseFailAlloc_2463_; 
v_reuseFailAlloc_2463_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2463_, 0, v___x_2460_);
lean_ctor_set(v_reuseFailAlloc_2463_, 1, v_k_2300_);
lean_ctor_set(v_reuseFailAlloc_2463_, 2, v_v_2301_);
lean_ctor_set(v_reuseFailAlloc_2463_, 3, v_l_2302_);
lean_ctor_set(v_reuseFailAlloc_2463_, 4, v_impl_2448_);
v___x_2462_ = v_reuseFailAlloc_2463_;
goto v_reusejp_2461_;
}
v_reusejp_2461_:
{
return v___x_2462_;
}
}
else
{
lean_object* v___x_2465_; uint8_t v_isShared_2466_; uint8_t v_isSharedCheck_2527_; 
v_isSharedCheck_2527_ = !lean_is_exclusive(v_impl_2448_);
if (v_isSharedCheck_2527_ == 0)
{
lean_object* v_unused_2528_; lean_object* v_unused_2529_; lean_object* v_unused_2530_; lean_object* v_unused_2531_; lean_object* v_unused_2532_; 
v_unused_2528_ = lean_ctor_get(v_impl_2448_, 4);
lean_dec(v_unused_2528_);
v_unused_2529_ = lean_ctor_get(v_impl_2448_, 3);
lean_dec(v_unused_2529_);
v_unused_2530_ = lean_ctor_get(v_impl_2448_, 2);
lean_dec(v_unused_2530_);
v_unused_2531_ = lean_ctor_get(v_impl_2448_, 1);
lean_dec(v_unused_2531_);
v_unused_2532_ = lean_ctor_get(v_impl_2448_, 0);
lean_dec(v_unused_2532_);
v___x_2465_ = v_impl_2448_;
v_isShared_2466_ = v_isSharedCheck_2527_;
goto v_resetjp_2464_;
}
else
{
lean_dec(v_impl_2448_);
v___x_2465_ = lean_box(0);
v_isShared_2466_ = v_isSharedCheck_2527_;
goto v_resetjp_2464_;
}
v_resetjp_2464_:
{
lean_object* v_size_2467_; lean_object* v_k_2468_; lean_object* v_v_2469_; lean_object* v_l_2470_; lean_object* v_r_2471_; lean_object* v_size_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; uint8_t v___x_2475_; 
v_size_2467_ = lean_ctor_get(v_l_2454_, 0);
v_k_2468_ = lean_ctor_get(v_l_2454_, 1);
v_v_2469_ = lean_ctor_get(v_l_2454_, 2);
v_l_2470_ = lean_ctor_get(v_l_2454_, 3);
v_r_2471_ = lean_ctor_get(v_l_2454_, 4);
v_size_2472_ = lean_ctor_get(v_r_2455_, 0);
v___x_2473_ = lean_unsigned_to_nat(2u);
v___x_2474_ = lean_nat_mul(v___x_2473_, v_size_2472_);
v___x_2475_ = lean_nat_dec_lt(v_size_2467_, v___x_2474_);
lean_dec(v___x_2474_);
if (v___x_2475_ == 0)
{
lean_object* v___x_2477_; uint8_t v_isShared_2478_; uint8_t v_isSharedCheck_2503_; 
lean_inc(v_r_2471_);
lean_inc(v_l_2470_);
lean_inc(v_v_2469_);
lean_inc(v_k_2468_);
v_isSharedCheck_2503_ = !lean_is_exclusive(v_l_2454_);
if (v_isSharedCheck_2503_ == 0)
{
lean_object* v_unused_2504_; lean_object* v_unused_2505_; lean_object* v_unused_2506_; lean_object* v_unused_2507_; lean_object* v_unused_2508_; 
v_unused_2504_ = lean_ctor_get(v_l_2454_, 4);
lean_dec(v_unused_2504_);
v_unused_2505_ = lean_ctor_get(v_l_2454_, 3);
lean_dec(v_unused_2505_);
v_unused_2506_ = lean_ctor_get(v_l_2454_, 2);
lean_dec(v_unused_2506_);
v_unused_2507_ = lean_ctor_get(v_l_2454_, 1);
lean_dec(v_unused_2507_);
v_unused_2508_ = lean_ctor_get(v_l_2454_, 0);
lean_dec(v_unused_2508_);
v___x_2477_ = v_l_2454_;
v_isShared_2478_ = v_isSharedCheck_2503_;
goto v_resetjp_2476_;
}
else
{
lean_dec(v_l_2454_);
v___x_2477_ = lean_box(0);
v_isShared_2478_ = v_isSharedCheck_2503_;
goto v_resetjp_2476_;
}
v_resetjp_2476_:
{
lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___y_2482_; lean_object* v___y_2483_; lean_object* v___y_2484_; lean_object* v___y_2493_; 
v___x_2479_ = lean_nat_add(v___x_2449_, v_size_2450_);
v___x_2480_ = lean_nat_add(v___x_2479_, v_size_2451_);
lean_dec(v_size_2451_);
if (lean_obj_tag(v_l_2470_) == 0)
{
lean_object* v_size_2501_; 
v_size_2501_ = lean_ctor_get(v_l_2470_, 0);
lean_inc(v_size_2501_);
v___y_2493_ = v_size_2501_;
goto v___jp_2492_;
}
else
{
lean_object* v___x_2502_; 
v___x_2502_ = lean_unsigned_to_nat(0u);
v___y_2493_ = v___x_2502_;
goto v___jp_2492_;
}
v___jp_2481_:
{
lean_object* v___x_2485_; lean_object* v___x_2487_; 
v___x_2485_ = lean_nat_add(v___y_2482_, v___y_2484_);
lean_dec(v___y_2484_);
lean_dec(v___y_2482_);
if (v_isShared_2478_ == 0)
{
lean_ctor_set(v___x_2477_, 4, v_r_2455_);
lean_ctor_set(v___x_2477_, 3, v_r_2471_);
lean_ctor_set(v___x_2477_, 2, v_v_2453_);
lean_ctor_set(v___x_2477_, 1, v_k_2452_);
lean_ctor_set(v___x_2477_, 0, v___x_2485_);
v___x_2487_ = v___x_2477_;
goto v_reusejp_2486_;
}
else
{
lean_object* v_reuseFailAlloc_2491_; 
v_reuseFailAlloc_2491_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2491_, 0, v___x_2485_);
lean_ctor_set(v_reuseFailAlloc_2491_, 1, v_k_2452_);
lean_ctor_set(v_reuseFailAlloc_2491_, 2, v_v_2453_);
lean_ctor_set(v_reuseFailAlloc_2491_, 3, v_r_2471_);
lean_ctor_set(v_reuseFailAlloc_2491_, 4, v_r_2455_);
v___x_2487_ = v_reuseFailAlloc_2491_;
goto v_reusejp_2486_;
}
v_reusejp_2486_:
{
lean_object* v___x_2489_; 
if (v_isShared_2466_ == 0)
{
lean_ctor_set(v___x_2465_, 4, v___x_2487_);
lean_ctor_set(v___x_2465_, 3, v___y_2483_);
lean_ctor_set(v___x_2465_, 2, v_v_2469_);
lean_ctor_set(v___x_2465_, 1, v_k_2468_);
lean_ctor_set(v___x_2465_, 0, v___x_2480_);
v___x_2489_ = v___x_2465_;
goto v_reusejp_2488_;
}
else
{
lean_object* v_reuseFailAlloc_2490_; 
v_reuseFailAlloc_2490_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2490_, 0, v___x_2480_);
lean_ctor_set(v_reuseFailAlloc_2490_, 1, v_k_2468_);
lean_ctor_set(v_reuseFailAlloc_2490_, 2, v_v_2469_);
lean_ctor_set(v_reuseFailAlloc_2490_, 3, v___y_2483_);
lean_ctor_set(v_reuseFailAlloc_2490_, 4, v___x_2487_);
v___x_2489_ = v_reuseFailAlloc_2490_;
goto v_reusejp_2488_;
}
v_reusejp_2488_:
{
return v___x_2489_;
}
}
}
v___jp_2492_:
{
lean_object* v___x_2494_; lean_object* v___x_2496_; 
v___x_2494_ = lean_nat_add(v___x_2479_, v___y_2493_);
lean_dec(v___y_2493_);
lean_dec(v___x_2479_);
if (v_isShared_2306_ == 0)
{
lean_ctor_set(v___x_2305_, 4, v_l_2470_);
lean_ctor_set(v___x_2305_, 0, v___x_2494_);
v___x_2496_ = v___x_2305_;
goto v_reusejp_2495_;
}
else
{
lean_object* v_reuseFailAlloc_2500_; 
v_reuseFailAlloc_2500_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2500_, 0, v___x_2494_);
lean_ctor_set(v_reuseFailAlloc_2500_, 1, v_k_2300_);
lean_ctor_set(v_reuseFailAlloc_2500_, 2, v_v_2301_);
lean_ctor_set(v_reuseFailAlloc_2500_, 3, v_l_2302_);
lean_ctor_set(v_reuseFailAlloc_2500_, 4, v_l_2470_);
v___x_2496_ = v_reuseFailAlloc_2500_;
goto v_reusejp_2495_;
}
v_reusejp_2495_:
{
lean_object* v___x_2497_; 
v___x_2497_ = lean_nat_add(v___x_2449_, v_size_2472_);
if (lean_obj_tag(v_r_2471_) == 0)
{
lean_object* v_size_2498_; 
v_size_2498_ = lean_ctor_get(v_r_2471_, 0);
lean_inc(v_size_2498_);
v___y_2482_ = v___x_2497_;
v___y_2483_ = v___x_2496_;
v___y_2484_ = v_size_2498_;
goto v___jp_2481_;
}
else
{
lean_object* v___x_2499_; 
v___x_2499_ = lean_unsigned_to_nat(0u);
v___y_2482_ = v___x_2497_;
v___y_2483_ = v___x_2496_;
v___y_2484_ = v___x_2499_;
goto v___jp_2481_;
}
}
}
}
}
else
{
lean_object* v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2513_; 
lean_del_object(v___x_2305_);
v___x_2509_ = lean_nat_add(v___x_2449_, v_size_2450_);
v___x_2510_ = lean_nat_add(v___x_2509_, v_size_2451_);
lean_dec(v_size_2451_);
v___x_2511_ = lean_nat_add(v___x_2509_, v_size_2467_);
lean_dec(v___x_2509_);
lean_inc_ref(v_l_2302_);
if (v_isShared_2466_ == 0)
{
lean_ctor_set(v___x_2465_, 4, v_l_2454_);
lean_ctor_set(v___x_2465_, 3, v_l_2302_);
lean_ctor_set(v___x_2465_, 2, v_v_2301_);
lean_ctor_set(v___x_2465_, 1, v_k_2300_);
lean_ctor_set(v___x_2465_, 0, v___x_2511_);
v___x_2513_ = v___x_2465_;
goto v_reusejp_2512_;
}
else
{
lean_object* v_reuseFailAlloc_2526_; 
v_reuseFailAlloc_2526_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2526_, 0, v___x_2511_);
lean_ctor_set(v_reuseFailAlloc_2526_, 1, v_k_2300_);
lean_ctor_set(v_reuseFailAlloc_2526_, 2, v_v_2301_);
lean_ctor_set(v_reuseFailAlloc_2526_, 3, v_l_2302_);
lean_ctor_set(v_reuseFailAlloc_2526_, 4, v_l_2454_);
v___x_2513_ = v_reuseFailAlloc_2526_;
goto v_reusejp_2512_;
}
v_reusejp_2512_:
{
lean_object* v___x_2515_; uint8_t v_isShared_2516_; uint8_t v_isSharedCheck_2520_; 
v_isSharedCheck_2520_ = !lean_is_exclusive(v_l_2302_);
if (v_isSharedCheck_2520_ == 0)
{
lean_object* v_unused_2521_; lean_object* v_unused_2522_; lean_object* v_unused_2523_; lean_object* v_unused_2524_; lean_object* v_unused_2525_; 
v_unused_2521_ = lean_ctor_get(v_l_2302_, 4);
lean_dec(v_unused_2521_);
v_unused_2522_ = lean_ctor_get(v_l_2302_, 3);
lean_dec(v_unused_2522_);
v_unused_2523_ = lean_ctor_get(v_l_2302_, 2);
lean_dec(v_unused_2523_);
v_unused_2524_ = lean_ctor_get(v_l_2302_, 1);
lean_dec(v_unused_2524_);
v_unused_2525_ = lean_ctor_get(v_l_2302_, 0);
lean_dec(v_unused_2525_);
v___x_2515_ = v_l_2302_;
v_isShared_2516_ = v_isSharedCheck_2520_;
goto v_resetjp_2514_;
}
else
{
lean_dec(v_l_2302_);
v___x_2515_ = lean_box(0);
v_isShared_2516_ = v_isSharedCheck_2520_;
goto v_resetjp_2514_;
}
v_resetjp_2514_:
{
lean_object* v___x_2518_; 
if (v_isShared_2516_ == 0)
{
lean_ctor_set(v___x_2515_, 4, v_r_2455_);
lean_ctor_set(v___x_2515_, 3, v___x_2513_);
lean_ctor_set(v___x_2515_, 2, v_v_2453_);
lean_ctor_set(v___x_2515_, 1, v_k_2452_);
lean_ctor_set(v___x_2515_, 0, v___x_2510_);
v___x_2518_ = v___x_2515_;
goto v_reusejp_2517_;
}
else
{
lean_object* v_reuseFailAlloc_2519_; 
v_reuseFailAlloc_2519_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2519_, 0, v___x_2510_);
lean_ctor_set(v_reuseFailAlloc_2519_, 1, v_k_2452_);
lean_ctor_set(v_reuseFailAlloc_2519_, 2, v_v_2453_);
lean_ctor_set(v_reuseFailAlloc_2519_, 3, v___x_2513_);
lean_ctor_set(v_reuseFailAlloc_2519_, 4, v_r_2455_);
v___x_2518_ = v_reuseFailAlloc_2519_;
goto v_reusejp_2517_;
}
v_reusejp_2517_:
{
return v___x_2518_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_2533_; 
v_l_2533_ = lean_ctor_get(v_impl_2448_, 3);
lean_inc(v_l_2533_);
if (lean_obj_tag(v_l_2533_) == 0)
{
lean_object* v_r_2534_; lean_object* v_k_2535_; lean_object* v_v_2536_; lean_object* v___x_2538_; uint8_t v_isShared_2539_; uint8_t v_isSharedCheck_2559_; 
v_r_2534_ = lean_ctor_get(v_impl_2448_, 4);
v_k_2535_ = lean_ctor_get(v_impl_2448_, 1);
v_v_2536_ = lean_ctor_get(v_impl_2448_, 2);
v_isSharedCheck_2559_ = !lean_is_exclusive(v_impl_2448_);
if (v_isSharedCheck_2559_ == 0)
{
lean_object* v_unused_2560_; lean_object* v_unused_2561_; 
v_unused_2560_ = lean_ctor_get(v_impl_2448_, 3);
lean_dec(v_unused_2560_);
v_unused_2561_ = lean_ctor_get(v_impl_2448_, 0);
lean_dec(v_unused_2561_);
v___x_2538_ = v_impl_2448_;
v_isShared_2539_ = v_isSharedCheck_2559_;
goto v_resetjp_2537_;
}
else
{
lean_inc(v_r_2534_);
lean_inc(v_v_2536_);
lean_inc(v_k_2535_);
lean_dec(v_impl_2448_);
v___x_2538_ = lean_box(0);
v_isShared_2539_ = v_isSharedCheck_2559_;
goto v_resetjp_2537_;
}
v_resetjp_2537_:
{
lean_object* v_k_2540_; lean_object* v_v_2541_; lean_object* v___x_2543_; uint8_t v_isShared_2544_; uint8_t v_isSharedCheck_2555_; 
v_k_2540_ = lean_ctor_get(v_l_2533_, 1);
v_v_2541_ = lean_ctor_get(v_l_2533_, 2);
v_isSharedCheck_2555_ = !lean_is_exclusive(v_l_2533_);
if (v_isSharedCheck_2555_ == 0)
{
lean_object* v_unused_2556_; lean_object* v_unused_2557_; lean_object* v_unused_2558_; 
v_unused_2556_ = lean_ctor_get(v_l_2533_, 4);
lean_dec(v_unused_2556_);
v_unused_2557_ = lean_ctor_get(v_l_2533_, 3);
lean_dec(v_unused_2557_);
v_unused_2558_ = lean_ctor_get(v_l_2533_, 0);
lean_dec(v_unused_2558_);
v___x_2543_ = v_l_2533_;
v_isShared_2544_ = v_isSharedCheck_2555_;
goto v_resetjp_2542_;
}
else
{
lean_inc(v_v_2541_);
lean_inc(v_k_2540_);
lean_dec(v_l_2533_);
v___x_2543_ = lean_box(0);
v_isShared_2544_ = v_isSharedCheck_2555_;
goto v_resetjp_2542_;
}
v_resetjp_2542_:
{
lean_object* v___x_2545_; lean_object* v___x_2547_; 
v___x_2545_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_2534_, 2);
if (v_isShared_2544_ == 0)
{
lean_ctor_set(v___x_2543_, 4, v_r_2534_);
lean_ctor_set(v___x_2543_, 3, v_r_2534_);
lean_ctor_set(v___x_2543_, 2, v_v_2301_);
lean_ctor_set(v___x_2543_, 1, v_k_2300_);
lean_ctor_set(v___x_2543_, 0, v___x_2449_);
v___x_2547_ = v___x_2543_;
goto v_reusejp_2546_;
}
else
{
lean_object* v_reuseFailAlloc_2554_; 
v_reuseFailAlloc_2554_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2554_, 0, v___x_2449_);
lean_ctor_set(v_reuseFailAlloc_2554_, 1, v_k_2300_);
lean_ctor_set(v_reuseFailAlloc_2554_, 2, v_v_2301_);
lean_ctor_set(v_reuseFailAlloc_2554_, 3, v_r_2534_);
lean_ctor_set(v_reuseFailAlloc_2554_, 4, v_r_2534_);
v___x_2547_ = v_reuseFailAlloc_2554_;
goto v_reusejp_2546_;
}
v_reusejp_2546_:
{
lean_object* v___x_2549_; 
lean_inc(v_r_2534_);
if (v_isShared_2539_ == 0)
{
lean_ctor_set(v___x_2538_, 3, v_r_2534_);
lean_ctor_set(v___x_2538_, 0, v___x_2449_);
v___x_2549_ = v___x_2538_;
goto v_reusejp_2548_;
}
else
{
lean_object* v_reuseFailAlloc_2553_; 
v_reuseFailAlloc_2553_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2553_, 0, v___x_2449_);
lean_ctor_set(v_reuseFailAlloc_2553_, 1, v_k_2535_);
lean_ctor_set(v_reuseFailAlloc_2553_, 2, v_v_2536_);
lean_ctor_set(v_reuseFailAlloc_2553_, 3, v_r_2534_);
lean_ctor_set(v_reuseFailAlloc_2553_, 4, v_r_2534_);
v___x_2549_ = v_reuseFailAlloc_2553_;
goto v_reusejp_2548_;
}
v_reusejp_2548_:
{
lean_object* v___x_2551_; 
if (v_isShared_2306_ == 0)
{
lean_ctor_set(v___x_2305_, 4, v___x_2549_);
lean_ctor_set(v___x_2305_, 3, v___x_2547_);
lean_ctor_set(v___x_2305_, 2, v_v_2541_);
lean_ctor_set(v___x_2305_, 1, v_k_2540_);
lean_ctor_set(v___x_2305_, 0, v___x_2545_);
v___x_2551_ = v___x_2305_;
goto v_reusejp_2550_;
}
else
{
lean_object* v_reuseFailAlloc_2552_; 
v_reuseFailAlloc_2552_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2552_, 0, v___x_2545_);
lean_ctor_set(v_reuseFailAlloc_2552_, 1, v_k_2540_);
lean_ctor_set(v_reuseFailAlloc_2552_, 2, v_v_2541_);
lean_ctor_set(v_reuseFailAlloc_2552_, 3, v___x_2547_);
lean_ctor_set(v_reuseFailAlloc_2552_, 4, v___x_2549_);
v___x_2551_ = v_reuseFailAlloc_2552_;
goto v_reusejp_2550_;
}
v_reusejp_2550_:
{
return v___x_2551_;
}
}
}
}
}
}
else
{
lean_object* v_r_2562_; 
v_r_2562_ = lean_ctor_get(v_impl_2448_, 4);
lean_inc(v_r_2562_);
if (lean_obj_tag(v_r_2562_) == 0)
{
lean_object* v_k_2563_; lean_object* v_v_2564_; lean_object* v___x_2566_; uint8_t v_isShared_2567_; uint8_t v_isSharedCheck_2575_; 
v_k_2563_ = lean_ctor_get(v_impl_2448_, 1);
v_v_2564_ = lean_ctor_get(v_impl_2448_, 2);
v_isSharedCheck_2575_ = !lean_is_exclusive(v_impl_2448_);
if (v_isSharedCheck_2575_ == 0)
{
lean_object* v_unused_2576_; lean_object* v_unused_2577_; lean_object* v_unused_2578_; 
v_unused_2576_ = lean_ctor_get(v_impl_2448_, 4);
lean_dec(v_unused_2576_);
v_unused_2577_ = lean_ctor_get(v_impl_2448_, 3);
lean_dec(v_unused_2577_);
v_unused_2578_ = lean_ctor_get(v_impl_2448_, 0);
lean_dec(v_unused_2578_);
v___x_2566_ = v_impl_2448_;
v_isShared_2567_ = v_isSharedCheck_2575_;
goto v_resetjp_2565_;
}
else
{
lean_inc(v_v_2564_);
lean_inc(v_k_2563_);
lean_dec(v_impl_2448_);
v___x_2566_ = lean_box(0);
v_isShared_2567_ = v_isSharedCheck_2575_;
goto v_resetjp_2565_;
}
v_resetjp_2565_:
{
lean_object* v___x_2568_; lean_object* v___x_2570_; 
v___x_2568_ = lean_unsigned_to_nat(3u);
if (v_isShared_2567_ == 0)
{
lean_ctor_set(v___x_2566_, 4, v_l_2533_);
lean_ctor_set(v___x_2566_, 2, v_v_2301_);
lean_ctor_set(v___x_2566_, 1, v_k_2300_);
lean_ctor_set(v___x_2566_, 0, v___x_2449_);
v___x_2570_ = v___x_2566_;
goto v_reusejp_2569_;
}
else
{
lean_object* v_reuseFailAlloc_2574_; 
v_reuseFailAlloc_2574_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2574_, 0, v___x_2449_);
lean_ctor_set(v_reuseFailAlloc_2574_, 1, v_k_2300_);
lean_ctor_set(v_reuseFailAlloc_2574_, 2, v_v_2301_);
lean_ctor_set(v_reuseFailAlloc_2574_, 3, v_l_2533_);
lean_ctor_set(v_reuseFailAlloc_2574_, 4, v_l_2533_);
v___x_2570_ = v_reuseFailAlloc_2574_;
goto v_reusejp_2569_;
}
v_reusejp_2569_:
{
lean_object* v___x_2572_; 
if (v_isShared_2306_ == 0)
{
lean_ctor_set(v___x_2305_, 4, v_r_2562_);
lean_ctor_set(v___x_2305_, 3, v___x_2570_);
lean_ctor_set(v___x_2305_, 2, v_v_2564_);
lean_ctor_set(v___x_2305_, 1, v_k_2563_);
lean_ctor_set(v___x_2305_, 0, v___x_2568_);
v___x_2572_ = v___x_2305_;
goto v_reusejp_2571_;
}
else
{
lean_object* v_reuseFailAlloc_2573_; 
v_reuseFailAlloc_2573_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2573_, 0, v___x_2568_);
lean_ctor_set(v_reuseFailAlloc_2573_, 1, v_k_2563_);
lean_ctor_set(v_reuseFailAlloc_2573_, 2, v_v_2564_);
lean_ctor_set(v_reuseFailAlloc_2573_, 3, v___x_2570_);
lean_ctor_set(v_reuseFailAlloc_2573_, 4, v_r_2562_);
v___x_2572_ = v_reuseFailAlloc_2573_;
goto v_reusejp_2571_;
}
v_reusejp_2571_:
{
return v___x_2572_;
}
}
}
}
else
{
lean_object* v___x_2579_; lean_object* v___x_2581_; 
v___x_2579_ = lean_unsigned_to_nat(2u);
if (v_isShared_2306_ == 0)
{
lean_ctor_set(v___x_2305_, 4, v_impl_2448_);
lean_ctor_set(v___x_2305_, 3, v_r_2562_);
lean_ctor_set(v___x_2305_, 0, v___x_2579_);
v___x_2581_ = v___x_2305_;
goto v_reusejp_2580_;
}
else
{
lean_object* v_reuseFailAlloc_2582_; 
v_reuseFailAlloc_2582_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2582_, 0, v___x_2579_);
lean_ctor_set(v_reuseFailAlloc_2582_, 1, v_k_2300_);
lean_ctor_set(v_reuseFailAlloc_2582_, 2, v_v_2301_);
lean_ctor_set(v_reuseFailAlloc_2582_, 3, v_r_2562_);
lean_ctor_set(v_reuseFailAlloc_2582_, 4, v_impl_2448_);
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
}
}
}
}
else
{
lean_object* v___x_2584_; lean_object* v___x_2585_; 
v___x_2584_ = lean_unsigned_to_nat(1u);
v___x_2585_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2585_, 0, v___x_2584_);
lean_ctor_set(v___x_2585_, 1, v_k_2296_);
lean_ctor_set(v___x_2585_, 2, v_v_2297_);
lean_ctor_set(v___x_2585_, 3, v_t_2298_);
lean_ctor_set(v___x_2585_, 4, v_t_2298_);
return v___x_2585_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Level_collectMVars_spec__0___redArg(lean_object* v_k_2586_, lean_object* v_t_2587_){
_start:
{
if (lean_obj_tag(v_t_2587_) == 0)
{
lean_object* v_k_2588_; lean_object* v_l_2589_; lean_object* v_r_2590_; uint8_t v___x_2591_; 
v_k_2588_ = lean_ctor_get(v_t_2587_, 1);
v_l_2589_ = lean_ctor_get(v_t_2587_, 3);
v_r_2590_ = lean_ctor_get(v_t_2587_, 4);
v___x_2591_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2586_, v_k_2588_);
switch(v___x_2591_)
{
case 0:
{
v_t_2587_ = v_l_2589_;
goto _start;
}
case 1:
{
uint8_t v___x_2593_; 
v___x_2593_ = 1;
return v___x_2593_;
}
default: 
{
v_t_2587_ = v_r_2590_;
goto _start;
}
}
}
else
{
uint8_t v___x_2595_; 
v___x_2595_ = 0;
return v___x_2595_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Level_collectMVars_spec__0___redArg___boxed(lean_object* v_k_2596_, lean_object* v_t_2597_){
_start:
{
uint8_t v_res_2598_; lean_object* v_r_2599_; 
v_res_2598_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Level_collectMVars_spec__0___redArg(v_k_2596_, v_t_2597_);
lean_dec(v_t_2597_);
lean_dec(v_k_2596_);
v_r_2599_ = lean_box(v_res_2598_);
return v_r_2599_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_collectMVars(lean_object* v_u_2600_, lean_object* v_s_2601_){
_start:
{
lean_object* v_u_2603_; lean_object* v_v_2604_; 
switch(lean_obj_tag(v_u_2600_))
{
case 1:
{
lean_object* v_a_2607_; 
v_a_2607_ = lean_ctor_get(v_u_2600_, 0);
lean_inc(v_a_2607_);
lean_dec_ref_known(v_u_2600_, 1);
v_u_2600_ = v_a_2607_;
goto _start;
}
case 2:
{
lean_object* v_a_2609_; lean_object* v_a_2610_; 
v_a_2609_ = lean_ctor_get(v_u_2600_, 0);
lean_inc(v_a_2609_);
v_a_2610_ = lean_ctor_get(v_u_2600_, 1);
lean_inc(v_a_2610_);
lean_dec_ref_known(v_u_2600_, 2);
v_u_2603_ = v_a_2609_;
v_v_2604_ = v_a_2610_;
goto v___jp_2602_;
}
case 3:
{
lean_object* v_a_2611_; lean_object* v_a_2612_; 
v_a_2611_ = lean_ctor_get(v_u_2600_, 0);
lean_inc(v_a_2611_);
v_a_2612_ = lean_ctor_get(v_u_2600_, 1);
lean_inc(v_a_2612_);
lean_dec_ref_known(v_u_2600_, 2);
v_u_2603_ = v_a_2611_;
v_v_2604_ = v_a_2612_;
goto v___jp_2602_;
}
case 5:
{
lean_object* v_a_2613_; uint8_t v___x_2614_; 
v_a_2613_ = lean_ctor_get(v_u_2600_, 0);
lean_inc(v_a_2613_);
lean_dec_ref_known(v_u_2600_, 1);
v___x_2614_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Level_collectMVars_spec__0___redArg(v_a_2613_, v_s_2601_);
if (v___x_2614_ == 0)
{
lean_object* v___x_2615_; lean_object* v___x_2616_; 
v___x_2615_ = lean_box(0);
v___x_2616_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Level_collectMVars_spec__1___redArg(v_a_2613_, v___x_2615_, v_s_2601_);
return v___x_2616_;
}
else
{
lean_dec(v_a_2613_);
return v_s_2601_;
}
}
default: 
{
lean_dec(v_u_2600_);
return v_s_2601_;
}
}
v___jp_2602_:
{
lean_object* v___x_2605_; 
v___x_2605_ = l_Lean_Level_collectMVars(v_v_2604_, v_s_2601_);
v_u_2600_ = v_u_2603_;
v_s_2601_ = v___x_2605_;
goto _start;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Level_collectMVars_spec__0(lean_object* v_00_u03b2_2617_, lean_object* v_k_2618_, lean_object* v_t_2619_){
_start:
{
uint8_t v___x_2620_; 
v___x_2620_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Level_collectMVars_spec__0___redArg(v_k_2618_, v_t_2619_);
return v___x_2620_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Level_collectMVars_spec__0___boxed(lean_object* v_00_u03b2_2621_, lean_object* v_k_2622_, lean_object* v_t_2623_){
_start:
{
uint8_t v_res_2624_; lean_object* v_r_2625_; 
v_res_2624_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Level_collectMVars_spec__0(v_00_u03b2_2621_, v_k_2622_, v_t_2623_);
lean_dec(v_t_2623_);
lean_dec(v_k_2622_);
v_r_2625_ = lean_box(v_res_2624_);
return v_r_2625_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Level_collectMVars_spec__1(lean_object* v_00_u03b2_2626_, lean_object* v_k_2627_, lean_object* v_v_2628_, lean_object* v_t_2629_, lean_object* v_hl_2630_){
_start:
{
lean_object* v___x_2631_; 
v___x_2631_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Level_collectMVars_spec__1___redArg(v_k_2627_, v_v_2628_, v_t_2629_);
return v___x_2631_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_find_x3f_visit(lean_object* v_p_2632_, lean_object* v_u_2633_){
_start:
{
lean_object* v_u_2635_; lean_object* v_v_2636_; lean_object* v___x_2639_; uint8_t v___x_2640_; 
lean_inc_ref(v_p_2632_);
lean_inc(v_u_2633_);
v___x_2639_ = lean_apply_1(v_p_2632_, v_u_2633_);
v___x_2640_ = lean_unbox(v___x_2639_);
if (v___x_2640_ == 0)
{
switch(lean_obj_tag(v_u_2633_))
{
case 1:
{
lean_object* v_a_2641_; 
v_a_2641_ = lean_ctor_get(v_u_2633_, 0);
lean_inc(v_a_2641_);
lean_dec_ref_known(v_u_2633_, 1);
v_u_2633_ = v_a_2641_;
goto _start;
}
case 2:
{
lean_object* v_a_2643_; lean_object* v_a_2644_; 
v_a_2643_ = lean_ctor_get(v_u_2633_, 0);
lean_inc(v_a_2643_);
v_a_2644_ = lean_ctor_get(v_u_2633_, 1);
lean_inc(v_a_2644_);
lean_dec_ref_known(v_u_2633_, 2);
v_u_2635_ = v_a_2643_;
v_v_2636_ = v_a_2644_;
goto v___jp_2634_;
}
case 3:
{
lean_object* v_a_2645_; lean_object* v_a_2646_; 
v_a_2645_ = lean_ctor_get(v_u_2633_, 0);
lean_inc(v_a_2645_);
v_a_2646_ = lean_ctor_get(v_u_2633_, 1);
lean_inc(v_a_2646_);
lean_dec_ref_known(v_u_2633_, 2);
v_u_2635_ = v_a_2645_;
v_v_2636_ = v_a_2646_;
goto v___jp_2634_;
}
default: 
{
lean_object* v___x_2647_; 
lean_dec(v_u_2633_);
lean_dec_ref(v_p_2632_);
v___x_2647_ = lean_box(0);
return v___x_2647_;
}
}
}
else
{
lean_object* v___x_2648_; 
lean_dec_ref(v_p_2632_);
v___x_2648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2648_, 0, v_u_2633_);
return v___x_2648_;
}
v___jp_2634_:
{
lean_object* v___x_2637_; 
lean_inc_ref(v_p_2632_);
v___x_2637_ = l___private_Lean_Level_0__Lean_Level_find_x3f_visit(v_p_2632_, v_u_2635_);
if (lean_obj_tag(v___x_2637_) == 0)
{
v_u_2633_ = v_v_2636_;
goto _start;
}
else
{
lean_dec(v_v_2636_);
lean_dec_ref(v_p_2632_);
return v___x_2637_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_find_x3f(lean_object* v_u_2649_, lean_object* v_p_2650_){
_start:
{
lean_object* v___x_2651_; 
v___x_2651_ = l___private_Lean_Level_0__Lean_Level_find_x3f_visit(v_p_2650_, v_u_2649_);
return v___x_2651_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_any(lean_object* v_u_2652_, lean_object* v_p_2653_){
_start:
{
lean_object* v___x_2654_; 
v___x_2654_ = l___private_Lean_Level_0__Lean_Level_find_x3f_visit(v_p_2653_, v_u_2652_);
if (lean_obj_tag(v___x_2654_) == 0)
{
uint8_t v___x_2655_; 
v___x_2655_ = 0;
return v___x_2655_;
}
else
{
uint8_t v___x_2656_; 
lean_dec_ref_known(v___x_2654_, 1);
v___x_2656_ = 1;
return v___x_2656_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_any___boxed(lean_object* v_u_2657_, lean_object* v_p_2658_){
_start:
{
uint8_t v_res_2659_; lean_object* v_r_2660_; 
v_res_2659_ = l_Lean_Level_any(v_u_2657_, v_p_2658_);
v_r_2660_ = lean_box(v_res_2659_);
return v_r_2660_;
}
}
LEAN_EXPORT lean_object* l_Lean_Nat_toLevel(lean_object* v_n_2661_){
_start:
{
lean_object* v___x_2662_; 
v___x_2662_ = l_Lean_Level_ofNat(v_n_2661_);
return v___x_2662_;
}
}
LEAN_EXPORT lean_object* l_Lean_Nat_toLevel___boxed(lean_object* v_n_2663_){
_start:
{
lean_object* v_res_2664_; 
v_res_2664_ = l_Lean_Nat_toLevel(v_n_2663_);
lean_dec(v_n_2663_);
return v_res_2664_;
}
}
lean_object* runtime_initialize_Init_Data_Array_QSort(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_PersistentHashSet(uint8_t builtin);
lean_object* runtime_initialize_Lean_Hygiene(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Option_Coe(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Internal_Linear(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Level(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
