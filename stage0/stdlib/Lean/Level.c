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
lean_object* l_Array_mkArray0___redArg();
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
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionLMVarIdMap___aux__1___redArg();
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionLMVarIdMap___aux__1___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionLMVarIdMap___aux__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionLMVarIdMap___redArg();
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionLMVarIdMap___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionLMVarIdMap(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instForInLMVarIdMapProdLMVarIdOfMonad___aux__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instForInLMVarIdMapProdLMVarIdOfMonad___aux__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instForInLMVarIdMapProdLMVarIdOfMonad___aux__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instForInLMVarIdMapProdLMVarIdOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instForInLMVarIdMapProdLMVarIdOfMonad(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedLMVarIdMap___redArg();
LEAN_EXPORT lean_object* l_Lean_instInhabitedLMVarIdMap___redArg___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_mkLevelZeroEx___redArg();
LEAN_EXPORT lean_object* l_Lean_mkLevelZeroEx___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lean_level_mk_zero(lean_object*);
LEAN_EXPORT lean_object* lean_level_mk_succ(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionLMVarIdMap___aux__1___redArg(){
_start:
{
lean_object* v___x_240_; 
v___x_240_ = lean_box(1);
return v___x_240_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionLMVarIdMap___aux__1___redArg___boxed(lean_object* v___dummy_241_){
_start:
{
lean_object* v_res_242_; 
v_res_242_ = l_Lean_instEmptyCollectionLMVarIdMap___aux__1___redArg();
return v_res_242_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionLMVarIdMap___aux__1(lean_object* v_00_u03b1_243_){
_start:
{
lean_object* v___x_244_; 
v___x_244_ = lean_box(1);
return v___x_244_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionLMVarIdMap___redArg(){
_start:
{
lean_object* v___x_246_; 
v___x_246_ = lean_box(1);
return v___x_246_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionLMVarIdMap___redArg___boxed(lean_object* v___dummy_247_){
_start:
{
lean_object* v_res_248_; 
v_res_248_ = l_Lean_instEmptyCollectionLMVarIdMap___redArg();
return v_res_248_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionLMVarIdMap(lean_object* v_00_u03b1_249_){
_start:
{
lean_object* v___x_250_; 
v___x_250_ = lean_box(1);
return v___x_250_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInLMVarIdMapProdLMVarIdOfMonad___aux__1___redArg___lam__0(lean_object* v_f_251_, lean_object* v_a_252_, lean_object* v_b_253_, lean_object* v_c_254_){
_start:
{
lean_object* v___x_255_; lean_object* v___x_256_; 
v___x_255_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_255_, 0, v_a_252_);
lean_ctor_set(v___x_255_, 1, v_b_253_);
v___x_256_ = lean_apply_2(v_f_251_, v___x_255_, v_c_254_);
return v___x_256_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInLMVarIdMapProdLMVarIdOfMonad___aux__1___redArg(lean_object* v_inst_257_, lean_object* v_m_258_, lean_object* v_init_259_, lean_object* v_f_260_){
_start:
{
lean_object* v_toApplicative_261_; lean_object* v_toBind_262_; lean_object* v_toPure_263_; lean_object* v___f_264_; lean_object* v___x_265_; lean_object* v___f_266_; lean_object* v___x_267_; 
v_toApplicative_261_ = lean_ctor_get(v_inst_257_, 0);
v_toBind_262_ = lean_ctor_get(v_inst_257_, 1);
lean_inc(v_toBind_262_);
v_toPure_263_ = lean_ctor_get(v_toApplicative_261_, 1);
lean_inc(v_toPure_263_);
v___f_264_ = lean_alloc_closure((void*)(l_Lean_instForInLMVarIdMapProdLMVarIdOfMonad___aux__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_264_, 0, v_f_260_);
v___x_265_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_257_, v___f_264_, v_init_259_, v_m_258_);
v___f_266_ = lean_alloc_closure((void*)(l_Lean_instForInLMVarIdSetLMVarIdOfMonad___aux__1___redArg___lam__1), 2, 1);
lean_closure_set(v___f_266_, 0, v_toPure_263_);
v___x_267_ = lean_apply_4(v_toBind_262_, lean_box(0), lean_box(0), v___x_265_, v___f_266_);
return v___x_267_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInLMVarIdMapProdLMVarIdOfMonad___aux__1(lean_object* v_m_268_, lean_object* v_00_u03b1_269_, lean_object* v_inst_270_, lean_object* v_00_u03b2_271_, lean_object* v_m_272_, lean_object* v_init_273_, lean_object* v_f_274_){
_start:
{
lean_object* v_toApplicative_275_; lean_object* v_toBind_276_; lean_object* v_toPure_277_; lean_object* v___f_278_; lean_object* v___x_279_; lean_object* v___f_280_; lean_object* v___x_281_; 
v_toApplicative_275_ = lean_ctor_get(v_inst_270_, 0);
v_toBind_276_ = lean_ctor_get(v_inst_270_, 1);
lean_inc(v_toBind_276_);
v_toPure_277_ = lean_ctor_get(v_toApplicative_275_, 1);
lean_inc(v_toPure_277_);
v___f_278_ = lean_alloc_closure((void*)(l_Lean_instForInLMVarIdMapProdLMVarIdOfMonad___aux__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_278_, 0, v_f_274_);
v___x_279_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_270_, v___f_278_, v_init_273_, v_m_272_);
v___f_280_ = lean_alloc_closure((void*)(l_Lean_instForInLMVarIdSetLMVarIdOfMonad___aux__1___redArg___lam__1), 2, 1);
lean_closure_set(v___f_280_, 0, v_toPure_277_);
v___x_281_ = lean_apply_4(v_toBind_276_, lean_box(0), lean_box(0), v___x_279_, v___f_280_);
return v___x_281_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInLMVarIdMapProdLMVarIdOfMonad___redArg(lean_object* v_inst_282_){
_start:
{
lean_object* v___x_283_; 
v___x_283_ = lean_alloc_closure((void*)(l_Lean_instForInLMVarIdMapProdLMVarIdOfMonad___aux__1), 7, 3);
lean_closure_set(v___x_283_, 0, lean_box(0));
lean_closure_set(v___x_283_, 1, lean_box(0));
lean_closure_set(v___x_283_, 2, v_inst_282_);
return v___x_283_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInLMVarIdMapProdLMVarIdOfMonad(lean_object* v_m_284_, lean_object* v_00_u03b1_285_, lean_object* v_inst_286_){
_start:
{
lean_object* v___x_287_; 
v___x_287_ = lean_alloc_closure((void*)(l_Lean_instForInLMVarIdMapProdLMVarIdOfMonad___aux__1), 7, 3);
lean_closure_set(v___x_287_, 0, lean_box(0));
lean_closure_set(v___x_287_, 1, lean_box(0));
lean_closure_set(v___x_287_, 2, v_inst_286_);
return v___x_287_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedLMVarIdMap___redArg(){
_start:
{
lean_object* v___x_289_; 
v___x_289_ = lean_box(1);
return v___x_289_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedLMVarIdMap___redArg___boxed(lean_object* v___dummy_290_){
_start:
{
lean_object* v_res_291_; 
v_res_291_ = l_Lean_instInhabitedLMVarIdMap___redArg();
return v_res_291_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedLMVarIdMap(lean_object* v_00_u03b1_292_){
_start:
{
lean_object* v___x_293_; 
v___x_293_ = lean_box(1);
return v___x_293_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_ctorIdx(lean_object* v_x_294_){
_start:
{
switch(lean_obj_tag(v_x_294_))
{
case 0:
{
lean_object* v___x_295_; 
v___x_295_ = lean_unsigned_to_nat(0u);
return v___x_295_;
}
case 1:
{
lean_object* v___x_296_; 
v___x_296_ = lean_unsigned_to_nat(1u);
return v___x_296_;
}
case 2:
{
lean_object* v___x_297_; 
v___x_297_ = lean_unsigned_to_nat(2u);
return v___x_297_;
}
case 3:
{
lean_object* v___x_298_; 
v___x_298_ = lean_unsigned_to_nat(3u);
return v___x_298_;
}
case 4:
{
lean_object* v___x_299_; 
v___x_299_ = lean_unsigned_to_nat(4u);
return v___x_299_;
}
default: 
{
lean_object* v___x_300_; 
v___x_300_ = lean_unsigned_to_nat(5u);
return v___x_300_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_ctorIdx___boxed(lean_object* v_x_301_){
_start:
{
lean_object* v_res_302_; 
v_res_302_ = l_Lean_Level_ctorIdx(v_x_301_);
lean_dec(v_x_301_);
return v_res_302_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_ctorElim___redArg(lean_object* v_t_303_, lean_object* v_k_304_){
_start:
{
switch(lean_obj_tag(v_t_303_))
{
case 0:
{
return v_k_304_;
}
case 2:
{
lean_object* v_a_305_; lean_object* v_a_306_; lean_object* v___x_307_; 
v_a_305_ = lean_ctor_get(v_t_303_, 0);
lean_inc(v_a_305_);
v_a_306_ = lean_ctor_get(v_t_303_, 1);
lean_inc(v_a_306_);
lean_dec_ref_known(v_t_303_, 2);
v___x_307_ = lean_apply_2(v_k_304_, v_a_305_, v_a_306_);
return v___x_307_;
}
case 3:
{
lean_object* v_a_308_; lean_object* v_a_309_; lean_object* v___x_310_; 
v_a_308_ = lean_ctor_get(v_t_303_, 0);
lean_inc(v_a_308_);
v_a_309_ = lean_ctor_get(v_t_303_, 1);
lean_inc(v_a_309_);
lean_dec_ref_known(v_t_303_, 2);
v___x_310_ = lean_apply_2(v_k_304_, v_a_308_, v_a_309_);
return v___x_310_;
}
default: 
{
lean_object* v_a_311_; lean_object* v___x_312_; 
v_a_311_ = lean_ctor_get(v_t_303_, 0);
lean_inc(v_a_311_);
lean_dec(v_t_303_);
v___x_312_ = lean_apply_1(v_k_304_, v_a_311_);
return v___x_312_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_ctorElim(lean_object* v_motive_313_, lean_object* v_ctorIdx_314_, lean_object* v_t_315_, lean_object* v_h_316_, lean_object* v_k_317_){
_start:
{
lean_object* v___x_318_; 
v___x_318_ = l_Lean_Level_ctorElim___redArg(v_t_315_, v_k_317_);
return v___x_318_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_ctorElim___boxed(lean_object* v_motive_319_, lean_object* v_ctorIdx_320_, lean_object* v_t_321_, lean_object* v_h_322_, lean_object* v_k_323_){
_start:
{
lean_object* v_res_324_; 
v_res_324_ = l_Lean_Level_ctorElim(v_motive_319_, v_ctorIdx_320_, v_t_321_, v_h_322_, v_k_323_);
lean_dec(v_ctorIdx_320_);
return v_res_324_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_zero_elim___redArg(lean_object* v_t_325_, lean_object* v_zero_326_){
_start:
{
lean_object* v___x_327_; 
v___x_327_ = l_Lean_Level_ctorElim___redArg(v_t_325_, v_zero_326_);
return v___x_327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_zero_elim(lean_object* v_motive_328_, lean_object* v_t_329_, lean_object* v_h_330_, lean_object* v_zero_331_){
_start:
{
lean_object* v___x_332_; 
v___x_332_ = l_Lean_Level_ctorElim___redArg(v_t_329_, v_zero_331_);
return v___x_332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_succ_elim___redArg(lean_object* v_t_333_, lean_object* v_succ_334_){
_start:
{
lean_object* v___x_335_; 
v___x_335_ = l_Lean_Level_ctorElim___redArg(v_t_333_, v_succ_334_);
return v___x_335_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_succ_elim(lean_object* v_motive_336_, lean_object* v_t_337_, lean_object* v_h_338_, lean_object* v_succ_339_){
_start:
{
lean_object* v___x_340_; 
v___x_340_ = l_Lean_Level_ctorElim___redArg(v_t_337_, v_succ_339_);
return v___x_340_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_max_elim___redArg(lean_object* v_t_341_, lean_object* v_max_342_){
_start:
{
lean_object* v___x_343_; 
v___x_343_ = l_Lean_Level_ctorElim___redArg(v_t_341_, v_max_342_);
return v___x_343_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_max_elim(lean_object* v_motive_344_, lean_object* v_t_345_, lean_object* v_h_346_, lean_object* v_max_347_){
_start:
{
lean_object* v___x_348_; 
v___x_348_ = l_Lean_Level_ctorElim___redArg(v_t_345_, v_max_347_);
return v___x_348_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_imax_elim___redArg(lean_object* v_t_349_, lean_object* v_imax_350_){
_start:
{
lean_object* v___x_351_; 
v___x_351_ = l_Lean_Level_ctorElim___redArg(v_t_349_, v_imax_350_);
return v___x_351_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_imax_elim(lean_object* v_motive_352_, lean_object* v_t_353_, lean_object* v_h_354_, lean_object* v_imax_355_){
_start:
{
lean_object* v___x_356_; 
v___x_356_ = l_Lean_Level_ctorElim___redArg(v_t_353_, v_imax_355_);
return v___x_356_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_param_elim___redArg(lean_object* v_t_357_, lean_object* v_param_358_){
_start:
{
lean_object* v___x_359_; 
v___x_359_ = l_Lean_Level_ctorElim___redArg(v_t_357_, v_param_358_);
return v___x_359_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_param_elim(lean_object* v_motive_360_, lean_object* v_t_361_, lean_object* v_h_362_, lean_object* v_param_363_){
_start:
{
lean_object* v___x_364_; 
v___x_364_ = l_Lean_Level_ctorElim___redArg(v_t_361_, v_param_363_);
return v___x_364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_mvar_elim___redArg(lean_object* v_t_365_, lean_object* v_mvar_366_){
_start:
{
lean_object* v___x_367_; 
v___x_367_ = l_Lean_Level_ctorElim___redArg(v_t_365_, v_mvar_366_);
return v___x_367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_mvar_elim(lean_object* v_motive_368_, lean_object* v_t_369_, lean_object* v_h_370_, lean_object* v_mvar_371_){
_start:
{
lean_object* v___x_372_; 
v___x_372_ = l_Lean_Level_ctorElim___redArg(v_t_369_, v_mvar_371_);
return v___x_372_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_casesOn___override___redArg(lean_object* v_t_373_, lean_object* v_zero_374_, lean_object* v_succ_375_, lean_object* v_max_376_, lean_object* v_imax_377_, lean_object* v_param_378_, lean_object* v_mvar_379_){
_start:
{
switch(lean_obj_tag(v_t_373_))
{
case 0:
{
lean_dec(v_mvar_379_);
lean_dec(v_param_378_);
lean_dec(v_imax_377_);
lean_dec(v_max_376_);
lean_dec(v_succ_375_);
lean_inc(v_zero_374_);
return v_zero_374_;
}
case 1:
{
lean_object* v_a_380_; lean_object* v___x_381_; 
lean_dec(v_mvar_379_);
lean_dec(v_param_378_);
lean_dec(v_imax_377_);
lean_dec(v_max_376_);
v_a_380_ = lean_ctor_get(v_t_373_, 0);
lean_inc(v_a_380_);
lean_dec_ref_known(v_t_373_, 1);
v___x_381_ = lean_apply_1(v_succ_375_, v_a_380_);
return v___x_381_;
}
case 2:
{
lean_object* v_a_382_; lean_object* v_a_383_; lean_object* v___x_384_; 
lean_dec(v_mvar_379_);
lean_dec(v_param_378_);
lean_dec(v_imax_377_);
lean_dec(v_succ_375_);
v_a_382_ = lean_ctor_get(v_t_373_, 0);
lean_inc(v_a_382_);
v_a_383_ = lean_ctor_get(v_t_373_, 1);
lean_inc(v_a_383_);
lean_dec_ref_known(v_t_373_, 2);
v___x_384_ = lean_apply_2(v_max_376_, v_a_382_, v_a_383_);
return v___x_384_;
}
case 3:
{
lean_object* v_a_385_; lean_object* v_a_386_; lean_object* v___x_387_; 
lean_dec(v_mvar_379_);
lean_dec(v_param_378_);
lean_dec(v_max_376_);
lean_dec(v_succ_375_);
v_a_385_ = lean_ctor_get(v_t_373_, 0);
lean_inc(v_a_385_);
v_a_386_ = lean_ctor_get(v_t_373_, 1);
lean_inc(v_a_386_);
lean_dec_ref_known(v_t_373_, 2);
v___x_387_ = lean_apply_2(v_imax_377_, v_a_385_, v_a_386_);
return v___x_387_;
}
case 4:
{
lean_object* v_a_388_; lean_object* v___x_389_; 
lean_dec(v_mvar_379_);
lean_dec(v_imax_377_);
lean_dec(v_max_376_);
lean_dec(v_succ_375_);
v_a_388_ = lean_ctor_get(v_t_373_, 0);
lean_inc(v_a_388_);
lean_dec_ref_known(v_t_373_, 1);
v___x_389_ = lean_apply_1(v_param_378_, v_a_388_);
return v___x_389_;
}
default: 
{
lean_object* v_a_390_; lean_object* v___x_391_; 
lean_dec(v_param_378_);
lean_dec(v_imax_377_);
lean_dec(v_max_376_);
lean_dec(v_succ_375_);
v_a_390_ = lean_ctor_get(v_t_373_, 0);
lean_inc(v_a_390_);
lean_dec_ref_known(v_t_373_, 1);
v___x_391_ = lean_apply_1(v_mvar_379_, v_a_390_);
return v___x_391_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_casesOn___override___redArg___boxed(lean_object* v_t_392_, lean_object* v_zero_393_, lean_object* v_succ_394_, lean_object* v_max_395_, lean_object* v_imax_396_, lean_object* v_param_397_, lean_object* v_mvar_398_){
_start:
{
lean_object* v_res_399_; 
v_res_399_ = l_Lean_Level_casesOn___override___redArg(v_t_392_, v_zero_393_, v_succ_394_, v_max_395_, v_imax_396_, v_param_397_, v_mvar_398_);
lean_dec(v_zero_393_);
return v_res_399_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_casesOn___override(lean_object* v_motive_400_, lean_object* v_t_401_, lean_object* v_zero_402_, lean_object* v_succ_403_, lean_object* v_max_404_, lean_object* v_imax_405_, lean_object* v_param_406_, lean_object* v_mvar_407_){
_start:
{
switch(lean_obj_tag(v_t_401_))
{
case 0:
{
lean_dec(v_mvar_407_);
lean_dec(v_param_406_);
lean_dec(v_imax_405_);
lean_dec(v_max_404_);
lean_dec(v_succ_403_);
lean_inc(v_zero_402_);
return v_zero_402_;
}
case 1:
{
lean_object* v_a_408_; lean_object* v___x_409_; 
lean_dec(v_mvar_407_);
lean_dec(v_param_406_);
lean_dec(v_imax_405_);
lean_dec(v_max_404_);
v_a_408_ = lean_ctor_get(v_t_401_, 0);
lean_inc(v_a_408_);
lean_dec_ref_known(v_t_401_, 1);
v___x_409_ = lean_apply_1(v_succ_403_, v_a_408_);
return v___x_409_;
}
case 2:
{
lean_object* v_a_410_; lean_object* v_a_411_; lean_object* v___x_412_; 
lean_dec(v_mvar_407_);
lean_dec(v_param_406_);
lean_dec(v_imax_405_);
lean_dec(v_succ_403_);
v_a_410_ = lean_ctor_get(v_t_401_, 0);
lean_inc(v_a_410_);
v_a_411_ = lean_ctor_get(v_t_401_, 1);
lean_inc(v_a_411_);
lean_dec_ref_known(v_t_401_, 2);
v___x_412_ = lean_apply_2(v_max_404_, v_a_410_, v_a_411_);
return v___x_412_;
}
case 3:
{
lean_object* v_a_413_; lean_object* v_a_414_; lean_object* v___x_415_; 
lean_dec(v_mvar_407_);
lean_dec(v_param_406_);
lean_dec(v_max_404_);
lean_dec(v_succ_403_);
v_a_413_ = lean_ctor_get(v_t_401_, 0);
lean_inc(v_a_413_);
v_a_414_ = lean_ctor_get(v_t_401_, 1);
lean_inc(v_a_414_);
lean_dec_ref_known(v_t_401_, 2);
v___x_415_ = lean_apply_2(v_imax_405_, v_a_413_, v_a_414_);
return v___x_415_;
}
case 4:
{
lean_object* v_a_416_; lean_object* v___x_417_; 
lean_dec(v_mvar_407_);
lean_dec(v_imax_405_);
lean_dec(v_max_404_);
lean_dec(v_succ_403_);
v_a_416_ = lean_ctor_get(v_t_401_, 0);
lean_inc(v_a_416_);
lean_dec_ref_known(v_t_401_, 1);
v___x_417_ = lean_apply_1(v_param_406_, v_a_416_);
return v___x_417_;
}
default: 
{
lean_object* v_a_418_; lean_object* v___x_419_; 
lean_dec(v_param_406_);
lean_dec(v_imax_405_);
lean_dec(v_max_404_);
lean_dec(v_succ_403_);
v_a_418_ = lean_ctor_get(v_t_401_, 0);
lean_inc(v_a_418_);
lean_dec_ref_known(v_t_401_, 1);
v___x_419_ = lean_apply_1(v_mvar_407_, v_a_418_);
return v___x_419_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_casesOn___override___boxed(lean_object* v_motive_420_, lean_object* v_t_421_, lean_object* v_zero_422_, lean_object* v_succ_423_, lean_object* v_max_424_, lean_object* v_imax_425_, lean_object* v_param_426_, lean_object* v_mvar_427_){
_start:
{
lean_object* v_res_428_; 
v_res_428_ = l_Lean_Level_casesOn___override(v_motive_420_, v_t_421_, v_zero_422_, v_succ_423_, v_max_424_, v_imax_425_, v_param_426_, v_mvar_427_);
lean_dec(v_zero_422_);
return v_res_428_;
}
}
static lean_object* _init_l_Lean_Level_zero___override(void){
_start:
{
lean_object* v___x_429_; 
v___x_429_ = lean_box(0);
return v___x_429_;
}
}
static uint64_t _init_l_Lean_Level_data___override___closed__0(void){
_start:
{
uint8_t v___x_430_; lean_object* v___x_431_; uint64_t v___x_432_; uint64_t v___x_433_; 
v___x_430_ = 0;
v___x_431_ = lean_unsigned_to_nat(0u);
v___x_432_ = 2221ULL;
v___x_433_ = lean_level_mk_data(v___x_432_, v___x_431_, v___x_430_, v___x_430_);
return v___x_433_;
}
}
LEAN_EXPORT uint64_t l_Lean_Level_data___override(lean_object* v_x_434_){
_start:
{
switch(lean_obj_tag(v_x_434_))
{
case 0:
{
uint64_t v___x_435_; 
v___x_435_ = lean_uint64_once(&l_Lean_Level_data___override___closed__0, &l_Lean_Level_data___override___closed__0_once, _init_l_Lean_Level_data___override___closed__0);
return v___x_435_;
}
case 2:
{
uint64_t v_data_436_; 
v_data_436_ = lean_ctor_get_uint64(v_x_434_, sizeof(void*)*2);
return v_data_436_;
}
case 3:
{
uint64_t v_data_437_; 
v_data_437_ = lean_ctor_get_uint64(v_x_434_, sizeof(void*)*2);
return v_data_437_;
}
default: 
{
uint64_t v_data_438_; 
v_data_438_ = lean_ctor_get_uint64(v_x_434_, sizeof(void*)*1);
return v_data_438_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_data___override___boxed(lean_object* v_x_439_){
_start:
{
uint64_t v_res_440_; lean_object* v_r_441_; 
v_res_440_ = l_Lean_Level_data___override(v_x_439_);
lean_dec(v_x_439_);
v_r_441_ = lean_box_uint64(v_res_440_);
return v_r_441_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_succ___override(lean_object* v_a_442_){
_start:
{
uint64_t v___x_443_; uint64_t v___x_444_; uint64_t v___x_445_; uint64_t v___x_446_; uint32_t v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; uint8_t v___x_451_; uint8_t v___x_452_; uint64_t v___x_453_; lean_object* v___x_454_; 
v___x_443_ = 2243ULL;
v___x_444_ = l_Lean_Level_data___override(v_a_442_);
v___x_445_ = l_Lean_Level_Data_hash(v___x_444_);
v___x_446_ = lean_uint64_mix_hash(v___x_443_, v___x_445_);
v___x_447_ = l_Lean_Level_Data_depth(v___x_444_);
v___x_448_ = lean_uint32_to_nat(v___x_447_);
v___x_449_ = lean_unsigned_to_nat(1u);
v___x_450_ = lean_nat_add(v___x_448_, v___x_449_);
lean_dec(v___x_448_);
v___x_451_ = l_Lean_Level_Data_hasMVar(v___x_444_);
v___x_452_ = l_Lean_Level_Data_hasParam(v___x_444_);
v___x_453_ = lean_level_mk_data(v___x_446_, v___x_450_, v___x_451_, v___x_452_);
v___x_454_ = lean_alloc_ctor(1, 1, 8);
lean_ctor_set(v___x_454_, 0, v_a_442_);
lean_ctor_set_uint64(v___x_454_, sizeof(void*)*1, v___x_453_);
return v___x_454_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_max___override(lean_object* v_a_455_, lean_object* v_a_456_){
_start:
{
uint64_t v___x_457_; uint64_t v___x_458_; uint64_t v___x_459_; uint64_t v___x_460_; uint64_t v___x_461_; uint64_t v___x_462_; uint64_t v___x_463_; uint8_t v___y_465_; lean_object* v___y_466_; uint8_t v___y_467_; lean_object* v___y_471_; uint8_t v___y_472_; lean_object* v___y_476_; uint32_t v___x_481_; lean_object* v___x_482_; uint32_t v___x_483_; lean_object* v___x_484_; uint8_t v___x_485_; 
v___x_457_ = 2251ULL;
v___x_458_ = l_Lean_Level_data___override(v_a_455_);
v___x_459_ = l_Lean_Level_Data_hash(v___x_458_);
v___x_460_ = l_Lean_Level_data___override(v_a_456_);
v___x_461_ = l_Lean_Level_Data_hash(v___x_460_);
v___x_462_ = lean_uint64_mix_hash(v___x_459_, v___x_461_);
v___x_463_ = lean_uint64_mix_hash(v___x_457_, v___x_462_);
v___x_481_ = l_Lean_Level_Data_depth(v___x_458_);
v___x_482_ = lean_uint32_to_nat(v___x_481_);
v___x_483_ = l_Lean_Level_Data_depth(v___x_460_);
v___x_484_ = lean_uint32_to_nat(v___x_483_);
v___x_485_ = lean_nat_dec_le(v___x_482_, v___x_484_);
if (v___x_485_ == 0)
{
lean_dec(v___x_484_);
v___y_476_ = v___x_482_;
goto v___jp_475_;
}
else
{
lean_dec(v___x_482_);
v___y_476_ = v___x_484_;
goto v___jp_475_;
}
v___jp_464_:
{
uint64_t v___x_468_; lean_object* v___x_469_; 
v___x_468_ = lean_level_mk_data(v___x_463_, v___y_466_, v___y_465_, v___y_467_);
v___x_469_ = lean_alloc_ctor(2, 2, 8);
lean_ctor_set(v___x_469_, 0, v_a_455_);
lean_ctor_set(v___x_469_, 1, v_a_456_);
lean_ctor_set_uint64(v___x_469_, sizeof(void*)*2, v___x_468_);
return v___x_469_;
}
v___jp_470_:
{
uint8_t v___x_473_; 
v___x_473_ = l_Lean_Level_Data_hasParam(v___x_458_);
if (v___x_473_ == 0)
{
uint8_t v___x_474_; 
v___x_474_ = l_Lean_Level_Data_hasParam(v___x_460_);
v___y_465_ = v___y_472_;
v___y_466_ = v___y_471_;
v___y_467_ = v___x_474_;
goto v___jp_464_;
}
else
{
v___y_465_ = v___y_472_;
v___y_466_ = v___y_471_;
v___y_467_ = v___x_473_;
goto v___jp_464_;
}
}
v___jp_475_:
{
lean_object* v___x_477_; lean_object* v___x_478_; uint8_t v___x_479_; 
v___x_477_ = lean_unsigned_to_nat(1u);
v___x_478_ = lean_nat_add(v___y_476_, v___x_477_);
lean_dec(v___y_476_);
v___x_479_ = l_Lean_Level_Data_hasMVar(v___x_458_);
if (v___x_479_ == 0)
{
uint8_t v___x_480_; 
v___x_480_ = l_Lean_Level_Data_hasMVar(v___x_460_);
v___y_471_ = v___x_478_;
v___y_472_ = v___x_480_;
goto v___jp_470_;
}
else
{
v___y_471_ = v___x_478_;
v___y_472_ = v___x_479_;
goto v___jp_470_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_imax___override(lean_object* v_a_486_, lean_object* v_a_487_){
_start:
{
uint64_t v___x_488_; uint64_t v___x_489_; uint64_t v___x_490_; uint64_t v___x_491_; uint64_t v___x_492_; uint64_t v___x_493_; uint64_t v___x_494_; uint8_t v___y_496_; lean_object* v___y_497_; uint8_t v___y_498_; lean_object* v___y_502_; uint8_t v___y_503_; lean_object* v___y_507_; uint32_t v___x_512_; lean_object* v___x_513_; uint32_t v___x_514_; lean_object* v___x_515_; uint8_t v___x_516_; 
v___x_488_ = 2267ULL;
v___x_489_ = l_Lean_Level_data___override(v_a_486_);
v___x_490_ = l_Lean_Level_Data_hash(v___x_489_);
v___x_491_ = l_Lean_Level_data___override(v_a_487_);
v___x_492_ = l_Lean_Level_Data_hash(v___x_491_);
v___x_493_ = lean_uint64_mix_hash(v___x_490_, v___x_492_);
v___x_494_ = lean_uint64_mix_hash(v___x_488_, v___x_493_);
v___x_512_ = l_Lean_Level_Data_depth(v___x_489_);
v___x_513_ = lean_uint32_to_nat(v___x_512_);
v___x_514_ = l_Lean_Level_Data_depth(v___x_491_);
v___x_515_ = lean_uint32_to_nat(v___x_514_);
v___x_516_ = lean_nat_dec_le(v___x_513_, v___x_515_);
if (v___x_516_ == 0)
{
lean_dec(v___x_515_);
v___y_507_ = v___x_513_;
goto v___jp_506_;
}
else
{
lean_dec(v___x_513_);
v___y_507_ = v___x_515_;
goto v___jp_506_;
}
v___jp_495_:
{
uint64_t v___x_499_; lean_object* v___x_500_; 
v___x_499_ = lean_level_mk_data(v___x_494_, v___y_497_, v___y_496_, v___y_498_);
v___x_500_ = lean_alloc_ctor(3, 2, 8);
lean_ctor_set(v___x_500_, 0, v_a_486_);
lean_ctor_set(v___x_500_, 1, v_a_487_);
lean_ctor_set_uint64(v___x_500_, sizeof(void*)*2, v___x_499_);
return v___x_500_;
}
v___jp_501_:
{
uint8_t v___x_504_; 
v___x_504_ = l_Lean_Level_Data_hasParam(v___x_489_);
if (v___x_504_ == 0)
{
uint8_t v___x_505_; 
v___x_505_ = l_Lean_Level_Data_hasParam(v___x_491_);
v___y_496_ = v___y_503_;
v___y_497_ = v___y_502_;
v___y_498_ = v___x_505_;
goto v___jp_495_;
}
else
{
v___y_496_ = v___y_503_;
v___y_497_ = v___y_502_;
v___y_498_ = v___x_504_;
goto v___jp_495_;
}
}
v___jp_506_:
{
lean_object* v___x_508_; lean_object* v___x_509_; uint8_t v___x_510_; 
v___x_508_ = lean_unsigned_to_nat(1u);
v___x_509_ = lean_nat_add(v___y_507_, v___x_508_);
lean_dec(v___y_507_);
v___x_510_ = l_Lean_Level_Data_hasMVar(v___x_489_);
if (v___x_510_ == 0)
{
uint8_t v___x_511_; 
v___x_511_ = l_Lean_Level_Data_hasMVar(v___x_491_);
v___y_502_ = v___x_509_;
v___y_503_ = v___x_511_;
goto v___jp_501_;
}
else
{
v___y_502_ = v___x_509_;
v___y_503_ = v___x_510_;
goto v___jp_501_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_param___override(lean_object* v_a_517_){
_start:
{
uint64_t v___x_518_; uint64_t v___y_520_; 
v___x_518_ = 2239ULL;
if (lean_obj_tag(v_a_517_) == 0)
{
uint64_t v___x_527_; 
v___x_527_ = 1723ULL;
v___y_520_ = v___x_527_;
goto v___jp_519_;
}
else
{
uint64_t v_hash_528_; 
v_hash_528_ = lean_ctor_get_uint64(v_a_517_, sizeof(void*)*2);
v___y_520_ = v_hash_528_;
goto v___jp_519_;
}
v___jp_519_:
{
uint64_t v___x_521_; lean_object* v___x_522_; uint8_t v___x_523_; uint8_t v___x_524_; uint64_t v___x_525_; lean_object* v___x_526_; 
v___x_521_ = lean_uint64_mix_hash(v___x_518_, v___y_520_);
v___x_522_ = lean_unsigned_to_nat(0u);
v___x_523_ = 0;
v___x_524_ = 1;
v___x_525_ = lean_level_mk_data(v___x_521_, v___x_522_, v___x_523_, v___x_524_);
v___x_526_ = lean_alloc_ctor(4, 1, 8);
lean_ctor_set(v___x_526_, 0, v_a_517_);
lean_ctor_set_uint64(v___x_526_, sizeof(void*)*1, v___x_525_);
return v___x_526_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_mvar___override(lean_object* v_a_529_){
_start:
{
uint64_t v___x_530_; uint64_t v___x_531_; uint64_t v___x_532_; lean_object* v___x_533_; uint8_t v___x_534_; uint8_t v___x_535_; uint64_t v___x_536_; lean_object* v___x_537_; 
v___x_530_ = 2237ULL;
v___x_531_ = l_Lean_instHashableLevelMVarId_hash(v_a_529_);
v___x_532_ = lean_uint64_mix_hash(v___x_530_, v___x_531_);
v___x_533_ = lean_unsigned_to_nat(0u);
v___x_534_ = 1;
v___x_535_ = 0;
v___x_536_ = lean_level_mk_data(v___x_532_, v___x_533_, v___x_534_, v___x_535_);
v___x_537_ = lean_alloc_ctor(5, 1, 8);
lean_ctor_set(v___x_537_, 0, v_a_529_);
lean_ctor_set_uint64(v___x_537_, sizeof(void*)*1, v___x_536_);
return v___x_537_;
}
}
static lean_object* _init_l_Lean_instInhabitedLevel_default(void){
_start:
{
lean_object* v___x_538_; 
v___x_538_ = lean_box(0);
return v___x_538_;
}
}
static lean_object* _init_l_Lean_instInhabitedLevel(void){
_start:
{
lean_object* v___x_539_; 
v___x_539_ = lean_box(0);
return v___x_539_;
}
}
static lean_object* _init_l_Lean_instReprLevel_repr___closed__2(void){
_start:
{
lean_object* v___x_543_; lean_object* v___x_544_; 
v___x_543_ = lean_unsigned_to_nat(2u);
v___x_544_ = lean_nat_to_int(v___x_543_);
return v___x_544_;
}
}
static lean_object* _init_l_Lean_instReprLevel_repr___closed__3(void){
_start:
{
lean_object* v___x_545_; lean_object* v___x_546_; 
v___x_545_ = lean_unsigned_to_nat(1u);
v___x_546_ = lean_nat_to_int(v___x_545_);
return v___x_546_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprLevel_repr(lean_object* v_x_577_, lean_object* v_prec_578_){
_start:
{
lean_object* v___y_580_; 
switch(lean_obj_tag(v_x_577_))
{
case 0:
{
lean_object* v___x_586_; uint8_t v___x_587_; 
v___x_586_ = lean_unsigned_to_nat(1024u);
v___x_587_ = lean_nat_dec_le(v___x_586_, v_prec_578_);
if (v___x_587_ == 0)
{
lean_object* v___x_588_; 
v___x_588_ = lean_obj_once(&l_Lean_instReprLevel_repr___closed__2, &l_Lean_instReprLevel_repr___closed__2_once, _init_l_Lean_instReprLevel_repr___closed__2);
v___y_580_ = v___x_588_;
goto v___jp_579_;
}
else
{
lean_object* v___x_589_; 
v___x_589_ = lean_obj_once(&l_Lean_instReprLevel_repr___closed__3, &l_Lean_instReprLevel_repr___closed__3_once, _init_l_Lean_instReprLevel_repr___closed__3);
v___y_580_ = v___x_589_;
goto v___jp_579_;
}
}
case 1:
{
lean_object* v_a_590_; lean_object* v___x_591_; lean_object* v___y_593_; uint8_t v___x_601_; 
v_a_590_ = lean_ctor_get(v_x_577_, 0);
lean_inc(v_a_590_);
lean_dec_ref_known(v_x_577_, 1);
v___x_591_ = lean_unsigned_to_nat(1024u);
v___x_601_ = lean_nat_dec_le(v___x_591_, v_prec_578_);
if (v___x_601_ == 0)
{
lean_object* v___x_602_; 
v___x_602_ = lean_obj_once(&l_Lean_instReprLevel_repr___closed__2, &l_Lean_instReprLevel_repr___closed__2_once, _init_l_Lean_instReprLevel_repr___closed__2);
v___y_593_ = v___x_602_;
goto v___jp_592_;
}
else
{
lean_object* v___x_603_; 
v___x_603_ = lean_obj_once(&l_Lean_instReprLevel_repr___closed__3, &l_Lean_instReprLevel_repr___closed__3_once, _init_l_Lean_instReprLevel_repr___closed__3);
v___y_593_ = v___x_603_;
goto v___jp_592_;
}
v___jp_592_:
{
lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; uint8_t v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; 
v___x_594_ = ((lean_object*)(l_Lean_instReprLevel_repr___closed__6));
v___x_595_ = l_Lean_instReprLevel_repr(v_a_590_, v___x_591_);
v___x_596_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_596_, 0, v___x_594_);
lean_ctor_set(v___x_596_, 1, v___x_595_);
lean_inc(v___y_593_);
v___x_597_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_597_, 0, v___y_593_);
lean_ctor_set(v___x_597_, 1, v___x_596_);
v___x_598_ = 0;
v___x_599_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_599_, 0, v___x_597_);
lean_ctor_set_uint8(v___x_599_, sizeof(void*)*1, v___x_598_);
v___x_600_ = l_Repr_addAppParen(v___x_599_, v_prec_578_);
return v___x_600_;
}
}
case 2:
{
lean_object* v_a_604_; lean_object* v_a_605_; lean_object* v___x_606_; lean_object* v___y_608_; uint8_t v___x_620_; 
v_a_604_ = lean_ctor_get(v_x_577_, 0);
lean_inc(v_a_604_);
v_a_605_ = lean_ctor_get(v_x_577_, 1);
lean_inc(v_a_605_);
lean_dec_ref_known(v_x_577_, 2);
v___x_606_ = lean_unsigned_to_nat(1024u);
v___x_620_ = lean_nat_dec_le(v___x_606_, v_prec_578_);
if (v___x_620_ == 0)
{
lean_object* v___x_621_; 
v___x_621_ = lean_obj_once(&l_Lean_instReprLevel_repr___closed__2, &l_Lean_instReprLevel_repr___closed__2_once, _init_l_Lean_instReprLevel_repr___closed__2);
v___y_608_ = v___x_621_;
goto v___jp_607_;
}
else
{
lean_object* v___x_622_; 
v___x_622_ = lean_obj_once(&l_Lean_instReprLevel_repr___closed__3, &l_Lean_instReprLevel_repr___closed__3_once, _init_l_Lean_instReprLevel_repr___closed__3);
v___y_608_ = v___x_622_;
goto v___jp_607_;
}
v___jp_607_:
{
lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; uint8_t v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; 
v___x_609_ = lean_box(1);
v___x_610_ = ((lean_object*)(l_Lean_instReprLevel_repr___closed__9));
v___x_611_ = l_Lean_instReprLevel_repr(v_a_604_, v___x_606_);
v___x_612_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_612_, 0, v___x_610_);
lean_ctor_set(v___x_612_, 1, v___x_611_);
v___x_613_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_613_, 0, v___x_612_);
lean_ctor_set(v___x_613_, 1, v___x_609_);
v___x_614_ = l_Lean_instReprLevel_repr(v_a_605_, v___x_606_);
v___x_615_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_615_, 0, v___x_613_);
lean_ctor_set(v___x_615_, 1, v___x_614_);
lean_inc(v___y_608_);
v___x_616_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_616_, 0, v___y_608_);
lean_ctor_set(v___x_616_, 1, v___x_615_);
v___x_617_ = 0;
v___x_618_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_618_, 0, v___x_616_);
lean_ctor_set_uint8(v___x_618_, sizeof(void*)*1, v___x_617_);
v___x_619_ = l_Repr_addAppParen(v___x_618_, v_prec_578_);
return v___x_619_;
}
}
case 3:
{
lean_object* v_a_623_; lean_object* v_a_624_; lean_object* v___x_625_; lean_object* v___y_627_; uint8_t v___x_639_; 
v_a_623_ = lean_ctor_get(v_x_577_, 0);
lean_inc(v_a_623_);
v_a_624_ = lean_ctor_get(v_x_577_, 1);
lean_inc(v_a_624_);
lean_dec_ref_known(v_x_577_, 2);
v___x_625_ = lean_unsigned_to_nat(1024u);
v___x_639_ = lean_nat_dec_le(v___x_625_, v_prec_578_);
if (v___x_639_ == 0)
{
lean_object* v___x_640_; 
v___x_640_ = lean_obj_once(&l_Lean_instReprLevel_repr___closed__2, &l_Lean_instReprLevel_repr___closed__2_once, _init_l_Lean_instReprLevel_repr___closed__2);
v___y_627_ = v___x_640_;
goto v___jp_626_;
}
else
{
lean_object* v___x_641_; 
v___x_641_ = lean_obj_once(&l_Lean_instReprLevel_repr___closed__3, &l_Lean_instReprLevel_repr___closed__3_once, _init_l_Lean_instReprLevel_repr___closed__3);
v___y_627_ = v___x_641_;
goto v___jp_626_;
}
v___jp_626_:
{
lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; uint8_t v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; 
v___x_628_ = lean_box(1);
v___x_629_ = ((lean_object*)(l_Lean_instReprLevel_repr___closed__12));
v___x_630_ = l_Lean_instReprLevel_repr(v_a_623_, v___x_625_);
v___x_631_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_631_, 0, v___x_629_);
lean_ctor_set(v___x_631_, 1, v___x_630_);
v___x_632_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_632_, 0, v___x_631_);
lean_ctor_set(v___x_632_, 1, v___x_628_);
v___x_633_ = l_Lean_instReprLevel_repr(v_a_624_, v___x_625_);
v___x_634_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_634_, 0, v___x_632_);
lean_ctor_set(v___x_634_, 1, v___x_633_);
lean_inc(v___y_627_);
v___x_635_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_635_, 0, v___y_627_);
lean_ctor_set(v___x_635_, 1, v___x_634_);
v___x_636_ = 0;
v___x_637_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_637_, 0, v___x_635_);
lean_ctor_set_uint8(v___x_637_, sizeof(void*)*1, v___x_636_);
v___x_638_ = l_Repr_addAppParen(v___x_637_, v_prec_578_);
return v___x_638_;
}
}
case 4:
{
lean_object* v_a_642_; lean_object* v___y_644_; lean_object* v___x_653_; uint8_t v___x_654_; 
v_a_642_ = lean_ctor_get(v_x_577_, 0);
lean_inc(v_a_642_);
lean_dec_ref_known(v_x_577_, 1);
v___x_653_ = lean_unsigned_to_nat(1024u);
v___x_654_ = lean_nat_dec_le(v___x_653_, v_prec_578_);
if (v___x_654_ == 0)
{
lean_object* v___x_655_; 
v___x_655_ = lean_obj_once(&l_Lean_instReprLevel_repr___closed__2, &l_Lean_instReprLevel_repr___closed__2_once, _init_l_Lean_instReprLevel_repr___closed__2);
v___y_644_ = v___x_655_;
goto v___jp_643_;
}
else
{
lean_object* v___x_656_; 
v___x_656_ = lean_obj_once(&l_Lean_instReprLevel_repr___closed__3, &l_Lean_instReprLevel_repr___closed__3_once, _init_l_Lean_instReprLevel_repr___closed__3);
v___y_644_ = v___x_656_;
goto v___jp_643_;
}
v___jp_643_:
{
lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; uint8_t v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; 
v___x_645_ = ((lean_object*)(l_Lean_instReprLevel_repr___closed__15));
v___x_646_ = lean_unsigned_to_nat(1024u);
v___x_647_ = l_Lean_Name_reprPrec(v_a_642_, v___x_646_);
v___x_648_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_648_, 0, v___x_645_);
lean_ctor_set(v___x_648_, 1, v___x_647_);
lean_inc(v___y_644_);
v___x_649_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_649_, 0, v___y_644_);
lean_ctor_set(v___x_649_, 1, v___x_648_);
v___x_650_ = 0;
v___x_651_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_651_, 0, v___x_649_);
lean_ctor_set_uint8(v___x_651_, sizeof(void*)*1, v___x_650_);
v___x_652_ = l_Repr_addAppParen(v___x_651_, v_prec_578_);
return v___x_652_;
}
}
default: 
{
lean_object* v_a_657_; lean_object* v___y_659_; lean_object* v___x_668_; uint8_t v___x_669_; 
v_a_657_ = lean_ctor_get(v_x_577_, 0);
lean_inc(v_a_657_);
lean_dec_ref_known(v_x_577_, 1);
v___x_668_ = lean_unsigned_to_nat(1024u);
v___x_669_ = lean_nat_dec_le(v___x_668_, v_prec_578_);
if (v___x_669_ == 0)
{
lean_object* v___x_670_; 
v___x_670_ = lean_obj_once(&l_Lean_instReprLevel_repr___closed__2, &l_Lean_instReprLevel_repr___closed__2_once, _init_l_Lean_instReprLevel_repr___closed__2);
v___y_659_ = v___x_670_;
goto v___jp_658_;
}
else
{
lean_object* v___x_671_; 
v___x_671_ = lean_obj_once(&l_Lean_instReprLevel_repr___closed__3, &l_Lean_instReprLevel_repr___closed__3_once, _init_l_Lean_instReprLevel_repr___closed__3);
v___y_659_ = v___x_671_;
goto v___jp_658_;
}
v___jp_658_:
{
lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; uint8_t v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; 
v___x_660_ = ((lean_object*)(l_Lean_instReprLevel_repr___closed__18));
v___x_661_ = lean_unsigned_to_nat(1024u);
v___x_662_ = l_Lean_Name_reprPrec(v_a_657_, v___x_661_);
v___x_663_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_663_, 0, v___x_660_);
lean_ctor_set(v___x_663_, 1, v___x_662_);
lean_inc(v___y_659_);
v___x_664_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_664_, 0, v___y_659_);
lean_ctor_set(v___x_664_, 1, v___x_663_);
v___x_665_ = 0;
v___x_666_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_666_, 0, v___x_664_);
lean_ctor_set_uint8(v___x_666_, sizeof(void*)*1, v___x_665_);
v___x_667_ = l_Repr_addAppParen(v___x_666_, v_prec_578_);
return v___x_667_;
}
}
}
v___jp_579_:
{
lean_object* v___x_581_; lean_object* v___x_582_; uint8_t v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; 
v___x_581_ = ((lean_object*)(l_Lean_instReprLevel_repr___closed__1));
lean_inc(v___y_580_);
v___x_582_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_582_, 0, v___y_580_);
lean_ctor_set(v___x_582_, 1, v___x_581_);
v___x_583_ = 0;
v___x_584_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_584_, 0, v___x_582_);
lean_ctor_set_uint8(v___x_584_, sizeof(void*)*1, v___x_583_);
v___x_585_ = l_Repr_addAppParen(v___x_584_, v_prec_578_);
return v___x_585_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instReprLevel_repr___boxed(lean_object* v_x_672_, lean_object* v_prec_673_){
_start:
{
lean_object* v_res_674_; 
v_res_674_ = l_Lean_instReprLevel_repr(v_x_672_, v_prec_673_);
lean_dec(v_prec_673_);
return v_res_674_;
}
}
LEAN_EXPORT uint64_t l_Lean_Level_hash(lean_object* v_u_677_){
_start:
{
uint64_t v___x_678_; uint64_t v___x_679_; 
v___x_678_ = l_Lean_Level_data___override(v_u_677_);
v___x_679_ = l_Lean_Level_Data_hash(v___x_678_);
return v___x_679_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_hash___boxed(lean_object* v_u_680_){
_start:
{
uint64_t v_res_681_; lean_object* v_r_682_; 
v_res_681_ = l_Lean_Level_hash(v_u_680_);
lean_dec(v_u_680_);
v_r_682_ = lean_box_uint64(v_res_681_);
return v_r_682_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_depth(lean_object* v_u_685_){
_start:
{
uint64_t v___x_686_; uint32_t v___x_687_; lean_object* v___x_688_; 
v___x_686_ = l_Lean_Level_data___override(v_u_685_);
v___x_687_ = l_Lean_Level_Data_depth(v___x_686_);
v___x_688_ = lean_uint32_to_nat(v___x_687_);
return v___x_688_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_depth___boxed(lean_object* v_u_689_){
_start:
{
lean_object* v_res_690_; 
v_res_690_ = l_Lean_Level_depth(v_u_689_);
lean_dec(v_u_689_);
return v_res_690_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_hasMVar(lean_object* v_u_691_){
_start:
{
uint64_t v___x_692_; uint8_t v___x_693_; 
v___x_692_ = l_Lean_Level_data___override(v_u_691_);
v___x_693_ = l_Lean_Level_Data_hasMVar(v___x_692_);
return v___x_693_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_hasMVar___boxed(lean_object* v_u_694_){
_start:
{
uint8_t v_res_695_; lean_object* v_r_696_; 
v_res_695_ = l_Lean_Level_hasMVar(v_u_694_);
lean_dec(v_u_694_);
v_r_696_ = lean_box(v_res_695_);
return v_r_696_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_hasParam(lean_object* v_u_697_){
_start:
{
uint64_t v___x_698_; uint8_t v___x_699_; 
v___x_698_ = l_Lean_Level_data___override(v_u_697_);
v___x_699_ = l_Lean_Level_Data_hasParam(v___x_698_);
return v___x_699_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_hasParam___boxed(lean_object* v_u_700_){
_start:
{
uint8_t v_res_701_; lean_object* v_r_702_; 
v_res_701_ = l_Lean_Level_hasParam(v_u_700_);
lean_dec(v_u_700_);
v_r_702_ = lean_box(v_res_701_);
return v_r_702_;
}
}
LEAN_EXPORT uint32_t lean_level_hash(lean_object* v_u_703_){
_start:
{
uint64_t v___x_704_; uint32_t v___x_705_; 
v___x_704_ = l_Lean_Level_hash(v_u_703_);
lean_dec(v_u_703_);
v___x_705_ = lean_uint64_to_uint32(v___x_704_);
return v___x_705_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_hashEx___boxed(lean_object* v_u_706_){
_start:
{
uint32_t v_res_707_; lean_object* v_r_708_; 
v_res_707_ = lean_level_hash(v_u_706_);
v_r_708_ = lean_box_uint32(v_res_707_);
return v_r_708_;
}
}
LEAN_EXPORT uint8_t lean_level_has_mvar(lean_object* v_u_709_){
_start:
{
uint8_t v___x_710_; 
v___x_710_ = l_Lean_Level_hasMVar(v_u_709_);
lean_dec(v_u_709_);
return v___x_710_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_hasMVarEx___boxed(lean_object* v_u_711_){
_start:
{
uint8_t v_res_712_; lean_object* v_r_713_; 
v_res_712_ = lean_level_has_mvar(v_u_711_);
v_r_713_ = lean_box(v_res_712_);
return v_r_713_;
}
}
LEAN_EXPORT uint8_t lean_level_has_param(lean_object* v_u_714_){
_start:
{
uint8_t v___x_715_; 
v___x_715_ = l_Lean_Level_hasParam(v_u_714_);
lean_dec(v_u_714_);
return v___x_715_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_hasParamEx___boxed(lean_object* v_u_716_){
_start:
{
uint8_t v_res_717_; lean_object* v_r_718_; 
v_res_717_ = lean_level_has_param(v_u_716_);
v_r_718_ = lean_box(v_res_717_);
return v_r_718_;
}
}
LEAN_EXPORT uint32_t lean_level_depth(lean_object* v_u_719_){
_start:
{
uint64_t v___x_720_; uint32_t v___x_721_; 
v___x_720_ = l_Lean_Level_data___override(v_u_719_);
lean_dec(v_u_719_);
v___x_721_ = l_Lean_Level_Data_depth(v___x_720_);
return v___x_721_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_depthEx___boxed(lean_object* v_u_722_){
_start:
{
uint32_t v_res_723_; lean_object* v_r_724_; 
v_res_723_ = lean_level_depth(v_u_722_);
v_r_724_ = lean_box_uint32(v_res_723_);
return v_r_724_;
}
}
static lean_object* _init_l_Lean_levelZero(void){
_start:
{
lean_object* v___x_725_; 
v___x_725_ = lean_box(0);
return v___x_725_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLevelMVar(lean_object* v_mvarId_726_){
_start:
{
lean_object* v___x_727_; 
v___x_727_ = l_Lean_Level_mvar___override(v_mvarId_726_);
return v___x_727_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLevelParam(lean_object* v_name_728_){
_start:
{
lean_object* v___x_729_; 
v___x_729_ = l_Lean_Level_param___override(v_name_728_);
return v___x_729_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLevelSucc(lean_object* v_u_730_){
_start:
{
lean_object* v___x_731_; 
v___x_731_ = l_Lean_Level_succ___override(v_u_730_);
return v___x_731_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLevelMax(lean_object* v_u_732_, lean_object* v_v_733_){
_start:
{
lean_object* v___x_734_; 
v___x_734_ = l_Lean_Level_max___override(v_u_732_, v_v_733_);
return v___x_734_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLevelIMax(lean_object* v_u_735_, lean_object* v_v_736_){
_start:
{
lean_object* v___x_737_; 
v___x_737_ = l_Lean_Level_imax___override(v_u_735_, v_v_736_);
return v___x_737_;
}
}
static lean_object* _init_l_Lean_Level_one___closed__0(void){
_start:
{
lean_object* v___x_738_; lean_object* v___x_739_; 
v___x_738_ = lean_box(0);
v___x_739_ = l_Lean_Level_succ___override(v___x_738_);
return v___x_739_;
}
}
static lean_object* _init_l_Lean_Level_one(void){
_start:
{
lean_object* v___x_740_; 
v___x_740_ = lean_obj_once(&l_Lean_Level_one___closed__0, &l_Lean_Level_one___closed__0_once, _init_l_Lean_Level_one___closed__0);
return v___x_740_;
}
}
static lean_object* _init_l_Lean_levelOne(void){
_start:
{
lean_object* v___x_741_; 
v___x_741_ = lean_obj_once(&l_Lean_Level_one___closed__0, &l_Lean_Level_one___closed__0_once, _init_l_Lean_Level_one___closed__0);
return v___x_741_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLevelZeroEx___redArg(){
_start:
{
lean_object* v___x_743_; 
v___x_743_ = lean_box(0);
return v___x_743_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLevelZeroEx___redArg___boxed(lean_object* v___dummy_744_){
_start:
{
lean_object* v_res_745_; 
v_res_745_ = l_Lean_mkLevelZeroEx___redArg();
return v_res_745_;
}
}
LEAN_EXPORT lean_object* lean_level_mk_zero(lean_object* v_x_746_){
_start:
{
lean_object* v___x_747_; 
v___x_747_ = lean_box(0);
return v___x_747_;
}
}
LEAN_EXPORT lean_object* lean_level_mk_succ(lean_object* v_u_748_){
_start:
{
lean_object* v___x_749_; 
v___x_749_ = l_Lean_Level_succ___override(v_u_748_);
return v___x_749_;
}
}
LEAN_EXPORT lean_object* lean_level_mk_param(lean_object* v_name_750_){
_start:
{
lean_object* v___x_751_; 
v___x_751_ = l_Lean_Level_param___override(v_name_750_);
return v___x_751_;
}
}
LEAN_EXPORT lean_object* lean_level_mk_max(lean_object* v_u_752_, lean_object* v_v_753_){
_start:
{
lean_object* v___x_754_; 
v___x_754_ = l_Lean_Level_max___override(v_u_752_, v_v_753_);
return v___x_754_;
}
}
LEAN_EXPORT lean_object* lean_level_mk_imax(lean_object* v_u_755_, lean_object* v_v_756_){
_start:
{
lean_object* v___x_757_; 
v___x_757_ = l_Lean_Level_imax___override(v_u_755_, v_v_756_);
return v___x_757_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_isZero(lean_object* v_x_758_){
_start:
{
if (lean_obj_tag(v_x_758_) == 0)
{
uint8_t v___x_759_; 
v___x_759_ = 1;
return v___x_759_;
}
else
{
uint8_t v___x_760_; 
v___x_760_ = 0;
return v___x_760_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_isZero___boxed(lean_object* v_x_761_){
_start:
{
uint8_t v_res_762_; lean_object* v_r_763_; 
v_res_762_ = l_Lean_Level_isZero(v_x_761_);
lean_dec(v_x_761_);
v_r_763_ = lean_box(v_res_762_);
return v_r_763_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_isSucc(lean_object* v_x_764_){
_start:
{
if (lean_obj_tag(v_x_764_) == 1)
{
uint8_t v___x_765_; 
v___x_765_ = 1;
return v___x_765_;
}
else
{
uint8_t v___x_766_; 
v___x_766_ = 0;
return v___x_766_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_isSucc___boxed(lean_object* v_x_767_){
_start:
{
uint8_t v_res_768_; lean_object* v_r_769_; 
v_res_768_ = l_Lean_Level_isSucc(v_x_767_);
lean_dec(v_x_767_);
v_r_769_ = lean_box(v_res_768_);
return v_r_769_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_isMax(lean_object* v_x_770_){
_start:
{
if (lean_obj_tag(v_x_770_) == 2)
{
uint8_t v___x_771_; 
v___x_771_ = 1;
return v___x_771_;
}
else
{
uint8_t v___x_772_; 
v___x_772_ = 0;
return v___x_772_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_isMax___boxed(lean_object* v_x_773_){
_start:
{
uint8_t v_res_774_; lean_object* v_r_775_; 
v_res_774_ = l_Lean_Level_isMax(v_x_773_);
lean_dec(v_x_773_);
v_r_775_ = lean_box(v_res_774_);
return v_r_775_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_isIMax(lean_object* v_x_776_){
_start:
{
if (lean_obj_tag(v_x_776_) == 3)
{
uint8_t v___x_777_; 
v___x_777_ = 1;
return v___x_777_;
}
else
{
uint8_t v___x_778_; 
v___x_778_ = 0;
return v___x_778_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_isIMax___boxed(lean_object* v_x_779_){
_start:
{
uint8_t v_res_780_; lean_object* v_r_781_; 
v_res_780_ = l_Lean_Level_isIMax(v_x_779_);
lean_dec(v_x_779_);
v_r_781_ = lean_box(v_res_780_);
return v_r_781_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_isMaxIMax(lean_object* v_x_782_){
_start:
{
switch(lean_obj_tag(v_x_782_))
{
case 2:
{
uint8_t v___x_783_; 
v___x_783_ = 1;
return v___x_783_;
}
case 3:
{
uint8_t v___x_784_; 
v___x_784_ = 1;
return v___x_784_;
}
default: 
{
uint8_t v___x_785_; 
v___x_785_ = 0;
return v___x_785_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_isMaxIMax___boxed(lean_object* v_x_786_){
_start:
{
uint8_t v_res_787_; lean_object* v_r_788_; 
v_res_787_ = l_Lean_Level_isMaxIMax(v_x_786_);
lean_dec(v_x_786_);
v_r_788_ = lean_box(v_res_787_);
return v_r_788_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_isParam(lean_object* v_x_789_){
_start:
{
if (lean_obj_tag(v_x_789_) == 4)
{
uint8_t v___x_790_; 
v___x_790_ = 1;
return v___x_790_;
}
else
{
uint8_t v___x_791_; 
v___x_791_ = 0;
return v___x_791_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_isParam___boxed(lean_object* v_x_792_){
_start:
{
uint8_t v_res_793_; lean_object* v_r_794_; 
v_res_793_ = l_Lean_Level_isParam(v_x_792_);
lean_dec(v_x_792_);
v_r_794_ = lean_box(v_res_793_);
return v_r_794_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_isMVar(lean_object* v_x_795_){
_start:
{
if (lean_obj_tag(v_x_795_) == 5)
{
uint8_t v___x_796_; 
v___x_796_ = 1;
return v___x_796_;
}
else
{
uint8_t v___x_797_; 
v___x_797_ = 0;
return v___x_797_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_isMVar___boxed(lean_object* v_x_798_){
_start:
{
uint8_t v_res_799_; lean_object* v_r_800_; 
v_res_799_ = l_Lean_Level_isMVar(v_x_798_);
lean_dec(v_x_798_);
v_r_800_ = lean_box(v_res_799_);
return v_r_800_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Level_mvarId_x21_spec__0(lean_object* v_msg_801_){
_start:
{
lean_object* v___x_802_; lean_object* v___x_803_; 
v___x_802_ = lean_box(0);
v___x_803_ = lean_panic_fn_borrowed(v___x_802_, v_msg_801_);
return v___x_803_;
}
}
static lean_object* _init_l_Lean_Level_mvarId_x21___closed__3(void){
_start:
{
lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; 
v___x_807_ = ((lean_object*)(l_Lean_Level_mvarId_x21___closed__2));
v___x_808_ = lean_unsigned_to_nat(19u);
v___x_809_ = lean_unsigned_to_nat(195u);
v___x_810_ = ((lean_object*)(l_Lean_Level_mvarId_x21___closed__1));
v___x_811_ = ((lean_object*)(l_Lean_Level_mvarId_x21___closed__0));
v___x_812_ = l_mkPanicMessageWithDecl(v___x_811_, v___x_810_, v___x_809_, v___x_808_, v___x_807_);
return v___x_812_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_mvarId_x21(lean_object* v_x_813_){
_start:
{
if (lean_obj_tag(v_x_813_) == 5)
{
lean_object* v_a_814_; 
v_a_814_ = lean_ctor_get(v_x_813_, 0);
lean_inc(v_a_814_);
return v_a_814_;
}
else
{
lean_object* v___x_815_; lean_object* v___x_816_; 
v___x_815_ = lean_obj_once(&l_Lean_Level_mvarId_x21___closed__3, &l_Lean_Level_mvarId_x21___closed__3_once, _init_l_Lean_Level_mvarId_x21___closed__3);
v___x_816_ = l_panic___at___00Lean_Level_mvarId_x21_spec__0(v___x_815_);
return v___x_816_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_mvarId_x21___boxed(lean_object* v_x_817_){
_start:
{
lean_object* v_res_818_; 
v_res_818_ = l_Lean_Level_mvarId_x21(v_x_817_);
lean_dec(v_x_817_);
return v_res_818_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_isNeverZero(lean_object* v_x_819_){
_start:
{
switch(lean_obj_tag(v_x_819_))
{
case 0:
{
uint8_t v___x_820_; 
v___x_820_ = 0;
return v___x_820_;
}
case 1:
{
uint8_t v___x_821_; 
v___x_821_ = 1;
return v___x_821_;
}
case 2:
{
lean_object* v_a_822_; lean_object* v_a_823_; uint8_t v___x_824_; 
v_a_822_ = lean_ctor_get(v_x_819_, 0);
v_a_823_ = lean_ctor_get(v_x_819_, 1);
v___x_824_ = l_Lean_Level_isNeverZero(v_a_822_);
if (v___x_824_ == 0)
{
v_x_819_ = v_a_823_;
goto _start;
}
else
{
return v___x_824_;
}
}
case 3:
{
lean_object* v_a_826_; 
v_a_826_ = lean_ctor_get(v_x_819_, 1);
v_x_819_ = v_a_826_;
goto _start;
}
default: 
{
uint8_t v___x_828_; 
v___x_828_ = 0;
return v___x_828_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_isNeverZero___boxed(lean_object* v_x_829_){
_start:
{
uint8_t v_res_830_; lean_object* v_r_831_; 
v_res_830_ = l_Lean_Level_isNeverZero(v_x_829_);
lean_dec(v_x_829_);
v_r_831_ = lean_box(v_res_830_);
return v_r_831_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_isAlwaysZero(lean_object* v_x_832_){
_start:
{
switch(lean_obj_tag(v_x_832_))
{
case 0:
{
uint8_t v___x_833_; 
v___x_833_ = 1;
return v___x_833_;
}
case 2:
{
lean_object* v_a_834_; lean_object* v_a_835_; uint8_t v___x_836_; 
v_a_834_ = lean_ctor_get(v_x_832_, 0);
v_a_835_ = lean_ctor_get(v_x_832_, 1);
v___x_836_ = l_Lean_Level_isAlwaysZero(v_a_834_);
if (v___x_836_ == 0)
{
return v___x_836_;
}
else
{
v_x_832_ = v_a_835_;
goto _start;
}
}
case 3:
{
lean_object* v_a_838_; 
v_a_838_ = lean_ctor_get(v_x_832_, 1);
v_x_832_ = v_a_838_;
goto _start;
}
default: 
{
uint8_t v___x_840_; 
v___x_840_ = 0;
return v___x_840_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_isAlwaysZero___boxed(lean_object* v_x_841_){
_start:
{
uint8_t v_res_842_; lean_object* v_r_843_; 
v_res_842_ = l_Lean_Level_isAlwaysZero(v_x_841_);
lean_dec(v_x_841_);
v_r_843_ = lean_box(v_res_842_);
return v_r_843_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_ofNat(lean_object* v_x_844_){
_start:
{
lean_object* v_zero_845_; uint8_t v_isZero_846_; 
v_zero_845_ = lean_unsigned_to_nat(0u);
v_isZero_846_ = lean_nat_dec_eq(v_x_844_, v_zero_845_);
if (v_isZero_846_ == 1)
{
lean_object* v___x_847_; 
v___x_847_ = lean_box(0);
return v___x_847_;
}
else
{
lean_object* v_one_848_; lean_object* v_n_849_; lean_object* v___x_850_; lean_object* v___x_851_; 
v_one_848_ = lean_unsigned_to_nat(1u);
v_n_849_ = lean_nat_sub(v_x_844_, v_one_848_);
v___x_850_ = l_Lean_Level_ofNat(v_n_849_);
lean_dec(v_n_849_);
v___x_851_ = l_Lean_Level_succ___override(v___x_850_);
return v___x_851_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_ofNat___boxed(lean_object* v_x_852_){
_start:
{
lean_object* v_res_853_; 
v_res_853_ = l_Lean_Level_ofNat(v_x_852_);
lean_dec(v_x_852_);
return v_res_853_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_instOfNat(lean_object* v_n_854_){
_start:
{
lean_object* v___x_855_; 
v___x_855_ = l_Lean_Level_ofNat(v_n_854_);
return v___x_855_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_instOfNat___boxed(lean_object* v_n_856_){
_start:
{
lean_object* v_res_857_; 
v_res_857_ = l_Lean_Level_instOfNat(v_n_856_);
lean_dec(v_n_856_);
return v_res_857_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_addOffsetAux(lean_object* v_x_858_, lean_object* v_x_859_){
_start:
{
lean_object* v_zero_860_; uint8_t v_isZero_861_; 
v_zero_860_ = lean_unsigned_to_nat(0u);
v_isZero_861_ = lean_nat_dec_eq(v_x_858_, v_zero_860_);
if (v_isZero_861_ == 1)
{
lean_dec(v_x_858_);
return v_x_859_;
}
else
{
lean_object* v_one_862_; lean_object* v_n_863_; lean_object* v___x_864_; 
v_one_862_ = lean_unsigned_to_nat(1u);
v_n_863_ = lean_nat_sub(v_x_858_, v_one_862_);
lean_dec(v_x_858_);
v___x_864_ = l_Lean_Level_succ___override(v_x_859_);
v_x_858_ = v_n_863_;
v_x_859_ = v___x_864_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_addOffset(lean_object* v_u_866_, lean_object* v_n_867_){
_start:
{
lean_object* v___x_868_; 
v___x_868_ = l_Lean_Level_addOffsetAux(v_n_867_, v_u_866_);
return v___x_868_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_isExplicit(lean_object* v_x_869_){
_start:
{
switch(lean_obj_tag(v_x_869_))
{
case 0:
{
uint8_t v___x_870_; 
v___x_870_ = 1;
return v___x_870_;
}
case 1:
{
lean_object* v_a_871_; uint8_t v___x_872_; 
v_a_871_ = lean_ctor_get(v_x_869_, 0);
v___x_872_ = l_Lean_Level_hasMVar(v_a_871_);
if (v___x_872_ == 0)
{
uint8_t v___x_873_; 
v___x_873_ = l_Lean_Level_hasParam(v_a_871_);
if (v___x_873_ == 0)
{
v_x_869_ = v_a_871_;
goto _start;
}
else
{
return v___x_872_;
}
}
else
{
uint8_t v___x_875_; 
v___x_875_ = 0;
return v___x_875_;
}
}
default: 
{
uint8_t v___x_876_; 
v___x_876_ = 0;
return v___x_876_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_isExplicit___boxed(lean_object* v_x_877_){
_start:
{
uint8_t v_res_878_; lean_object* v_r_879_; 
v_res_878_ = l_Lean_Level_isExplicit(v_x_877_);
lean_dec(v_x_877_);
v_r_879_ = lean_box(v_res_878_);
return v_r_879_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_getOffsetAux(lean_object* v_x_880_, lean_object* v_x_881_){
_start:
{
if (lean_obj_tag(v_x_880_) == 1)
{
lean_object* v_a_882_; lean_object* v___x_883_; lean_object* v___x_884_; 
v_a_882_ = lean_ctor_get(v_x_880_, 0);
v___x_883_ = lean_unsigned_to_nat(1u);
v___x_884_ = lean_nat_add(v_x_881_, v___x_883_);
lean_dec(v_x_881_);
v_x_880_ = v_a_882_;
v_x_881_ = v___x_884_;
goto _start;
}
else
{
return v_x_881_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_getOffsetAux___boxed(lean_object* v_x_886_, lean_object* v_x_887_){
_start:
{
lean_object* v_res_888_; 
v_res_888_ = l_Lean_Level_getOffsetAux(v_x_886_, v_x_887_);
lean_dec(v_x_886_);
return v_res_888_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_getOffset(lean_object* v_lvl_889_){
_start:
{
lean_object* v___x_890_; lean_object* v___x_891_; 
v___x_890_ = lean_unsigned_to_nat(0u);
v___x_891_ = l_Lean_Level_getOffsetAux(v_lvl_889_, v___x_890_);
return v___x_891_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_getOffset___boxed(lean_object* v_lvl_892_){
_start:
{
lean_object* v_res_893_; 
v_res_893_ = l_Lean_Level_getOffset(v_lvl_892_);
lean_dec(v_lvl_892_);
return v_res_893_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_getLevelOffset(lean_object* v_x_894_){
_start:
{
if (lean_obj_tag(v_x_894_) == 1)
{
lean_object* v_a_895_; 
v_a_895_ = lean_ctor_get(v_x_894_, 0);
v_x_894_ = v_a_895_;
goto _start;
}
else
{
lean_inc(v_x_894_);
return v_x_894_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_getLevelOffset___boxed(lean_object* v_x_897_){
_start:
{
lean_object* v_res_898_; 
v_res_898_ = l_Lean_Level_getLevelOffset(v_x_897_);
lean_dec(v_x_897_);
return v_res_898_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_toNat(lean_object* v_lvl_899_){
_start:
{
lean_object* v___x_900_; 
v___x_900_ = l_Lean_Level_getLevelOffset(v_lvl_899_);
if (lean_obj_tag(v___x_900_) == 0)
{
lean_object* v___x_901_; lean_object* v___x_902_; 
v___x_901_ = l_Lean_Level_getOffset(v_lvl_899_);
v___x_902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_902_, 0, v___x_901_);
return v___x_902_;
}
else
{
lean_object* v___x_903_; 
lean_dec(v___x_900_);
v___x_903_ = lean_box(0);
return v___x_903_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_toNat___boxed(lean_object* v_lvl_904_){
_start:
{
lean_object* v_res_905_; 
v_res_905_ = l_Lean_Level_toNat(v_lvl_904_);
lean_dec(v_lvl_904_);
return v_res_905_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_beq___boxed(lean_object* v_a_908_, lean_object* v_b_909_){
_start:
{
uint8_t v_res_910_; lean_object* v_r_911_; 
v_res_910_ = lean_level_eq(v_a_908_, v_b_909_);
lean_dec(v_b_909_);
lean_dec(v_a_908_);
v_r_911_ = lean_box(v_res_910_);
return v_r_911_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_occurs(lean_object* v_x_914_, lean_object* v_x_915_){
_start:
{
switch(lean_obj_tag(v_x_915_))
{
case 1:
{
lean_object* v_a_916_; uint8_t v___x_917_; 
v_a_916_ = lean_ctor_get(v_x_915_, 0);
v___x_917_ = lean_level_eq(v_x_914_, v_x_915_);
if (v___x_917_ == 0)
{
v_x_915_ = v_a_916_;
goto _start;
}
else
{
return v___x_917_;
}
}
case 2:
{
lean_object* v_a_919_; lean_object* v_a_920_; uint8_t v___y_922_; uint8_t v___x_924_; 
v_a_919_ = lean_ctor_get(v_x_915_, 0);
v_a_920_ = lean_ctor_get(v_x_915_, 1);
v___x_924_ = lean_level_eq(v_x_914_, v_x_915_);
if (v___x_924_ == 0)
{
uint8_t v___x_925_; 
v___x_925_ = l_Lean_Level_occurs(v_x_914_, v_a_919_);
v___y_922_ = v___x_925_;
goto v___jp_921_;
}
else
{
v___y_922_ = v___x_924_;
goto v___jp_921_;
}
v___jp_921_:
{
if (v___y_922_ == 0)
{
v_x_915_ = v_a_920_;
goto _start;
}
else
{
return v___y_922_;
}
}
}
case 3:
{
lean_object* v_a_926_; lean_object* v_a_927_; uint8_t v___y_929_; uint8_t v___x_931_; 
v_a_926_ = lean_ctor_get(v_x_915_, 0);
v_a_927_ = lean_ctor_get(v_x_915_, 1);
v___x_931_ = lean_level_eq(v_x_914_, v_x_915_);
if (v___x_931_ == 0)
{
uint8_t v___x_932_; 
v___x_932_ = l_Lean_Level_occurs(v_x_914_, v_a_926_);
v___y_929_ = v___x_932_;
goto v___jp_928_;
}
else
{
v___y_929_ = v___x_931_;
goto v___jp_928_;
}
v___jp_928_:
{
if (v___y_929_ == 0)
{
v_x_915_ = v_a_927_;
goto _start;
}
else
{
return v___y_929_;
}
}
}
default: 
{
uint8_t v___x_933_; 
v___x_933_ = lean_level_eq(v_x_914_, v_x_915_);
return v___x_933_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_occurs___boxed(lean_object* v_x_934_, lean_object* v_x_935_){
_start:
{
uint8_t v_res_936_; lean_object* v_r_937_; 
v_res_936_ = l_Lean_Level_occurs(v_x_934_, v_x_935_);
lean_dec(v_x_935_);
lean_dec(v_x_934_);
v_r_937_ = lean_box(v_res_936_);
return v_r_937_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_ctorToNat(lean_object* v_x_938_){
_start:
{
switch(lean_obj_tag(v_x_938_))
{
case 0:
{
lean_object* v___x_939_; 
v___x_939_ = lean_unsigned_to_nat(0u);
return v___x_939_;
}
case 1:
{
lean_object* v___x_940_; 
v___x_940_ = lean_unsigned_to_nat(3u);
return v___x_940_;
}
case 2:
{
lean_object* v___x_941_; 
v___x_941_ = lean_unsigned_to_nat(4u);
return v___x_941_;
}
case 3:
{
lean_object* v___x_942_; 
v___x_942_ = lean_unsigned_to_nat(5u);
return v___x_942_;
}
case 4:
{
lean_object* v___x_943_; 
v___x_943_ = lean_unsigned_to_nat(1u);
return v___x_943_;
}
default: 
{
lean_object* v___x_944_; 
v___x_944_ = lean_unsigned_to_nat(2u);
return v___x_944_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_ctorToNat___boxed(lean_object* v_x_945_){
_start:
{
lean_object* v_res_946_; 
v_res_946_ = l_Lean_Level_ctorToNat(v_x_945_);
lean_dec(v_x_945_);
return v_res_946_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_normLtAux(lean_object* v_x_947_, lean_object* v_x_948_, lean_object* v_x_949_, lean_object* v_x_950_){
_start:
{
lean_object* v_l_u2081_952_; lean_object* v_k_u2081_953_; lean_object* v_l_u2082_954_; lean_object* v_k_u2082_955_; lean_object* v_l_u2081_960_; lean_object* v_k_u2081_961_; lean_object* v_l_u2082_962_; lean_object* v_k_u2082_963_; 
switch(lean_obj_tag(v_x_947_))
{
case 1:
{
lean_object* v_a_969_; lean_object* v___x_970_; lean_object* v___x_971_; 
v_a_969_ = lean_ctor_get(v_x_947_, 0);
v___x_970_ = lean_unsigned_to_nat(1u);
v___x_971_ = lean_nat_add(v_x_948_, v___x_970_);
lean_dec(v_x_948_);
v_x_947_ = v_a_969_;
v_x_948_ = v___x_971_;
goto _start;
}
case 2:
{
switch(lean_obj_tag(v_x_949_))
{
case 1:
{
lean_object* v_a_973_; 
v_a_973_ = lean_ctor_get(v_x_949_, 0);
v_l_u2081_952_ = v_x_947_;
v_k_u2081_953_ = v_x_948_;
v_l_u2082_954_ = v_a_973_;
v_k_u2082_955_ = v_x_950_;
goto v___jp_951_;
}
case 2:
{
lean_object* v_a_974_; lean_object* v_a_975_; lean_object* v_a_976_; lean_object* v_a_977_; uint8_t v___x_981_; 
v_a_974_ = lean_ctor_get(v_x_947_, 0);
v_a_975_ = lean_ctor_get(v_x_947_, 1);
v_a_976_ = lean_ctor_get(v_x_949_, 0);
v_a_977_ = lean_ctor_get(v_x_949_, 1);
v___x_981_ = lean_level_eq(v_x_947_, v_x_949_);
if (v___x_981_ == 0)
{
uint8_t v___x_982_; 
lean_dec(v_x_950_);
lean_dec(v_x_948_);
v___x_982_ = lean_level_eq(v_a_974_, v_a_976_);
if (v___x_982_ == 0)
{
goto v___jp_978_;
}
else
{
if (v___x_981_ == 0)
{
lean_object* v___x_983_; 
v___x_983_ = lean_unsigned_to_nat(0u);
v_x_947_ = v_a_975_;
v_x_948_ = v___x_983_;
v_x_949_ = v_a_977_;
v_x_950_ = v___x_983_;
goto _start;
}
else
{
goto v___jp_978_;
}
}
}
else
{
uint8_t v___x_985_; 
v___x_985_ = lean_nat_dec_lt(v_x_948_, v_x_950_);
lean_dec(v_x_950_);
lean_dec(v_x_948_);
return v___x_985_;
}
v___jp_978_:
{
lean_object* v___x_979_; 
v___x_979_ = lean_unsigned_to_nat(0u);
v_x_947_ = v_a_974_;
v_x_948_ = v___x_979_;
v_x_949_ = v_a_976_;
v_x_950_ = v___x_979_;
goto _start;
}
}
default: 
{
v_l_u2081_960_ = v_x_947_;
v_k_u2081_961_ = v_x_948_;
v_l_u2082_962_ = v_x_949_;
v_k_u2082_963_ = v_x_950_;
goto v___jp_959_;
}
}
}
case 3:
{
switch(lean_obj_tag(v_x_949_))
{
case 1:
{
lean_object* v_a_986_; 
v_a_986_ = lean_ctor_get(v_x_949_, 0);
v_l_u2081_952_ = v_x_947_;
v_k_u2081_953_ = v_x_948_;
v_l_u2082_954_ = v_a_986_;
v_k_u2082_955_ = v_x_950_;
goto v___jp_951_;
}
case 3:
{
lean_object* v_a_987_; lean_object* v_a_988_; lean_object* v_a_989_; lean_object* v_a_990_; uint8_t v___x_994_; 
v_a_987_ = lean_ctor_get(v_x_947_, 0);
v_a_988_ = lean_ctor_get(v_x_947_, 1);
v_a_989_ = lean_ctor_get(v_x_949_, 0);
v_a_990_ = lean_ctor_get(v_x_949_, 1);
v___x_994_ = lean_level_eq(v_x_947_, v_x_949_);
if (v___x_994_ == 0)
{
uint8_t v___x_995_; 
lean_dec(v_x_950_);
lean_dec(v_x_948_);
v___x_995_ = lean_level_eq(v_a_987_, v_a_989_);
if (v___x_995_ == 0)
{
goto v___jp_991_;
}
else
{
if (v___x_994_ == 0)
{
lean_object* v___x_996_; 
v___x_996_ = lean_unsigned_to_nat(0u);
v_x_947_ = v_a_988_;
v_x_948_ = v___x_996_;
v_x_949_ = v_a_990_;
v_x_950_ = v___x_996_;
goto _start;
}
else
{
goto v___jp_991_;
}
}
}
else
{
uint8_t v___x_998_; 
v___x_998_ = lean_nat_dec_lt(v_x_948_, v_x_950_);
lean_dec(v_x_950_);
lean_dec(v_x_948_);
return v___x_998_;
}
v___jp_991_:
{
lean_object* v___x_992_; 
v___x_992_ = lean_unsigned_to_nat(0u);
v_x_947_ = v_a_987_;
v_x_948_ = v___x_992_;
v_x_949_ = v_a_989_;
v_x_950_ = v___x_992_;
goto _start;
}
}
default: 
{
v_l_u2081_960_ = v_x_947_;
v_k_u2081_961_ = v_x_948_;
v_l_u2082_962_ = v_x_949_;
v_k_u2082_963_ = v_x_950_;
goto v___jp_959_;
}
}
}
case 4:
{
switch(lean_obj_tag(v_x_949_))
{
case 1:
{
lean_object* v_a_999_; 
v_a_999_ = lean_ctor_get(v_x_949_, 0);
v_l_u2081_952_ = v_x_947_;
v_k_u2081_953_ = v_x_948_;
v_l_u2082_954_ = v_a_999_;
v_k_u2082_955_ = v_x_950_;
goto v___jp_951_;
}
case 4:
{
lean_object* v_a_1000_; lean_object* v_a_1001_; uint8_t v___x_1002_; 
v_a_1000_ = lean_ctor_get(v_x_947_, 0);
v_a_1001_ = lean_ctor_get(v_x_949_, 0);
v___x_1002_ = lean_name_eq(v_a_1000_, v_a_1001_);
if (v___x_1002_ == 0)
{
uint8_t v___x_1003_; 
lean_dec(v_x_950_);
lean_dec(v_x_948_);
v___x_1003_ = l_Lean_Name_lt(v_a_1000_, v_a_1001_);
return v___x_1003_;
}
else
{
uint8_t v___x_1004_; 
v___x_1004_ = lean_nat_dec_lt(v_x_948_, v_x_950_);
lean_dec(v_x_950_);
lean_dec(v_x_948_);
return v___x_1004_;
}
}
default: 
{
v_l_u2081_960_ = v_x_947_;
v_k_u2081_961_ = v_x_948_;
v_l_u2082_962_ = v_x_949_;
v_k_u2082_963_ = v_x_950_;
goto v___jp_959_;
}
}
}
case 5:
{
switch(lean_obj_tag(v_x_949_))
{
case 1:
{
lean_object* v_a_1005_; 
v_a_1005_ = lean_ctor_get(v_x_949_, 0);
v_l_u2081_952_ = v_x_947_;
v_k_u2081_953_ = v_x_948_;
v_l_u2082_954_ = v_a_1005_;
v_k_u2082_955_ = v_x_950_;
goto v___jp_951_;
}
case 5:
{
lean_object* v_a_1006_; lean_object* v_a_1007_; uint8_t v___x_1008_; 
v_a_1006_ = lean_ctor_get(v_x_947_, 0);
v_a_1007_ = lean_ctor_get(v_x_949_, 0);
v___x_1008_ = lean_name_eq(v_a_1006_, v_a_1007_);
if (v___x_1008_ == 0)
{
uint8_t v___x_1009_; 
lean_dec(v_x_950_);
lean_dec(v_x_948_);
v___x_1009_ = l_Lean_Name_lt(v_a_1006_, v_a_1007_);
return v___x_1009_;
}
else
{
uint8_t v___x_1010_; 
v___x_1010_ = lean_nat_dec_lt(v_x_948_, v_x_950_);
lean_dec(v_x_950_);
lean_dec(v_x_948_);
return v___x_1010_;
}
}
default: 
{
v_l_u2081_960_ = v_x_947_;
v_k_u2081_961_ = v_x_948_;
v_l_u2082_962_ = v_x_949_;
v_k_u2082_963_ = v_x_950_;
goto v___jp_959_;
}
}
}
default: 
{
if (lean_obj_tag(v_x_949_) == 1)
{
lean_object* v_a_1011_; 
v_a_1011_ = lean_ctor_get(v_x_949_, 0);
v_l_u2081_952_ = v_x_947_;
v_k_u2081_953_ = v_x_948_;
v_l_u2082_954_ = v_a_1011_;
v_k_u2082_955_ = v_x_950_;
goto v___jp_951_;
}
else
{
v_l_u2081_960_ = v_x_947_;
v_k_u2081_961_ = v_x_948_;
v_l_u2082_962_ = v_x_949_;
v_k_u2082_963_ = v_x_950_;
goto v___jp_959_;
}
}
}
v___jp_951_:
{
lean_object* v___x_956_; lean_object* v___x_957_; 
v___x_956_ = lean_unsigned_to_nat(1u);
v___x_957_ = lean_nat_add(v_k_u2082_955_, v___x_956_);
lean_dec(v_k_u2082_955_);
v_x_947_ = v_l_u2081_952_;
v_x_948_ = v_k_u2081_953_;
v_x_949_ = v_l_u2082_954_;
v_x_950_ = v___x_957_;
goto _start;
}
v___jp_959_:
{
uint8_t v___x_964_; 
v___x_964_ = lean_level_eq(v_l_u2081_960_, v_l_u2082_962_);
if (v___x_964_ == 0)
{
lean_object* v___x_965_; lean_object* v___x_966_; uint8_t v___x_967_; 
lean_dec(v_k_u2082_963_);
lean_dec(v_k_u2081_961_);
v___x_965_ = l_Lean_Level_ctorToNat(v_l_u2081_960_);
v___x_966_ = l_Lean_Level_ctorToNat(v_l_u2082_962_);
v___x_967_ = lean_nat_dec_lt(v___x_965_, v___x_966_);
lean_dec(v___x_966_);
lean_dec(v___x_965_);
return v___x_967_;
}
else
{
uint8_t v___x_968_; 
v___x_968_ = lean_nat_dec_lt(v_k_u2081_961_, v_k_u2082_963_);
lean_dec(v_k_u2082_963_);
lean_dec(v_k_u2081_961_);
return v___x_968_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_normLtAux___boxed(lean_object* v_x_1012_, lean_object* v_x_1013_, lean_object* v_x_1014_, lean_object* v_x_1015_){
_start:
{
uint8_t v_res_1016_; lean_object* v_r_1017_; 
v_res_1016_ = l_Lean_Level_normLtAux(v_x_1012_, v_x_1013_, v_x_1014_, v_x_1015_);
lean_dec(v_x_1014_);
lean_dec(v_x_1012_);
v_r_1017_ = lean_box(v_res_1016_);
return v_r_1017_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_normLtAux_match__1_splitter___redArg(lean_object* v_x_1018_, lean_object* v_x_1019_, lean_object* v_x_1020_, lean_object* v_x_1021_, lean_object* v_h__1_1022_, lean_object* v_h__2_1023_, lean_object* v_h__3_1024_, lean_object* v_h__4_1025_, lean_object* v_h__5_1026_, lean_object* v_h__6_1027_, lean_object* v_h__7_1028_){
_start:
{
switch(lean_obj_tag(v_x_1018_))
{
case 1:
{
lean_object* v_a_1029_; lean_object* v___x_1030_; 
lean_dec(v_h__7_1028_);
lean_dec(v_h__6_1027_);
lean_dec(v_h__5_1026_);
lean_dec(v_h__4_1025_);
lean_dec(v_h__3_1024_);
lean_dec(v_h__2_1023_);
v_a_1029_ = lean_ctor_get(v_x_1018_, 0);
lean_inc(v_a_1029_);
lean_dec_ref_known(v_x_1018_, 1);
v___x_1030_ = lean_apply_4(v_h__1_1022_, v_a_1029_, v_x_1019_, v_x_1020_, v_x_1021_);
return v___x_1030_;
}
case 2:
{
lean_dec(v_h__6_1027_);
lean_dec(v_h__5_1026_);
lean_dec(v_h__4_1025_);
lean_dec(v_h__1_1022_);
switch(lean_obj_tag(v_x_1020_))
{
case 1:
{
lean_object* v_a_1031_; lean_object* v___x_1032_; 
lean_dec(v_h__7_1028_);
lean_dec(v_h__3_1024_);
v_a_1031_ = lean_ctor_get(v_x_1020_, 0);
lean_inc(v_a_1031_);
lean_dec_ref_known(v_x_1020_, 1);
v___x_1032_ = lean_apply_5(v_h__2_1023_, v_x_1018_, v_x_1019_, v_a_1031_, v_x_1021_, lean_box(0));
return v___x_1032_;
}
case 2:
{
lean_object* v_a_1033_; lean_object* v_a_1034_; lean_object* v_a_1035_; lean_object* v_a_1036_; lean_object* v___x_1037_; 
lean_dec(v_h__7_1028_);
lean_dec(v_h__2_1023_);
v_a_1033_ = lean_ctor_get(v_x_1018_, 0);
lean_inc(v_a_1033_);
v_a_1034_ = lean_ctor_get(v_x_1018_, 1);
lean_inc(v_a_1034_);
lean_dec_ref_known(v_x_1018_, 2);
v_a_1035_ = lean_ctor_get(v_x_1020_, 0);
lean_inc(v_a_1035_);
v_a_1036_ = lean_ctor_get(v_x_1020_, 1);
lean_inc(v_a_1036_);
lean_dec_ref_known(v_x_1020_, 2);
v___x_1037_ = lean_apply_6(v_h__3_1024_, v_a_1033_, v_a_1034_, v_x_1019_, v_a_1035_, v_a_1036_, v_x_1021_);
return v___x_1037_;
}
default: 
{
lean_object* v___x_1038_; 
lean_dec(v_h__3_1024_);
lean_dec(v_h__2_1023_);
v___x_1038_ = lean_apply_10(v_h__7_1028_, v_x_1018_, v_x_1019_, v_x_1020_, v_x_1021_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_1038_;
}
}
}
case 3:
{
lean_dec(v_h__6_1027_);
lean_dec(v_h__5_1026_);
lean_dec(v_h__3_1024_);
lean_dec(v_h__1_1022_);
switch(lean_obj_tag(v_x_1020_))
{
case 1:
{
lean_object* v_a_1039_; lean_object* v___x_1040_; 
lean_dec(v_h__7_1028_);
lean_dec(v_h__4_1025_);
v_a_1039_ = lean_ctor_get(v_x_1020_, 0);
lean_inc(v_a_1039_);
lean_dec_ref_known(v_x_1020_, 1);
v___x_1040_ = lean_apply_5(v_h__2_1023_, v_x_1018_, v_x_1019_, v_a_1039_, v_x_1021_, lean_box(0));
return v___x_1040_;
}
case 3:
{
lean_object* v_a_1041_; lean_object* v_a_1042_; lean_object* v_a_1043_; lean_object* v_a_1044_; lean_object* v___x_1045_; 
lean_dec(v_h__7_1028_);
lean_dec(v_h__2_1023_);
v_a_1041_ = lean_ctor_get(v_x_1018_, 0);
lean_inc(v_a_1041_);
v_a_1042_ = lean_ctor_get(v_x_1018_, 1);
lean_inc(v_a_1042_);
lean_dec_ref_known(v_x_1018_, 2);
v_a_1043_ = lean_ctor_get(v_x_1020_, 0);
lean_inc(v_a_1043_);
v_a_1044_ = lean_ctor_get(v_x_1020_, 1);
lean_inc(v_a_1044_);
lean_dec_ref_known(v_x_1020_, 2);
v___x_1045_ = lean_apply_6(v_h__4_1025_, v_a_1041_, v_a_1042_, v_x_1019_, v_a_1043_, v_a_1044_, v_x_1021_);
return v___x_1045_;
}
default: 
{
lean_object* v___x_1046_; 
lean_dec(v_h__4_1025_);
lean_dec(v_h__2_1023_);
v___x_1046_ = lean_apply_10(v_h__7_1028_, v_x_1018_, v_x_1019_, v_x_1020_, v_x_1021_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_1046_;
}
}
}
case 4:
{
lean_dec(v_h__6_1027_);
lean_dec(v_h__4_1025_);
lean_dec(v_h__3_1024_);
lean_dec(v_h__1_1022_);
switch(lean_obj_tag(v_x_1020_))
{
case 1:
{
lean_object* v_a_1047_; lean_object* v___x_1048_; 
lean_dec(v_h__7_1028_);
lean_dec(v_h__5_1026_);
v_a_1047_ = lean_ctor_get(v_x_1020_, 0);
lean_inc(v_a_1047_);
lean_dec_ref_known(v_x_1020_, 1);
v___x_1048_ = lean_apply_5(v_h__2_1023_, v_x_1018_, v_x_1019_, v_a_1047_, v_x_1021_, lean_box(0));
return v___x_1048_;
}
case 4:
{
lean_object* v_a_1049_; lean_object* v_a_1050_; lean_object* v___x_1051_; 
lean_dec(v_h__7_1028_);
lean_dec(v_h__2_1023_);
v_a_1049_ = lean_ctor_get(v_x_1018_, 0);
lean_inc(v_a_1049_);
lean_dec_ref_known(v_x_1018_, 1);
v_a_1050_ = lean_ctor_get(v_x_1020_, 0);
lean_inc(v_a_1050_);
lean_dec_ref_known(v_x_1020_, 1);
v___x_1051_ = lean_apply_4(v_h__5_1026_, v_a_1049_, v_x_1019_, v_a_1050_, v_x_1021_);
return v___x_1051_;
}
default: 
{
lean_object* v___x_1052_; 
lean_dec(v_h__5_1026_);
lean_dec(v_h__2_1023_);
v___x_1052_ = lean_apply_10(v_h__7_1028_, v_x_1018_, v_x_1019_, v_x_1020_, v_x_1021_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_1052_;
}
}
}
case 5:
{
lean_dec(v_h__5_1026_);
lean_dec(v_h__4_1025_);
lean_dec(v_h__3_1024_);
lean_dec(v_h__1_1022_);
switch(lean_obj_tag(v_x_1020_))
{
case 1:
{
lean_object* v_a_1053_; lean_object* v___x_1054_; 
lean_dec(v_h__7_1028_);
lean_dec(v_h__6_1027_);
v_a_1053_ = lean_ctor_get(v_x_1020_, 0);
lean_inc(v_a_1053_);
lean_dec_ref_known(v_x_1020_, 1);
v___x_1054_ = lean_apply_5(v_h__2_1023_, v_x_1018_, v_x_1019_, v_a_1053_, v_x_1021_, lean_box(0));
return v___x_1054_;
}
case 5:
{
lean_object* v_a_1055_; lean_object* v_a_1056_; lean_object* v___x_1057_; 
lean_dec(v_h__7_1028_);
lean_dec(v_h__2_1023_);
v_a_1055_ = lean_ctor_get(v_x_1018_, 0);
lean_inc(v_a_1055_);
lean_dec_ref_known(v_x_1018_, 1);
v_a_1056_ = lean_ctor_get(v_x_1020_, 0);
lean_inc(v_a_1056_);
lean_dec_ref_known(v_x_1020_, 1);
v___x_1057_ = lean_apply_4(v_h__6_1027_, v_a_1055_, v_x_1019_, v_a_1056_, v_x_1021_);
return v___x_1057_;
}
default: 
{
lean_object* v___x_1058_; 
lean_dec(v_h__6_1027_);
lean_dec(v_h__2_1023_);
v___x_1058_ = lean_apply_10(v_h__7_1028_, v_x_1018_, v_x_1019_, v_x_1020_, v_x_1021_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_1058_;
}
}
}
default: 
{
lean_dec(v_h__6_1027_);
lean_dec(v_h__5_1026_);
lean_dec(v_h__4_1025_);
lean_dec(v_h__3_1024_);
lean_dec(v_h__1_1022_);
if (lean_obj_tag(v_x_1020_) == 1)
{
lean_object* v_a_1059_; lean_object* v___x_1060_; 
lean_dec(v_h__7_1028_);
v_a_1059_ = lean_ctor_get(v_x_1020_, 0);
lean_inc(v_a_1059_);
lean_dec_ref_known(v_x_1020_, 1);
v___x_1060_ = lean_apply_5(v_h__2_1023_, v_x_1018_, v_x_1019_, v_a_1059_, v_x_1021_, lean_box(0));
return v___x_1060_;
}
else
{
lean_object* v___x_1061_; 
lean_dec(v_h__2_1023_);
v___x_1061_ = lean_apply_10(v_h__7_1028_, v_x_1018_, v_x_1019_, v_x_1020_, v_x_1021_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_1061_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_normLtAux_match__1_splitter(lean_object* v_motive_1062_, lean_object* v_x_1063_, lean_object* v_x_1064_, lean_object* v_x_1065_, lean_object* v_x_1066_, lean_object* v_h__1_1067_, lean_object* v_h__2_1068_, lean_object* v_h__3_1069_, lean_object* v_h__4_1070_, lean_object* v_h__5_1071_, lean_object* v_h__6_1072_, lean_object* v_h__7_1073_){
_start:
{
switch(lean_obj_tag(v_x_1063_))
{
case 1:
{
lean_object* v_a_1074_; lean_object* v___x_1075_; 
lean_dec(v_h__7_1073_);
lean_dec(v_h__6_1072_);
lean_dec(v_h__5_1071_);
lean_dec(v_h__4_1070_);
lean_dec(v_h__3_1069_);
lean_dec(v_h__2_1068_);
v_a_1074_ = lean_ctor_get(v_x_1063_, 0);
lean_inc(v_a_1074_);
lean_dec_ref_known(v_x_1063_, 1);
v___x_1075_ = lean_apply_4(v_h__1_1067_, v_a_1074_, v_x_1064_, v_x_1065_, v_x_1066_);
return v___x_1075_;
}
case 2:
{
lean_dec(v_h__6_1072_);
lean_dec(v_h__5_1071_);
lean_dec(v_h__4_1070_);
lean_dec(v_h__1_1067_);
switch(lean_obj_tag(v_x_1065_))
{
case 1:
{
lean_object* v_a_1076_; lean_object* v___x_1077_; 
lean_dec(v_h__7_1073_);
lean_dec(v_h__3_1069_);
v_a_1076_ = lean_ctor_get(v_x_1065_, 0);
lean_inc(v_a_1076_);
lean_dec_ref_known(v_x_1065_, 1);
v___x_1077_ = lean_apply_5(v_h__2_1068_, v_x_1063_, v_x_1064_, v_a_1076_, v_x_1066_, lean_box(0));
return v___x_1077_;
}
case 2:
{
lean_object* v_a_1078_; lean_object* v_a_1079_; lean_object* v_a_1080_; lean_object* v_a_1081_; lean_object* v___x_1082_; 
lean_dec(v_h__7_1073_);
lean_dec(v_h__2_1068_);
v_a_1078_ = lean_ctor_get(v_x_1063_, 0);
lean_inc(v_a_1078_);
v_a_1079_ = lean_ctor_get(v_x_1063_, 1);
lean_inc(v_a_1079_);
lean_dec_ref_known(v_x_1063_, 2);
v_a_1080_ = lean_ctor_get(v_x_1065_, 0);
lean_inc(v_a_1080_);
v_a_1081_ = lean_ctor_get(v_x_1065_, 1);
lean_inc(v_a_1081_);
lean_dec_ref_known(v_x_1065_, 2);
v___x_1082_ = lean_apply_6(v_h__3_1069_, v_a_1078_, v_a_1079_, v_x_1064_, v_a_1080_, v_a_1081_, v_x_1066_);
return v___x_1082_;
}
default: 
{
lean_object* v___x_1083_; 
lean_dec(v_h__3_1069_);
lean_dec(v_h__2_1068_);
v___x_1083_ = lean_apply_10(v_h__7_1073_, v_x_1063_, v_x_1064_, v_x_1065_, v_x_1066_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_1083_;
}
}
}
case 3:
{
lean_dec(v_h__6_1072_);
lean_dec(v_h__5_1071_);
lean_dec(v_h__3_1069_);
lean_dec(v_h__1_1067_);
switch(lean_obj_tag(v_x_1065_))
{
case 1:
{
lean_object* v_a_1084_; lean_object* v___x_1085_; 
lean_dec(v_h__7_1073_);
lean_dec(v_h__4_1070_);
v_a_1084_ = lean_ctor_get(v_x_1065_, 0);
lean_inc(v_a_1084_);
lean_dec_ref_known(v_x_1065_, 1);
v___x_1085_ = lean_apply_5(v_h__2_1068_, v_x_1063_, v_x_1064_, v_a_1084_, v_x_1066_, lean_box(0));
return v___x_1085_;
}
case 3:
{
lean_object* v_a_1086_; lean_object* v_a_1087_; lean_object* v_a_1088_; lean_object* v_a_1089_; lean_object* v___x_1090_; 
lean_dec(v_h__7_1073_);
lean_dec(v_h__2_1068_);
v_a_1086_ = lean_ctor_get(v_x_1063_, 0);
lean_inc(v_a_1086_);
v_a_1087_ = lean_ctor_get(v_x_1063_, 1);
lean_inc(v_a_1087_);
lean_dec_ref_known(v_x_1063_, 2);
v_a_1088_ = lean_ctor_get(v_x_1065_, 0);
lean_inc(v_a_1088_);
v_a_1089_ = lean_ctor_get(v_x_1065_, 1);
lean_inc(v_a_1089_);
lean_dec_ref_known(v_x_1065_, 2);
v___x_1090_ = lean_apply_6(v_h__4_1070_, v_a_1086_, v_a_1087_, v_x_1064_, v_a_1088_, v_a_1089_, v_x_1066_);
return v___x_1090_;
}
default: 
{
lean_object* v___x_1091_; 
lean_dec(v_h__4_1070_);
lean_dec(v_h__2_1068_);
v___x_1091_ = lean_apply_10(v_h__7_1073_, v_x_1063_, v_x_1064_, v_x_1065_, v_x_1066_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_1091_;
}
}
}
case 4:
{
lean_dec(v_h__6_1072_);
lean_dec(v_h__4_1070_);
lean_dec(v_h__3_1069_);
lean_dec(v_h__1_1067_);
switch(lean_obj_tag(v_x_1065_))
{
case 1:
{
lean_object* v_a_1092_; lean_object* v___x_1093_; 
lean_dec(v_h__7_1073_);
lean_dec(v_h__5_1071_);
v_a_1092_ = lean_ctor_get(v_x_1065_, 0);
lean_inc(v_a_1092_);
lean_dec_ref_known(v_x_1065_, 1);
v___x_1093_ = lean_apply_5(v_h__2_1068_, v_x_1063_, v_x_1064_, v_a_1092_, v_x_1066_, lean_box(0));
return v___x_1093_;
}
case 4:
{
lean_object* v_a_1094_; lean_object* v_a_1095_; lean_object* v___x_1096_; 
lean_dec(v_h__7_1073_);
lean_dec(v_h__2_1068_);
v_a_1094_ = lean_ctor_get(v_x_1063_, 0);
lean_inc(v_a_1094_);
lean_dec_ref_known(v_x_1063_, 1);
v_a_1095_ = lean_ctor_get(v_x_1065_, 0);
lean_inc(v_a_1095_);
lean_dec_ref_known(v_x_1065_, 1);
v___x_1096_ = lean_apply_4(v_h__5_1071_, v_a_1094_, v_x_1064_, v_a_1095_, v_x_1066_);
return v___x_1096_;
}
default: 
{
lean_object* v___x_1097_; 
lean_dec(v_h__5_1071_);
lean_dec(v_h__2_1068_);
v___x_1097_ = lean_apply_10(v_h__7_1073_, v_x_1063_, v_x_1064_, v_x_1065_, v_x_1066_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_1097_;
}
}
}
case 5:
{
lean_dec(v_h__5_1071_);
lean_dec(v_h__4_1070_);
lean_dec(v_h__3_1069_);
lean_dec(v_h__1_1067_);
switch(lean_obj_tag(v_x_1065_))
{
case 1:
{
lean_object* v_a_1098_; lean_object* v___x_1099_; 
lean_dec(v_h__7_1073_);
lean_dec(v_h__6_1072_);
v_a_1098_ = lean_ctor_get(v_x_1065_, 0);
lean_inc(v_a_1098_);
lean_dec_ref_known(v_x_1065_, 1);
v___x_1099_ = lean_apply_5(v_h__2_1068_, v_x_1063_, v_x_1064_, v_a_1098_, v_x_1066_, lean_box(0));
return v___x_1099_;
}
case 5:
{
lean_object* v_a_1100_; lean_object* v_a_1101_; lean_object* v___x_1102_; 
lean_dec(v_h__7_1073_);
lean_dec(v_h__2_1068_);
v_a_1100_ = lean_ctor_get(v_x_1063_, 0);
lean_inc(v_a_1100_);
lean_dec_ref_known(v_x_1063_, 1);
v_a_1101_ = lean_ctor_get(v_x_1065_, 0);
lean_inc(v_a_1101_);
lean_dec_ref_known(v_x_1065_, 1);
v___x_1102_ = lean_apply_4(v_h__6_1072_, v_a_1100_, v_x_1064_, v_a_1101_, v_x_1066_);
return v___x_1102_;
}
default: 
{
lean_object* v___x_1103_; 
lean_dec(v_h__6_1072_);
lean_dec(v_h__2_1068_);
v___x_1103_ = lean_apply_10(v_h__7_1073_, v_x_1063_, v_x_1064_, v_x_1065_, v_x_1066_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_1103_;
}
}
}
default: 
{
lean_dec(v_h__6_1072_);
lean_dec(v_h__5_1071_);
lean_dec(v_h__4_1070_);
lean_dec(v_h__3_1069_);
lean_dec(v_h__1_1067_);
if (lean_obj_tag(v_x_1065_) == 1)
{
lean_object* v_a_1104_; lean_object* v___x_1105_; 
lean_dec(v_h__7_1073_);
v_a_1104_ = lean_ctor_get(v_x_1065_, 0);
lean_inc(v_a_1104_);
lean_dec_ref_known(v_x_1065_, 1);
v___x_1105_ = lean_apply_5(v_h__2_1068_, v_x_1063_, v_x_1064_, v_a_1104_, v_x_1066_, lean_box(0));
return v___x_1105_;
}
else
{
lean_object* v___x_1106_; 
lean_dec(v_h__2_1068_);
v___x_1106_ = lean_apply_10(v_h__7_1073_, v_x_1063_, v_x_1064_, v_x_1065_, v_x_1066_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_1106_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Level_normLt(lean_object* v_l_u2081_1107_, lean_object* v_l_u2082_1108_){
_start:
{
lean_object* v___x_1109_; uint8_t v___x_1110_; 
v___x_1109_ = lean_unsigned_to_nat(0u);
v___x_1110_ = l_Lean_Level_normLtAux(v_l_u2081_1107_, v___x_1109_, v_l_u2082_1108_, v___x_1109_);
return v___x_1110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_normLt___boxed(lean_object* v_l_u2081_1111_, lean_object* v_l_u2082_1112_){
_start:
{
uint8_t v_res_1113_; lean_object* v_r_1114_; 
v_res_1113_ = l_Lean_Level_normLt(v_l_u2081_1111_, v_l_u2082_1112_);
lean_dec(v_l_u2082_1112_);
lean_dec(v_l_u2081_1111_);
v_r_1114_ = lean_box(v_res_1113_);
return v_r_1114_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_isAlreadyNormalizedCheap(lean_object* v_x_1115_){
_start:
{
switch(lean_obj_tag(v_x_1115_))
{
case 0:
{
uint8_t v___x_1116_; 
v___x_1116_ = 1;
return v___x_1116_;
}
case 4:
{
uint8_t v___x_1117_; 
v___x_1117_ = 1;
return v___x_1117_;
}
case 5:
{
uint8_t v___x_1118_; 
v___x_1118_ = 1;
return v___x_1118_;
}
case 1:
{
lean_object* v_a_1119_; 
v_a_1119_ = lean_ctor_get(v_x_1115_, 0);
v_x_1115_ = v_a_1119_;
goto _start;
}
default: 
{
uint8_t v___x_1121_; 
v___x_1121_ = 0;
return v___x_1121_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_isAlreadyNormalizedCheap___boxed(lean_object* v_x_1122_){
_start:
{
uint8_t v_res_1123_; lean_object* v_r_1124_; 
v_res_1123_ = l_Lean_Level_isAlreadyNormalizedCheap(v_x_1122_);
lean_dec(v_x_1122_);
v_r_1124_ = lean_box(v_res_1123_);
return v_r_1124_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_mkIMaxAux(lean_object* v_x_1125_, lean_object* v_x_1126_){
_start:
{
lean_object* v_u_u2081_1128_; lean_object* v_u_u2082_1129_; 
if (lean_obj_tag(v_x_1126_) == 0)
{
lean_dec(v_x_1125_);
return v_x_1126_;
}
else
{
switch(lean_obj_tag(v_x_1125_))
{
case 0:
{
return v_x_1126_;
}
case 1:
{
lean_object* v_a_1132_; 
v_a_1132_ = lean_ctor_get(v_x_1125_, 0);
if (lean_obj_tag(v_a_1132_) == 0)
{
lean_dec_ref_known(v_x_1125_, 1);
return v_x_1126_;
}
else
{
v_u_u2081_1128_ = v_x_1125_;
v_u_u2082_1129_ = v_x_1126_;
goto v___jp_1127_;
}
}
default: 
{
v_u_u2081_1128_ = v_x_1125_;
v_u_u2082_1129_ = v_x_1126_;
goto v___jp_1127_;
}
}
}
v___jp_1127_:
{
uint8_t v___x_1130_; 
v___x_1130_ = lean_level_eq(v_u_u2081_1128_, v_u_u2082_1129_);
if (v___x_1130_ == 0)
{
lean_object* v___x_1131_; 
v___x_1131_ = l_Lean_Level_imax___override(v_u_u2081_1128_, v_u_u2082_1129_);
return v___x_1131_;
}
else
{
lean_dec(v_u_u2082_1129_);
return v_u_u2081_1128_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_getMaxArgsAux(lean_object* v_normalize_1133_, lean_object* v_x_1134_, uint8_t v_x_1135_, lean_object* v_x_1136_){
_start:
{
if (lean_obj_tag(v_x_1134_) == 2)
{
lean_object* v_a_1137_; lean_object* v_a_1138_; lean_object* v___x_1139_; 
v_a_1137_ = lean_ctor_get(v_x_1134_, 0);
lean_inc(v_a_1137_);
v_a_1138_ = lean_ctor_get(v_x_1134_, 1);
lean_inc(v_a_1138_);
lean_dec_ref_known(v_x_1134_, 2);
lean_inc_ref(v_normalize_1133_);
v___x_1139_ = l___private_Lean_Level_0__Lean_Level_getMaxArgsAux(v_normalize_1133_, v_a_1137_, v_x_1135_, v_x_1136_);
v_x_1134_ = v_a_1138_;
v_x_1136_ = v___x_1139_;
goto _start;
}
else
{
if (v_x_1135_ == 0)
{
lean_object* v___x_1141_; uint8_t v___x_1142_; 
lean_inc_ref(v_normalize_1133_);
v___x_1141_ = lean_apply_1(v_normalize_1133_, v_x_1134_);
v___x_1142_ = 1;
v_x_1134_ = v___x_1141_;
v_x_1135_ = v___x_1142_;
goto _start;
}
else
{
lean_object* v___x_1144_; 
lean_dec_ref(v_normalize_1133_);
v___x_1144_ = lean_array_push(v_x_1136_, v_x_1134_);
return v___x_1144_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_getMaxArgsAux___boxed(lean_object* v_normalize_1145_, lean_object* v_x_1146_, lean_object* v_x_1147_, lean_object* v_x_1148_){
_start:
{
uint8_t v_x_31__boxed_1149_; lean_object* v_res_1150_; 
v_x_31__boxed_1149_ = lean_unbox(v_x_1147_);
v_res_1150_ = l___private_Lean_Level_0__Lean_Level_getMaxArgsAux(v_normalize_1145_, v_x_1146_, v_x_31__boxed_1149_, v_x_1148_);
return v_res_1150_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_accMax(lean_object* v_result_1151_, lean_object* v_prev_1152_, lean_object* v_offset_1153_){
_start:
{
uint8_t v___x_1154_; 
v___x_1154_ = l_Lean_Level_isZero(v_result_1151_);
if (v___x_1154_ == 0)
{
lean_object* v___x_1155_; lean_object* v___x_1156_; 
v___x_1155_ = l_Lean_Level_addOffsetAux(v_offset_1153_, v_prev_1152_);
v___x_1156_ = l_Lean_Level_max___override(v_result_1151_, v___x_1155_);
return v___x_1156_;
}
else
{
lean_object* v___x_1157_; 
lean_dec(v_result_1151_);
v___x_1157_ = l_Lean_Level_addOffsetAux(v_offset_1153_, v_prev_1152_);
return v___x_1157_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_mkMaxAux(lean_object* v_lvls_1158_, lean_object* v_extraK_1159_, lean_object* v_i_1160_, lean_object* v_prev_1161_, lean_object* v_prevK_1162_, lean_object* v_result_1163_){
_start:
{
lean_object* v___x_1164_; uint8_t v___x_1165_; 
v___x_1164_ = lean_array_get_size(v_lvls_1158_);
v___x_1165_ = lean_nat_dec_lt(v_i_1160_, v___x_1164_);
if (v___x_1165_ == 0)
{
lean_object* v___x_1166_; lean_object* v___x_1167_; 
lean_dec(v_i_1160_);
v___x_1166_ = lean_nat_add(v_extraK_1159_, v_prevK_1162_);
lean_dec(v_prevK_1162_);
v___x_1167_ = l___private_Lean_Level_0__Lean_Level_accMax(v_result_1163_, v_prev_1161_, v___x_1166_);
return v___x_1167_;
}
else
{
lean_object* v_lvl_1168_; lean_object* v_curr_1169_; lean_object* v_currK_1170_; uint8_t v___x_1171_; 
v_lvl_1168_ = lean_array_fget_borrowed(v_lvls_1158_, v_i_1160_);
v_curr_1169_ = l_Lean_Level_getLevelOffset(v_lvl_1168_);
v_currK_1170_ = l_Lean_Level_getOffset(v_lvl_1168_);
v___x_1171_ = lean_level_eq(v_curr_1169_, v_prev_1161_);
if (v___x_1171_ == 0)
{
lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; 
v___x_1172_ = lean_unsigned_to_nat(1u);
v___x_1173_ = lean_nat_add(v_i_1160_, v___x_1172_);
lean_dec(v_i_1160_);
v___x_1174_ = lean_nat_add(v_extraK_1159_, v_prevK_1162_);
lean_dec(v_prevK_1162_);
v___x_1175_ = l___private_Lean_Level_0__Lean_Level_accMax(v_result_1163_, v_prev_1161_, v___x_1174_);
v_i_1160_ = v___x_1173_;
v_prev_1161_ = v_curr_1169_;
v_prevK_1162_ = v_currK_1170_;
v_result_1163_ = v___x_1175_;
goto _start;
}
else
{
lean_object* v___x_1177_; lean_object* v___x_1178_; 
lean_dec(v_prevK_1162_);
lean_dec(v_prev_1161_);
v___x_1177_ = lean_unsigned_to_nat(1u);
v___x_1178_ = lean_nat_add(v_i_1160_, v___x_1177_);
lean_dec(v_i_1160_);
v_i_1160_ = v___x_1178_;
v_prev_1161_ = v_curr_1169_;
v_prevK_1162_ = v_currK_1170_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_mkMaxAux___boxed(lean_object* v_lvls_1180_, lean_object* v_extraK_1181_, lean_object* v_i_1182_, lean_object* v_prev_1183_, lean_object* v_prevK_1184_, lean_object* v_result_1185_){
_start:
{
lean_object* v_res_1186_; 
v_res_1186_ = l___private_Lean_Level_0__Lean_Level_mkMaxAux(v_lvls_1180_, v_extraK_1181_, v_i_1182_, v_prev_1183_, v_prevK_1184_, v_result_1185_);
lean_dec(v_extraK_1181_);
lean_dec_ref(v_lvls_1180_);
return v_res_1186_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_skipExplicit(lean_object* v_lvls_1187_, lean_object* v_i_1188_){
_start:
{
lean_object* v___x_1189_; uint8_t v___x_1190_; 
v___x_1189_ = lean_array_get_size(v_lvls_1187_);
v___x_1190_ = lean_nat_dec_lt(v_i_1188_, v___x_1189_);
if (v___x_1190_ == 0)
{
return v_i_1188_;
}
else
{
lean_object* v_lvl_1191_; lean_object* v___x_1192_; uint8_t v___x_1193_; 
v_lvl_1191_ = lean_array_fget_borrowed(v_lvls_1187_, v_i_1188_);
v___x_1192_ = l_Lean_Level_getLevelOffset(v_lvl_1191_);
v___x_1193_ = l_Lean_Level_isZero(v___x_1192_);
lean_dec(v___x_1192_);
if (v___x_1193_ == 0)
{
return v_i_1188_;
}
else
{
lean_object* v___x_1194_; lean_object* v___x_1195_; 
v___x_1194_ = lean_unsigned_to_nat(1u);
v___x_1195_ = lean_nat_add(v_i_1188_, v___x_1194_);
lean_dec(v_i_1188_);
v_i_1188_ = v___x_1195_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_skipExplicit___boxed(lean_object* v_lvls_1197_, lean_object* v_i_1198_){
_start:
{
lean_object* v_res_1199_; 
v_res_1199_ = l___private_Lean_Level_0__Lean_Level_skipExplicit(v_lvls_1197_, v_i_1198_);
lean_dec_ref(v_lvls_1197_);
return v_res_1199_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Level_0__Lean_Level_isExplicitSubsumedAux(lean_object* v_lvls_1200_, lean_object* v_maxExplicit_1201_, lean_object* v_i_1202_){
_start:
{
lean_object* v___x_1203_; uint8_t v___x_1204_; 
v___x_1203_ = lean_array_get_size(v_lvls_1200_);
v___x_1204_ = lean_nat_dec_lt(v_i_1202_, v___x_1203_);
if (v___x_1204_ == 0)
{
lean_dec(v_i_1202_);
return v___x_1204_;
}
else
{
lean_object* v_lvl_1205_; lean_object* v___x_1206_; uint8_t v___x_1207_; 
v_lvl_1205_ = lean_array_fget_borrowed(v_lvls_1200_, v_i_1202_);
v___x_1206_ = l_Lean_Level_getOffset(v_lvl_1205_);
v___x_1207_ = lean_nat_dec_le(v_maxExplicit_1201_, v___x_1206_);
lean_dec(v___x_1206_);
if (v___x_1207_ == 0)
{
lean_object* v___x_1208_; lean_object* v___x_1209_; 
v___x_1208_ = lean_unsigned_to_nat(1u);
v___x_1209_ = lean_nat_add(v_i_1202_, v___x_1208_);
lean_dec(v_i_1202_);
v_i_1202_ = v___x_1209_;
goto _start;
}
else
{
lean_dec(v_i_1202_);
return v___x_1207_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_isExplicitSubsumedAux___boxed(lean_object* v_lvls_1211_, lean_object* v_maxExplicit_1212_, lean_object* v_i_1213_){
_start:
{
uint8_t v_res_1214_; lean_object* v_r_1215_; 
v_res_1214_ = l___private_Lean_Level_0__Lean_Level_isExplicitSubsumedAux(v_lvls_1211_, v_maxExplicit_1212_, v_i_1213_);
lean_dec(v_maxExplicit_1212_);
lean_dec_ref(v_lvls_1211_);
v_r_1215_ = lean_box(v_res_1214_);
return v_r_1215_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Level_0__Lean_Level_isExplicitSubsumed(lean_object* v_lvls_1216_, lean_object* v_firstNonExplicit_1217_){
_start:
{
lean_object* v___x_1218_; uint8_t v___x_1219_; 
v___x_1218_ = lean_unsigned_to_nat(0u);
v___x_1219_ = lean_nat_dec_eq(v_firstNonExplicit_1217_, v___x_1218_);
if (v___x_1219_ == 0)
{
lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v_max_1224_; uint8_t v___x_1225_; 
v___x_1220_ = lean_box(0);
v___x_1221_ = lean_unsigned_to_nat(1u);
v___x_1222_ = lean_nat_sub(v_firstNonExplicit_1217_, v___x_1221_);
v___x_1223_ = lean_array_get_borrowed(v___x_1220_, v_lvls_1216_, v___x_1222_);
lean_dec(v___x_1222_);
v_max_1224_ = l_Lean_Level_getOffset(v___x_1223_);
v___x_1225_ = l___private_Lean_Level_0__Lean_Level_isExplicitSubsumedAux(v_lvls_1216_, v_max_1224_, v_firstNonExplicit_1217_);
lean_dec(v_max_1224_);
return v___x_1225_;
}
else
{
uint8_t v___x_1226_; 
lean_dec(v_firstNonExplicit_1217_);
v___x_1226_ = 0;
return v___x_1226_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_isExplicitSubsumed___boxed(lean_object* v_lvls_1227_, lean_object* v_firstNonExplicit_1228_){
_start:
{
uint8_t v_res_1229_; lean_object* v_r_1230_; 
v_res_1229_ = l___private_Lean_Level_0__Lean_Level_isExplicitSubsumed(v_lvls_1227_, v_firstNonExplicit_1228_);
lean_dec_ref(v_lvls_1227_);
v_r_1230_ = lean_box(v_res_1229_);
return v_r_1230_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Level_normalize_spec__2(lean_object* v_msg_1231_){
_start:
{
lean_object* v___x_1232_; lean_object* v___x_1233_; 
v___x_1232_ = lean_box(0);
v___x_1233_ = lean_panic_fn_borrowed(v___x_1232_, v_msg_1231_);
return v___x_1233_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1_spec__1___redArg(lean_object* v_hi_1234_, lean_object* v_pivot_1235_, lean_object* v_as_1236_, lean_object* v_i_1237_, lean_object* v_k_1238_){
_start:
{
uint8_t v___x_1239_; 
v___x_1239_ = lean_nat_dec_lt(v_k_1238_, v_hi_1234_);
if (v___x_1239_ == 0)
{
lean_object* v___x_1240_; lean_object* v___x_1241_; 
lean_dec(v_k_1238_);
v___x_1240_ = lean_array_fswap(v_as_1236_, v_i_1237_, v_hi_1234_);
v___x_1241_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1241_, 0, v_i_1237_);
lean_ctor_set(v___x_1241_, 1, v___x_1240_);
return v___x_1241_;
}
else
{
lean_object* v___x_1242_; uint8_t v___x_1243_; 
v___x_1242_ = lean_array_fget_borrowed(v_as_1236_, v_k_1238_);
v___x_1243_ = l_Lean_Level_normLt(v___x_1242_, v_pivot_1235_);
if (v___x_1243_ == 0)
{
lean_object* v___x_1244_; lean_object* v___x_1245_; 
v___x_1244_ = lean_unsigned_to_nat(1u);
v___x_1245_ = lean_nat_add(v_k_1238_, v___x_1244_);
lean_dec(v_k_1238_);
v_k_1238_ = v___x_1245_;
goto _start;
}
else
{
lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; 
v___x_1247_ = lean_array_fswap(v_as_1236_, v_i_1237_, v_k_1238_);
v___x_1248_ = lean_unsigned_to_nat(1u);
v___x_1249_ = lean_nat_add(v_i_1237_, v___x_1248_);
lean_dec(v_i_1237_);
v___x_1250_ = lean_nat_add(v_k_1238_, v___x_1248_);
lean_dec(v_k_1238_);
v_as_1236_ = v___x_1247_;
v_i_1237_ = v___x_1249_;
v_k_1238_ = v___x_1250_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1_spec__1___redArg___boxed(lean_object* v_hi_1252_, lean_object* v_pivot_1253_, lean_object* v_as_1254_, lean_object* v_i_1255_, lean_object* v_k_1256_){
_start:
{
lean_object* v_res_1257_; 
v_res_1257_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1_spec__1___redArg(v_hi_1252_, v_pivot_1253_, v_as_1254_, v_i_1255_, v_k_1256_);
lean_dec(v_pivot_1253_);
lean_dec(v_hi_1252_);
return v_res_1257_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1___redArg(lean_object* v_n_1258_, lean_object* v_as_1259_, lean_object* v_lo_1260_, lean_object* v_hi_1261_){
_start:
{
lean_object* v___y_1263_; uint8_t v___x_1273_; 
v___x_1273_ = lean_nat_dec_lt(v_lo_1260_, v_hi_1261_);
if (v___x_1273_ == 0)
{
lean_dec(v_lo_1260_);
return v_as_1259_;
}
else
{
lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v_mid_1276_; lean_object* v___y_1278_; lean_object* v___y_1284_; lean_object* v___x_1289_; lean_object* v___x_1290_; uint8_t v___x_1291_; 
v___x_1274_ = lean_nat_add(v_lo_1260_, v_hi_1261_);
v___x_1275_ = lean_unsigned_to_nat(1u);
v_mid_1276_ = lean_nat_shiftr(v___x_1274_, v___x_1275_);
lean_dec(v___x_1274_);
v___x_1289_ = lean_array_fget_borrowed(v_as_1259_, v_mid_1276_);
v___x_1290_ = lean_array_fget_borrowed(v_as_1259_, v_lo_1260_);
v___x_1291_ = l_Lean_Level_normLt(v___x_1289_, v___x_1290_);
if (v___x_1291_ == 0)
{
v___y_1284_ = v_as_1259_;
goto v___jp_1283_;
}
else
{
lean_object* v___x_1292_; 
v___x_1292_ = lean_array_fswap(v_as_1259_, v_lo_1260_, v_mid_1276_);
v___y_1284_ = v___x_1292_;
goto v___jp_1283_;
}
v___jp_1277_:
{
lean_object* v___x_1279_; lean_object* v___x_1280_; uint8_t v___x_1281_; 
v___x_1279_ = lean_array_fget_borrowed(v___y_1278_, v_mid_1276_);
v___x_1280_ = lean_array_fget_borrowed(v___y_1278_, v_hi_1261_);
v___x_1281_ = l_Lean_Level_normLt(v___x_1279_, v___x_1280_);
if (v___x_1281_ == 0)
{
lean_dec(v_mid_1276_);
v___y_1263_ = v___y_1278_;
goto v___jp_1262_;
}
else
{
lean_object* v___x_1282_; 
v___x_1282_ = lean_array_fswap(v___y_1278_, v_mid_1276_, v_hi_1261_);
lean_dec(v_mid_1276_);
v___y_1263_ = v___x_1282_;
goto v___jp_1262_;
}
}
v___jp_1283_:
{
lean_object* v___x_1285_; lean_object* v___x_1286_; uint8_t v___x_1287_; 
v___x_1285_ = lean_array_fget_borrowed(v___y_1284_, v_hi_1261_);
v___x_1286_ = lean_array_fget_borrowed(v___y_1284_, v_lo_1260_);
v___x_1287_ = l_Lean_Level_normLt(v___x_1285_, v___x_1286_);
if (v___x_1287_ == 0)
{
v___y_1278_ = v___y_1284_;
goto v___jp_1277_;
}
else
{
lean_object* v___x_1288_; 
v___x_1288_ = lean_array_fswap(v___y_1284_, v_lo_1260_, v_hi_1261_);
v___y_1278_ = v___x_1288_;
goto v___jp_1277_;
}
}
}
v___jp_1262_:
{
lean_object* v_pivot_1264_; lean_object* v___x_1265_; lean_object* v_fst_1266_; lean_object* v_snd_1267_; uint8_t v___x_1268_; 
v_pivot_1264_ = lean_array_fget(v___y_1263_, v_hi_1261_);
lean_inc_n(v_lo_1260_, 2);
v___x_1265_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1_spec__1___redArg(v_hi_1261_, v_pivot_1264_, v___y_1263_, v_lo_1260_, v_lo_1260_);
lean_dec(v_pivot_1264_);
v_fst_1266_ = lean_ctor_get(v___x_1265_, 0);
lean_inc(v_fst_1266_);
v_snd_1267_ = lean_ctor_get(v___x_1265_, 1);
lean_inc(v_snd_1267_);
lean_dec_ref(v___x_1265_);
v___x_1268_ = lean_nat_dec_le(v_hi_1261_, v_fst_1266_);
if (v___x_1268_ == 0)
{
lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; 
v___x_1269_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1___redArg(v_n_1258_, v_snd_1267_, v_lo_1260_, v_fst_1266_);
v___x_1270_ = lean_unsigned_to_nat(1u);
v___x_1271_ = lean_nat_add(v_fst_1266_, v___x_1270_);
lean_dec(v_fst_1266_);
v_as_1259_ = v___x_1269_;
v_lo_1260_ = v___x_1271_;
goto _start;
}
else
{
lean_dec(v_fst_1266_);
lean_dec(v_lo_1260_);
return v_snd_1267_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1___redArg___boxed(lean_object* v_n_1293_, lean_object* v_as_1294_, lean_object* v_lo_1295_, lean_object* v_hi_1296_){
_start:
{
lean_object* v_res_1297_; 
v_res_1297_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1___redArg(v_n_1293_, v_as_1294_, v_lo_1295_, v_hi_1296_);
lean_dec(v_hi_1296_);
lean_dec(v_n_1293_);
return v_res_1297_;
}
}
static lean_object* _init_l_Lean_Level_normalize___closed__3(void){
_start:
{
lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; 
v___x_1302_ = ((lean_object*)(l_Lean_Level_normalize___closed__2));
v___x_1303_ = lean_unsigned_to_nat(11u);
v___x_1304_ = lean_unsigned_to_nat(403u);
v___x_1305_ = ((lean_object*)(l_Lean_Level_normalize___closed__1));
v___x_1306_ = ((lean_object*)(l_Lean_Level_mvarId_x21___closed__0));
v___x_1307_ = l_mkPanicMessageWithDecl(v___x_1306_, v___x_1305_, v___x_1304_, v___x_1303_, v___x_1302_);
return v___x_1307_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_normalize(lean_object* v_l_1308_){
_start:
{
uint8_t v___x_1309_; 
v___x_1309_ = l_Lean_Level_isAlreadyNormalizedCheap(v_l_1308_);
if (v___x_1309_ == 0)
{
lean_object* v_k_1310_; lean_object* v_u_1311_; 
v_k_1310_ = l_Lean_Level_getOffset(v_l_1308_);
v_u_1311_ = l_Lean_Level_getLevelOffset(v_l_1308_);
switch(lean_obj_tag(v_u_1311_))
{
case 2:
{
lean_object* v_a_1312_; lean_object* v_a_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v_lvls_1317_; lean_object* v_lvls_1318_; lean_object* v___x_1319_; lean_object* v___y_1321_; lean_object* v___y_1322_; lean_object* v___y_1329_; lean_object* v___x_1333_; lean_object* v___y_1335_; lean_object* v___y_1336_; uint8_t v___x_1338_; 
v_a_1312_ = lean_ctor_get(v_u_1311_, 0);
lean_inc(v_a_1312_);
v_a_1313_ = lean_ctor_get(v_u_1311_, 1);
lean_inc(v_a_1313_);
lean_dec_ref_known(v_u_1311_, 2);
v___x_1314_ = lean_box(0);
v___x_1315_ = lean_unsigned_to_nat(0u);
v___x_1316_ = ((lean_object*)(l_Lean_Level_normalize___closed__0));
v_lvls_1317_ = l___private_Lean_Level_0__Lean_Level_getMaxArgsAux___at___00Lean_Level_normalize_spec__0(v_a_1312_, v___x_1309_, v___x_1316_);
v_lvls_1318_ = l___private_Lean_Level_0__Lean_Level_getMaxArgsAux___at___00Lean_Level_normalize_spec__0(v_a_1313_, v___x_1309_, v_lvls_1317_);
v___x_1319_ = lean_unsigned_to_nat(1u);
v___x_1333_ = lean_array_get_size(v_lvls_1318_);
v___x_1338_ = lean_nat_dec_eq(v___x_1333_, v___x_1315_);
if (v___x_1338_ == 0)
{
lean_object* v___x_1339_; lean_object* v___y_1341_; uint8_t v___x_1343_; 
v___x_1339_ = lean_nat_sub(v___x_1333_, v___x_1319_);
v___x_1343_ = lean_nat_dec_le(v___x_1315_, v___x_1339_);
if (v___x_1343_ == 0)
{
lean_inc(v___x_1339_);
v___y_1341_ = v___x_1339_;
goto v___jp_1340_;
}
else
{
v___y_1341_ = v___x_1315_;
goto v___jp_1340_;
}
v___jp_1340_:
{
uint8_t v___x_1342_; 
v___x_1342_ = lean_nat_dec_le(v___y_1341_, v___x_1339_);
if (v___x_1342_ == 0)
{
lean_dec(v___x_1339_);
lean_inc(v___y_1341_);
v___y_1335_ = v___y_1341_;
v___y_1336_ = v___y_1341_;
goto v___jp_1334_;
}
else
{
v___y_1335_ = v___y_1341_;
v___y_1336_ = v___x_1339_;
goto v___jp_1334_;
}
}
}
else
{
v___y_1329_ = v_lvls_1318_;
goto v___jp_1328_;
}
v___jp_1320_:
{
lean_object* v_lvl_u2081_1323_; lean_object* v_prev_1324_; lean_object* v_prevK_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; 
v_lvl_u2081_1323_ = lean_array_get_borrowed(v___x_1314_, v___y_1321_, v___y_1322_);
v_prev_1324_ = l_Lean_Level_getLevelOffset(v_lvl_u2081_1323_);
v_prevK_1325_ = l_Lean_Level_getOffset(v_lvl_u2081_1323_);
v___x_1326_ = lean_nat_add(v___y_1322_, v___x_1319_);
lean_dec(v___y_1322_);
v___x_1327_ = l___private_Lean_Level_0__Lean_Level_mkMaxAux(v___y_1321_, v_k_1310_, v___x_1326_, v_prev_1324_, v_prevK_1325_, v___x_1314_);
lean_dec(v_k_1310_);
lean_dec_ref(v___y_1321_);
return v___x_1327_;
}
v___jp_1328_:
{
lean_object* v_firstNonExplicit_1330_; uint8_t v___x_1331_; 
v_firstNonExplicit_1330_ = l___private_Lean_Level_0__Lean_Level_skipExplicit(v___y_1329_, v___x_1315_);
lean_inc(v_firstNonExplicit_1330_);
v___x_1331_ = l___private_Lean_Level_0__Lean_Level_isExplicitSubsumed(v___y_1329_, v_firstNonExplicit_1330_);
if (v___x_1331_ == 0)
{
lean_object* v___x_1332_; 
v___x_1332_ = lean_nat_sub(v_firstNonExplicit_1330_, v___x_1319_);
lean_dec(v_firstNonExplicit_1330_);
v___y_1321_ = v___y_1329_;
v___y_1322_ = v___x_1332_;
goto v___jp_1320_;
}
else
{
v___y_1321_ = v___y_1329_;
v___y_1322_ = v_firstNonExplicit_1330_;
goto v___jp_1320_;
}
}
v___jp_1334_:
{
lean_object* v___x_1337_; 
v___x_1337_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1___redArg(v___x_1333_, v_lvls_1318_, v___y_1335_, v___y_1336_);
lean_dec(v___y_1336_);
v___y_1329_ = v___x_1337_;
goto v___jp_1328_;
}
}
case 3:
{
lean_object* v_a_1344_; lean_object* v_a_1345_; uint8_t v___x_1346_; 
v_a_1344_ = lean_ctor_get(v_u_1311_, 0);
lean_inc(v_a_1344_);
v_a_1345_ = lean_ctor_get(v_u_1311_, 1);
lean_inc(v_a_1345_);
lean_dec_ref_known(v_u_1311_, 2);
v___x_1346_ = l_Lean_Level_isNeverZero(v_a_1345_);
if (v___x_1346_ == 0)
{
lean_object* v_l_u2081_1347_; lean_object* v_l_u2082_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; 
v_l_u2081_1347_ = l_Lean_Level_normalize(v_a_1344_);
lean_dec(v_a_1344_);
v_l_u2082_1348_ = l_Lean_Level_normalize(v_a_1345_);
lean_dec(v_a_1345_);
v___x_1349_ = l___private_Lean_Level_0__Lean_Level_mkIMaxAux(v_l_u2081_1347_, v_l_u2082_1348_);
v___x_1350_ = l_Lean_Level_addOffsetAux(v_k_1310_, v___x_1349_);
return v___x_1350_;
}
else
{
lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; 
v___x_1351_ = l_Lean_Level_max___override(v_a_1344_, v_a_1345_);
v___x_1352_ = l_Lean_Level_normalize(v___x_1351_);
lean_dec(v___x_1351_);
v___x_1353_ = l_Lean_Level_addOffsetAux(v_k_1310_, v___x_1352_);
return v___x_1353_;
}
}
default: 
{
lean_object* v___x_1354_; lean_object* v___x_1355_; 
lean_dec(v_u_1311_);
lean_dec(v_k_1310_);
v___x_1354_ = lean_obj_once(&l_Lean_Level_normalize___closed__3, &l_Lean_Level_normalize___closed__3_once, _init_l_Lean_Level_normalize___closed__3);
v___x_1355_ = l_panic___at___00Lean_Level_normalize_spec__2(v___x_1354_);
return v___x_1355_;
}
}
}
else
{
lean_inc(v_l_1308_);
return v_l_1308_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_getMaxArgsAux___at___00Lean_Level_normalize_spec__0(lean_object* v_x_1356_, uint8_t v_x_1357_, lean_object* v_x_1358_){
_start:
{
if (lean_obj_tag(v_x_1356_) == 2)
{
lean_object* v_a_1359_; lean_object* v_a_1360_; lean_object* v___x_1361_; 
v_a_1359_ = lean_ctor_get(v_x_1356_, 0);
lean_inc(v_a_1359_);
v_a_1360_ = lean_ctor_get(v_x_1356_, 1);
lean_inc(v_a_1360_);
lean_dec_ref_known(v_x_1356_, 2);
v___x_1361_ = l___private_Lean_Level_0__Lean_Level_getMaxArgsAux___at___00Lean_Level_normalize_spec__0(v_a_1359_, v_x_1357_, v_x_1358_);
v_x_1356_ = v_a_1360_;
v_x_1358_ = v___x_1361_;
goto _start;
}
else
{
if (v_x_1357_ == 0)
{
lean_object* v___x_1363_; uint8_t v___x_1364_; 
v___x_1363_ = l_Lean_Level_normalize(v_x_1356_);
lean_dec(v_x_1356_);
v___x_1364_ = 1;
v_x_1356_ = v___x_1363_;
v_x_1357_ = v___x_1364_;
goto _start;
}
else
{
lean_object* v___x_1366_; 
v___x_1366_ = lean_array_push(v_x_1358_, v_x_1356_);
return v___x_1366_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_getMaxArgsAux___at___00Lean_Level_normalize_spec__0___boxed(lean_object* v_x_1367_, lean_object* v_x_1368_, lean_object* v_x_1369_){
_start:
{
uint8_t v_x_483__boxed_1370_; lean_object* v_res_1371_; 
v_x_483__boxed_1370_ = lean_unbox(v_x_1368_);
v_res_1371_ = l___private_Lean_Level_0__Lean_Level_getMaxArgsAux___at___00Lean_Level_normalize_spec__0(v_x_1367_, v_x_483__boxed_1370_, v_x_1369_);
return v_res_1371_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_normalize___boxed(lean_object* v_l_1372_){
_start:
{
lean_object* v_res_1373_; 
v_res_1373_ = l_Lean_Level_normalize(v_l_1372_);
lean_dec(v_l_1372_);
return v_res_1373_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1(lean_object* v_n_1374_, lean_object* v_as_1375_, lean_object* v_lo_1376_, lean_object* v_hi_1377_, lean_object* v_w_1378_, lean_object* v_hlo_1379_, lean_object* v_hhi_1380_){
_start:
{
lean_object* v___x_1381_; 
v___x_1381_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1___redArg(v_n_1374_, v_as_1375_, v_lo_1376_, v_hi_1377_);
return v___x_1381_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1___boxed(lean_object* v_n_1382_, lean_object* v_as_1383_, lean_object* v_lo_1384_, lean_object* v_hi_1385_, lean_object* v_w_1386_, lean_object* v_hlo_1387_, lean_object* v_hhi_1388_){
_start:
{
lean_object* v_res_1389_; 
v_res_1389_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1(v_n_1382_, v_as_1383_, v_lo_1384_, v_hi_1385_, v_w_1386_, v_hlo_1387_, v_hhi_1388_);
lean_dec(v_hi_1385_);
lean_dec(v_n_1382_);
return v_res_1389_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1_spec__1(lean_object* v_n_1390_, lean_object* v_lo_1391_, lean_object* v_hi_1392_, lean_object* v_hhi_1393_, lean_object* v_pivot_1394_, lean_object* v_as_1395_, lean_object* v_i_1396_, lean_object* v_k_1397_, lean_object* v_ilo_1398_, lean_object* v_ik_1399_, lean_object* v_w_1400_){
_start:
{
lean_object* v___x_1401_; 
v___x_1401_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1_spec__1___redArg(v_hi_1392_, v_pivot_1394_, v_as_1395_, v_i_1396_, v_k_1397_);
return v___x_1401_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1_spec__1___boxed(lean_object* v_n_1402_, lean_object* v_lo_1403_, lean_object* v_hi_1404_, lean_object* v_hhi_1405_, lean_object* v_pivot_1406_, lean_object* v_as_1407_, lean_object* v_i_1408_, lean_object* v_k_1409_, lean_object* v_ilo_1410_, lean_object* v_ik_1411_, lean_object* v_w_1412_){
_start:
{
lean_object* v_res_1413_; 
v_res_1413_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1_spec__1(v_n_1402_, v_lo_1403_, v_hi_1404_, v_hhi_1405_, v_pivot_1406_, v_as_1407_, v_i_1408_, v_k_1409_, v_ilo_1410_, v_ik_1411_, v_w_1412_);
lean_dec(v_pivot_1406_);
lean_dec(v_hi_1404_);
lean_dec(v_lo_1403_);
lean_dec(v_n_1402_);
return v_res_1413_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_isEquiv(lean_object* v_u_1414_, lean_object* v_v_1415_){
_start:
{
uint8_t v___x_1416_; 
v___x_1416_ = lean_level_eq(v_u_1414_, v_v_1415_);
if (v___x_1416_ == 0)
{
lean_object* v___x_1417_; lean_object* v___x_1418_; uint8_t v___x_1419_; 
v___x_1417_ = l_Lean_Level_normalize(v_u_1414_);
v___x_1418_ = l_Lean_Level_normalize(v_v_1415_);
v___x_1419_ = lean_level_eq(v___x_1417_, v___x_1418_);
lean_dec(v___x_1418_);
lean_dec(v___x_1417_);
return v___x_1419_;
}
else
{
return v___x_1416_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_isEquiv___boxed(lean_object* v_u_1420_, lean_object* v_v_1421_){
_start:
{
uint8_t v_res_1422_; lean_object* v_r_1423_; 
v_res_1422_ = l_Lean_Level_isEquiv(v_u_1420_, v_v_1421_);
lean_dec(v_v_1421_);
lean_dec(v_u_1420_);
v_r_1423_ = lean_box(v_res_1422_);
return v_r_1423_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_dec(lean_object* v_x_1424_){
_start:
{
lean_object* v_l_u2081_1426_; lean_object* v_l_u2082_1427_; 
switch(lean_obj_tag(v_x_1424_))
{
case 0:
{
lean_object* v___x_1440_; 
v___x_1440_ = lean_box(0);
return v___x_1440_;
}
case 1:
{
lean_object* v_a_1441_; lean_object* v___x_1442_; 
v_a_1441_ = lean_ctor_get(v_x_1424_, 0);
lean_inc(v_a_1441_);
v___x_1442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1442_, 0, v_a_1441_);
return v___x_1442_;
}
case 2:
{
lean_object* v_a_1443_; lean_object* v_a_1444_; 
v_a_1443_ = lean_ctor_get(v_x_1424_, 0);
v_a_1444_ = lean_ctor_get(v_x_1424_, 1);
v_l_u2081_1426_ = v_a_1443_;
v_l_u2082_1427_ = v_a_1444_;
goto v___jp_1425_;
}
case 3:
{
lean_object* v_a_1445_; lean_object* v_a_1446_; 
v_a_1445_ = lean_ctor_get(v_x_1424_, 0);
v_a_1446_ = lean_ctor_get(v_x_1424_, 1);
v_l_u2081_1426_ = v_a_1445_;
v_l_u2082_1427_ = v_a_1446_;
goto v___jp_1425_;
}
default: 
{
lean_object* v___x_1447_; 
v___x_1447_ = lean_box(0);
return v___x_1447_;
}
}
v___jp_1425_:
{
lean_object* v___x_1428_; 
v___x_1428_ = l_Lean_Level_dec(v_l_u2081_1426_);
if (lean_obj_tag(v___x_1428_) == 0)
{
return v___x_1428_;
}
else
{
lean_object* v_val_1429_; lean_object* v___x_1430_; 
v_val_1429_ = lean_ctor_get(v___x_1428_, 0);
lean_inc(v_val_1429_);
lean_dec_ref_known(v___x_1428_, 1);
v___x_1430_ = l_Lean_Level_dec(v_l_u2082_1427_);
if (lean_obj_tag(v___x_1430_) == 0)
{
lean_dec(v_val_1429_);
return v___x_1430_;
}
else
{
lean_object* v_val_1431_; lean_object* v___x_1433_; uint8_t v_isShared_1434_; uint8_t v_isSharedCheck_1439_; 
v_val_1431_ = lean_ctor_get(v___x_1430_, 0);
v_isSharedCheck_1439_ = !lean_is_exclusive(v___x_1430_);
if (v_isSharedCheck_1439_ == 0)
{
v___x_1433_ = v___x_1430_;
v_isShared_1434_ = v_isSharedCheck_1439_;
goto v_resetjp_1432_;
}
else
{
lean_inc(v_val_1431_);
lean_dec(v___x_1430_);
v___x_1433_ = lean_box(0);
v_isShared_1434_ = v_isSharedCheck_1439_;
goto v_resetjp_1432_;
}
v_resetjp_1432_:
{
lean_object* v___x_1435_; lean_object* v___x_1437_; 
v___x_1435_ = l_Lean_Level_max___override(v_val_1429_, v_val_1431_);
if (v_isShared_1434_ == 0)
{
lean_ctor_set(v___x_1433_, 0, v___x_1435_);
v___x_1437_ = v___x_1433_;
goto v_reusejp_1436_;
}
else
{
lean_object* v_reuseFailAlloc_1438_; 
v_reuseFailAlloc_1438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1438_, 0, v___x_1435_);
v___x_1437_ = v_reuseFailAlloc_1438_;
goto v_reusejp_1436_;
}
v_reusejp_1436_:
{
return v___x_1437_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_dec___boxed(lean_object* v_x_1448_){
_start:
{
lean_object* v_res_1449_; 
v_res_1449_ = l_Lean_Level_dec(v_x_1448_);
lean_dec(v_x_1448_);
return v_res_1449_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_ctorIdx(lean_object* v_x_1450_){
_start:
{
switch(lean_obj_tag(v_x_1450_))
{
case 0:
{
lean_object* v___x_1451_; 
v___x_1451_ = lean_unsigned_to_nat(0u);
return v___x_1451_;
}
case 1:
{
lean_object* v___x_1452_; 
v___x_1452_ = lean_unsigned_to_nat(1u);
return v___x_1452_;
}
case 2:
{
lean_object* v___x_1453_; 
v___x_1453_ = lean_unsigned_to_nat(2u);
return v___x_1453_;
}
case 3:
{
lean_object* v___x_1454_; 
v___x_1454_ = lean_unsigned_to_nat(3u);
return v___x_1454_;
}
default: 
{
lean_object* v___x_1455_; 
v___x_1455_ = lean_unsigned_to_nat(4u);
return v___x_1455_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_ctorIdx___boxed(lean_object* v_x_1456_){
_start:
{
lean_object* v_res_1457_; 
v_res_1457_ = l_Lean_Level_PP_Result_ctorIdx(v_x_1456_);
lean_dec_ref(v_x_1456_);
return v_res_1457_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_ctorElim___redArg(lean_object* v_t_1458_, lean_object* v_k_1459_){
_start:
{
if (lean_obj_tag(v_t_1458_) == 2)
{
lean_object* v_a_1460_; lean_object* v_a_1461_; lean_object* v___x_1462_; 
v_a_1460_ = lean_ctor_get(v_t_1458_, 0);
lean_inc_ref(v_a_1460_);
v_a_1461_ = lean_ctor_get(v_t_1458_, 1);
lean_inc(v_a_1461_);
lean_dec_ref_known(v_t_1458_, 2);
v___x_1462_ = lean_apply_2(v_k_1459_, v_a_1460_, v_a_1461_);
return v___x_1462_;
}
else
{
lean_object* v_a_1463_; lean_object* v___x_1464_; 
v_a_1463_ = lean_ctor_get(v_t_1458_, 0);
lean_inc(v_a_1463_);
lean_dec_ref(v_t_1458_);
v___x_1464_ = lean_apply_1(v_k_1459_, v_a_1463_);
return v___x_1464_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_ctorElim(lean_object* v_motive__1_1465_, lean_object* v_ctorIdx_1466_, lean_object* v_t_1467_, lean_object* v_h_1468_, lean_object* v_k_1469_){
_start:
{
lean_object* v___x_1470_; 
v___x_1470_ = l_Lean_Level_PP_Result_ctorElim___redArg(v_t_1467_, v_k_1469_);
return v___x_1470_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_ctorElim___boxed(lean_object* v_motive__1_1471_, lean_object* v_ctorIdx_1472_, lean_object* v_t_1473_, lean_object* v_h_1474_, lean_object* v_k_1475_){
_start:
{
lean_object* v_res_1476_; 
v_res_1476_ = l_Lean_Level_PP_Result_ctorElim(v_motive__1_1471_, v_ctorIdx_1472_, v_t_1473_, v_h_1474_, v_k_1475_);
lean_dec(v_ctorIdx_1472_);
return v_res_1476_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_leaf_elim___redArg(lean_object* v_t_1477_, lean_object* v_leaf_1478_){
_start:
{
lean_object* v___x_1479_; 
v___x_1479_ = l_Lean_Level_PP_Result_ctorElim___redArg(v_t_1477_, v_leaf_1478_);
return v___x_1479_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_leaf_elim(lean_object* v_motive__1_1480_, lean_object* v_t_1481_, lean_object* v_h_1482_, lean_object* v_leaf_1483_){
_start:
{
lean_object* v___x_1484_; 
v___x_1484_ = l_Lean_Level_PP_Result_ctorElim___redArg(v_t_1481_, v_leaf_1483_);
return v___x_1484_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_num_elim___redArg(lean_object* v_t_1485_, lean_object* v_num_1486_){
_start:
{
lean_object* v___x_1487_; 
v___x_1487_ = l_Lean_Level_PP_Result_ctorElim___redArg(v_t_1485_, v_num_1486_);
return v___x_1487_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_num_elim(lean_object* v_motive__1_1488_, lean_object* v_t_1489_, lean_object* v_h_1490_, lean_object* v_num_1491_){
_start:
{
lean_object* v___x_1492_; 
v___x_1492_ = l_Lean_Level_PP_Result_ctorElim___redArg(v_t_1489_, v_num_1491_);
return v___x_1492_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_offset_elim___redArg(lean_object* v_t_1493_, lean_object* v_offset_1494_){
_start:
{
lean_object* v___x_1495_; 
v___x_1495_ = l_Lean_Level_PP_Result_ctorElim___redArg(v_t_1493_, v_offset_1494_);
return v___x_1495_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_offset_elim(lean_object* v_motive__1_1496_, lean_object* v_t_1497_, lean_object* v_h_1498_, lean_object* v_offset_1499_){
_start:
{
lean_object* v___x_1500_; 
v___x_1500_ = l_Lean_Level_PP_Result_ctorElim___redArg(v_t_1497_, v_offset_1499_);
return v___x_1500_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_maxNode_elim___redArg(lean_object* v_t_1501_, lean_object* v_maxNode_1502_){
_start:
{
lean_object* v___x_1503_; 
v___x_1503_ = l_Lean_Level_PP_Result_ctorElim___redArg(v_t_1501_, v_maxNode_1502_);
return v___x_1503_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_maxNode_elim(lean_object* v_motive__1_1504_, lean_object* v_t_1505_, lean_object* v_h_1506_, lean_object* v_maxNode_1507_){
_start:
{
lean_object* v___x_1508_; 
v___x_1508_ = l_Lean_Level_PP_Result_ctorElim___redArg(v_t_1505_, v_maxNode_1507_);
return v___x_1508_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_imaxNode_elim___redArg(lean_object* v_t_1509_, lean_object* v_imaxNode_1510_){
_start:
{
lean_object* v___x_1511_; 
v___x_1511_ = l_Lean_Level_PP_Result_ctorElim___redArg(v_t_1509_, v_imaxNode_1510_);
return v___x_1511_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_imaxNode_elim(lean_object* v_motive__1_1512_, lean_object* v_t_1513_, lean_object* v_h_1514_, lean_object* v_imaxNode_1515_){
_start:
{
lean_object* v___x_1516_; 
v___x_1516_ = l_Lean_Level_PP_Result_ctorElim___redArg(v_t_1513_, v_imaxNode_1515_);
return v___x_1516_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_succ(lean_object* v_x_1517_){
_start:
{
switch(lean_obj_tag(v_x_1517_))
{
case 2:
{
lean_object* v_a_1518_; lean_object* v_a_1519_; lean_object* v___x_1521_; uint8_t v_isShared_1522_; uint8_t v_isSharedCheck_1528_; 
v_a_1518_ = lean_ctor_get(v_x_1517_, 0);
v_a_1519_ = lean_ctor_get(v_x_1517_, 1);
v_isSharedCheck_1528_ = !lean_is_exclusive(v_x_1517_);
if (v_isSharedCheck_1528_ == 0)
{
v___x_1521_ = v_x_1517_;
v_isShared_1522_ = v_isSharedCheck_1528_;
goto v_resetjp_1520_;
}
else
{
lean_inc(v_a_1519_);
lean_inc(v_a_1518_);
lean_dec(v_x_1517_);
v___x_1521_ = lean_box(0);
v_isShared_1522_ = v_isSharedCheck_1528_;
goto v_resetjp_1520_;
}
v_resetjp_1520_:
{
lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1526_; 
v___x_1523_ = lean_unsigned_to_nat(1u);
v___x_1524_ = lean_nat_add(v_a_1519_, v___x_1523_);
lean_dec(v_a_1519_);
if (v_isShared_1522_ == 0)
{
lean_ctor_set(v___x_1521_, 1, v___x_1524_);
v___x_1526_ = v___x_1521_;
goto v_reusejp_1525_;
}
else
{
lean_object* v_reuseFailAlloc_1527_; 
v_reuseFailAlloc_1527_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1527_, 0, v_a_1518_);
lean_ctor_set(v_reuseFailAlloc_1527_, 1, v___x_1524_);
v___x_1526_ = v_reuseFailAlloc_1527_;
goto v_reusejp_1525_;
}
v_reusejp_1525_:
{
return v___x_1526_;
}
}
}
case 1:
{
lean_object* v_a_1529_; lean_object* v___x_1531_; uint8_t v_isShared_1532_; uint8_t v_isSharedCheck_1538_; 
v_a_1529_ = lean_ctor_get(v_x_1517_, 0);
v_isSharedCheck_1538_ = !lean_is_exclusive(v_x_1517_);
if (v_isSharedCheck_1538_ == 0)
{
v___x_1531_ = v_x_1517_;
v_isShared_1532_ = v_isSharedCheck_1538_;
goto v_resetjp_1530_;
}
else
{
lean_inc(v_a_1529_);
lean_dec(v_x_1517_);
v___x_1531_ = lean_box(0);
v_isShared_1532_ = v_isSharedCheck_1538_;
goto v_resetjp_1530_;
}
v_resetjp_1530_:
{
lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1536_; 
v___x_1533_ = lean_unsigned_to_nat(1u);
v___x_1534_ = lean_nat_add(v_a_1529_, v___x_1533_);
lean_dec(v_a_1529_);
if (v_isShared_1532_ == 0)
{
lean_ctor_set(v___x_1531_, 0, v___x_1534_);
v___x_1536_ = v___x_1531_;
goto v_reusejp_1535_;
}
else
{
lean_object* v_reuseFailAlloc_1537_; 
v_reuseFailAlloc_1537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1537_, 0, v___x_1534_);
v___x_1536_ = v_reuseFailAlloc_1537_;
goto v_reusejp_1535_;
}
v_reusejp_1535_:
{
return v___x_1536_;
}
}
}
default: 
{
lean_object* v___x_1539_; lean_object* v___x_1540_; 
v___x_1539_ = lean_unsigned_to_nat(1u);
v___x_1540_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1540_, 0, v_x_1517_);
lean_ctor_set(v___x_1540_, 1, v___x_1539_);
return v___x_1540_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_max(lean_object* v_x_1541_, lean_object* v_x_1542_){
_start:
{
if (lean_obj_tag(v_x_1542_) == 3)
{
lean_object* v_a_1543_; lean_object* v___x_1545_; uint8_t v_isShared_1546_; uint8_t v_isSharedCheck_1551_; 
v_a_1543_ = lean_ctor_get(v_x_1542_, 0);
v_isSharedCheck_1551_ = !lean_is_exclusive(v_x_1542_);
if (v_isSharedCheck_1551_ == 0)
{
v___x_1545_ = v_x_1542_;
v_isShared_1546_ = v_isSharedCheck_1551_;
goto v_resetjp_1544_;
}
else
{
lean_inc(v_a_1543_);
lean_dec(v_x_1542_);
v___x_1545_ = lean_box(0);
v_isShared_1546_ = v_isSharedCheck_1551_;
goto v_resetjp_1544_;
}
v_resetjp_1544_:
{
lean_object* v___x_1547_; lean_object* v___x_1549_; 
v___x_1547_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1547_, 0, v_x_1541_);
lean_ctor_set(v___x_1547_, 1, v_a_1543_);
if (v_isShared_1546_ == 0)
{
lean_ctor_set(v___x_1545_, 0, v___x_1547_);
v___x_1549_ = v___x_1545_;
goto v_reusejp_1548_;
}
else
{
lean_object* v_reuseFailAlloc_1550_; 
v_reuseFailAlloc_1550_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1550_, 0, v___x_1547_);
v___x_1549_ = v_reuseFailAlloc_1550_;
goto v_reusejp_1548_;
}
v_reusejp_1548_:
{
return v___x_1549_;
}
}
}
else
{
lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; 
v___x_1552_ = lean_box(0);
v___x_1553_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1553_, 0, v_x_1542_);
lean_ctor_set(v___x_1553_, 1, v___x_1552_);
v___x_1554_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1554_, 0, v_x_1541_);
lean_ctor_set(v___x_1554_, 1, v___x_1553_);
v___x_1555_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1555_, 0, v___x_1554_);
return v___x_1555_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_imax(lean_object* v_x_1556_, lean_object* v_x_1557_){
_start:
{
if (lean_obj_tag(v_x_1557_) == 4)
{
lean_object* v_a_1558_; lean_object* v___x_1560_; uint8_t v_isShared_1561_; uint8_t v_isSharedCheck_1566_; 
v_a_1558_ = lean_ctor_get(v_x_1557_, 0);
v_isSharedCheck_1566_ = !lean_is_exclusive(v_x_1557_);
if (v_isSharedCheck_1566_ == 0)
{
v___x_1560_ = v_x_1557_;
v_isShared_1561_ = v_isSharedCheck_1566_;
goto v_resetjp_1559_;
}
else
{
lean_inc(v_a_1558_);
lean_dec(v_x_1557_);
v___x_1560_ = lean_box(0);
v_isShared_1561_ = v_isSharedCheck_1566_;
goto v_resetjp_1559_;
}
v_resetjp_1559_:
{
lean_object* v___x_1562_; lean_object* v___x_1564_; 
v___x_1562_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1562_, 0, v_x_1556_);
lean_ctor_set(v___x_1562_, 1, v_a_1558_);
if (v_isShared_1561_ == 0)
{
lean_ctor_set(v___x_1560_, 0, v___x_1562_);
v___x_1564_ = v___x_1560_;
goto v_reusejp_1563_;
}
else
{
lean_object* v_reuseFailAlloc_1565_; 
v_reuseFailAlloc_1565_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1565_, 0, v___x_1562_);
v___x_1564_ = v_reuseFailAlloc_1565_;
goto v_reusejp_1563_;
}
v_reusejp_1563_:
{
return v___x_1564_;
}
}
}
else
{
lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; 
v___x_1567_ = lean_box(0);
v___x_1568_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1568_, 0, v_x_1557_);
lean_ctor_set(v___x_1568_, 1, v___x_1567_);
v___x_1569_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1569_, 0, v_x_1556_);
lean_ctor_set(v___x_1569_, 1, v___x_1568_);
v___x_1570_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1570_, 0, v___x_1569_);
return v___x_1570_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_toResult(lean_object* v_l_1589_, lean_object* v_a_1590_){
_start:
{
switch(lean_obj_tag(v_l_1589_))
{
case 0:
{
lean_object* v___x_1591_; 
v___x_1591_ = ((lean_object*)(l_Lean_Level_PP_toResult___closed__0));
return v___x_1591_;
}
case 1:
{
lean_object* v_a_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; 
v_a_1592_ = lean_ctor_get(v_l_1589_, 0);
lean_inc(v_a_1592_);
lean_dec_ref_known(v_l_1589_, 1);
v___x_1593_ = l_Lean_Level_PP_toResult(v_a_1592_, v_a_1590_);
v___x_1594_ = l_Lean_Level_PP_Result_succ(v___x_1593_);
return v___x_1594_;
}
case 2:
{
lean_object* v_a_1595_; lean_object* v_a_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; 
v_a_1595_ = lean_ctor_get(v_l_1589_, 0);
lean_inc(v_a_1595_);
v_a_1596_ = lean_ctor_get(v_l_1589_, 1);
lean_inc(v_a_1596_);
lean_dec_ref_known(v_l_1589_, 2);
v___x_1597_ = l_Lean_Level_PP_toResult(v_a_1595_, v_a_1590_);
v___x_1598_ = l_Lean_Level_PP_toResult(v_a_1596_, v_a_1590_);
v___x_1599_ = l_Lean_Level_PP_Result_max(v___x_1597_, v___x_1598_);
return v___x_1599_;
}
case 3:
{
lean_object* v_a_1600_; lean_object* v_a_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; 
v_a_1600_ = lean_ctor_get(v_l_1589_, 0);
lean_inc(v_a_1600_);
v_a_1601_ = lean_ctor_get(v_l_1589_, 1);
lean_inc(v_a_1601_);
lean_dec_ref_known(v_l_1589_, 2);
v___x_1602_ = l_Lean_Level_PP_toResult(v_a_1600_, v_a_1590_);
v___x_1603_ = l_Lean_Level_PP_toResult(v_a_1601_, v_a_1590_);
v___x_1604_ = l_Lean_Level_PP_Result_imax(v___x_1602_, v___x_1603_);
return v___x_1604_;
}
case 4:
{
lean_object* v_a_1605_; lean_object* v___x_1606_; 
v_a_1605_ = lean_ctor_get(v_l_1589_, 0);
lean_inc(v_a_1605_);
lean_dec_ref_known(v_l_1589_, 1);
v___x_1606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1606_, 0, v_a_1605_);
return v___x_1606_;
}
default: 
{
uint8_t v_mvars_1607_; 
v_mvars_1607_ = lean_ctor_get_uint8(v_a_1590_, sizeof(void*)*1);
if (v_mvars_1607_ == 0)
{
lean_object* v___x_1608_; 
lean_dec_ref_known(v_l_1589_, 1);
v___x_1608_ = ((lean_object*)(l_Lean_Level_PP_toResult___closed__3));
return v___x_1608_;
}
else
{
lean_object* v_a_1609_; lean_object* v_lIndex_x3f_1610_; lean_object* v___x_1611_; 
v_a_1609_ = lean_ctor_get(v_l_1589_, 0);
lean_inc_n(v_a_1609_, 2);
lean_dec_ref_known(v_l_1589_, 1);
v_lIndex_x3f_1610_ = lean_ctor_get(v_a_1590_, 0);
lean_inc_ref(v_lIndex_x3f_1610_);
v___x_1611_ = lean_apply_1(v_lIndex_x3f_1610_, v_a_1609_);
if (lean_obj_tag(v___x_1611_) == 1)
{
lean_object* v_val_1612_; lean_object* v___x_1614_; uint8_t v_isShared_1615_; uint8_t v_isSharedCheck_1623_; 
lean_dec(v_a_1609_);
v_val_1612_ = lean_ctor_get(v___x_1611_, 0);
v_isSharedCheck_1623_ = !lean_is_exclusive(v___x_1611_);
if (v_isSharedCheck_1623_ == 0)
{
v___x_1614_ = v___x_1611_;
v_isShared_1615_ = v_isSharedCheck_1623_;
goto v_resetjp_1613_;
}
else
{
lean_inc(v_val_1612_);
lean_dec(v___x_1611_);
v___x_1614_ = lean_box(0);
v_isShared_1615_ = v_isSharedCheck_1623_;
goto v_resetjp_1613_;
}
v_resetjp_1613_:
{
lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1621_; 
v___x_1616_ = ((lean_object*)(l_Lean_Level_PP_toResult___closed__5));
v___x_1617_ = lean_unsigned_to_nat(1u);
v___x_1618_ = lean_nat_add(v_val_1612_, v___x_1617_);
lean_dec(v_val_1612_);
v___x_1619_ = l_Lean_Name_num___override(v___x_1616_, v___x_1618_);
if (v_isShared_1615_ == 0)
{
lean_ctor_set_tag(v___x_1614_, 0);
lean_ctor_set(v___x_1614_, 0, v___x_1619_);
v___x_1621_ = v___x_1614_;
goto v_reusejp_1620_;
}
else
{
lean_object* v_reuseFailAlloc_1622_; 
v_reuseFailAlloc_1622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1622_, 0, v___x_1619_);
v___x_1621_ = v_reuseFailAlloc_1622_;
goto v_reusejp_1620_;
}
v_reusejp_1620_:
{
return v___x_1621_;
}
}
}
else
{
lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; 
lean_dec(v___x_1611_);
v___x_1624_ = ((lean_object*)(l_Lean_Level_PP_toResult___closed__7));
v___x_1625_ = ((lean_object*)(l_Lean_Level_PP_toResult___closed__9));
v___x_1626_ = l_Lean_Name_replacePrefix(v_a_1609_, v___x_1624_, v___x_1625_);
v___x_1627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1627_, 0, v___x_1626_);
return v___x_1627_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_toResult___boxed(lean_object* v_l_1628_, lean_object* v_a_1629_){
_start:
{
lean_object* v_res_1630_; 
v_res_1630_ = l_Lean_Level_PP_toResult(v_l_1628_, v_a_1629_);
lean_dec_ref(v_a_1629_);
return v_res_1630_;
}
}
static lean_object* _init_l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__1(void){
_start:
{
lean_object* v___x_1632_; lean_object* v___x_1633_; 
v___x_1632_ = ((lean_object*)(l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__0));
v___x_1633_ = lean_string_length(v___x_1632_);
return v___x_1633_;
}
}
static lean_object* _init_l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__2(void){
_start:
{
lean_object* v___x_1634_; lean_object* v___x_1635_; 
v___x_1634_ = lean_obj_once(&l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__1, &l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__1_once, _init_l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__1);
v___x_1635_ = lean_nat_to_int(v___x_1634_);
return v___x_1635_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse(lean_object* v_x_1640_, uint8_t v_x_1641_){
_start:
{
if (v_x_1641_ == 0)
{
lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; uint8_t v___x_1648_; lean_object* v___x_1649_; 
v___x_1642_ = lean_obj_once(&l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__2, &l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__2_once, _init_l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__2);
v___x_1643_ = ((lean_object*)(l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__3));
v___x_1644_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1644_, 0, v___x_1643_);
lean_ctor_set(v___x_1644_, 1, v_x_1640_);
v___x_1645_ = ((lean_object*)(l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__4));
v___x_1646_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1646_, 0, v___x_1644_);
lean_ctor_set(v___x_1646_, 1, v___x_1645_);
v___x_1647_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1647_, 0, v___x_1642_);
lean_ctor_set(v___x_1647_, 1, v___x_1646_);
v___x_1648_ = 0;
v___x_1649_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1649_, 0, v___x_1647_);
lean_ctor_set_uint8(v___x_1649_, sizeof(void*)*1, v___x_1648_);
return v___x_1649_;
}
else
{
return v_x_1640_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___boxed(lean_object* v_x_1650_, lean_object* v_x_1651_){
_start:
{
uint8_t v_x_57__boxed_1652_; lean_object* v_res_1653_; 
v_x_57__boxed_1652_ = lean_unbox(v_x_1651_);
v_res_1653_ = l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse(v_x_1650_, v_x_57__boxed_1652_);
return v_res_1653_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_format(lean_object* v_x_1663_, uint8_t v_x_1664_){
_start:
{
switch(lean_obj_tag(v_x_1663_))
{
case 0:
{
lean_object* v_a_1665_; lean_object* v___x_1667_; uint8_t v_isShared_1668_; uint8_t v_isSharedCheck_1674_; 
v_a_1665_ = lean_ctor_get(v_x_1663_, 0);
v_isSharedCheck_1674_ = !lean_is_exclusive(v_x_1663_);
if (v_isSharedCheck_1674_ == 0)
{
v___x_1667_ = v_x_1663_;
v_isShared_1668_ = v_isSharedCheck_1674_;
goto v_resetjp_1666_;
}
else
{
lean_inc(v_a_1665_);
lean_dec(v_x_1663_);
v___x_1667_ = lean_box(0);
v_isShared_1668_ = v_isSharedCheck_1674_;
goto v_resetjp_1666_;
}
v_resetjp_1666_:
{
uint8_t v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1672_; 
v___x_1669_ = 1;
v___x_1670_ = l_Lean_Name_toString(v_a_1665_, v___x_1669_);
if (v_isShared_1668_ == 0)
{
lean_ctor_set_tag(v___x_1667_, 3);
lean_ctor_set(v___x_1667_, 0, v___x_1670_);
v___x_1672_ = v___x_1667_;
goto v_reusejp_1671_;
}
else
{
lean_object* v_reuseFailAlloc_1673_; 
v_reuseFailAlloc_1673_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1673_, 0, v___x_1670_);
v___x_1672_ = v_reuseFailAlloc_1673_;
goto v_reusejp_1671_;
}
v_reusejp_1671_:
{
return v___x_1672_;
}
}
}
case 1:
{
lean_object* v_a_1675_; lean_object* v___x_1677_; uint8_t v_isShared_1678_; uint8_t v_isSharedCheck_1683_; 
v_a_1675_ = lean_ctor_get(v_x_1663_, 0);
v_isSharedCheck_1683_ = !lean_is_exclusive(v_x_1663_);
if (v_isSharedCheck_1683_ == 0)
{
v___x_1677_ = v_x_1663_;
v_isShared_1678_ = v_isSharedCheck_1683_;
goto v_resetjp_1676_;
}
else
{
lean_inc(v_a_1675_);
lean_dec(v_x_1663_);
v___x_1677_ = lean_box(0);
v_isShared_1678_ = v_isSharedCheck_1683_;
goto v_resetjp_1676_;
}
v_resetjp_1676_:
{
lean_object* v___x_1679_; lean_object* v___x_1681_; 
v___x_1679_ = l_Nat_reprFast(v_a_1675_);
if (v_isShared_1678_ == 0)
{
lean_ctor_set_tag(v___x_1677_, 3);
lean_ctor_set(v___x_1677_, 0, v___x_1679_);
v___x_1681_ = v___x_1677_;
goto v_reusejp_1680_;
}
else
{
lean_object* v_reuseFailAlloc_1682_; 
v_reuseFailAlloc_1682_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1682_, 0, v___x_1679_);
v___x_1681_ = v_reuseFailAlloc_1682_;
goto v_reusejp_1680_;
}
v_reusejp_1680_:
{
return v___x_1681_;
}
}
}
case 2:
{
lean_object* v_a_1684_; lean_object* v_a_1685_; lean_object* v___x_1687_; uint8_t v_isShared_1688_; uint8_t v_isSharedCheck_1704_; 
v_a_1684_ = lean_ctor_get(v_x_1663_, 0);
v_a_1685_ = lean_ctor_get(v_x_1663_, 1);
v_isSharedCheck_1704_ = !lean_is_exclusive(v_x_1663_);
if (v_isSharedCheck_1704_ == 0)
{
v___x_1687_ = v_x_1663_;
v_isShared_1688_ = v_isSharedCheck_1704_;
goto v_resetjp_1686_;
}
else
{
lean_inc(v_a_1685_);
lean_inc(v_a_1684_);
lean_dec(v_x_1663_);
v___x_1687_ = lean_box(0);
v_isShared_1688_ = v_isSharedCheck_1704_;
goto v_resetjp_1686_;
}
v_resetjp_1686_:
{
lean_object* v_zero_1689_; uint8_t v_isZero_1690_; 
v_zero_1689_ = lean_unsigned_to_nat(0u);
v_isZero_1690_ = lean_nat_dec_eq(v_a_1685_, v_zero_1689_);
if (v_isZero_1690_ == 1)
{
lean_del_object(v___x_1687_);
lean_dec(v_a_1685_);
v_x_1663_ = v_a_1684_;
goto _start;
}
else
{
lean_object* v_one_1692_; lean_object* v_n_1693_; lean_object* v_f_x27_1694_; lean_object* v___x_1695_; lean_object* v___x_1697_; 
v_one_1692_ = lean_unsigned_to_nat(1u);
v_n_1693_ = lean_nat_sub(v_a_1685_, v_one_1692_);
lean_dec(v_a_1685_);
v_f_x27_1694_ = l_Lean_Level_PP_Result_format(v_a_1684_, v_isZero_1690_);
v___x_1695_ = ((lean_object*)(l_Lean_Level_PP_Result_format___closed__1));
if (v_isShared_1688_ == 0)
{
lean_ctor_set_tag(v___x_1687_, 5);
lean_ctor_set(v___x_1687_, 1, v___x_1695_);
lean_ctor_set(v___x_1687_, 0, v_f_x27_1694_);
v___x_1697_ = v___x_1687_;
goto v_reusejp_1696_;
}
else
{
lean_object* v_reuseFailAlloc_1703_; 
v_reuseFailAlloc_1703_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1703_, 0, v_f_x27_1694_);
lean_ctor_set(v_reuseFailAlloc_1703_, 1, v___x_1695_);
v___x_1697_ = v_reuseFailAlloc_1703_;
goto v_reusejp_1696_;
}
v_reusejp_1696_:
{
lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; 
v___x_1698_ = lean_nat_add(v_n_1693_, v_one_1692_);
lean_dec(v_n_1693_);
v___x_1699_ = l_Nat_reprFast(v___x_1698_);
v___x_1700_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1700_, 0, v___x_1699_);
v___x_1701_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1701_, 0, v___x_1697_);
lean_ctor_set(v___x_1701_, 1, v___x_1700_);
v___x_1702_ = l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse(v___x_1701_, v_x_1664_);
return v___x_1702_;
}
}
}
}
case 3:
{
lean_object* v_a_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; uint8_t v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; 
v_a_1705_ = lean_ctor_get(v_x_1663_, 0);
lean_inc(v_a_1705_);
lean_dec_ref_known(v_x_1663_, 1);
v___x_1706_ = ((lean_object*)(l_Lean_Level_PP_Result_format___closed__3));
v___x_1707_ = l___private_Lean_Level_0__Lean_Level_PP_Result_formatLst(v_a_1705_);
v___x_1708_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1708_, 0, v___x_1706_);
lean_ctor_set(v___x_1708_, 1, v___x_1707_);
v___x_1709_ = 0;
v___x_1710_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1710_, 0, v___x_1708_);
lean_ctor_set_uint8(v___x_1710_, sizeof(void*)*1, v___x_1709_);
v___x_1711_ = l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse(v___x_1710_, v_x_1664_);
return v___x_1711_;
}
default: 
{
lean_object* v_a_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; uint8_t v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; 
v_a_1712_ = lean_ctor_get(v_x_1663_, 0);
lean_inc(v_a_1712_);
lean_dec_ref_known(v_x_1663_, 1);
v___x_1713_ = ((lean_object*)(l_Lean_Level_PP_Result_format___closed__5));
v___x_1714_ = l___private_Lean_Level_0__Lean_Level_PP_Result_formatLst(v_a_1712_);
v___x_1715_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1715_, 0, v___x_1713_);
lean_ctor_set(v___x_1715_, 1, v___x_1714_);
v___x_1716_ = 0;
v___x_1717_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1717_, 0, v___x_1715_);
lean_ctor_set_uint8(v___x_1717_, sizeof(void*)*1, v___x_1716_);
v___x_1718_ = l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse(v___x_1717_, v_x_1664_);
return v___x_1718_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_PP_Result_formatLst(lean_object* v_x_1719_){
_start:
{
if (lean_obj_tag(v_x_1719_) == 0)
{
lean_object* v___x_1720_; 
v___x_1720_ = lean_box(0);
return v___x_1720_;
}
else
{
lean_object* v_head_1721_; lean_object* v_tail_1722_; lean_object* v___x_1724_; uint8_t v_isShared_1725_; uint8_t v_isSharedCheck_1734_; 
v_head_1721_ = lean_ctor_get(v_x_1719_, 0);
v_tail_1722_ = lean_ctor_get(v_x_1719_, 1);
v_isSharedCheck_1734_ = !lean_is_exclusive(v_x_1719_);
if (v_isSharedCheck_1734_ == 0)
{
v___x_1724_ = v_x_1719_;
v_isShared_1725_ = v_isSharedCheck_1734_;
goto v_resetjp_1723_;
}
else
{
lean_inc(v_tail_1722_);
lean_inc(v_head_1721_);
lean_dec(v_x_1719_);
v___x_1724_ = lean_box(0);
v_isShared_1725_ = v_isSharedCheck_1734_;
goto v_resetjp_1723_;
}
v_resetjp_1723_:
{
lean_object* v___x_1726_; uint8_t v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1730_; 
v___x_1726_ = lean_box(1);
v___x_1727_ = 0;
v___x_1728_ = l_Lean_Level_PP_Result_format(v_head_1721_, v___x_1727_);
if (v_isShared_1725_ == 0)
{
lean_ctor_set_tag(v___x_1724_, 5);
lean_ctor_set(v___x_1724_, 1, v___x_1728_);
lean_ctor_set(v___x_1724_, 0, v___x_1726_);
v___x_1730_ = v___x_1724_;
goto v_reusejp_1729_;
}
else
{
lean_object* v_reuseFailAlloc_1733_; 
v_reuseFailAlloc_1733_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1733_, 0, v___x_1726_);
lean_ctor_set(v_reuseFailAlloc_1733_, 1, v___x_1728_);
v___x_1730_ = v_reuseFailAlloc_1733_;
goto v_reusejp_1729_;
}
v_reusejp_1729_:
{
lean_object* v___x_1731_; lean_object* v___x_1732_; 
v___x_1731_ = l___private_Lean_Level_0__Lean_Level_PP_Result_formatLst(v_tail_1722_);
v___x_1732_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1732_, 0, v___x_1730_);
lean_ctor_set(v___x_1732_, 1, v___x_1731_);
return v___x_1732_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_format___boxed(lean_object* v_x_1735_, lean_object* v_x_1736_){
_start:
{
uint8_t v_x_270__boxed_1737_; lean_object* v_res_1738_; 
v_x_270__boxed_1737_ = lean_unbox(v_x_1736_);
v_res_1738_ = l_Lean_Level_PP_Result_format(v_x_1735_, v_x_270__boxed_1737_);
return v_res_1738_;
}
}
static lean_object* _init_l_Lean_Level_PP_Result_quote___closed__0(void){
_start:
{
uint8_t v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; 
v___x_1739_ = 0;
v___x_1740_ = lean_box(0);
v___x_1741_ = l_Lean_SourceInfo_fromRef(v___x_1740_, v___x_1739_);
return v___x_1741_;
}
}
static lean_object* _init_l_Lean_Level_PP_Result_quote___closed__6(void){
_start:
{
lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; 
v___x_1751_ = ((lean_object*)(l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__0));
v___x_1752_ = lean_obj_once(&l_Lean_Level_PP_Result_quote___closed__0, &l_Lean_Level_PP_Result_quote___closed__0_once, _init_l_Lean_Level_PP_Result_quote___closed__0);
v___x_1753_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1753_, 0, v___x_1752_);
lean_ctor_set(v___x_1753_, 1, v___x_1751_);
return v___x_1753_;
}
}
static lean_object* _init_l_Lean_Level_PP_Result_quote___closed__7(void){
_start:
{
lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; 
v___x_1754_ = ((lean_object*)(l_Lean_instReprData___lam__0___closed__0));
v___x_1755_ = lean_obj_once(&l_Lean_Level_PP_Result_quote___closed__0, &l_Lean_Level_PP_Result_quote___closed__0_once, _init_l_Lean_Level_PP_Result_quote___closed__0);
v___x_1756_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1756_, 0, v___x_1755_);
lean_ctor_set(v___x_1756_, 1, v___x_1754_);
return v___x_1756_;
}
}
static lean_object* _init_l_Lean_Level_PP_Result_quote___closed__12(void){
_start:
{
lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; 
v___x_1769_ = ((lean_object*)(l_Lean_Level_PP_Result_format___closed__2));
v___x_1770_ = lean_obj_once(&l_Lean_Level_PP_Result_quote___closed__0, &l_Lean_Level_PP_Result_quote___closed__0_once, _init_l_Lean_Level_PP_Result_quote___closed__0);
v___x_1771_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1771_, 0, v___x_1770_);
lean_ctor_set(v___x_1771_, 1, v___x_1769_);
return v___x_1771_;
}
}
static lean_object* _init_l_Lean_Level_PP_Result_quote___closed__15(void){
_start:
{
lean_object* v___x_1775_; 
v___x_1775_ = l_Array_mkArray0___redArg();
return v___x_1775_;
}
}
static lean_object* _init_l_Lean_Level_PP_Result_quote___closed__17(void){
_start:
{
lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; 
v___x_1781_ = ((lean_object*)(l_Lean_Level_PP_Result_format___closed__4));
v___x_1782_ = lean_obj_once(&l_Lean_Level_PP_Result_quote___closed__0, &l_Lean_Level_PP_Result_quote___closed__0_once, _init_l_Lean_Level_PP_Result_quote___closed__0);
v___x_1783_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1783_, 0, v___x_1782_);
lean_ctor_set(v___x_1783_, 1, v___x_1781_);
return v___x_1783_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_quote(lean_object* v_r_1784_, lean_object* v_prec_1785_){
_start:
{
lean_object* v_s_1787_; 
switch(lean_obj_tag(v_r_1784_))
{
case 0:
{
lean_object* v_a_1795_; lean_object* v___x_1796_; 
v_a_1795_ = lean_ctor_get(v_r_1784_, 0);
lean_inc(v_a_1795_);
lean_dec_ref_known(v_r_1784_, 1);
v___x_1796_ = l_Lean_mkIdent(v_a_1795_);
return v___x_1796_;
}
case 1:
{
lean_object* v_a_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; 
v_a_1797_ = lean_ctor_get(v_r_1784_, 0);
lean_inc(v_a_1797_);
lean_dec_ref_known(v_r_1784_, 1);
v___x_1798_ = l_Nat_reprFast(v_a_1797_);
v___x_1799_ = lean_box(2);
v___x_1800_ = l_Lean_Syntax_mkNumLit(v___x_1798_, v___x_1799_);
return v___x_1800_;
}
case 2:
{
lean_object* v_a_1801_; lean_object* v_a_1802_; lean_object* v___x_1804_; uint8_t v_isShared_1805_; uint8_t v_isSharedCheck_1825_; 
v_a_1801_ = lean_ctor_get(v_r_1784_, 0);
v_a_1802_ = lean_ctor_get(v_r_1784_, 1);
v_isSharedCheck_1825_ = !lean_is_exclusive(v_r_1784_);
if (v_isSharedCheck_1825_ == 0)
{
v___x_1804_ = v_r_1784_;
v_isShared_1805_ = v_isSharedCheck_1825_;
goto v_resetjp_1803_;
}
else
{
lean_inc(v_a_1802_);
lean_inc(v_a_1801_);
lean_dec(v_r_1784_);
v___x_1804_ = lean_box(0);
v_isShared_1805_ = v_isSharedCheck_1825_;
goto v_resetjp_1803_;
}
v_resetjp_1803_:
{
lean_object* v_zero_1806_; uint8_t v_isZero_1807_; 
v_zero_1806_ = lean_unsigned_to_nat(0u);
v_isZero_1807_ = lean_nat_dec_eq(v_a_1802_, v_zero_1806_);
if (v_isZero_1807_ == 1)
{
lean_del_object(v___x_1804_);
lean_dec(v_a_1802_);
v_r_1784_ = v_a_1801_;
goto _start;
}
else
{
lean_object* v_one_1809_; lean_object* v_n_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1818_; 
v_one_1809_ = lean_unsigned_to_nat(1u);
v_n_1810_ = lean_nat_sub(v_a_1802_, v_one_1809_);
lean_dec(v_a_1802_);
v___x_1811_ = lean_box(0);
v___x_1812_ = l_Lean_SourceInfo_fromRef(v___x_1811_, v_isZero_1807_);
v___x_1813_ = ((lean_object*)(l_Lean_Level_PP_Result_quote___closed__9));
v___x_1814_ = lean_unsigned_to_nat(65u);
v___x_1815_ = l_Lean_Level_PP_Result_quote(v_a_1801_, v___x_1814_);
v___x_1816_ = ((lean_object*)(l_Lean_Level_PP_Result_quote___closed__10));
lean_inc(v___x_1812_);
if (v_isShared_1805_ == 0)
{
lean_ctor_set(v___x_1804_, 1, v___x_1816_);
lean_ctor_set(v___x_1804_, 0, v___x_1812_);
v___x_1818_ = v___x_1804_;
goto v_reusejp_1817_;
}
else
{
lean_object* v_reuseFailAlloc_1824_; 
v_reuseFailAlloc_1824_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1824_, 0, v___x_1812_);
lean_ctor_set(v_reuseFailAlloc_1824_, 1, v___x_1816_);
v___x_1818_ = v_reuseFailAlloc_1824_;
goto v_reusejp_1817_;
}
v_reusejp_1817_:
{
lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; 
v___x_1819_ = lean_nat_add(v_n_1810_, v_one_1809_);
lean_dec(v_n_1810_);
v___x_1820_ = l_Nat_reprFast(v___x_1819_);
v___x_1821_ = lean_box(2);
v___x_1822_ = l_Lean_Syntax_mkNumLit(v___x_1820_, v___x_1821_);
v___x_1823_ = l_Lean_Syntax_node3(v___x_1812_, v___x_1813_, v___x_1815_, v___x_1818_, v___x_1822_);
v_s_1787_ = v___x_1823_;
goto v___jp_1786_;
}
}
}
}
case 3:
{
lean_object* v_a_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; size_t v_sz_1833_; size_t v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; 
v_a_1826_ = lean_ctor_get(v_r_1784_, 0);
lean_inc(v_a_1826_);
lean_dec_ref_known(v_r_1784_, 1);
v___x_1827_ = lean_obj_once(&l_Lean_Level_PP_Result_quote___closed__0, &l_Lean_Level_PP_Result_quote___closed__0_once, _init_l_Lean_Level_PP_Result_quote___closed__0);
v___x_1828_ = ((lean_object*)(l_Lean_Level_PP_Result_quote___closed__11));
v___x_1829_ = lean_obj_once(&l_Lean_Level_PP_Result_quote___closed__12, &l_Lean_Level_PP_Result_quote___closed__12_once, _init_l_Lean_Level_PP_Result_quote___closed__12);
v___x_1830_ = ((lean_object*)(l_Lean_Level_PP_Result_quote___closed__14));
v___x_1831_ = lean_obj_once(&l_Lean_Level_PP_Result_quote___closed__15, &l_Lean_Level_PP_Result_quote___closed__15_once, _init_l_Lean_Level_PP_Result_quote___closed__15);
v___x_1832_ = lean_array_mk(v_a_1826_);
v_sz_1833_ = lean_array_size(v___x_1832_);
v___x_1834_ = ((size_t)0ULL);
v___x_1835_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Level_PP_Result_quote_spec__0(v_sz_1833_, v___x_1834_, v___x_1832_);
v___x_1836_ = l_Array_append___redArg(v___x_1831_, v___x_1835_);
lean_dec_ref(v___x_1835_);
v___x_1837_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1837_, 0, v___x_1827_);
lean_ctor_set(v___x_1837_, 1, v___x_1830_);
lean_ctor_set(v___x_1837_, 2, v___x_1836_);
v___x_1838_ = l_Lean_Syntax_node2(v___x_1827_, v___x_1828_, v___x_1829_, v___x_1837_);
v_s_1787_ = v___x_1838_;
goto v___jp_1786_;
}
default: 
{
lean_object* v_a_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; size_t v_sz_1846_; size_t v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; 
v_a_1839_ = lean_ctor_get(v_r_1784_, 0);
lean_inc(v_a_1839_);
lean_dec_ref_known(v_r_1784_, 1);
v___x_1840_ = lean_obj_once(&l_Lean_Level_PP_Result_quote___closed__0, &l_Lean_Level_PP_Result_quote___closed__0_once, _init_l_Lean_Level_PP_Result_quote___closed__0);
v___x_1841_ = ((lean_object*)(l_Lean_Level_PP_Result_quote___closed__16));
v___x_1842_ = lean_obj_once(&l_Lean_Level_PP_Result_quote___closed__17, &l_Lean_Level_PP_Result_quote___closed__17_once, _init_l_Lean_Level_PP_Result_quote___closed__17);
v___x_1843_ = ((lean_object*)(l_Lean_Level_PP_Result_quote___closed__14));
v___x_1844_ = lean_obj_once(&l_Lean_Level_PP_Result_quote___closed__15, &l_Lean_Level_PP_Result_quote___closed__15_once, _init_l_Lean_Level_PP_Result_quote___closed__15);
v___x_1845_ = lean_array_mk(v_a_1839_);
v_sz_1846_ = lean_array_size(v___x_1845_);
v___x_1847_ = ((size_t)0ULL);
v___x_1848_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Level_PP_Result_quote_spec__0(v_sz_1846_, v___x_1847_, v___x_1845_);
v___x_1849_ = l_Array_append___redArg(v___x_1844_, v___x_1848_);
lean_dec_ref(v___x_1848_);
v___x_1850_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1850_, 0, v___x_1840_);
lean_ctor_set(v___x_1850_, 1, v___x_1843_);
lean_ctor_set(v___x_1850_, 2, v___x_1849_);
v___x_1851_ = l_Lean_Syntax_node2(v___x_1840_, v___x_1841_, v___x_1842_, v___x_1850_);
v_s_1787_ = v___x_1851_;
goto v___jp_1786_;
}
}
v___jp_1786_:
{
lean_object* v___x_1788_; uint8_t v___x_1789_; 
v___x_1788_ = lean_unsigned_to_nat(0u);
v___x_1789_ = lean_nat_dec_lt(v___x_1788_, v_prec_1785_);
if (v___x_1789_ == 0)
{
return v_s_1787_;
}
else
{
lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; 
v___x_1790_ = lean_obj_once(&l_Lean_Level_PP_Result_quote___closed__0, &l_Lean_Level_PP_Result_quote___closed__0_once, _init_l_Lean_Level_PP_Result_quote___closed__0);
v___x_1791_ = ((lean_object*)(l_Lean_Level_PP_Result_quote___closed__5));
v___x_1792_ = lean_obj_once(&l_Lean_Level_PP_Result_quote___closed__6, &l_Lean_Level_PP_Result_quote___closed__6_once, _init_l_Lean_Level_PP_Result_quote___closed__6);
v___x_1793_ = lean_obj_once(&l_Lean_Level_PP_Result_quote___closed__7, &l_Lean_Level_PP_Result_quote___closed__7_once, _init_l_Lean_Level_PP_Result_quote___closed__7);
v___x_1794_ = l_Lean_Syntax_node3(v___x_1790_, v___x_1791_, v___x_1792_, v_s_1787_, v___x_1793_);
return v___x_1794_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Level_PP_Result_quote_spec__0(size_t v_sz_1852_, size_t v_i_1853_, lean_object* v_bs_1854_){
_start:
{
uint8_t v___x_1855_; 
v___x_1855_ = lean_usize_dec_lt(v_i_1853_, v_sz_1852_);
if (v___x_1855_ == 0)
{
return v_bs_1854_;
}
else
{
lean_object* v_v_1856_; lean_object* v___x_1857_; lean_object* v_bs_x27_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; size_t v___x_1861_; size_t v___x_1862_; lean_object* v___x_1863_; 
v_v_1856_ = lean_array_uget(v_bs_1854_, v_i_1853_);
v___x_1857_ = lean_unsigned_to_nat(0u);
v_bs_x27_1858_ = lean_array_uset(v_bs_1854_, v_i_1853_, v___x_1857_);
v___x_1859_ = lean_unsigned_to_nat(1024u);
v___x_1860_ = l_Lean_Level_PP_Result_quote(v_v_1856_, v___x_1859_);
v___x_1861_ = ((size_t)1ULL);
v___x_1862_ = lean_usize_add(v_i_1853_, v___x_1861_);
v___x_1863_ = lean_array_uset(v_bs_x27_1858_, v_i_1853_, v___x_1860_);
v_i_1853_ = v___x_1862_;
v_bs_1854_ = v___x_1863_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Level_PP_Result_quote_spec__0___boxed(lean_object* v_sz_1865_, lean_object* v_i_1866_, lean_object* v_bs_1867_){
_start:
{
size_t v_sz_boxed_1868_; size_t v_i_boxed_1869_; lean_object* v_res_1870_; 
v_sz_boxed_1868_ = lean_unbox_usize(v_sz_1865_);
lean_dec(v_sz_1865_);
v_i_boxed_1869_ = lean_unbox_usize(v_i_1866_);
lean_dec(v_i_1866_);
v_res_1870_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Level_PP_Result_quote_spec__0(v_sz_boxed_1868_, v_i_boxed_1869_, v_bs_1867_);
return v_res_1870_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_quote___boxed(lean_object* v_r_1871_, lean_object* v_prec_1872_){
_start:
{
lean_object* v_res_1873_; 
v_res_1873_ = l_Lean_Level_PP_Result_quote(v_r_1871_, v_prec_1872_);
lean_dec(v_prec_1872_);
return v_res_1873_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_format(lean_object* v_u_1874_, uint8_t v_mvars_1875_, lean_object* v_lIndex_x3f_1876_){
_start:
{
lean_object* v___x_1877_; lean_object* v___x_1878_; uint8_t v___x_1879_; lean_object* v___x_1880_; 
v___x_1877_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1877_, 0, v_lIndex_x3f_1876_);
lean_ctor_set_uint8(v___x_1877_, sizeof(void*)*1, v_mvars_1875_);
v___x_1878_ = l_Lean_Level_PP_toResult(v_u_1874_, v___x_1877_);
lean_dec_ref_known(v___x_1877_, 1);
v___x_1879_ = 1;
v___x_1880_ = l_Lean_Level_PP_Result_format(v___x_1878_, v___x_1879_);
return v___x_1880_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_format___boxed(lean_object* v_u_1881_, lean_object* v_mvars_1882_, lean_object* v_lIndex_x3f_1883_){
_start:
{
uint8_t v_mvars_boxed_1884_; lean_object* v_res_1885_; 
v_mvars_boxed_1884_ = lean_unbox(v_mvars_1882_);
v_res_1885_ = l_Lean_Level_format(v_u_1881_, v_mvars_boxed_1884_, v_lIndex_x3f_1883_);
return v_res_1885_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_instToFormat___lam__0(lean_object* v_x_1886_){
_start:
{
lean_object* v___x_1887_; 
v___x_1887_ = lean_box(0);
return v___x_1887_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_instToFormat___lam__0___boxed(lean_object* v_x_1888_){
_start:
{
lean_object* v_res_1889_; 
v_res_1889_ = l_Lean_Level_instToFormat___lam__0(v_x_1888_);
lean_dec(v_x_1888_);
return v_res_1889_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_instToFormat___lam__1(lean_object* v___f_1890_, lean_object* v_u_1891_){
_start:
{
uint8_t v___x_1892_; lean_object* v___x_1893_; 
v___x_1892_ = 1;
v___x_1893_ = l_Lean_Level_format(v_u_1891_, v___x_1892_, v___f_1890_);
return v___x_1893_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_instToString___lam__1(lean_object* v___f_1898_, lean_object* v_u_1899_){
_start:
{
uint8_t v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; 
v___x_1900_ = 1;
v___x_1901_ = l_Lean_Level_format(v_u_1899_, v___x_1900_, v___f_1898_);
v___x_1902_ = l_Std_Format_defWidth;
v___x_1903_ = lean_unsigned_to_nat(0u);
v___x_1904_ = l_Std_Format_pretty(v___x_1901_, v___x_1902_, v___x_1903_, v___x_1903_);
return v___x_1904_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_quote(lean_object* v_u_1908_, lean_object* v_prec_1909_, uint8_t v_mvars_1910_, lean_object* v_lIndex_x3f_1911_){
_start:
{
lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; 
v___x_1912_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1912_, 0, v_lIndex_x3f_1911_);
lean_ctor_set_uint8(v___x_1912_, sizeof(void*)*1, v_mvars_1910_);
v___x_1913_ = l_Lean_Level_PP_toResult(v_u_1908_, v___x_1912_);
lean_dec_ref_known(v___x_1912_, 1);
v___x_1914_ = l_Lean_Level_PP_Result_quote(v___x_1913_, v_prec_1909_);
return v___x_1914_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_quote___boxed(lean_object* v_u_1915_, lean_object* v_prec_1916_, lean_object* v_mvars_1917_, lean_object* v_lIndex_x3f_1918_){
_start:
{
uint8_t v_mvars_boxed_1919_; lean_object* v_res_1920_; 
v_mvars_boxed_1919_ = lean_unbox(v_mvars_1917_);
v_res_1920_ = l_Lean_Level_quote(v_u_1915_, v_prec_1916_, v_mvars_boxed_1919_, v_lIndex_x3f_1918_);
lean_dec(v_prec_1916_);
return v_res_1920_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_instQuoteMkStr1___lam__1(lean_object* v___f_1921_, lean_object* v_u_1922_){
_start:
{
lean_object* v___x_1923_; uint8_t v___x_1924_; lean_object* v___x_1925_; 
v___x_1923_ = lean_unsigned_to_nat(0u);
v___x_1924_ = 1;
v___x_1925_ = l_Lean_Level_quote(v_u_1922_, v___x_1923_, v___x_1924_, v___f_1921_);
return v___x_1925_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Level_0__Lean_mkLevelMaxCore___lam__0(lean_object* v_u_1929_, lean_object* v_v_1930_){
_start:
{
uint8_t v___y_1932_; uint8_t v___x_1938_; 
v___x_1938_ = l_Lean_Level_isExplicit(v_v_1930_);
if (v___x_1938_ == 0)
{
v___y_1932_ = v___x_1938_;
goto v___jp_1931_;
}
else
{
lean_object* v___x_1939_; lean_object* v___x_1940_; uint8_t v___x_1941_; 
v___x_1939_ = l_Lean_Level_getOffset(v_v_1930_);
v___x_1940_ = l_Lean_Level_getOffset(v_u_1929_);
v___x_1941_ = lean_nat_dec_le(v___x_1939_, v___x_1940_);
lean_dec(v___x_1940_);
lean_dec(v___x_1939_);
v___y_1932_ = v___x_1941_;
goto v___jp_1931_;
}
v___jp_1931_:
{
uint8_t v___x_1933_; 
v___x_1933_ = 1;
if (v___y_1932_ == 0)
{
if (lean_obj_tag(v_u_1929_) == 2)
{
lean_object* v_a_1934_; lean_object* v_a_1935_; uint8_t v___x_1936_; 
v_a_1934_ = lean_ctor_get(v_u_1929_, 0);
v_a_1935_ = lean_ctor_get(v_u_1929_, 1);
v___x_1936_ = lean_level_eq(v_v_1930_, v_a_1934_);
if (v___x_1936_ == 0)
{
uint8_t v___x_1937_; 
v___x_1937_ = lean_level_eq(v_v_1930_, v_a_1935_);
return v___x_1937_;
}
else
{
return v___x_1933_;
}
}
else
{
return v___y_1932_;
}
}
else
{
return v___x_1933_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_mkLevelMaxCore___lam__0___boxed(lean_object* v_u_1942_, lean_object* v_v_1943_){
_start:
{
uint8_t v_res_1944_; lean_object* v_r_1945_; 
v_res_1944_ = l___private_Lean_Level_0__Lean_mkLevelMaxCore___lam__0(v_u_1942_, v_v_1943_);
lean_dec(v_v_1943_);
lean_dec(v_u_1942_);
v_r_1945_ = lean_box(v_res_1944_);
return v_r_1945_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_mkLevelMaxCore(lean_object* v_u_1946_, lean_object* v_v_1947_, lean_object* v_elseK_1948_){
_start:
{
uint8_t v___x_1949_; 
v___x_1949_ = lean_level_eq(v_u_1946_, v_v_1947_);
if (v___x_1949_ == 0)
{
uint8_t v___x_1950_; 
v___x_1950_ = l_Lean_Level_isZero(v_u_1946_);
if (v___x_1950_ == 0)
{
uint8_t v___x_1951_; 
v___x_1951_ = l_Lean_Level_isZero(v_v_1947_);
if (v___x_1951_ == 0)
{
uint8_t v___x_1952_; 
v___x_1952_ = l___private_Lean_Level_0__Lean_mkLevelMaxCore___lam__0(v_u_1946_, v_v_1947_);
if (v___x_1952_ == 0)
{
uint8_t v___x_1953_; 
v___x_1953_ = l___private_Lean_Level_0__Lean_mkLevelMaxCore___lam__0(v_v_1947_, v_u_1946_);
if (v___x_1953_ == 0)
{
lean_object* v___x_1954_; lean_object* v___x_1955_; uint8_t v___x_1956_; 
v___x_1954_ = l_Lean_Level_getLevelOffset(v_u_1946_);
v___x_1955_ = l_Lean_Level_getLevelOffset(v_v_1947_);
v___x_1956_ = lean_level_eq(v___x_1954_, v___x_1955_);
lean_dec(v___x_1955_);
lean_dec(v___x_1954_);
if (v___x_1956_ == 0)
{
lean_object* v___x_1957_; lean_object* v___x_1958_; 
v___x_1957_ = lean_box(0);
v___x_1958_ = lean_apply_1(v_elseK_1948_, v___x_1957_);
return v___x_1958_;
}
else
{
lean_object* v___x_1959_; lean_object* v___x_1960_; uint8_t v___x_1961_; 
lean_dec_ref(v_elseK_1948_);
v___x_1959_ = l_Lean_Level_getOffset(v_v_1947_);
v___x_1960_ = l_Lean_Level_getOffset(v_u_1946_);
v___x_1961_ = lean_nat_dec_le(v___x_1959_, v___x_1960_);
lean_dec(v___x_1960_);
lean_dec(v___x_1959_);
if (v___x_1961_ == 0)
{
lean_inc(v_v_1947_);
return v_v_1947_;
}
else
{
lean_inc(v_u_1946_);
return v_u_1946_;
}
}
}
else
{
lean_dec_ref(v_elseK_1948_);
lean_inc(v_v_1947_);
return v_v_1947_;
}
}
else
{
lean_dec_ref(v_elseK_1948_);
lean_inc(v_u_1946_);
return v_u_1946_;
}
}
else
{
lean_dec_ref(v_elseK_1948_);
lean_inc(v_u_1946_);
return v_u_1946_;
}
}
else
{
lean_dec_ref(v_elseK_1948_);
lean_inc(v_v_1947_);
return v_v_1947_;
}
}
else
{
lean_dec_ref(v_elseK_1948_);
lean_inc(v_u_1946_);
return v_u_1946_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_mkLevelMaxCore___boxed(lean_object* v_u_1962_, lean_object* v_v_1963_, lean_object* v_elseK_1964_){
_start:
{
lean_object* v_res_1965_; 
v_res_1965_ = l___private_Lean_Level_0__Lean_mkLevelMaxCore(v_u_1962_, v_v_1963_, v_elseK_1964_);
lean_dec(v_v_1963_);
lean_dec(v_u_1962_);
return v_res_1965_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLevelMax_x27(lean_object* v_u_1966_, lean_object* v_v_1967_){
_start:
{
uint8_t v___x_1968_; 
v___x_1968_ = lean_level_eq(v_u_1966_, v_v_1967_);
if (v___x_1968_ == 0)
{
uint8_t v___x_1969_; 
v___x_1969_ = l_Lean_Level_isZero(v_u_1966_);
if (v___x_1969_ == 0)
{
uint8_t v___x_1970_; 
v___x_1970_ = l_Lean_Level_isZero(v_v_1967_);
if (v___x_1970_ == 0)
{
uint8_t v___x_1971_; 
v___x_1971_ = l___private_Lean_Level_0__Lean_mkLevelMaxCore___lam__0(v_u_1966_, v_v_1967_);
if (v___x_1971_ == 0)
{
uint8_t v___x_1972_; 
v___x_1972_ = l___private_Lean_Level_0__Lean_mkLevelMaxCore___lam__0(v_v_1967_, v_u_1966_);
if (v___x_1972_ == 0)
{
lean_object* v___x_1973_; lean_object* v___x_1974_; uint8_t v___x_1975_; 
v___x_1973_ = l_Lean_Level_getLevelOffset(v_u_1966_);
v___x_1974_ = l_Lean_Level_getLevelOffset(v_v_1967_);
v___x_1975_ = lean_level_eq(v___x_1973_, v___x_1974_);
lean_dec(v___x_1974_);
lean_dec(v___x_1973_);
if (v___x_1975_ == 0)
{
lean_object* v___x_1976_; 
v___x_1976_ = l_Lean_Level_max___override(v_u_1966_, v_v_1967_);
return v___x_1976_;
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
lean_dec(v_u_1966_);
return v_v_1967_;
}
else
{
lean_dec(v_v_1967_);
return v_u_1966_;
}
}
}
else
{
lean_dec(v_u_1966_);
return v_v_1967_;
}
}
else
{
lean_dec(v_v_1967_);
return v_u_1966_;
}
}
else
{
lean_dec(v_v_1967_);
return v_u_1966_;
}
}
else
{
lean_dec(v_u_1966_);
return v_v_1967_;
}
}
else
{
lean_dec(v_v_1967_);
return v_u_1966_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_simpLevelMax_x27(lean_object* v_u_1980_, lean_object* v_v_1981_, lean_object* v_d_1982_){
_start:
{
uint8_t v___x_1983_; 
v___x_1983_ = lean_level_eq(v_u_1980_, v_v_1981_);
if (v___x_1983_ == 0)
{
uint8_t v___x_1984_; 
v___x_1984_ = l_Lean_Level_isZero(v_u_1980_);
if (v___x_1984_ == 0)
{
uint8_t v___x_1985_; 
v___x_1985_ = l_Lean_Level_isZero(v_v_1981_);
if (v___x_1985_ == 0)
{
uint8_t v___x_1986_; 
v___x_1986_ = l___private_Lean_Level_0__Lean_mkLevelMaxCore___lam__0(v_u_1980_, v_v_1981_);
if (v___x_1986_ == 0)
{
uint8_t v___x_1987_; 
v___x_1987_ = l___private_Lean_Level_0__Lean_mkLevelMaxCore___lam__0(v_v_1981_, v_u_1980_);
if (v___x_1987_ == 0)
{
lean_object* v___x_1988_; lean_object* v___x_1989_; uint8_t v___x_1990_; 
v___x_1988_ = l_Lean_Level_getLevelOffset(v_u_1980_);
v___x_1989_ = l_Lean_Level_getLevelOffset(v_v_1981_);
v___x_1990_ = lean_level_eq(v___x_1988_, v___x_1989_);
lean_dec(v___x_1989_);
lean_dec(v___x_1988_);
if (v___x_1990_ == 0)
{
lean_inc(v_d_1982_);
return v_d_1982_;
}
else
{
lean_object* v___x_1991_; lean_object* v___x_1992_; uint8_t v___x_1993_; 
v___x_1991_ = l_Lean_Level_getOffset(v_v_1981_);
v___x_1992_ = l_Lean_Level_getOffset(v_u_1980_);
v___x_1993_ = lean_nat_dec_le(v___x_1991_, v___x_1992_);
lean_dec(v___x_1992_);
lean_dec(v___x_1991_);
if (v___x_1993_ == 0)
{
lean_inc(v_v_1981_);
return v_v_1981_;
}
else
{
lean_inc(v_u_1980_);
return v_u_1980_;
}
}
}
else
{
lean_inc(v_v_1981_);
return v_v_1981_;
}
}
else
{
lean_inc(v_u_1980_);
return v_u_1980_;
}
}
else
{
lean_inc(v_u_1980_);
return v_u_1980_;
}
}
else
{
lean_inc(v_v_1981_);
return v_v_1981_;
}
}
else
{
lean_inc(v_u_1980_);
return v_u_1980_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_simpLevelMax_x27___boxed(lean_object* v_u_1994_, lean_object* v_v_1995_, lean_object* v_d_1996_){
_start:
{
lean_object* v_res_1997_; 
v_res_1997_ = l_Lean_simpLevelMax_x27(v_u_1994_, v_v_1995_, v_d_1996_);
lean_dec(v_d_1996_);
lean_dec(v_v_1995_);
lean_dec(v_u_1994_);
return v_res_1997_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_mkLevelIMaxCore(lean_object* v_u_1998_, lean_object* v_v_1999_, lean_object* v_elseK_2000_){
_start:
{
uint8_t v___x_2001_; 
v___x_2001_ = l_Lean_Level_isNeverZero(v_v_1999_);
if (v___x_2001_ == 0)
{
uint8_t v___x_2002_; 
v___x_2002_ = l_Lean_Level_isZero(v_v_1999_);
if (v___x_2002_ == 0)
{
uint8_t v___x_2003_; 
v___x_2003_ = l_Lean_Level_isZero(v_u_1998_);
if (v___x_2003_ == 0)
{
uint8_t v___x_2004_; 
v___x_2004_ = lean_level_eq(v_u_1998_, v_v_1999_);
lean_dec(v_v_1999_);
if (v___x_2004_ == 0)
{
lean_object* v___x_2005_; lean_object* v___x_2006_; 
lean_dec(v_u_1998_);
v___x_2005_ = lean_box(0);
v___x_2006_ = lean_apply_1(v_elseK_2000_, v___x_2005_);
return v___x_2006_;
}
else
{
lean_dec_ref(v_elseK_2000_);
return v_u_1998_;
}
}
else
{
lean_dec_ref(v_elseK_2000_);
lean_dec(v_u_1998_);
return v_v_1999_;
}
}
else
{
lean_dec_ref(v_elseK_2000_);
lean_dec(v_u_1998_);
return v_v_1999_;
}
}
else
{
lean_object* v___x_2007_; 
lean_dec_ref(v_elseK_2000_);
v___x_2007_ = l_Lean_mkLevelMax_x27(v_u_1998_, v_v_1999_);
return v___x_2007_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkLevelIMax_x27(lean_object* v_u_2008_, lean_object* v_v_2009_){
_start:
{
uint8_t v___x_2010_; 
v___x_2010_ = l_Lean_Level_isNeverZero(v_v_2009_);
if (v___x_2010_ == 0)
{
uint8_t v___x_2011_; 
v___x_2011_ = l_Lean_Level_isZero(v_v_2009_);
if (v___x_2011_ == 0)
{
uint8_t v___x_2012_; 
v___x_2012_ = l_Lean_Level_isZero(v_u_2008_);
if (v___x_2012_ == 0)
{
uint8_t v___x_2013_; 
v___x_2013_ = lean_level_eq(v_u_2008_, v_v_2009_);
if (v___x_2013_ == 0)
{
lean_object* v___x_2014_; 
v___x_2014_ = l_Lean_Level_imax___override(v_u_2008_, v_v_2009_);
return v___x_2014_;
}
else
{
lean_dec(v_v_2009_);
return v_u_2008_;
}
}
else
{
lean_dec(v_u_2008_);
return v_v_2009_;
}
}
else
{
lean_dec(v_u_2008_);
return v_v_2009_;
}
}
else
{
lean_object* v___x_2015_; 
v___x_2015_ = l_Lean_mkLevelMax_x27(v_u_2008_, v_v_2009_);
return v___x_2015_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_simpLevelIMax_x27(lean_object* v_u_2016_, lean_object* v_v_2017_, lean_object* v_d_2018_){
_start:
{
uint8_t v___x_2019_; 
v___x_2019_ = l_Lean_Level_isNeverZero(v_v_2017_);
if (v___x_2019_ == 0)
{
uint8_t v___x_2020_; 
v___x_2020_ = l_Lean_Level_isZero(v_v_2017_);
if (v___x_2020_ == 0)
{
uint8_t v___x_2021_; 
v___x_2021_ = l_Lean_Level_isZero(v_u_2016_);
if (v___x_2021_ == 0)
{
uint8_t v___x_2022_; 
v___x_2022_ = lean_level_eq(v_u_2016_, v_v_2017_);
lean_dec(v_v_2017_);
if (v___x_2022_ == 0)
{
lean_dec(v_u_2016_);
lean_inc(v_d_2018_);
return v_d_2018_;
}
else
{
return v_u_2016_;
}
}
else
{
lean_dec(v_u_2016_);
return v_v_2017_;
}
}
else
{
lean_dec(v_u_2016_);
return v_v_2017_;
}
}
else
{
lean_object* v___x_2023_; 
v___x_2023_ = l_Lean_mkLevelMax_x27(v_u_2016_, v_v_2017_);
return v___x_2023_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_simpLevelIMax_x27___boxed(lean_object* v_u_2024_, lean_object* v_v_2025_, lean_object* v_d_2026_){
_start:
{
lean_object* v_res_2027_; 
v_res_2027_ = l_Lean_simpLevelIMax_x27(v_u_2024_, v_v_2025_, v_d_2026_);
lean_dec(v_d_2026_);
return v_res_2027_;
}
}
static lean_object* _init_l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl___closed__2(void){
_start:
{
lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; 
v___x_2030_ = ((lean_object*)(l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl___closed__1));
v___x_2031_ = lean_unsigned_to_nat(14u);
v___x_2032_ = lean_unsigned_to_nat(566u);
v___x_2033_ = ((lean_object*)(l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl___closed__0));
v___x_2034_ = ((lean_object*)(l_Lean_Level_mvarId_x21___closed__0));
v___x_2035_ = l_mkPanicMessageWithDecl(v___x_2034_, v___x_2033_, v___x_2032_, v___x_2031_, v___x_2030_);
return v___x_2035_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl(lean_object* v_lvl_2036_, lean_object* v_newLvl_2037_){
_start:
{
if (lean_obj_tag(v_lvl_2036_) == 1)
{
lean_object* v_a_2038_; size_t v___x_2039_; size_t v___x_2040_; uint8_t v___x_2041_; 
v_a_2038_ = lean_ctor_get(v_lvl_2036_, 0);
v___x_2039_ = lean_ptr_addr(v_a_2038_);
v___x_2040_ = lean_ptr_addr(v_newLvl_2037_);
v___x_2041_ = lean_usize_dec_eq(v___x_2039_, v___x_2040_);
if (v___x_2041_ == 0)
{
lean_object* v___x_2042_; 
v___x_2042_ = l_Lean_Level_succ___override(v_newLvl_2037_);
return v___x_2042_;
}
else
{
lean_dec(v_newLvl_2037_);
lean_inc_ref(v_lvl_2036_);
return v_lvl_2036_;
}
}
else
{
lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; 
lean_dec(v_newLvl_2037_);
v___x_2043_ = lean_box(0);
v___x_2044_ = lean_obj_once(&l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl___closed__2, &l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl___closed__2_once, _init_l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl___closed__2);
v___x_2045_ = l_panic___redArg(v___x_2043_, v___x_2044_);
return v___x_2045_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl___boxed(lean_object* v_lvl_2046_, lean_object* v_newLvl_2047_){
_start:
{
lean_object* v_res_2048_; 
v_res_2048_ = l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl(v_lvl_2046_, v_newLvl_2047_);
lean_dec(v_lvl_2046_);
return v_res_2048_;
}
}
static lean_object* _init_l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl___closed__2(void){
_start:
{
lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; 
v___x_2051_ = ((lean_object*)(l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl___closed__1));
v___x_2052_ = lean_unsigned_to_nat(19u);
v___x_2053_ = lean_unsigned_to_nat(577u);
v___x_2054_ = ((lean_object*)(l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl___closed__0));
v___x_2055_ = ((lean_object*)(l_Lean_Level_mvarId_x21___closed__0));
v___x_2056_ = l_mkPanicMessageWithDecl(v___x_2055_, v___x_2054_, v___x_2053_, v___x_2052_, v___x_2051_);
return v___x_2056_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl(lean_object* v_lvl_2057_, lean_object* v_newLhs_2058_, lean_object* v_newRhs_2059_){
_start:
{
if (lean_obj_tag(v_lvl_2057_) == 2)
{
lean_object* v_a_2060_; lean_object* v_a_2061_; size_t v___x_2062_; size_t v___x_2063_; uint8_t v___x_2064_; 
v_a_2060_ = lean_ctor_get(v_lvl_2057_, 0);
v_a_2061_ = lean_ctor_get(v_lvl_2057_, 1);
v___x_2062_ = lean_ptr_addr(v_a_2060_);
v___x_2063_ = lean_ptr_addr(v_newLhs_2058_);
v___x_2064_ = lean_usize_dec_eq(v___x_2062_, v___x_2063_);
if (v___x_2064_ == 0)
{
lean_object* v___x_2065_; 
v___x_2065_ = l_Lean_mkLevelMax_x27(v_newLhs_2058_, v_newRhs_2059_);
return v___x_2065_;
}
else
{
size_t v___x_2066_; size_t v___x_2067_; uint8_t v___x_2068_; 
v___x_2066_ = lean_ptr_addr(v_a_2061_);
v___x_2067_ = lean_ptr_addr(v_newRhs_2059_);
v___x_2068_ = lean_usize_dec_eq(v___x_2066_, v___x_2067_);
if (v___x_2068_ == 0)
{
lean_object* v___x_2069_; 
v___x_2069_ = l_Lean_mkLevelMax_x27(v_newLhs_2058_, v_newRhs_2059_);
return v___x_2069_;
}
else
{
lean_object* v___x_2070_; 
v___x_2070_ = l_Lean_simpLevelMax_x27(v_newLhs_2058_, v_newRhs_2059_, v_lvl_2057_);
lean_dec(v_newRhs_2059_);
lean_dec(v_newLhs_2058_);
return v___x_2070_;
}
}
}
else
{
lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; 
lean_dec(v_newRhs_2059_);
lean_dec(v_newLhs_2058_);
v___x_2071_ = lean_box(0);
v___x_2072_ = lean_obj_once(&l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl___closed__2, &l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl___closed__2_once, _init_l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl___closed__2);
v___x_2073_ = l_panic___redArg(v___x_2071_, v___x_2072_);
return v___x_2073_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl___boxed(lean_object* v_lvl_2074_, lean_object* v_newLhs_2075_, lean_object* v_newRhs_2076_){
_start:
{
lean_object* v_res_2077_; 
v_res_2077_ = l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl(v_lvl_2074_, v_newLhs_2075_, v_newRhs_2076_);
lean_dec(v_lvl_2074_);
return v_res_2077_;
}
}
static lean_object* _init_l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl___closed__2(void){
_start:
{
lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; 
v___x_2080_ = ((lean_object*)(l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl___closed__1));
v___x_2081_ = lean_unsigned_to_nat(20u);
v___x_2082_ = lean_unsigned_to_nat(588u);
v___x_2083_ = ((lean_object*)(l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl___closed__0));
v___x_2084_ = ((lean_object*)(l_Lean_Level_mvarId_x21___closed__0));
v___x_2085_ = l_mkPanicMessageWithDecl(v___x_2084_, v___x_2083_, v___x_2082_, v___x_2081_, v___x_2080_);
return v___x_2085_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl(lean_object* v_lvl_2086_, lean_object* v_newLhs_2087_, lean_object* v_newRhs_2088_){
_start:
{
if (lean_obj_tag(v_lvl_2086_) == 3)
{
lean_object* v_a_2089_; lean_object* v_a_2090_; size_t v___x_2091_; size_t v___x_2092_; uint8_t v___x_2093_; 
v_a_2089_ = lean_ctor_get(v_lvl_2086_, 0);
v_a_2090_ = lean_ctor_get(v_lvl_2086_, 1);
v___x_2091_ = lean_ptr_addr(v_a_2089_);
v___x_2092_ = lean_ptr_addr(v_newLhs_2087_);
v___x_2093_ = lean_usize_dec_eq(v___x_2091_, v___x_2092_);
if (v___x_2093_ == 0)
{
lean_object* v___x_2094_; 
v___x_2094_ = l_Lean_mkLevelIMax_x27(v_newLhs_2087_, v_newRhs_2088_);
return v___x_2094_;
}
else
{
size_t v___x_2095_; size_t v___x_2096_; uint8_t v___x_2097_; 
v___x_2095_ = lean_ptr_addr(v_a_2090_);
v___x_2096_ = lean_ptr_addr(v_newRhs_2088_);
v___x_2097_ = lean_usize_dec_eq(v___x_2095_, v___x_2096_);
if (v___x_2097_ == 0)
{
lean_object* v___x_2098_; 
v___x_2098_ = l_Lean_mkLevelIMax_x27(v_newLhs_2087_, v_newRhs_2088_);
return v___x_2098_;
}
else
{
lean_object* v___x_2099_; 
v___x_2099_ = l_Lean_simpLevelIMax_x27(v_newLhs_2087_, v_newRhs_2088_, v_lvl_2086_);
return v___x_2099_;
}
}
}
else
{
lean_object* v___x_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; 
lean_dec(v_newRhs_2088_);
lean_dec(v_newLhs_2087_);
v___x_2100_ = lean_box(0);
v___x_2101_ = lean_obj_once(&l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl___closed__2, &l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl___closed__2_once, _init_l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl___closed__2);
v___x_2102_ = l_panic___redArg(v___x_2100_, v___x_2101_);
return v___x_2102_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl___boxed(lean_object* v_lvl_2103_, lean_object* v_newLhs_2104_, lean_object* v_newRhs_2105_){
_start:
{
lean_object* v_res_2106_; 
v_res_2106_ = l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl(v_lvl_2103_, v_newLhs_2104_, v_newRhs_2105_);
lean_dec(v_lvl_2103_);
return v_res_2106_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_mkNaryMax(lean_object* v_x_2107_){
_start:
{
if (lean_obj_tag(v_x_2107_) == 0)
{
lean_object* v___x_2108_; 
v___x_2108_ = lean_box(0);
return v___x_2108_;
}
else
{
lean_object* v_tail_2109_; 
v_tail_2109_ = lean_ctor_get(v_x_2107_, 1);
if (lean_obj_tag(v_tail_2109_) == 0)
{
lean_object* v_head_2110_; 
v_head_2110_ = lean_ctor_get(v_x_2107_, 0);
lean_inc(v_head_2110_);
lean_dec_ref_known(v_x_2107_, 2);
return v_head_2110_;
}
else
{
lean_object* v_head_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; 
lean_inc(v_tail_2109_);
v_head_2111_ = lean_ctor_get(v_x_2107_, 0);
lean_inc(v_head_2111_);
lean_dec_ref_known(v_x_2107_, 2);
v___x_2112_ = l_Lean_Level_mkNaryMax(v_tail_2109_);
v___x_2113_ = l_Lean_mkLevelMax_x27(v_head_2111_, v___x_2112_);
return v___x_2113_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_substParams_go(lean_object* v_s_2114_, lean_object* v_u_2115_){
_start:
{
switch(lean_obj_tag(v_u_2115_))
{
case 0:
{
lean_dec_ref(v_s_2114_);
return v_u_2115_;
}
case 1:
{
lean_object* v_a_2116_; uint8_t v___x_2117_; 
v_a_2116_ = lean_ctor_get(v_u_2115_, 0);
v___x_2117_ = l_Lean_Level_hasParam(v_u_2115_);
if (v___x_2117_ == 0)
{
lean_dec_ref(v_s_2114_);
return v_u_2115_;
}
else
{
lean_object* v___x_2118_; size_t v___x_2119_; size_t v___x_2120_; uint8_t v___x_2121_; 
lean_inc(v_a_2116_);
v___x_2118_ = l___private_Lean_Level_0__Lean_Level_substParams_go(v_s_2114_, v_a_2116_);
v___x_2119_ = lean_ptr_addr(v_a_2116_);
v___x_2120_ = lean_ptr_addr(v___x_2118_);
v___x_2121_ = lean_usize_dec_eq(v___x_2119_, v___x_2120_);
if (v___x_2121_ == 0)
{
lean_object* v___x_2122_; 
lean_dec_ref_known(v_u_2115_, 1);
v___x_2122_ = l_Lean_Level_succ___override(v___x_2118_);
return v___x_2122_;
}
else
{
lean_dec(v___x_2118_);
return v_u_2115_;
}
}
}
case 2:
{
lean_object* v_a_2123_; lean_object* v_a_2124_; uint8_t v___x_2125_; 
v_a_2123_ = lean_ctor_get(v_u_2115_, 0);
v_a_2124_ = lean_ctor_get(v_u_2115_, 1);
v___x_2125_ = l_Lean_Level_hasParam(v_u_2115_);
if (v___x_2125_ == 0)
{
lean_dec_ref(v_s_2114_);
return v_u_2115_;
}
else
{
lean_object* v___x_2126_; lean_object* v___x_2127_; size_t v___x_2128_; size_t v___x_2129_; uint8_t v___x_2130_; 
lean_inc(v_a_2123_);
lean_inc_ref(v_s_2114_);
v___x_2126_ = l___private_Lean_Level_0__Lean_Level_substParams_go(v_s_2114_, v_a_2123_);
lean_inc(v_a_2124_);
v___x_2127_ = l___private_Lean_Level_0__Lean_Level_substParams_go(v_s_2114_, v_a_2124_);
v___x_2128_ = lean_ptr_addr(v_a_2123_);
v___x_2129_ = lean_ptr_addr(v___x_2126_);
v___x_2130_ = lean_usize_dec_eq(v___x_2128_, v___x_2129_);
if (v___x_2130_ == 0)
{
lean_object* v___x_2131_; 
lean_dec_ref_known(v_u_2115_, 2);
v___x_2131_ = l_Lean_mkLevelMax_x27(v___x_2126_, v___x_2127_);
return v___x_2131_;
}
else
{
size_t v___x_2132_; size_t v___x_2133_; uint8_t v___x_2134_; 
v___x_2132_ = lean_ptr_addr(v_a_2124_);
v___x_2133_ = lean_ptr_addr(v___x_2127_);
v___x_2134_ = lean_usize_dec_eq(v___x_2132_, v___x_2133_);
if (v___x_2134_ == 0)
{
lean_object* v___x_2135_; 
lean_dec_ref_known(v_u_2115_, 2);
v___x_2135_ = l_Lean_mkLevelMax_x27(v___x_2126_, v___x_2127_);
return v___x_2135_;
}
else
{
lean_object* v___x_2136_; 
v___x_2136_ = l_Lean_simpLevelMax_x27(v___x_2126_, v___x_2127_, v_u_2115_);
lean_dec_ref_known(v_u_2115_, 2);
lean_dec(v___x_2127_);
lean_dec(v___x_2126_);
return v___x_2136_;
}
}
}
}
case 3:
{
lean_object* v_a_2137_; lean_object* v_a_2138_; uint8_t v___x_2139_; 
v_a_2137_ = lean_ctor_get(v_u_2115_, 0);
v_a_2138_ = lean_ctor_get(v_u_2115_, 1);
v___x_2139_ = l_Lean_Level_hasParam(v_u_2115_);
if (v___x_2139_ == 0)
{
lean_dec_ref(v_s_2114_);
return v_u_2115_;
}
else
{
lean_object* v___x_2140_; lean_object* v___x_2141_; size_t v___x_2142_; size_t v___x_2143_; uint8_t v___x_2144_; 
lean_inc(v_a_2137_);
lean_inc_ref(v_s_2114_);
v___x_2140_ = l___private_Lean_Level_0__Lean_Level_substParams_go(v_s_2114_, v_a_2137_);
lean_inc(v_a_2138_);
v___x_2141_ = l___private_Lean_Level_0__Lean_Level_substParams_go(v_s_2114_, v_a_2138_);
v___x_2142_ = lean_ptr_addr(v_a_2137_);
v___x_2143_ = lean_ptr_addr(v___x_2140_);
v___x_2144_ = lean_usize_dec_eq(v___x_2142_, v___x_2143_);
if (v___x_2144_ == 0)
{
lean_object* v___x_2145_; 
lean_dec_ref_known(v_u_2115_, 2);
v___x_2145_ = l_Lean_mkLevelIMax_x27(v___x_2140_, v___x_2141_);
return v___x_2145_;
}
else
{
size_t v___x_2146_; size_t v___x_2147_; uint8_t v___x_2148_; 
v___x_2146_ = lean_ptr_addr(v_a_2138_);
v___x_2147_ = lean_ptr_addr(v___x_2141_);
v___x_2148_ = lean_usize_dec_eq(v___x_2146_, v___x_2147_);
if (v___x_2148_ == 0)
{
lean_object* v___x_2149_; 
lean_dec_ref_known(v_u_2115_, 2);
v___x_2149_ = l_Lean_mkLevelIMax_x27(v___x_2140_, v___x_2141_);
return v___x_2149_;
}
else
{
lean_object* v___x_2150_; 
v___x_2150_ = l_Lean_simpLevelIMax_x27(v___x_2140_, v___x_2141_, v_u_2115_);
lean_dec_ref_known(v_u_2115_, 2);
return v___x_2150_;
}
}
}
}
case 4:
{
lean_object* v_a_2151_; lean_object* v___x_2152_; 
v_a_2151_ = lean_ctor_get(v_u_2115_, 0);
lean_inc(v_a_2151_);
v___x_2152_ = lean_apply_1(v_s_2114_, v_a_2151_);
if (lean_obj_tag(v___x_2152_) == 0)
{
return v_u_2115_;
}
else
{
lean_object* v_val_2153_; 
lean_dec_ref_known(v_u_2115_, 1);
v_val_2153_ = lean_ctor_get(v___x_2152_, 0);
lean_inc(v_val_2153_);
lean_dec_ref_known(v___x_2152_, 1);
return v_val_2153_;
}
}
default: 
{
lean_dec_ref(v_s_2114_);
return v_u_2115_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_substParams(lean_object* v_u_2154_, lean_object* v_s_2155_){
_start:
{
lean_object* v___x_2156_; 
v___x_2156_ = l___private_Lean_Level_0__Lean_Level_substParams_go(v_s_2155_, v_u_2154_);
return v___x_2156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_getParamSubst(lean_object* v_x_2157_, lean_object* v_x_2158_, lean_object* v_x_2159_){
_start:
{
if (lean_obj_tag(v_x_2157_) == 1)
{
if (lean_obj_tag(v_x_2158_) == 1)
{
lean_object* v_head_2160_; lean_object* v_tail_2161_; lean_object* v_head_2162_; lean_object* v_tail_2163_; uint8_t v___x_2164_; 
v_head_2160_ = lean_ctor_get(v_x_2157_, 0);
v_tail_2161_ = lean_ctor_get(v_x_2157_, 1);
v_head_2162_ = lean_ctor_get(v_x_2158_, 0);
v_tail_2163_ = lean_ctor_get(v_x_2158_, 1);
v___x_2164_ = lean_name_eq(v_head_2160_, v_x_2159_);
if (v___x_2164_ == 0)
{
v_x_2157_ = v_tail_2161_;
v_x_2158_ = v_tail_2163_;
goto _start;
}
else
{
lean_object* v___x_2166_; 
lean_inc(v_head_2162_);
v___x_2166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2166_, 0, v_head_2162_);
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
else
{
lean_object* v___x_2168_; 
v___x_2168_ = lean_box(0);
return v___x_2168_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_getParamSubst___boxed(lean_object* v_x_2169_, lean_object* v_x_2170_, lean_object* v_x_2171_){
_start:
{
lean_object* v_res_2172_; 
v_res_2172_ = l_Lean_Level_getParamSubst(v_x_2169_, v_x_2170_, v_x_2171_);
lean_dec(v_x_2171_);
lean_dec(v_x_2170_);
lean_dec(v_x_2169_);
return v_res_2172_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_instantiateParams(lean_object* v_u_2173_, lean_object* v_paramNames_2174_, lean_object* v_vs_2175_){
_start:
{
lean_object* v___x_2176_; lean_object* v___x_2177_; 
v___x_2176_ = lean_alloc_closure((void*)(l_Lean_Level_getParamSubst___boxed), 3, 2);
lean_closure_set(v___x_2176_, 0, v_paramNames_2174_);
lean_closure_set(v___x_2176_, 1, v_vs_2175_);
v___x_2177_ = l___private_Lean_Level_0__Lean_Level_substParams_go(v___x_2176_, v_u_2173_);
return v___x_2177_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Level_0__Lean_Level_geq_go(lean_object* v_u_2178_, lean_object* v_v_2179_){
_start:
{
uint8_t v___y_2181_; uint8_t v___y_2195_; lean_object* v_u_u2081_2197_; lean_object* v_u_u2082_2198_; lean_object* v_v_2199_; uint8_t v___x_2202_; 
v___x_2202_ = lean_level_eq(v_u_2178_, v_v_2179_);
if (v___x_2202_ == 0)
{
switch(lean_obj_tag(v_v_2179_))
{
case 0:
{
uint8_t v___x_2203_; 
v___x_2203_ = 1;
return v___x_2203_;
}
case 2:
{
lean_object* v_a_2204_; lean_object* v_a_2205_; uint8_t v___x_2206_; 
v_a_2204_ = lean_ctor_get(v_v_2179_, 0);
v_a_2205_ = lean_ctor_get(v_v_2179_, 1);
v___x_2206_ = l___private_Lean_Level_0__Lean_Level_geq_go(v_u_2178_, v_a_2204_);
if (v___x_2206_ == 0)
{
return v___x_2206_;
}
else
{
v_v_2179_ = v_a_2205_;
goto _start;
}
}
case 1:
{
switch(lean_obj_tag(v_u_2178_))
{
case 2:
{
lean_object* v_a_2208_; lean_object* v_a_2209_; 
v_a_2208_ = lean_ctor_get(v_u_2178_, 0);
v_a_2209_ = lean_ctor_get(v_u_2178_, 1);
v_u_u2081_2197_ = v_a_2208_;
v_u_u2082_2198_ = v_a_2209_;
v_v_2199_ = v_v_2179_;
goto v___jp_2196_;
}
case 3:
{
lean_object* v_a_2210_; 
v_a_2210_ = lean_ctor_get(v_u_2178_, 1);
v_u_2178_ = v_a_2210_;
goto _start;
}
case 1:
{
lean_object* v_a_2212_; lean_object* v_a_2213_; 
v_a_2212_ = lean_ctor_get(v_v_2179_, 0);
v_a_2213_ = lean_ctor_get(v_u_2178_, 0);
v_u_2178_ = v_a_2213_;
v_v_2179_ = v_a_2212_;
goto _start;
}
default: 
{
goto v___jp_2185_;
}
}
}
default: 
{
switch(lean_obj_tag(v_u_2178_))
{
case 2:
{
lean_object* v_a_2215_; lean_object* v_a_2216_; 
v_a_2215_ = lean_ctor_get(v_u_2178_, 0);
v_a_2216_ = lean_ctor_get(v_u_2178_, 1);
v_u_u2081_2197_ = v_a_2215_;
v_u_u2082_2198_ = v_a_2216_;
v_v_2199_ = v_v_2179_;
goto v___jp_2196_;
}
case 3:
{
lean_object* v_a_2217_; 
v_a_2217_ = lean_ctor_get(v_u_2178_, 1);
v_u_2178_ = v_a_2217_;
goto _start;
}
default: 
{
goto v___jp_2185_;
}
}
}
}
}
else
{
return v___x_2202_;
}
v___jp_2180_:
{
if (v___y_2181_ == 0)
{
return v___y_2181_;
}
else
{
lean_object* v___x_2182_; lean_object* v___x_2183_; uint8_t v___x_2184_; 
v___x_2182_ = l_Lean_Level_getOffset(v_v_2179_);
v___x_2183_ = l_Lean_Level_getOffset(v_u_2178_);
v___x_2184_ = lean_nat_dec_le(v___x_2182_, v___x_2183_);
lean_dec(v___x_2183_);
lean_dec(v___x_2182_);
return v___x_2184_;
}
}
v___jp_2185_:
{
if (lean_obj_tag(v_v_2179_) == 3)
{
lean_object* v_a_2186_; lean_object* v_a_2187_; uint8_t v___x_2188_; 
v_a_2186_ = lean_ctor_get(v_v_2179_, 0);
v_a_2187_ = lean_ctor_get(v_v_2179_, 1);
v___x_2188_ = l___private_Lean_Level_0__Lean_Level_geq_go(v_u_2178_, v_a_2186_);
if (v___x_2188_ == 0)
{
return v___x_2188_;
}
else
{
v_v_2179_ = v_a_2187_;
goto _start;
}
}
else
{
lean_object* v_v_x27_2190_; lean_object* v___x_2191_; uint8_t v___x_2192_; 
v_v_x27_2190_ = l_Lean_Level_getLevelOffset(v_v_2179_);
v___x_2191_ = l_Lean_Level_getLevelOffset(v_u_2178_);
v___x_2192_ = lean_level_eq(v___x_2191_, v_v_x27_2190_);
lean_dec(v___x_2191_);
if (v___x_2192_ == 0)
{
uint8_t v___x_2193_; 
v___x_2193_ = l_Lean_Level_isZero(v_v_x27_2190_);
lean_dec(v_v_x27_2190_);
v___y_2181_ = v___x_2193_;
goto v___jp_2180_;
}
else
{
lean_dec(v_v_x27_2190_);
v___y_2181_ = v___x_2192_;
goto v___jp_2180_;
}
}
}
v___jp_2194_:
{
if (v___y_2195_ == 0)
{
goto v___jp_2185_;
}
else
{
return v___y_2195_;
}
}
v___jp_2196_:
{
uint8_t v___x_2200_; 
v___x_2200_ = l___private_Lean_Level_0__Lean_Level_geq_go(v_u_u2081_2197_, v_v_2199_);
if (v___x_2200_ == 0)
{
uint8_t v___x_2201_; 
v___x_2201_ = l___private_Lean_Level_0__Lean_Level_geq_go(v_u_u2082_2198_, v_v_2199_);
v___y_2195_ = v___x_2201_;
goto v___jp_2194_;
}
else
{
v___y_2195_ = v___x_2200_;
goto v___jp_2194_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_geq_go___boxed(lean_object* v_u_2219_, lean_object* v_v_2220_){
_start:
{
uint8_t v_res_2221_; lean_object* v_r_2222_; 
v_res_2221_ = l___private_Lean_Level_0__Lean_Level_geq_go(v_u_2219_, v_v_2220_);
lean_dec(v_v_2220_);
lean_dec(v_u_2219_);
v_r_2222_ = lean_box(v_res_2221_);
return v_r_2222_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_geq_go_match__1_splitter___redArg(lean_object* v_u_2223_, lean_object* v_v_2224_, lean_object* v_h__1_2225_, lean_object* v_h__2_2226_, lean_object* v_h__3_2227_, lean_object* v_h__4_2228_, lean_object* v_h__5_2229_, lean_object* v_h__6_2230_){
_start:
{
switch(lean_obj_tag(v_v_2224_))
{
case 0:
{
lean_object* v___x_2231_; 
lean_dec(v_h__6_2230_);
lean_dec(v_h__5_2229_);
lean_dec(v_h__4_2228_);
lean_dec(v_h__3_2227_);
lean_dec(v_h__2_2226_);
v___x_2231_ = lean_apply_1(v_h__1_2225_, v_u_2223_);
return v___x_2231_;
}
case 2:
{
lean_object* v_a_2232_; lean_object* v_a_2233_; lean_object* v___x_2234_; 
lean_dec(v_h__6_2230_);
lean_dec(v_h__5_2229_);
lean_dec(v_h__4_2228_);
lean_dec(v_h__3_2227_);
lean_dec(v_h__1_2225_);
v_a_2232_ = lean_ctor_get(v_v_2224_, 0);
lean_inc(v_a_2232_);
v_a_2233_ = lean_ctor_get(v_v_2224_, 1);
lean_inc(v_a_2233_);
lean_dec_ref_known(v_v_2224_, 2);
v___x_2234_ = lean_apply_3(v_h__2_2226_, v_u_2223_, v_a_2232_, v_a_2233_);
return v___x_2234_;
}
case 1:
{
lean_dec(v_h__2_2226_);
lean_dec(v_h__1_2225_);
switch(lean_obj_tag(v_u_2223_))
{
case 2:
{
lean_object* v_a_2235_; lean_object* v_a_2236_; lean_object* v___x_2237_; 
lean_dec(v_h__6_2230_);
lean_dec(v_h__5_2229_);
lean_dec(v_h__4_2228_);
v_a_2235_ = lean_ctor_get(v_u_2223_, 0);
lean_inc(v_a_2235_);
v_a_2236_ = lean_ctor_get(v_u_2223_, 1);
lean_inc(v_a_2236_);
lean_dec_ref_known(v_u_2223_, 2);
v___x_2237_ = lean_apply_5(v_h__3_2227_, v_a_2235_, v_a_2236_, v_v_2224_, lean_box(0), lean_box(0));
return v___x_2237_;
}
case 3:
{
lean_object* v_a_2238_; lean_object* v_a_2239_; lean_object* v___x_2240_; 
lean_dec(v_h__6_2230_);
lean_dec(v_h__5_2229_);
lean_dec(v_h__3_2227_);
v_a_2238_ = lean_ctor_get(v_u_2223_, 0);
lean_inc(v_a_2238_);
v_a_2239_ = lean_ctor_get(v_u_2223_, 1);
lean_inc(v_a_2239_);
lean_dec_ref_known(v_u_2223_, 2);
v___x_2240_ = lean_apply_5(v_h__4_2228_, v_a_2238_, v_a_2239_, v_v_2224_, lean_box(0), lean_box(0));
return v___x_2240_;
}
case 1:
{
lean_object* v_a_2241_; lean_object* v_a_2242_; lean_object* v___x_2243_; 
lean_dec(v_h__6_2230_);
lean_dec(v_h__4_2228_);
lean_dec(v_h__3_2227_);
v_a_2241_ = lean_ctor_get(v_v_2224_, 0);
lean_inc(v_a_2241_);
lean_dec_ref_known(v_v_2224_, 1);
v_a_2242_ = lean_ctor_get(v_u_2223_, 0);
lean_inc(v_a_2242_);
lean_dec_ref_known(v_u_2223_, 1);
v___x_2243_ = lean_apply_2(v_h__5_2229_, v_a_2242_, v_a_2241_);
return v___x_2243_;
}
default: 
{
lean_object* v___x_2244_; 
lean_dec(v_h__5_2229_);
lean_dec(v_h__4_2228_);
lean_dec(v_h__3_2227_);
v___x_2244_ = lean_apply_7(v_h__6_2230_, v_u_2223_, v_v_2224_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_2244_;
}
}
}
default: 
{
lean_dec(v_h__5_2229_);
lean_dec(v_h__2_2226_);
lean_dec(v_h__1_2225_);
switch(lean_obj_tag(v_u_2223_))
{
case 2:
{
lean_object* v_a_2245_; lean_object* v_a_2246_; lean_object* v___x_2247_; 
lean_dec(v_h__6_2230_);
lean_dec(v_h__4_2228_);
v_a_2245_ = lean_ctor_get(v_u_2223_, 0);
lean_inc(v_a_2245_);
v_a_2246_ = lean_ctor_get(v_u_2223_, 1);
lean_inc(v_a_2246_);
lean_dec_ref_known(v_u_2223_, 2);
v___x_2247_ = lean_apply_5(v_h__3_2227_, v_a_2245_, v_a_2246_, v_v_2224_, lean_box(0), lean_box(0));
return v___x_2247_;
}
case 3:
{
lean_object* v_a_2248_; lean_object* v_a_2249_; lean_object* v___x_2250_; 
lean_dec(v_h__6_2230_);
lean_dec(v_h__3_2227_);
v_a_2248_ = lean_ctor_get(v_u_2223_, 0);
lean_inc(v_a_2248_);
v_a_2249_ = lean_ctor_get(v_u_2223_, 1);
lean_inc(v_a_2249_);
lean_dec_ref_known(v_u_2223_, 2);
v___x_2250_ = lean_apply_5(v_h__4_2228_, v_a_2248_, v_a_2249_, v_v_2224_, lean_box(0), lean_box(0));
return v___x_2250_;
}
default: 
{
lean_object* v___x_2251_; 
lean_dec(v_h__4_2228_);
lean_dec(v_h__3_2227_);
v___x_2251_ = lean_apply_7(v_h__6_2230_, v_u_2223_, v_v_2224_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_2251_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_geq_go_match__1_splitter(lean_object* v_motive_2252_, lean_object* v_u_2253_, lean_object* v_v_2254_, lean_object* v_h__1_2255_, lean_object* v_h__2_2256_, lean_object* v_h__3_2257_, lean_object* v_h__4_2258_, lean_object* v_h__5_2259_, lean_object* v_h__6_2260_){
_start:
{
switch(lean_obj_tag(v_v_2254_))
{
case 0:
{
lean_object* v___x_2261_; 
lean_dec(v_h__6_2260_);
lean_dec(v_h__5_2259_);
lean_dec(v_h__4_2258_);
lean_dec(v_h__3_2257_);
lean_dec(v_h__2_2256_);
v___x_2261_ = lean_apply_1(v_h__1_2255_, v_u_2253_);
return v___x_2261_;
}
case 2:
{
lean_object* v_a_2262_; lean_object* v_a_2263_; lean_object* v___x_2264_; 
lean_dec(v_h__6_2260_);
lean_dec(v_h__5_2259_);
lean_dec(v_h__4_2258_);
lean_dec(v_h__3_2257_);
lean_dec(v_h__1_2255_);
v_a_2262_ = lean_ctor_get(v_v_2254_, 0);
lean_inc(v_a_2262_);
v_a_2263_ = lean_ctor_get(v_v_2254_, 1);
lean_inc(v_a_2263_);
lean_dec_ref_known(v_v_2254_, 2);
v___x_2264_ = lean_apply_3(v_h__2_2256_, v_u_2253_, v_a_2262_, v_a_2263_);
return v___x_2264_;
}
case 1:
{
lean_dec(v_h__2_2256_);
lean_dec(v_h__1_2255_);
switch(lean_obj_tag(v_u_2253_))
{
case 2:
{
lean_object* v_a_2265_; lean_object* v_a_2266_; lean_object* v___x_2267_; 
lean_dec(v_h__6_2260_);
lean_dec(v_h__5_2259_);
lean_dec(v_h__4_2258_);
v_a_2265_ = lean_ctor_get(v_u_2253_, 0);
lean_inc(v_a_2265_);
v_a_2266_ = lean_ctor_get(v_u_2253_, 1);
lean_inc(v_a_2266_);
lean_dec_ref_known(v_u_2253_, 2);
v___x_2267_ = lean_apply_5(v_h__3_2257_, v_a_2265_, v_a_2266_, v_v_2254_, lean_box(0), lean_box(0));
return v___x_2267_;
}
case 3:
{
lean_object* v_a_2268_; lean_object* v_a_2269_; lean_object* v___x_2270_; 
lean_dec(v_h__6_2260_);
lean_dec(v_h__5_2259_);
lean_dec(v_h__3_2257_);
v_a_2268_ = lean_ctor_get(v_u_2253_, 0);
lean_inc(v_a_2268_);
v_a_2269_ = lean_ctor_get(v_u_2253_, 1);
lean_inc(v_a_2269_);
lean_dec_ref_known(v_u_2253_, 2);
v___x_2270_ = lean_apply_5(v_h__4_2258_, v_a_2268_, v_a_2269_, v_v_2254_, lean_box(0), lean_box(0));
return v___x_2270_;
}
case 1:
{
lean_object* v_a_2271_; lean_object* v_a_2272_; lean_object* v___x_2273_; 
lean_dec(v_h__6_2260_);
lean_dec(v_h__4_2258_);
lean_dec(v_h__3_2257_);
v_a_2271_ = lean_ctor_get(v_v_2254_, 0);
lean_inc(v_a_2271_);
lean_dec_ref_known(v_v_2254_, 1);
v_a_2272_ = lean_ctor_get(v_u_2253_, 0);
lean_inc(v_a_2272_);
lean_dec_ref_known(v_u_2253_, 1);
v___x_2273_ = lean_apply_2(v_h__5_2259_, v_a_2272_, v_a_2271_);
return v___x_2273_;
}
default: 
{
lean_object* v___x_2274_; 
lean_dec(v_h__5_2259_);
lean_dec(v_h__4_2258_);
lean_dec(v_h__3_2257_);
v___x_2274_ = lean_apply_7(v_h__6_2260_, v_u_2253_, v_v_2254_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_2274_;
}
}
}
default: 
{
lean_dec(v_h__5_2259_);
lean_dec(v_h__2_2256_);
lean_dec(v_h__1_2255_);
switch(lean_obj_tag(v_u_2253_))
{
case 2:
{
lean_object* v_a_2275_; lean_object* v_a_2276_; lean_object* v___x_2277_; 
lean_dec(v_h__6_2260_);
lean_dec(v_h__4_2258_);
v_a_2275_ = lean_ctor_get(v_u_2253_, 0);
lean_inc(v_a_2275_);
v_a_2276_ = lean_ctor_get(v_u_2253_, 1);
lean_inc(v_a_2276_);
lean_dec_ref_known(v_u_2253_, 2);
v___x_2277_ = lean_apply_5(v_h__3_2257_, v_a_2275_, v_a_2276_, v_v_2254_, lean_box(0), lean_box(0));
return v___x_2277_;
}
case 3:
{
lean_object* v_a_2278_; lean_object* v_a_2279_; lean_object* v___x_2280_; 
lean_dec(v_h__6_2260_);
lean_dec(v_h__3_2257_);
v_a_2278_ = lean_ctor_get(v_u_2253_, 0);
lean_inc(v_a_2278_);
v_a_2279_ = lean_ctor_get(v_u_2253_, 1);
lean_inc(v_a_2279_);
lean_dec_ref_known(v_u_2253_, 2);
v___x_2280_ = lean_apply_5(v_h__4_2258_, v_a_2278_, v_a_2279_, v_v_2254_, lean_box(0), lean_box(0));
return v___x_2280_;
}
default: 
{
lean_object* v___x_2281_; 
lean_dec(v_h__4_2258_);
lean_dec(v_h__3_2257_);
v___x_2281_ = lean_apply_7(v_h__6_2260_, v_u_2253_, v_v_2254_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_2281_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_isIMax_match__1_splitter___redArg(lean_object* v_x_2282_, lean_object* v_h__1_2283_, lean_object* v_h__2_2284_){
_start:
{
if (lean_obj_tag(v_x_2282_) == 3)
{
lean_object* v_a_2285_; lean_object* v_a_2286_; lean_object* v___x_2287_; 
lean_dec(v_h__2_2284_);
v_a_2285_ = lean_ctor_get(v_x_2282_, 0);
lean_inc(v_a_2285_);
v_a_2286_ = lean_ctor_get(v_x_2282_, 1);
lean_inc(v_a_2286_);
lean_dec_ref_known(v_x_2282_, 2);
v___x_2287_ = lean_apply_2(v_h__1_2283_, v_a_2285_, v_a_2286_);
return v___x_2287_;
}
else
{
lean_object* v___x_2288_; 
lean_dec(v_h__1_2283_);
v___x_2288_ = lean_apply_2(v_h__2_2284_, v_x_2282_, lean_box(0));
return v___x_2288_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_isIMax_match__1_splitter(lean_object* v_motive_2289_, lean_object* v_x_2290_, lean_object* v_h__1_2291_, lean_object* v_h__2_2292_){
_start:
{
if (lean_obj_tag(v_x_2290_) == 3)
{
lean_object* v_a_2293_; lean_object* v_a_2294_; lean_object* v___x_2295_; 
lean_dec(v_h__2_2292_);
v_a_2293_ = lean_ctor_get(v_x_2290_, 0);
lean_inc(v_a_2293_);
v_a_2294_ = lean_ctor_get(v_x_2290_, 1);
lean_inc(v_a_2294_);
lean_dec_ref_known(v_x_2290_, 2);
v___x_2295_ = lean_apply_2(v_h__1_2291_, v_a_2293_, v_a_2294_);
return v___x_2295_;
}
else
{
lean_object* v___x_2296_; 
lean_dec(v_h__1_2291_);
v___x_2296_ = lean_apply_2(v_h__2_2292_, v_x_2290_, lean_box(0));
return v___x_2296_;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Level_geq(lean_object* v_u_2297_, lean_object* v_v_2298_){
_start:
{
lean_object* v___x_2299_; lean_object* v___x_2300_; uint8_t v___x_2301_; 
v___x_2299_ = l_Lean_Level_normalize(v_u_2297_);
v___x_2300_ = l_Lean_Level_normalize(v_v_2298_);
v___x_2301_ = l___private_Lean_Level_0__Lean_Level_geq_go(v___x_2299_, v___x_2300_);
lean_dec(v___x_2300_);
lean_dec(v___x_2299_);
return v___x_2301_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_geq___boxed(lean_object* v_u_2302_, lean_object* v_v_2303_){
_start:
{
uint8_t v_res_2304_; lean_object* v_r_2305_; 
v_res_2304_ = l_Lean_Level_geq(v_u_2302_, v_v_2303_);
lean_dec(v_v_2303_);
lean_dec(v_u_2302_);
v_r_2305_ = lean_box(v_res_2304_);
return v_r_2305_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Level_collectMVars_spec__1___redArg(lean_object* v_k_2306_, lean_object* v_v_2307_, lean_object* v_t_2308_){
_start:
{
if (lean_obj_tag(v_t_2308_) == 0)
{
lean_object* v_size_2309_; lean_object* v_k_2310_; lean_object* v_v_2311_; lean_object* v_l_2312_; lean_object* v_r_2313_; lean_object* v___x_2315_; uint8_t v_isShared_2316_; uint8_t v_isSharedCheck_2593_; 
v_size_2309_ = lean_ctor_get(v_t_2308_, 0);
v_k_2310_ = lean_ctor_get(v_t_2308_, 1);
v_v_2311_ = lean_ctor_get(v_t_2308_, 2);
v_l_2312_ = lean_ctor_get(v_t_2308_, 3);
v_r_2313_ = lean_ctor_get(v_t_2308_, 4);
v_isSharedCheck_2593_ = !lean_is_exclusive(v_t_2308_);
if (v_isSharedCheck_2593_ == 0)
{
v___x_2315_ = v_t_2308_;
v_isShared_2316_ = v_isSharedCheck_2593_;
goto v_resetjp_2314_;
}
else
{
lean_inc(v_r_2313_);
lean_inc(v_l_2312_);
lean_inc(v_v_2311_);
lean_inc(v_k_2310_);
lean_inc(v_size_2309_);
lean_dec(v_t_2308_);
v___x_2315_ = lean_box(0);
v_isShared_2316_ = v_isSharedCheck_2593_;
goto v_resetjp_2314_;
}
v_resetjp_2314_:
{
uint8_t v___x_2317_; 
v___x_2317_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2306_, v_k_2310_);
switch(v___x_2317_)
{
case 0:
{
lean_object* v_impl_2318_; lean_object* v___x_2319_; 
lean_dec(v_size_2309_);
v_impl_2318_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Level_collectMVars_spec__1___redArg(v_k_2306_, v_v_2307_, v_l_2312_);
v___x_2319_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_2313_) == 0)
{
lean_object* v_size_2320_; lean_object* v_size_2321_; lean_object* v_k_2322_; lean_object* v_v_2323_; lean_object* v_l_2324_; lean_object* v_r_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; uint8_t v___x_2328_; 
v_size_2320_ = lean_ctor_get(v_r_2313_, 0);
v_size_2321_ = lean_ctor_get(v_impl_2318_, 0);
lean_inc(v_size_2321_);
v_k_2322_ = lean_ctor_get(v_impl_2318_, 1);
lean_inc(v_k_2322_);
v_v_2323_ = lean_ctor_get(v_impl_2318_, 2);
lean_inc(v_v_2323_);
v_l_2324_ = lean_ctor_get(v_impl_2318_, 3);
lean_inc(v_l_2324_);
v_r_2325_ = lean_ctor_get(v_impl_2318_, 4);
lean_inc(v_r_2325_);
v___x_2326_ = lean_unsigned_to_nat(3u);
v___x_2327_ = lean_nat_mul(v___x_2326_, v_size_2320_);
v___x_2328_ = lean_nat_dec_lt(v___x_2327_, v_size_2321_);
lean_dec(v___x_2327_);
if (v___x_2328_ == 0)
{
lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2332_; 
lean_dec(v_r_2325_);
lean_dec(v_l_2324_);
lean_dec(v_v_2323_);
lean_dec(v_k_2322_);
v___x_2329_ = lean_nat_add(v___x_2319_, v_size_2321_);
lean_dec(v_size_2321_);
v___x_2330_ = lean_nat_add(v___x_2329_, v_size_2320_);
lean_dec(v___x_2329_);
if (v_isShared_2316_ == 0)
{
lean_ctor_set(v___x_2315_, 3, v_impl_2318_);
lean_ctor_set(v___x_2315_, 0, v___x_2330_);
v___x_2332_ = v___x_2315_;
goto v_reusejp_2331_;
}
else
{
lean_object* v_reuseFailAlloc_2333_; 
v_reuseFailAlloc_2333_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2333_, 0, v___x_2330_);
lean_ctor_set(v_reuseFailAlloc_2333_, 1, v_k_2310_);
lean_ctor_set(v_reuseFailAlloc_2333_, 2, v_v_2311_);
lean_ctor_set(v_reuseFailAlloc_2333_, 3, v_impl_2318_);
lean_ctor_set(v_reuseFailAlloc_2333_, 4, v_r_2313_);
v___x_2332_ = v_reuseFailAlloc_2333_;
goto v_reusejp_2331_;
}
v_reusejp_2331_:
{
return v___x_2332_;
}
}
else
{
lean_object* v___x_2335_; uint8_t v_isShared_2336_; uint8_t v_isSharedCheck_2399_; 
v_isSharedCheck_2399_ = !lean_is_exclusive(v_impl_2318_);
if (v_isSharedCheck_2399_ == 0)
{
lean_object* v_unused_2400_; lean_object* v_unused_2401_; lean_object* v_unused_2402_; lean_object* v_unused_2403_; lean_object* v_unused_2404_; 
v_unused_2400_ = lean_ctor_get(v_impl_2318_, 4);
lean_dec(v_unused_2400_);
v_unused_2401_ = lean_ctor_get(v_impl_2318_, 3);
lean_dec(v_unused_2401_);
v_unused_2402_ = lean_ctor_get(v_impl_2318_, 2);
lean_dec(v_unused_2402_);
v_unused_2403_ = lean_ctor_get(v_impl_2318_, 1);
lean_dec(v_unused_2403_);
v_unused_2404_ = lean_ctor_get(v_impl_2318_, 0);
lean_dec(v_unused_2404_);
v___x_2335_ = v_impl_2318_;
v_isShared_2336_ = v_isSharedCheck_2399_;
goto v_resetjp_2334_;
}
else
{
lean_dec(v_impl_2318_);
v___x_2335_ = lean_box(0);
v_isShared_2336_ = v_isSharedCheck_2399_;
goto v_resetjp_2334_;
}
v_resetjp_2334_:
{
lean_object* v_size_2337_; lean_object* v_size_2338_; lean_object* v_k_2339_; lean_object* v_v_2340_; lean_object* v_l_2341_; lean_object* v_r_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; uint8_t v___x_2345_; 
v_size_2337_ = lean_ctor_get(v_l_2324_, 0);
v_size_2338_ = lean_ctor_get(v_r_2325_, 0);
v_k_2339_ = lean_ctor_get(v_r_2325_, 1);
v_v_2340_ = lean_ctor_get(v_r_2325_, 2);
v_l_2341_ = lean_ctor_get(v_r_2325_, 3);
v_r_2342_ = lean_ctor_get(v_r_2325_, 4);
v___x_2343_ = lean_unsigned_to_nat(2u);
v___x_2344_ = lean_nat_mul(v___x_2343_, v_size_2337_);
v___x_2345_ = lean_nat_dec_lt(v_size_2338_, v___x_2344_);
lean_dec(v___x_2344_);
if (v___x_2345_ == 0)
{
lean_object* v___x_2347_; uint8_t v_isShared_2348_; uint8_t v_isSharedCheck_2374_; 
lean_inc(v_r_2342_);
lean_inc(v_l_2341_);
lean_inc(v_v_2340_);
lean_inc(v_k_2339_);
v_isSharedCheck_2374_ = !lean_is_exclusive(v_r_2325_);
if (v_isSharedCheck_2374_ == 0)
{
lean_object* v_unused_2375_; lean_object* v_unused_2376_; lean_object* v_unused_2377_; lean_object* v_unused_2378_; lean_object* v_unused_2379_; 
v_unused_2375_ = lean_ctor_get(v_r_2325_, 4);
lean_dec(v_unused_2375_);
v_unused_2376_ = lean_ctor_get(v_r_2325_, 3);
lean_dec(v_unused_2376_);
v_unused_2377_ = lean_ctor_get(v_r_2325_, 2);
lean_dec(v_unused_2377_);
v_unused_2378_ = lean_ctor_get(v_r_2325_, 1);
lean_dec(v_unused_2378_);
v_unused_2379_ = lean_ctor_get(v_r_2325_, 0);
lean_dec(v_unused_2379_);
v___x_2347_ = v_r_2325_;
v_isShared_2348_ = v_isSharedCheck_2374_;
goto v_resetjp_2346_;
}
else
{
lean_dec(v_r_2325_);
v___x_2347_ = lean_box(0);
v_isShared_2348_ = v_isSharedCheck_2374_;
goto v_resetjp_2346_;
}
v_resetjp_2346_:
{
lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___y_2352_; lean_object* v___y_2353_; lean_object* v___y_2354_; lean_object* v___x_2362_; lean_object* v___y_2364_; 
v___x_2349_ = lean_nat_add(v___x_2319_, v_size_2321_);
lean_dec(v_size_2321_);
v___x_2350_ = lean_nat_add(v___x_2349_, v_size_2320_);
lean_dec(v___x_2349_);
v___x_2362_ = lean_nat_add(v___x_2319_, v_size_2337_);
if (lean_obj_tag(v_l_2341_) == 0)
{
lean_object* v_size_2372_; 
v_size_2372_ = lean_ctor_get(v_l_2341_, 0);
lean_inc(v_size_2372_);
v___y_2364_ = v_size_2372_;
goto v___jp_2363_;
}
else
{
lean_object* v___x_2373_; 
v___x_2373_ = lean_unsigned_to_nat(0u);
v___y_2364_ = v___x_2373_;
goto v___jp_2363_;
}
v___jp_2351_:
{
lean_object* v___x_2355_; lean_object* v___x_2357_; 
v___x_2355_ = lean_nat_add(v___y_2352_, v___y_2354_);
lean_dec(v___y_2354_);
lean_dec(v___y_2352_);
if (v_isShared_2348_ == 0)
{
lean_ctor_set(v___x_2347_, 4, v_r_2313_);
lean_ctor_set(v___x_2347_, 3, v_r_2342_);
lean_ctor_set(v___x_2347_, 2, v_v_2311_);
lean_ctor_set(v___x_2347_, 1, v_k_2310_);
lean_ctor_set(v___x_2347_, 0, v___x_2355_);
v___x_2357_ = v___x_2347_;
goto v_reusejp_2356_;
}
else
{
lean_object* v_reuseFailAlloc_2361_; 
v_reuseFailAlloc_2361_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2361_, 0, v___x_2355_);
lean_ctor_set(v_reuseFailAlloc_2361_, 1, v_k_2310_);
lean_ctor_set(v_reuseFailAlloc_2361_, 2, v_v_2311_);
lean_ctor_set(v_reuseFailAlloc_2361_, 3, v_r_2342_);
lean_ctor_set(v_reuseFailAlloc_2361_, 4, v_r_2313_);
v___x_2357_ = v_reuseFailAlloc_2361_;
goto v_reusejp_2356_;
}
v_reusejp_2356_:
{
lean_object* v___x_2359_; 
if (v_isShared_2336_ == 0)
{
lean_ctor_set(v___x_2335_, 4, v___x_2357_);
lean_ctor_set(v___x_2335_, 3, v___y_2353_);
lean_ctor_set(v___x_2335_, 2, v_v_2340_);
lean_ctor_set(v___x_2335_, 1, v_k_2339_);
lean_ctor_set(v___x_2335_, 0, v___x_2350_);
v___x_2359_ = v___x_2335_;
goto v_reusejp_2358_;
}
else
{
lean_object* v_reuseFailAlloc_2360_; 
v_reuseFailAlloc_2360_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2360_, 0, v___x_2350_);
lean_ctor_set(v_reuseFailAlloc_2360_, 1, v_k_2339_);
lean_ctor_set(v_reuseFailAlloc_2360_, 2, v_v_2340_);
lean_ctor_set(v_reuseFailAlloc_2360_, 3, v___y_2353_);
lean_ctor_set(v_reuseFailAlloc_2360_, 4, v___x_2357_);
v___x_2359_ = v_reuseFailAlloc_2360_;
goto v_reusejp_2358_;
}
v_reusejp_2358_:
{
return v___x_2359_;
}
}
}
v___jp_2363_:
{
lean_object* v___x_2365_; lean_object* v___x_2367_; 
v___x_2365_ = lean_nat_add(v___x_2362_, v___y_2364_);
lean_dec(v___y_2364_);
lean_dec(v___x_2362_);
if (v_isShared_2316_ == 0)
{
lean_ctor_set(v___x_2315_, 4, v_l_2341_);
lean_ctor_set(v___x_2315_, 3, v_l_2324_);
lean_ctor_set(v___x_2315_, 2, v_v_2323_);
lean_ctor_set(v___x_2315_, 1, v_k_2322_);
lean_ctor_set(v___x_2315_, 0, v___x_2365_);
v___x_2367_ = v___x_2315_;
goto v_reusejp_2366_;
}
else
{
lean_object* v_reuseFailAlloc_2371_; 
v_reuseFailAlloc_2371_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2371_, 0, v___x_2365_);
lean_ctor_set(v_reuseFailAlloc_2371_, 1, v_k_2322_);
lean_ctor_set(v_reuseFailAlloc_2371_, 2, v_v_2323_);
lean_ctor_set(v_reuseFailAlloc_2371_, 3, v_l_2324_);
lean_ctor_set(v_reuseFailAlloc_2371_, 4, v_l_2341_);
v___x_2367_ = v_reuseFailAlloc_2371_;
goto v_reusejp_2366_;
}
v_reusejp_2366_:
{
lean_object* v___x_2368_; 
v___x_2368_ = lean_nat_add(v___x_2319_, v_size_2320_);
if (lean_obj_tag(v_r_2342_) == 0)
{
lean_object* v_size_2369_; 
v_size_2369_ = lean_ctor_get(v_r_2342_, 0);
lean_inc(v_size_2369_);
v___y_2352_ = v___x_2368_;
v___y_2353_ = v___x_2367_;
v___y_2354_ = v_size_2369_;
goto v___jp_2351_;
}
else
{
lean_object* v___x_2370_; 
v___x_2370_ = lean_unsigned_to_nat(0u);
v___y_2352_ = v___x_2368_;
v___y_2353_ = v___x_2367_;
v___y_2354_ = v___x_2370_;
goto v___jp_2351_;
}
}
}
}
}
else
{
lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2385_; 
lean_del_object(v___x_2315_);
v___x_2380_ = lean_nat_add(v___x_2319_, v_size_2321_);
lean_dec(v_size_2321_);
v___x_2381_ = lean_nat_add(v___x_2380_, v_size_2320_);
lean_dec(v___x_2380_);
v___x_2382_ = lean_nat_add(v___x_2319_, v_size_2320_);
v___x_2383_ = lean_nat_add(v___x_2382_, v_size_2338_);
lean_dec(v___x_2382_);
lean_inc_ref(v_r_2313_);
if (v_isShared_2336_ == 0)
{
lean_ctor_set(v___x_2335_, 4, v_r_2313_);
lean_ctor_set(v___x_2335_, 3, v_r_2325_);
lean_ctor_set(v___x_2335_, 2, v_v_2311_);
lean_ctor_set(v___x_2335_, 1, v_k_2310_);
lean_ctor_set(v___x_2335_, 0, v___x_2383_);
v___x_2385_ = v___x_2335_;
goto v_reusejp_2384_;
}
else
{
lean_object* v_reuseFailAlloc_2398_; 
v_reuseFailAlloc_2398_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2398_, 0, v___x_2383_);
lean_ctor_set(v_reuseFailAlloc_2398_, 1, v_k_2310_);
lean_ctor_set(v_reuseFailAlloc_2398_, 2, v_v_2311_);
lean_ctor_set(v_reuseFailAlloc_2398_, 3, v_r_2325_);
lean_ctor_set(v_reuseFailAlloc_2398_, 4, v_r_2313_);
v___x_2385_ = v_reuseFailAlloc_2398_;
goto v_reusejp_2384_;
}
v_reusejp_2384_:
{
lean_object* v___x_2387_; uint8_t v_isShared_2388_; uint8_t v_isSharedCheck_2392_; 
v_isSharedCheck_2392_ = !lean_is_exclusive(v_r_2313_);
if (v_isSharedCheck_2392_ == 0)
{
lean_object* v_unused_2393_; lean_object* v_unused_2394_; lean_object* v_unused_2395_; lean_object* v_unused_2396_; lean_object* v_unused_2397_; 
v_unused_2393_ = lean_ctor_get(v_r_2313_, 4);
lean_dec(v_unused_2393_);
v_unused_2394_ = lean_ctor_get(v_r_2313_, 3);
lean_dec(v_unused_2394_);
v_unused_2395_ = lean_ctor_get(v_r_2313_, 2);
lean_dec(v_unused_2395_);
v_unused_2396_ = lean_ctor_get(v_r_2313_, 1);
lean_dec(v_unused_2396_);
v_unused_2397_ = lean_ctor_get(v_r_2313_, 0);
lean_dec(v_unused_2397_);
v___x_2387_ = v_r_2313_;
v_isShared_2388_ = v_isSharedCheck_2392_;
goto v_resetjp_2386_;
}
else
{
lean_dec(v_r_2313_);
v___x_2387_ = lean_box(0);
v_isShared_2388_ = v_isSharedCheck_2392_;
goto v_resetjp_2386_;
}
v_resetjp_2386_:
{
lean_object* v___x_2390_; 
if (v_isShared_2388_ == 0)
{
lean_ctor_set(v___x_2387_, 4, v___x_2385_);
lean_ctor_set(v___x_2387_, 3, v_l_2324_);
lean_ctor_set(v___x_2387_, 2, v_v_2323_);
lean_ctor_set(v___x_2387_, 1, v_k_2322_);
lean_ctor_set(v___x_2387_, 0, v___x_2381_);
v___x_2390_ = v___x_2387_;
goto v_reusejp_2389_;
}
else
{
lean_object* v_reuseFailAlloc_2391_; 
v_reuseFailAlloc_2391_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2391_, 0, v___x_2381_);
lean_ctor_set(v_reuseFailAlloc_2391_, 1, v_k_2322_);
lean_ctor_set(v_reuseFailAlloc_2391_, 2, v_v_2323_);
lean_ctor_set(v_reuseFailAlloc_2391_, 3, v_l_2324_);
lean_ctor_set(v_reuseFailAlloc_2391_, 4, v___x_2385_);
v___x_2390_ = v_reuseFailAlloc_2391_;
goto v_reusejp_2389_;
}
v_reusejp_2389_:
{
return v___x_2390_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_2405_; 
v_l_2405_ = lean_ctor_get(v_impl_2318_, 3);
lean_inc(v_l_2405_);
if (lean_obj_tag(v_l_2405_) == 0)
{
lean_object* v_r_2406_; lean_object* v_k_2407_; lean_object* v_v_2408_; lean_object* v___x_2410_; uint8_t v_isShared_2411_; uint8_t v_isSharedCheck_2419_; 
v_r_2406_ = lean_ctor_get(v_impl_2318_, 4);
v_k_2407_ = lean_ctor_get(v_impl_2318_, 1);
v_v_2408_ = lean_ctor_get(v_impl_2318_, 2);
v_isSharedCheck_2419_ = !lean_is_exclusive(v_impl_2318_);
if (v_isSharedCheck_2419_ == 0)
{
lean_object* v_unused_2420_; lean_object* v_unused_2421_; 
v_unused_2420_ = lean_ctor_get(v_impl_2318_, 3);
lean_dec(v_unused_2420_);
v_unused_2421_ = lean_ctor_get(v_impl_2318_, 0);
lean_dec(v_unused_2421_);
v___x_2410_ = v_impl_2318_;
v_isShared_2411_ = v_isSharedCheck_2419_;
goto v_resetjp_2409_;
}
else
{
lean_inc(v_r_2406_);
lean_inc(v_v_2408_);
lean_inc(v_k_2407_);
lean_dec(v_impl_2318_);
v___x_2410_ = lean_box(0);
v_isShared_2411_ = v_isSharedCheck_2419_;
goto v_resetjp_2409_;
}
v_resetjp_2409_:
{
lean_object* v___x_2412_; lean_object* v___x_2414_; 
v___x_2412_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_2406_);
if (v_isShared_2411_ == 0)
{
lean_ctor_set(v___x_2410_, 3, v_r_2406_);
lean_ctor_set(v___x_2410_, 2, v_v_2311_);
lean_ctor_set(v___x_2410_, 1, v_k_2310_);
lean_ctor_set(v___x_2410_, 0, v___x_2319_);
v___x_2414_ = v___x_2410_;
goto v_reusejp_2413_;
}
else
{
lean_object* v_reuseFailAlloc_2418_; 
v_reuseFailAlloc_2418_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2418_, 0, v___x_2319_);
lean_ctor_set(v_reuseFailAlloc_2418_, 1, v_k_2310_);
lean_ctor_set(v_reuseFailAlloc_2418_, 2, v_v_2311_);
lean_ctor_set(v_reuseFailAlloc_2418_, 3, v_r_2406_);
lean_ctor_set(v_reuseFailAlloc_2418_, 4, v_r_2406_);
v___x_2414_ = v_reuseFailAlloc_2418_;
goto v_reusejp_2413_;
}
v_reusejp_2413_:
{
lean_object* v___x_2416_; 
if (v_isShared_2316_ == 0)
{
lean_ctor_set(v___x_2315_, 4, v___x_2414_);
lean_ctor_set(v___x_2315_, 3, v_l_2405_);
lean_ctor_set(v___x_2315_, 2, v_v_2408_);
lean_ctor_set(v___x_2315_, 1, v_k_2407_);
lean_ctor_set(v___x_2315_, 0, v___x_2412_);
v___x_2416_ = v___x_2315_;
goto v_reusejp_2415_;
}
else
{
lean_object* v_reuseFailAlloc_2417_; 
v_reuseFailAlloc_2417_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2417_, 0, v___x_2412_);
lean_ctor_set(v_reuseFailAlloc_2417_, 1, v_k_2407_);
lean_ctor_set(v_reuseFailAlloc_2417_, 2, v_v_2408_);
lean_ctor_set(v_reuseFailAlloc_2417_, 3, v_l_2405_);
lean_ctor_set(v_reuseFailAlloc_2417_, 4, v___x_2414_);
v___x_2416_ = v_reuseFailAlloc_2417_;
goto v_reusejp_2415_;
}
v_reusejp_2415_:
{
return v___x_2416_;
}
}
}
}
else
{
lean_object* v_r_2422_; 
v_r_2422_ = lean_ctor_get(v_impl_2318_, 4);
lean_inc(v_r_2422_);
if (lean_obj_tag(v_r_2422_) == 0)
{
lean_object* v_k_2423_; lean_object* v_v_2424_; lean_object* v___x_2426_; uint8_t v_isShared_2427_; uint8_t v_isSharedCheck_2447_; 
v_k_2423_ = lean_ctor_get(v_impl_2318_, 1);
v_v_2424_ = lean_ctor_get(v_impl_2318_, 2);
v_isSharedCheck_2447_ = !lean_is_exclusive(v_impl_2318_);
if (v_isSharedCheck_2447_ == 0)
{
lean_object* v_unused_2448_; lean_object* v_unused_2449_; lean_object* v_unused_2450_; 
v_unused_2448_ = lean_ctor_get(v_impl_2318_, 4);
lean_dec(v_unused_2448_);
v_unused_2449_ = lean_ctor_get(v_impl_2318_, 3);
lean_dec(v_unused_2449_);
v_unused_2450_ = lean_ctor_get(v_impl_2318_, 0);
lean_dec(v_unused_2450_);
v___x_2426_ = v_impl_2318_;
v_isShared_2427_ = v_isSharedCheck_2447_;
goto v_resetjp_2425_;
}
else
{
lean_inc(v_v_2424_);
lean_inc(v_k_2423_);
lean_dec(v_impl_2318_);
v___x_2426_ = lean_box(0);
v_isShared_2427_ = v_isSharedCheck_2447_;
goto v_resetjp_2425_;
}
v_resetjp_2425_:
{
lean_object* v_k_2428_; lean_object* v_v_2429_; lean_object* v___x_2431_; uint8_t v_isShared_2432_; uint8_t v_isSharedCheck_2443_; 
v_k_2428_ = lean_ctor_get(v_r_2422_, 1);
v_v_2429_ = lean_ctor_get(v_r_2422_, 2);
v_isSharedCheck_2443_ = !lean_is_exclusive(v_r_2422_);
if (v_isSharedCheck_2443_ == 0)
{
lean_object* v_unused_2444_; lean_object* v_unused_2445_; lean_object* v_unused_2446_; 
v_unused_2444_ = lean_ctor_get(v_r_2422_, 4);
lean_dec(v_unused_2444_);
v_unused_2445_ = lean_ctor_get(v_r_2422_, 3);
lean_dec(v_unused_2445_);
v_unused_2446_ = lean_ctor_get(v_r_2422_, 0);
lean_dec(v_unused_2446_);
v___x_2431_ = v_r_2422_;
v_isShared_2432_ = v_isSharedCheck_2443_;
goto v_resetjp_2430_;
}
else
{
lean_inc(v_v_2429_);
lean_inc(v_k_2428_);
lean_dec(v_r_2422_);
v___x_2431_ = lean_box(0);
v_isShared_2432_ = v_isSharedCheck_2443_;
goto v_resetjp_2430_;
}
v_resetjp_2430_:
{
lean_object* v___x_2433_; lean_object* v___x_2435_; 
v___x_2433_ = lean_unsigned_to_nat(3u);
if (v_isShared_2432_ == 0)
{
lean_ctor_set(v___x_2431_, 4, v_l_2405_);
lean_ctor_set(v___x_2431_, 3, v_l_2405_);
lean_ctor_set(v___x_2431_, 2, v_v_2424_);
lean_ctor_set(v___x_2431_, 1, v_k_2423_);
lean_ctor_set(v___x_2431_, 0, v___x_2319_);
v___x_2435_ = v___x_2431_;
goto v_reusejp_2434_;
}
else
{
lean_object* v_reuseFailAlloc_2442_; 
v_reuseFailAlloc_2442_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2442_, 0, v___x_2319_);
lean_ctor_set(v_reuseFailAlloc_2442_, 1, v_k_2423_);
lean_ctor_set(v_reuseFailAlloc_2442_, 2, v_v_2424_);
lean_ctor_set(v_reuseFailAlloc_2442_, 3, v_l_2405_);
lean_ctor_set(v_reuseFailAlloc_2442_, 4, v_l_2405_);
v___x_2435_ = v_reuseFailAlloc_2442_;
goto v_reusejp_2434_;
}
v_reusejp_2434_:
{
lean_object* v___x_2437_; 
if (v_isShared_2427_ == 0)
{
lean_ctor_set(v___x_2426_, 4, v_l_2405_);
lean_ctor_set(v___x_2426_, 2, v_v_2311_);
lean_ctor_set(v___x_2426_, 1, v_k_2310_);
lean_ctor_set(v___x_2426_, 0, v___x_2319_);
v___x_2437_ = v___x_2426_;
goto v_reusejp_2436_;
}
else
{
lean_object* v_reuseFailAlloc_2441_; 
v_reuseFailAlloc_2441_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2441_, 0, v___x_2319_);
lean_ctor_set(v_reuseFailAlloc_2441_, 1, v_k_2310_);
lean_ctor_set(v_reuseFailAlloc_2441_, 2, v_v_2311_);
lean_ctor_set(v_reuseFailAlloc_2441_, 3, v_l_2405_);
lean_ctor_set(v_reuseFailAlloc_2441_, 4, v_l_2405_);
v___x_2437_ = v_reuseFailAlloc_2441_;
goto v_reusejp_2436_;
}
v_reusejp_2436_:
{
lean_object* v___x_2439_; 
if (v_isShared_2316_ == 0)
{
lean_ctor_set(v___x_2315_, 4, v___x_2437_);
lean_ctor_set(v___x_2315_, 3, v___x_2435_);
lean_ctor_set(v___x_2315_, 2, v_v_2429_);
lean_ctor_set(v___x_2315_, 1, v_k_2428_);
lean_ctor_set(v___x_2315_, 0, v___x_2433_);
v___x_2439_ = v___x_2315_;
goto v_reusejp_2438_;
}
else
{
lean_object* v_reuseFailAlloc_2440_; 
v_reuseFailAlloc_2440_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2440_, 0, v___x_2433_);
lean_ctor_set(v_reuseFailAlloc_2440_, 1, v_k_2428_);
lean_ctor_set(v_reuseFailAlloc_2440_, 2, v_v_2429_);
lean_ctor_set(v_reuseFailAlloc_2440_, 3, v___x_2435_);
lean_ctor_set(v_reuseFailAlloc_2440_, 4, v___x_2437_);
v___x_2439_ = v_reuseFailAlloc_2440_;
goto v_reusejp_2438_;
}
v_reusejp_2438_:
{
return v___x_2439_;
}
}
}
}
}
}
else
{
lean_object* v___x_2451_; lean_object* v___x_2453_; 
v___x_2451_ = lean_unsigned_to_nat(2u);
if (v_isShared_2316_ == 0)
{
lean_ctor_set(v___x_2315_, 4, v_r_2422_);
lean_ctor_set(v___x_2315_, 3, v_impl_2318_);
lean_ctor_set(v___x_2315_, 0, v___x_2451_);
v___x_2453_ = v___x_2315_;
goto v_reusejp_2452_;
}
else
{
lean_object* v_reuseFailAlloc_2454_; 
v_reuseFailAlloc_2454_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2454_, 0, v___x_2451_);
lean_ctor_set(v_reuseFailAlloc_2454_, 1, v_k_2310_);
lean_ctor_set(v_reuseFailAlloc_2454_, 2, v_v_2311_);
lean_ctor_set(v_reuseFailAlloc_2454_, 3, v_impl_2318_);
lean_ctor_set(v_reuseFailAlloc_2454_, 4, v_r_2422_);
v___x_2453_ = v_reuseFailAlloc_2454_;
goto v_reusejp_2452_;
}
v_reusejp_2452_:
{
return v___x_2453_;
}
}
}
}
}
case 1:
{
lean_object* v___x_2456_; 
lean_dec(v_v_2311_);
lean_dec(v_k_2310_);
if (v_isShared_2316_ == 0)
{
lean_ctor_set(v___x_2315_, 2, v_v_2307_);
lean_ctor_set(v___x_2315_, 1, v_k_2306_);
v___x_2456_ = v___x_2315_;
goto v_reusejp_2455_;
}
else
{
lean_object* v_reuseFailAlloc_2457_; 
v_reuseFailAlloc_2457_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2457_, 0, v_size_2309_);
lean_ctor_set(v_reuseFailAlloc_2457_, 1, v_k_2306_);
lean_ctor_set(v_reuseFailAlloc_2457_, 2, v_v_2307_);
lean_ctor_set(v_reuseFailAlloc_2457_, 3, v_l_2312_);
lean_ctor_set(v_reuseFailAlloc_2457_, 4, v_r_2313_);
v___x_2456_ = v_reuseFailAlloc_2457_;
goto v_reusejp_2455_;
}
v_reusejp_2455_:
{
return v___x_2456_;
}
}
default: 
{
lean_object* v_impl_2458_; lean_object* v___x_2459_; 
lean_dec(v_size_2309_);
v_impl_2458_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Level_collectMVars_spec__1___redArg(v_k_2306_, v_v_2307_, v_r_2313_);
v___x_2459_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_2312_) == 0)
{
lean_object* v_size_2460_; lean_object* v_size_2461_; lean_object* v_k_2462_; lean_object* v_v_2463_; lean_object* v_l_2464_; lean_object* v_r_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; uint8_t v___x_2468_; 
v_size_2460_ = lean_ctor_get(v_l_2312_, 0);
v_size_2461_ = lean_ctor_get(v_impl_2458_, 0);
lean_inc(v_size_2461_);
v_k_2462_ = lean_ctor_get(v_impl_2458_, 1);
lean_inc(v_k_2462_);
v_v_2463_ = lean_ctor_get(v_impl_2458_, 2);
lean_inc(v_v_2463_);
v_l_2464_ = lean_ctor_get(v_impl_2458_, 3);
lean_inc(v_l_2464_);
v_r_2465_ = lean_ctor_get(v_impl_2458_, 4);
lean_inc(v_r_2465_);
v___x_2466_ = lean_unsigned_to_nat(3u);
v___x_2467_ = lean_nat_mul(v___x_2466_, v_size_2460_);
v___x_2468_ = lean_nat_dec_lt(v___x_2467_, v_size_2461_);
lean_dec(v___x_2467_);
if (v___x_2468_ == 0)
{
lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2472_; 
lean_dec(v_r_2465_);
lean_dec(v_l_2464_);
lean_dec(v_v_2463_);
lean_dec(v_k_2462_);
v___x_2469_ = lean_nat_add(v___x_2459_, v_size_2460_);
v___x_2470_ = lean_nat_add(v___x_2469_, v_size_2461_);
lean_dec(v_size_2461_);
lean_dec(v___x_2469_);
if (v_isShared_2316_ == 0)
{
lean_ctor_set(v___x_2315_, 4, v_impl_2458_);
lean_ctor_set(v___x_2315_, 0, v___x_2470_);
v___x_2472_ = v___x_2315_;
goto v_reusejp_2471_;
}
else
{
lean_object* v_reuseFailAlloc_2473_; 
v_reuseFailAlloc_2473_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2473_, 0, v___x_2470_);
lean_ctor_set(v_reuseFailAlloc_2473_, 1, v_k_2310_);
lean_ctor_set(v_reuseFailAlloc_2473_, 2, v_v_2311_);
lean_ctor_set(v_reuseFailAlloc_2473_, 3, v_l_2312_);
lean_ctor_set(v_reuseFailAlloc_2473_, 4, v_impl_2458_);
v___x_2472_ = v_reuseFailAlloc_2473_;
goto v_reusejp_2471_;
}
v_reusejp_2471_:
{
return v___x_2472_;
}
}
else
{
lean_object* v___x_2475_; uint8_t v_isShared_2476_; uint8_t v_isSharedCheck_2537_; 
v_isSharedCheck_2537_ = !lean_is_exclusive(v_impl_2458_);
if (v_isSharedCheck_2537_ == 0)
{
lean_object* v_unused_2538_; lean_object* v_unused_2539_; lean_object* v_unused_2540_; lean_object* v_unused_2541_; lean_object* v_unused_2542_; 
v_unused_2538_ = lean_ctor_get(v_impl_2458_, 4);
lean_dec(v_unused_2538_);
v_unused_2539_ = lean_ctor_get(v_impl_2458_, 3);
lean_dec(v_unused_2539_);
v_unused_2540_ = lean_ctor_get(v_impl_2458_, 2);
lean_dec(v_unused_2540_);
v_unused_2541_ = lean_ctor_get(v_impl_2458_, 1);
lean_dec(v_unused_2541_);
v_unused_2542_ = lean_ctor_get(v_impl_2458_, 0);
lean_dec(v_unused_2542_);
v___x_2475_ = v_impl_2458_;
v_isShared_2476_ = v_isSharedCheck_2537_;
goto v_resetjp_2474_;
}
else
{
lean_dec(v_impl_2458_);
v___x_2475_ = lean_box(0);
v_isShared_2476_ = v_isSharedCheck_2537_;
goto v_resetjp_2474_;
}
v_resetjp_2474_:
{
lean_object* v_size_2477_; lean_object* v_k_2478_; lean_object* v_v_2479_; lean_object* v_l_2480_; lean_object* v_r_2481_; lean_object* v_size_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; uint8_t v___x_2485_; 
v_size_2477_ = lean_ctor_get(v_l_2464_, 0);
v_k_2478_ = lean_ctor_get(v_l_2464_, 1);
v_v_2479_ = lean_ctor_get(v_l_2464_, 2);
v_l_2480_ = lean_ctor_get(v_l_2464_, 3);
v_r_2481_ = lean_ctor_get(v_l_2464_, 4);
v_size_2482_ = lean_ctor_get(v_r_2465_, 0);
v___x_2483_ = lean_unsigned_to_nat(2u);
v___x_2484_ = lean_nat_mul(v___x_2483_, v_size_2482_);
v___x_2485_ = lean_nat_dec_lt(v_size_2477_, v___x_2484_);
lean_dec(v___x_2484_);
if (v___x_2485_ == 0)
{
lean_object* v___x_2487_; uint8_t v_isShared_2488_; uint8_t v_isSharedCheck_2513_; 
lean_inc(v_r_2481_);
lean_inc(v_l_2480_);
lean_inc(v_v_2479_);
lean_inc(v_k_2478_);
v_isSharedCheck_2513_ = !lean_is_exclusive(v_l_2464_);
if (v_isSharedCheck_2513_ == 0)
{
lean_object* v_unused_2514_; lean_object* v_unused_2515_; lean_object* v_unused_2516_; lean_object* v_unused_2517_; lean_object* v_unused_2518_; 
v_unused_2514_ = lean_ctor_get(v_l_2464_, 4);
lean_dec(v_unused_2514_);
v_unused_2515_ = lean_ctor_get(v_l_2464_, 3);
lean_dec(v_unused_2515_);
v_unused_2516_ = lean_ctor_get(v_l_2464_, 2);
lean_dec(v_unused_2516_);
v_unused_2517_ = lean_ctor_get(v_l_2464_, 1);
lean_dec(v_unused_2517_);
v_unused_2518_ = lean_ctor_get(v_l_2464_, 0);
lean_dec(v_unused_2518_);
v___x_2487_ = v_l_2464_;
v_isShared_2488_ = v_isSharedCheck_2513_;
goto v_resetjp_2486_;
}
else
{
lean_dec(v_l_2464_);
v___x_2487_ = lean_box(0);
v_isShared_2488_ = v_isSharedCheck_2513_;
goto v_resetjp_2486_;
}
v_resetjp_2486_:
{
lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___y_2492_; lean_object* v___y_2493_; lean_object* v___y_2494_; lean_object* v___y_2503_; 
v___x_2489_ = lean_nat_add(v___x_2459_, v_size_2460_);
v___x_2490_ = lean_nat_add(v___x_2489_, v_size_2461_);
lean_dec(v_size_2461_);
if (lean_obj_tag(v_l_2480_) == 0)
{
lean_object* v_size_2511_; 
v_size_2511_ = lean_ctor_get(v_l_2480_, 0);
lean_inc(v_size_2511_);
v___y_2503_ = v_size_2511_;
goto v___jp_2502_;
}
else
{
lean_object* v___x_2512_; 
v___x_2512_ = lean_unsigned_to_nat(0u);
v___y_2503_ = v___x_2512_;
goto v___jp_2502_;
}
v___jp_2491_:
{
lean_object* v___x_2495_; lean_object* v___x_2497_; 
v___x_2495_ = lean_nat_add(v___y_2492_, v___y_2494_);
lean_dec(v___y_2494_);
lean_dec(v___y_2492_);
if (v_isShared_2488_ == 0)
{
lean_ctor_set(v___x_2487_, 4, v_r_2465_);
lean_ctor_set(v___x_2487_, 3, v_r_2481_);
lean_ctor_set(v___x_2487_, 2, v_v_2463_);
lean_ctor_set(v___x_2487_, 1, v_k_2462_);
lean_ctor_set(v___x_2487_, 0, v___x_2495_);
v___x_2497_ = v___x_2487_;
goto v_reusejp_2496_;
}
else
{
lean_object* v_reuseFailAlloc_2501_; 
v_reuseFailAlloc_2501_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2501_, 0, v___x_2495_);
lean_ctor_set(v_reuseFailAlloc_2501_, 1, v_k_2462_);
lean_ctor_set(v_reuseFailAlloc_2501_, 2, v_v_2463_);
lean_ctor_set(v_reuseFailAlloc_2501_, 3, v_r_2481_);
lean_ctor_set(v_reuseFailAlloc_2501_, 4, v_r_2465_);
v___x_2497_ = v_reuseFailAlloc_2501_;
goto v_reusejp_2496_;
}
v_reusejp_2496_:
{
lean_object* v___x_2499_; 
if (v_isShared_2476_ == 0)
{
lean_ctor_set(v___x_2475_, 4, v___x_2497_);
lean_ctor_set(v___x_2475_, 3, v___y_2493_);
lean_ctor_set(v___x_2475_, 2, v_v_2479_);
lean_ctor_set(v___x_2475_, 1, v_k_2478_);
lean_ctor_set(v___x_2475_, 0, v___x_2490_);
v___x_2499_ = v___x_2475_;
goto v_reusejp_2498_;
}
else
{
lean_object* v_reuseFailAlloc_2500_; 
v_reuseFailAlloc_2500_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2500_, 0, v___x_2490_);
lean_ctor_set(v_reuseFailAlloc_2500_, 1, v_k_2478_);
lean_ctor_set(v_reuseFailAlloc_2500_, 2, v_v_2479_);
lean_ctor_set(v_reuseFailAlloc_2500_, 3, v___y_2493_);
lean_ctor_set(v_reuseFailAlloc_2500_, 4, v___x_2497_);
v___x_2499_ = v_reuseFailAlloc_2500_;
goto v_reusejp_2498_;
}
v_reusejp_2498_:
{
return v___x_2499_;
}
}
}
v___jp_2502_:
{
lean_object* v___x_2504_; lean_object* v___x_2506_; 
v___x_2504_ = lean_nat_add(v___x_2489_, v___y_2503_);
lean_dec(v___y_2503_);
lean_dec(v___x_2489_);
if (v_isShared_2316_ == 0)
{
lean_ctor_set(v___x_2315_, 4, v_l_2480_);
lean_ctor_set(v___x_2315_, 0, v___x_2504_);
v___x_2506_ = v___x_2315_;
goto v_reusejp_2505_;
}
else
{
lean_object* v_reuseFailAlloc_2510_; 
v_reuseFailAlloc_2510_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2510_, 0, v___x_2504_);
lean_ctor_set(v_reuseFailAlloc_2510_, 1, v_k_2310_);
lean_ctor_set(v_reuseFailAlloc_2510_, 2, v_v_2311_);
lean_ctor_set(v_reuseFailAlloc_2510_, 3, v_l_2312_);
lean_ctor_set(v_reuseFailAlloc_2510_, 4, v_l_2480_);
v___x_2506_ = v_reuseFailAlloc_2510_;
goto v_reusejp_2505_;
}
v_reusejp_2505_:
{
lean_object* v___x_2507_; 
v___x_2507_ = lean_nat_add(v___x_2459_, v_size_2482_);
if (lean_obj_tag(v_r_2481_) == 0)
{
lean_object* v_size_2508_; 
v_size_2508_ = lean_ctor_get(v_r_2481_, 0);
lean_inc(v_size_2508_);
v___y_2492_ = v___x_2507_;
v___y_2493_ = v___x_2506_;
v___y_2494_ = v_size_2508_;
goto v___jp_2491_;
}
else
{
lean_object* v___x_2509_; 
v___x_2509_ = lean_unsigned_to_nat(0u);
v___y_2492_ = v___x_2507_;
v___y_2493_ = v___x_2506_;
v___y_2494_ = v___x_2509_;
goto v___jp_2491_;
}
}
}
}
}
else
{
lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2523_; 
lean_del_object(v___x_2315_);
v___x_2519_ = lean_nat_add(v___x_2459_, v_size_2460_);
v___x_2520_ = lean_nat_add(v___x_2519_, v_size_2461_);
lean_dec(v_size_2461_);
v___x_2521_ = lean_nat_add(v___x_2519_, v_size_2477_);
lean_dec(v___x_2519_);
lean_inc_ref(v_l_2312_);
if (v_isShared_2476_ == 0)
{
lean_ctor_set(v___x_2475_, 4, v_l_2464_);
lean_ctor_set(v___x_2475_, 3, v_l_2312_);
lean_ctor_set(v___x_2475_, 2, v_v_2311_);
lean_ctor_set(v___x_2475_, 1, v_k_2310_);
lean_ctor_set(v___x_2475_, 0, v___x_2521_);
v___x_2523_ = v___x_2475_;
goto v_reusejp_2522_;
}
else
{
lean_object* v_reuseFailAlloc_2536_; 
v_reuseFailAlloc_2536_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2536_, 0, v___x_2521_);
lean_ctor_set(v_reuseFailAlloc_2536_, 1, v_k_2310_);
lean_ctor_set(v_reuseFailAlloc_2536_, 2, v_v_2311_);
lean_ctor_set(v_reuseFailAlloc_2536_, 3, v_l_2312_);
lean_ctor_set(v_reuseFailAlloc_2536_, 4, v_l_2464_);
v___x_2523_ = v_reuseFailAlloc_2536_;
goto v_reusejp_2522_;
}
v_reusejp_2522_:
{
lean_object* v___x_2525_; uint8_t v_isShared_2526_; uint8_t v_isSharedCheck_2530_; 
v_isSharedCheck_2530_ = !lean_is_exclusive(v_l_2312_);
if (v_isSharedCheck_2530_ == 0)
{
lean_object* v_unused_2531_; lean_object* v_unused_2532_; lean_object* v_unused_2533_; lean_object* v_unused_2534_; lean_object* v_unused_2535_; 
v_unused_2531_ = lean_ctor_get(v_l_2312_, 4);
lean_dec(v_unused_2531_);
v_unused_2532_ = lean_ctor_get(v_l_2312_, 3);
lean_dec(v_unused_2532_);
v_unused_2533_ = lean_ctor_get(v_l_2312_, 2);
lean_dec(v_unused_2533_);
v_unused_2534_ = lean_ctor_get(v_l_2312_, 1);
lean_dec(v_unused_2534_);
v_unused_2535_ = lean_ctor_get(v_l_2312_, 0);
lean_dec(v_unused_2535_);
v___x_2525_ = v_l_2312_;
v_isShared_2526_ = v_isSharedCheck_2530_;
goto v_resetjp_2524_;
}
else
{
lean_dec(v_l_2312_);
v___x_2525_ = lean_box(0);
v_isShared_2526_ = v_isSharedCheck_2530_;
goto v_resetjp_2524_;
}
v_resetjp_2524_:
{
lean_object* v___x_2528_; 
if (v_isShared_2526_ == 0)
{
lean_ctor_set(v___x_2525_, 4, v_r_2465_);
lean_ctor_set(v___x_2525_, 3, v___x_2523_);
lean_ctor_set(v___x_2525_, 2, v_v_2463_);
lean_ctor_set(v___x_2525_, 1, v_k_2462_);
lean_ctor_set(v___x_2525_, 0, v___x_2520_);
v___x_2528_ = v___x_2525_;
goto v_reusejp_2527_;
}
else
{
lean_object* v_reuseFailAlloc_2529_; 
v_reuseFailAlloc_2529_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2529_, 0, v___x_2520_);
lean_ctor_set(v_reuseFailAlloc_2529_, 1, v_k_2462_);
lean_ctor_set(v_reuseFailAlloc_2529_, 2, v_v_2463_);
lean_ctor_set(v_reuseFailAlloc_2529_, 3, v___x_2523_);
lean_ctor_set(v_reuseFailAlloc_2529_, 4, v_r_2465_);
v___x_2528_ = v_reuseFailAlloc_2529_;
goto v_reusejp_2527_;
}
v_reusejp_2527_:
{
return v___x_2528_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_2543_; 
v_l_2543_ = lean_ctor_get(v_impl_2458_, 3);
lean_inc(v_l_2543_);
if (lean_obj_tag(v_l_2543_) == 0)
{
lean_object* v_r_2544_; lean_object* v_k_2545_; lean_object* v_v_2546_; lean_object* v___x_2548_; uint8_t v_isShared_2549_; uint8_t v_isSharedCheck_2569_; 
v_r_2544_ = lean_ctor_get(v_impl_2458_, 4);
v_k_2545_ = lean_ctor_get(v_impl_2458_, 1);
v_v_2546_ = lean_ctor_get(v_impl_2458_, 2);
v_isSharedCheck_2569_ = !lean_is_exclusive(v_impl_2458_);
if (v_isSharedCheck_2569_ == 0)
{
lean_object* v_unused_2570_; lean_object* v_unused_2571_; 
v_unused_2570_ = lean_ctor_get(v_impl_2458_, 3);
lean_dec(v_unused_2570_);
v_unused_2571_ = lean_ctor_get(v_impl_2458_, 0);
lean_dec(v_unused_2571_);
v___x_2548_ = v_impl_2458_;
v_isShared_2549_ = v_isSharedCheck_2569_;
goto v_resetjp_2547_;
}
else
{
lean_inc(v_r_2544_);
lean_inc(v_v_2546_);
lean_inc(v_k_2545_);
lean_dec(v_impl_2458_);
v___x_2548_ = lean_box(0);
v_isShared_2549_ = v_isSharedCheck_2569_;
goto v_resetjp_2547_;
}
v_resetjp_2547_:
{
lean_object* v_k_2550_; lean_object* v_v_2551_; lean_object* v___x_2553_; uint8_t v_isShared_2554_; uint8_t v_isSharedCheck_2565_; 
v_k_2550_ = lean_ctor_get(v_l_2543_, 1);
v_v_2551_ = lean_ctor_get(v_l_2543_, 2);
v_isSharedCheck_2565_ = !lean_is_exclusive(v_l_2543_);
if (v_isSharedCheck_2565_ == 0)
{
lean_object* v_unused_2566_; lean_object* v_unused_2567_; lean_object* v_unused_2568_; 
v_unused_2566_ = lean_ctor_get(v_l_2543_, 4);
lean_dec(v_unused_2566_);
v_unused_2567_ = lean_ctor_get(v_l_2543_, 3);
lean_dec(v_unused_2567_);
v_unused_2568_ = lean_ctor_get(v_l_2543_, 0);
lean_dec(v_unused_2568_);
v___x_2553_ = v_l_2543_;
v_isShared_2554_ = v_isSharedCheck_2565_;
goto v_resetjp_2552_;
}
else
{
lean_inc(v_v_2551_);
lean_inc(v_k_2550_);
lean_dec(v_l_2543_);
v___x_2553_ = lean_box(0);
v_isShared_2554_ = v_isSharedCheck_2565_;
goto v_resetjp_2552_;
}
v_resetjp_2552_:
{
lean_object* v___x_2555_; lean_object* v___x_2557_; 
v___x_2555_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_2544_, 2);
if (v_isShared_2554_ == 0)
{
lean_ctor_set(v___x_2553_, 4, v_r_2544_);
lean_ctor_set(v___x_2553_, 3, v_r_2544_);
lean_ctor_set(v___x_2553_, 2, v_v_2311_);
lean_ctor_set(v___x_2553_, 1, v_k_2310_);
lean_ctor_set(v___x_2553_, 0, v___x_2459_);
v___x_2557_ = v___x_2553_;
goto v_reusejp_2556_;
}
else
{
lean_object* v_reuseFailAlloc_2564_; 
v_reuseFailAlloc_2564_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2564_, 0, v___x_2459_);
lean_ctor_set(v_reuseFailAlloc_2564_, 1, v_k_2310_);
lean_ctor_set(v_reuseFailAlloc_2564_, 2, v_v_2311_);
lean_ctor_set(v_reuseFailAlloc_2564_, 3, v_r_2544_);
lean_ctor_set(v_reuseFailAlloc_2564_, 4, v_r_2544_);
v___x_2557_ = v_reuseFailAlloc_2564_;
goto v_reusejp_2556_;
}
v_reusejp_2556_:
{
lean_object* v___x_2559_; 
lean_inc(v_r_2544_);
if (v_isShared_2549_ == 0)
{
lean_ctor_set(v___x_2548_, 3, v_r_2544_);
lean_ctor_set(v___x_2548_, 0, v___x_2459_);
v___x_2559_ = v___x_2548_;
goto v_reusejp_2558_;
}
else
{
lean_object* v_reuseFailAlloc_2563_; 
v_reuseFailAlloc_2563_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2563_, 0, v___x_2459_);
lean_ctor_set(v_reuseFailAlloc_2563_, 1, v_k_2545_);
lean_ctor_set(v_reuseFailAlloc_2563_, 2, v_v_2546_);
lean_ctor_set(v_reuseFailAlloc_2563_, 3, v_r_2544_);
lean_ctor_set(v_reuseFailAlloc_2563_, 4, v_r_2544_);
v___x_2559_ = v_reuseFailAlloc_2563_;
goto v_reusejp_2558_;
}
v_reusejp_2558_:
{
lean_object* v___x_2561_; 
if (v_isShared_2316_ == 0)
{
lean_ctor_set(v___x_2315_, 4, v___x_2559_);
lean_ctor_set(v___x_2315_, 3, v___x_2557_);
lean_ctor_set(v___x_2315_, 2, v_v_2551_);
lean_ctor_set(v___x_2315_, 1, v_k_2550_);
lean_ctor_set(v___x_2315_, 0, v___x_2555_);
v___x_2561_ = v___x_2315_;
goto v_reusejp_2560_;
}
else
{
lean_object* v_reuseFailAlloc_2562_; 
v_reuseFailAlloc_2562_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2562_, 0, v___x_2555_);
lean_ctor_set(v_reuseFailAlloc_2562_, 1, v_k_2550_);
lean_ctor_set(v_reuseFailAlloc_2562_, 2, v_v_2551_);
lean_ctor_set(v_reuseFailAlloc_2562_, 3, v___x_2557_);
lean_ctor_set(v_reuseFailAlloc_2562_, 4, v___x_2559_);
v___x_2561_ = v_reuseFailAlloc_2562_;
goto v_reusejp_2560_;
}
v_reusejp_2560_:
{
return v___x_2561_;
}
}
}
}
}
}
else
{
lean_object* v_r_2572_; 
v_r_2572_ = lean_ctor_get(v_impl_2458_, 4);
lean_inc(v_r_2572_);
if (lean_obj_tag(v_r_2572_) == 0)
{
lean_object* v_k_2573_; lean_object* v_v_2574_; lean_object* v___x_2576_; uint8_t v_isShared_2577_; uint8_t v_isSharedCheck_2585_; 
v_k_2573_ = lean_ctor_get(v_impl_2458_, 1);
v_v_2574_ = lean_ctor_get(v_impl_2458_, 2);
v_isSharedCheck_2585_ = !lean_is_exclusive(v_impl_2458_);
if (v_isSharedCheck_2585_ == 0)
{
lean_object* v_unused_2586_; lean_object* v_unused_2587_; lean_object* v_unused_2588_; 
v_unused_2586_ = lean_ctor_get(v_impl_2458_, 4);
lean_dec(v_unused_2586_);
v_unused_2587_ = lean_ctor_get(v_impl_2458_, 3);
lean_dec(v_unused_2587_);
v_unused_2588_ = lean_ctor_get(v_impl_2458_, 0);
lean_dec(v_unused_2588_);
v___x_2576_ = v_impl_2458_;
v_isShared_2577_ = v_isSharedCheck_2585_;
goto v_resetjp_2575_;
}
else
{
lean_inc(v_v_2574_);
lean_inc(v_k_2573_);
lean_dec(v_impl_2458_);
v___x_2576_ = lean_box(0);
v_isShared_2577_ = v_isSharedCheck_2585_;
goto v_resetjp_2575_;
}
v_resetjp_2575_:
{
lean_object* v___x_2578_; lean_object* v___x_2580_; 
v___x_2578_ = lean_unsigned_to_nat(3u);
if (v_isShared_2577_ == 0)
{
lean_ctor_set(v___x_2576_, 4, v_l_2543_);
lean_ctor_set(v___x_2576_, 2, v_v_2311_);
lean_ctor_set(v___x_2576_, 1, v_k_2310_);
lean_ctor_set(v___x_2576_, 0, v___x_2459_);
v___x_2580_ = v___x_2576_;
goto v_reusejp_2579_;
}
else
{
lean_object* v_reuseFailAlloc_2584_; 
v_reuseFailAlloc_2584_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2584_, 0, v___x_2459_);
lean_ctor_set(v_reuseFailAlloc_2584_, 1, v_k_2310_);
lean_ctor_set(v_reuseFailAlloc_2584_, 2, v_v_2311_);
lean_ctor_set(v_reuseFailAlloc_2584_, 3, v_l_2543_);
lean_ctor_set(v_reuseFailAlloc_2584_, 4, v_l_2543_);
v___x_2580_ = v_reuseFailAlloc_2584_;
goto v_reusejp_2579_;
}
v_reusejp_2579_:
{
lean_object* v___x_2582_; 
if (v_isShared_2316_ == 0)
{
lean_ctor_set(v___x_2315_, 4, v_r_2572_);
lean_ctor_set(v___x_2315_, 3, v___x_2580_);
lean_ctor_set(v___x_2315_, 2, v_v_2574_);
lean_ctor_set(v___x_2315_, 1, v_k_2573_);
lean_ctor_set(v___x_2315_, 0, v___x_2578_);
v___x_2582_ = v___x_2315_;
goto v_reusejp_2581_;
}
else
{
lean_object* v_reuseFailAlloc_2583_; 
v_reuseFailAlloc_2583_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2583_, 0, v___x_2578_);
lean_ctor_set(v_reuseFailAlloc_2583_, 1, v_k_2573_);
lean_ctor_set(v_reuseFailAlloc_2583_, 2, v_v_2574_);
lean_ctor_set(v_reuseFailAlloc_2583_, 3, v___x_2580_);
lean_ctor_set(v_reuseFailAlloc_2583_, 4, v_r_2572_);
v___x_2582_ = v_reuseFailAlloc_2583_;
goto v_reusejp_2581_;
}
v_reusejp_2581_:
{
return v___x_2582_;
}
}
}
}
else
{
lean_object* v___x_2589_; lean_object* v___x_2591_; 
v___x_2589_ = lean_unsigned_to_nat(2u);
if (v_isShared_2316_ == 0)
{
lean_ctor_set(v___x_2315_, 4, v_impl_2458_);
lean_ctor_set(v___x_2315_, 3, v_r_2572_);
lean_ctor_set(v___x_2315_, 0, v___x_2589_);
v___x_2591_ = v___x_2315_;
goto v_reusejp_2590_;
}
else
{
lean_object* v_reuseFailAlloc_2592_; 
v_reuseFailAlloc_2592_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2592_, 0, v___x_2589_);
lean_ctor_set(v_reuseFailAlloc_2592_, 1, v_k_2310_);
lean_ctor_set(v_reuseFailAlloc_2592_, 2, v_v_2311_);
lean_ctor_set(v_reuseFailAlloc_2592_, 3, v_r_2572_);
lean_ctor_set(v_reuseFailAlloc_2592_, 4, v_impl_2458_);
v___x_2591_ = v_reuseFailAlloc_2592_;
goto v_reusejp_2590_;
}
v_reusejp_2590_:
{
return v___x_2591_;
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
lean_object* v___x_2594_; lean_object* v___x_2595_; 
v___x_2594_ = lean_unsigned_to_nat(1u);
v___x_2595_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2595_, 0, v___x_2594_);
lean_ctor_set(v___x_2595_, 1, v_k_2306_);
lean_ctor_set(v___x_2595_, 2, v_v_2307_);
lean_ctor_set(v___x_2595_, 3, v_t_2308_);
lean_ctor_set(v___x_2595_, 4, v_t_2308_);
return v___x_2595_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Level_collectMVars_spec__0___redArg(lean_object* v_k_2596_, lean_object* v_t_2597_){
_start:
{
if (lean_obj_tag(v_t_2597_) == 0)
{
lean_object* v_k_2598_; lean_object* v_l_2599_; lean_object* v_r_2600_; uint8_t v___x_2601_; 
v_k_2598_ = lean_ctor_get(v_t_2597_, 1);
v_l_2599_ = lean_ctor_get(v_t_2597_, 3);
v_r_2600_ = lean_ctor_get(v_t_2597_, 4);
v___x_2601_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2596_, v_k_2598_);
switch(v___x_2601_)
{
case 0:
{
v_t_2597_ = v_l_2599_;
goto _start;
}
case 1:
{
uint8_t v___x_2603_; 
v___x_2603_ = 1;
return v___x_2603_;
}
default: 
{
v_t_2597_ = v_r_2600_;
goto _start;
}
}
}
else
{
uint8_t v___x_2605_; 
v___x_2605_ = 0;
return v___x_2605_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Level_collectMVars_spec__0___redArg___boxed(lean_object* v_k_2606_, lean_object* v_t_2607_){
_start:
{
uint8_t v_res_2608_; lean_object* v_r_2609_; 
v_res_2608_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Level_collectMVars_spec__0___redArg(v_k_2606_, v_t_2607_);
lean_dec(v_t_2607_);
lean_dec(v_k_2606_);
v_r_2609_ = lean_box(v_res_2608_);
return v_r_2609_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_collectMVars(lean_object* v_u_2610_, lean_object* v_s_2611_){
_start:
{
lean_object* v_u_2613_; lean_object* v_v_2614_; 
switch(lean_obj_tag(v_u_2610_))
{
case 1:
{
lean_object* v_a_2617_; 
v_a_2617_ = lean_ctor_get(v_u_2610_, 0);
lean_inc(v_a_2617_);
lean_dec_ref_known(v_u_2610_, 1);
v_u_2610_ = v_a_2617_;
goto _start;
}
case 2:
{
lean_object* v_a_2619_; lean_object* v_a_2620_; 
v_a_2619_ = lean_ctor_get(v_u_2610_, 0);
lean_inc(v_a_2619_);
v_a_2620_ = lean_ctor_get(v_u_2610_, 1);
lean_inc(v_a_2620_);
lean_dec_ref_known(v_u_2610_, 2);
v_u_2613_ = v_a_2619_;
v_v_2614_ = v_a_2620_;
goto v___jp_2612_;
}
case 3:
{
lean_object* v_a_2621_; lean_object* v_a_2622_; 
v_a_2621_ = lean_ctor_get(v_u_2610_, 0);
lean_inc(v_a_2621_);
v_a_2622_ = lean_ctor_get(v_u_2610_, 1);
lean_inc(v_a_2622_);
lean_dec_ref_known(v_u_2610_, 2);
v_u_2613_ = v_a_2621_;
v_v_2614_ = v_a_2622_;
goto v___jp_2612_;
}
case 5:
{
lean_object* v_a_2623_; uint8_t v___x_2624_; 
v_a_2623_ = lean_ctor_get(v_u_2610_, 0);
lean_inc(v_a_2623_);
lean_dec_ref_known(v_u_2610_, 1);
v___x_2624_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Level_collectMVars_spec__0___redArg(v_a_2623_, v_s_2611_);
if (v___x_2624_ == 0)
{
lean_object* v___x_2625_; lean_object* v___x_2626_; 
v___x_2625_ = lean_box(0);
v___x_2626_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Level_collectMVars_spec__1___redArg(v_a_2623_, v___x_2625_, v_s_2611_);
return v___x_2626_;
}
else
{
lean_dec(v_a_2623_);
return v_s_2611_;
}
}
default: 
{
lean_dec(v_u_2610_);
return v_s_2611_;
}
}
v___jp_2612_:
{
lean_object* v___x_2615_; 
v___x_2615_ = l_Lean_Level_collectMVars(v_v_2614_, v_s_2611_);
v_u_2610_ = v_u_2613_;
v_s_2611_ = v___x_2615_;
goto _start;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Level_collectMVars_spec__0(lean_object* v_00_u03b2_2627_, lean_object* v_k_2628_, lean_object* v_t_2629_){
_start:
{
uint8_t v___x_2630_; 
v___x_2630_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Level_collectMVars_spec__0___redArg(v_k_2628_, v_t_2629_);
return v___x_2630_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Level_collectMVars_spec__0___boxed(lean_object* v_00_u03b2_2631_, lean_object* v_k_2632_, lean_object* v_t_2633_){
_start:
{
uint8_t v_res_2634_; lean_object* v_r_2635_; 
v_res_2634_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Level_collectMVars_spec__0(v_00_u03b2_2631_, v_k_2632_, v_t_2633_);
lean_dec(v_t_2633_);
lean_dec(v_k_2632_);
v_r_2635_ = lean_box(v_res_2634_);
return v_r_2635_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Level_collectMVars_spec__1(lean_object* v_00_u03b2_2636_, lean_object* v_k_2637_, lean_object* v_v_2638_, lean_object* v_t_2639_, lean_object* v_hl_2640_){
_start:
{
lean_object* v___x_2641_; 
v___x_2641_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Level_collectMVars_spec__1___redArg(v_k_2637_, v_v_2638_, v_t_2639_);
return v___x_2641_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_find_x3f_visit(lean_object* v_p_2642_, lean_object* v_u_2643_){
_start:
{
lean_object* v_u_2645_; lean_object* v_v_2646_; lean_object* v___x_2649_; uint8_t v___x_2650_; 
lean_inc_ref(v_p_2642_);
lean_inc(v_u_2643_);
v___x_2649_ = lean_apply_1(v_p_2642_, v_u_2643_);
v___x_2650_ = lean_unbox(v___x_2649_);
if (v___x_2650_ == 0)
{
switch(lean_obj_tag(v_u_2643_))
{
case 1:
{
lean_object* v_a_2651_; 
v_a_2651_ = lean_ctor_get(v_u_2643_, 0);
lean_inc(v_a_2651_);
lean_dec_ref_known(v_u_2643_, 1);
v_u_2643_ = v_a_2651_;
goto _start;
}
case 2:
{
lean_object* v_a_2653_; lean_object* v_a_2654_; 
v_a_2653_ = lean_ctor_get(v_u_2643_, 0);
lean_inc(v_a_2653_);
v_a_2654_ = lean_ctor_get(v_u_2643_, 1);
lean_inc(v_a_2654_);
lean_dec_ref_known(v_u_2643_, 2);
v_u_2645_ = v_a_2653_;
v_v_2646_ = v_a_2654_;
goto v___jp_2644_;
}
case 3:
{
lean_object* v_a_2655_; lean_object* v_a_2656_; 
v_a_2655_ = lean_ctor_get(v_u_2643_, 0);
lean_inc(v_a_2655_);
v_a_2656_ = lean_ctor_get(v_u_2643_, 1);
lean_inc(v_a_2656_);
lean_dec_ref_known(v_u_2643_, 2);
v_u_2645_ = v_a_2655_;
v_v_2646_ = v_a_2656_;
goto v___jp_2644_;
}
default: 
{
lean_object* v___x_2657_; 
lean_dec(v_u_2643_);
lean_dec_ref(v_p_2642_);
v___x_2657_ = lean_box(0);
return v___x_2657_;
}
}
}
else
{
lean_object* v___x_2658_; 
lean_dec_ref(v_p_2642_);
v___x_2658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2658_, 0, v_u_2643_);
return v___x_2658_;
}
v___jp_2644_:
{
lean_object* v___x_2647_; 
lean_inc_ref(v_p_2642_);
v___x_2647_ = l___private_Lean_Level_0__Lean_Level_find_x3f_visit(v_p_2642_, v_u_2645_);
if (lean_obj_tag(v___x_2647_) == 0)
{
v_u_2643_ = v_v_2646_;
goto _start;
}
else
{
lean_dec(v_v_2646_);
lean_dec_ref(v_p_2642_);
return v___x_2647_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_find_x3f(lean_object* v_u_2659_, lean_object* v_p_2660_){
_start:
{
lean_object* v___x_2661_; 
v___x_2661_ = l___private_Lean_Level_0__Lean_Level_find_x3f_visit(v_p_2660_, v_u_2659_);
return v___x_2661_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_any(lean_object* v_u_2662_, lean_object* v_p_2663_){
_start:
{
lean_object* v___x_2664_; 
v___x_2664_ = l___private_Lean_Level_0__Lean_Level_find_x3f_visit(v_p_2663_, v_u_2662_);
if (lean_obj_tag(v___x_2664_) == 0)
{
uint8_t v___x_2665_; 
v___x_2665_ = 0;
return v___x_2665_;
}
else
{
uint8_t v___x_2666_; 
lean_dec_ref_known(v___x_2664_, 1);
v___x_2666_ = 1;
return v___x_2666_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_any___boxed(lean_object* v_u_2667_, lean_object* v_p_2668_){
_start:
{
uint8_t v_res_2669_; lean_object* v_r_2670_; 
v_res_2669_ = l_Lean_Level_any(v_u_2667_, v_p_2668_);
v_r_2670_ = lean_box(v_res_2669_);
return v_r_2670_;
}
}
LEAN_EXPORT lean_object* l_Lean_Nat_toLevel(lean_object* v_n_2671_){
_start:
{
lean_object* v___x_2672_; 
v___x_2672_ = l_Lean_Level_ofNat(v_n_2671_);
return v___x_2672_;
}
}
LEAN_EXPORT lean_object* l_Lean_Nat_toLevel___boxed(lean_object* v_n_2673_){
_start:
{
lean_object* v_res_2674_; 
v_res_2674_ = l_Lean_Nat_toLevel(v_n_2673_);
lean_dec(v_n_2673_);
return v_res_2674_;
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
