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
LEAN_EXPORT lean_object* lean_level_mk_mvar(lean_object* v_mvarId_750_){
_start:
{
lean_object* v___x_751_; 
v___x_751_ = l_Lean_Level_mvar___override(v_mvarId_750_);
return v___x_751_;
}
}
LEAN_EXPORT lean_object* lean_level_mk_param(lean_object* v_name_752_){
_start:
{
lean_object* v___x_753_; 
v___x_753_ = l_Lean_Level_param___override(v_name_752_);
return v___x_753_;
}
}
LEAN_EXPORT lean_object* lean_level_mk_max(lean_object* v_u_754_, lean_object* v_v_755_){
_start:
{
lean_object* v___x_756_; 
v___x_756_ = l_Lean_Level_max___override(v_u_754_, v_v_755_);
return v___x_756_;
}
}
LEAN_EXPORT lean_object* lean_level_mk_imax(lean_object* v_u_757_, lean_object* v_v_758_){
_start:
{
lean_object* v___x_759_; 
v___x_759_ = l_Lean_Level_imax___override(v_u_757_, v_v_758_);
return v___x_759_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_isZero(lean_object* v_x_760_){
_start:
{
if (lean_obj_tag(v_x_760_) == 0)
{
uint8_t v___x_761_; 
v___x_761_ = 1;
return v___x_761_;
}
else
{
uint8_t v___x_762_; 
v___x_762_ = 0;
return v___x_762_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_isZero___boxed(lean_object* v_x_763_){
_start:
{
uint8_t v_res_764_; lean_object* v_r_765_; 
v_res_764_ = l_Lean_Level_isZero(v_x_763_);
lean_dec(v_x_763_);
v_r_765_ = lean_box(v_res_764_);
return v_r_765_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_isSucc(lean_object* v_x_766_){
_start:
{
if (lean_obj_tag(v_x_766_) == 1)
{
uint8_t v___x_767_; 
v___x_767_ = 1;
return v___x_767_;
}
else
{
uint8_t v___x_768_; 
v___x_768_ = 0;
return v___x_768_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_isSucc___boxed(lean_object* v_x_769_){
_start:
{
uint8_t v_res_770_; lean_object* v_r_771_; 
v_res_770_ = l_Lean_Level_isSucc(v_x_769_);
lean_dec(v_x_769_);
v_r_771_ = lean_box(v_res_770_);
return v_r_771_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_isMax(lean_object* v_x_772_){
_start:
{
if (lean_obj_tag(v_x_772_) == 2)
{
uint8_t v___x_773_; 
v___x_773_ = 1;
return v___x_773_;
}
else
{
uint8_t v___x_774_; 
v___x_774_ = 0;
return v___x_774_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_isMax___boxed(lean_object* v_x_775_){
_start:
{
uint8_t v_res_776_; lean_object* v_r_777_; 
v_res_776_ = l_Lean_Level_isMax(v_x_775_);
lean_dec(v_x_775_);
v_r_777_ = lean_box(v_res_776_);
return v_r_777_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_isIMax(lean_object* v_x_778_){
_start:
{
if (lean_obj_tag(v_x_778_) == 3)
{
uint8_t v___x_779_; 
v___x_779_ = 1;
return v___x_779_;
}
else
{
uint8_t v___x_780_; 
v___x_780_ = 0;
return v___x_780_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_isIMax___boxed(lean_object* v_x_781_){
_start:
{
uint8_t v_res_782_; lean_object* v_r_783_; 
v_res_782_ = l_Lean_Level_isIMax(v_x_781_);
lean_dec(v_x_781_);
v_r_783_ = lean_box(v_res_782_);
return v_r_783_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_isMaxIMax(lean_object* v_x_784_){
_start:
{
switch(lean_obj_tag(v_x_784_))
{
case 2:
{
uint8_t v___x_785_; 
v___x_785_ = 1;
return v___x_785_;
}
case 3:
{
uint8_t v___x_786_; 
v___x_786_ = 1;
return v___x_786_;
}
default: 
{
uint8_t v___x_787_; 
v___x_787_ = 0;
return v___x_787_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_isMaxIMax___boxed(lean_object* v_x_788_){
_start:
{
uint8_t v_res_789_; lean_object* v_r_790_; 
v_res_789_ = l_Lean_Level_isMaxIMax(v_x_788_);
lean_dec(v_x_788_);
v_r_790_ = lean_box(v_res_789_);
return v_r_790_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_isParam(lean_object* v_x_791_){
_start:
{
if (lean_obj_tag(v_x_791_) == 4)
{
uint8_t v___x_792_; 
v___x_792_ = 1;
return v___x_792_;
}
else
{
uint8_t v___x_793_; 
v___x_793_ = 0;
return v___x_793_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_isParam___boxed(lean_object* v_x_794_){
_start:
{
uint8_t v_res_795_; lean_object* v_r_796_; 
v_res_795_ = l_Lean_Level_isParam(v_x_794_);
lean_dec(v_x_794_);
v_r_796_ = lean_box(v_res_795_);
return v_r_796_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_isMVar(lean_object* v_x_797_){
_start:
{
if (lean_obj_tag(v_x_797_) == 5)
{
uint8_t v___x_798_; 
v___x_798_ = 1;
return v___x_798_;
}
else
{
uint8_t v___x_799_; 
v___x_799_ = 0;
return v___x_799_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_isMVar___boxed(lean_object* v_x_800_){
_start:
{
uint8_t v_res_801_; lean_object* v_r_802_; 
v_res_801_ = l_Lean_Level_isMVar(v_x_800_);
lean_dec(v_x_800_);
v_r_802_ = lean_box(v_res_801_);
return v_r_802_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Level_mvarId_x21_spec__0(lean_object* v_msg_803_){
_start:
{
lean_object* v___x_804_; lean_object* v___x_805_; 
v___x_804_ = lean_box(0);
v___x_805_ = lean_panic_fn_borrowed(v___x_804_, v_msg_803_);
return v___x_805_;
}
}
static lean_object* _init_l_Lean_Level_mvarId_x21___closed__3(void){
_start:
{
lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; 
v___x_809_ = ((lean_object*)(l_Lean_Level_mvarId_x21___closed__2));
v___x_810_ = lean_unsigned_to_nat(19u);
v___x_811_ = lean_unsigned_to_nat(196u);
v___x_812_ = ((lean_object*)(l_Lean_Level_mvarId_x21___closed__1));
v___x_813_ = ((lean_object*)(l_Lean_Level_mvarId_x21___closed__0));
v___x_814_ = l_mkPanicMessageWithDecl(v___x_813_, v___x_812_, v___x_811_, v___x_810_, v___x_809_);
return v___x_814_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_mvarId_x21(lean_object* v_x_815_){
_start:
{
if (lean_obj_tag(v_x_815_) == 5)
{
lean_object* v_a_816_; 
v_a_816_ = lean_ctor_get(v_x_815_, 0);
lean_inc(v_a_816_);
return v_a_816_;
}
else
{
lean_object* v___x_817_; lean_object* v___x_818_; 
v___x_817_ = lean_obj_once(&l_Lean_Level_mvarId_x21___closed__3, &l_Lean_Level_mvarId_x21___closed__3_once, _init_l_Lean_Level_mvarId_x21___closed__3);
v___x_818_ = l_panic___at___00Lean_Level_mvarId_x21_spec__0(v___x_817_);
return v___x_818_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_mvarId_x21___boxed(lean_object* v_x_819_){
_start:
{
lean_object* v_res_820_; 
v_res_820_ = l_Lean_Level_mvarId_x21(v_x_819_);
lean_dec(v_x_819_);
return v_res_820_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_isNeverZero(lean_object* v_x_821_){
_start:
{
switch(lean_obj_tag(v_x_821_))
{
case 0:
{
uint8_t v___x_822_; 
v___x_822_ = 0;
return v___x_822_;
}
case 1:
{
uint8_t v___x_823_; 
v___x_823_ = 1;
return v___x_823_;
}
case 2:
{
lean_object* v_a_824_; lean_object* v_a_825_; uint8_t v___x_826_; 
v_a_824_ = lean_ctor_get(v_x_821_, 0);
v_a_825_ = lean_ctor_get(v_x_821_, 1);
v___x_826_ = l_Lean_Level_isNeverZero(v_a_824_);
if (v___x_826_ == 0)
{
v_x_821_ = v_a_825_;
goto _start;
}
else
{
return v___x_826_;
}
}
case 3:
{
lean_object* v_a_828_; 
v_a_828_ = lean_ctor_get(v_x_821_, 1);
v_x_821_ = v_a_828_;
goto _start;
}
default: 
{
uint8_t v___x_830_; 
v___x_830_ = 0;
return v___x_830_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_isNeverZero___boxed(lean_object* v_x_831_){
_start:
{
uint8_t v_res_832_; lean_object* v_r_833_; 
v_res_832_ = l_Lean_Level_isNeverZero(v_x_831_);
lean_dec(v_x_831_);
v_r_833_ = lean_box(v_res_832_);
return v_r_833_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_isAlwaysZero(lean_object* v_x_834_){
_start:
{
switch(lean_obj_tag(v_x_834_))
{
case 0:
{
uint8_t v___x_835_; 
v___x_835_ = 1;
return v___x_835_;
}
case 2:
{
lean_object* v_a_836_; lean_object* v_a_837_; uint8_t v___x_838_; 
v_a_836_ = lean_ctor_get(v_x_834_, 0);
v_a_837_ = lean_ctor_get(v_x_834_, 1);
v___x_838_ = l_Lean_Level_isAlwaysZero(v_a_836_);
if (v___x_838_ == 0)
{
return v___x_838_;
}
else
{
v_x_834_ = v_a_837_;
goto _start;
}
}
case 3:
{
lean_object* v_a_840_; 
v_a_840_ = lean_ctor_get(v_x_834_, 1);
v_x_834_ = v_a_840_;
goto _start;
}
default: 
{
uint8_t v___x_842_; 
v___x_842_ = 0;
return v___x_842_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_isAlwaysZero___boxed(lean_object* v_x_843_){
_start:
{
uint8_t v_res_844_; lean_object* v_r_845_; 
v_res_844_ = l_Lean_Level_isAlwaysZero(v_x_843_);
lean_dec(v_x_843_);
v_r_845_ = lean_box(v_res_844_);
return v_r_845_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_ofNat(lean_object* v_x_846_){
_start:
{
lean_object* v_zero_847_; uint8_t v_isZero_848_; 
v_zero_847_ = lean_unsigned_to_nat(0u);
v_isZero_848_ = lean_nat_dec_eq(v_x_846_, v_zero_847_);
if (v_isZero_848_ == 1)
{
lean_object* v___x_849_; 
v___x_849_ = lean_box(0);
return v___x_849_;
}
else
{
lean_object* v_one_850_; lean_object* v_n_851_; lean_object* v___x_852_; lean_object* v___x_853_; 
v_one_850_ = lean_unsigned_to_nat(1u);
v_n_851_ = lean_nat_sub(v_x_846_, v_one_850_);
v___x_852_ = l_Lean_Level_ofNat(v_n_851_);
lean_dec(v_n_851_);
v___x_853_ = l_Lean_Level_succ___override(v___x_852_);
return v___x_853_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_ofNat___boxed(lean_object* v_x_854_){
_start:
{
lean_object* v_res_855_; 
v_res_855_ = l_Lean_Level_ofNat(v_x_854_);
lean_dec(v_x_854_);
return v_res_855_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_instOfNat(lean_object* v_n_856_){
_start:
{
lean_object* v___x_857_; 
v___x_857_ = l_Lean_Level_ofNat(v_n_856_);
return v___x_857_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_instOfNat___boxed(lean_object* v_n_858_){
_start:
{
lean_object* v_res_859_; 
v_res_859_ = l_Lean_Level_instOfNat(v_n_858_);
lean_dec(v_n_858_);
return v_res_859_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_addOffsetAux(lean_object* v_x_860_, lean_object* v_x_861_){
_start:
{
lean_object* v_zero_862_; uint8_t v_isZero_863_; 
v_zero_862_ = lean_unsigned_to_nat(0u);
v_isZero_863_ = lean_nat_dec_eq(v_x_860_, v_zero_862_);
if (v_isZero_863_ == 1)
{
lean_dec(v_x_860_);
return v_x_861_;
}
else
{
lean_object* v_one_864_; lean_object* v_n_865_; lean_object* v___x_866_; 
v_one_864_ = lean_unsigned_to_nat(1u);
v_n_865_ = lean_nat_sub(v_x_860_, v_one_864_);
lean_dec(v_x_860_);
v___x_866_ = l_Lean_Level_succ___override(v_x_861_);
v_x_860_ = v_n_865_;
v_x_861_ = v___x_866_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_addOffset(lean_object* v_u_868_, lean_object* v_n_869_){
_start:
{
lean_object* v___x_870_; 
v___x_870_ = l_Lean_Level_addOffsetAux(v_n_869_, v_u_868_);
return v___x_870_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_isExplicit(lean_object* v_x_871_){
_start:
{
switch(lean_obj_tag(v_x_871_))
{
case 0:
{
uint8_t v___x_872_; 
v___x_872_ = 1;
return v___x_872_;
}
case 1:
{
lean_object* v_a_873_; uint8_t v___x_874_; 
v_a_873_ = lean_ctor_get(v_x_871_, 0);
v___x_874_ = l_Lean_Level_hasMVar(v_a_873_);
if (v___x_874_ == 0)
{
uint8_t v___x_875_; 
v___x_875_ = l_Lean_Level_hasParam(v_a_873_);
if (v___x_875_ == 0)
{
v_x_871_ = v_a_873_;
goto _start;
}
else
{
return v___x_874_;
}
}
else
{
uint8_t v___x_877_; 
v___x_877_ = 0;
return v___x_877_;
}
}
default: 
{
uint8_t v___x_878_; 
v___x_878_ = 0;
return v___x_878_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_isExplicit___boxed(lean_object* v_x_879_){
_start:
{
uint8_t v_res_880_; lean_object* v_r_881_; 
v_res_880_ = l_Lean_Level_isExplicit(v_x_879_);
lean_dec(v_x_879_);
v_r_881_ = lean_box(v_res_880_);
return v_r_881_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_getOffsetAux(lean_object* v_x_882_, lean_object* v_x_883_){
_start:
{
if (lean_obj_tag(v_x_882_) == 1)
{
lean_object* v_a_884_; lean_object* v___x_885_; lean_object* v___x_886_; 
v_a_884_ = lean_ctor_get(v_x_882_, 0);
v___x_885_ = lean_unsigned_to_nat(1u);
v___x_886_ = lean_nat_add(v_x_883_, v___x_885_);
lean_dec(v_x_883_);
v_x_882_ = v_a_884_;
v_x_883_ = v___x_886_;
goto _start;
}
else
{
return v_x_883_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_getOffsetAux___boxed(lean_object* v_x_888_, lean_object* v_x_889_){
_start:
{
lean_object* v_res_890_; 
v_res_890_ = l_Lean_Level_getOffsetAux(v_x_888_, v_x_889_);
lean_dec(v_x_888_);
return v_res_890_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_getOffset(lean_object* v_lvl_891_){
_start:
{
lean_object* v___x_892_; lean_object* v___x_893_; 
v___x_892_ = lean_unsigned_to_nat(0u);
v___x_893_ = l_Lean_Level_getOffsetAux(v_lvl_891_, v___x_892_);
return v___x_893_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_getOffset___boxed(lean_object* v_lvl_894_){
_start:
{
lean_object* v_res_895_; 
v_res_895_ = l_Lean_Level_getOffset(v_lvl_894_);
lean_dec(v_lvl_894_);
return v_res_895_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_getLevelOffset(lean_object* v_x_896_){
_start:
{
if (lean_obj_tag(v_x_896_) == 1)
{
lean_object* v_a_897_; 
v_a_897_ = lean_ctor_get(v_x_896_, 0);
v_x_896_ = v_a_897_;
goto _start;
}
else
{
lean_inc(v_x_896_);
return v_x_896_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_getLevelOffset___boxed(lean_object* v_x_899_){
_start:
{
lean_object* v_res_900_; 
v_res_900_ = l_Lean_Level_getLevelOffset(v_x_899_);
lean_dec(v_x_899_);
return v_res_900_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_toNat(lean_object* v_lvl_901_){
_start:
{
lean_object* v___x_902_; 
v___x_902_ = l_Lean_Level_getLevelOffset(v_lvl_901_);
if (lean_obj_tag(v___x_902_) == 0)
{
lean_object* v___x_903_; lean_object* v___x_904_; 
v___x_903_ = l_Lean_Level_getOffset(v_lvl_901_);
v___x_904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_904_, 0, v___x_903_);
return v___x_904_;
}
else
{
lean_object* v___x_905_; 
lean_dec(v___x_902_);
v___x_905_ = lean_box(0);
return v___x_905_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_toNat___boxed(lean_object* v_lvl_906_){
_start:
{
lean_object* v_res_907_; 
v_res_907_ = l_Lean_Level_toNat(v_lvl_906_);
lean_dec(v_lvl_906_);
return v_res_907_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_beq___boxed(lean_object* v_a_910_, lean_object* v_b_911_){
_start:
{
uint8_t v_res_912_; lean_object* v_r_913_; 
v_res_912_ = lean_level_eq(v_a_910_, v_b_911_);
lean_dec(v_b_911_);
lean_dec(v_a_910_);
v_r_913_ = lean_box(v_res_912_);
return v_r_913_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_occurs(lean_object* v_x_916_, lean_object* v_x_917_){
_start:
{
switch(lean_obj_tag(v_x_917_))
{
case 1:
{
lean_object* v_a_918_; uint8_t v___x_919_; 
v_a_918_ = lean_ctor_get(v_x_917_, 0);
v___x_919_ = lean_level_eq(v_x_916_, v_x_917_);
if (v___x_919_ == 0)
{
v_x_917_ = v_a_918_;
goto _start;
}
else
{
return v___x_919_;
}
}
case 2:
{
lean_object* v_a_921_; lean_object* v_a_922_; uint8_t v___y_924_; uint8_t v___x_926_; 
v_a_921_ = lean_ctor_get(v_x_917_, 0);
v_a_922_ = lean_ctor_get(v_x_917_, 1);
v___x_926_ = lean_level_eq(v_x_916_, v_x_917_);
if (v___x_926_ == 0)
{
uint8_t v___x_927_; 
v___x_927_ = l_Lean_Level_occurs(v_x_916_, v_a_921_);
v___y_924_ = v___x_927_;
goto v___jp_923_;
}
else
{
v___y_924_ = v___x_926_;
goto v___jp_923_;
}
v___jp_923_:
{
if (v___y_924_ == 0)
{
v_x_917_ = v_a_922_;
goto _start;
}
else
{
return v___y_924_;
}
}
}
case 3:
{
lean_object* v_a_928_; lean_object* v_a_929_; uint8_t v___y_931_; uint8_t v___x_933_; 
v_a_928_ = lean_ctor_get(v_x_917_, 0);
v_a_929_ = lean_ctor_get(v_x_917_, 1);
v___x_933_ = lean_level_eq(v_x_916_, v_x_917_);
if (v___x_933_ == 0)
{
uint8_t v___x_934_; 
v___x_934_ = l_Lean_Level_occurs(v_x_916_, v_a_928_);
v___y_931_ = v___x_934_;
goto v___jp_930_;
}
else
{
v___y_931_ = v___x_933_;
goto v___jp_930_;
}
v___jp_930_:
{
if (v___y_931_ == 0)
{
v_x_917_ = v_a_929_;
goto _start;
}
else
{
return v___y_931_;
}
}
}
default: 
{
uint8_t v___x_935_; 
v___x_935_ = lean_level_eq(v_x_916_, v_x_917_);
return v___x_935_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_occurs___boxed(lean_object* v_x_936_, lean_object* v_x_937_){
_start:
{
uint8_t v_res_938_; lean_object* v_r_939_; 
v_res_938_ = l_Lean_Level_occurs(v_x_936_, v_x_937_);
lean_dec(v_x_937_);
lean_dec(v_x_936_);
v_r_939_ = lean_box(v_res_938_);
return v_r_939_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_ctorToNat(lean_object* v_x_940_){
_start:
{
switch(lean_obj_tag(v_x_940_))
{
case 0:
{
lean_object* v___x_941_; 
v___x_941_ = lean_unsigned_to_nat(0u);
return v___x_941_;
}
case 1:
{
lean_object* v___x_942_; 
v___x_942_ = lean_unsigned_to_nat(3u);
return v___x_942_;
}
case 2:
{
lean_object* v___x_943_; 
v___x_943_ = lean_unsigned_to_nat(4u);
return v___x_943_;
}
case 3:
{
lean_object* v___x_944_; 
v___x_944_ = lean_unsigned_to_nat(5u);
return v___x_944_;
}
case 4:
{
lean_object* v___x_945_; 
v___x_945_ = lean_unsigned_to_nat(1u);
return v___x_945_;
}
default: 
{
lean_object* v___x_946_; 
v___x_946_ = lean_unsigned_to_nat(2u);
return v___x_946_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_ctorToNat___boxed(lean_object* v_x_947_){
_start:
{
lean_object* v_res_948_; 
v_res_948_ = l_Lean_Level_ctorToNat(v_x_947_);
lean_dec(v_x_947_);
return v_res_948_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_normLtAux(lean_object* v_x_949_, lean_object* v_x_950_, lean_object* v_x_951_, lean_object* v_x_952_){
_start:
{
lean_object* v_l_u2081_954_; lean_object* v_k_u2081_955_; lean_object* v_l_u2082_956_; lean_object* v_k_u2082_957_; lean_object* v_l_u2081_962_; lean_object* v_k_u2081_963_; lean_object* v_l_u2082_964_; lean_object* v_k_u2082_965_; 
switch(lean_obj_tag(v_x_949_))
{
case 1:
{
lean_object* v_a_971_; lean_object* v___x_972_; lean_object* v___x_973_; 
v_a_971_ = lean_ctor_get(v_x_949_, 0);
v___x_972_ = lean_unsigned_to_nat(1u);
v___x_973_ = lean_nat_add(v_x_950_, v___x_972_);
lean_dec(v_x_950_);
v_x_949_ = v_a_971_;
v_x_950_ = v___x_973_;
goto _start;
}
case 2:
{
switch(lean_obj_tag(v_x_951_))
{
case 1:
{
lean_object* v_a_975_; 
v_a_975_ = lean_ctor_get(v_x_951_, 0);
v_l_u2081_954_ = v_x_949_;
v_k_u2081_955_ = v_x_950_;
v_l_u2082_956_ = v_a_975_;
v_k_u2082_957_ = v_x_952_;
goto v___jp_953_;
}
case 2:
{
lean_object* v_a_976_; lean_object* v_a_977_; lean_object* v_a_978_; lean_object* v_a_979_; uint8_t v___x_983_; 
v_a_976_ = lean_ctor_get(v_x_949_, 0);
v_a_977_ = lean_ctor_get(v_x_949_, 1);
v_a_978_ = lean_ctor_get(v_x_951_, 0);
v_a_979_ = lean_ctor_get(v_x_951_, 1);
v___x_983_ = lean_level_eq(v_x_949_, v_x_951_);
if (v___x_983_ == 0)
{
uint8_t v___x_984_; 
lean_dec(v_x_952_);
lean_dec(v_x_950_);
v___x_984_ = lean_level_eq(v_a_976_, v_a_978_);
if (v___x_984_ == 0)
{
goto v___jp_980_;
}
else
{
if (v___x_983_ == 0)
{
lean_object* v___x_985_; 
v___x_985_ = lean_unsigned_to_nat(0u);
v_x_949_ = v_a_977_;
v_x_950_ = v___x_985_;
v_x_951_ = v_a_979_;
v_x_952_ = v___x_985_;
goto _start;
}
else
{
goto v___jp_980_;
}
}
}
else
{
uint8_t v___x_987_; 
v___x_987_ = lean_nat_dec_lt(v_x_950_, v_x_952_);
lean_dec(v_x_952_);
lean_dec(v_x_950_);
return v___x_987_;
}
v___jp_980_:
{
lean_object* v___x_981_; 
v___x_981_ = lean_unsigned_to_nat(0u);
v_x_949_ = v_a_976_;
v_x_950_ = v___x_981_;
v_x_951_ = v_a_978_;
v_x_952_ = v___x_981_;
goto _start;
}
}
default: 
{
v_l_u2081_962_ = v_x_949_;
v_k_u2081_963_ = v_x_950_;
v_l_u2082_964_ = v_x_951_;
v_k_u2082_965_ = v_x_952_;
goto v___jp_961_;
}
}
}
case 3:
{
switch(lean_obj_tag(v_x_951_))
{
case 1:
{
lean_object* v_a_988_; 
v_a_988_ = lean_ctor_get(v_x_951_, 0);
v_l_u2081_954_ = v_x_949_;
v_k_u2081_955_ = v_x_950_;
v_l_u2082_956_ = v_a_988_;
v_k_u2082_957_ = v_x_952_;
goto v___jp_953_;
}
case 3:
{
lean_object* v_a_989_; lean_object* v_a_990_; lean_object* v_a_991_; lean_object* v_a_992_; uint8_t v___x_996_; 
v_a_989_ = lean_ctor_get(v_x_949_, 0);
v_a_990_ = lean_ctor_get(v_x_949_, 1);
v_a_991_ = lean_ctor_get(v_x_951_, 0);
v_a_992_ = lean_ctor_get(v_x_951_, 1);
v___x_996_ = lean_level_eq(v_x_949_, v_x_951_);
if (v___x_996_ == 0)
{
uint8_t v___x_997_; 
lean_dec(v_x_952_);
lean_dec(v_x_950_);
v___x_997_ = lean_level_eq(v_a_989_, v_a_991_);
if (v___x_997_ == 0)
{
goto v___jp_993_;
}
else
{
if (v___x_996_ == 0)
{
lean_object* v___x_998_; 
v___x_998_ = lean_unsigned_to_nat(0u);
v_x_949_ = v_a_990_;
v_x_950_ = v___x_998_;
v_x_951_ = v_a_992_;
v_x_952_ = v___x_998_;
goto _start;
}
else
{
goto v___jp_993_;
}
}
}
else
{
uint8_t v___x_1000_; 
v___x_1000_ = lean_nat_dec_lt(v_x_950_, v_x_952_);
lean_dec(v_x_952_);
lean_dec(v_x_950_);
return v___x_1000_;
}
v___jp_993_:
{
lean_object* v___x_994_; 
v___x_994_ = lean_unsigned_to_nat(0u);
v_x_949_ = v_a_989_;
v_x_950_ = v___x_994_;
v_x_951_ = v_a_991_;
v_x_952_ = v___x_994_;
goto _start;
}
}
default: 
{
v_l_u2081_962_ = v_x_949_;
v_k_u2081_963_ = v_x_950_;
v_l_u2082_964_ = v_x_951_;
v_k_u2082_965_ = v_x_952_;
goto v___jp_961_;
}
}
}
case 4:
{
switch(lean_obj_tag(v_x_951_))
{
case 1:
{
lean_object* v_a_1001_; 
v_a_1001_ = lean_ctor_get(v_x_951_, 0);
v_l_u2081_954_ = v_x_949_;
v_k_u2081_955_ = v_x_950_;
v_l_u2082_956_ = v_a_1001_;
v_k_u2082_957_ = v_x_952_;
goto v___jp_953_;
}
case 4:
{
lean_object* v_a_1002_; lean_object* v_a_1003_; uint8_t v___x_1004_; 
v_a_1002_ = lean_ctor_get(v_x_949_, 0);
v_a_1003_ = lean_ctor_get(v_x_951_, 0);
v___x_1004_ = lean_name_eq(v_a_1002_, v_a_1003_);
if (v___x_1004_ == 0)
{
uint8_t v___x_1005_; 
lean_dec(v_x_952_);
lean_dec(v_x_950_);
v___x_1005_ = l_Lean_Name_lt(v_a_1002_, v_a_1003_);
return v___x_1005_;
}
else
{
uint8_t v___x_1006_; 
v___x_1006_ = lean_nat_dec_lt(v_x_950_, v_x_952_);
lean_dec(v_x_952_);
lean_dec(v_x_950_);
return v___x_1006_;
}
}
default: 
{
v_l_u2081_962_ = v_x_949_;
v_k_u2081_963_ = v_x_950_;
v_l_u2082_964_ = v_x_951_;
v_k_u2082_965_ = v_x_952_;
goto v___jp_961_;
}
}
}
case 5:
{
switch(lean_obj_tag(v_x_951_))
{
case 1:
{
lean_object* v_a_1007_; 
v_a_1007_ = lean_ctor_get(v_x_951_, 0);
v_l_u2081_954_ = v_x_949_;
v_k_u2081_955_ = v_x_950_;
v_l_u2082_956_ = v_a_1007_;
v_k_u2082_957_ = v_x_952_;
goto v___jp_953_;
}
case 5:
{
lean_object* v_a_1008_; lean_object* v_a_1009_; uint8_t v___x_1010_; 
v_a_1008_ = lean_ctor_get(v_x_949_, 0);
v_a_1009_ = lean_ctor_get(v_x_951_, 0);
v___x_1010_ = lean_name_eq(v_a_1008_, v_a_1009_);
if (v___x_1010_ == 0)
{
uint8_t v___x_1011_; 
lean_dec(v_x_952_);
lean_dec(v_x_950_);
v___x_1011_ = l_Lean_Name_lt(v_a_1008_, v_a_1009_);
return v___x_1011_;
}
else
{
uint8_t v___x_1012_; 
v___x_1012_ = lean_nat_dec_lt(v_x_950_, v_x_952_);
lean_dec(v_x_952_);
lean_dec(v_x_950_);
return v___x_1012_;
}
}
default: 
{
v_l_u2081_962_ = v_x_949_;
v_k_u2081_963_ = v_x_950_;
v_l_u2082_964_ = v_x_951_;
v_k_u2082_965_ = v_x_952_;
goto v___jp_961_;
}
}
}
default: 
{
if (lean_obj_tag(v_x_951_) == 1)
{
lean_object* v_a_1013_; 
v_a_1013_ = lean_ctor_get(v_x_951_, 0);
v_l_u2081_954_ = v_x_949_;
v_k_u2081_955_ = v_x_950_;
v_l_u2082_956_ = v_a_1013_;
v_k_u2082_957_ = v_x_952_;
goto v___jp_953_;
}
else
{
v_l_u2081_962_ = v_x_949_;
v_k_u2081_963_ = v_x_950_;
v_l_u2082_964_ = v_x_951_;
v_k_u2082_965_ = v_x_952_;
goto v___jp_961_;
}
}
}
v___jp_953_:
{
lean_object* v___x_958_; lean_object* v___x_959_; 
v___x_958_ = lean_unsigned_to_nat(1u);
v___x_959_ = lean_nat_add(v_k_u2082_957_, v___x_958_);
lean_dec(v_k_u2082_957_);
v_x_949_ = v_l_u2081_954_;
v_x_950_ = v_k_u2081_955_;
v_x_951_ = v_l_u2082_956_;
v_x_952_ = v___x_959_;
goto _start;
}
v___jp_961_:
{
uint8_t v___x_966_; 
v___x_966_ = lean_level_eq(v_l_u2081_962_, v_l_u2082_964_);
if (v___x_966_ == 0)
{
lean_object* v___x_967_; lean_object* v___x_968_; uint8_t v___x_969_; 
lean_dec(v_k_u2082_965_);
lean_dec(v_k_u2081_963_);
v___x_967_ = l_Lean_Level_ctorToNat(v_l_u2081_962_);
v___x_968_ = l_Lean_Level_ctorToNat(v_l_u2082_964_);
v___x_969_ = lean_nat_dec_lt(v___x_967_, v___x_968_);
lean_dec(v___x_968_);
lean_dec(v___x_967_);
return v___x_969_;
}
else
{
uint8_t v___x_970_; 
v___x_970_ = lean_nat_dec_lt(v_k_u2081_963_, v_k_u2082_965_);
lean_dec(v_k_u2082_965_);
lean_dec(v_k_u2081_963_);
return v___x_970_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_normLtAux___boxed(lean_object* v_x_1014_, lean_object* v_x_1015_, lean_object* v_x_1016_, lean_object* v_x_1017_){
_start:
{
uint8_t v_res_1018_; lean_object* v_r_1019_; 
v_res_1018_ = l_Lean_Level_normLtAux(v_x_1014_, v_x_1015_, v_x_1016_, v_x_1017_);
lean_dec(v_x_1016_);
lean_dec(v_x_1014_);
v_r_1019_ = lean_box(v_res_1018_);
return v_r_1019_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_normLtAux_match__1_splitter___redArg(lean_object* v_x_1020_, lean_object* v_x_1021_, lean_object* v_x_1022_, lean_object* v_x_1023_, lean_object* v_h__1_1024_, lean_object* v_h__2_1025_, lean_object* v_h__3_1026_, lean_object* v_h__4_1027_, lean_object* v_h__5_1028_, lean_object* v_h__6_1029_, lean_object* v_h__7_1030_){
_start:
{
switch(lean_obj_tag(v_x_1020_))
{
case 1:
{
lean_object* v_a_1031_; lean_object* v___x_1032_; 
lean_dec(v_h__7_1030_);
lean_dec(v_h__6_1029_);
lean_dec(v_h__5_1028_);
lean_dec(v_h__4_1027_);
lean_dec(v_h__3_1026_);
lean_dec(v_h__2_1025_);
v_a_1031_ = lean_ctor_get(v_x_1020_, 0);
lean_inc(v_a_1031_);
lean_dec_ref_known(v_x_1020_, 1);
v___x_1032_ = lean_apply_4(v_h__1_1024_, v_a_1031_, v_x_1021_, v_x_1022_, v_x_1023_);
return v___x_1032_;
}
case 2:
{
lean_dec(v_h__6_1029_);
lean_dec(v_h__5_1028_);
lean_dec(v_h__4_1027_);
lean_dec(v_h__1_1024_);
switch(lean_obj_tag(v_x_1022_))
{
case 1:
{
lean_object* v_a_1033_; lean_object* v___x_1034_; 
lean_dec(v_h__7_1030_);
lean_dec(v_h__3_1026_);
v_a_1033_ = lean_ctor_get(v_x_1022_, 0);
lean_inc(v_a_1033_);
lean_dec_ref_known(v_x_1022_, 1);
v___x_1034_ = lean_apply_5(v_h__2_1025_, v_x_1020_, v_x_1021_, v_a_1033_, v_x_1023_, lean_box(0));
return v___x_1034_;
}
case 2:
{
lean_object* v_a_1035_; lean_object* v_a_1036_; lean_object* v_a_1037_; lean_object* v_a_1038_; lean_object* v___x_1039_; 
lean_dec(v_h__7_1030_);
lean_dec(v_h__2_1025_);
v_a_1035_ = lean_ctor_get(v_x_1020_, 0);
lean_inc(v_a_1035_);
v_a_1036_ = lean_ctor_get(v_x_1020_, 1);
lean_inc(v_a_1036_);
lean_dec_ref_known(v_x_1020_, 2);
v_a_1037_ = lean_ctor_get(v_x_1022_, 0);
lean_inc(v_a_1037_);
v_a_1038_ = lean_ctor_get(v_x_1022_, 1);
lean_inc(v_a_1038_);
lean_dec_ref_known(v_x_1022_, 2);
v___x_1039_ = lean_apply_6(v_h__3_1026_, v_a_1035_, v_a_1036_, v_x_1021_, v_a_1037_, v_a_1038_, v_x_1023_);
return v___x_1039_;
}
default: 
{
lean_object* v___x_1040_; 
lean_dec(v_h__3_1026_);
lean_dec(v_h__2_1025_);
v___x_1040_ = lean_apply_10(v_h__7_1030_, v_x_1020_, v_x_1021_, v_x_1022_, v_x_1023_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_1040_;
}
}
}
case 3:
{
lean_dec(v_h__6_1029_);
lean_dec(v_h__5_1028_);
lean_dec(v_h__3_1026_);
lean_dec(v_h__1_1024_);
switch(lean_obj_tag(v_x_1022_))
{
case 1:
{
lean_object* v_a_1041_; lean_object* v___x_1042_; 
lean_dec(v_h__7_1030_);
lean_dec(v_h__4_1027_);
v_a_1041_ = lean_ctor_get(v_x_1022_, 0);
lean_inc(v_a_1041_);
lean_dec_ref_known(v_x_1022_, 1);
v___x_1042_ = lean_apply_5(v_h__2_1025_, v_x_1020_, v_x_1021_, v_a_1041_, v_x_1023_, lean_box(0));
return v___x_1042_;
}
case 3:
{
lean_object* v_a_1043_; lean_object* v_a_1044_; lean_object* v_a_1045_; lean_object* v_a_1046_; lean_object* v___x_1047_; 
lean_dec(v_h__7_1030_);
lean_dec(v_h__2_1025_);
v_a_1043_ = lean_ctor_get(v_x_1020_, 0);
lean_inc(v_a_1043_);
v_a_1044_ = lean_ctor_get(v_x_1020_, 1);
lean_inc(v_a_1044_);
lean_dec_ref_known(v_x_1020_, 2);
v_a_1045_ = lean_ctor_get(v_x_1022_, 0);
lean_inc(v_a_1045_);
v_a_1046_ = lean_ctor_get(v_x_1022_, 1);
lean_inc(v_a_1046_);
lean_dec_ref_known(v_x_1022_, 2);
v___x_1047_ = lean_apply_6(v_h__4_1027_, v_a_1043_, v_a_1044_, v_x_1021_, v_a_1045_, v_a_1046_, v_x_1023_);
return v___x_1047_;
}
default: 
{
lean_object* v___x_1048_; 
lean_dec(v_h__4_1027_);
lean_dec(v_h__2_1025_);
v___x_1048_ = lean_apply_10(v_h__7_1030_, v_x_1020_, v_x_1021_, v_x_1022_, v_x_1023_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_1048_;
}
}
}
case 4:
{
lean_dec(v_h__6_1029_);
lean_dec(v_h__4_1027_);
lean_dec(v_h__3_1026_);
lean_dec(v_h__1_1024_);
switch(lean_obj_tag(v_x_1022_))
{
case 1:
{
lean_object* v_a_1049_; lean_object* v___x_1050_; 
lean_dec(v_h__7_1030_);
lean_dec(v_h__5_1028_);
v_a_1049_ = lean_ctor_get(v_x_1022_, 0);
lean_inc(v_a_1049_);
lean_dec_ref_known(v_x_1022_, 1);
v___x_1050_ = lean_apply_5(v_h__2_1025_, v_x_1020_, v_x_1021_, v_a_1049_, v_x_1023_, lean_box(0));
return v___x_1050_;
}
case 4:
{
lean_object* v_a_1051_; lean_object* v_a_1052_; lean_object* v___x_1053_; 
lean_dec(v_h__7_1030_);
lean_dec(v_h__2_1025_);
v_a_1051_ = lean_ctor_get(v_x_1020_, 0);
lean_inc(v_a_1051_);
lean_dec_ref_known(v_x_1020_, 1);
v_a_1052_ = lean_ctor_get(v_x_1022_, 0);
lean_inc(v_a_1052_);
lean_dec_ref_known(v_x_1022_, 1);
v___x_1053_ = lean_apply_4(v_h__5_1028_, v_a_1051_, v_x_1021_, v_a_1052_, v_x_1023_);
return v___x_1053_;
}
default: 
{
lean_object* v___x_1054_; 
lean_dec(v_h__5_1028_);
lean_dec(v_h__2_1025_);
v___x_1054_ = lean_apply_10(v_h__7_1030_, v_x_1020_, v_x_1021_, v_x_1022_, v_x_1023_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_1054_;
}
}
}
case 5:
{
lean_dec(v_h__5_1028_);
lean_dec(v_h__4_1027_);
lean_dec(v_h__3_1026_);
lean_dec(v_h__1_1024_);
switch(lean_obj_tag(v_x_1022_))
{
case 1:
{
lean_object* v_a_1055_; lean_object* v___x_1056_; 
lean_dec(v_h__7_1030_);
lean_dec(v_h__6_1029_);
v_a_1055_ = lean_ctor_get(v_x_1022_, 0);
lean_inc(v_a_1055_);
lean_dec_ref_known(v_x_1022_, 1);
v___x_1056_ = lean_apply_5(v_h__2_1025_, v_x_1020_, v_x_1021_, v_a_1055_, v_x_1023_, lean_box(0));
return v___x_1056_;
}
case 5:
{
lean_object* v_a_1057_; lean_object* v_a_1058_; lean_object* v___x_1059_; 
lean_dec(v_h__7_1030_);
lean_dec(v_h__2_1025_);
v_a_1057_ = lean_ctor_get(v_x_1020_, 0);
lean_inc(v_a_1057_);
lean_dec_ref_known(v_x_1020_, 1);
v_a_1058_ = lean_ctor_get(v_x_1022_, 0);
lean_inc(v_a_1058_);
lean_dec_ref_known(v_x_1022_, 1);
v___x_1059_ = lean_apply_4(v_h__6_1029_, v_a_1057_, v_x_1021_, v_a_1058_, v_x_1023_);
return v___x_1059_;
}
default: 
{
lean_object* v___x_1060_; 
lean_dec(v_h__6_1029_);
lean_dec(v_h__2_1025_);
v___x_1060_ = lean_apply_10(v_h__7_1030_, v_x_1020_, v_x_1021_, v_x_1022_, v_x_1023_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_1060_;
}
}
}
default: 
{
lean_dec(v_h__6_1029_);
lean_dec(v_h__5_1028_);
lean_dec(v_h__4_1027_);
lean_dec(v_h__3_1026_);
lean_dec(v_h__1_1024_);
if (lean_obj_tag(v_x_1022_) == 1)
{
lean_object* v_a_1061_; lean_object* v___x_1062_; 
lean_dec(v_h__7_1030_);
v_a_1061_ = lean_ctor_get(v_x_1022_, 0);
lean_inc(v_a_1061_);
lean_dec_ref_known(v_x_1022_, 1);
v___x_1062_ = lean_apply_5(v_h__2_1025_, v_x_1020_, v_x_1021_, v_a_1061_, v_x_1023_, lean_box(0));
return v___x_1062_;
}
else
{
lean_object* v___x_1063_; 
lean_dec(v_h__2_1025_);
v___x_1063_ = lean_apply_10(v_h__7_1030_, v_x_1020_, v_x_1021_, v_x_1022_, v_x_1023_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_1063_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_normLtAux_match__1_splitter(lean_object* v_motive_1064_, lean_object* v_x_1065_, lean_object* v_x_1066_, lean_object* v_x_1067_, lean_object* v_x_1068_, lean_object* v_h__1_1069_, lean_object* v_h__2_1070_, lean_object* v_h__3_1071_, lean_object* v_h__4_1072_, lean_object* v_h__5_1073_, lean_object* v_h__6_1074_, lean_object* v_h__7_1075_){
_start:
{
switch(lean_obj_tag(v_x_1065_))
{
case 1:
{
lean_object* v_a_1076_; lean_object* v___x_1077_; 
lean_dec(v_h__7_1075_);
lean_dec(v_h__6_1074_);
lean_dec(v_h__5_1073_);
lean_dec(v_h__4_1072_);
lean_dec(v_h__3_1071_);
lean_dec(v_h__2_1070_);
v_a_1076_ = lean_ctor_get(v_x_1065_, 0);
lean_inc(v_a_1076_);
lean_dec_ref_known(v_x_1065_, 1);
v___x_1077_ = lean_apply_4(v_h__1_1069_, v_a_1076_, v_x_1066_, v_x_1067_, v_x_1068_);
return v___x_1077_;
}
case 2:
{
lean_dec(v_h__6_1074_);
lean_dec(v_h__5_1073_);
lean_dec(v_h__4_1072_);
lean_dec(v_h__1_1069_);
switch(lean_obj_tag(v_x_1067_))
{
case 1:
{
lean_object* v_a_1078_; lean_object* v___x_1079_; 
lean_dec(v_h__7_1075_);
lean_dec(v_h__3_1071_);
v_a_1078_ = lean_ctor_get(v_x_1067_, 0);
lean_inc(v_a_1078_);
lean_dec_ref_known(v_x_1067_, 1);
v___x_1079_ = lean_apply_5(v_h__2_1070_, v_x_1065_, v_x_1066_, v_a_1078_, v_x_1068_, lean_box(0));
return v___x_1079_;
}
case 2:
{
lean_object* v_a_1080_; lean_object* v_a_1081_; lean_object* v_a_1082_; lean_object* v_a_1083_; lean_object* v___x_1084_; 
lean_dec(v_h__7_1075_);
lean_dec(v_h__2_1070_);
v_a_1080_ = lean_ctor_get(v_x_1065_, 0);
lean_inc(v_a_1080_);
v_a_1081_ = lean_ctor_get(v_x_1065_, 1);
lean_inc(v_a_1081_);
lean_dec_ref_known(v_x_1065_, 2);
v_a_1082_ = lean_ctor_get(v_x_1067_, 0);
lean_inc(v_a_1082_);
v_a_1083_ = lean_ctor_get(v_x_1067_, 1);
lean_inc(v_a_1083_);
lean_dec_ref_known(v_x_1067_, 2);
v___x_1084_ = lean_apply_6(v_h__3_1071_, v_a_1080_, v_a_1081_, v_x_1066_, v_a_1082_, v_a_1083_, v_x_1068_);
return v___x_1084_;
}
default: 
{
lean_object* v___x_1085_; 
lean_dec(v_h__3_1071_);
lean_dec(v_h__2_1070_);
v___x_1085_ = lean_apply_10(v_h__7_1075_, v_x_1065_, v_x_1066_, v_x_1067_, v_x_1068_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_1085_;
}
}
}
case 3:
{
lean_dec(v_h__6_1074_);
lean_dec(v_h__5_1073_);
lean_dec(v_h__3_1071_);
lean_dec(v_h__1_1069_);
switch(lean_obj_tag(v_x_1067_))
{
case 1:
{
lean_object* v_a_1086_; lean_object* v___x_1087_; 
lean_dec(v_h__7_1075_);
lean_dec(v_h__4_1072_);
v_a_1086_ = lean_ctor_get(v_x_1067_, 0);
lean_inc(v_a_1086_);
lean_dec_ref_known(v_x_1067_, 1);
v___x_1087_ = lean_apply_5(v_h__2_1070_, v_x_1065_, v_x_1066_, v_a_1086_, v_x_1068_, lean_box(0));
return v___x_1087_;
}
case 3:
{
lean_object* v_a_1088_; lean_object* v_a_1089_; lean_object* v_a_1090_; lean_object* v_a_1091_; lean_object* v___x_1092_; 
lean_dec(v_h__7_1075_);
lean_dec(v_h__2_1070_);
v_a_1088_ = lean_ctor_get(v_x_1065_, 0);
lean_inc(v_a_1088_);
v_a_1089_ = lean_ctor_get(v_x_1065_, 1);
lean_inc(v_a_1089_);
lean_dec_ref_known(v_x_1065_, 2);
v_a_1090_ = lean_ctor_get(v_x_1067_, 0);
lean_inc(v_a_1090_);
v_a_1091_ = lean_ctor_get(v_x_1067_, 1);
lean_inc(v_a_1091_);
lean_dec_ref_known(v_x_1067_, 2);
v___x_1092_ = lean_apply_6(v_h__4_1072_, v_a_1088_, v_a_1089_, v_x_1066_, v_a_1090_, v_a_1091_, v_x_1068_);
return v___x_1092_;
}
default: 
{
lean_object* v___x_1093_; 
lean_dec(v_h__4_1072_);
lean_dec(v_h__2_1070_);
v___x_1093_ = lean_apply_10(v_h__7_1075_, v_x_1065_, v_x_1066_, v_x_1067_, v_x_1068_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_1093_;
}
}
}
case 4:
{
lean_dec(v_h__6_1074_);
lean_dec(v_h__4_1072_);
lean_dec(v_h__3_1071_);
lean_dec(v_h__1_1069_);
switch(lean_obj_tag(v_x_1067_))
{
case 1:
{
lean_object* v_a_1094_; lean_object* v___x_1095_; 
lean_dec(v_h__7_1075_);
lean_dec(v_h__5_1073_);
v_a_1094_ = lean_ctor_get(v_x_1067_, 0);
lean_inc(v_a_1094_);
lean_dec_ref_known(v_x_1067_, 1);
v___x_1095_ = lean_apply_5(v_h__2_1070_, v_x_1065_, v_x_1066_, v_a_1094_, v_x_1068_, lean_box(0));
return v___x_1095_;
}
case 4:
{
lean_object* v_a_1096_; lean_object* v_a_1097_; lean_object* v___x_1098_; 
lean_dec(v_h__7_1075_);
lean_dec(v_h__2_1070_);
v_a_1096_ = lean_ctor_get(v_x_1065_, 0);
lean_inc(v_a_1096_);
lean_dec_ref_known(v_x_1065_, 1);
v_a_1097_ = lean_ctor_get(v_x_1067_, 0);
lean_inc(v_a_1097_);
lean_dec_ref_known(v_x_1067_, 1);
v___x_1098_ = lean_apply_4(v_h__5_1073_, v_a_1096_, v_x_1066_, v_a_1097_, v_x_1068_);
return v___x_1098_;
}
default: 
{
lean_object* v___x_1099_; 
lean_dec(v_h__5_1073_);
lean_dec(v_h__2_1070_);
v___x_1099_ = lean_apply_10(v_h__7_1075_, v_x_1065_, v_x_1066_, v_x_1067_, v_x_1068_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_1099_;
}
}
}
case 5:
{
lean_dec(v_h__5_1073_);
lean_dec(v_h__4_1072_);
lean_dec(v_h__3_1071_);
lean_dec(v_h__1_1069_);
switch(lean_obj_tag(v_x_1067_))
{
case 1:
{
lean_object* v_a_1100_; lean_object* v___x_1101_; 
lean_dec(v_h__7_1075_);
lean_dec(v_h__6_1074_);
v_a_1100_ = lean_ctor_get(v_x_1067_, 0);
lean_inc(v_a_1100_);
lean_dec_ref_known(v_x_1067_, 1);
v___x_1101_ = lean_apply_5(v_h__2_1070_, v_x_1065_, v_x_1066_, v_a_1100_, v_x_1068_, lean_box(0));
return v___x_1101_;
}
case 5:
{
lean_object* v_a_1102_; lean_object* v_a_1103_; lean_object* v___x_1104_; 
lean_dec(v_h__7_1075_);
lean_dec(v_h__2_1070_);
v_a_1102_ = lean_ctor_get(v_x_1065_, 0);
lean_inc(v_a_1102_);
lean_dec_ref_known(v_x_1065_, 1);
v_a_1103_ = lean_ctor_get(v_x_1067_, 0);
lean_inc(v_a_1103_);
lean_dec_ref_known(v_x_1067_, 1);
v___x_1104_ = lean_apply_4(v_h__6_1074_, v_a_1102_, v_x_1066_, v_a_1103_, v_x_1068_);
return v___x_1104_;
}
default: 
{
lean_object* v___x_1105_; 
lean_dec(v_h__6_1074_);
lean_dec(v_h__2_1070_);
v___x_1105_ = lean_apply_10(v_h__7_1075_, v_x_1065_, v_x_1066_, v_x_1067_, v_x_1068_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_1105_;
}
}
}
default: 
{
lean_dec(v_h__6_1074_);
lean_dec(v_h__5_1073_);
lean_dec(v_h__4_1072_);
lean_dec(v_h__3_1071_);
lean_dec(v_h__1_1069_);
if (lean_obj_tag(v_x_1067_) == 1)
{
lean_object* v_a_1106_; lean_object* v___x_1107_; 
lean_dec(v_h__7_1075_);
v_a_1106_ = lean_ctor_get(v_x_1067_, 0);
lean_inc(v_a_1106_);
lean_dec_ref_known(v_x_1067_, 1);
v___x_1107_ = lean_apply_5(v_h__2_1070_, v_x_1065_, v_x_1066_, v_a_1106_, v_x_1068_, lean_box(0));
return v___x_1107_;
}
else
{
lean_object* v___x_1108_; 
lean_dec(v_h__2_1070_);
v___x_1108_ = lean_apply_10(v_h__7_1075_, v_x_1065_, v_x_1066_, v_x_1067_, v_x_1068_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_1108_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Level_normLt(lean_object* v_l_u2081_1109_, lean_object* v_l_u2082_1110_){
_start:
{
lean_object* v___x_1111_; uint8_t v___x_1112_; 
v___x_1111_ = lean_unsigned_to_nat(0u);
v___x_1112_ = l_Lean_Level_normLtAux(v_l_u2081_1109_, v___x_1111_, v_l_u2082_1110_, v___x_1111_);
return v___x_1112_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_normLt___boxed(lean_object* v_l_u2081_1113_, lean_object* v_l_u2082_1114_){
_start:
{
uint8_t v_res_1115_; lean_object* v_r_1116_; 
v_res_1115_ = l_Lean_Level_normLt(v_l_u2081_1113_, v_l_u2082_1114_);
lean_dec(v_l_u2082_1114_);
lean_dec(v_l_u2081_1113_);
v_r_1116_ = lean_box(v_res_1115_);
return v_r_1116_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_isAlreadyNormalizedCheap(lean_object* v_x_1117_){
_start:
{
switch(lean_obj_tag(v_x_1117_))
{
case 0:
{
uint8_t v___x_1118_; 
v___x_1118_ = 1;
return v___x_1118_;
}
case 4:
{
uint8_t v___x_1119_; 
v___x_1119_ = 1;
return v___x_1119_;
}
case 5:
{
uint8_t v___x_1120_; 
v___x_1120_ = 1;
return v___x_1120_;
}
case 1:
{
lean_object* v_a_1121_; 
v_a_1121_ = lean_ctor_get(v_x_1117_, 0);
v_x_1117_ = v_a_1121_;
goto _start;
}
default: 
{
uint8_t v___x_1123_; 
v___x_1123_ = 0;
return v___x_1123_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_isAlreadyNormalizedCheap___boxed(lean_object* v_x_1124_){
_start:
{
uint8_t v_res_1125_; lean_object* v_r_1126_; 
v_res_1125_ = l_Lean_Level_isAlreadyNormalizedCheap(v_x_1124_);
lean_dec(v_x_1124_);
v_r_1126_ = lean_box(v_res_1125_);
return v_r_1126_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_mkIMaxAux(lean_object* v_x_1127_, lean_object* v_x_1128_){
_start:
{
lean_object* v_u_u2081_1130_; lean_object* v_u_u2082_1131_; 
if (lean_obj_tag(v_x_1128_) == 0)
{
lean_dec(v_x_1127_);
return v_x_1128_;
}
else
{
switch(lean_obj_tag(v_x_1127_))
{
case 0:
{
return v_x_1128_;
}
case 1:
{
lean_object* v_a_1134_; 
v_a_1134_ = lean_ctor_get(v_x_1127_, 0);
if (lean_obj_tag(v_a_1134_) == 0)
{
lean_dec_ref_known(v_x_1127_, 1);
return v_x_1128_;
}
else
{
v_u_u2081_1130_ = v_x_1127_;
v_u_u2082_1131_ = v_x_1128_;
goto v___jp_1129_;
}
}
default: 
{
v_u_u2081_1130_ = v_x_1127_;
v_u_u2082_1131_ = v_x_1128_;
goto v___jp_1129_;
}
}
}
v___jp_1129_:
{
uint8_t v___x_1132_; 
v___x_1132_ = lean_level_eq(v_u_u2081_1130_, v_u_u2082_1131_);
if (v___x_1132_ == 0)
{
lean_object* v___x_1133_; 
v___x_1133_ = l_Lean_Level_imax___override(v_u_u2081_1130_, v_u_u2082_1131_);
return v___x_1133_;
}
else
{
lean_dec(v_u_u2082_1131_);
return v_u_u2081_1130_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_getMaxArgsAux(lean_object* v_normalize_1135_, lean_object* v_x_1136_, uint8_t v_x_1137_, lean_object* v_x_1138_){
_start:
{
if (lean_obj_tag(v_x_1136_) == 2)
{
lean_object* v_a_1139_; lean_object* v_a_1140_; lean_object* v___x_1141_; 
v_a_1139_ = lean_ctor_get(v_x_1136_, 0);
lean_inc(v_a_1139_);
v_a_1140_ = lean_ctor_get(v_x_1136_, 1);
lean_inc(v_a_1140_);
lean_dec_ref_known(v_x_1136_, 2);
lean_inc_ref(v_normalize_1135_);
v___x_1141_ = l___private_Lean_Level_0__Lean_Level_getMaxArgsAux(v_normalize_1135_, v_a_1139_, v_x_1137_, v_x_1138_);
v_x_1136_ = v_a_1140_;
v_x_1138_ = v___x_1141_;
goto _start;
}
else
{
if (v_x_1137_ == 0)
{
lean_object* v___x_1143_; uint8_t v___x_1144_; 
lean_inc_ref(v_normalize_1135_);
v___x_1143_ = lean_apply_1(v_normalize_1135_, v_x_1136_);
v___x_1144_ = 1;
v_x_1136_ = v___x_1143_;
v_x_1137_ = v___x_1144_;
goto _start;
}
else
{
lean_object* v___x_1146_; 
lean_dec_ref(v_normalize_1135_);
v___x_1146_ = lean_array_push(v_x_1138_, v_x_1136_);
return v___x_1146_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_getMaxArgsAux___boxed(lean_object* v_normalize_1147_, lean_object* v_x_1148_, lean_object* v_x_1149_, lean_object* v_x_1150_){
_start:
{
uint8_t v_x_31__boxed_1151_; lean_object* v_res_1152_; 
v_x_31__boxed_1151_ = lean_unbox(v_x_1149_);
v_res_1152_ = l___private_Lean_Level_0__Lean_Level_getMaxArgsAux(v_normalize_1147_, v_x_1148_, v_x_31__boxed_1151_, v_x_1150_);
return v_res_1152_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_accMax(lean_object* v_result_1153_, lean_object* v_prev_1154_, lean_object* v_offset_1155_){
_start:
{
uint8_t v___x_1156_; 
v___x_1156_ = l_Lean_Level_isZero(v_result_1153_);
if (v___x_1156_ == 0)
{
lean_object* v___x_1157_; lean_object* v___x_1158_; 
v___x_1157_ = l_Lean_Level_addOffsetAux(v_offset_1155_, v_prev_1154_);
v___x_1158_ = l_Lean_Level_max___override(v_result_1153_, v___x_1157_);
return v___x_1158_;
}
else
{
lean_object* v___x_1159_; 
lean_dec(v_result_1153_);
v___x_1159_ = l_Lean_Level_addOffsetAux(v_offset_1155_, v_prev_1154_);
return v___x_1159_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_mkMaxAux(lean_object* v_lvls_1160_, lean_object* v_extraK_1161_, lean_object* v_i_1162_, lean_object* v_prev_1163_, lean_object* v_prevK_1164_, lean_object* v_result_1165_){
_start:
{
lean_object* v___x_1166_; uint8_t v___x_1167_; 
v___x_1166_ = lean_array_get_size(v_lvls_1160_);
v___x_1167_ = lean_nat_dec_lt(v_i_1162_, v___x_1166_);
if (v___x_1167_ == 0)
{
lean_object* v___x_1168_; lean_object* v___x_1169_; 
lean_dec(v_i_1162_);
v___x_1168_ = lean_nat_add(v_extraK_1161_, v_prevK_1164_);
lean_dec(v_prevK_1164_);
v___x_1169_ = l___private_Lean_Level_0__Lean_Level_accMax(v_result_1165_, v_prev_1163_, v___x_1168_);
return v___x_1169_;
}
else
{
lean_object* v_lvl_1170_; lean_object* v_curr_1171_; lean_object* v_currK_1172_; uint8_t v___x_1173_; 
v_lvl_1170_ = lean_array_fget_borrowed(v_lvls_1160_, v_i_1162_);
v_curr_1171_ = l_Lean_Level_getLevelOffset(v_lvl_1170_);
v_currK_1172_ = l_Lean_Level_getOffset(v_lvl_1170_);
v___x_1173_ = lean_level_eq(v_curr_1171_, v_prev_1163_);
if (v___x_1173_ == 0)
{
lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; 
v___x_1174_ = lean_unsigned_to_nat(1u);
v___x_1175_ = lean_nat_add(v_i_1162_, v___x_1174_);
lean_dec(v_i_1162_);
v___x_1176_ = lean_nat_add(v_extraK_1161_, v_prevK_1164_);
lean_dec(v_prevK_1164_);
v___x_1177_ = l___private_Lean_Level_0__Lean_Level_accMax(v_result_1165_, v_prev_1163_, v___x_1176_);
v_i_1162_ = v___x_1175_;
v_prev_1163_ = v_curr_1171_;
v_prevK_1164_ = v_currK_1172_;
v_result_1165_ = v___x_1177_;
goto _start;
}
else
{
lean_object* v___x_1179_; lean_object* v___x_1180_; 
lean_dec(v_prevK_1164_);
lean_dec(v_prev_1163_);
v___x_1179_ = lean_unsigned_to_nat(1u);
v___x_1180_ = lean_nat_add(v_i_1162_, v___x_1179_);
lean_dec(v_i_1162_);
v_i_1162_ = v___x_1180_;
v_prev_1163_ = v_curr_1171_;
v_prevK_1164_ = v_currK_1172_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_mkMaxAux___boxed(lean_object* v_lvls_1182_, lean_object* v_extraK_1183_, lean_object* v_i_1184_, lean_object* v_prev_1185_, lean_object* v_prevK_1186_, lean_object* v_result_1187_){
_start:
{
lean_object* v_res_1188_; 
v_res_1188_ = l___private_Lean_Level_0__Lean_Level_mkMaxAux(v_lvls_1182_, v_extraK_1183_, v_i_1184_, v_prev_1185_, v_prevK_1186_, v_result_1187_);
lean_dec(v_extraK_1183_);
lean_dec_ref(v_lvls_1182_);
return v_res_1188_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_skipExplicit(lean_object* v_lvls_1189_, lean_object* v_i_1190_){
_start:
{
lean_object* v___x_1191_; uint8_t v___x_1192_; 
v___x_1191_ = lean_array_get_size(v_lvls_1189_);
v___x_1192_ = lean_nat_dec_lt(v_i_1190_, v___x_1191_);
if (v___x_1192_ == 0)
{
return v_i_1190_;
}
else
{
lean_object* v_lvl_1193_; lean_object* v___x_1194_; uint8_t v___x_1195_; 
v_lvl_1193_ = lean_array_fget_borrowed(v_lvls_1189_, v_i_1190_);
v___x_1194_ = l_Lean_Level_getLevelOffset(v_lvl_1193_);
v___x_1195_ = l_Lean_Level_isZero(v___x_1194_);
lean_dec(v___x_1194_);
if (v___x_1195_ == 0)
{
return v_i_1190_;
}
else
{
lean_object* v___x_1196_; lean_object* v___x_1197_; 
v___x_1196_ = lean_unsigned_to_nat(1u);
v___x_1197_ = lean_nat_add(v_i_1190_, v___x_1196_);
lean_dec(v_i_1190_);
v_i_1190_ = v___x_1197_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_skipExplicit___boxed(lean_object* v_lvls_1199_, lean_object* v_i_1200_){
_start:
{
lean_object* v_res_1201_; 
v_res_1201_ = l___private_Lean_Level_0__Lean_Level_skipExplicit(v_lvls_1199_, v_i_1200_);
lean_dec_ref(v_lvls_1199_);
return v_res_1201_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Level_0__Lean_Level_isExplicitSubsumedAux(lean_object* v_lvls_1202_, lean_object* v_maxExplicit_1203_, lean_object* v_i_1204_){
_start:
{
lean_object* v___x_1205_; uint8_t v___x_1206_; 
v___x_1205_ = lean_array_get_size(v_lvls_1202_);
v___x_1206_ = lean_nat_dec_lt(v_i_1204_, v___x_1205_);
if (v___x_1206_ == 0)
{
lean_dec(v_i_1204_);
return v___x_1206_;
}
else
{
lean_object* v_lvl_1207_; lean_object* v___x_1208_; uint8_t v___x_1209_; 
v_lvl_1207_ = lean_array_fget_borrowed(v_lvls_1202_, v_i_1204_);
v___x_1208_ = l_Lean_Level_getOffset(v_lvl_1207_);
v___x_1209_ = lean_nat_dec_le(v_maxExplicit_1203_, v___x_1208_);
lean_dec(v___x_1208_);
if (v___x_1209_ == 0)
{
lean_object* v___x_1210_; lean_object* v___x_1211_; 
v___x_1210_ = lean_unsigned_to_nat(1u);
v___x_1211_ = lean_nat_add(v_i_1204_, v___x_1210_);
lean_dec(v_i_1204_);
v_i_1204_ = v___x_1211_;
goto _start;
}
else
{
lean_dec(v_i_1204_);
return v___x_1209_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_isExplicitSubsumedAux___boxed(lean_object* v_lvls_1213_, lean_object* v_maxExplicit_1214_, lean_object* v_i_1215_){
_start:
{
uint8_t v_res_1216_; lean_object* v_r_1217_; 
v_res_1216_ = l___private_Lean_Level_0__Lean_Level_isExplicitSubsumedAux(v_lvls_1213_, v_maxExplicit_1214_, v_i_1215_);
lean_dec(v_maxExplicit_1214_);
lean_dec_ref(v_lvls_1213_);
v_r_1217_ = lean_box(v_res_1216_);
return v_r_1217_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Level_0__Lean_Level_isExplicitSubsumed(lean_object* v_lvls_1218_, lean_object* v_firstNonExplicit_1219_){
_start:
{
lean_object* v___x_1220_; uint8_t v___x_1221_; 
v___x_1220_ = lean_unsigned_to_nat(0u);
v___x_1221_ = lean_nat_dec_eq(v_firstNonExplicit_1219_, v___x_1220_);
if (v___x_1221_ == 0)
{
lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v_max_1226_; uint8_t v___x_1227_; 
v___x_1222_ = lean_box(0);
v___x_1223_ = lean_unsigned_to_nat(1u);
v___x_1224_ = lean_nat_sub(v_firstNonExplicit_1219_, v___x_1223_);
v___x_1225_ = lean_array_get_borrowed(v___x_1222_, v_lvls_1218_, v___x_1224_);
lean_dec(v___x_1224_);
v_max_1226_ = l_Lean_Level_getOffset(v___x_1225_);
v___x_1227_ = l___private_Lean_Level_0__Lean_Level_isExplicitSubsumedAux(v_lvls_1218_, v_max_1226_, v_firstNonExplicit_1219_);
lean_dec(v_max_1226_);
return v___x_1227_;
}
else
{
uint8_t v___x_1228_; 
lean_dec(v_firstNonExplicit_1219_);
v___x_1228_ = 0;
return v___x_1228_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_isExplicitSubsumed___boxed(lean_object* v_lvls_1229_, lean_object* v_firstNonExplicit_1230_){
_start:
{
uint8_t v_res_1231_; lean_object* v_r_1232_; 
v_res_1231_ = l___private_Lean_Level_0__Lean_Level_isExplicitSubsumed(v_lvls_1229_, v_firstNonExplicit_1230_);
lean_dec_ref(v_lvls_1229_);
v_r_1232_ = lean_box(v_res_1231_);
return v_r_1232_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Level_normalize_spec__2(lean_object* v_msg_1233_){
_start:
{
lean_object* v___x_1234_; lean_object* v___x_1235_; 
v___x_1234_ = lean_box(0);
v___x_1235_ = lean_panic_fn_borrowed(v___x_1234_, v_msg_1233_);
return v___x_1235_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1_spec__1___redArg(lean_object* v_hi_1236_, lean_object* v_pivot_1237_, lean_object* v_as_1238_, lean_object* v_i_1239_, lean_object* v_k_1240_){
_start:
{
uint8_t v___x_1241_; 
v___x_1241_ = lean_nat_dec_lt(v_k_1240_, v_hi_1236_);
if (v___x_1241_ == 0)
{
lean_object* v___x_1242_; lean_object* v___x_1243_; 
lean_dec(v_k_1240_);
v___x_1242_ = lean_array_fswap(v_as_1238_, v_i_1239_, v_hi_1236_);
v___x_1243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1243_, 0, v_i_1239_);
lean_ctor_set(v___x_1243_, 1, v___x_1242_);
return v___x_1243_;
}
else
{
lean_object* v___x_1244_; uint8_t v___x_1245_; 
v___x_1244_ = lean_array_fget_borrowed(v_as_1238_, v_k_1240_);
v___x_1245_ = l_Lean_Level_normLt(v___x_1244_, v_pivot_1237_);
if (v___x_1245_ == 0)
{
lean_object* v___x_1246_; lean_object* v___x_1247_; 
v___x_1246_ = lean_unsigned_to_nat(1u);
v___x_1247_ = lean_nat_add(v_k_1240_, v___x_1246_);
lean_dec(v_k_1240_);
v_k_1240_ = v___x_1247_;
goto _start;
}
else
{
lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; 
v___x_1249_ = lean_array_fswap(v_as_1238_, v_i_1239_, v_k_1240_);
v___x_1250_ = lean_unsigned_to_nat(1u);
v___x_1251_ = lean_nat_add(v_i_1239_, v___x_1250_);
lean_dec(v_i_1239_);
v___x_1252_ = lean_nat_add(v_k_1240_, v___x_1250_);
lean_dec(v_k_1240_);
v_as_1238_ = v___x_1249_;
v_i_1239_ = v___x_1251_;
v_k_1240_ = v___x_1252_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1_spec__1___redArg___boxed(lean_object* v_hi_1254_, lean_object* v_pivot_1255_, lean_object* v_as_1256_, lean_object* v_i_1257_, lean_object* v_k_1258_){
_start:
{
lean_object* v_res_1259_; 
v_res_1259_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1_spec__1___redArg(v_hi_1254_, v_pivot_1255_, v_as_1256_, v_i_1257_, v_k_1258_);
lean_dec(v_pivot_1255_);
lean_dec(v_hi_1254_);
return v_res_1259_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1___redArg(lean_object* v_n_1260_, lean_object* v_as_1261_, lean_object* v_lo_1262_, lean_object* v_hi_1263_){
_start:
{
lean_object* v___y_1265_; uint8_t v___x_1275_; 
v___x_1275_ = lean_nat_dec_lt(v_lo_1262_, v_hi_1263_);
if (v___x_1275_ == 0)
{
lean_dec(v_lo_1262_);
return v_as_1261_;
}
else
{
lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v_mid_1278_; lean_object* v___y_1280_; lean_object* v___y_1286_; lean_object* v___x_1291_; lean_object* v___x_1292_; uint8_t v___x_1293_; 
v___x_1276_ = lean_nat_add(v_lo_1262_, v_hi_1263_);
v___x_1277_ = lean_unsigned_to_nat(1u);
v_mid_1278_ = lean_nat_shiftr(v___x_1276_, v___x_1277_);
lean_dec(v___x_1276_);
v___x_1291_ = lean_array_fget_borrowed(v_as_1261_, v_mid_1278_);
v___x_1292_ = lean_array_fget_borrowed(v_as_1261_, v_lo_1262_);
v___x_1293_ = l_Lean_Level_normLt(v___x_1291_, v___x_1292_);
if (v___x_1293_ == 0)
{
v___y_1286_ = v_as_1261_;
goto v___jp_1285_;
}
else
{
lean_object* v___x_1294_; 
v___x_1294_ = lean_array_fswap(v_as_1261_, v_lo_1262_, v_mid_1278_);
v___y_1286_ = v___x_1294_;
goto v___jp_1285_;
}
v___jp_1279_:
{
lean_object* v___x_1281_; lean_object* v___x_1282_; uint8_t v___x_1283_; 
v___x_1281_ = lean_array_fget_borrowed(v___y_1280_, v_mid_1278_);
v___x_1282_ = lean_array_fget_borrowed(v___y_1280_, v_hi_1263_);
v___x_1283_ = l_Lean_Level_normLt(v___x_1281_, v___x_1282_);
if (v___x_1283_ == 0)
{
lean_dec(v_mid_1278_);
v___y_1265_ = v___y_1280_;
goto v___jp_1264_;
}
else
{
lean_object* v___x_1284_; 
v___x_1284_ = lean_array_fswap(v___y_1280_, v_mid_1278_, v_hi_1263_);
lean_dec(v_mid_1278_);
v___y_1265_ = v___x_1284_;
goto v___jp_1264_;
}
}
v___jp_1285_:
{
lean_object* v___x_1287_; lean_object* v___x_1288_; uint8_t v___x_1289_; 
v___x_1287_ = lean_array_fget_borrowed(v___y_1286_, v_hi_1263_);
v___x_1288_ = lean_array_fget_borrowed(v___y_1286_, v_lo_1262_);
v___x_1289_ = l_Lean_Level_normLt(v___x_1287_, v___x_1288_);
if (v___x_1289_ == 0)
{
v___y_1280_ = v___y_1286_;
goto v___jp_1279_;
}
else
{
lean_object* v___x_1290_; 
v___x_1290_ = lean_array_fswap(v___y_1286_, v_lo_1262_, v_hi_1263_);
v___y_1280_ = v___x_1290_;
goto v___jp_1279_;
}
}
}
v___jp_1264_:
{
lean_object* v_pivot_1266_; lean_object* v___x_1267_; lean_object* v_fst_1268_; lean_object* v_snd_1269_; uint8_t v___x_1270_; 
v_pivot_1266_ = lean_array_fget(v___y_1265_, v_hi_1263_);
lean_inc_n(v_lo_1262_, 2);
v___x_1267_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1_spec__1___redArg(v_hi_1263_, v_pivot_1266_, v___y_1265_, v_lo_1262_, v_lo_1262_);
lean_dec(v_pivot_1266_);
v_fst_1268_ = lean_ctor_get(v___x_1267_, 0);
lean_inc(v_fst_1268_);
v_snd_1269_ = lean_ctor_get(v___x_1267_, 1);
lean_inc(v_snd_1269_);
lean_dec_ref(v___x_1267_);
v___x_1270_ = lean_nat_dec_le(v_hi_1263_, v_fst_1268_);
if (v___x_1270_ == 0)
{
lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; 
v___x_1271_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1___redArg(v_n_1260_, v_snd_1269_, v_lo_1262_, v_fst_1268_);
v___x_1272_ = lean_unsigned_to_nat(1u);
v___x_1273_ = lean_nat_add(v_fst_1268_, v___x_1272_);
lean_dec(v_fst_1268_);
v_as_1261_ = v___x_1271_;
v_lo_1262_ = v___x_1273_;
goto _start;
}
else
{
lean_dec(v_fst_1268_);
lean_dec(v_lo_1262_);
return v_snd_1269_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1___redArg___boxed(lean_object* v_n_1295_, lean_object* v_as_1296_, lean_object* v_lo_1297_, lean_object* v_hi_1298_){
_start:
{
lean_object* v_res_1299_; 
v_res_1299_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1___redArg(v_n_1295_, v_as_1296_, v_lo_1297_, v_hi_1298_);
lean_dec(v_hi_1298_);
lean_dec(v_n_1295_);
return v_res_1299_;
}
}
static lean_object* _init_l_Lean_Level_normalize___closed__3(void){
_start:
{
lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; 
v___x_1304_ = ((lean_object*)(l_Lean_Level_normalize___closed__2));
v___x_1305_ = lean_unsigned_to_nat(11u);
v___x_1306_ = lean_unsigned_to_nat(404u);
v___x_1307_ = ((lean_object*)(l_Lean_Level_normalize___closed__1));
v___x_1308_ = ((lean_object*)(l_Lean_Level_mvarId_x21___closed__0));
v___x_1309_ = l_mkPanicMessageWithDecl(v___x_1308_, v___x_1307_, v___x_1306_, v___x_1305_, v___x_1304_);
return v___x_1309_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_normalize(lean_object* v_l_1310_){
_start:
{
uint8_t v___x_1311_; 
v___x_1311_ = l_Lean_Level_isAlreadyNormalizedCheap(v_l_1310_);
if (v___x_1311_ == 0)
{
lean_object* v_k_1312_; lean_object* v_u_1313_; 
v_k_1312_ = l_Lean_Level_getOffset(v_l_1310_);
v_u_1313_ = l_Lean_Level_getLevelOffset(v_l_1310_);
switch(lean_obj_tag(v_u_1313_))
{
case 2:
{
lean_object* v_a_1314_; lean_object* v_a_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v_lvls_1319_; lean_object* v_lvls_1320_; lean_object* v___x_1321_; lean_object* v___y_1323_; lean_object* v___y_1324_; lean_object* v___y_1331_; lean_object* v___x_1335_; lean_object* v___y_1337_; lean_object* v___y_1338_; uint8_t v___x_1340_; 
v_a_1314_ = lean_ctor_get(v_u_1313_, 0);
lean_inc(v_a_1314_);
v_a_1315_ = lean_ctor_get(v_u_1313_, 1);
lean_inc(v_a_1315_);
lean_dec_ref_known(v_u_1313_, 2);
v___x_1316_ = lean_box(0);
v___x_1317_ = lean_unsigned_to_nat(0u);
v___x_1318_ = ((lean_object*)(l_Lean_Level_normalize___closed__0));
v_lvls_1319_ = l___private_Lean_Level_0__Lean_Level_getMaxArgsAux___at___00Lean_Level_normalize_spec__0(v_a_1314_, v___x_1311_, v___x_1318_);
v_lvls_1320_ = l___private_Lean_Level_0__Lean_Level_getMaxArgsAux___at___00Lean_Level_normalize_spec__0(v_a_1315_, v___x_1311_, v_lvls_1319_);
v___x_1321_ = lean_unsigned_to_nat(1u);
v___x_1335_ = lean_array_get_size(v_lvls_1320_);
v___x_1340_ = lean_nat_dec_eq(v___x_1335_, v___x_1317_);
if (v___x_1340_ == 0)
{
lean_object* v___x_1341_; lean_object* v___y_1343_; uint8_t v___x_1345_; 
v___x_1341_ = lean_nat_sub(v___x_1335_, v___x_1321_);
v___x_1345_ = lean_nat_dec_le(v___x_1317_, v___x_1341_);
if (v___x_1345_ == 0)
{
lean_inc(v___x_1341_);
v___y_1343_ = v___x_1341_;
goto v___jp_1342_;
}
else
{
v___y_1343_ = v___x_1317_;
goto v___jp_1342_;
}
v___jp_1342_:
{
uint8_t v___x_1344_; 
v___x_1344_ = lean_nat_dec_le(v___y_1343_, v___x_1341_);
if (v___x_1344_ == 0)
{
lean_dec(v___x_1341_);
lean_inc(v___y_1343_);
v___y_1337_ = v___y_1343_;
v___y_1338_ = v___y_1343_;
goto v___jp_1336_;
}
else
{
v___y_1337_ = v___y_1343_;
v___y_1338_ = v___x_1341_;
goto v___jp_1336_;
}
}
}
else
{
v___y_1331_ = v_lvls_1320_;
goto v___jp_1330_;
}
v___jp_1322_:
{
lean_object* v_lvl_u2081_1325_; lean_object* v_prev_1326_; lean_object* v_prevK_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; 
v_lvl_u2081_1325_ = lean_array_get_borrowed(v___x_1316_, v___y_1323_, v___y_1324_);
v_prev_1326_ = l_Lean_Level_getLevelOffset(v_lvl_u2081_1325_);
v_prevK_1327_ = l_Lean_Level_getOffset(v_lvl_u2081_1325_);
v___x_1328_ = lean_nat_add(v___y_1324_, v___x_1321_);
lean_dec(v___y_1324_);
v___x_1329_ = l___private_Lean_Level_0__Lean_Level_mkMaxAux(v___y_1323_, v_k_1312_, v___x_1328_, v_prev_1326_, v_prevK_1327_, v___x_1316_);
lean_dec(v_k_1312_);
lean_dec_ref(v___y_1323_);
return v___x_1329_;
}
v___jp_1330_:
{
lean_object* v_firstNonExplicit_1332_; uint8_t v___x_1333_; 
v_firstNonExplicit_1332_ = l___private_Lean_Level_0__Lean_Level_skipExplicit(v___y_1331_, v___x_1317_);
lean_inc(v_firstNonExplicit_1332_);
v___x_1333_ = l___private_Lean_Level_0__Lean_Level_isExplicitSubsumed(v___y_1331_, v_firstNonExplicit_1332_);
if (v___x_1333_ == 0)
{
lean_object* v___x_1334_; 
v___x_1334_ = lean_nat_sub(v_firstNonExplicit_1332_, v___x_1321_);
lean_dec(v_firstNonExplicit_1332_);
v___y_1323_ = v___y_1331_;
v___y_1324_ = v___x_1334_;
goto v___jp_1322_;
}
else
{
v___y_1323_ = v___y_1331_;
v___y_1324_ = v_firstNonExplicit_1332_;
goto v___jp_1322_;
}
}
v___jp_1336_:
{
lean_object* v___x_1339_; 
v___x_1339_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1___redArg(v___x_1335_, v_lvls_1320_, v___y_1337_, v___y_1338_);
lean_dec(v___y_1338_);
v___y_1331_ = v___x_1339_;
goto v___jp_1330_;
}
}
case 3:
{
lean_object* v_a_1346_; lean_object* v_a_1347_; uint8_t v___x_1348_; 
v_a_1346_ = lean_ctor_get(v_u_1313_, 0);
lean_inc(v_a_1346_);
v_a_1347_ = lean_ctor_get(v_u_1313_, 1);
lean_inc(v_a_1347_);
lean_dec_ref_known(v_u_1313_, 2);
v___x_1348_ = l_Lean_Level_isNeverZero(v_a_1347_);
if (v___x_1348_ == 0)
{
lean_object* v_l_u2081_1349_; lean_object* v_l_u2082_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; 
v_l_u2081_1349_ = l_Lean_Level_normalize(v_a_1346_);
lean_dec(v_a_1346_);
v_l_u2082_1350_ = l_Lean_Level_normalize(v_a_1347_);
lean_dec(v_a_1347_);
v___x_1351_ = l___private_Lean_Level_0__Lean_Level_mkIMaxAux(v_l_u2081_1349_, v_l_u2082_1350_);
v___x_1352_ = l_Lean_Level_addOffsetAux(v_k_1312_, v___x_1351_);
return v___x_1352_;
}
else
{
lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; 
v___x_1353_ = l_Lean_Level_max___override(v_a_1346_, v_a_1347_);
v___x_1354_ = l_Lean_Level_normalize(v___x_1353_);
lean_dec(v___x_1353_);
v___x_1355_ = l_Lean_Level_addOffsetAux(v_k_1312_, v___x_1354_);
return v___x_1355_;
}
}
default: 
{
lean_object* v___x_1356_; lean_object* v___x_1357_; 
lean_dec(v_u_1313_);
lean_dec(v_k_1312_);
v___x_1356_ = lean_obj_once(&l_Lean_Level_normalize___closed__3, &l_Lean_Level_normalize___closed__3_once, _init_l_Lean_Level_normalize___closed__3);
v___x_1357_ = l_panic___at___00Lean_Level_normalize_spec__2(v___x_1356_);
return v___x_1357_;
}
}
}
else
{
lean_inc(v_l_1310_);
return v_l_1310_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_getMaxArgsAux___at___00Lean_Level_normalize_spec__0(lean_object* v_x_1358_, uint8_t v_x_1359_, lean_object* v_x_1360_){
_start:
{
if (lean_obj_tag(v_x_1358_) == 2)
{
lean_object* v_a_1361_; lean_object* v_a_1362_; lean_object* v___x_1363_; 
v_a_1361_ = lean_ctor_get(v_x_1358_, 0);
lean_inc(v_a_1361_);
v_a_1362_ = lean_ctor_get(v_x_1358_, 1);
lean_inc(v_a_1362_);
lean_dec_ref_known(v_x_1358_, 2);
v___x_1363_ = l___private_Lean_Level_0__Lean_Level_getMaxArgsAux___at___00Lean_Level_normalize_spec__0(v_a_1361_, v_x_1359_, v_x_1360_);
v_x_1358_ = v_a_1362_;
v_x_1360_ = v___x_1363_;
goto _start;
}
else
{
if (v_x_1359_ == 0)
{
lean_object* v___x_1365_; uint8_t v___x_1366_; 
v___x_1365_ = l_Lean_Level_normalize(v_x_1358_);
lean_dec(v_x_1358_);
v___x_1366_ = 1;
v_x_1358_ = v___x_1365_;
v_x_1359_ = v___x_1366_;
goto _start;
}
else
{
lean_object* v___x_1368_; 
v___x_1368_ = lean_array_push(v_x_1360_, v_x_1358_);
return v___x_1368_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_getMaxArgsAux___at___00Lean_Level_normalize_spec__0___boxed(lean_object* v_x_1369_, lean_object* v_x_1370_, lean_object* v_x_1371_){
_start:
{
uint8_t v_x_483__boxed_1372_; lean_object* v_res_1373_; 
v_x_483__boxed_1372_ = lean_unbox(v_x_1370_);
v_res_1373_ = l___private_Lean_Level_0__Lean_Level_getMaxArgsAux___at___00Lean_Level_normalize_spec__0(v_x_1369_, v_x_483__boxed_1372_, v_x_1371_);
return v_res_1373_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_normalize___boxed(lean_object* v_l_1374_){
_start:
{
lean_object* v_res_1375_; 
v_res_1375_ = l_Lean_Level_normalize(v_l_1374_);
lean_dec(v_l_1374_);
return v_res_1375_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1(lean_object* v_n_1376_, lean_object* v_as_1377_, lean_object* v_lo_1378_, lean_object* v_hi_1379_, lean_object* v_w_1380_, lean_object* v_hlo_1381_, lean_object* v_hhi_1382_){
_start:
{
lean_object* v___x_1383_; 
v___x_1383_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1___redArg(v_n_1376_, v_as_1377_, v_lo_1378_, v_hi_1379_);
return v___x_1383_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1___boxed(lean_object* v_n_1384_, lean_object* v_as_1385_, lean_object* v_lo_1386_, lean_object* v_hi_1387_, lean_object* v_w_1388_, lean_object* v_hlo_1389_, lean_object* v_hhi_1390_){
_start:
{
lean_object* v_res_1391_; 
v_res_1391_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1(v_n_1384_, v_as_1385_, v_lo_1386_, v_hi_1387_, v_w_1388_, v_hlo_1389_, v_hhi_1390_);
lean_dec(v_hi_1387_);
lean_dec(v_n_1384_);
return v_res_1391_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1_spec__1(lean_object* v_n_1392_, lean_object* v_lo_1393_, lean_object* v_hi_1394_, lean_object* v_hhi_1395_, lean_object* v_pivot_1396_, lean_object* v_as_1397_, lean_object* v_i_1398_, lean_object* v_k_1399_, lean_object* v_ilo_1400_, lean_object* v_ik_1401_, lean_object* v_w_1402_){
_start:
{
lean_object* v___x_1403_; 
v___x_1403_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1_spec__1___redArg(v_hi_1394_, v_pivot_1396_, v_as_1397_, v_i_1398_, v_k_1399_);
return v___x_1403_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1_spec__1___boxed(lean_object* v_n_1404_, lean_object* v_lo_1405_, lean_object* v_hi_1406_, lean_object* v_hhi_1407_, lean_object* v_pivot_1408_, lean_object* v_as_1409_, lean_object* v_i_1410_, lean_object* v_k_1411_, lean_object* v_ilo_1412_, lean_object* v_ik_1413_, lean_object* v_w_1414_){
_start:
{
lean_object* v_res_1415_; 
v_res_1415_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1_spec__1(v_n_1404_, v_lo_1405_, v_hi_1406_, v_hhi_1407_, v_pivot_1408_, v_as_1409_, v_i_1410_, v_k_1411_, v_ilo_1412_, v_ik_1413_, v_w_1414_);
lean_dec(v_pivot_1408_);
lean_dec(v_hi_1406_);
lean_dec(v_lo_1405_);
lean_dec(v_n_1404_);
return v_res_1415_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_isEquiv(lean_object* v_u_1416_, lean_object* v_v_1417_){
_start:
{
uint8_t v___x_1418_; 
v___x_1418_ = lean_level_eq(v_u_1416_, v_v_1417_);
if (v___x_1418_ == 0)
{
lean_object* v___x_1419_; lean_object* v___x_1420_; uint8_t v___x_1421_; 
v___x_1419_ = l_Lean_Level_normalize(v_u_1416_);
v___x_1420_ = l_Lean_Level_normalize(v_v_1417_);
v___x_1421_ = lean_level_eq(v___x_1419_, v___x_1420_);
lean_dec(v___x_1420_);
lean_dec(v___x_1419_);
return v___x_1421_;
}
else
{
return v___x_1418_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_isEquiv___boxed(lean_object* v_u_1422_, lean_object* v_v_1423_){
_start:
{
uint8_t v_res_1424_; lean_object* v_r_1425_; 
v_res_1424_ = l_Lean_Level_isEquiv(v_u_1422_, v_v_1423_);
lean_dec(v_v_1423_);
lean_dec(v_u_1422_);
v_r_1425_ = lean_box(v_res_1424_);
return v_r_1425_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_dec(lean_object* v_x_1426_){
_start:
{
lean_object* v_l_u2081_1428_; lean_object* v_l_u2082_1429_; 
switch(lean_obj_tag(v_x_1426_))
{
case 0:
{
lean_object* v___x_1442_; 
v___x_1442_ = lean_box(0);
return v___x_1442_;
}
case 1:
{
lean_object* v_a_1443_; lean_object* v___x_1444_; 
v_a_1443_ = lean_ctor_get(v_x_1426_, 0);
lean_inc(v_a_1443_);
v___x_1444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1444_, 0, v_a_1443_);
return v___x_1444_;
}
case 2:
{
lean_object* v_a_1445_; lean_object* v_a_1446_; 
v_a_1445_ = lean_ctor_get(v_x_1426_, 0);
v_a_1446_ = lean_ctor_get(v_x_1426_, 1);
v_l_u2081_1428_ = v_a_1445_;
v_l_u2082_1429_ = v_a_1446_;
goto v___jp_1427_;
}
case 3:
{
lean_object* v_a_1447_; lean_object* v_a_1448_; 
v_a_1447_ = lean_ctor_get(v_x_1426_, 0);
v_a_1448_ = lean_ctor_get(v_x_1426_, 1);
v_l_u2081_1428_ = v_a_1447_;
v_l_u2082_1429_ = v_a_1448_;
goto v___jp_1427_;
}
default: 
{
lean_object* v___x_1449_; 
v___x_1449_ = lean_box(0);
return v___x_1449_;
}
}
v___jp_1427_:
{
lean_object* v___x_1430_; 
v___x_1430_ = l_Lean_Level_dec(v_l_u2081_1428_);
if (lean_obj_tag(v___x_1430_) == 0)
{
return v___x_1430_;
}
else
{
lean_object* v_val_1431_; lean_object* v___x_1432_; 
v_val_1431_ = lean_ctor_get(v___x_1430_, 0);
lean_inc(v_val_1431_);
lean_dec_ref_known(v___x_1430_, 1);
v___x_1432_ = l_Lean_Level_dec(v_l_u2082_1429_);
if (lean_obj_tag(v___x_1432_) == 0)
{
lean_dec(v_val_1431_);
return v___x_1432_;
}
else
{
lean_object* v_val_1433_; lean_object* v___x_1435_; uint8_t v_isShared_1436_; uint8_t v_isSharedCheck_1441_; 
v_val_1433_ = lean_ctor_get(v___x_1432_, 0);
v_isSharedCheck_1441_ = !lean_is_exclusive(v___x_1432_);
if (v_isSharedCheck_1441_ == 0)
{
v___x_1435_ = v___x_1432_;
v_isShared_1436_ = v_isSharedCheck_1441_;
goto v_resetjp_1434_;
}
else
{
lean_inc(v_val_1433_);
lean_dec(v___x_1432_);
v___x_1435_ = lean_box(0);
v_isShared_1436_ = v_isSharedCheck_1441_;
goto v_resetjp_1434_;
}
v_resetjp_1434_:
{
lean_object* v___x_1437_; lean_object* v___x_1439_; 
v___x_1437_ = l_Lean_Level_max___override(v_val_1431_, v_val_1433_);
if (v_isShared_1436_ == 0)
{
lean_ctor_set(v___x_1435_, 0, v___x_1437_);
v___x_1439_ = v___x_1435_;
goto v_reusejp_1438_;
}
else
{
lean_object* v_reuseFailAlloc_1440_; 
v_reuseFailAlloc_1440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1440_, 0, v___x_1437_);
v___x_1439_ = v_reuseFailAlloc_1440_;
goto v_reusejp_1438_;
}
v_reusejp_1438_:
{
return v___x_1439_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_dec___boxed(lean_object* v_x_1450_){
_start:
{
lean_object* v_res_1451_; 
v_res_1451_ = l_Lean_Level_dec(v_x_1450_);
lean_dec(v_x_1450_);
return v_res_1451_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_ctorIdx(lean_object* v_x_1452_){
_start:
{
switch(lean_obj_tag(v_x_1452_))
{
case 0:
{
lean_object* v___x_1453_; 
v___x_1453_ = lean_unsigned_to_nat(0u);
return v___x_1453_;
}
case 1:
{
lean_object* v___x_1454_; 
v___x_1454_ = lean_unsigned_to_nat(1u);
return v___x_1454_;
}
case 2:
{
lean_object* v___x_1455_; 
v___x_1455_ = lean_unsigned_to_nat(2u);
return v___x_1455_;
}
case 3:
{
lean_object* v___x_1456_; 
v___x_1456_ = lean_unsigned_to_nat(3u);
return v___x_1456_;
}
default: 
{
lean_object* v___x_1457_; 
v___x_1457_ = lean_unsigned_to_nat(4u);
return v___x_1457_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_ctorIdx___boxed(lean_object* v_x_1458_){
_start:
{
lean_object* v_res_1459_; 
v_res_1459_ = l_Lean_Level_PP_Result_ctorIdx(v_x_1458_);
lean_dec_ref(v_x_1458_);
return v_res_1459_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_ctorElim___redArg(lean_object* v_t_1460_, lean_object* v_k_1461_){
_start:
{
if (lean_obj_tag(v_t_1460_) == 2)
{
lean_object* v_a_1462_; lean_object* v_a_1463_; lean_object* v___x_1464_; 
v_a_1462_ = lean_ctor_get(v_t_1460_, 0);
lean_inc_ref(v_a_1462_);
v_a_1463_ = lean_ctor_get(v_t_1460_, 1);
lean_inc(v_a_1463_);
lean_dec_ref_known(v_t_1460_, 2);
v___x_1464_ = lean_apply_2(v_k_1461_, v_a_1462_, v_a_1463_);
return v___x_1464_;
}
else
{
lean_object* v_a_1465_; lean_object* v___x_1466_; 
v_a_1465_ = lean_ctor_get(v_t_1460_, 0);
lean_inc(v_a_1465_);
lean_dec_ref(v_t_1460_);
v___x_1466_ = lean_apply_1(v_k_1461_, v_a_1465_);
return v___x_1466_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_ctorElim(lean_object* v_motive__1_1467_, lean_object* v_ctorIdx_1468_, lean_object* v_t_1469_, lean_object* v_h_1470_, lean_object* v_k_1471_){
_start:
{
lean_object* v___x_1472_; 
v___x_1472_ = l_Lean_Level_PP_Result_ctorElim___redArg(v_t_1469_, v_k_1471_);
return v___x_1472_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_ctorElim___boxed(lean_object* v_motive__1_1473_, lean_object* v_ctorIdx_1474_, lean_object* v_t_1475_, lean_object* v_h_1476_, lean_object* v_k_1477_){
_start:
{
lean_object* v_res_1478_; 
v_res_1478_ = l_Lean_Level_PP_Result_ctorElim(v_motive__1_1473_, v_ctorIdx_1474_, v_t_1475_, v_h_1476_, v_k_1477_);
lean_dec(v_ctorIdx_1474_);
return v_res_1478_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_leaf_elim___redArg(lean_object* v_t_1479_, lean_object* v_leaf_1480_){
_start:
{
lean_object* v___x_1481_; 
v___x_1481_ = l_Lean_Level_PP_Result_ctorElim___redArg(v_t_1479_, v_leaf_1480_);
return v___x_1481_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_leaf_elim(lean_object* v_motive__1_1482_, lean_object* v_t_1483_, lean_object* v_h_1484_, lean_object* v_leaf_1485_){
_start:
{
lean_object* v___x_1486_; 
v___x_1486_ = l_Lean_Level_PP_Result_ctorElim___redArg(v_t_1483_, v_leaf_1485_);
return v___x_1486_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_num_elim___redArg(lean_object* v_t_1487_, lean_object* v_num_1488_){
_start:
{
lean_object* v___x_1489_; 
v___x_1489_ = l_Lean_Level_PP_Result_ctorElim___redArg(v_t_1487_, v_num_1488_);
return v___x_1489_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_num_elim(lean_object* v_motive__1_1490_, lean_object* v_t_1491_, lean_object* v_h_1492_, lean_object* v_num_1493_){
_start:
{
lean_object* v___x_1494_; 
v___x_1494_ = l_Lean_Level_PP_Result_ctorElim___redArg(v_t_1491_, v_num_1493_);
return v___x_1494_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_offset_elim___redArg(lean_object* v_t_1495_, lean_object* v_offset_1496_){
_start:
{
lean_object* v___x_1497_; 
v___x_1497_ = l_Lean_Level_PP_Result_ctorElim___redArg(v_t_1495_, v_offset_1496_);
return v___x_1497_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_offset_elim(lean_object* v_motive__1_1498_, lean_object* v_t_1499_, lean_object* v_h_1500_, lean_object* v_offset_1501_){
_start:
{
lean_object* v___x_1502_; 
v___x_1502_ = l_Lean_Level_PP_Result_ctorElim___redArg(v_t_1499_, v_offset_1501_);
return v___x_1502_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_maxNode_elim___redArg(lean_object* v_t_1503_, lean_object* v_maxNode_1504_){
_start:
{
lean_object* v___x_1505_; 
v___x_1505_ = l_Lean_Level_PP_Result_ctorElim___redArg(v_t_1503_, v_maxNode_1504_);
return v___x_1505_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_maxNode_elim(lean_object* v_motive__1_1506_, lean_object* v_t_1507_, lean_object* v_h_1508_, lean_object* v_maxNode_1509_){
_start:
{
lean_object* v___x_1510_; 
v___x_1510_ = l_Lean_Level_PP_Result_ctorElim___redArg(v_t_1507_, v_maxNode_1509_);
return v___x_1510_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_imaxNode_elim___redArg(lean_object* v_t_1511_, lean_object* v_imaxNode_1512_){
_start:
{
lean_object* v___x_1513_; 
v___x_1513_ = l_Lean_Level_PP_Result_ctorElim___redArg(v_t_1511_, v_imaxNode_1512_);
return v___x_1513_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_imaxNode_elim(lean_object* v_motive__1_1514_, lean_object* v_t_1515_, lean_object* v_h_1516_, lean_object* v_imaxNode_1517_){
_start:
{
lean_object* v___x_1518_; 
v___x_1518_ = l_Lean_Level_PP_Result_ctorElim___redArg(v_t_1515_, v_imaxNode_1517_);
return v___x_1518_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_succ(lean_object* v_x_1519_){
_start:
{
switch(lean_obj_tag(v_x_1519_))
{
case 2:
{
lean_object* v_a_1520_; lean_object* v_a_1521_; lean_object* v___x_1523_; uint8_t v_isShared_1524_; uint8_t v_isSharedCheck_1530_; 
v_a_1520_ = lean_ctor_get(v_x_1519_, 0);
v_a_1521_ = lean_ctor_get(v_x_1519_, 1);
v_isSharedCheck_1530_ = !lean_is_exclusive(v_x_1519_);
if (v_isSharedCheck_1530_ == 0)
{
v___x_1523_ = v_x_1519_;
v_isShared_1524_ = v_isSharedCheck_1530_;
goto v_resetjp_1522_;
}
else
{
lean_inc(v_a_1521_);
lean_inc(v_a_1520_);
lean_dec(v_x_1519_);
v___x_1523_ = lean_box(0);
v_isShared_1524_ = v_isSharedCheck_1530_;
goto v_resetjp_1522_;
}
v_resetjp_1522_:
{
lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1528_; 
v___x_1525_ = lean_unsigned_to_nat(1u);
v___x_1526_ = lean_nat_add(v_a_1521_, v___x_1525_);
lean_dec(v_a_1521_);
if (v_isShared_1524_ == 0)
{
lean_ctor_set(v___x_1523_, 1, v___x_1526_);
v___x_1528_ = v___x_1523_;
goto v_reusejp_1527_;
}
else
{
lean_object* v_reuseFailAlloc_1529_; 
v_reuseFailAlloc_1529_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1529_, 0, v_a_1520_);
lean_ctor_set(v_reuseFailAlloc_1529_, 1, v___x_1526_);
v___x_1528_ = v_reuseFailAlloc_1529_;
goto v_reusejp_1527_;
}
v_reusejp_1527_:
{
return v___x_1528_;
}
}
}
case 1:
{
lean_object* v_a_1531_; lean_object* v___x_1533_; uint8_t v_isShared_1534_; uint8_t v_isSharedCheck_1540_; 
v_a_1531_ = lean_ctor_get(v_x_1519_, 0);
v_isSharedCheck_1540_ = !lean_is_exclusive(v_x_1519_);
if (v_isSharedCheck_1540_ == 0)
{
v___x_1533_ = v_x_1519_;
v_isShared_1534_ = v_isSharedCheck_1540_;
goto v_resetjp_1532_;
}
else
{
lean_inc(v_a_1531_);
lean_dec(v_x_1519_);
v___x_1533_ = lean_box(0);
v_isShared_1534_ = v_isSharedCheck_1540_;
goto v_resetjp_1532_;
}
v_resetjp_1532_:
{
lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1538_; 
v___x_1535_ = lean_unsigned_to_nat(1u);
v___x_1536_ = lean_nat_add(v_a_1531_, v___x_1535_);
lean_dec(v_a_1531_);
if (v_isShared_1534_ == 0)
{
lean_ctor_set(v___x_1533_, 0, v___x_1536_);
v___x_1538_ = v___x_1533_;
goto v_reusejp_1537_;
}
else
{
lean_object* v_reuseFailAlloc_1539_; 
v_reuseFailAlloc_1539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1539_, 0, v___x_1536_);
v___x_1538_ = v_reuseFailAlloc_1539_;
goto v_reusejp_1537_;
}
v_reusejp_1537_:
{
return v___x_1538_;
}
}
}
default: 
{
lean_object* v___x_1541_; lean_object* v___x_1542_; 
v___x_1541_ = lean_unsigned_to_nat(1u);
v___x_1542_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1542_, 0, v_x_1519_);
lean_ctor_set(v___x_1542_, 1, v___x_1541_);
return v___x_1542_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_max(lean_object* v_x_1543_, lean_object* v_x_1544_){
_start:
{
if (lean_obj_tag(v_x_1544_) == 3)
{
lean_object* v_a_1545_; lean_object* v___x_1547_; uint8_t v_isShared_1548_; uint8_t v_isSharedCheck_1553_; 
v_a_1545_ = lean_ctor_get(v_x_1544_, 0);
v_isSharedCheck_1553_ = !lean_is_exclusive(v_x_1544_);
if (v_isSharedCheck_1553_ == 0)
{
v___x_1547_ = v_x_1544_;
v_isShared_1548_ = v_isSharedCheck_1553_;
goto v_resetjp_1546_;
}
else
{
lean_inc(v_a_1545_);
lean_dec(v_x_1544_);
v___x_1547_ = lean_box(0);
v_isShared_1548_ = v_isSharedCheck_1553_;
goto v_resetjp_1546_;
}
v_resetjp_1546_:
{
lean_object* v___x_1549_; lean_object* v___x_1551_; 
v___x_1549_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1549_, 0, v_x_1543_);
lean_ctor_set(v___x_1549_, 1, v_a_1545_);
if (v_isShared_1548_ == 0)
{
lean_ctor_set(v___x_1547_, 0, v___x_1549_);
v___x_1551_ = v___x_1547_;
goto v_reusejp_1550_;
}
else
{
lean_object* v_reuseFailAlloc_1552_; 
v_reuseFailAlloc_1552_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1552_, 0, v___x_1549_);
v___x_1551_ = v_reuseFailAlloc_1552_;
goto v_reusejp_1550_;
}
v_reusejp_1550_:
{
return v___x_1551_;
}
}
}
else
{
lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; 
v___x_1554_ = lean_box(0);
v___x_1555_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1555_, 0, v_x_1544_);
lean_ctor_set(v___x_1555_, 1, v___x_1554_);
v___x_1556_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1556_, 0, v_x_1543_);
lean_ctor_set(v___x_1556_, 1, v___x_1555_);
v___x_1557_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1557_, 0, v___x_1556_);
return v___x_1557_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_imax(lean_object* v_x_1558_, lean_object* v_x_1559_){
_start:
{
if (lean_obj_tag(v_x_1559_) == 4)
{
lean_object* v_a_1560_; lean_object* v___x_1562_; uint8_t v_isShared_1563_; uint8_t v_isSharedCheck_1568_; 
v_a_1560_ = lean_ctor_get(v_x_1559_, 0);
v_isSharedCheck_1568_ = !lean_is_exclusive(v_x_1559_);
if (v_isSharedCheck_1568_ == 0)
{
v___x_1562_ = v_x_1559_;
v_isShared_1563_ = v_isSharedCheck_1568_;
goto v_resetjp_1561_;
}
else
{
lean_inc(v_a_1560_);
lean_dec(v_x_1559_);
v___x_1562_ = lean_box(0);
v_isShared_1563_ = v_isSharedCheck_1568_;
goto v_resetjp_1561_;
}
v_resetjp_1561_:
{
lean_object* v___x_1564_; lean_object* v___x_1566_; 
v___x_1564_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1564_, 0, v_x_1558_);
lean_ctor_set(v___x_1564_, 1, v_a_1560_);
if (v_isShared_1563_ == 0)
{
lean_ctor_set(v___x_1562_, 0, v___x_1564_);
v___x_1566_ = v___x_1562_;
goto v_reusejp_1565_;
}
else
{
lean_object* v_reuseFailAlloc_1567_; 
v_reuseFailAlloc_1567_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1567_, 0, v___x_1564_);
v___x_1566_ = v_reuseFailAlloc_1567_;
goto v_reusejp_1565_;
}
v_reusejp_1565_:
{
return v___x_1566_;
}
}
}
else
{
lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; 
v___x_1569_ = lean_box(0);
v___x_1570_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1570_, 0, v_x_1559_);
lean_ctor_set(v___x_1570_, 1, v___x_1569_);
v___x_1571_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1571_, 0, v_x_1558_);
lean_ctor_set(v___x_1571_, 1, v___x_1570_);
v___x_1572_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1572_, 0, v___x_1571_);
return v___x_1572_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_toResult(lean_object* v_l_1591_, lean_object* v_a_1592_){
_start:
{
switch(lean_obj_tag(v_l_1591_))
{
case 0:
{
lean_object* v___x_1593_; 
v___x_1593_ = ((lean_object*)(l_Lean_Level_PP_toResult___closed__0));
return v___x_1593_;
}
case 1:
{
lean_object* v_a_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; 
v_a_1594_ = lean_ctor_get(v_l_1591_, 0);
lean_inc(v_a_1594_);
lean_dec_ref_known(v_l_1591_, 1);
v___x_1595_ = l_Lean_Level_PP_toResult(v_a_1594_, v_a_1592_);
v___x_1596_ = l_Lean_Level_PP_Result_succ(v___x_1595_);
return v___x_1596_;
}
case 2:
{
lean_object* v_a_1597_; lean_object* v_a_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; 
v_a_1597_ = lean_ctor_get(v_l_1591_, 0);
lean_inc(v_a_1597_);
v_a_1598_ = lean_ctor_get(v_l_1591_, 1);
lean_inc(v_a_1598_);
lean_dec_ref_known(v_l_1591_, 2);
v___x_1599_ = l_Lean_Level_PP_toResult(v_a_1597_, v_a_1592_);
v___x_1600_ = l_Lean_Level_PP_toResult(v_a_1598_, v_a_1592_);
v___x_1601_ = l_Lean_Level_PP_Result_max(v___x_1599_, v___x_1600_);
return v___x_1601_;
}
case 3:
{
lean_object* v_a_1602_; lean_object* v_a_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; 
v_a_1602_ = lean_ctor_get(v_l_1591_, 0);
lean_inc(v_a_1602_);
v_a_1603_ = lean_ctor_get(v_l_1591_, 1);
lean_inc(v_a_1603_);
lean_dec_ref_known(v_l_1591_, 2);
v___x_1604_ = l_Lean_Level_PP_toResult(v_a_1602_, v_a_1592_);
v___x_1605_ = l_Lean_Level_PP_toResult(v_a_1603_, v_a_1592_);
v___x_1606_ = l_Lean_Level_PP_Result_imax(v___x_1604_, v___x_1605_);
return v___x_1606_;
}
case 4:
{
lean_object* v_a_1607_; lean_object* v___x_1608_; 
v_a_1607_ = lean_ctor_get(v_l_1591_, 0);
lean_inc(v_a_1607_);
lean_dec_ref_known(v_l_1591_, 1);
v___x_1608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1608_, 0, v_a_1607_);
return v___x_1608_;
}
default: 
{
uint8_t v_mvars_1609_; 
v_mvars_1609_ = lean_ctor_get_uint8(v_a_1592_, sizeof(void*)*1);
if (v_mvars_1609_ == 0)
{
lean_object* v___x_1610_; 
lean_dec_ref_known(v_l_1591_, 1);
v___x_1610_ = ((lean_object*)(l_Lean_Level_PP_toResult___closed__3));
return v___x_1610_;
}
else
{
lean_object* v_a_1611_; lean_object* v_lIndex_x3f_1612_; lean_object* v___x_1613_; 
v_a_1611_ = lean_ctor_get(v_l_1591_, 0);
lean_inc_n(v_a_1611_, 2);
lean_dec_ref_known(v_l_1591_, 1);
v_lIndex_x3f_1612_ = lean_ctor_get(v_a_1592_, 0);
lean_inc_ref(v_lIndex_x3f_1612_);
v___x_1613_ = lean_apply_1(v_lIndex_x3f_1612_, v_a_1611_);
if (lean_obj_tag(v___x_1613_) == 1)
{
lean_object* v_val_1614_; lean_object* v___x_1616_; uint8_t v_isShared_1617_; uint8_t v_isSharedCheck_1625_; 
lean_dec(v_a_1611_);
v_val_1614_ = lean_ctor_get(v___x_1613_, 0);
v_isSharedCheck_1625_ = !lean_is_exclusive(v___x_1613_);
if (v_isSharedCheck_1625_ == 0)
{
v___x_1616_ = v___x_1613_;
v_isShared_1617_ = v_isSharedCheck_1625_;
goto v_resetjp_1615_;
}
else
{
lean_inc(v_val_1614_);
lean_dec(v___x_1613_);
v___x_1616_ = lean_box(0);
v_isShared_1617_ = v_isSharedCheck_1625_;
goto v_resetjp_1615_;
}
v_resetjp_1615_:
{
lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1623_; 
v___x_1618_ = ((lean_object*)(l_Lean_Level_PP_toResult___closed__5));
v___x_1619_ = lean_unsigned_to_nat(1u);
v___x_1620_ = lean_nat_add(v_val_1614_, v___x_1619_);
lean_dec(v_val_1614_);
v___x_1621_ = l_Lean_Name_num___override(v___x_1618_, v___x_1620_);
if (v_isShared_1617_ == 0)
{
lean_ctor_set_tag(v___x_1616_, 0);
lean_ctor_set(v___x_1616_, 0, v___x_1621_);
v___x_1623_ = v___x_1616_;
goto v_reusejp_1622_;
}
else
{
lean_object* v_reuseFailAlloc_1624_; 
v_reuseFailAlloc_1624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1624_, 0, v___x_1621_);
v___x_1623_ = v_reuseFailAlloc_1624_;
goto v_reusejp_1622_;
}
v_reusejp_1622_:
{
return v___x_1623_;
}
}
}
else
{
lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; 
lean_dec(v___x_1613_);
v___x_1626_ = ((lean_object*)(l_Lean_Level_PP_toResult___closed__7));
v___x_1627_ = ((lean_object*)(l_Lean_Level_PP_toResult___closed__9));
v___x_1628_ = l_Lean_Name_replacePrefix(v_a_1611_, v___x_1626_, v___x_1627_);
v___x_1629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1629_, 0, v___x_1628_);
return v___x_1629_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_toResult___boxed(lean_object* v_l_1630_, lean_object* v_a_1631_){
_start:
{
lean_object* v_res_1632_; 
v_res_1632_ = l_Lean_Level_PP_toResult(v_l_1630_, v_a_1631_);
lean_dec_ref(v_a_1631_);
return v_res_1632_;
}
}
static lean_object* _init_l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__1(void){
_start:
{
lean_object* v___x_1634_; lean_object* v___x_1635_; 
v___x_1634_ = ((lean_object*)(l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__0));
v___x_1635_ = lean_string_length(v___x_1634_);
return v___x_1635_;
}
}
static lean_object* _init_l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__2(void){
_start:
{
lean_object* v___x_1636_; lean_object* v___x_1637_; 
v___x_1636_ = lean_obj_once(&l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__1, &l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__1_once, _init_l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__1);
v___x_1637_ = lean_nat_to_int(v___x_1636_);
return v___x_1637_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse(lean_object* v_x_1642_, uint8_t v_x_1643_){
_start:
{
if (v_x_1643_ == 0)
{
lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; uint8_t v___x_1650_; lean_object* v___x_1651_; 
v___x_1644_ = lean_obj_once(&l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__2, &l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__2_once, _init_l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__2);
v___x_1645_ = ((lean_object*)(l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__3));
v___x_1646_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1646_, 0, v___x_1645_);
lean_ctor_set(v___x_1646_, 1, v_x_1642_);
v___x_1647_ = ((lean_object*)(l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__4));
v___x_1648_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1648_, 0, v___x_1646_);
lean_ctor_set(v___x_1648_, 1, v___x_1647_);
v___x_1649_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1649_, 0, v___x_1644_);
lean_ctor_set(v___x_1649_, 1, v___x_1648_);
v___x_1650_ = 0;
v___x_1651_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1651_, 0, v___x_1649_);
lean_ctor_set_uint8(v___x_1651_, sizeof(void*)*1, v___x_1650_);
return v___x_1651_;
}
else
{
return v_x_1642_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___boxed(lean_object* v_x_1652_, lean_object* v_x_1653_){
_start:
{
uint8_t v_x_57__boxed_1654_; lean_object* v_res_1655_; 
v_x_57__boxed_1654_ = lean_unbox(v_x_1653_);
v_res_1655_ = l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse(v_x_1652_, v_x_57__boxed_1654_);
return v_res_1655_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_format(lean_object* v_x_1665_, uint8_t v_x_1666_){
_start:
{
switch(lean_obj_tag(v_x_1665_))
{
case 0:
{
lean_object* v_a_1667_; lean_object* v___x_1669_; uint8_t v_isShared_1670_; uint8_t v_isSharedCheck_1676_; 
v_a_1667_ = lean_ctor_get(v_x_1665_, 0);
v_isSharedCheck_1676_ = !lean_is_exclusive(v_x_1665_);
if (v_isSharedCheck_1676_ == 0)
{
v___x_1669_ = v_x_1665_;
v_isShared_1670_ = v_isSharedCheck_1676_;
goto v_resetjp_1668_;
}
else
{
lean_inc(v_a_1667_);
lean_dec(v_x_1665_);
v___x_1669_ = lean_box(0);
v_isShared_1670_ = v_isSharedCheck_1676_;
goto v_resetjp_1668_;
}
v_resetjp_1668_:
{
uint8_t v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1674_; 
v___x_1671_ = 1;
v___x_1672_ = l_Lean_Name_toString(v_a_1667_, v___x_1671_);
if (v_isShared_1670_ == 0)
{
lean_ctor_set_tag(v___x_1669_, 3);
lean_ctor_set(v___x_1669_, 0, v___x_1672_);
v___x_1674_ = v___x_1669_;
goto v_reusejp_1673_;
}
else
{
lean_object* v_reuseFailAlloc_1675_; 
v_reuseFailAlloc_1675_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1675_, 0, v___x_1672_);
v___x_1674_ = v_reuseFailAlloc_1675_;
goto v_reusejp_1673_;
}
v_reusejp_1673_:
{
return v___x_1674_;
}
}
}
case 1:
{
lean_object* v_a_1677_; lean_object* v___x_1679_; uint8_t v_isShared_1680_; uint8_t v_isSharedCheck_1685_; 
v_a_1677_ = lean_ctor_get(v_x_1665_, 0);
v_isSharedCheck_1685_ = !lean_is_exclusive(v_x_1665_);
if (v_isSharedCheck_1685_ == 0)
{
v___x_1679_ = v_x_1665_;
v_isShared_1680_ = v_isSharedCheck_1685_;
goto v_resetjp_1678_;
}
else
{
lean_inc(v_a_1677_);
lean_dec(v_x_1665_);
v___x_1679_ = lean_box(0);
v_isShared_1680_ = v_isSharedCheck_1685_;
goto v_resetjp_1678_;
}
v_resetjp_1678_:
{
lean_object* v___x_1681_; lean_object* v___x_1683_; 
v___x_1681_ = l_Nat_reprFast(v_a_1677_);
if (v_isShared_1680_ == 0)
{
lean_ctor_set_tag(v___x_1679_, 3);
lean_ctor_set(v___x_1679_, 0, v___x_1681_);
v___x_1683_ = v___x_1679_;
goto v_reusejp_1682_;
}
else
{
lean_object* v_reuseFailAlloc_1684_; 
v_reuseFailAlloc_1684_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1684_, 0, v___x_1681_);
v___x_1683_ = v_reuseFailAlloc_1684_;
goto v_reusejp_1682_;
}
v_reusejp_1682_:
{
return v___x_1683_;
}
}
}
case 2:
{
lean_object* v_a_1686_; lean_object* v_a_1687_; lean_object* v___x_1689_; uint8_t v_isShared_1690_; uint8_t v_isSharedCheck_1706_; 
v_a_1686_ = lean_ctor_get(v_x_1665_, 0);
v_a_1687_ = lean_ctor_get(v_x_1665_, 1);
v_isSharedCheck_1706_ = !lean_is_exclusive(v_x_1665_);
if (v_isSharedCheck_1706_ == 0)
{
v___x_1689_ = v_x_1665_;
v_isShared_1690_ = v_isSharedCheck_1706_;
goto v_resetjp_1688_;
}
else
{
lean_inc(v_a_1687_);
lean_inc(v_a_1686_);
lean_dec(v_x_1665_);
v___x_1689_ = lean_box(0);
v_isShared_1690_ = v_isSharedCheck_1706_;
goto v_resetjp_1688_;
}
v_resetjp_1688_:
{
lean_object* v_zero_1691_; uint8_t v_isZero_1692_; 
v_zero_1691_ = lean_unsigned_to_nat(0u);
v_isZero_1692_ = lean_nat_dec_eq(v_a_1687_, v_zero_1691_);
if (v_isZero_1692_ == 1)
{
lean_del_object(v___x_1689_);
lean_dec(v_a_1687_);
v_x_1665_ = v_a_1686_;
goto _start;
}
else
{
lean_object* v_one_1694_; lean_object* v_n_1695_; lean_object* v_f_x27_1696_; lean_object* v___x_1697_; lean_object* v___x_1699_; 
v_one_1694_ = lean_unsigned_to_nat(1u);
v_n_1695_ = lean_nat_sub(v_a_1687_, v_one_1694_);
lean_dec(v_a_1687_);
v_f_x27_1696_ = l_Lean_Level_PP_Result_format(v_a_1686_, v_isZero_1692_);
v___x_1697_ = ((lean_object*)(l_Lean_Level_PP_Result_format___closed__1));
if (v_isShared_1690_ == 0)
{
lean_ctor_set_tag(v___x_1689_, 5);
lean_ctor_set(v___x_1689_, 1, v___x_1697_);
lean_ctor_set(v___x_1689_, 0, v_f_x27_1696_);
v___x_1699_ = v___x_1689_;
goto v_reusejp_1698_;
}
else
{
lean_object* v_reuseFailAlloc_1705_; 
v_reuseFailAlloc_1705_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1705_, 0, v_f_x27_1696_);
lean_ctor_set(v_reuseFailAlloc_1705_, 1, v___x_1697_);
v___x_1699_ = v_reuseFailAlloc_1705_;
goto v_reusejp_1698_;
}
v_reusejp_1698_:
{
lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; 
v___x_1700_ = lean_nat_add(v_n_1695_, v_one_1694_);
lean_dec(v_n_1695_);
v___x_1701_ = l_Nat_reprFast(v___x_1700_);
v___x_1702_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1702_, 0, v___x_1701_);
v___x_1703_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1703_, 0, v___x_1699_);
lean_ctor_set(v___x_1703_, 1, v___x_1702_);
v___x_1704_ = l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse(v___x_1703_, v_x_1666_);
return v___x_1704_;
}
}
}
}
case 3:
{
lean_object* v_a_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; uint8_t v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; 
v_a_1707_ = lean_ctor_get(v_x_1665_, 0);
lean_inc(v_a_1707_);
lean_dec_ref_known(v_x_1665_, 1);
v___x_1708_ = ((lean_object*)(l_Lean_Level_PP_Result_format___closed__3));
v___x_1709_ = l___private_Lean_Level_0__Lean_Level_PP_Result_formatLst(v_a_1707_);
v___x_1710_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1710_, 0, v___x_1708_);
lean_ctor_set(v___x_1710_, 1, v___x_1709_);
v___x_1711_ = 0;
v___x_1712_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1712_, 0, v___x_1710_);
lean_ctor_set_uint8(v___x_1712_, sizeof(void*)*1, v___x_1711_);
v___x_1713_ = l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse(v___x_1712_, v_x_1666_);
return v___x_1713_;
}
default: 
{
lean_object* v_a_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; uint8_t v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; 
v_a_1714_ = lean_ctor_get(v_x_1665_, 0);
lean_inc(v_a_1714_);
lean_dec_ref_known(v_x_1665_, 1);
v___x_1715_ = ((lean_object*)(l_Lean_Level_PP_Result_format___closed__5));
v___x_1716_ = l___private_Lean_Level_0__Lean_Level_PP_Result_formatLst(v_a_1714_);
v___x_1717_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1717_, 0, v___x_1715_);
lean_ctor_set(v___x_1717_, 1, v___x_1716_);
v___x_1718_ = 0;
v___x_1719_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1719_, 0, v___x_1717_);
lean_ctor_set_uint8(v___x_1719_, sizeof(void*)*1, v___x_1718_);
v___x_1720_ = l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse(v___x_1719_, v_x_1666_);
return v___x_1720_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_PP_Result_formatLst(lean_object* v_x_1721_){
_start:
{
if (lean_obj_tag(v_x_1721_) == 0)
{
lean_object* v___x_1722_; 
v___x_1722_ = lean_box(0);
return v___x_1722_;
}
else
{
lean_object* v_head_1723_; lean_object* v_tail_1724_; lean_object* v___x_1726_; uint8_t v_isShared_1727_; uint8_t v_isSharedCheck_1736_; 
v_head_1723_ = lean_ctor_get(v_x_1721_, 0);
v_tail_1724_ = lean_ctor_get(v_x_1721_, 1);
v_isSharedCheck_1736_ = !lean_is_exclusive(v_x_1721_);
if (v_isSharedCheck_1736_ == 0)
{
v___x_1726_ = v_x_1721_;
v_isShared_1727_ = v_isSharedCheck_1736_;
goto v_resetjp_1725_;
}
else
{
lean_inc(v_tail_1724_);
lean_inc(v_head_1723_);
lean_dec(v_x_1721_);
v___x_1726_ = lean_box(0);
v_isShared_1727_ = v_isSharedCheck_1736_;
goto v_resetjp_1725_;
}
v_resetjp_1725_:
{
lean_object* v___x_1728_; uint8_t v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1732_; 
v___x_1728_ = lean_box(1);
v___x_1729_ = 0;
v___x_1730_ = l_Lean_Level_PP_Result_format(v_head_1723_, v___x_1729_);
if (v_isShared_1727_ == 0)
{
lean_ctor_set_tag(v___x_1726_, 5);
lean_ctor_set(v___x_1726_, 1, v___x_1730_);
lean_ctor_set(v___x_1726_, 0, v___x_1728_);
v___x_1732_ = v___x_1726_;
goto v_reusejp_1731_;
}
else
{
lean_object* v_reuseFailAlloc_1735_; 
v_reuseFailAlloc_1735_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1735_, 0, v___x_1728_);
lean_ctor_set(v_reuseFailAlloc_1735_, 1, v___x_1730_);
v___x_1732_ = v_reuseFailAlloc_1735_;
goto v_reusejp_1731_;
}
v_reusejp_1731_:
{
lean_object* v___x_1733_; lean_object* v___x_1734_; 
v___x_1733_ = l___private_Lean_Level_0__Lean_Level_PP_Result_formatLst(v_tail_1724_);
v___x_1734_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1734_, 0, v___x_1732_);
lean_ctor_set(v___x_1734_, 1, v___x_1733_);
return v___x_1734_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_format___boxed(lean_object* v_x_1737_, lean_object* v_x_1738_){
_start:
{
uint8_t v_x_270__boxed_1739_; lean_object* v_res_1740_; 
v_x_270__boxed_1739_ = lean_unbox(v_x_1738_);
v_res_1740_ = l_Lean_Level_PP_Result_format(v_x_1737_, v_x_270__boxed_1739_);
return v_res_1740_;
}
}
static lean_object* _init_l_Lean_Level_PP_Result_quote___closed__0(void){
_start:
{
uint8_t v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; 
v___x_1741_ = 0;
v___x_1742_ = lean_box(0);
v___x_1743_ = l_Lean_SourceInfo_fromRef(v___x_1742_, v___x_1741_);
return v___x_1743_;
}
}
static lean_object* _init_l_Lean_Level_PP_Result_quote___closed__6(void){
_start:
{
lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; 
v___x_1753_ = ((lean_object*)(l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__0));
v___x_1754_ = lean_obj_once(&l_Lean_Level_PP_Result_quote___closed__0, &l_Lean_Level_PP_Result_quote___closed__0_once, _init_l_Lean_Level_PP_Result_quote___closed__0);
v___x_1755_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1755_, 0, v___x_1754_);
lean_ctor_set(v___x_1755_, 1, v___x_1753_);
return v___x_1755_;
}
}
static lean_object* _init_l_Lean_Level_PP_Result_quote___closed__7(void){
_start:
{
lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; 
v___x_1756_ = ((lean_object*)(l_Lean_instReprData___lam__0___closed__0));
v___x_1757_ = lean_obj_once(&l_Lean_Level_PP_Result_quote___closed__0, &l_Lean_Level_PP_Result_quote___closed__0_once, _init_l_Lean_Level_PP_Result_quote___closed__0);
v___x_1758_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1758_, 0, v___x_1757_);
lean_ctor_set(v___x_1758_, 1, v___x_1756_);
return v___x_1758_;
}
}
static lean_object* _init_l_Lean_Level_PP_Result_quote___closed__12(void){
_start:
{
lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; 
v___x_1771_ = ((lean_object*)(l_Lean_Level_PP_Result_format___closed__2));
v___x_1772_ = lean_obj_once(&l_Lean_Level_PP_Result_quote___closed__0, &l_Lean_Level_PP_Result_quote___closed__0_once, _init_l_Lean_Level_PP_Result_quote___closed__0);
v___x_1773_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1773_, 0, v___x_1772_);
lean_ctor_set(v___x_1773_, 1, v___x_1771_);
return v___x_1773_;
}
}
static lean_object* _init_l_Lean_Level_PP_Result_quote___closed__15(void){
_start:
{
lean_object* v___x_1777_; 
v___x_1777_ = l_Array_mkArray0___redArg();
return v___x_1777_;
}
}
static lean_object* _init_l_Lean_Level_PP_Result_quote___closed__17(void){
_start:
{
lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; 
v___x_1783_ = ((lean_object*)(l_Lean_Level_PP_Result_format___closed__4));
v___x_1784_ = lean_obj_once(&l_Lean_Level_PP_Result_quote___closed__0, &l_Lean_Level_PP_Result_quote___closed__0_once, _init_l_Lean_Level_PP_Result_quote___closed__0);
v___x_1785_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1785_, 0, v___x_1784_);
lean_ctor_set(v___x_1785_, 1, v___x_1783_);
return v___x_1785_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_quote(lean_object* v_r_1786_, lean_object* v_prec_1787_){
_start:
{
lean_object* v_s_1789_; 
switch(lean_obj_tag(v_r_1786_))
{
case 0:
{
lean_object* v_a_1797_; lean_object* v___x_1798_; 
v_a_1797_ = lean_ctor_get(v_r_1786_, 0);
lean_inc(v_a_1797_);
lean_dec_ref_known(v_r_1786_, 1);
v___x_1798_ = l_Lean_mkIdent(v_a_1797_);
return v___x_1798_;
}
case 1:
{
lean_object* v_a_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; 
v_a_1799_ = lean_ctor_get(v_r_1786_, 0);
lean_inc(v_a_1799_);
lean_dec_ref_known(v_r_1786_, 1);
v___x_1800_ = l_Nat_reprFast(v_a_1799_);
v___x_1801_ = lean_box(2);
v___x_1802_ = l_Lean_Syntax_mkNumLit(v___x_1800_, v___x_1801_);
return v___x_1802_;
}
case 2:
{
lean_object* v_a_1803_; lean_object* v_a_1804_; lean_object* v___x_1806_; uint8_t v_isShared_1807_; uint8_t v_isSharedCheck_1827_; 
v_a_1803_ = lean_ctor_get(v_r_1786_, 0);
v_a_1804_ = lean_ctor_get(v_r_1786_, 1);
v_isSharedCheck_1827_ = !lean_is_exclusive(v_r_1786_);
if (v_isSharedCheck_1827_ == 0)
{
v___x_1806_ = v_r_1786_;
v_isShared_1807_ = v_isSharedCheck_1827_;
goto v_resetjp_1805_;
}
else
{
lean_inc(v_a_1804_);
lean_inc(v_a_1803_);
lean_dec(v_r_1786_);
v___x_1806_ = lean_box(0);
v_isShared_1807_ = v_isSharedCheck_1827_;
goto v_resetjp_1805_;
}
v_resetjp_1805_:
{
lean_object* v_zero_1808_; uint8_t v_isZero_1809_; 
v_zero_1808_ = lean_unsigned_to_nat(0u);
v_isZero_1809_ = lean_nat_dec_eq(v_a_1804_, v_zero_1808_);
if (v_isZero_1809_ == 1)
{
lean_del_object(v___x_1806_);
lean_dec(v_a_1804_);
v_r_1786_ = v_a_1803_;
goto _start;
}
else
{
lean_object* v_one_1811_; lean_object* v_n_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1820_; 
v_one_1811_ = lean_unsigned_to_nat(1u);
v_n_1812_ = lean_nat_sub(v_a_1804_, v_one_1811_);
lean_dec(v_a_1804_);
v___x_1813_ = lean_box(0);
v___x_1814_ = l_Lean_SourceInfo_fromRef(v___x_1813_, v_isZero_1809_);
v___x_1815_ = ((lean_object*)(l_Lean_Level_PP_Result_quote___closed__9));
v___x_1816_ = lean_unsigned_to_nat(65u);
v___x_1817_ = l_Lean_Level_PP_Result_quote(v_a_1803_, v___x_1816_);
v___x_1818_ = ((lean_object*)(l_Lean_Level_PP_Result_quote___closed__10));
lean_inc(v___x_1814_);
if (v_isShared_1807_ == 0)
{
lean_ctor_set(v___x_1806_, 1, v___x_1818_);
lean_ctor_set(v___x_1806_, 0, v___x_1814_);
v___x_1820_ = v___x_1806_;
goto v_reusejp_1819_;
}
else
{
lean_object* v_reuseFailAlloc_1826_; 
v_reuseFailAlloc_1826_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1826_, 0, v___x_1814_);
lean_ctor_set(v_reuseFailAlloc_1826_, 1, v___x_1818_);
v___x_1820_ = v_reuseFailAlloc_1826_;
goto v_reusejp_1819_;
}
v_reusejp_1819_:
{
lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; 
v___x_1821_ = lean_nat_add(v_n_1812_, v_one_1811_);
lean_dec(v_n_1812_);
v___x_1822_ = l_Nat_reprFast(v___x_1821_);
v___x_1823_ = lean_box(2);
v___x_1824_ = l_Lean_Syntax_mkNumLit(v___x_1822_, v___x_1823_);
v___x_1825_ = l_Lean_Syntax_node3(v___x_1814_, v___x_1815_, v___x_1817_, v___x_1820_, v___x_1824_);
v_s_1789_ = v___x_1825_;
goto v___jp_1788_;
}
}
}
}
case 3:
{
lean_object* v_a_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; size_t v_sz_1835_; size_t v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; 
v_a_1828_ = lean_ctor_get(v_r_1786_, 0);
lean_inc(v_a_1828_);
lean_dec_ref_known(v_r_1786_, 1);
v___x_1829_ = lean_obj_once(&l_Lean_Level_PP_Result_quote___closed__0, &l_Lean_Level_PP_Result_quote___closed__0_once, _init_l_Lean_Level_PP_Result_quote___closed__0);
v___x_1830_ = ((lean_object*)(l_Lean_Level_PP_Result_quote___closed__11));
v___x_1831_ = lean_obj_once(&l_Lean_Level_PP_Result_quote___closed__12, &l_Lean_Level_PP_Result_quote___closed__12_once, _init_l_Lean_Level_PP_Result_quote___closed__12);
v___x_1832_ = ((lean_object*)(l_Lean_Level_PP_Result_quote___closed__14));
v___x_1833_ = lean_obj_once(&l_Lean_Level_PP_Result_quote___closed__15, &l_Lean_Level_PP_Result_quote___closed__15_once, _init_l_Lean_Level_PP_Result_quote___closed__15);
v___x_1834_ = lean_array_mk(v_a_1828_);
v_sz_1835_ = lean_array_size(v___x_1834_);
v___x_1836_ = ((size_t)0ULL);
v___x_1837_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Level_PP_Result_quote_spec__0(v_sz_1835_, v___x_1836_, v___x_1834_);
v___x_1838_ = l_Array_append___redArg(v___x_1833_, v___x_1837_);
lean_dec_ref(v___x_1837_);
v___x_1839_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1839_, 0, v___x_1829_);
lean_ctor_set(v___x_1839_, 1, v___x_1832_);
lean_ctor_set(v___x_1839_, 2, v___x_1838_);
v___x_1840_ = l_Lean_Syntax_node2(v___x_1829_, v___x_1830_, v___x_1831_, v___x_1839_);
v_s_1789_ = v___x_1840_;
goto v___jp_1788_;
}
default: 
{
lean_object* v_a_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; size_t v_sz_1848_; size_t v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; 
v_a_1841_ = lean_ctor_get(v_r_1786_, 0);
lean_inc(v_a_1841_);
lean_dec_ref_known(v_r_1786_, 1);
v___x_1842_ = lean_obj_once(&l_Lean_Level_PP_Result_quote___closed__0, &l_Lean_Level_PP_Result_quote___closed__0_once, _init_l_Lean_Level_PP_Result_quote___closed__0);
v___x_1843_ = ((lean_object*)(l_Lean_Level_PP_Result_quote___closed__16));
v___x_1844_ = lean_obj_once(&l_Lean_Level_PP_Result_quote___closed__17, &l_Lean_Level_PP_Result_quote___closed__17_once, _init_l_Lean_Level_PP_Result_quote___closed__17);
v___x_1845_ = ((lean_object*)(l_Lean_Level_PP_Result_quote___closed__14));
v___x_1846_ = lean_obj_once(&l_Lean_Level_PP_Result_quote___closed__15, &l_Lean_Level_PP_Result_quote___closed__15_once, _init_l_Lean_Level_PP_Result_quote___closed__15);
v___x_1847_ = lean_array_mk(v_a_1841_);
v_sz_1848_ = lean_array_size(v___x_1847_);
v___x_1849_ = ((size_t)0ULL);
v___x_1850_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Level_PP_Result_quote_spec__0(v_sz_1848_, v___x_1849_, v___x_1847_);
v___x_1851_ = l_Array_append___redArg(v___x_1846_, v___x_1850_);
lean_dec_ref(v___x_1850_);
v___x_1852_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1852_, 0, v___x_1842_);
lean_ctor_set(v___x_1852_, 1, v___x_1845_);
lean_ctor_set(v___x_1852_, 2, v___x_1851_);
v___x_1853_ = l_Lean_Syntax_node2(v___x_1842_, v___x_1843_, v___x_1844_, v___x_1852_);
v_s_1789_ = v___x_1853_;
goto v___jp_1788_;
}
}
v___jp_1788_:
{
lean_object* v___x_1790_; uint8_t v___x_1791_; 
v___x_1790_ = lean_unsigned_to_nat(0u);
v___x_1791_ = lean_nat_dec_lt(v___x_1790_, v_prec_1787_);
if (v___x_1791_ == 0)
{
return v_s_1789_;
}
else
{
lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; 
v___x_1792_ = lean_obj_once(&l_Lean_Level_PP_Result_quote___closed__0, &l_Lean_Level_PP_Result_quote___closed__0_once, _init_l_Lean_Level_PP_Result_quote___closed__0);
v___x_1793_ = ((lean_object*)(l_Lean_Level_PP_Result_quote___closed__5));
v___x_1794_ = lean_obj_once(&l_Lean_Level_PP_Result_quote___closed__6, &l_Lean_Level_PP_Result_quote___closed__6_once, _init_l_Lean_Level_PP_Result_quote___closed__6);
v___x_1795_ = lean_obj_once(&l_Lean_Level_PP_Result_quote___closed__7, &l_Lean_Level_PP_Result_quote___closed__7_once, _init_l_Lean_Level_PP_Result_quote___closed__7);
v___x_1796_ = l_Lean_Syntax_node3(v___x_1792_, v___x_1793_, v___x_1794_, v_s_1789_, v___x_1795_);
return v___x_1796_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Level_PP_Result_quote_spec__0(size_t v_sz_1854_, size_t v_i_1855_, lean_object* v_bs_1856_){
_start:
{
uint8_t v___x_1857_; 
v___x_1857_ = lean_usize_dec_lt(v_i_1855_, v_sz_1854_);
if (v___x_1857_ == 0)
{
return v_bs_1856_;
}
else
{
lean_object* v_v_1858_; lean_object* v___x_1859_; lean_object* v_bs_x27_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; size_t v___x_1863_; size_t v___x_1864_; lean_object* v___x_1865_; 
v_v_1858_ = lean_array_uget(v_bs_1856_, v_i_1855_);
v___x_1859_ = lean_unsigned_to_nat(0u);
v_bs_x27_1860_ = lean_array_uset(v_bs_1856_, v_i_1855_, v___x_1859_);
v___x_1861_ = lean_unsigned_to_nat(1024u);
v___x_1862_ = l_Lean_Level_PP_Result_quote(v_v_1858_, v___x_1861_);
v___x_1863_ = ((size_t)1ULL);
v___x_1864_ = lean_usize_add(v_i_1855_, v___x_1863_);
v___x_1865_ = lean_array_uset(v_bs_x27_1860_, v_i_1855_, v___x_1862_);
v_i_1855_ = v___x_1864_;
v_bs_1856_ = v___x_1865_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Level_PP_Result_quote_spec__0___boxed(lean_object* v_sz_1867_, lean_object* v_i_1868_, lean_object* v_bs_1869_){
_start:
{
size_t v_sz_boxed_1870_; size_t v_i_boxed_1871_; lean_object* v_res_1872_; 
v_sz_boxed_1870_ = lean_unbox_usize(v_sz_1867_);
lean_dec(v_sz_1867_);
v_i_boxed_1871_ = lean_unbox_usize(v_i_1868_);
lean_dec(v_i_1868_);
v_res_1872_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Level_PP_Result_quote_spec__0(v_sz_boxed_1870_, v_i_boxed_1871_, v_bs_1869_);
return v_res_1872_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_quote___boxed(lean_object* v_r_1873_, lean_object* v_prec_1874_){
_start:
{
lean_object* v_res_1875_; 
v_res_1875_ = l_Lean_Level_PP_Result_quote(v_r_1873_, v_prec_1874_);
lean_dec(v_prec_1874_);
return v_res_1875_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_format(lean_object* v_u_1876_, uint8_t v_mvars_1877_, lean_object* v_lIndex_x3f_1878_){
_start:
{
lean_object* v___x_1879_; lean_object* v___x_1880_; uint8_t v___x_1881_; lean_object* v___x_1882_; 
v___x_1879_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1879_, 0, v_lIndex_x3f_1878_);
lean_ctor_set_uint8(v___x_1879_, sizeof(void*)*1, v_mvars_1877_);
v___x_1880_ = l_Lean_Level_PP_toResult(v_u_1876_, v___x_1879_);
lean_dec_ref_known(v___x_1879_, 1);
v___x_1881_ = 1;
v___x_1882_ = l_Lean_Level_PP_Result_format(v___x_1880_, v___x_1881_);
return v___x_1882_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_format___boxed(lean_object* v_u_1883_, lean_object* v_mvars_1884_, lean_object* v_lIndex_x3f_1885_){
_start:
{
uint8_t v_mvars_boxed_1886_; lean_object* v_res_1887_; 
v_mvars_boxed_1886_ = lean_unbox(v_mvars_1884_);
v_res_1887_ = l_Lean_Level_format(v_u_1883_, v_mvars_boxed_1886_, v_lIndex_x3f_1885_);
return v_res_1887_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_instToFormat___lam__0(lean_object* v_x_1888_){
_start:
{
lean_object* v___x_1889_; 
v___x_1889_ = lean_box(0);
return v___x_1889_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_instToFormat___lam__0___boxed(lean_object* v_x_1890_){
_start:
{
lean_object* v_res_1891_; 
v_res_1891_ = l_Lean_Level_instToFormat___lam__0(v_x_1890_);
lean_dec(v_x_1890_);
return v_res_1891_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_instToFormat___lam__1(lean_object* v___f_1892_, lean_object* v_u_1893_){
_start:
{
uint8_t v___x_1894_; lean_object* v___x_1895_; 
v___x_1894_ = 1;
v___x_1895_ = l_Lean_Level_format(v_u_1893_, v___x_1894_, v___f_1892_);
return v___x_1895_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_instToString___lam__1(lean_object* v___f_1900_, lean_object* v_u_1901_){
_start:
{
uint8_t v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; 
v___x_1902_ = 1;
v___x_1903_ = l_Lean_Level_format(v_u_1901_, v___x_1902_, v___f_1900_);
v___x_1904_ = l_Std_Format_defWidth;
v___x_1905_ = lean_unsigned_to_nat(0u);
v___x_1906_ = l_Std_Format_pretty(v___x_1903_, v___x_1904_, v___x_1905_, v___x_1905_);
return v___x_1906_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_quote(lean_object* v_u_1910_, lean_object* v_prec_1911_, uint8_t v_mvars_1912_, lean_object* v_lIndex_x3f_1913_){
_start:
{
lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; 
v___x_1914_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1914_, 0, v_lIndex_x3f_1913_);
lean_ctor_set_uint8(v___x_1914_, sizeof(void*)*1, v_mvars_1912_);
v___x_1915_ = l_Lean_Level_PP_toResult(v_u_1910_, v___x_1914_);
lean_dec_ref_known(v___x_1914_, 1);
v___x_1916_ = l_Lean_Level_PP_Result_quote(v___x_1915_, v_prec_1911_);
return v___x_1916_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_quote___boxed(lean_object* v_u_1917_, lean_object* v_prec_1918_, lean_object* v_mvars_1919_, lean_object* v_lIndex_x3f_1920_){
_start:
{
uint8_t v_mvars_boxed_1921_; lean_object* v_res_1922_; 
v_mvars_boxed_1921_ = lean_unbox(v_mvars_1919_);
v_res_1922_ = l_Lean_Level_quote(v_u_1917_, v_prec_1918_, v_mvars_boxed_1921_, v_lIndex_x3f_1920_);
lean_dec(v_prec_1918_);
return v_res_1922_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_instQuoteMkStr1___lam__1(lean_object* v___f_1923_, lean_object* v_u_1924_){
_start:
{
lean_object* v___x_1925_; uint8_t v___x_1926_; lean_object* v___x_1927_; 
v___x_1925_ = lean_unsigned_to_nat(0u);
v___x_1926_ = 1;
v___x_1927_ = l_Lean_Level_quote(v_u_1924_, v___x_1925_, v___x_1926_, v___f_1923_);
return v___x_1927_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Level_0__Lean_mkLevelMaxCore___lam__0(lean_object* v_u_1931_, lean_object* v_v_1932_){
_start:
{
uint8_t v___y_1934_; uint8_t v___x_1940_; 
v___x_1940_ = l_Lean_Level_isExplicit(v_v_1932_);
if (v___x_1940_ == 0)
{
v___y_1934_ = v___x_1940_;
goto v___jp_1933_;
}
else
{
lean_object* v___x_1941_; lean_object* v___x_1942_; uint8_t v___x_1943_; 
v___x_1941_ = l_Lean_Level_getOffset(v_v_1932_);
v___x_1942_ = l_Lean_Level_getOffset(v_u_1931_);
v___x_1943_ = lean_nat_dec_le(v___x_1941_, v___x_1942_);
lean_dec(v___x_1942_);
lean_dec(v___x_1941_);
v___y_1934_ = v___x_1943_;
goto v___jp_1933_;
}
v___jp_1933_:
{
uint8_t v___x_1935_; 
v___x_1935_ = 1;
if (v___y_1934_ == 0)
{
if (lean_obj_tag(v_u_1931_) == 2)
{
lean_object* v_a_1936_; lean_object* v_a_1937_; uint8_t v___x_1938_; 
v_a_1936_ = lean_ctor_get(v_u_1931_, 0);
v_a_1937_ = lean_ctor_get(v_u_1931_, 1);
v___x_1938_ = lean_level_eq(v_v_1932_, v_a_1936_);
if (v___x_1938_ == 0)
{
uint8_t v___x_1939_; 
v___x_1939_ = lean_level_eq(v_v_1932_, v_a_1937_);
return v___x_1939_;
}
else
{
return v___x_1935_;
}
}
else
{
return v___y_1934_;
}
}
else
{
return v___x_1935_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_mkLevelMaxCore___lam__0___boxed(lean_object* v_u_1944_, lean_object* v_v_1945_){
_start:
{
uint8_t v_res_1946_; lean_object* v_r_1947_; 
v_res_1946_ = l___private_Lean_Level_0__Lean_mkLevelMaxCore___lam__0(v_u_1944_, v_v_1945_);
lean_dec(v_v_1945_);
lean_dec(v_u_1944_);
v_r_1947_ = lean_box(v_res_1946_);
return v_r_1947_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_mkLevelMaxCore(lean_object* v_u_1948_, lean_object* v_v_1949_, lean_object* v_elseK_1950_){
_start:
{
uint8_t v___x_1951_; 
v___x_1951_ = lean_level_eq(v_u_1948_, v_v_1949_);
if (v___x_1951_ == 0)
{
uint8_t v___x_1952_; 
v___x_1952_ = l_Lean_Level_isZero(v_u_1948_);
if (v___x_1952_ == 0)
{
uint8_t v___x_1953_; 
v___x_1953_ = l_Lean_Level_isZero(v_v_1949_);
if (v___x_1953_ == 0)
{
uint8_t v___x_1954_; 
v___x_1954_ = l___private_Lean_Level_0__Lean_mkLevelMaxCore___lam__0(v_u_1948_, v_v_1949_);
if (v___x_1954_ == 0)
{
uint8_t v___x_1955_; 
v___x_1955_ = l___private_Lean_Level_0__Lean_mkLevelMaxCore___lam__0(v_v_1949_, v_u_1948_);
if (v___x_1955_ == 0)
{
lean_object* v___x_1956_; lean_object* v___x_1957_; uint8_t v___x_1958_; 
v___x_1956_ = l_Lean_Level_getLevelOffset(v_u_1948_);
v___x_1957_ = l_Lean_Level_getLevelOffset(v_v_1949_);
v___x_1958_ = lean_level_eq(v___x_1956_, v___x_1957_);
lean_dec(v___x_1957_);
lean_dec(v___x_1956_);
if (v___x_1958_ == 0)
{
lean_object* v___x_1959_; lean_object* v___x_1960_; 
v___x_1959_ = lean_box(0);
v___x_1960_ = lean_apply_1(v_elseK_1950_, v___x_1959_);
return v___x_1960_;
}
else
{
lean_object* v___x_1961_; lean_object* v___x_1962_; uint8_t v___x_1963_; 
lean_dec_ref(v_elseK_1950_);
v___x_1961_ = l_Lean_Level_getOffset(v_v_1949_);
v___x_1962_ = l_Lean_Level_getOffset(v_u_1948_);
v___x_1963_ = lean_nat_dec_le(v___x_1961_, v___x_1962_);
lean_dec(v___x_1962_);
lean_dec(v___x_1961_);
if (v___x_1963_ == 0)
{
lean_inc(v_v_1949_);
return v_v_1949_;
}
else
{
lean_inc(v_u_1948_);
return v_u_1948_;
}
}
}
else
{
lean_dec_ref(v_elseK_1950_);
lean_inc(v_v_1949_);
return v_v_1949_;
}
}
else
{
lean_dec_ref(v_elseK_1950_);
lean_inc(v_u_1948_);
return v_u_1948_;
}
}
else
{
lean_dec_ref(v_elseK_1950_);
lean_inc(v_u_1948_);
return v_u_1948_;
}
}
else
{
lean_dec_ref(v_elseK_1950_);
lean_inc(v_v_1949_);
return v_v_1949_;
}
}
else
{
lean_dec_ref(v_elseK_1950_);
lean_inc(v_u_1948_);
return v_u_1948_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_mkLevelMaxCore___boxed(lean_object* v_u_1964_, lean_object* v_v_1965_, lean_object* v_elseK_1966_){
_start:
{
lean_object* v_res_1967_; 
v_res_1967_ = l___private_Lean_Level_0__Lean_mkLevelMaxCore(v_u_1964_, v_v_1965_, v_elseK_1966_);
lean_dec(v_v_1965_);
lean_dec(v_u_1964_);
return v_res_1967_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLevelMax_x27(lean_object* v_u_1968_, lean_object* v_v_1969_){
_start:
{
uint8_t v___x_1970_; 
v___x_1970_ = lean_level_eq(v_u_1968_, v_v_1969_);
if (v___x_1970_ == 0)
{
uint8_t v___x_1971_; 
v___x_1971_ = l_Lean_Level_isZero(v_u_1968_);
if (v___x_1971_ == 0)
{
uint8_t v___x_1972_; 
v___x_1972_ = l_Lean_Level_isZero(v_v_1969_);
if (v___x_1972_ == 0)
{
uint8_t v___x_1973_; 
v___x_1973_ = l___private_Lean_Level_0__Lean_mkLevelMaxCore___lam__0(v_u_1968_, v_v_1969_);
if (v___x_1973_ == 0)
{
uint8_t v___x_1974_; 
v___x_1974_ = l___private_Lean_Level_0__Lean_mkLevelMaxCore___lam__0(v_v_1969_, v_u_1968_);
if (v___x_1974_ == 0)
{
lean_object* v___x_1975_; lean_object* v___x_1976_; uint8_t v___x_1977_; 
v___x_1975_ = l_Lean_Level_getLevelOffset(v_u_1968_);
v___x_1976_ = l_Lean_Level_getLevelOffset(v_v_1969_);
v___x_1977_ = lean_level_eq(v___x_1975_, v___x_1976_);
lean_dec(v___x_1976_);
lean_dec(v___x_1975_);
if (v___x_1977_ == 0)
{
lean_object* v___x_1978_; 
v___x_1978_ = l_Lean_Level_max___override(v_u_1968_, v_v_1969_);
return v___x_1978_;
}
else
{
lean_object* v___x_1979_; lean_object* v___x_1980_; uint8_t v___x_1981_; 
v___x_1979_ = l_Lean_Level_getOffset(v_v_1969_);
v___x_1980_ = l_Lean_Level_getOffset(v_u_1968_);
v___x_1981_ = lean_nat_dec_le(v___x_1979_, v___x_1980_);
lean_dec(v___x_1980_);
lean_dec(v___x_1979_);
if (v___x_1981_ == 0)
{
lean_dec(v_u_1968_);
return v_v_1969_;
}
else
{
lean_dec(v_v_1969_);
return v_u_1968_;
}
}
}
else
{
lean_dec(v_u_1968_);
return v_v_1969_;
}
}
else
{
lean_dec(v_v_1969_);
return v_u_1968_;
}
}
else
{
lean_dec(v_v_1969_);
return v_u_1968_;
}
}
else
{
lean_dec(v_u_1968_);
return v_v_1969_;
}
}
else
{
lean_dec(v_v_1969_);
return v_u_1968_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_simpLevelMax_x27(lean_object* v_u_1982_, lean_object* v_v_1983_, lean_object* v_d_1984_){
_start:
{
uint8_t v___x_1985_; 
v___x_1985_ = lean_level_eq(v_u_1982_, v_v_1983_);
if (v___x_1985_ == 0)
{
uint8_t v___x_1986_; 
v___x_1986_ = l_Lean_Level_isZero(v_u_1982_);
if (v___x_1986_ == 0)
{
uint8_t v___x_1987_; 
v___x_1987_ = l_Lean_Level_isZero(v_v_1983_);
if (v___x_1987_ == 0)
{
uint8_t v___x_1988_; 
v___x_1988_ = l___private_Lean_Level_0__Lean_mkLevelMaxCore___lam__0(v_u_1982_, v_v_1983_);
if (v___x_1988_ == 0)
{
uint8_t v___x_1989_; 
v___x_1989_ = l___private_Lean_Level_0__Lean_mkLevelMaxCore___lam__0(v_v_1983_, v_u_1982_);
if (v___x_1989_ == 0)
{
lean_object* v___x_1990_; lean_object* v___x_1991_; uint8_t v___x_1992_; 
v___x_1990_ = l_Lean_Level_getLevelOffset(v_u_1982_);
v___x_1991_ = l_Lean_Level_getLevelOffset(v_v_1983_);
v___x_1992_ = lean_level_eq(v___x_1990_, v___x_1991_);
lean_dec(v___x_1991_);
lean_dec(v___x_1990_);
if (v___x_1992_ == 0)
{
lean_inc(v_d_1984_);
return v_d_1984_;
}
else
{
lean_object* v___x_1993_; lean_object* v___x_1994_; uint8_t v___x_1995_; 
v___x_1993_ = l_Lean_Level_getOffset(v_v_1983_);
v___x_1994_ = l_Lean_Level_getOffset(v_u_1982_);
v___x_1995_ = lean_nat_dec_le(v___x_1993_, v___x_1994_);
lean_dec(v___x_1994_);
lean_dec(v___x_1993_);
if (v___x_1995_ == 0)
{
lean_inc(v_v_1983_);
return v_v_1983_;
}
else
{
lean_inc(v_u_1982_);
return v_u_1982_;
}
}
}
else
{
lean_inc(v_v_1983_);
return v_v_1983_;
}
}
else
{
lean_inc(v_u_1982_);
return v_u_1982_;
}
}
else
{
lean_inc(v_u_1982_);
return v_u_1982_;
}
}
else
{
lean_inc(v_v_1983_);
return v_v_1983_;
}
}
else
{
lean_inc(v_u_1982_);
return v_u_1982_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_simpLevelMax_x27___boxed(lean_object* v_u_1996_, lean_object* v_v_1997_, lean_object* v_d_1998_){
_start:
{
lean_object* v_res_1999_; 
v_res_1999_ = l_Lean_simpLevelMax_x27(v_u_1996_, v_v_1997_, v_d_1998_);
lean_dec(v_d_1998_);
lean_dec(v_v_1997_);
lean_dec(v_u_1996_);
return v_res_1999_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_mkLevelIMaxCore(lean_object* v_u_2000_, lean_object* v_v_2001_, lean_object* v_elseK_2002_){
_start:
{
uint8_t v___x_2003_; 
v___x_2003_ = l_Lean_Level_isNeverZero(v_v_2001_);
if (v___x_2003_ == 0)
{
uint8_t v___x_2004_; 
v___x_2004_ = l_Lean_Level_isZero(v_v_2001_);
if (v___x_2004_ == 0)
{
uint8_t v___x_2005_; 
v___x_2005_ = l_Lean_Level_isZero(v_u_2000_);
if (v___x_2005_ == 0)
{
uint8_t v___x_2006_; 
v___x_2006_ = lean_level_eq(v_u_2000_, v_v_2001_);
lean_dec(v_v_2001_);
if (v___x_2006_ == 0)
{
lean_object* v___x_2007_; lean_object* v___x_2008_; 
lean_dec(v_u_2000_);
v___x_2007_ = lean_box(0);
v___x_2008_ = lean_apply_1(v_elseK_2002_, v___x_2007_);
return v___x_2008_;
}
else
{
lean_dec_ref(v_elseK_2002_);
return v_u_2000_;
}
}
else
{
lean_dec_ref(v_elseK_2002_);
lean_dec(v_u_2000_);
return v_v_2001_;
}
}
else
{
lean_dec_ref(v_elseK_2002_);
lean_dec(v_u_2000_);
return v_v_2001_;
}
}
else
{
lean_object* v___x_2009_; 
lean_dec_ref(v_elseK_2002_);
v___x_2009_ = l_Lean_mkLevelMax_x27(v_u_2000_, v_v_2001_);
return v___x_2009_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkLevelIMax_x27(lean_object* v_u_2010_, lean_object* v_v_2011_){
_start:
{
uint8_t v___x_2012_; 
v___x_2012_ = l_Lean_Level_isNeverZero(v_v_2011_);
if (v___x_2012_ == 0)
{
uint8_t v___x_2013_; 
v___x_2013_ = l_Lean_Level_isZero(v_v_2011_);
if (v___x_2013_ == 0)
{
uint8_t v___x_2014_; 
v___x_2014_ = l_Lean_Level_isZero(v_u_2010_);
if (v___x_2014_ == 0)
{
uint8_t v___x_2015_; 
v___x_2015_ = lean_level_eq(v_u_2010_, v_v_2011_);
if (v___x_2015_ == 0)
{
lean_object* v___x_2016_; 
v___x_2016_ = l_Lean_Level_imax___override(v_u_2010_, v_v_2011_);
return v___x_2016_;
}
else
{
lean_dec(v_v_2011_);
return v_u_2010_;
}
}
else
{
lean_dec(v_u_2010_);
return v_v_2011_;
}
}
else
{
lean_dec(v_u_2010_);
return v_v_2011_;
}
}
else
{
lean_object* v___x_2017_; 
v___x_2017_ = l_Lean_mkLevelMax_x27(v_u_2010_, v_v_2011_);
return v___x_2017_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_simpLevelIMax_x27(lean_object* v_u_2018_, lean_object* v_v_2019_, lean_object* v_d_2020_){
_start:
{
uint8_t v___x_2021_; 
v___x_2021_ = l_Lean_Level_isNeverZero(v_v_2019_);
if (v___x_2021_ == 0)
{
uint8_t v___x_2022_; 
v___x_2022_ = l_Lean_Level_isZero(v_v_2019_);
if (v___x_2022_ == 0)
{
uint8_t v___x_2023_; 
v___x_2023_ = l_Lean_Level_isZero(v_u_2018_);
if (v___x_2023_ == 0)
{
uint8_t v___x_2024_; 
v___x_2024_ = lean_level_eq(v_u_2018_, v_v_2019_);
lean_dec(v_v_2019_);
if (v___x_2024_ == 0)
{
lean_dec(v_u_2018_);
lean_inc(v_d_2020_);
return v_d_2020_;
}
else
{
return v_u_2018_;
}
}
else
{
lean_dec(v_u_2018_);
return v_v_2019_;
}
}
else
{
lean_dec(v_u_2018_);
return v_v_2019_;
}
}
else
{
lean_object* v___x_2025_; 
v___x_2025_ = l_Lean_mkLevelMax_x27(v_u_2018_, v_v_2019_);
return v___x_2025_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_simpLevelIMax_x27___boxed(lean_object* v_u_2026_, lean_object* v_v_2027_, lean_object* v_d_2028_){
_start:
{
lean_object* v_res_2029_; 
v_res_2029_ = l_Lean_simpLevelIMax_x27(v_u_2026_, v_v_2027_, v_d_2028_);
lean_dec(v_d_2028_);
return v_res_2029_;
}
}
static lean_object* _init_l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl___closed__2(void){
_start:
{
lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; 
v___x_2032_ = ((lean_object*)(l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl___closed__1));
v___x_2033_ = lean_unsigned_to_nat(14u);
v___x_2034_ = lean_unsigned_to_nat(567u);
v___x_2035_ = ((lean_object*)(l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl___closed__0));
v___x_2036_ = ((lean_object*)(l_Lean_Level_mvarId_x21___closed__0));
v___x_2037_ = l_mkPanicMessageWithDecl(v___x_2036_, v___x_2035_, v___x_2034_, v___x_2033_, v___x_2032_);
return v___x_2037_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl(lean_object* v_lvl_2038_, lean_object* v_newLvl_2039_){
_start:
{
if (lean_obj_tag(v_lvl_2038_) == 1)
{
lean_object* v_a_2040_; size_t v___x_2041_; size_t v___x_2042_; uint8_t v___x_2043_; 
v_a_2040_ = lean_ctor_get(v_lvl_2038_, 0);
v___x_2041_ = lean_ptr_addr(v_a_2040_);
v___x_2042_ = lean_ptr_addr(v_newLvl_2039_);
v___x_2043_ = lean_usize_dec_eq(v___x_2041_, v___x_2042_);
if (v___x_2043_ == 0)
{
lean_object* v___x_2044_; 
v___x_2044_ = l_Lean_Level_succ___override(v_newLvl_2039_);
return v___x_2044_;
}
else
{
lean_dec(v_newLvl_2039_);
lean_inc_ref(v_lvl_2038_);
return v_lvl_2038_;
}
}
else
{
lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; 
lean_dec(v_newLvl_2039_);
v___x_2045_ = lean_box(0);
v___x_2046_ = lean_obj_once(&l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl___closed__2, &l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl___closed__2_once, _init_l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl___closed__2);
v___x_2047_ = l_panic___redArg(v___x_2045_, v___x_2046_);
return v___x_2047_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl___boxed(lean_object* v_lvl_2048_, lean_object* v_newLvl_2049_){
_start:
{
lean_object* v_res_2050_; 
v_res_2050_ = l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl(v_lvl_2048_, v_newLvl_2049_);
lean_dec(v_lvl_2048_);
return v_res_2050_;
}
}
static lean_object* _init_l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl___closed__2(void){
_start:
{
lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; 
v___x_2053_ = ((lean_object*)(l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl___closed__1));
v___x_2054_ = lean_unsigned_to_nat(19u);
v___x_2055_ = lean_unsigned_to_nat(578u);
v___x_2056_ = ((lean_object*)(l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl___closed__0));
v___x_2057_ = ((lean_object*)(l_Lean_Level_mvarId_x21___closed__0));
v___x_2058_ = l_mkPanicMessageWithDecl(v___x_2057_, v___x_2056_, v___x_2055_, v___x_2054_, v___x_2053_);
return v___x_2058_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl(lean_object* v_lvl_2059_, lean_object* v_newLhs_2060_, lean_object* v_newRhs_2061_){
_start:
{
if (lean_obj_tag(v_lvl_2059_) == 2)
{
lean_object* v_a_2062_; lean_object* v_a_2063_; size_t v___x_2064_; size_t v___x_2065_; uint8_t v___x_2066_; 
v_a_2062_ = lean_ctor_get(v_lvl_2059_, 0);
v_a_2063_ = lean_ctor_get(v_lvl_2059_, 1);
v___x_2064_ = lean_ptr_addr(v_a_2062_);
v___x_2065_ = lean_ptr_addr(v_newLhs_2060_);
v___x_2066_ = lean_usize_dec_eq(v___x_2064_, v___x_2065_);
if (v___x_2066_ == 0)
{
lean_object* v___x_2067_; 
v___x_2067_ = l_Lean_mkLevelMax_x27(v_newLhs_2060_, v_newRhs_2061_);
return v___x_2067_;
}
else
{
size_t v___x_2068_; size_t v___x_2069_; uint8_t v___x_2070_; 
v___x_2068_ = lean_ptr_addr(v_a_2063_);
v___x_2069_ = lean_ptr_addr(v_newRhs_2061_);
v___x_2070_ = lean_usize_dec_eq(v___x_2068_, v___x_2069_);
if (v___x_2070_ == 0)
{
lean_object* v___x_2071_; 
v___x_2071_ = l_Lean_mkLevelMax_x27(v_newLhs_2060_, v_newRhs_2061_);
return v___x_2071_;
}
else
{
lean_object* v___x_2072_; 
v___x_2072_ = l_Lean_simpLevelMax_x27(v_newLhs_2060_, v_newRhs_2061_, v_lvl_2059_);
lean_dec(v_newRhs_2061_);
lean_dec(v_newLhs_2060_);
return v___x_2072_;
}
}
}
else
{
lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; 
lean_dec(v_newRhs_2061_);
lean_dec(v_newLhs_2060_);
v___x_2073_ = lean_box(0);
v___x_2074_ = lean_obj_once(&l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl___closed__2, &l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl___closed__2_once, _init_l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl___closed__2);
v___x_2075_ = l_panic___redArg(v___x_2073_, v___x_2074_);
return v___x_2075_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl___boxed(lean_object* v_lvl_2076_, lean_object* v_newLhs_2077_, lean_object* v_newRhs_2078_){
_start:
{
lean_object* v_res_2079_; 
v_res_2079_ = l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl(v_lvl_2076_, v_newLhs_2077_, v_newRhs_2078_);
lean_dec(v_lvl_2076_);
return v_res_2079_;
}
}
static lean_object* _init_l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl___closed__2(void){
_start:
{
lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; 
v___x_2082_ = ((lean_object*)(l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl___closed__1));
v___x_2083_ = lean_unsigned_to_nat(20u);
v___x_2084_ = lean_unsigned_to_nat(589u);
v___x_2085_ = ((lean_object*)(l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl___closed__0));
v___x_2086_ = ((lean_object*)(l_Lean_Level_mvarId_x21___closed__0));
v___x_2087_ = l_mkPanicMessageWithDecl(v___x_2086_, v___x_2085_, v___x_2084_, v___x_2083_, v___x_2082_);
return v___x_2087_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl(lean_object* v_lvl_2088_, lean_object* v_newLhs_2089_, lean_object* v_newRhs_2090_){
_start:
{
if (lean_obj_tag(v_lvl_2088_) == 3)
{
lean_object* v_a_2091_; lean_object* v_a_2092_; size_t v___x_2093_; size_t v___x_2094_; uint8_t v___x_2095_; 
v_a_2091_ = lean_ctor_get(v_lvl_2088_, 0);
v_a_2092_ = lean_ctor_get(v_lvl_2088_, 1);
v___x_2093_ = lean_ptr_addr(v_a_2091_);
v___x_2094_ = lean_ptr_addr(v_newLhs_2089_);
v___x_2095_ = lean_usize_dec_eq(v___x_2093_, v___x_2094_);
if (v___x_2095_ == 0)
{
lean_object* v___x_2096_; 
v___x_2096_ = l_Lean_mkLevelIMax_x27(v_newLhs_2089_, v_newRhs_2090_);
return v___x_2096_;
}
else
{
size_t v___x_2097_; size_t v___x_2098_; uint8_t v___x_2099_; 
v___x_2097_ = lean_ptr_addr(v_a_2092_);
v___x_2098_ = lean_ptr_addr(v_newRhs_2090_);
v___x_2099_ = lean_usize_dec_eq(v___x_2097_, v___x_2098_);
if (v___x_2099_ == 0)
{
lean_object* v___x_2100_; 
v___x_2100_ = l_Lean_mkLevelIMax_x27(v_newLhs_2089_, v_newRhs_2090_);
return v___x_2100_;
}
else
{
lean_object* v___x_2101_; 
v___x_2101_ = l_Lean_simpLevelIMax_x27(v_newLhs_2089_, v_newRhs_2090_, v_lvl_2088_);
return v___x_2101_;
}
}
}
else
{
lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; 
lean_dec(v_newRhs_2090_);
lean_dec(v_newLhs_2089_);
v___x_2102_ = lean_box(0);
v___x_2103_ = lean_obj_once(&l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl___closed__2, &l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl___closed__2_once, _init_l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl___closed__2);
v___x_2104_ = l_panic___redArg(v___x_2102_, v___x_2103_);
return v___x_2104_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl___boxed(lean_object* v_lvl_2105_, lean_object* v_newLhs_2106_, lean_object* v_newRhs_2107_){
_start:
{
lean_object* v_res_2108_; 
v_res_2108_ = l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl(v_lvl_2105_, v_newLhs_2106_, v_newRhs_2107_);
lean_dec(v_lvl_2105_);
return v_res_2108_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_mkNaryMax(lean_object* v_x_2109_){
_start:
{
if (lean_obj_tag(v_x_2109_) == 0)
{
lean_object* v___x_2110_; 
v___x_2110_ = lean_box(0);
return v___x_2110_;
}
else
{
lean_object* v_tail_2111_; 
v_tail_2111_ = lean_ctor_get(v_x_2109_, 1);
if (lean_obj_tag(v_tail_2111_) == 0)
{
lean_object* v_head_2112_; 
v_head_2112_ = lean_ctor_get(v_x_2109_, 0);
lean_inc(v_head_2112_);
lean_dec_ref_known(v_x_2109_, 2);
return v_head_2112_;
}
else
{
lean_object* v_head_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; 
lean_inc(v_tail_2111_);
v_head_2113_ = lean_ctor_get(v_x_2109_, 0);
lean_inc(v_head_2113_);
lean_dec_ref_known(v_x_2109_, 2);
v___x_2114_ = l_Lean_Level_mkNaryMax(v_tail_2111_);
v___x_2115_ = l_Lean_mkLevelMax_x27(v_head_2113_, v___x_2114_);
return v___x_2115_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_substParams_go(lean_object* v_s_2116_, lean_object* v_u_2117_){
_start:
{
switch(lean_obj_tag(v_u_2117_))
{
case 0:
{
lean_dec_ref(v_s_2116_);
return v_u_2117_;
}
case 1:
{
lean_object* v_a_2118_; uint8_t v___x_2119_; 
v_a_2118_ = lean_ctor_get(v_u_2117_, 0);
v___x_2119_ = l_Lean_Level_hasParam(v_u_2117_);
if (v___x_2119_ == 0)
{
lean_dec_ref(v_s_2116_);
return v_u_2117_;
}
else
{
lean_object* v___x_2120_; size_t v___x_2121_; size_t v___x_2122_; uint8_t v___x_2123_; 
lean_inc(v_a_2118_);
v___x_2120_ = l___private_Lean_Level_0__Lean_Level_substParams_go(v_s_2116_, v_a_2118_);
v___x_2121_ = lean_ptr_addr(v_a_2118_);
v___x_2122_ = lean_ptr_addr(v___x_2120_);
v___x_2123_ = lean_usize_dec_eq(v___x_2121_, v___x_2122_);
if (v___x_2123_ == 0)
{
lean_object* v___x_2124_; 
lean_dec_ref_known(v_u_2117_, 1);
v___x_2124_ = l_Lean_Level_succ___override(v___x_2120_);
return v___x_2124_;
}
else
{
lean_dec(v___x_2120_);
return v_u_2117_;
}
}
}
case 2:
{
lean_object* v_a_2125_; lean_object* v_a_2126_; uint8_t v___x_2127_; 
v_a_2125_ = lean_ctor_get(v_u_2117_, 0);
v_a_2126_ = lean_ctor_get(v_u_2117_, 1);
v___x_2127_ = l_Lean_Level_hasParam(v_u_2117_);
if (v___x_2127_ == 0)
{
lean_dec_ref(v_s_2116_);
return v_u_2117_;
}
else
{
lean_object* v___x_2128_; lean_object* v___x_2129_; size_t v___x_2130_; size_t v___x_2131_; uint8_t v___x_2132_; 
lean_inc(v_a_2125_);
lean_inc_ref(v_s_2116_);
v___x_2128_ = l___private_Lean_Level_0__Lean_Level_substParams_go(v_s_2116_, v_a_2125_);
lean_inc(v_a_2126_);
v___x_2129_ = l___private_Lean_Level_0__Lean_Level_substParams_go(v_s_2116_, v_a_2126_);
v___x_2130_ = lean_ptr_addr(v_a_2125_);
v___x_2131_ = lean_ptr_addr(v___x_2128_);
v___x_2132_ = lean_usize_dec_eq(v___x_2130_, v___x_2131_);
if (v___x_2132_ == 0)
{
lean_object* v___x_2133_; 
lean_dec_ref_known(v_u_2117_, 2);
v___x_2133_ = l_Lean_mkLevelMax_x27(v___x_2128_, v___x_2129_);
return v___x_2133_;
}
else
{
size_t v___x_2134_; size_t v___x_2135_; uint8_t v___x_2136_; 
v___x_2134_ = lean_ptr_addr(v_a_2126_);
v___x_2135_ = lean_ptr_addr(v___x_2129_);
v___x_2136_ = lean_usize_dec_eq(v___x_2134_, v___x_2135_);
if (v___x_2136_ == 0)
{
lean_object* v___x_2137_; 
lean_dec_ref_known(v_u_2117_, 2);
v___x_2137_ = l_Lean_mkLevelMax_x27(v___x_2128_, v___x_2129_);
return v___x_2137_;
}
else
{
lean_object* v___x_2138_; 
v___x_2138_ = l_Lean_simpLevelMax_x27(v___x_2128_, v___x_2129_, v_u_2117_);
lean_dec_ref_known(v_u_2117_, 2);
lean_dec(v___x_2129_);
lean_dec(v___x_2128_);
return v___x_2138_;
}
}
}
}
case 3:
{
lean_object* v_a_2139_; lean_object* v_a_2140_; uint8_t v___x_2141_; 
v_a_2139_ = lean_ctor_get(v_u_2117_, 0);
v_a_2140_ = lean_ctor_get(v_u_2117_, 1);
v___x_2141_ = l_Lean_Level_hasParam(v_u_2117_);
if (v___x_2141_ == 0)
{
lean_dec_ref(v_s_2116_);
return v_u_2117_;
}
else
{
lean_object* v___x_2142_; lean_object* v___x_2143_; size_t v___x_2144_; size_t v___x_2145_; uint8_t v___x_2146_; 
lean_inc(v_a_2139_);
lean_inc_ref(v_s_2116_);
v___x_2142_ = l___private_Lean_Level_0__Lean_Level_substParams_go(v_s_2116_, v_a_2139_);
lean_inc(v_a_2140_);
v___x_2143_ = l___private_Lean_Level_0__Lean_Level_substParams_go(v_s_2116_, v_a_2140_);
v___x_2144_ = lean_ptr_addr(v_a_2139_);
v___x_2145_ = lean_ptr_addr(v___x_2142_);
v___x_2146_ = lean_usize_dec_eq(v___x_2144_, v___x_2145_);
if (v___x_2146_ == 0)
{
lean_object* v___x_2147_; 
lean_dec_ref_known(v_u_2117_, 2);
v___x_2147_ = l_Lean_mkLevelIMax_x27(v___x_2142_, v___x_2143_);
return v___x_2147_;
}
else
{
size_t v___x_2148_; size_t v___x_2149_; uint8_t v___x_2150_; 
v___x_2148_ = lean_ptr_addr(v_a_2140_);
v___x_2149_ = lean_ptr_addr(v___x_2143_);
v___x_2150_ = lean_usize_dec_eq(v___x_2148_, v___x_2149_);
if (v___x_2150_ == 0)
{
lean_object* v___x_2151_; 
lean_dec_ref_known(v_u_2117_, 2);
v___x_2151_ = l_Lean_mkLevelIMax_x27(v___x_2142_, v___x_2143_);
return v___x_2151_;
}
else
{
lean_object* v___x_2152_; 
v___x_2152_ = l_Lean_simpLevelIMax_x27(v___x_2142_, v___x_2143_, v_u_2117_);
lean_dec_ref_known(v_u_2117_, 2);
return v___x_2152_;
}
}
}
}
case 4:
{
lean_object* v_a_2153_; lean_object* v___x_2154_; 
v_a_2153_ = lean_ctor_get(v_u_2117_, 0);
lean_inc(v_a_2153_);
v___x_2154_ = lean_apply_1(v_s_2116_, v_a_2153_);
if (lean_obj_tag(v___x_2154_) == 0)
{
return v_u_2117_;
}
else
{
lean_object* v_val_2155_; 
lean_dec_ref_known(v_u_2117_, 1);
v_val_2155_ = lean_ctor_get(v___x_2154_, 0);
lean_inc(v_val_2155_);
lean_dec_ref_known(v___x_2154_, 1);
return v_val_2155_;
}
}
default: 
{
lean_dec_ref(v_s_2116_);
return v_u_2117_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_substParams(lean_object* v_u_2156_, lean_object* v_s_2157_){
_start:
{
lean_object* v___x_2158_; 
v___x_2158_ = l___private_Lean_Level_0__Lean_Level_substParams_go(v_s_2157_, v_u_2156_);
return v___x_2158_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_getParamSubst(lean_object* v_x_2159_, lean_object* v_x_2160_, lean_object* v_x_2161_){
_start:
{
if (lean_obj_tag(v_x_2159_) == 1)
{
if (lean_obj_tag(v_x_2160_) == 1)
{
lean_object* v_head_2162_; lean_object* v_tail_2163_; lean_object* v_head_2164_; lean_object* v_tail_2165_; uint8_t v___x_2166_; 
v_head_2162_ = lean_ctor_get(v_x_2159_, 0);
v_tail_2163_ = lean_ctor_get(v_x_2159_, 1);
v_head_2164_ = lean_ctor_get(v_x_2160_, 0);
v_tail_2165_ = lean_ctor_get(v_x_2160_, 1);
v___x_2166_ = lean_name_eq(v_head_2162_, v_x_2161_);
if (v___x_2166_ == 0)
{
v_x_2159_ = v_tail_2163_;
v_x_2160_ = v_tail_2165_;
goto _start;
}
else
{
lean_object* v___x_2168_; 
lean_inc(v_head_2164_);
v___x_2168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2168_, 0, v_head_2164_);
return v___x_2168_;
}
}
else
{
lean_object* v___x_2169_; 
v___x_2169_ = lean_box(0);
return v___x_2169_;
}
}
else
{
lean_object* v___x_2170_; 
v___x_2170_ = lean_box(0);
return v___x_2170_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_getParamSubst___boxed(lean_object* v_x_2171_, lean_object* v_x_2172_, lean_object* v_x_2173_){
_start:
{
lean_object* v_res_2174_; 
v_res_2174_ = l_Lean_Level_getParamSubst(v_x_2171_, v_x_2172_, v_x_2173_);
lean_dec(v_x_2173_);
lean_dec(v_x_2172_);
lean_dec(v_x_2171_);
return v_res_2174_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_instantiateParams(lean_object* v_u_2175_, lean_object* v_paramNames_2176_, lean_object* v_vs_2177_){
_start:
{
lean_object* v___x_2178_; lean_object* v___x_2179_; 
v___x_2178_ = lean_alloc_closure((void*)(l_Lean_Level_getParamSubst___boxed), 3, 2);
lean_closure_set(v___x_2178_, 0, v_paramNames_2176_);
lean_closure_set(v___x_2178_, 1, v_vs_2177_);
v___x_2179_ = l___private_Lean_Level_0__Lean_Level_substParams_go(v___x_2178_, v_u_2175_);
return v___x_2179_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Level_0__Lean_Level_geq_go(lean_object* v_u_2180_, lean_object* v_v_2181_){
_start:
{
uint8_t v___y_2183_; uint8_t v___y_2197_; lean_object* v_u_u2081_2199_; lean_object* v_u_u2082_2200_; lean_object* v_v_2201_; uint8_t v___x_2204_; 
v___x_2204_ = lean_level_eq(v_u_2180_, v_v_2181_);
if (v___x_2204_ == 0)
{
switch(lean_obj_tag(v_v_2181_))
{
case 0:
{
uint8_t v___x_2205_; 
v___x_2205_ = 1;
return v___x_2205_;
}
case 2:
{
lean_object* v_a_2206_; lean_object* v_a_2207_; uint8_t v___x_2208_; 
v_a_2206_ = lean_ctor_get(v_v_2181_, 0);
v_a_2207_ = lean_ctor_get(v_v_2181_, 1);
v___x_2208_ = l___private_Lean_Level_0__Lean_Level_geq_go(v_u_2180_, v_a_2206_);
if (v___x_2208_ == 0)
{
return v___x_2208_;
}
else
{
v_v_2181_ = v_a_2207_;
goto _start;
}
}
case 1:
{
switch(lean_obj_tag(v_u_2180_))
{
case 2:
{
lean_object* v_a_2210_; lean_object* v_a_2211_; 
v_a_2210_ = lean_ctor_get(v_u_2180_, 0);
v_a_2211_ = lean_ctor_get(v_u_2180_, 1);
v_u_u2081_2199_ = v_a_2210_;
v_u_u2082_2200_ = v_a_2211_;
v_v_2201_ = v_v_2181_;
goto v___jp_2198_;
}
case 3:
{
lean_object* v_a_2212_; 
v_a_2212_ = lean_ctor_get(v_u_2180_, 1);
v_u_2180_ = v_a_2212_;
goto _start;
}
case 1:
{
lean_object* v_a_2214_; lean_object* v_a_2215_; 
v_a_2214_ = lean_ctor_get(v_v_2181_, 0);
v_a_2215_ = lean_ctor_get(v_u_2180_, 0);
v_u_2180_ = v_a_2215_;
v_v_2181_ = v_a_2214_;
goto _start;
}
default: 
{
goto v___jp_2187_;
}
}
}
default: 
{
switch(lean_obj_tag(v_u_2180_))
{
case 2:
{
lean_object* v_a_2217_; lean_object* v_a_2218_; 
v_a_2217_ = lean_ctor_get(v_u_2180_, 0);
v_a_2218_ = lean_ctor_get(v_u_2180_, 1);
v_u_u2081_2199_ = v_a_2217_;
v_u_u2082_2200_ = v_a_2218_;
v_v_2201_ = v_v_2181_;
goto v___jp_2198_;
}
case 3:
{
lean_object* v_a_2219_; 
v_a_2219_ = lean_ctor_get(v_u_2180_, 1);
v_u_2180_ = v_a_2219_;
goto _start;
}
default: 
{
goto v___jp_2187_;
}
}
}
}
}
else
{
return v___x_2204_;
}
v___jp_2182_:
{
if (v___y_2183_ == 0)
{
return v___y_2183_;
}
else
{
lean_object* v___x_2184_; lean_object* v___x_2185_; uint8_t v___x_2186_; 
v___x_2184_ = l_Lean_Level_getOffset(v_v_2181_);
v___x_2185_ = l_Lean_Level_getOffset(v_u_2180_);
v___x_2186_ = lean_nat_dec_le(v___x_2184_, v___x_2185_);
lean_dec(v___x_2185_);
lean_dec(v___x_2184_);
return v___x_2186_;
}
}
v___jp_2187_:
{
if (lean_obj_tag(v_v_2181_) == 3)
{
lean_object* v_a_2188_; lean_object* v_a_2189_; uint8_t v___x_2190_; 
v_a_2188_ = lean_ctor_get(v_v_2181_, 0);
v_a_2189_ = lean_ctor_get(v_v_2181_, 1);
v___x_2190_ = l___private_Lean_Level_0__Lean_Level_geq_go(v_u_2180_, v_a_2188_);
if (v___x_2190_ == 0)
{
return v___x_2190_;
}
else
{
v_v_2181_ = v_a_2189_;
goto _start;
}
}
else
{
lean_object* v_v_x27_2192_; lean_object* v___x_2193_; uint8_t v___x_2194_; 
v_v_x27_2192_ = l_Lean_Level_getLevelOffset(v_v_2181_);
v___x_2193_ = l_Lean_Level_getLevelOffset(v_u_2180_);
v___x_2194_ = lean_level_eq(v___x_2193_, v_v_x27_2192_);
lean_dec(v___x_2193_);
if (v___x_2194_ == 0)
{
uint8_t v___x_2195_; 
v___x_2195_ = l_Lean_Level_isZero(v_v_x27_2192_);
lean_dec(v_v_x27_2192_);
v___y_2183_ = v___x_2195_;
goto v___jp_2182_;
}
else
{
lean_dec(v_v_x27_2192_);
v___y_2183_ = v___x_2194_;
goto v___jp_2182_;
}
}
}
v___jp_2196_:
{
if (v___y_2197_ == 0)
{
goto v___jp_2187_;
}
else
{
return v___y_2197_;
}
}
v___jp_2198_:
{
uint8_t v___x_2202_; 
v___x_2202_ = l___private_Lean_Level_0__Lean_Level_geq_go(v_u_u2081_2199_, v_v_2201_);
if (v___x_2202_ == 0)
{
uint8_t v___x_2203_; 
v___x_2203_ = l___private_Lean_Level_0__Lean_Level_geq_go(v_u_u2082_2200_, v_v_2201_);
v___y_2197_ = v___x_2203_;
goto v___jp_2196_;
}
else
{
v___y_2197_ = v___x_2202_;
goto v___jp_2196_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_geq_go___boxed(lean_object* v_u_2221_, lean_object* v_v_2222_){
_start:
{
uint8_t v_res_2223_; lean_object* v_r_2224_; 
v_res_2223_ = l___private_Lean_Level_0__Lean_Level_geq_go(v_u_2221_, v_v_2222_);
lean_dec(v_v_2222_);
lean_dec(v_u_2221_);
v_r_2224_ = lean_box(v_res_2223_);
return v_r_2224_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_geq_go_match__1_splitter___redArg(lean_object* v_u_2225_, lean_object* v_v_2226_, lean_object* v_h__1_2227_, lean_object* v_h__2_2228_, lean_object* v_h__3_2229_, lean_object* v_h__4_2230_, lean_object* v_h__5_2231_, lean_object* v_h__6_2232_){
_start:
{
switch(lean_obj_tag(v_v_2226_))
{
case 0:
{
lean_object* v___x_2233_; 
lean_dec(v_h__6_2232_);
lean_dec(v_h__5_2231_);
lean_dec(v_h__4_2230_);
lean_dec(v_h__3_2229_);
lean_dec(v_h__2_2228_);
v___x_2233_ = lean_apply_1(v_h__1_2227_, v_u_2225_);
return v___x_2233_;
}
case 2:
{
lean_object* v_a_2234_; lean_object* v_a_2235_; lean_object* v___x_2236_; 
lean_dec(v_h__6_2232_);
lean_dec(v_h__5_2231_);
lean_dec(v_h__4_2230_);
lean_dec(v_h__3_2229_);
lean_dec(v_h__1_2227_);
v_a_2234_ = lean_ctor_get(v_v_2226_, 0);
lean_inc(v_a_2234_);
v_a_2235_ = lean_ctor_get(v_v_2226_, 1);
lean_inc(v_a_2235_);
lean_dec_ref_known(v_v_2226_, 2);
v___x_2236_ = lean_apply_3(v_h__2_2228_, v_u_2225_, v_a_2234_, v_a_2235_);
return v___x_2236_;
}
case 1:
{
lean_dec(v_h__2_2228_);
lean_dec(v_h__1_2227_);
switch(lean_obj_tag(v_u_2225_))
{
case 2:
{
lean_object* v_a_2237_; lean_object* v_a_2238_; lean_object* v___x_2239_; 
lean_dec(v_h__6_2232_);
lean_dec(v_h__5_2231_);
lean_dec(v_h__4_2230_);
v_a_2237_ = lean_ctor_get(v_u_2225_, 0);
lean_inc(v_a_2237_);
v_a_2238_ = lean_ctor_get(v_u_2225_, 1);
lean_inc(v_a_2238_);
lean_dec_ref_known(v_u_2225_, 2);
v___x_2239_ = lean_apply_5(v_h__3_2229_, v_a_2237_, v_a_2238_, v_v_2226_, lean_box(0), lean_box(0));
return v___x_2239_;
}
case 3:
{
lean_object* v_a_2240_; lean_object* v_a_2241_; lean_object* v___x_2242_; 
lean_dec(v_h__6_2232_);
lean_dec(v_h__5_2231_);
lean_dec(v_h__3_2229_);
v_a_2240_ = lean_ctor_get(v_u_2225_, 0);
lean_inc(v_a_2240_);
v_a_2241_ = lean_ctor_get(v_u_2225_, 1);
lean_inc(v_a_2241_);
lean_dec_ref_known(v_u_2225_, 2);
v___x_2242_ = lean_apply_5(v_h__4_2230_, v_a_2240_, v_a_2241_, v_v_2226_, lean_box(0), lean_box(0));
return v___x_2242_;
}
case 1:
{
lean_object* v_a_2243_; lean_object* v_a_2244_; lean_object* v___x_2245_; 
lean_dec(v_h__6_2232_);
lean_dec(v_h__4_2230_);
lean_dec(v_h__3_2229_);
v_a_2243_ = lean_ctor_get(v_v_2226_, 0);
lean_inc(v_a_2243_);
lean_dec_ref_known(v_v_2226_, 1);
v_a_2244_ = lean_ctor_get(v_u_2225_, 0);
lean_inc(v_a_2244_);
lean_dec_ref_known(v_u_2225_, 1);
v___x_2245_ = lean_apply_2(v_h__5_2231_, v_a_2244_, v_a_2243_);
return v___x_2245_;
}
default: 
{
lean_object* v___x_2246_; 
lean_dec(v_h__5_2231_);
lean_dec(v_h__4_2230_);
lean_dec(v_h__3_2229_);
v___x_2246_ = lean_apply_7(v_h__6_2232_, v_u_2225_, v_v_2226_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_2246_;
}
}
}
default: 
{
lean_dec(v_h__5_2231_);
lean_dec(v_h__2_2228_);
lean_dec(v_h__1_2227_);
switch(lean_obj_tag(v_u_2225_))
{
case 2:
{
lean_object* v_a_2247_; lean_object* v_a_2248_; lean_object* v___x_2249_; 
lean_dec(v_h__6_2232_);
lean_dec(v_h__4_2230_);
v_a_2247_ = lean_ctor_get(v_u_2225_, 0);
lean_inc(v_a_2247_);
v_a_2248_ = lean_ctor_get(v_u_2225_, 1);
lean_inc(v_a_2248_);
lean_dec_ref_known(v_u_2225_, 2);
v___x_2249_ = lean_apply_5(v_h__3_2229_, v_a_2247_, v_a_2248_, v_v_2226_, lean_box(0), lean_box(0));
return v___x_2249_;
}
case 3:
{
lean_object* v_a_2250_; lean_object* v_a_2251_; lean_object* v___x_2252_; 
lean_dec(v_h__6_2232_);
lean_dec(v_h__3_2229_);
v_a_2250_ = lean_ctor_get(v_u_2225_, 0);
lean_inc(v_a_2250_);
v_a_2251_ = lean_ctor_get(v_u_2225_, 1);
lean_inc(v_a_2251_);
lean_dec_ref_known(v_u_2225_, 2);
v___x_2252_ = lean_apply_5(v_h__4_2230_, v_a_2250_, v_a_2251_, v_v_2226_, lean_box(0), lean_box(0));
return v___x_2252_;
}
default: 
{
lean_object* v___x_2253_; 
lean_dec(v_h__4_2230_);
lean_dec(v_h__3_2229_);
v___x_2253_ = lean_apply_7(v_h__6_2232_, v_u_2225_, v_v_2226_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_2253_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_geq_go_match__1_splitter(lean_object* v_motive_2254_, lean_object* v_u_2255_, lean_object* v_v_2256_, lean_object* v_h__1_2257_, lean_object* v_h__2_2258_, lean_object* v_h__3_2259_, lean_object* v_h__4_2260_, lean_object* v_h__5_2261_, lean_object* v_h__6_2262_){
_start:
{
switch(lean_obj_tag(v_v_2256_))
{
case 0:
{
lean_object* v___x_2263_; 
lean_dec(v_h__6_2262_);
lean_dec(v_h__5_2261_);
lean_dec(v_h__4_2260_);
lean_dec(v_h__3_2259_);
lean_dec(v_h__2_2258_);
v___x_2263_ = lean_apply_1(v_h__1_2257_, v_u_2255_);
return v___x_2263_;
}
case 2:
{
lean_object* v_a_2264_; lean_object* v_a_2265_; lean_object* v___x_2266_; 
lean_dec(v_h__6_2262_);
lean_dec(v_h__5_2261_);
lean_dec(v_h__4_2260_);
lean_dec(v_h__3_2259_);
lean_dec(v_h__1_2257_);
v_a_2264_ = lean_ctor_get(v_v_2256_, 0);
lean_inc(v_a_2264_);
v_a_2265_ = lean_ctor_get(v_v_2256_, 1);
lean_inc(v_a_2265_);
lean_dec_ref_known(v_v_2256_, 2);
v___x_2266_ = lean_apply_3(v_h__2_2258_, v_u_2255_, v_a_2264_, v_a_2265_);
return v___x_2266_;
}
case 1:
{
lean_dec(v_h__2_2258_);
lean_dec(v_h__1_2257_);
switch(lean_obj_tag(v_u_2255_))
{
case 2:
{
lean_object* v_a_2267_; lean_object* v_a_2268_; lean_object* v___x_2269_; 
lean_dec(v_h__6_2262_);
lean_dec(v_h__5_2261_);
lean_dec(v_h__4_2260_);
v_a_2267_ = lean_ctor_get(v_u_2255_, 0);
lean_inc(v_a_2267_);
v_a_2268_ = lean_ctor_get(v_u_2255_, 1);
lean_inc(v_a_2268_);
lean_dec_ref_known(v_u_2255_, 2);
v___x_2269_ = lean_apply_5(v_h__3_2259_, v_a_2267_, v_a_2268_, v_v_2256_, lean_box(0), lean_box(0));
return v___x_2269_;
}
case 3:
{
lean_object* v_a_2270_; lean_object* v_a_2271_; lean_object* v___x_2272_; 
lean_dec(v_h__6_2262_);
lean_dec(v_h__5_2261_);
lean_dec(v_h__3_2259_);
v_a_2270_ = lean_ctor_get(v_u_2255_, 0);
lean_inc(v_a_2270_);
v_a_2271_ = lean_ctor_get(v_u_2255_, 1);
lean_inc(v_a_2271_);
lean_dec_ref_known(v_u_2255_, 2);
v___x_2272_ = lean_apply_5(v_h__4_2260_, v_a_2270_, v_a_2271_, v_v_2256_, lean_box(0), lean_box(0));
return v___x_2272_;
}
case 1:
{
lean_object* v_a_2273_; lean_object* v_a_2274_; lean_object* v___x_2275_; 
lean_dec(v_h__6_2262_);
lean_dec(v_h__4_2260_);
lean_dec(v_h__3_2259_);
v_a_2273_ = lean_ctor_get(v_v_2256_, 0);
lean_inc(v_a_2273_);
lean_dec_ref_known(v_v_2256_, 1);
v_a_2274_ = lean_ctor_get(v_u_2255_, 0);
lean_inc(v_a_2274_);
lean_dec_ref_known(v_u_2255_, 1);
v___x_2275_ = lean_apply_2(v_h__5_2261_, v_a_2274_, v_a_2273_);
return v___x_2275_;
}
default: 
{
lean_object* v___x_2276_; 
lean_dec(v_h__5_2261_);
lean_dec(v_h__4_2260_);
lean_dec(v_h__3_2259_);
v___x_2276_ = lean_apply_7(v_h__6_2262_, v_u_2255_, v_v_2256_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_2276_;
}
}
}
default: 
{
lean_dec(v_h__5_2261_);
lean_dec(v_h__2_2258_);
lean_dec(v_h__1_2257_);
switch(lean_obj_tag(v_u_2255_))
{
case 2:
{
lean_object* v_a_2277_; lean_object* v_a_2278_; lean_object* v___x_2279_; 
lean_dec(v_h__6_2262_);
lean_dec(v_h__4_2260_);
v_a_2277_ = lean_ctor_get(v_u_2255_, 0);
lean_inc(v_a_2277_);
v_a_2278_ = lean_ctor_get(v_u_2255_, 1);
lean_inc(v_a_2278_);
lean_dec_ref_known(v_u_2255_, 2);
v___x_2279_ = lean_apply_5(v_h__3_2259_, v_a_2277_, v_a_2278_, v_v_2256_, lean_box(0), lean_box(0));
return v___x_2279_;
}
case 3:
{
lean_object* v_a_2280_; lean_object* v_a_2281_; lean_object* v___x_2282_; 
lean_dec(v_h__6_2262_);
lean_dec(v_h__3_2259_);
v_a_2280_ = lean_ctor_get(v_u_2255_, 0);
lean_inc(v_a_2280_);
v_a_2281_ = lean_ctor_get(v_u_2255_, 1);
lean_inc(v_a_2281_);
lean_dec_ref_known(v_u_2255_, 2);
v___x_2282_ = lean_apply_5(v_h__4_2260_, v_a_2280_, v_a_2281_, v_v_2256_, lean_box(0), lean_box(0));
return v___x_2282_;
}
default: 
{
lean_object* v___x_2283_; 
lean_dec(v_h__4_2260_);
lean_dec(v_h__3_2259_);
v___x_2283_ = lean_apply_7(v_h__6_2262_, v_u_2255_, v_v_2256_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_2283_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_isIMax_match__1_splitter___redArg(lean_object* v_x_2284_, lean_object* v_h__1_2285_, lean_object* v_h__2_2286_){
_start:
{
if (lean_obj_tag(v_x_2284_) == 3)
{
lean_object* v_a_2287_; lean_object* v_a_2288_; lean_object* v___x_2289_; 
lean_dec(v_h__2_2286_);
v_a_2287_ = lean_ctor_get(v_x_2284_, 0);
lean_inc(v_a_2287_);
v_a_2288_ = lean_ctor_get(v_x_2284_, 1);
lean_inc(v_a_2288_);
lean_dec_ref_known(v_x_2284_, 2);
v___x_2289_ = lean_apply_2(v_h__1_2285_, v_a_2287_, v_a_2288_);
return v___x_2289_;
}
else
{
lean_object* v___x_2290_; 
lean_dec(v_h__1_2285_);
v___x_2290_ = lean_apply_2(v_h__2_2286_, v_x_2284_, lean_box(0));
return v___x_2290_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_isIMax_match__1_splitter(lean_object* v_motive_2291_, lean_object* v_x_2292_, lean_object* v_h__1_2293_, lean_object* v_h__2_2294_){
_start:
{
if (lean_obj_tag(v_x_2292_) == 3)
{
lean_object* v_a_2295_; lean_object* v_a_2296_; lean_object* v___x_2297_; 
lean_dec(v_h__2_2294_);
v_a_2295_ = lean_ctor_get(v_x_2292_, 0);
lean_inc(v_a_2295_);
v_a_2296_ = lean_ctor_get(v_x_2292_, 1);
lean_inc(v_a_2296_);
lean_dec_ref_known(v_x_2292_, 2);
v___x_2297_ = lean_apply_2(v_h__1_2293_, v_a_2295_, v_a_2296_);
return v___x_2297_;
}
else
{
lean_object* v___x_2298_; 
lean_dec(v_h__1_2293_);
v___x_2298_ = lean_apply_2(v_h__2_2294_, v_x_2292_, lean_box(0));
return v___x_2298_;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Level_geq(lean_object* v_u_2299_, lean_object* v_v_2300_){
_start:
{
lean_object* v___x_2301_; lean_object* v___x_2302_; uint8_t v___x_2303_; 
v___x_2301_ = l_Lean_Level_normalize(v_u_2299_);
v___x_2302_ = l_Lean_Level_normalize(v_v_2300_);
v___x_2303_ = l___private_Lean_Level_0__Lean_Level_geq_go(v___x_2301_, v___x_2302_);
lean_dec(v___x_2302_);
lean_dec(v___x_2301_);
return v___x_2303_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_geq___boxed(lean_object* v_u_2304_, lean_object* v_v_2305_){
_start:
{
uint8_t v_res_2306_; lean_object* v_r_2307_; 
v_res_2306_ = l_Lean_Level_geq(v_u_2304_, v_v_2305_);
lean_dec(v_v_2305_);
lean_dec(v_u_2304_);
v_r_2307_ = lean_box(v_res_2306_);
return v_r_2307_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Level_collectMVars_spec__1___redArg(lean_object* v_k_2308_, lean_object* v_v_2309_, lean_object* v_t_2310_){
_start:
{
if (lean_obj_tag(v_t_2310_) == 0)
{
lean_object* v_size_2311_; lean_object* v_k_2312_; lean_object* v_v_2313_; lean_object* v_l_2314_; lean_object* v_r_2315_; lean_object* v___x_2317_; uint8_t v_isShared_2318_; uint8_t v_isSharedCheck_2595_; 
v_size_2311_ = lean_ctor_get(v_t_2310_, 0);
v_k_2312_ = lean_ctor_get(v_t_2310_, 1);
v_v_2313_ = lean_ctor_get(v_t_2310_, 2);
v_l_2314_ = lean_ctor_get(v_t_2310_, 3);
v_r_2315_ = lean_ctor_get(v_t_2310_, 4);
v_isSharedCheck_2595_ = !lean_is_exclusive(v_t_2310_);
if (v_isSharedCheck_2595_ == 0)
{
v___x_2317_ = v_t_2310_;
v_isShared_2318_ = v_isSharedCheck_2595_;
goto v_resetjp_2316_;
}
else
{
lean_inc(v_r_2315_);
lean_inc(v_l_2314_);
lean_inc(v_v_2313_);
lean_inc(v_k_2312_);
lean_inc(v_size_2311_);
lean_dec(v_t_2310_);
v___x_2317_ = lean_box(0);
v_isShared_2318_ = v_isSharedCheck_2595_;
goto v_resetjp_2316_;
}
v_resetjp_2316_:
{
uint8_t v___x_2319_; 
v___x_2319_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2308_, v_k_2312_);
switch(v___x_2319_)
{
case 0:
{
lean_object* v_impl_2320_; lean_object* v___x_2321_; 
lean_dec(v_size_2311_);
v_impl_2320_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Level_collectMVars_spec__1___redArg(v_k_2308_, v_v_2309_, v_l_2314_);
v___x_2321_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_2315_) == 0)
{
lean_object* v_size_2322_; lean_object* v_size_2323_; lean_object* v_k_2324_; lean_object* v_v_2325_; lean_object* v_l_2326_; lean_object* v_r_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; uint8_t v___x_2330_; 
v_size_2322_ = lean_ctor_get(v_r_2315_, 0);
v_size_2323_ = lean_ctor_get(v_impl_2320_, 0);
lean_inc(v_size_2323_);
v_k_2324_ = lean_ctor_get(v_impl_2320_, 1);
lean_inc(v_k_2324_);
v_v_2325_ = lean_ctor_get(v_impl_2320_, 2);
lean_inc(v_v_2325_);
v_l_2326_ = lean_ctor_get(v_impl_2320_, 3);
lean_inc(v_l_2326_);
v_r_2327_ = lean_ctor_get(v_impl_2320_, 4);
lean_inc(v_r_2327_);
v___x_2328_ = lean_unsigned_to_nat(3u);
v___x_2329_ = lean_nat_mul(v___x_2328_, v_size_2322_);
v___x_2330_ = lean_nat_dec_lt(v___x_2329_, v_size_2323_);
lean_dec(v___x_2329_);
if (v___x_2330_ == 0)
{
lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2334_; 
lean_dec(v_r_2327_);
lean_dec(v_l_2326_);
lean_dec(v_v_2325_);
lean_dec(v_k_2324_);
v___x_2331_ = lean_nat_add(v___x_2321_, v_size_2323_);
lean_dec(v_size_2323_);
v___x_2332_ = lean_nat_add(v___x_2331_, v_size_2322_);
lean_dec(v___x_2331_);
if (v_isShared_2318_ == 0)
{
lean_ctor_set(v___x_2317_, 3, v_impl_2320_);
lean_ctor_set(v___x_2317_, 0, v___x_2332_);
v___x_2334_ = v___x_2317_;
goto v_reusejp_2333_;
}
else
{
lean_object* v_reuseFailAlloc_2335_; 
v_reuseFailAlloc_2335_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2335_, 0, v___x_2332_);
lean_ctor_set(v_reuseFailAlloc_2335_, 1, v_k_2312_);
lean_ctor_set(v_reuseFailAlloc_2335_, 2, v_v_2313_);
lean_ctor_set(v_reuseFailAlloc_2335_, 3, v_impl_2320_);
lean_ctor_set(v_reuseFailAlloc_2335_, 4, v_r_2315_);
v___x_2334_ = v_reuseFailAlloc_2335_;
goto v_reusejp_2333_;
}
v_reusejp_2333_:
{
return v___x_2334_;
}
}
else
{
lean_object* v___x_2337_; uint8_t v_isShared_2338_; uint8_t v_isSharedCheck_2401_; 
v_isSharedCheck_2401_ = !lean_is_exclusive(v_impl_2320_);
if (v_isSharedCheck_2401_ == 0)
{
lean_object* v_unused_2402_; lean_object* v_unused_2403_; lean_object* v_unused_2404_; lean_object* v_unused_2405_; lean_object* v_unused_2406_; 
v_unused_2402_ = lean_ctor_get(v_impl_2320_, 4);
lean_dec(v_unused_2402_);
v_unused_2403_ = lean_ctor_get(v_impl_2320_, 3);
lean_dec(v_unused_2403_);
v_unused_2404_ = lean_ctor_get(v_impl_2320_, 2);
lean_dec(v_unused_2404_);
v_unused_2405_ = lean_ctor_get(v_impl_2320_, 1);
lean_dec(v_unused_2405_);
v_unused_2406_ = lean_ctor_get(v_impl_2320_, 0);
lean_dec(v_unused_2406_);
v___x_2337_ = v_impl_2320_;
v_isShared_2338_ = v_isSharedCheck_2401_;
goto v_resetjp_2336_;
}
else
{
lean_dec(v_impl_2320_);
v___x_2337_ = lean_box(0);
v_isShared_2338_ = v_isSharedCheck_2401_;
goto v_resetjp_2336_;
}
v_resetjp_2336_:
{
lean_object* v_size_2339_; lean_object* v_size_2340_; lean_object* v_k_2341_; lean_object* v_v_2342_; lean_object* v_l_2343_; lean_object* v_r_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; uint8_t v___x_2347_; 
v_size_2339_ = lean_ctor_get(v_l_2326_, 0);
v_size_2340_ = lean_ctor_get(v_r_2327_, 0);
v_k_2341_ = lean_ctor_get(v_r_2327_, 1);
v_v_2342_ = lean_ctor_get(v_r_2327_, 2);
v_l_2343_ = lean_ctor_get(v_r_2327_, 3);
v_r_2344_ = lean_ctor_get(v_r_2327_, 4);
v___x_2345_ = lean_unsigned_to_nat(2u);
v___x_2346_ = lean_nat_mul(v___x_2345_, v_size_2339_);
v___x_2347_ = lean_nat_dec_lt(v_size_2340_, v___x_2346_);
lean_dec(v___x_2346_);
if (v___x_2347_ == 0)
{
lean_object* v___x_2349_; uint8_t v_isShared_2350_; uint8_t v_isSharedCheck_2376_; 
lean_inc(v_r_2344_);
lean_inc(v_l_2343_);
lean_inc(v_v_2342_);
lean_inc(v_k_2341_);
v_isSharedCheck_2376_ = !lean_is_exclusive(v_r_2327_);
if (v_isSharedCheck_2376_ == 0)
{
lean_object* v_unused_2377_; lean_object* v_unused_2378_; lean_object* v_unused_2379_; lean_object* v_unused_2380_; lean_object* v_unused_2381_; 
v_unused_2377_ = lean_ctor_get(v_r_2327_, 4);
lean_dec(v_unused_2377_);
v_unused_2378_ = lean_ctor_get(v_r_2327_, 3);
lean_dec(v_unused_2378_);
v_unused_2379_ = lean_ctor_get(v_r_2327_, 2);
lean_dec(v_unused_2379_);
v_unused_2380_ = lean_ctor_get(v_r_2327_, 1);
lean_dec(v_unused_2380_);
v_unused_2381_ = lean_ctor_get(v_r_2327_, 0);
lean_dec(v_unused_2381_);
v___x_2349_ = v_r_2327_;
v_isShared_2350_ = v_isSharedCheck_2376_;
goto v_resetjp_2348_;
}
else
{
lean_dec(v_r_2327_);
v___x_2349_ = lean_box(0);
v_isShared_2350_ = v_isSharedCheck_2376_;
goto v_resetjp_2348_;
}
v_resetjp_2348_:
{
lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___y_2354_; lean_object* v___y_2355_; lean_object* v___y_2356_; lean_object* v___x_2364_; lean_object* v___y_2366_; 
v___x_2351_ = lean_nat_add(v___x_2321_, v_size_2323_);
lean_dec(v_size_2323_);
v___x_2352_ = lean_nat_add(v___x_2351_, v_size_2322_);
lean_dec(v___x_2351_);
v___x_2364_ = lean_nat_add(v___x_2321_, v_size_2339_);
if (lean_obj_tag(v_l_2343_) == 0)
{
lean_object* v_size_2374_; 
v_size_2374_ = lean_ctor_get(v_l_2343_, 0);
lean_inc(v_size_2374_);
v___y_2366_ = v_size_2374_;
goto v___jp_2365_;
}
else
{
lean_object* v___x_2375_; 
v___x_2375_ = lean_unsigned_to_nat(0u);
v___y_2366_ = v___x_2375_;
goto v___jp_2365_;
}
v___jp_2353_:
{
lean_object* v___x_2357_; lean_object* v___x_2359_; 
v___x_2357_ = lean_nat_add(v___y_2355_, v___y_2356_);
lean_dec(v___y_2356_);
lean_dec(v___y_2355_);
if (v_isShared_2350_ == 0)
{
lean_ctor_set(v___x_2349_, 4, v_r_2315_);
lean_ctor_set(v___x_2349_, 3, v_r_2344_);
lean_ctor_set(v___x_2349_, 2, v_v_2313_);
lean_ctor_set(v___x_2349_, 1, v_k_2312_);
lean_ctor_set(v___x_2349_, 0, v___x_2357_);
v___x_2359_ = v___x_2349_;
goto v_reusejp_2358_;
}
else
{
lean_object* v_reuseFailAlloc_2363_; 
v_reuseFailAlloc_2363_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2363_, 0, v___x_2357_);
lean_ctor_set(v_reuseFailAlloc_2363_, 1, v_k_2312_);
lean_ctor_set(v_reuseFailAlloc_2363_, 2, v_v_2313_);
lean_ctor_set(v_reuseFailAlloc_2363_, 3, v_r_2344_);
lean_ctor_set(v_reuseFailAlloc_2363_, 4, v_r_2315_);
v___x_2359_ = v_reuseFailAlloc_2363_;
goto v_reusejp_2358_;
}
v_reusejp_2358_:
{
lean_object* v___x_2361_; 
if (v_isShared_2338_ == 0)
{
lean_ctor_set(v___x_2337_, 4, v___x_2359_);
lean_ctor_set(v___x_2337_, 3, v___y_2354_);
lean_ctor_set(v___x_2337_, 2, v_v_2342_);
lean_ctor_set(v___x_2337_, 1, v_k_2341_);
lean_ctor_set(v___x_2337_, 0, v___x_2352_);
v___x_2361_ = v___x_2337_;
goto v_reusejp_2360_;
}
else
{
lean_object* v_reuseFailAlloc_2362_; 
v_reuseFailAlloc_2362_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2362_, 0, v___x_2352_);
lean_ctor_set(v_reuseFailAlloc_2362_, 1, v_k_2341_);
lean_ctor_set(v_reuseFailAlloc_2362_, 2, v_v_2342_);
lean_ctor_set(v_reuseFailAlloc_2362_, 3, v___y_2354_);
lean_ctor_set(v_reuseFailAlloc_2362_, 4, v___x_2359_);
v___x_2361_ = v_reuseFailAlloc_2362_;
goto v_reusejp_2360_;
}
v_reusejp_2360_:
{
return v___x_2361_;
}
}
}
v___jp_2365_:
{
lean_object* v___x_2367_; lean_object* v___x_2369_; 
v___x_2367_ = lean_nat_add(v___x_2364_, v___y_2366_);
lean_dec(v___y_2366_);
lean_dec(v___x_2364_);
if (v_isShared_2318_ == 0)
{
lean_ctor_set(v___x_2317_, 4, v_l_2343_);
lean_ctor_set(v___x_2317_, 3, v_l_2326_);
lean_ctor_set(v___x_2317_, 2, v_v_2325_);
lean_ctor_set(v___x_2317_, 1, v_k_2324_);
lean_ctor_set(v___x_2317_, 0, v___x_2367_);
v___x_2369_ = v___x_2317_;
goto v_reusejp_2368_;
}
else
{
lean_object* v_reuseFailAlloc_2373_; 
v_reuseFailAlloc_2373_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2373_, 0, v___x_2367_);
lean_ctor_set(v_reuseFailAlloc_2373_, 1, v_k_2324_);
lean_ctor_set(v_reuseFailAlloc_2373_, 2, v_v_2325_);
lean_ctor_set(v_reuseFailAlloc_2373_, 3, v_l_2326_);
lean_ctor_set(v_reuseFailAlloc_2373_, 4, v_l_2343_);
v___x_2369_ = v_reuseFailAlloc_2373_;
goto v_reusejp_2368_;
}
v_reusejp_2368_:
{
lean_object* v___x_2370_; 
v___x_2370_ = lean_nat_add(v___x_2321_, v_size_2322_);
if (lean_obj_tag(v_r_2344_) == 0)
{
lean_object* v_size_2371_; 
v_size_2371_ = lean_ctor_get(v_r_2344_, 0);
lean_inc(v_size_2371_);
v___y_2354_ = v___x_2369_;
v___y_2355_ = v___x_2370_;
v___y_2356_ = v_size_2371_;
goto v___jp_2353_;
}
else
{
lean_object* v___x_2372_; 
v___x_2372_ = lean_unsigned_to_nat(0u);
v___y_2354_ = v___x_2369_;
v___y_2355_ = v___x_2370_;
v___y_2356_ = v___x_2372_;
goto v___jp_2353_;
}
}
}
}
}
else
{
lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2387_; 
lean_del_object(v___x_2317_);
v___x_2382_ = lean_nat_add(v___x_2321_, v_size_2323_);
lean_dec(v_size_2323_);
v___x_2383_ = lean_nat_add(v___x_2382_, v_size_2322_);
lean_dec(v___x_2382_);
v___x_2384_ = lean_nat_add(v___x_2321_, v_size_2322_);
v___x_2385_ = lean_nat_add(v___x_2384_, v_size_2340_);
lean_dec(v___x_2384_);
lean_inc_ref(v_r_2315_);
if (v_isShared_2338_ == 0)
{
lean_ctor_set(v___x_2337_, 4, v_r_2315_);
lean_ctor_set(v___x_2337_, 3, v_r_2327_);
lean_ctor_set(v___x_2337_, 2, v_v_2313_);
lean_ctor_set(v___x_2337_, 1, v_k_2312_);
lean_ctor_set(v___x_2337_, 0, v___x_2385_);
v___x_2387_ = v___x_2337_;
goto v_reusejp_2386_;
}
else
{
lean_object* v_reuseFailAlloc_2400_; 
v_reuseFailAlloc_2400_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2400_, 0, v___x_2385_);
lean_ctor_set(v_reuseFailAlloc_2400_, 1, v_k_2312_);
lean_ctor_set(v_reuseFailAlloc_2400_, 2, v_v_2313_);
lean_ctor_set(v_reuseFailAlloc_2400_, 3, v_r_2327_);
lean_ctor_set(v_reuseFailAlloc_2400_, 4, v_r_2315_);
v___x_2387_ = v_reuseFailAlloc_2400_;
goto v_reusejp_2386_;
}
v_reusejp_2386_:
{
lean_object* v___x_2389_; uint8_t v_isShared_2390_; uint8_t v_isSharedCheck_2394_; 
v_isSharedCheck_2394_ = !lean_is_exclusive(v_r_2315_);
if (v_isSharedCheck_2394_ == 0)
{
lean_object* v_unused_2395_; lean_object* v_unused_2396_; lean_object* v_unused_2397_; lean_object* v_unused_2398_; lean_object* v_unused_2399_; 
v_unused_2395_ = lean_ctor_get(v_r_2315_, 4);
lean_dec(v_unused_2395_);
v_unused_2396_ = lean_ctor_get(v_r_2315_, 3);
lean_dec(v_unused_2396_);
v_unused_2397_ = lean_ctor_get(v_r_2315_, 2);
lean_dec(v_unused_2397_);
v_unused_2398_ = lean_ctor_get(v_r_2315_, 1);
lean_dec(v_unused_2398_);
v_unused_2399_ = lean_ctor_get(v_r_2315_, 0);
lean_dec(v_unused_2399_);
v___x_2389_ = v_r_2315_;
v_isShared_2390_ = v_isSharedCheck_2394_;
goto v_resetjp_2388_;
}
else
{
lean_dec(v_r_2315_);
v___x_2389_ = lean_box(0);
v_isShared_2390_ = v_isSharedCheck_2394_;
goto v_resetjp_2388_;
}
v_resetjp_2388_:
{
lean_object* v___x_2392_; 
if (v_isShared_2390_ == 0)
{
lean_ctor_set(v___x_2389_, 4, v___x_2387_);
lean_ctor_set(v___x_2389_, 3, v_l_2326_);
lean_ctor_set(v___x_2389_, 2, v_v_2325_);
lean_ctor_set(v___x_2389_, 1, v_k_2324_);
lean_ctor_set(v___x_2389_, 0, v___x_2383_);
v___x_2392_ = v___x_2389_;
goto v_reusejp_2391_;
}
else
{
lean_object* v_reuseFailAlloc_2393_; 
v_reuseFailAlloc_2393_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2393_, 0, v___x_2383_);
lean_ctor_set(v_reuseFailAlloc_2393_, 1, v_k_2324_);
lean_ctor_set(v_reuseFailAlloc_2393_, 2, v_v_2325_);
lean_ctor_set(v_reuseFailAlloc_2393_, 3, v_l_2326_);
lean_ctor_set(v_reuseFailAlloc_2393_, 4, v___x_2387_);
v___x_2392_ = v_reuseFailAlloc_2393_;
goto v_reusejp_2391_;
}
v_reusejp_2391_:
{
return v___x_2392_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_2407_; 
v_l_2407_ = lean_ctor_get(v_impl_2320_, 3);
lean_inc(v_l_2407_);
if (lean_obj_tag(v_l_2407_) == 0)
{
lean_object* v_r_2408_; lean_object* v_k_2409_; lean_object* v_v_2410_; lean_object* v___x_2412_; uint8_t v_isShared_2413_; uint8_t v_isSharedCheck_2421_; 
v_r_2408_ = lean_ctor_get(v_impl_2320_, 4);
v_k_2409_ = lean_ctor_get(v_impl_2320_, 1);
v_v_2410_ = lean_ctor_get(v_impl_2320_, 2);
v_isSharedCheck_2421_ = !lean_is_exclusive(v_impl_2320_);
if (v_isSharedCheck_2421_ == 0)
{
lean_object* v_unused_2422_; lean_object* v_unused_2423_; 
v_unused_2422_ = lean_ctor_get(v_impl_2320_, 3);
lean_dec(v_unused_2422_);
v_unused_2423_ = lean_ctor_get(v_impl_2320_, 0);
lean_dec(v_unused_2423_);
v___x_2412_ = v_impl_2320_;
v_isShared_2413_ = v_isSharedCheck_2421_;
goto v_resetjp_2411_;
}
else
{
lean_inc(v_r_2408_);
lean_inc(v_v_2410_);
lean_inc(v_k_2409_);
lean_dec(v_impl_2320_);
v___x_2412_ = lean_box(0);
v_isShared_2413_ = v_isSharedCheck_2421_;
goto v_resetjp_2411_;
}
v_resetjp_2411_:
{
lean_object* v___x_2414_; lean_object* v___x_2416_; 
v___x_2414_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_2408_);
if (v_isShared_2413_ == 0)
{
lean_ctor_set(v___x_2412_, 3, v_r_2408_);
lean_ctor_set(v___x_2412_, 2, v_v_2313_);
lean_ctor_set(v___x_2412_, 1, v_k_2312_);
lean_ctor_set(v___x_2412_, 0, v___x_2321_);
v___x_2416_ = v___x_2412_;
goto v_reusejp_2415_;
}
else
{
lean_object* v_reuseFailAlloc_2420_; 
v_reuseFailAlloc_2420_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2420_, 0, v___x_2321_);
lean_ctor_set(v_reuseFailAlloc_2420_, 1, v_k_2312_);
lean_ctor_set(v_reuseFailAlloc_2420_, 2, v_v_2313_);
lean_ctor_set(v_reuseFailAlloc_2420_, 3, v_r_2408_);
lean_ctor_set(v_reuseFailAlloc_2420_, 4, v_r_2408_);
v___x_2416_ = v_reuseFailAlloc_2420_;
goto v_reusejp_2415_;
}
v_reusejp_2415_:
{
lean_object* v___x_2418_; 
if (v_isShared_2318_ == 0)
{
lean_ctor_set(v___x_2317_, 4, v___x_2416_);
lean_ctor_set(v___x_2317_, 3, v_l_2407_);
lean_ctor_set(v___x_2317_, 2, v_v_2410_);
lean_ctor_set(v___x_2317_, 1, v_k_2409_);
lean_ctor_set(v___x_2317_, 0, v___x_2414_);
v___x_2418_ = v___x_2317_;
goto v_reusejp_2417_;
}
else
{
lean_object* v_reuseFailAlloc_2419_; 
v_reuseFailAlloc_2419_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2419_, 0, v___x_2414_);
lean_ctor_set(v_reuseFailAlloc_2419_, 1, v_k_2409_);
lean_ctor_set(v_reuseFailAlloc_2419_, 2, v_v_2410_);
lean_ctor_set(v_reuseFailAlloc_2419_, 3, v_l_2407_);
lean_ctor_set(v_reuseFailAlloc_2419_, 4, v___x_2416_);
v___x_2418_ = v_reuseFailAlloc_2419_;
goto v_reusejp_2417_;
}
v_reusejp_2417_:
{
return v___x_2418_;
}
}
}
}
else
{
lean_object* v_r_2424_; 
v_r_2424_ = lean_ctor_get(v_impl_2320_, 4);
lean_inc(v_r_2424_);
if (lean_obj_tag(v_r_2424_) == 0)
{
lean_object* v_k_2425_; lean_object* v_v_2426_; lean_object* v___x_2428_; uint8_t v_isShared_2429_; uint8_t v_isSharedCheck_2449_; 
v_k_2425_ = lean_ctor_get(v_impl_2320_, 1);
v_v_2426_ = lean_ctor_get(v_impl_2320_, 2);
v_isSharedCheck_2449_ = !lean_is_exclusive(v_impl_2320_);
if (v_isSharedCheck_2449_ == 0)
{
lean_object* v_unused_2450_; lean_object* v_unused_2451_; lean_object* v_unused_2452_; 
v_unused_2450_ = lean_ctor_get(v_impl_2320_, 4);
lean_dec(v_unused_2450_);
v_unused_2451_ = lean_ctor_get(v_impl_2320_, 3);
lean_dec(v_unused_2451_);
v_unused_2452_ = lean_ctor_get(v_impl_2320_, 0);
lean_dec(v_unused_2452_);
v___x_2428_ = v_impl_2320_;
v_isShared_2429_ = v_isSharedCheck_2449_;
goto v_resetjp_2427_;
}
else
{
lean_inc(v_v_2426_);
lean_inc(v_k_2425_);
lean_dec(v_impl_2320_);
v___x_2428_ = lean_box(0);
v_isShared_2429_ = v_isSharedCheck_2449_;
goto v_resetjp_2427_;
}
v_resetjp_2427_:
{
lean_object* v_k_2430_; lean_object* v_v_2431_; lean_object* v___x_2433_; uint8_t v_isShared_2434_; uint8_t v_isSharedCheck_2445_; 
v_k_2430_ = lean_ctor_get(v_r_2424_, 1);
v_v_2431_ = lean_ctor_get(v_r_2424_, 2);
v_isSharedCheck_2445_ = !lean_is_exclusive(v_r_2424_);
if (v_isSharedCheck_2445_ == 0)
{
lean_object* v_unused_2446_; lean_object* v_unused_2447_; lean_object* v_unused_2448_; 
v_unused_2446_ = lean_ctor_get(v_r_2424_, 4);
lean_dec(v_unused_2446_);
v_unused_2447_ = lean_ctor_get(v_r_2424_, 3);
lean_dec(v_unused_2447_);
v_unused_2448_ = lean_ctor_get(v_r_2424_, 0);
lean_dec(v_unused_2448_);
v___x_2433_ = v_r_2424_;
v_isShared_2434_ = v_isSharedCheck_2445_;
goto v_resetjp_2432_;
}
else
{
lean_inc(v_v_2431_);
lean_inc(v_k_2430_);
lean_dec(v_r_2424_);
v___x_2433_ = lean_box(0);
v_isShared_2434_ = v_isSharedCheck_2445_;
goto v_resetjp_2432_;
}
v_resetjp_2432_:
{
lean_object* v___x_2435_; lean_object* v___x_2437_; 
v___x_2435_ = lean_unsigned_to_nat(3u);
if (v_isShared_2434_ == 0)
{
lean_ctor_set(v___x_2433_, 4, v_l_2407_);
lean_ctor_set(v___x_2433_, 3, v_l_2407_);
lean_ctor_set(v___x_2433_, 2, v_v_2426_);
lean_ctor_set(v___x_2433_, 1, v_k_2425_);
lean_ctor_set(v___x_2433_, 0, v___x_2321_);
v___x_2437_ = v___x_2433_;
goto v_reusejp_2436_;
}
else
{
lean_object* v_reuseFailAlloc_2444_; 
v_reuseFailAlloc_2444_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2444_, 0, v___x_2321_);
lean_ctor_set(v_reuseFailAlloc_2444_, 1, v_k_2425_);
lean_ctor_set(v_reuseFailAlloc_2444_, 2, v_v_2426_);
lean_ctor_set(v_reuseFailAlloc_2444_, 3, v_l_2407_);
lean_ctor_set(v_reuseFailAlloc_2444_, 4, v_l_2407_);
v___x_2437_ = v_reuseFailAlloc_2444_;
goto v_reusejp_2436_;
}
v_reusejp_2436_:
{
lean_object* v___x_2439_; 
if (v_isShared_2429_ == 0)
{
lean_ctor_set(v___x_2428_, 4, v_l_2407_);
lean_ctor_set(v___x_2428_, 2, v_v_2313_);
lean_ctor_set(v___x_2428_, 1, v_k_2312_);
lean_ctor_set(v___x_2428_, 0, v___x_2321_);
v___x_2439_ = v___x_2428_;
goto v_reusejp_2438_;
}
else
{
lean_object* v_reuseFailAlloc_2443_; 
v_reuseFailAlloc_2443_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2443_, 0, v___x_2321_);
lean_ctor_set(v_reuseFailAlloc_2443_, 1, v_k_2312_);
lean_ctor_set(v_reuseFailAlloc_2443_, 2, v_v_2313_);
lean_ctor_set(v_reuseFailAlloc_2443_, 3, v_l_2407_);
lean_ctor_set(v_reuseFailAlloc_2443_, 4, v_l_2407_);
v___x_2439_ = v_reuseFailAlloc_2443_;
goto v_reusejp_2438_;
}
v_reusejp_2438_:
{
lean_object* v___x_2441_; 
if (v_isShared_2318_ == 0)
{
lean_ctor_set(v___x_2317_, 4, v___x_2439_);
lean_ctor_set(v___x_2317_, 3, v___x_2437_);
lean_ctor_set(v___x_2317_, 2, v_v_2431_);
lean_ctor_set(v___x_2317_, 1, v_k_2430_);
lean_ctor_set(v___x_2317_, 0, v___x_2435_);
v___x_2441_ = v___x_2317_;
goto v_reusejp_2440_;
}
else
{
lean_object* v_reuseFailAlloc_2442_; 
v_reuseFailAlloc_2442_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2442_, 0, v___x_2435_);
lean_ctor_set(v_reuseFailAlloc_2442_, 1, v_k_2430_);
lean_ctor_set(v_reuseFailAlloc_2442_, 2, v_v_2431_);
lean_ctor_set(v_reuseFailAlloc_2442_, 3, v___x_2437_);
lean_ctor_set(v_reuseFailAlloc_2442_, 4, v___x_2439_);
v___x_2441_ = v_reuseFailAlloc_2442_;
goto v_reusejp_2440_;
}
v_reusejp_2440_:
{
return v___x_2441_;
}
}
}
}
}
}
else
{
lean_object* v___x_2453_; lean_object* v___x_2455_; 
v___x_2453_ = lean_unsigned_to_nat(2u);
if (v_isShared_2318_ == 0)
{
lean_ctor_set(v___x_2317_, 4, v_r_2424_);
lean_ctor_set(v___x_2317_, 3, v_impl_2320_);
lean_ctor_set(v___x_2317_, 0, v___x_2453_);
v___x_2455_ = v___x_2317_;
goto v_reusejp_2454_;
}
else
{
lean_object* v_reuseFailAlloc_2456_; 
v_reuseFailAlloc_2456_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2456_, 0, v___x_2453_);
lean_ctor_set(v_reuseFailAlloc_2456_, 1, v_k_2312_);
lean_ctor_set(v_reuseFailAlloc_2456_, 2, v_v_2313_);
lean_ctor_set(v_reuseFailAlloc_2456_, 3, v_impl_2320_);
lean_ctor_set(v_reuseFailAlloc_2456_, 4, v_r_2424_);
v___x_2455_ = v_reuseFailAlloc_2456_;
goto v_reusejp_2454_;
}
v_reusejp_2454_:
{
return v___x_2455_;
}
}
}
}
}
case 1:
{
lean_object* v___x_2458_; 
lean_dec(v_v_2313_);
lean_dec(v_k_2312_);
if (v_isShared_2318_ == 0)
{
lean_ctor_set(v___x_2317_, 2, v_v_2309_);
lean_ctor_set(v___x_2317_, 1, v_k_2308_);
v___x_2458_ = v___x_2317_;
goto v_reusejp_2457_;
}
else
{
lean_object* v_reuseFailAlloc_2459_; 
v_reuseFailAlloc_2459_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2459_, 0, v_size_2311_);
lean_ctor_set(v_reuseFailAlloc_2459_, 1, v_k_2308_);
lean_ctor_set(v_reuseFailAlloc_2459_, 2, v_v_2309_);
lean_ctor_set(v_reuseFailAlloc_2459_, 3, v_l_2314_);
lean_ctor_set(v_reuseFailAlloc_2459_, 4, v_r_2315_);
v___x_2458_ = v_reuseFailAlloc_2459_;
goto v_reusejp_2457_;
}
v_reusejp_2457_:
{
return v___x_2458_;
}
}
default: 
{
lean_object* v_impl_2460_; lean_object* v___x_2461_; 
lean_dec(v_size_2311_);
v_impl_2460_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Level_collectMVars_spec__1___redArg(v_k_2308_, v_v_2309_, v_r_2315_);
v___x_2461_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_2314_) == 0)
{
lean_object* v_size_2462_; lean_object* v_size_2463_; lean_object* v_k_2464_; lean_object* v_v_2465_; lean_object* v_l_2466_; lean_object* v_r_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; uint8_t v___x_2470_; 
v_size_2462_ = lean_ctor_get(v_l_2314_, 0);
v_size_2463_ = lean_ctor_get(v_impl_2460_, 0);
lean_inc(v_size_2463_);
v_k_2464_ = lean_ctor_get(v_impl_2460_, 1);
lean_inc(v_k_2464_);
v_v_2465_ = lean_ctor_get(v_impl_2460_, 2);
lean_inc(v_v_2465_);
v_l_2466_ = lean_ctor_get(v_impl_2460_, 3);
lean_inc(v_l_2466_);
v_r_2467_ = lean_ctor_get(v_impl_2460_, 4);
lean_inc(v_r_2467_);
v___x_2468_ = lean_unsigned_to_nat(3u);
v___x_2469_ = lean_nat_mul(v___x_2468_, v_size_2462_);
v___x_2470_ = lean_nat_dec_lt(v___x_2469_, v_size_2463_);
lean_dec(v___x_2469_);
if (v___x_2470_ == 0)
{
lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2474_; 
lean_dec(v_r_2467_);
lean_dec(v_l_2466_);
lean_dec(v_v_2465_);
lean_dec(v_k_2464_);
v___x_2471_ = lean_nat_add(v___x_2461_, v_size_2462_);
v___x_2472_ = lean_nat_add(v___x_2471_, v_size_2463_);
lean_dec(v_size_2463_);
lean_dec(v___x_2471_);
if (v_isShared_2318_ == 0)
{
lean_ctor_set(v___x_2317_, 4, v_impl_2460_);
lean_ctor_set(v___x_2317_, 0, v___x_2472_);
v___x_2474_ = v___x_2317_;
goto v_reusejp_2473_;
}
else
{
lean_object* v_reuseFailAlloc_2475_; 
v_reuseFailAlloc_2475_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2475_, 0, v___x_2472_);
lean_ctor_set(v_reuseFailAlloc_2475_, 1, v_k_2312_);
lean_ctor_set(v_reuseFailAlloc_2475_, 2, v_v_2313_);
lean_ctor_set(v_reuseFailAlloc_2475_, 3, v_l_2314_);
lean_ctor_set(v_reuseFailAlloc_2475_, 4, v_impl_2460_);
v___x_2474_ = v_reuseFailAlloc_2475_;
goto v_reusejp_2473_;
}
v_reusejp_2473_:
{
return v___x_2474_;
}
}
else
{
lean_object* v___x_2477_; uint8_t v_isShared_2478_; uint8_t v_isSharedCheck_2539_; 
v_isSharedCheck_2539_ = !lean_is_exclusive(v_impl_2460_);
if (v_isSharedCheck_2539_ == 0)
{
lean_object* v_unused_2540_; lean_object* v_unused_2541_; lean_object* v_unused_2542_; lean_object* v_unused_2543_; lean_object* v_unused_2544_; 
v_unused_2540_ = lean_ctor_get(v_impl_2460_, 4);
lean_dec(v_unused_2540_);
v_unused_2541_ = lean_ctor_get(v_impl_2460_, 3);
lean_dec(v_unused_2541_);
v_unused_2542_ = lean_ctor_get(v_impl_2460_, 2);
lean_dec(v_unused_2542_);
v_unused_2543_ = lean_ctor_get(v_impl_2460_, 1);
lean_dec(v_unused_2543_);
v_unused_2544_ = lean_ctor_get(v_impl_2460_, 0);
lean_dec(v_unused_2544_);
v___x_2477_ = v_impl_2460_;
v_isShared_2478_ = v_isSharedCheck_2539_;
goto v_resetjp_2476_;
}
else
{
lean_dec(v_impl_2460_);
v___x_2477_ = lean_box(0);
v_isShared_2478_ = v_isSharedCheck_2539_;
goto v_resetjp_2476_;
}
v_resetjp_2476_:
{
lean_object* v_size_2479_; lean_object* v_k_2480_; lean_object* v_v_2481_; lean_object* v_l_2482_; lean_object* v_r_2483_; lean_object* v_size_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; uint8_t v___x_2487_; 
v_size_2479_ = lean_ctor_get(v_l_2466_, 0);
v_k_2480_ = lean_ctor_get(v_l_2466_, 1);
v_v_2481_ = lean_ctor_get(v_l_2466_, 2);
v_l_2482_ = lean_ctor_get(v_l_2466_, 3);
v_r_2483_ = lean_ctor_get(v_l_2466_, 4);
v_size_2484_ = lean_ctor_get(v_r_2467_, 0);
v___x_2485_ = lean_unsigned_to_nat(2u);
v___x_2486_ = lean_nat_mul(v___x_2485_, v_size_2484_);
v___x_2487_ = lean_nat_dec_lt(v_size_2479_, v___x_2486_);
lean_dec(v___x_2486_);
if (v___x_2487_ == 0)
{
lean_object* v___x_2489_; uint8_t v_isShared_2490_; uint8_t v_isSharedCheck_2515_; 
lean_inc(v_r_2483_);
lean_inc(v_l_2482_);
lean_inc(v_v_2481_);
lean_inc(v_k_2480_);
v_isSharedCheck_2515_ = !lean_is_exclusive(v_l_2466_);
if (v_isSharedCheck_2515_ == 0)
{
lean_object* v_unused_2516_; lean_object* v_unused_2517_; lean_object* v_unused_2518_; lean_object* v_unused_2519_; lean_object* v_unused_2520_; 
v_unused_2516_ = lean_ctor_get(v_l_2466_, 4);
lean_dec(v_unused_2516_);
v_unused_2517_ = lean_ctor_get(v_l_2466_, 3);
lean_dec(v_unused_2517_);
v_unused_2518_ = lean_ctor_get(v_l_2466_, 2);
lean_dec(v_unused_2518_);
v_unused_2519_ = lean_ctor_get(v_l_2466_, 1);
lean_dec(v_unused_2519_);
v_unused_2520_ = lean_ctor_get(v_l_2466_, 0);
lean_dec(v_unused_2520_);
v___x_2489_ = v_l_2466_;
v_isShared_2490_ = v_isSharedCheck_2515_;
goto v_resetjp_2488_;
}
else
{
lean_dec(v_l_2466_);
v___x_2489_ = lean_box(0);
v_isShared_2490_ = v_isSharedCheck_2515_;
goto v_resetjp_2488_;
}
v_resetjp_2488_:
{
lean_object* v___x_2491_; lean_object* v___x_2492_; lean_object* v___y_2494_; lean_object* v___y_2495_; lean_object* v___y_2496_; lean_object* v___y_2505_; 
v___x_2491_ = lean_nat_add(v___x_2461_, v_size_2462_);
v___x_2492_ = lean_nat_add(v___x_2491_, v_size_2463_);
lean_dec(v_size_2463_);
if (lean_obj_tag(v_l_2482_) == 0)
{
lean_object* v_size_2513_; 
v_size_2513_ = lean_ctor_get(v_l_2482_, 0);
lean_inc(v_size_2513_);
v___y_2505_ = v_size_2513_;
goto v___jp_2504_;
}
else
{
lean_object* v___x_2514_; 
v___x_2514_ = lean_unsigned_to_nat(0u);
v___y_2505_ = v___x_2514_;
goto v___jp_2504_;
}
v___jp_2493_:
{
lean_object* v___x_2497_; lean_object* v___x_2499_; 
v___x_2497_ = lean_nat_add(v___y_2494_, v___y_2496_);
lean_dec(v___y_2496_);
lean_dec(v___y_2494_);
if (v_isShared_2490_ == 0)
{
lean_ctor_set(v___x_2489_, 4, v_r_2467_);
lean_ctor_set(v___x_2489_, 3, v_r_2483_);
lean_ctor_set(v___x_2489_, 2, v_v_2465_);
lean_ctor_set(v___x_2489_, 1, v_k_2464_);
lean_ctor_set(v___x_2489_, 0, v___x_2497_);
v___x_2499_ = v___x_2489_;
goto v_reusejp_2498_;
}
else
{
lean_object* v_reuseFailAlloc_2503_; 
v_reuseFailAlloc_2503_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2503_, 0, v___x_2497_);
lean_ctor_set(v_reuseFailAlloc_2503_, 1, v_k_2464_);
lean_ctor_set(v_reuseFailAlloc_2503_, 2, v_v_2465_);
lean_ctor_set(v_reuseFailAlloc_2503_, 3, v_r_2483_);
lean_ctor_set(v_reuseFailAlloc_2503_, 4, v_r_2467_);
v___x_2499_ = v_reuseFailAlloc_2503_;
goto v_reusejp_2498_;
}
v_reusejp_2498_:
{
lean_object* v___x_2501_; 
if (v_isShared_2478_ == 0)
{
lean_ctor_set(v___x_2477_, 4, v___x_2499_);
lean_ctor_set(v___x_2477_, 3, v___y_2495_);
lean_ctor_set(v___x_2477_, 2, v_v_2481_);
lean_ctor_set(v___x_2477_, 1, v_k_2480_);
lean_ctor_set(v___x_2477_, 0, v___x_2492_);
v___x_2501_ = v___x_2477_;
goto v_reusejp_2500_;
}
else
{
lean_object* v_reuseFailAlloc_2502_; 
v_reuseFailAlloc_2502_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2502_, 0, v___x_2492_);
lean_ctor_set(v_reuseFailAlloc_2502_, 1, v_k_2480_);
lean_ctor_set(v_reuseFailAlloc_2502_, 2, v_v_2481_);
lean_ctor_set(v_reuseFailAlloc_2502_, 3, v___y_2495_);
lean_ctor_set(v_reuseFailAlloc_2502_, 4, v___x_2499_);
v___x_2501_ = v_reuseFailAlloc_2502_;
goto v_reusejp_2500_;
}
v_reusejp_2500_:
{
return v___x_2501_;
}
}
}
v___jp_2504_:
{
lean_object* v___x_2506_; lean_object* v___x_2508_; 
v___x_2506_ = lean_nat_add(v___x_2491_, v___y_2505_);
lean_dec(v___y_2505_);
lean_dec(v___x_2491_);
if (v_isShared_2318_ == 0)
{
lean_ctor_set(v___x_2317_, 4, v_l_2482_);
lean_ctor_set(v___x_2317_, 0, v___x_2506_);
v___x_2508_ = v___x_2317_;
goto v_reusejp_2507_;
}
else
{
lean_object* v_reuseFailAlloc_2512_; 
v_reuseFailAlloc_2512_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2512_, 0, v___x_2506_);
lean_ctor_set(v_reuseFailAlloc_2512_, 1, v_k_2312_);
lean_ctor_set(v_reuseFailAlloc_2512_, 2, v_v_2313_);
lean_ctor_set(v_reuseFailAlloc_2512_, 3, v_l_2314_);
lean_ctor_set(v_reuseFailAlloc_2512_, 4, v_l_2482_);
v___x_2508_ = v_reuseFailAlloc_2512_;
goto v_reusejp_2507_;
}
v_reusejp_2507_:
{
lean_object* v___x_2509_; 
v___x_2509_ = lean_nat_add(v___x_2461_, v_size_2484_);
if (lean_obj_tag(v_r_2483_) == 0)
{
lean_object* v_size_2510_; 
v_size_2510_ = lean_ctor_get(v_r_2483_, 0);
lean_inc(v_size_2510_);
v___y_2494_ = v___x_2509_;
v___y_2495_ = v___x_2508_;
v___y_2496_ = v_size_2510_;
goto v___jp_2493_;
}
else
{
lean_object* v___x_2511_; 
v___x_2511_ = lean_unsigned_to_nat(0u);
v___y_2494_ = v___x_2509_;
v___y_2495_ = v___x_2508_;
v___y_2496_ = v___x_2511_;
goto v___jp_2493_;
}
}
}
}
}
else
{
lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2525_; 
lean_del_object(v___x_2317_);
v___x_2521_ = lean_nat_add(v___x_2461_, v_size_2462_);
v___x_2522_ = lean_nat_add(v___x_2521_, v_size_2463_);
lean_dec(v_size_2463_);
v___x_2523_ = lean_nat_add(v___x_2521_, v_size_2479_);
lean_dec(v___x_2521_);
lean_inc_ref(v_l_2314_);
if (v_isShared_2478_ == 0)
{
lean_ctor_set(v___x_2477_, 4, v_l_2466_);
lean_ctor_set(v___x_2477_, 3, v_l_2314_);
lean_ctor_set(v___x_2477_, 2, v_v_2313_);
lean_ctor_set(v___x_2477_, 1, v_k_2312_);
lean_ctor_set(v___x_2477_, 0, v___x_2523_);
v___x_2525_ = v___x_2477_;
goto v_reusejp_2524_;
}
else
{
lean_object* v_reuseFailAlloc_2538_; 
v_reuseFailAlloc_2538_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2538_, 0, v___x_2523_);
lean_ctor_set(v_reuseFailAlloc_2538_, 1, v_k_2312_);
lean_ctor_set(v_reuseFailAlloc_2538_, 2, v_v_2313_);
lean_ctor_set(v_reuseFailAlloc_2538_, 3, v_l_2314_);
lean_ctor_set(v_reuseFailAlloc_2538_, 4, v_l_2466_);
v___x_2525_ = v_reuseFailAlloc_2538_;
goto v_reusejp_2524_;
}
v_reusejp_2524_:
{
lean_object* v___x_2527_; uint8_t v_isShared_2528_; uint8_t v_isSharedCheck_2532_; 
v_isSharedCheck_2532_ = !lean_is_exclusive(v_l_2314_);
if (v_isSharedCheck_2532_ == 0)
{
lean_object* v_unused_2533_; lean_object* v_unused_2534_; lean_object* v_unused_2535_; lean_object* v_unused_2536_; lean_object* v_unused_2537_; 
v_unused_2533_ = lean_ctor_get(v_l_2314_, 4);
lean_dec(v_unused_2533_);
v_unused_2534_ = lean_ctor_get(v_l_2314_, 3);
lean_dec(v_unused_2534_);
v_unused_2535_ = lean_ctor_get(v_l_2314_, 2);
lean_dec(v_unused_2535_);
v_unused_2536_ = lean_ctor_get(v_l_2314_, 1);
lean_dec(v_unused_2536_);
v_unused_2537_ = lean_ctor_get(v_l_2314_, 0);
lean_dec(v_unused_2537_);
v___x_2527_ = v_l_2314_;
v_isShared_2528_ = v_isSharedCheck_2532_;
goto v_resetjp_2526_;
}
else
{
lean_dec(v_l_2314_);
v___x_2527_ = lean_box(0);
v_isShared_2528_ = v_isSharedCheck_2532_;
goto v_resetjp_2526_;
}
v_resetjp_2526_:
{
lean_object* v___x_2530_; 
if (v_isShared_2528_ == 0)
{
lean_ctor_set(v___x_2527_, 4, v_r_2467_);
lean_ctor_set(v___x_2527_, 3, v___x_2525_);
lean_ctor_set(v___x_2527_, 2, v_v_2465_);
lean_ctor_set(v___x_2527_, 1, v_k_2464_);
lean_ctor_set(v___x_2527_, 0, v___x_2522_);
v___x_2530_ = v___x_2527_;
goto v_reusejp_2529_;
}
else
{
lean_object* v_reuseFailAlloc_2531_; 
v_reuseFailAlloc_2531_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2531_, 0, v___x_2522_);
lean_ctor_set(v_reuseFailAlloc_2531_, 1, v_k_2464_);
lean_ctor_set(v_reuseFailAlloc_2531_, 2, v_v_2465_);
lean_ctor_set(v_reuseFailAlloc_2531_, 3, v___x_2525_);
lean_ctor_set(v_reuseFailAlloc_2531_, 4, v_r_2467_);
v___x_2530_ = v_reuseFailAlloc_2531_;
goto v_reusejp_2529_;
}
v_reusejp_2529_:
{
return v___x_2530_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_2545_; 
v_l_2545_ = lean_ctor_get(v_impl_2460_, 3);
lean_inc(v_l_2545_);
if (lean_obj_tag(v_l_2545_) == 0)
{
lean_object* v_r_2546_; lean_object* v_k_2547_; lean_object* v_v_2548_; lean_object* v___x_2550_; uint8_t v_isShared_2551_; uint8_t v_isSharedCheck_2571_; 
v_r_2546_ = lean_ctor_get(v_impl_2460_, 4);
v_k_2547_ = lean_ctor_get(v_impl_2460_, 1);
v_v_2548_ = lean_ctor_get(v_impl_2460_, 2);
v_isSharedCheck_2571_ = !lean_is_exclusive(v_impl_2460_);
if (v_isSharedCheck_2571_ == 0)
{
lean_object* v_unused_2572_; lean_object* v_unused_2573_; 
v_unused_2572_ = lean_ctor_get(v_impl_2460_, 3);
lean_dec(v_unused_2572_);
v_unused_2573_ = lean_ctor_get(v_impl_2460_, 0);
lean_dec(v_unused_2573_);
v___x_2550_ = v_impl_2460_;
v_isShared_2551_ = v_isSharedCheck_2571_;
goto v_resetjp_2549_;
}
else
{
lean_inc(v_r_2546_);
lean_inc(v_v_2548_);
lean_inc(v_k_2547_);
lean_dec(v_impl_2460_);
v___x_2550_ = lean_box(0);
v_isShared_2551_ = v_isSharedCheck_2571_;
goto v_resetjp_2549_;
}
v_resetjp_2549_:
{
lean_object* v_k_2552_; lean_object* v_v_2553_; lean_object* v___x_2555_; uint8_t v_isShared_2556_; uint8_t v_isSharedCheck_2567_; 
v_k_2552_ = lean_ctor_get(v_l_2545_, 1);
v_v_2553_ = lean_ctor_get(v_l_2545_, 2);
v_isSharedCheck_2567_ = !lean_is_exclusive(v_l_2545_);
if (v_isSharedCheck_2567_ == 0)
{
lean_object* v_unused_2568_; lean_object* v_unused_2569_; lean_object* v_unused_2570_; 
v_unused_2568_ = lean_ctor_get(v_l_2545_, 4);
lean_dec(v_unused_2568_);
v_unused_2569_ = lean_ctor_get(v_l_2545_, 3);
lean_dec(v_unused_2569_);
v_unused_2570_ = lean_ctor_get(v_l_2545_, 0);
lean_dec(v_unused_2570_);
v___x_2555_ = v_l_2545_;
v_isShared_2556_ = v_isSharedCheck_2567_;
goto v_resetjp_2554_;
}
else
{
lean_inc(v_v_2553_);
lean_inc(v_k_2552_);
lean_dec(v_l_2545_);
v___x_2555_ = lean_box(0);
v_isShared_2556_ = v_isSharedCheck_2567_;
goto v_resetjp_2554_;
}
v_resetjp_2554_:
{
lean_object* v___x_2557_; lean_object* v___x_2559_; 
v___x_2557_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_2546_, 2);
if (v_isShared_2556_ == 0)
{
lean_ctor_set(v___x_2555_, 4, v_r_2546_);
lean_ctor_set(v___x_2555_, 3, v_r_2546_);
lean_ctor_set(v___x_2555_, 2, v_v_2313_);
lean_ctor_set(v___x_2555_, 1, v_k_2312_);
lean_ctor_set(v___x_2555_, 0, v___x_2461_);
v___x_2559_ = v___x_2555_;
goto v_reusejp_2558_;
}
else
{
lean_object* v_reuseFailAlloc_2566_; 
v_reuseFailAlloc_2566_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2566_, 0, v___x_2461_);
lean_ctor_set(v_reuseFailAlloc_2566_, 1, v_k_2312_);
lean_ctor_set(v_reuseFailAlloc_2566_, 2, v_v_2313_);
lean_ctor_set(v_reuseFailAlloc_2566_, 3, v_r_2546_);
lean_ctor_set(v_reuseFailAlloc_2566_, 4, v_r_2546_);
v___x_2559_ = v_reuseFailAlloc_2566_;
goto v_reusejp_2558_;
}
v_reusejp_2558_:
{
lean_object* v___x_2561_; 
lean_inc(v_r_2546_);
if (v_isShared_2551_ == 0)
{
lean_ctor_set(v___x_2550_, 3, v_r_2546_);
lean_ctor_set(v___x_2550_, 0, v___x_2461_);
v___x_2561_ = v___x_2550_;
goto v_reusejp_2560_;
}
else
{
lean_object* v_reuseFailAlloc_2565_; 
v_reuseFailAlloc_2565_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2565_, 0, v___x_2461_);
lean_ctor_set(v_reuseFailAlloc_2565_, 1, v_k_2547_);
lean_ctor_set(v_reuseFailAlloc_2565_, 2, v_v_2548_);
lean_ctor_set(v_reuseFailAlloc_2565_, 3, v_r_2546_);
lean_ctor_set(v_reuseFailAlloc_2565_, 4, v_r_2546_);
v___x_2561_ = v_reuseFailAlloc_2565_;
goto v_reusejp_2560_;
}
v_reusejp_2560_:
{
lean_object* v___x_2563_; 
if (v_isShared_2318_ == 0)
{
lean_ctor_set(v___x_2317_, 4, v___x_2561_);
lean_ctor_set(v___x_2317_, 3, v___x_2559_);
lean_ctor_set(v___x_2317_, 2, v_v_2553_);
lean_ctor_set(v___x_2317_, 1, v_k_2552_);
lean_ctor_set(v___x_2317_, 0, v___x_2557_);
v___x_2563_ = v___x_2317_;
goto v_reusejp_2562_;
}
else
{
lean_object* v_reuseFailAlloc_2564_; 
v_reuseFailAlloc_2564_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2564_, 0, v___x_2557_);
lean_ctor_set(v_reuseFailAlloc_2564_, 1, v_k_2552_);
lean_ctor_set(v_reuseFailAlloc_2564_, 2, v_v_2553_);
lean_ctor_set(v_reuseFailAlloc_2564_, 3, v___x_2559_);
lean_ctor_set(v_reuseFailAlloc_2564_, 4, v___x_2561_);
v___x_2563_ = v_reuseFailAlloc_2564_;
goto v_reusejp_2562_;
}
v_reusejp_2562_:
{
return v___x_2563_;
}
}
}
}
}
}
else
{
lean_object* v_r_2574_; 
v_r_2574_ = lean_ctor_get(v_impl_2460_, 4);
lean_inc(v_r_2574_);
if (lean_obj_tag(v_r_2574_) == 0)
{
lean_object* v_k_2575_; lean_object* v_v_2576_; lean_object* v___x_2578_; uint8_t v_isShared_2579_; uint8_t v_isSharedCheck_2587_; 
v_k_2575_ = lean_ctor_get(v_impl_2460_, 1);
v_v_2576_ = lean_ctor_get(v_impl_2460_, 2);
v_isSharedCheck_2587_ = !lean_is_exclusive(v_impl_2460_);
if (v_isSharedCheck_2587_ == 0)
{
lean_object* v_unused_2588_; lean_object* v_unused_2589_; lean_object* v_unused_2590_; 
v_unused_2588_ = lean_ctor_get(v_impl_2460_, 4);
lean_dec(v_unused_2588_);
v_unused_2589_ = lean_ctor_get(v_impl_2460_, 3);
lean_dec(v_unused_2589_);
v_unused_2590_ = lean_ctor_get(v_impl_2460_, 0);
lean_dec(v_unused_2590_);
v___x_2578_ = v_impl_2460_;
v_isShared_2579_ = v_isSharedCheck_2587_;
goto v_resetjp_2577_;
}
else
{
lean_inc(v_v_2576_);
lean_inc(v_k_2575_);
lean_dec(v_impl_2460_);
v___x_2578_ = lean_box(0);
v_isShared_2579_ = v_isSharedCheck_2587_;
goto v_resetjp_2577_;
}
v_resetjp_2577_:
{
lean_object* v___x_2580_; lean_object* v___x_2582_; 
v___x_2580_ = lean_unsigned_to_nat(3u);
if (v_isShared_2579_ == 0)
{
lean_ctor_set(v___x_2578_, 4, v_l_2545_);
lean_ctor_set(v___x_2578_, 2, v_v_2313_);
lean_ctor_set(v___x_2578_, 1, v_k_2312_);
lean_ctor_set(v___x_2578_, 0, v___x_2461_);
v___x_2582_ = v___x_2578_;
goto v_reusejp_2581_;
}
else
{
lean_object* v_reuseFailAlloc_2586_; 
v_reuseFailAlloc_2586_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2586_, 0, v___x_2461_);
lean_ctor_set(v_reuseFailAlloc_2586_, 1, v_k_2312_);
lean_ctor_set(v_reuseFailAlloc_2586_, 2, v_v_2313_);
lean_ctor_set(v_reuseFailAlloc_2586_, 3, v_l_2545_);
lean_ctor_set(v_reuseFailAlloc_2586_, 4, v_l_2545_);
v___x_2582_ = v_reuseFailAlloc_2586_;
goto v_reusejp_2581_;
}
v_reusejp_2581_:
{
lean_object* v___x_2584_; 
if (v_isShared_2318_ == 0)
{
lean_ctor_set(v___x_2317_, 4, v_r_2574_);
lean_ctor_set(v___x_2317_, 3, v___x_2582_);
lean_ctor_set(v___x_2317_, 2, v_v_2576_);
lean_ctor_set(v___x_2317_, 1, v_k_2575_);
lean_ctor_set(v___x_2317_, 0, v___x_2580_);
v___x_2584_ = v___x_2317_;
goto v_reusejp_2583_;
}
else
{
lean_object* v_reuseFailAlloc_2585_; 
v_reuseFailAlloc_2585_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2585_, 0, v___x_2580_);
lean_ctor_set(v_reuseFailAlloc_2585_, 1, v_k_2575_);
lean_ctor_set(v_reuseFailAlloc_2585_, 2, v_v_2576_);
lean_ctor_set(v_reuseFailAlloc_2585_, 3, v___x_2582_);
lean_ctor_set(v_reuseFailAlloc_2585_, 4, v_r_2574_);
v___x_2584_ = v_reuseFailAlloc_2585_;
goto v_reusejp_2583_;
}
v_reusejp_2583_:
{
return v___x_2584_;
}
}
}
}
else
{
lean_object* v___x_2591_; lean_object* v___x_2593_; 
v___x_2591_ = lean_unsigned_to_nat(2u);
if (v_isShared_2318_ == 0)
{
lean_ctor_set(v___x_2317_, 4, v_impl_2460_);
lean_ctor_set(v___x_2317_, 3, v_r_2574_);
lean_ctor_set(v___x_2317_, 0, v___x_2591_);
v___x_2593_ = v___x_2317_;
goto v_reusejp_2592_;
}
else
{
lean_object* v_reuseFailAlloc_2594_; 
v_reuseFailAlloc_2594_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2594_, 0, v___x_2591_);
lean_ctor_set(v_reuseFailAlloc_2594_, 1, v_k_2312_);
lean_ctor_set(v_reuseFailAlloc_2594_, 2, v_v_2313_);
lean_ctor_set(v_reuseFailAlloc_2594_, 3, v_r_2574_);
lean_ctor_set(v_reuseFailAlloc_2594_, 4, v_impl_2460_);
v___x_2593_ = v_reuseFailAlloc_2594_;
goto v_reusejp_2592_;
}
v_reusejp_2592_:
{
return v___x_2593_;
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
lean_object* v___x_2596_; lean_object* v___x_2597_; 
v___x_2596_ = lean_unsigned_to_nat(1u);
v___x_2597_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2597_, 0, v___x_2596_);
lean_ctor_set(v___x_2597_, 1, v_k_2308_);
lean_ctor_set(v___x_2597_, 2, v_v_2309_);
lean_ctor_set(v___x_2597_, 3, v_t_2310_);
lean_ctor_set(v___x_2597_, 4, v_t_2310_);
return v___x_2597_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Level_collectMVars_spec__0___redArg(lean_object* v_k_2598_, lean_object* v_t_2599_){
_start:
{
if (lean_obj_tag(v_t_2599_) == 0)
{
lean_object* v_k_2600_; lean_object* v_l_2601_; lean_object* v_r_2602_; uint8_t v___x_2603_; 
v_k_2600_ = lean_ctor_get(v_t_2599_, 1);
v_l_2601_ = lean_ctor_get(v_t_2599_, 3);
v_r_2602_ = lean_ctor_get(v_t_2599_, 4);
v___x_2603_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2598_, v_k_2600_);
switch(v___x_2603_)
{
case 0:
{
v_t_2599_ = v_l_2601_;
goto _start;
}
case 1:
{
uint8_t v___x_2605_; 
v___x_2605_ = 1;
return v___x_2605_;
}
default: 
{
v_t_2599_ = v_r_2602_;
goto _start;
}
}
}
else
{
uint8_t v___x_2607_; 
v___x_2607_ = 0;
return v___x_2607_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Level_collectMVars_spec__0___redArg___boxed(lean_object* v_k_2608_, lean_object* v_t_2609_){
_start:
{
uint8_t v_res_2610_; lean_object* v_r_2611_; 
v_res_2610_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Level_collectMVars_spec__0___redArg(v_k_2608_, v_t_2609_);
lean_dec(v_t_2609_);
lean_dec(v_k_2608_);
v_r_2611_ = lean_box(v_res_2610_);
return v_r_2611_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_collectMVars(lean_object* v_u_2612_, lean_object* v_s_2613_){
_start:
{
lean_object* v_u_2615_; lean_object* v_v_2616_; 
switch(lean_obj_tag(v_u_2612_))
{
case 1:
{
lean_object* v_a_2619_; 
v_a_2619_ = lean_ctor_get(v_u_2612_, 0);
lean_inc(v_a_2619_);
lean_dec_ref_known(v_u_2612_, 1);
v_u_2612_ = v_a_2619_;
goto _start;
}
case 2:
{
lean_object* v_a_2621_; lean_object* v_a_2622_; 
v_a_2621_ = lean_ctor_get(v_u_2612_, 0);
lean_inc(v_a_2621_);
v_a_2622_ = lean_ctor_get(v_u_2612_, 1);
lean_inc(v_a_2622_);
lean_dec_ref_known(v_u_2612_, 2);
v_u_2615_ = v_a_2621_;
v_v_2616_ = v_a_2622_;
goto v___jp_2614_;
}
case 3:
{
lean_object* v_a_2623_; lean_object* v_a_2624_; 
v_a_2623_ = lean_ctor_get(v_u_2612_, 0);
lean_inc(v_a_2623_);
v_a_2624_ = lean_ctor_get(v_u_2612_, 1);
lean_inc(v_a_2624_);
lean_dec_ref_known(v_u_2612_, 2);
v_u_2615_ = v_a_2623_;
v_v_2616_ = v_a_2624_;
goto v___jp_2614_;
}
case 5:
{
lean_object* v_a_2625_; uint8_t v___x_2626_; 
v_a_2625_ = lean_ctor_get(v_u_2612_, 0);
lean_inc(v_a_2625_);
lean_dec_ref_known(v_u_2612_, 1);
v___x_2626_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Level_collectMVars_spec__0___redArg(v_a_2625_, v_s_2613_);
if (v___x_2626_ == 0)
{
lean_object* v___x_2627_; lean_object* v___x_2628_; 
v___x_2627_ = lean_box(0);
v___x_2628_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Level_collectMVars_spec__1___redArg(v_a_2625_, v___x_2627_, v_s_2613_);
return v___x_2628_;
}
else
{
lean_dec(v_a_2625_);
return v_s_2613_;
}
}
default: 
{
lean_dec(v_u_2612_);
return v_s_2613_;
}
}
v___jp_2614_:
{
lean_object* v___x_2617_; 
v___x_2617_ = l_Lean_Level_collectMVars(v_v_2616_, v_s_2613_);
v_u_2612_ = v_u_2615_;
v_s_2613_ = v___x_2617_;
goto _start;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Level_collectMVars_spec__0(lean_object* v_00_u03b2_2629_, lean_object* v_k_2630_, lean_object* v_t_2631_){
_start:
{
uint8_t v___x_2632_; 
v___x_2632_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Level_collectMVars_spec__0___redArg(v_k_2630_, v_t_2631_);
return v___x_2632_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Level_collectMVars_spec__0___boxed(lean_object* v_00_u03b2_2633_, lean_object* v_k_2634_, lean_object* v_t_2635_){
_start:
{
uint8_t v_res_2636_; lean_object* v_r_2637_; 
v_res_2636_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Level_collectMVars_spec__0(v_00_u03b2_2633_, v_k_2634_, v_t_2635_);
lean_dec(v_t_2635_);
lean_dec(v_k_2634_);
v_r_2637_ = lean_box(v_res_2636_);
return v_r_2637_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Level_collectMVars_spec__1(lean_object* v_00_u03b2_2638_, lean_object* v_k_2639_, lean_object* v_v_2640_, lean_object* v_t_2641_, lean_object* v_hl_2642_){
_start:
{
lean_object* v___x_2643_; 
v___x_2643_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Level_collectMVars_spec__1___redArg(v_k_2639_, v_v_2640_, v_t_2641_);
return v___x_2643_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_find_x3f_visit(lean_object* v_p_2644_, lean_object* v_u_2645_){
_start:
{
lean_object* v_u_2647_; lean_object* v_v_2648_; lean_object* v___x_2651_; uint8_t v___x_2652_; 
lean_inc_ref(v_p_2644_);
lean_inc(v_u_2645_);
v___x_2651_ = lean_apply_1(v_p_2644_, v_u_2645_);
v___x_2652_ = lean_unbox(v___x_2651_);
if (v___x_2652_ == 0)
{
switch(lean_obj_tag(v_u_2645_))
{
case 1:
{
lean_object* v_a_2653_; 
v_a_2653_ = lean_ctor_get(v_u_2645_, 0);
lean_inc(v_a_2653_);
lean_dec_ref_known(v_u_2645_, 1);
v_u_2645_ = v_a_2653_;
goto _start;
}
case 2:
{
lean_object* v_a_2655_; lean_object* v_a_2656_; 
v_a_2655_ = lean_ctor_get(v_u_2645_, 0);
lean_inc(v_a_2655_);
v_a_2656_ = lean_ctor_get(v_u_2645_, 1);
lean_inc(v_a_2656_);
lean_dec_ref_known(v_u_2645_, 2);
v_u_2647_ = v_a_2655_;
v_v_2648_ = v_a_2656_;
goto v___jp_2646_;
}
case 3:
{
lean_object* v_a_2657_; lean_object* v_a_2658_; 
v_a_2657_ = lean_ctor_get(v_u_2645_, 0);
lean_inc(v_a_2657_);
v_a_2658_ = lean_ctor_get(v_u_2645_, 1);
lean_inc(v_a_2658_);
lean_dec_ref_known(v_u_2645_, 2);
v_u_2647_ = v_a_2657_;
v_v_2648_ = v_a_2658_;
goto v___jp_2646_;
}
default: 
{
lean_object* v___x_2659_; 
lean_dec(v_u_2645_);
lean_dec_ref(v_p_2644_);
v___x_2659_ = lean_box(0);
return v___x_2659_;
}
}
}
else
{
lean_object* v___x_2660_; 
lean_dec_ref(v_p_2644_);
v___x_2660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2660_, 0, v_u_2645_);
return v___x_2660_;
}
v___jp_2646_:
{
lean_object* v___x_2649_; 
lean_inc_ref(v_p_2644_);
v___x_2649_ = l___private_Lean_Level_0__Lean_Level_find_x3f_visit(v_p_2644_, v_u_2647_);
if (lean_obj_tag(v___x_2649_) == 0)
{
v_u_2645_ = v_v_2648_;
goto _start;
}
else
{
lean_dec(v_v_2648_);
lean_dec_ref(v_p_2644_);
return v___x_2649_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_find_x3f(lean_object* v_u_2661_, lean_object* v_p_2662_){
_start:
{
lean_object* v___x_2663_; 
v___x_2663_ = l___private_Lean_Level_0__Lean_Level_find_x3f_visit(v_p_2662_, v_u_2661_);
return v___x_2663_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_any(lean_object* v_u_2664_, lean_object* v_p_2665_){
_start:
{
lean_object* v___x_2666_; 
v___x_2666_ = l___private_Lean_Level_0__Lean_Level_find_x3f_visit(v_p_2665_, v_u_2664_);
if (lean_obj_tag(v___x_2666_) == 0)
{
uint8_t v___x_2667_; 
v___x_2667_ = 0;
return v___x_2667_;
}
else
{
uint8_t v___x_2668_; 
lean_dec_ref_known(v___x_2666_, 1);
v___x_2668_ = 1;
return v___x_2668_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_any___boxed(lean_object* v_u_2669_, lean_object* v_p_2670_){
_start:
{
uint8_t v_res_2671_; lean_object* v_r_2672_; 
v_res_2671_ = l_Lean_Level_any(v_u_2669_, v_p_2670_);
v_r_2672_ = lean_box(v_res_2671_);
return v_r_2672_;
}
}
LEAN_EXPORT lean_object* l_Lean_Nat_toLevel(lean_object* v_n_2673_){
_start:
{
lean_object* v___x_2674_; 
v___x_2674_ = l_Lean_Level_ofNat(v_n_2673_);
return v___x_2674_;
}
}
LEAN_EXPORT lean_object* l_Lean_Nat_toLevel___boxed(lean_object* v_n_2675_){
_start:
{
lean_object* v_res_2676_; 
v_res_2676_ = l_Lean_Nat_toLevel(v_n_2675_);
lean_dec(v_n_2675_);
return v_res_2676_;
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
