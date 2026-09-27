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
LEAN_EXPORT uint64_t l_Lean_instHashableLevelMVarId_hash(lean_object* v_x_132_){
_start:
{
uint64_t v___x_133_; 
v___x_133_ = 0ULL;
if (lean_obj_tag(v_x_132_) == 0)
{
uint64_t v___x_134_; 
v___x_134_ = 8934034000889494153ULL;
return v___x_134_;
}
else
{
uint64_t v_hash_135_; uint64_t v___x_136_; 
v_hash_135_ = lean_ctor_get_uint64(v_x_132_, sizeof(void*)*2);
v___x_136_ = lean_uint64_mix_hash(v___x_133_, v_hash_135_);
return v___x_136_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instHashableLevelMVarId_hash___boxed(lean_object* v_x_137_){
_start:
{
uint64_t v_res_138_; lean_object* v_r_139_; 
v_res_138_ = l_Lean_instHashableLevelMVarId_hash(v_x_137_);
lean_dec(v_x_137_);
v_r_139_ = lean_box_uint64(v_res_138_);
return v_r_139_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_instReprLevelMVarId_repr_spec__0(lean_object* v_a_142_){
_start:
{
lean_object* v___x_143_; 
v___x_143_ = lean_nat_to_int(v_a_142_);
return v___x_143_;
}
}
static lean_object* _init_l_Lean_instReprLevelMVarId_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_157_; lean_object* v___x_158_; 
v___x_157_ = lean_unsigned_to_nat(8u);
v___x_158_ = lean_nat_to_int(v___x_157_);
return v___x_158_;
}
}
static lean_object* _init_l_Lean_instReprLevelMVarId_repr___redArg___closed__9(void){
_start:
{
lean_object* v___x_160_; lean_object* v___x_161_; 
v___x_160_ = ((lean_object*)(l_Lean_instReprLevelMVarId_repr___redArg___closed__0));
v___x_161_ = lean_string_length(v___x_160_);
return v___x_161_;
}
}
static lean_object* _init_l_Lean_instReprLevelMVarId_repr___redArg___closed__10(void){
_start:
{
lean_object* v___x_162_; lean_object* v___x_163_; 
v___x_162_ = lean_obj_once(&l_Lean_instReprLevelMVarId_repr___redArg___closed__9, &l_Lean_instReprLevelMVarId_repr___redArg___closed__9_once, _init_l_Lean_instReprLevelMVarId_repr___redArg___closed__9);
v___x_163_ = lean_nat_to_int(v___x_162_);
return v___x_163_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprLevelMVarId_repr___redArg(lean_object* v_x_168_){
_start:
{
lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; uint8_t v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; 
v___x_169_ = ((lean_object*)(l_Lean_instReprLevelMVarId_repr___redArg___closed__6));
v___x_170_ = lean_obj_once(&l_Lean_instReprLevelMVarId_repr___redArg___closed__7, &l_Lean_instReprLevelMVarId_repr___redArg___closed__7_once, _init_l_Lean_instReprLevelMVarId_repr___redArg___closed__7);
v___x_171_ = lean_unsigned_to_nat(0u);
v___x_172_ = l_Lean_Name_reprPrec(v_x_168_, v___x_171_);
v___x_173_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_173_, 0, v___x_170_);
lean_ctor_set(v___x_173_, 1, v___x_172_);
v___x_174_ = 0;
v___x_175_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_175_, 0, v___x_173_);
lean_ctor_set_uint8(v___x_175_, sizeof(void*)*1, v___x_174_);
v___x_176_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_176_, 0, v___x_169_);
lean_ctor_set(v___x_176_, 1, v___x_175_);
v___x_177_ = lean_obj_once(&l_Lean_instReprLevelMVarId_repr___redArg___closed__10, &l_Lean_instReprLevelMVarId_repr___redArg___closed__10_once, _init_l_Lean_instReprLevelMVarId_repr___redArg___closed__10);
v___x_178_ = ((lean_object*)(l_Lean_instReprLevelMVarId_repr___redArg___closed__11));
v___x_179_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_179_, 0, v___x_178_);
lean_ctor_set(v___x_179_, 1, v___x_176_);
v___x_180_ = ((lean_object*)(l_Lean_instReprLevelMVarId_repr___redArg___closed__12));
v___x_181_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_181_, 0, v___x_179_);
lean_ctor_set(v___x_181_, 1, v___x_180_);
v___x_182_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_182_, 0, v___x_177_);
lean_ctor_set(v___x_182_, 1, v___x_181_);
v___x_183_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_183_, 0, v___x_182_);
lean_ctor_set_uint8(v___x_183_, sizeof(void*)*1, v___x_174_);
return v___x_183_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprLevelMVarId_repr(lean_object* v_x_184_, lean_object* v_prec_185_){
_start:
{
lean_object* v___x_186_; 
v___x_186_ = l_Lean_instReprLevelMVarId_repr___redArg(v_x_184_);
return v___x_186_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprLevelMVarId_repr___boxed(lean_object* v_x_187_, lean_object* v_prec_188_){
_start:
{
lean_object* v_res_189_; 
v_res_189_ = l_Lean_instReprLevelMVarId_repr(v_x_187_, v_prec_188_);
lean_dec(v_prec_188_);
return v_res_189_;
}
}
static lean_object* _init_l_Lean_instInhabitedLMVarIdSet___aux__1(void){
_start:
{
lean_object* v___x_194_; 
v___x_194_ = lean_box(1);
return v___x_194_;
}
}
static lean_object* _init_l_Lean_instInhabitedLMVarIdSet(void){
_start:
{
lean_object* v___x_195_; 
v___x_195_ = lean_box(1);
return v___x_195_;
}
}
static lean_object* _init_l_Lean_instEmptyCollectionLMVarIdSet___aux__1(void){
_start:
{
lean_object* v___x_196_; 
v___x_196_ = lean_box(1);
return v___x_196_;
}
}
static lean_object* _init_l_Lean_instEmptyCollectionLMVarIdSet(void){
_start:
{
lean_object* v___x_197_; 
v___x_197_ = lean_box(1);
return v___x_197_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInLMVarIdSetLMVarIdOfMonad___aux__1___redArg___lam__0(lean_object* v_f_198_, lean_object* v_a_199_, lean_object* v_b_200_, lean_object* v_c_201_){
_start:
{
lean_object* v___x_202_; 
v___x_202_ = lean_apply_2(v_f_198_, v_a_199_, v_c_201_);
return v___x_202_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInLMVarIdSetLMVarIdOfMonad___aux__1___redArg___lam__1(lean_object* v_toPure_203_, lean_object* v_____do__lift_204_){
_start:
{
lean_object* v_a_205_; lean_object* v___x_206_; 
v_a_205_ = lean_ctor_get(v_____do__lift_204_, 0);
lean_inc(v_a_205_);
lean_dec_ref(v_____do__lift_204_);
v___x_206_ = lean_apply_2(v_toPure_203_, lean_box(0), v_a_205_);
return v___x_206_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInLMVarIdSetLMVarIdOfMonad___aux__1___redArg(lean_object* v_inst_207_, lean_object* v_m_208_, lean_object* v_init_209_, lean_object* v_f_210_){
_start:
{
lean_object* v_toApplicative_211_; lean_object* v_toBind_212_; lean_object* v_toPure_213_; lean_object* v___f_214_; lean_object* v___x_215_; lean_object* v___f_216_; lean_object* v___x_217_; 
v_toApplicative_211_ = lean_ctor_get(v_inst_207_, 0);
v_toBind_212_ = lean_ctor_get(v_inst_207_, 1);
lean_inc(v_toBind_212_);
v_toPure_213_ = lean_ctor_get(v_toApplicative_211_, 1);
lean_inc(v_toPure_213_);
v___f_214_ = lean_alloc_closure((void*)(l_Lean_instForInLMVarIdSetLMVarIdOfMonad___aux__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_214_, 0, v_f_210_);
v___x_215_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_207_, v___f_214_, v_init_209_, v_m_208_);
v___f_216_ = lean_alloc_closure((void*)(l_Lean_instForInLMVarIdSetLMVarIdOfMonad___aux__1___redArg___lam__1), 2, 1);
lean_closure_set(v___f_216_, 0, v_toPure_213_);
v___x_217_ = lean_apply_4(v_toBind_212_, lean_box(0), lean_box(0), v___x_215_, v___f_216_);
return v___x_217_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInLMVarIdSetLMVarIdOfMonad___aux__1(lean_object* v_m_218_, lean_object* v_inst_219_, lean_object* v_00_u03b2_220_, lean_object* v_m_221_, lean_object* v_init_222_, lean_object* v_f_223_){
_start:
{
lean_object* v_toApplicative_224_; lean_object* v_toBind_225_; lean_object* v_toPure_226_; lean_object* v___f_227_; lean_object* v___x_228_; lean_object* v___f_229_; lean_object* v___x_230_; 
v_toApplicative_224_ = lean_ctor_get(v_inst_219_, 0);
v_toBind_225_ = lean_ctor_get(v_inst_219_, 1);
lean_inc(v_toBind_225_);
v_toPure_226_ = lean_ctor_get(v_toApplicative_224_, 1);
lean_inc(v_toPure_226_);
v___f_227_ = lean_alloc_closure((void*)(l_Lean_instForInLMVarIdSetLMVarIdOfMonad___aux__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_227_, 0, v_f_223_);
v___x_228_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_219_, v___f_227_, v_init_222_, v_m_221_);
v___f_229_ = lean_alloc_closure((void*)(l_Lean_instForInLMVarIdSetLMVarIdOfMonad___aux__1___redArg___lam__1), 2, 1);
lean_closure_set(v___f_229_, 0, v_toPure_226_);
v___x_230_ = lean_apply_4(v_toBind_225_, lean_box(0), lean_box(0), v___x_228_, v___f_229_);
return v___x_230_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInLMVarIdSetLMVarIdOfMonad___redArg(lean_object* v_inst_231_){
_start:
{
lean_object* v___x_232_; 
v___x_232_ = lean_alloc_closure((void*)(l_Lean_instForInLMVarIdSetLMVarIdOfMonad___aux__1), 6, 2);
lean_closure_set(v___x_232_, 0, lean_box(0));
lean_closure_set(v___x_232_, 1, v_inst_231_);
return v___x_232_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInLMVarIdSetLMVarIdOfMonad(lean_object* v_m_233_, lean_object* v_inst_234_){
_start:
{
lean_object* v___x_235_; 
v___x_235_ = lean_alloc_closure((void*)(l_Lean_instForInLMVarIdSetLMVarIdOfMonad___aux__1), 6, 2);
lean_closure_set(v___x_235_, 0, lean_box(0));
lean_closure_set(v___x_235_, 1, v_inst_234_);
return v___x_235_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionLMVarIdMap___aux__1___redArg(){
_start:
{
lean_object* v___x_237_; 
v___x_237_ = lean_box(1);
return v___x_237_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionLMVarIdMap___aux__1___redArg___boxed(lean_object* v___dummy_238_){
_start:
{
lean_object* v_res_239_; 
v_res_239_ = l_Lean_instEmptyCollectionLMVarIdMap___aux__1___redArg();
return v_res_239_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionLMVarIdMap___aux__1(lean_object* v_00_u03b1_240_){
_start:
{
lean_object* v___x_241_; 
v___x_241_ = lean_box(1);
return v___x_241_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionLMVarIdMap___redArg(){
_start:
{
lean_object* v___x_243_; 
v___x_243_ = lean_box(1);
return v___x_243_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionLMVarIdMap___redArg___boxed(lean_object* v___dummy_244_){
_start:
{
lean_object* v_res_245_; 
v_res_245_ = l_Lean_instEmptyCollectionLMVarIdMap___redArg();
return v_res_245_;
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
LEAN_EXPORT lean_object* l_Lean_instInhabitedLMVarIdMap___redArg(){
_start:
{
lean_object* v___x_286_; 
v___x_286_ = lean_box(1);
return v___x_286_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedLMVarIdMap___redArg___boxed(lean_object* v___dummy_287_){
_start:
{
lean_object* v_res_288_; 
v_res_288_ = l_Lean_instInhabitedLMVarIdMap___redArg();
return v_res_288_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedLMVarIdMap(lean_object* v_00_u03b1_289_){
_start:
{
lean_object* v___x_290_; 
v___x_290_ = lean_box(1);
return v___x_290_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_ctorIdx(lean_object* v_x_291_){
_start:
{
switch(lean_obj_tag(v_x_291_))
{
case 0:
{
lean_object* v___x_292_; 
v___x_292_ = lean_unsigned_to_nat(0u);
return v___x_292_;
}
case 1:
{
lean_object* v___x_293_; 
v___x_293_ = lean_unsigned_to_nat(1u);
return v___x_293_;
}
case 2:
{
lean_object* v___x_294_; 
v___x_294_ = lean_unsigned_to_nat(2u);
return v___x_294_;
}
case 3:
{
lean_object* v___x_295_; 
v___x_295_ = lean_unsigned_to_nat(3u);
return v___x_295_;
}
case 4:
{
lean_object* v___x_296_; 
v___x_296_ = lean_unsigned_to_nat(4u);
return v___x_296_;
}
default: 
{
lean_object* v___x_297_; 
v___x_297_ = lean_unsigned_to_nat(5u);
return v___x_297_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_ctorIdx___boxed(lean_object* v_x_298_){
_start:
{
lean_object* v_res_299_; 
v_res_299_ = l_Lean_Level_ctorIdx(v_x_298_);
lean_dec(v_x_298_);
return v_res_299_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_ctorElim___redArg(lean_object* v_t_300_, lean_object* v_k_301_){
_start:
{
switch(lean_obj_tag(v_t_300_))
{
case 0:
{
return v_k_301_;
}
case 2:
{
lean_object* v_a_302_; lean_object* v_a_303_; lean_object* v___x_304_; 
v_a_302_ = lean_ctor_get(v_t_300_, 0);
lean_inc(v_a_302_);
v_a_303_ = lean_ctor_get(v_t_300_, 1);
lean_inc(v_a_303_);
lean_dec_ref_known(v_t_300_, 2);
v___x_304_ = lean_apply_2(v_k_301_, v_a_302_, v_a_303_);
return v___x_304_;
}
case 3:
{
lean_object* v_a_305_; lean_object* v_a_306_; lean_object* v___x_307_; 
v_a_305_ = lean_ctor_get(v_t_300_, 0);
lean_inc(v_a_305_);
v_a_306_ = lean_ctor_get(v_t_300_, 1);
lean_inc(v_a_306_);
lean_dec_ref_known(v_t_300_, 2);
v___x_307_ = lean_apply_2(v_k_301_, v_a_305_, v_a_306_);
return v___x_307_;
}
default: 
{
lean_object* v_a_308_; lean_object* v___x_309_; 
v_a_308_ = lean_ctor_get(v_t_300_, 0);
lean_inc(v_a_308_);
lean_dec(v_t_300_);
v___x_309_ = lean_apply_1(v_k_301_, v_a_308_);
return v___x_309_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_ctorElim(lean_object* v_motive_310_, lean_object* v_ctorIdx_311_, lean_object* v_t_312_, lean_object* v_h_313_, lean_object* v_k_314_){
_start:
{
lean_object* v___x_315_; 
v___x_315_ = l_Lean_Level_ctorElim___redArg(v_t_312_, v_k_314_);
return v___x_315_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_ctorElim___boxed(lean_object* v_motive_316_, lean_object* v_ctorIdx_317_, lean_object* v_t_318_, lean_object* v_h_319_, lean_object* v_k_320_){
_start:
{
lean_object* v_res_321_; 
v_res_321_ = l_Lean_Level_ctorElim(v_motive_316_, v_ctorIdx_317_, v_t_318_, v_h_319_, v_k_320_);
lean_dec(v_ctorIdx_317_);
return v_res_321_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_zero_elim___redArg(lean_object* v_t_322_, lean_object* v_zero_323_){
_start:
{
lean_object* v___x_324_; 
v___x_324_ = l_Lean_Level_ctorElim___redArg(v_t_322_, v_zero_323_);
return v___x_324_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_zero_elim(lean_object* v_motive_325_, lean_object* v_t_326_, lean_object* v_h_327_, lean_object* v_zero_328_){
_start:
{
lean_object* v___x_329_; 
v___x_329_ = l_Lean_Level_ctorElim___redArg(v_t_326_, v_zero_328_);
return v___x_329_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_succ_elim___redArg(lean_object* v_t_330_, lean_object* v_succ_331_){
_start:
{
lean_object* v___x_332_; 
v___x_332_ = l_Lean_Level_ctorElim___redArg(v_t_330_, v_succ_331_);
return v___x_332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_succ_elim(lean_object* v_motive_333_, lean_object* v_t_334_, lean_object* v_h_335_, lean_object* v_succ_336_){
_start:
{
lean_object* v___x_337_; 
v___x_337_ = l_Lean_Level_ctorElim___redArg(v_t_334_, v_succ_336_);
return v___x_337_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_max_elim___redArg(lean_object* v_t_338_, lean_object* v_max_339_){
_start:
{
lean_object* v___x_340_; 
v___x_340_ = l_Lean_Level_ctorElim___redArg(v_t_338_, v_max_339_);
return v___x_340_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_max_elim(lean_object* v_motive_341_, lean_object* v_t_342_, lean_object* v_h_343_, lean_object* v_max_344_){
_start:
{
lean_object* v___x_345_; 
v___x_345_ = l_Lean_Level_ctorElim___redArg(v_t_342_, v_max_344_);
return v___x_345_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_imax_elim___redArg(lean_object* v_t_346_, lean_object* v_imax_347_){
_start:
{
lean_object* v___x_348_; 
v___x_348_ = l_Lean_Level_ctorElim___redArg(v_t_346_, v_imax_347_);
return v___x_348_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_imax_elim(lean_object* v_motive_349_, lean_object* v_t_350_, lean_object* v_h_351_, lean_object* v_imax_352_){
_start:
{
lean_object* v___x_353_; 
v___x_353_ = l_Lean_Level_ctorElim___redArg(v_t_350_, v_imax_352_);
return v___x_353_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_param_elim___redArg(lean_object* v_t_354_, lean_object* v_param_355_){
_start:
{
lean_object* v___x_356_; 
v___x_356_ = l_Lean_Level_ctorElim___redArg(v_t_354_, v_param_355_);
return v___x_356_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_param_elim(lean_object* v_motive_357_, lean_object* v_t_358_, lean_object* v_h_359_, lean_object* v_param_360_){
_start:
{
lean_object* v___x_361_; 
v___x_361_ = l_Lean_Level_ctorElim___redArg(v_t_358_, v_param_360_);
return v___x_361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_mvar_elim___redArg(lean_object* v_t_362_, lean_object* v_mvar_363_){
_start:
{
lean_object* v___x_364_; 
v___x_364_ = l_Lean_Level_ctorElim___redArg(v_t_362_, v_mvar_363_);
return v___x_364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_mvar_elim(lean_object* v_motive_365_, lean_object* v_t_366_, lean_object* v_h_367_, lean_object* v_mvar_368_){
_start:
{
lean_object* v___x_369_; 
v___x_369_ = l_Lean_Level_ctorElim___redArg(v_t_366_, v_mvar_368_);
return v___x_369_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_casesOn___override___redArg(lean_object* v_t_370_, lean_object* v_zero_371_, lean_object* v_succ_372_, lean_object* v_max_373_, lean_object* v_imax_374_, lean_object* v_param_375_, lean_object* v_mvar_376_){
_start:
{
switch(lean_obj_tag(v_t_370_))
{
case 0:
{
lean_dec(v_mvar_376_);
lean_dec(v_param_375_);
lean_dec(v_imax_374_);
lean_dec(v_max_373_);
lean_dec(v_succ_372_);
lean_inc(v_zero_371_);
return v_zero_371_;
}
case 1:
{
lean_object* v_a_377_; lean_object* v___x_378_; 
lean_dec(v_mvar_376_);
lean_dec(v_param_375_);
lean_dec(v_imax_374_);
lean_dec(v_max_373_);
v_a_377_ = lean_ctor_get(v_t_370_, 0);
lean_inc(v_a_377_);
lean_dec_ref_known(v_t_370_, 1);
v___x_378_ = lean_apply_1(v_succ_372_, v_a_377_);
return v___x_378_;
}
case 2:
{
lean_object* v_a_379_; lean_object* v_a_380_; lean_object* v___x_381_; 
lean_dec(v_mvar_376_);
lean_dec(v_param_375_);
lean_dec(v_imax_374_);
lean_dec(v_succ_372_);
v_a_379_ = lean_ctor_get(v_t_370_, 0);
lean_inc(v_a_379_);
v_a_380_ = lean_ctor_get(v_t_370_, 1);
lean_inc(v_a_380_);
lean_dec_ref_known(v_t_370_, 2);
v___x_381_ = lean_apply_2(v_max_373_, v_a_379_, v_a_380_);
return v___x_381_;
}
case 3:
{
lean_object* v_a_382_; lean_object* v_a_383_; lean_object* v___x_384_; 
lean_dec(v_mvar_376_);
lean_dec(v_param_375_);
lean_dec(v_max_373_);
lean_dec(v_succ_372_);
v_a_382_ = lean_ctor_get(v_t_370_, 0);
lean_inc(v_a_382_);
v_a_383_ = lean_ctor_get(v_t_370_, 1);
lean_inc(v_a_383_);
lean_dec_ref_known(v_t_370_, 2);
v___x_384_ = lean_apply_2(v_imax_374_, v_a_382_, v_a_383_);
return v___x_384_;
}
case 4:
{
lean_object* v_a_385_; lean_object* v___x_386_; 
lean_dec(v_mvar_376_);
lean_dec(v_imax_374_);
lean_dec(v_max_373_);
lean_dec(v_succ_372_);
v_a_385_ = lean_ctor_get(v_t_370_, 0);
lean_inc(v_a_385_);
lean_dec_ref_known(v_t_370_, 1);
v___x_386_ = lean_apply_1(v_param_375_, v_a_385_);
return v___x_386_;
}
default: 
{
lean_object* v_a_387_; lean_object* v___x_388_; 
lean_dec(v_param_375_);
lean_dec(v_imax_374_);
lean_dec(v_max_373_);
lean_dec(v_succ_372_);
v_a_387_ = lean_ctor_get(v_t_370_, 0);
lean_inc(v_a_387_);
lean_dec_ref_known(v_t_370_, 1);
v___x_388_ = lean_apply_1(v_mvar_376_, v_a_387_);
return v___x_388_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_casesOn___override___redArg___boxed(lean_object* v_t_389_, lean_object* v_zero_390_, lean_object* v_succ_391_, lean_object* v_max_392_, lean_object* v_imax_393_, lean_object* v_param_394_, lean_object* v_mvar_395_){
_start:
{
lean_object* v_res_396_; 
v_res_396_ = l_Lean_Level_casesOn___override___redArg(v_t_389_, v_zero_390_, v_succ_391_, v_max_392_, v_imax_393_, v_param_394_, v_mvar_395_);
lean_dec(v_zero_390_);
return v_res_396_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_casesOn___override(lean_object* v_motive_397_, lean_object* v_t_398_, lean_object* v_zero_399_, lean_object* v_succ_400_, lean_object* v_max_401_, lean_object* v_imax_402_, lean_object* v_param_403_, lean_object* v_mvar_404_){
_start:
{
switch(lean_obj_tag(v_t_398_))
{
case 0:
{
lean_dec(v_mvar_404_);
lean_dec(v_param_403_);
lean_dec(v_imax_402_);
lean_dec(v_max_401_);
lean_dec(v_succ_400_);
lean_inc(v_zero_399_);
return v_zero_399_;
}
case 1:
{
lean_object* v_a_405_; lean_object* v___x_406_; 
lean_dec(v_mvar_404_);
lean_dec(v_param_403_);
lean_dec(v_imax_402_);
lean_dec(v_max_401_);
v_a_405_ = lean_ctor_get(v_t_398_, 0);
lean_inc(v_a_405_);
lean_dec_ref_known(v_t_398_, 1);
v___x_406_ = lean_apply_1(v_succ_400_, v_a_405_);
return v___x_406_;
}
case 2:
{
lean_object* v_a_407_; lean_object* v_a_408_; lean_object* v___x_409_; 
lean_dec(v_mvar_404_);
lean_dec(v_param_403_);
lean_dec(v_imax_402_);
lean_dec(v_succ_400_);
v_a_407_ = lean_ctor_get(v_t_398_, 0);
lean_inc(v_a_407_);
v_a_408_ = lean_ctor_get(v_t_398_, 1);
lean_inc(v_a_408_);
lean_dec_ref_known(v_t_398_, 2);
v___x_409_ = lean_apply_2(v_max_401_, v_a_407_, v_a_408_);
return v___x_409_;
}
case 3:
{
lean_object* v_a_410_; lean_object* v_a_411_; lean_object* v___x_412_; 
lean_dec(v_mvar_404_);
lean_dec(v_param_403_);
lean_dec(v_max_401_);
lean_dec(v_succ_400_);
v_a_410_ = lean_ctor_get(v_t_398_, 0);
lean_inc(v_a_410_);
v_a_411_ = lean_ctor_get(v_t_398_, 1);
lean_inc(v_a_411_);
lean_dec_ref_known(v_t_398_, 2);
v___x_412_ = lean_apply_2(v_imax_402_, v_a_410_, v_a_411_);
return v___x_412_;
}
case 4:
{
lean_object* v_a_413_; lean_object* v___x_414_; 
lean_dec(v_mvar_404_);
lean_dec(v_imax_402_);
lean_dec(v_max_401_);
lean_dec(v_succ_400_);
v_a_413_ = lean_ctor_get(v_t_398_, 0);
lean_inc(v_a_413_);
lean_dec_ref_known(v_t_398_, 1);
v___x_414_ = lean_apply_1(v_param_403_, v_a_413_);
return v___x_414_;
}
default: 
{
lean_object* v_a_415_; lean_object* v___x_416_; 
lean_dec(v_param_403_);
lean_dec(v_imax_402_);
lean_dec(v_max_401_);
lean_dec(v_succ_400_);
v_a_415_ = lean_ctor_get(v_t_398_, 0);
lean_inc(v_a_415_);
lean_dec_ref_known(v_t_398_, 1);
v___x_416_ = lean_apply_1(v_mvar_404_, v_a_415_);
return v___x_416_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_casesOn___override___boxed(lean_object* v_motive_417_, lean_object* v_t_418_, lean_object* v_zero_419_, lean_object* v_succ_420_, lean_object* v_max_421_, lean_object* v_imax_422_, lean_object* v_param_423_, lean_object* v_mvar_424_){
_start:
{
lean_object* v_res_425_; 
v_res_425_ = l_Lean_Level_casesOn___override(v_motive_417_, v_t_418_, v_zero_419_, v_succ_420_, v_max_421_, v_imax_422_, v_param_423_, v_mvar_424_);
lean_dec(v_zero_419_);
return v_res_425_;
}
}
static lean_object* _init_l_Lean_Level_zero___override(void){
_start:
{
lean_object* v___x_426_; 
v___x_426_ = lean_box(0);
return v___x_426_;
}
}
static uint64_t _init_l_Lean_Level_data___override___closed__0(void){
_start:
{
uint8_t v___x_427_; lean_object* v___x_428_; uint64_t v___x_429_; uint64_t v___x_430_; 
v___x_427_ = 0;
v___x_428_ = lean_unsigned_to_nat(0u);
v___x_429_ = 2221ULL;
v___x_430_ = lean_level_mk_data(v___x_429_, v___x_428_, v___x_427_, v___x_427_);
return v___x_430_;
}
}
LEAN_EXPORT uint64_t l_Lean_Level_data___override(lean_object* v_x_431_){
_start:
{
switch(lean_obj_tag(v_x_431_))
{
case 0:
{
uint64_t v___x_432_; 
v___x_432_ = lean_uint64_once(&l_Lean_Level_data___override___closed__0, &l_Lean_Level_data___override___closed__0_once, _init_l_Lean_Level_data___override___closed__0);
return v___x_432_;
}
case 2:
{
uint64_t v_data_433_; 
v_data_433_ = lean_ctor_get_uint64(v_x_431_, sizeof(void*)*2);
return v_data_433_;
}
case 3:
{
uint64_t v_data_434_; 
v_data_434_ = lean_ctor_get_uint64(v_x_431_, sizeof(void*)*2);
return v_data_434_;
}
default: 
{
uint64_t v_data_435_; 
v_data_435_ = lean_ctor_get_uint64(v_x_431_, sizeof(void*)*1);
return v_data_435_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_data___override___boxed(lean_object* v_x_436_){
_start:
{
uint64_t v_res_437_; lean_object* v_r_438_; 
v_res_437_ = l_Lean_Level_data___override(v_x_436_);
lean_dec(v_x_436_);
v_r_438_ = lean_box_uint64(v_res_437_);
return v_r_438_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_succ___override(lean_object* v_a_439_){
_start:
{
uint64_t v___x_440_; uint64_t v___x_441_; uint64_t v___x_442_; uint64_t v___x_443_; uint32_t v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; uint8_t v___x_448_; uint8_t v___x_449_; uint64_t v___x_450_; lean_object* v___x_451_; 
v___x_440_ = 2243ULL;
v___x_441_ = l_Lean_Level_data___override(v_a_439_);
v___x_442_ = l_Lean_Level_Data_hash(v___x_441_);
v___x_443_ = lean_uint64_mix_hash(v___x_440_, v___x_442_);
v___x_444_ = l_Lean_Level_Data_depth(v___x_441_);
v___x_445_ = lean_uint32_to_nat(v___x_444_);
v___x_446_ = lean_unsigned_to_nat(1u);
v___x_447_ = lean_nat_add(v___x_445_, v___x_446_);
lean_dec(v___x_445_);
v___x_448_ = l_Lean_Level_Data_hasMVar(v___x_441_);
v___x_449_ = l_Lean_Level_Data_hasParam(v___x_441_);
v___x_450_ = lean_level_mk_data(v___x_443_, v___x_447_, v___x_448_, v___x_449_);
v___x_451_ = lean_alloc_ctor(1, 1, 8);
lean_ctor_set(v___x_451_, 0, v_a_439_);
lean_ctor_set_uint64(v___x_451_, sizeof(void*)*1, v___x_450_);
return v___x_451_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_max___override(lean_object* v_a_452_, lean_object* v_a_453_){
_start:
{
uint64_t v___x_454_; uint64_t v___x_455_; uint64_t v___x_456_; uint64_t v___x_457_; uint64_t v___x_458_; uint64_t v___x_459_; uint64_t v___x_460_; lean_object* v___y_462_; uint8_t v___y_463_; uint8_t v___y_464_; lean_object* v___y_468_; uint8_t v___y_469_; lean_object* v___y_473_; uint32_t v___x_478_; lean_object* v___x_479_; uint32_t v___x_480_; lean_object* v___x_481_; uint8_t v___x_482_; 
v___x_454_ = 2251ULL;
v___x_455_ = l_Lean_Level_data___override(v_a_452_);
v___x_456_ = l_Lean_Level_Data_hash(v___x_455_);
v___x_457_ = l_Lean_Level_data___override(v_a_453_);
v___x_458_ = l_Lean_Level_Data_hash(v___x_457_);
v___x_459_ = lean_uint64_mix_hash(v___x_456_, v___x_458_);
v___x_460_ = lean_uint64_mix_hash(v___x_454_, v___x_459_);
v___x_478_ = l_Lean_Level_Data_depth(v___x_455_);
v___x_479_ = lean_uint32_to_nat(v___x_478_);
v___x_480_ = l_Lean_Level_Data_depth(v___x_457_);
v___x_481_ = lean_uint32_to_nat(v___x_480_);
v___x_482_ = lean_nat_dec_le(v___x_479_, v___x_481_);
if (v___x_482_ == 0)
{
lean_dec(v___x_481_);
v___y_473_ = v___x_479_;
goto v___jp_472_;
}
else
{
lean_dec(v___x_479_);
v___y_473_ = v___x_481_;
goto v___jp_472_;
}
v___jp_461_:
{
uint64_t v___x_465_; lean_object* v___x_466_; 
v___x_465_ = lean_level_mk_data(v___x_460_, v___y_462_, v___y_463_, v___y_464_);
v___x_466_ = lean_alloc_ctor(2, 2, 8);
lean_ctor_set(v___x_466_, 0, v_a_452_);
lean_ctor_set(v___x_466_, 1, v_a_453_);
lean_ctor_set_uint64(v___x_466_, sizeof(void*)*2, v___x_465_);
return v___x_466_;
}
v___jp_467_:
{
uint8_t v___x_470_; 
v___x_470_ = l_Lean_Level_Data_hasParam(v___x_455_);
if (v___x_470_ == 0)
{
uint8_t v___x_471_; 
v___x_471_ = l_Lean_Level_Data_hasParam(v___x_457_);
v___y_462_ = v___y_468_;
v___y_463_ = v___y_469_;
v___y_464_ = v___x_471_;
goto v___jp_461_;
}
else
{
v___y_462_ = v___y_468_;
v___y_463_ = v___y_469_;
v___y_464_ = v___x_470_;
goto v___jp_461_;
}
}
v___jp_472_:
{
lean_object* v___x_474_; lean_object* v___x_475_; uint8_t v___x_476_; 
v___x_474_ = lean_unsigned_to_nat(1u);
v___x_475_ = lean_nat_add(v___y_473_, v___x_474_);
lean_dec(v___y_473_);
v___x_476_ = l_Lean_Level_Data_hasMVar(v___x_455_);
if (v___x_476_ == 0)
{
uint8_t v___x_477_; 
v___x_477_ = l_Lean_Level_Data_hasMVar(v___x_457_);
v___y_468_ = v___x_475_;
v___y_469_ = v___x_477_;
goto v___jp_467_;
}
else
{
v___y_468_ = v___x_475_;
v___y_469_ = v___x_476_;
goto v___jp_467_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_imax___override(lean_object* v_a_483_, lean_object* v_a_484_){
_start:
{
uint64_t v___x_485_; uint64_t v___x_486_; uint64_t v___x_487_; uint64_t v___x_488_; uint64_t v___x_489_; uint64_t v___x_490_; uint64_t v___x_491_; uint8_t v___y_493_; lean_object* v___y_494_; uint8_t v___y_495_; lean_object* v___y_499_; uint8_t v___y_500_; lean_object* v___y_504_; uint32_t v___x_509_; lean_object* v___x_510_; uint32_t v___x_511_; lean_object* v___x_512_; uint8_t v___x_513_; 
v___x_485_ = 2267ULL;
v___x_486_ = l_Lean_Level_data___override(v_a_483_);
v___x_487_ = l_Lean_Level_Data_hash(v___x_486_);
v___x_488_ = l_Lean_Level_data___override(v_a_484_);
v___x_489_ = l_Lean_Level_Data_hash(v___x_488_);
v___x_490_ = lean_uint64_mix_hash(v___x_487_, v___x_489_);
v___x_491_ = lean_uint64_mix_hash(v___x_485_, v___x_490_);
v___x_509_ = l_Lean_Level_Data_depth(v___x_486_);
v___x_510_ = lean_uint32_to_nat(v___x_509_);
v___x_511_ = l_Lean_Level_Data_depth(v___x_488_);
v___x_512_ = lean_uint32_to_nat(v___x_511_);
v___x_513_ = lean_nat_dec_le(v___x_510_, v___x_512_);
if (v___x_513_ == 0)
{
lean_dec(v___x_512_);
v___y_504_ = v___x_510_;
goto v___jp_503_;
}
else
{
lean_dec(v___x_510_);
v___y_504_ = v___x_512_;
goto v___jp_503_;
}
v___jp_492_:
{
uint64_t v___x_496_; lean_object* v___x_497_; 
v___x_496_ = lean_level_mk_data(v___x_491_, v___y_494_, v___y_493_, v___y_495_);
v___x_497_ = lean_alloc_ctor(3, 2, 8);
lean_ctor_set(v___x_497_, 0, v_a_483_);
lean_ctor_set(v___x_497_, 1, v_a_484_);
lean_ctor_set_uint64(v___x_497_, sizeof(void*)*2, v___x_496_);
return v___x_497_;
}
v___jp_498_:
{
uint8_t v___x_501_; 
v___x_501_ = l_Lean_Level_Data_hasParam(v___x_486_);
if (v___x_501_ == 0)
{
uint8_t v___x_502_; 
v___x_502_ = l_Lean_Level_Data_hasParam(v___x_488_);
v___y_493_ = v___y_500_;
v___y_494_ = v___y_499_;
v___y_495_ = v___x_502_;
goto v___jp_492_;
}
else
{
v___y_493_ = v___y_500_;
v___y_494_ = v___y_499_;
v___y_495_ = v___x_501_;
goto v___jp_492_;
}
}
v___jp_503_:
{
lean_object* v___x_505_; lean_object* v___x_506_; uint8_t v___x_507_; 
v___x_505_ = lean_unsigned_to_nat(1u);
v___x_506_ = lean_nat_add(v___y_504_, v___x_505_);
lean_dec(v___y_504_);
v___x_507_ = l_Lean_Level_Data_hasMVar(v___x_486_);
if (v___x_507_ == 0)
{
uint8_t v___x_508_; 
v___x_508_ = l_Lean_Level_Data_hasMVar(v___x_488_);
v___y_499_ = v___x_506_;
v___y_500_ = v___x_508_;
goto v___jp_498_;
}
else
{
v___y_499_ = v___x_506_;
v___y_500_ = v___x_507_;
goto v___jp_498_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_param___override(lean_object* v_a_514_){
_start:
{
uint64_t v___x_515_; uint64_t v___y_517_; 
v___x_515_ = 2239ULL;
if (lean_obj_tag(v_a_514_) == 0)
{
uint64_t v___x_524_; 
v___x_524_ = 1723ULL;
v___y_517_ = v___x_524_;
goto v___jp_516_;
}
else
{
uint64_t v_hash_525_; 
v_hash_525_ = lean_ctor_get_uint64(v_a_514_, sizeof(void*)*2);
v___y_517_ = v_hash_525_;
goto v___jp_516_;
}
v___jp_516_:
{
uint64_t v___x_518_; lean_object* v___x_519_; uint8_t v___x_520_; uint8_t v___x_521_; uint64_t v___x_522_; lean_object* v___x_523_; 
v___x_518_ = lean_uint64_mix_hash(v___x_515_, v___y_517_);
v___x_519_ = lean_unsigned_to_nat(0u);
v___x_520_ = 0;
v___x_521_ = 1;
v___x_522_ = lean_level_mk_data(v___x_518_, v___x_519_, v___x_520_, v___x_521_);
v___x_523_ = lean_alloc_ctor(4, 1, 8);
lean_ctor_set(v___x_523_, 0, v_a_514_);
lean_ctor_set_uint64(v___x_523_, sizeof(void*)*1, v___x_522_);
return v___x_523_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_mvar___override(lean_object* v_a_526_){
_start:
{
uint64_t v___x_527_; uint64_t v___x_528_; uint64_t v___x_529_; lean_object* v___x_530_; uint8_t v___x_531_; uint8_t v___x_532_; uint64_t v___x_533_; lean_object* v___x_534_; 
v___x_527_ = 2237ULL;
v___x_528_ = l_Lean_instHashableLevelMVarId_hash(v_a_526_);
v___x_529_ = lean_uint64_mix_hash(v___x_527_, v___x_528_);
v___x_530_ = lean_unsigned_to_nat(0u);
v___x_531_ = 1;
v___x_532_ = 0;
v___x_533_ = lean_level_mk_data(v___x_529_, v___x_530_, v___x_531_, v___x_532_);
v___x_534_ = lean_alloc_ctor(5, 1, 8);
lean_ctor_set(v___x_534_, 0, v_a_526_);
lean_ctor_set_uint64(v___x_534_, sizeof(void*)*1, v___x_533_);
return v___x_534_;
}
}
static lean_object* _init_l_Lean_instInhabitedLevel_default(void){
_start:
{
lean_object* v___x_535_; 
v___x_535_ = lean_box(0);
return v___x_535_;
}
}
static lean_object* _init_l_Lean_instInhabitedLevel(void){
_start:
{
lean_object* v___x_536_; 
v___x_536_ = lean_box(0);
return v___x_536_;
}
}
static lean_object* _init_l_Lean_instReprLevel_repr___closed__2(void){
_start:
{
lean_object* v___x_540_; lean_object* v___x_541_; 
v___x_540_ = lean_unsigned_to_nat(2u);
v___x_541_ = lean_nat_to_int(v___x_540_);
return v___x_541_;
}
}
static lean_object* _init_l_Lean_instReprLevel_repr___closed__3(void){
_start:
{
lean_object* v___x_542_; lean_object* v___x_543_; 
v___x_542_ = lean_unsigned_to_nat(1u);
v___x_543_ = lean_nat_to_int(v___x_542_);
return v___x_543_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprLevel_repr(lean_object* v_x_574_, lean_object* v_prec_575_){
_start:
{
lean_object* v___y_577_; 
switch(lean_obj_tag(v_x_574_))
{
case 0:
{
lean_object* v___x_583_; uint8_t v___x_584_; 
v___x_583_ = lean_unsigned_to_nat(1024u);
v___x_584_ = lean_nat_dec_le(v___x_583_, v_prec_575_);
if (v___x_584_ == 0)
{
lean_object* v___x_585_; 
v___x_585_ = lean_obj_once(&l_Lean_instReprLevel_repr___closed__2, &l_Lean_instReprLevel_repr___closed__2_once, _init_l_Lean_instReprLevel_repr___closed__2);
v___y_577_ = v___x_585_;
goto v___jp_576_;
}
else
{
lean_object* v___x_586_; 
v___x_586_ = lean_obj_once(&l_Lean_instReprLevel_repr___closed__3, &l_Lean_instReprLevel_repr___closed__3_once, _init_l_Lean_instReprLevel_repr___closed__3);
v___y_577_ = v___x_586_;
goto v___jp_576_;
}
}
case 1:
{
lean_object* v_a_587_; lean_object* v___x_588_; lean_object* v___y_590_; uint8_t v___x_598_; 
v_a_587_ = lean_ctor_get(v_x_574_, 0);
lean_inc(v_a_587_);
lean_dec_ref_known(v_x_574_, 1);
v___x_588_ = lean_unsigned_to_nat(1024u);
v___x_598_ = lean_nat_dec_le(v___x_588_, v_prec_575_);
if (v___x_598_ == 0)
{
lean_object* v___x_599_; 
v___x_599_ = lean_obj_once(&l_Lean_instReprLevel_repr___closed__2, &l_Lean_instReprLevel_repr___closed__2_once, _init_l_Lean_instReprLevel_repr___closed__2);
v___y_590_ = v___x_599_;
goto v___jp_589_;
}
else
{
lean_object* v___x_600_; 
v___x_600_ = lean_obj_once(&l_Lean_instReprLevel_repr___closed__3, &l_Lean_instReprLevel_repr___closed__3_once, _init_l_Lean_instReprLevel_repr___closed__3);
v___y_590_ = v___x_600_;
goto v___jp_589_;
}
v___jp_589_:
{
lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; uint8_t v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; 
v___x_591_ = ((lean_object*)(l_Lean_instReprLevel_repr___closed__6));
v___x_592_ = l_Lean_instReprLevel_repr(v_a_587_, v___x_588_);
v___x_593_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_593_, 0, v___x_591_);
lean_ctor_set(v___x_593_, 1, v___x_592_);
lean_inc(v___y_590_);
v___x_594_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_594_, 0, v___y_590_);
lean_ctor_set(v___x_594_, 1, v___x_593_);
v___x_595_ = 0;
v___x_596_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_596_, 0, v___x_594_);
lean_ctor_set_uint8(v___x_596_, sizeof(void*)*1, v___x_595_);
v___x_597_ = l_Repr_addAppParen(v___x_596_, v_prec_575_);
return v___x_597_;
}
}
case 2:
{
lean_object* v_a_601_; lean_object* v_a_602_; lean_object* v___x_603_; lean_object* v___y_605_; uint8_t v___x_617_; 
v_a_601_ = lean_ctor_get(v_x_574_, 0);
lean_inc(v_a_601_);
v_a_602_ = lean_ctor_get(v_x_574_, 1);
lean_inc(v_a_602_);
lean_dec_ref_known(v_x_574_, 2);
v___x_603_ = lean_unsigned_to_nat(1024u);
v___x_617_ = lean_nat_dec_le(v___x_603_, v_prec_575_);
if (v___x_617_ == 0)
{
lean_object* v___x_618_; 
v___x_618_ = lean_obj_once(&l_Lean_instReprLevel_repr___closed__2, &l_Lean_instReprLevel_repr___closed__2_once, _init_l_Lean_instReprLevel_repr___closed__2);
v___y_605_ = v___x_618_;
goto v___jp_604_;
}
else
{
lean_object* v___x_619_; 
v___x_619_ = lean_obj_once(&l_Lean_instReprLevel_repr___closed__3, &l_Lean_instReprLevel_repr___closed__3_once, _init_l_Lean_instReprLevel_repr___closed__3);
v___y_605_ = v___x_619_;
goto v___jp_604_;
}
v___jp_604_:
{
lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; uint8_t v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; 
v___x_606_ = lean_box(1);
v___x_607_ = ((lean_object*)(l_Lean_instReprLevel_repr___closed__9));
v___x_608_ = l_Lean_instReprLevel_repr(v_a_601_, v___x_603_);
v___x_609_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_609_, 0, v___x_607_);
lean_ctor_set(v___x_609_, 1, v___x_608_);
v___x_610_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_610_, 0, v___x_609_);
lean_ctor_set(v___x_610_, 1, v___x_606_);
v___x_611_ = l_Lean_instReprLevel_repr(v_a_602_, v___x_603_);
v___x_612_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_612_, 0, v___x_610_);
lean_ctor_set(v___x_612_, 1, v___x_611_);
lean_inc(v___y_605_);
v___x_613_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_613_, 0, v___y_605_);
lean_ctor_set(v___x_613_, 1, v___x_612_);
v___x_614_ = 0;
v___x_615_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_615_, 0, v___x_613_);
lean_ctor_set_uint8(v___x_615_, sizeof(void*)*1, v___x_614_);
v___x_616_ = l_Repr_addAppParen(v___x_615_, v_prec_575_);
return v___x_616_;
}
}
case 3:
{
lean_object* v_a_620_; lean_object* v_a_621_; lean_object* v___x_622_; lean_object* v___y_624_; uint8_t v___x_636_; 
v_a_620_ = lean_ctor_get(v_x_574_, 0);
lean_inc(v_a_620_);
v_a_621_ = lean_ctor_get(v_x_574_, 1);
lean_inc(v_a_621_);
lean_dec_ref_known(v_x_574_, 2);
v___x_622_ = lean_unsigned_to_nat(1024u);
v___x_636_ = lean_nat_dec_le(v___x_622_, v_prec_575_);
if (v___x_636_ == 0)
{
lean_object* v___x_637_; 
v___x_637_ = lean_obj_once(&l_Lean_instReprLevel_repr___closed__2, &l_Lean_instReprLevel_repr___closed__2_once, _init_l_Lean_instReprLevel_repr___closed__2);
v___y_624_ = v___x_637_;
goto v___jp_623_;
}
else
{
lean_object* v___x_638_; 
v___x_638_ = lean_obj_once(&l_Lean_instReprLevel_repr___closed__3, &l_Lean_instReprLevel_repr___closed__3_once, _init_l_Lean_instReprLevel_repr___closed__3);
v___y_624_ = v___x_638_;
goto v___jp_623_;
}
v___jp_623_:
{
lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; uint8_t v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; 
v___x_625_ = lean_box(1);
v___x_626_ = ((lean_object*)(l_Lean_instReprLevel_repr___closed__12));
v___x_627_ = l_Lean_instReprLevel_repr(v_a_620_, v___x_622_);
v___x_628_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_628_, 0, v___x_626_);
lean_ctor_set(v___x_628_, 1, v___x_627_);
v___x_629_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_629_, 0, v___x_628_);
lean_ctor_set(v___x_629_, 1, v___x_625_);
v___x_630_ = l_Lean_instReprLevel_repr(v_a_621_, v___x_622_);
v___x_631_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_631_, 0, v___x_629_);
lean_ctor_set(v___x_631_, 1, v___x_630_);
lean_inc(v___y_624_);
v___x_632_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_632_, 0, v___y_624_);
lean_ctor_set(v___x_632_, 1, v___x_631_);
v___x_633_ = 0;
v___x_634_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_634_, 0, v___x_632_);
lean_ctor_set_uint8(v___x_634_, sizeof(void*)*1, v___x_633_);
v___x_635_ = l_Repr_addAppParen(v___x_634_, v_prec_575_);
return v___x_635_;
}
}
case 4:
{
lean_object* v_a_639_; lean_object* v___y_641_; lean_object* v___x_650_; uint8_t v___x_651_; 
v_a_639_ = lean_ctor_get(v_x_574_, 0);
lean_inc(v_a_639_);
lean_dec_ref_known(v_x_574_, 1);
v___x_650_ = lean_unsigned_to_nat(1024u);
v___x_651_ = lean_nat_dec_le(v___x_650_, v_prec_575_);
if (v___x_651_ == 0)
{
lean_object* v___x_652_; 
v___x_652_ = lean_obj_once(&l_Lean_instReprLevel_repr___closed__2, &l_Lean_instReprLevel_repr___closed__2_once, _init_l_Lean_instReprLevel_repr___closed__2);
v___y_641_ = v___x_652_;
goto v___jp_640_;
}
else
{
lean_object* v___x_653_; 
v___x_653_ = lean_obj_once(&l_Lean_instReprLevel_repr___closed__3, &l_Lean_instReprLevel_repr___closed__3_once, _init_l_Lean_instReprLevel_repr___closed__3);
v___y_641_ = v___x_653_;
goto v___jp_640_;
}
v___jp_640_:
{
lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; uint8_t v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; 
v___x_642_ = ((lean_object*)(l_Lean_instReprLevel_repr___closed__15));
v___x_643_ = lean_unsigned_to_nat(1024u);
v___x_644_ = l_Lean_Name_reprPrec(v_a_639_, v___x_643_);
v___x_645_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_645_, 0, v___x_642_);
lean_ctor_set(v___x_645_, 1, v___x_644_);
lean_inc(v___y_641_);
v___x_646_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_646_, 0, v___y_641_);
lean_ctor_set(v___x_646_, 1, v___x_645_);
v___x_647_ = 0;
v___x_648_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_648_, 0, v___x_646_);
lean_ctor_set_uint8(v___x_648_, sizeof(void*)*1, v___x_647_);
v___x_649_ = l_Repr_addAppParen(v___x_648_, v_prec_575_);
return v___x_649_;
}
}
default: 
{
lean_object* v_a_654_; lean_object* v___y_656_; lean_object* v___x_665_; uint8_t v___x_666_; 
v_a_654_ = lean_ctor_get(v_x_574_, 0);
lean_inc(v_a_654_);
lean_dec_ref_known(v_x_574_, 1);
v___x_665_ = lean_unsigned_to_nat(1024u);
v___x_666_ = lean_nat_dec_le(v___x_665_, v_prec_575_);
if (v___x_666_ == 0)
{
lean_object* v___x_667_; 
v___x_667_ = lean_obj_once(&l_Lean_instReprLevel_repr___closed__2, &l_Lean_instReprLevel_repr___closed__2_once, _init_l_Lean_instReprLevel_repr___closed__2);
v___y_656_ = v___x_667_;
goto v___jp_655_;
}
else
{
lean_object* v___x_668_; 
v___x_668_ = lean_obj_once(&l_Lean_instReprLevel_repr___closed__3, &l_Lean_instReprLevel_repr___closed__3_once, _init_l_Lean_instReprLevel_repr___closed__3);
v___y_656_ = v___x_668_;
goto v___jp_655_;
}
v___jp_655_:
{
lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; uint8_t v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; 
v___x_657_ = ((lean_object*)(l_Lean_instReprLevel_repr___closed__18));
v___x_658_ = lean_unsigned_to_nat(1024u);
v___x_659_ = l_Lean_Name_reprPrec(v_a_654_, v___x_658_);
v___x_660_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_660_, 0, v___x_657_);
lean_ctor_set(v___x_660_, 1, v___x_659_);
lean_inc(v___y_656_);
v___x_661_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_661_, 0, v___y_656_);
lean_ctor_set(v___x_661_, 1, v___x_660_);
v___x_662_ = 0;
v___x_663_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_663_, 0, v___x_661_);
lean_ctor_set_uint8(v___x_663_, sizeof(void*)*1, v___x_662_);
v___x_664_ = l_Repr_addAppParen(v___x_663_, v_prec_575_);
return v___x_664_;
}
}
}
v___jp_576_:
{
lean_object* v___x_578_; lean_object* v___x_579_; uint8_t v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; 
v___x_578_ = ((lean_object*)(l_Lean_instReprLevel_repr___closed__1));
lean_inc(v___y_577_);
v___x_579_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_579_, 0, v___y_577_);
lean_ctor_set(v___x_579_, 1, v___x_578_);
v___x_580_ = 0;
v___x_581_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_581_, 0, v___x_579_);
lean_ctor_set_uint8(v___x_581_, sizeof(void*)*1, v___x_580_);
v___x_582_ = l_Repr_addAppParen(v___x_581_, v_prec_575_);
return v___x_582_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instReprLevel_repr___boxed(lean_object* v_x_669_, lean_object* v_prec_670_){
_start:
{
lean_object* v_res_671_; 
v_res_671_ = l_Lean_instReprLevel_repr(v_x_669_, v_prec_670_);
lean_dec(v_prec_670_);
return v_res_671_;
}
}
LEAN_EXPORT uint64_t l_Lean_Level_hash(lean_object* v_u_674_){
_start:
{
uint64_t v___x_675_; uint64_t v___x_676_; 
v___x_675_ = l_Lean_Level_data___override(v_u_674_);
v___x_676_ = l_Lean_Level_Data_hash(v___x_675_);
return v___x_676_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_hash___boxed(lean_object* v_u_677_){
_start:
{
uint64_t v_res_678_; lean_object* v_r_679_; 
v_res_678_ = l_Lean_Level_hash(v_u_677_);
lean_dec(v_u_677_);
v_r_679_ = lean_box_uint64(v_res_678_);
return v_r_679_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_depth(lean_object* v_u_682_){
_start:
{
uint64_t v___x_683_; uint32_t v___x_684_; lean_object* v___x_685_; 
v___x_683_ = l_Lean_Level_data___override(v_u_682_);
v___x_684_ = l_Lean_Level_Data_depth(v___x_683_);
v___x_685_ = lean_uint32_to_nat(v___x_684_);
return v___x_685_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_depth___boxed(lean_object* v_u_686_){
_start:
{
lean_object* v_res_687_; 
v_res_687_ = l_Lean_Level_depth(v_u_686_);
lean_dec(v_u_686_);
return v_res_687_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_hasMVar(lean_object* v_u_688_){
_start:
{
uint64_t v___x_689_; uint8_t v___x_690_; 
v___x_689_ = l_Lean_Level_data___override(v_u_688_);
v___x_690_ = l_Lean_Level_Data_hasMVar(v___x_689_);
return v___x_690_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_hasMVar___boxed(lean_object* v_u_691_){
_start:
{
uint8_t v_res_692_; lean_object* v_r_693_; 
v_res_692_ = l_Lean_Level_hasMVar(v_u_691_);
lean_dec(v_u_691_);
v_r_693_ = lean_box(v_res_692_);
return v_r_693_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_hasParam(lean_object* v_u_694_){
_start:
{
uint64_t v___x_695_; uint8_t v___x_696_; 
v___x_695_ = l_Lean_Level_data___override(v_u_694_);
v___x_696_ = l_Lean_Level_Data_hasParam(v___x_695_);
return v___x_696_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_hasParam___boxed(lean_object* v_u_697_){
_start:
{
uint8_t v_res_698_; lean_object* v_r_699_; 
v_res_698_ = l_Lean_Level_hasParam(v_u_697_);
lean_dec(v_u_697_);
v_r_699_ = lean_box(v_res_698_);
return v_r_699_;
}
}
LEAN_EXPORT uint32_t lean_level_hash(lean_object* v_u_700_){
_start:
{
uint64_t v___x_701_; uint32_t v___x_702_; 
v___x_701_ = l_Lean_Level_hash(v_u_700_);
lean_dec(v_u_700_);
v___x_702_ = lean_uint64_to_uint32(v___x_701_);
return v___x_702_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_hashEx___boxed(lean_object* v_u_703_){
_start:
{
uint32_t v_res_704_; lean_object* v_r_705_; 
v_res_704_ = lean_level_hash(v_u_703_);
v_r_705_ = lean_box_uint32(v_res_704_);
return v_r_705_;
}
}
LEAN_EXPORT uint8_t lean_level_has_mvar(lean_object* v_u_706_){
_start:
{
uint8_t v___x_707_; 
v___x_707_ = l_Lean_Level_hasMVar(v_u_706_);
lean_dec(v_u_706_);
return v___x_707_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_hasMVarEx___boxed(lean_object* v_u_708_){
_start:
{
uint8_t v_res_709_; lean_object* v_r_710_; 
v_res_709_ = lean_level_has_mvar(v_u_708_);
v_r_710_ = lean_box(v_res_709_);
return v_r_710_;
}
}
LEAN_EXPORT uint8_t lean_level_has_param(lean_object* v_u_711_){
_start:
{
uint8_t v___x_712_; 
v___x_712_ = l_Lean_Level_hasParam(v_u_711_);
lean_dec(v_u_711_);
return v___x_712_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_hasParamEx___boxed(lean_object* v_u_713_){
_start:
{
uint8_t v_res_714_; lean_object* v_r_715_; 
v_res_714_ = lean_level_has_param(v_u_713_);
v_r_715_ = lean_box(v_res_714_);
return v_r_715_;
}
}
LEAN_EXPORT uint32_t lean_level_depth(lean_object* v_u_716_){
_start:
{
uint64_t v___x_717_; uint32_t v___x_718_; 
v___x_717_ = l_Lean_Level_data___override(v_u_716_);
lean_dec(v_u_716_);
v___x_718_ = l_Lean_Level_Data_depth(v___x_717_);
return v___x_718_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_depthEx___boxed(lean_object* v_u_719_){
_start:
{
uint32_t v_res_720_; lean_object* v_r_721_; 
v_res_720_ = lean_level_depth(v_u_719_);
v_r_721_ = lean_box_uint32(v_res_720_);
return v_r_721_;
}
}
static lean_object* _init_l_Lean_levelZero(void){
_start:
{
lean_object* v___x_722_; 
v___x_722_ = lean_box(0);
return v___x_722_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLevelMVar(lean_object* v_mvarId_723_){
_start:
{
lean_object* v___x_724_; 
v___x_724_ = l_Lean_Level_mvar___override(v_mvarId_723_);
return v___x_724_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLevelParam(lean_object* v_name_725_){
_start:
{
lean_object* v___x_726_; 
v___x_726_ = l_Lean_Level_param___override(v_name_725_);
return v___x_726_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLevelSucc(lean_object* v_u_727_){
_start:
{
lean_object* v___x_728_; 
v___x_728_ = l_Lean_Level_succ___override(v_u_727_);
return v___x_728_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLevelMax(lean_object* v_u_729_, lean_object* v_v_730_){
_start:
{
lean_object* v___x_731_; 
v___x_731_ = l_Lean_Level_max___override(v_u_729_, v_v_730_);
return v___x_731_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLevelIMax(lean_object* v_u_732_, lean_object* v_v_733_){
_start:
{
lean_object* v___x_734_; 
v___x_734_ = l_Lean_Level_imax___override(v_u_732_, v_v_733_);
return v___x_734_;
}
}
static lean_object* _init_l_Lean_Level_one___closed__0(void){
_start:
{
lean_object* v___x_735_; lean_object* v___x_736_; 
v___x_735_ = lean_box(0);
v___x_736_ = l_Lean_Level_succ___override(v___x_735_);
return v___x_736_;
}
}
static lean_object* _init_l_Lean_Level_one(void){
_start:
{
lean_object* v___x_737_; 
v___x_737_ = lean_obj_once(&l_Lean_Level_one___closed__0, &l_Lean_Level_one___closed__0_once, _init_l_Lean_Level_one___closed__0);
return v___x_737_;
}
}
static lean_object* _init_l_Lean_levelOne(void){
_start:
{
lean_object* v___x_738_; 
v___x_738_ = lean_obj_once(&l_Lean_Level_one___closed__0, &l_Lean_Level_one___closed__0_once, _init_l_Lean_Level_one___closed__0);
return v___x_738_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLevelZeroEx___redArg(){
_start:
{
lean_object* v___x_740_; 
v___x_740_ = lean_box(0);
return v___x_740_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLevelZeroEx___redArg___boxed(lean_object* v___dummy_741_){
_start:
{
lean_object* v_res_742_; 
v_res_742_ = l_Lean_mkLevelZeroEx___redArg();
return v_res_742_;
}
}
LEAN_EXPORT lean_object* lean_level_mk_zero(lean_object* v_x_743_){
_start:
{
lean_object* v___x_744_; 
v___x_744_ = lean_box(0);
return v___x_744_;
}
}
LEAN_EXPORT lean_object* lean_level_mk_succ(lean_object* v_u_745_){
_start:
{
lean_object* v___x_746_; 
v___x_746_ = l_Lean_Level_succ___override(v_u_745_);
return v___x_746_;
}
}
LEAN_EXPORT lean_object* lean_level_mk_param(lean_object* v_name_747_){
_start:
{
lean_object* v___x_748_; 
v___x_748_ = l_Lean_Level_param___override(v_name_747_);
return v___x_748_;
}
}
LEAN_EXPORT lean_object* lean_level_mk_max(lean_object* v_u_749_, lean_object* v_v_750_){
_start:
{
lean_object* v___x_751_; 
v___x_751_ = l_Lean_Level_max___override(v_u_749_, v_v_750_);
return v___x_751_;
}
}
LEAN_EXPORT lean_object* lean_level_mk_imax(lean_object* v_u_752_, lean_object* v_v_753_){
_start:
{
lean_object* v___x_754_; 
v___x_754_ = l_Lean_Level_imax___override(v_u_752_, v_v_753_);
return v___x_754_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_isZero(lean_object* v_x_755_){
_start:
{
if (lean_obj_tag(v_x_755_) == 0)
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
LEAN_EXPORT lean_object* l_Lean_Level_isZero___boxed(lean_object* v_x_758_){
_start:
{
uint8_t v_res_759_; lean_object* v_r_760_; 
v_res_759_ = l_Lean_Level_isZero(v_x_758_);
lean_dec(v_x_758_);
v_r_760_ = lean_box(v_res_759_);
return v_r_760_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_isSucc(lean_object* v_x_761_){
_start:
{
if (lean_obj_tag(v_x_761_) == 1)
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
LEAN_EXPORT lean_object* l_Lean_Level_isSucc___boxed(lean_object* v_x_764_){
_start:
{
uint8_t v_res_765_; lean_object* v_r_766_; 
v_res_765_ = l_Lean_Level_isSucc(v_x_764_);
lean_dec(v_x_764_);
v_r_766_ = lean_box(v_res_765_);
return v_r_766_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_isMax(lean_object* v_x_767_){
_start:
{
if (lean_obj_tag(v_x_767_) == 2)
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
LEAN_EXPORT lean_object* l_Lean_Level_isMax___boxed(lean_object* v_x_770_){
_start:
{
uint8_t v_res_771_; lean_object* v_r_772_; 
v_res_771_ = l_Lean_Level_isMax(v_x_770_);
lean_dec(v_x_770_);
v_r_772_ = lean_box(v_res_771_);
return v_r_772_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_isIMax(lean_object* v_x_773_){
_start:
{
if (lean_obj_tag(v_x_773_) == 3)
{
uint8_t v___x_774_; 
v___x_774_ = 1;
return v___x_774_;
}
else
{
uint8_t v___x_775_; 
v___x_775_ = 0;
return v___x_775_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_isIMax___boxed(lean_object* v_x_776_){
_start:
{
uint8_t v_res_777_; lean_object* v_r_778_; 
v_res_777_ = l_Lean_Level_isIMax(v_x_776_);
lean_dec(v_x_776_);
v_r_778_ = lean_box(v_res_777_);
return v_r_778_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_isMaxIMax(lean_object* v_x_779_){
_start:
{
switch(lean_obj_tag(v_x_779_))
{
case 2:
{
uint8_t v___x_780_; 
v___x_780_ = 1;
return v___x_780_;
}
case 3:
{
uint8_t v___x_781_; 
v___x_781_ = 1;
return v___x_781_;
}
default: 
{
uint8_t v___x_782_; 
v___x_782_ = 0;
return v___x_782_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_isMaxIMax___boxed(lean_object* v_x_783_){
_start:
{
uint8_t v_res_784_; lean_object* v_r_785_; 
v_res_784_ = l_Lean_Level_isMaxIMax(v_x_783_);
lean_dec(v_x_783_);
v_r_785_ = lean_box(v_res_784_);
return v_r_785_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_isParam(lean_object* v_x_786_){
_start:
{
if (lean_obj_tag(v_x_786_) == 4)
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
LEAN_EXPORT lean_object* l_Lean_Level_isParam___boxed(lean_object* v_x_789_){
_start:
{
uint8_t v_res_790_; lean_object* v_r_791_; 
v_res_790_ = l_Lean_Level_isParam(v_x_789_);
lean_dec(v_x_789_);
v_r_791_ = lean_box(v_res_790_);
return v_r_791_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_isMVar(lean_object* v_x_792_){
_start:
{
if (lean_obj_tag(v_x_792_) == 5)
{
uint8_t v___x_793_; 
v___x_793_ = 1;
return v___x_793_;
}
else
{
uint8_t v___x_794_; 
v___x_794_ = 0;
return v___x_794_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_isMVar___boxed(lean_object* v_x_795_){
_start:
{
uint8_t v_res_796_; lean_object* v_r_797_; 
v_res_796_ = l_Lean_Level_isMVar(v_x_795_);
lean_dec(v_x_795_);
v_r_797_ = lean_box(v_res_796_);
return v_r_797_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Level_mvarId_x21_spec__0(lean_object* v_msg_798_){
_start:
{
lean_object* v___x_799_; lean_object* v___x_800_; 
v___x_799_ = lean_box(0);
v___x_800_ = lean_panic_fn_borrowed(v___x_799_, v_msg_798_);
return v___x_800_;
}
}
static lean_object* _init_l_Lean_Level_mvarId_x21___closed__3(void){
_start:
{
lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; 
v___x_804_ = ((lean_object*)(l_Lean_Level_mvarId_x21___closed__2));
v___x_805_ = lean_unsigned_to_nat(19u);
v___x_806_ = lean_unsigned_to_nat(195u);
v___x_807_ = ((lean_object*)(l_Lean_Level_mvarId_x21___closed__1));
v___x_808_ = ((lean_object*)(l_Lean_Level_mvarId_x21___closed__0));
v___x_809_ = l_mkPanicMessageWithDecl(v___x_808_, v___x_807_, v___x_806_, v___x_805_, v___x_804_);
return v___x_809_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_mvarId_x21(lean_object* v_x_810_){
_start:
{
if (lean_obj_tag(v_x_810_) == 5)
{
lean_object* v_a_811_; 
v_a_811_ = lean_ctor_get(v_x_810_, 0);
lean_inc(v_a_811_);
return v_a_811_;
}
else
{
lean_object* v___x_812_; lean_object* v___x_813_; 
v___x_812_ = lean_obj_once(&l_Lean_Level_mvarId_x21___closed__3, &l_Lean_Level_mvarId_x21___closed__3_once, _init_l_Lean_Level_mvarId_x21___closed__3);
v___x_813_ = l_panic___at___00Lean_Level_mvarId_x21_spec__0(v___x_812_);
return v___x_813_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_mvarId_x21___boxed(lean_object* v_x_814_){
_start:
{
lean_object* v_res_815_; 
v_res_815_ = l_Lean_Level_mvarId_x21(v_x_814_);
lean_dec(v_x_814_);
return v_res_815_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_isNeverZero(lean_object* v_x_816_){
_start:
{
switch(lean_obj_tag(v_x_816_))
{
case 1:
{
uint8_t v___x_817_; 
v___x_817_ = 1;
return v___x_817_;
}
case 2:
{
lean_object* v_a_818_; lean_object* v_a_819_; uint8_t v___x_820_; 
v_a_818_ = lean_ctor_get(v_x_816_, 0);
v_a_819_ = lean_ctor_get(v_x_816_, 1);
v___x_820_ = l_Lean_Level_isNeverZero(v_a_818_);
if (v___x_820_ == 0)
{
v_x_816_ = v_a_819_;
goto _start;
}
else
{
return v___x_820_;
}
}
case 3:
{
lean_object* v_a_822_; 
v_a_822_ = lean_ctor_get(v_x_816_, 1);
v_x_816_ = v_a_822_;
goto _start;
}
default: 
{
uint8_t v___x_824_; 
v___x_824_ = 0;
return v___x_824_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_isNeverZero___boxed(lean_object* v_x_825_){
_start:
{
uint8_t v_res_826_; lean_object* v_r_827_; 
v_res_826_ = l_Lean_Level_isNeverZero(v_x_825_);
lean_dec(v_x_825_);
v_r_827_ = lean_box(v_res_826_);
return v_r_827_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_isAlwaysZero(lean_object* v_x_828_){
_start:
{
switch(lean_obj_tag(v_x_828_))
{
case 0:
{
uint8_t v___x_829_; 
v___x_829_ = 1;
return v___x_829_;
}
case 2:
{
lean_object* v_a_830_; lean_object* v_a_831_; uint8_t v___x_832_; 
v_a_830_ = lean_ctor_get(v_x_828_, 0);
v_a_831_ = lean_ctor_get(v_x_828_, 1);
v___x_832_ = l_Lean_Level_isAlwaysZero(v_a_830_);
if (v___x_832_ == 0)
{
return v___x_832_;
}
else
{
v_x_828_ = v_a_831_;
goto _start;
}
}
case 3:
{
lean_object* v_a_834_; 
v_a_834_ = lean_ctor_get(v_x_828_, 1);
v_x_828_ = v_a_834_;
goto _start;
}
default: 
{
uint8_t v___x_836_; 
v___x_836_ = 0;
return v___x_836_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_isAlwaysZero___boxed(lean_object* v_x_837_){
_start:
{
uint8_t v_res_838_; lean_object* v_r_839_; 
v_res_838_ = l_Lean_Level_isAlwaysZero(v_x_837_);
lean_dec(v_x_837_);
v_r_839_ = lean_box(v_res_838_);
return v_r_839_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_ofNat(lean_object* v_x_840_){
_start:
{
lean_object* v_zero_841_; uint8_t v_isZero_842_; 
v_zero_841_ = lean_unsigned_to_nat(0u);
v_isZero_842_ = lean_nat_dec_eq(v_x_840_, v_zero_841_);
if (v_isZero_842_ == 1)
{
lean_object* v___x_843_; 
v___x_843_ = lean_box(0);
return v___x_843_;
}
else
{
lean_object* v_one_844_; lean_object* v_n_845_; lean_object* v___x_846_; lean_object* v___x_847_; 
v_one_844_ = lean_unsigned_to_nat(1u);
v_n_845_ = lean_nat_sub(v_x_840_, v_one_844_);
v___x_846_ = l_Lean_Level_ofNat(v_n_845_);
lean_dec(v_n_845_);
v___x_847_ = l_Lean_Level_succ___override(v___x_846_);
return v___x_847_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_ofNat___boxed(lean_object* v_x_848_){
_start:
{
lean_object* v_res_849_; 
v_res_849_ = l_Lean_Level_ofNat(v_x_848_);
lean_dec(v_x_848_);
return v_res_849_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_instOfNat(lean_object* v_n_850_){
_start:
{
lean_object* v___x_851_; 
v___x_851_ = l_Lean_Level_ofNat(v_n_850_);
return v___x_851_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_instOfNat___boxed(lean_object* v_n_852_){
_start:
{
lean_object* v_res_853_; 
v_res_853_ = l_Lean_Level_instOfNat(v_n_852_);
lean_dec(v_n_852_);
return v_res_853_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_addOffsetAux(lean_object* v_x_854_, lean_object* v_x_855_){
_start:
{
lean_object* v_zero_856_; uint8_t v_isZero_857_; 
v_zero_856_ = lean_unsigned_to_nat(0u);
v_isZero_857_ = lean_nat_dec_eq(v_x_854_, v_zero_856_);
if (v_isZero_857_ == 1)
{
lean_dec(v_x_854_);
return v_x_855_;
}
else
{
lean_object* v_one_858_; lean_object* v_n_859_; lean_object* v___x_860_; 
v_one_858_ = lean_unsigned_to_nat(1u);
v_n_859_ = lean_nat_sub(v_x_854_, v_one_858_);
lean_dec(v_x_854_);
v___x_860_ = l_Lean_Level_succ___override(v_x_855_);
v_x_854_ = v_n_859_;
v_x_855_ = v___x_860_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_addOffset(lean_object* v_u_862_, lean_object* v_n_863_){
_start:
{
lean_object* v___x_864_; 
v___x_864_ = l_Lean_Level_addOffsetAux(v_n_863_, v_u_862_);
return v___x_864_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_isExplicit(lean_object* v_x_865_){
_start:
{
switch(lean_obj_tag(v_x_865_))
{
case 0:
{
uint8_t v___x_866_; 
v___x_866_ = 1;
return v___x_866_;
}
case 1:
{
lean_object* v_a_867_; uint8_t v___x_868_; 
v_a_867_ = lean_ctor_get(v_x_865_, 0);
v___x_868_ = l_Lean_Level_hasMVar(v_a_867_);
if (v___x_868_ == 0)
{
uint8_t v___x_869_; 
v___x_869_ = l_Lean_Level_hasParam(v_a_867_);
if (v___x_869_ == 0)
{
v_x_865_ = v_a_867_;
goto _start;
}
else
{
return v___x_868_;
}
}
else
{
uint8_t v___x_871_; 
v___x_871_ = 0;
return v___x_871_;
}
}
default: 
{
uint8_t v___x_872_; 
v___x_872_ = 0;
return v___x_872_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_isExplicit___boxed(lean_object* v_x_873_){
_start:
{
uint8_t v_res_874_; lean_object* v_r_875_; 
v_res_874_ = l_Lean_Level_isExplicit(v_x_873_);
lean_dec(v_x_873_);
v_r_875_ = lean_box(v_res_874_);
return v_r_875_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_getOffsetAux(lean_object* v_x_876_, lean_object* v_x_877_){
_start:
{
if (lean_obj_tag(v_x_876_) == 1)
{
lean_object* v_a_878_; lean_object* v___x_879_; lean_object* v___x_880_; 
v_a_878_ = lean_ctor_get(v_x_876_, 0);
v___x_879_ = lean_unsigned_to_nat(1u);
v___x_880_ = lean_nat_add(v_x_877_, v___x_879_);
lean_dec(v_x_877_);
v_x_876_ = v_a_878_;
v_x_877_ = v___x_880_;
goto _start;
}
else
{
return v_x_877_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_getOffsetAux___boxed(lean_object* v_x_882_, lean_object* v_x_883_){
_start:
{
lean_object* v_res_884_; 
v_res_884_ = l_Lean_Level_getOffsetAux(v_x_882_, v_x_883_);
lean_dec(v_x_882_);
return v_res_884_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_getOffset(lean_object* v_lvl_885_){
_start:
{
lean_object* v___x_886_; lean_object* v___x_887_; 
v___x_886_ = lean_unsigned_to_nat(0u);
v___x_887_ = l_Lean_Level_getOffsetAux(v_lvl_885_, v___x_886_);
return v___x_887_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_getOffset___boxed(lean_object* v_lvl_888_){
_start:
{
lean_object* v_res_889_; 
v_res_889_ = l_Lean_Level_getOffset(v_lvl_888_);
lean_dec(v_lvl_888_);
return v_res_889_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_getLevelOffset(lean_object* v_x_890_){
_start:
{
if (lean_obj_tag(v_x_890_) == 1)
{
lean_object* v_a_891_; 
v_a_891_ = lean_ctor_get(v_x_890_, 0);
v_x_890_ = v_a_891_;
goto _start;
}
else
{
lean_inc(v_x_890_);
return v_x_890_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_getLevelOffset___boxed(lean_object* v_x_893_){
_start:
{
lean_object* v_res_894_; 
v_res_894_ = l_Lean_Level_getLevelOffset(v_x_893_);
lean_dec(v_x_893_);
return v_res_894_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_toNat(lean_object* v_lvl_895_){
_start:
{
lean_object* v___x_896_; 
v___x_896_ = l_Lean_Level_getLevelOffset(v_lvl_895_);
if (lean_obj_tag(v___x_896_) == 0)
{
lean_object* v___x_897_; lean_object* v___x_898_; 
v___x_897_ = l_Lean_Level_getOffset(v_lvl_895_);
v___x_898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_898_, 0, v___x_897_);
return v___x_898_;
}
else
{
lean_object* v___x_899_; 
lean_dec(v___x_896_);
v___x_899_ = lean_box(0);
return v___x_899_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_toNat___boxed(lean_object* v_lvl_900_){
_start:
{
lean_object* v_res_901_; 
v_res_901_ = l_Lean_Level_toNat(v_lvl_900_);
lean_dec(v_lvl_900_);
return v_res_901_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_beq___boxed(lean_object* v_a_904_, lean_object* v_b_905_){
_start:
{
uint8_t v_res_906_; lean_object* v_r_907_; 
v_res_906_ = lean_level_eq(v_a_904_, v_b_905_);
lean_dec(v_b_905_);
lean_dec(v_a_904_);
v_r_907_ = lean_box(v_res_906_);
return v_r_907_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_occurs(lean_object* v_x_910_, lean_object* v_x_911_){
_start:
{
switch(lean_obj_tag(v_x_911_))
{
case 1:
{
lean_object* v_a_912_; uint8_t v___x_913_; 
v_a_912_ = lean_ctor_get(v_x_911_, 0);
v___x_913_ = lean_level_eq(v_x_910_, v_x_911_);
if (v___x_913_ == 0)
{
v_x_911_ = v_a_912_;
goto _start;
}
else
{
return v___x_913_;
}
}
case 2:
{
lean_object* v_a_915_; lean_object* v_a_916_; uint8_t v___y_918_; uint8_t v___x_920_; 
v_a_915_ = lean_ctor_get(v_x_911_, 0);
v_a_916_ = lean_ctor_get(v_x_911_, 1);
v___x_920_ = lean_level_eq(v_x_910_, v_x_911_);
if (v___x_920_ == 0)
{
uint8_t v___x_921_; 
v___x_921_ = l_Lean_Level_occurs(v_x_910_, v_a_915_);
v___y_918_ = v___x_921_;
goto v___jp_917_;
}
else
{
v___y_918_ = v___x_920_;
goto v___jp_917_;
}
v___jp_917_:
{
if (v___y_918_ == 0)
{
v_x_911_ = v_a_916_;
goto _start;
}
else
{
return v___y_918_;
}
}
}
case 3:
{
lean_object* v_a_922_; lean_object* v_a_923_; uint8_t v___y_925_; uint8_t v___x_927_; 
v_a_922_ = lean_ctor_get(v_x_911_, 0);
v_a_923_ = lean_ctor_get(v_x_911_, 1);
v___x_927_ = lean_level_eq(v_x_910_, v_x_911_);
if (v___x_927_ == 0)
{
uint8_t v___x_928_; 
v___x_928_ = l_Lean_Level_occurs(v_x_910_, v_a_922_);
v___y_925_ = v___x_928_;
goto v___jp_924_;
}
else
{
v___y_925_ = v___x_927_;
goto v___jp_924_;
}
v___jp_924_:
{
if (v___y_925_ == 0)
{
v_x_911_ = v_a_923_;
goto _start;
}
else
{
return v___y_925_;
}
}
}
default: 
{
uint8_t v___x_929_; 
v___x_929_ = lean_level_eq(v_x_910_, v_x_911_);
return v___x_929_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_occurs___boxed(lean_object* v_x_930_, lean_object* v_x_931_){
_start:
{
uint8_t v_res_932_; lean_object* v_r_933_; 
v_res_932_ = l_Lean_Level_occurs(v_x_930_, v_x_931_);
lean_dec(v_x_931_);
lean_dec(v_x_930_);
v_r_933_ = lean_box(v_res_932_);
return v_r_933_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_ctorToNat(lean_object* v_x_934_){
_start:
{
switch(lean_obj_tag(v_x_934_))
{
case 0:
{
lean_object* v___x_935_; 
v___x_935_ = lean_unsigned_to_nat(0u);
return v___x_935_;
}
case 1:
{
lean_object* v___x_936_; 
v___x_936_ = lean_unsigned_to_nat(3u);
return v___x_936_;
}
case 2:
{
lean_object* v___x_937_; 
v___x_937_ = lean_unsigned_to_nat(4u);
return v___x_937_;
}
case 3:
{
lean_object* v___x_938_; 
v___x_938_ = lean_unsigned_to_nat(5u);
return v___x_938_;
}
case 4:
{
lean_object* v___x_939_; 
v___x_939_ = lean_unsigned_to_nat(1u);
return v___x_939_;
}
default: 
{
lean_object* v___x_940_; 
v___x_940_ = lean_unsigned_to_nat(2u);
return v___x_940_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_ctorToNat___boxed(lean_object* v_x_941_){
_start:
{
lean_object* v_res_942_; 
v_res_942_ = l_Lean_Level_ctorToNat(v_x_941_);
lean_dec(v_x_941_);
return v_res_942_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_normLtAux(lean_object* v_x_943_, lean_object* v_x_944_, lean_object* v_x_945_, lean_object* v_x_946_){
_start:
{
lean_object* v_l_u2081_948_; lean_object* v_k_u2081_949_; lean_object* v_l_u2082_950_; lean_object* v_k_u2082_951_; lean_object* v_l_u2081_956_; lean_object* v_k_u2081_957_; lean_object* v_l_u2082_958_; lean_object* v_k_u2082_959_; 
switch(lean_obj_tag(v_x_943_))
{
case 1:
{
lean_object* v_a_965_; lean_object* v___x_966_; lean_object* v___x_967_; 
v_a_965_ = lean_ctor_get(v_x_943_, 0);
v___x_966_ = lean_unsigned_to_nat(1u);
v___x_967_ = lean_nat_add(v_x_944_, v___x_966_);
lean_dec(v_x_944_);
v_x_943_ = v_a_965_;
v_x_944_ = v___x_967_;
goto _start;
}
case 2:
{
switch(lean_obj_tag(v_x_945_))
{
case 1:
{
lean_object* v_a_969_; 
v_a_969_ = lean_ctor_get(v_x_945_, 0);
v_l_u2081_948_ = v_x_943_;
v_k_u2081_949_ = v_x_944_;
v_l_u2082_950_ = v_a_969_;
v_k_u2082_951_ = v_x_946_;
goto v___jp_947_;
}
case 2:
{
lean_object* v_a_970_; lean_object* v_a_971_; lean_object* v_a_972_; lean_object* v_a_973_; uint8_t v___x_977_; 
v_a_970_ = lean_ctor_get(v_x_943_, 0);
v_a_971_ = lean_ctor_get(v_x_943_, 1);
v_a_972_ = lean_ctor_get(v_x_945_, 0);
v_a_973_ = lean_ctor_get(v_x_945_, 1);
v___x_977_ = lean_level_eq(v_x_943_, v_x_945_);
if (v___x_977_ == 0)
{
uint8_t v___x_978_; 
lean_dec(v_x_946_);
lean_dec(v_x_944_);
v___x_978_ = lean_level_eq(v_a_970_, v_a_972_);
if (v___x_978_ == 0)
{
goto v___jp_974_;
}
else
{
if (v___x_977_ == 0)
{
lean_object* v___x_979_; 
v___x_979_ = lean_unsigned_to_nat(0u);
v_x_943_ = v_a_971_;
v_x_944_ = v___x_979_;
v_x_945_ = v_a_973_;
v_x_946_ = v___x_979_;
goto _start;
}
else
{
goto v___jp_974_;
}
}
}
else
{
uint8_t v___x_981_; 
v___x_981_ = lean_nat_dec_lt(v_x_944_, v_x_946_);
lean_dec(v_x_946_);
lean_dec(v_x_944_);
return v___x_981_;
}
v___jp_974_:
{
lean_object* v___x_975_; 
v___x_975_ = lean_unsigned_to_nat(0u);
v_x_943_ = v_a_970_;
v_x_944_ = v___x_975_;
v_x_945_ = v_a_972_;
v_x_946_ = v___x_975_;
goto _start;
}
}
default: 
{
v_l_u2081_956_ = v_x_943_;
v_k_u2081_957_ = v_x_944_;
v_l_u2082_958_ = v_x_945_;
v_k_u2082_959_ = v_x_946_;
goto v___jp_955_;
}
}
}
case 3:
{
switch(lean_obj_tag(v_x_945_))
{
case 1:
{
lean_object* v_a_982_; 
v_a_982_ = lean_ctor_get(v_x_945_, 0);
v_l_u2081_948_ = v_x_943_;
v_k_u2081_949_ = v_x_944_;
v_l_u2082_950_ = v_a_982_;
v_k_u2082_951_ = v_x_946_;
goto v___jp_947_;
}
case 3:
{
lean_object* v_a_983_; lean_object* v_a_984_; lean_object* v_a_985_; lean_object* v_a_986_; uint8_t v___x_990_; 
v_a_983_ = lean_ctor_get(v_x_943_, 0);
v_a_984_ = lean_ctor_get(v_x_943_, 1);
v_a_985_ = lean_ctor_get(v_x_945_, 0);
v_a_986_ = lean_ctor_get(v_x_945_, 1);
v___x_990_ = lean_level_eq(v_x_943_, v_x_945_);
if (v___x_990_ == 0)
{
uint8_t v___x_991_; 
lean_dec(v_x_946_);
lean_dec(v_x_944_);
v___x_991_ = lean_level_eq(v_a_983_, v_a_985_);
if (v___x_991_ == 0)
{
goto v___jp_987_;
}
else
{
if (v___x_990_ == 0)
{
lean_object* v___x_992_; 
v___x_992_ = lean_unsigned_to_nat(0u);
v_x_943_ = v_a_984_;
v_x_944_ = v___x_992_;
v_x_945_ = v_a_986_;
v_x_946_ = v___x_992_;
goto _start;
}
else
{
goto v___jp_987_;
}
}
}
else
{
uint8_t v___x_994_; 
v___x_994_ = lean_nat_dec_lt(v_x_944_, v_x_946_);
lean_dec(v_x_946_);
lean_dec(v_x_944_);
return v___x_994_;
}
v___jp_987_:
{
lean_object* v___x_988_; 
v___x_988_ = lean_unsigned_to_nat(0u);
v_x_943_ = v_a_983_;
v_x_944_ = v___x_988_;
v_x_945_ = v_a_985_;
v_x_946_ = v___x_988_;
goto _start;
}
}
default: 
{
v_l_u2081_956_ = v_x_943_;
v_k_u2081_957_ = v_x_944_;
v_l_u2082_958_ = v_x_945_;
v_k_u2082_959_ = v_x_946_;
goto v___jp_955_;
}
}
}
case 4:
{
switch(lean_obj_tag(v_x_945_))
{
case 1:
{
lean_object* v_a_995_; 
v_a_995_ = lean_ctor_get(v_x_945_, 0);
v_l_u2081_948_ = v_x_943_;
v_k_u2081_949_ = v_x_944_;
v_l_u2082_950_ = v_a_995_;
v_k_u2082_951_ = v_x_946_;
goto v___jp_947_;
}
case 4:
{
lean_object* v_a_996_; lean_object* v_a_997_; uint8_t v___x_998_; 
v_a_996_ = lean_ctor_get(v_x_943_, 0);
v_a_997_ = lean_ctor_get(v_x_945_, 0);
v___x_998_ = lean_name_eq(v_a_996_, v_a_997_);
if (v___x_998_ == 0)
{
uint8_t v___x_999_; 
lean_dec(v_x_946_);
lean_dec(v_x_944_);
v___x_999_ = l_Lean_Name_lt(v_a_996_, v_a_997_);
return v___x_999_;
}
else
{
uint8_t v___x_1000_; 
v___x_1000_ = lean_nat_dec_lt(v_x_944_, v_x_946_);
lean_dec(v_x_946_);
lean_dec(v_x_944_);
return v___x_1000_;
}
}
default: 
{
v_l_u2081_956_ = v_x_943_;
v_k_u2081_957_ = v_x_944_;
v_l_u2082_958_ = v_x_945_;
v_k_u2082_959_ = v_x_946_;
goto v___jp_955_;
}
}
}
case 5:
{
switch(lean_obj_tag(v_x_945_))
{
case 1:
{
lean_object* v_a_1001_; 
v_a_1001_ = lean_ctor_get(v_x_945_, 0);
v_l_u2081_948_ = v_x_943_;
v_k_u2081_949_ = v_x_944_;
v_l_u2082_950_ = v_a_1001_;
v_k_u2082_951_ = v_x_946_;
goto v___jp_947_;
}
case 5:
{
lean_object* v_a_1002_; lean_object* v_a_1003_; uint8_t v___x_1004_; 
v_a_1002_ = lean_ctor_get(v_x_943_, 0);
v_a_1003_ = lean_ctor_get(v_x_945_, 0);
v___x_1004_ = lean_name_eq(v_a_1002_, v_a_1003_);
if (v___x_1004_ == 0)
{
uint8_t v___x_1005_; 
lean_dec(v_x_946_);
lean_dec(v_x_944_);
v___x_1005_ = l_Lean_Name_lt(v_a_1002_, v_a_1003_);
return v___x_1005_;
}
else
{
uint8_t v___x_1006_; 
v___x_1006_ = lean_nat_dec_lt(v_x_944_, v_x_946_);
lean_dec(v_x_946_);
lean_dec(v_x_944_);
return v___x_1006_;
}
}
default: 
{
v_l_u2081_956_ = v_x_943_;
v_k_u2081_957_ = v_x_944_;
v_l_u2082_958_ = v_x_945_;
v_k_u2082_959_ = v_x_946_;
goto v___jp_955_;
}
}
}
default: 
{
if (lean_obj_tag(v_x_945_) == 1)
{
lean_object* v_a_1007_; 
v_a_1007_ = lean_ctor_get(v_x_945_, 0);
v_l_u2081_948_ = v_x_943_;
v_k_u2081_949_ = v_x_944_;
v_l_u2082_950_ = v_a_1007_;
v_k_u2082_951_ = v_x_946_;
goto v___jp_947_;
}
else
{
v_l_u2081_956_ = v_x_943_;
v_k_u2081_957_ = v_x_944_;
v_l_u2082_958_ = v_x_945_;
v_k_u2082_959_ = v_x_946_;
goto v___jp_955_;
}
}
}
v___jp_947_:
{
lean_object* v___x_952_; lean_object* v___x_953_; 
v___x_952_ = lean_unsigned_to_nat(1u);
v___x_953_ = lean_nat_add(v_k_u2082_951_, v___x_952_);
lean_dec(v_k_u2082_951_);
v_x_943_ = v_l_u2081_948_;
v_x_944_ = v_k_u2081_949_;
v_x_945_ = v_l_u2082_950_;
v_x_946_ = v___x_953_;
goto _start;
}
v___jp_955_:
{
uint8_t v___x_960_; 
v___x_960_ = lean_level_eq(v_l_u2081_956_, v_l_u2082_958_);
if (v___x_960_ == 0)
{
lean_object* v___x_961_; lean_object* v___x_962_; uint8_t v___x_963_; 
lean_dec(v_k_u2082_959_);
lean_dec(v_k_u2081_957_);
v___x_961_ = l_Lean_Level_ctorToNat(v_l_u2081_956_);
v___x_962_ = l_Lean_Level_ctorToNat(v_l_u2082_958_);
v___x_963_ = lean_nat_dec_lt(v___x_961_, v___x_962_);
lean_dec(v___x_962_);
lean_dec(v___x_961_);
return v___x_963_;
}
else
{
uint8_t v___x_964_; 
v___x_964_ = lean_nat_dec_lt(v_k_u2081_957_, v_k_u2082_959_);
lean_dec(v_k_u2082_959_);
lean_dec(v_k_u2081_957_);
return v___x_964_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_normLtAux___boxed(lean_object* v_x_1008_, lean_object* v_x_1009_, lean_object* v_x_1010_, lean_object* v_x_1011_){
_start:
{
uint8_t v_res_1012_; lean_object* v_r_1013_; 
v_res_1012_ = l_Lean_Level_normLtAux(v_x_1008_, v_x_1009_, v_x_1010_, v_x_1011_);
lean_dec(v_x_1010_);
lean_dec(v_x_1008_);
v_r_1013_ = lean_box(v_res_1012_);
return v_r_1013_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_normLtAux_match__1_splitter___redArg(lean_object* v_x_1014_, lean_object* v_x_1015_, lean_object* v_x_1016_, lean_object* v_x_1017_, lean_object* v_h__1_1018_, lean_object* v_h__2_1019_, lean_object* v_h__3_1020_, lean_object* v_h__4_1021_, lean_object* v_h__5_1022_, lean_object* v_h__6_1023_, lean_object* v_h__7_1024_){
_start:
{
switch(lean_obj_tag(v_x_1014_))
{
case 1:
{
lean_object* v_a_1025_; lean_object* v___x_1026_; 
lean_dec(v_h__7_1024_);
lean_dec(v_h__6_1023_);
lean_dec(v_h__5_1022_);
lean_dec(v_h__4_1021_);
lean_dec(v_h__3_1020_);
lean_dec(v_h__2_1019_);
v_a_1025_ = lean_ctor_get(v_x_1014_, 0);
lean_inc(v_a_1025_);
lean_dec_ref_known(v_x_1014_, 1);
v___x_1026_ = lean_apply_4(v_h__1_1018_, v_a_1025_, v_x_1015_, v_x_1016_, v_x_1017_);
return v___x_1026_;
}
case 2:
{
lean_dec(v_h__6_1023_);
lean_dec(v_h__5_1022_);
lean_dec(v_h__4_1021_);
lean_dec(v_h__1_1018_);
switch(lean_obj_tag(v_x_1016_))
{
case 1:
{
lean_object* v_a_1027_; lean_object* v___x_1028_; 
lean_dec(v_h__7_1024_);
lean_dec(v_h__3_1020_);
v_a_1027_ = lean_ctor_get(v_x_1016_, 0);
lean_inc(v_a_1027_);
lean_dec_ref_known(v_x_1016_, 1);
v___x_1028_ = lean_apply_5(v_h__2_1019_, v_x_1014_, v_x_1015_, v_a_1027_, v_x_1017_, lean_box(0));
return v___x_1028_;
}
case 2:
{
lean_object* v_a_1029_; lean_object* v_a_1030_; lean_object* v_a_1031_; lean_object* v_a_1032_; lean_object* v___x_1033_; 
lean_dec(v_h__7_1024_);
lean_dec(v_h__2_1019_);
v_a_1029_ = lean_ctor_get(v_x_1014_, 0);
lean_inc(v_a_1029_);
v_a_1030_ = lean_ctor_get(v_x_1014_, 1);
lean_inc(v_a_1030_);
lean_dec_ref_known(v_x_1014_, 2);
v_a_1031_ = lean_ctor_get(v_x_1016_, 0);
lean_inc(v_a_1031_);
v_a_1032_ = lean_ctor_get(v_x_1016_, 1);
lean_inc(v_a_1032_);
lean_dec_ref_known(v_x_1016_, 2);
v___x_1033_ = lean_apply_6(v_h__3_1020_, v_a_1029_, v_a_1030_, v_x_1015_, v_a_1031_, v_a_1032_, v_x_1017_);
return v___x_1033_;
}
default: 
{
lean_object* v___x_1034_; 
lean_dec(v_h__3_1020_);
lean_dec(v_h__2_1019_);
v___x_1034_ = lean_apply_10(v_h__7_1024_, v_x_1014_, v_x_1015_, v_x_1016_, v_x_1017_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_1034_;
}
}
}
case 3:
{
lean_dec(v_h__6_1023_);
lean_dec(v_h__5_1022_);
lean_dec(v_h__3_1020_);
lean_dec(v_h__1_1018_);
switch(lean_obj_tag(v_x_1016_))
{
case 1:
{
lean_object* v_a_1035_; lean_object* v___x_1036_; 
lean_dec(v_h__7_1024_);
lean_dec(v_h__4_1021_);
v_a_1035_ = lean_ctor_get(v_x_1016_, 0);
lean_inc(v_a_1035_);
lean_dec_ref_known(v_x_1016_, 1);
v___x_1036_ = lean_apply_5(v_h__2_1019_, v_x_1014_, v_x_1015_, v_a_1035_, v_x_1017_, lean_box(0));
return v___x_1036_;
}
case 3:
{
lean_object* v_a_1037_; lean_object* v_a_1038_; lean_object* v_a_1039_; lean_object* v_a_1040_; lean_object* v___x_1041_; 
lean_dec(v_h__7_1024_);
lean_dec(v_h__2_1019_);
v_a_1037_ = lean_ctor_get(v_x_1014_, 0);
lean_inc(v_a_1037_);
v_a_1038_ = lean_ctor_get(v_x_1014_, 1);
lean_inc(v_a_1038_);
lean_dec_ref_known(v_x_1014_, 2);
v_a_1039_ = lean_ctor_get(v_x_1016_, 0);
lean_inc(v_a_1039_);
v_a_1040_ = lean_ctor_get(v_x_1016_, 1);
lean_inc(v_a_1040_);
lean_dec_ref_known(v_x_1016_, 2);
v___x_1041_ = lean_apply_6(v_h__4_1021_, v_a_1037_, v_a_1038_, v_x_1015_, v_a_1039_, v_a_1040_, v_x_1017_);
return v___x_1041_;
}
default: 
{
lean_object* v___x_1042_; 
lean_dec(v_h__4_1021_);
lean_dec(v_h__2_1019_);
v___x_1042_ = lean_apply_10(v_h__7_1024_, v_x_1014_, v_x_1015_, v_x_1016_, v_x_1017_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_1042_;
}
}
}
case 4:
{
lean_dec(v_h__6_1023_);
lean_dec(v_h__4_1021_);
lean_dec(v_h__3_1020_);
lean_dec(v_h__1_1018_);
switch(lean_obj_tag(v_x_1016_))
{
case 1:
{
lean_object* v_a_1043_; lean_object* v___x_1044_; 
lean_dec(v_h__7_1024_);
lean_dec(v_h__5_1022_);
v_a_1043_ = lean_ctor_get(v_x_1016_, 0);
lean_inc(v_a_1043_);
lean_dec_ref_known(v_x_1016_, 1);
v___x_1044_ = lean_apply_5(v_h__2_1019_, v_x_1014_, v_x_1015_, v_a_1043_, v_x_1017_, lean_box(0));
return v___x_1044_;
}
case 4:
{
lean_object* v_a_1045_; lean_object* v_a_1046_; lean_object* v___x_1047_; 
lean_dec(v_h__7_1024_);
lean_dec(v_h__2_1019_);
v_a_1045_ = lean_ctor_get(v_x_1014_, 0);
lean_inc(v_a_1045_);
lean_dec_ref_known(v_x_1014_, 1);
v_a_1046_ = lean_ctor_get(v_x_1016_, 0);
lean_inc(v_a_1046_);
lean_dec_ref_known(v_x_1016_, 1);
v___x_1047_ = lean_apply_4(v_h__5_1022_, v_a_1045_, v_x_1015_, v_a_1046_, v_x_1017_);
return v___x_1047_;
}
default: 
{
lean_object* v___x_1048_; 
lean_dec(v_h__5_1022_);
lean_dec(v_h__2_1019_);
v___x_1048_ = lean_apply_10(v_h__7_1024_, v_x_1014_, v_x_1015_, v_x_1016_, v_x_1017_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_1048_;
}
}
}
case 5:
{
lean_dec(v_h__5_1022_);
lean_dec(v_h__4_1021_);
lean_dec(v_h__3_1020_);
lean_dec(v_h__1_1018_);
switch(lean_obj_tag(v_x_1016_))
{
case 1:
{
lean_object* v_a_1049_; lean_object* v___x_1050_; 
lean_dec(v_h__7_1024_);
lean_dec(v_h__6_1023_);
v_a_1049_ = lean_ctor_get(v_x_1016_, 0);
lean_inc(v_a_1049_);
lean_dec_ref_known(v_x_1016_, 1);
v___x_1050_ = lean_apply_5(v_h__2_1019_, v_x_1014_, v_x_1015_, v_a_1049_, v_x_1017_, lean_box(0));
return v___x_1050_;
}
case 5:
{
lean_object* v_a_1051_; lean_object* v_a_1052_; lean_object* v___x_1053_; 
lean_dec(v_h__7_1024_);
lean_dec(v_h__2_1019_);
v_a_1051_ = lean_ctor_get(v_x_1014_, 0);
lean_inc(v_a_1051_);
lean_dec_ref_known(v_x_1014_, 1);
v_a_1052_ = lean_ctor_get(v_x_1016_, 0);
lean_inc(v_a_1052_);
lean_dec_ref_known(v_x_1016_, 1);
v___x_1053_ = lean_apply_4(v_h__6_1023_, v_a_1051_, v_x_1015_, v_a_1052_, v_x_1017_);
return v___x_1053_;
}
default: 
{
lean_object* v___x_1054_; 
lean_dec(v_h__6_1023_);
lean_dec(v_h__2_1019_);
v___x_1054_ = lean_apply_10(v_h__7_1024_, v_x_1014_, v_x_1015_, v_x_1016_, v_x_1017_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_1054_;
}
}
}
default: 
{
lean_dec(v_h__6_1023_);
lean_dec(v_h__5_1022_);
lean_dec(v_h__4_1021_);
lean_dec(v_h__3_1020_);
lean_dec(v_h__1_1018_);
if (lean_obj_tag(v_x_1016_) == 1)
{
lean_object* v_a_1055_; lean_object* v___x_1056_; 
lean_dec(v_h__7_1024_);
v_a_1055_ = lean_ctor_get(v_x_1016_, 0);
lean_inc(v_a_1055_);
lean_dec_ref_known(v_x_1016_, 1);
v___x_1056_ = lean_apply_5(v_h__2_1019_, v_x_1014_, v_x_1015_, v_a_1055_, v_x_1017_, lean_box(0));
return v___x_1056_;
}
else
{
lean_object* v___x_1057_; 
lean_dec(v_h__2_1019_);
v___x_1057_ = lean_apply_10(v_h__7_1024_, v_x_1014_, v_x_1015_, v_x_1016_, v_x_1017_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_1057_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_normLtAux_match__1_splitter(lean_object* v_motive_1058_, lean_object* v_x_1059_, lean_object* v_x_1060_, lean_object* v_x_1061_, lean_object* v_x_1062_, lean_object* v_h__1_1063_, lean_object* v_h__2_1064_, lean_object* v_h__3_1065_, lean_object* v_h__4_1066_, lean_object* v_h__5_1067_, lean_object* v_h__6_1068_, lean_object* v_h__7_1069_){
_start:
{
switch(lean_obj_tag(v_x_1059_))
{
case 1:
{
lean_object* v_a_1070_; lean_object* v___x_1071_; 
lean_dec(v_h__7_1069_);
lean_dec(v_h__6_1068_);
lean_dec(v_h__5_1067_);
lean_dec(v_h__4_1066_);
lean_dec(v_h__3_1065_);
lean_dec(v_h__2_1064_);
v_a_1070_ = lean_ctor_get(v_x_1059_, 0);
lean_inc(v_a_1070_);
lean_dec_ref_known(v_x_1059_, 1);
v___x_1071_ = lean_apply_4(v_h__1_1063_, v_a_1070_, v_x_1060_, v_x_1061_, v_x_1062_);
return v___x_1071_;
}
case 2:
{
lean_dec(v_h__6_1068_);
lean_dec(v_h__5_1067_);
lean_dec(v_h__4_1066_);
lean_dec(v_h__1_1063_);
switch(lean_obj_tag(v_x_1061_))
{
case 1:
{
lean_object* v_a_1072_; lean_object* v___x_1073_; 
lean_dec(v_h__7_1069_);
lean_dec(v_h__3_1065_);
v_a_1072_ = lean_ctor_get(v_x_1061_, 0);
lean_inc(v_a_1072_);
lean_dec_ref_known(v_x_1061_, 1);
v___x_1073_ = lean_apply_5(v_h__2_1064_, v_x_1059_, v_x_1060_, v_a_1072_, v_x_1062_, lean_box(0));
return v___x_1073_;
}
case 2:
{
lean_object* v_a_1074_; lean_object* v_a_1075_; lean_object* v_a_1076_; lean_object* v_a_1077_; lean_object* v___x_1078_; 
lean_dec(v_h__7_1069_);
lean_dec(v_h__2_1064_);
v_a_1074_ = lean_ctor_get(v_x_1059_, 0);
lean_inc(v_a_1074_);
v_a_1075_ = lean_ctor_get(v_x_1059_, 1);
lean_inc(v_a_1075_);
lean_dec_ref_known(v_x_1059_, 2);
v_a_1076_ = lean_ctor_get(v_x_1061_, 0);
lean_inc(v_a_1076_);
v_a_1077_ = lean_ctor_get(v_x_1061_, 1);
lean_inc(v_a_1077_);
lean_dec_ref_known(v_x_1061_, 2);
v___x_1078_ = lean_apply_6(v_h__3_1065_, v_a_1074_, v_a_1075_, v_x_1060_, v_a_1076_, v_a_1077_, v_x_1062_);
return v___x_1078_;
}
default: 
{
lean_object* v___x_1079_; 
lean_dec(v_h__3_1065_);
lean_dec(v_h__2_1064_);
v___x_1079_ = lean_apply_10(v_h__7_1069_, v_x_1059_, v_x_1060_, v_x_1061_, v_x_1062_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_1079_;
}
}
}
case 3:
{
lean_dec(v_h__6_1068_);
lean_dec(v_h__5_1067_);
lean_dec(v_h__3_1065_);
lean_dec(v_h__1_1063_);
switch(lean_obj_tag(v_x_1061_))
{
case 1:
{
lean_object* v_a_1080_; lean_object* v___x_1081_; 
lean_dec(v_h__7_1069_);
lean_dec(v_h__4_1066_);
v_a_1080_ = lean_ctor_get(v_x_1061_, 0);
lean_inc(v_a_1080_);
lean_dec_ref_known(v_x_1061_, 1);
v___x_1081_ = lean_apply_5(v_h__2_1064_, v_x_1059_, v_x_1060_, v_a_1080_, v_x_1062_, lean_box(0));
return v___x_1081_;
}
case 3:
{
lean_object* v_a_1082_; lean_object* v_a_1083_; lean_object* v_a_1084_; lean_object* v_a_1085_; lean_object* v___x_1086_; 
lean_dec(v_h__7_1069_);
lean_dec(v_h__2_1064_);
v_a_1082_ = lean_ctor_get(v_x_1059_, 0);
lean_inc(v_a_1082_);
v_a_1083_ = lean_ctor_get(v_x_1059_, 1);
lean_inc(v_a_1083_);
lean_dec_ref_known(v_x_1059_, 2);
v_a_1084_ = lean_ctor_get(v_x_1061_, 0);
lean_inc(v_a_1084_);
v_a_1085_ = lean_ctor_get(v_x_1061_, 1);
lean_inc(v_a_1085_);
lean_dec_ref_known(v_x_1061_, 2);
v___x_1086_ = lean_apply_6(v_h__4_1066_, v_a_1082_, v_a_1083_, v_x_1060_, v_a_1084_, v_a_1085_, v_x_1062_);
return v___x_1086_;
}
default: 
{
lean_object* v___x_1087_; 
lean_dec(v_h__4_1066_);
lean_dec(v_h__2_1064_);
v___x_1087_ = lean_apply_10(v_h__7_1069_, v_x_1059_, v_x_1060_, v_x_1061_, v_x_1062_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_1087_;
}
}
}
case 4:
{
lean_dec(v_h__6_1068_);
lean_dec(v_h__4_1066_);
lean_dec(v_h__3_1065_);
lean_dec(v_h__1_1063_);
switch(lean_obj_tag(v_x_1061_))
{
case 1:
{
lean_object* v_a_1088_; lean_object* v___x_1089_; 
lean_dec(v_h__7_1069_);
lean_dec(v_h__5_1067_);
v_a_1088_ = lean_ctor_get(v_x_1061_, 0);
lean_inc(v_a_1088_);
lean_dec_ref_known(v_x_1061_, 1);
v___x_1089_ = lean_apply_5(v_h__2_1064_, v_x_1059_, v_x_1060_, v_a_1088_, v_x_1062_, lean_box(0));
return v___x_1089_;
}
case 4:
{
lean_object* v_a_1090_; lean_object* v_a_1091_; lean_object* v___x_1092_; 
lean_dec(v_h__7_1069_);
lean_dec(v_h__2_1064_);
v_a_1090_ = lean_ctor_get(v_x_1059_, 0);
lean_inc(v_a_1090_);
lean_dec_ref_known(v_x_1059_, 1);
v_a_1091_ = lean_ctor_get(v_x_1061_, 0);
lean_inc(v_a_1091_);
lean_dec_ref_known(v_x_1061_, 1);
v___x_1092_ = lean_apply_4(v_h__5_1067_, v_a_1090_, v_x_1060_, v_a_1091_, v_x_1062_);
return v___x_1092_;
}
default: 
{
lean_object* v___x_1093_; 
lean_dec(v_h__5_1067_);
lean_dec(v_h__2_1064_);
v___x_1093_ = lean_apply_10(v_h__7_1069_, v_x_1059_, v_x_1060_, v_x_1061_, v_x_1062_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_1093_;
}
}
}
case 5:
{
lean_dec(v_h__5_1067_);
lean_dec(v_h__4_1066_);
lean_dec(v_h__3_1065_);
lean_dec(v_h__1_1063_);
switch(lean_obj_tag(v_x_1061_))
{
case 1:
{
lean_object* v_a_1094_; lean_object* v___x_1095_; 
lean_dec(v_h__7_1069_);
lean_dec(v_h__6_1068_);
v_a_1094_ = lean_ctor_get(v_x_1061_, 0);
lean_inc(v_a_1094_);
lean_dec_ref_known(v_x_1061_, 1);
v___x_1095_ = lean_apply_5(v_h__2_1064_, v_x_1059_, v_x_1060_, v_a_1094_, v_x_1062_, lean_box(0));
return v___x_1095_;
}
case 5:
{
lean_object* v_a_1096_; lean_object* v_a_1097_; lean_object* v___x_1098_; 
lean_dec(v_h__7_1069_);
lean_dec(v_h__2_1064_);
v_a_1096_ = lean_ctor_get(v_x_1059_, 0);
lean_inc(v_a_1096_);
lean_dec_ref_known(v_x_1059_, 1);
v_a_1097_ = lean_ctor_get(v_x_1061_, 0);
lean_inc(v_a_1097_);
lean_dec_ref_known(v_x_1061_, 1);
v___x_1098_ = lean_apply_4(v_h__6_1068_, v_a_1096_, v_x_1060_, v_a_1097_, v_x_1062_);
return v___x_1098_;
}
default: 
{
lean_object* v___x_1099_; 
lean_dec(v_h__6_1068_);
lean_dec(v_h__2_1064_);
v___x_1099_ = lean_apply_10(v_h__7_1069_, v_x_1059_, v_x_1060_, v_x_1061_, v_x_1062_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_1099_;
}
}
}
default: 
{
lean_dec(v_h__6_1068_);
lean_dec(v_h__5_1067_);
lean_dec(v_h__4_1066_);
lean_dec(v_h__3_1065_);
lean_dec(v_h__1_1063_);
if (lean_obj_tag(v_x_1061_) == 1)
{
lean_object* v_a_1100_; lean_object* v___x_1101_; 
lean_dec(v_h__7_1069_);
v_a_1100_ = lean_ctor_get(v_x_1061_, 0);
lean_inc(v_a_1100_);
lean_dec_ref_known(v_x_1061_, 1);
v___x_1101_ = lean_apply_5(v_h__2_1064_, v_x_1059_, v_x_1060_, v_a_1100_, v_x_1062_, lean_box(0));
return v___x_1101_;
}
else
{
lean_object* v___x_1102_; 
lean_dec(v_h__2_1064_);
v___x_1102_ = lean_apply_10(v_h__7_1069_, v_x_1059_, v_x_1060_, v_x_1061_, v_x_1062_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_1102_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Level_normLt(lean_object* v_l_u2081_1103_, lean_object* v_l_u2082_1104_){
_start:
{
lean_object* v___x_1105_; uint8_t v___x_1106_; 
v___x_1105_ = lean_unsigned_to_nat(0u);
v___x_1106_ = l_Lean_Level_normLtAux(v_l_u2081_1103_, v___x_1105_, v_l_u2082_1104_, v___x_1105_);
return v___x_1106_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_normLt___boxed(lean_object* v_l_u2081_1107_, lean_object* v_l_u2082_1108_){
_start:
{
uint8_t v_res_1109_; lean_object* v_r_1110_; 
v_res_1109_ = l_Lean_Level_normLt(v_l_u2081_1107_, v_l_u2082_1108_);
lean_dec(v_l_u2082_1108_);
lean_dec(v_l_u2081_1107_);
v_r_1110_ = lean_box(v_res_1109_);
return v_r_1110_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_isAlreadyNormalizedCheap(lean_object* v_x_1111_){
_start:
{
switch(lean_obj_tag(v_x_1111_))
{
case 0:
{
uint8_t v___x_1112_; 
v___x_1112_ = 1;
return v___x_1112_;
}
case 4:
{
uint8_t v___x_1113_; 
v___x_1113_ = 1;
return v___x_1113_;
}
case 5:
{
uint8_t v___x_1114_; 
v___x_1114_ = 1;
return v___x_1114_;
}
case 1:
{
lean_object* v_a_1115_; 
v_a_1115_ = lean_ctor_get(v_x_1111_, 0);
v_x_1111_ = v_a_1115_;
goto _start;
}
default: 
{
uint8_t v___x_1117_; 
v___x_1117_ = 0;
return v___x_1117_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_isAlreadyNormalizedCheap___boxed(lean_object* v_x_1118_){
_start:
{
uint8_t v_res_1119_; lean_object* v_r_1120_; 
v_res_1119_ = l_Lean_Level_isAlreadyNormalizedCheap(v_x_1118_);
lean_dec(v_x_1118_);
v_r_1120_ = lean_box(v_res_1119_);
return v_r_1120_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_mkIMaxAux(lean_object* v_x_1121_, lean_object* v_x_1122_){
_start:
{
lean_object* v_u_u2081_1124_; lean_object* v_u_u2082_1125_; 
if (lean_obj_tag(v_x_1122_) == 0)
{
lean_dec(v_x_1121_);
return v_x_1122_;
}
else
{
switch(lean_obj_tag(v_x_1121_))
{
case 0:
{
return v_x_1122_;
}
case 1:
{
lean_object* v_a_1128_; 
v_a_1128_ = lean_ctor_get(v_x_1121_, 0);
if (lean_obj_tag(v_a_1128_) == 0)
{
lean_dec_ref_known(v_x_1121_, 1);
return v_x_1122_;
}
else
{
v_u_u2081_1124_ = v_x_1121_;
v_u_u2082_1125_ = v_x_1122_;
goto v___jp_1123_;
}
}
default: 
{
v_u_u2081_1124_ = v_x_1121_;
v_u_u2082_1125_ = v_x_1122_;
goto v___jp_1123_;
}
}
}
v___jp_1123_:
{
uint8_t v___x_1126_; 
v___x_1126_ = lean_level_eq(v_u_u2081_1124_, v_u_u2082_1125_);
if (v___x_1126_ == 0)
{
lean_object* v___x_1127_; 
v___x_1127_ = l_Lean_Level_imax___override(v_u_u2081_1124_, v_u_u2082_1125_);
return v___x_1127_;
}
else
{
lean_dec(v_u_u2082_1125_);
return v_u_u2081_1124_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_getMaxArgsAux(lean_object* v_normalize_1129_, lean_object* v_x_1130_, uint8_t v_x_1131_, lean_object* v_x_1132_){
_start:
{
if (lean_obj_tag(v_x_1130_) == 2)
{
lean_object* v_a_1133_; lean_object* v_a_1134_; lean_object* v___x_1135_; 
v_a_1133_ = lean_ctor_get(v_x_1130_, 0);
lean_inc(v_a_1133_);
v_a_1134_ = lean_ctor_get(v_x_1130_, 1);
lean_inc(v_a_1134_);
lean_dec_ref_known(v_x_1130_, 2);
lean_inc_ref(v_normalize_1129_);
v___x_1135_ = l___private_Lean_Level_0__Lean_Level_getMaxArgsAux(v_normalize_1129_, v_a_1133_, v_x_1131_, v_x_1132_);
v_x_1130_ = v_a_1134_;
v_x_1132_ = v___x_1135_;
goto _start;
}
else
{
if (v_x_1131_ == 0)
{
lean_object* v___x_1137_; uint8_t v___x_1138_; 
lean_inc_ref(v_normalize_1129_);
v___x_1137_ = lean_apply_1(v_normalize_1129_, v_x_1130_);
v___x_1138_ = 1;
v_x_1130_ = v___x_1137_;
v_x_1131_ = v___x_1138_;
goto _start;
}
else
{
lean_object* v___x_1140_; 
lean_dec_ref(v_normalize_1129_);
v___x_1140_ = lean_array_push(v_x_1132_, v_x_1130_);
return v___x_1140_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_getMaxArgsAux___boxed(lean_object* v_normalize_1141_, lean_object* v_x_1142_, lean_object* v_x_1143_, lean_object* v_x_1144_){
_start:
{
uint8_t v_x_31__boxed_1145_; lean_object* v_res_1146_; 
v_x_31__boxed_1145_ = lean_unbox(v_x_1143_);
v_res_1146_ = l___private_Lean_Level_0__Lean_Level_getMaxArgsAux(v_normalize_1141_, v_x_1142_, v_x_31__boxed_1145_, v_x_1144_);
return v_res_1146_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_accMax(lean_object* v_result_1147_, lean_object* v_prev_1148_, lean_object* v_offset_1149_){
_start:
{
uint8_t v___x_1150_; 
v___x_1150_ = l_Lean_Level_isZero(v_result_1147_);
if (v___x_1150_ == 0)
{
lean_object* v___x_1151_; lean_object* v___x_1152_; 
v___x_1151_ = l_Lean_Level_addOffsetAux(v_offset_1149_, v_prev_1148_);
v___x_1152_ = l_Lean_Level_max___override(v_result_1147_, v___x_1151_);
return v___x_1152_;
}
else
{
lean_object* v___x_1153_; 
lean_dec(v_result_1147_);
v___x_1153_ = l_Lean_Level_addOffsetAux(v_offset_1149_, v_prev_1148_);
return v___x_1153_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_mkMaxAux(lean_object* v_lvls_1154_, lean_object* v_extraK_1155_, lean_object* v_i_1156_, lean_object* v_prev_1157_, lean_object* v_prevK_1158_, lean_object* v_result_1159_){
_start:
{
lean_object* v___x_1160_; uint8_t v___x_1161_; 
v___x_1160_ = lean_array_get_size(v_lvls_1154_);
v___x_1161_ = lean_nat_dec_lt(v_i_1156_, v___x_1160_);
if (v___x_1161_ == 0)
{
lean_object* v___x_1162_; lean_object* v___x_1163_; 
lean_dec(v_i_1156_);
v___x_1162_ = lean_nat_add(v_extraK_1155_, v_prevK_1158_);
lean_dec(v_prevK_1158_);
v___x_1163_ = l___private_Lean_Level_0__Lean_Level_accMax(v_result_1159_, v_prev_1157_, v___x_1162_);
return v___x_1163_;
}
else
{
lean_object* v_lvl_1164_; lean_object* v_curr_1165_; lean_object* v_currK_1166_; uint8_t v___x_1167_; 
v_lvl_1164_ = lean_array_fget_borrowed(v_lvls_1154_, v_i_1156_);
v_curr_1165_ = l_Lean_Level_getLevelOffset(v_lvl_1164_);
v_currK_1166_ = l_Lean_Level_getOffset(v_lvl_1164_);
v___x_1167_ = lean_level_eq(v_curr_1165_, v_prev_1157_);
if (v___x_1167_ == 0)
{
lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; 
v___x_1168_ = lean_unsigned_to_nat(1u);
v___x_1169_ = lean_nat_add(v_i_1156_, v___x_1168_);
lean_dec(v_i_1156_);
v___x_1170_ = lean_nat_add(v_extraK_1155_, v_prevK_1158_);
lean_dec(v_prevK_1158_);
v___x_1171_ = l___private_Lean_Level_0__Lean_Level_accMax(v_result_1159_, v_prev_1157_, v___x_1170_);
v_i_1156_ = v___x_1169_;
v_prev_1157_ = v_curr_1165_;
v_prevK_1158_ = v_currK_1166_;
v_result_1159_ = v___x_1171_;
goto _start;
}
else
{
lean_object* v___x_1173_; lean_object* v___x_1174_; 
lean_dec(v_prevK_1158_);
lean_dec(v_prev_1157_);
v___x_1173_ = lean_unsigned_to_nat(1u);
v___x_1174_ = lean_nat_add(v_i_1156_, v___x_1173_);
lean_dec(v_i_1156_);
v_i_1156_ = v___x_1174_;
v_prev_1157_ = v_curr_1165_;
v_prevK_1158_ = v_currK_1166_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_mkMaxAux___boxed(lean_object* v_lvls_1176_, lean_object* v_extraK_1177_, lean_object* v_i_1178_, lean_object* v_prev_1179_, lean_object* v_prevK_1180_, lean_object* v_result_1181_){
_start:
{
lean_object* v_res_1182_; 
v_res_1182_ = l___private_Lean_Level_0__Lean_Level_mkMaxAux(v_lvls_1176_, v_extraK_1177_, v_i_1178_, v_prev_1179_, v_prevK_1180_, v_result_1181_);
lean_dec(v_extraK_1177_);
lean_dec_ref(v_lvls_1176_);
return v_res_1182_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_skipExplicit(lean_object* v_lvls_1183_, lean_object* v_i_1184_){
_start:
{
lean_object* v___x_1185_; uint8_t v___x_1186_; 
v___x_1185_ = lean_array_get_size(v_lvls_1183_);
v___x_1186_ = lean_nat_dec_lt(v_i_1184_, v___x_1185_);
if (v___x_1186_ == 0)
{
return v_i_1184_;
}
else
{
lean_object* v_lvl_1187_; lean_object* v___x_1188_; uint8_t v___x_1189_; 
v_lvl_1187_ = lean_array_fget_borrowed(v_lvls_1183_, v_i_1184_);
v___x_1188_ = l_Lean_Level_getLevelOffset(v_lvl_1187_);
v___x_1189_ = l_Lean_Level_isZero(v___x_1188_);
lean_dec(v___x_1188_);
if (v___x_1189_ == 0)
{
return v_i_1184_;
}
else
{
lean_object* v___x_1190_; lean_object* v___x_1191_; 
v___x_1190_ = lean_unsigned_to_nat(1u);
v___x_1191_ = lean_nat_add(v_i_1184_, v___x_1190_);
lean_dec(v_i_1184_);
v_i_1184_ = v___x_1191_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_skipExplicit___boxed(lean_object* v_lvls_1193_, lean_object* v_i_1194_){
_start:
{
lean_object* v_res_1195_; 
v_res_1195_ = l___private_Lean_Level_0__Lean_Level_skipExplicit(v_lvls_1193_, v_i_1194_);
lean_dec_ref(v_lvls_1193_);
return v_res_1195_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Level_0__Lean_Level_isExplicitSubsumedAux(lean_object* v_lvls_1196_, lean_object* v_maxExplicit_1197_, lean_object* v_i_1198_){
_start:
{
lean_object* v___x_1199_; uint8_t v___x_1200_; 
v___x_1199_ = lean_array_get_size(v_lvls_1196_);
v___x_1200_ = lean_nat_dec_lt(v_i_1198_, v___x_1199_);
if (v___x_1200_ == 0)
{
lean_dec(v_i_1198_);
return v___x_1200_;
}
else
{
lean_object* v_lvl_1201_; lean_object* v___x_1202_; uint8_t v___x_1203_; 
v_lvl_1201_ = lean_array_fget_borrowed(v_lvls_1196_, v_i_1198_);
v___x_1202_ = l_Lean_Level_getOffset(v_lvl_1201_);
v___x_1203_ = lean_nat_dec_le(v_maxExplicit_1197_, v___x_1202_);
lean_dec(v___x_1202_);
if (v___x_1203_ == 0)
{
lean_object* v___x_1204_; lean_object* v___x_1205_; 
v___x_1204_ = lean_unsigned_to_nat(1u);
v___x_1205_ = lean_nat_add(v_i_1198_, v___x_1204_);
lean_dec(v_i_1198_);
v_i_1198_ = v___x_1205_;
goto _start;
}
else
{
lean_dec(v_i_1198_);
return v___x_1203_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_isExplicitSubsumedAux___boxed(lean_object* v_lvls_1207_, lean_object* v_maxExplicit_1208_, lean_object* v_i_1209_){
_start:
{
uint8_t v_res_1210_; lean_object* v_r_1211_; 
v_res_1210_ = l___private_Lean_Level_0__Lean_Level_isExplicitSubsumedAux(v_lvls_1207_, v_maxExplicit_1208_, v_i_1209_);
lean_dec(v_maxExplicit_1208_);
lean_dec_ref(v_lvls_1207_);
v_r_1211_ = lean_box(v_res_1210_);
return v_r_1211_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Level_0__Lean_Level_isExplicitSubsumed(lean_object* v_lvls_1212_, lean_object* v_firstNonExplicit_1213_){
_start:
{
lean_object* v___x_1214_; uint8_t v___x_1215_; 
v___x_1214_ = lean_unsigned_to_nat(0u);
v___x_1215_ = lean_nat_dec_eq(v_firstNonExplicit_1213_, v___x_1214_);
if (v___x_1215_ == 0)
{
lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v_max_1220_; uint8_t v___x_1221_; 
v___x_1216_ = lean_box(0);
v___x_1217_ = lean_unsigned_to_nat(1u);
v___x_1218_ = lean_nat_sub(v_firstNonExplicit_1213_, v___x_1217_);
v___x_1219_ = lean_array_get_borrowed(v___x_1216_, v_lvls_1212_, v___x_1218_);
lean_dec(v___x_1218_);
v_max_1220_ = l_Lean_Level_getOffset(v___x_1219_);
v___x_1221_ = l___private_Lean_Level_0__Lean_Level_isExplicitSubsumedAux(v_lvls_1212_, v_max_1220_, v_firstNonExplicit_1213_);
lean_dec(v_max_1220_);
return v___x_1221_;
}
else
{
uint8_t v___x_1222_; 
lean_dec(v_firstNonExplicit_1213_);
v___x_1222_ = 0;
return v___x_1222_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_isExplicitSubsumed___boxed(lean_object* v_lvls_1223_, lean_object* v_firstNonExplicit_1224_){
_start:
{
uint8_t v_res_1225_; lean_object* v_r_1226_; 
v_res_1225_ = l___private_Lean_Level_0__Lean_Level_isExplicitSubsumed(v_lvls_1223_, v_firstNonExplicit_1224_);
lean_dec_ref(v_lvls_1223_);
v_r_1226_ = lean_box(v_res_1225_);
return v_r_1226_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Level_normalize_spec__2(lean_object* v_msg_1227_){
_start:
{
lean_object* v___x_1228_; lean_object* v___x_1229_; 
v___x_1228_ = lean_box(0);
v___x_1229_ = lean_panic_fn_borrowed(v___x_1228_, v_msg_1227_);
return v___x_1229_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1_spec__1___redArg(lean_object* v_hi_1230_, lean_object* v_pivot_1231_, lean_object* v_as_1232_, lean_object* v_i_1233_, lean_object* v_k_1234_){
_start:
{
uint8_t v___x_1235_; 
v___x_1235_ = lean_nat_dec_lt(v_k_1234_, v_hi_1230_);
if (v___x_1235_ == 0)
{
lean_object* v___x_1236_; lean_object* v___x_1237_; 
lean_dec(v_k_1234_);
v___x_1236_ = lean_array_fswap(v_as_1232_, v_i_1233_, v_hi_1230_);
v___x_1237_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1237_, 0, v_i_1233_);
lean_ctor_set(v___x_1237_, 1, v___x_1236_);
return v___x_1237_;
}
else
{
lean_object* v___x_1238_; uint8_t v___x_1239_; 
v___x_1238_ = lean_array_fget_borrowed(v_as_1232_, v_k_1234_);
v___x_1239_ = l_Lean_Level_normLt(v___x_1238_, v_pivot_1231_);
if (v___x_1239_ == 0)
{
lean_object* v___x_1240_; lean_object* v___x_1241_; 
v___x_1240_ = lean_unsigned_to_nat(1u);
v___x_1241_ = lean_nat_add(v_k_1234_, v___x_1240_);
lean_dec(v_k_1234_);
v_k_1234_ = v___x_1241_;
goto _start;
}
else
{
lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; 
v___x_1243_ = lean_array_fswap(v_as_1232_, v_i_1233_, v_k_1234_);
v___x_1244_ = lean_unsigned_to_nat(1u);
v___x_1245_ = lean_nat_add(v_i_1233_, v___x_1244_);
lean_dec(v_i_1233_);
v___x_1246_ = lean_nat_add(v_k_1234_, v___x_1244_);
lean_dec(v_k_1234_);
v_as_1232_ = v___x_1243_;
v_i_1233_ = v___x_1245_;
v_k_1234_ = v___x_1246_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1_spec__1___redArg___boxed(lean_object* v_hi_1248_, lean_object* v_pivot_1249_, lean_object* v_as_1250_, lean_object* v_i_1251_, lean_object* v_k_1252_){
_start:
{
lean_object* v_res_1253_; 
v_res_1253_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1_spec__1___redArg(v_hi_1248_, v_pivot_1249_, v_as_1250_, v_i_1251_, v_k_1252_);
lean_dec(v_pivot_1249_);
lean_dec(v_hi_1248_);
return v_res_1253_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1___redArg(lean_object* v_n_1254_, lean_object* v_as_1255_, lean_object* v_lo_1256_, lean_object* v_hi_1257_){
_start:
{
lean_object* v___y_1259_; uint8_t v___x_1269_; 
v___x_1269_ = lean_nat_dec_lt(v_lo_1256_, v_hi_1257_);
if (v___x_1269_ == 0)
{
lean_dec(v_lo_1256_);
return v_as_1255_;
}
else
{
lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v_mid_1272_; lean_object* v___y_1274_; lean_object* v___y_1280_; lean_object* v___x_1285_; lean_object* v___x_1286_; uint8_t v___x_1287_; 
v___x_1270_ = lean_nat_add(v_lo_1256_, v_hi_1257_);
v___x_1271_ = lean_unsigned_to_nat(1u);
v_mid_1272_ = lean_nat_shiftr(v___x_1270_, v___x_1271_);
lean_dec(v___x_1270_);
v___x_1285_ = lean_array_fget_borrowed(v_as_1255_, v_mid_1272_);
v___x_1286_ = lean_array_fget_borrowed(v_as_1255_, v_lo_1256_);
v___x_1287_ = l_Lean_Level_normLt(v___x_1285_, v___x_1286_);
if (v___x_1287_ == 0)
{
v___y_1280_ = v_as_1255_;
goto v___jp_1279_;
}
else
{
lean_object* v___x_1288_; 
v___x_1288_ = lean_array_fswap(v_as_1255_, v_lo_1256_, v_mid_1272_);
v___y_1280_ = v___x_1288_;
goto v___jp_1279_;
}
v___jp_1273_:
{
lean_object* v___x_1275_; lean_object* v___x_1276_; uint8_t v___x_1277_; 
v___x_1275_ = lean_array_fget_borrowed(v___y_1274_, v_mid_1272_);
v___x_1276_ = lean_array_fget_borrowed(v___y_1274_, v_hi_1257_);
v___x_1277_ = l_Lean_Level_normLt(v___x_1275_, v___x_1276_);
if (v___x_1277_ == 0)
{
lean_dec(v_mid_1272_);
v___y_1259_ = v___y_1274_;
goto v___jp_1258_;
}
else
{
lean_object* v___x_1278_; 
v___x_1278_ = lean_array_fswap(v___y_1274_, v_mid_1272_, v_hi_1257_);
lean_dec(v_mid_1272_);
v___y_1259_ = v___x_1278_;
goto v___jp_1258_;
}
}
v___jp_1279_:
{
lean_object* v___x_1281_; lean_object* v___x_1282_; uint8_t v___x_1283_; 
v___x_1281_ = lean_array_fget_borrowed(v___y_1280_, v_hi_1257_);
v___x_1282_ = lean_array_fget_borrowed(v___y_1280_, v_lo_1256_);
v___x_1283_ = l_Lean_Level_normLt(v___x_1281_, v___x_1282_);
if (v___x_1283_ == 0)
{
v___y_1274_ = v___y_1280_;
goto v___jp_1273_;
}
else
{
lean_object* v___x_1284_; 
v___x_1284_ = lean_array_fswap(v___y_1280_, v_lo_1256_, v_hi_1257_);
v___y_1274_ = v___x_1284_;
goto v___jp_1273_;
}
}
}
v___jp_1258_:
{
lean_object* v_pivot_1260_; lean_object* v___x_1261_; lean_object* v_fst_1262_; lean_object* v_snd_1263_; uint8_t v___x_1264_; 
v_pivot_1260_ = lean_array_fget(v___y_1259_, v_hi_1257_);
lean_inc_n(v_lo_1256_, 2);
v___x_1261_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1_spec__1___redArg(v_hi_1257_, v_pivot_1260_, v___y_1259_, v_lo_1256_, v_lo_1256_);
lean_dec(v_pivot_1260_);
v_fst_1262_ = lean_ctor_get(v___x_1261_, 0);
lean_inc(v_fst_1262_);
v_snd_1263_ = lean_ctor_get(v___x_1261_, 1);
lean_inc(v_snd_1263_);
lean_dec_ref(v___x_1261_);
v___x_1264_ = lean_nat_dec_le(v_hi_1257_, v_fst_1262_);
if (v___x_1264_ == 0)
{
lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; 
v___x_1265_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1___redArg(v_n_1254_, v_snd_1263_, v_lo_1256_, v_fst_1262_);
v___x_1266_ = lean_unsigned_to_nat(1u);
v___x_1267_ = lean_nat_add(v_fst_1262_, v___x_1266_);
lean_dec(v_fst_1262_);
v_as_1255_ = v___x_1265_;
v_lo_1256_ = v___x_1267_;
goto _start;
}
else
{
lean_dec(v_fst_1262_);
lean_dec(v_lo_1256_);
return v_snd_1263_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1___redArg___boxed(lean_object* v_n_1289_, lean_object* v_as_1290_, lean_object* v_lo_1291_, lean_object* v_hi_1292_){
_start:
{
lean_object* v_res_1293_; 
v_res_1293_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1___redArg(v_n_1289_, v_as_1290_, v_lo_1291_, v_hi_1292_);
lean_dec(v_hi_1292_);
lean_dec(v_n_1289_);
return v_res_1293_;
}
}
static lean_object* _init_l_Lean_Level_normalize___closed__3(void){
_start:
{
lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; 
v___x_1298_ = ((lean_object*)(l_Lean_Level_normalize___closed__2));
v___x_1299_ = lean_unsigned_to_nat(11u);
v___x_1300_ = lean_unsigned_to_nat(403u);
v___x_1301_ = ((lean_object*)(l_Lean_Level_normalize___closed__1));
v___x_1302_ = ((lean_object*)(l_Lean_Level_mvarId_x21___closed__0));
v___x_1303_ = l_mkPanicMessageWithDecl(v___x_1302_, v___x_1301_, v___x_1300_, v___x_1299_, v___x_1298_);
return v___x_1303_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_normalize(lean_object* v_l_1304_){
_start:
{
uint8_t v___x_1305_; 
v___x_1305_ = l_Lean_Level_isAlreadyNormalizedCheap(v_l_1304_);
if (v___x_1305_ == 0)
{
lean_object* v_k_1306_; lean_object* v_u_1307_; 
v_k_1306_ = l_Lean_Level_getOffset(v_l_1304_);
v_u_1307_ = l_Lean_Level_getLevelOffset(v_l_1304_);
switch(lean_obj_tag(v_u_1307_))
{
case 2:
{
lean_object* v_a_1308_; lean_object* v_a_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v_lvls_1313_; lean_object* v_lvls_1314_; lean_object* v___x_1315_; lean_object* v___y_1317_; lean_object* v___y_1318_; lean_object* v___y_1325_; lean_object* v___x_1329_; lean_object* v___y_1331_; lean_object* v___y_1332_; uint8_t v___x_1334_; 
v_a_1308_ = lean_ctor_get(v_u_1307_, 0);
lean_inc(v_a_1308_);
v_a_1309_ = lean_ctor_get(v_u_1307_, 1);
lean_inc(v_a_1309_);
lean_dec_ref_known(v_u_1307_, 2);
v___x_1310_ = lean_box(0);
v___x_1311_ = lean_unsigned_to_nat(0u);
v___x_1312_ = ((lean_object*)(l_Lean_Level_normalize___closed__0));
v_lvls_1313_ = l___private_Lean_Level_0__Lean_Level_getMaxArgsAux___at___00Lean_Level_normalize_spec__0(v_a_1308_, v___x_1305_, v___x_1312_);
v_lvls_1314_ = l___private_Lean_Level_0__Lean_Level_getMaxArgsAux___at___00Lean_Level_normalize_spec__0(v_a_1309_, v___x_1305_, v_lvls_1313_);
v___x_1315_ = lean_unsigned_to_nat(1u);
v___x_1329_ = lean_array_get_size(v_lvls_1314_);
v___x_1334_ = lean_nat_dec_eq(v___x_1329_, v___x_1311_);
if (v___x_1334_ == 0)
{
lean_object* v___x_1335_; lean_object* v___y_1337_; uint8_t v___x_1339_; 
v___x_1335_ = lean_nat_sub(v___x_1329_, v___x_1315_);
v___x_1339_ = lean_nat_dec_le(v___x_1311_, v___x_1335_);
if (v___x_1339_ == 0)
{
lean_inc(v___x_1335_);
v___y_1337_ = v___x_1335_;
goto v___jp_1336_;
}
else
{
v___y_1337_ = v___x_1311_;
goto v___jp_1336_;
}
v___jp_1336_:
{
uint8_t v___x_1338_; 
v___x_1338_ = lean_nat_dec_le(v___y_1337_, v___x_1335_);
if (v___x_1338_ == 0)
{
lean_dec(v___x_1335_);
lean_inc(v___y_1337_);
v___y_1331_ = v___y_1337_;
v___y_1332_ = v___y_1337_;
goto v___jp_1330_;
}
else
{
v___y_1331_ = v___y_1337_;
v___y_1332_ = v___x_1335_;
goto v___jp_1330_;
}
}
}
else
{
v___y_1325_ = v_lvls_1314_;
goto v___jp_1324_;
}
v___jp_1316_:
{
lean_object* v_lvl_u2081_1319_; lean_object* v_prev_1320_; lean_object* v_prevK_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; 
v_lvl_u2081_1319_ = lean_array_get_borrowed(v___x_1310_, v___y_1317_, v___y_1318_);
v_prev_1320_ = l_Lean_Level_getLevelOffset(v_lvl_u2081_1319_);
v_prevK_1321_ = l_Lean_Level_getOffset(v_lvl_u2081_1319_);
v___x_1322_ = lean_nat_add(v___y_1318_, v___x_1315_);
lean_dec(v___y_1318_);
v___x_1323_ = l___private_Lean_Level_0__Lean_Level_mkMaxAux(v___y_1317_, v_k_1306_, v___x_1322_, v_prev_1320_, v_prevK_1321_, v___x_1310_);
lean_dec(v_k_1306_);
lean_dec_ref(v___y_1317_);
return v___x_1323_;
}
v___jp_1324_:
{
lean_object* v_firstNonExplicit_1326_; uint8_t v___x_1327_; 
v_firstNonExplicit_1326_ = l___private_Lean_Level_0__Lean_Level_skipExplicit(v___y_1325_, v___x_1311_);
lean_inc(v_firstNonExplicit_1326_);
v___x_1327_ = l___private_Lean_Level_0__Lean_Level_isExplicitSubsumed(v___y_1325_, v_firstNonExplicit_1326_);
if (v___x_1327_ == 0)
{
lean_object* v___x_1328_; 
v___x_1328_ = lean_nat_sub(v_firstNonExplicit_1326_, v___x_1315_);
lean_dec(v_firstNonExplicit_1326_);
v___y_1317_ = v___y_1325_;
v___y_1318_ = v___x_1328_;
goto v___jp_1316_;
}
else
{
v___y_1317_ = v___y_1325_;
v___y_1318_ = v_firstNonExplicit_1326_;
goto v___jp_1316_;
}
}
v___jp_1330_:
{
lean_object* v___x_1333_; 
v___x_1333_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1___redArg(v___x_1329_, v_lvls_1314_, v___y_1331_, v___y_1332_);
lean_dec(v___y_1332_);
v___y_1325_ = v___x_1333_;
goto v___jp_1324_;
}
}
case 3:
{
lean_object* v_a_1340_; lean_object* v_a_1341_; uint8_t v___x_1342_; 
v_a_1340_ = lean_ctor_get(v_u_1307_, 0);
lean_inc(v_a_1340_);
v_a_1341_ = lean_ctor_get(v_u_1307_, 1);
lean_inc(v_a_1341_);
lean_dec_ref_known(v_u_1307_, 2);
v___x_1342_ = l_Lean_Level_isNeverZero(v_a_1341_);
if (v___x_1342_ == 0)
{
lean_object* v_l_u2081_1343_; lean_object* v_l_u2082_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; 
v_l_u2081_1343_ = l_Lean_Level_normalize(v_a_1340_);
lean_dec(v_a_1340_);
v_l_u2082_1344_ = l_Lean_Level_normalize(v_a_1341_);
lean_dec(v_a_1341_);
v___x_1345_ = l___private_Lean_Level_0__Lean_Level_mkIMaxAux(v_l_u2081_1343_, v_l_u2082_1344_);
v___x_1346_ = l_Lean_Level_addOffsetAux(v_k_1306_, v___x_1345_);
return v___x_1346_;
}
else
{
lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; 
v___x_1347_ = l_Lean_Level_max___override(v_a_1340_, v_a_1341_);
v___x_1348_ = l_Lean_Level_normalize(v___x_1347_);
lean_dec(v___x_1347_);
v___x_1349_ = l_Lean_Level_addOffsetAux(v_k_1306_, v___x_1348_);
return v___x_1349_;
}
}
default: 
{
lean_object* v___x_1350_; lean_object* v___x_1351_; 
lean_dec(v_u_1307_);
lean_dec(v_k_1306_);
v___x_1350_ = lean_obj_once(&l_Lean_Level_normalize___closed__3, &l_Lean_Level_normalize___closed__3_once, _init_l_Lean_Level_normalize___closed__3);
v___x_1351_ = l_panic___at___00Lean_Level_normalize_spec__2(v___x_1350_);
return v___x_1351_;
}
}
}
else
{
lean_inc(v_l_1304_);
return v_l_1304_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_getMaxArgsAux___at___00Lean_Level_normalize_spec__0(lean_object* v_x_1352_, uint8_t v_x_1353_, lean_object* v_x_1354_){
_start:
{
if (lean_obj_tag(v_x_1352_) == 2)
{
lean_object* v_a_1355_; lean_object* v_a_1356_; lean_object* v___x_1357_; 
v_a_1355_ = lean_ctor_get(v_x_1352_, 0);
lean_inc(v_a_1355_);
v_a_1356_ = lean_ctor_get(v_x_1352_, 1);
lean_inc(v_a_1356_);
lean_dec_ref_known(v_x_1352_, 2);
v___x_1357_ = l___private_Lean_Level_0__Lean_Level_getMaxArgsAux___at___00Lean_Level_normalize_spec__0(v_a_1355_, v_x_1353_, v_x_1354_);
v_x_1352_ = v_a_1356_;
v_x_1354_ = v___x_1357_;
goto _start;
}
else
{
if (v_x_1353_ == 0)
{
lean_object* v___x_1359_; uint8_t v___x_1360_; 
v___x_1359_ = l_Lean_Level_normalize(v_x_1352_);
lean_dec(v_x_1352_);
v___x_1360_ = 1;
v_x_1352_ = v___x_1359_;
v_x_1353_ = v___x_1360_;
goto _start;
}
else
{
lean_object* v___x_1362_; 
v___x_1362_ = lean_array_push(v_x_1354_, v_x_1352_);
return v___x_1362_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_getMaxArgsAux___at___00Lean_Level_normalize_spec__0___boxed(lean_object* v_x_1363_, lean_object* v_x_1364_, lean_object* v_x_1365_){
_start:
{
uint8_t v_x_483__boxed_1366_; lean_object* v_res_1367_; 
v_x_483__boxed_1366_ = lean_unbox(v_x_1364_);
v_res_1367_ = l___private_Lean_Level_0__Lean_Level_getMaxArgsAux___at___00Lean_Level_normalize_spec__0(v_x_1363_, v_x_483__boxed_1366_, v_x_1365_);
return v_res_1367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_normalize___boxed(lean_object* v_l_1368_){
_start:
{
lean_object* v_res_1369_; 
v_res_1369_ = l_Lean_Level_normalize(v_l_1368_);
lean_dec(v_l_1368_);
return v_res_1369_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1(lean_object* v_n_1370_, lean_object* v_as_1371_, lean_object* v_lo_1372_, lean_object* v_hi_1373_, lean_object* v_w_1374_, lean_object* v_hlo_1375_, lean_object* v_hhi_1376_){
_start:
{
lean_object* v___x_1377_; 
v___x_1377_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1___redArg(v_n_1370_, v_as_1371_, v_lo_1372_, v_hi_1373_);
return v___x_1377_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1___boxed(lean_object* v_n_1378_, lean_object* v_as_1379_, lean_object* v_lo_1380_, lean_object* v_hi_1381_, lean_object* v_w_1382_, lean_object* v_hlo_1383_, lean_object* v_hhi_1384_){
_start:
{
lean_object* v_res_1385_; 
v_res_1385_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1(v_n_1378_, v_as_1379_, v_lo_1380_, v_hi_1381_, v_w_1382_, v_hlo_1383_, v_hhi_1384_);
lean_dec(v_hi_1381_);
lean_dec(v_n_1378_);
return v_res_1385_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1_spec__1(lean_object* v_n_1386_, lean_object* v_lo_1387_, lean_object* v_hi_1388_, lean_object* v_hhi_1389_, lean_object* v_pivot_1390_, lean_object* v_as_1391_, lean_object* v_i_1392_, lean_object* v_k_1393_, lean_object* v_ilo_1394_, lean_object* v_ik_1395_, lean_object* v_w_1396_){
_start:
{
lean_object* v___x_1397_; 
v___x_1397_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1_spec__1___redArg(v_hi_1388_, v_pivot_1390_, v_as_1391_, v_i_1392_, v_k_1393_);
return v___x_1397_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1_spec__1___boxed(lean_object* v_n_1398_, lean_object* v_lo_1399_, lean_object* v_hi_1400_, lean_object* v_hhi_1401_, lean_object* v_pivot_1402_, lean_object* v_as_1403_, lean_object* v_i_1404_, lean_object* v_k_1405_, lean_object* v_ilo_1406_, lean_object* v_ik_1407_, lean_object* v_w_1408_){
_start:
{
lean_object* v_res_1409_; 
v_res_1409_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1_spec__1(v_n_1398_, v_lo_1399_, v_hi_1400_, v_hhi_1401_, v_pivot_1402_, v_as_1403_, v_i_1404_, v_k_1405_, v_ilo_1406_, v_ik_1407_, v_w_1408_);
lean_dec(v_pivot_1402_);
lean_dec(v_hi_1400_);
lean_dec(v_lo_1399_);
lean_dec(v_n_1398_);
return v_res_1409_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_isEquiv(lean_object* v_u_1410_, lean_object* v_v_1411_){
_start:
{
uint8_t v___x_1412_; 
v___x_1412_ = lean_level_eq(v_u_1410_, v_v_1411_);
if (v___x_1412_ == 0)
{
lean_object* v___x_1413_; lean_object* v___x_1414_; uint8_t v___x_1415_; 
v___x_1413_ = l_Lean_Level_normalize(v_u_1410_);
v___x_1414_ = l_Lean_Level_normalize(v_v_1411_);
v___x_1415_ = lean_level_eq(v___x_1413_, v___x_1414_);
lean_dec(v___x_1414_);
lean_dec(v___x_1413_);
return v___x_1415_;
}
else
{
return v___x_1412_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_isEquiv___boxed(lean_object* v_u_1416_, lean_object* v_v_1417_){
_start:
{
uint8_t v_res_1418_; lean_object* v_r_1419_; 
v_res_1418_ = l_Lean_Level_isEquiv(v_u_1416_, v_v_1417_);
lean_dec(v_v_1417_);
lean_dec(v_u_1416_);
v_r_1419_ = lean_box(v_res_1418_);
return v_r_1419_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_dec(lean_object* v_x_1420_){
_start:
{
lean_object* v_l_u2081_1422_; lean_object* v_l_u2082_1423_; 
switch(lean_obj_tag(v_x_1420_))
{
case 1:
{
lean_object* v_a_1436_; lean_object* v___x_1437_; 
v_a_1436_ = lean_ctor_get(v_x_1420_, 0);
lean_inc(v_a_1436_);
v___x_1437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1437_, 0, v_a_1436_);
return v___x_1437_;
}
case 2:
{
lean_object* v_a_1438_; lean_object* v_a_1439_; 
v_a_1438_ = lean_ctor_get(v_x_1420_, 0);
v_a_1439_ = lean_ctor_get(v_x_1420_, 1);
v_l_u2081_1422_ = v_a_1438_;
v_l_u2082_1423_ = v_a_1439_;
goto v___jp_1421_;
}
case 3:
{
lean_object* v_a_1440_; lean_object* v_a_1441_; 
v_a_1440_ = lean_ctor_get(v_x_1420_, 0);
v_a_1441_ = lean_ctor_get(v_x_1420_, 1);
v_l_u2081_1422_ = v_a_1440_;
v_l_u2082_1423_ = v_a_1441_;
goto v___jp_1421_;
}
default: 
{
lean_object* v___x_1442_; 
v___x_1442_ = lean_box(0);
return v___x_1442_;
}
}
v___jp_1421_:
{
lean_object* v___x_1424_; 
v___x_1424_ = l_Lean_Level_dec(v_l_u2081_1422_);
if (lean_obj_tag(v___x_1424_) == 0)
{
return v___x_1424_;
}
else
{
lean_object* v_val_1425_; lean_object* v___x_1426_; 
v_val_1425_ = lean_ctor_get(v___x_1424_, 0);
lean_inc(v_val_1425_);
lean_dec_ref_known(v___x_1424_, 1);
v___x_1426_ = l_Lean_Level_dec(v_l_u2082_1423_);
if (lean_obj_tag(v___x_1426_) == 0)
{
lean_dec(v_val_1425_);
return v___x_1426_;
}
else
{
lean_object* v_val_1427_; lean_object* v___x_1429_; uint8_t v_isShared_1430_; uint8_t v_isSharedCheck_1435_; 
v_val_1427_ = lean_ctor_get(v___x_1426_, 0);
v_isSharedCheck_1435_ = !lean_is_exclusive(v___x_1426_);
if (v_isSharedCheck_1435_ == 0)
{
v___x_1429_ = v___x_1426_;
v_isShared_1430_ = v_isSharedCheck_1435_;
goto v_resetjp_1428_;
}
else
{
lean_inc(v_val_1427_);
lean_dec(v___x_1426_);
v___x_1429_ = lean_box(0);
v_isShared_1430_ = v_isSharedCheck_1435_;
goto v_resetjp_1428_;
}
v_resetjp_1428_:
{
lean_object* v___x_1431_; lean_object* v___x_1433_; 
v___x_1431_ = l_Lean_Level_max___override(v_val_1425_, v_val_1427_);
if (v_isShared_1430_ == 0)
{
lean_ctor_set(v___x_1429_, 0, v___x_1431_);
v___x_1433_ = v___x_1429_;
goto v_reusejp_1432_;
}
else
{
lean_object* v_reuseFailAlloc_1434_; 
v_reuseFailAlloc_1434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1434_, 0, v___x_1431_);
v___x_1433_ = v_reuseFailAlloc_1434_;
goto v_reusejp_1432_;
}
v_reusejp_1432_:
{
return v___x_1433_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_dec___boxed(lean_object* v_x_1443_){
_start:
{
lean_object* v_res_1444_; 
v_res_1444_ = l_Lean_Level_dec(v_x_1443_);
lean_dec(v_x_1443_);
return v_res_1444_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_ctorIdx(lean_object* v_x_1445_){
_start:
{
switch(lean_obj_tag(v_x_1445_))
{
case 0:
{
lean_object* v___x_1446_; 
v___x_1446_ = lean_unsigned_to_nat(0u);
return v___x_1446_;
}
case 1:
{
lean_object* v___x_1447_; 
v___x_1447_ = lean_unsigned_to_nat(1u);
return v___x_1447_;
}
case 2:
{
lean_object* v___x_1448_; 
v___x_1448_ = lean_unsigned_to_nat(2u);
return v___x_1448_;
}
case 3:
{
lean_object* v___x_1449_; 
v___x_1449_ = lean_unsigned_to_nat(3u);
return v___x_1449_;
}
default: 
{
lean_object* v___x_1450_; 
v___x_1450_ = lean_unsigned_to_nat(4u);
return v___x_1450_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_ctorIdx___boxed(lean_object* v_x_1451_){
_start:
{
lean_object* v_res_1452_; 
v_res_1452_ = l_Lean_Level_PP_Result_ctorIdx(v_x_1451_);
lean_dec_ref(v_x_1451_);
return v_res_1452_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_ctorElim___redArg(lean_object* v_t_1453_, lean_object* v_k_1454_){
_start:
{
if (lean_obj_tag(v_t_1453_) == 2)
{
lean_object* v_a_1455_; lean_object* v_a_1456_; lean_object* v___x_1457_; 
v_a_1455_ = lean_ctor_get(v_t_1453_, 0);
lean_inc_ref(v_a_1455_);
v_a_1456_ = lean_ctor_get(v_t_1453_, 1);
lean_inc(v_a_1456_);
lean_dec_ref_known(v_t_1453_, 2);
v___x_1457_ = lean_apply_2(v_k_1454_, v_a_1455_, v_a_1456_);
return v___x_1457_;
}
else
{
lean_object* v_a_1458_; lean_object* v___x_1459_; 
v_a_1458_ = lean_ctor_get(v_t_1453_, 0);
lean_inc(v_a_1458_);
lean_dec_ref(v_t_1453_);
v___x_1459_ = lean_apply_1(v_k_1454_, v_a_1458_);
return v___x_1459_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_ctorElim(lean_object* v_motive__1_1460_, lean_object* v_ctorIdx_1461_, lean_object* v_t_1462_, lean_object* v_h_1463_, lean_object* v_k_1464_){
_start:
{
lean_object* v___x_1465_; 
v___x_1465_ = l_Lean_Level_PP_Result_ctorElim___redArg(v_t_1462_, v_k_1464_);
return v___x_1465_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_ctorElim___boxed(lean_object* v_motive__1_1466_, lean_object* v_ctorIdx_1467_, lean_object* v_t_1468_, lean_object* v_h_1469_, lean_object* v_k_1470_){
_start:
{
lean_object* v_res_1471_; 
v_res_1471_ = l_Lean_Level_PP_Result_ctorElim(v_motive__1_1466_, v_ctorIdx_1467_, v_t_1468_, v_h_1469_, v_k_1470_);
lean_dec(v_ctorIdx_1467_);
return v_res_1471_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_leaf_elim___redArg(lean_object* v_t_1472_, lean_object* v_leaf_1473_){
_start:
{
lean_object* v___x_1474_; 
v___x_1474_ = l_Lean_Level_PP_Result_ctorElim___redArg(v_t_1472_, v_leaf_1473_);
return v___x_1474_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_leaf_elim(lean_object* v_motive__1_1475_, lean_object* v_t_1476_, lean_object* v_h_1477_, lean_object* v_leaf_1478_){
_start:
{
lean_object* v___x_1479_; 
v___x_1479_ = l_Lean_Level_PP_Result_ctorElim___redArg(v_t_1476_, v_leaf_1478_);
return v___x_1479_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_num_elim___redArg(lean_object* v_t_1480_, lean_object* v_num_1481_){
_start:
{
lean_object* v___x_1482_; 
v___x_1482_ = l_Lean_Level_PP_Result_ctorElim___redArg(v_t_1480_, v_num_1481_);
return v___x_1482_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_num_elim(lean_object* v_motive__1_1483_, lean_object* v_t_1484_, lean_object* v_h_1485_, lean_object* v_num_1486_){
_start:
{
lean_object* v___x_1487_; 
v___x_1487_ = l_Lean_Level_PP_Result_ctorElim___redArg(v_t_1484_, v_num_1486_);
return v___x_1487_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_offset_elim___redArg(lean_object* v_t_1488_, lean_object* v_offset_1489_){
_start:
{
lean_object* v___x_1490_; 
v___x_1490_ = l_Lean_Level_PP_Result_ctorElim___redArg(v_t_1488_, v_offset_1489_);
return v___x_1490_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_offset_elim(lean_object* v_motive__1_1491_, lean_object* v_t_1492_, lean_object* v_h_1493_, lean_object* v_offset_1494_){
_start:
{
lean_object* v___x_1495_; 
v___x_1495_ = l_Lean_Level_PP_Result_ctorElim___redArg(v_t_1492_, v_offset_1494_);
return v___x_1495_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_maxNode_elim___redArg(lean_object* v_t_1496_, lean_object* v_maxNode_1497_){
_start:
{
lean_object* v___x_1498_; 
v___x_1498_ = l_Lean_Level_PP_Result_ctorElim___redArg(v_t_1496_, v_maxNode_1497_);
return v___x_1498_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_maxNode_elim(lean_object* v_motive__1_1499_, lean_object* v_t_1500_, lean_object* v_h_1501_, lean_object* v_maxNode_1502_){
_start:
{
lean_object* v___x_1503_; 
v___x_1503_ = l_Lean_Level_PP_Result_ctorElim___redArg(v_t_1500_, v_maxNode_1502_);
return v___x_1503_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_imaxNode_elim___redArg(lean_object* v_t_1504_, lean_object* v_imaxNode_1505_){
_start:
{
lean_object* v___x_1506_; 
v___x_1506_ = l_Lean_Level_PP_Result_ctorElim___redArg(v_t_1504_, v_imaxNode_1505_);
return v___x_1506_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_imaxNode_elim(lean_object* v_motive__1_1507_, lean_object* v_t_1508_, lean_object* v_h_1509_, lean_object* v_imaxNode_1510_){
_start:
{
lean_object* v___x_1511_; 
v___x_1511_ = l_Lean_Level_PP_Result_ctorElim___redArg(v_t_1508_, v_imaxNode_1510_);
return v___x_1511_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_succ(lean_object* v_x_1512_){
_start:
{
switch(lean_obj_tag(v_x_1512_))
{
case 2:
{
lean_object* v_a_1513_; lean_object* v_a_1514_; lean_object* v___x_1516_; uint8_t v_isShared_1517_; uint8_t v_isSharedCheck_1523_; 
v_a_1513_ = lean_ctor_get(v_x_1512_, 0);
v_a_1514_ = lean_ctor_get(v_x_1512_, 1);
v_isSharedCheck_1523_ = !lean_is_exclusive(v_x_1512_);
if (v_isSharedCheck_1523_ == 0)
{
v___x_1516_ = v_x_1512_;
v_isShared_1517_ = v_isSharedCheck_1523_;
goto v_resetjp_1515_;
}
else
{
lean_inc(v_a_1514_);
lean_inc(v_a_1513_);
lean_dec(v_x_1512_);
v___x_1516_ = lean_box(0);
v_isShared_1517_ = v_isSharedCheck_1523_;
goto v_resetjp_1515_;
}
v_resetjp_1515_:
{
lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1521_; 
v___x_1518_ = lean_unsigned_to_nat(1u);
v___x_1519_ = lean_nat_add(v_a_1514_, v___x_1518_);
lean_dec(v_a_1514_);
if (v_isShared_1517_ == 0)
{
lean_ctor_set(v___x_1516_, 1, v___x_1519_);
v___x_1521_ = v___x_1516_;
goto v_reusejp_1520_;
}
else
{
lean_object* v_reuseFailAlloc_1522_; 
v_reuseFailAlloc_1522_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1522_, 0, v_a_1513_);
lean_ctor_set(v_reuseFailAlloc_1522_, 1, v___x_1519_);
v___x_1521_ = v_reuseFailAlloc_1522_;
goto v_reusejp_1520_;
}
v_reusejp_1520_:
{
return v___x_1521_;
}
}
}
case 1:
{
lean_object* v_a_1524_; lean_object* v___x_1526_; uint8_t v_isShared_1527_; uint8_t v_isSharedCheck_1533_; 
v_a_1524_ = lean_ctor_get(v_x_1512_, 0);
v_isSharedCheck_1533_ = !lean_is_exclusive(v_x_1512_);
if (v_isSharedCheck_1533_ == 0)
{
v___x_1526_ = v_x_1512_;
v_isShared_1527_ = v_isSharedCheck_1533_;
goto v_resetjp_1525_;
}
else
{
lean_inc(v_a_1524_);
lean_dec(v_x_1512_);
v___x_1526_ = lean_box(0);
v_isShared_1527_ = v_isSharedCheck_1533_;
goto v_resetjp_1525_;
}
v_resetjp_1525_:
{
lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1531_; 
v___x_1528_ = lean_unsigned_to_nat(1u);
v___x_1529_ = lean_nat_add(v_a_1524_, v___x_1528_);
lean_dec(v_a_1524_);
if (v_isShared_1527_ == 0)
{
lean_ctor_set(v___x_1526_, 0, v___x_1529_);
v___x_1531_ = v___x_1526_;
goto v_reusejp_1530_;
}
else
{
lean_object* v_reuseFailAlloc_1532_; 
v_reuseFailAlloc_1532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1532_, 0, v___x_1529_);
v___x_1531_ = v_reuseFailAlloc_1532_;
goto v_reusejp_1530_;
}
v_reusejp_1530_:
{
return v___x_1531_;
}
}
}
default: 
{
lean_object* v___x_1534_; lean_object* v___x_1535_; 
v___x_1534_ = lean_unsigned_to_nat(1u);
v___x_1535_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1535_, 0, v_x_1512_);
lean_ctor_set(v___x_1535_, 1, v___x_1534_);
return v___x_1535_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_max(lean_object* v_x_1536_, lean_object* v_x_1537_){
_start:
{
if (lean_obj_tag(v_x_1537_) == 3)
{
lean_object* v_a_1538_; lean_object* v___x_1540_; uint8_t v_isShared_1541_; uint8_t v_isSharedCheck_1546_; 
v_a_1538_ = lean_ctor_get(v_x_1537_, 0);
v_isSharedCheck_1546_ = !lean_is_exclusive(v_x_1537_);
if (v_isSharedCheck_1546_ == 0)
{
v___x_1540_ = v_x_1537_;
v_isShared_1541_ = v_isSharedCheck_1546_;
goto v_resetjp_1539_;
}
else
{
lean_inc(v_a_1538_);
lean_dec(v_x_1537_);
v___x_1540_ = lean_box(0);
v_isShared_1541_ = v_isSharedCheck_1546_;
goto v_resetjp_1539_;
}
v_resetjp_1539_:
{
lean_object* v___x_1542_; lean_object* v___x_1544_; 
v___x_1542_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1542_, 0, v_x_1536_);
lean_ctor_set(v___x_1542_, 1, v_a_1538_);
if (v_isShared_1541_ == 0)
{
lean_ctor_set(v___x_1540_, 0, v___x_1542_);
v___x_1544_ = v___x_1540_;
goto v_reusejp_1543_;
}
else
{
lean_object* v_reuseFailAlloc_1545_; 
v_reuseFailAlloc_1545_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1545_, 0, v___x_1542_);
v___x_1544_ = v_reuseFailAlloc_1545_;
goto v_reusejp_1543_;
}
v_reusejp_1543_:
{
return v___x_1544_;
}
}
}
else
{
lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; 
v___x_1547_ = lean_box(0);
v___x_1548_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1548_, 0, v_x_1537_);
lean_ctor_set(v___x_1548_, 1, v___x_1547_);
v___x_1549_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1549_, 0, v_x_1536_);
lean_ctor_set(v___x_1549_, 1, v___x_1548_);
v___x_1550_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1550_, 0, v___x_1549_);
return v___x_1550_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_imax(lean_object* v_x_1551_, lean_object* v_x_1552_){
_start:
{
if (lean_obj_tag(v_x_1552_) == 4)
{
lean_object* v_a_1553_; lean_object* v___x_1555_; uint8_t v_isShared_1556_; uint8_t v_isSharedCheck_1561_; 
v_a_1553_ = lean_ctor_get(v_x_1552_, 0);
v_isSharedCheck_1561_ = !lean_is_exclusive(v_x_1552_);
if (v_isSharedCheck_1561_ == 0)
{
v___x_1555_ = v_x_1552_;
v_isShared_1556_ = v_isSharedCheck_1561_;
goto v_resetjp_1554_;
}
else
{
lean_inc(v_a_1553_);
lean_dec(v_x_1552_);
v___x_1555_ = lean_box(0);
v_isShared_1556_ = v_isSharedCheck_1561_;
goto v_resetjp_1554_;
}
v_resetjp_1554_:
{
lean_object* v___x_1557_; lean_object* v___x_1559_; 
v___x_1557_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1557_, 0, v_x_1551_);
lean_ctor_set(v___x_1557_, 1, v_a_1553_);
if (v_isShared_1556_ == 0)
{
lean_ctor_set(v___x_1555_, 0, v___x_1557_);
v___x_1559_ = v___x_1555_;
goto v_reusejp_1558_;
}
else
{
lean_object* v_reuseFailAlloc_1560_; 
v_reuseFailAlloc_1560_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1560_, 0, v___x_1557_);
v___x_1559_ = v_reuseFailAlloc_1560_;
goto v_reusejp_1558_;
}
v_reusejp_1558_:
{
return v___x_1559_;
}
}
}
else
{
lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; 
v___x_1562_ = lean_box(0);
v___x_1563_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1563_, 0, v_x_1552_);
lean_ctor_set(v___x_1563_, 1, v___x_1562_);
v___x_1564_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1564_, 0, v_x_1551_);
lean_ctor_set(v___x_1564_, 1, v___x_1563_);
v___x_1565_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1565_, 0, v___x_1564_);
return v___x_1565_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_toResult(lean_object* v_l_1584_, lean_object* v_a_1585_){
_start:
{
switch(lean_obj_tag(v_l_1584_))
{
case 0:
{
lean_object* v___x_1586_; 
v___x_1586_ = ((lean_object*)(l_Lean_Level_PP_toResult___closed__0));
return v___x_1586_;
}
case 1:
{
lean_object* v_a_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; 
v_a_1587_ = lean_ctor_get(v_l_1584_, 0);
lean_inc(v_a_1587_);
lean_dec_ref_known(v_l_1584_, 1);
v___x_1588_ = l_Lean_Level_PP_toResult(v_a_1587_, v_a_1585_);
v___x_1589_ = l_Lean_Level_PP_Result_succ(v___x_1588_);
return v___x_1589_;
}
case 2:
{
lean_object* v_a_1590_; lean_object* v_a_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; 
v_a_1590_ = lean_ctor_get(v_l_1584_, 0);
lean_inc(v_a_1590_);
v_a_1591_ = lean_ctor_get(v_l_1584_, 1);
lean_inc(v_a_1591_);
lean_dec_ref_known(v_l_1584_, 2);
v___x_1592_ = l_Lean_Level_PP_toResult(v_a_1590_, v_a_1585_);
v___x_1593_ = l_Lean_Level_PP_toResult(v_a_1591_, v_a_1585_);
v___x_1594_ = l_Lean_Level_PP_Result_max(v___x_1592_, v___x_1593_);
return v___x_1594_;
}
case 3:
{
lean_object* v_a_1595_; lean_object* v_a_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; 
v_a_1595_ = lean_ctor_get(v_l_1584_, 0);
lean_inc(v_a_1595_);
v_a_1596_ = lean_ctor_get(v_l_1584_, 1);
lean_inc(v_a_1596_);
lean_dec_ref_known(v_l_1584_, 2);
v___x_1597_ = l_Lean_Level_PP_toResult(v_a_1595_, v_a_1585_);
v___x_1598_ = l_Lean_Level_PP_toResult(v_a_1596_, v_a_1585_);
v___x_1599_ = l_Lean_Level_PP_Result_imax(v___x_1597_, v___x_1598_);
return v___x_1599_;
}
case 4:
{
lean_object* v_a_1600_; lean_object* v___x_1601_; 
v_a_1600_ = lean_ctor_get(v_l_1584_, 0);
lean_inc(v_a_1600_);
lean_dec_ref_known(v_l_1584_, 1);
v___x_1601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1601_, 0, v_a_1600_);
return v___x_1601_;
}
default: 
{
uint8_t v_mvars_1602_; 
v_mvars_1602_ = lean_ctor_get_uint8(v_a_1585_, sizeof(void*)*1);
if (v_mvars_1602_ == 0)
{
lean_object* v___x_1603_; 
lean_dec_ref_known(v_l_1584_, 1);
v___x_1603_ = ((lean_object*)(l_Lean_Level_PP_toResult___closed__3));
return v___x_1603_;
}
else
{
lean_object* v_a_1604_; lean_object* v_lIndex_x3f_1605_; lean_object* v___x_1606_; 
v_a_1604_ = lean_ctor_get(v_l_1584_, 0);
lean_inc_n(v_a_1604_, 2);
lean_dec_ref_known(v_l_1584_, 1);
v_lIndex_x3f_1605_ = lean_ctor_get(v_a_1585_, 0);
lean_inc_ref(v_lIndex_x3f_1605_);
v___x_1606_ = lean_apply_1(v_lIndex_x3f_1605_, v_a_1604_);
if (lean_obj_tag(v___x_1606_) == 1)
{
lean_object* v_val_1607_; lean_object* v___x_1609_; uint8_t v_isShared_1610_; uint8_t v_isSharedCheck_1618_; 
lean_dec(v_a_1604_);
v_val_1607_ = lean_ctor_get(v___x_1606_, 0);
v_isSharedCheck_1618_ = !lean_is_exclusive(v___x_1606_);
if (v_isSharedCheck_1618_ == 0)
{
v___x_1609_ = v___x_1606_;
v_isShared_1610_ = v_isSharedCheck_1618_;
goto v_resetjp_1608_;
}
else
{
lean_inc(v_val_1607_);
lean_dec(v___x_1606_);
v___x_1609_ = lean_box(0);
v_isShared_1610_ = v_isSharedCheck_1618_;
goto v_resetjp_1608_;
}
v_resetjp_1608_:
{
lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1616_; 
v___x_1611_ = ((lean_object*)(l_Lean_Level_PP_toResult___closed__5));
v___x_1612_ = lean_unsigned_to_nat(1u);
v___x_1613_ = lean_nat_add(v_val_1607_, v___x_1612_);
lean_dec(v_val_1607_);
v___x_1614_ = l_Lean_Name_num___override(v___x_1611_, v___x_1613_);
if (v_isShared_1610_ == 0)
{
lean_ctor_set_tag(v___x_1609_, 0);
lean_ctor_set(v___x_1609_, 0, v___x_1614_);
v___x_1616_ = v___x_1609_;
goto v_reusejp_1615_;
}
else
{
lean_object* v_reuseFailAlloc_1617_; 
v_reuseFailAlloc_1617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1617_, 0, v___x_1614_);
v___x_1616_ = v_reuseFailAlloc_1617_;
goto v_reusejp_1615_;
}
v_reusejp_1615_:
{
return v___x_1616_;
}
}
}
else
{
lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; 
lean_dec(v___x_1606_);
v___x_1619_ = ((lean_object*)(l_Lean_Level_PP_toResult___closed__7));
v___x_1620_ = ((lean_object*)(l_Lean_Level_PP_toResult___closed__9));
v___x_1621_ = l_Lean_Name_replacePrefix(v_a_1604_, v___x_1619_, v___x_1620_);
v___x_1622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1622_, 0, v___x_1621_);
return v___x_1622_;
}
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
v___x_1770_ = l_Array_mkArray0___redArg();
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
v___x_2027_ = lean_unsigned_to_nat(566u);
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
v___x_2048_ = lean_unsigned_to_nat(577u);
v___x_2049_ = ((lean_object*)(l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl___closed__0));
v___x_2050_ = ((lean_object*)(l_Lean_Level_mvarId_x21___closed__0));
v___x_2051_ = l_mkPanicMessageWithDecl(v___x_2050_, v___x_2049_, v___x_2048_, v___x_2047_, v___x_2046_);
return v___x_2051_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl(lean_object* v_lvl_2052_, lean_object* v_newLhs_2053_, lean_object* v_newRhs_2054_){
_start:
{
if (lean_obj_tag(v_lvl_2052_) == 2)
{
lean_object* v_a_2055_; lean_object* v_a_2056_; size_t v___x_2057_; size_t v___x_2058_; uint8_t v___x_2059_; 
v_a_2055_ = lean_ctor_get(v_lvl_2052_, 0);
v_a_2056_ = lean_ctor_get(v_lvl_2052_, 1);
v___x_2057_ = lean_ptr_addr(v_a_2055_);
v___x_2058_ = lean_ptr_addr(v_newLhs_2053_);
v___x_2059_ = lean_usize_dec_eq(v___x_2057_, v___x_2058_);
if (v___x_2059_ == 0)
{
lean_object* v___x_2060_; 
v___x_2060_ = l_Lean_mkLevelMax_x27(v_newLhs_2053_, v_newRhs_2054_);
return v___x_2060_;
}
else
{
size_t v___x_2061_; size_t v___x_2062_; uint8_t v___x_2063_; 
v___x_2061_ = lean_ptr_addr(v_a_2056_);
v___x_2062_ = lean_ptr_addr(v_newRhs_2054_);
v___x_2063_ = lean_usize_dec_eq(v___x_2061_, v___x_2062_);
if (v___x_2063_ == 0)
{
lean_object* v___x_2064_; 
v___x_2064_ = l_Lean_mkLevelMax_x27(v_newLhs_2053_, v_newRhs_2054_);
return v___x_2064_;
}
else
{
lean_object* v___x_2065_; 
v___x_2065_ = l_Lean_simpLevelMax_x27(v_newLhs_2053_, v_newRhs_2054_, v_lvl_2052_);
lean_dec(v_newRhs_2054_);
lean_dec(v_newLhs_2053_);
return v___x_2065_;
}
}
}
else
{
lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; 
lean_dec(v_newRhs_2054_);
lean_dec(v_newLhs_2053_);
v___x_2066_ = lean_box(0);
v___x_2067_ = lean_obj_once(&l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl___closed__2, &l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl___closed__2_once, _init_l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl___closed__2);
v___x_2068_ = l_panic___redArg(v___x_2066_, v___x_2067_);
return v___x_2068_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl___boxed(lean_object* v_lvl_2069_, lean_object* v_newLhs_2070_, lean_object* v_newRhs_2071_){
_start:
{
lean_object* v_res_2072_; 
v_res_2072_ = l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl(v_lvl_2069_, v_newLhs_2070_, v_newRhs_2071_);
lean_dec(v_lvl_2069_);
return v_res_2072_;
}
}
static lean_object* _init_l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl___closed__2(void){
_start:
{
lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; 
v___x_2075_ = ((lean_object*)(l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl___closed__1));
v___x_2076_ = lean_unsigned_to_nat(20u);
v___x_2077_ = lean_unsigned_to_nat(588u);
v___x_2078_ = ((lean_object*)(l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl___closed__0));
v___x_2079_ = ((lean_object*)(l_Lean_Level_mvarId_x21___closed__0));
v___x_2080_ = l_mkPanicMessageWithDecl(v___x_2079_, v___x_2078_, v___x_2077_, v___x_2076_, v___x_2075_);
return v___x_2080_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl(lean_object* v_lvl_2081_, lean_object* v_newLhs_2082_, lean_object* v_newRhs_2083_){
_start:
{
if (lean_obj_tag(v_lvl_2081_) == 3)
{
lean_object* v_a_2084_; lean_object* v_a_2085_; size_t v___x_2086_; size_t v___x_2087_; uint8_t v___x_2088_; 
v_a_2084_ = lean_ctor_get(v_lvl_2081_, 0);
v_a_2085_ = lean_ctor_get(v_lvl_2081_, 1);
v___x_2086_ = lean_ptr_addr(v_a_2084_);
v___x_2087_ = lean_ptr_addr(v_newLhs_2082_);
v___x_2088_ = lean_usize_dec_eq(v___x_2086_, v___x_2087_);
if (v___x_2088_ == 0)
{
lean_object* v___x_2089_; 
v___x_2089_ = l_Lean_mkLevelIMax_x27(v_newLhs_2082_, v_newRhs_2083_);
return v___x_2089_;
}
else
{
size_t v___x_2090_; size_t v___x_2091_; uint8_t v___x_2092_; 
v___x_2090_ = lean_ptr_addr(v_a_2085_);
v___x_2091_ = lean_ptr_addr(v_newRhs_2083_);
v___x_2092_ = lean_usize_dec_eq(v___x_2090_, v___x_2091_);
if (v___x_2092_ == 0)
{
lean_object* v___x_2093_; 
v___x_2093_ = l_Lean_mkLevelIMax_x27(v_newLhs_2082_, v_newRhs_2083_);
return v___x_2093_;
}
else
{
lean_object* v___x_2094_; 
v___x_2094_ = l_Lean_simpLevelIMax_x27(v_newLhs_2082_, v_newRhs_2083_, v_lvl_2081_);
return v___x_2094_;
}
}
}
else
{
lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; 
lean_dec(v_newRhs_2083_);
lean_dec(v_newLhs_2082_);
v___x_2095_ = lean_box(0);
v___x_2096_ = lean_obj_once(&l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl___closed__2, &l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl___closed__2_once, _init_l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl___closed__2);
v___x_2097_ = l_panic___redArg(v___x_2095_, v___x_2096_);
return v___x_2097_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl___boxed(lean_object* v_lvl_2098_, lean_object* v_newLhs_2099_, lean_object* v_newRhs_2100_){
_start:
{
lean_object* v_res_2101_; 
v_res_2101_ = l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl(v_lvl_2098_, v_newLhs_2099_, v_newRhs_2100_);
lean_dec(v_lvl_2098_);
return v_res_2101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_mkNaryMax(lean_object* v_x_2102_){
_start:
{
if (lean_obj_tag(v_x_2102_) == 0)
{
lean_object* v___x_2103_; 
v___x_2103_ = lean_box(0);
return v___x_2103_;
}
else
{
lean_object* v_tail_2104_; 
v_tail_2104_ = lean_ctor_get(v_x_2102_, 1);
if (lean_obj_tag(v_tail_2104_) == 0)
{
lean_object* v_head_2105_; 
v_head_2105_ = lean_ctor_get(v_x_2102_, 0);
lean_inc(v_head_2105_);
lean_dec_ref_known(v_x_2102_, 2);
return v_head_2105_;
}
else
{
lean_object* v_head_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; 
lean_inc(v_tail_2104_);
v_head_2106_ = lean_ctor_get(v_x_2102_, 0);
lean_inc(v_head_2106_);
lean_dec_ref_known(v_x_2102_, 2);
v___x_2107_ = l_Lean_Level_mkNaryMax(v_tail_2104_);
v___x_2108_ = l_Lean_mkLevelMax_x27(v_head_2106_, v___x_2107_);
return v___x_2108_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_substParams_go(lean_object* v_s_2109_, lean_object* v_u_2110_){
_start:
{
switch(lean_obj_tag(v_u_2110_))
{
case 1:
{
lean_object* v_a_2111_; uint8_t v___x_2112_; 
v_a_2111_ = lean_ctor_get(v_u_2110_, 0);
v___x_2112_ = l_Lean_Level_hasParam(v_u_2110_);
if (v___x_2112_ == 0)
{
lean_dec_ref(v_s_2109_);
return v_u_2110_;
}
else
{
lean_object* v___x_2113_; size_t v___x_2114_; size_t v___x_2115_; uint8_t v___x_2116_; 
lean_inc(v_a_2111_);
v___x_2113_ = l___private_Lean_Level_0__Lean_Level_substParams_go(v_s_2109_, v_a_2111_);
v___x_2114_ = lean_ptr_addr(v_a_2111_);
v___x_2115_ = lean_ptr_addr(v___x_2113_);
v___x_2116_ = lean_usize_dec_eq(v___x_2114_, v___x_2115_);
if (v___x_2116_ == 0)
{
lean_object* v___x_2117_; 
lean_dec_ref_known(v_u_2110_, 1);
v___x_2117_ = l_Lean_Level_succ___override(v___x_2113_);
return v___x_2117_;
}
else
{
lean_dec(v___x_2113_);
return v_u_2110_;
}
}
}
case 2:
{
lean_object* v_a_2118_; lean_object* v_a_2119_; uint8_t v___x_2120_; 
v_a_2118_ = lean_ctor_get(v_u_2110_, 0);
v_a_2119_ = lean_ctor_get(v_u_2110_, 1);
v___x_2120_ = l_Lean_Level_hasParam(v_u_2110_);
if (v___x_2120_ == 0)
{
lean_dec_ref(v_s_2109_);
return v_u_2110_;
}
else
{
lean_object* v___x_2121_; lean_object* v___x_2122_; size_t v___x_2123_; size_t v___x_2124_; uint8_t v___x_2125_; 
lean_inc(v_a_2118_);
lean_inc_ref(v_s_2109_);
v___x_2121_ = l___private_Lean_Level_0__Lean_Level_substParams_go(v_s_2109_, v_a_2118_);
lean_inc(v_a_2119_);
v___x_2122_ = l___private_Lean_Level_0__Lean_Level_substParams_go(v_s_2109_, v_a_2119_);
v___x_2123_ = lean_ptr_addr(v_a_2118_);
v___x_2124_ = lean_ptr_addr(v___x_2121_);
v___x_2125_ = lean_usize_dec_eq(v___x_2123_, v___x_2124_);
if (v___x_2125_ == 0)
{
lean_object* v___x_2126_; 
lean_dec_ref_known(v_u_2110_, 2);
v___x_2126_ = l_Lean_mkLevelMax_x27(v___x_2121_, v___x_2122_);
return v___x_2126_;
}
else
{
size_t v___x_2127_; size_t v___x_2128_; uint8_t v___x_2129_; 
v___x_2127_ = lean_ptr_addr(v_a_2119_);
v___x_2128_ = lean_ptr_addr(v___x_2122_);
v___x_2129_ = lean_usize_dec_eq(v___x_2127_, v___x_2128_);
if (v___x_2129_ == 0)
{
lean_object* v___x_2130_; 
lean_dec_ref_known(v_u_2110_, 2);
v___x_2130_ = l_Lean_mkLevelMax_x27(v___x_2121_, v___x_2122_);
return v___x_2130_;
}
else
{
lean_object* v___x_2131_; 
v___x_2131_ = l_Lean_simpLevelMax_x27(v___x_2121_, v___x_2122_, v_u_2110_);
lean_dec_ref_known(v_u_2110_, 2);
lean_dec(v___x_2122_);
lean_dec(v___x_2121_);
return v___x_2131_;
}
}
}
}
case 3:
{
lean_object* v_a_2132_; lean_object* v_a_2133_; uint8_t v___x_2134_; 
v_a_2132_ = lean_ctor_get(v_u_2110_, 0);
v_a_2133_ = lean_ctor_get(v_u_2110_, 1);
v___x_2134_ = l_Lean_Level_hasParam(v_u_2110_);
if (v___x_2134_ == 0)
{
lean_dec_ref(v_s_2109_);
return v_u_2110_;
}
else
{
lean_object* v___x_2135_; lean_object* v___x_2136_; size_t v___x_2137_; size_t v___x_2138_; uint8_t v___x_2139_; 
lean_inc(v_a_2132_);
lean_inc_ref(v_s_2109_);
v___x_2135_ = l___private_Lean_Level_0__Lean_Level_substParams_go(v_s_2109_, v_a_2132_);
lean_inc(v_a_2133_);
v___x_2136_ = l___private_Lean_Level_0__Lean_Level_substParams_go(v_s_2109_, v_a_2133_);
v___x_2137_ = lean_ptr_addr(v_a_2132_);
v___x_2138_ = lean_ptr_addr(v___x_2135_);
v___x_2139_ = lean_usize_dec_eq(v___x_2137_, v___x_2138_);
if (v___x_2139_ == 0)
{
lean_object* v___x_2140_; 
lean_dec_ref_known(v_u_2110_, 2);
v___x_2140_ = l_Lean_mkLevelIMax_x27(v___x_2135_, v___x_2136_);
return v___x_2140_;
}
else
{
size_t v___x_2141_; size_t v___x_2142_; uint8_t v___x_2143_; 
v___x_2141_ = lean_ptr_addr(v_a_2133_);
v___x_2142_ = lean_ptr_addr(v___x_2136_);
v___x_2143_ = lean_usize_dec_eq(v___x_2141_, v___x_2142_);
if (v___x_2143_ == 0)
{
lean_object* v___x_2144_; 
lean_dec_ref_known(v_u_2110_, 2);
v___x_2144_ = l_Lean_mkLevelIMax_x27(v___x_2135_, v___x_2136_);
return v___x_2144_;
}
else
{
lean_object* v___x_2145_; 
v___x_2145_ = l_Lean_simpLevelIMax_x27(v___x_2135_, v___x_2136_, v_u_2110_);
lean_dec_ref_known(v_u_2110_, 2);
return v___x_2145_;
}
}
}
}
case 4:
{
lean_object* v_a_2146_; lean_object* v___x_2147_; 
v_a_2146_ = lean_ctor_get(v_u_2110_, 0);
lean_inc(v_a_2146_);
v___x_2147_ = lean_apply_1(v_s_2109_, v_a_2146_);
if (lean_obj_tag(v___x_2147_) == 0)
{
return v_u_2110_;
}
else
{
lean_object* v_val_2148_; 
lean_dec_ref_known(v_u_2110_, 1);
v_val_2148_ = lean_ctor_get(v___x_2147_, 0);
lean_inc(v_val_2148_);
lean_dec_ref_known(v___x_2147_, 1);
return v_val_2148_;
}
}
default: 
{
lean_dec_ref(v_s_2109_);
return v_u_2110_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_substParams(lean_object* v_u_2149_, lean_object* v_s_2150_){
_start:
{
lean_object* v___x_2151_; 
v___x_2151_ = l___private_Lean_Level_0__Lean_Level_substParams_go(v_s_2150_, v_u_2149_);
return v___x_2151_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_getParamSubst(lean_object* v_x_2152_, lean_object* v_x_2153_, lean_object* v_x_2154_){
_start:
{
if (lean_obj_tag(v_x_2152_) == 1)
{
if (lean_obj_tag(v_x_2153_) == 1)
{
lean_object* v_head_2155_; lean_object* v_tail_2156_; lean_object* v_head_2157_; lean_object* v_tail_2158_; uint8_t v___x_2159_; 
v_head_2155_ = lean_ctor_get(v_x_2152_, 0);
v_tail_2156_ = lean_ctor_get(v_x_2152_, 1);
v_head_2157_ = lean_ctor_get(v_x_2153_, 0);
v_tail_2158_ = lean_ctor_get(v_x_2153_, 1);
v___x_2159_ = lean_name_eq(v_head_2155_, v_x_2154_);
if (v___x_2159_ == 0)
{
v_x_2152_ = v_tail_2156_;
v_x_2153_ = v_tail_2158_;
goto _start;
}
else
{
lean_object* v___x_2161_; 
lean_inc(v_head_2157_);
v___x_2161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2161_, 0, v_head_2157_);
return v___x_2161_;
}
}
else
{
lean_object* v___x_2162_; 
v___x_2162_ = lean_box(0);
return v___x_2162_;
}
}
else
{
lean_object* v___x_2163_; 
v___x_2163_ = lean_box(0);
return v___x_2163_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_getParamSubst___boxed(lean_object* v_x_2164_, lean_object* v_x_2165_, lean_object* v_x_2166_){
_start:
{
lean_object* v_res_2167_; 
v_res_2167_ = l_Lean_Level_getParamSubst(v_x_2164_, v_x_2165_, v_x_2166_);
lean_dec(v_x_2166_);
lean_dec(v_x_2165_);
lean_dec(v_x_2164_);
return v_res_2167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_instantiateParams(lean_object* v_u_2168_, lean_object* v_paramNames_2169_, lean_object* v_vs_2170_){
_start:
{
lean_object* v___x_2171_; lean_object* v___x_2172_; 
v___x_2171_ = lean_alloc_closure((void*)(l_Lean_Level_getParamSubst___boxed), 3, 2);
lean_closure_set(v___x_2171_, 0, v_paramNames_2169_);
lean_closure_set(v___x_2171_, 1, v_vs_2170_);
v___x_2172_ = l___private_Lean_Level_0__Lean_Level_substParams_go(v___x_2171_, v_u_2168_);
return v___x_2172_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Level_0__Lean_Level_geq_go(lean_object* v_u_2173_, lean_object* v_v_2174_){
_start:
{
uint8_t v___y_2176_; uint8_t v___y_2190_; lean_object* v_u_u2081_2192_; lean_object* v_u_u2082_2193_; lean_object* v_v_2194_; uint8_t v___x_2197_; 
v___x_2197_ = lean_level_eq(v_u_2173_, v_v_2174_);
if (v___x_2197_ == 0)
{
switch(lean_obj_tag(v_v_2174_))
{
case 0:
{
uint8_t v___x_2198_; 
v___x_2198_ = 1;
return v___x_2198_;
}
case 2:
{
lean_object* v_a_2199_; lean_object* v_a_2200_; uint8_t v___x_2201_; 
v_a_2199_ = lean_ctor_get(v_v_2174_, 0);
v_a_2200_ = lean_ctor_get(v_v_2174_, 1);
v___x_2201_ = l___private_Lean_Level_0__Lean_Level_geq_go(v_u_2173_, v_a_2199_);
if (v___x_2201_ == 0)
{
return v___x_2201_;
}
else
{
v_v_2174_ = v_a_2200_;
goto _start;
}
}
case 1:
{
switch(lean_obj_tag(v_u_2173_))
{
case 2:
{
lean_object* v_a_2203_; lean_object* v_a_2204_; 
v_a_2203_ = lean_ctor_get(v_u_2173_, 0);
v_a_2204_ = lean_ctor_get(v_u_2173_, 1);
v_u_u2081_2192_ = v_a_2203_;
v_u_u2082_2193_ = v_a_2204_;
v_v_2194_ = v_v_2174_;
goto v___jp_2191_;
}
case 3:
{
lean_object* v_a_2205_; 
v_a_2205_ = lean_ctor_get(v_u_2173_, 1);
v_u_2173_ = v_a_2205_;
goto _start;
}
case 1:
{
lean_object* v_a_2207_; lean_object* v_a_2208_; 
v_a_2207_ = lean_ctor_get(v_v_2174_, 0);
v_a_2208_ = lean_ctor_get(v_u_2173_, 0);
v_u_2173_ = v_a_2208_;
v_v_2174_ = v_a_2207_;
goto _start;
}
default: 
{
goto v___jp_2180_;
}
}
}
default: 
{
switch(lean_obj_tag(v_u_2173_))
{
case 2:
{
lean_object* v_a_2210_; lean_object* v_a_2211_; 
v_a_2210_ = lean_ctor_get(v_u_2173_, 0);
v_a_2211_ = lean_ctor_get(v_u_2173_, 1);
v_u_u2081_2192_ = v_a_2210_;
v_u_u2082_2193_ = v_a_2211_;
v_v_2194_ = v_v_2174_;
goto v___jp_2191_;
}
case 3:
{
lean_object* v_a_2212_; 
v_a_2212_ = lean_ctor_get(v_u_2173_, 1);
v_u_2173_ = v_a_2212_;
goto _start;
}
default: 
{
goto v___jp_2180_;
}
}
}
}
}
else
{
return v___x_2197_;
}
v___jp_2175_:
{
if (v___y_2176_ == 0)
{
return v___y_2176_;
}
else
{
lean_object* v___x_2177_; lean_object* v___x_2178_; uint8_t v___x_2179_; 
v___x_2177_ = l_Lean_Level_getOffset(v_v_2174_);
v___x_2178_ = l_Lean_Level_getOffset(v_u_2173_);
v___x_2179_ = lean_nat_dec_le(v___x_2177_, v___x_2178_);
lean_dec(v___x_2178_);
lean_dec(v___x_2177_);
return v___x_2179_;
}
}
v___jp_2180_:
{
if (lean_obj_tag(v_v_2174_) == 3)
{
lean_object* v_a_2181_; lean_object* v_a_2182_; uint8_t v___x_2183_; 
v_a_2181_ = lean_ctor_get(v_v_2174_, 0);
v_a_2182_ = lean_ctor_get(v_v_2174_, 1);
v___x_2183_ = l___private_Lean_Level_0__Lean_Level_geq_go(v_u_2173_, v_a_2181_);
if (v___x_2183_ == 0)
{
return v___x_2183_;
}
else
{
v_v_2174_ = v_a_2182_;
goto _start;
}
}
else
{
lean_object* v_v_x27_2185_; lean_object* v___x_2186_; uint8_t v___x_2187_; 
v_v_x27_2185_ = l_Lean_Level_getLevelOffset(v_v_2174_);
v___x_2186_ = l_Lean_Level_getLevelOffset(v_u_2173_);
v___x_2187_ = lean_level_eq(v___x_2186_, v_v_x27_2185_);
lean_dec(v___x_2186_);
if (v___x_2187_ == 0)
{
uint8_t v___x_2188_; 
v___x_2188_ = l_Lean_Level_isZero(v_v_x27_2185_);
lean_dec(v_v_x27_2185_);
v___y_2176_ = v___x_2188_;
goto v___jp_2175_;
}
else
{
lean_dec(v_v_x27_2185_);
v___y_2176_ = v___x_2187_;
goto v___jp_2175_;
}
}
}
v___jp_2189_:
{
if (v___y_2190_ == 0)
{
goto v___jp_2180_;
}
else
{
return v___y_2190_;
}
}
v___jp_2191_:
{
uint8_t v___x_2195_; 
v___x_2195_ = l___private_Lean_Level_0__Lean_Level_geq_go(v_u_u2081_2192_, v_v_2194_);
if (v___x_2195_ == 0)
{
uint8_t v___x_2196_; 
v___x_2196_ = l___private_Lean_Level_0__Lean_Level_geq_go(v_u_u2082_2193_, v_v_2194_);
v___y_2190_ = v___x_2196_;
goto v___jp_2189_;
}
else
{
v___y_2190_ = v___x_2195_;
goto v___jp_2189_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_geq_go___boxed(lean_object* v_u_2214_, lean_object* v_v_2215_){
_start:
{
uint8_t v_res_2216_; lean_object* v_r_2217_; 
v_res_2216_ = l___private_Lean_Level_0__Lean_Level_geq_go(v_u_2214_, v_v_2215_);
lean_dec(v_v_2215_);
lean_dec(v_u_2214_);
v_r_2217_ = lean_box(v_res_2216_);
return v_r_2217_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_geq_go_match__1_splitter___redArg(lean_object* v_u_2218_, lean_object* v_v_2219_, lean_object* v_h__1_2220_, lean_object* v_h__2_2221_, lean_object* v_h__3_2222_, lean_object* v_h__4_2223_, lean_object* v_h__5_2224_, lean_object* v_h__6_2225_){
_start:
{
switch(lean_obj_tag(v_v_2219_))
{
case 0:
{
lean_object* v___x_2226_; 
lean_dec(v_h__6_2225_);
lean_dec(v_h__5_2224_);
lean_dec(v_h__4_2223_);
lean_dec(v_h__3_2222_);
lean_dec(v_h__2_2221_);
v___x_2226_ = lean_apply_1(v_h__1_2220_, v_u_2218_);
return v___x_2226_;
}
case 2:
{
lean_object* v_a_2227_; lean_object* v_a_2228_; lean_object* v___x_2229_; 
lean_dec(v_h__6_2225_);
lean_dec(v_h__5_2224_);
lean_dec(v_h__4_2223_);
lean_dec(v_h__3_2222_);
lean_dec(v_h__1_2220_);
v_a_2227_ = lean_ctor_get(v_v_2219_, 0);
lean_inc(v_a_2227_);
v_a_2228_ = lean_ctor_get(v_v_2219_, 1);
lean_inc(v_a_2228_);
lean_dec_ref_known(v_v_2219_, 2);
v___x_2229_ = lean_apply_3(v_h__2_2221_, v_u_2218_, v_a_2227_, v_a_2228_);
return v___x_2229_;
}
case 1:
{
lean_dec(v_h__2_2221_);
lean_dec(v_h__1_2220_);
switch(lean_obj_tag(v_u_2218_))
{
case 2:
{
lean_object* v_a_2230_; lean_object* v_a_2231_; lean_object* v___x_2232_; 
lean_dec(v_h__6_2225_);
lean_dec(v_h__5_2224_);
lean_dec(v_h__4_2223_);
v_a_2230_ = lean_ctor_get(v_u_2218_, 0);
lean_inc(v_a_2230_);
v_a_2231_ = lean_ctor_get(v_u_2218_, 1);
lean_inc(v_a_2231_);
lean_dec_ref_known(v_u_2218_, 2);
v___x_2232_ = lean_apply_5(v_h__3_2222_, v_a_2230_, v_a_2231_, v_v_2219_, lean_box(0), lean_box(0));
return v___x_2232_;
}
case 3:
{
lean_object* v_a_2233_; lean_object* v_a_2234_; lean_object* v___x_2235_; 
lean_dec(v_h__6_2225_);
lean_dec(v_h__5_2224_);
lean_dec(v_h__3_2222_);
v_a_2233_ = lean_ctor_get(v_u_2218_, 0);
lean_inc(v_a_2233_);
v_a_2234_ = lean_ctor_get(v_u_2218_, 1);
lean_inc(v_a_2234_);
lean_dec_ref_known(v_u_2218_, 2);
v___x_2235_ = lean_apply_5(v_h__4_2223_, v_a_2233_, v_a_2234_, v_v_2219_, lean_box(0), lean_box(0));
return v___x_2235_;
}
case 1:
{
lean_object* v_a_2236_; lean_object* v_a_2237_; lean_object* v___x_2238_; 
lean_dec(v_h__6_2225_);
lean_dec(v_h__4_2223_);
lean_dec(v_h__3_2222_);
v_a_2236_ = lean_ctor_get(v_v_2219_, 0);
lean_inc(v_a_2236_);
lean_dec_ref_known(v_v_2219_, 1);
v_a_2237_ = lean_ctor_get(v_u_2218_, 0);
lean_inc(v_a_2237_);
lean_dec_ref_known(v_u_2218_, 1);
v___x_2238_ = lean_apply_2(v_h__5_2224_, v_a_2237_, v_a_2236_);
return v___x_2238_;
}
default: 
{
lean_object* v___x_2239_; 
lean_dec(v_h__5_2224_);
lean_dec(v_h__4_2223_);
lean_dec(v_h__3_2222_);
v___x_2239_ = lean_apply_7(v_h__6_2225_, v_u_2218_, v_v_2219_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_2239_;
}
}
}
default: 
{
lean_dec(v_h__5_2224_);
lean_dec(v_h__2_2221_);
lean_dec(v_h__1_2220_);
switch(lean_obj_tag(v_u_2218_))
{
case 2:
{
lean_object* v_a_2240_; lean_object* v_a_2241_; lean_object* v___x_2242_; 
lean_dec(v_h__6_2225_);
lean_dec(v_h__4_2223_);
v_a_2240_ = lean_ctor_get(v_u_2218_, 0);
lean_inc(v_a_2240_);
v_a_2241_ = lean_ctor_get(v_u_2218_, 1);
lean_inc(v_a_2241_);
lean_dec_ref_known(v_u_2218_, 2);
v___x_2242_ = lean_apply_5(v_h__3_2222_, v_a_2240_, v_a_2241_, v_v_2219_, lean_box(0), lean_box(0));
return v___x_2242_;
}
case 3:
{
lean_object* v_a_2243_; lean_object* v_a_2244_; lean_object* v___x_2245_; 
lean_dec(v_h__6_2225_);
lean_dec(v_h__3_2222_);
v_a_2243_ = lean_ctor_get(v_u_2218_, 0);
lean_inc(v_a_2243_);
v_a_2244_ = lean_ctor_get(v_u_2218_, 1);
lean_inc(v_a_2244_);
lean_dec_ref_known(v_u_2218_, 2);
v___x_2245_ = lean_apply_5(v_h__4_2223_, v_a_2243_, v_a_2244_, v_v_2219_, lean_box(0), lean_box(0));
return v___x_2245_;
}
default: 
{
lean_object* v___x_2246_; 
lean_dec(v_h__4_2223_);
lean_dec(v_h__3_2222_);
v___x_2246_ = lean_apply_7(v_h__6_2225_, v_u_2218_, v_v_2219_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_2246_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_geq_go_match__1_splitter(lean_object* v_motive_2247_, lean_object* v_u_2248_, lean_object* v_v_2249_, lean_object* v_h__1_2250_, lean_object* v_h__2_2251_, lean_object* v_h__3_2252_, lean_object* v_h__4_2253_, lean_object* v_h__5_2254_, lean_object* v_h__6_2255_){
_start:
{
switch(lean_obj_tag(v_v_2249_))
{
case 0:
{
lean_object* v___x_2256_; 
lean_dec(v_h__6_2255_);
lean_dec(v_h__5_2254_);
lean_dec(v_h__4_2253_);
lean_dec(v_h__3_2252_);
lean_dec(v_h__2_2251_);
v___x_2256_ = lean_apply_1(v_h__1_2250_, v_u_2248_);
return v___x_2256_;
}
case 2:
{
lean_object* v_a_2257_; lean_object* v_a_2258_; lean_object* v___x_2259_; 
lean_dec(v_h__6_2255_);
lean_dec(v_h__5_2254_);
lean_dec(v_h__4_2253_);
lean_dec(v_h__3_2252_);
lean_dec(v_h__1_2250_);
v_a_2257_ = lean_ctor_get(v_v_2249_, 0);
lean_inc(v_a_2257_);
v_a_2258_ = lean_ctor_get(v_v_2249_, 1);
lean_inc(v_a_2258_);
lean_dec_ref_known(v_v_2249_, 2);
v___x_2259_ = lean_apply_3(v_h__2_2251_, v_u_2248_, v_a_2257_, v_a_2258_);
return v___x_2259_;
}
case 1:
{
lean_dec(v_h__2_2251_);
lean_dec(v_h__1_2250_);
switch(lean_obj_tag(v_u_2248_))
{
case 2:
{
lean_object* v_a_2260_; lean_object* v_a_2261_; lean_object* v___x_2262_; 
lean_dec(v_h__6_2255_);
lean_dec(v_h__5_2254_);
lean_dec(v_h__4_2253_);
v_a_2260_ = lean_ctor_get(v_u_2248_, 0);
lean_inc(v_a_2260_);
v_a_2261_ = lean_ctor_get(v_u_2248_, 1);
lean_inc(v_a_2261_);
lean_dec_ref_known(v_u_2248_, 2);
v___x_2262_ = lean_apply_5(v_h__3_2252_, v_a_2260_, v_a_2261_, v_v_2249_, lean_box(0), lean_box(0));
return v___x_2262_;
}
case 3:
{
lean_object* v_a_2263_; lean_object* v_a_2264_; lean_object* v___x_2265_; 
lean_dec(v_h__6_2255_);
lean_dec(v_h__5_2254_);
lean_dec(v_h__3_2252_);
v_a_2263_ = lean_ctor_get(v_u_2248_, 0);
lean_inc(v_a_2263_);
v_a_2264_ = lean_ctor_get(v_u_2248_, 1);
lean_inc(v_a_2264_);
lean_dec_ref_known(v_u_2248_, 2);
v___x_2265_ = lean_apply_5(v_h__4_2253_, v_a_2263_, v_a_2264_, v_v_2249_, lean_box(0), lean_box(0));
return v___x_2265_;
}
case 1:
{
lean_object* v_a_2266_; lean_object* v_a_2267_; lean_object* v___x_2268_; 
lean_dec(v_h__6_2255_);
lean_dec(v_h__4_2253_);
lean_dec(v_h__3_2252_);
v_a_2266_ = lean_ctor_get(v_v_2249_, 0);
lean_inc(v_a_2266_);
lean_dec_ref_known(v_v_2249_, 1);
v_a_2267_ = lean_ctor_get(v_u_2248_, 0);
lean_inc(v_a_2267_);
lean_dec_ref_known(v_u_2248_, 1);
v___x_2268_ = lean_apply_2(v_h__5_2254_, v_a_2267_, v_a_2266_);
return v___x_2268_;
}
default: 
{
lean_object* v___x_2269_; 
lean_dec(v_h__5_2254_);
lean_dec(v_h__4_2253_);
lean_dec(v_h__3_2252_);
v___x_2269_ = lean_apply_7(v_h__6_2255_, v_u_2248_, v_v_2249_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_2269_;
}
}
}
default: 
{
lean_dec(v_h__5_2254_);
lean_dec(v_h__2_2251_);
lean_dec(v_h__1_2250_);
switch(lean_obj_tag(v_u_2248_))
{
case 2:
{
lean_object* v_a_2270_; lean_object* v_a_2271_; lean_object* v___x_2272_; 
lean_dec(v_h__6_2255_);
lean_dec(v_h__4_2253_);
v_a_2270_ = lean_ctor_get(v_u_2248_, 0);
lean_inc(v_a_2270_);
v_a_2271_ = lean_ctor_get(v_u_2248_, 1);
lean_inc(v_a_2271_);
lean_dec_ref_known(v_u_2248_, 2);
v___x_2272_ = lean_apply_5(v_h__3_2252_, v_a_2270_, v_a_2271_, v_v_2249_, lean_box(0), lean_box(0));
return v___x_2272_;
}
case 3:
{
lean_object* v_a_2273_; lean_object* v_a_2274_; lean_object* v___x_2275_; 
lean_dec(v_h__6_2255_);
lean_dec(v_h__3_2252_);
v_a_2273_ = lean_ctor_get(v_u_2248_, 0);
lean_inc(v_a_2273_);
v_a_2274_ = lean_ctor_get(v_u_2248_, 1);
lean_inc(v_a_2274_);
lean_dec_ref_known(v_u_2248_, 2);
v___x_2275_ = lean_apply_5(v_h__4_2253_, v_a_2273_, v_a_2274_, v_v_2249_, lean_box(0), lean_box(0));
return v___x_2275_;
}
default: 
{
lean_object* v___x_2276_; 
lean_dec(v_h__4_2253_);
lean_dec(v_h__3_2252_);
v___x_2276_ = lean_apply_7(v_h__6_2255_, v_u_2248_, v_v_2249_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_2276_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_isIMax_match__1_splitter___redArg(lean_object* v_x_2277_, lean_object* v_h__1_2278_, lean_object* v_h__2_2279_){
_start:
{
if (lean_obj_tag(v_x_2277_) == 3)
{
lean_object* v_a_2280_; lean_object* v_a_2281_; lean_object* v___x_2282_; 
lean_dec(v_h__2_2279_);
v_a_2280_ = lean_ctor_get(v_x_2277_, 0);
lean_inc(v_a_2280_);
v_a_2281_ = lean_ctor_get(v_x_2277_, 1);
lean_inc(v_a_2281_);
lean_dec_ref_known(v_x_2277_, 2);
v___x_2282_ = lean_apply_2(v_h__1_2278_, v_a_2280_, v_a_2281_);
return v___x_2282_;
}
else
{
lean_object* v___x_2283_; 
lean_dec(v_h__1_2278_);
v___x_2283_ = lean_apply_2(v_h__2_2279_, v_x_2277_, lean_box(0));
return v___x_2283_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_isIMax_match__1_splitter(lean_object* v_motive_2284_, lean_object* v_x_2285_, lean_object* v_h__1_2286_, lean_object* v_h__2_2287_){
_start:
{
if (lean_obj_tag(v_x_2285_) == 3)
{
lean_object* v_a_2288_; lean_object* v_a_2289_; lean_object* v___x_2290_; 
lean_dec(v_h__2_2287_);
v_a_2288_ = lean_ctor_get(v_x_2285_, 0);
lean_inc(v_a_2288_);
v_a_2289_ = lean_ctor_get(v_x_2285_, 1);
lean_inc(v_a_2289_);
lean_dec_ref_known(v_x_2285_, 2);
v___x_2290_ = lean_apply_2(v_h__1_2286_, v_a_2288_, v_a_2289_);
return v___x_2290_;
}
else
{
lean_object* v___x_2291_; 
lean_dec(v_h__1_2286_);
v___x_2291_ = lean_apply_2(v_h__2_2287_, v_x_2285_, lean_box(0));
return v___x_2291_;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Level_geq(lean_object* v_u_2292_, lean_object* v_v_2293_){
_start:
{
lean_object* v___x_2294_; lean_object* v___x_2295_; uint8_t v___x_2296_; 
v___x_2294_ = l_Lean_Level_normalize(v_u_2292_);
v___x_2295_ = l_Lean_Level_normalize(v_v_2293_);
v___x_2296_ = l___private_Lean_Level_0__Lean_Level_geq_go(v___x_2294_, v___x_2295_);
lean_dec(v___x_2295_);
lean_dec(v___x_2294_);
return v___x_2296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_geq___boxed(lean_object* v_u_2297_, lean_object* v_v_2298_){
_start:
{
uint8_t v_res_2299_; lean_object* v_r_2300_; 
v_res_2299_ = l_Lean_Level_geq(v_u_2297_, v_v_2298_);
lean_dec(v_v_2298_);
lean_dec(v_u_2297_);
v_r_2300_ = lean_box(v_res_2299_);
return v_r_2300_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Level_collectMVars_spec__1___redArg(lean_object* v_k_2301_, lean_object* v_v_2302_, lean_object* v_t_2303_){
_start:
{
if (lean_obj_tag(v_t_2303_) == 0)
{
lean_object* v_size_2304_; lean_object* v_k_2305_; lean_object* v_v_2306_; lean_object* v_l_2307_; lean_object* v_r_2308_; lean_object* v___x_2310_; uint8_t v_isShared_2311_; uint8_t v_isSharedCheck_2588_; 
v_size_2304_ = lean_ctor_get(v_t_2303_, 0);
v_k_2305_ = lean_ctor_get(v_t_2303_, 1);
v_v_2306_ = lean_ctor_get(v_t_2303_, 2);
v_l_2307_ = lean_ctor_get(v_t_2303_, 3);
v_r_2308_ = lean_ctor_get(v_t_2303_, 4);
v_isSharedCheck_2588_ = !lean_is_exclusive(v_t_2303_);
if (v_isSharedCheck_2588_ == 0)
{
v___x_2310_ = v_t_2303_;
v_isShared_2311_ = v_isSharedCheck_2588_;
goto v_resetjp_2309_;
}
else
{
lean_inc(v_r_2308_);
lean_inc(v_l_2307_);
lean_inc(v_v_2306_);
lean_inc(v_k_2305_);
lean_inc(v_size_2304_);
lean_dec(v_t_2303_);
v___x_2310_ = lean_box(0);
v_isShared_2311_ = v_isSharedCheck_2588_;
goto v_resetjp_2309_;
}
v_resetjp_2309_:
{
uint8_t v___x_2312_; 
v___x_2312_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2301_, v_k_2305_);
switch(v___x_2312_)
{
case 0:
{
lean_object* v_impl_2313_; lean_object* v___x_2314_; 
lean_dec(v_size_2304_);
v_impl_2313_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Level_collectMVars_spec__1___redArg(v_k_2301_, v_v_2302_, v_l_2307_);
v___x_2314_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_2308_) == 0)
{
lean_object* v_size_2315_; lean_object* v_size_2316_; lean_object* v_k_2317_; lean_object* v_v_2318_; lean_object* v_l_2319_; lean_object* v_r_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; uint8_t v___x_2323_; 
v_size_2315_ = lean_ctor_get(v_r_2308_, 0);
v_size_2316_ = lean_ctor_get(v_impl_2313_, 0);
v_k_2317_ = lean_ctor_get(v_impl_2313_, 1);
v_v_2318_ = lean_ctor_get(v_impl_2313_, 2);
v_l_2319_ = lean_ctor_get(v_impl_2313_, 3);
v_r_2320_ = lean_ctor_get(v_impl_2313_, 4);
lean_inc(v_r_2320_);
v___x_2321_ = lean_unsigned_to_nat(3u);
v___x_2322_ = lean_nat_mul(v___x_2321_, v_size_2315_);
v___x_2323_ = lean_nat_dec_lt(v___x_2322_, v_size_2316_);
lean_dec(v___x_2322_);
if (v___x_2323_ == 0)
{
lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2327_; 
lean_dec(v_r_2320_);
v___x_2324_ = lean_nat_add(v___x_2314_, v_size_2316_);
v___x_2325_ = lean_nat_add(v___x_2324_, v_size_2315_);
lean_dec(v___x_2324_);
if (v_isShared_2311_ == 0)
{
lean_ctor_set(v___x_2310_, 3, v_impl_2313_);
lean_ctor_set(v___x_2310_, 0, v___x_2325_);
v___x_2327_ = v___x_2310_;
goto v_reusejp_2326_;
}
else
{
lean_object* v_reuseFailAlloc_2328_; 
v_reuseFailAlloc_2328_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2328_, 0, v___x_2325_);
lean_ctor_set(v_reuseFailAlloc_2328_, 1, v_k_2305_);
lean_ctor_set(v_reuseFailAlloc_2328_, 2, v_v_2306_);
lean_ctor_set(v_reuseFailAlloc_2328_, 3, v_impl_2313_);
lean_ctor_set(v_reuseFailAlloc_2328_, 4, v_r_2308_);
v___x_2327_ = v_reuseFailAlloc_2328_;
goto v_reusejp_2326_;
}
v_reusejp_2326_:
{
return v___x_2327_;
}
}
else
{
lean_object* v___x_2330_; uint8_t v_isShared_2331_; uint8_t v_isSharedCheck_2394_; 
lean_inc(v_l_2319_);
lean_inc(v_v_2318_);
lean_inc(v_k_2317_);
lean_inc(v_size_2316_);
v_isSharedCheck_2394_ = !lean_is_exclusive(v_impl_2313_);
if (v_isSharedCheck_2394_ == 0)
{
lean_object* v_unused_2395_; lean_object* v_unused_2396_; lean_object* v_unused_2397_; lean_object* v_unused_2398_; lean_object* v_unused_2399_; 
v_unused_2395_ = lean_ctor_get(v_impl_2313_, 4);
lean_dec(v_unused_2395_);
v_unused_2396_ = lean_ctor_get(v_impl_2313_, 3);
lean_dec(v_unused_2396_);
v_unused_2397_ = lean_ctor_get(v_impl_2313_, 2);
lean_dec(v_unused_2397_);
v_unused_2398_ = lean_ctor_get(v_impl_2313_, 1);
lean_dec(v_unused_2398_);
v_unused_2399_ = lean_ctor_get(v_impl_2313_, 0);
lean_dec(v_unused_2399_);
v___x_2330_ = v_impl_2313_;
v_isShared_2331_ = v_isSharedCheck_2394_;
goto v_resetjp_2329_;
}
else
{
lean_dec(v_impl_2313_);
v___x_2330_ = lean_box(0);
v_isShared_2331_ = v_isSharedCheck_2394_;
goto v_resetjp_2329_;
}
v_resetjp_2329_:
{
lean_object* v_size_2332_; lean_object* v_size_2333_; lean_object* v_k_2334_; lean_object* v_v_2335_; lean_object* v_l_2336_; lean_object* v_r_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; uint8_t v___x_2340_; 
v_size_2332_ = lean_ctor_get(v_l_2319_, 0);
v_size_2333_ = lean_ctor_get(v_r_2320_, 0);
v_k_2334_ = lean_ctor_get(v_r_2320_, 1);
v_v_2335_ = lean_ctor_get(v_r_2320_, 2);
v_l_2336_ = lean_ctor_get(v_r_2320_, 3);
v_r_2337_ = lean_ctor_get(v_r_2320_, 4);
v___x_2338_ = lean_unsigned_to_nat(2u);
v___x_2339_ = lean_nat_mul(v___x_2338_, v_size_2332_);
v___x_2340_ = lean_nat_dec_lt(v_size_2333_, v___x_2339_);
lean_dec(v___x_2339_);
if (v___x_2340_ == 0)
{
lean_object* v___x_2342_; uint8_t v_isShared_2343_; uint8_t v_isSharedCheck_2369_; 
lean_inc(v_r_2337_);
lean_inc(v_l_2336_);
lean_inc(v_v_2335_);
lean_inc(v_k_2334_);
v_isSharedCheck_2369_ = !lean_is_exclusive(v_r_2320_);
if (v_isSharedCheck_2369_ == 0)
{
lean_object* v_unused_2370_; lean_object* v_unused_2371_; lean_object* v_unused_2372_; lean_object* v_unused_2373_; lean_object* v_unused_2374_; 
v_unused_2370_ = lean_ctor_get(v_r_2320_, 4);
lean_dec(v_unused_2370_);
v_unused_2371_ = lean_ctor_get(v_r_2320_, 3);
lean_dec(v_unused_2371_);
v_unused_2372_ = lean_ctor_get(v_r_2320_, 2);
lean_dec(v_unused_2372_);
v_unused_2373_ = lean_ctor_get(v_r_2320_, 1);
lean_dec(v_unused_2373_);
v_unused_2374_ = lean_ctor_get(v_r_2320_, 0);
lean_dec(v_unused_2374_);
v___x_2342_ = v_r_2320_;
v_isShared_2343_ = v_isSharedCheck_2369_;
goto v_resetjp_2341_;
}
else
{
lean_dec(v_r_2320_);
v___x_2342_ = lean_box(0);
v_isShared_2343_ = v_isSharedCheck_2369_;
goto v_resetjp_2341_;
}
v_resetjp_2341_:
{
lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___y_2347_; lean_object* v___y_2348_; lean_object* v___y_2349_; lean_object* v___x_2357_; lean_object* v___y_2359_; 
v___x_2344_ = lean_nat_add(v___x_2314_, v_size_2316_);
lean_dec(v_size_2316_);
v___x_2345_ = lean_nat_add(v___x_2344_, v_size_2315_);
lean_dec(v___x_2344_);
v___x_2357_ = lean_nat_add(v___x_2314_, v_size_2332_);
if (lean_obj_tag(v_l_2336_) == 0)
{
lean_object* v_size_2367_; 
v_size_2367_ = lean_ctor_get(v_l_2336_, 0);
lean_inc(v_size_2367_);
v___y_2359_ = v_size_2367_;
goto v___jp_2358_;
}
else
{
lean_object* v___x_2368_; 
v___x_2368_ = lean_unsigned_to_nat(0u);
v___y_2359_ = v___x_2368_;
goto v___jp_2358_;
}
v___jp_2346_:
{
lean_object* v___x_2350_; lean_object* v___x_2352_; 
v___x_2350_ = lean_nat_add(v___y_2347_, v___y_2349_);
lean_dec(v___y_2349_);
lean_dec(v___y_2347_);
if (v_isShared_2343_ == 0)
{
lean_ctor_set(v___x_2342_, 4, v_r_2308_);
lean_ctor_set(v___x_2342_, 3, v_r_2337_);
lean_ctor_set(v___x_2342_, 2, v_v_2306_);
lean_ctor_set(v___x_2342_, 1, v_k_2305_);
lean_ctor_set(v___x_2342_, 0, v___x_2350_);
v___x_2352_ = v___x_2342_;
goto v_reusejp_2351_;
}
else
{
lean_object* v_reuseFailAlloc_2356_; 
v_reuseFailAlloc_2356_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2356_, 0, v___x_2350_);
lean_ctor_set(v_reuseFailAlloc_2356_, 1, v_k_2305_);
lean_ctor_set(v_reuseFailAlloc_2356_, 2, v_v_2306_);
lean_ctor_set(v_reuseFailAlloc_2356_, 3, v_r_2337_);
lean_ctor_set(v_reuseFailAlloc_2356_, 4, v_r_2308_);
v___x_2352_ = v_reuseFailAlloc_2356_;
goto v_reusejp_2351_;
}
v_reusejp_2351_:
{
lean_object* v___x_2354_; 
if (v_isShared_2331_ == 0)
{
lean_ctor_set(v___x_2330_, 4, v___x_2352_);
lean_ctor_set(v___x_2330_, 3, v___y_2348_);
lean_ctor_set(v___x_2330_, 2, v_v_2335_);
lean_ctor_set(v___x_2330_, 1, v_k_2334_);
lean_ctor_set(v___x_2330_, 0, v___x_2345_);
v___x_2354_ = v___x_2330_;
goto v_reusejp_2353_;
}
else
{
lean_object* v_reuseFailAlloc_2355_; 
v_reuseFailAlloc_2355_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2355_, 0, v___x_2345_);
lean_ctor_set(v_reuseFailAlloc_2355_, 1, v_k_2334_);
lean_ctor_set(v_reuseFailAlloc_2355_, 2, v_v_2335_);
lean_ctor_set(v_reuseFailAlloc_2355_, 3, v___y_2348_);
lean_ctor_set(v_reuseFailAlloc_2355_, 4, v___x_2352_);
v___x_2354_ = v_reuseFailAlloc_2355_;
goto v_reusejp_2353_;
}
v_reusejp_2353_:
{
return v___x_2354_;
}
}
}
v___jp_2358_:
{
lean_object* v___x_2360_; lean_object* v___x_2362_; 
v___x_2360_ = lean_nat_add(v___x_2357_, v___y_2359_);
lean_dec(v___y_2359_);
lean_dec(v___x_2357_);
if (v_isShared_2311_ == 0)
{
lean_ctor_set(v___x_2310_, 4, v_l_2336_);
lean_ctor_set(v___x_2310_, 3, v_l_2319_);
lean_ctor_set(v___x_2310_, 2, v_v_2318_);
lean_ctor_set(v___x_2310_, 1, v_k_2317_);
lean_ctor_set(v___x_2310_, 0, v___x_2360_);
v___x_2362_ = v___x_2310_;
goto v_reusejp_2361_;
}
else
{
lean_object* v_reuseFailAlloc_2366_; 
v_reuseFailAlloc_2366_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2366_, 0, v___x_2360_);
lean_ctor_set(v_reuseFailAlloc_2366_, 1, v_k_2317_);
lean_ctor_set(v_reuseFailAlloc_2366_, 2, v_v_2318_);
lean_ctor_set(v_reuseFailAlloc_2366_, 3, v_l_2319_);
lean_ctor_set(v_reuseFailAlloc_2366_, 4, v_l_2336_);
v___x_2362_ = v_reuseFailAlloc_2366_;
goto v_reusejp_2361_;
}
v_reusejp_2361_:
{
lean_object* v___x_2363_; 
v___x_2363_ = lean_nat_add(v___x_2314_, v_size_2315_);
if (lean_obj_tag(v_r_2337_) == 0)
{
lean_object* v_size_2364_; 
v_size_2364_ = lean_ctor_get(v_r_2337_, 0);
lean_inc(v_size_2364_);
v___y_2347_ = v___x_2363_;
v___y_2348_ = v___x_2362_;
v___y_2349_ = v_size_2364_;
goto v___jp_2346_;
}
else
{
lean_object* v___x_2365_; 
v___x_2365_ = lean_unsigned_to_nat(0u);
v___y_2347_ = v___x_2363_;
v___y_2348_ = v___x_2362_;
v___y_2349_ = v___x_2365_;
goto v___jp_2346_;
}
}
}
}
}
else
{
lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2380_; 
lean_del_object(v___x_2310_);
v___x_2375_ = lean_nat_add(v___x_2314_, v_size_2316_);
lean_dec(v_size_2316_);
v___x_2376_ = lean_nat_add(v___x_2375_, v_size_2315_);
lean_dec(v___x_2375_);
v___x_2377_ = lean_nat_add(v___x_2314_, v_size_2315_);
v___x_2378_ = lean_nat_add(v___x_2377_, v_size_2333_);
lean_dec(v___x_2377_);
lean_inc_ref(v_r_2308_);
if (v_isShared_2331_ == 0)
{
lean_ctor_set(v___x_2330_, 4, v_r_2308_);
lean_ctor_set(v___x_2330_, 3, v_r_2320_);
lean_ctor_set(v___x_2330_, 2, v_v_2306_);
lean_ctor_set(v___x_2330_, 1, v_k_2305_);
lean_ctor_set(v___x_2330_, 0, v___x_2378_);
v___x_2380_ = v___x_2330_;
goto v_reusejp_2379_;
}
else
{
lean_object* v_reuseFailAlloc_2393_; 
v_reuseFailAlloc_2393_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2393_, 0, v___x_2378_);
lean_ctor_set(v_reuseFailAlloc_2393_, 1, v_k_2305_);
lean_ctor_set(v_reuseFailAlloc_2393_, 2, v_v_2306_);
lean_ctor_set(v_reuseFailAlloc_2393_, 3, v_r_2320_);
lean_ctor_set(v_reuseFailAlloc_2393_, 4, v_r_2308_);
v___x_2380_ = v_reuseFailAlloc_2393_;
goto v_reusejp_2379_;
}
v_reusejp_2379_:
{
lean_object* v___x_2382_; uint8_t v_isShared_2383_; uint8_t v_isSharedCheck_2387_; 
v_isSharedCheck_2387_ = !lean_is_exclusive(v_r_2308_);
if (v_isSharedCheck_2387_ == 0)
{
lean_object* v_unused_2388_; lean_object* v_unused_2389_; lean_object* v_unused_2390_; lean_object* v_unused_2391_; lean_object* v_unused_2392_; 
v_unused_2388_ = lean_ctor_get(v_r_2308_, 4);
lean_dec(v_unused_2388_);
v_unused_2389_ = lean_ctor_get(v_r_2308_, 3);
lean_dec(v_unused_2389_);
v_unused_2390_ = lean_ctor_get(v_r_2308_, 2);
lean_dec(v_unused_2390_);
v_unused_2391_ = lean_ctor_get(v_r_2308_, 1);
lean_dec(v_unused_2391_);
v_unused_2392_ = lean_ctor_get(v_r_2308_, 0);
lean_dec(v_unused_2392_);
v___x_2382_ = v_r_2308_;
v_isShared_2383_ = v_isSharedCheck_2387_;
goto v_resetjp_2381_;
}
else
{
lean_dec(v_r_2308_);
v___x_2382_ = lean_box(0);
v_isShared_2383_ = v_isSharedCheck_2387_;
goto v_resetjp_2381_;
}
v_resetjp_2381_:
{
lean_object* v___x_2385_; 
if (v_isShared_2383_ == 0)
{
lean_ctor_set(v___x_2382_, 4, v___x_2380_);
lean_ctor_set(v___x_2382_, 3, v_l_2319_);
lean_ctor_set(v___x_2382_, 2, v_v_2318_);
lean_ctor_set(v___x_2382_, 1, v_k_2317_);
lean_ctor_set(v___x_2382_, 0, v___x_2376_);
v___x_2385_ = v___x_2382_;
goto v_reusejp_2384_;
}
else
{
lean_object* v_reuseFailAlloc_2386_; 
v_reuseFailAlloc_2386_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2386_, 0, v___x_2376_);
lean_ctor_set(v_reuseFailAlloc_2386_, 1, v_k_2317_);
lean_ctor_set(v_reuseFailAlloc_2386_, 2, v_v_2318_);
lean_ctor_set(v_reuseFailAlloc_2386_, 3, v_l_2319_);
lean_ctor_set(v_reuseFailAlloc_2386_, 4, v___x_2380_);
v___x_2385_ = v_reuseFailAlloc_2386_;
goto v_reusejp_2384_;
}
v_reusejp_2384_:
{
return v___x_2385_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_2400_; 
v_l_2400_ = lean_ctor_get(v_impl_2313_, 3);
if (lean_obj_tag(v_l_2400_) == 0)
{
lean_object* v_r_2401_; lean_object* v_k_2402_; lean_object* v_v_2403_; lean_object* v___x_2405_; uint8_t v_isShared_2406_; uint8_t v_isSharedCheck_2414_; 
lean_inc_ref(v_l_2400_);
v_r_2401_ = lean_ctor_get(v_impl_2313_, 4);
v_k_2402_ = lean_ctor_get(v_impl_2313_, 1);
v_v_2403_ = lean_ctor_get(v_impl_2313_, 2);
v_isSharedCheck_2414_ = !lean_is_exclusive(v_impl_2313_);
if (v_isSharedCheck_2414_ == 0)
{
lean_object* v_unused_2415_; lean_object* v_unused_2416_; 
v_unused_2415_ = lean_ctor_get(v_impl_2313_, 3);
lean_dec(v_unused_2415_);
v_unused_2416_ = lean_ctor_get(v_impl_2313_, 0);
lean_dec(v_unused_2416_);
v___x_2405_ = v_impl_2313_;
v_isShared_2406_ = v_isSharedCheck_2414_;
goto v_resetjp_2404_;
}
else
{
lean_inc(v_r_2401_);
lean_inc(v_v_2403_);
lean_inc(v_k_2402_);
lean_dec(v_impl_2313_);
v___x_2405_ = lean_box(0);
v_isShared_2406_ = v_isSharedCheck_2414_;
goto v_resetjp_2404_;
}
v_resetjp_2404_:
{
lean_object* v___x_2407_; lean_object* v___x_2409_; 
v___x_2407_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_2401_);
if (v_isShared_2406_ == 0)
{
lean_ctor_set(v___x_2405_, 3, v_r_2401_);
lean_ctor_set(v___x_2405_, 2, v_v_2306_);
lean_ctor_set(v___x_2405_, 1, v_k_2305_);
lean_ctor_set(v___x_2405_, 0, v___x_2314_);
v___x_2409_ = v___x_2405_;
goto v_reusejp_2408_;
}
else
{
lean_object* v_reuseFailAlloc_2413_; 
v_reuseFailAlloc_2413_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2413_, 0, v___x_2314_);
lean_ctor_set(v_reuseFailAlloc_2413_, 1, v_k_2305_);
lean_ctor_set(v_reuseFailAlloc_2413_, 2, v_v_2306_);
lean_ctor_set(v_reuseFailAlloc_2413_, 3, v_r_2401_);
lean_ctor_set(v_reuseFailAlloc_2413_, 4, v_r_2401_);
v___x_2409_ = v_reuseFailAlloc_2413_;
goto v_reusejp_2408_;
}
v_reusejp_2408_:
{
lean_object* v___x_2411_; 
if (v_isShared_2311_ == 0)
{
lean_ctor_set(v___x_2310_, 4, v___x_2409_);
lean_ctor_set(v___x_2310_, 3, v_l_2400_);
lean_ctor_set(v___x_2310_, 2, v_v_2403_);
lean_ctor_set(v___x_2310_, 1, v_k_2402_);
lean_ctor_set(v___x_2310_, 0, v___x_2407_);
v___x_2411_ = v___x_2310_;
goto v_reusejp_2410_;
}
else
{
lean_object* v_reuseFailAlloc_2412_; 
v_reuseFailAlloc_2412_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2412_, 0, v___x_2407_);
lean_ctor_set(v_reuseFailAlloc_2412_, 1, v_k_2402_);
lean_ctor_set(v_reuseFailAlloc_2412_, 2, v_v_2403_);
lean_ctor_set(v_reuseFailAlloc_2412_, 3, v_l_2400_);
lean_ctor_set(v_reuseFailAlloc_2412_, 4, v___x_2409_);
v___x_2411_ = v_reuseFailAlloc_2412_;
goto v_reusejp_2410_;
}
v_reusejp_2410_:
{
return v___x_2411_;
}
}
}
}
else
{
lean_object* v_r_2417_; 
v_r_2417_ = lean_ctor_get(v_impl_2313_, 4);
lean_inc(v_r_2417_);
if (lean_obj_tag(v_r_2417_) == 0)
{
lean_object* v_k_2418_; lean_object* v_v_2419_; lean_object* v___x_2421_; uint8_t v_isShared_2422_; uint8_t v_isSharedCheck_2442_; 
lean_inc(v_l_2400_);
v_k_2418_ = lean_ctor_get(v_impl_2313_, 1);
v_v_2419_ = lean_ctor_get(v_impl_2313_, 2);
v_isSharedCheck_2442_ = !lean_is_exclusive(v_impl_2313_);
if (v_isSharedCheck_2442_ == 0)
{
lean_object* v_unused_2443_; lean_object* v_unused_2444_; lean_object* v_unused_2445_; 
v_unused_2443_ = lean_ctor_get(v_impl_2313_, 4);
lean_dec(v_unused_2443_);
v_unused_2444_ = lean_ctor_get(v_impl_2313_, 3);
lean_dec(v_unused_2444_);
v_unused_2445_ = lean_ctor_get(v_impl_2313_, 0);
lean_dec(v_unused_2445_);
v___x_2421_ = v_impl_2313_;
v_isShared_2422_ = v_isSharedCheck_2442_;
goto v_resetjp_2420_;
}
else
{
lean_inc(v_v_2419_);
lean_inc(v_k_2418_);
lean_dec(v_impl_2313_);
v___x_2421_ = lean_box(0);
v_isShared_2422_ = v_isSharedCheck_2442_;
goto v_resetjp_2420_;
}
v_resetjp_2420_:
{
lean_object* v_k_2423_; lean_object* v_v_2424_; lean_object* v___x_2426_; uint8_t v_isShared_2427_; uint8_t v_isSharedCheck_2438_; 
v_k_2423_ = lean_ctor_get(v_r_2417_, 1);
v_v_2424_ = lean_ctor_get(v_r_2417_, 2);
v_isSharedCheck_2438_ = !lean_is_exclusive(v_r_2417_);
if (v_isSharedCheck_2438_ == 0)
{
lean_object* v_unused_2439_; lean_object* v_unused_2440_; lean_object* v_unused_2441_; 
v_unused_2439_ = lean_ctor_get(v_r_2417_, 4);
lean_dec(v_unused_2439_);
v_unused_2440_ = lean_ctor_get(v_r_2417_, 3);
lean_dec(v_unused_2440_);
v_unused_2441_ = lean_ctor_get(v_r_2417_, 0);
lean_dec(v_unused_2441_);
v___x_2426_ = v_r_2417_;
v_isShared_2427_ = v_isSharedCheck_2438_;
goto v_resetjp_2425_;
}
else
{
lean_inc(v_v_2424_);
lean_inc(v_k_2423_);
lean_dec(v_r_2417_);
v___x_2426_ = lean_box(0);
v_isShared_2427_ = v_isSharedCheck_2438_;
goto v_resetjp_2425_;
}
v_resetjp_2425_:
{
lean_object* v___x_2428_; lean_object* v___x_2430_; 
v___x_2428_ = lean_unsigned_to_nat(3u);
if (v_isShared_2427_ == 0)
{
lean_ctor_set(v___x_2426_, 4, v_l_2400_);
lean_ctor_set(v___x_2426_, 3, v_l_2400_);
lean_ctor_set(v___x_2426_, 2, v_v_2419_);
lean_ctor_set(v___x_2426_, 1, v_k_2418_);
lean_ctor_set(v___x_2426_, 0, v___x_2314_);
v___x_2430_ = v___x_2426_;
goto v_reusejp_2429_;
}
else
{
lean_object* v_reuseFailAlloc_2437_; 
v_reuseFailAlloc_2437_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2437_, 0, v___x_2314_);
lean_ctor_set(v_reuseFailAlloc_2437_, 1, v_k_2418_);
lean_ctor_set(v_reuseFailAlloc_2437_, 2, v_v_2419_);
lean_ctor_set(v_reuseFailAlloc_2437_, 3, v_l_2400_);
lean_ctor_set(v_reuseFailAlloc_2437_, 4, v_l_2400_);
v___x_2430_ = v_reuseFailAlloc_2437_;
goto v_reusejp_2429_;
}
v_reusejp_2429_:
{
lean_object* v___x_2432_; 
if (v_isShared_2422_ == 0)
{
lean_ctor_set(v___x_2421_, 4, v_l_2400_);
lean_ctor_set(v___x_2421_, 2, v_v_2306_);
lean_ctor_set(v___x_2421_, 1, v_k_2305_);
lean_ctor_set(v___x_2421_, 0, v___x_2314_);
v___x_2432_ = v___x_2421_;
goto v_reusejp_2431_;
}
else
{
lean_object* v_reuseFailAlloc_2436_; 
v_reuseFailAlloc_2436_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2436_, 0, v___x_2314_);
lean_ctor_set(v_reuseFailAlloc_2436_, 1, v_k_2305_);
lean_ctor_set(v_reuseFailAlloc_2436_, 2, v_v_2306_);
lean_ctor_set(v_reuseFailAlloc_2436_, 3, v_l_2400_);
lean_ctor_set(v_reuseFailAlloc_2436_, 4, v_l_2400_);
v___x_2432_ = v_reuseFailAlloc_2436_;
goto v_reusejp_2431_;
}
v_reusejp_2431_:
{
lean_object* v___x_2434_; 
if (v_isShared_2311_ == 0)
{
lean_ctor_set(v___x_2310_, 4, v___x_2432_);
lean_ctor_set(v___x_2310_, 3, v___x_2430_);
lean_ctor_set(v___x_2310_, 2, v_v_2424_);
lean_ctor_set(v___x_2310_, 1, v_k_2423_);
lean_ctor_set(v___x_2310_, 0, v___x_2428_);
v___x_2434_ = v___x_2310_;
goto v_reusejp_2433_;
}
else
{
lean_object* v_reuseFailAlloc_2435_; 
v_reuseFailAlloc_2435_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2435_, 0, v___x_2428_);
lean_ctor_set(v_reuseFailAlloc_2435_, 1, v_k_2423_);
lean_ctor_set(v_reuseFailAlloc_2435_, 2, v_v_2424_);
lean_ctor_set(v_reuseFailAlloc_2435_, 3, v___x_2430_);
lean_ctor_set(v_reuseFailAlloc_2435_, 4, v___x_2432_);
v___x_2434_ = v_reuseFailAlloc_2435_;
goto v_reusejp_2433_;
}
v_reusejp_2433_:
{
return v___x_2434_;
}
}
}
}
}
}
else
{
lean_object* v___x_2446_; lean_object* v___x_2448_; 
v___x_2446_ = lean_unsigned_to_nat(2u);
if (v_isShared_2311_ == 0)
{
lean_ctor_set(v___x_2310_, 4, v_r_2417_);
lean_ctor_set(v___x_2310_, 3, v_impl_2313_);
lean_ctor_set(v___x_2310_, 0, v___x_2446_);
v___x_2448_ = v___x_2310_;
goto v_reusejp_2447_;
}
else
{
lean_object* v_reuseFailAlloc_2449_; 
v_reuseFailAlloc_2449_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2449_, 0, v___x_2446_);
lean_ctor_set(v_reuseFailAlloc_2449_, 1, v_k_2305_);
lean_ctor_set(v_reuseFailAlloc_2449_, 2, v_v_2306_);
lean_ctor_set(v_reuseFailAlloc_2449_, 3, v_impl_2313_);
lean_ctor_set(v_reuseFailAlloc_2449_, 4, v_r_2417_);
v___x_2448_ = v_reuseFailAlloc_2449_;
goto v_reusejp_2447_;
}
v_reusejp_2447_:
{
return v___x_2448_;
}
}
}
}
}
case 1:
{
lean_object* v___x_2451_; 
lean_dec(v_v_2306_);
lean_dec(v_k_2305_);
if (v_isShared_2311_ == 0)
{
lean_ctor_set(v___x_2310_, 2, v_v_2302_);
lean_ctor_set(v___x_2310_, 1, v_k_2301_);
v___x_2451_ = v___x_2310_;
goto v_reusejp_2450_;
}
else
{
lean_object* v_reuseFailAlloc_2452_; 
v_reuseFailAlloc_2452_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2452_, 0, v_size_2304_);
lean_ctor_set(v_reuseFailAlloc_2452_, 1, v_k_2301_);
lean_ctor_set(v_reuseFailAlloc_2452_, 2, v_v_2302_);
lean_ctor_set(v_reuseFailAlloc_2452_, 3, v_l_2307_);
lean_ctor_set(v_reuseFailAlloc_2452_, 4, v_r_2308_);
v___x_2451_ = v_reuseFailAlloc_2452_;
goto v_reusejp_2450_;
}
v_reusejp_2450_:
{
return v___x_2451_;
}
}
default: 
{
lean_object* v_impl_2453_; lean_object* v___x_2454_; 
lean_dec(v_size_2304_);
v_impl_2453_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Level_collectMVars_spec__1___redArg(v_k_2301_, v_v_2302_, v_r_2308_);
v___x_2454_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_2307_) == 0)
{
lean_object* v_size_2455_; lean_object* v_size_2456_; lean_object* v_k_2457_; lean_object* v_v_2458_; lean_object* v_l_2459_; lean_object* v_r_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; uint8_t v___x_2463_; 
v_size_2455_ = lean_ctor_get(v_l_2307_, 0);
v_size_2456_ = lean_ctor_get(v_impl_2453_, 0);
v_k_2457_ = lean_ctor_get(v_impl_2453_, 1);
v_v_2458_ = lean_ctor_get(v_impl_2453_, 2);
v_l_2459_ = lean_ctor_get(v_impl_2453_, 3);
lean_inc(v_l_2459_);
v_r_2460_ = lean_ctor_get(v_impl_2453_, 4);
v___x_2461_ = lean_unsigned_to_nat(3u);
v___x_2462_ = lean_nat_mul(v___x_2461_, v_size_2455_);
v___x_2463_ = lean_nat_dec_lt(v___x_2462_, v_size_2456_);
lean_dec(v___x_2462_);
if (v___x_2463_ == 0)
{
lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2467_; 
lean_dec(v_l_2459_);
v___x_2464_ = lean_nat_add(v___x_2454_, v_size_2455_);
v___x_2465_ = lean_nat_add(v___x_2464_, v_size_2456_);
lean_dec(v___x_2464_);
if (v_isShared_2311_ == 0)
{
lean_ctor_set(v___x_2310_, 4, v_impl_2453_);
lean_ctor_set(v___x_2310_, 0, v___x_2465_);
v___x_2467_ = v___x_2310_;
goto v_reusejp_2466_;
}
else
{
lean_object* v_reuseFailAlloc_2468_; 
v_reuseFailAlloc_2468_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2468_, 0, v___x_2465_);
lean_ctor_set(v_reuseFailAlloc_2468_, 1, v_k_2305_);
lean_ctor_set(v_reuseFailAlloc_2468_, 2, v_v_2306_);
lean_ctor_set(v_reuseFailAlloc_2468_, 3, v_l_2307_);
lean_ctor_set(v_reuseFailAlloc_2468_, 4, v_impl_2453_);
v___x_2467_ = v_reuseFailAlloc_2468_;
goto v_reusejp_2466_;
}
v_reusejp_2466_:
{
return v___x_2467_;
}
}
else
{
lean_object* v___x_2470_; uint8_t v_isShared_2471_; uint8_t v_isSharedCheck_2532_; 
lean_inc(v_r_2460_);
lean_inc(v_v_2458_);
lean_inc(v_k_2457_);
lean_inc(v_size_2456_);
v_isSharedCheck_2532_ = !lean_is_exclusive(v_impl_2453_);
if (v_isSharedCheck_2532_ == 0)
{
lean_object* v_unused_2533_; lean_object* v_unused_2534_; lean_object* v_unused_2535_; lean_object* v_unused_2536_; lean_object* v_unused_2537_; 
v_unused_2533_ = lean_ctor_get(v_impl_2453_, 4);
lean_dec(v_unused_2533_);
v_unused_2534_ = lean_ctor_get(v_impl_2453_, 3);
lean_dec(v_unused_2534_);
v_unused_2535_ = lean_ctor_get(v_impl_2453_, 2);
lean_dec(v_unused_2535_);
v_unused_2536_ = lean_ctor_get(v_impl_2453_, 1);
lean_dec(v_unused_2536_);
v_unused_2537_ = lean_ctor_get(v_impl_2453_, 0);
lean_dec(v_unused_2537_);
v___x_2470_ = v_impl_2453_;
v_isShared_2471_ = v_isSharedCheck_2532_;
goto v_resetjp_2469_;
}
else
{
lean_dec(v_impl_2453_);
v___x_2470_ = lean_box(0);
v_isShared_2471_ = v_isSharedCheck_2532_;
goto v_resetjp_2469_;
}
v_resetjp_2469_:
{
lean_object* v_size_2472_; lean_object* v_k_2473_; lean_object* v_v_2474_; lean_object* v_l_2475_; lean_object* v_r_2476_; lean_object* v_size_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; uint8_t v___x_2480_; 
v_size_2472_ = lean_ctor_get(v_l_2459_, 0);
v_k_2473_ = lean_ctor_get(v_l_2459_, 1);
v_v_2474_ = lean_ctor_get(v_l_2459_, 2);
v_l_2475_ = lean_ctor_get(v_l_2459_, 3);
v_r_2476_ = lean_ctor_get(v_l_2459_, 4);
v_size_2477_ = lean_ctor_get(v_r_2460_, 0);
v___x_2478_ = lean_unsigned_to_nat(2u);
v___x_2479_ = lean_nat_mul(v___x_2478_, v_size_2477_);
v___x_2480_ = lean_nat_dec_lt(v_size_2472_, v___x_2479_);
lean_dec(v___x_2479_);
if (v___x_2480_ == 0)
{
lean_object* v___x_2482_; uint8_t v_isShared_2483_; uint8_t v_isSharedCheck_2508_; 
lean_inc(v_r_2476_);
lean_inc(v_l_2475_);
lean_inc(v_v_2474_);
lean_inc(v_k_2473_);
v_isSharedCheck_2508_ = !lean_is_exclusive(v_l_2459_);
if (v_isSharedCheck_2508_ == 0)
{
lean_object* v_unused_2509_; lean_object* v_unused_2510_; lean_object* v_unused_2511_; lean_object* v_unused_2512_; lean_object* v_unused_2513_; 
v_unused_2509_ = lean_ctor_get(v_l_2459_, 4);
lean_dec(v_unused_2509_);
v_unused_2510_ = lean_ctor_get(v_l_2459_, 3);
lean_dec(v_unused_2510_);
v_unused_2511_ = lean_ctor_get(v_l_2459_, 2);
lean_dec(v_unused_2511_);
v_unused_2512_ = lean_ctor_get(v_l_2459_, 1);
lean_dec(v_unused_2512_);
v_unused_2513_ = lean_ctor_get(v_l_2459_, 0);
lean_dec(v_unused_2513_);
v___x_2482_ = v_l_2459_;
v_isShared_2483_ = v_isSharedCheck_2508_;
goto v_resetjp_2481_;
}
else
{
lean_dec(v_l_2459_);
v___x_2482_ = lean_box(0);
v_isShared_2483_ = v_isSharedCheck_2508_;
goto v_resetjp_2481_;
}
v_resetjp_2481_:
{
lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___y_2487_; lean_object* v___y_2488_; lean_object* v___y_2489_; lean_object* v___y_2498_; 
v___x_2484_ = lean_nat_add(v___x_2454_, v_size_2455_);
v___x_2485_ = lean_nat_add(v___x_2484_, v_size_2456_);
lean_dec(v_size_2456_);
if (lean_obj_tag(v_l_2475_) == 0)
{
lean_object* v_size_2506_; 
v_size_2506_ = lean_ctor_get(v_l_2475_, 0);
lean_inc(v_size_2506_);
v___y_2498_ = v_size_2506_;
goto v___jp_2497_;
}
else
{
lean_object* v___x_2507_; 
v___x_2507_ = lean_unsigned_to_nat(0u);
v___y_2498_ = v___x_2507_;
goto v___jp_2497_;
}
v___jp_2486_:
{
lean_object* v___x_2490_; lean_object* v___x_2492_; 
v___x_2490_ = lean_nat_add(v___y_2487_, v___y_2489_);
lean_dec(v___y_2489_);
lean_dec(v___y_2487_);
if (v_isShared_2483_ == 0)
{
lean_ctor_set(v___x_2482_, 4, v_r_2460_);
lean_ctor_set(v___x_2482_, 3, v_r_2476_);
lean_ctor_set(v___x_2482_, 2, v_v_2458_);
lean_ctor_set(v___x_2482_, 1, v_k_2457_);
lean_ctor_set(v___x_2482_, 0, v___x_2490_);
v___x_2492_ = v___x_2482_;
goto v_reusejp_2491_;
}
else
{
lean_object* v_reuseFailAlloc_2496_; 
v_reuseFailAlloc_2496_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2496_, 0, v___x_2490_);
lean_ctor_set(v_reuseFailAlloc_2496_, 1, v_k_2457_);
lean_ctor_set(v_reuseFailAlloc_2496_, 2, v_v_2458_);
lean_ctor_set(v_reuseFailAlloc_2496_, 3, v_r_2476_);
lean_ctor_set(v_reuseFailAlloc_2496_, 4, v_r_2460_);
v___x_2492_ = v_reuseFailAlloc_2496_;
goto v_reusejp_2491_;
}
v_reusejp_2491_:
{
lean_object* v___x_2494_; 
if (v_isShared_2471_ == 0)
{
lean_ctor_set(v___x_2470_, 4, v___x_2492_);
lean_ctor_set(v___x_2470_, 3, v___y_2488_);
lean_ctor_set(v___x_2470_, 2, v_v_2474_);
lean_ctor_set(v___x_2470_, 1, v_k_2473_);
lean_ctor_set(v___x_2470_, 0, v___x_2485_);
v___x_2494_ = v___x_2470_;
goto v_reusejp_2493_;
}
else
{
lean_object* v_reuseFailAlloc_2495_; 
v_reuseFailAlloc_2495_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2495_, 0, v___x_2485_);
lean_ctor_set(v_reuseFailAlloc_2495_, 1, v_k_2473_);
lean_ctor_set(v_reuseFailAlloc_2495_, 2, v_v_2474_);
lean_ctor_set(v_reuseFailAlloc_2495_, 3, v___y_2488_);
lean_ctor_set(v_reuseFailAlloc_2495_, 4, v___x_2492_);
v___x_2494_ = v_reuseFailAlloc_2495_;
goto v_reusejp_2493_;
}
v_reusejp_2493_:
{
return v___x_2494_;
}
}
}
v___jp_2497_:
{
lean_object* v___x_2499_; lean_object* v___x_2501_; 
v___x_2499_ = lean_nat_add(v___x_2484_, v___y_2498_);
lean_dec(v___y_2498_);
lean_dec(v___x_2484_);
if (v_isShared_2311_ == 0)
{
lean_ctor_set(v___x_2310_, 4, v_l_2475_);
lean_ctor_set(v___x_2310_, 0, v___x_2499_);
v___x_2501_ = v___x_2310_;
goto v_reusejp_2500_;
}
else
{
lean_object* v_reuseFailAlloc_2505_; 
v_reuseFailAlloc_2505_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2505_, 0, v___x_2499_);
lean_ctor_set(v_reuseFailAlloc_2505_, 1, v_k_2305_);
lean_ctor_set(v_reuseFailAlloc_2505_, 2, v_v_2306_);
lean_ctor_set(v_reuseFailAlloc_2505_, 3, v_l_2307_);
lean_ctor_set(v_reuseFailAlloc_2505_, 4, v_l_2475_);
v___x_2501_ = v_reuseFailAlloc_2505_;
goto v_reusejp_2500_;
}
v_reusejp_2500_:
{
lean_object* v___x_2502_; 
v___x_2502_ = lean_nat_add(v___x_2454_, v_size_2477_);
if (lean_obj_tag(v_r_2476_) == 0)
{
lean_object* v_size_2503_; 
v_size_2503_ = lean_ctor_get(v_r_2476_, 0);
lean_inc(v_size_2503_);
v___y_2487_ = v___x_2502_;
v___y_2488_ = v___x_2501_;
v___y_2489_ = v_size_2503_;
goto v___jp_2486_;
}
else
{
lean_object* v___x_2504_; 
v___x_2504_ = lean_unsigned_to_nat(0u);
v___y_2487_ = v___x_2502_;
v___y_2488_ = v___x_2501_;
v___y_2489_ = v___x_2504_;
goto v___jp_2486_;
}
}
}
}
}
else
{
lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2518_; 
lean_del_object(v___x_2310_);
v___x_2514_ = lean_nat_add(v___x_2454_, v_size_2455_);
v___x_2515_ = lean_nat_add(v___x_2514_, v_size_2456_);
lean_dec(v_size_2456_);
v___x_2516_ = lean_nat_add(v___x_2514_, v_size_2472_);
lean_dec(v___x_2514_);
lean_inc_ref(v_l_2307_);
if (v_isShared_2471_ == 0)
{
lean_ctor_set(v___x_2470_, 4, v_l_2459_);
lean_ctor_set(v___x_2470_, 3, v_l_2307_);
lean_ctor_set(v___x_2470_, 2, v_v_2306_);
lean_ctor_set(v___x_2470_, 1, v_k_2305_);
lean_ctor_set(v___x_2470_, 0, v___x_2516_);
v___x_2518_ = v___x_2470_;
goto v_reusejp_2517_;
}
else
{
lean_object* v_reuseFailAlloc_2531_; 
v_reuseFailAlloc_2531_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2531_, 0, v___x_2516_);
lean_ctor_set(v_reuseFailAlloc_2531_, 1, v_k_2305_);
lean_ctor_set(v_reuseFailAlloc_2531_, 2, v_v_2306_);
lean_ctor_set(v_reuseFailAlloc_2531_, 3, v_l_2307_);
lean_ctor_set(v_reuseFailAlloc_2531_, 4, v_l_2459_);
v___x_2518_ = v_reuseFailAlloc_2531_;
goto v_reusejp_2517_;
}
v_reusejp_2517_:
{
lean_object* v___x_2520_; uint8_t v_isShared_2521_; uint8_t v_isSharedCheck_2525_; 
v_isSharedCheck_2525_ = !lean_is_exclusive(v_l_2307_);
if (v_isSharedCheck_2525_ == 0)
{
lean_object* v_unused_2526_; lean_object* v_unused_2527_; lean_object* v_unused_2528_; lean_object* v_unused_2529_; lean_object* v_unused_2530_; 
v_unused_2526_ = lean_ctor_get(v_l_2307_, 4);
lean_dec(v_unused_2526_);
v_unused_2527_ = lean_ctor_get(v_l_2307_, 3);
lean_dec(v_unused_2527_);
v_unused_2528_ = lean_ctor_get(v_l_2307_, 2);
lean_dec(v_unused_2528_);
v_unused_2529_ = lean_ctor_get(v_l_2307_, 1);
lean_dec(v_unused_2529_);
v_unused_2530_ = lean_ctor_get(v_l_2307_, 0);
lean_dec(v_unused_2530_);
v___x_2520_ = v_l_2307_;
v_isShared_2521_ = v_isSharedCheck_2525_;
goto v_resetjp_2519_;
}
else
{
lean_dec(v_l_2307_);
v___x_2520_ = lean_box(0);
v_isShared_2521_ = v_isSharedCheck_2525_;
goto v_resetjp_2519_;
}
v_resetjp_2519_:
{
lean_object* v___x_2523_; 
if (v_isShared_2521_ == 0)
{
lean_ctor_set(v___x_2520_, 4, v_r_2460_);
lean_ctor_set(v___x_2520_, 3, v___x_2518_);
lean_ctor_set(v___x_2520_, 2, v_v_2458_);
lean_ctor_set(v___x_2520_, 1, v_k_2457_);
lean_ctor_set(v___x_2520_, 0, v___x_2515_);
v___x_2523_ = v___x_2520_;
goto v_reusejp_2522_;
}
else
{
lean_object* v_reuseFailAlloc_2524_; 
v_reuseFailAlloc_2524_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2524_, 0, v___x_2515_);
lean_ctor_set(v_reuseFailAlloc_2524_, 1, v_k_2457_);
lean_ctor_set(v_reuseFailAlloc_2524_, 2, v_v_2458_);
lean_ctor_set(v_reuseFailAlloc_2524_, 3, v___x_2518_);
lean_ctor_set(v_reuseFailAlloc_2524_, 4, v_r_2460_);
v___x_2523_ = v_reuseFailAlloc_2524_;
goto v_reusejp_2522_;
}
v_reusejp_2522_:
{
return v___x_2523_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_2538_; 
v_l_2538_ = lean_ctor_get(v_impl_2453_, 3);
lean_inc(v_l_2538_);
if (lean_obj_tag(v_l_2538_) == 0)
{
lean_object* v_r_2539_; lean_object* v_k_2540_; lean_object* v_v_2541_; lean_object* v___x_2543_; uint8_t v_isShared_2544_; uint8_t v_isSharedCheck_2564_; 
v_r_2539_ = lean_ctor_get(v_impl_2453_, 4);
v_k_2540_ = lean_ctor_get(v_impl_2453_, 1);
v_v_2541_ = lean_ctor_get(v_impl_2453_, 2);
v_isSharedCheck_2564_ = !lean_is_exclusive(v_impl_2453_);
if (v_isSharedCheck_2564_ == 0)
{
lean_object* v_unused_2565_; lean_object* v_unused_2566_; 
v_unused_2565_ = lean_ctor_get(v_impl_2453_, 3);
lean_dec(v_unused_2565_);
v_unused_2566_ = lean_ctor_get(v_impl_2453_, 0);
lean_dec(v_unused_2566_);
v___x_2543_ = v_impl_2453_;
v_isShared_2544_ = v_isSharedCheck_2564_;
goto v_resetjp_2542_;
}
else
{
lean_inc(v_r_2539_);
lean_inc(v_v_2541_);
lean_inc(v_k_2540_);
lean_dec(v_impl_2453_);
v___x_2543_ = lean_box(0);
v_isShared_2544_ = v_isSharedCheck_2564_;
goto v_resetjp_2542_;
}
v_resetjp_2542_:
{
lean_object* v_k_2545_; lean_object* v_v_2546_; lean_object* v___x_2548_; uint8_t v_isShared_2549_; uint8_t v_isSharedCheck_2560_; 
v_k_2545_ = lean_ctor_get(v_l_2538_, 1);
v_v_2546_ = lean_ctor_get(v_l_2538_, 2);
v_isSharedCheck_2560_ = !lean_is_exclusive(v_l_2538_);
if (v_isSharedCheck_2560_ == 0)
{
lean_object* v_unused_2561_; lean_object* v_unused_2562_; lean_object* v_unused_2563_; 
v_unused_2561_ = lean_ctor_get(v_l_2538_, 4);
lean_dec(v_unused_2561_);
v_unused_2562_ = lean_ctor_get(v_l_2538_, 3);
lean_dec(v_unused_2562_);
v_unused_2563_ = lean_ctor_get(v_l_2538_, 0);
lean_dec(v_unused_2563_);
v___x_2548_ = v_l_2538_;
v_isShared_2549_ = v_isSharedCheck_2560_;
goto v_resetjp_2547_;
}
else
{
lean_inc(v_v_2546_);
lean_inc(v_k_2545_);
lean_dec(v_l_2538_);
v___x_2548_ = lean_box(0);
v_isShared_2549_ = v_isSharedCheck_2560_;
goto v_resetjp_2547_;
}
v_resetjp_2547_:
{
lean_object* v___x_2550_; lean_object* v___x_2552_; 
v___x_2550_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_2539_, 2);
if (v_isShared_2549_ == 0)
{
lean_ctor_set(v___x_2548_, 4, v_r_2539_);
lean_ctor_set(v___x_2548_, 3, v_r_2539_);
lean_ctor_set(v___x_2548_, 2, v_v_2306_);
lean_ctor_set(v___x_2548_, 1, v_k_2305_);
lean_ctor_set(v___x_2548_, 0, v___x_2454_);
v___x_2552_ = v___x_2548_;
goto v_reusejp_2551_;
}
else
{
lean_object* v_reuseFailAlloc_2559_; 
v_reuseFailAlloc_2559_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2559_, 0, v___x_2454_);
lean_ctor_set(v_reuseFailAlloc_2559_, 1, v_k_2305_);
lean_ctor_set(v_reuseFailAlloc_2559_, 2, v_v_2306_);
lean_ctor_set(v_reuseFailAlloc_2559_, 3, v_r_2539_);
lean_ctor_set(v_reuseFailAlloc_2559_, 4, v_r_2539_);
v___x_2552_ = v_reuseFailAlloc_2559_;
goto v_reusejp_2551_;
}
v_reusejp_2551_:
{
lean_object* v___x_2554_; 
lean_inc(v_r_2539_);
if (v_isShared_2544_ == 0)
{
lean_ctor_set(v___x_2543_, 3, v_r_2539_);
lean_ctor_set(v___x_2543_, 0, v___x_2454_);
v___x_2554_ = v___x_2543_;
goto v_reusejp_2553_;
}
else
{
lean_object* v_reuseFailAlloc_2558_; 
v_reuseFailAlloc_2558_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2558_, 0, v___x_2454_);
lean_ctor_set(v_reuseFailAlloc_2558_, 1, v_k_2540_);
lean_ctor_set(v_reuseFailAlloc_2558_, 2, v_v_2541_);
lean_ctor_set(v_reuseFailAlloc_2558_, 3, v_r_2539_);
lean_ctor_set(v_reuseFailAlloc_2558_, 4, v_r_2539_);
v___x_2554_ = v_reuseFailAlloc_2558_;
goto v_reusejp_2553_;
}
v_reusejp_2553_:
{
lean_object* v___x_2556_; 
if (v_isShared_2311_ == 0)
{
lean_ctor_set(v___x_2310_, 4, v___x_2554_);
lean_ctor_set(v___x_2310_, 3, v___x_2552_);
lean_ctor_set(v___x_2310_, 2, v_v_2546_);
lean_ctor_set(v___x_2310_, 1, v_k_2545_);
lean_ctor_set(v___x_2310_, 0, v___x_2550_);
v___x_2556_ = v___x_2310_;
goto v_reusejp_2555_;
}
else
{
lean_object* v_reuseFailAlloc_2557_; 
v_reuseFailAlloc_2557_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2557_, 0, v___x_2550_);
lean_ctor_set(v_reuseFailAlloc_2557_, 1, v_k_2545_);
lean_ctor_set(v_reuseFailAlloc_2557_, 2, v_v_2546_);
lean_ctor_set(v_reuseFailAlloc_2557_, 3, v___x_2552_);
lean_ctor_set(v_reuseFailAlloc_2557_, 4, v___x_2554_);
v___x_2556_ = v_reuseFailAlloc_2557_;
goto v_reusejp_2555_;
}
v_reusejp_2555_:
{
return v___x_2556_;
}
}
}
}
}
}
else
{
lean_object* v_r_2567_; 
v_r_2567_ = lean_ctor_get(v_impl_2453_, 4);
lean_inc(v_r_2567_);
if (lean_obj_tag(v_r_2567_) == 0)
{
lean_object* v_k_2568_; lean_object* v_v_2569_; lean_object* v___x_2571_; uint8_t v_isShared_2572_; uint8_t v_isSharedCheck_2580_; 
v_k_2568_ = lean_ctor_get(v_impl_2453_, 1);
v_v_2569_ = lean_ctor_get(v_impl_2453_, 2);
v_isSharedCheck_2580_ = !lean_is_exclusive(v_impl_2453_);
if (v_isSharedCheck_2580_ == 0)
{
lean_object* v_unused_2581_; lean_object* v_unused_2582_; lean_object* v_unused_2583_; 
v_unused_2581_ = lean_ctor_get(v_impl_2453_, 4);
lean_dec(v_unused_2581_);
v_unused_2582_ = lean_ctor_get(v_impl_2453_, 3);
lean_dec(v_unused_2582_);
v_unused_2583_ = lean_ctor_get(v_impl_2453_, 0);
lean_dec(v_unused_2583_);
v___x_2571_ = v_impl_2453_;
v_isShared_2572_ = v_isSharedCheck_2580_;
goto v_resetjp_2570_;
}
else
{
lean_inc(v_v_2569_);
lean_inc(v_k_2568_);
lean_dec(v_impl_2453_);
v___x_2571_ = lean_box(0);
v_isShared_2572_ = v_isSharedCheck_2580_;
goto v_resetjp_2570_;
}
v_resetjp_2570_:
{
lean_object* v___x_2573_; lean_object* v___x_2575_; 
v___x_2573_ = lean_unsigned_to_nat(3u);
if (v_isShared_2572_ == 0)
{
lean_ctor_set(v___x_2571_, 4, v_l_2538_);
lean_ctor_set(v___x_2571_, 2, v_v_2306_);
lean_ctor_set(v___x_2571_, 1, v_k_2305_);
lean_ctor_set(v___x_2571_, 0, v___x_2454_);
v___x_2575_ = v___x_2571_;
goto v_reusejp_2574_;
}
else
{
lean_object* v_reuseFailAlloc_2579_; 
v_reuseFailAlloc_2579_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2579_, 0, v___x_2454_);
lean_ctor_set(v_reuseFailAlloc_2579_, 1, v_k_2305_);
lean_ctor_set(v_reuseFailAlloc_2579_, 2, v_v_2306_);
lean_ctor_set(v_reuseFailAlloc_2579_, 3, v_l_2538_);
lean_ctor_set(v_reuseFailAlloc_2579_, 4, v_l_2538_);
v___x_2575_ = v_reuseFailAlloc_2579_;
goto v_reusejp_2574_;
}
v_reusejp_2574_:
{
lean_object* v___x_2577_; 
if (v_isShared_2311_ == 0)
{
lean_ctor_set(v___x_2310_, 4, v_r_2567_);
lean_ctor_set(v___x_2310_, 3, v___x_2575_);
lean_ctor_set(v___x_2310_, 2, v_v_2569_);
lean_ctor_set(v___x_2310_, 1, v_k_2568_);
lean_ctor_set(v___x_2310_, 0, v___x_2573_);
v___x_2577_ = v___x_2310_;
goto v_reusejp_2576_;
}
else
{
lean_object* v_reuseFailAlloc_2578_; 
v_reuseFailAlloc_2578_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2578_, 0, v___x_2573_);
lean_ctor_set(v_reuseFailAlloc_2578_, 1, v_k_2568_);
lean_ctor_set(v_reuseFailAlloc_2578_, 2, v_v_2569_);
lean_ctor_set(v_reuseFailAlloc_2578_, 3, v___x_2575_);
lean_ctor_set(v_reuseFailAlloc_2578_, 4, v_r_2567_);
v___x_2577_ = v_reuseFailAlloc_2578_;
goto v_reusejp_2576_;
}
v_reusejp_2576_:
{
return v___x_2577_;
}
}
}
}
else
{
lean_object* v___x_2584_; lean_object* v___x_2586_; 
v___x_2584_ = lean_unsigned_to_nat(2u);
if (v_isShared_2311_ == 0)
{
lean_ctor_set(v___x_2310_, 4, v_impl_2453_);
lean_ctor_set(v___x_2310_, 3, v_r_2567_);
lean_ctor_set(v___x_2310_, 0, v___x_2584_);
v___x_2586_ = v___x_2310_;
goto v_reusejp_2585_;
}
else
{
lean_object* v_reuseFailAlloc_2587_; 
v_reuseFailAlloc_2587_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2587_, 0, v___x_2584_);
lean_ctor_set(v_reuseFailAlloc_2587_, 1, v_k_2305_);
lean_ctor_set(v_reuseFailAlloc_2587_, 2, v_v_2306_);
lean_ctor_set(v_reuseFailAlloc_2587_, 3, v_r_2567_);
lean_ctor_set(v_reuseFailAlloc_2587_, 4, v_impl_2453_);
v___x_2586_ = v_reuseFailAlloc_2587_;
goto v_reusejp_2585_;
}
v_reusejp_2585_:
{
return v___x_2586_;
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
lean_object* v___x_2589_; lean_object* v___x_2590_; 
v___x_2589_ = lean_unsigned_to_nat(1u);
v___x_2590_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2590_, 0, v___x_2589_);
lean_ctor_set(v___x_2590_, 1, v_k_2301_);
lean_ctor_set(v___x_2590_, 2, v_v_2302_);
lean_ctor_set(v___x_2590_, 3, v_t_2303_);
lean_ctor_set(v___x_2590_, 4, v_t_2303_);
return v___x_2590_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Level_collectMVars_spec__0___redArg(lean_object* v_k_2591_, lean_object* v_t_2592_){
_start:
{
if (lean_obj_tag(v_t_2592_) == 0)
{
lean_object* v_k_2593_; lean_object* v_l_2594_; lean_object* v_r_2595_; uint8_t v___x_2596_; 
v_k_2593_ = lean_ctor_get(v_t_2592_, 1);
v_l_2594_ = lean_ctor_get(v_t_2592_, 3);
v_r_2595_ = lean_ctor_get(v_t_2592_, 4);
v___x_2596_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2591_, v_k_2593_);
switch(v___x_2596_)
{
case 0:
{
v_t_2592_ = v_l_2594_;
goto _start;
}
case 1:
{
uint8_t v___x_2598_; 
v___x_2598_ = 1;
return v___x_2598_;
}
default: 
{
v_t_2592_ = v_r_2595_;
goto _start;
}
}
}
else
{
uint8_t v___x_2600_; 
v___x_2600_ = 0;
return v___x_2600_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Level_collectMVars_spec__0___redArg___boxed(lean_object* v_k_2601_, lean_object* v_t_2602_){
_start:
{
uint8_t v_res_2603_; lean_object* v_r_2604_; 
v_res_2603_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Level_collectMVars_spec__0___redArg(v_k_2601_, v_t_2602_);
lean_dec(v_t_2602_);
lean_dec(v_k_2601_);
v_r_2604_ = lean_box(v_res_2603_);
return v_r_2604_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_collectMVars(lean_object* v_u_2605_, lean_object* v_s_2606_){
_start:
{
lean_object* v_u_2608_; lean_object* v_v_2609_; 
switch(lean_obj_tag(v_u_2605_))
{
case 1:
{
lean_object* v_a_2612_; 
v_a_2612_ = lean_ctor_get(v_u_2605_, 0);
lean_inc(v_a_2612_);
lean_dec_ref_known(v_u_2605_, 1);
v_u_2605_ = v_a_2612_;
goto _start;
}
case 2:
{
lean_object* v_a_2614_; lean_object* v_a_2615_; 
v_a_2614_ = lean_ctor_get(v_u_2605_, 0);
lean_inc(v_a_2614_);
v_a_2615_ = lean_ctor_get(v_u_2605_, 1);
lean_inc(v_a_2615_);
lean_dec_ref_known(v_u_2605_, 2);
v_u_2608_ = v_a_2614_;
v_v_2609_ = v_a_2615_;
goto v___jp_2607_;
}
case 3:
{
lean_object* v_a_2616_; lean_object* v_a_2617_; 
v_a_2616_ = lean_ctor_get(v_u_2605_, 0);
lean_inc(v_a_2616_);
v_a_2617_ = lean_ctor_get(v_u_2605_, 1);
lean_inc(v_a_2617_);
lean_dec_ref_known(v_u_2605_, 2);
v_u_2608_ = v_a_2616_;
v_v_2609_ = v_a_2617_;
goto v___jp_2607_;
}
case 5:
{
lean_object* v_a_2618_; uint8_t v___x_2619_; 
v_a_2618_ = lean_ctor_get(v_u_2605_, 0);
lean_inc(v_a_2618_);
lean_dec_ref_known(v_u_2605_, 1);
v___x_2619_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Level_collectMVars_spec__0___redArg(v_a_2618_, v_s_2606_);
if (v___x_2619_ == 0)
{
lean_object* v___x_2620_; lean_object* v___x_2621_; 
v___x_2620_ = lean_box(0);
v___x_2621_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Level_collectMVars_spec__1___redArg(v_a_2618_, v___x_2620_, v_s_2606_);
return v___x_2621_;
}
else
{
lean_dec(v_a_2618_);
return v_s_2606_;
}
}
default: 
{
lean_dec(v_u_2605_);
return v_s_2606_;
}
}
v___jp_2607_:
{
lean_object* v___x_2610_; 
v___x_2610_ = l_Lean_Level_collectMVars(v_v_2609_, v_s_2606_);
v_u_2605_ = v_u_2608_;
v_s_2606_ = v___x_2610_;
goto _start;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Level_collectMVars_spec__0(lean_object* v_00_u03b2_2622_, lean_object* v_k_2623_, lean_object* v_t_2624_){
_start:
{
uint8_t v___x_2625_; 
v___x_2625_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Level_collectMVars_spec__0___redArg(v_k_2623_, v_t_2624_);
return v___x_2625_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Level_collectMVars_spec__0___boxed(lean_object* v_00_u03b2_2626_, lean_object* v_k_2627_, lean_object* v_t_2628_){
_start:
{
uint8_t v_res_2629_; lean_object* v_r_2630_; 
v_res_2629_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Level_collectMVars_spec__0(v_00_u03b2_2626_, v_k_2627_, v_t_2628_);
lean_dec(v_t_2628_);
lean_dec(v_k_2627_);
v_r_2630_ = lean_box(v_res_2629_);
return v_r_2630_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Level_collectMVars_spec__1(lean_object* v_00_u03b2_2631_, lean_object* v_k_2632_, lean_object* v_v_2633_, lean_object* v_t_2634_, lean_object* v_hl_2635_){
_start:
{
lean_object* v___x_2636_; 
v___x_2636_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Level_collectMVars_spec__1___redArg(v_k_2632_, v_v_2633_, v_t_2634_);
return v___x_2636_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_find_x3f_visit(lean_object* v_p_2637_, lean_object* v_u_2638_){
_start:
{
lean_object* v_u_2640_; lean_object* v_v_2641_; lean_object* v___x_2644_; uint8_t v___x_2645_; 
lean_inc_ref(v_p_2637_);
lean_inc(v_u_2638_);
v___x_2644_ = lean_apply_1(v_p_2637_, v_u_2638_);
v___x_2645_ = lean_unbox(v___x_2644_);
if (v___x_2645_ == 0)
{
switch(lean_obj_tag(v_u_2638_))
{
case 1:
{
lean_object* v_a_2646_; 
v_a_2646_ = lean_ctor_get(v_u_2638_, 0);
lean_inc(v_a_2646_);
lean_dec_ref_known(v_u_2638_, 1);
v_u_2638_ = v_a_2646_;
goto _start;
}
case 2:
{
lean_object* v_a_2648_; lean_object* v_a_2649_; 
v_a_2648_ = lean_ctor_get(v_u_2638_, 0);
lean_inc(v_a_2648_);
v_a_2649_ = lean_ctor_get(v_u_2638_, 1);
lean_inc(v_a_2649_);
lean_dec_ref_known(v_u_2638_, 2);
v_u_2640_ = v_a_2648_;
v_v_2641_ = v_a_2649_;
goto v___jp_2639_;
}
case 3:
{
lean_object* v_a_2650_; lean_object* v_a_2651_; 
v_a_2650_ = lean_ctor_get(v_u_2638_, 0);
lean_inc(v_a_2650_);
v_a_2651_ = lean_ctor_get(v_u_2638_, 1);
lean_inc(v_a_2651_);
lean_dec_ref_known(v_u_2638_, 2);
v_u_2640_ = v_a_2650_;
v_v_2641_ = v_a_2651_;
goto v___jp_2639_;
}
default: 
{
lean_object* v___x_2652_; 
lean_dec(v_u_2638_);
lean_dec_ref(v_p_2637_);
v___x_2652_ = lean_box(0);
return v___x_2652_;
}
}
}
else
{
lean_object* v___x_2653_; 
lean_dec_ref(v_p_2637_);
v___x_2653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2653_, 0, v_u_2638_);
return v___x_2653_;
}
v___jp_2639_:
{
lean_object* v___x_2642_; 
lean_inc_ref(v_p_2637_);
v___x_2642_ = l___private_Lean_Level_0__Lean_Level_find_x3f_visit(v_p_2637_, v_u_2640_);
if (lean_obj_tag(v___x_2642_) == 0)
{
v_u_2638_ = v_v_2641_;
goto _start;
}
else
{
lean_dec(v_v_2641_);
lean_dec_ref(v_p_2637_);
return v___x_2642_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_find_x3f(lean_object* v_u_2654_, lean_object* v_p_2655_){
_start:
{
lean_object* v___x_2656_; 
v___x_2656_ = l___private_Lean_Level_0__Lean_Level_find_x3f_visit(v_p_2655_, v_u_2654_);
return v___x_2656_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_any(lean_object* v_u_2657_, lean_object* v_p_2658_){
_start:
{
lean_object* v___x_2659_; 
v___x_2659_ = l___private_Lean_Level_0__Lean_Level_find_x3f_visit(v_p_2658_, v_u_2657_);
if (lean_obj_tag(v___x_2659_) == 0)
{
uint8_t v___x_2660_; 
v___x_2660_ = 0;
return v___x_2660_;
}
else
{
uint8_t v___x_2661_; 
lean_dec_ref_known(v___x_2659_, 1);
v___x_2661_ = 1;
return v___x_2661_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_any___boxed(lean_object* v_u_2662_, lean_object* v_p_2663_){
_start:
{
uint8_t v_res_2664_; lean_object* v_r_2665_; 
v_res_2664_ = l_Lean_Level_any(v_u_2662_, v_p_2663_);
v_r_2665_ = lean_box(v_res_2664_);
return v_r_2665_;
}
}
LEAN_EXPORT lean_object* l_Lean_Nat_toLevel(lean_object* v_n_2666_){
_start:
{
lean_object* v___x_2667_; 
v___x_2667_ = l_Lean_Level_ofNat(v_n_2666_);
return v___x_2667_;
}
}
LEAN_EXPORT lean_object* l_Lean_Nat_toLevel___boxed(lean_object* v_n_2668_){
_start:
{
lean_object* v_res_2669_; 
v_res_2669_ = l_Lean_Nat_toLevel(v_n_2668_);
lean_dec(v_n_2668_);
return v_res_2669_;
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
