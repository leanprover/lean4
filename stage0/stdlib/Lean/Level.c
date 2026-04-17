// Lean compiler output
// Module: Lean.Level
// Imports: public import Init.Data.Array.QSort public import Lean.Data.PersistentHashSet public import Lean.Hygiene public import Init.Data.Option.Coe import Init.Data.Nat.Linear
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
lean_object* lean_mk_syntax_ident(lean_object*);
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
LEAN_EXPORT lean_object* l_Nat_imax(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_imax___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Nat_toLevel(lean_object*);
LEAN_EXPORT lean_object* l_Nat_toLevel___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Nat_imax(lean_object* v_n_1_, lean_object* v_m_2_){
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
LEAN_EXPORT lean_object* l_Nat_imax___boxed(lean_object* v_n_6_, lean_object* v_m_7_){
_start:
{
lean_object* v_res_8_; 
v_res_8_ = l_Nat_imax(v_n_6_, v_m_7_);
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
lean_object* v_r_73_; lean_object* v___y_77_; lean_object* v___y_78_; lean_object* v_r_83_; lean_object* v___y_90_; lean_object* v___y_91_; lean_object* v_r_96_; lean_object* v___x_102_; uint64_t v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v_r_106_; uint32_t v___x_107_; uint32_t v___x_108_; uint8_t v___x_109_; 
v___x_102_ = ((lean_object*)(l_Lean_instReprData___lam__0___closed__5));
v___x_103_ = l_Lean_Level_Data_hash(v_v_70_);
v___x_104_ = lean_uint64_to_nat(v___x_103_);
v___x_105_ = l_Nat_reprFast(v___x_104_);
v_r_106_ = lean_string_append(v___x_102_, v___x_105_);
lean_dec_ref(v___x_105_);
v___x_107_ = l_Lean_Level_Data_depth(v_v_70_);
v___x_108_ = 0;
v___x_109_ = lean_uint32_dec_eq(v___x_107_, v___x_108_);
if (v___x_109_ == 0)
{
lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v_r_116_; 
v___x_110_ = ((lean_object*)(l_Lean_instReprData___lam__0___closed__6));
v___x_111_ = lean_string_append(v_r_106_, v___x_110_);
v___x_112_ = lean_uint32_to_nat(v___x_107_);
v___x_113_ = l_Nat_reprFast(v___x_112_);
v___x_114_ = lean_string_append(v___x_111_, v___x_113_);
lean_dec_ref(v___x_113_);
v___x_115_ = ((lean_object*)(l_Lean_instReprData___lam__0___closed__0));
v_r_116_ = lean_string_append(v___x_114_, v___x_115_);
v_r_96_ = v_r_116_;
goto v___jp_95_;
}
else
{
v_r_96_ = v_r_106_;
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
LEAN_EXPORT lean_object* l_Lean_instReprData___lam__0___boxed(lean_object* v_v_117_, lean_object* v_prec_118_){
_start:
{
uint64_t v_v_boxed_119_; lean_object* v_res_120_; 
v_v_boxed_119_ = lean_unbox_uint64(v_v_117_);
lean_dec_ref(v_v_117_);
v_res_120_ = l_Lean_instReprData___lam__0(v_v_boxed_119_, v_prec_118_);
lean_dec(v_prec_118_);
return v_res_120_;
}
}
static lean_object* _init_l_Lean_instInhabitedLevelMVarId_default(void){
_start:
{
lean_object* v___x_123_; 
v___x_123_ = lean_box(0);
return v___x_123_;
}
}
static lean_object* _init_l_Lean_instInhabitedLevelMVarId(void){
_start:
{
lean_object* v___x_124_; 
v___x_124_ = lean_box(0);
return v___x_124_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqLevelMVarId_beq(lean_object* v_x_125_, lean_object* v_x_126_){
_start:
{
uint8_t v___x_127_; 
v___x_127_ = lean_name_eq(v_x_125_, v_x_126_);
return v___x_127_;
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqLevelMVarId_beq___boxed(lean_object* v_x_128_, lean_object* v_x_129_){
_start:
{
uint8_t v_res_130_; lean_object* v_r_131_; 
v_res_130_ = l_Lean_instBEqLevelMVarId_beq(v_x_128_, v_x_129_);
lean_dec(v_x_129_);
lean_dec(v_x_128_);
v_r_131_ = lean_box(v_res_130_);
return v_r_131_;
}
}
static uint64_t _init_l_Lean_instHashableLevelMVarId_hash___closed__0(void){
_start:
{
lean_object* v___x_134_; uint64_t v___x_135_; 
v___x_134_ = lean_unsigned_to_nat(1723u);
v___x_135_ = lean_uint64_of_nat(v___x_134_);
return v___x_135_;
}
}
static uint64_t _init_l_Lean_instHashableLevelMVarId_hash___closed__1(void){
_start:
{
uint64_t v___x_136_; uint64_t v___x_137_; uint64_t v___x_138_; 
v___x_136_ = lean_uint64_once(&l_Lean_instHashableLevelMVarId_hash___closed__0, &l_Lean_instHashableLevelMVarId_hash___closed__0_once, _init_l_Lean_instHashableLevelMVarId_hash___closed__0);
v___x_137_ = 0ULL;
v___x_138_ = lean_uint64_mix_hash(v___x_137_, v___x_136_);
return v___x_138_;
}
}
LEAN_EXPORT uint64_t l_Lean_instHashableLevelMVarId_hash(lean_object* v_x_139_){
_start:
{
uint64_t v___x_140_; 
v___x_140_ = 0ULL;
if (lean_obj_tag(v_x_139_) == 0)
{
uint64_t v___x_141_; 
v___x_141_ = lean_uint64_once(&l_Lean_instHashableLevelMVarId_hash___closed__1, &l_Lean_instHashableLevelMVarId_hash___closed__1_once, _init_l_Lean_instHashableLevelMVarId_hash___closed__1);
return v___x_141_;
}
else
{
uint64_t v_hash_142_; uint64_t v___x_143_; 
v_hash_142_ = lean_ctor_get_uint64(v_x_139_, sizeof(void*)*2);
v___x_143_ = lean_uint64_mix_hash(v___x_140_, v_hash_142_);
return v___x_143_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instHashableLevelMVarId_hash___boxed(lean_object* v_x_144_){
_start:
{
uint64_t v_res_145_; lean_object* v_r_146_; 
v_res_145_ = l_Lean_instHashableLevelMVarId_hash(v_x_144_);
lean_dec(v_x_144_);
v_r_146_ = lean_box_uint64(v_res_145_);
return v_r_146_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_instReprLevelMVarId_repr_spec__0(lean_object* v_a_149_){
_start:
{
lean_object* v___x_150_; 
v___x_150_ = lean_nat_to_int(v_a_149_);
return v___x_150_;
}
}
static lean_object* _init_l_Lean_instReprLevelMVarId_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_164_; lean_object* v___x_165_; 
v___x_164_ = lean_unsigned_to_nat(8u);
v___x_165_ = lean_nat_to_int(v___x_164_);
return v___x_165_;
}
}
static lean_object* _init_l_Lean_instReprLevelMVarId_repr___redArg___closed__9(void){
_start:
{
lean_object* v___x_167_; lean_object* v___x_168_; 
v___x_167_ = ((lean_object*)(l_Lean_instReprLevelMVarId_repr___redArg___closed__0));
v___x_168_ = lean_string_length(v___x_167_);
return v___x_168_;
}
}
static lean_object* _init_l_Lean_instReprLevelMVarId_repr___redArg___closed__10(void){
_start:
{
lean_object* v___x_169_; lean_object* v___x_170_; 
v___x_169_ = lean_obj_once(&l_Lean_instReprLevelMVarId_repr___redArg___closed__9, &l_Lean_instReprLevelMVarId_repr___redArg___closed__9_once, _init_l_Lean_instReprLevelMVarId_repr___redArg___closed__9);
v___x_170_ = lean_nat_to_int(v___x_169_);
return v___x_170_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprLevelMVarId_repr___redArg(lean_object* v_x_175_){
_start:
{
lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; uint8_t v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; 
v___x_176_ = ((lean_object*)(l_Lean_instReprLevelMVarId_repr___redArg___closed__6));
v___x_177_ = lean_obj_once(&l_Lean_instReprLevelMVarId_repr___redArg___closed__7, &l_Lean_instReprLevelMVarId_repr___redArg___closed__7_once, _init_l_Lean_instReprLevelMVarId_repr___redArg___closed__7);
v___x_178_ = lean_unsigned_to_nat(0u);
v___x_179_ = l_Lean_Name_reprPrec(v_x_175_, v___x_178_);
v___x_180_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_180_, 0, v___x_177_);
lean_ctor_set(v___x_180_, 1, v___x_179_);
v___x_181_ = 0;
v___x_182_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_182_, 0, v___x_180_);
lean_ctor_set_uint8(v___x_182_, sizeof(void*)*1, v___x_181_);
v___x_183_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_183_, 0, v___x_176_);
lean_ctor_set(v___x_183_, 1, v___x_182_);
v___x_184_ = lean_obj_once(&l_Lean_instReprLevelMVarId_repr___redArg___closed__10, &l_Lean_instReprLevelMVarId_repr___redArg___closed__10_once, _init_l_Lean_instReprLevelMVarId_repr___redArg___closed__10);
v___x_185_ = ((lean_object*)(l_Lean_instReprLevelMVarId_repr___redArg___closed__11));
v___x_186_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_186_, 0, v___x_185_);
lean_ctor_set(v___x_186_, 1, v___x_183_);
v___x_187_ = ((lean_object*)(l_Lean_instReprLevelMVarId_repr___redArg___closed__12));
v___x_188_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_188_, 0, v___x_186_);
lean_ctor_set(v___x_188_, 1, v___x_187_);
v___x_189_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_189_, 0, v___x_184_);
lean_ctor_set(v___x_189_, 1, v___x_188_);
v___x_190_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_190_, 0, v___x_189_);
lean_ctor_set_uint8(v___x_190_, sizeof(void*)*1, v___x_181_);
return v___x_190_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprLevelMVarId_repr(lean_object* v_x_191_, lean_object* v_prec_192_){
_start:
{
lean_object* v___x_193_; 
v___x_193_ = l_Lean_instReprLevelMVarId_repr___redArg(v_x_191_);
return v___x_193_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprLevelMVarId_repr___boxed(lean_object* v_x_194_, lean_object* v_prec_195_){
_start:
{
lean_object* v_res_196_; 
v_res_196_ = l_Lean_instReprLevelMVarId_repr(v_x_194_, v_prec_195_);
lean_dec(v_prec_195_);
return v_res_196_;
}
}
static lean_object* _init_l_Lean_instInhabitedLMVarIdSet___aux__1(void){
_start:
{
lean_object* v___x_201_; 
v___x_201_ = lean_box(1);
return v___x_201_;
}
}
static lean_object* _init_l_Lean_instInhabitedLMVarIdSet(void){
_start:
{
lean_object* v___x_202_; 
v___x_202_ = lean_box(1);
return v___x_202_;
}
}
static lean_object* _init_l_Lean_instEmptyCollectionLMVarIdSet___aux__1(void){
_start:
{
lean_object* v___x_203_; 
v___x_203_ = lean_box(1);
return v___x_203_;
}
}
static lean_object* _init_l_Lean_instEmptyCollectionLMVarIdSet(void){
_start:
{
lean_object* v___x_204_; 
v___x_204_ = lean_box(1);
return v___x_204_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInLMVarIdSetLMVarIdOfMonad___aux__1___redArg___lam__0(lean_object* v_f_205_, lean_object* v_a_206_, lean_object* v_b_207_, lean_object* v_c_208_){
_start:
{
lean_object* v___x_209_; 
v___x_209_ = lean_apply_2(v_f_205_, v_a_206_, v_c_208_);
return v___x_209_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInLMVarIdSetLMVarIdOfMonad___aux__1___redArg___lam__1(lean_object* v_toPure_210_, lean_object* v_____do__lift_211_){
_start:
{
lean_object* v_a_212_; lean_object* v___x_213_; 
v_a_212_ = lean_ctor_get(v_____do__lift_211_, 0);
lean_inc(v_a_212_);
lean_dec_ref(v_____do__lift_211_);
v___x_213_ = lean_apply_2(v_toPure_210_, lean_box(0), v_a_212_);
return v___x_213_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInLMVarIdSetLMVarIdOfMonad___aux__1___redArg(lean_object* v_inst_214_, lean_object* v_m_215_, lean_object* v_init_216_, lean_object* v_f_217_){
_start:
{
lean_object* v_toApplicative_218_; lean_object* v_toBind_219_; lean_object* v_toPure_220_; lean_object* v___f_221_; lean_object* v___x_222_; lean_object* v___f_223_; lean_object* v___x_224_; 
v_toApplicative_218_ = lean_ctor_get(v_inst_214_, 0);
v_toBind_219_ = lean_ctor_get(v_inst_214_, 1);
lean_inc(v_toBind_219_);
v_toPure_220_ = lean_ctor_get(v_toApplicative_218_, 1);
lean_inc(v_toPure_220_);
v___f_221_ = lean_alloc_closure((void*)(l_Lean_instForInLMVarIdSetLMVarIdOfMonad___aux__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_221_, 0, v_f_217_);
v___x_222_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_214_, v___f_221_, v_init_216_, v_m_215_);
v___f_223_ = lean_alloc_closure((void*)(l_Lean_instForInLMVarIdSetLMVarIdOfMonad___aux__1___redArg___lam__1), 2, 1);
lean_closure_set(v___f_223_, 0, v_toPure_220_);
v___x_224_ = lean_apply_4(v_toBind_219_, lean_box(0), lean_box(0), v___x_222_, v___f_223_);
return v___x_224_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInLMVarIdSetLMVarIdOfMonad___aux__1(lean_object* v_m_225_, lean_object* v_inst_226_, lean_object* v_00_u03b2_227_, lean_object* v_m_228_, lean_object* v_init_229_, lean_object* v_f_230_){
_start:
{
lean_object* v_toApplicative_231_; lean_object* v_toBind_232_; lean_object* v_toPure_233_; lean_object* v___f_234_; lean_object* v___x_235_; lean_object* v___f_236_; lean_object* v___x_237_; 
v_toApplicative_231_ = lean_ctor_get(v_inst_226_, 0);
v_toBind_232_ = lean_ctor_get(v_inst_226_, 1);
lean_inc(v_toBind_232_);
v_toPure_233_ = lean_ctor_get(v_toApplicative_231_, 1);
lean_inc(v_toPure_233_);
v___f_234_ = lean_alloc_closure((void*)(l_Lean_instForInLMVarIdSetLMVarIdOfMonad___aux__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_234_, 0, v_f_230_);
v___x_235_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_226_, v___f_234_, v_init_229_, v_m_228_);
v___f_236_ = lean_alloc_closure((void*)(l_Lean_instForInLMVarIdSetLMVarIdOfMonad___aux__1___redArg___lam__1), 2, 1);
lean_closure_set(v___f_236_, 0, v_toPure_233_);
v___x_237_ = lean_apply_4(v_toBind_232_, lean_box(0), lean_box(0), v___x_235_, v___f_236_);
return v___x_237_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInLMVarIdSetLMVarIdOfMonad___redArg(lean_object* v_inst_238_){
_start:
{
lean_object* v___x_239_; 
v___x_239_ = lean_alloc_closure((void*)(l_Lean_instForInLMVarIdSetLMVarIdOfMonad___aux__1), 6, 2);
lean_closure_set(v___x_239_, 0, lean_box(0));
lean_closure_set(v___x_239_, 1, v_inst_238_);
return v___x_239_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInLMVarIdSetLMVarIdOfMonad(lean_object* v_m_240_, lean_object* v_inst_241_){
_start:
{
lean_object* v___x_242_; 
v___x_242_ = lean_alloc_closure((void*)(l_Lean_instForInLMVarIdSetLMVarIdOfMonad___aux__1), 6, 2);
lean_closure_set(v___x_242_, 0, lean_box(0));
lean_closure_set(v___x_242_, 1, v_inst_241_);
return v___x_242_;
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
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionLMVarIdMap(lean_object* v_00_u03b1_245_){
_start:
{
lean_object* v___x_246_; 
v___x_246_ = lean_box(1);
return v___x_246_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInLMVarIdMapProdLMVarIdOfMonad___aux__1___redArg___lam__0(lean_object* v_f_247_, lean_object* v_a_248_, lean_object* v_b_249_, lean_object* v_c_250_){
_start:
{
lean_object* v___x_251_; lean_object* v___x_252_; 
v___x_251_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_251_, 0, v_a_248_);
lean_ctor_set(v___x_251_, 1, v_b_249_);
v___x_252_ = lean_apply_2(v_f_247_, v___x_251_, v_c_250_);
return v___x_252_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInLMVarIdMapProdLMVarIdOfMonad___aux__1___redArg(lean_object* v_inst_253_, lean_object* v_m_254_, lean_object* v_init_255_, lean_object* v_f_256_){
_start:
{
lean_object* v_toApplicative_257_; lean_object* v_toBind_258_; lean_object* v_toPure_259_; lean_object* v___f_260_; lean_object* v___x_261_; lean_object* v___f_262_; lean_object* v___x_263_; 
v_toApplicative_257_ = lean_ctor_get(v_inst_253_, 0);
v_toBind_258_ = lean_ctor_get(v_inst_253_, 1);
lean_inc(v_toBind_258_);
v_toPure_259_ = lean_ctor_get(v_toApplicative_257_, 1);
lean_inc(v_toPure_259_);
v___f_260_ = lean_alloc_closure((void*)(l_Lean_instForInLMVarIdMapProdLMVarIdOfMonad___aux__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_260_, 0, v_f_256_);
v___x_261_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_253_, v___f_260_, v_init_255_, v_m_254_);
v___f_262_ = lean_alloc_closure((void*)(l_Lean_instForInLMVarIdSetLMVarIdOfMonad___aux__1___redArg___lam__1), 2, 1);
lean_closure_set(v___f_262_, 0, v_toPure_259_);
v___x_263_ = lean_apply_4(v_toBind_258_, lean_box(0), lean_box(0), v___x_261_, v___f_262_);
return v___x_263_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInLMVarIdMapProdLMVarIdOfMonad___aux__1(lean_object* v_m_264_, lean_object* v_00_u03b1_265_, lean_object* v_inst_266_, lean_object* v_00_u03b2_267_, lean_object* v_m_268_, lean_object* v_init_269_, lean_object* v_f_270_){
_start:
{
lean_object* v_toApplicative_271_; lean_object* v_toBind_272_; lean_object* v_toPure_273_; lean_object* v___f_274_; lean_object* v___x_275_; lean_object* v___f_276_; lean_object* v___x_277_; 
v_toApplicative_271_ = lean_ctor_get(v_inst_266_, 0);
v_toBind_272_ = lean_ctor_get(v_inst_266_, 1);
lean_inc(v_toBind_272_);
v_toPure_273_ = lean_ctor_get(v_toApplicative_271_, 1);
lean_inc(v_toPure_273_);
v___f_274_ = lean_alloc_closure((void*)(l_Lean_instForInLMVarIdMapProdLMVarIdOfMonad___aux__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_274_, 0, v_f_270_);
v___x_275_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_266_, v___f_274_, v_init_269_, v_m_268_);
v___f_276_ = lean_alloc_closure((void*)(l_Lean_instForInLMVarIdSetLMVarIdOfMonad___aux__1___redArg___lam__1), 2, 1);
lean_closure_set(v___f_276_, 0, v_toPure_273_);
v___x_277_ = lean_apply_4(v_toBind_272_, lean_box(0), lean_box(0), v___x_275_, v___f_276_);
return v___x_277_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInLMVarIdMapProdLMVarIdOfMonad___redArg(lean_object* v_inst_278_){
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
LEAN_EXPORT lean_object* l_Lean_instForInLMVarIdMapProdLMVarIdOfMonad(lean_object* v_m_280_, lean_object* v_00_u03b1_281_, lean_object* v_inst_282_){
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
LEAN_EXPORT lean_object* l_Lean_instInhabitedLMVarIdMap(lean_object* v_00_u03b1_284_){
_start:
{
lean_object* v___x_285_; 
v___x_285_ = lean_box(1);
return v___x_285_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_ctorIdx(lean_object* v_x_286_){
_start:
{
switch(lean_obj_tag(v_x_286_))
{
case 0:
{
lean_object* v___x_287_; 
v___x_287_ = lean_unsigned_to_nat(0u);
return v___x_287_;
}
case 1:
{
lean_object* v___x_288_; 
v___x_288_ = lean_unsigned_to_nat(1u);
return v___x_288_;
}
case 2:
{
lean_object* v___x_289_; 
v___x_289_ = lean_unsigned_to_nat(2u);
return v___x_289_;
}
case 3:
{
lean_object* v___x_290_; 
v___x_290_ = lean_unsigned_to_nat(3u);
return v___x_290_;
}
case 4:
{
lean_object* v___x_291_; 
v___x_291_ = lean_unsigned_to_nat(4u);
return v___x_291_;
}
default: 
{
lean_object* v___x_292_; 
v___x_292_ = lean_unsigned_to_nat(5u);
return v___x_292_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_ctorIdx___boxed(lean_object* v_x_293_){
_start:
{
lean_object* v_res_294_; 
v_res_294_ = l_Lean_Level_ctorIdx(v_x_293_);
lean_dec(v_x_293_);
return v_res_294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_ctorElim___redArg(lean_object* v_t_295_, lean_object* v_k_296_){
_start:
{
switch(lean_obj_tag(v_t_295_))
{
case 0:
{
return v_k_296_;
}
case 2:
{
lean_object* v_a_297_; lean_object* v_a_298_; lean_object* v___x_299_; 
v_a_297_ = lean_ctor_get(v_t_295_, 0);
lean_inc(v_a_297_);
v_a_298_ = lean_ctor_get(v_t_295_, 1);
lean_inc(v_a_298_);
lean_dec_ref(v_t_295_);
v___x_299_ = lean_apply_2(v_k_296_, v_a_297_, v_a_298_);
return v___x_299_;
}
case 3:
{
lean_object* v_a_300_; lean_object* v_a_301_; lean_object* v___x_302_; 
v_a_300_ = lean_ctor_get(v_t_295_, 0);
lean_inc(v_a_300_);
v_a_301_ = lean_ctor_get(v_t_295_, 1);
lean_inc(v_a_301_);
lean_dec_ref(v_t_295_);
v___x_302_ = lean_apply_2(v_k_296_, v_a_300_, v_a_301_);
return v___x_302_;
}
default: 
{
lean_object* v_a_303_; lean_object* v___x_304_; 
v_a_303_ = lean_ctor_get(v_t_295_, 0);
lean_inc(v_a_303_);
lean_dec(v_t_295_);
v___x_304_ = lean_apply_1(v_k_296_, v_a_303_);
return v___x_304_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_ctorElim(lean_object* v_motive_305_, lean_object* v_ctorIdx_306_, lean_object* v_t_307_, lean_object* v_h_308_, lean_object* v_k_309_){
_start:
{
lean_object* v___x_310_; 
v___x_310_ = l_Lean_Level_ctorElim___redArg(v_t_307_, v_k_309_);
return v___x_310_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_ctorElim___boxed(lean_object* v_motive_311_, lean_object* v_ctorIdx_312_, lean_object* v_t_313_, lean_object* v_h_314_, lean_object* v_k_315_){
_start:
{
lean_object* v_res_316_; 
v_res_316_ = l_Lean_Level_ctorElim(v_motive_311_, v_ctorIdx_312_, v_t_313_, v_h_314_, v_k_315_);
lean_dec(v_ctorIdx_312_);
return v_res_316_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_zero_elim___redArg(lean_object* v_t_317_, lean_object* v_zero_318_){
_start:
{
lean_object* v___x_319_; 
v___x_319_ = l_Lean_Level_ctorElim___redArg(v_t_317_, v_zero_318_);
return v___x_319_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_zero_elim(lean_object* v_motive_320_, lean_object* v_t_321_, lean_object* v_h_322_, lean_object* v_zero_323_){
_start:
{
lean_object* v___x_324_; 
v___x_324_ = l_Lean_Level_ctorElim___redArg(v_t_321_, v_zero_323_);
return v___x_324_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_succ_elim___redArg(lean_object* v_t_325_, lean_object* v_succ_326_){
_start:
{
lean_object* v___x_327_; 
v___x_327_ = l_Lean_Level_ctorElim___redArg(v_t_325_, v_succ_326_);
return v___x_327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_succ_elim(lean_object* v_motive_328_, lean_object* v_t_329_, lean_object* v_h_330_, lean_object* v_succ_331_){
_start:
{
lean_object* v___x_332_; 
v___x_332_ = l_Lean_Level_ctorElim___redArg(v_t_329_, v_succ_331_);
return v___x_332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_max_elim___redArg(lean_object* v_t_333_, lean_object* v_max_334_){
_start:
{
lean_object* v___x_335_; 
v___x_335_ = l_Lean_Level_ctorElim___redArg(v_t_333_, v_max_334_);
return v___x_335_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_max_elim(lean_object* v_motive_336_, lean_object* v_t_337_, lean_object* v_h_338_, lean_object* v_max_339_){
_start:
{
lean_object* v___x_340_; 
v___x_340_ = l_Lean_Level_ctorElim___redArg(v_t_337_, v_max_339_);
return v___x_340_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_imax_elim___redArg(lean_object* v_t_341_, lean_object* v_imax_342_){
_start:
{
lean_object* v___x_343_; 
v___x_343_ = l_Lean_Level_ctorElim___redArg(v_t_341_, v_imax_342_);
return v___x_343_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_imax_elim(lean_object* v_motive_344_, lean_object* v_t_345_, lean_object* v_h_346_, lean_object* v_imax_347_){
_start:
{
lean_object* v___x_348_; 
v___x_348_ = l_Lean_Level_ctorElim___redArg(v_t_345_, v_imax_347_);
return v___x_348_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_param_elim___redArg(lean_object* v_t_349_, lean_object* v_param_350_){
_start:
{
lean_object* v___x_351_; 
v___x_351_ = l_Lean_Level_ctorElim___redArg(v_t_349_, v_param_350_);
return v___x_351_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_param_elim(lean_object* v_motive_352_, lean_object* v_t_353_, lean_object* v_h_354_, lean_object* v_param_355_){
_start:
{
lean_object* v___x_356_; 
v___x_356_ = l_Lean_Level_ctorElim___redArg(v_t_353_, v_param_355_);
return v___x_356_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_mvar_elim___redArg(lean_object* v_t_357_, lean_object* v_mvar_358_){
_start:
{
lean_object* v___x_359_; 
v___x_359_ = l_Lean_Level_ctorElim___redArg(v_t_357_, v_mvar_358_);
return v___x_359_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_mvar_elim(lean_object* v_motive_360_, lean_object* v_t_361_, lean_object* v_h_362_, lean_object* v_mvar_363_){
_start:
{
lean_object* v___x_364_; 
v___x_364_ = l_Lean_Level_ctorElim___redArg(v_t_361_, v_mvar_363_);
return v___x_364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_casesOn___override___redArg(lean_object* v_t_365_, lean_object* v_zero_366_, lean_object* v_succ_367_, lean_object* v_max_368_, lean_object* v_imax_369_, lean_object* v_param_370_, lean_object* v_mvar_371_){
_start:
{
switch(lean_obj_tag(v_t_365_))
{
case 0:
{
lean_dec(v_mvar_371_);
lean_dec(v_param_370_);
lean_dec(v_imax_369_);
lean_dec(v_max_368_);
lean_dec(v_succ_367_);
lean_inc(v_zero_366_);
return v_zero_366_;
}
case 1:
{
lean_object* v_a_372_; lean_object* v___x_373_; 
lean_dec(v_mvar_371_);
lean_dec(v_param_370_);
lean_dec(v_imax_369_);
lean_dec(v_max_368_);
v_a_372_ = lean_ctor_get(v_t_365_, 0);
lean_inc(v_a_372_);
lean_dec_ref(v_t_365_);
v___x_373_ = lean_apply_1(v_succ_367_, v_a_372_);
return v___x_373_;
}
case 2:
{
lean_object* v_a_374_; lean_object* v_a_375_; lean_object* v___x_376_; 
lean_dec(v_mvar_371_);
lean_dec(v_param_370_);
lean_dec(v_imax_369_);
lean_dec(v_succ_367_);
v_a_374_ = lean_ctor_get(v_t_365_, 0);
lean_inc(v_a_374_);
v_a_375_ = lean_ctor_get(v_t_365_, 1);
lean_inc(v_a_375_);
lean_dec_ref(v_t_365_);
v___x_376_ = lean_apply_2(v_max_368_, v_a_374_, v_a_375_);
return v___x_376_;
}
case 3:
{
lean_object* v_a_377_; lean_object* v_a_378_; lean_object* v___x_379_; 
lean_dec(v_mvar_371_);
lean_dec(v_param_370_);
lean_dec(v_max_368_);
lean_dec(v_succ_367_);
v_a_377_ = lean_ctor_get(v_t_365_, 0);
lean_inc(v_a_377_);
v_a_378_ = lean_ctor_get(v_t_365_, 1);
lean_inc(v_a_378_);
lean_dec_ref(v_t_365_);
v___x_379_ = lean_apply_2(v_imax_369_, v_a_377_, v_a_378_);
return v___x_379_;
}
case 4:
{
lean_object* v_a_380_; lean_object* v___x_381_; 
lean_dec(v_mvar_371_);
lean_dec(v_imax_369_);
lean_dec(v_max_368_);
lean_dec(v_succ_367_);
v_a_380_ = lean_ctor_get(v_t_365_, 0);
lean_inc(v_a_380_);
lean_dec_ref(v_t_365_);
v___x_381_ = lean_apply_1(v_param_370_, v_a_380_);
return v___x_381_;
}
default: 
{
lean_object* v_a_382_; lean_object* v___x_383_; 
lean_dec(v_param_370_);
lean_dec(v_imax_369_);
lean_dec(v_max_368_);
lean_dec(v_succ_367_);
v_a_382_ = lean_ctor_get(v_t_365_, 0);
lean_inc(v_a_382_);
lean_dec_ref(v_t_365_);
v___x_383_ = lean_apply_1(v_mvar_371_, v_a_382_);
return v___x_383_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_casesOn___override___redArg___boxed(lean_object* v_t_384_, lean_object* v_zero_385_, lean_object* v_succ_386_, lean_object* v_max_387_, lean_object* v_imax_388_, lean_object* v_param_389_, lean_object* v_mvar_390_){
_start:
{
lean_object* v_res_391_; 
v_res_391_ = l_Lean_Level_casesOn___override___redArg(v_t_384_, v_zero_385_, v_succ_386_, v_max_387_, v_imax_388_, v_param_389_, v_mvar_390_);
lean_dec(v_zero_385_);
return v_res_391_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_casesOn___override(lean_object* v_motive_392_, lean_object* v_t_393_, lean_object* v_zero_394_, lean_object* v_succ_395_, lean_object* v_max_396_, lean_object* v_imax_397_, lean_object* v_param_398_, lean_object* v_mvar_399_){
_start:
{
switch(lean_obj_tag(v_t_393_))
{
case 0:
{
lean_dec(v_mvar_399_);
lean_dec(v_param_398_);
lean_dec(v_imax_397_);
lean_dec(v_max_396_);
lean_dec(v_succ_395_);
lean_inc(v_zero_394_);
return v_zero_394_;
}
case 1:
{
lean_object* v_a_400_; lean_object* v___x_401_; 
lean_dec(v_mvar_399_);
lean_dec(v_param_398_);
lean_dec(v_imax_397_);
lean_dec(v_max_396_);
v_a_400_ = lean_ctor_get(v_t_393_, 0);
lean_inc(v_a_400_);
lean_dec_ref(v_t_393_);
v___x_401_ = lean_apply_1(v_succ_395_, v_a_400_);
return v___x_401_;
}
case 2:
{
lean_object* v_a_402_; lean_object* v_a_403_; lean_object* v___x_404_; 
lean_dec(v_mvar_399_);
lean_dec(v_param_398_);
lean_dec(v_imax_397_);
lean_dec(v_succ_395_);
v_a_402_ = lean_ctor_get(v_t_393_, 0);
lean_inc(v_a_402_);
v_a_403_ = lean_ctor_get(v_t_393_, 1);
lean_inc(v_a_403_);
lean_dec_ref(v_t_393_);
v___x_404_ = lean_apply_2(v_max_396_, v_a_402_, v_a_403_);
return v___x_404_;
}
case 3:
{
lean_object* v_a_405_; lean_object* v_a_406_; lean_object* v___x_407_; 
lean_dec(v_mvar_399_);
lean_dec(v_param_398_);
lean_dec(v_max_396_);
lean_dec(v_succ_395_);
v_a_405_ = lean_ctor_get(v_t_393_, 0);
lean_inc(v_a_405_);
v_a_406_ = lean_ctor_get(v_t_393_, 1);
lean_inc(v_a_406_);
lean_dec_ref(v_t_393_);
v___x_407_ = lean_apply_2(v_imax_397_, v_a_405_, v_a_406_);
return v___x_407_;
}
case 4:
{
lean_object* v_a_408_; lean_object* v___x_409_; 
lean_dec(v_mvar_399_);
lean_dec(v_imax_397_);
lean_dec(v_max_396_);
lean_dec(v_succ_395_);
v_a_408_ = lean_ctor_get(v_t_393_, 0);
lean_inc(v_a_408_);
lean_dec_ref(v_t_393_);
v___x_409_ = lean_apply_1(v_param_398_, v_a_408_);
return v___x_409_;
}
default: 
{
lean_object* v_a_410_; lean_object* v___x_411_; 
lean_dec(v_param_398_);
lean_dec(v_imax_397_);
lean_dec(v_max_396_);
lean_dec(v_succ_395_);
v_a_410_ = lean_ctor_get(v_t_393_, 0);
lean_inc(v_a_410_);
lean_dec_ref(v_t_393_);
v___x_411_ = lean_apply_1(v_mvar_399_, v_a_410_);
return v___x_411_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_casesOn___override___boxed(lean_object* v_motive_412_, lean_object* v_t_413_, lean_object* v_zero_414_, lean_object* v_succ_415_, lean_object* v_max_416_, lean_object* v_imax_417_, lean_object* v_param_418_, lean_object* v_mvar_419_){
_start:
{
lean_object* v_res_420_; 
v_res_420_ = l_Lean_Level_casesOn___override(v_motive_412_, v_t_413_, v_zero_414_, v_succ_415_, v_max_416_, v_imax_417_, v_param_418_, v_mvar_419_);
lean_dec(v_zero_414_);
return v_res_420_;
}
}
static lean_object* _init_l_Lean_Level_zero___override(void){
_start:
{
lean_object* v___x_421_; 
v___x_421_ = lean_box(0);
return v___x_421_;
}
}
static uint64_t _init_l_Lean_Level_data___override___closed__0(void){
_start:
{
uint8_t v___x_422_; lean_object* v___x_423_; uint64_t v___x_424_; uint64_t v___x_425_; 
v___x_422_ = 0;
v___x_423_ = lean_unsigned_to_nat(0u);
v___x_424_ = 2221ULL;
v___x_425_ = lean_level_mk_data(v___x_424_, v___x_423_, v___x_422_, v___x_422_);
return v___x_425_;
}
}
LEAN_EXPORT uint64_t l_Lean_Level_data___override(lean_object* v_x_426_){
_start:
{
switch(lean_obj_tag(v_x_426_))
{
case 0:
{
uint64_t v___x_427_; 
v___x_427_ = lean_uint64_once(&l_Lean_Level_data___override___closed__0, &l_Lean_Level_data___override___closed__0_once, _init_l_Lean_Level_data___override___closed__0);
return v___x_427_;
}
case 2:
{
uint64_t v_data_428_; 
v_data_428_ = lean_ctor_get_uint64(v_x_426_, sizeof(void*)*2);
return v_data_428_;
}
case 3:
{
uint64_t v_data_429_; 
v_data_429_ = lean_ctor_get_uint64(v_x_426_, sizeof(void*)*2);
return v_data_429_;
}
default: 
{
uint64_t v_data_430_; 
v_data_430_ = lean_ctor_get_uint64(v_x_426_, sizeof(void*)*1);
return v_data_430_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_data___override___boxed(lean_object* v_x_431_){
_start:
{
uint64_t v_res_432_; lean_object* v_r_433_; 
v_res_432_ = l_Lean_Level_data___override(v_x_431_);
lean_dec(v_x_431_);
v_r_433_ = lean_box_uint64(v_res_432_);
return v_r_433_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_succ___override(lean_object* v_a_434_){
_start:
{
uint64_t v___x_435_; uint64_t v___x_436_; uint64_t v___x_437_; uint64_t v___x_438_; uint32_t v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; uint8_t v___x_443_; uint8_t v___x_444_; uint64_t v___x_445_; lean_object* v___x_446_; 
v___x_435_ = 2243ULL;
v___x_436_ = l_Lean_Level_data___override(v_a_434_);
v___x_437_ = l_Lean_Level_Data_hash(v___x_436_);
v___x_438_ = lean_uint64_mix_hash(v___x_435_, v___x_437_);
v___x_439_ = l_Lean_Level_Data_depth(v___x_436_);
v___x_440_ = lean_uint32_to_nat(v___x_439_);
v___x_441_ = lean_unsigned_to_nat(1u);
v___x_442_ = lean_nat_add(v___x_440_, v___x_441_);
lean_dec(v___x_440_);
v___x_443_ = l_Lean_Level_Data_hasMVar(v___x_436_);
v___x_444_ = l_Lean_Level_Data_hasParam(v___x_436_);
v___x_445_ = lean_level_mk_data(v___x_438_, v___x_442_, v___x_443_, v___x_444_);
v___x_446_ = lean_alloc_ctor(1, 1, 8);
lean_ctor_set(v___x_446_, 0, v_a_434_);
lean_ctor_set_uint64(v___x_446_, sizeof(void*)*1, v___x_445_);
return v___x_446_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_max___override(lean_object* v_a_447_, lean_object* v_a_448_){
_start:
{
uint64_t v___x_449_; uint64_t v___x_450_; uint64_t v___x_451_; uint64_t v___x_452_; uint64_t v___x_453_; uint64_t v___x_454_; uint64_t v___x_455_; uint8_t v___y_457_; lean_object* v___y_458_; uint8_t v___y_459_; lean_object* v___y_463_; uint8_t v___y_464_; lean_object* v___y_468_; uint32_t v___x_473_; lean_object* v___x_474_; uint32_t v___x_475_; lean_object* v___x_476_; uint8_t v___x_477_; 
v___x_449_ = 2251ULL;
v___x_450_ = l_Lean_Level_data___override(v_a_447_);
v___x_451_ = l_Lean_Level_Data_hash(v___x_450_);
v___x_452_ = l_Lean_Level_data___override(v_a_448_);
v___x_453_ = l_Lean_Level_Data_hash(v___x_452_);
v___x_454_ = lean_uint64_mix_hash(v___x_451_, v___x_453_);
v___x_455_ = lean_uint64_mix_hash(v___x_449_, v___x_454_);
v___x_473_ = l_Lean_Level_Data_depth(v___x_450_);
v___x_474_ = lean_uint32_to_nat(v___x_473_);
v___x_475_ = l_Lean_Level_Data_depth(v___x_452_);
v___x_476_ = lean_uint32_to_nat(v___x_475_);
v___x_477_ = lean_nat_dec_le(v___x_474_, v___x_476_);
if (v___x_477_ == 0)
{
lean_dec(v___x_476_);
v___y_468_ = v___x_474_;
goto v___jp_467_;
}
else
{
lean_dec(v___x_474_);
v___y_468_ = v___x_476_;
goto v___jp_467_;
}
v___jp_456_:
{
uint64_t v___x_460_; lean_object* v___x_461_; 
v___x_460_ = lean_level_mk_data(v___x_455_, v___y_458_, v___y_457_, v___y_459_);
v___x_461_ = lean_alloc_ctor(2, 2, 8);
lean_ctor_set(v___x_461_, 0, v_a_447_);
lean_ctor_set(v___x_461_, 1, v_a_448_);
lean_ctor_set_uint64(v___x_461_, sizeof(void*)*2, v___x_460_);
return v___x_461_;
}
v___jp_462_:
{
uint8_t v___x_465_; 
v___x_465_ = l_Lean_Level_Data_hasParam(v___x_450_);
if (v___x_465_ == 0)
{
uint8_t v___x_466_; 
v___x_466_ = l_Lean_Level_Data_hasParam(v___x_452_);
v___y_457_ = v___y_464_;
v___y_458_ = v___y_463_;
v___y_459_ = v___x_466_;
goto v___jp_456_;
}
else
{
v___y_457_ = v___y_464_;
v___y_458_ = v___y_463_;
v___y_459_ = v___x_465_;
goto v___jp_456_;
}
}
v___jp_467_:
{
lean_object* v___x_469_; lean_object* v___x_470_; uint8_t v___x_471_; 
v___x_469_ = lean_unsigned_to_nat(1u);
v___x_470_ = lean_nat_add(v___y_468_, v___x_469_);
lean_dec(v___y_468_);
v___x_471_ = l_Lean_Level_Data_hasMVar(v___x_450_);
if (v___x_471_ == 0)
{
uint8_t v___x_472_; 
v___x_472_ = l_Lean_Level_Data_hasMVar(v___x_452_);
v___y_463_ = v___x_470_;
v___y_464_ = v___x_472_;
goto v___jp_462_;
}
else
{
v___y_463_ = v___x_470_;
v___y_464_ = v___x_471_;
goto v___jp_462_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_imax___override(lean_object* v_a_478_, lean_object* v_a_479_){
_start:
{
uint64_t v___x_480_; uint64_t v___x_481_; uint64_t v___x_482_; uint64_t v___x_483_; uint64_t v___x_484_; uint64_t v___x_485_; uint64_t v___x_486_; uint8_t v___y_488_; lean_object* v___y_489_; uint8_t v___y_490_; lean_object* v___y_494_; uint8_t v___y_495_; lean_object* v___y_499_; uint32_t v___x_504_; lean_object* v___x_505_; uint32_t v___x_506_; lean_object* v___x_507_; uint8_t v___x_508_; 
v___x_480_ = 2267ULL;
v___x_481_ = l_Lean_Level_data___override(v_a_478_);
v___x_482_ = l_Lean_Level_Data_hash(v___x_481_);
v___x_483_ = l_Lean_Level_data___override(v_a_479_);
v___x_484_ = l_Lean_Level_Data_hash(v___x_483_);
v___x_485_ = lean_uint64_mix_hash(v___x_482_, v___x_484_);
v___x_486_ = lean_uint64_mix_hash(v___x_480_, v___x_485_);
v___x_504_ = l_Lean_Level_Data_depth(v___x_481_);
v___x_505_ = lean_uint32_to_nat(v___x_504_);
v___x_506_ = l_Lean_Level_Data_depth(v___x_483_);
v___x_507_ = lean_uint32_to_nat(v___x_506_);
v___x_508_ = lean_nat_dec_le(v___x_505_, v___x_507_);
if (v___x_508_ == 0)
{
lean_dec(v___x_507_);
v___y_499_ = v___x_505_;
goto v___jp_498_;
}
else
{
lean_dec(v___x_505_);
v___y_499_ = v___x_507_;
goto v___jp_498_;
}
v___jp_487_:
{
uint64_t v___x_491_; lean_object* v___x_492_; 
v___x_491_ = lean_level_mk_data(v___x_486_, v___y_489_, v___y_488_, v___y_490_);
v___x_492_ = lean_alloc_ctor(3, 2, 8);
lean_ctor_set(v___x_492_, 0, v_a_478_);
lean_ctor_set(v___x_492_, 1, v_a_479_);
lean_ctor_set_uint64(v___x_492_, sizeof(void*)*2, v___x_491_);
return v___x_492_;
}
v___jp_493_:
{
uint8_t v___x_496_; 
v___x_496_ = l_Lean_Level_Data_hasParam(v___x_481_);
if (v___x_496_ == 0)
{
uint8_t v___x_497_; 
v___x_497_ = l_Lean_Level_Data_hasParam(v___x_483_);
v___y_488_ = v___y_495_;
v___y_489_ = v___y_494_;
v___y_490_ = v___x_497_;
goto v___jp_487_;
}
else
{
v___y_488_ = v___y_495_;
v___y_489_ = v___y_494_;
v___y_490_ = v___x_496_;
goto v___jp_487_;
}
}
v___jp_498_:
{
lean_object* v___x_500_; lean_object* v___x_501_; uint8_t v___x_502_; 
v___x_500_ = lean_unsigned_to_nat(1u);
v___x_501_ = lean_nat_add(v___y_499_, v___x_500_);
lean_dec(v___y_499_);
v___x_502_ = l_Lean_Level_Data_hasMVar(v___x_481_);
if (v___x_502_ == 0)
{
uint8_t v___x_503_; 
v___x_503_ = l_Lean_Level_Data_hasMVar(v___x_483_);
v___y_494_ = v___x_501_;
v___y_495_ = v___x_503_;
goto v___jp_493_;
}
else
{
v___y_494_ = v___x_501_;
v___y_495_ = v___x_502_;
goto v___jp_493_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_param___override(lean_object* v_a_509_){
_start:
{
uint64_t v___x_510_; uint64_t v___y_512_; 
v___x_510_ = 2239ULL;
if (lean_obj_tag(v_a_509_) == 0)
{
uint64_t v___x_519_; 
v___x_519_ = lean_uint64_once(&l_Lean_instHashableLevelMVarId_hash___closed__0, &l_Lean_instHashableLevelMVarId_hash___closed__0_once, _init_l_Lean_instHashableLevelMVarId_hash___closed__0);
v___y_512_ = v___x_519_;
goto v___jp_511_;
}
else
{
uint64_t v_hash_520_; 
v_hash_520_ = lean_ctor_get_uint64(v_a_509_, sizeof(void*)*2);
v___y_512_ = v_hash_520_;
goto v___jp_511_;
}
v___jp_511_:
{
uint64_t v___x_513_; lean_object* v___x_514_; uint8_t v___x_515_; uint8_t v___x_516_; uint64_t v___x_517_; lean_object* v___x_518_; 
v___x_513_ = lean_uint64_mix_hash(v___x_510_, v___y_512_);
v___x_514_ = lean_unsigned_to_nat(0u);
v___x_515_ = 0;
v___x_516_ = 1;
v___x_517_ = lean_level_mk_data(v___x_513_, v___x_514_, v___x_515_, v___x_516_);
v___x_518_ = lean_alloc_ctor(4, 1, 8);
lean_ctor_set(v___x_518_, 0, v_a_509_);
lean_ctor_set_uint64(v___x_518_, sizeof(void*)*1, v___x_517_);
return v___x_518_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_mvar___override(lean_object* v_a_521_){
_start:
{
uint64_t v___x_522_; uint64_t v___x_523_; uint64_t v___x_524_; lean_object* v___x_525_; uint8_t v___x_526_; uint8_t v___x_527_; uint64_t v___x_528_; lean_object* v___x_529_; 
v___x_522_ = 2237ULL;
v___x_523_ = l_Lean_instHashableLevelMVarId_hash(v_a_521_);
v___x_524_ = lean_uint64_mix_hash(v___x_522_, v___x_523_);
v___x_525_ = lean_unsigned_to_nat(0u);
v___x_526_ = 1;
v___x_527_ = 0;
v___x_528_ = lean_level_mk_data(v___x_524_, v___x_525_, v___x_526_, v___x_527_);
v___x_529_ = lean_alloc_ctor(5, 1, 8);
lean_ctor_set(v___x_529_, 0, v_a_521_);
lean_ctor_set_uint64(v___x_529_, sizeof(void*)*1, v___x_528_);
return v___x_529_;
}
}
static lean_object* _init_l_Lean_instInhabitedLevel_default(void){
_start:
{
lean_object* v___x_530_; 
v___x_530_ = lean_box(0);
return v___x_530_;
}
}
static lean_object* _init_l_Lean_instInhabitedLevel(void){
_start:
{
lean_object* v___x_531_; 
v___x_531_ = lean_box(0);
return v___x_531_;
}
}
static lean_object* _init_l_Lean_instReprLevel_repr___closed__2(void){
_start:
{
lean_object* v___x_535_; lean_object* v___x_536_; 
v___x_535_ = lean_unsigned_to_nat(2u);
v___x_536_ = lean_nat_to_int(v___x_535_);
return v___x_536_;
}
}
static lean_object* _init_l_Lean_instReprLevel_repr___closed__3(void){
_start:
{
lean_object* v___x_537_; lean_object* v___x_538_; 
v___x_537_ = lean_unsigned_to_nat(1u);
v___x_538_ = lean_nat_to_int(v___x_537_);
return v___x_538_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprLevel_repr(lean_object* v_x_569_, lean_object* v_prec_570_){
_start:
{
lean_object* v___y_572_; 
switch(lean_obj_tag(v_x_569_))
{
case 0:
{
lean_object* v___x_578_; uint8_t v___x_579_; 
v___x_578_ = lean_unsigned_to_nat(1024u);
v___x_579_ = lean_nat_dec_le(v___x_578_, v_prec_570_);
if (v___x_579_ == 0)
{
lean_object* v___x_580_; 
v___x_580_ = lean_obj_once(&l_Lean_instReprLevel_repr___closed__2, &l_Lean_instReprLevel_repr___closed__2_once, _init_l_Lean_instReprLevel_repr___closed__2);
v___y_572_ = v___x_580_;
goto v___jp_571_;
}
else
{
lean_object* v___x_581_; 
v___x_581_ = lean_obj_once(&l_Lean_instReprLevel_repr___closed__3, &l_Lean_instReprLevel_repr___closed__3_once, _init_l_Lean_instReprLevel_repr___closed__3);
v___y_572_ = v___x_581_;
goto v___jp_571_;
}
}
case 1:
{
lean_object* v_a_582_; lean_object* v___x_583_; lean_object* v___y_585_; uint8_t v___x_593_; 
v_a_582_ = lean_ctor_get(v_x_569_, 0);
lean_inc(v_a_582_);
lean_dec_ref(v_x_569_);
v___x_583_ = lean_unsigned_to_nat(1024u);
v___x_593_ = lean_nat_dec_le(v___x_583_, v_prec_570_);
if (v___x_593_ == 0)
{
lean_object* v___x_594_; 
v___x_594_ = lean_obj_once(&l_Lean_instReprLevel_repr___closed__2, &l_Lean_instReprLevel_repr___closed__2_once, _init_l_Lean_instReprLevel_repr___closed__2);
v___y_585_ = v___x_594_;
goto v___jp_584_;
}
else
{
lean_object* v___x_595_; 
v___x_595_ = lean_obj_once(&l_Lean_instReprLevel_repr___closed__3, &l_Lean_instReprLevel_repr___closed__3_once, _init_l_Lean_instReprLevel_repr___closed__3);
v___y_585_ = v___x_595_;
goto v___jp_584_;
}
v___jp_584_:
{
lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; uint8_t v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; 
v___x_586_ = ((lean_object*)(l_Lean_instReprLevel_repr___closed__6));
v___x_587_ = l_Lean_instReprLevel_repr(v_a_582_, v___x_583_);
v___x_588_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_588_, 0, v___x_586_);
lean_ctor_set(v___x_588_, 1, v___x_587_);
lean_inc(v___y_585_);
v___x_589_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_589_, 0, v___y_585_);
lean_ctor_set(v___x_589_, 1, v___x_588_);
v___x_590_ = 0;
v___x_591_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_591_, 0, v___x_589_);
lean_ctor_set_uint8(v___x_591_, sizeof(void*)*1, v___x_590_);
v___x_592_ = l_Repr_addAppParen(v___x_591_, v_prec_570_);
return v___x_592_;
}
}
case 2:
{
lean_object* v_a_596_; lean_object* v_a_597_; lean_object* v___x_598_; lean_object* v___y_600_; uint8_t v___x_612_; 
v_a_596_ = lean_ctor_get(v_x_569_, 0);
lean_inc(v_a_596_);
v_a_597_ = lean_ctor_get(v_x_569_, 1);
lean_inc(v_a_597_);
lean_dec_ref(v_x_569_);
v___x_598_ = lean_unsigned_to_nat(1024u);
v___x_612_ = lean_nat_dec_le(v___x_598_, v_prec_570_);
if (v___x_612_ == 0)
{
lean_object* v___x_613_; 
v___x_613_ = lean_obj_once(&l_Lean_instReprLevel_repr___closed__2, &l_Lean_instReprLevel_repr___closed__2_once, _init_l_Lean_instReprLevel_repr___closed__2);
v___y_600_ = v___x_613_;
goto v___jp_599_;
}
else
{
lean_object* v___x_614_; 
v___x_614_ = lean_obj_once(&l_Lean_instReprLevel_repr___closed__3, &l_Lean_instReprLevel_repr___closed__3_once, _init_l_Lean_instReprLevel_repr___closed__3);
v___y_600_ = v___x_614_;
goto v___jp_599_;
}
v___jp_599_:
{
lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; uint8_t v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; 
v___x_601_ = lean_box(1);
v___x_602_ = ((lean_object*)(l_Lean_instReprLevel_repr___closed__9));
v___x_603_ = l_Lean_instReprLevel_repr(v_a_596_, v___x_598_);
v___x_604_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_604_, 0, v___x_602_);
lean_ctor_set(v___x_604_, 1, v___x_603_);
v___x_605_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_605_, 0, v___x_604_);
lean_ctor_set(v___x_605_, 1, v___x_601_);
v___x_606_ = l_Lean_instReprLevel_repr(v_a_597_, v___x_598_);
v___x_607_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_607_, 0, v___x_605_);
lean_ctor_set(v___x_607_, 1, v___x_606_);
lean_inc(v___y_600_);
v___x_608_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_608_, 0, v___y_600_);
lean_ctor_set(v___x_608_, 1, v___x_607_);
v___x_609_ = 0;
v___x_610_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_610_, 0, v___x_608_);
lean_ctor_set_uint8(v___x_610_, sizeof(void*)*1, v___x_609_);
v___x_611_ = l_Repr_addAppParen(v___x_610_, v_prec_570_);
return v___x_611_;
}
}
case 3:
{
lean_object* v_a_615_; lean_object* v_a_616_; lean_object* v___x_617_; lean_object* v___y_619_; uint8_t v___x_631_; 
v_a_615_ = lean_ctor_get(v_x_569_, 0);
lean_inc(v_a_615_);
v_a_616_ = lean_ctor_get(v_x_569_, 1);
lean_inc(v_a_616_);
lean_dec_ref(v_x_569_);
v___x_617_ = lean_unsigned_to_nat(1024u);
v___x_631_ = lean_nat_dec_le(v___x_617_, v_prec_570_);
if (v___x_631_ == 0)
{
lean_object* v___x_632_; 
v___x_632_ = lean_obj_once(&l_Lean_instReprLevel_repr___closed__2, &l_Lean_instReprLevel_repr___closed__2_once, _init_l_Lean_instReprLevel_repr___closed__2);
v___y_619_ = v___x_632_;
goto v___jp_618_;
}
else
{
lean_object* v___x_633_; 
v___x_633_ = lean_obj_once(&l_Lean_instReprLevel_repr___closed__3, &l_Lean_instReprLevel_repr___closed__3_once, _init_l_Lean_instReprLevel_repr___closed__3);
v___y_619_ = v___x_633_;
goto v___jp_618_;
}
v___jp_618_:
{
lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; uint8_t v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; 
v___x_620_ = lean_box(1);
v___x_621_ = ((lean_object*)(l_Lean_instReprLevel_repr___closed__12));
v___x_622_ = l_Lean_instReprLevel_repr(v_a_615_, v___x_617_);
v___x_623_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_623_, 0, v___x_621_);
lean_ctor_set(v___x_623_, 1, v___x_622_);
v___x_624_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_624_, 0, v___x_623_);
lean_ctor_set(v___x_624_, 1, v___x_620_);
v___x_625_ = l_Lean_instReprLevel_repr(v_a_616_, v___x_617_);
v___x_626_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_626_, 0, v___x_624_);
lean_ctor_set(v___x_626_, 1, v___x_625_);
lean_inc(v___y_619_);
v___x_627_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_627_, 0, v___y_619_);
lean_ctor_set(v___x_627_, 1, v___x_626_);
v___x_628_ = 0;
v___x_629_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_629_, 0, v___x_627_);
lean_ctor_set_uint8(v___x_629_, sizeof(void*)*1, v___x_628_);
v___x_630_ = l_Repr_addAppParen(v___x_629_, v_prec_570_);
return v___x_630_;
}
}
case 4:
{
lean_object* v_a_634_; lean_object* v___y_636_; lean_object* v___x_645_; uint8_t v___x_646_; 
v_a_634_ = lean_ctor_get(v_x_569_, 0);
lean_inc(v_a_634_);
lean_dec_ref(v_x_569_);
v___x_645_ = lean_unsigned_to_nat(1024u);
v___x_646_ = lean_nat_dec_le(v___x_645_, v_prec_570_);
if (v___x_646_ == 0)
{
lean_object* v___x_647_; 
v___x_647_ = lean_obj_once(&l_Lean_instReprLevel_repr___closed__2, &l_Lean_instReprLevel_repr___closed__2_once, _init_l_Lean_instReprLevel_repr___closed__2);
v___y_636_ = v___x_647_;
goto v___jp_635_;
}
else
{
lean_object* v___x_648_; 
v___x_648_ = lean_obj_once(&l_Lean_instReprLevel_repr___closed__3, &l_Lean_instReprLevel_repr___closed__3_once, _init_l_Lean_instReprLevel_repr___closed__3);
v___y_636_ = v___x_648_;
goto v___jp_635_;
}
v___jp_635_:
{
lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; uint8_t v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; 
v___x_637_ = ((lean_object*)(l_Lean_instReprLevel_repr___closed__15));
v___x_638_ = lean_unsigned_to_nat(1024u);
v___x_639_ = l_Lean_Name_reprPrec(v_a_634_, v___x_638_);
v___x_640_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_640_, 0, v___x_637_);
lean_ctor_set(v___x_640_, 1, v___x_639_);
lean_inc(v___y_636_);
v___x_641_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_641_, 0, v___y_636_);
lean_ctor_set(v___x_641_, 1, v___x_640_);
v___x_642_ = 0;
v___x_643_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_643_, 0, v___x_641_);
lean_ctor_set_uint8(v___x_643_, sizeof(void*)*1, v___x_642_);
v___x_644_ = l_Repr_addAppParen(v___x_643_, v_prec_570_);
return v___x_644_;
}
}
default: 
{
lean_object* v_a_649_; lean_object* v___y_651_; lean_object* v___x_660_; uint8_t v___x_661_; 
v_a_649_ = lean_ctor_get(v_x_569_, 0);
lean_inc(v_a_649_);
lean_dec_ref(v_x_569_);
v___x_660_ = lean_unsigned_to_nat(1024u);
v___x_661_ = lean_nat_dec_le(v___x_660_, v_prec_570_);
if (v___x_661_ == 0)
{
lean_object* v___x_662_; 
v___x_662_ = lean_obj_once(&l_Lean_instReprLevel_repr___closed__2, &l_Lean_instReprLevel_repr___closed__2_once, _init_l_Lean_instReprLevel_repr___closed__2);
v___y_651_ = v___x_662_;
goto v___jp_650_;
}
else
{
lean_object* v___x_663_; 
v___x_663_ = lean_obj_once(&l_Lean_instReprLevel_repr___closed__3, &l_Lean_instReprLevel_repr___closed__3_once, _init_l_Lean_instReprLevel_repr___closed__3);
v___y_651_ = v___x_663_;
goto v___jp_650_;
}
v___jp_650_:
{
lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; uint8_t v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; 
v___x_652_ = ((lean_object*)(l_Lean_instReprLevel_repr___closed__18));
v___x_653_ = lean_unsigned_to_nat(1024u);
v___x_654_ = l_Lean_Name_reprPrec(v_a_649_, v___x_653_);
v___x_655_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_655_, 0, v___x_652_);
lean_ctor_set(v___x_655_, 1, v___x_654_);
lean_inc(v___y_651_);
v___x_656_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_656_, 0, v___y_651_);
lean_ctor_set(v___x_656_, 1, v___x_655_);
v___x_657_ = 0;
v___x_658_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_658_, 0, v___x_656_);
lean_ctor_set_uint8(v___x_658_, sizeof(void*)*1, v___x_657_);
v___x_659_ = l_Repr_addAppParen(v___x_658_, v_prec_570_);
return v___x_659_;
}
}
}
v___jp_571_:
{
lean_object* v___x_573_; lean_object* v___x_574_; uint8_t v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; 
v___x_573_ = ((lean_object*)(l_Lean_instReprLevel_repr___closed__1));
lean_inc(v___y_572_);
v___x_574_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_574_, 0, v___y_572_);
lean_ctor_set(v___x_574_, 1, v___x_573_);
v___x_575_ = 0;
v___x_576_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_576_, 0, v___x_574_);
lean_ctor_set_uint8(v___x_576_, sizeof(void*)*1, v___x_575_);
v___x_577_ = l_Repr_addAppParen(v___x_576_, v_prec_570_);
return v___x_577_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instReprLevel_repr___boxed(lean_object* v_x_664_, lean_object* v_prec_665_){
_start:
{
lean_object* v_res_666_; 
v_res_666_ = l_Lean_instReprLevel_repr(v_x_664_, v_prec_665_);
lean_dec(v_prec_665_);
return v_res_666_;
}
}
LEAN_EXPORT uint64_t l_Lean_Level_hash(lean_object* v_u_669_){
_start:
{
uint64_t v___x_670_; uint64_t v___x_671_; 
v___x_670_ = l_Lean_Level_data___override(v_u_669_);
v___x_671_ = l_Lean_Level_Data_hash(v___x_670_);
return v___x_671_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_hash___boxed(lean_object* v_u_672_){
_start:
{
uint64_t v_res_673_; lean_object* v_r_674_; 
v_res_673_ = l_Lean_Level_hash(v_u_672_);
lean_dec(v_u_672_);
v_r_674_ = lean_box_uint64(v_res_673_);
return v_r_674_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_depth(lean_object* v_u_677_){
_start:
{
uint64_t v___x_678_; uint32_t v___x_679_; lean_object* v___x_680_; 
v___x_678_ = l_Lean_Level_data___override(v_u_677_);
v___x_679_ = l_Lean_Level_Data_depth(v___x_678_);
v___x_680_ = lean_uint32_to_nat(v___x_679_);
return v___x_680_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_depth___boxed(lean_object* v_u_681_){
_start:
{
lean_object* v_res_682_; 
v_res_682_ = l_Lean_Level_depth(v_u_681_);
lean_dec(v_u_681_);
return v_res_682_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_hasMVar(lean_object* v_u_683_){
_start:
{
uint64_t v___x_684_; uint8_t v___x_685_; 
v___x_684_ = l_Lean_Level_data___override(v_u_683_);
v___x_685_ = l_Lean_Level_Data_hasMVar(v___x_684_);
return v___x_685_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_hasMVar___boxed(lean_object* v_u_686_){
_start:
{
uint8_t v_res_687_; lean_object* v_r_688_; 
v_res_687_ = l_Lean_Level_hasMVar(v_u_686_);
lean_dec(v_u_686_);
v_r_688_ = lean_box(v_res_687_);
return v_r_688_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_hasParam(lean_object* v_u_689_){
_start:
{
uint64_t v___x_690_; uint8_t v___x_691_; 
v___x_690_ = l_Lean_Level_data___override(v_u_689_);
v___x_691_ = l_Lean_Level_Data_hasParam(v___x_690_);
return v___x_691_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_hasParam___boxed(lean_object* v_u_692_){
_start:
{
uint8_t v_res_693_; lean_object* v_r_694_; 
v_res_693_ = l_Lean_Level_hasParam(v_u_692_);
lean_dec(v_u_692_);
v_r_694_ = lean_box(v_res_693_);
return v_r_694_;
}
}
LEAN_EXPORT uint32_t lean_level_hash(lean_object* v_u_695_){
_start:
{
uint64_t v___x_696_; uint32_t v___x_697_; 
v___x_696_ = l_Lean_Level_hash(v_u_695_);
lean_dec(v_u_695_);
v___x_697_ = lean_uint64_to_uint32(v___x_696_);
return v___x_697_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_hashEx___boxed(lean_object* v_u_698_){
_start:
{
uint32_t v_res_699_; lean_object* v_r_700_; 
v_res_699_ = lean_level_hash(v_u_698_);
v_r_700_ = lean_box_uint32(v_res_699_);
return v_r_700_;
}
}
LEAN_EXPORT uint8_t lean_level_has_mvar(lean_object* v_u_701_){
_start:
{
uint8_t v___x_702_; 
v___x_702_ = l_Lean_Level_hasMVar(v_u_701_);
lean_dec(v_u_701_);
return v___x_702_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_hasMVarEx___boxed(lean_object* v_u_703_){
_start:
{
uint8_t v_res_704_; lean_object* v_r_705_; 
v_res_704_ = lean_level_has_mvar(v_u_703_);
v_r_705_ = lean_box(v_res_704_);
return v_r_705_;
}
}
LEAN_EXPORT uint8_t lean_level_has_param(lean_object* v_u_706_){
_start:
{
uint8_t v___x_707_; 
v___x_707_ = l_Lean_Level_hasParam(v_u_706_);
lean_dec(v_u_706_);
return v___x_707_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_hasParamEx___boxed(lean_object* v_u_708_){
_start:
{
uint8_t v_res_709_; lean_object* v_r_710_; 
v_res_709_ = lean_level_has_param(v_u_708_);
v_r_710_ = lean_box(v_res_709_);
return v_r_710_;
}
}
LEAN_EXPORT uint32_t lean_level_depth(lean_object* v_u_711_){
_start:
{
uint64_t v___x_712_; uint32_t v___x_713_; 
v___x_712_ = l_Lean_Level_data___override(v_u_711_);
lean_dec(v_u_711_);
v___x_713_ = l_Lean_Level_Data_depth(v___x_712_);
return v___x_713_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_depthEx___boxed(lean_object* v_u_714_){
_start:
{
uint32_t v_res_715_; lean_object* v_r_716_; 
v_res_715_ = lean_level_depth(v_u_714_);
v_r_716_ = lean_box_uint32(v_res_715_);
return v_r_716_;
}
}
static lean_object* _init_l_Lean_levelZero(void){
_start:
{
lean_object* v___x_717_; 
v___x_717_ = lean_box(0);
return v___x_717_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLevelMVar(lean_object* v_mvarId_718_){
_start:
{
lean_object* v___x_719_; 
v___x_719_ = l_Lean_Level_mvar___override(v_mvarId_718_);
return v___x_719_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLevelParam(lean_object* v_name_720_){
_start:
{
lean_object* v___x_721_; 
v___x_721_ = l_Lean_Level_param___override(v_name_720_);
return v___x_721_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLevelSucc(lean_object* v_u_722_){
_start:
{
lean_object* v___x_723_; 
v___x_723_ = l_Lean_Level_succ___override(v_u_722_);
return v___x_723_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLevelMax(lean_object* v_u_724_, lean_object* v_v_725_){
_start:
{
lean_object* v___x_726_; 
v___x_726_ = l_Lean_Level_max___override(v_u_724_, v_v_725_);
return v___x_726_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLevelIMax(lean_object* v_u_727_, lean_object* v_v_728_){
_start:
{
lean_object* v___x_729_; 
v___x_729_ = l_Lean_Level_imax___override(v_u_727_, v_v_728_);
return v___x_729_;
}
}
static lean_object* _init_l_Lean_Level_one___closed__0(void){
_start:
{
lean_object* v___x_730_; lean_object* v___x_731_; 
v___x_730_ = lean_box(0);
v___x_731_ = l_Lean_Level_succ___override(v___x_730_);
return v___x_731_;
}
}
static lean_object* _init_l_Lean_Level_one(void){
_start:
{
lean_object* v___x_732_; 
v___x_732_ = lean_obj_once(&l_Lean_Level_one___closed__0, &l_Lean_Level_one___closed__0_once, _init_l_Lean_Level_one___closed__0);
return v___x_732_;
}
}
static lean_object* _init_l_Lean_levelOne(void){
_start:
{
lean_object* v___x_733_; 
v___x_733_ = lean_obj_once(&l_Lean_Level_one___closed__0, &l_Lean_Level_one___closed__0_once, _init_l_Lean_Level_one___closed__0);
return v___x_733_;
}
}
LEAN_EXPORT lean_object* lean_level_mk_zero(lean_object* v_x_734_){
_start:
{
lean_object* v___x_735_; 
v___x_735_ = lean_box(0);
return v___x_735_;
}
}
LEAN_EXPORT lean_object* lean_level_mk_succ(lean_object* v_u_736_){
_start:
{
lean_object* v___x_737_; 
v___x_737_ = l_Lean_Level_succ___override(v_u_736_);
return v___x_737_;
}
}
LEAN_EXPORT lean_object* lean_level_mk_mvar(lean_object* v_mvarId_738_){
_start:
{
lean_object* v___x_739_; 
v___x_739_ = l_Lean_Level_mvar___override(v_mvarId_738_);
return v___x_739_;
}
}
LEAN_EXPORT lean_object* lean_level_mk_param(lean_object* v_name_740_){
_start:
{
lean_object* v___x_741_; 
v___x_741_ = l_Lean_Level_param___override(v_name_740_);
return v___x_741_;
}
}
LEAN_EXPORT lean_object* lean_level_mk_max(lean_object* v_u_742_, lean_object* v_v_743_){
_start:
{
lean_object* v___x_744_; 
v___x_744_ = l_Lean_Level_max___override(v_u_742_, v_v_743_);
return v___x_744_;
}
}
LEAN_EXPORT lean_object* lean_level_mk_imax(lean_object* v_u_745_, lean_object* v_v_746_){
_start:
{
lean_object* v___x_747_; 
v___x_747_ = l_Lean_Level_imax___override(v_u_745_, v_v_746_);
return v___x_747_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_isZero(lean_object* v_x_748_){
_start:
{
if (lean_obj_tag(v_x_748_) == 0)
{
uint8_t v___x_749_; 
v___x_749_ = 1;
return v___x_749_;
}
else
{
uint8_t v___x_750_; 
v___x_750_ = 0;
return v___x_750_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_isZero___boxed(lean_object* v_x_751_){
_start:
{
uint8_t v_res_752_; lean_object* v_r_753_; 
v_res_752_ = l_Lean_Level_isZero(v_x_751_);
lean_dec(v_x_751_);
v_r_753_ = lean_box(v_res_752_);
return v_r_753_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_isSucc(lean_object* v_x_754_){
_start:
{
if (lean_obj_tag(v_x_754_) == 1)
{
uint8_t v___x_755_; 
v___x_755_ = 1;
return v___x_755_;
}
else
{
uint8_t v___x_756_; 
v___x_756_ = 0;
return v___x_756_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_isSucc___boxed(lean_object* v_x_757_){
_start:
{
uint8_t v_res_758_; lean_object* v_r_759_; 
v_res_758_ = l_Lean_Level_isSucc(v_x_757_);
lean_dec(v_x_757_);
v_r_759_ = lean_box(v_res_758_);
return v_r_759_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_isMax(lean_object* v_x_760_){
_start:
{
if (lean_obj_tag(v_x_760_) == 2)
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
LEAN_EXPORT lean_object* l_Lean_Level_isMax___boxed(lean_object* v_x_763_){
_start:
{
uint8_t v_res_764_; lean_object* v_r_765_; 
v_res_764_ = l_Lean_Level_isMax(v_x_763_);
lean_dec(v_x_763_);
v_r_765_ = lean_box(v_res_764_);
return v_r_765_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_isIMax(lean_object* v_x_766_){
_start:
{
if (lean_obj_tag(v_x_766_) == 3)
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
LEAN_EXPORT lean_object* l_Lean_Level_isIMax___boxed(lean_object* v_x_769_){
_start:
{
uint8_t v_res_770_; lean_object* v_r_771_; 
v_res_770_ = l_Lean_Level_isIMax(v_x_769_);
lean_dec(v_x_769_);
v_r_771_ = lean_box(v_res_770_);
return v_r_771_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_isMaxIMax(lean_object* v_x_772_){
_start:
{
switch(lean_obj_tag(v_x_772_))
{
case 2:
{
uint8_t v___x_773_; 
v___x_773_ = 1;
return v___x_773_;
}
case 3:
{
uint8_t v___x_774_; 
v___x_774_ = 1;
return v___x_774_;
}
default: 
{
uint8_t v___x_775_; 
v___x_775_ = 0;
return v___x_775_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_isMaxIMax___boxed(lean_object* v_x_776_){
_start:
{
uint8_t v_res_777_; lean_object* v_r_778_; 
v_res_777_ = l_Lean_Level_isMaxIMax(v_x_776_);
lean_dec(v_x_776_);
v_r_778_ = lean_box(v_res_777_);
return v_r_778_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_isParam(lean_object* v_x_779_){
_start:
{
if (lean_obj_tag(v_x_779_) == 4)
{
uint8_t v___x_780_; 
v___x_780_ = 1;
return v___x_780_;
}
else
{
uint8_t v___x_781_; 
v___x_781_ = 0;
return v___x_781_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_isParam___boxed(lean_object* v_x_782_){
_start:
{
uint8_t v_res_783_; lean_object* v_r_784_; 
v_res_783_ = l_Lean_Level_isParam(v_x_782_);
lean_dec(v_x_782_);
v_r_784_ = lean_box(v_res_783_);
return v_r_784_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_isMVar(lean_object* v_x_785_){
_start:
{
if (lean_obj_tag(v_x_785_) == 5)
{
uint8_t v___x_786_; 
v___x_786_ = 1;
return v___x_786_;
}
else
{
uint8_t v___x_787_; 
v___x_787_ = 0;
return v___x_787_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_isMVar___boxed(lean_object* v_x_788_){
_start:
{
uint8_t v_res_789_; lean_object* v_r_790_; 
v_res_789_ = l_Lean_Level_isMVar(v_x_788_);
lean_dec(v_x_788_);
v_r_790_ = lean_box(v_res_789_);
return v_r_790_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Level_mvarId_x21_spec__0(lean_object* v_msg_791_){
_start:
{
lean_object* v___x_792_; lean_object* v___x_793_; 
v___x_792_ = lean_box(0);
v___x_793_ = lean_panic_fn_borrowed(v___x_792_, v_msg_791_);
return v___x_793_;
}
}
static lean_object* _init_l_Lean_Level_mvarId_x21___closed__3(void){
_start:
{
lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; 
v___x_797_ = ((lean_object*)(l_Lean_Level_mvarId_x21___closed__2));
v___x_798_ = lean_unsigned_to_nat(19u);
v___x_799_ = lean_unsigned_to_nat(195u);
v___x_800_ = ((lean_object*)(l_Lean_Level_mvarId_x21___closed__1));
v___x_801_ = ((lean_object*)(l_Lean_Level_mvarId_x21___closed__0));
v___x_802_ = l_mkPanicMessageWithDecl(v___x_801_, v___x_800_, v___x_799_, v___x_798_, v___x_797_);
return v___x_802_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_mvarId_x21(lean_object* v_x_803_){
_start:
{
if (lean_obj_tag(v_x_803_) == 5)
{
lean_object* v_a_804_; 
v_a_804_ = lean_ctor_get(v_x_803_, 0);
lean_inc(v_a_804_);
return v_a_804_;
}
else
{
lean_object* v___x_805_; lean_object* v___x_806_; 
v___x_805_ = lean_obj_once(&l_Lean_Level_mvarId_x21___closed__3, &l_Lean_Level_mvarId_x21___closed__3_once, _init_l_Lean_Level_mvarId_x21___closed__3);
v___x_806_ = l_panic___at___00Lean_Level_mvarId_x21_spec__0(v___x_805_);
return v___x_806_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_mvarId_x21___boxed(lean_object* v_x_807_){
_start:
{
lean_object* v_res_808_; 
v_res_808_ = l_Lean_Level_mvarId_x21(v_x_807_);
lean_dec(v_x_807_);
return v_res_808_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_isNeverZero(lean_object* v_x_809_){
_start:
{
switch(lean_obj_tag(v_x_809_))
{
case 0:
{
uint8_t v___x_810_; 
v___x_810_ = 0;
return v___x_810_;
}
case 1:
{
uint8_t v___x_811_; 
v___x_811_ = 1;
return v___x_811_;
}
case 2:
{
lean_object* v_a_812_; lean_object* v_a_813_; uint8_t v___x_814_; 
v_a_812_ = lean_ctor_get(v_x_809_, 0);
v_a_813_ = lean_ctor_get(v_x_809_, 1);
v___x_814_ = l_Lean_Level_isNeverZero(v_a_812_);
if (v___x_814_ == 0)
{
v_x_809_ = v_a_813_;
goto _start;
}
else
{
return v___x_814_;
}
}
case 3:
{
lean_object* v_a_816_; 
v_a_816_ = lean_ctor_get(v_x_809_, 1);
v_x_809_ = v_a_816_;
goto _start;
}
default: 
{
uint8_t v___x_818_; 
v___x_818_ = 0;
return v___x_818_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_isNeverZero___boxed(lean_object* v_x_819_){
_start:
{
uint8_t v_res_820_; lean_object* v_r_821_; 
v_res_820_ = l_Lean_Level_isNeverZero(v_x_819_);
lean_dec(v_x_819_);
v_r_821_ = lean_box(v_res_820_);
return v_r_821_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_isAlwaysZero(lean_object* v_x_822_){
_start:
{
switch(lean_obj_tag(v_x_822_))
{
case 0:
{
uint8_t v___x_823_; 
v___x_823_ = 1;
return v___x_823_;
}
case 2:
{
lean_object* v_a_824_; lean_object* v_a_825_; uint8_t v___x_826_; 
v_a_824_ = lean_ctor_get(v_x_822_, 0);
v_a_825_ = lean_ctor_get(v_x_822_, 1);
v___x_826_ = l_Lean_Level_isAlwaysZero(v_a_824_);
if (v___x_826_ == 0)
{
return v___x_826_;
}
else
{
v_x_822_ = v_a_825_;
goto _start;
}
}
case 3:
{
lean_object* v_a_828_; 
v_a_828_ = lean_ctor_get(v_x_822_, 1);
v_x_822_ = v_a_828_;
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
LEAN_EXPORT lean_object* l_Lean_Level_isAlwaysZero___boxed(lean_object* v_x_831_){
_start:
{
uint8_t v_res_832_; lean_object* v_r_833_; 
v_res_832_ = l_Lean_Level_isAlwaysZero(v_x_831_);
lean_dec(v_x_831_);
v_r_833_ = lean_box(v_res_832_);
return v_r_833_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_ofNat(lean_object* v_x_834_){
_start:
{
lean_object* v_zero_835_; uint8_t v_isZero_836_; 
v_zero_835_ = lean_unsigned_to_nat(0u);
v_isZero_836_ = lean_nat_dec_eq(v_x_834_, v_zero_835_);
if (v_isZero_836_ == 1)
{
lean_object* v___x_837_; 
v___x_837_ = lean_box(0);
return v___x_837_;
}
else
{
lean_object* v_one_838_; lean_object* v_n_839_; lean_object* v___x_840_; lean_object* v___x_841_; 
v_one_838_ = lean_unsigned_to_nat(1u);
v_n_839_ = lean_nat_sub(v_x_834_, v_one_838_);
v___x_840_ = l_Lean_Level_ofNat(v_n_839_);
lean_dec(v_n_839_);
v___x_841_ = l_Lean_Level_succ___override(v___x_840_);
return v___x_841_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_ofNat___boxed(lean_object* v_x_842_){
_start:
{
lean_object* v_res_843_; 
v_res_843_ = l_Lean_Level_ofNat(v_x_842_);
lean_dec(v_x_842_);
return v_res_843_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_instOfNat(lean_object* v_n_844_){
_start:
{
lean_object* v___x_845_; 
v___x_845_ = l_Lean_Level_ofNat(v_n_844_);
return v___x_845_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_instOfNat___boxed(lean_object* v_n_846_){
_start:
{
lean_object* v_res_847_; 
v_res_847_ = l_Lean_Level_instOfNat(v_n_846_);
lean_dec(v_n_846_);
return v_res_847_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_addOffsetAux(lean_object* v_x_848_, lean_object* v_x_849_){
_start:
{
lean_object* v_zero_850_; uint8_t v_isZero_851_; 
v_zero_850_ = lean_unsigned_to_nat(0u);
v_isZero_851_ = lean_nat_dec_eq(v_x_848_, v_zero_850_);
if (v_isZero_851_ == 1)
{
lean_dec(v_x_848_);
return v_x_849_;
}
else
{
lean_object* v_one_852_; lean_object* v_n_853_; lean_object* v___x_854_; 
v_one_852_ = lean_unsigned_to_nat(1u);
v_n_853_ = lean_nat_sub(v_x_848_, v_one_852_);
lean_dec(v_x_848_);
v___x_854_ = l_Lean_Level_succ___override(v_x_849_);
v_x_848_ = v_n_853_;
v_x_849_ = v___x_854_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_addOffset(lean_object* v_u_856_, lean_object* v_n_857_){
_start:
{
lean_object* v___x_858_; 
v___x_858_ = l_Lean_Level_addOffsetAux(v_n_857_, v_u_856_);
return v___x_858_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_isExplicit(lean_object* v_x_859_){
_start:
{
switch(lean_obj_tag(v_x_859_))
{
case 0:
{
uint8_t v___x_860_; 
v___x_860_ = 1;
return v___x_860_;
}
case 1:
{
lean_object* v_a_861_; uint8_t v___x_862_; 
v_a_861_ = lean_ctor_get(v_x_859_, 0);
v___x_862_ = l_Lean_Level_hasMVar(v_a_861_);
if (v___x_862_ == 0)
{
uint8_t v___x_863_; 
v___x_863_ = l_Lean_Level_hasParam(v_a_861_);
if (v___x_863_ == 0)
{
v_x_859_ = v_a_861_;
goto _start;
}
else
{
return v___x_862_;
}
}
else
{
uint8_t v___x_865_; 
v___x_865_ = 0;
return v___x_865_;
}
}
default: 
{
uint8_t v___x_866_; 
v___x_866_ = 0;
return v___x_866_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_isExplicit___boxed(lean_object* v_x_867_){
_start:
{
uint8_t v_res_868_; lean_object* v_r_869_; 
v_res_868_ = l_Lean_Level_isExplicit(v_x_867_);
lean_dec(v_x_867_);
v_r_869_ = lean_box(v_res_868_);
return v_r_869_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_getOffsetAux(lean_object* v_x_870_, lean_object* v_x_871_){
_start:
{
if (lean_obj_tag(v_x_870_) == 1)
{
lean_object* v_a_872_; lean_object* v___x_873_; lean_object* v___x_874_; 
v_a_872_ = lean_ctor_get(v_x_870_, 0);
v___x_873_ = lean_unsigned_to_nat(1u);
v___x_874_ = lean_nat_add(v_x_871_, v___x_873_);
lean_dec(v_x_871_);
v_x_870_ = v_a_872_;
v_x_871_ = v___x_874_;
goto _start;
}
else
{
return v_x_871_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_getOffsetAux___boxed(lean_object* v_x_876_, lean_object* v_x_877_){
_start:
{
lean_object* v_res_878_; 
v_res_878_ = l_Lean_Level_getOffsetAux(v_x_876_, v_x_877_);
lean_dec(v_x_876_);
return v_res_878_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_getOffset(lean_object* v_lvl_879_){
_start:
{
lean_object* v___x_880_; lean_object* v___x_881_; 
v___x_880_ = lean_unsigned_to_nat(0u);
v___x_881_ = l_Lean_Level_getOffsetAux(v_lvl_879_, v___x_880_);
return v___x_881_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_getOffset___boxed(lean_object* v_lvl_882_){
_start:
{
lean_object* v_res_883_; 
v_res_883_ = l_Lean_Level_getOffset(v_lvl_882_);
lean_dec(v_lvl_882_);
return v_res_883_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_getLevelOffset(lean_object* v_x_884_){
_start:
{
if (lean_obj_tag(v_x_884_) == 1)
{
lean_object* v_a_885_; 
v_a_885_ = lean_ctor_get(v_x_884_, 0);
v_x_884_ = v_a_885_;
goto _start;
}
else
{
lean_inc(v_x_884_);
return v_x_884_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_getLevelOffset___boxed(lean_object* v_x_887_){
_start:
{
lean_object* v_res_888_; 
v_res_888_ = l_Lean_Level_getLevelOffset(v_x_887_);
lean_dec(v_x_887_);
return v_res_888_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_toNat(lean_object* v_lvl_889_){
_start:
{
lean_object* v___x_890_; 
v___x_890_ = l_Lean_Level_getLevelOffset(v_lvl_889_);
if (lean_obj_tag(v___x_890_) == 0)
{
lean_object* v___x_891_; lean_object* v___x_892_; 
v___x_891_ = l_Lean_Level_getOffset(v_lvl_889_);
v___x_892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_892_, 0, v___x_891_);
return v___x_892_;
}
else
{
lean_object* v___x_893_; 
lean_dec(v___x_890_);
v___x_893_ = lean_box(0);
return v___x_893_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_toNat___boxed(lean_object* v_lvl_894_){
_start:
{
lean_object* v_res_895_; 
v_res_895_ = l_Lean_Level_toNat(v_lvl_894_);
lean_dec(v_lvl_894_);
return v_res_895_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_beq___boxed(lean_object* v_a_898_, lean_object* v_b_899_){
_start:
{
uint8_t v_res_900_; lean_object* v_r_901_; 
v_res_900_ = lean_level_eq(v_a_898_, v_b_899_);
lean_dec(v_b_899_);
lean_dec(v_a_898_);
v_r_901_ = lean_box(v_res_900_);
return v_r_901_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_occurs(lean_object* v_x_904_, lean_object* v_x_905_){
_start:
{
switch(lean_obj_tag(v_x_905_))
{
case 1:
{
lean_object* v_a_906_; uint8_t v___x_907_; 
v_a_906_ = lean_ctor_get(v_x_905_, 0);
v___x_907_ = lean_level_eq(v_x_904_, v_x_905_);
if (v___x_907_ == 0)
{
v_x_905_ = v_a_906_;
goto _start;
}
else
{
return v___x_907_;
}
}
case 2:
{
lean_object* v_a_909_; lean_object* v_a_910_; uint8_t v___y_912_; uint8_t v___x_914_; 
v_a_909_ = lean_ctor_get(v_x_905_, 0);
v_a_910_ = lean_ctor_get(v_x_905_, 1);
v___x_914_ = lean_level_eq(v_x_904_, v_x_905_);
if (v___x_914_ == 0)
{
uint8_t v___x_915_; 
v___x_915_ = l_Lean_Level_occurs(v_x_904_, v_a_909_);
v___y_912_ = v___x_915_;
goto v___jp_911_;
}
else
{
v___y_912_ = v___x_914_;
goto v___jp_911_;
}
v___jp_911_:
{
if (v___y_912_ == 0)
{
v_x_905_ = v_a_910_;
goto _start;
}
else
{
return v___y_912_;
}
}
}
case 3:
{
lean_object* v_a_916_; lean_object* v_a_917_; uint8_t v___y_919_; uint8_t v___x_921_; 
v_a_916_ = lean_ctor_get(v_x_905_, 0);
v_a_917_ = lean_ctor_get(v_x_905_, 1);
v___x_921_ = lean_level_eq(v_x_904_, v_x_905_);
if (v___x_921_ == 0)
{
uint8_t v___x_922_; 
v___x_922_ = l_Lean_Level_occurs(v_x_904_, v_a_916_);
v___y_919_ = v___x_922_;
goto v___jp_918_;
}
else
{
v___y_919_ = v___x_921_;
goto v___jp_918_;
}
v___jp_918_:
{
if (v___y_919_ == 0)
{
v_x_905_ = v_a_917_;
goto _start;
}
else
{
return v___y_919_;
}
}
}
default: 
{
uint8_t v___x_923_; 
v___x_923_ = lean_level_eq(v_x_904_, v_x_905_);
return v___x_923_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_occurs___boxed(lean_object* v_x_924_, lean_object* v_x_925_){
_start:
{
uint8_t v_res_926_; lean_object* v_r_927_; 
v_res_926_ = l_Lean_Level_occurs(v_x_924_, v_x_925_);
lean_dec(v_x_925_);
lean_dec(v_x_924_);
v_r_927_ = lean_box(v_res_926_);
return v_r_927_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_ctorToNat(lean_object* v_x_928_){
_start:
{
switch(lean_obj_tag(v_x_928_))
{
case 0:
{
lean_object* v___x_929_; 
v___x_929_ = lean_unsigned_to_nat(0u);
return v___x_929_;
}
case 1:
{
lean_object* v___x_930_; 
v___x_930_ = lean_unsigned_to_nat(3u);
return v___x_930_;
}
case 2:
{
lean_object* v___x_931_; 
v___x_931_ = lean_unsigned_to_nat(4u);
return v___x_931_;
}
case 3:
{
lean_object* v___x_932_; 
v___x_932_ = lean_unsigned_to_nat(5u);
return v___x_932_;
}
case 4:
{
lean_object* v___x_933_; 
v___x_933_ = lean_unsigned_to_nat(1u);
return v___x_933_;
}
default: 
{
lean_object* v___x_934_; 
v___x_934_ = lean_unsigned_to_nat(2u);
return v___x_934_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_ctorToNat___boxed(lean_object* v_x_935_){
_start:
{
lean_object* v_res_936_; 
v_res_936_ = l_Lean_Level_ctorToNat(v_x_935_);
lean_dec(v_x_935_);
return v_res_936_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_normLtAux(lean_object* v_x_937_, lean_object* v_x_938_, lean_object* v_x_939_, lean_object* v_x_940_){
_start:
{
lean_object* v_l_u2081_942_; lean_object* v_k_u2081_943_; lean_object* v_l_u2082_944_; lean_object* v_k_u2082_945_; lean_object* v_l_u2081_950_; lean_object* v_k_u2081_951_; lean_object* v_l_u2082_952_; lean_object* v_k_u2082_953_; 
switch(lean_obj_tag(v_x_937_))
{
case 1:
{
lean_object* v_a_959_; lean_object* v___x_960_; lean_object* v___x_961_; 
v_a_959_ = lean_ctor_get(v_x_937_, 0);
v___x_960_ = lean_unsigned_to_nat(1u);
v___x_961_ = lean_nat_add(v_x_938_, v___x_960_);
lean_dec(v_x_938_);
v_x_937_ = v_a_959_;
v_x_938_ = v___x_961_;
goto _start;
}
case 2:
{
switch(lean_obj_tag(v_x_939_))
{
case 1:
{
lean_object* v_a_963_; 
v_a_963_ = lean_ctor_get(v_x_939_, 0);
v_l_u2081_942_ = v_x_937_;
v_k_u2081_943_ = v_x_938_;
v_l_u2082_944_ = v_a_963_;
v_k_u2082_945_ = v_x_940_;
goto v___jp_941_;
}
case 2:
{
lean_object* v_a_964_; lean_object* v_a_965_; lean_object* v_a_966_; lean_object* v_a_967_; uint8_t v___x_971_; 
v_a_964_ = lean_ctor_get(v_x_937_, 0);
v_a_965_ = lean_ctor_get(v_x_937_, 1);
v_a_966_ = lean_ctor_get(v_x_939_, 0);
v_a_967_ = lean_ctor_get(v_x_939_, 1);
v___x_971_ = lean_level_eq(v_x_937_, v_x_939_);
if (v___x_971_ == 0)
{
uint8_t v___x_972_; 
lean_dec(v_x_940_);
lean_dec(v_x_938_);
v___x_972_ = lean_level_eq(v_a_964_, v_a_966_);
if (v___x_972_ == 0)
{
goto v___jp_968_;
}
else
{
if (v___x_971_ == 0)
{
lean_object* v___x_973_; 
v___x_973_ = lean_unsigned_to_nat(0u);
v_x_937_ = v_a_965_;
v_x_938_ = v___x_973_;
v_x_939_ = v_a_967_;
v_x_940_ = v___x_973_;
goto _start;
}
else
{
goto v___jp_968_;
}
}
}
else
{
uint8_t v___x_975_; 
v___x_975_ = lean_nat_dec_lt(v_x_938_, v_x_940_);
lean_dec(v_x_940_);
lean_dec(v_x_938_);
return v___x_975_;
}
v___jp_968_:
{
lean_object* v___x_969_; 
v___x_969_ = lean_unsigned_to_nat(0u);
v_x_937_ = v_a_964_;
v_x_938_ = v___x_969_;
v_x_939_ = v_a_966_;
v_x_940_ = v___x_969_;
goto _start;
}
}
default: 
{
v_l_u2081_950_ = v_x_937_;
v_k_u2081_951_ = v_x_938_;
v_l_u2082_952_ = v_x_939_;
v_k_u2082_953_ = v_x_940_;
goto v___jp_949_;
}
}
}
case 3:
{
switch(lean_obj_tag(v_x_939_))
{
case 1:
{
lean_object* v_a_976_; 
v_a_976_ = lean_ctor_get(v_x_939_, 0);
v_l_u2081_942_ = v_x_937_;
v_k_u2081_943_ = v_x_938_;
v_l_u2082_944_ = v_a_976_;
v_k_u2082_945_ = v_x_940_;
goto v___jp_941_;
}
case 3:
{
lean_object* v_a_977_; lean_object* v_a_978_; lean_object* v_a_979_; lean_object* v_a_980_; uint8_t v___x_984_; 
v_a_977_ = lean_ctor_get(v_x_937_, 0);
v_a_978_ = lean_ctor_get(v_x_937_, 1);
v_a_979_ = lean_ctor_get(v_x_939_, 0);
v_a_980_ = lean_ctor_get(v_x_939_, 1);
v___x_984_ = lean_level_eq(v_x_937_, v_x_939_);
if (v___x_984_ == 0)
{
uint8_t v___x_985_; 
lean_dec(v_x_940_);
lean_dec(v_x_938_);
v___x_985_ = lean_level_eq(v_a_977_, v_a_979_);
if (v___x_985_ == 0)
{
goto v___jp_981_;
}
else
{
if (v___x_984_ == 0)
{
lean_object* v___x_986_; 
v___x_986_ = lean_unsigned_to_nat(0u);
v_x_937_ = v_a_978_;
v_x_938_ = v___x_986_;
v_x_939_ = v_a_980_;
v_x_940_ = v___x_986_;
goto _start;
}
else
{
goto v___jp_981_;
}
}
}
else
{
uint8_t v___x_988_; 
v___x_988_ = lean_nat_dec_lt(v_x_938_, v_x_940_);
lean_dec(v_x_940_);
lean_dec(v_x_938_);
return v___x_988_;
}
v___jp_981_:
{
lean_object* v___x_982_; 
v___x_982_ = lean_unsigned_to_nat(0u);
v_x_937_ = v_a_977_;
v_x_938_ = v___x_982_;
v_x_939_ = v_a_979_;
v_x_940_ = v___x_982_;
goto _start;
}
}
default: 
{
v_l_u2081_950_ = v_x_937_;
v_k_u2081_951_ = v_x_938_;
v_l_u2082_952_ = v_x_939_;
v_k_u2082_953_ = v_x_940_;
goto v___jp_949_;
}
}
}
case 4:
{
switch(lean_obj_tag(v_x_939_))
{
case 1:
{
lean_object* v_a_989_; 
v_a_989_ = lean_ctor_get(v_x_939_, 0);
v_l_u2081_942_ = v_x_937_;
v_k_u2081_943_ = v_x_938_;
v_l_u2082_944_ = v_a_989_;
v_k_u2082_945_ = v_x_940_;
goto v___jp_941_;
}
case 4:
{
lean_object* v_a_990_; lean_object* v_a_991_; uint8_t v___x_992_; 
v_a_990_ = lean_ctor_get(v_x_937_, 0);
v_a_991_ = lean_ctor_get(v_x_939_, 0);
v___x_992_ = lean_name_eq(v_a_990_, v_a_991_);
if (v___x_992_ == 0)
{
uint8_t v___x_993_; 
lean_dec(v_x_940_);
lean_dec(v_x_938_);
v___x_993_ = l_Lean_Name_lt(v_a_990_, v_a_991_);
return v___x_993_;
}
else
{
uint8_t v___x_994_; 
v___x_994_ = lean_nat_dec_lt(v_x_938_, v_x_940_);
lean_dec(v_x_940_);
lean_dec(v_x_938_);
return v___x_994_;
}
}
default: 
{
v_l_u2081_950_ = v_x_937_;
v_k_u2081_951_ = v_x_938_;
v_l_u2082_952_ = v_x_939_;
v_k_u2082_953_ = v_x_940_;
goto v___jp_949_;
}
}
}
case 5:
{
switch(lean_obj_tag(v_x_939_))
{
case 1:
{
lean_object* v_a_995_; 
v_a_995_ = lean_ctor_get(v_x_939_, 0);
v_l_u2081_942_ = v_x_937_;
v_k_u2081_943_ = v_x_938_;
v_l_u2082_944_ = v_a_995_;
v_k_u2082_945_ = v_x_940_;
goto v___jp_941_;
}
case 5:
{
lean_object* v_a_996_; lean_object* v_a_997_; uint8_t v___x_998_; 
v_a_996_ = lean_ctor_get(v_x_937_, 0);
v_a_997_ = lean_ctor_get(v_x_939_, 0);
v___x_998_ = lean_name_eq(v_a_996_, v_a_997_);
if (v___x_998_ == 0)
{
uint8_t v___x_999_; 
lean_dec(v_x_940_);
lean_dec(v_x_938_);
v___x_999_ = l_Lean_Name_lt(v_a_996_, v_a_997_);
return v___x_999_;
}
else
{
uint8_t v___x_1000_; 
v___x_1000_ = lean_nat_dec_lt(v_x_938_, v_x_940_);
lean_dec(v_x_940_);
lean_dec(v_x_938_);
return v___x_1000_;
}
}
default: 
{
v_l_u2081_950_ = v_x_937_;
v_k_u2081_951_ = v_x_938_;
v_l_u2082_952_ = v_x_939_;
v_k_u2082_953_ = v_x_940_;
goto v___jp_949_;
}
}
}
default: 
{
if (lean_obj_tag(v_x_939_) == 1)
{
lean_object* v_a_1001_; 
v_a_1001_ = lean_ctor_get(v_x_939_, 0);
v_l_u2081_942_ = v_x_937_;
v_k_u2081_943_ = v_x_938_;
v_l_u2082_944_ = v_a_1001_;
v_k_u2082_945_ = v_x_940_;
goto v___jp_941_;
}
else
{
v_l_u2081_950_ = v_x_937_;
v_k_u2081_951_ = v_x_938_;
v_l_u2082_952_ = v_x_939_;
v_k_u2082_953_ = v_x_940_;
goto v___jp_949_;
}
}
}
v___jp_941_:
{
lean_object* v___x_946_; lean_object* v___x_947_; 
v___x_946_ = lean_unsigned_to_nat(1u);
v___x_947_ = lean_nat_add(v_k_u2082_945_, v___x_946_);
lean_dec(v_k_u2082_945_);
v_x_937_ = v_l_u2081_942_;
v_x_938_ = v_k_u2081_943_;
v_x_939_ = v_l_u2082_944_;
v_x_940_ = v___x_947_;
goto _start;
}
v___jp_949_:
{
uint8_t v___x_954_; 
v___x_954_ = lean_level_eq(v_l_u2081_950_, v_l_u2082_952_);
if (v___x_954_ == 0)
{
lean_object* v___x_955_; lean_object* v___x_956_; uint8_t v___x_957_; 
lean_dec(v_k_u2082_953_);
lean_dec(v_k_u2081_951_);
v___x_955_ = l_Lean_Level_ctorToNat(v_l_u2081_950_);
v___x_956_ = l_Lean_Level_ctorToNat(v_l_u2082_952_);
v___x_957_ = lean_nat_dec_lt(v___x_955_, v___x_956_);
lean_dec(v___x_956_);
lean_dec(v___x_955_);
return v___x_957_;
}
else
{
uint8_t v___x_958_; 
v___x_958_ = lean_nat_dec_lt(v_k_u2081_951_, v_k_u2082_953_);
lean_dec(v_k_u2082_953_);
lean_dec(v_k_u2081_951_);
return v___x_958_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_normLtAux___boxed(lean_object* v_x_1002_, lean_object* v_x_1003_, lean_object* v_x_1004_, lean_object* v_x_1005_){
_start:
{
uint8_t v_res_1006_; lean_object* v_r_1007_; 
v_res_1006_ = l_Lean_Level_normLtAux(v_x_1002_, v_x_1003_, v_x_1004_, v_x_1005_);
lean_dec(v_x_1004_);
lean_dec(v_x_1002_);
v_r_1007_ = lean_box(v_res_1006_);
return v_r_1007_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_normLtAux_match__1_splitter___redArg(lean_object* v_x_1008_, lean_object* v_x_1009_, lean_object* v_x_1010_, lean_object* v_x_1011_, lean_object* v_h__1_1012_, lean_object* v_h__2_1013_, lean_object* v_h__3_1014_, lean_object* v_h__4_1015_, lean_object* v_h__5_1016_, lean_object* v_h__6_1017_, lean_object* v_h__7_1018_){
_start:
{
switch(lean_obj_tag(v_x_1008_))
{
case 1:
{
lean_object* v_a_1019_; lean_object* v___x_1020_; 
lean_dec(v_h__7_1018_);
lean_dec(v_h__6_1017_);
lean_dec(v_h__5_1016_);
lean_dec(v_h__4_1015_);
lean_dec(v_h__3_1014_);
lean_dec(v_h__2_1013_);
v_a_1019_ = lean_ctor_get(v_x_1008_, 0);
lean_inc(v_a_1019_);
lean_dec_ref(v_x_1008_);
v___x_1020_ = lean_apply_4(v_h__1_1012_, v_a_1019_, v_x_1009_, v_x_1010_, v_x_1011_);
return v___x_1020_;
}
case 2:
{
lean_dec(v_h__6_1017_);
lean_dec(v_h__5_1016_);
lean_dec(v_h__4_1015_);
lean_dec(v_h__1_1012_);
switch(lean_obj_tag(v_x_1010_))
{
case 1:
{
lean_object* v_a_1021_; lean_object* v___x_1022_; 
lean_dec(v_h__7_1018_);
lean_dec(v_h__3_1014_);
v_a_1021_ = lean_ctor_get(v_x_1010_, 0);
lean_inc(v_a_1021_);
lean_dec_ref(v_x_1010_);
v___x_1022_ = lean_apply_5(v_h__2_1013_, v_x_1008_, v_x_1009_, v_a_1021_, v_x_1011_, lean_box(0));
return v___x_1022_;
}
case 2:
{
lean_object* v_a_1023_; lean_object* v_a_1024_; lean_object* v_a_1025_; lean_object* v_a_1026_; lean_object* v___x_1027_; 
lean_dec(v_h__7_1018_);
lean_dec(v_h__2_1013_);
v_a_1023_ = lean_ctor_get(v_x_1008_, 0);
lean_inc(v_a_1023_);
v_a_1024_ = lean_ctor_get(v_x_1008_, 1);
lean_inc(v_a_1024_);
lean_dec_ref(v_x_1008_);
v_a_1025_ = lean_ctor_get(v_x_1010_, 0);
lean_inc(v_a_1025_);
v_a_1026_ = lean_ctor_get(v_x_1010_, 1);
lean_inc(v_a_1026_);
lean_dec_ref(v_x_1010_);
v___x_1027_ = lean_apply_6(v_h__3_1014_, v_a_1023_, v_a_1024_, v_x_1009_, v_a_1025_, v_a_1026_, v_x_1011_);
return v___x_1027_;
}
default: 
{
lean_object* v___x_1028_; 
lean_dec(v_h__3_1014_);
lean_dec(v_h__2_1013_);
v___x_1028_ = lean_apply_10(v_h__7_1018_, v_x_1008_, v_x_1009_, v_x_1010_, v_x_1011_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_1028_;
}
}
}
case 3:
{
lean_dec(v_h__6_1017_);
lean_dec(v_h__5_1016_);
lean_dec(v_h__3_1014_);
lean_dec(v_h__1_1012_);
switch(lean_obj_tag(v_x_1010_))
{
case 1:
{
lean_object* v_a_1029_; lean_object* v___x_1030_; 
lean_dec(v_h__7_1018_);
lean_dec(v_h__4_1015_);
v_a_1029_ = lean_ctor_get(v_x_1010_, 0);
lean_inc(v_a_1029_);
lean_dec_ref(v_x_1010_);
v___x_1030_ = lean_apply_5(v_h__2_1013_, v_x_1008_, v_x_1009_, v_a_1029_, v_x_1011_, lean_box(0));
return v___x_1030_;
}
case 3:
{
lean_object* v_a_1031_; lean_object* v_a_1032_; lean_object* v_a_1033_; lean_object* v_a_1034_; lean_object* v___x_1035_; 
lean_dec(v_h__7_1018_);
lean_dec(v_h__2_1013_);
v_a_1031_ = lean_ctor_get(v_x_1008_, 0);
lean_inc(v_a_1031_);
v_a_1032_ = lean_ctor_get(v_x_1008_, 1);
lean_inc(v_a_1032_);
lean_dec_ref(v_x_1008_);
v_a_1033_ = lean_ctor_get(v_x_1010_, 0);
lean_inc(v_a_1033_);
v_a_1034_ = lean_ctor_get(v_x_1010_, 1);
lean_inc(v_a_1034_);
lean_dec_ref(v_x_1010_);
v___x_1035_ = lean_apply_6(v_h__4_1015_, v_a_1031_, v_a_1032_, v_x_1009_, v_a_1033_, v_a_1034_, v_x_1011_);
return v___x_1035_;
}
default: 
{
lean_object* v___x_1036_; 
lean_dec(v_h__4_1015_);
lean_dec(v_h__2_1013_);
v___x_1036_ = lean_apply_10(v_h__7_1018_, v_x_1008_, v_x_1009_, v_x_1010_, v_x_1011_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_1036_;
}
}
}
case 4:
{
lean_dec(v_h__6_1017_);
lean_dec(v_h__4_1015_);
lean_dec(v_h__3_1014_);
lean_dec(v_h__1_1012_);
switch(lean_obj_tag(v_x_1010_))
{
case 1:
{
lean_object* v_a_1037_; lean_object* v___x_1038_; 
lean_dec(v_h__7_1018_);
lean_dec(v_h__5_1016_);
v_a_1037_ = lean_ctor_get(v_x_1010_, 0);
lean_inc(v_a_1037_);
lean_dec_ref(v_x_1010_);
v___x_1038_ = lean_apply_5(v_h__2_1013_, v_x_1008_, v_x_1009_, v_a_1037_, v_x_1011_, lean_box(0));
return v___x_1038_;
}
case 4:
{
lean_object* v_a_1039_; lean_object* v_a_1040_; lean_object* v___x_1041_; 
lean_dec(v_h__7_1018_);
lean_dec(v_h__2_1013_);
v_a_1039_ = lean_ctor_get(v_x_1008_, 0);
lean_inc(v_a_1039_);
lean_dec_ref(v_x_1008_);
v_a_1040_ = lean_ctor_get(v_x_1010_, 0);
lean_inc(v_a_1040_);
lean_dec_ref(v_x_1010_);
v___x_1041_ = lean_apply_4(v_h__5_1016_, v_a_1039_, v_x_1009_, v_a_1040_, v_x_1011_);
return v___x_1041_;
}
default: 
{
lean_object* v___x_1042_; 
lean_dec(v_h__5_1016_);
lean_dec(v_h__2_1013_);
v___x_1042_ = lean_apply_10(v_h__7_1018_, v_x_1008_, v_x_1009_, v_x_1010_, v_x_1011_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_1042_;
}
}
}
case 5:
{
lean_dec(v_h__5_1016_);
lean_dec(v_h__4_1015_);
lean_dec(v_h__3_1014_);
lean_dec(v_h__1_1012_);
switch(lean_obj_tag(v_x_1010_))
{
case 1:
{
lean_object* v_a_1043_; lean_object* v___x_1044_; 
lean_dec(v_h__7_1018_);
lean_dec(v_h__6_1017_);
v_a_1043_ = lean_ctor_get(v_x_1010_, 0);
lean_inc(v_a_1043_);
lean_dec_ref(v_x_1010_);
v___x_1044_ = lean_apply_5(v_h__2_1013_, v_x_1008_, v_x_1009_, v_a_1043_, v_x_1011_, lean_box(0));
return v___x_1044_;
}
case 5:
{
lean_object* v_a_1045_; lean_object* v_a_1046_; lean_object* v___x_1047_; 
lean_dec(v_h__7_1018_);
lean_dec(v_h__2_1013_);
v_a_1045_ = lean_ctor_get(v_x_1008_, 0);
lean_inc(v_a_1045_);
lean_dec_ref(v_x_1008_);
v_a_1046_ = lean_ctor_get(v_x_1010_, 0);
lean_inc(v_a_1046_);
lean_dec_ref(v_x_1010_);
v___x_1047_ = lean_apply_4(v_h__6_1017_, v_a_1045_, v_x_1009_, v_a_1046_, v_x_1011_);
return v___x_1047_;
}
default: 
{
lean_object* v___x_1048_; 
lean_dec(v_h__6_1017_);
lean_dec(v_h__2_1013_);
v___x_1048_ = lean_apply_10(v_h__7_1018_, v_x_1008_, v_x_1009_, v_x_1010_, v_x_1011_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_1048_;
}
}
}
default: 
{
lean_dec(v_h__6_1017_);
lean_dec(v_h__5_1016_);
lean_dec(v_h__4_1015_);
lean_dec(v_h__3_1014_);
lean_dec(v_h__1_1012_);
if (lean_obj_tag(v_x_1010_) == 1)
{
lean_object* v_a_1049_; lean_object* v___x_1050_; 
lean_dec(v_h__7_1018_);
v_a_1049_ = lean_ctor_get(v_x_1010_, 0);
lean_inc(v_a_1049_);
lean_dec_ref(v_x_1010_);
v___x_1050_ = lean_apply_5(v_h__2_1013_, v_x_1008_, v_x_1009_, v_a_1049_, v_x_1011_, lean_box(0));
return v___x_1050_;
}
else
{
lean_object* v___x_1051_; 
lean_dec(v_h__2_1013_);
v___x_1051_ = lean_apply_10(v_h__7_1018_, v_x_1008_, v_x_1009_, v_x_1010_, v_x_1011_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_1051_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_normLtAux_match__1_splitter(lean_object* v_motive_1052_, lean_object* v_x_1053_, lean_object* v_x_1054_, lean_object* v_x_1055_, lean_object* v_x_1056_, lean_object* v_h__1_1057_, lean_object* v_h__2_1058_, lean_object* v_h__3_1059_, lean_object* v_h__4_1060_, lean_object* v_h__5_1061_, lean_object* v_h__6_1062_, lean_object* v_h__7_1063_){
_start:
{
switch(lean_obj_tag(v_x_1053_))
{
case 1:
{
lean_object* v_a_1064_; lean_object* v___x_1065_; 
lean_dec(v_h__7_1063_);
lean_dec(v_h__6_1062_);
lean_dec(v_h__5_1061_);
lean_dec(v_h__4_1060_);
lean_dec(v_h__3_1059_);
lean_dec(v_h__2_1058_);
v_a_1064_ = lean_ctor_get(v_x_1053_, 0);
lean_inc(v_a_1064_);
lean_dec_ref(v_x_1053_);
v___x_1065_ = lean_apply_4(v_h__1_1057_, v_a_1064_, v_x_1054_, v_x_1055_, v_x_1056_);
return v___x_1065_;
}
case 2:
{
lean_dec(v_h__6_1062_);
lean_dec(v_h__5_1061_);
lean_dec(v_h__4_1060_);
lean_dec(v_h__1_1057_);
switch(lean_obj_tag(v_x_1055_))
{
case 1:
{
lean_object* v_a_1066_; lean_object* v___x_1067_; 
lean_dec(v_h__7_1063_);
lean_dec(v_h__3_1059_);
v_a_1066_ = lean_ctor_get(v_x_1055_, 0);
lean_inc(v_a_1066_);
lean_dec_ref(v_x_1055_);
v___x_1067_ = lean_apply_5(v_h__2_1058_, v_x_1053_, v_x_1054_, v_a_1066_, v_x_1056_, lean_box(0));
return v___x_1067_;
}
case 2:
{
lean_object* v_a_1068_; lean_object* v_a_1069_; lean_object* v_a_1070_; lean_object* v_a_1071_; lean_object* v___x_1072_; 
lean_dec(v_h__7_1063_);
lean_dec(v_h__2_1058_);
v_a_1068_ = lean_ctor_get(v_x_1053_, 0);
lean_inc(v_a_1068_);
v_a_1069_ = lean_ctor_get(v_x_1053_, 1);
lean_inc(v_a_1069_);
lean_dec_ref(v_x_1053_);
v_a_1070_ = lean_ctor_get(v_x_1055_, 0);
lean_inc(v_a_1070_);
v_a_1071_ = lean_ctor_get(v_x_1055_, 1);
lean_inc(v_a_1071_);
lean_dec_ref(v_x_1055_);
v___x_1072_ = lean_apply_6(v_h__3_1059_, v_a_1068_, v_a_1069_, v_x_1054_, v_a_1070_, v_a_1071_, v_x_1056_);
return v___x_1072_;
}
default: 
{
lean_object* v___x_1073_; 
lean_dec(v_h__3_1059_);
lean_dec(v_h__2_1058_);
v___x_1073_ = lean_apply_10(v_h__7_1063_, v_x_1053_, v_x_1054_, v_x_1055_, v_x_1056_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_1073_;
}
}
}
case 3:
{
lean_dec(v_h__6_1062_);
lean_dec(v_h__5_1061_);
lean_dec(v_h__3_1059_);
lean_dec(v_h__1_1057_);
switch(lean_obj_tag(v_x_1055_))
{
case 1:
{
lean_object* v_a_1074_; lean_object* v___x_1075_; 
lean_dec(v_h__7_1063_);
lean_dec(v_h__4_1060_);
v_a_1074_ = lean_ctor_get(v_x_1055_, 0);
lean_inc(v_a_1074_);
lean_dec_ref(v_x_1055_);
v___x_1075_ = lean_apply_5(v_h__2_1058_, v_x_1053_, v_x_1054_, v_a_1074_, v_x_1056_, lean_box(0));
return v___x_1075_;
}
case 3:
{
lean_object* v_a_1076_; lean_object* v_a_1077_; lean_object* v_a_1078_; lean_object* v_a_1079_; lean_object* v___x_1080_; 
lean_dec(v_h__7_1063_);
lean_dec(v_h__2_1058_);
v_a_1076_ = lean_ctor_get(v_x_1053_, 0);
lean_inc(v_a_1076_);
v_a_1077_ = lean_ctor_get(v_x_1053_, 1);
lean_inc(v_a_1077_);
lean_dec_ref(v_x_1053_);
v_a_1078_ = lean_ctor_get(v_x_1055_, 0);
lean_inc(v_a_1078_);
v_a_1079_ = lean_ctor_get(v_x_1055_, 1);
lean_inc(v_a_1079_);
lean_dec_ref(v_x_1055_);
v___x_1080_ = lean_apply_6(v_h__4_1060_, v_a_1076_, v_a_1077_, v_x_1054_, v_a_1078_, v_a_1079_, v_x_1056_);
return v___x_1080_;
}
default: 
{
lean_object* v___x_1081_; 
lean_dec(v_h__4_1060_);
lean_dec(v_h__2_1058_);
v___x_1081_ = lean_apply_10(v_h__7_1063_, v_x_1053_, v_x_1054_, v_x_1055_, v_x_1056_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_1081_;
}
}
}
case 4:
{
lean_dec(v_h__6_1062_);
lean_dec(v_h__4_1060_);
lean_dec(v_h__3_1059_);
lean_dec(v_h__1_1057_);
switch(lean_obj_tag(v_x_1055_))
{
case 1:
{
lean_object* v_a_1082_; lean_object* v___x_1083_; 
lean_dec(v_h__7_1063_);
lean_dec(v_h__5_1061_);
v_a_1082_ = lean_ctor_get(v_x_1055_, 0);
lean_inc(v_a_1082_);
lean_dec_ref(v_x_1055_);
v___x_1083_ = lean_apply_5(v_h__2_1058_, v_x_1053_, v_x_1054_, v_a_1082_, v_x_1056_, lean_box(0));
return v___x_1083_;
}
case 4:
{
lean_object* v_a_1084_; lean_object* v_a_1085_; lean_object* v___x_1086_; 
lean_dec(v_h__7_1063_);
lean_dec(v_h__2_1058_);
v_a_1084_ = lean_ctor_get(v_x_1053_, 0);
lean_inc(v_a_1084_);
lean_dec_ref(v_x_1053_);
v_a_1085_ = lean_ctor_get(v_x_1055_, 0);
lean_inc(v_a_1085_);
lean_dec_ref(v_x_1055_);
v___x_1086_ = lean_apply_4(v_h__5_1061_, v_a_1084_, v_x_1054_, v_a_1085_, v_x_1056_);
return v___x_1086_;
}
default: 
{
lean_object* v___x_1087_; 
lean_dec(v_h__5_1061_);
lean_dec(v_h__2_1058_);
v___x_1087_ = lean_apply_10(v_h__7_1063_, v_x_1053_, v_x_1054_, v_x_1055_, v_x_1056_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_1087_;
}
}
}
case 5:
{
lean_dec(v_h__5_1061_);
lean_dec(v_h__4_1060_);
lean_dec(v_h__3_1059_);
lean_dec(v_h__1_1057_);
switch(lean_obj_tag(v_x_1055_))
{
case 1:
{
lean_object* v_a_1088_; lean_object* v___x_1089_; 
lean_dec(v_h__7_1063_);
lean_dec(v_h__6_1062_);
v_a_1088_ = lean_ctor_get(v_x_1055_, 0);
lean_inc(v_a_1088_);
lean_dec_ref(v_x_1055_);
v___x_1089_ = lean_apply_5(v_h__2_1058_, v_x_1053_, v_x_1054_, v_a_1088_, v_x_1056_, lean_box(0));
return v___x_1089_;
}
case 5:
{
lean_object* v_a_1090_; lean_object* v_a_1091_; lean_object* v___x_1092_; 
lean_dec(v_h__7_1063_);
lean_dec(v_h__2_1058_);
v_a_1090_ = lean_ctor_get(v_x_1053_, 0);
lean_inc(v_a_1090_);
lean_dec_ref(v_x_1053_);
v_a_1091_ = lean_ctor_get(v_x_1055_, 0);
lean_inc(v_a_1091_);
lean_dec_ref(v_x_1055_);
v___x_1092_ = lean_apply_4(v_h__6_1062_, v_a_1090_, v_x_1054_, v_a_1091_, v_x_1056_);
return v___x_1092_;
}
default: 
{
lean_object* v___x_1093_; 
lean_dec(v_h__6_1062_);
lean_dec(v_h__2_1058_);
v___x_1093_ = lean_apply_10(v_h__7_1063_, v_x_1053_, v_x_1054_, v_x_1055_, v_x_1056_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_1093_;
}
}
}
default: 
{
lean_dec(v_h__6_1062_);
lean_dec(v_h__5_1061_);
lean_dec(v_h__4_1060_);
lean_dec(v_h__3_1059_);
lean_dec(v_h__1_1057_);
if (lean_obj_tag(v_x_1055_) == 1)
{
lean_object* v_a_1094_; lean_object* v___x_1095_; 
lean_dec(v_h__7_1063_);
v_a_1094_ = lean_ctor_get(v_x_1055_, 0);
lean_inc(v_a_1094_);
lean_dec_ref(v_x_1055_);
v___x_1095_ = lean_apply_5(v_h__2_1058_, v_x_1053_, v_x_1054_, v_a_1094_, v_x_1056_, lean_box(0));
return v___x_1095_;
}
else
{
lean_object* v___x_1096_; 
lean_dec(v_h__2_1058_);
v___x_1096_ = lean_apply_10(v_h__7_1063_, v_x_1053_, v_x_1054_, v_x_1055_, v_x_1056_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_1096_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Level_normLt(lean_object* v_l_u2081_1097_, lean_object* v_l_u2082_1098_){
_start:
{
lean_object* v___x_1099_; uint8_t v___x_1100_; 
v___x_1099_ = lean_unsigned_to_nat(0u);
v___x_1100_ = l_Lean_Level_normLtAux(v_l_u2081_1097_, v___x_1099_, v_l_u2082_1098_, v___x_1099_);
return v___x_1100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_normLt___boxed(lean_object* v_l_u2081_1101_, lean_object* v_l_u2082_1102_){
_start:
{
uint8_t v_res_1103_; lean_object* v_r_1104_; 
v_res_1103_ = l_Lean_Level_normLt(v_l_u2081_1101_, v_l_u2082_1102_);
lean_dec(v_l_u2082_1102_);
lean_dec(v_l_u2081_1101_);
v_r_1104_ = lean_box(v_res_1103_);
return v_r_1104_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_isAlreadyNormalizedCheap(lean_object* v_x_1105_){
_start:
{
switch(lean_obj_tag(v_x_1105_))
{
case 0:
{
uint8_t v___x_1106_; 
v___x_1106_ = 1;
return v___x_1106_;
}
case 4:
{
uint8_t v___x_1107_; 
v___x_1107_ = 1;
return v___x_1107_;
}
case 5:
{
uint8_t v___x_1108_; 
v___x_1108_ = 1;
return v___x_1108_;
}
case 1:
{
lean_object* v_a_1109_; 
v_a_1109_ = lean_ctor_get(v_x_1105_, 0);
v_x_1105_ = v_a_1109_;
goto _start;
}
default: 
{
uint8_t v___x_1111_; 
v___x_1111_ = 0;
return v___x_1111_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_isAlreadyNormalizedCheap___boxed(lean_object* v_x_1112_){
_start:
{
uint8_t v_res_1113_; lean_object* v_r_1114_; 
v_res_1113_ = l_Lean_Level_isAlreadyNormalizedCheap(v_x_1112_);
lean_dec(v_x_1112_);
v_r_1114_ = lean_box(v_res_1113_);
return v_r_1114_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_mkIMaxAux(lean_object* v_x_1115_, lean_object* v_x_1116_){
_start:
{
lean_object* v_u_u2081_1118_; lean_object* v_u_u2082_1119_; 
if (lean_obj_tag(v_x_1116_) == 0)
{
lean_dec(v_x_1115_);
return v_x_1116_;
}
else
{
switch(lean_obj_tag(v_x_1115_))
{
case 0:
{
return v_x_1116_;
}
case 1:
{
lean_object* v_a_1122_; 
v_a_1122_ = lean_ctor_get(v_x_1115_, 0);
if (lean_obj_tag(v_a_1122_) == 0)
{
lean_dec_ref(v_x_1115_);
return v_x_1116_;
}
else
{
v_u_u2081_1118_ = v_x_1115_;
v_u_u2082_1119_ = v_x_1116_;
goto v___jp_1117_;
}
}
default: 
{
v_u_u2081_1118_ = v_x_1115_;
v_u_u2082_1119_ = v_x_1116_;
goto v___jp_1117_;
}
}
}
v___jp_1117_:
{
uint8_t v___x_1120_; 
v___x_1120_ = lean_level_eq(v_u_u2081_1118_, v_u_u2082_1119_);
if (v___x_1120_ == 0)
{
lean_object* v___x_1121_; 
v___x_1121_ = l_Lean_Level_imax___override(v_u_u2081_1118_, v_u_u2082_1119_);
return v___x_1121_;
}
else
{
lean_dec(v_u_u2082_1119_);
return v_u_u2081_1118_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_getMaxArgsAux(lean_object* v_normalize_1123_, lean_object* v_x_1124_, uint8_t v_x_1125_, lean_object* v_x_1126_){
_start:
{
if (lean_obj_tag(v_x_1124_) == 2)
{
lean_object* v_a_1127_; lean_object* v_a_1128_; lean_object* v___x_1129_; 
v_a_1127_ = lean_ctor_get(v_x_1124_, 0);
lean_inc(v_a_1127_);
v_a_1128_ = lean_ctor_get(v_x_1124_, 1);
lean_inc(v_a_1128_);
lean_dec_ref(v_x_1124_);
lean_inc_ref(v_normalize_1123_);
v___x_1129_ = l___private_Lean_Level_0__Lean_Level_getMaxArgsAux(v_normalize_1123_, v_a_1127_, v_x_1125_, v_x_1126_);
v_x_1124_ = v_a_1128_;
v_x_1126_ = v___x_1129_;
goto _start;
}
else
{
if (v_x_1125_ == 0)
{
lean_object* v___x_1131_; uint8_t v___x_1132_; 
lean_inc_ref(v_normalize_1123_);
v___x_1131_ = lean_apply_1(v_normalize_1123_, v_x_1124_);
v___x_1132_ = 1;
v_x_1124_ = v___x_1131_;
v_x_1125_ = v___x_1132_;
goto _start;
}
else
{
lean_object* v___x_1134_; 
lean_dec_ref(v_normalize_1123_);
v___x_1134_ = lean_array_push(v_x_1126_, v_x_1124_);
return v___x_1134_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_getMaxArgsAux___boxed(lean_object* v_normalize_1135_, lean_object* v_x_1136_, lean_object* v_x_1137_, lean_object* v_x_1138_){
_start:
{
uint8_t v_x_36__boxed_1139_; lean_object* v_res_1140_; 
v_x_36__boxed_1139_ = lean_unbox(v_x_1137_);
v_res_1140_ = l___private_Lean_Level_0__Lean_Level_getMaxArgsAux(v_normalize_1135_, v_x_1136_, v_x_36__boxed_1139_, v_x_1138_);
return v_res_1140_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_accMax(lean_object* v_result_1141_, lean_object* v_prev_1142_, lean_object* v_offset_1143_){
_start:
{
uint8_t v___x_1144_; 
v___x_1144_ = l_Lean_Level_isZero(v_result_1141_);
if (v___x_1144_ == 0)
{
lean_object* v___x_1145_; lean_object* v___x_1146_; 
v___x_1145_ = l_Lean_Level_addOffsetAux(v_offset_1143_, v_prev_1142_);
v___x_1146_ = l_Lean_Level_max___override(v_result_1141_, v___x_1145_);
return v___x_1146_;
}
else
{
lean_object* v___x_1147_; 
lean_dec(v_result_1141_);
v___x_1147_ = l_Lean_Level_addOffsetAux(v_offset_1143_, v_prev_1142_);
return v___x_1147_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_mkMaxAux(lean_object* v_lvls_1148_, lean_object* v_extraK_1149_, lean_object* v_i_1150_, lean_object* v_prev_1151_, lean_object* v_prevK_1152_, lean_object* v_result_1153_){
_start:
{
lean_object* v___x_1154_; uint8_t v___x_1155_; 
v___x_1154_ = lean_array_get_size(v_lvls_1148_);
v___x_1155_ = lean_nat_dec_lt(v_i_1150_, v___x_1154_);
if (v___x_1155_ == 0)
{
lean_object* v___x_1156_; lean_object* v___x_1157_; 
lean_dec(v_i_1150_);
v___x_1156_ = lean_nat_add(v_extraK_1149_, v_prevK_1152_);
lean_dec(v_prevK_1152_);
v___x_1157_ = l___private_Lean_Level_0__Lean_Level_accMax(v_result_1153_, v_prev_1151_, v___x_1156_);
return v___x_1157_;
}
else
{
lean_object* v_lvl_1158_; lean_object* v_curr_1159_; lean_object* v_currK_1160_; uint8_t v___x_1161_; 
v_lvl_1158_ = lean_array_fget_borrowed(v_lvls_1148_, v_i_1150_);
v_curr_1159_ = l_Lean_Level_getLevelOffset(v_lvl_1158_);
v_currK_1160_ = l_Lean_Level_getOffset(v_lvl_1158_);
v___x_1161_ = lean_level_eq(v_curr_1159_, v_prev_1151_);
if (v___x_1161_ == 0)
{
lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; 
v___x_1162_ = lean_unsigned_to_nat(1u);
v___x_1163_ = lean_nat_add(v_i_1150_, v___x_1162_);
lean_dec(v_i_1150_);
v___x_1164_ = lean_nat_add(v_extraK_1149_, v_prevK_1152_);
lean_dec(v_prevK_1152_);
v___x_1165_ = l___private_Lean_Level_0__Lean_Level_accMax(v_result_1153_, v_prev_1151_, v___x_1164_);
v_i_1150_ = v___x_1163_;
v_prev_1151_ = v_curr_1159_;
v_prevK_1152_ = v_currK_1160_;
v_result_1153_ = v___x_1165_;
goto _start;
}
else
{
lean_object* v___x_1167_; lean_object* v___x_1168_; 
lean_dec(v_prevK_1152_);
lean_dec(v_prev_1151_);
v___x_1167_ = lean_unsigned_to_nat(1u);
v___x_1168_ = lean_nat_add(v_i_1150_, v___x_1167_);
lean_dec(v_i_1150_);
v_i_1150_ = v___x_1168_;
v_prev_1151_ = v_curr_1159_;
v_prevK_1152_ = v_currK_1160_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_mkMaxAux___boxed(lean_object* v_lvls_1170_, lean_object* v_extraK_1171_, lean_object* v_i_1172_, lean_object* v_prev_1173_, lean_object* v_prevK_1174_, lean_object* v_result_1175_){
_start:
{
lean_object* v_res_1176_; 
v_res_1176_ = l___private_Lean_Level_0__Lean_Level_mkMaxAux(v_lvls_1170_, v_extraK_1171_, v_i_1172_, v_prev_1173_, v_prevK_1174_, v_result_1175_);
lean_dec(v_extraK_1171_);
lean_dec_ref(v_lvls_1170_);
return v_res_1176_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_skipExplicit(lean_object* v_lvls_1177_, lean_object* v_i_1178_){
_start:
{
lean_object* v___x_1179_; uint8_t v___x_1180_; 
v___x_1179_ = lean_array_get_size(v_lvls_1177_);
v___x_1180_ = lean_nat_dec_lt(v_i_1178_, v___x_1179_);
if (v___x_1180_ == 0)
{
return v_i_1178_;
}
else
{
lean_object* v_lvl_1181_; lean_object* v___x_1182_; uint8_t v___x_1183_; 
v_lvl_1181_ = lean_array_fget_borrowed(v_lvls_1177_, v_i_1178_);
v___x_1182_ = l_Lean_Level_getLevelOffset(v_lvl_1181_);
v___x_1183_ = l_Lean_Level_isZero(v___x_1182_);
lean_dec(v___x_1182_);
if (v___x_1183_ == 0)
{
return v_i_1178_;
}
else
{
lean_object* v___x_1184_; lean_object* v___x_1185_; 
v___x_1184_ = lean_unsigned_to_nat(1u);
v___x_1185_ = lean_nat_add(v_i_1178_, v___x_1184_);
lean_dec(v_i_1178_);
v_i_1178_ = v___x_1185_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_skipExplicit___boxed(lean_object* v_lvls_1187_, lean_object* v_i_1188_){
_start:
{
lean_object* v_res_1189_; 
v_res_1189_ = l___private_Lean_Level_0__Lean_Level_skipExplicit(v_lvls_1187_, v_i_1188_);
lean_dec_ref(v_lvls_1187_);
return v_res_1189_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Level_0__Lean_Level_isExplicitSubsumedAux(lean_object* v_lvls_1190_, lean_object* v_maxExplicit_1191_, lean_object* v_i_1192_){
_start:
{
lean_object* v___x_1193_; uint8_t v___x_1194_; 
v___x_1193_ = lean_array_get_size(v_lvls_1190_);
v___x_1194_ = lean_nat_dec_lt(v_i_1192_, v___x_1193_);
if (v___x_1194_ == 0)
{
lean_dec(v_i_1192_);
return v___x_1194_;
}
else
{
lean_object* v_lvl_1195_; lean_object* v___x_1196_; uint8_t v___x_1197_; 
v_lvl_1195_ = lean_array_fget_borrowed(v_lvls_1190_, v_i_1192_);
v___x_1196_ = l_Lean_Level_getOffset(v_lvl_1195_);
v___x_1197_ = lean_nat_dec_le(v_maxExplicit_1191_, v___x_1196_);
lean_dec(v___x_1196_);
if (v___x_1197_ == 0)
{
lean_object* v___x_1198_; lean_object* v___x_1199_; 
v___x_1198_ = lean_unsigned_to_nat(1u);
v___x_1199_ = lean_nat_add(v_i_1192_, v___x_1198_);
lean_dec(v_i_1192_);
v_i_1192_ = v___x_1199_;
goto _start;
}
else
{
lean_dec(v_i_1192_);
return v___x_1197_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_isExplicitSubsumedAux___boxed(lean_object* v_lvls_1201_, lean_object* v_maxExplicit_1202_, lean_object* v_i_1203_){
_start:
{
uint8_t v_res_1204_; lean_object* v_r_1205_; 
v_res_1204_ = l___private_Lean_Level_0__Lean_Level_isExplicitSubsumedAux(v_lvls_1201_, v_maxExplicit_1202_, v_i_1203_);
lean_dec(v_maxExplicit_1202_);
lean_dec_ref(v_lvls_1201_);
v_r_1205_ = lean_box(v_res_1204_);
return v_r_1205_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Level_0__Lean_Level_isExplicitSubsumed(lean_object* v_lvls_1206_, lean_object* v_firstNonExplicit_1207_){
_start:
{
lean_object* v___x_1208_; uint8_t v___x_1209_; 
v___x_1208_ = lean_unsigned_to_nat(0u);
v___x_1209_ = lean_nat_dec_eq(v_firstNonExplicit_1207_, v___x_1208_);
if (v___x_1209_ == 0)
{
lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v_max_1214_; uint8_t v___x_1215_; 
v___x_1210_ = lean_box(0);
v___x_1211_ = lean_unsigned_to_nat(1u);
v___x_1212_ = lean_nat_sub(v_firstNonExplicit_1207_, v___x_1211_);
v___x_1213_ = lean_array_get_borrowed(v___x_1210_, v_lvls_1206_, v___x_1212_);
lean_dec(v___x_1212_);
v_max_1214_ = l_Lean_Level_getOffset(v___x_1213_);
v___x_1215_ = l___private_Lean_Level_0__Lean_Level_isExplicitSubsumedAux(v_lvls_1206_, v_max_1214_, v_firstNonExplicit_1207_);
lean_dec(v_max_1214_);
return v___x_1215_;
}
else
{
uint8_t v___x_1216_; 
lean_dec(v_firstNonExplicit_1207_);
v___x_1216_ = 0;
return v___x_1216_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_isExplicitSubsumed___boxed(lean_object* v_lvls_1217_, lean_object* v_firstNonExplicit_1218_){
_start:
{
uint8_t v_res_1219_; lean_object* v_r_1220_; 
v_res_1219_ = l___private_Lean_Level_0__Lean_Level_isExplicitSubsumed(v_lvls_1217_, v_firstNonExplicit_1218_);
lean_dec_ref(v_lvls_1217_);
v_r_1220_ = lean_box(v_res_1219_);
return v_r_1220_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Level_normalize_spec__2(lean_object* v_msg_1221_){
_start:
{
lean_object* v___x_1222_; lean_object* v___x_1223_; 
v___x_1222_ = lean_box(0);
v___x_1223_ = lean_panic_fn_borrowed(v___x_1222_, v_msg_1221_);
return v___x_1223_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1_spec__1___redArg(lean_object* v_hi_1224_, lean_object* v_pivot_1225_, lean_object* v_as_1226_, lean_object* v_i_1227_, lean_object* v_k_1228_){
_start:
{
uint8_t v___x_1229_; 
v___x_1229_ = lean_nat_dec_lt(v_k_1228_, v_hi_1224_);
if (v___x_1229_ == 0)
{
lean_object* v___x_1230_; lean_object* v___x_1231_; 
lean_dec(v_k_1228_);
v___x_1230_ = lean_array_fswap(v_as_1226_, v_i_1227_, v_hi_1224_);
v___x_1231_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1231_, 0, v_i_1227_);
lean_ctor_set(v___x_1231_, 1, v___x_1230_);
return v___x_1231_;
}
else
{
lean_object* v___x_1232_; uint8_t v___x_1233_; 
v___x_1232_ = lean_array_fget_borrowed(v_as_1226_, v_k_1228_);
v___x_1233_ = l_Lean_Level_normLt(v___x_1232_, v_pivot_1225_);
if (v___x_1233_ == 0)
{
lean_object* v___x_1234_; lean_object* v___x_1235_; 
v___x_1234_ = lean_unsigned_to_nat(1u);
v___x_1235_ = lean_nat_add(v_k_1228_, v___x_1234_);
lean_dec(v_k_1228_);
v_k_1228_ = v___x_1235_;
goto _start;
}
else
{
lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; 
v___x_1237_ = lean_array_fswap(v_as_1226_, v_i_1227_, v_k_1228_);
v___x_1238_ = lean_unsigned_to_nat(1u);
v___x_1239_ = lean_nat_add(v_i_1227_, v___x_1238_);
lean_dec(v_i_1227_);
v___x_1240_ = lean_nat_add(v_k_1228_, v___x_1238_);
lean_dec(v_k_1228_);
v_as_1226_ = v___x_1237_;
v_i_1227_ = v___x_1239_;
v_k_1228_ = v___x_1240_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1_spec__1___redArg___boxed(lean_object* v_hi_1242_, lean_object* v_pivot_1243_, lean_object* v_as_1244_, lean_object* v_i_1245_, lean_object* v_k_1246_){
_start:
{
lean_object* v_res_1247_; 
v_res_1247_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1_spec__1___redArg(v_hi_1242_, v_pivot_1243_, v_as_1244_, v_i_1245_, v_k_1246_);
lean_dec(v_pivot_1243_);
lean_dec(v_hi_1242_);
return v_res_1247_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1___redArg(lean_object* v_n_1248_, lean_object* v_as_1249_, lean_object* v_lo_1250_, lean_object* v_hi_1251_){
_start:
{
lean_object* v___y_1253_; uint8_t v___x_1263_; 
v___x_1263_ = lean_nat_dec_lt(v_lo_1250_, v_hi_1251_);
if (v___x_1263_ == 0)
{
lean_dec(v_lo_1250_);
return v_as_1249_;
}
else
{
lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v_mid_1266_; lean_object* v___y_1268_; lean_object* v___y_1274_; lean_object* v___x_1279_; lean_object* v___x_1280_; uint8_t v___x_1281_; 
v___x_1264_ = lean_nat_add(v_lo_1250_, v_hi_1251_);
v___x_1265_ = lean_unsigned_to_nat(1u);
v_mid_1266_ = lean_nat_shiftr(v___x_1264_, v___x_1265_);
lean_dec(v___x_1264_);
v___x_1279_ = lean_array_fget_borrowed(v_as_1249_, v_mid_1266_);
v___x_1280_ = lean_array_fget_borrowed(v_as_1249_, v_lo_1250_);
v___x_1281_ = l_Lean_Level_normLt(v___x_1279_, v___x_1280_);
if (v___x_1281_ == 0)
{
v___y_1274_ = v_as_1249_;
goto v___jp_1273_;
}
else
{
lean_object* v___x_1282_; 
v___x_1282_ = lean_array_fswap(v_as_1249_, v_lo_1250_, v_mid_1266_);
v___y_1274_ = v___x_1282_;
goto v___jp_1273_;
}
v___jp_1267_:
{
lean_object* v___x_1269_; lean_object* v___x_1270_; uint8_t v___x_1271_; 
v___x_1269_ = lean_array_fget_borrowed(v___y_1268_, v_mid_1266_);
v___x_1270_ = lean_array_fget_borrowed(v___y_1268_, v_hi_1251_);
v___x_1271_ = l_Lean_Level_normLt(v___x_1269_, v___x_1270_);
if (v___x_1271_ == 0)
{
lean_dec(v_mid_1266_);
v___y_1253_ = v___y_1268_;
goto v___jp_1252_;
}
else
{
lean_object* v___x_1272_; 
v___x_1272_ = lean_array_fswap(v___y_1268_, v_mid_1266_, v_hi_1251_);
lean_dec(v_mid_1266_);
v___y_1253_ = v___x_1272_;
goto v___jp_1252_;
}
}
v___jp_1273_:
{
lean_object* v___x_1275_; lean_object* v___x_1276_; uint8_t v___x_1277_; 
v___x_1275_ = lean_array_fget_borrowed(v___y_1274_, v_hi_1251_);
v___x_1276_ = lean_array_fget_borrowed(v___y_1274_, v_lo_1250_);
v___x_1277_ = l_Lean_Level_normLt(v___x_1275_, v___x_1276_);
if (v___x_1277_ == 0)
{
v___y_1268_ = v___y_1274_;
goto v___jp_1267_;
}
else
{
lean_object* v___x_1278_; 
v___x_1278_ = lean_array_fswap(v___y_1274_, v_lo_1250_, v_hi_1251_);
v___y_1268_ = v___x_1278_;
goto v___jp_1267_;
}
}
}
v___jp_1252_:
{
lean_object* v_pivot_1254_; lean_object* v___x_1255_; lean_object* v_fst_1256_; lean_object* v_snd_1257_; uint8_t v___x_1258_; 
v_pivot_1254_ = lean_array_fget(v___y_1253_, v_hi_1251_);
lean_inc_n(v_lo_1250_, 2);
v___x_1255_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1_spec__1___redArg(v_hi_1251_, v_pivot_1254_, v___y_1253_, v_lo_1250_, v_lo_1250_);
lean_dec(v_pivot_1254_);
v_fst_1256_ = lean_ctor_get(v___x_1255_, 0);
lean_inc(v_fst_1256_);
v_snd_1257_ = lean_ctor_get(v___x_1255_, 1);
lean_inc(v_snd_1257_);
lean_dec_ref(v___x_1255_);
v___x_1258_ = lean_nat_dec_le(v_hi_1251_, v_fst_1256_);
if (v___x_1258_ == 0)
{
lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; 
v___x_1259_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1___redArg(v_n_1248_, v_snd_1257_, v_lo_1250_, v_fst_1256_);
v___x_1260_ = lean_unsigned_to_nat(1u);
v___x_1261_ = lean_nat_add(v_fst_1256_, v___x_1260_);
lean_dec(v_fst_1256_);
v_as_1249_ = v___x_1259_;
v_lo_1250_ = v___x_1261_;
goto _start;
}
else
{
lean_dec(v_fst_1256_);
lean_dec(v_lo_1250_);
return v_snd_1257_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1___redArg___boxed(lean_object* v_n_1283_, lean_object* v_as_1284_, lean_object* v_lo_1285_, lean_object* v_hi_1286_){
_start:
{
lean_object* v_res_1287_; 
v_res_1287_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1___redArg(v_n_1283_, v_as_1284_, v_lo_1285_, v_hi_1286_);
lean_dec(v_hi_1286_);
lean_dec(v_n_1283_);
return v_res_1287_;
}
}
static lean_object* _init_l_Lean_Level_normalize___closed__3(void){
_start:
{
lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; 
v___x_1292_ = ((lean_object*)(l_Lean_Level_normalize___closed__2));
v___x_1293_ = lean_unsigned_to_nat(11u);
v___x_1294_ = lean_unsigned_to_nat(401u);
v___x_1295_ = ((lean_object*)(l_Lean_Level_normalize___closed__1));
v___x_1296_ = ((lean_object*)(l_Lean_Level_mvarId_x21___closed__0));
v___x_1297_ = l_mkPanicMessageWithDecl(v___x_1296_, v___x_1295_, v___x_1294_, v___x_1293_, v___x_1292_);
return v___x_1297_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_normalize(lean_object* v_l_1298_){
_start:
{
uint8_t v___x_1299_; 
v___x_1299_ = l_Lean_Level_isAlreadyNormalizedCheap(v_l_1298_);
if (v___x_1299_ == 0)
{
lean_object* v_k_1300_; lean_object* v_u_1301_; 
v_k_1300_ = l_Lean_Level_getOffset(v_l_1298_);
v_u_1301_ = l_Lean_Level_getLevelOffset(v_l_1298_);
switch(lean_obj_tag(v_u_1301_))
{
case 2:
{
lean_object* v_a_1302_; lean_object* v_a_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v_lvls_1306_; lean_object* v_lvls_1307_; lean_object* v___x_1308_; lean_object* v___y_1310_; lean_object* v___y_1311_; lean_object* v___y_1319_; lean_object* v___x_1323_; lean_object* v___y_1325_; lean_object* v___y_1326_; uint8_t v___x_1328_; 
v_a_1302_ = lean_ctor_get(v_u_1301_, 0);
lean_inc(v_a_1302_);
v_a_1303_ = lean_ctor_get(v_u_1301_, 1);
lean_inc(v_a_1303_);
lean_dec_ref(v_u_1301_);
v___x_1304_ = lean_unsigned_to_nat(0u);
v___x_1305_ = ((lean_object*)(l_Lean_Level_normalize___closed__0));
v_lvls_1306_ = l___private_Lean_Level_0__Lean_Level_getMaxArgsAux___at___00Lean_Level_normalize_spec__0(v_a_1302_, v___x_1299_, v___x_1305_);
v_lvls_1307_ = l___private_Lean_Level_0__Lean_Level_getMaxArgsAux___at___00Lean_Level_normalize_spec__0(v_a_1303_, v___x_1299_, v_lvls_1306_);
v___x_1308_ = lean_unsigned_to_nat(1u);
v___x_1323_ = lean_array_get_size(v_lvls_1307_);
v___x_1328_ = lean_nat_dec_eq(v___x_1323_, v___x_1304_);
if (v___x_1328_ == 0)
{
lean_object* v___x_1329_; lean_object* v___y_1331_; uint8_t v___x_1333_; 
v___x_1329_ = lean_nat_sub(v___x_1323_, v___x_1308_);
v___x_1333_ = lean_nat_dec_le(v___x_1304_, v___x_1329_);
if (v___x_1333_ == 0)
{
lean_inc(v___x_1329_);
v___y_1331_ = v___x_1329_;
goto v___jp_1330_;
}
else
{
v___y_1331_ = v___x_1304_;
goto v___jp_1330_;
}
v___jp_1330_:
{
uint8_t v___x_1332_; 
v___x_1332_ = lean_nat_dec_le(v___y_1331_, v___x_1329_);
if (v___x_1332_ == 0)
{
lean_dec(v___x_1329_);
lean_inc(v___y_1331_);
v___y_1325_ = v___y_1331_;
v___y_1326_ = v___y_1331_;
goto v___jp_1324_;
}
else
{
v___y_1325_ = v___y_1331_;
v___y_1326_ = v___x_1329_;
goto v___jp_1324_;
}
}
}
else
{
v___y_1319_ = v_lvls_1307_;
goto v___jp_1318_;
}
v___jp_1309_:
{
lean_object* v___x_1312_; lean_object* v_lvl_u2081_1313_; lean_object* v_prev_1314_; lean_object* v_prevK_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; 
v___x_1312_ = lean_box(0);
v_lvl_u2081_1313_ = lean_array_get_borrowed(v___x_1312_, v___y_1310_, v___y_1311_);
v_prev_1314_ = l_Lean_Level_getLevelOffset(v_lvl_u2081_1313_);
v_prevK_1315_ = l_Lean_Level_getOffset(v_lvl_u2081_1313_);
v___x_1316_ = lean_nat_add(v___y_1311_, v___x_1308_);
lean_dec(v___y_1311_);
v___x_1317_ = l___private_Lean_Level_0__Lean_Level_mkMaxAux(v___y_1310_, v_k_1300_, v___x_1316_, v_prev_1314_, v_prevK_1315_, v___x_1312_);
lean_dec(v_k_1300_);
lean_dec_ref(v___y_1310_);
return v___x_1317_;
}
v___jp_1318_:
{
lean_object* v_firstNonExplicit_1320_; uint8_t v___x_1321_; 
v_firstNonExplicit_1320_ = l___private_Lean_Level_0__Lean_Level_skipExplicit(v___y_1319_, v___x_1304_);
lean_inc(v_firstNonExplicit_1320_);
v___x_1321_ = l___private_Lean_Level_0__Lean_Level_isExplicitSubsumed(v___y_1319_, v_firstNonExplicit_1320_);
if (v___x_1321_ == 0)
{
lean_object* v___x_1322_; 
v___x_1322_ = lean_nat_sub(v_firstNonExplicit_1320_, v___x_1308_);
lean_dec(v_firstNonExplicit_1320_);
v___y_1310_ = v___y_1319_;
v___y_1311_ = v___x_1322_;
goto v___jp_1309_;
}
else
{
v___y_1310_ = v___y_1319_;
v___y_1311_ = v_firstNonExplicit_1320_;
goto v___jp_1309_;
}
}
v___jp_1324_:
{
lean_object* v___x_1327_; 
v___x_1327_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1___redArg(v___x_1323_, v_lvls_1307_, v___y_1325_, v___y_1326_);
lean_dec(v___y_1326_);
v___y_1319_ = v___x_1327_;
goto v___jp_1318_;
}
}
case 3:
{
lean_object* v_a_1334_; lean_object* v_a_1335_; uint8_t v___x_1336_; 
v_a_1334_ = lean_ctor_get(v_u_1301_, 0);
lean_inc(v_a_1334_);
v_a_1335_ = lean_ctor_get(v_u_1301_, 1);
lean_inc(v_a_1335_);
lean_dec_ref(v_u_1301_);
v___x_1336_ = l_Lean_Level_isNeverZero(v_a_1335_);
if (v___x_1336_ == 0)
{
lean_object* v_l_u2081_1337_; lean_object* v_l_u2082_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; 
v_l_u2081_1337_ = l_Lean_Level_normalize(v_a_1334_);
lean_dec(v_a_1334_);
v_l_u2082_1338_ = l_Lean_Level_normalize(v_a_1335_);
lean_dec(v_a_1335_);
v___x_1339_ = l___private_Lean_Level_0__Lean_Level_mkIMaxAux(v_l_u2081_1337_, v_l_u2082_1338_);
v___x_1340_ = l_Lean_Level_addOffsetAux(v_k_1300_, v___x_1339_);
return v___x_1340_;
}
else
{
lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; 
v___x_1341_ = l_Lean_Level_max___override(v_a_1334_, v_a_1335_);
v___x_1342_ = l_Lean_Level_normalize(v___x_1341_);
lean_dec(v___x_1341_);
v___x_1343_ = l_Lean_Level_addOffsetAux(v_k_1300_, v___x_1342_);
return v___x_1343_;
}
}
default: 
{
lean_object* v___x_1344_; lean_object* v___x_1345_; 
lean_dec(v_u_1301_);
lean_dec(v_k_1300_);
v___x_1344_ = lean_obj_once(&l_Lean_Level_normalize___closed__3, &l_Lean_Level_normalize___closed__3_once, _init_l_Lean_Level_normalize___closed__3);
v___x_1345_ = l_panic___at___00Lean_Level_normalize_spec__2(v___x_1344_);
return v___x_1345_;
}
}
}
else
{
lean_inc(v_l_1298_);
return v_l_1298_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_getMaxArgsAux___at___00Lean_Level_normalize_spec__0(lean_object* v_x_1346_, uint8_t v_x_1347_, lean_object* v_x_1348_){
_start:
{
if (lean_obj_tag(v_x_1346_) == 2)
{
lean_object* v_a_1349_; lean_object* v_a_1350_; lean_object* v___x_1351_; 
v_a_1349_ = lean_ctor_get(v_x_1346_, 0);
lean_inc(v_a_1349_);
v_a_1350_ = lean_ctor_get(v_x_1346_, 1);
lean_inc(v_a_1350_);
lean_dec_ref(v_x_1346_);
v___x_1351_ = l___private_Lean_Level_0__Lean_Level_getMaxArgsAux___at___00Lean_Level_normalize_spec__0(v_a_1349_, v_x_1347_, v_x_1348_);
v_x_1346_ = v_a_1350_;
v_x_1348_ = v___x_1351_;
goto _start;
}
else
{
if (v_x_1347_ == 0)
{
lean_object* v___x_1353_; uint8_t v___x_1354_; 
v___x_1353_ = l_Lean_Level_normalize(v_x_1346_);
lean_dec(v_x_1346_);
v___x_1354_ = 1;
v_x_1346_ = v___x_1353_;
v_x_1347_ = v___x_1354_;
goto _start;
}
else
{
lean_object* v___x_1356_; 
v___x_1356_ = lean_array_push(v_x_1348_, v_x_1346_);
return v___x_1356_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_getMaxArgsAux___at___00Lean_Level_normalize_spec__0___boxed(lean_object* v_x_1357_, lean_object* v_x_1358_, lean_object* v_x_1359_){
_start:
{
uint8_t v_x_676__boxed_1360_; lean_object* v_res_1361_; 
v_x_676__boxed_1360_ = lean_unbox(v_x_1358_);
v_res_1361_ = l___private_Lean_Level_0__Lean_Level_getMaxArgsAux___at___00Lean_Level_normalize_spec__0(v_x_1357_, v_x_676__boxed_1360_, v_x_1359_);
return v_res_1361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_normalize___boxed(lean_object* v_l_1362_){
_start:
{
lean_object* v_res_1363_; 
v_res_1363_ = l_Lean_Level_normalize(v_l_1362_);
lean_dec(v_l_1362_);
return v_res_1363_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1(lean_object* v_n_1364_, lean_object* v_as_1365_, lean_object* v_lo_1366_, lean_object* v_hi_1367_, lean_object* v_w_1368_, lean_object* v_hlo_1369_, lean_object* v_hhi_1370_){
_start:
{
lean_object* v___x_1371_; 
v___x_1371_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1___redArg(v_n_1364_, v_as_1365_, v_lo_1366_, v_hi_1367_);
return v___x_1371_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1___boxed(lean_object* v_n_1372_, lean_object* v_as_1373_, lean_object* v_lo_1374_, lean_object* v_hi_1375_, lean_object* v_w_1376_, lean_object* v_hlo_1377_, lean_object* v_hhi_1378_){
_start:
{
lean_object* v_res_1379_; 
v_res_1379_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1(v_n_1372_, v_as_1373_, v_lo_1374_, v_hi_1375_, v_w_1376_, v_hlo_1377_, v_hhi_1378_);
lean_dec(v_hi_1375_);
lean_dec(v_n_1372_);
return v_res_1379_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1_spec__1(lean_object* v_n_1380_, lean_object* v_lo_1381_, lean_object* v_hi_1382_, lean_object* v_hhi_1383_, lean_object* v_pivot_1384_, lean_object* v_as_1385_, lean_object* v_i_1386_, lean_object* v_k_1387_, lean_object* v_ilo_1388_, lean_object* v_ik_1389_, lean_object* v_w_1390_){
_start:
{
lean_object* v___x_1391_; 
v___x_1391_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1_spec__1___redArg(v_hi_1382_, v_pivot_1384_, v_as_1385_, v_i_1386_, v_k_1387_);
return v___x_1391_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1_spec__1___boxed(lean_object* v_n_1392_, lean_object* v_lo_1393_, lean_object* v_hi_1394_, lean_object* v_hhi_1395_, lean_object* v_pivot_1396_, lean_object* v_as_1397_, lean_object* v_i_1398_, lean_object* v_k_1399_, lean_object* v_ilo_1400_, lean_object* v_ik_1401_, lean_object* v_w_1402_){
_start:
{
lean_object* v_res_1403_; 
v_res_1403_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1_spec__1(v_n_1392_, v_lo_1393_, v_hi_1394_, v_hhi_1395_, v_pivot_1396_, v_as_1397_, v_i_1398_, v_k_1399_, v_ilo_1400_, v_ik_1401_, v_w_1402_);
lean_dec(v_pivot_1396_);
lean_dec(v_hi_1394_);
lean_dec(v_lo_1393_);
lean_dec(v_n_1392_);
return v_res_1403_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_isEquiv(lean_object* v_u_1404_, lean_object* v_v_1405_){
_start:
{
uint8_t v___x_1406_; 
v___x_1406_ = lean_level_eq(v_u_1404_, v_v_1405_);
if (v___x_1406_ == 0)
{
lean_object* v___x_1407_; lean_object* v___x_1408_; uint8_t v___x_1409_; 
v___x_1407_ = l_Lean_Level_normalize(v_u_1404_);
v___x_1408_ = l_Lean_Level_normalize(v_v_1405_);
v___x_1409_ = lean_level_eq(v___x_1407_, v___x_1408_);
lean_dec(v___x_1408_);
lean_dec(v___x_1407_);
return v___x_1409_;
}
else
{
return v___x_1406_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_isEquiv___boxed(lean_object* v_u_1410_, lean_object* v_v_1411_){
_start:
{
uint8_t v_res_1412_; lean_object* v_r_1413_; 
v_res_1412_ = l_Lean_Level_isEquiv(v_u_1410_, v_v_1411_);
lean_dec(v_v_1411_);
lean_dec(v_u_1410_);
v_r_1413_ = lean_box(v_res_1412_);
return v_r_1413_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_dec(lean_object* v_x_1414_){
_start:
{
lean_object* v_l_u2081_1416_; lean_object* v_l_u2082_1417_; 
switch(lean_obj_tag(v_x_1414_))
{
case 0:
{
lean_object* v___x_1430_; 
v___x_1430_ = lean_box(0);
return v___x_1430_;
}
case 1:
{
lean_object* v_a_1431_; lean_object* v___x_1432_; 
v_a_1431_ = lean_ctor_get(v_x_1414_, 0);
lean_inc(v_a_1431_);
v___x_1432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1432_, 0, v_a_1431_);
return v___x_1432_;
}
case 2:
{
lean_object* v_a_1433_; lean_object* v_a_1434_; 
v_a_1433_ = lean_ctor_get(v_x_1414_, 0);
v_a_1434_ = lean_ctor_get(v_x_1414_, 1);
v_l_u2081_1416_ = v_a_1433_;
v_l_u2082_1417_ = v_a_1434_;
goto v___jp_1415_;
}
case 3:
{
lean_object* v_a_1435_; lean_object* v_a_1436_; 
v_a_1435_ = lean_ctor_get(v_x_1414_, 0);
v_a_1436_ = lean_ctor_get(v_x_1414_, 1);
v_l_u2081_1416_ = v_a_1435_;
v_l_u2082_1417_ = v_a_1436_;
goto v___jp_1415_;
}
default: 
{
lean_object* v___x_1437_; 
v___x_1437_ = lean_box(0);
return v___x_1437_;
}
}
v___jp_1415_:
{
lean_object* v___x_1418_; 
v___x_1418_ = l_Lean_Level_dec(v_l_u2081_1416_);
if (lean_obj_tag(v___x_1418_) == 0)
{
return v___x_1418_;
}
else
{
lean_object* v_val_1419_; lean_object* v___x_1420_; 
v_val_1419_ = lean_ctor_get(v___x_1418_, 0);
lean_inc(v_val_1419_);
lean_dec_ref(v___x_1418_);
v___x_1420_ = l_Lean_Level_dec(v_l_u2082_1417_);
if (lean_obj_tag(v___x_1420_) == 0)
{
lean_dec(v_val_1419_);
return v___x_1420_;
}
else
{
lean_object* v_val_1421_; lean_object* v___x_1423_; uint8_t v_isShared_1424_; uint8_t v_isSharedCheck_1429_; 
v_val_1421_ = lean_ctor_get(v___x_1420_, 0);
v_isSharedCheck_1429_ = !lean_is_exclusive(v___x_1420_);
if (v_isSharedCheck_1429_ == 0)
{
v___x_1423_ = v___x_1420_;
v_isShared_1424_ = v_isSharedCheck_1429_;
goto v_resetjp_1422_;
}
else
{
lean_inc(v_val_1421_);
lean_dec(v___x_1420_);
v___x_1423_ = lean_box(0);
v_isShared_1424_ = v_isSharedCheck_1429_;
goto v_resetjp_1422_;
}
v_resetjp_1422_:
{
lean_object* v___x_1425_; lean_object* v___x_1427_; 
v___x_1425_ = l_Lean_Level_max___override(v_val_1419_, v_val_1421_);
if (v_isShared_1424_ == 0)
{
lean_ctor_set(v___x_1423_, 0, v___x_1425_);
v___x_1427_ = v___x_1423_;
goto v_reusejp_1426_;
}
else
{
lean_object* v_reuseFailAlloc_1428_; 
v_reuseFailAlloc_1428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1428_, 0, v___x_1425_);
v___x_1427_ = v_reuseFailAlloc_1428_;
goto v_reusejp_1426_;
}
v_reusejp_1426_:
{
return v___x_1427_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_dec___boxed(lean_object* v_x_1438_){
_start:
{
lean_object* v_res_1439_; 
v_res_1439_ = l_Lean_Level_dec(v_x_1438_);
lean_dec(v_x_1438_);
return v_res_1439_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_ctorIdx(lean_object* v_x_1440_){
_start:
{
switch(lean_obj_tag(v_x_1440_))
{
case 0:
{
lean_object* v___x_1441_; 
v___x_1441_ = lean_unsigned_to_nat(0u);
return v___x_1441_;
}
case 1:
{
lean_object* v___x_1442_; 
v___x_1442_ = lean_unsigned_to_nat(1u);
return v___x_1442_;
}
case 2:
{
lean_object* v___x_1443_; 
v___x_1443_ = lean_unsigned_to_nat(2u);
return v___x_1443_;
}
case 3:
{
lean_object* v___x_1444_; 
v___x_1444_ = lean_unsigned_to_nat(3u);
return v___x_1444_;
}
default: 
{
lean_object* v___x_1445_; 
v___x_1445_ = lean_unsigned_to_nat(4u);
return v___x_1445_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_ctorIdx___boxed(lean_object* v_x_1446_){
_start:
{
lean_object* v_res_1447_; 
v_res_1447_ = l_Lean_Level_PP_Result_ctorIdx(v_x_1446_);
lean_dec_ref(v_x_1446_);
return v_res_1447_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_ctorElim___redArg(lean_object* v_t_1448_, lean_object* v_k_1449_){
_start:
{
if (lean_obj_tag(v_t_1448_) == 2)
{
lean_object* v_a_1450_; lean_object* v_a_1451_; lean_object* v___x_1452_; 
v_a_1450_ = lean_ctor_get(v_t_1448_, 0);
lean_inc_ref(v_a_1450_);
v_a_1451_ = lean_ctor_get(v_t_1448_, 1);
lean_inc(v_a_1451_);
lean_dec_ref(v_t_1448_);
v___x_1452_ = lean_apply_2(v_k_1449_, v_a_1450_, v_a_1451_);
return v___x_1452_;
}
else
{
lean_object* v_a_1453_; lean_object* v___x_1454_; 
v_a_1453_ = lean_ctor_get(v_t_1448_, 0);
lean_inc(v_a_1453_);
lean_dec_ref(v_t_1448_);
v___x_1454_ = lean_apply_1(v_k_1449_, v_a_1453_);
return v___x_1454_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_ctorElim(lean_object* v_motive__1_1455_, lean_object* v_ctorIdx_1456_, lean_object* v_t_1457_, lean_object* v_h_1458_, lean_object* v_k_1459_){
_start:
{
lean_object* v___x_1460_; 
v___x_1460_ = l_Lean_Level_PP_Result_ctorElim___redArg(v_t_1457_, v_k_1459_);
return v___x_1460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_ctorElim___boxed(lean_object* v_motive__1_1461_, lean_object* v_ctorIdx_1462_, lean_object* v_t_1463_, lean_object* v_h_1464_, lean_object* v_k_1465_){
_start:
{
lean_object* v_res_1466_; 
v_res_1466_ = l_Lean_Level_PP_Result_ctorElim(v_motive__1_1461_, v_ctorIdx_1462_, v_t_1463_, v_h_1464_, v_k_1465_);
lean_dec(v_ctorIdx_1462_);
return v_res_1466_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_leaf_elim___redArg(lean_object* v_t_1467_, lean_object* v_leaf_1468_){
_start:
{
lean_object* v___x_1469_; 
v___x_1469_ = l_Lean_Level_PP_Result_ctorElim___redArg(v_t_1467_, v_leaf_1468_);
return v___x_1469_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_leaf_elim(lean_object* v_motive__1_1470_, lean_object* v_t_1471_, lean_object* v_h_1472_, lean_object* v_leaf_1473_){
_start:
{
lean_object* v___x_1474_; 
v___x_1474_ = l_Lean_Level_PP_Result_ctorElim___redArg(v_t_1471_, v_leaf_1473_);
return v___x_1474_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_num_elim___redArg(lean_object* v_t_1475_, lean_object* v_num_1476_){
_start:
{
lean_object* v___x_1477_; 
v___x_1477_ = l_Lean_Level_PP_Result_ctorElim___redArg(v_t_1475_, v_num_1476_);
return v___x_1477_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_num_elim(lean_object* v_motive__1_1478_, lean_object* v_t_1479_, lean_object* v_h_1480_, lean_object* v_num_1481_){
_start:
{
lean_object* v___x_1482_; 
v___x_1482_ = l_Lean_Level_PP_Result_ctorElim___redArg(v_t_1479_, v_num_1481_);
return v___x_1482_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_offset_elim___redArg(lean_object* v_t_1483_, lean_object* v_offset_1484_){
_start:
{
lean_object* v___x_1485_; 
v___x_1485_ = l_Lean_Level_PP_Result_ctorElim___redArg(v_t_1483_, v_offset_1484_);
return v___x_1485_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_offset_elim(lean_object* v_motive__1_1486_, lean_object* v_t_1487_, lean_object* v_h_1488_, lean_object* v_offset_1489_){
_start:
{
lean_object* v___x_1490_; 
v___x_1490_ = l_Lean_Level_PP_Result_ctorElim___redArg(v_t_1487_, v_offset_1489_);
return v___x_1490_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_maxNode_elim___redArg(lean_object* v_t_1491_, lean_object* v_maxNode_1492_){
_start:
{
lean_object* v___x_1493_; 
v___x_1493_ = l_Lean_Level_PP_Result_ctorElim___redArg(v_t_1491_, v_maxNode_1492_);
return v___x_1493_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_maxNode_elim(lean_object* v_motive__1_1494_, lean_object* v_t_1495_, lean_object* v_h_1496_, lean_object* v_maxNode_1497_){
_start:
{
lean_object* v___x_1498_; 
v___x_1498_ = l_Lean_Level_PP_Result_ctorElim___redArg(v_t_1495_, v_maxNode_1497_);
return v___x_1498_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_imaxNode_elim___redArg(lean_object* v_t_1499_, lean_object* v_imaxNode_1500_){
_start:
{
lean_object* v___x_1501_; 
v___x_1501_ = l_Lean_Level_PP_Result_ctorElim___redArg(v_t_1499_, v_imaxNode_1500_);
return v___x_1501_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_imaxNode_elim(lean_object* v_motive__1_1502_, lean_object* v_t_1503_, lean_object* v_h_1504_, lean_object* v_imaxNode_1505_){
_start:
{
lean_object* v___x_1506_; 
v___x_1506_ = l_Lean_Level_PP_Result_ctorElim___redArg(v_t_1503_, v_imaxNode_1505_);
return v___x_1506_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_succ(lean_object* v_x_1507_){
_start:
{
switch(lean_obj_tag(v_x_1507_))
{
case 2:
{
lean_object* v_a_1508_; lean_object* v_a_1509_; lean_object* v___x_1511_; uint8_t v_isShared_1512_; uint8_t v_isSharedCheck_1518_; 
v_a_1508_ = lean_ctor_get(v_x_1507_, 0);
v_a_1509_ = lean_ctor_get(v_x_1507_, 1);
v_isSharedCheck_1518_ = !lean_is_exclusive(v_x_1507_);
if (v_isSharedCheck_1518_ == 0)
{
v___x_1511_ = v_x_1507_;
v_isShared_1512_ = v_isSharedCheck_1518_;
goto v_resetjp_1510_;
}
else
{
lean_inc(v_a_1509_);
lean_inc(v_a_1508_);
lean_dec(v_x_1507_);
v___x_1511_ = lean_box(0);
v_isShared_1512_ = v_isSharedCheck_1518_;
goto v_resetjp_1510_;
}
v_resetjp_1510_:
{
lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1516_; 
v___x_1513_ = lean_unsigned_to_nat(1u);
v___x_1514_ = lean_nat_add(v_a_1509_, v___x_1513_);
lean_dec(v_a_1509_);
if (v_isShared_1512_ == 0)
{
lean_ctor_set(v___x_1511_, 1, v___x_1514_);
v___x_1516_ = v___x_1511_;
goto v_reusejp_1515_;
}
else
{
lean_object* v_reuseFailAlloc_1517_; 
v_reuseFailAlloc_1517_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1517_, 0, v_a_1508_);
lean_ctor_set(v_reuseFailAlloc_1517_, 1, v___x_1514_);
v___x_1516_ = v_reuseFailAlloc_1517_;
goto v_reusejp_1515_;
}
v_reusejp_1515_:
{
return v___x_1516_;
}
}
}
case 1:
{
lean_object* v_a_1519_; lean_object* v___x_1521_; uint8_t v_isShared_1522_; uint8_t v_isSharedCheck_1528_; 
v_a_1519_ = lean_ctor_get(v_x_1507_, 0);
v_isSharedCheck_1528_ = !lean_is_exclusive(v_x_1507_);
if (v_isSharedCheck_1528_ == 0)
{
v___x_1521_ = v_x_1507_;
v_isShared_1522_ = v_isSharedCheck_1528_;
goto v_resetjp_1520_;
}
else
{
lean_inc(v_a_1519_);
lean_dec(v_x_1507_);
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
lean_ctor_set(v___x_1521_, 0, v___x_1524_);
v___x_1526_ = v___x_1521_;
goto v_reusejp_1525_;
}
else
{
lean_object* v_reuseFailAlloc_1527_; 
v_reuseFailAlloc_1527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1527_, 0, v___x_1524_);
v___x_1526_ = v_reuseFailAlloc_1527_;
goto v_reusejp_1525_;
}
v_reusejp_1525_:
{
return v___x_1526_;
}
}
}
default: 
{
lean_object* v___x_1529_; lean_object* v___x_1530_; 
v___x_1529_ = lean_unsigned_to_nat(1u);
v___x_1530_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1530_, 0, v_x_1507_);
lean_ctor_set(v___x_1530_, 1, v___x_1529_);
return v___x_1530_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_max(lean_object* v_x_1531_, lean_object* v_x_1532_){
_start:
{
if (lean_obj_tag(v_x_1532_) == 3)
{
lean_object* v_a_1533_; lean_object* v___x_1535_; uint8_t v_isShared_1536_; uint8_t v_isSharedCheck_1541_; 
v_a_1533_ = lean_ctor_get(v_x_1532_, 0);
v_isSharedCheck_1541_ = !lean_is_exclusive(v_x_1532_);
if (v_isSharedCheck_1541_ == 0)
{
v___x_1535_ = v_x_1532_;
v_isShared_1536_ = v_isSharedCheck_1541_;
goto v_resetjp_1534_;
}
else
{
lean_inc(v_a_1533_);
lean_dec(v_x_1532_);
v___x_1535_ = lean_box(0);
v_isShared_1536_ = v_isSharedCheck_1541_;
goto v_resetjp_1534_;
}
v_resetjp_1534_:
{
lean_object* v___x_1537_; lean_object* v___x_1539_; 
v___x_1537_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1537_, 0, v_x_1531_);
lean_ctor_set(v___x_1537_, 1, v_a_1533_);
if (v_isShared_1536_ == 0)
{
lean_ctor_set(v___x_1535_, 0, v___x_1537_);
v___x_1539_ = v___x_1535_;
goto v_reusejp_1538_;
}
else
{
lean_object* v_reuseFailAlloc_1540_; 
v_reuseFailAlloc_1540_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1540_, 0, v___x_1537_);
v___x_1539_ = v_reuseFailAlloc_1540_;
goto v_reusejp_1538_;
}
v_reusejp_1538_:
{
return v___x_1539_;
}
}
}
else
{
lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; 
v___x_1542_ = lean_box(0);
v___x_1543_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1543_, 0, v_x_1532_);
lean_ctor_set(v___x_1543_, 1, v___x_1542_);
v___x_1544_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1544_, 0, v_x_1531_);
lean_ctor_set(v___x_1544_, 1, v___x_1543_);
v___x_1545_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1545_, 0, v___x_1544_);
return v___x_1545_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_imax(lean_object* v_x_1546_, lean_object* v_x_1547_){
_start:
{
if (lean_obj_tag(v_x_1547_) == 4)
{
lean_object* v_a_1548_; lean_object* v___x_1550_; uint8_t v_isShared_1551_; uint8_t v_isSharedCheck_1556_; 
v_a_1548_ = lean_ctor_get(v_x_1547_, 0);
v_isSharedCheck_1556_ = !lean_is_exclusive(v_x_1547_);
if (v_isSharedCheck_1556_ == 0)
{
v___x_1550_ = v_x_1547_;
v_isShared_1551_ = v_isSharedCheck_1556_;
goto v_resetjp_1549_;
}
else
{
lean_inc(v_a_1548_);
lean_dec(v_x_1547_);
v___x_1550_ = lean_box(0);
v_isShared_1551_ = v_isSharedCheck_1556_;
goto v_resetjp_1549_;
}
v_resetjp_1549_:
{
lean_object* v___x_1552_; lean_object* v___x_1554_; 
v___x_1552_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1552_, 0, v_x_1546_);
lean_ctor_set(v___x_1552_, 1, v_a_1548_);
if (v_isShared_1551_ == 0)
{
lean_ctor_set(v___x_1550_, 0, v___x_1552_);
v___x_1554_ = v___x_1550_;
goto v_reusejp_1553_;
}
else
{
lean_object* v_reuseFailAlloc_1555_; 
v_reuseFailAlloc_1555_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1555_, 0, v___x_1552_);
v___x_1554_ = v_reuseFailAlloc_1555_;
goto v_reusejp_1553_;
}
v_reusejp_1553_:
{
return v___x_1554_;
}
}
}
else
{
lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; 
v___x_1557_ = lean_box(0);
v___x_1558_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1558_, 0, v_x_1547_);
lean_ctor_set(v___x_1558_, 1, v___x_1557_);
v___x_1559_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1559_, 0, v_x_1546_);
lean_ctor_set(v___x_1559_, 1, v___x_1558_);
v___x_1560_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1560_, 0, v___x_1559_);
return v___x_1560_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_toResult(lean_object* v_l_1579_, lean_object* v_a_1580_){
_start:
{
switch(lean_obj_tag(v_l_1579_))
{
case 0:
{
lean_object* v___x_1581_; 
v___x_1581_ = ((lean_object*)(l_Lean_Level_PP_toResult___closed__0));
return v___x_1581_;
}
case 1:
{
lean_object* v_a_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; 
v_a_1582_ = lean_ctor_get(v_l_1579_, 0);
lean_inc(v_a_1582_);
lean_dec_ref(v_l_1579_);
v___x_1583_ = l_Lean_Level_PP_toResult(v_a_1582_, v_a_1580_);
v___x_1584_ = l_Lean_Level_PP_Result_succ(v___x_1583_);
return v___x_1584_;
}
case 2:
{
lean_object* v_a_1585_; lean_object* v_a_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; 
v_a_1585_ = lean_ctor_get(v_l_1579_, 0);
lean_inc(v_a_1585_);
v_a_1586_ = lean_ctor_get(v_l_1579_, 1);
lean_inc(v_a_1586_);
lean_dec_ref(v_l_1579_);
v___x_1587_ = l_Lean_Level_PP_toResult(v_a_1585_, v_a_1580_);
v___x_1588_ = l_Lean_Level_PP_toResult(v_a_1586_, v_a_1580_);
v___x_1589_ = l_Lean_Level_PP_Result_max(v___x_1587_, v___x_1588_);
return v___x_1589_;
}
case 3:
{
lean_object* v_a_1590_; lean_object* v_a_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; 
v_a_1590_ = lean_ctor_get(v_l_1579_, 0);
lean_inc(v_a_1590_);
v_a_1591_ = lean_ctor_get(v_l_1579_, 1);
lean_inc(v_a_1591_);
lean_dec_ref(v_l_1579_);
v___x_1592_ = l_Lean_Level_PP_toResult(v_a_1590_, v_a_1580_);
v___x_1593_ = l_Lean_Level_PP_toResult(v_a_1591_, v_a_1580_);
v___x_1594_ = l_Lean_Level_PP_Result_imax(v___x_1592_, v___x_1593_);
return v___x_1594_;
}
case 4:
{
lean_object* v_a_1595_; lean_object* v___x_1596_; 
v_a_1595_ = lean_ctor_get(v_l_1579_, 0);
lean_inc(v_a_1595_);
lean_dec_ref(v_l_1579_);
v___x_1596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1596_, 0, v_a_1595_);
return v___x_1596_;
}
default: 
{
uint8_t v_mvars_1597_; 
v_mvars_1597_ = lean_ctor_get_uint8(v_a_1580_, sizeof(void*)*1);
if (v_mvars_1597_ == 0)
{
lean_object* v___x_1598_; 
lean_dec_ref(v_l_1579_);
v___x_1598_ = ((lean_object*)(l_Lean_Level_PP_toResult___closed__3));
return v___x_1598_;
}
else
{
lean_object* v_a_1599_; lean_object* v_lIndex_x3f_1600_; lean_object* v___x_1601_; 
v_a_1599_ = lean_ctor_get(v_l_1579_, 0);
lean_inc_n(v_a_1599_, 2);
lean_dec_ref(v_l_1579_);
v_lIndex_x3f_1600_ = lean_ctor_get(v_a_1580_, 0);
lean_inc_ref(v_lIndex_x3f_1600_);
v___x_1601_ = lean_apply_1(v_lIndex_x3f_1600_, v_a_1599_);
if (lean_obj_tag(v___x_1601_) == 1)
{
lean_object* v_val_1602_; lean_object* v___x_1604_; uint8_t v_isShared_1605_; uint8_t v_isSharedCheck_1613_; 
lean_dec(v_a_1599_);
v_val_1602_ = lean_ctor_get(v___x_1601_, 0);
v_isSharedCheck_1613_ = !lean_is_exclusive(v___x_1601_);
if (v_isSharedCheck_1613_ == 0)
{
v___x_1604_ = v___x_1601_;
v_isShared_1605_ = v_isSharedCheck_1613_;
goto v_resetjp_1603_;
}
else
{
lean_inc(v_val_1602_);
lean_dec(v___x_1601_);
v___x_1604_ = lean_box(0);
v_isShared_1605_ = v_isSharedCheck_1613_;
goto v_resetjp_1603_;
}
v_resetjp_1603_:
{
lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1611_; 
v___x_1606_ = ((lean_object*)(l_Lean_Level_PP_toResult___closed__5));
v___x_1607_ = lean_unsigned_to_nat(1u);
v___x_1608_ = lean_nat_add(v_val_1602_, v___x_1607_);
lean_dec(v_val_1602_);
v___x_1609_ = l_Lean_Name_num___override(v___x_1606_, v___x_1608_);
if (v_isShared_1605_ == 0)
{
lean_ctor_set_tag(v___x_1604_, 0);
lean_ctor_set(v___x_1604_, 0, v___x_1609_);
v___x_1611_ = v___x_1604_;
goto v_reusejp_1610_;
}
else
{
lean_object* v_reuseFailAlloc_1612_; 
v_reuseFailAlloc_1612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1612_, 0, v___x_1609_);
v___x_1611_ = v_reuseFailAlloc_1612_;
goto v_reusejp_1610_;
}
v_reusejp_1610_:
{
return v___x_1611_;
}
}
}
else
{
lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; 
lean_dec(v___x_1601_);
v___x_1614_ = ((lean_object*)(l_Lean_Level_PP_toResult___closed__7));
v___x_1615_ = ((lean_object*)(l_Lean_Level_PP_toResult___closed__9));
v___x_1616_ = l_Lean_Name_replacePrefix(v_a_1599_, v___x_1614_, v___x_1615_);
v___x_1617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1617_, 0, v___x_1616_);
return v___x_1617_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_toResult___boxed(lean_object* v_l_1618_, lean_object* v_a_1619_){
_start:
{
lean_object* v_res_1620_; 
v_res_1620_ = l_Lean_Level_PP_toResult(v_l_1618_, v_a_1619_);
lean_dec_ref(v_a_1619_);
return v_res_1620_;
}
}
static lean_object* _init_l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__1(void){
_start:
{
lean_object* v___x_1622_; lean_object* v___x_1623_; 
v___x_1622_ = ((lean_object*)(l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__0));
v___x_1623_ = lean_string_length(v___x_1622_);
return v___x_1623_;
}
}
static lean_object* _init_l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__2(void){
_start:
{
lean_object* v___x_1624_; lean_object* v___x_1625_; 
v___x_1624_ = lean_obj_once(&l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__1, &l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__1_once, _init_l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__1);
v___x_1625_ = lean_nat_to_int(v___x_1624_);
return v___x_1625_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse(lean_object* v_x_1630_, uint8_t v_x_1631_){
_start:
{
if (v_x_1631_ == 0)
{
lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; uint8_t v___x_1638_; lean_object* v___x_1639_; 
v___x_1632_ = lean_obj_once(&l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__2, &l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__2_once, _init_l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__2);
v___x_1633_ = ((lean_object*)(l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__3));
v___x_1634_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1634_, 0, v___x_1633_);
lean_ctor_set(v___x_1634_, 1, v_x_1630_);
v___x_1635_ = ((lean_object*)(l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__4));
v___x_1636_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1636_, 0, v___x_1634_);
lean_ctor_set(v___x_1636_, 1, v___x_1635_);
v___x_1637_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1637_, 0, v___x_1632_);
lean_ctor_set(v___x_1637_, 1, v___x_1636_);
v___x_1638_ = 0;
v___x_1639_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1639_, 0, v___x_1637_);
lean_ctor_set_uint8(v___x_1639_, sizeof(void*)*1, v___x_1638_);
return v___x_1639_;
}
else
{
return v_x_1630_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___boxed(lean_object* v_x_1640_, lean_object* v_x_1641_){
_start:
{
uint8_t v_x_57__boxed_1642_; lean_object* v_res_1643_; 
v_x_57__boxed_1642_ = lean_unbox(v_x_1641_);
v_res_1643_ = l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse(v_x_1640_, v_x_57__boxed_1642_);
return v_res_1643_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_format(lean_object* v_x_1653_, uint8_t v_x_1654_){
_start:
{
switch(lean_obj_tag(v_x_1653_))
{
case 0:
{
lean_object* v_a_1655_; lean_object* v___x_1657_; uint8_t v_isShared_1658_; uint8_t v_isSharedCheck_1664_; 
v_a_1655_ = lean_ctor_get(v_x_1653_, 0);
v_isSharedCheck_1664_ = !lean_is_exclusive(v_x_1653_);
if (v_isSharedCheck_1664_ == 0)
{
v___x_1657_ = v_x_1653_;
v_isShared_1658_ = v_isSharedCheck_1664_;
goto v_resetjp_1656_;
}
else
{
lean_inc(v_a_1655_);
lean_dec(v_x_1653_);
v___x_1657_ = lean_box(0);
v_isShared_1658_ = v_isSharedCheck_1664_;
goto v_resetjp_1656_;
}
v_resetjp_1656_:
{
uint8_t v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1662_; 
v___x_1659_ = 1;
v___x_1660_ = l_Lean_Name_toString(v_a_1655_, v___x_1659_);
if (v_isShared_1658_ == 0)
{
lean_ctor_set_tag(v___x_1657_, 3);
lean_ctor_set(v___x_1657_, 0, v___x_1660_);
v___x_1662_ = v___x_1657_;
goto v_reusejp_1661_;
}
else
{
lean_object* v_reuseFailAlloc_1663_; 
v_reuseFailAlloc_1663_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1663_, 0, v___x_1660_);
v___x_1662_ = v_reuseFailAlloc_1663_;
goto v_reusejp_1661_;
}
v_reusejp_1661_:
{
return v___x_1662_;
}
}
}
case 1:
{
lean_object* v_a_1665_; lean_object* v___x_1667_; uint8_t v_isShared_1668_; uint8_t v_isSharedCheck_1673_; 
v_a_1665_ = lean_ctor_get(v_x_1653_, 0);
v_isSharedCheck_1673_ = !lean_is_exclusive(v_x_1653_);
if (v_isSharedCheck_1673_ == 0)
{
v___x_1667_ = v_x_1653_;
v_isShared_1668_ = v_isSharedCheck_1673_;
goto v_resetjp_1666_;
}
else
{
lean_inc(v_a_1665_);
lean_dec(v_x_1653_);
v___x_1667_ = lean_box(0);
v_isShared_1668_ = v_isSharedCheck_1673_;
goto v_resetjp_1666_;
}
v_resetjp_1666_:
{
lean_object* v___x_1669_; lean_object* v___x_1671_; 
v___x_1669_ = l_Nat_reprFast(v_a_1665_);
if (v_isShared_1668_ == 0)
{
lean_ctor_set_tag(v___x_1667_, 3);
lean_ctor_set(v___x_1667_, 0, v___x_1669_);
v___x_1671_ = v___x_1667_;
goto v_reusejp_1670_;
}
else
{
lean_object* v_reuseFailAlloc_1672_; 
v_reuseFailAlloc_1672_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1672_, 0, v___x_1669_);
v___x_1671_ = v_reuseFailAlloc_1672_;
goto v_reusejp_1670_;
}
v_reusejp_1670_:
{
return v___x_1671_;
}
}
}
case 2:
{
lean_object* v_a_1674_; lean_object* v_a_1675_; lean_object* v___x_1677_; uint8_t v_isShared_1678_; uint8_t v_isSharedCheck_1694_; 
v_a_1674_ = lean_ctor_get(v_x_1653_, 0);
v_a_1675_ = lean_ctor_get(v_x_1653_, 1);
v_isSharedCheck_1694_ = !lean_is_exclusive(v_x_1653_);
if (v_isSharedCheck_1694_ == 0)
{
v___x_1677_ = v_x_1653_;
v_isShared_1678_ = v_isSharedCheck_1694_;
goto v_resetjp_1676_;
}
else
{
lean_inc(v_a_1675_);
lean_inc(v_a_1674_);
lean_dec(v_x_1653_);
v___x_1677_ = lean_box(0);
v_isShared_1678_ = v_isSharedCheck_1694_;
goto v_resetjp_1676_;
}
v_resetjp_1676_:
{
lean_object* v_zero_1679_; uint8_t v_isZero_1680_; 
v_zero_1679_ = lean_unsigned_to_nat(0u);
v_isZero_1680_ = lean_nat_dec_eq(v_a_1675_, v_zero_1679_);
if (v_isZero_1680_ == 1)
{
lean_del_object(v___x_1677_);
lean_dec(v_a_1675_);
v_x_1653_ = v_a_1674_;
goto _start;
}
else
{
lean_object* v_one_1682_; lean_object* v_n_1683_; lean_object* v_f_x27_1684_; lean_object* v___x_1685_; lean_object* v___x_1687_; 
v_one_1682_ = lean_unsigned_to_nat(1u);
v_n_1683_ = lean_nat_sub(v_a_1675_, v_one_1682_);
lean_dec(v_a_1675_);
v_f_x27_1684_ = l_Lean_Level_PP_Result_format(v_a_1674_, v_isZero_1680_);
v___x_1685_ = ((lean_object*)(l_Lean_Level_PP_Result_format___closed__1));
if (v_isShared_1678_ == 0)
{
lean_ctor_set_tag(v___x_1677_, 5);
lean_ctor_set(v___x_1677_, 1, v___x_1685_);
lean_ctor_set(v___x_1677_, 0, v_f_x27_1684_);
v___x_1687_ = v___x_1677_;
goto v_reusejp_1686_;
}
else
{
lean_object* v_reuseFailAlloc_1693_; 
v_reuseFailAlloc_1693_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1693_, 0, v_f_x27_1684_);
lean_ctor_set(v_reuseFailAlloc_1693_, 1, v___x_1685_);
v___x_1687_ = v_reuseFailAlloc_1693_;
goto v_reusejp_1686_;
}
v_reusejp_1686_:
{
lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; 
v___x_1688_ = lean_nat_add(v_n_1683_, v_one_1682_);
lean_dec(v_n_1683_);
v___x_1689_ = l_Nat_reprFast(v___x_1688_);
v___x_1690_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1690_, 0, v___x_1689_);
v___x_1691_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1691_, 0, v___x_1687_);
lean_ctor_set(v___x_1691_, 1, v___x_1690_);
v___x_1692_ = l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse(v___x_1691_, v_x_1654_);
return v___x_1692_;
}
}
}
}
case 3:
{
lean_object* v_a_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; uint8_t v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; 
v_a_1695_ = lean_ctor_get(v_x_1653_, 0);
lean_inc(v_a_1695_);
lean_dec_ref(v_x_1653_);
v___x_1696_ = ((lean_object*)(l_Lean_Level_PP_Result_format___closed__3));
v___x_1697_ = l___private_Lean_Level_0__Lean_Level_PP_Result_formatLst(v_a_1695_);
v___x_1698_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1698_, 0, v___x_1696_);
lean_ctor_set(v___x_1698_, 1, v___x_1697_);
v___x_1699_ = 0;
v___x_1700_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1700_, 0, v___x_1698_);
lean_ctor_set_uint8(v___x_1700_, sizeof(void*)*1, v___x_1699_);
v___x_1701_ = l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse(v___x_1700_, v_x_1654_);
return v___x_1701_;
}
default: 
{
lean_object* v_a_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; uint8_t v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; 
v_a_1702_ = lean_ctor_get(v_x_1653_, 0);
lean_inc(v_a_1702_);
lean_dec_ref(v_x_1653_);
v___x_1703_ = ((lean_object*)(l_Lean_Level_PP_Result_format___closed__5));
v___x_1704_ = l___private_Lean_Level_0__Lean_Level_PP_Result_formatLst(v_a_1702_);
v___x_1705_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1705_, 0, v___x_1703_);
lean_ctor_set(v___x_1705_, 1, v___x_1704_);
v___x_1706_ = 0;
v___x_1707_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1707_, 0, v___x_1705_);
lean_ctor_set_uint8(v___x_1707_, sizeof(void*)*1, v___x_1706_);
v___x_1708_ = l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse(v___x_1707_, v_x_1654_);
return v___x_1708_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_PP_Result_formatLst(lean_object* v_x_1709_){
_start:
{
if (lean_obj_tag(v_x_1709_) == 0)
{
lean_object* v___x_1710_; 
v___x_1710_ = lean_box(0);
return v___x_1710_;
}
else
{
lean_object* v_head_1711_; lean_object* v_tail_1712_; lean_object* v___x_1714_; uint8_t v_isShared_1715_; uint8_t v_isSharedCheck_1724_; 
v_head_1711_ = lean_ctor_get(v_x_1709_, 0);
v_tail_1712_ = lean_ctor_get(v_x_1709_, 1);
v_isSharedCheck_1724_ = !lean_is_exclusive(v_x_1709_);
if (v_isSharedCheck_1724_ == 0)
{
v___x_1714_ = v_x_1709_;
v_isShared_1715_ = v_isSharedCheck_1724_;
goto v_resetjp_1713_;
}
else
{
lean_inc(v_tail_1712_);
lean_inc(v_head_1711_);
lean_dec(v_x_1709_);
v___x_1714_ = lean_box(0);
v_isShared_1715_ = v_isSharedCheck_1724_;
goto v_resetjp_1713_;
}
v_resetjp_1713_:
{
lean_object* v___x_1716_; uint8_t v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1720_; 
v___x_1716_ = lean_box(1);
v___x_1717_ = 0;
v___x_1718_ = l_Lean_Level_PP_Result_format(v_head_1711_, v___x_1717_);
if (v_isShared_1715_ == 0)
{
lean_ctor_set_tag(v___x_1714_, 5);
lean_ctor_set(v___x_1714_, 1, v___x_1718_);
lean_ctor_set(v___x_1714_, 0, v___x_1716_);
v___x_1720_ = v___x_1714_;
goto v_reusejp_1719_;
}
else
{
lean_object* v_reuseFailAlloc_1723_; 
v_reuseFailAlloc_1723_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1723_, 0, v___x_1716_);
lean_ctor_set(v_reuseFailAlloc_1723_, 1, v___x_1718_);
v___x_1720_ = v_reuseFailAlloc_1723_;
goto v_reusejp_1719_;
}
v_reusejp_1719_:
{
lean_object* v___x_1721_; lean_object* v___x_1722_; 
v___x_1721_ = l___private_Lean_Level_0__Lean_Level_PP_Result_formatLst(v_tail_1712_);
v___x_1722_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1722_, 0, v___x_1720_);
lean_ctor_set(v___x_1722_, 1, v___x_1721_);
return v___x_1722_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_format___boxed(lean_object* v_x_1725_, lean_object* v_x_1726_){
_start:
{
uint8_t v_x_270__boxed_1727_; lean_object* v_res_1728_; 
v_x_270__boxed_1727_ = lean_unbox(v_x_1726_);
v_res_1728_ = l_Lean_Level_PP_Result_format(v_x_1725_, v_x_270__boxed_1727_);
return v_res_1728_;
}
}
static lean_object* _init_l_Lean_Level_PP_Result_quote___closed__0(void){
_start:
{
uint8_t v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; 
v___x_1729_ = 0;
v___x_1730_ = lean_box(0);
v___x_1731_ = l_Lean_SourceInfo_fromRef(v___x_1730_, v___x_1729_);
return v___x_1731_;
}
}
static lean_object* _init_l_Lean_Level_PP_Result_quote___closed__6(void){
_start:
{
lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; 
v___x_1741_ = ((lean_object*)(l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__0));
v___x_1742_ = lean_obj_once(&l_Lean_Level_PP_Result_quote___closed__0, &l_Lean_Level_PP_Result_quote___closed__0_once, _init_l_Lean_Level_PP_Result_quote___closed__0);
v___x_1743_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1743_, 0, v___x_1742_);
lean_ctor_set(v___x_1743_, 1, v___x_1741_);
return v___x_1743_;
}
}
static lean_object* _init_l_Lean_Level_PP_Result_quote___closed__7(void){
_start:
{
lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; 
v___x_1744_ = ((lean_object*)(l_Lean_instReprData___lam__0___closed__0));
v___x_1745_ = lean_obj_once(&l_Lean_Level_PP_Result_quote___closed__0, &l_Lean_Level_PP_Result_quote___closed__0_once, _init_l_Lean_Level_PP_Result_quote___closed__0);
v___x_1746_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1746_, 0, v___x_1745_);
lean_ctor_set(v___x_1746_, 1, v___x_1744_);
return v___x_1746_;
}
}
static lean_object* _init_l_Lean_Level_PP_Result_quote___closed__12(void){
_start:
{
lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; 
v___x_1759_ = ((lean_object*)(l_Lean_Level_PP_Result_format___closed__2));
v___x_1760_ = lean_obj_once(&l_Lean_Level_PP_Result_quote___closed__0, &l_Lean_Level_PP_Result_quote___closed__0_once, _init_l_Lean_Level_PP_Result_quote___closed__0);
v___x_1761_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1761_, 0, v___x_1760_);
lean_ctor_set(v___x_1761_, 1, v___x_1759_);
return v___x_1761_;
}
}
static lean_object* _init_l_Lean_Level_PP_Result_quote___closed__15(void){
_start:
{
lean_object* v___x_1765_; 
v___x_1765_ = l_Array_mkArray0(lean_box(0));
return v___x_1765_;
}
}
static lean_object* _init_l_Lean_Level_PP_Result_quote___closed__17(void){
_start:
{
lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; 
v___x_1771_ = ((lean_object*)(l_Lean_Level_PP_Result_format___closed__4));
v___x_1772_ = lean_obj_once(&l_Lean_Level_PP_Result_quote___closed__0, &l_Lean_Level_PP_Result_quote___closed__0_once, _init_l_Lean_Level_PP_Result_quote___closed__0);
v___x_1773_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1773_, 0, v___x_1772_);
lean_ctor_set(v___x_1773_, 1, v___x_1771_);
return v___x_1773_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_quote(lean_object* v_r_1774_, lean_object* v_prec_1775_){
_start:
{
lean_object* v_s_1777_; 
switch(lean_obj_tag(v_r_1774_))
{
case 0:
{
lean_object* v_a_1785_; lean_object* v___x_1786_; 
v_a_1785_ = lean_ctor_get(v_r_1774_, 0);
lean_inc(v_a_1785_);
lean_dec_ref(v_r_1774_);
v___x_1786_ = lean_mk_syntax_ident(v_a_1785_);
return v___x_1786_;
}
case 1:
{
lean_object* v_a_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; 
v_a_1787_ = lean_ctor_get(v_r_1774_, 0);
lean_inc(v_a_1787_);
lean_dec_ref(v_r_1774_);
v___x_1788_ = l_Nat_reprFast(v_a_1787_);
v___x_1789_ = lean_box(2);
v___x_1790_ = l_Lean_Syntax_mkNumLit(v___x_1788_, v___x_1789_);
return v___x_1790_;
}
case 2:
{
lean_object* v_a_1791_; lean_object* v_a_1792_; lean_object* v___x_1794_; uint8_t v_isShared_1795_; uint8_t v_isSharedCheck_1815_; 
v_a_1791_ = lean_ctor_get(v_r_1774_, 0);
v_a_1792_ = lean_ctor_get(v_r_1774_, 1);
v_isSharedCheck_1815_ = !lean_is_exclusive(v_r_1774_);
if (v_isSharedCheck_1815_ == 0)
{
v___x_1794_ = v_r_1774_;
v_isShared_1795_ = v_isSharedCheck_1815_;
goto v_resetjp_1793_;
}
else
{
lean_inc(v_a_1792_);
lean_inc(v_a_1791_);
lean_dec(v_r_1774_);
v___x_1794_ = lean_box(0);
v_isShared_1795_ = v_isSharedCheck_1815_;
goto v_resetjp_1793_;
}
v_resetjp_1793_:
{
lean_object* v_zero_1796_; uint8_t v_isZero_1797_; 
v_zero_1796_ = lean_unsigned_to_nat(0u);
v_isZero_1797_ = lean_nat_dec_eq(v_a_1792_, v_zero_1796_);
if (v_isZero_1797_ == 1)
{
lean_del_object(v___x_1794_);
lean_dec(v_a_1792_);
v_r_1774_ = v_a_1791_;
goto _start;
}
else
{
lean_object* v_one_1799_; lean_object* v_n_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1808_; 
v_one_1799_ = lean_unsigned_to_nat(1u);
v_n_1800_ = lean_nat_sub(v_a_1792_, v_one_1799_);
lean_dec(v_a_1792_);
v___x_1801_ = lean_box(0);
v___x_1802_ = l_Lean_SourceInfo_fromRef(v___x_1801_, v_isZero_1797_);
v___x_1803_ = ((lean_object*)(l_Lean_Level_PP_Result_quote___closed__9));
v___x_1804_ = lean_unsigned_to_nat(65u);
v___x_1805_ = l_Lean_Level_PP_Result_quote(v_a_1791_, v___x_1804_);
v___x_1806_ = ((lean_object*)(l_Lean_Level_PP_Result_quote___closed__10));
lean_inc(v___x_1802_);
if (v_isShared_1795_ == 0)
{
lean_ctor_set(v___x_1794_, 1, v___x_1806_);
lean_ctor_set(v___x_1794_, 0, v___x_1802_);
v___x_1808_ = v___x_1794_;
goto v_reusejp_1807_;
}
else
{
lean_object* v_reuseFailAlloc_1814_; 
v_reuseFailAlloc_1814_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1814_, 0, v___x_1802_);
lean_ctor_set(v_reuseFailAlloc_1814_, 1, v___x_1806_);
v___x_1808_ = v_reuseFailAlloc_1814_;
goto v_reusejp_1807_;
}
v_reusejp_1807_:
{
lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; 
v___x_1809_ = lean_nat_add(v_n_1800_, v_one_1799_);
lean_dec(v_n_1800_);
v___x_1810_ = l_Nat_reprFast(v___x_1809_);
v___x_1811_ = lean_box(2);
v___x_1812_ = l_Lean_Syntax_mkNumLit(v___x_1810_, v___x_1811_);
v___x_1813_ = l_Lean_Syntax_node3(v___x_1802_, v___x_1803_, v___x_1805_, v___x_1808_, v___x_1812_);
v_s_1777_ = v___x_1813_;
goto v___jp_1776_;
}
}
}
}
case 3:
{
lean_object* v_a_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; size_t v_sz_1823_; size_t v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; 
v_a_1816_ = lean_ctor_get(v_r_1774_, 0);
lean_inc(v_a_1816_);
lean_dec_ref(v_r_1774_);
v___x_1817_ = lean_obj_once(&l_Lean_Level_PP_Result_quote___closed__0, &l_Lean_Level_PP_Result_quote___closed__0_once, _init_l_Lean_Level_PP_Result_quote___closed__0);
v___x_1818_ = ((lean_object*)(l_Lean_Level_PP_Result_quote___closed__11));
v___x_1819_ = lean_obj_once(&l_Lean_Level_PP_Result_quote___closed__12, &l_Lean_Level_PP_Result_quote___closed__12_once, _init_l_Lean_Level_PP_Result_quote___closed__12);
v___x_1820_ = ((lean_object*)(l_Lean_Level_PP_Result_quote___closed__14));
v___x_1821_ = lean_obj_once(&l_Lean_Level_PP_Result_quote___closed__15, &l_Lean_Level_PP_Result_quote___closed__15_once, _init_l_Lean_Level_PP_Result_quote___closed__15);
v___x_1822_ = lean_array_mk(v_a_1816_);
v_sz_1823_ = lean_array_size(v___x_1822_);
v___x_1824_ = ((size_t)0ULL);
v___x_1825_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Level_PP_Result_quote_spec__0(v_sz_1823_, v___x_1824_, v___x_1822_);
v___x_1826_ = l_Array_append___redArg(v___x_1821_, v___x_1825_);
lean_dec_ref(v___x_1825_);
v___x_1827_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1827_, 0, v___x_1817_);
lean_ctor_set(v___x_1827_, 1, v___x_1820_);
lean_ctor_set(v___x_1827_, 2, v___x_1826_);
v___x_1828_ = l_Lean_Syntax_node2(v___x_1817_, v___x_1818_, v___x_1819_, v___x_1827_);
v_s_1777_ = v___x_1828_;
goto v___jp_1776_;
}
default: 
{
lean_object* v_a_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; size_t v_sz_1836_; size_t v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; 
v_a_1829_ = lean_ctor_get(v_r_1774_, 0);
lean_inc(v_a_1829_);
lean_dec_ref(v_r_1774_);
v___x_1830_ = lean_obj_once(&l_Lean_Level_PP_Result_quote___closed__0, &l_Lean_Level_PP_Result_quote___closed__0_once, _init_l_Lean_Level_PP_Result_quote___closed__0);
v___x_1831_ = ((lean_object*)(l_Lean_Level_PP_Result_quote___closed__16));
v___x_1832_ = lean_obj_once(&l_Lean_Level_PP_Result_quote___closed__17, &l_Lean_Level_PP_Result_quote___closed__17_once, _init_l_Lean_Level_PP_Result_quote___closed__17);
v___x_1833_ = ((lean_object*)(l_Lean_Level_PP_Result_quote___closed__14));
v___x_1834_ = lean_obj_once(&l_Lean_Level_PP_Result_quote___closed__15, &l_Lean_Level_PP_Result_quote___closed__15_once, _init_l_Lean_Level_PP_Result_quote___closed__15);
v___x_1835_ = lean_array_mk(v_a_1829_);
v_sz_1836_ = lean_array_size(v___x_1835_);
v___x_1837_ = ((size_t)0ULL);
v___x_1838_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Level_PP_Result_quote_spec__0(v_sz_1836_, v___x_1837_, v___x_1835_);
v___x_1839_ = l_Array_append___redArg(v___x_1834_, v___x_1838_);
lean_dec_ref(v___x_1838_);
v___x_1840_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1840_, 0, v___x_1830_);
lean_ctor_set(v___x_1840_, 1, v___x_1833_);
lean_ctor_set(v___x_1840_, 2, v___x_1839_);
v___x_1841_ = l_Lean_Syntax_node2(v___x_1830_, v___x_1831_, v___x_1832_, v___x_1840_);
v_s_1777_ = v___x_1841_;
goto v___jp_1776_;
}
}
v___jp_1776_:
{
lean_object* v___x_1778_; uint8_t v___x_1779_; 
v___x_1778_ = lean_unsigned_to_nat(0u);
v___x_1779_ = lean_nat_dec_lt(v___x_1778_, v_prec_1775_);
if (v___x_1779_ == 0)
{
return v_s_1777_;
}
else
{
lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; 
v___x_1780_ = lean_obj_once(&l_Lean_Level_PP_Result_quote___closed__0, &l_Lean_Level_PP_Result_quote___closed__0_once, _init_l_Lean_Level_PP_Result_quote___closed__0);
v___x_1781_ = ((lean_object*)(l_Lean_Level_PP_Result_quote___closed__5));
v___x_1782_ = lean_obj_once(&l_Lean_Level_PP_Result_quote___closed__6, &l_Lean_Level_PP_Result_quote___closed__6_once, _init_l_Lean_Level_PP_Result_quote___closed__6);
v___x_1783_ = lean_obj_once(&l_Lean_Level_PP_Result_quote___closed__7, &l_Lean_Level_PP_Result_quote___closed__7_once, _init_l_Lean_Level_PP_Result_quote___closed__7);
v___x_1784_ = l_Lean_Syntax_node3(v___x_1780_, v___x_1781_, v___x_1782_, v_s_1777_, v___x_1783_);
return v___x_1784_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Level_PP_Result_quote_spec__0(size_t v_sz_1842_, size_t v_i_1843_, lean_object* v_bs_1844_){
_start:
{
uint8_t v___x_1845_; 
v___x_1845_ = lean_usize_dec_lt(v_i_1843_, v_sz_1842_);
if (v___x_1845_ == 0)
{
return v_bs_1844_;
}
else
{
lean_object* v_v_1846_; lean_object* v___x_1847_; lean_object* v_bs_x27_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; size_t v___x_1851_; size_t v___x_1852_; lean_object* v___x_1853_; 
v_v_1846_ = lean_array_uget(v_bs_1844_, v_i_1843_);
v___x_1847_ = lean_unsigned_to_nat(0u);
v_bs_x27_1848_ = lean_array_uset(v_bs_1844_, v_i_1843_, v___x_1847_);
v___x_1849_ = lean_unsigned_to_nat(1024u);
v___x_1850_ = l_Lean_Level_PP_Result_quote(v_v_1846_, v___x_1849_);
v___x_1851_ = ((size_t)1ULL);
v___x_1852_ = lean_usize_add(v_i_1843_, v___x_1851_);
v___x_1853_ = lean_array_uset(v_bs_x27_1848_, v_i_1843_, v___x_1850_);
v_i_1843_ = v___x_1852_;
v_bs_1844_ = v___x_1853_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Level_PP_Result_quote_spec__0___boxed(lean_object* v_sz_1855_, lean_object* v_i_1856_, lean_object* v_bs_1857_){
_start:
{
size_t v_sz_boxed_1858_; size_t v_i_boxed_1859_; lean_object* v_res_1860_; 
v_sz_boxed_1858_ = lean_unbox_usize(v_sz_1855_);
lean_dec(v_sz_1855_);
v_i_boxed_1859_ = lean_unbox_usize(v_i_1856_);
lean_dec(v_i_1856_);
v_res_1860_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Level_PP_Result_quote_spec__0(v_sz_boxed_1858_, v_i_boxed_1859_, v_bs_1857_);
return v_res_1860_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_quote___boxed(lean_object* v_r_1861_, lean_object* v_prec_1862_){
_start:
{
lean_object* v_res_1863_; 
v_res_1863_ = l_Lean_Level_PP_Result_quote(v_r_1861_, v_prec_1862_);
lean_dec(v_prec_1862_);
return v_res_1863_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_format(lean_object* v_u_1864_, uint8_t v_mvars_1865_, lean_object* v_lIndex_x3f_1866_){
_start:
{
lean_object* v___x_1867_; lean_object* v___x_1868_; uint8_t v___x_1869_; lean_object* v___x_1870_; 
v___x_1867_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1867_, 0, v_lIndex_x3f_1866_);
lean_ctor_set_uint8(v___x_1867_, sizeof(void*)*1, v_mvars_1865_);
v___x_1868_ = l_Lean_Level_PP_toResult(v_u_1864_, v___x_1867_);
lean_dec_ref(v___x_1867_);
v___x_1869_ = 1;
v___x_1870_ = l_Lean_Level_PP_Result_format(v___x_1868_, v___x_1869_);
return v___x_1870_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_format___boxed(lean_object* v_u_1871_, lean_object* v_mvars_1872_, lean_object* v_lIndex_x3f_1873_){
_start:
{
uint8_t v_mvars_boxed_1874_; lean_object* v_res_1875_; 
v_mvars_boxed_1874_ = lean_unbox(v_mvars_1872_);
v_res_1875_ = l_Lean_Level_format(v_u_1871_, v_mvars_boxed_1874_, v_lIndex_x3f_1873_);
return v_res_1875_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_instToFormat___lam__0(lean_object* v_x_1876_){
_start:
{
lean_object* v___x_1877_; 
v___x_1877_ = lean_box(0);
return v___x_1877_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_instToFormat___lam__0___boxed(lean_object* v_x_1878_){
_start:
{
lean_object* v_res_1879_; 
v_res_1879_ = l_Lean_Level_instToFormat___lam__0(v_x_1878_);
lean_dec(v_x_1878_);
return v_res_1879_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_instToFormat___lam__1(lean_object* v___f_1880_, lean_object* v_u_1881_){
_start:
{
uint8_t v___x_1882_; lean_object* v___x_1883_; 
v___x_1882_ = 1;
v___x_1883_ = l_Lean_Level_format(v_u_1881_, v___x_1882_, v___f_1880_);
return v___x_1883_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_instToString___lam__1(lean_object* v___f_1888_, lean_object* v_u_1889_){
_start:
{
uint8_t v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; 
v___x_1890_ = 1;
v___x_1891_ = l_Lean_Level_format(v_u_1889_, v___x_1890_, v___f_1888_);
v___x_1892_ = l_Std_Format_defWidth;
v___x_1893_ = lean_unsigned_to_nat(0u);
v___x_1894_ = l_Std_Format_pretty(v___x_1891_, v___x_1892_, v___x_1893_, v___x_1893_);
return v___x_1894_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_quote(lean_object* v_u_1898_, lean_object* v_prec_1899_, uint8_t v_mvars_1900_, lean_object* v_lIndex_x3f_1901_){
_start:
{
lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; 
v___x_1902_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1902_, 0, v_lIndex_x3f_1901_);
lean_ctor_set_uint8(v___x_1902_, sizeof(void*)*1, v_mvars_1900_);
v___x_1903_ = l_Lean_Level_PP_toResult(v_u_1898_, v___x_1902_);
lean_dec_ref(v___x_1902_);
v___x_1904_ = l_Lean_Level_PP_Result_quote(v___x_1903_, v_prec_1899_);
return v___x_1904_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_quote___boxed(lean_object* v_u_1905_, lean_object* v_prec_1906_, lean_object* v_mvars_1907_, lean_object* v_lIndex_x3f_1908_){
_start:
{
uint8_t v_mvars_boxed_1909_; lean_object* v_res_1910_; 
v_mvars_boxed_1909_ = lean_unbox(v_mvars_1907_);
v_res_1910_ = l_Lean_Level_quote(v_u_1905_, v_prec_1906_, v_mvars_boxed_1909_, v_lIndex_x3f_1908_);
lean_dec(v_prec_1906_);
return v_res_1910_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_instQuoteMkStr1___lam__1(lean_object* v___f_1911_, lean_object* v_u_1912_){
_start:
{
lean_object* v___x_1913_; uint8_t v___x_1914_; lean_object* v___x_1915_; 
v___x_1913_ = lean_unsigned_to_nat(0u);
v___x_1914_ = 1;
v___x_1915_ = l_Lean_Level_quote(v_u_1912_, v___x_1913_, v___x_1914_, v___f_1911_);
return v___x_1915_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Level_0__Lean_mkLevelMaxCore___lam__0(lean_object* v_u_1919_, lean_object* v_v_1920_){
_start:
{
uint8_t v___y_1922_; uint8_t v___x_1928_; 
v___x_1928_ = l_Lean_Level_isExplicit(v_v_1920_);
if (v___x_1928_ == 0)
{
v___y_1922_ = v___x_1928_;
goto v___jp_1921_;
}
else
{
lean_object* v___x_1929_; lean_object* v___x_1930_; uint8_t v___x_1931_; 
v___x_1929_ = l_Lean_Level_getOffset(v_v_1920_);
v___x_1930_ = l_Lean_Level_getOffset(v_u_1919_);
v___x_1931_ = lean_nat_dec_le(v___x_1929_, v___x_1930_);
lean_dec(v___x_1930_);
lean_dec(v___x_1929_);
v___y_1922_ = v___x_1931_;
goto v___jp_1921_;
}
v___jp_1921_:
{
uint8_t v___x_1923_; 
v___x_1923_ = 1;
if (v___y_1922_ == 0)
{
if (lean_obj_tag(v_u_1919_) == 2)
{
lean_object* v_a_1924_; lean_object* v_a_1925_; uint8_t v___x_1926_; 
v_a_1924_ = lean_ctor_get(v_u_1919_, 0);
v_a_1925_ = lean_ctor_get(v_u_1919_, 1);
v___x_1926_ = lean_level_eq(v_v_1920_, v_a_1924_);
if (v___x_1926_ == 0)
{
uint8_t v___x_1927_; 
v___x_1927_ = lean_level_eq(v_v_1920_, v_a_1925_);
return v___x_1927_;
}
else
{
return v___x_1923_;
}
}
else
{
return v___y_1922_;
}
}
else
{
return v___x_1923_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_mkLevelMaxCore___lam__0___boxed(lean_object* v_u_1932_, lean_object* v_v_1933_){
_start:
{
uint8_t v_res_1934_; lean_object* v_r_1935_; 
v_res_1934_ = l___private_Lean_Level_0__Lean_mkLevelMaxCore___lam__0(v_u_1932_, v_v_1933_);
lean_dec(v_v_1933_);
lean_dec(v_u_1932_);
v_r_1935_ = lean_box(v_res_1934_);
return v_r_1935_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_mkLevelMaxCore(lean_object* v_u_1936_, lean_object* v_v_1937_, lean_object* v_elseK_1938_){
_start:
{
uint8_t v___x_1939_; 
v___x_1939_ = lean_level_eq(v_u_1936_, v_v_1937_);
if (v___x_1939_ == 0)
{
uint8_t v___x_1940_; 
v___x_1940_ = l_Lean_Level_isZero(v_u_1936_);
if (v___x_1940_ == 0)
{
uint8_t v___x_1941_; 
v___x_1941_ = l_Lean_Level_isZero(v_v_1937_);
if (v___x_1941_ == 0)
{
uint8_t v___x_1942_; 
v___x_1942_ = l___private_Lean_Level_0__Lean_mkLevelMaxCore___lam__0(v_u_1936_, v_v_1937_);
if (v___x_1942_ == 0)
{
uint8_t v___x_1943_; 
v___x_1943_ = l___private_Lean_Level_0__Lean_mkLevelMaxCore___lam__0(v_v_1937_, v_u_1936_);
if (v___x_1943_ == 0)
{
lean_object* v___x_1944_; lean_object* v___x_1945_; uint8_t v___x_1946_; 
v___x_1944_ = l_Lean_Level_getLevelOffset(v_u_1936_);
v___x_1945_ = l_Lean_Level_getLevelOffset(v_v_1937_);
v___x_1946_ = lean_level_eq(v___x_1944_, v___x_1945_);
lean_dec(v___x_1945_);
lean_dec(v___x_1944_);
if (v___x_1946_ == 0)
{
lean_object* v___x_1947_; lean_object* v___x_1948_; 
v___x_1947_ = lean_box(0);
v___x_1948_ = lean_apply_1(v_elseK_1938_, v___x_1947_);
return v___x_1948_;
}
else
{
lean_object* v___x_1949_; lean_object* v___x_1950_; uint8_t v___x_1951_; 
lean_dec_ref(v_elseK_1938_);
v___x_1949_ = l_Lean_Level_getOffset(v_v_1937_);
v___x_1950_ = l_Lean_Level_getOffset(v_u_1936_);
v___x_1951_ = lean_nat_dec_le(v___x_1949_, v___x_1950_);
lean_dec(v___x_1950_);
lean_dec(v___x_1949_);
if (v___x_1951_ == 0)
{
lean_inc(v_v_1937_);
return v_v_1937_;
}
else
{
lean_inc(v_u_1936_);
return v_u_1936_;
}
}
}
else
{
lean_dec_ref(v_elseK_1938_);
lean_inc(v_v_1937_);
return v_v_1937_;
}
}
else
{
lean_dec_ref(v_elseK_1938_);
lean_inc(v_u_1936_);
return v_u_1936_;
}
}
else
{
lean_dec_ref(v_elseK_1938_);
lean_inc(v_u_1936_);
return v_u_1936_;
}
}
else
{
lean_dec_ref(v_elseK_1938_);
lean_inc(v_v_1937_);
return v_v_1937_;
}
}
else
{
lean_dec_ref(v_elseK_1938_);
lean_inc(v_u_1936_);
return v_u_1936_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_mkLevelMaxCore___boxed(lean_object* v_u_1952_, lean_object* v_v_1953_, lean_object* v_elseK_1954_){
_start:
{
lean_object* v_res_1955_; 
v_res_1955_ = l___private_Lean_Level_0__Lean_mkLevelMaxCore(v_u_1952_, v_v_1953_, v_elseK_1954_);
lean_dec(v_v_1953_);
lean_dec(v_u_1952_);
return v_res_1955_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLevelMax_x27(lean_object* v_u_1956_, lean_object* v_v_1957_){
_start:
{
uint8_t v___x_1958_; 
v___x_1958_ = lean_level_eq(v_u_1956_, v_v_1957_);
if (v___x_1958_ == 0)
{
uint8_t v___x_1959_; 
v___x_1959_ = l_Lean_Level_isZero(v_u_1956_);
if (v___x_1959_ == 0)
{
uint8_t v___x_1960_; 
v___x_1960_ = l_Lean_Level_isZero(v_v_1957_);
if (v___x_1960_ == 0)
{
uint8_t v___x_1961_; 
v___x_1961_ = l___private_Lean_Level_0__Lean_mkLevelMaxCore___lam__0(v_u_1956_, v_v_1957_);
if (v___x_1961_ == 0)
{
uint8_t v___x_1962_; 
v___x_1962_ = l___private_Lean_Level_0__Lean_mkLevelMaxCore___lam__0(v_v_1957_, v_u_1956_);
if (v___x_1962_ == 0)
{
lean_object* v___x_1963_; lean_object* v___x_1964_; uint8_t v___x_1965_; 
v___x_1963_ = l_Lean_Level_getLevelOffset(v_u_1956_);
v___x_1964_ = l_Lean_Level_getLevelOffset(v_v_1957_);
v___x_1965_ = lean_level_eq(v___x_1963_, v___x_1964_);
lean_dec(v___x_1964_);
lean_dec(v___x_1963_);
if (v___x_1965_ == 0)
{
lean_object* v___x_1966_; 
v___x_1966_ = l_Lean_Level_max___override(v_u_1956_, v_v_1957_);
return v___x_1966_;
}
else
{
lean_object* v___x_1967_; lean_object* v___x_1968_; uint8_t v___x_1969_; 
v___x_1967_ = l_Lean_Level_getOffset(v_v_1957_);
v___x_1968_ = l_Lean_Level_getOffset(v_u_1956_);
v___x_1969_ = lean_nat_dec_le(v___x_1967_, v___x_1968_);
lean_dec(v___x_1968_);
lean_dec(v___x_1967_);
if (v___x_1969_ == 0)
{
lean_dec(v_u_1956_);
return v_v_1957_;
}
else
{
lean_dec(v_v_1957_);
return v_u_1956_;
}
}
}
else
{
lean_dec(v_u_1956_);
return v_v_1957_;
}
}
else
{
lean_dec(v_v_1957_);
return v_u_1956_;
}
}
else
{
lean_dec(v_v_1957_);
return v_u_1956_;
}
}
else
{
lean_dec(v_u_1956_);
return v_v_1957_;
}
}
else
{
lean_dec(v_v_1957_);
return v_u_1956_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_simpLevelMax_x27(lean_object* v_u_1970_, lean_object* v_v_1971_, lean_object* v_d_1972_){
_start:
{
uint8_t v___x_1973_; 
v___x_1973_ = lean_level_eq(v_u_1970_, v_v_1971_);
if (v___x_1973_ == 0)
{
uint8_t v___x_1974_; 
v___x_1974_ = l_Lean_Level_isZero(v_u_1970_);
if (v___x_1974_ == 0)
{
uint8_t v___x_1975_; 
v___x_1975_ = l_Lean_Level_isZero(v_v_1971_);
if (v___x_1975_ == 0)
{
uint8_t v___x_1976_; 
v___x_1976_ = l___private_Lean_Level_0__Lean_mkLevelMaxCore___lam__0(v_u_1970_, v_v_1971_);
if (v___x_1976_ == 0)
{
uint8_t v___x_1977_; 
v___x_1977_ = l___private_Lean_Level_0__Lean_mkLevelMaxCore___lam__0(v_v_1971_, v_u_1970_);
if (v___x_1977_ == 0)
{
lean_object* v___x_1978_; lean_object* v___x_1979_; uint8_t v___x_1980_; 
v___x_1978_ = l_Lean_Level_getLevelOffset(v_u_1970_);
v___x_1979_ = l_Lean_Level_getLevelOffset(v_v_1971_);
v___x_1980_ = lean_level_eq(v___x_1978_, v___x_1979_);
lean_dec(v___x_1979_);
lean_dec(v___x_1978_);
if (v___x_1980_ == 0)
{
lean_inc(v_d_1972_);
return v_d_1972_;
}
else
{
lean_object* v___x_1981_; lean_object* v___x_1982_; uint8_t v___x_1983_; 
v___x_1981_ = l_Lean_Level_getOffset(v_v_1971_);
v___x_1982_ = l_Lean_Level_getOffset(v_u_1970_);
v___x_1983_ = lean_nat_dec_le(v___x_1981_, v___x_1982_);
lean_dec(v___x_1982_);
lean_dec(v___x_1981_);
if (v___x_1983_ == 0)
{
lean_inc(v_v_1971_);
return v_v_1971_;
}
else
{
lean_inc(v_u_1970_);
return v_u_1970_;
}
}
}
else
{
lean_inc(v_v_1971_);
return v_v_1971_;
}
}
else
{
lean_inc(v_u_1970_);
return v_u_1970_;
}
}
else
{
lean_inc(v_u_1970_);
return v_u_1970_;
}
}
else
{
lean_inc(v_v_1971_);
return v_v_1971_;
}
}
else
{
lean_inc(v_u_1970_);
return v_u_1970_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_simpLevelMax_x27___boxed(lean_object* v_u_1984_, lean_object* v_v_1985_, lean_object* v_d_1986_){
_start:
{
lean_object* v_res_1987_; 
v_res_1987_ = l_Lean_simpLevelMax_x27(v_u_1984_, v_v_1985_, v_d_1986_);
lean_dec(v_d_1986_);
lean_dec(v_v_1985_);
lean_dec(v_u_1984_);
return v_res_1987_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_mkLevelIMaxCore(lean_object* v_u_1988_, lean_object* v_v_1989_, lean_object* v_elseK_1990_){
_start:
{
uint8_t v___x_1991_; 
v___x_1991_ = l_Lean_Level_isNeverZero(v_v_1989_);
if (v___x_1991_ == 0)
{
uint8_t v___x_1992_; 
v___x_1992_ = l_Lean_Level_isZero(v_v_1989_);
if (v___x_1992_ == 0)
{
uint8_t v___x_1993_; 
v___x_1993_ = l_Lean_Level_isZero(v_u_1988_);
if (v___x_1993_ == 0)
{
uint8_t v___x_1994_; 
v___x_1994_ = lean_level_eq(v_u_1988_, v_v_1989_);
lean_dec(v_v_1989_);
if (v___x_1994_ == 0)
{
lean_object* v___x_1995_; lean_object* v___x_1996_; 
lean_dec(v_u_1988_);
v___x_1995_ = lean_box(0);
v___x_1996_ = lean_apply_1(v_elseK_1990_, v___x_1995_);
return v___x_1996_;
}
else
{
lean_dec_ref(v_elseK_1990_);
return v_u_1988_;
}
}
else
{
lean_dec_ref(v_elseK_1990_);
lean_dec(v_u_1988_);
return v_v_1989_;
}
}
else
{
lean_dec_ref(v_elseK_1990_);
lean_dec(v_u_1988_);
return v_v_1989_;
}
}
else
{
lean_object* v___x_1997_; 
lean_dec_ref(v_elseK_1990_);
v___x_1997_ = l_Lean_mkLevelMax_x27(v_u_1988_, v_v_1989_);
return v___x_1997_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkLevelIMax_x27(lean_object* v_u_1998_, lean_object* v_v_1999_){
_start:
{
uint8_t v___x_2000_; 
v___x_2000_ = l_Lean_Level_isNeverZero(v_v_1999_);
if (v___x_2000_ == 0)
{
uint8_t v___x_2001_; 
v___x_2001_ = l_Lean_Level_isZero(v_v_1999_);
if (v___x_2001_ == 0)
{
uint8_t v___x_2002_; 
v___x_2002_ = l_Lean_Level_isZero(v_u_1998_);
if (v___x_2002_ == 0)
{
uint8_t v___x_2003_; 
v___x_2003_ = lean_level_eq(v_u_1998_, v_v_1999_);
if (v___x_2003_ == 0)
{
lean_object* v___x_2004_; 
v___x_2004_ = l_Lean_Level_imax___override(v_u_1998_, v_v_1999_);
return v___x_2004_;
}
else
{
lean_dec(v_v_1999_);
return v_u_1998_;
}
}
else
{
lean_dec(v_u_1998_);
return v_v_1999_;
}
}
else
{
lean_dec(v_u_1998_);
return v_v_1999_;
}
}
else
{
lean_object* v___x_2005_; 
v___x_2005_ = l_Lean_mkLevelMax_x27(v_u_1998_, v_v_1999_);
return v___x_2005_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_simpLevelIMax_x27(lean_object* v_u_2006_, lean_object* v_v_2007_, lean_object* v_d_2008_){
_start:
{
uint8_t v___x_2009_; 
v___x_2009_ = l_Lean_Level_isNeverZero(v_v_2007_);
if (v___x_2009_ == 0)
{
uint8_t v___x_2010_; 
v___x_2010_ = l_Lean_Level_isZero(v_v_2007_);
if (v___x_2010_ == 0)
{
uint8_t v___x_2011_; 
v___x_2011_ = l_Lean_Level_isZero(v_u_2006_);
if (v___x_2011_ == 0)
{
uint8_t v___x_2012_; 
v___x_2012_ = lean_level_eq(v_u_2006_, v_v_2007_);
lean_dec(v_v_2007_);
if (v___x_2012_ == 0)
{
lean_dec(v_u_2006_);
lean_inc(v_d_2008_);
return v_d_2008_;
}
else
{
return v_u_2006_;
}
}
else
{
lean_dec(v_u_2006_);
return v_v_2007_;
}
}
else
{
lean_dec(v_u_2006_);
return v_v_2007_;
}
}
else
{
lean_object* v___x_2013_; 
v___x_2013_ = l_Lean_mkLevelMax_x27(v_u_2006_, v_v_2007_);
return v___x_2013_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_simpLevelIMax_x27___boxed(lean_object* v_u_2014_, lean_object* v_v_2015_, lean_object* v_d_2016_){
_start:
{
lean_object* v_res_2017_; 
v_res_2017_ = l_Lean_simpLevelIMax_x27(v_u_2014_, v_v_2015_, v_d_2016_);
lean_dec(v_d_2016_);
return v_res_2017_;
}
}
static lean_object* _init_l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl___closed__2(void){
_start:
{
lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; 
v___x_2020_ = ((lean_object*)(l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl___closed__1));
v___x_2021_ = lean_unsigned_to_nat(14u);
v___x_2022_ = lean_unsigned_to_nat(564u);
v___x_2023_ = ((lean_object*)(l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl___closed__0));
v___x_2024_ = ((lean_object*)(l_Lean_Level_mvarId_x21___closed__0));
v___x_2025_ = l_mkPanicMessageWithDecl(v___x_2024_, v___x_2023_, v___x_2022_, v___x_2021_, v___x_2020_);
return v___x_2025_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl(lean_object* v_lvl_2026_, lean_object* v_newLvl_2027_){
_start:
{
if (lean_obj_tag(v_lvl_2026_) == 1)
{
lean_object* v_a_2028_; size_t v___x_2029_; size_t v___x_2030_; uint8_t v___x_2031_; 
v_a_2028_ = lean_ctor_get(v_lvl_2026_, 0);
v___x_2029_ = lean_ptr_addr(v_a_2028_);
v___x_2030_ = lean_ptr_addr(v_newLvl_2027_);
v___x_2031_ = lean_usize_dec_eq(v___x_2029_, v___x_2030_);
if (v___x_2031_ == 0)
{
lean_object* v___x_2032_; 
v___x_2032_ = l_Lean_Level_succ___override(v_newLvl_2027_);
return v___x_2032_;
}
else
{
lean_dec(v_newLvl_2027_);
lean_inc_ref(v_lvl_2026_);
return v_lvl_2026_;
}
}
else
{
lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; 
lean_dec(v_newLvl_2027_);
v___x_2033_ = lean_box(0);
v___x_2034_ = lean_obj_once(&l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl___closed__2, &l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl___closed__2_once, _init_l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl___closed__2);
v___x_2035_ = l_panic___redArg(v___x_2033_, v___x_2034_);
return v___x_2035_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl___boxed(lean_object* v_lvl_2036_, lean_object* v_newLvl_2037_){
_start:
{
lean_object* v_res_2038_; 
v_res_2038_ = l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl(v_lvl_2036_, v_newLvl_2037_);
lean_dec(v_lvl_2036_);
return v_res_2038_;
}
}
static lean_object* _init_l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl___closed__2(void){
_start:
{
lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; 
v___x_2041_ = ((lean_object*)(l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl___closed__1));
v___x_2042_ = lean_unsigned_to_nat(19u);
v___x_2043_ = lean_unsigned_to_nat(575u);
v___x_2044_ = ((lean_object*)(l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl___closed__0));
v___x_2045_ = ((lean_object*)(l_Lean_Level_mvarId_x21___closed__0));
v___x_2046_ = l_mkPanicMessageWithDecl(v___x_2045_, v___x_2044_, v___x_2043_, v___x_2042_, v___x_2041_);
return v___x_2046_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl(lean_object* v_lvl_2047_, lean_object* v_newLhs_2048_, lean_object* v_newRhs_2049_){
_start:
{
uint8_t v___y_2051_; 
if (lean_obj_tag(v_lvl_2047_) == 2)
{
lean_object* v_a_2054_; lean_object* v_a_2055_; size_t v___x_2056_; size_t v___x_2057_; uint8_t v___x_2058_; 
v_a_2054_ = lean_ctor_get(v_lvl_2047_, 0);
v_a_2055_ = lean_ctor_get(v_lvl_2047_, 1);
v___x_2056_ = lean_ptr_addr(v_a_2054_);
v___x_2057_ = lean_ptr_addr(v_newLhs_2048_);
v___x_2058_ = lean_usize_dec_eq(v___x_2056_, v___x_2057_);
if (v___x_2058_ == 0)
{
v___y_2051_ = v___x_2058_;
goto v___jp_2050_;
}
else
{
size_t v___x_2059_; size_t v___x_2060_; uint8_t v___x_2061_; 
v___x_2059_ = lean_ptr_addr(v_a_2055_);
v___x_2060_ = lean_ptr_addr(v_newRhs_2049_);
v___x_2061_ = lean_usize_dec_eq(v___x_2059_, v___x_2060_);
v___y_2051_ = v___x_2061_;
goto v___jp_2050_;
}
}
else
{
lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; 
lean_dec(v_newRhs_2049_);
lean_dec(v_newLhs_2048_);
v___x_2062_ = lean_box(0);
v___x_2063_ = lean_obj_once(&l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl___closed__2, &l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl___closed__2_once, _init_l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl___closed__2);
v___x_2064_ = l_panic___redArg(v___x_2062_, v___x_2063_);
return v___x_2064_;
}
v___jp_2050_:
{
if (v___y_2051_ == 0)
{
lean_object* v___x_2052_; 
v___x_2052_ = l_Lean_mkLevelMax_x27(v_newLhs_2048_, v_newRhs_2049_);
return v___x_2052_;
}
else
{
lean_object* v___x_2053_; 
v___x_2053_ = l_Lean_simpLevelMax_x27(v_newLhs_2048_, v_newRhs_2049_, v_lvl_2047_);
lean_dec(v_newRhs_2049_);
lean_dec(v_newLhs_2048_);
return v___x_2053_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl___boxed(lean_object* v_lvl_2065_, lean_object* v_newLhs_2066_, lean_object* v_newRhs_2067_){
_start:
{
lean_object* v_res_2068_; 
v_res_2068_ = l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl(v_lvl_2065_, v_newLhs_2066_, v_newRhs_2067_);
lean_dec(v_lvl_2065_);
return v_res_2068_;
}
}
static lean_object* _init_l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl___closed__2(void){
_start:
{
lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; 
v___x_2071_ = ((lean_object*)(l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl___closed__1));
v___x_2072_ = lean_unsigned_to_nat(20u);
v___x_2073_ = lean_unsigned_to_nat(586u);
v___x_2074_ = ((lean_object*)(l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl___closed__0));
v___x_2075_ = ((lean_object*)(l_Lean_Level_mvarId_x21___closed__0));
v___x_2076_ = l_mkPanicMessageWithDecl(v___x_2075_, v___x_2074_, v___x_2073_, v___x_2072_, v___x_2071_);
return v___x_2076_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl(lean_object* v_lvl_2077_, lean_object* v_newLhs_2078_, lean_object* v_newRhs_2079_){
_start:
{
uint8_t v___y_2081_; 
if (lean_obj_tag(v_lvl_2077_) == 3)
{
lean_object* v_a_2084_; lean_object* v_a_2085_; size_t v___x_2086_; size_t v___x_2087_; uint8_t v___x_2088_; 
v_a_2084_ = lean_ctor_get(v_lvl_2077_, 0);
v_a_2085_ = lean_ctor_get(v_lvl_2077_, 1);
v___x_2086_ = lean_ptr_addr(v_a_2084_);
v___x_2087_ = lean_ptr_addr(v_newLhs_2078_);
v___x_2088_ = lean_usize_dec_eq(v___x_2086_, v___x_2087_);
if (v___x_2088_ == 0)
{
v___y_2081_ = v___x_2088_;
goto v___jp_2080_;
}
else
{
size_t v___x_2089_; size_t v___x_2090_; uint8_t v___x_2091_; 
v___x_2089_ = lean_ptr_addr(v_a_2085_);
v___x_2090_ = lean_ptr_addr(v_newRhs_2079_);
v___x_2091_ = lean_usize_dec_eq(v___x_2089_, v___x_2090_);
v___y_2081_ = v___x_2091_;
goto v___jp_2080_;
}
}
else
{
lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; 
lean_dec(v_newRhs_2079_);
lean_dec(v_newLhs_2078_);
v___x_2092_ = lean_box(0);
v___x_2093_ = lean_obj_once(&l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl___closed__2, &l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl___closed__2_once, _init_l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl___closed__2);
v___x_2094_ = l_panic___redArg(v___x_2092_, v___x_2093_);
return v___x_2094_;
}
v___jp_2080_:
{
if (v___y_2081_ == 0)
{
lean_object* v___x_2082_; 
v___x_2082_ = l_Lean_mkLevelIMax_x27(v_newLhs_2078_, v_newRhs_2079_);
return v___x_2082_;
}
else
{
lean_object* v___x_2083_; 
v___x_2083_ = l_Lean_simpLevelIMax_x27(v_newLhs_2078_, v_newRhs_2079_, v_lvl_2077_);
return v___x_2083_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl___boxed(lean_object* v_lvl_2095_, lean_object* v_newLhs_2096_, lean_object* v_newRhs_2097_){
_start:
{
lean_object* v_res_2098_; 
v_res_2098_ = l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl(v_lvl_2095_, v_newLhs_2096_, v_newRhs_2097_);
lean_dec(v_lvl_2095_);
return v_res_2098_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_mkNaryMax(lean_object* v_x_2099_){
_start:
{
if (lean_obj_tag(v_x_2099_) == 0)
{
lean_object* v___x_2100_; 
v___x_2100_ = lean_box(0);
return v___x_2100_;
}
else
{
lean_object* v_tail_2101_; 
v_tail_2101_ = lean_ctor_get(v_x_2099_, 1);
if (lean_obj_tag(v_tail_2101_) == 0)
{
lean_object* v_head_2102_; 
v_head_2102_ = lean_ctor_get(v_x_2099_, 0);
lean_inc(v_head_2102_);
lean_dec_ref(v_x_2099_);
return v_head_2102_;
}
else
{
lean_object* v_head_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; 
lean_inc(v_tail_2101_);
v_head_2103_ = lean_ctor_get(v_x_2099_, 0);
lean_inc(v_head_2103_);
lean_dec_ref(v_x_2099_);
v___x_2104_ = l_Lean_Level_mkNaryMax(v_tail_2101_);
v___x_2105_ = l_Lean_mkLevelMax_x27(v_head_2103_, v___x_2104_);
return v___x_2105_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_substParams_go(lean_object* v_s_2106_, lean_object* v_u_2107_){
_start:
{
switch(lean_obj_tag(v_u_2107_))
{
case 0:
{
lean_dec_ref(v_s_2106_);
return v_u_2107_;
}
case 1:
{
lean_object* v_a_2108_; uint8_t v___x_2109_; 
v_a_2108_ = lean_ctor_get(v_u_2107_, 0);
v___x_2109_ = l_Lean_Level_hasParam(v_u_2107_);
if (v___x_2109_ == 0)
{
lean_dec_ref(v_s_2106_);
return v_u_2107_;
}
else
{
lean_object* v___x_2110_; size_t v___x_2111_; size_t v___x_2112_; uint8_t v___x_2113_; 
lean_inc(v_a_2108_);
v___x_2110_ = l___private_Lean_Level_0__Lean_Level_substParams_go(v_s_2106_, v_a_2108_);
v___x_2111_ = lean_ptr_addr(v_a_2108_);
v___x_2112_ = lean_ptr_addr(v___x_2110_);
v___x_2113_ = lean_usize_dec_eq(v___x_2111_, v___x_2112_);
if (v___x_2113_ == 0)
{
lean_object* v___x_2114_; 
lean_dec_ref(v_u_2107_);
v___x_2114_ = l_Lean_Level_succ___override(v___x_2110_);
return v___x_2114_;
}
else
{
lean_dec(v___x_2110_);
return v_u_2107_;
}
}
}
case 2:
{
lean_object* v_a_2115_; lean_object* v_a_2116_; uint8_t v___x_2117_; 
v_a_2115_ = lean_ctor_get(v_u_2107_, 0);
v_a_2116_ = lean_ctor_get(v_u_2107_, 1);
v___x_2117_ = l_Lean_Level_hasParam(v_u_2107_);
if (v___x_2117_ == 0)
{
lean_dec_ref(v_s_2106_);
return v_u_2107_;
}
else
{
lean_object* v___x_2118_; lean_object* v___x_2119_; uint8_t v___y_2121_; size_t v___x_2124_; size_t v___x_2125_; uint8_t v___x_2126_; 
lean_inc(v_a_2115_);
lean_inc_ref(v_s_2106_);
v___x_2118_ = l___private_Lean_Level_0__Lean_Level_substParams_go(v_s_2106_, v_a_2115_);
lean_inc(v_a_2116_);
v___x_2119_ = l___private_Lean_Level_0__Lean_Level_substParams_go(v_s_2106_, v_a_2116_);
v___x_2124_ = lean_ptr_addr(v_a_2115_);
v___x_2125_ = lean_ptr_addr(v___x_2118_);
v___x_2126_ = lean_usize_dec_eq(v___x_2124_, v___x_2125_);
if (v___x_2126_ == 0)
{
v___y_2121_ = v___x_2126_;
goto v___jp_2120_;
}
else
{
size_t v___x_2127_; size_t v___x_2128_; uint8_t v___x_2129_; 
v___x_2127_ = lean_ptr_addr(v_a_2116_);
v___x_2128_ = lean_ptr_addr(v___x_2119_);
v___x_2129_ = lean_usize_dec_eq(v___x_2127_, v___x_2128_);
v___y_2121_ = v___x_2129_;
goto v___jp_2120_;
}
v___jp_2120_:
{
if (v___y_2121_ == 0)
{
lean_object* v___x_2122_; 
lean_dec_ref(v_u_2107_);
v___x_2122_ = l_Lean_mkLevelMax_x27(v___x_2118_, v___x_2119_);
return v___x_2122_;
}
else
{
lean_object* v___x_2123_; 
v___x_2123_ = l_Lean_simpLevelMax_x27(v___x_2118_, v___x_2119_, v_u_2107_);
lean_dec_ref(v_u_2107_);
lean_dec(v___x_2119_);
lean_dec(v___x_2118_);
return v___x_2123_;
}
}
}
}
case 3:
{
lean_object* v_a_2130_; lean_object* v_a_2131_; uint8_t v___x_2132_; 
v_a_2130_ = lean_ctor_get(v_u_2107_, 0);
v_a_2131_ = lean_ctor_get(v_u_2107_, 1);
v___x_2132_ = l_Lean_Level_hasParam(v_u_2107_);
if (v___x_2132_ == 0)
{
lean_dec_ref(v_s_2106_);
return v_u_2107_;
}
else
{
lean_object* v___x_2133_; lean_object* v___x_2134_; uint8_t v___y_2136_; size_t v___x_2139_; size_t v___x_2140_; uint8_t v___x_2141_; 
lean_inc(v_a_2130_);
lean_inc_ref(v_s_2106_);
v___x_2133_ = l___private_Lean_Level_0__Lean_Level_substParams_go(v_s_2106_, v_a_2130_);
lean_inc(v_a_2131_);
v___x_2134_ = l___private_Lean_Level_0__Lean_Level_substParams_go(v_s_2106_, v_a_2131_);
v___x_2139_ = lean_ptr_addr(v_a_2130_);
v___x_2140_ = lean_ptr_addr(v___x_2133_);
v___x_2141_ = lean_usize_dec_eq(v___x_2139_, v___x_2140_);
if (v___x_2141_ == 0)
{
v___y_2136_ = v___x_2141_;
goto v___jp_2135_;
}
else
{
size_t v___x_2142_; size_t v___x_2143_; uint8_t v___x_2144_; 
v___x_2142_ = lean_ptr_addr(v_a_2131_);
v___x_2143_ = lean_ptr_addr(v___x_2134_);
v___x_2144_ = lean_usize_dec_eq(v___x_2142_, v___x_2143_);
v___y_2136_ = v___x_2144_;
goto v___jp_2135_;
}
v___jp_2135_:
{
if (v___y_2136_ == 0)
{
lean_object* v___x_2137_; 
lean_dec_ref(v_u_2107_);
v___x_2137_ = l_Lean_mkLevelIMax_x27(v___x_2133_, v___x_2134_);
return v___x_2137_;
}
else
{
lean_object* v___x_2138_; 
v___x_2138_ = l_Lean_simpLevelIMax_x27(v___x_2133_, v___x_2134_, v_u_2107_);
lean_dec_ref(v_u_2107_);
return v___x_2138_;
}
}
}
}
case 4:
{
lean_object* v_a_2145_; lean_object* v___x_2146_; 
v_a_2145_ = lean_ctor_get(v_u_2107_, 0);
lean_inc(v_a_2145_);
v___x_2146_ = lean_apply_1(v_s_2106_, v_a_2145_);
if (lean_obj_tag(v___x_2146_) == 0)
{
return v_u_2107_;
}
else
{
lean_object* v_val_2147_; 
lean_dec_ref(v_u_2107_);
v_val_2147_ = lean_ctor_get(v___x_2146_, 0);
lean_inc(v_val_2147_);
lean_dec_ref(v___x_2146_);
return v_val_2147_;
}
}
default: 
{
lean_dec_ref(v_s_2106_);
return v_u_2107_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_substParams(lean_object* v_u_2148_, lean_object* v_s_2149_){
_start:
{
lean_object* v___x_2150_; 
v___x_2150_ = l___private_Lean_Level_0__Lean_Level_substParams_go(v_s_2149_, v_u_2148_);
return v___x_2150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_getParamSubst(lean_object* v_x_2151_, lean_object* v_x_2152_, lean_object* v_x_2153_){
_start:
{
if (lean_obj_tag(v_x_2151_) == 1)
{
if (lean_obj_tag(v_x_2152_) == 1)
{
lean_object* v_head_2154_; lean_object* v_tail_2155_; lean_object* v_head_2156_; lean_object* v_tail_2157_; uint8_t v___x_2158_; 
v_head_2154_ = lean_ctor_get(v_x_2151_, 0);
v_tail_2155_ = lean_ctor_get(v_x_2151_, 1);
v_head_2156_ = lean_ctor_get(v_x_2152_, 0);
v_tail_2157_ = lean_ctor_get(v_x_2152_, 1);
v___x_2158_ = lean_name_eq(v_head_2154_, v_x_2153_);
if (v___x_2158_ == 0)
{
v_x_2151_ = v_tail_2155_;
v_x_2152_ = v_tail_2157_;
goto _start;
}
else
{
lean_object* v___x_2160_; 
lean_inc(v_head_2156_);
v___x_2160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2160_, 0, v_head_2156_);
return v___x_2160_;
}
}
else
{
lean_object* v___x_2161_; 
v___x_2161_ = lean_box(0);
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
}
LEAN_EXPORT lean_object* l_Lean_Level_getParamSubst___boxed(lean_object* v_x_2163_, lean_object* v_x_2164_, lean_object* v_x_2165_){
_start:
{
lean_object* v_res_2166_; 
v_res_2166_ = l_Lean_Level_getParamSubst(v_x_2163_, v_x_2164_, v_x_2165_);
lean_dec(v_x_2165_);
lean_dec(v_x_2164_);
lean_dec(v_x_2163_);
return v_res_2166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_instantiateParams(lean_object* v_u_2167_, lean_object* v_paramNames_2168_, lean_object* v_vs_2169_){
_start:
{
lean_object* v___x_2170_; lean_object* v___x_2171_; 
v___x_2170_ = lean_alloc_closure((void*)(l_Lean_Level_getParamSubst___boxed), 3, 2);
lean_closure_set(v___x_2170_, 0, v_paramNames_2168_);
lean_closure_set(v___x_2170_, 1, v_vs_2169_);
v___x_2171_ = l___private_Lean_Level_0__Lean_Level_substParams_go(v___x_2170_, v_u_2167_);
return v___x_2171_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Level_0__Lean_Level_geq_go(lean_object* v_u_2172_, lean_object* v_v_2173_){
_start:
{
uint8_t v___y_2175_; uint8_t v___y_2189_; lean_object* v_u_u2081_2191_; lean_object* v_u_u2082_2192_; lean_object* v_v_2193_; uint8_t v___x_2196_; 
v___x_2196_ = lean_level_eq(v_u_2172_, v_v_2173_);
if (v___x_2196_ == 0)
{
switch(lean_obj_tag(v_v_2173_))
{
case 0:
{
uint8_t v___x_2197_; 
v___x_2197_ = 1;
return v___x_2197_;
}
case 2:
{
lean_object* v_a_2198_; lean_object* v_a_2199_; uint8_t v___x_2200_; 
v_a_2198_ = lean_ctor_get(v_v_2173_, 0);
v_a_2199_ = lean_ctor_get(v_v_2173_, 1);
v___x_2200_ = l___private_Lean_Level_0__Lean_Level_geq_go(v_u_2172_, v_a_2198_);
if (v___x_2200_ == 0)
{
return v___x_2200_;
}
else
{
v_v_2173_ = v_a_2199_;
goto _start;
}
}
case 1:
{
switch(lean_obj_tag(v_u_2172_))
{
case 2:
{
lean_object* v_a_2202_; lean_object* v_a_2203_; 
v_a_2202_ = lean_ctor_get(v_u_2172_, 0);
v_a_2203_ = lean_ctor_get(v_u_2172_, 1);
v_u_u2081_2191_ = v_a_2202_;
v_u_u2082_2192_ = v_a_2203_;
v_v_2193_ = v_v_2173_;
goto v___jp_2190_;
}
case 3:
{
lean_object* v_a_2204_; 
v_a_2204_ = lean_ctor_get(v_u_2172_, 1);
v_u_2172_ = v_a_2204_;
goto _start;
}
case 1:
{
lean_object* v_a_2206_; lean_object* v_a_2207_; 
v_a_2206_ = lean_ctor_get(v_v_2173_, 0);
v_a_2207_ = lean_ctor_get(v_u_2172_, 0);
v_u_2172_ = v_a_2207_;
v_v_2173_ = v_a_2206_;
goto _start;
}
default: 
{
goto v___jp_2179_;
}
}
}
default: 
{
switch(lean_obj_tag(v_u_2172_))
{
case 2:
{
lean_object* v_a_2209_; lean_object* v_a_2210_; 
v_a_2209_ = lean_ctor_get(v_u_2172_, 0);
v_a_2210_ = lean_ctor_get(v_u_2172_, 1);
v_u_u2081_2191_ = v_a_2209_;
v_u_u2082_2192_ = v_a_2210_;
v_v_2193_ = v_v_2173_;
goto v___jp_2190_;
}
case 3:
{
lean_object* v_a_2211_; 
v_a_2211_ = lean_ctor_get(v_u_2172_, 1);
v_u_2172_ = v_a_2211_;
goto _start;
}
default: 
{
goto v___jp_2179_;
}
}
}
}
}
else
{
return v___x_2196_;
}
v___jp_2174_:
{
if (v___y_2175_ == 0)
{
return v___y_2175_;
}
else
{
lean_object* v___x_2176_; lean_object* v___x_2177_; uint8_t v___x_2178_; 
v___x_2176_ = l_Lean_Level_getOffset(v_v_2173_);
v___x_2177_ = l_Lean_Level_getOffset(v_u_2172_);
v___x_2178_ = lean_nat_dec_le(v___x_2176_, v___x_2177_);
lean_dec(v___x_2177_);
lean_dec(v___x_2176_);
return v___x_2178_;
}
}
v___jp_2179_:
{
if (lean_obj_tag(v_v_2173_) == 3)
{
lean_object* v_a_2180_; lean_object* v_a_2181_; uint8_t v___x_2182_; 
v_a_2180_ = lean_ctor_get(v_v_2173_, 0);
v_a_2181_ = lean_ctor_get(v_v_2173_, 1);
v___x_2182_ = l___private_Lean_Level_0__Lean_Level_geq_go(v_u_2172_, v_a_2180_);
if (v___x_2182_ == 0)
{
return v___x_2182_;
}
else
{
v_v_2173_ = v_a_2181_;
goto _start;
}
}
else
{
lean_object* v_v_x27_2184_; lean_object* v___x_2185_; uint8_t v___x_2186_; 
v_v_x27_2184_ = l_Lean_Level_getLevelOffset(v_v_2173_);
v___x_2185_ = l_Lean_Level_getLevelOffset(v_u_2172_);
v___x_2186_ = lean_level_eq(v___x_2185_, v_v_x27_2184_);
lean_dec(v___x_2185_);
if (v___x_2186_ == 0)
{
uint8_t v___x_2187_; 
v___x_2187_ = l_Lean_Level_isZero(v_v_x27_2184_);
lean_dec(v_v_x27_2184_);
v___y_2175_ = v___x_2187_;
goto v___jp_2174_;
}
else
{
lean_dec(v_v_x27_2184_);
v___y_2175_ = v___x_2186_;
goto v___jp_2174_;
}
}
}
v___jp_2188_:
{
if (v___y_2189_ == 0)
{
goto v___jp_2179_;
}
else
{
return v___y_2189_;
}
}
v___jp_2190_:
{
uint8_t v___x_2194_; 
v___x_2194_ = l___private_Lean_Level_0__Lean_Level_geq_go(v_u_u2081_2191_, v_v_2193_);
if (v___x_2194_ == 0)
{
uint8_t v___x_2195_; 
v___x_2195_ = l___private_Lean_Level_0__Lean_Level_geq_go(v_u_u2082_2192_, v_v_2193_);
v___y_2189_ = v___x_2195_;
goto v___jp_2188_;
}
else
{
v___y_2189_ = v___x_2194_;
goto v___jp_2188_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_geq_go___boxed(lean_object* v_u_2213_, lean_object* v_v_2214_){
_start:
{
uint8_t v_res_2215_; lean_object* v_r_2216_; 
v_res_2215_ = l___private_Lean_Level_0__Lean_Level_geq_go(v_u_2213_, v_v_2214_);
lean_dec(v_v_2214_);
lean_dec(v_u_2213_);
v_r_2216_ = lean_box(v_res_2215_);
return v_r_2216_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_geq_go_match__1_splitter___redArg(lean_object* v_u_2217_, lean_object* v_v_2218_, lean_object* v_h__1_2219_, lean_object* v_h__2_2220_, lean_object* v_h__3_2221_, lean_object* v_h__4_2222_, lean_object* v_h__5_2223_, lean_object* v_h__6_2224_){
_start:
{
switch(lean_obj_tag(v_v_2218_))
{
case 0:
{
lean_object* v___x_2225_; 
lean_dec(v_h__6_2224_);
lean_dec(v_h__5_2223_);
lean_dec(v_h__4_2222_);
lean_dec(v_h__3_2221_);
lean_dec(v_h__2_2220_);
v___x_2225_ = lean_apply_1(v_h__1_2219_, v_u_2217_);
return v___x_2225_;
}
case 2:
{
lean_object* v_a_2226_; lean_object* v_a_2227_; lean_object* v___x_2228_; 
lean_dec(v_h__6_2224_);
lean_dec(v_h__5_2223_);
lean_dec(v_h__4_2222_);
lean_dec(v_h__3_2221_);
lean_dec(v_h__1_2219_);
v_a_2226_ = lean_ctor_get(v_v_2218_, 0);
lean_inc(v_a_2226_);
v_a_2227_ = lean_ctor_get(v_v_2218_, 1);
lean_inc(v_a_2227_);
lean_dec_ref(v_v_2218_);
v___x_2228_ = lean_apply_3(v_h__2_2220_, v_u_2217_, v_a_2226_, v_a_2227_);
return v___x_2228_;
}
case 1:
{
lean_dec(v_h__2_2220_);
lean_dec(v_h__1_2219_);
switch(lean_obj_tag(v_u_2217_))
{
case 2:
{
lean_object* v_a_2229_; lean_object* v_a_2230_; lean_object* v___x_2231_; 
lean_dec(v_h__6_2224_);
lean_dec(v_h__5_2223_);
lean_dec(v_h__4_2222_);
v_a_2229_ = lean_ctor_get(v_u_2217_, 0);
lean_inc(v_a_2229_);
v_a_2230_ = lean_ctor_get(v_u_2217_, 1);
lean_inc(v_a_2230_);
lean_dec_ref(v_u_2217_);
v___x_2231_ = lean_apply_5(v_h__3_2221_, v_a_2229_, v_a_2230_, v_v_2218_, lean_box(0), lean_box(0));
return v___x_2231_;
}
case 3:
{
lean_object* v_a_2232_; lean_object* v_a_2233_; lean_object* v___x_2234_; 
lean_dec(v_h__6_2224_);
lean_dec(v_h__5_2223_);
lean_dec(v_h__3_2221_);
v_a_2232_ = lean_ctor_get(v_u_2217_, 0);
lean_inc(v_a_2232_);
v_a_2233_ = lean_ctor_get(v_u_2217_, 1);
lean_inc(v_a_2233_);
lean_dec_ref(v_u_2217_);
v___x_2234_ = lean_apply_5(v_h__4_2222_, v_a_2232_, v_a_2233_, v_v_2218_, lean_box(0), lean_box(0));
return v___x_2234_;
}
case 1:
{
lean_object* v_a_2235_; lean_object* v_a_2236_; lean_object* v___x_2237_; 
lean_dec(v_h__6_2224_);
lean_dec(v_h__4_2222_);
lean_dec(v_h__3_2221_);
v_a_2235_ = lean_ctor_get(v_v_2218_, 0);
lean_inc(v_a_2235_);
lean_dec_ref(v_v_2218_);
v_a_2236_ = lean_ctor_get(v_u_2217_, 0);
lean_inc(v_a_2236_);
lean_dec_ref(v_u_2217_);
v___x_2237_ = lean_apply_2(v_h__5_2223_, v_a_2236_, v_a_2235_);
return v___x_2237_;
}
default: 
{
lean_object* v___x_2238_; 
lean_dec(v_h__5_2223_);
lean_dec(v_h__4_2222_);
lean_dec(v_h__3_2221_);
v___x_2238_ = lean_apply_7(v_h__6_2224_, v_u_2217_, v_v_2218_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_2238_;
}
}
}
default: 
{
lean_dec(v_h__5_2223_);
lean_dec(v_h__2_2220_);
lean_dec(v_h__1_2219_);
switch(lean_obj_tag(v_u_2217_))
{
case 2:
{
lean_object* v_a_2239_; lean_object* v_a_2240_; lean_object* v___x_2241_; 
lean_dec(v_h__6_2224_);
lean_dec(v_h__4_2222_);
v_a_2239_ = lean_ctor_get(v_u_2217_, 0);
lean_inc(v_a_2239_);
v_a_2240_ = lean_ctor_get(v_u_2217_, 1);
lean_inc(v_a_2240_);
lean_dec_ref(v_u_2217_);
v___x_2241_ = lean_apply_5(v_h__3_2221_, v_a_2239_, v_a_2240_, v_v_2218_, lean_box(0), lean_box(0));
return v___x_2241_;
}
case 3:
{
lean_object* v_a_2242_; lean_object* v_a_2243_; lean_object* v___x_2244_; 
lean_dec(v_h__6_2224_);
lean_dec(v_h__3_2221_);
v_a_2242_ = lean_ctor_get(v_u_2217_, 0);
lean_inc(v_a_2242_);
v_a_2243_ = lean_ctor_get(v_u_2217_, 1);
lean_inc(v_a_2243_);
lean_dec_ref(v_u_2217_);
v___x_2244_ = lean_apply_5(v_h__4_2222_, v_a_2242_, v_a_2243_, v_v_2218_, lean_box(0), lean_box(0));
return v___x_2244_;
}
default: 
{
lean_object* v___x_2245_; 
lean_dec(v_h__4_2222_);
lean_dec(v_h__3_2221_);
v___x_2245_ = lean_apply_7(v_h__6_2224_, v_u_2217_, v_v_2218_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_2245_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_geq_go_match__1_splitter(lean_object* v_motive_2246_, lean_object* v_u_2247_, lean_object* v_v_2248_, lean_object* v_h__1_2249_, lean_object* v_h__2_2250_, lean_object* v_h__3_2251_, lean_object* v_h__4_2252_, lean_object* v_h__5_2253_, lean_object* v_h__6_2254_){
_start:
{
switch(lean_obj_tag(v_v_2248_))
{
case 0:
{
lean_object* v___x_2255_; 
lean_dec(v_h__6_2254_);
lean_dec(v_h__5_2253_);
lean_dec(v_h__4_2252_);
lean_dec(v_h__3_2251_);
lean_dec(v_h__2_2250_);
v___x_2255_ = lean_apply_1(v_h__1_2249_, v_u_2247_);
return v___x_2255_;
}
case 2:
{
lean_object* v_a_2256_; lean_object* v_a_2257_; lean_object* v___x_2258_; 
lean_dec(v_h__6_2254_);
lean_dec(v_h__5_2253_);
lean_dec(v_h__4_2252_);
lean_dec(v_h__3_2251_);
lean_dec(v_h__1_2249_);
v_a_2256_ = lean_ctor_get(v_v_2248_, 0);
lean_inc(v_a_2256_);
v_a_2257_ = lean_ctor_get(v_v_2248_, 1);
lean_inc(v_a_2257_);
lean_dec_ref(v_v_2248_);
v___x_2258_ = lean_apply_3(v_h__2_2250_, v_u_2247_, v_a_2256_, v_a_2257_);
return v___x_2258_;
}
case 1:
{
lean_dec(v_h__2_2250_);
lean_dec(v_h__1_2249_);
switch(lean_obj_tag(v_u_2247_))
{
case 2:
{
lean_object* v_a_2259_; lean_object* v_a_2260_; lean_object* v___x_2261_; 
lean_dec(v_h__6_2254_);
lean_dec(v_h__5_2253_);
lean_dec(v_h__4_2252_);
v_a_2259_ = lean_ctor_get(v_u_2247_, 0);
lean_inc(v_a_2259_);
v_a_2260_ = lean_ctor_get(v_u_2247_, 1);
lean_inc(v_a_2260_);
lean_dec_ref(v_u_2247_);
v___x_2261_ = lean_apply_5(v_h__3_2251_, v_a_2259_, v_a_2260_, v_v_2248_, lean_box(0), lean_box(0));
return v___x_2261_;
}
case 3:
{
lean_object* v_a_2262_; lean_object* v_a_2263_; lean_object* v___x_2264_; 
lean_dec(v_h__6_2254_);
lean_dec(v_h__5_2253_);
lean_dec(v_h__3_2251_);
v_a_2262_ = lean_ctor_get(v_u_2247_, 0);
lean_inc(v_a_2262_);
v_a_2263_ = lean_ctor_get(v_u_2247_, 1);
lean_inc(v_a_2263_);
lean_dec_ref(v_u_2247_);
v___x_2264_ = lean_apply_5(v_h__4_2252_, v_a_2262_, v_a_2263_, v_v_2248_, lean_box(0), lean_box(0));
return v___x_2264_;
}
case 1:
{
lean_object* v_a_2265_; lean_object* v_a_2266_; lean_object* v___x_2267_; 
lean_dec(v_h__6_2254_);
lean_dec(v_h__4_2252_);
lean_dec(v_h__3_2251_);
v_a_2265_ = lean_ctor_get(v_v_2248_, 0);
lean_inc(v_a_2265_);
lean_dec_ref(v_v_2248_);
v_a_2266_ = lean_ctor_get(v_u_2247_, 0);
lean_inc(v_a_2266_);
lean_dec_ref(v_u_2247_);
v___x_2267_ = lean_apply_2(v_h__5_2253_, v_a_2266_, v_a_2265_);
return v___x_2267_;
}
default: 
{
lean_object* v___x_2268_; 
lean_dec(v_h__5_2253_);
lean_dec(v_h__4_2252_);
lean_dec(v_h__3_2251_);
v___x_2268_ = lean_apply_7(v_h__6_2254_, v_u_2247_, v_v_2248_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_2268_;
}
}
}
default: 
{
lean_dec(v_h__5_2253_);
lean_dec(v_h__2_2250_);
lean_dec(v_h__1_2249_);
switch(lean_obj_tag(v_u_2247_))
{
case 2:
{
lean_object* v_a_2269_; lean_object* v_a_2270_; lean_object* v___x_2271_; 
lean_dec(v_h__6_2254_);
lean_dec(v_h__4_2252_);
v_a_2269_ = lean_ctor_get(v_u_2247_, 0);
lean_inc(v_a_2269_);
v_a_2270_ = lean_ctor_get(v_u_2247_, 1);
lean_inc(v_a_2270_);
lean_dec_ref(v_u_2247_);
v___x_2271_ = lean_apply_5(v_h__3_2251_, v_a_2269_, v_a_2270_, v_v_2248_, lean_box(0), lean_box(0));
return v___x_2271_;
}
case 3:
{
lean_object* v_a_2272_; lean_object* v_a_2273_; lean_object* v___x_2274_; 
lean_dec(v_h__6_2254_);
lean_dec(v_h__3_2251_);
v_a_2272_ = lean_ctor_get(v_u_2247_, 0);
lean_inc(v_a_2272_);
v_a_2273_ = lean_ctor_get(v_u_2247_, 1);
lean_inc(v_a_2273_);
lean_dec_ref(v_u_2247_);
v___x_2274_ = lean_apply_5(v_h__4_2252_, v_a_2272_, v_a_2273_, v_v_2248_, lean_box(0), lean_box(0));
return v___x_2274_;
}
default: 
{
lean_object* v___x_2275_; 
lean_dec(v_h__4_2252_);
lean_dec(v_h__3_2251_);
v___x_2275_ = lean_apply_7(v_h__6_2254_, v_u_2247_, v_v_2248_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_2275_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_isIMax_match__1_splitter___redArg(lean_object* v_x_2276_, lean_object* v_h__1_2277_, lean_object* v_h__2_2278_){
_start:
{
if (lean_obj_tag(v_x_2276_) == 3)
{
lean_object* v_a_2279_; lean_object* v_a_2280_; lean_object* v___x_2281_; 
lean_dec(v_h__2_2278_);
v_a_2279_ = lean_ctor_get(v_x_2276_, 0);
lean_inc(v_a_2279_);
v_a_2280_ = lean_ctor_get(v_x_2276_, 1);
lean_inc(v_a_2280_);
lean_dec_ref(v_x_2276_);
v___x_2281_ = lean_apply_2(v_h__1_2277_, v_a_2279_, v_a_2280_);
return v___x_2281_;
}
else
{
lean_object* v___x_2282_; 
lean_dec(v_h__1_2277_);
v___x_2282_ = lean_apply_2(v_h__2_2278_, v_x_2276_, lean_box(0));
return v___x_2282_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_isIMax_match__1_splitter(lean_object* v_motive_2283_, lean_object* v_x_2284_, lean_object* v_h__1_2285_, lean_object* v_h__2_2286_){
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
lean_dec_ref(v_x_2284_);
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
LEAN_EXPORT uint8_t l_Lean_Level_geq(lean_object* v_u_2291_, lean_object* v_v_2292_){
_start:
{
lean_object* v___x_2293_; lean_object* v___x_2294_; uint8_t v___x_2295_; 
v___x_2293_ = l_Lean_Level_normalize(v_u_2291_);
v___x_2294_ = l_Lean_Level_normalize(v_v_2292_);
v___x_2295_ = l___private_Lean_Level_0__Lean_Level_geq_go(v___x_2293_, v___x_2294_);
lean_dec(v___x_2294_);
lean_dec(v___x_2293_);
return v___x_2295_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_geq___boxed(lean_object* v_u_2296_, lean_object* v_v_2297_){
_start:
{
uint8_t v_res_2298_; lean_object* v_r_2299_; 
v_res_2298_ = l_Lean_Level_geq(v_u_2296_, v_v_2297_);
lean_dec(v_v_2297_);
lean_dec(v_u_2296_);
v_r_2299_ = lean_box(v_res_2298_);
return v_r_2299_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Level_collectMVars_spec__1___redArg(lean_object* v_k_2300_, lean_object* v_v_2301_, lean_object* v_t_2302_){
_start:
{
if (lean_obj_tag(v_t_2302_) == 0)
{
lean_object* v_size_2303_; lean_object* v_k_2304_; lean_object* v_v_2305_; lean_object* v_l_2306_; lean_object* v_r_2307_; lean_object* v___x_2309_; uint8_t v_isShared_2310_; uint8_t v_isSharedCheck_2587_; 
v_size_2303_ = lean_ctor_get(v_t_2302_, 0);
v_k_2304_ = lean_ctor_get(v_t_2302_, 1);
v_v_2305_ = lean_ctor_get(v_t_2302_, 2);
v_l_2306_ = lean_ctor_get(v_t_2302_, 3);
v_r_2307_ = lean_ctor_get(v_t_2302_, 4);
v_isSharedCheck_2587_ = !lean_is_exclusive(v_t_2302_);
if (v_isSharedCheck_2587_ == 0)
{
v___x_2309_ = v_t_2302_;
v_isShared_2310_ = v_isSharedCheck_2587_;
goto v_resetjp_2308_;
}
else
{
lean_inc(v_r_2307_);
lean_inc(v_l_2306_);
lean_inc(v_v_2305_);
lean_inc(v_k_2304_);
lean_inc(v_size_2303_);
lean_dec(v_t_2302_);
v___x_2309_ = lean_box(0);
v_isShared_2310_ = v_isSharedCheck_2587_;
goto v_resetjp_2308_;
}
v_resetjp_2308_:
{
uint8_t v___x_2311_; 
v___x_2311_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2300_, v_k_2304_);
switch(v___x_2311_)
{
case 0:
{
lean_object* v_impl_2312_; lean_object* v___x_2313_; 
lean_dec(v_size_2303_);
v_impl_2312_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Level_collectMVars_spec__1___redArg(v_k_2300_, v_v_2301_, v_l_2306_);
v___x_2313_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_2307_) == 0)
{
lean_object* v_size_2314_; lean_object* v_size_2315_; lean_object* v_k_2316_; lean_object* v_v_2317_; lean_object* v_l_2318_; lean_object* v_r_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; uint8_t v___x_2322_; 
v_size_2314_ = lean_ctor_get(v_r_2307_, 0);
v_size_2315_ = lean_ctor_get(v_impl_2312_, 0);
lean_inc(v_size_2315_);
v_k_2316_ = lean_ctor_get(v_impl_2312_, 1);
lean_inc(v_k_2316_);
v_v_2317_ = lean_ctor_get(v_impl_2312_, 2);
lean_inc(v_v_2317_);
v_l_2318_ = lean_ctor_get(v_impl_2312_, 3);
lean_inc(v_l_2318_);
v_r_2319_ = lean_ctor_get(v_impl_2312_, 4);
lean_inc(v_r_2319_);
v___x_2320_ = lean_unsigned_to_nat(3u);
v___x_2321_ = lean_nat_mul(v___x_2320_, v_size_2314_);
v___x_2322_ = lean_nat_dec_lt(v___x_2321_, v_size_2315_);
lean_dec(v___x_2321_);
if (v___x_2322_ == 0)
{
lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2326_; 
lean_dec(v_r_2319_);
lean_dec(v_l_2318_);
lean_dec(v_v_2317_);
lean_dec(v_k_2316_);
v___x_2323_ = lean_nat_add(v___x_2313_, v_size_2315_);
lean_dec(v_size_2315_);
v___x_2324_ = lean_nat_add(v___x_2323_, v_size_2314_);
lean_dec(v___x_2323_);
if (v_isShared_2310_ == 0)
{
lean_ctor_set(v___x_2309_, 3, v_impl_2312_);
lean_ctor_set(v___x_2309_, 0, v___x_2324_);
v___x_2326_ = v___x_2309_;
goto v_reusejp_2325_;
}
else
{
lean_object* v_reuseFailAlloc_2327_; 
v_reuseFailAlloc_2327_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2327_, 0, v___x_2324_);
lean_ctor_set(v_reuseFailAlloc_2327_, 1, v_k_2304_);
lean_ctor_set(v_reuseFailAlloc_2327_, 2, v_v_2305_);
lean_ctor_set(v_reuseFailAlloc_2327_, 3, v_impl_2312_);
lean_ctor_set(v_reuseFailAlloc_2327_, 4, v_r_2307_);
v___x_2326_ = v_reuseFailAlloc_2327_;
goto v_reusejp_2325_;
}
v_reusejp_2325_:
{
return v___x_2326_;
}
}
else
{
lean_object* v___x_2329_; uint8_t v_isShared_2330_; uint8_t v_isSharedCheck_2393_; 
v_isSharedCheck_2393_ = !lean_is_exclusive(v_impl_2312_);
if (v_isSharedCheck_2393_ == 0)
{
lean_object* v_unused_2394_; lean_object* v_unused_2395_; lean_object* v_unused_2396_; lean_object* v_unused_2397_; lean_object* v_unused_2398_; 
v_unused_2394_ = lean_ctor_get(v_impl_2312_, 4);
lean_dec(v_unused_2394_);
v_unused_2395_ = lean_ctor_get(v_impl_2312_, 3);
lean_dec(v_unused_2395_);
v_unused_2396_ = lean_ctor_get(v_impl_2312_, 2);
lean_dec(v_unused_2396_);
v_unused_2397_ = lean_ctor_get(v_impl_2312_, 1);
lean_dec(v_unused_2397_);
v_unused_2398_ = lean_ctor_get(v_impl_2312_, 0);
lean_dec(v_unused_2398_);
v___x_2329_ = v_impl_2312_;
v_isShared_2330_ = v_isSharedCheck_2393_;
goto v_resetjp_2328_;
}
else
{
lean_dec(v_impl_2312_);
v___x_2329_ = lean_box(0);
v_isShared_2330_ = v_isSharedCheck_2393_;
goto v_resetjp_2328_;
}
v_resetjp_2328_:
{
lean_object* v_size_2331_; lean_object* v_size_2332_; lean_object* v_k_2333_; lean_object* v_v_2334_; lean_object* v_l_2335_; lean_object* v_r_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; uint8_t v___x_2339_; 
v_size_2331_ = lean_ctor_get(v_l_2318_, 0);
v_size_2332_ = lean_ctor_get(v_r_2319_, 0);
v_k_2333_ = lean_ctor_get(v_r_2319_, 1);
v_v_2334_ = lean_ctor_get(v_r_2319_, 2);
v_l_2335_ = lean_ctor_get(v_r_2319_, 3);
v_r_2336_ = lean_ctor_get(v_r_2319_, 4);
v___x_2337_ = lean_unsigned_to_nat(2u);
v___x_2338_ = lean_nat_mul(v___x_2337_, v_size_2331_);
v___x_2339_ = lean_nat_dec_lt(v_size_2332_, v___x_2338_);
lean_dec(v___x_2338_);
if (v___x_2339_ == 0)
{
lean_object* v___x_2341_; uint8_t v_isShared_2342_; uint8_t v_isSharedCheck_2368_; 
lean_inc(v_r_2336_);
lean_inc(v_l_2335_);
lean_inc(v_v_2334_);
lean_inc(v_k_2333_);
v_isSharedCheck_2368_ = !lean_is_exclusive(v_r_2319_);
if (v_isSharedCheck_2368_ == 0)
{
lean_object* v_unused_2369_; lean_object* v_unused_2370_; lean_object* v_unused_2371_; lean_object* v_unused_2372_; lean_object* v_unused_2373_; 
v_unused_2369_ = lean_ctor_get(v_r_2319_, 4);
lean_dec(v_unused_2369_);
v_unused_2370_ = lean_ctor_get(v_r_2319_, 3);
lean_dec(v_unused_2370_);
v_unused_2371_ = lean_ctor_get(v_r_2319_, 2);
lean_dec(v_unused_2371_);
v_unused_2372_ = lean_ctor_get(v_r_2319_, 1);
lean_dec(v_unused_2372_);
v_unused_2373_ = lean_ctor_get(v_r_2319_, 0);
lean_dec(v_unused_2373_);
v___x_2341_ = v_r_2319_;
v_isShared_2342_ = v_isSharedCheck_2368_;
goto v_resetjp_2340_;
}
else
{
lean_dec(v_r_2319_);
v___x_2341_ = lean_box(0);
v_isShared_2342_ = v_isSharedCheck_2368_;
goto v_resetjp_2340_;
}
v_resetjp_2340_:
{
lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___y_2346_; lean_object* v___y_2347_; lean_object* v___y_2348_; lean_object* v___x_2356_; lean_object* v___y_2358_; 
v___x_2343_ = lean_nat_add(v___x_2313_, v_size_2315_);
lean_dec(v_size_2315_);
v___x_2344_ = lean_nat_add(v___x_2343_, v_size_2314_);
lean_dec(v___x_2343_);
v___x_2356_ = lean_nat_add(v___x_2313_, v_size_2331_);
if (lean_obj_tag(v_l_2335_) == 0)
{
lean_object* v_size_2366_; 
v_size_2366_ = lean_ctor_get(v_l_2335_, 0);
lean_inc(v_size_2366_);
v___y_2358_ = v_size_2366_;
goto v___jp_2357_;
}
else
{
lean_object* v___x_2367_; 
v___x_2367_ = lean_unsigned_to_nat(0u);
v___y_2358_ = v___x_2367_;
goto v___jp_2357_;
}
v___jp_2345_:
{
lean_object* v___x_2349_; lean_object* v___x_2351_; 
v___x_2349_ = lean_nat_add(v___y_2347_, v___y_2348_);
lean_dec(v___y_2348_);
lean_dec(v___y_2347_);
if (v_isShared_2342_ == 0)
{
lean_ctor_set(v___x_2341_, 4, v_r_2307_);
lean_ctor_set(v___x_2341_, 3, v_r_2336_);
lean_ctor_set(v___x_2341_, 2, v_v_2305_);
lean_ctor_set(v___x_2341_, 1, v_k_2304_);
lean_ctor_set(v___x_2341_, 0, v___x_2349_);
v___x_2351_ = v___x_2341_;
goto v_reusejp_2350_;
}
else
{
lean_object* v_reuseFailAlloc_2355_; 
v_reuseFailAlloc_2355_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2355_, 0, v___x_2349_);
lean_ctor_set(v_reuseFailAlloc_2355_, 1, v_k_2304_);
lean_ctor_set(v_reuseFailAlloc_2355_, 2, v_v_2305_);
lean_ctor_set(v_reuseFailAlloc_2355_, 3, v_r_2336_);
lean_ctor_set(v_reuseFailAlloc_2355_, 4, v_r_2307_);
v___x_2351_ = v_reuseFailAlloc_2355_;
goto v_reusejp_2350_;
}
v_reusejp_2350_:
{
lean_object* v___x_2353_; 
if (v_isShared_2330_ == 0)
{
lean_ctor_set(v___x_2329_, 4, v___x_2351_);
lean_ctor_set(v___x_2329_, 3, v___y_2346_);
lean_ctor_set(v___x_2329_, 2, v_v_2334_);
lean_ctor_set(v___x_2329_, 1, v_k_2333_);
lean_ctor_set(v___x_2329_, 0, v___x_2344_);
v___x_2353_ = v___x_2329_;
goto v_reusejp_2352_;
}
else
{
lean_object* v_reuseFailAlloc_2354_; 
v_reuseFailAlloc_2354_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2354_, 0, v___x_2344_);
lean_ctor_set(v_reuseFailAlloc_2354_, 1, v_k_2333_);
lean_ctor_set(v_reuseFailAlloc_2354_, 2, v_v_2334_);
lean_ctor_set(v_reuseFailAlloc_2354_, 3, v___y_2346_);
lean_ctor_set(v_reuseFailAlloc_2354_, 4, v___x_2351_);
v___x_2353_ = v_reuseFailAlloc_2354_;
goto v_reusejp_2352_;
}
v_reusejp_2352_:
{
return v___x_2353_;
}
}
}
v___jp_2357_:
{
lean_object* v___x_2359_; lean_object* v___x_2361_; 
v___x_2359_ = lean_nat_add(v___x_2356_, v___y_2358_);
lean_dec(v___y_2358_);
lean_dec(v___x_2356_);
if (v_isShared_2310_ == 0)
{
lean_ctor_set(v___x_2309_, 4, v_l_2335_);
lean_ctor_set(v___x_2309_, 3, v_l_2318_);
lean_ctor_set(v___x_2309_, 2, v_v_2317_);
lean_ctor_set(v___x_2309_, 1, v_k_2316_);
lean_ctor_set(v___x_2309_, 0, v___x_2359_);
v___x_2361_ = v___x_2309_;
goto v_reusejp_2360_;
}
else
{
lean_object* v_reuseFailAlloc_2365_; 
v_reuseFailAlloc_2365_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2365_, 0, v___x_2359_);
lean_ctor_set(v_reuseFailAlloc_2365_, 1, v_k_2316_);
lean_ctor_set(v_reuseFailAlloc_2365_, 2, v_v_2317_);
lean_ctor_set(v_reuseFailAlloc_2365_, 3, v_l_2318_);
lean_ctor_set(v_reuseFailAlloc_2365_, 4, v_l_2335_);
v___x_2361_ = v_reuseFailAlloc_2365_;
goto v_reusejp_2360_;
}
v_reusejp_2360_:
{
lean_object* v___x_2362_; 
v___x_2362_ = lean_nat_add(v___x_2313_, v_size_2314_);
if (lean_obj_tag(v_r_2336_) == 0)
{
lean_object* v_size_2363_; 
v_size_2363_ = lean_ctor_get(v_r_2336_, 0);
lean_inc(v_size_2363_);
v___y_2346_ = v___x_2361_;
v___y_2347_ = v___x_2362_;
v___y_2348_ = v_size_2363_;
goto v___jp_2345_;
}
else
{
lean_object* v___x_2364_; 
v___x_2364_ = lean_unsigned_to_nat(0u);
v___y_2346_ = v___x_2361_;
v___y_2347_ = v___x_2362_;
v___y_2348_ = v___x_2364_;
goto v___jp_2345_;
}
}
}
}
}
else
{
lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2379_; 
lean_del_object(v___x_2309_);
v___x_2374_ = lean_nat_add(v___x_2313_, v_size_2315_);
lean_dec(v_size_2315_);
v___x_2375_ = lean_nat_add(v___x_2374_, v_size_2314_);
lean_dec(v___x_2374_);
v___x_2376_ = lean_nat_add(v___x_2313_, v_size_2314_);
v___x_2377_ = lean_nat_add(v___x_2376_, v_size_2332_);
lean_dec(v___x_2376_);
lean_inc_ref(v_r_2307_);
if (v_isShared_2330_ == 0)
{
lean_ctor_set(v___x_2329_, 4, v_r_2307_);
lean_ctor_set(v___x_2329_, 3, v_r_2319_);
lean_ctor_set(v___x_2329_, 2, v_v_2305_);
lean_ctor_set(v___x_2329_, 1, v_k_2304_);
lean_ctor_set(v___x_2329_, 0, v___x_2377_);
v___x_2379_ = v___x_2329_;
goto v_reusejp_2378_;
}
else
{
lean_object* v_reuseFailAlloc_2392_; 
v_reuseFailAlloc_2392_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2392_, 0, v___x_2377_);
lean_ctor_set(v_reuseFailAlloc_2392_, 1, v_k_2304_);
lean_ctor_set(v_reuseFailAlloc_2392_, 2, v_v_2305_);
lean_ctor_set(v_reuseFailAlloc_2392_, 3, v_r_2319_);
lean_ctor_set(v_reuseFailAlloc_2392_, 4, v_r_2307_);
v___x_2379_ = v_reuseFailAlloc_2392_;
goto v_reusejp_2378_;
}
v_reusejp_2378_:
{
lean_object* v___x_2381_; uint8_t v_isShared_2382_; uint8_t v_isSharedCheck_2386_; 
v_isSharedCheck_2386_ = !lean_is_exclusive(v_r_2307_);
if (v_isSharedCheck_2386_ == 0)
{
lean_object* v_unused_2387_; lean_object* v_unused_2388_; lean_object* v_unused_2389_; lean_object* v_unused_2390_; lean_object* v_unused_2391_; 
v_unused_2387_ = lean_ctor_get(v_r_2307_, 4);
lean_dec(v_unused_2387_);
v_unused_2388_ = lean_ctor_get(v_r_2307_, 3);
lean_dec(v_unused_2388_);
v_unused_2389_ = lean_ctor_get(v_r_2307_, 2);
lean_dec(v_unused_2389_);
v_unused_2390_ = lean_ctor_get(v_r_2307_, 1);
lean_dec(v_unused_2390_);
v_unused_2391_ = lean_ctor_get(v_r_2307_, 0);
lean_dec(v_unused_2391_);
v___x_2381_ = v_r_2307_;
v_isShared_2382_ = v_isSharedCheck_2386_;
goto v_resetjp_2380_;
}
else
{
lean_dec(v_r_2307_);
v___x_2381_ = lean_box(0);
v_isShared_2382_ = v_isSharedCheck_2386_;
goto v_resetjp_2380_;
}
v_resetjp_2380_:
{
lean_object* v___x_2384_; 
if (v_isShared_2382_ == 0)
{
lean_ctor_set(v___x_2381_, 4, v___x_2379_);
lean_ctor_set(v___x_2381_, 3, v_l_2318_);
lean_ctor_set(v___x_2381_, 2, v_v_2317_);
lean_ctor_set(v___x_2381_, 1, v_k_2316_);
lean_ctor_set(v___x_2381_, 0, v___x_2375_);
v___x_2384_ = v___x_2381_;
goto v_reusejp_2383_;
}
else
{
lean_object* v_reuseFailAlloc_2385_; 
v_reuseFailAlloc_2385_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2385_, 0, v___x_2375_);
lean_ctor_set(v_reuseFailAlloc_2385_, 1, v_k_2316_);
lean_ctor_set(v_reuseFailAlloc_2385_, 2, v_v_2317_);
lean_ctor_set(v_reuseFailAlloc_2385_, 3, v_l_2318_);
lean_ctor_set(v_reuseFailAlloc_2385_, 4, v___x_2379_);
v___x_2384_ = v_reuseFailAlloc_2385_;
goto v_reusejp_2383_;
}
v_reusejp_2383_:
{
return v___x_2384_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_2399_; 
v_l_2399_ = lean_ctor_get(v_impl_2312_, 3);
lean_inc(v_l_2399_);
if (lean_obj_tag(v_l_2399_) == 0)
{
lean_object* v_r_2400_; lean_object* v_k_2401_; lean_object* v_v_2402_; lean_object* v___x_2404_; uint8_t v_isShared_2405_; uint8_t v_isSharedCheck_2413_; 
v_r_2400_ = lean_ctor_get(v_impl_2312_, 4);
v_k_2401_ = lean_ctor_get(v_impl_2312_, 1);
v_v_2402_ = lean_ctor_get(v_impl_2312_, 2);
v_isSharedCheck_2413_ = !lean_is_exclusive(v_impl_2312_);
if (v_isSharedCheck_2413_ == 0)
{
lean_object* v_unused_2414_; lean_object* v_unused_2415_; 
v_unused_2414_ = lean_ctor_get(v_impl_2312_, 3);
lean_dec(v_unused_2414_);
v_unused_2415_ = lean_ctor_get(v_impl_2312_, 0);
lean_dec(v_unused_2415_);
v___x_2404_ = v_impl_2312_;
v_isShared_2405_ = v_isSharedCheck_2413_;
goto v_resetjp_2403_;
}
else
{
lean_inc(v_r_2400_);
lean_inc(v_v_2402_);
lean_inc(v_k_2401_);
lean_dec(v_impl_2312_);
v___x_2404_ = lean_box(0);
v_isShared_2405_ = v_isSharedCheck_2413_;
goto v_resetjp_2403_;
}
v_resetjp_2403_:
{
lean_object* v___x_2406_; lean_object* v___x_2408_; 
v___x_2406_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_2400_);
if (v_isShared_2405_ == 0)
{
lean_ctor_set(v___x_2404_, 3, v_r_2400_);
lean_ctor_set(v___x_2404_, 2, v_v_2305_);
lean_ctor_set(v___x_2404_, 1, v_k_2304_);
lean_ctor_set(v___x_2404_, 0, v___x_2313_);
v___x_2408_ = v___x_2404_;
goto v_reusejp_2407_;
}
else
{
lean_object* v_reuseFailAlloc_2412_; 
v_reuseFailAlloc_2412_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2412_, 0, v___x_2313_);
lean_ctor_set(v_reuseFailAlloc_2412_, 1, v_k_2304_);
lean_ctor_set(v_reuseFailAlloc_2412_, 2, v_v_2305_);
lean_ctor_set(v_reuseFailAlloc_2412_, 3, v_r_2400_);
lean_ctor_set(v_reuseFailAlloc_2412_, 4, v_r_2400_);
v___x_2408_ = v_reuseFailAlloc_2412_;
goto v_reusejp_2407_;
}
v_reusejp_2407_:
{
lean_object* v___x_2410_; 
if (v_isShared_2310_ == 0)
{
lean_ctor_set(v___x_2309_, 4, v___x_2408_);
lean_ctor_set(v___x_2309_, 3, v_l_2399_);
lean_ctor_set(v___x_2309_, 2, v_v_2402_);
lean_ctor_set(v___x_2309_, 1, v_k_2401_);
lean_ctor_set(v___x_2309_, 0, v___x_2406_);
v___x_2410_ = v___x_2309_;
goto v_reusejp_2409_;
}
else
{
lean_object* v_reuseFailAlloc_2411_; 
v_reuseFailAlloc_2411_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2411_, 0, v___x_2406_);
lean_ctor_set(v_reuseFailAlloc_2411_, 1, v_k_2401_);
lean_ctor_set(v_reuseFailAlloc_2411_, 2, v_v_2402_);
lean_ctor_set(v_reuseFailAlloc_2411_, 3, v_l_2399_);
lean_ctor_set(v_reuseFailAlloc_2411_, 4, v___x_2408_);
v___x_2410_ = v_reuseFailAlloc_2411_;
goto v_reusejp_2409_;
}
v_reusejp_2409_:
{
return v___x_2410_;
}
}
}
}
else
{
lean_object* v_r_2416_; 
v_r_2416_ = lean_ctor_get(v_impl_2312_, 4);
lean_inc(v_r_2416_);
if (lean_obj_tag(v_r_2416_) == 0)
{
lean_object* v_k_2417_; lean_object* v_v_2418_; lean_object* v___x_2420_; uint8_t v_isShared_2421_; uint8_t v_isSharedCheck_2441_; 
v_k_2417_ = lean_ctor_get(v_impl_2312_, 1);
v_v_2418_ = lean_ctor_get(v_impl_2312_, 2);
v_isSharedCheck_2441_ = !lean_is_exclusive(v_impl_2312_);
if (v_isSharedCheck_2441_ == 0)
{
lean_object* v_unused_2442_; lean_object* v_unused_2443_; lean_object* v_unused_2444_; 
v_unused_2442_ = lean_ctor_get(v_impl_2312_, 4);
lean_dec(v_unused_2442_);
v_unused_2443_ = lean_ctor_get(v_impl_2312_, 3);
lean_dec(v_unused_2443_);
v_unused_2444_ = lean_ctor_get(v_impl_2312_, 0);
lean_dec(v_unused_2444_);
v___x_2420_ = v_impl_2312_;
v_isShared_2421_ = v_isSharedCheck_2441_;
goto v_resetjp_2419_;
}
else
{
lean_inc(v_v_2418_);
lean_inc(v_k_2417_);
lean_dec(v_impl_2312_);
v___x_2420_ = lean_box(0);
v_isShared_2421_ = v_isSharedCheck_2441_;
goto v_resetjp_2419_;
}
v_resetjp_2419_:
{
lean_object* v_k_2422_; lean_object* v_v_2423_; lean_object* v___x_2425_; uint8_t v_isShared_2426_; uint8_t v_isSharedCheck_2437_; 
v_k_2422_ = lean_ctor_get(v_r_2416_, 1);
v_v_2423_ = lean_ctor_get(v_r_2416_, 2);
v_isSharedCheck_2437_ = !lean_is_exclusive(v_r_2416_);
if (v_isSharedCheck_2437_ == 0)
{
lean_object* v_unused_2438_; lean_object* v_unused_2439_; lean_object* v_unused_2440_; 
v_unused_2438_ = lean_ctor_get(v_r_2416_, 4);
lean_dec(v_unused_2438_);
v_unused_2439_ = lean_ctor_get(v_r_2416_, 3);
lean_dec(v_unused_2439_);
v_unused_2440_ = lean_ctor_get(v_r_2416_, 0);
lean_dec(v_unused_2440_);
v___x_2425_ = v_r_2416_;
v_isShared_2426_ = v_isSharedCheck_2437_;
goto v_resetjp_2424_;
}
else
{
lean_inc(v_v_2423_);
lean_inc(v_k_2422_);
lean_dec(v_r_2416_);
v___x_2425_ = lean_box(0);
v_isShared_2426_ = v_isSharedCheck_2437_;
goto v_resetjp_2424_;
}
v_resetjp_2424_:
{
lean_object* v___x_2427_; lean_object* v___x_2429_; 
v___x_2427_ = lean_unsigned_to_nat(3u);
if (v_isShared_2426_ == 0)
{
lean_ctor_set(v___x_2425_, 4, v_l_2399_);
lean_ctor_set(v___x_2425_, 3, v_l_2399_);
lean_ctor_set(v___x_2425_, 2, v_v_2418_);
lean_ctor_set(v___x_2425_, 1, v_k_2417_);
lean_ctor_set(v___x_2425_, 0, v___x_2313_);
v___x_2429_ = v___x_2425_;
goto v_reusejp_2428_;
}
else
{
lean_object* v_reuseFailAlloc_2436_; 
v_reuseFailAlloc_2436_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2436_, 0, v___x_2313_);
lean_ctor_set(v_reuseFailAlloc_2436_, 1, v_k_2417_);
lean_ctor_set(v_reuseFailAlloc_2436_, 2, v_v_2418_);
lean_ctor_set(v_reuseFailAlloc_2436_, 3, v_l_2399_);
lean_ctor_set(v_reuseFailAlloc_2436_, 4, v_l_2399_);
v___x_2429_ = v_reuseFailAlloc_2436_;
goto v_reusejp_2428_;
}
v_reusejp_2428_:
{
lean_object* v___x_2431_; 
if (v_isShared_2421_ == 0)
{
lean_ctor_set(v___x_2420_, 4, v_l_2399_);
lean_ctor_set(v___x_2420_, 2, v_v_2305_);
lean_ctor_set(v___x_2420_, 1, v_k_2304_);
lean_ctor_set(v___x_2420_, 0, v___x_2313_);
v___x_2431_ = v___x_2420_;
goto v_reusejp_2430_;
}
else
{
lean_object* v_reuseFailAlloc_2435_; 
v_reuseFailAlloc_2435_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2435_, 0, v___x_2313_);
lean_ctor_set(v_reuseFailAlloc_2435_, 1, v_k_2304_);
lean_ctor_set(v_reuseFailAlloc_2435_, 2, v_v_2305_);
lean_ctor_set(v_reuseFailAlloc_2435_, 3, v_l_2399_);
lean_ctor_set(v_reuseFailAlloc_2435_, 4, v_l_2399_);
v___x_2431_ = v_reuseFailAlloc_2435_;
goto v_reusejp_2430_;
}
v_reusejp_2430_:
{
lean_object* v___x_2433_; 
if (v_isShared_2310_ == 0)
{
lean_ctor_set(v___x_2309_, 4, v___x_2431_);
lean_ctor_set(v___x_2309_, 3, v___x_2429_);
lean_ctor_set(v___x_2309_, 2, v_v_2423_);
lean_ctor_set(v___x_2309_, 1, v_k_2422_);
lean_ctor_set(v___x_2309_, 0, v___x_2427_);
v___x_2433_ = v___x_2309_;
goto v_reusejp_2432_;
}
else
{
lean_object* v_reuseFailAlloc_2434_; 
v_reuseFailAlloc_2434_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2434_, 0, v___x_2427_);
lean_ctor_set(v_reuseFailAlloc_2434_, 1, v_k_2422_);
lean_ctor_set(v_reuseFailAlloc_2434_, 2, v_v_2423_);
lean_ctor_set(v_reuseFailAlloc_2434_, 3, v___x_2429_);
lean_ctor_set(v_reuseFailAlloc_2434_, 4, v___x_2431_);
v___x_2433_ = v_reuseFailAlloc_2434_;
goto v_reusejp_2432_;
}
v_reusejp_2432_:
{
return v___x_2433_;
}
}
}
}
}
}
else
{
lean_object* v___x_2445_; lean_object* v___x_2447_; 
v___x_2445_ = lean_unsigned_to_nat(2u);
if (v_isShared_2310_ == 0)
{
lean_ctor_set(v___x_2309_, 4, v_r_2416_);
lean_ctor_set(v___x_2309_, 3, v_impl_2312_);
lean_ctor_set(v___x_2309_, 0, v___x_2445_);
v___x_2447_ = v___x_2309_;
goto v_reusejp_2446_;
}
else
{
lean_object* v_reuseFailAlloc_2448_; 
v_reuseFailAlloc_2448_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2448_, 0, v___x_2445_);
lean_ctor_set(v_reuseFailAlloc_2448_, 1, v_k_2304_);
lean_ctor_set(v_reuseFailAlloc_2448_, 2, v_v_2305_);
lean_ctor_set(v_reuseFailAlloc_2448_, 3, v_impl_2312_);
lean_ctor_set(v_reuseFailAlloc_2448_, 4, v_r_2416_);
v___x_2447_ = v_reuseFailAlloc_2448_;
goto v_reusejp_2446_;
}
v_reusejp_2446_:
{
return v___x_2447_;
}
}
}
}
}
case 1:
{
lean_object* v___x_2450_; 
lean_dec(v_v_2305_);
lean_dec(v_k_2304_);
if (v_isShared_2310_ == 0)
{
lean_ctor_set(v___x_2309_, 2, v_v_2301_);
lean_ctor_set(v___x_2309_, 1, v_k_2300_);
v___x_2450_ = v___x_2309_;
goto v_reusejp_2449_;
}
else
{
lean_object* v_reuseFailAlloc_2451_; 
v_reuseFailAlloc_2451_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2451_, 0, v_size_2303_);
lean_ctor_set(v_reuseFailAlloc_2451_, 1, v_k_2300_);
lean_ctor_set(v_reuseFailAlloc_2451_, 2, v_v_2301_);
lean_ctor_set(v_reuseFailAlloc_2451_, 3, v_l_2306_);
lean_ctor_set(v_reuseFailAlloc_2451_, 4, v_r_2307_);
v___x_2450_ = v_reuseFailAlloc_2451_;
goto v_reusejp_2449_;
}
v_reusejp_2449_:
{
return v___x_2450_;
}
}
default: 
{
lean_object* v_impl_2452_; lean_object* v___x_2453_; 
lean_dec(v_size_2303_);
v_impl_2452_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Level_collectMVars_spec__1___redArg(v_k_2300_, v_v_2301_, v_r_2307_);
v___x_2453_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_2306_) == 0)
{
lean_object* v_size_2454_; lean_object* v_size_2455_; lean_object* v_k_2456_; lean_object* v_v_2457_; lean_object* v_l_2458_; lean_object* v_r_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; uint8_t v___x_2462_; 
v_size_2454_ = lean_ctor_get(v_l_2306_, 0);
v_size_2455_ = lean_ctor_get(v_impl_2452_, 0);
lean_inc(v_size_2455_);
v_k_2456_ = lean_ctor_get(v_impl_2452_, 1);
lean_inc(v_k_2456_);
v_v_2457_ = lean_ctor_get(v_impl_2452_, 2);
lean_inc(v_v_2457_);
v_l_2458_ = lean_ctor_get(v_impl_2452_, 3);
lean_inc(v_l_2458_);
v_r_2459_ = lean_ctor_get(v_impl_2452_, 4);
lean_inc(v_r_2459_);
v___x_2460_ = lean_unsigned_to_nat(3u);
v___x_2461_ = lean_nat_mul(v___x_2460_, v_size_2454_);
v___x_2462_ = lean_nat_dec_lt(v___x_2461_, v_size_2455_);
lean_dec(v___x_2461_);
if (v___x_2462_ == 0)
{
lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2466_; 
lean_dec(v_r_2459_);
lean_dec(v_l_2458_);
lean_dec(v_v_2457_);
lean_dec(v_k_2456_);
v___x_2463_ = lean_nat_add(v___x_2453_, v_size_2454_);
v___x_2464_ = lean_nat_add(v___x_2463_, v_size_2455_);
lean_dec(v_size_2455_);
lean_dec(v___x_2463_);
if (v_isShared_2310_ == 0)
{
lean_ctor_set(v___x_2309_, 4, v_impl_2452_);
lean_ctor_set(v___x_2309_, 0, v___x_2464_);
v___x_2466_ = v___x_2309_;
goto v_reusejp_2465_;
}
else
{
lean_object* v_reuseFailAlloc_2467_; 
v_reuseFailAlloc_2467_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2467_, 0, v___x_2464_);
lean_ctor_set(v_reuseFailAlloc_2467_, 1, v_k_2304_);
lean_ctor_set(v_reuseFailAlloc_2467_, 2, v_v_2305_);
lean_ctor_set(v_reuseFailAlloc_2467_, 3, v_l_2306_);
lean_ctor_set(v_reuseFailAlloc_2467_, 4, v_impl_2452_);
v___x_2466_ = v_reuseFailAlloc_2467_;
goto v_reusejp_2465_;
}
v_reusejp_2465_:
{
return v___x_2466_;
}
}
else
{
lean_object* v___x_2469_; uint8_t v_isShared_2470_; uint8_t v_isSharedCheck_2531_; 
v_isSharedCheck_2531_ = !lean_is_exclusive(v_impl_2452_);
if (v_isSharedCheck_2531_ == 0)
{
lean_object* v_unused_2532_; lean_object* v_unused_2533_; lean_object* v_unused_2534_; lean_object* v_unused_2535_; lean_object* v_unused_2536_; 
v_unused_2532_ = lean_ctor_get(v_impl_2452_, 4);
lean_dec(v_unused_2532_);
v_unused_2533_ = lean_ctor_get(v_impl_2452_, 3);
lean_dec(v_unused_2533_);
v_unused_2534_ = lean_ctor_get(v_impl_2452_, 2);
lean_dec(v_unused_2534_);
v_unused_2535_ = lean_ctor_get(v_impl_2452_, 1);
lean_dec(v_unused_2535_);
v_unused_2536_ = lean_ctor_get(v_impl_2452_, 0);
lean_dec(v_unused_2536_);
v___x_2469_ = v_impl_2452_;
v_isShared_2470_ = v_isSharedCheck_2531_;
goto v_resetjp_2468_;
}
else
{
lean_dec(v_impl_2452_);
v___x_2469_ = lean_box(0);
v_isShared_2470_ = v_isSharedCheck_2531_;
goto v_resetjp_2468_;
}
v_resetjp_2468_:
{
lean_object* v_size_2471_; lean_object* v_k_2472_; lean_object* v_v_2473_; lean_object* v_l_2474_; lean_object* v_r_2475_; lean_object* v_size_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; uint8_t v___x_2479_; 
v_size_2471_ = lean_ctor_get(v_l_2458_, 0);
v_k_2472_ = lean_ctor_get(v_l_2458_, 1);
v_v_2473_ = lean_ctor_get(v_l_2458_, 2);
v_l_2474_ = lean_ctor_get(v_l_2458_, 3);
v_r_2475_ = lean_ctor_get(v_l_2458_, 4);
v_size_2476_ = lean_ctor_get(v_r_2459_, 0);
v___x_2477_ = lean_unsigned_to_nat(2u);
v___x_2478_ = lean_nat_mul(v___x_2477_, v_size_2476_);
v___x_2479_ = lean_nat_dec_lt(v_size_2471_, v___x_2478_);
lean_dec(v___x_2478_);
if (v___x_2479_ == 0)
{
lean_object* v___x_2481_; uint8_t v_isShared_2482_; uint8_t v_isSharedCheck_2507_; 
lean_inc(v_r_2475_);
lean_inc(v_l_2474_);
lean_inc(v_v_2473_);
lean_inc(v_k_2472_);
v_isSharedCheck_2507_ = !lean_is_exclusive(v_l_2458_);
if (v_isSharedCheck_2507_ == 0)
{
lean_object* v_unused_2508_; lean_object* v_unused_2509_; lean_object* v_unused_2510_; lean_object* v_unused_2511_; lean_object* v_unused_2512_; 
v_unused_2508_ = lean_ctor_get(v_l_2458_, 4);
lean_dec(v_unused_2508_);
v_unused_2509_ = lean_ctor_get(v_l_2458_, 3);
lean_dec(v_unused_2509_);
v_unused_2510_ = lean_ctor_get(v_l_2458_, 2);
lean_dec(v_unused_2510_);
v_unused_2511_ = lean_ctor_get(v_l_2458_, 1);
lean_dec(v_unused_2511_);
v_unused_2512_ = lean_ctor_get(v_l_2458_, 0);
lean_dec(v_unused_2512_);
v___x_2481_ = v_l_2458_;
v_isShared_2482_ = v_isSharedCheck_2507_;
goto v_resetjp_2480_;
}
else
{
lean_dec(v_l_2458_);
v___x_2481_ = lean_box(0);
v_isShared_2482_ = v_isSharedCheck_2507_;
goto v_resetjp_2480_;
}
v_resetjp_2480_:
{
lean_object* v___x_2483_; lean_object* v___x_2484_; lean_object* v___y_2486_; lean_object* v___y_2487_; lean_object* v___y_2488_; lean_object* v___y_2497_; 
v___x_2483_ = lean_nat_add(v___x_2453_, v_size_2454_);
v___x_2484_ = lean_nat_add(v___x_2483_, v_size_2455_);
lean_dec(v_size_2455_);
if (lean_obj_tag(v_l_2474_) == 0)
{
lean_object* v_size_2505_; 
v_size_2505_ = lean_ctor_get(v_l_2474_, 0);
lean_inc(v_size_2505_);
v___y_2497_ = v_size_2505_;
goto v___jp_2496_;
}
else
{
lean_object* v___x_2506_; 
v___x_2506_ = lean_unsigned_to_nat(0u);
v___y_2497_ = v___x_2506_;
goto v___jp_2496_;
}
v___jp_2485_:
{
lean_object* v___x_2489_; lean_object* v___x_2491_; 
v___x_2489_ = lean_nat_add(v___y_2487_, v___y_2488_);
lean_dec(v___y_2488_);
lean_dec(v___y_2487_);
if (v_isShared_2482_ == 0)
{
lean_ctor_set(v___x_2481_, 4, v_r_2459_);
lean_ctor_set(v___x_2481_, 3, v_r_2475_);
lean_ctor_set(v___x_2481_, 2, v_v_2457_);
lean_ctor_set(v___x_2481_, 1, v_k_2456_);
lean_ctor_set(v___x_2481_, 0, v___x_2489_);
v___x_2491_ = v___x_2481_;
goto v_reusejp_2490_;
}
else
{
lean_object* v_reuseFailAlloc_2495_; 
v_reuseFailAlloc_2495_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2495_, 0, v___x_2489_);
lean_ctor_set(v_reuseFailAlloc_2495_, 1, v_k_2456_);
lean_ctor_set(v_reuseFailAlloc_2495_, 2, v_v_2457_);
lean_ctor_set(v_reuseFailAlloc_2495_, 3, v_r_2475_);
lean_ctor_set(v_reuseFailAlloc_2495_, 4, v_r_2459_);
v___x_2491_ = v_reuseFailAlloc_2495_;
goto v_reusejp_2490_;
}
v_reusejp_2490_:
{
lean_object* v___x_2493_; 
if (v_isShared_2470_ == 0)
{
lean_ctor_set(v___x_2469_, 4, v___x_2491_);
lean_ctor_set(v___x_2469_, 3, v___y_2486_);
lean_ctor_set(v___x_2469_, 2, v_v_2473_);
lean_ctor_set(v___x_2469_, 1, v_k_2472_);
lean_ctor_set(v___x_2469_, 0, v___x_2484_);
v___x_2493_ = v___x_2469_;
goto v_reusejp_2492_;
}
else
{
lean_object* v_reuseFailAlloc_2494_; 
v_reuseFailAlloc_2494_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2494_, 0, v___x_2484_);
lean_ctor_set(v_reuseFailAlloc_2494_, 1, v_k_2472_);
lean_ctor_set(v_reuseFailAlloc_2494_, 2, v_v_2473_);
lean_ctor_set(v_reuseFailAlloc_2494_, 3, v___y_2486_);
lean_ctor_set(v_reuseFailAlloc_2494_, 4, v___x_2491_);
v___x_2493_ = v_reuseFailAlloc_2494_;
goto v_reusejp_2492_;
}
v_reusejp_2492_:
{
return v___x_2493_;
}
}
}
v___jp_2496_:
{
lean_object* v___x_2498_; lean_object* v___x_2500_; 
v___x_2498_ = lean_nat_add(v___x_2483_, v___y_2497_);
lean_dec(v___y_2497_);
lean_dec(v___x_2483_);
if (v_isShared_2310_ == 0)
{
lean_ctor_set(v___x_2309_, 4, v_l_2474_);
lean_ctor_set(v___x_2309_, 0, v___x_2498_);
v___x_2500_ = v___x_2309_;
goto v_reusejp_2499_;
}
else
{
lean_object* v_reuseFailAlloc_2504_; 
v_reuseFailAlloc_2504_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2504_, 0, v___x_2498_);
lean_ctor_set(v_reuseFailAlloc_2504_, 1, v_k_2304_);
lean_ctor_set(v_reuseFailAlloc_2504_, 2, v_v_2305_);
lean_ctor_set(v_reuseFailAlloc_2504_, 3, v_l_2306_);
lean_ctor_set(v_reuseFailAlloc_2504_, 4, v_l_2474_);
v___x_2500_ = v_reuseFailAlloc_2504_;
goto v_reusejp_2499_;
}
v_reusejp_2499_:
{
lean_object* v___x_2501_; 
v___x_2501_ = lean_nat_add(v___x_2453_, v_size_2476_);
if (lean_obj_tag(v_r_2475_) == 0)
{
lean_object* v_size_2502_; 
v_size_2502_ = lean_ctor_get(v_r_2475_, 0);
lean_inc(v_size_2502_);
v___y_2486_ = v___x_2500_;
v___y_2487_ = v___x_2501_;
v___y_2488_ = v_size_2502_;
goto v___jp_2485_;
}
else
{
lean_object* v___x_2503_; 
v___x_2503_ = lean_unsigned_to_nat(0u);
v___y_2486_ = v___x_2500_;
v___y_2487_ = v___x_2501_;
v___y_2488_ = v___x_2503_;
goto v___jp_2485_;
}
}
}
}
}
else
{
lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2517_; 
lean_del_object(v___x_2309_);
v___x_2513_ = lean_nat_add(v___x_2453_, v_size_2454_);
v___x_2514_ = lean_nat_add(v___x_2513_, v_size_2455_);
lean_dec(v_size_2455_);
v___x_2515_ = lean_nat_add(v___x_2513_, v_size_2471_);
lean_dec(v___x_2513_);
lean_inc_ref(v_l_2306_);
if (v_isShared_2470_ == 0)
{
lean_ctor_set(v___x_2469_, 4, v_l_2458_);
lean_ctor_set(v___x_2469_, 3, v_l_2306_);
lean_ctor_set(v___x_2469_, 2, v_v_2305_);
lean_ctor_set(v___x_2469_, 1, v_k_2304_);
lean_ctor_set(v___x_2469_, 0, v___x_2515_);
v___x_2517_ = v___x_2469_;
goto v_reusejp_2516_;
}
else
{
lean_object* v_reuseFailAlloc_2530_; 
v_reuseFailAlloc_2530_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2530_, 0, v___x_2515_);
lean_ctor_set(v_reuseFailAlloc_2530_, 1, v_k_2304_);
lean_ctor_set(v_reuseFailAlloc_2530_, 2, v_v_2305_);
lean_ctor_set(v_reuseFailAlloc_2530_, 3, v_l_2306_);
lean_ctor_set(v_reuseFailAlloc_2530_, 4, v_l_2458_);
v___x_2517_ = v_reuseFailAlloc_2530_;
goto v_reusejp_2516_;
}
v_reusejp_2516_:
{
lean_object* v___x_2519_; uint8_t v_isShared_2520_; uint8_t v_isSharedCheck_2524_; 
v_isSharedCheck_2524_ = !lean_is_exclusive(v_l_2306_);
if (v_isSharedCheck_2524_ == 0)
{
lean_object* v_unused_2525_; lean_object* v_unused_2526_; lean_object* v_unused_2527_; lean_object* v_unused_2528_; lean_object* v_unused_2529_; 
v_unused_2525_ = lean_ctor_get(v_l_2306_, 4);
lean_dec(v_unused_2525_);
v_unused_2526_ = lean_ctor_get(v_l_2306_, 3);
lean_dec(v_unused_2526_);
v_unused_2527_ = lean_ctor_get(v_l_2306_, 2);
lean_dec(v_unused_2527_);
v_unused_2528_ = lean_ctor_get(v_l_2306_, 1);
lean_dec(v_unused_2528_);
v_unused_2529_ = lean_ctor_get(v_l_2306_, 0);
lean_dec(v_unused_2529_);
v___x_2519_ = v_l_2306_;
v_isShared_2520_ = v_isSharedCheck_2524_;
goto v_resetjp_2518_;
}
else
{
lean_dec(v_l_2306_);
v___x_2519_ = lean_box(0);
v_isShared_2520_ = v_isSharedCheck_2524_;
goto v_resetjp_2518_;
}
v_resetjp_2518_:
{
lean_object* v___x_2522_; 
if (v_isShared_2520_ == 0)
{
lean_ctor_set(v___x_2519_, 4, v_r_2459_);
lean_ctor_set(v___x_2519_, 3, v___x_2517_);
lean_ctor_set(v___x_2519_, 2, v_v_2457_);
lean_ctor_set(v___x_2519_, 1, v_k_2456_);
lean_ctor_set(v___x_2519_, 0, v___x_2514_);
v___x_2522_ = v___x_2519_;
goto v_reusejp_2521_;
}
else
{
lean_object* v_reuseFailAlloc_2523_; 
v_reuseFailAlloc_2523_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2523_, 0, v___x_2514_);
lean_ctor_set(v_reuseFailAlloc_2523_, 1, v_k_2456_);
lean_ctor_set(v_reuseFailAlloc_2523_, 2, v_v_2457_);
lean_ctor_set(v_reuseFailAlloc_2523_, 3, v___x_2517_);
lean_ctor_set(v_reuseFailAlloc_2523_, 4, v_r_2459_);
v___x_2522_ = v_reuseFailAlloc_2523_;
goto v_reusejp_2521_;
}
v_reusejp_2521_:
{
return v___x_2522_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_2537_; 
v_l_2537_ = lean_ctor_get(v_impl_2452_, 3);
lean_inc(v_l_2537_);
if (lean_obj_tag(v_l_2537_) == 0)
{
lean_object* v_r_2538_; lean_object* v_k_2539_; lean_object* v_v_2540_; lean_object* v___x_2542_; uint8_t v_isShared_2543_; uint8_t v_isSharedCheck_2563_; 
v_r_2538_ = lean_ctor_get(v_impl_2452_, 4);
v_k_2539_ = lean_ctor_get(v_impl_2452_, 1);
v_v_2540_ = lean_ctor_get(v_impl_2452_, 2);
v_isSharedCheck_2563_ = !lean_is_exclusive(v_impl_2452_);
if (v_isSharedCheck_2563_ == 0)
{
lean_object* v_unused_2564_; lean_object* v_unused_2565_; 
v_unused_2564_ = lean_ctor_get(v_impl_2452_, 3);
lean_dec(v_unused_2564_);
v_unused_2565_ = lean_ctor_get(v_impl_2452_, 0);
lean_dec(v_unused_2565_);
v___x_2542_ = v_impl_2452_;
v_isShared_2543_ = v_isSharedCheck_2563_;
goto v_resetjp_2541_;
}
else
{
lean_inc(v_r_2538_);
lean_inc(v_v_2540_);
lean_inc(v_k_2539_);
lean_dec(v_impl_2452_);
v___x_2542_ = lean_box(0);
v_isShared_2543_ = v_isSharedCheck_2563_;
goto v_resetjp_2541_;
}
v_resetjp_2541_:
{
lean_object* v_k_2544_; lean_object* v_v_2545_; lean_object* v___x_2547_; uint8_t v_isShared_2548_; uint8_t v_isSharedCheck_2559_; 
v_k_2544_ = lean_ctor_get(v_l_2537_, 1);
v_v_2545_ = lean_ctor_get(v_l_2537_, 2);
v_isSharedCheck_2559_ = !lean_is_exclusive(v_l_2537_);
if (v_isSharedCheck_2559_ == 0)
{
lean_object* v_unused_2560_; lean_object* v_unused_2561_; lean_object* v_unused_2562_; 
v_unused_2560_ = lean_ctor_get(v_l_2537_, 4);
lean_dec(v_unused_2560_);
v_unused_2561_ = lean_ctor_get(v_l_2537_, 3);
lean_dec(v_unused_2561_);
v_unused_2562_ = lean_ctor_get(v_l_2537_, 0);
lean_dec(v_unused_2562_);
v___x_2547_ = v_l_2537_;
v_isShared_2548_ = v_isSharedCheck_2559_;
goto v_resetjp_2546_;
}
else
{
lean_inc(v_v_2545_);
lean_inc(v_k_2544_);
lean_dec(v_l_2537_);
v___x_2547_ = lean_box(0);
v_isShared_2548_ = v_isSharedCheck_2559_;
goto v_resetjp_2546_;
}
v_resetjp_2546_:
{
lean_object* v___x_2549_; lean_object* v___x_2551_; 
v___x_2549_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_2538_, 2);
if (v_isShared_2548_ == 0)
{
lean_ctor_set(v___x_2547_, 4, v_r_2538_);
lean_ctor_set(v___x_2547_, 3, v_r_2538_);
lean_ctor_set(v___x_2547_, 2, v_v_2305_);
lean_ctor_set(v___x_2547_, 1, v_k_2304_);
lean_ctor_set(v___x_2547_, 0, v___x_2453_);
v___x_2551_ = v___x_2547_;
goto v_reusejp_2550_;
}
else
{
lean_object* v_reuseFailAlloc_2558_; 
v_reuseFailAlloc_2558_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2558_, 0, v___x_2453_);
lean_ctor_set(v_reuseFailAlloc_2558_, 1, v_k_2304_);
lean_ctor_set(v_reuseFailAlloc_2558_, 2, v_v_2305_);
lean_ctor_set(v_reuseFailAlloc_2558_, 3, v_r_2538_);
lean_ctor_set(v_reuseFailAlloc_2558_, 4, v_r_2538_);
v___x_2551_ = v_reuseFailAlloc_2558_;
goto v_reusejp_2550_;
}
v_reusejp_2550_:
{
lean_object* v___x_2553_; 
lean_inc(v_r_2538_);
if (v_isShared_2543_ == 0)
{
lean_ctor_set(v___x_2542_, 3, v_r_2538_);
lean_ctor_set(v___x_2542_, 0, v___x_2453_);
v___x_2553_ = v___x_2542_;
goto v_reusejp_2552_;
}
else
{
lean_object* v_reuseFailAlloc_2557_; 
v_reuseFailAlloc_2557_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2557_, 0, v___x_2453_);
lean_ctor_set(v_reuseFailAlloc_2557_, 1, v_k_2539_);
lean_ctor_set(v_reuseFailAlloc_2557_, 2, v_v_2540_);
lean_ctor_set(v_reuseFailAlloc_2557_, 3, v_r_2538_);
lean_ctor_set(v_reuseFailAlloc_2557_, 4, v_r_2538_);
v___x_2553_ = v_reuseFailAlloc_2557_;
goto v_reusejp_2552_;
}
v_reusejp_2552_:
{
lean_object* v___x_2555_; 
if (v_isShared_2310_ == 0)
{
lean_ctor_set(v___x_2309_, 4, v___x_2553_);
lean_ctor_set(v___x_2309_, 3, v___x_2551_);
lean_ctor_set(v___x_2309_, 2, v_v_2545_);
lean_ctor_set(v___x_2309_, 1, v_k_2544_);
lean_ctor_set(v___x_2309_, 0, v___x_2549_);
v___x_2555_ = v___x_2309_;
goto v_reusejp_2554_;
}
else
{
lean_object* v_reuseFailAlloc_2556_; 
v_reuseFailAlloc_2556_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2556_, 0, v___x_2549_);
lean_ctor_set(v_reuseFailAlloc_2556_, 1, v_k_2544_);
lean_ctor_set(v_reuseFailAlloc_2556_, 2, v_v_2545_);
lean_ctor_set(v_reuseFailAlloc_2556_, 3, v___x_2551_);
lean_ctor_set(v_reuseFailAlloc_2556_, 4, v___x_2553_);
v___x_2555_ = v_reuseFailAlloc_2556_;
goto v_reusejp_2554_;
}
v_reusejp_2554_:
{
return v___x_2555_;
}
}
}
}
}
}
else
{
lean_object* v_r_2566_; 
v_r_2566_ = lean_ctor_get(v_impl_2452_, 4);
lean_inc(v_r_2566_);
if (lean_obj_tag(v_r_2566_) == 0)
{
lean_object* v_k_2567_; lean_object* v_v_2568_; lean_object* v___x_2570_; uint8_t v_isShared_2571_; uint8_t v_isSharedCheck_2579_; 
v_k_2567_ = lean_ctor_get(v_impl_2452_, 1);
v_v_2568_ = lean_ctor_get(v_impl_2452_, 2);
v_isSharedCheck_2579_ = !lean_is_exclusive(v_impl_2452_);
if (v_isSharedCheck_2579_ == 0)
{
lean_object* v_unused_2580_; lean_object* v_unused_2581_; lean_object* v_unused_2582_; 
v_unused_2580_ = lean_ctor_get(v_impl_2452_, 4);
lean_dec(v_unused_2580_);
v_unused_2581_ = lean_ctor_get(v_impl_2452_, 3);
lean_dec(v_unused_2581_);
v_unused_2582_ = lean_ctor_get(v_impl_2452_, 0);
lean_dec(v_unused_2582_);
v___x_2570_ = v_impl_2452_;
v_isShared_2571_ = v_isSharedCheck_2579_;
goto v_resetjp_2569_;
}
else
{
lean_inc(v_v_2568_);
lean_inc(v_k_2567_);
lean_dec(v_impl_2452_);
v___x_2570_ = lean_box(0);
v_isShared_2571_ = v_isSharedCheck_2579_;
goto v_resetjp_2569_;
}
v_resetjp_2569_:
{
lean_object* v___x_2572_; lean_object* v___x_2574_; 
v___x_2572_ = lean_unsigned_to_nat(3u);
if (v_isShared_2571_ == 0)
{
lean_ctor_set(v___x_2570_, 4, v_l_2537_);
lean_ctor_set(v___x_2570_, 2, v_v_2305_);
lean_ctor_set(v___x_2570_, 1, v_k_2304_);
lean_ctor_set(v___x_2570_, 0, v___x_2453_);
v___x_2574_ = v___x_2570_;
goto v_reusejp_2573_;
}
else
{
lean_object* v_reuseFailAlloc_2578_; 
v_reuseFailAlloc_2578_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2578_, 0, v___x_2453_);
lean_ctor_set(v_reuseFailAlloc_2578_, 1, v_k_2304_);
lean_ctor_set(v_reuseFailAlloc_2578_, 2, v_v_2305_);
lean_ctor_set(v_reuseFailAlloc_2578_, 3, v_l_2537_);
lean_ctor_set(v_reuseFailAlloc_2578_, 4, v_l_2537_);
v___x_2574_ = v_reuseFailAlloc_2578_;
goto v_reusejp_2573_;
}
v_reusejp_2573_:
{
lean_object* v___x_2576_; 
if (v_isShared_2310_ == 0)
{
lean_ctor_set(v___x_2309_, 4, v_r_2566_);
lean_ctor_set(v___x_2309_, 3, v___x_2574_);
lean_ctor_set(v___x_2309_, 2, v_v_2568_);
lean_ctor_set(v___x_2309_, 1, v_k_2567_);
lean_ctor_set(v___x_2309_, 0, v___x_2572_);
v___x_2576_ = v___x_2309_;
goto v_reusejp_2575_;
}
else
{
lean_object* v_reuseFailAlloc_2577_; 
v_reuseFailAlloc_2577_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2577_, 0, v___x_2572_);
lean_ctor_set(v_reuseFailAlloc_2577_, 1, v_k_2567_);
lean_ctor_set(v_reuseFailAlloc_2577_, 2, v_v_2568_);
lean_ctor_set(v_reuseFailAlloc_2577_, 3, v___x_2574_);
lean_ctor_set(v_reuseFailAlloc_2577_, 4, v_r_2566_);
v___x_2576_ = v_reuseFailAlloc_2577_;
goto v_reusejp_2575_;
}
v_reusejp_2575_:
{
return v___x_2576_;
}
}
}
}
else
{
lean_object* v___x_2583_; lean_object* v___x_2585_; 
v___x_2583_ = lean_unsigned_to_nat(2u);
if (v_isShared_2310_ == 0)
{
lean_ctor_set(v___x_2309_, 4, v_impl_2452_);
lean_ctor_set(v___x_2309_, 3, v_r_2566_);
lean_ctor_set(v___x_2309_, 0, v___x_2583_);
v___x_2585_ = v___x_2309_;
goto v_reusejp_2584_;
}
else
{
lean_object* v_reuseFailAlloc_2586_; 
v_reuseFailAlloc_2586_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2586_, 0, v___x_2583_);
lean_ctor_set(v_reuseFailAlloc_2586_, 1, v_k_2304_);
lean_ctor_set(v_reuseFailAlloc_2586_, 2, v_v_2305_);
lean_ctor_set(v_reuseFailAlloc_2586_, 3, v_r_2566_);
lean_ctor_set(v_reuseFailAlloc_2586_, 4, v_impl_2452_);
v___x_2585_ = v_reuseFailAlloc_2586_;
goto v_reusejp_2584_;
}
v_reusejp_2584_:
{
return v___x_2585_;
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
lean_object* v___x_2588_; lean_object* v___x_2589_; 
v___x_2588_ = lean_unsigned_to_nat(1u);
v___x_2589_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2589_, 0, v___x_2588_);
lean_ctor_set(v___x_2589_, 1, v_k_2300_);
lean_ctor_set(v___x_2589_, 2, v_v_2301_);
lean_ctor_set(v___x_2589_, 3, v_t_2302_);
lean_ctor_set(v___x_2589_, 4, v_t_2302_);
return v___x_2589_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Level_collectMVars_spec__0___redArg(lean_object* v_k_2590_, lean_object* v_t_2591_){
_start:
{
if (lean_obj_tag(v_t_2591_) == 0)
{
lean_object* v_k_2592_; lean_object* v_l_2593_; lean_object* v_r_2594_; uint8_t v___x_2595_; 
v_k_2592_ = lean_ctor_get(v_t_2591_, 1);
v_l_2593_ = lean_ctor_get(v_t_2591_, 3);
v_r_2594_ = lean_ctor_get(v_t_2591_, 4);
v___x_2595_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2590_, v_k_2592_);
switch(v___x_2595_)
{
case 0:
{
v_t_2591_ = v_l_2593_;
goto _start;
}
case 1:
{
uint8_t v___x_2597_; 
v___x_2597_ = 1;
return v___x_2597_;
}
default: 
{
v_t_2591_ = v_r_2594_;
goto _start;
}
}
}
else
{
uint8_t v___x_2599_; 
v___x_2599_ = 0;
return v___x_2599_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Level_collectMVars_spec__0___redArg___boxed(lean_object* v_k_2600_, lean_object* v_t_2601_){
_start:
{
uint8_t v_res_2602_; lean_object* v_r_2603_; 
v_res_2602_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Level_collectMVars_spec__0___redArg(v_k_2600_, v_t_2601_);
lean_dec(v_t_2601_);
lean_dec(v_k_2600_);
v_r_2603_ = lean_box(v_res_2602_);
return v_r_2603_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_collectMVars(lean_object* v_u_2604_, lean_object* v_s_2605_){
_start:
{
lean_object* v_u_2607_; lean_object* v_v_2608_; 
switch(lean_obj_tag(v_u_2604_))
{
case 1:
{
lean_object* v_a_2611_; 
v_a_2611_ = lean_ctor_get(v_u_2604_, 0);
lean_inc(v_a_2611_);
lean_dec_ref(v_u_2604_);
v_u_2604_ = v_a_2611_;
goto _start;
}
case 2:
{
lean_object* v_a_2613_; lean_object* v_a_2614_; 
v_a_2613_ = lean_ctor_get(v_u_2604_, 0);
lean_inc(v_a_2613_);
v_a_2614_ = lean_ctor_get(v_u_2604_, 1);
lean_inc(v_a_2614_);
lean_dec_ref(v_u_2604_);
v_u_2607_ = v_a_2613_;
v_v_2608_ = v_a_2614_;
goto v___jp_2606_;
}
case 3:
{
lean_object* v_a_2615_; lean_object* v_a_2616_; 
v_a_2615_ = lean_ctor_get(v_u_2604_, 0);
lean_inc(v_a_2615_);
v_a_2616_ = lean_ctor_get(v_u_2604_, 1);
lean_inc(v_a_2616_);
lean_dec_ref(v_u_2604_);
v_u_2607_ = v_a_2615_;
v_v_2608_ = v_a_2616_;
goto v___jp_2606_;
}
case 5:
{
lean_object* v_a_2617_; uint8_t v___x_2618_; 
v_a_2617_ = lean_ctor_get(v_u_2604_, 0);
lean_inc(v_a_2617_);
lean_dec_ref(v_u_2604_);
v___x_2618_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Level_collectMVars_spec__0___redArg(v_a_2617_, v_s_2605_);
if (v___x_2618_ == 0)
{
lean_object* v___x_2619_; lean_object* v___x_2620_; 
v___x_2619_ = lean_box(0);
v___x_2620_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Level_collectMVars_spec__1___redArg(v_a_2617_, v___x_2619_, v_s_2605_);
return v___x_2620_;
}
else
{
lean_dec(v_a_2617_);
return v_s_2605_;
}
}
default: 
{
lean_dec(v_u_2604_);
return v_s_2605_;
}
}
v___jp_2606_:
{
lean_object* v___x_2609_; 
v___x_2609_ = l_Lean_Level_collectMVars(v_v_2608_, v_s_2605_);
v_u_2604_ = v_u_2607_;
v_s_2605_ = v___x_2609_;
goto _start;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Level_collectMVars_spec__0(lean_object* v_00_u03b2_2621_, lean_object* v_k_2622_, lean_object* v_t_2623_){
_start:
{
uint8_t v___x_2624_; 
v___x_2624_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Level_collectMVars_spec__0___redArg(v_k_2622_, v_t_2623_);
return v___x_2624_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Level_collectMVars_spec__0___boxed(lean_object* v_00_u03b2_2625_, lean_object* v_k_2626_, lean_object* v_t_2627_){
_start:
{
uint8_t v_res_2628_; lean_object* v_r_2629_; 
v_res_2628_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Level_collectMVars_spec__0(v_00_u03b2_2625_, v_k_2626_, v_t_2627_);
lean_dec(v_t_2627_);
lean_dec(v_k_2626_);
v_r_2629_ = lean_box(v_res_2628_);
return v_r_2629_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Level_collectMVars_spec__1(lean_object* v_00_u03b2_2630_, lean_object* v_k_2631_, lean_object* v_v_2632_, lean_object* v_t_2633_, lean_object* v_hl_2634_){
_start:
{
lean_object* v___x_2635_; 
v___x_2635_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Level_collectMVars_spec__1___redArg(v_k_2631_, v_v_2632_, v_t_2633_);
return v___x_2635_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_find_x3f_visit(lean_object* v_p_2636_, lean_object* v_u_2637_){
_start:
{
lean_object* v_u_2639_; lean_object* v_v_2640_; lean_object* v___x_2643_; uint8_t v___x_2644_; 
lean_inc_ref(v_p_2636_);
lean_inc(v_u_2637_);
v___x_2643_ = lean_apply_1(v_p_2636_, v_u_2637_);
v___x_2644_ = lean_unbox(v___x_2643_);
if (v___x_2644_ == 0)
{
switch(lean_obj_tag(v_u_2637_))
{
case 1:
{
lean_object* v_a_2645_; 
v_a_2645_ = lean_ctor_get(v_u_2637_, 0);
lean_inc(v_a_2645_);
lean_dec_ref(v_u_2637_);
v_u_2637_ = v_a_2645_;
goto _start;
}
case 2:
{
lean_object* v_a_2647_; lean_object* v_a_2648_; 
v_a_2647_ = lean_ctor_get(v_u_2637_, 0);
lean_inc(v_a_2647_);
v_a_2648_ = lean_ctor_get(v_u_2637_, 1);
lean_inc(v_a_2648_);
lean_dec_ref(v_u_2637_);
v_u_2639_ = v_a_2647_;
v_v_2640_ = v_a_2648_;
goto v___jp_2638_;
}
case 3:
{
lean_object* v_a_2649_; lean_object* v_a_2650_; 
v_a_2649_ = lean_ctor_get(v_u_2637_, 0);
lean_inc(v_a_2649_);
v_a_2650_ = lean_ctor_get(v_u_2637_, 1);
lean_inc(v_a_2650_);
lean_dec_ref(v_u_2637_);
v_u_2639_ = v_a_2649_;
v_v_2640_ = v_a_2650_;
goto v___jp_2638_;
}
default: 
{
lean_object* v___x_2651_; 
lean_dec(v_u_2637_);
lean_dec_ref(v_p_2636_);
v___x_2651_ = lean_box(0);
return v___x_2651_;
}
}
}
else
{
lean_object* v___x_2652_; 
lean_dec_ref(v_p_2636_);
v___x_2652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2652_, 0, v_u_2637_);
return v___x_2652_;
}
v___jp_2638_:
{
lean_object* v___x_2641_; 
lean_inc_ref(v_p_2636_);
v___x_2641_ = l___private_Lean_Level_0__Lean_Level_find_x3f_visit(v_p_2636_, v_u_2639_);
if (lean_obj_tag(v___x_2641_) == 0)
{
v_u_2637_ = v_v_2640_;
goto _start;
}
else
{
lean_dec(v_v_2640_);
lean_dec_ref(v_p_2636_);
return v___x_2641_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_find_x3f(lean_object* v_u_2653_, lean_object* v_p_2654_){
_start:
{
lean_object* v___x_2655_; 
v___x_2655_ = l___private_Lean_Level_0__Lean_Level_find_x3f_visit(v_p_2654_, v_u_2653_);
return v___x_2655_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_any(lean_object* v_u_2656_, lean_object* v_p_2657_){
_start:
{
lean_object* v___x_2658_; 
v___x_2658_ = l___private_Lean_Level_0__Lean_Level_find_x3f_visit(v_p_2657_, v_u_2656_);
if (lean_obj_tag(v___x_2658_) == 0)
{
uint8_t v___x_2659_; 
v___x_2659_ = 0;
return v___x_2659_;
}
else
{
uint8_t v___x_2660_; 
lean_dec_ref(v___x_2658_);
v___x_2660_ = 1;
return v___x_2660_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_any___boxed(lean_object* v_u_2661_, lean_object* v_p_2662_){
_start:
{
uint8_t v_res_2663_; lean_object* v_r_2664_; 
v_res_2663_ = l_Lean_Level_any(v_u_2661_, v_p_2662_);
v_r_2664_ = lean_box(v_res_2663_);
return v_r_2664_;
}
}
LEAN_EXPORT lean_object* l_Nat_toLevel(lean_object* v_n_2665_){
_start:
{
lean_object* v___x_2666_; 
v___x_2666_ = l_Lean_Level_ofNat(v_n_2665_);
return v___x_2666_;
}
}
LEAN_EXPORT lean_object* l_Nat_toLevel___boxed(lean_object* v_n_2667_){
_start:
{
lean_object* v_res_2668_; 
v_res_2668_ = l_Nat_toLevel(v_n_2667_);
lean_dec(v_n_2667_);
return v_res_2668_;
}
}
lean_object* runtime_initialize_Init_Data_Array_QSort(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_PersistentHashSet(uint8_t builtin);
lean_object* runtime_initialize_Lean_Hygiene(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Option_Coe(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Linear(uint8_t builtin);
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
res = runtime_initialize_Init_Data_Nat_Linear(builtin);
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
lean_object* initialize_Init_Data_Nat_Linear(uint8_t builtin);
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
res = initialize_Init_Data_Nat_Linear(builtin);
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
