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
lean_object* lean_obj_tag_nat(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Level_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Level_ctorIdx___impl(lean_object* v_x_291_){
_start:
{
lean_object* v___x_292_; 
v___x_292_ = lean_obj_tag_nat(v_x_291_);
return v___x_292_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_ctorIdx___impl___boxed(lean_object* v_x_293_){
_start:
{
lean_object* v_res_294_; 
v_res_294_ = l_Lean_Level_ctorIdx___impl(v_x_293_);
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
lean_dec_ref_known(v_t_295_, 2);
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
lean_dec_ref_known(v_t_295_, 2);
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
lean_dec_ref_known(v_t_365_, 1);
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
lean_dec_ref_known(v_t_365_, 2);
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
lean_dec_ref_known(v_t_365_, 2);
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
lean_dec_ref_known(v_t_365_, 1);
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
lean_dec_ref_known(v_t_365_, 1);
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
lean_dec_ref_known(v_t_393_, 1);
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
lean_dec_ref_known(v_t_393_, 2);
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
lean_dec_ref_known(v_t_393_, 2);
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
lean_dec_ref_known(v_t_393_, 1);
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
lean_dec_ref_known(v_t_393_, 1);
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
uint64_t v___x_449_; uint64_t v___x_450_; uint64_t v___x_451_; uint64_t v___x_452_; uint64_t v___x_453_; uint64_t v___x_454_; uint64_t v___x_455_; lean_object* v___y_457_; uint8_t v___y_458_; uint8_t v___y_459_; lean_object* v___y_463_; uint8_t v___y_464_; lean_object* v___y_468_; uint32_t v___x_473_; lean_object* v___x_474_; uint32_t v___x_475_; lean_object* v___x_476_; uint8_t v___x_477_; 
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
v___x_460_ = lean_level_mk_data(v___x_455_, v___y_457_, v___y_458_, v___y_459_);
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
v___y_457_ = v___y_463_;
v___y_458_ = v___y_464_;
v___y_459_ = v___x_466_;
goto v___jp_456_;
}
else
{
v___y_457_ = v___y_463_;
v___y_458_ = v___y_464_;
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
uint64_t v___x_480_; uint64_t v___x_481_; uint64_t v___x_482_; uint64_t v___x_483_; uint64_t v___x_484_; uint64_t v___x_485_; uint64_t v___x_486_; lean_object* v___y_488_; uint8_t v___y_489_; uint8_t v___y_490_; lean_object* v___y_494_; uint8_t v___y_495_; lean_object* v___y_499_; uint32_t v___x_504_; lean_object* v___x_505_; uint32_t v___x_506_; lean_object* v___x_507_; uint8_t v___x_508_; 
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
v___x_491_ = lean_level_mk_data(v___x_486_, v___y_488_, v___y_489_, v___y_490_);
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
v___y_488_ = v___y_494_;
v___y_489_ = v___y_495_;
v___y_490_ = v___x_497_;
goto v___jp_487_;
}
else
{
v___y_488_ = v___y_494_;
v___y_489_ = v___y_495_;
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
v___x_519_ = 1723ULL;
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
lean_dec_ref_known(v_x_569_, 1);
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
lean_dec_ref_known(v_x_569_, 2);
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
lean_dec_ref_known(v_x_569_, 2);
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
lean_dec_ref_known(v_x_569_, 1);
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
lean_dec_ref_known(v_x_569_, 1);
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
LEAN_EXPORT lean_object* l_Lean_mkLevelZeroEx___redArg(){
_start:
{
lean_object* v___x_735_; 
v___x_735_ = lean_box(0);
return v___x_735_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLevelZeroEx___redArg___boxed(lean_object* v___dummy_736_){
_start:
{
lean_object* v_res_737_; 
v_res_737_ = l_Lean_mkLevelZeroEx___redArg();
return v_res_737_;
}
}
LEAN_EXPORT lean_object* lean_level_mk_zero(lean_object* v_x_738_){
_start:
{
lean_object* v___x_739_; 
v___x_739_ = lean_box(0);
return v___x_739_;
}
}
LEAN_EXPORT lean_object* lean_level_mk_succ(lean_object* v_u_740_){
_start:
{
lean_object* v___x_741_; 
v___x_741_ = l_Lean_Level_succ___override(v_u_740_);
return v___x_741_;
}
}
LEAN_EXPORT lean_object* lean_level_mk_param(lean_object* v_name_742_){
_start:
{
lean_object* v___x_743_; 
v___x_743_ = l_Lean_Level_param___override(v_name_742_);
return v___x_743_;
}
}
LEAN_EXPORT lean_object* lean_level_mk_max(lean_object* v_u_744_, lean_object* v_v_745_){
_start:
{
lean_object* v___x_746_; 
v___x_746_ = l_Lean_Level_max___override(v_u_744_, v_v_745_);
return v___x_746_;
}
}
LEAN_EXPORT lean_object* lean_level_mk_imax(lean_object* v_u_747_, lean_object* v_v_748_){
_start:
{
lean_object* v___x_749_; 
v___x_749_ = l_Lean_Level_imax___override(v_u_747_, v_v_748_);
return v___x_749_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_isZero(lean_object* v_x_750_){
_start:
{
if (lean_obj_tag(v_x_750_) == 0)
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
LEAN_EXPORT lean_object* l_Lean_Level_isZero___boxed(lean_object* v_x_753_){
_start:
{
uint8_t v_res_754_; lean_object* v_r_755_; 
v_res_754_ = l_Lean_Level_isZero(v_x_753_);
lean_dec(v_x_753_);
v_r_755_ = lean_box(v_res_754_);
return v_r_755_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_isSucc(lean_object* v_x_756_){
_start:
{
if (lean_obj_tag(v_x_756_) == 1)
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
LEAN_EXPORT lean_object* l_Lean_Level_isSucc___boxed(lean_object* v_x_759_){
_start:
{
uint8_t v_res_760_; lean_object* v_r_761_; 
v_res_760_ = l_Lean_Level_isSucc(v_x_759_);
lean_dec(v_x_759_);
v_r_761_ = lean_box(v_res_760_);
return v_r_761_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_isMax(lean_object* v_x_762_){
_start:
{
if (lean_obj_tag(v_x_762_) == 2)
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
LEAN_EXPORT lean_object* l_Lean_Level_isMax___boxed(lean_object* v_x_765_){
_start:
{
uint8_t v_res_766_; lean_object* v_r_767_; 
v_res_766_ = l_Lean_Level_isMax(v_x_765_);
lean_dec(v_x_765_);
v_r_767_ = lean_box(v_res_766_);
return v_r_767_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_isIMax(lean_object* v_x_768_){
_start:
{
if (lean_obj_tag(v_x_768_) == 3)
{
uint8_t v___x_769_; 
v___x_769_ = 1;
return v___x_769_;
}
else
{
uint8_t v___x_770_; 
v___x_770_ = 0;
return v___x_770_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_isIMax___boxed(lean_object* v_x_771_){
_start:
{
uint8_t v_res_772_; lean_object* v_r_773_; 
v_res_772_ = l_Lean_Level_isIMax(v_x_771_);
lean_dec(v_x_771_);
v_r_773_ = lean_box(v_res_772_);
return v_r_773_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_isMaxIMax(lean_object* v_x_774_){
_start:
{
switch(lean_obj_tag(v_x_774_))
{
case 2:
{
uint8_t v___x_775_; 
v___x_775_ = 1;
return v___x_775_;
}
case 3:
{
uint8_t v___x_776_; 
v___x_776_ = 1;
return v___x_776_;
}
default: 
{
uint8_t v___x_777_; 
v___x_777_ = 0;
return v___x_777_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_isMaxIMax___boxed(lean_object* v_x_778_){
_start:
{
uint8_t v_res_779_; lean_object* v_r_780_; 
v_res_779_ = l_Lean_Level_isMaxIMax(v_x_778_);
lean_dec(v_x_778_);
v_r_780_ = lean_box(v_res_779_);
return v_r_780_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_isParam(lean_object* v_x_781_){
_start:
{
if (lean_obj_tag(v_x_781_) == 4)
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
LEAN_EXPORT lean_object* l_Lean_Level_isParam___boxed(lean_object* v_x_784_){
_start:
{
uint8_t v_res_785_; lean_object* v_r_786_; 
v_res_785_ = l_Lean_Level_isParam(v_x_784_);
lean_dec(v_x_784_);
v_r_786_ = lean_box(v_res_785_);
return v_r_786_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_isMVar(lean_object* v_x_787_){
_start:
{
if (lean_obj_tag(v_x_787_) == 5)
{
uint8_t v___x_788_; 
v___x_788_ = 1;
return v___x_788_;
}
else
{
uint8_t v___x_789_; 
v___x_789_ = 0;
return v___x_789_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_isMVar___boxed(lean_object* v_x_790_){
_start:
{
uint8_t v_res_791_; lean_object* v_r_792_; 
v_res_791_ = l_Lean_Level_isMVar(v_x_790_);
lean_dec(v_x_790_);
v_r_792_ = lean_box(v_res_791_);
return v_r_792_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Level_mvarId_x21_spec__0(lean_object* v_msg_793_){
_start:
{
lean_object* v___x_794_; lean_object* v___x_795_; 
v___x_794_ = lean_box(0);
v___x_795_ = lean_panic_fn_borrowed(v___x_794_, v_msg_793_);
return v___x_795_;
}
}
static lean_object* _init_l_Lean_Level_mvarId_x21___closed__3(void){
_start:
{
lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; 
v___x_799_ = ((lean_object*)(l_Lean_Level_mvarId_x21___closed__2));
v___x_800_ = lean_unsigned_to_nat(19u);
v___x_801_ = lean_unsigned_to_nat(195u);
v___x_802_ = ((lean_object*)(l_Lean_Level_mvarId_x21___closed__1));
v___x_803_ = ((lean_object*)(l_Lean_Level_mvarId_x21___closed__0));
v___x_804_ = l_mkPanicMessageWithDecl(v___x_803_, v___x_802_, v___x_801_, v___x_800_, v___x_799_);
return v___x_804_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_mvarId_x21(lean_object* v_x_805_){
_start:
{
if (lean_obj_tag(v_x_805_) == 5)
{
lean_object* v_a_806_; 
v_a_806_ = lean_ctor_get(v_x_805_, 0);
lean_inc(v_a_806_);
return v_a_806_;
}
else
{
lean_object* v___x_807_; lean_object* v___x_808_; 
v___x_807_ = lean_obj_once(&l_Lean_Level_mvarId_x21___closed__3, &l_Lean_Level_mvarId_x21___closed__3_once, _init_l_Lean_Level_mvarId_x21___closed__3);
v___x_808_ = l_panic___at___00Lean_Level_mvarId_x21_spec__0(v___x_807_);
return v___x_808_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_mvarId_x21___boxed(lean_object* v_x_809_){
_start:
{
lean_object* v_res_810_; 
v_res_810_ = l_Lean_Level_mvarId_x21(v_x_809_);
lean_dec(v_x_809_);
return v_res_810_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_isNeverZero(lean_object* v_x_811_){
_start:
{
switch(lean_obj_tag(v_x_811_))
{
case 1:
{
uint8_t v___x_812_; 
v___x_812_ = 1;
return v___x_812_;
}
case 2:
{
lean_object* v_a_813_; lean_object* v_a_814_; uint8_t v___x_815_; 
v_a_813_ = lean_ctor_get(v_x_811_, 0);
v_a_814_ = lean_ctor_get(v_x_811_, 1);
v___x_815_ = l_Lean_Level_isNeverZero(v_a_813_);
if (v___x_815_ == 0)
{
v_x_811_ = v_a_814_;
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
v_a_817_ = lean_ctor_get(v_x_811_, 1);
v_x_811_ = v_a_817_;
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
lean_object* v_a_862_; uint8_t v___x_863_; 
v_a_862_ = lean_ctor_get(v_x_860_, 0);
v___x_863_ = l_Lean_Level_hasMVar(v_a_862_);
if (v___x_863_ == 0)
{
uint8_t v___x_864_; 
v___x_864_ = l_Lean_Level_hasParam(v_a_862_);
if (v___x_864_ == 0)
{
v_x_860_ = v_a_862_;
goto _start;
}
else
{
return v___x_863_;
}
}
else
{
uint8_t v___x_866_; 
v___x_866_ = 0;
return v___x_866_;
}
}
default: 
{
uint8_t v___x_867_; 
v___x_867_ = 0;
return v___x_867_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_isExplicit___boxed(lean_object* v_x_868_){
_start:
{
uint8_t v_res_869_; lean_object* v_r_870_; 
v_res_869_ = l_Lean_Level_isExplicit(v_x_868_);
lean_dec(v_x_868_);
v_r_870_ = lean_box(v_res_869_);
return v_r_870_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_getOffsetAux(lean_object* v_x_871_, lean_object* v_x_872_){
_start:
{
if (lean_obj_tag(v_x_871_) == 1)
{
lean_object* v_a_873_; lean_object* v___x_874_; lean_object* v___x_875_; 
v_a_873_ = lean_ctor_get(v_x_871_, 0);
v___x_874_ = lean_unsigned_to_nat(1u);
v___x_875_ = lean_nat_add(v_x_872_, v___x_874_);
lean_dec(v_x_872_);
v_x_871_ = v_a_873_;
v_x_872_ = v___x_875_;
goto _start;
}
else
{
return v_x_872_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_getOffsetAux___boxed(lean_object* v_x_877_, lean_object* v_x_878_){
_start:
{
lean_object* v_res_879_; 
v_res_879_ = l_Lean_Level_getOffsetAux(v_x_877_, v_x_878_);
lean_dec(v_x_877_);
return v_res_879_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_getOffset(lean_object* v_lvl_880_){
_start:
{
lean_object* v___x_881_; lean_object* v___x_882_; 
v___x_881_ = lean_unsigned_to_nat(0u);
v___x_882_ = l_Lean_Level_getOffsetAux(v_lvl_880_, v___x_881_);
return v___x_882_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_getOffset___boxed(lean_object* v_lvl_883_){
_start:
{
lean_object* v_res_884_; 
v_res_884_ = l_Lean_Level_getOffset(v_lvl_883_);
lean_dec(v_lvl_883_);
return v_res_884_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_getLevelOffset(lean_object* v_x_885_){
_start:
{
if (lean_obj_tag(v_x_885_) == 1)
{
lean_object* v_a_886_; 
v_a_886_ = lean_ctor_get(v_x_885_, 0);
v_x_885_ = v_a_886_;
goto _start;
}
else
{
lean_inc(v_x_885_);
return v_x_885_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_getLevelOffset___boxed(lean_object* v_x_888_){
_start:
{
lean_object* v_res_889_; 
v_res_889_ = l_Lean_Level_getLevelOffset(v_x_888_);
lean_dec(v_x_888_);
return v_res_889_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_toNat(lean_object* v_lvl_890_){
_start:
{
lean_object* v___x_891_; 
v___x_891_ = l_Lean_Level_getLevelOffset(v_lvl_890_);
if (lean_obj_tag(v___x_891_) == 0)
{
lean_object* v___x_892_; lean_object* v___x_893_; 
v___x_892_ = l_Lean_Level_getOffset(v_lvl_890_);
v___x_893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_893_, 0, v___x_892_);
return v___x_893_;
}
else
{
lean_object* v___x_894_; 
lean_dec(v___x_891_);
v___x_894_ = lean_box(0);
return v___x_894_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_toNat___boxed(lean_object* v_lvl_895_){
_start:
{
lean_object* v_res_896_; 
v_res_896_ = l_Lean_Level_toNat(v_lvl_895_);
lean_dec(v_lvl_895_);
return v_res_896_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_beq___boxed(lean_object* v_a_899_, lean_object* v_b_900_){
_start:
{
uint8_t v_res_901_; lean_object* v_r_902_; 
v_res_901_ = lean_level_eq(v_a_899_, v_b_900_);
lean_dec(v_b_900_);
lean_dec(v_a_899_);
v_r_902_ = lean_box(v_res_901_);
return v_r_902_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_occurs(lean_object* v_x_905_, lean_object* v_x_906_){
_start:
{
switch(lean_obj_tag(v_x_906_))
{
case 1:
{
lean_object* v_a_907_; uint8_t v___x_908_; 
v_a_907_ = lean_ctor_get(v_x_906_, 0);
v___x_908_ = lean_level_eq(v_x_905_, v_x_906_);
if (v___x_908_ == 0)
{
v_x_906_ = v_a_907_;
goto _start;
}
else
{
return v___x_908_;
}
}
case 2:
{
lean_object* v_a_910_; lean_object* v_a_911_; uint8_t v___y_913_; uint8_t v___x_915_; 
v_a_910_ = lean_ctor_get(v_x_906_, 0);
v_a_911_ = lean_ctor_get(v_x_906_, 1);
v___x_915_ = lean_level_eq(v_x_905_, v_x_906_);
if (v___x_915_ == 0)
{
uint8_t v___x_916_; 
v___x_916_ = l_Lean_Level_occurs(v_x_905_, v_a_910_);
v___y_913_ = v___x_916_;
goto v___jp_912_;
}
else
{
v___y_913_ = v___x_915_;
goto v___jp_912_;
}
v___jp_912_:
{
if (v___y_913_ == 0)
{
v_x_906_ = v_a_911_;
goto _start;
}
else
{
return v___y_913_;
}
}
}
case 3:
{
lean_object* v_a_917_; lean_object* v_a_918_; uint8_t v___y_920_; uint8_t v___x_922_; 
v_a_917_ = lean_ctor_get(v_x_906_, 0);
v_a_918_ = lean_ctor_get(v_x_906_, 1);
v___x_922_ = lean_level_eq(v_x_905_, v_x_906_);
if (v___x_922_ == 0)
{
uint8_t v___x_923_; 
v___x_923_ = l_Lean_Level_occurs(v_x_905_, v_a_917_);
v___y_920_ = v___x_923_;
goto v___jp_919_;
}
else
{
v___y_920_ = v___x_922_;
goto v___jp_919_;
}
v___jp_919_:
{
if (v___y_920_ == 0)
{
v_x_906_ = v_a_918_;
goto _start;
}
else
{
return v___y_920_;
}
}
}
default: 
{
uint8_t v___x_924_; 
v___x_924_ = lean_level_eq(v_x_905_, v_x_906_);
return v___x_924_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_occurs___boxed(lean_object* v_x_925_, lean_object* v_x_926_){
_start:
{
uint8_t v_res_927_; lean_object* v_r_928_; 
v_res_927_ = l_Lean_Level_occurs(v_x_925_, v_x_926_);
lean_dec(v_x_926_);
lean_dec(v_x_925_);
v_r_928_ = lean_box(v_res_927_);
return v_r_928_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_ctorToNat(lean_object* v_x_929_){
_start:
{
switch(lean_obj_tag(v_x_929_))
{
case 0:
{
lean_object* v___x_930_; 
v___x_930_ = lean_unsigned_to_nat(0u);
return v___x_930_;
}
case 1:
{
lean_object* v___x_931_; 
v___x_931_ = lean_unsigned_to_nat(3u);
return v___x_931_;
}
case 2:
{
lean_object* v___x_932_; 
v___x_932_ = lean_unsigned_to_nat(4u);
return v___x_932_;
}
case 3:
{
lean_object* v___x_933_; 
v___x_933_ = lean_unsigned_to_nat(5u);
return v___x_933_;
}
case 4:
{
lean_object* v___x_934_; 
v___x_934_ = lean_unsigned_to_nat(1u);
return v___x_934_;
}
default: 
{
lean_object* v___x_935_; 
v___x_935_ = lean_unsigned_to_nat(2u);
return v___x_935_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_ctorToNat___boxed(lean_object* v_x_936_){
_start:
{
lean_object* v_res_937_; 
v_res_937_ = l_Lean_Level_ctorToNat(v_x_936_);
lean_dec(v_x_936_);
return v_res_937_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_normLtAux(lean_object* v_x_938_, lean_object* v_x_939_, lean_object* v_x_940_, lean_object* v_x_941_){
_start:
{
lean_object* v_l_u2081_943_; lean_object* v_k_u2081_944_; lean_object* v_l_u2082_945_; lean_object* v_k_u2082_946_; lean_object* v_l_u2081_951_; lean_object* v_k_u2081_952_; lean_object* v_l_u2082_953_; lean_object* v_k_u2082_954_; 
switch(lean_obj_tag(v_x_938_))
{
case 1:
{
lean_object* v_a_960_; lean_object* v___x_961_; lean_object* v___x_962_; 
v_a_960_ = lean_ctor_get(v_x_938_, 0);
v___x_961_ = lean_unsigned_to_nat(1u);
v___x_962_ = lean_nat_add(v_x_939_, v___x_961_);
lean_dec(v_x_939_);
v_x_938_ = v_a_960_;
v_x_939_ = v___x_962_;
goto _start;
}
case 2:
{
switch(lean_obj_tag(v_x_940_))
{
case 1:
{
lean_object* v_a_964_; 
v_a_964_ = lean_ctor_get(v_x_940_, 0);
v_l_u2081_943_ = v_x_938_;
v_k_u2081_944_ = v_x_939_;
v_l_u2082_945_ = v_a_964_;
v_k_u2082_946_ = v_x_941_;
goto v___jp_942_;
}
case 2:
{
lean_object* v_a_965_; lean_object* v_a_966_; lean_object* v_a_967_; lean_object* v_a_968_; uint8_t v___x_972_; 
v_a_965_ = lean_ctor_get(v_x_938_, 0);
v_a_966_ = lean_ctor_get(v_x_938_, 1);
v_a_967_ = lean_ctor_get(v_x_940_, 0);
v_a_968_ = lean_ctor_get(v_x_940_, 1);
v___x_972_ = lean_level_eq(v_x_938_, v_x_940_);
if (v___x_972_ == 0)
{
uint8_t v___x_973_; 
lean_dec(v_x_941_);
lean_dec(v_x_939_);
v___x_973_ = lean_level_eq(v_a_965_, v_a_967_);
if (v___x_973_ == 0)
{
goto v___jp_969_;
}
else
{
if (v___x_972_ == 0)
{
lean_object* v___x_974_; 
v___x_974_ = lean_unsigned_to_nat(0u);
v_x_938_ = v_a_966_;
v_x_939_ = v___x_974_;
v_x_940_ = v_a_968_;
v_x_941_ = v___x_974_;
goto _start;
}
else
{
goto v___jp_969_;
}
}
}
else
{
uint8_t v___x_976_; 
v___x_976_ = lean_nat_dec_lt(v_x_939_, v_x_941_);
lean_dec(v_x_941_);
lean_dec(v_x_939_);
return v___x_976_;
}
v___jp_969_:
{
lean_object* v___x_970_; 
v___x_970_ = lean_unsigned_to_nat(0u);
v_x_938_ = v_a_965_;
v_x_939_ = v___x_970_;
v_x_940_ = v_a_967_;
v_x_941_ = v___x_970_;
goto _start;
}
}
default: 
{
v_l_u2081_951_ = v_x_938_;
v_k_u2081_952_ = v_x_939_;
v_l_u2082_953_ = v_x_940_;
v_k_u2082_954_ = v_x_941_;
goto v___jp_950_;
}
}
}
case 3:
{
switch(lean_obj_tag(v_x_940_))
{
case 1:
{
lean_object* v_a_977_; 
v_a_977_ = lean_ctor_get(v_x_940_, 0);
v_l_u2081_943_ = v_x_938_;
v_k_u2081_944_ = v_x_939_;
v_l_u2082_945_ = v_a_977_;
v_k_u2082_946_ = v_x_941_;
goto v___jp_942_;
}
case 3:
{
lean_object* v_a_978_; lean_object* v_a_979_; lean_object* v_a_980_; lean_object* v_a_981_; uint8_t v___x_985_; 
v_a_978_ = lean_ctor_get(v_x_938_, 0);
v_a_979_ = lean_ctor_get(v_x_938_, 1);
v_a_980_ = lean_ctor_get(v_x_940_, 0);
v_a_981_ = lean_ctor_get(v_x_940_, 1);
v___x_985_ = lean_level_eq(v_x_938_, v_x_940_);
if (v___x_985_ == 0)
{
uint8_t v___x_986_; 
lean_dec(v_x_941_);
lean_dec(v_x_939_);
v___x_986_ = lean_level_eq(v_a_978_, v_a_980_);
if (v___x_986_ == 0)
{
goto v___jp_982_;
}
else
{
if (v___x_985_ == 0)
{
lean_object* v___x_987_; 
v___x_987_ = lean_unsigned_to_nat(0u);
v_x_938_ = v_a_979_;
v_x_939_ = v___x_987_;
v_x_940_ = v_a_981_;
v_x_941_ = v___x_987_;
goto _start;
}
else
{
goto v___jp_982_;
}
}
}
else
{
uint8_t v___x_989_; 
v___x_989_ = lean_nat_dec_lt(v_x_939_, v_x_941_);
lean_dec(v_x_941_);
lean_dec(v_x_939_);
return v___x_989_;
}
v___jp_982_:
{
lean_object* v___x_983_; 
v___x_983_ = lean_unsigned_to_nat(0u);
v_x_938_ = v_a_978_;
v_x_939_ = v___x_983_;
v_x_940_ = v_a_980_;
v_x_941_ = v___x_983_;
goto _start;
}
}
default: 
{
v_l_u2081_951_ = v_x_938_;
v_k_u2081_952_ = v_x_939_;
v_l_u2082_953_ = v_x_940_;
v_k_u2082_954_ = v_x_941_;
goto v___jp_950_;
}
}
}
case 4:
{
switch(lean_obj_tag(v_x_940_))
{
case 1:
{
lean_object* v_a_990_; 
v_a_990_ = lean_ctor_get(v_x_940_, 0);
v_l_u2081_943_ = v_x_938_;
v_k_u2081_944_ = v_x_939_;
v_l_u2082_945_ = v_a_990_;
v_k_u2082_946_ = v_x_941_;
goto v___jp_942_;
}
case 4:
{
lean_object* v_a_991_; lean_object* v_a_992_; uint8_t v___x_993_; 
v_a_991_ = lean_ctor_get(v_x_938_, 0);
v_a_992_ = lean_ctor_get(v_x_940_, 0);
v___x_993_ = lean_name_eq(v_a_991_, v_a_992_);
if (v___x_993_ == 0)
{
uint8_t v___x_994_; 
lean_dec(v_x_941_);
lean_dec(v_x_939_);
v___x_994_ = l_Lean_Name_lt(v_a_991_, v_a_992_);
return v___x_994_;
}
else
{
uint8_t v___x_995_; 
v___x_995_ = lean_nat_dec_lt(v_x_939_, v_x_941_);
lean_dec(v_x_941_);
lean_dec(v_x_939_);
return v___x_995_;
}
}
default: 
{
v_l_u2081_951_ = v_x_938_;
v_k_u2081_952_ = v_x_939_;
v_l_u2082_953_ = v_x_940_;
v_k_u2082_954_ = v_x_941_;
goto v___jp_950_;
}
}
}
case 5:
{
switch(lean_obj_tag(v_x_940_))
{
case 1:
{
lean_object* v_a_996_; 
v_a_996_ = lean_ctor_get(v_x_940_, 0);
v_l_u2081_943_ = v_x_938_;
v_k_u2081_944_ = v_x_939_;
v_l_u2082_945_ = v_a_996_;
v_k_u2082_946_ = v_x_941_;
goto v___jp_942_;
}
case 5:
{
lean_object* v_a_997_; lean_object* v_a_998_; uint8_t v___x_999_; 
v_a_997_ = lean_ctor_get(v_x_938_, 0);
v_a_998_ = lean_ctor_get(v_x_940_, 0);
v___x_999_ = lean_name_eq(v_a_997_, v_a_998_);
if (v___x_999_ == 0)
{
uint8_t v___x_1000_; 
lean_dec(v_x_941_);
lean_dec(v_x_939_);
v___x_1000_ = l_Lean_Name_lt(v_a_997_, v_a_998_);
return v___x_1000_;
}
else
{
uint8_t v___x_1001_; 
v___x_1001_ = lean_nat_dec_lt(v_x_939_, v_x_941_);
lean_dec(v_x_941_);
lean_dec(v_x_939_);
return v___x_1001_;
}
}
default: 
{
v_l_u2081_951_ = v_x_938_;
v_k_u2081_952_ = v_x_939_;
v_l_u2082_953_ = v_x_940_;
v_k_u2082_954_ = v_x_941_;
goto v___jp_950_;
}
}
}
default: 
{
if (lean_obj_tag(v_x_940_) == 1)
{
lean_object* v_a_1002_; 
v_a_1002_ = lean_ctor_get(v_x_940_, 0);
v_l_u2081_943_ = v_x_938_;
v_k_u2081_944_ = v_x_939_;
v_l_u2082_945_ = v_a_1002_;
v_k_u2082_946_ = v_x_941_;
goto v___jp_942_;
}
else
{
v_l_u2081_951_ = v_x_938_;
v_k_u2081_952_ = v_x_939_;
v_l_u2082_953_ = v_x_940_;
v_k_u2082_954_ = v_x_941_;
goto v___jp_950_;
}
}
}
v___jp_942_:
{
lean_object* v___x_947_; lean_object* v___x_948_; 
v___x_947_ = lean_unsigned_to_nat(1u);
v___x_948_ = lean_nat_add(v_k_u2082_946_, v___x_947_);
lean_dec(v_k_u2082_946_);
v_x_938_ = v_l_u2081_943_;
v_x_939_ = v_k_u2081_944_;
v_x_940_ = v_l_u2082_945_;
v_x_941_ = v___x_948_;
goto _start;
}
v___jp_950_:
{
uint8_t v___x_955_; 
v___x_955_ = lean_level_eq(v_l_u2081_951_, v_l_u2082_953_);
if (v___x_955_ == 0)
{
lean_object* v___x_956_; lean_object* v___x_957_; uint8_t v___x_958_; 
lean_dec(v_k_u2082_954_);
lean_dec(v_k_u2081_952_);
v___x_956_ = l_Lean_Level_ctorToNat(v_l_u2081_951_);
v___x_957_ = l_Lean_Level_ctorToNat(v_l_u2082_953_);
v___x_958_ = lean_nat_dec_lt(v___x_956_, v___x_957_);
lean_dec(v___x_957_);
lean_dec(v___x_956_);
return v___x_958_;
}
else
{
uint8_t v___x_959_; 
v___x_959_ = lean_nat_dec_lt(v_k_u2081_952_, v_k_u2082_954_);
lean_dec(v_k_u2082_954_);
lean_dec(v_k_u2081_952_);
return v___x_959_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_normLtAux___boxed(lean_object* v_x_1003_, lean_object* v_x_1004_, lean_object* v_x_1005_, lean_object* v_x_1006_){
_start:
{
uint8_t v_res_1007_; lean_object* v_r_1008_; 
v_res_1007_ = l_Lean_Level_normLtAux(v_x_1003_, v_x_1004_, v_x_1005_, v_x_1006_);
lean_dec(v_x_1005_);
lean_dec(v_x_1003_);
v_r_1008_ = lean_box(v_res_1007_);
return v_r_1008_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_normLtAux_match__1_splitter___redArg(lean_object* v_x_1009_, lean_object* v_x_1010_, lean_object* v_x_1011_, lean_object* v_x_1012_, lean_object* v_h__1_1013_, lean_object* v_h__2_1014_, lean_object* v_h__3_1015_, lean_object* v_h__4_1016_, lean_object* v_h__5_1017_, lean_object* v_h__6_1018_, lean_object* v_h__7_1019_){
_start:
{
switch(lean_obj_tag(v_x_1009_))
{
case 1:
{
lean_object* v_a_1020_; lean_object* v___x_1021_; 
lean_dec(v_h__7_1019_);
lean_dec(v_h__6_1018_);
lean_dec(v_h__5_1017_);
lean_dec(v_h__4_1016_);
lean_dec(v_h__3_1015_);
lean_dec(v_h__2_1014_);
v_a_1020_ = lean_ctor_get(v_x_1009_, 0);
lean_inc(v_a_1020_);
lean_dec_ref_known(v_x_1009_, 1);
v___x_1021_ = lean_apply_4(v_h__1_1013_, v_a_1020_, v_x_1010_, v_x_1011_, v_x_1012_);
return v___x_1021_;
}
case 2:
{
lean_dec(v_h__6_1018_);
lean_dec(v_h__5_1017_);
lean_dec(v_h__4_1016_);
lean_dec(v_h__1_1013_);
switch(lean_obj_tag(v_x_1011_))
{
case 1:
{
lean_object* v_a_1022_; lean_object* v___x_1023_; 
lean_dec(v_h__7_1019_);
lean_dec(v_h__3_1015_);
v_a_1022_ = lean_ctor_get(v_x_1011_, 0);
lean_inc(v_a_1022_);
lean_dec_ref_known(v_x_1011_, 1);
v___x_1023_ = lean_apply_5(v_h__2_1014_, v_x_1009_, v_x_1010_, v_a_1022_, v_x_1012_, lean_box(0));
return v___x_1023_;
}
case 2:
{
lean_object* v_a_1024_; lean_object* v_a_1025_; lean_object* v_a_1026_; lean_object* v_a_1027_; lean_object* v___x_1028_; 
lean_dec(v_h__7_1019_);
lean_dec(v_h__2_1014_);
v_a_1024_ = lean_ctor_get(v_x_1009_, 0);
lean_inc(v_a_1024_);
v_a_1025_ = lean_ctor_get(v_x_1009_, 1);
lean_inc(v_a_1025_);
lean_dec_ref_known(v_x_1009_, 2);
v_a_1026_ = lean_ctor_get(v_x_1011_, 0);
lean_inc(v_a_1026_);
v_a_1027_ = lean_ctor_get(v_x_1011_, 1);
lean_inc(v_a_1027_);
lean_dec_ref_known(v_x_1011_, 2);
v___x_1028_ = lean_apply_6(v_h__3_1015_, v_a_1024_, v_a_1025_, v_x_1010_, v_a_1026_, v_a_1027_, v_x_1012_);
return v___x_1028_;
}
default: 
{
lean_object* v___x_1029_; 
lean_dec(v_h__3_1015_);
lean_dec(v_h__2_1014_);
v___x_1029_ = lean_apply_10(v_h__7_1019_, v_x_1009_, v_x_1010_, v_x_1011_, v_x_1012_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_1029_;
}
}
}
case 3:
{
lean_dec(v_h__6_1018_);
lean_dec(v_h__5_1017_);
lean_dec(v_h__3_1015_);
lean_dec(v_h__1_1013_);
switch(lean_obj_tag(v_x_1011_))
{
case 1:
{
lean_object* v_a_1030_; lean_object* v___x_1031_; 
lean_dec(v_h__7_1019_);
lean_dec(v_h__4_1016_);
v_a_1030_ = lean_ctor_get(v_x_1011_, 0);
lean_inc(v_a_1030_);
lean_dec_ref_known(v_x_1011_, 1);
v___x_1031_ = lean_apply_5(v_h__2_1014_, v_x_1009_, v_x_1010_, v_a_1030_, v_x_1012_, lean_box(0));
return v___x_1031_;
}
case 3:
{
lean_object* v_a_1032_; lean_object* v_a_1033_; lean_object* v_a_1034_; lean_object* v_a_1035_; lean_object* v___x_1036_; 
lean_dec(v_h__7_1019_);
lean_dec(v_h__2_1014_);
v_a_1032_ = lean_ctor_get(v_x_1009_, 0);
lean_inc(v_a_1032_);
v_a_1033_ = lean_ctor_get(v_x_1009_, 1);
lean_inc(v_a_1033_);
lean_dec_ref_known(v_x_1009_, 2);
v_a_1034_ = lean_ctor_get(v_x_1011_, 0);
lean_inc(v_a_1034_);
v_a_1035_ = lean_ctor_get(v_x_1011_, 1);
lean_inc(v_a_1035_);
lean_dec_ref_known(v_x_1011_, 2);
v___x_1036_ = lean_apply_6(v_h__4_1016_, v_a_1032_, v_a_1033_, v_x_1010_, v_a_1034_, v_a_1035_, v_x_1012_);
return v___x_1036_;
}
default: 
{
lean_object* v___x_1037_; 
lean_dec(v_h__4_1016_);
lean_dec(v_h__2_1014_);
v___x_1037_ = lean_apply_10(v_h__7_1019_, v_x_1009_, v_x_1010_, v_x_1011_, v_x_1012_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_1037_;
}
}
}
case 4:
{
lean_dec(v_h__6_1018_);
lean_dec(v_h__4_1016_);
lean_dec(v_h__3_1015_);
lean_dec(v_h__1_1013_);
switch(lean_obj_tag(v_x_1011_))
{
case 1:
{
lean_object* v_a_1038_; lean_object* v___x_1039_; 
lean_dec(v_h__7_1019_);
lean_dec(v_h__5_1017_);
v_a_1038_ = lean_ctor_get(v_x_1011_, 0);
lean_inc(v_a_1038_);
lean_dec_ref_known(v_x_1011_, 1);
v___x_1039_ = lean_apply_5(v_h__2_1014_, v_x_1009_, v_x_1010_, v_a_1038_, v_x_1012_, lean_box(0));
return v___x_1039_;
}
case 4:
{
lean_object* v_a_1040_; lean_object* v_a_1041_; lean_object* v___x_1042_; 
lean_dec(v_h__7_1019_);
lean_dec(v_h__2_1014_);
v_a_1040_ = lean_ctor_get(v_x_1009_, 0);
lean_inc(v_a_1040_);
lean_dec_ref_known(v_x_1009_, 1);
v_a_1041_ = lean_ctor_get(v_x_1011_, 0);
lean_inc(v_a_1041_);
lean_dec_ref_known(v_x_1011_, 1);
v___x_1042_ = lean_apply_4(v_h__5_1017_, v_a_1040_, v_x_1010_, v_a_1041_, v_x_1012_);
return v___x_1042_;
}
default: 
{
lean_object* v___x_1043_; 
lean_dec(v_h__5_1017_);
lean_dec(v_h__2_1014_);
v___x_1043_ = lean_apply_10(v_h__7_1019_, v_x_1009_, v_x_1010_, v_x_1011_, v_x_1012_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_1043_;
}
}
}
case 5:
{
lean_dec(v_h__5_1017_);
lean_dec(v_h__4_1016_);
lean_dec(v_h__3_1015_);
lean_dec(v_h__1_1013_);
switch(lean_obj_tag(v_x_1011_))
{
case 1:
{
lean_object* v_a_1044_; lean_object* v___x_1045_; 
lean_dec(v_h__7_1019_);
lean_dec(v_h__6_1018_);
v_a_1044_ = lean_ctor_get(v_x_1011_, 0);
lean_inc(v_a_1044_);
lean_dec_ref_known(v_x_1011_, 1);
v___x_1045_ = lean_apply_5(v_h__2_1014_, v_x_1009_, v_x_1010_, v_a_1044_, v_x_1012_, lean_box(0));
return v___x_1045_;
}
case 5:
{
lean_object* v_a_1046_; lean_object* v_a_1047_; lean_object* v___x_1048_; 
lean_dec(v_h__7_1019_);
lean_dec(v_h__2_1014_);
v_a_1046_ = lean_ctor_get(v_x_1009_, 0);
lean_inc(v_a_1046_);
lean_dec_ref_known(v_x_1009_, 1);
v_a_1047_ = lean_ctor_get(v_x_1011_, 0);
lean_inc(v_a_1047_);
lean_dec_ref_known(v_x_1011_, 1);
v___x_1048_ = lean_apply_4(v_h__6_1018_, v_a_1046_, v_x_1010_, v_a_1047_, v_x_1012_);
return v___x_1048_;
}
default: 
{
lean_object* v___x_1049_; 
lean_dec(v_h__6_1018_);
lean_dec(v_h__2_1014_);
v___x_1049_ = lean_apply_10(v_h__7_1019_, v_x_1009_, v_x_1010_, v_x_1011_, v_x_1012_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_1049_;
}
}
}
default: 
{
lean_dec(v_h__6_1018_);
lean_dec(v_h__5_1017_);
lean_dec(v_h__4_1016_);
lean_dec(v_h__3_1015_);
lean_dec(v_h__1_1013_);
if (lean_obj_tag(v_x_1011_) == 1)
{
lean_object* v_a_1050_; lean_object* v___x_1051_; 
lean_dec(v_h__7_1019_);
v_a_1050_ = lean_ctor_get(v_x_1011_, 0);
lean_inc(v_a_1050_);
lean_dec_ref_known(v_x_1011_, 1);
v___x_1051_ = lean_apply_5(v_h__2_1014_, v_x_1009_, v_x_1010_, v_a_1050_, v_x_1012_, lean_box(0));
return v___x_1051_;
}
else
{
lean_object* v___x_1052_; 
lean_dec(v_h__2_1014_);
v___x_1052_ = lean_apply_10(v_h__7_1019_, v_x_1009_, v_x_1010_, v_x_1011_, v_x_1012_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_1052_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_normLtAux_match__1_splitter(lean_object* v_motive_1053_, lean_object* v_x_1054_, lean_object* v_x_1055_, lean_object* v_x_1056_, lean_object* v_x_1057_, lean_object* v_h__1_1058_, lean_object* v_h__2_1059_, lean_object* v_h__3_1060_, lean_object* v_h__4_1061_, lean_object* v_h__5_1062_, lean_object* v_h__6_1063_, lean_object* v_h__7_1064_){
_start:
{
switch(lean_obj_tag(v_x_1054_))
{
case 1:
{
lean_object* v_a_1065_; lean_object* v___x_1066_; 
lean_dec(v_h__7_1064_);
lean_dec(v_h__6_1063_);
lean_dec(v_h__5_1062_);
lean_dec(v_h__4_1061_);
lean_dec(v_h__3_1060_);
lean_dec(v_h__2_1059_);
v_a_1065_ = lean_ctor_get(v_x_1054_, 0);
lean_inc(v_a_1065_);
lean_dec_ref_known(v_x_1054_, 1);
v___x_1066_ = lean_apply_4(v_h__1_1058_, v_a_1065_, v_x_1055_, v_x_1056_, v_x_1057_);
return v___x_1066_;
}
case 2:
{
lean_dec(v_h__6_1063_);
lean_dec(v_h__5_1062_);
lean_dec(v_h__4_1061_);
lean_dec(v_h__1_1058_);
switch(lean_obj_tag(v_x_1056_))
{
case 1:
{
lean_object* v_a_1067_; lean_object* v___x_1068_; 
lean_dec(v_h__7_1064_);
lean_dec(v_h__3_1060_);
v_a_1067_ = lean_ctor_get(v_x_1056_, 0);
lean_inc(v_a_1067_);
lean_dec_ref_known(v_x_1056_, 1);
v___x_1068_ = lean_apply_5(v_h__2_1059_, v_x_1054_, v_x_1055_, v_a_1067_, v_x_1057_, lean_box(0));
return v___x_1068_;
}
case 2:
{
lean_object* v_a_1069_; lean_object* v_a_1070_; lean_object* v_a_1071_; lean_object* v_a_1072_; lean_object* v___x_1073_; 
lean_dec(v_h__7_1064_);
lean_dec(v_h__2_1059_);
v_a_1069_ = lean_ctor_get(v_x_1054_, 0);
lean_inc(v_a_1069_);
v_a_1070_ = lean_ctor_get(v_x_1054_, 1);
lean_inc(v_a_1070_);
lean_dec_ref_known(v_x_1054_, 2);
v_a_1071_ = lean_ctor_get(v_x_1056_, 0);
lean_inc(v_a_1071_);
v_a_1072_ = lean_ctor_get(v_x_1056_, 1);
lean_inc(v_a_1072_);
lean_dec_ref_known(v_x_1056_, 2);
v___x_1073_ = lean_apply_6(v_h__3_1060_, v_a_1069_, v_a_1070_, v_x_1055_, v_a_1071_, v_a_1072_, v_x_1057_);
return v___x_1073_;
}
default: 
{
lean_object* v___x_1074_; 
lean_dec(v_h__3_1060_);
lean_dec(v_h__2_1059_);
v___x_1074_ = lean_apply_10(v_h__7_1064_, v_x_1054_, v_x_1055_, v_x_1056_, v_x_1057_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_1074_;
}
}
}
case 3:
{
lean_dec(v_h__6_1063_);
lean_dec(v_h__5_1062_);
lean_dec(v_h__3_1060_);
lean_dec(v_h__1_1058_);
switch(lean_obj_tag(v_x_1056_))
{
case 1:
{
lean_object* v_a_1075_; lean_object* v___x_1076_; 
lean_dec(v_h__7_1064_);
lean_dec(v_h__4_1061_);
v_a_1075_ = lean_ctor_get(v_x_1056_, 0);
lean_inc(v_a_1075_);
lean_dec_ref_known(v_x_1056_, 1);
v___x_1076_ = lean_apply_5(v_h__2_1059_, v_x_1054_, v_x_1055_, v_a_1075_, v_x_1057_, lean_box(0));
return v___x_1076_;
}
case 3:
{
lean_object* v_a_1077_; lean_object* v_a_1078_; lean_object* v_a_1079_; lean_object* v_a_1080_; lean_object* v___x_1081_; 
lean_dec(v_h__7_1064_);
lean_dec(v_h__2_1059_);
v_a_1077_ = lean_ctor_get(v_x_1054_, 0);
lean_inc(v_a_1077_);
v_a_1078_ = lean_ctor_get(v_x_1054_, 1);
lean_inc(v_a_1078_);
lean_dec_ref_known(v_x_1054_, 2);
v_a_1079_ = lean_ctor_get(v_x_1056_, 0);
lean_inc(v_a_1079_);
v_a_1080_ = lean_ctor_get(v_x_1056_, 1);
lean_inc(v_a_1080_);
lean_dec_ref_known(v_x_1056_, 2);
v___x_1081_ = lean_apply_6(v_h__4_1061_, v_a_1077_, v_a_1078_, v_x_1055_, v_a_1079_, v_a_1080_, v_x_1057_);
return v___x_1081_;
}
default: 
{
lean_object* v___x_1082_; 
lean_dec(v_h__4_1061_);
lean_dec(v_h__2_1059_);
v___x_1082_ = lean_apply_10(v_h__7_1064_, v_x_1054_, v_x_1055_, v_x_1056_, v_x_1057_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_1082_;
}
}
}
case 4:
{
lean_dec(v_h__6_1063_);
lean_dec(v_h__4_1061_);
lean_dec(v_h__3_1060_);
lean_dec(v_h__1_1058_);
switch(lean_obj_tag(v_x_1056_))
{
case 1:
{
lean_object* v_a_1083_; lean_object* v___x_1084_; 
lean_dec(v_h__7_1064_);
lean_dec(v_h__5_1062_);
v_a_1083_ = lean_ctor_get(v_x_1056_, 0);
lean_inc(v_a_1083_);
lean_dec_ref_known(v_x_1056_, 1);
v___x_1084_ = lean_apply_5(v_h__2_1059_, v_x_1054_, v_x_1055_, v_a_1083_, v_x_1057_, lean_box(0));
return v___x_1084_;
}
case 4:
{
lean_object* v_a_1085_; lean_object* v_a_1086_; lean_object* v___x_1087_; 
lean_dec(v_h__7_1064_);
lean_dec(v_h__2_1059_);
v_a_1085_ = lean_ctor_get(v_x_1054_, 0);
lean_inc(v_a_1085_);
lean_dec_ref_known(v_x_1054_, 1);
v_a_1086_ = lean_ctor_get(v_x_1056_, 0);
lean_inc(v_a_1086_);
lean_dec_ref_known(v_x_1056_, 1);
v___x_1087_ = lean_apply_4(v_h__5_1062_, v_a_1085_, v_x_1055_, v_a_1086_, v_x_1057_);
return v___x_1087_;
}
default: 
{
lean_object* v___x_1088_; 
lean_dec(v_h__5_1062_);
lean_dec(v_h__2_1059_);
v___x_1088_ = lean_apply_10(v_h__7_1064_, v_x_1054_, v_x_1055_, v_x_1056_, v_x_1057_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_1088_;
}
}
}
case 5:
{
lean_dec(v_h__5_1062_);
lean_dec(v_h__4_1061_);
lean_dec(v_h__3_1060_);
lean_dec(v_h__1_1058_);
switch(lean_obj_tag(v_x_1056_))
{
case 1:
{
lean_object* v_a_1089_; lean_object* v___x_1090_; 
lean_dec(v_h__7_1064_);
lean_dec(v_h__6_1063_);
v_a_1089_ = lean_ctor_get(v_x_1056_, 0);
lean_inc(v_a_1089_);
lean_dec_ref_known(v_x_1056_, 1);
v___x_1090_ = lean_apply_5(v_h__2_1059_, v_x_1054_, v_x_1055_, v_a_1089_, v_x_1057_, lean_box(0));
return v___x_1090_;
}
case 5:
{
lean_object* v_a_1091_; lean_object* v_a_1092_; lean_object* v___x_1093_; 
lean_dec(v_h__7_1064_);
lean_dec(v_h__2_1059_);
v_a_1091_ = lean_ctor_get(v_x_1054_, 0);
lean_inc(v_a_1091_);
lean_dec_ref_known(v_x_1054_, 1);
v_a_1092_ = lean_ctor_get(v_x_1056_, 0);
lean_inc(v_a_1092_);
lean_dec_ref_known(v_x_1056_, 1);
v___x_1093_ = lean_apply_4(v_h__6_1063_, v_a_1091_, v_x_1055_, v_a_1092_, v_x_1057_);
return v___x_1093_;
}
default: 
{
lean_object* v___x_1094_; 
lean_dec(v_h__6_1063_);
lean_dec(v_h__2_1059_);
v___x_1094_ = lean_apply_10(v_h__7_1064_, v_x_1054_, v_x_1055_, v_x_1056_, v_x_1057_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_1094_;
}
}
}
default: 
{
lean_dec(v_h__6_1063_);
lean_dec(v_h__5_1062_);
lean_dec(v_h__4_1061_);
lean_dec(v_h__3_1060_);
lean_dec(v_h__1_1058_);
if (lean_obj_tag(v_x_1056_) == 1)
{
lean_object* v_a_1095_; lean_object* v___x_1096_; 
lean_dec(v_h__7_1064_);
v_a_1095_ = lean_ctor_get(v_x_1056_, 0);
lean_inc(v_a_1095_);
lean_dec_ref_known(v_x_1056_, 1);
v___x_1096_ = lean_apply_5(v_h__2_1059_, v_x_1054_, v_x_1055_, v_a_1095_, v_x_1057_, lean_box(0));
return v___x_1096_;
}
else
{
lean_object* v___x_1097_; 
lean_dec(v_h__2_1059_);
v___x_1097_ = lean_apply_10(v_h__7_1064_, v_x_1054_, v_x_1055_, v_x_1056_, v_x_1057_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_1097_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Level_normLt(lean_object* v_l_u2081_1098_, lean_object* v_l_u2082_1099_){
_start:
{
lean_object* v___x_1100_; uint8_t v___x_1101_; 
v___x_1100_ = lean_unsigned_to_nat(0u);
v___x_1101_ = l_Lean_Level_normLtAux(v_l_u2081_1098_, v___x_1100_, v_l_u2082_1099_, v___x_1100_);
return v___x_1101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_normLt___boxed(lean_object* v_l_u2081_1102_, lean_object* v_l_u2082_1103_){
_start:
{
uint8_t v_res_1104_; lean_object* v_r_1105_; 
v_res_1104_ = l_Lean_Level_normLt(v_l_u2081_1102_, v_l_u2082_1103_);
lean_dec(v_l_u2082_1103_);
lean_dec(v_l_u2081_1102_);
v_r_1105_ = lean_box(v_res_1104_);
return v_r_1105_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_isAlreadyNormalizedCheap(lean_object* v_x_1106_){
_start:
{
switch(lean_obj_tag(v_x_1106_))
{
case 0:
{
uint8_t v___x_1107_; 
v___x_1107_ = 1;
return v___x_1107_;
}
case 4:
{
uint8_t v___x_1108_; 
v___x_1108_ = 1;
return v___x_1108_;
}
case 5:
{
uint8_t v___x_1109_; 
v___x_1109_ = 1;
return v___x_1109_;
}
case 1:
{
lean_object* v_a_1110_; 
v_a_1110_ = lean_ctor_get(v_x_1106_, 0);
v_x_1106_ = v_a_1110_;
goto _start;
}
default: 
{
uint8_t v___x_1112_; 
v___x_1112_ = 0;
return v___x_1112_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_isAlreadyNormalizedCheap___boxed(lean_object* v_x_1113_){
_start:
{
uint8_t v_res_1114_; lean_object* v_r_1115_; 
v_res_1114_ = l_Lean_Level_isAlreadyNormalizedCheap(v_x_1113_);
lean_dec(v_x_1113_);
v_r_1115_ = lean_box(v_res_1114_);
return v_r_1115_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_mkIMaxAux(lean_object* v_x_1116_, lean_object* v_x_1117_){
_start:
{
lean_object* v_u_u2081_1119_; lean_object* v_u_u2082_1120_; 
if (lean_obj_tag(v_x_1117_) == 0)
{
lean_dec(v_x_1116_);
return v_x_1117_;
}
else
{
switch(lean_obj_tag(v_x_1116_))
{
case 0:
{
return v_x_1117_;
}
case 1:
{
lean_object* v_a_1123_; 
v_a_1123_ = lean_ctor_get(v_x_1116_, 0);
if (lean_obj_tag(v_a_1123_) == 0)
{
lean_dec_ref_known(v_x_1116_, 1);
return v_x_1117_;
}
else
{
v_u_u2081_1119_ = v_x_1116_;
v_u_u2082_1120_ = v_x_1117_;
goto v___jp_1118_;
}
}
default: 
{
v_u_u2081_1119_ = v_x_1116_;
v_u_u2082_1120_ = v_x_1117_;
goto v___jp_1118_;
}
}
}
v___jp_1118_:
{
uint8_t v___x_1121_; 
v___x_1121_ = lean_level_eq(v_u_u2081_1119_, v_u_u2082_1120_);
if (v___x_1121_ == 0)
{
lean_object* v___x_1122_; 
v___x_1122_ = l_Lean_Level_imax___override(v_u_u2081_1119_, v_u_u2082_1120_);
return v___x_1122_;
}
else
{
lean_dec(v_u_u2082_1120_);
return v_u_u2081_1119_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_getMaxArgsAux(lean_object* v_normalize_1124_, lean_object* v_x_1125_, uint8_t v_x_1126_, lean_object* v_x_1127_){
_start:
{
if (lean_obj_tag(v_x_1125_) == 2)
{
lean_object* v_a_1128_; lean_object* v_a_1129_; lean_object* v___x_1130_; 
v_a_1128_ = lean_ctor_get(v_x_1125_, 0);
lean_inc(v_a_1128_);
v_a_1129_ = lean_ctor_get(v_x_1125_, 1);
lean_inc(v_a_1129_);
lean_dec_ref_known(v_x_1125_, 2);
lean_inc_ref(v_normalize_1124_);
v___x_1130_ = l___private_Lean_Level_0__Lean_Level_getMaxArgsAux(v_normalize_1124_, v_a_1128_, v_x_1126_, v_x_1127_);
v_x_1125_ = v_a_1129_;
v_x_1127_ = v___x_1130_;
goto _start;
}
else
{
if (v_x_1126_ == 0)
{
lean_object* v___x_1132_; uint8_t v___x_1133_; 
lean_inc_ref(v_normalize_1124_);
v___x_1132_ = lean_apply_1(v_normalize_1124_, v_x_1125_);
v___x_1133_ = 1;
v_x_1125_ = v___x_1132_;
v_x_1126_ = v___x_1133_;
goto _start;
}
else
{
lean_object* v___x_1135_; 
lean_dec_ref(v_normalize_1124_);
v___x_1135_ = lean_array_push(v_x_1127_, v_x_1125_);
return v___x_1135_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_getMaxArgsAux___boxed(lean_object* v_normalize_1136_, lean_object* v_x_1137_, lean_object* v_x_1138_, lean_object* v_x_1139_){
_start:
{
uint8_t v_x_31__boxed_1140_; lean_object* v_res_1141_; 
v_x_31__boxed_1140_ = lean_unbox(v_x_1138_);
v_res_1141_ = l___private_Lean_Level_0__Lean_Level_getMaxArgsAux(v_normalize_1136_, v_x_1137_, v_x_31__boxed_1140_, v_x_1139_);
return v_res_1141_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_accMax(lean_object* v_result_1142_, lean_object* v_prev_1143_, lean_object* v_offset_1144_){
_start:
{
uint8_t v___x_1145_; 
v___x_1145_ = l_Lean_Level_isZero(v_result_1142_);
if (v___x_1145_ == 0)
{
lean_object* v___x_1146_; lean_object* v___x_1147_; 
v___x_1146_ = l_Lean_Level_addOffsetAux(v_offset_1144_, v_prev_1143_);
v___x_1147_ = l_Lean_Level_max___override(v_result_1142_, v___x_1146_);
return v___x_1147_;
}
else
{
lean_object* v___x_1148_; 
lean_dec(v_result_1142_);
v___x_1148_ = l_Lean_Level_addOffsetAux(v_offset_1144_, v_prev_1143_);
return v___x_1148_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_mkMaxAux(lean_object* v_lvls_1149_, lean_object* v_extraK_1150_, lean_object* v_i_1151_, lean_object* v_prev_1152_, lean_object* v_prevK_1153_, lean_object* v_result_1154_){
_start:
{
lean_object* v___x_1155_; uint8_t v___x_1156_; 
v___x_1155_ = lean_array_get_size(v_lvls_1149_);
v___x_1156_ = lean_nat_dec_lt(v_i_1151_, v___x_1155_);
if (v___x_1156_ == 0)
{
lean_object* v___x_1157_; lean_object* v___x_1158_; 
lean_dec(v_i_1151_);
v___x_1157_ = lean_nat_add(v_extraK_1150_, v_prevK_1153_);
lean_dec(v_prevK_1153_);
v___x_1158_ = l___private_Lean_Level_0__Lean_Level_accMax(v_result_1154_, v_prev_1152_, v___x_1157_);
return v___x_1158_;
}
else
{
lean_object* v_lvl_1159_; lean_object* v_curr_1160_; lean_object* v_currK_1161_; uint8_t v___x_1162_; 
v_lvl_1159_ = lean_array_fget_borrowed(v_lvls_1149_, v_i_1151_);
v_curr_1160_ = l_Lean_Level_getLevelOffset(v_lvl_1159_);
v_currK_1161_ = l_Lean_Level_getOffset(v_lvl_1159_);
v___x_1162_ = lean_level_eq(v_curr_1160_, v_prev_1152_);
if (v___x_1162_ == 0)
{
lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; 
v___x_1163_ = lean_unsigned_to_nat(1u);
v___x_1164_ = lean_nat_add(v_i_1151_, v___x_1163_);
lean_dec(v_i_1151_);
v___x_1165_ = lean_nat_add(v_extraK_1150_, v_prevK_1153_);
lean_dec(v_prevK_1153_);
v___x_1166_ = l___private_Lean_Level_0__Lean_Level_accMax(v_result_1154_, v_prev_1152_, v___x_1165_);
v_i_1151_ = v___x_1164_;
v_prev_1152_ = v_curr_1160_;
v_prevK_1153_ = v_currK_1161_;
v_result_1154_ = v___x_1166_;
goto _start;
}
else
{
lean_object* v___x_1168_; lean_object* v___x_1169_; 
lean_dec(v_prevK_1153_);
lean_dec(v_prev_1152_);
v___x_1168_ = lean_unsigned_to_nat(1u);
v___x_1169_ = lean_nat_add(v_i_1151_, v___x_1168_);
lean_dec(v_i_1151_);
v_i_1151_ = v___x_1169_;
v_prev_1152_ = v_curr_1160_;
v_prevK_1153_ = v_currK_1161_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_mkMaxAux___boxed(lean_object* v_lvls_1171_, lean_object* v_extraK_1172_, lean_object* v_i_1173_, lean_object* v_prev_1174_, lean_object* v_prevK_1175_, lean_object* v_result_1176_){
_start:
{
lean_object* v_res_1177_; 
v_res_1177_ = l___private_Lean_Level_0__Lean_Level_mkMaxAux(v_lvls_1171_, v_extraK_1172_, v_i_1173_, v_prev_1174_, v_prevK_1175_, v_result_1176_);
lean_dec(v_extraK_1172_);
lean_dec_ref(v_lvls_1171_);
return v_res_1177_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_skipExplicit(lean_object* v_lvls_1178_, lean_object* v_i_1179_){
_start:
{
lean_object* v___x_1180_; uint8_t v___x_1181_; 
v___x_1180_ = lean_array_get_size(v_lvls_1178_);
v___x_1181_ = lean_nat_dec_lt(v_i_1179_, v___x_1180_);
if (v___x_1181_ == 0)
{
return v_i_1179_;
}
else
{
lean_object* v_lvl_1182_; lean_object* v___x_1183_; uint8_t v___x_1184_; 
v_lvl_1182_ = lean_array_fget_borrowed(v_lvls_1178_, v_i_1179_);
v___x_1183_ = l_Lean_Level_getLevelOffset(v_lvl_1182_);
v___x_1184_ = l_Lean_Level_isZero(v___x_1183_);
lean_dec(v___x_1183_);
if (v___x_1184_ == 0)
{
return v_i_1179_;
}
else
{
lean_object* v___x_1185_; lean_object* v___x_1186_; 
v___x_1185_ = lean_unsigned_to_nat(1u);
v___x_1186_ = lean_nat_add(v_i_1179_, v___x_1185_);
lean_dec(v_i_1179_);
v_i_1179_ = v___x_1186_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_skipExplicit___boxed(lean_object* v_lvls_1188_, lean_object* v_i_1189_){
_start:
{
lean_object* v_res_1190_; 
v_res_1190_ = l___private_Lean_Level_0__Lean_Level_skipExplicit(v_lvls_1188_, v_i_1189_);
lean_dec_ref(v_lvls_1188_);
return v_res_1190_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Level_0__Lean_Level_isExplicitSubsumedAux(lean_object* v_lvls_1191_, lean_object* v_maxExplicit_1192_, lean_object* v_i_1193_){
_start:
{
lean_object* v___x_1194_; uint8_t v___x_1195_; 
v___x_1194_ = lean_array_get_size(v_lvls_1191_);
v___x_1195_ = lean_nat_dec_lt(v_i_1193_, v___x_1194_);
if (v___x_1195_ == 0)
{
lean_dec(v_i_1193_);
return v___x_1195_;
}
else
{
lean_object* v_lvl_1196_; lean_object* v___x_1197_; uint8_t v___x_1198_; 
v_lvl_1196_ = lean_array_fget_borrowed(v_lvls_1191_, v_i_1193_);
v___x_1197_ = l_Lean_Level_getOffset(v_lvl_1196_);
v___x_1198_ = lean_nat_dec_le(v_maxExplicit_1192_, v___x_1197_);
lean_dec(v___x_1197_);
if (v___x_1198_ == 0)
{
lean_object* v___x_1199_; lean_object* v___x_1200_; 
v___x_1199_ = lean_unsigned_to_nat(1u);
v___x_1200_ = lean_nat_add(v_i_1193_, v___x_1199_);
lean_dec(v_i_1193_);
v_i_1193_ = v___x_1200_;
goto _start;
}
else
{
lean_dec(v_i_1193_);
return v___x_1198_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_isExplicitSubsumedAux___boxed(lean_object* v_lvls_1202_, lean_object* v_maxExplicit_1203_, lean_object* v_i_1204_){
_start:
{
uint8_t v_res_1205_; lean_object* v_r_1206_; 
v_res_1205_ = l___private_Lean_Level_0__Lean_Level_isExplicitSubsumedAux(v_lvls_1202_, v_maxExplicit_1203_, v_i_1204_);
lean_dec(v_maxExplicit_1203_);
lean_dec_ref(v_lvls_1202_);
v_r_1206_ = lean_box(v_res_1205_);
return v_r_1206_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Level_0__Lean_Level_isExplicitSubsumed(lean_object* v_lvls_1207_, lean_object* v_firstNonExplicit_1208_){
_start:
{
lean_object* v___x_1209_; uint8_t v___x_1210_; 
v___x_1209_ = lean_unsigned_to_nat(0u);
v___x_1210_ = lean_nat_dec_eq(v_firstNonExplicit_1208_, v___x_1209_);
if (v___x_1210_ == 0)
{
lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v_max_1215_; uint8_t v___x_1216_; 
v___x_1211_ = lean_box(0);
v___x_1212_ = lean_unsigned_to_nat(1u);
v___x_1213_ = lean_nat_sub(v_firstNonExplicit_1208_, v___x_1212_);
v___x_1214_ = lean_array_get_borrowed(v___x_1211_, v_lvls_1207_, v___x_1213_);
lean_dec(v___x_1213_);
v_max_1215_ = l_Lean_Level_getOffset(v___x_1214_);
v___x_1216_ = l___private_Lean_Level_0__Lean_Level_isExplicitSubsumedAux(v_lvls_1207_, v_max_1215_, v_firstNonExplicit_1208_);
lean_dec(v_max_1215_);
return v___x_1216_;
}
else
{
uint8_t v___x_1217_; 
lean_dec(v_firstNonExplicit_1208_);
v___x_1217_ = 0;
return v___x_1217_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_isExplicitSubsumed___boxed(lean_object* v_lvls_1218_, lean_object* v_firstNonExplicit_1219_){
_start:
{
uint8_t v_res_1220_; lean_object* v_r_1221_; 
v_res_1220_ = l___private_Lean_Level_0__Lean_Level_isExplicitSubsumed(v_lvls_1218_, v_firstNonExplicit_1219_);
lean_dec_ref(v_lvls_1218_);
v_r_1221_ = lean_box(v_res_1220_);
return v_r_1221_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Level_normalize_spec__2(lean_object* v_msg_1222_){
_start:
{
lean_object* v___x_1223_; lean_object* v___x_1224_; 
v___x_1223_ = lean_box(0);
v___x_1224_ = lean_panic_fn_borrowed(v___x_1223_, v_msg_1222_);
return v___x_1224_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1_spec__1___redArg(lean_object* v_hi_1225_, lean_object* v_pivot_1226_, lean_object* v_as_1227_, lean_object* v_i_1228_, lean_object* v_k_1229_){
_start:
{
uint8_t v___x_1230_; 
v___x_1230_ = lean_nat_dec_lt(v_k_1229_, v_hi_1225_);
if (v___x_1230_ == 0)
{
lean_object* v___x_1231_; lean_object* v___x_1232_; 
lean_dec(v_k_1229_);
v___x_1231_ = lean_array_fswap(v_as_1227_, v_i_1228_, v_hi_1225_);
v___x_1232_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1232_, 0, v_i_1228_);
lean_ctor_set(v___x_1232_, 1, v___x_1231_);
return v___x_1232_;
}
else
{
lean_object* v___x_1233_; uint8_t v___x_1234_; 
v___x_1233_ = lean_array_fget_borrowed(v_as_1227_, v_k_1229_);
v___x_1234_ = l_Lean_Level_normLt(v___x_1233_, v_pivot_1226_);
if (v___x_1234_ == 0)
{
lean_object* v___x_1235_; lean_object* v___x_1236_; 
v___x_1235_ = lean_unsigned_to_nat(1u);
v___x_1236_ = lean_nat_add(v_k_1229_, v___x_1235_);
lean_dec(v_k_1229_);
v_k_1229_ = v___x_1236_;
goto _start;
}
else
{
lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; 
v___x_1238_ = lean_array_fswap(v_as_1227_, v_i_1228_, v_k_1229_);
v___x_1239_ = lean_unsigned_to_nat(1u);
v___x_1240_ = lean_nat_add(v_i_1228_, v___x_1239_);
lean_dec(v_i_1228_);
v___x_1241_ = lean_nat_add(v_k_1229_, v___x_1239_);
lean_dec(v_k_1229_);
v_as_1227_ = v___x_1238_;
v_i_1228_ = v___x_1240_;
v_k_1229_ = v___x_1241_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1_spec__1___redArg___boxed(lean_object* v_hi_1243_, lean_object* v_pivot_1244_, lean_object* v_as_1245_, lean_object* v_i_1246_, lean_object* v_k_1247_){
_start:
{
lean_object* v_res_1248_; 
v_res_1248_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1_spec__1___redArg(v_hi_1243_, v_pivot_1244_, v_as_1245_, v_i_1246_, v_k_1247_);
lean_dec(v_pivot_1244_);
lean_dec(v_hi_1243_);
return v_res_1248_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1___redArg(lean_object* v_n_1249_, lean_object* v_as_1250_, lean_object* v_lo_1251_, lean_object* v_hi_1252_){
_start:
{
lean_object* v___y_1254_; uint8_t v___x_1264_; 
v___x_1264_ = lean_nat_dec_lt(v_lo_1251_, v_hi_1252_);
if (v___x_1264_ == 0)
{
lean_dec(v_lo_1251_);
return v_as_1250_;
}
else
{
lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v_mid_1267_; lean_object* v___y_1269_; lean_object* v___y_1275_; lean_object* v___x_1280_; lean_object* v___x_1281_; uint8_t v___x_1282_; 
v___x_1265_ = lean_nat_add(v_lo_1251_, v_hi_1252_);
v___x_1266_ = lean_unsigned_to_nat(1u);
v_mid_1267_ = lean_nat_shiftr(v___x_1265_, v___x_1266_);
lean_dec(v___x_1265_);
v___x_1280_ = lean_array_fget_borrowed(v_as_1250_, v_mid_1267_);
v___x_1281_ = lean_array_fget_borrowed(v_as_1250_, v_lo_1251_);
v___x_1282_ = l_Lean_Level_normLt(v___x_1280_, v___x_1281_);
if (v___x_1282_ == 0)
{
v___y_1275_ = v_as_1250_;
goto v___jp_1274_;
}
else
{
lean_object* v___x_1283_; 
v___x_1283_ = lean_array_fswap(v_as_1250_, v_lo_1251_, v_mid_1267_);
v___y_1275_ = v___x_1283_;
goto v___jp_1274_;
}
v___jp_1268_:
{
lean_object* v___x_1270_; lean_object* v___x_1271_; uint8_t v___x_1272_; 
v___x_1270_ = lean_array_fget_borrowed(v___y_1269_, v_mid_1267_);
v___x_1271_ = lean_array_fget_borrowed(v___y_1269_, v_hi_1252_);
v___x_1272_ = l_Lean_Level_normLt(v___x_1270_, v___x_1271_);
if (v___x_1272_ == 0)
{
lean_dec(v_mid_1267_);
v___y_1254_ = v___y_1269_;
goto v___jp_1253_;
}
else
{
lean_object* v___x_1273_; 
v___x_1273_ = lean_array_fswap(v___y_1269_, v_mid_1267_, v_hi_1252_);
lean_dec(v_mid_1267_);
v___y_1254_ = v___x_1273_;
goto v___jp_1253_;
}
}
v___jp_1274_:
{
lean_object* v___x_1276_; lean_object* v___x_1277_; uint8_t v___x_1278_; 
v___x_1276_ = lean_array_fget_borrowed(v___y_1275_, v_hi_1252_);
v___x_1277_ = lean_array_fget_borrowed(v___y_1275_, v_lo_1251_);
v___x_1278_ = l_Lean_Level_normLt(v___x_1276_, v___x_1277_);
if (v___x_1278_ == 0)
{
v___y_1269_ = v___y_1275_;
goto v___jp_1268_;
}
else
{
lean_object* v___x_1279_; 
v___x_1279_ = lean_array_fswap(v___y_1275_, v_lo_1251_, v_hi_1252_);
v___y_1269_ = v___x_1279_;
goto v___jp_1268_;
}
}
}
v___jp_1253_:
{
lean_object* v_pivot_1255_; lean_object* v___x_1256_; lean_object* v_fst_1257_; lean_object* v_snd_1258_; uint8_t v___x_1259_; 
v_pivot_1255_ = lean_array_fget(v___y_1254_, v_hi_1252_);
lean_inc_n(v_lo_1251_, 2);
v___x_1256_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1_spec__1___redArg(v_hi_1252_, v_pivot_1255_, v___y_1254_, v_lo_1251_, v_lo_1251_);
lean_dec(v_pivot_1255_);
v_fst_1257_ = lean_ctor_get(v___x_1256_, 0);
lean_inc(v_fst_1257_);
v_snd_1258_ = lean_ctor_get(v___x_1256_, 1);
lean_inc(v_snd_1258_);
lean_dec_ref(v___x_1256_);
v___x_1259_ = lean_nat_dec_le(v_hi_1252_, v_fst_1257_);
if (v___x_1259_ == 0)
{
lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; 
v___x_1260_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1___redArg(v_n_1249_, v_snd_1258_, v_lo_1251_, v_fst_1257_);
v___x_1261_ = lean_unsigned_to_nat(1u);
v___x_1262_ = lean_nat_add(v_fst_1257_, v___x_1261_);
lean_dec(v_fst_1257_);
v_as_1250_ = v___x_1260_;
v_lo_1251_ = v___x_1262_;
goto _start;
}
else
{
lean_dec(v_fst_1257_);
lean_dec(v_lo_1251_);
return v_snd_1258_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1___redArg___boxed(lean_object* v_n_1284_, lean_object* v_as_1285_, lean_object* v_lo_1286_, lean_object* v_hi_1287_){
_start:
{
lean_object* v_res_1288_; 
v_res_1288_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1___redArg(v_n_1284_, v_as_1285_, v_lo_1286_, v_hi_1287_);
lean_dec(v_hi_1287_);
lean_dec(v_n_1284_);
return v_res_1288_;
}
}
static lean_object* _init_l_Lean_Level_normalize___closed__3(void){
_start:
{
lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; 
v___x_1293_ = ((lean_object*)(l_Lean_Level_normalize___closed__2));
v___x_1294_ = lean_unsigned_to_nat(11u);
v___x_1295_ = lean_unsigned_to_nat(403u);
v___x_1296_ = ((lean_object*)(l_Lean_Level_normalize___closed__1));
v___x_1297_ = ((lean_object*)(l_Lean_Level_mvarId_x21___closed__0));
v___x_1298_ = l_mkPanicMessageWithDecl(v___x_1297_, v___x_1296_, v___x_1295_, v___x_1294_, v___x_1293_);
return v___x_1298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_normalize(lean_object* v_l_1299_){
_start:
{
uint8_t v___x_1300_; 
v___x_1300_ = l_Lean_Level_isAlreadyNormalizedCheap(v_l_1299_);
if (v___x_1300_ == 0)
{
lean_object* v_k_1301_; lean_object* v_u_1302_; 
v_k_1301_ = l_Lean_Level_getOffset(v_l_1299_);
v_u_1302_ = l_Lean_Level_getLevelOffset(v_l_1299_);
switch(lean_obj_tag(v_u_1302_))
{
case 2:
{
lean_object* v_a_1303_; lean_object* v_a_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v_lvls_1308_; lean_object* v_lvls_1309_; lean_object* v___x_1310_; lean_object* v___y_1312_; lean_object* v___y_1313_; lean_object* v___y_1320_; lean_object* v___x_1324_; lean_object* v___y_1326_; lean_object* v___y_1327_; uint8_t v___x_1329_; 
v_a_1303_ = lean_ctor_get(v_u_1302_, 0);
lean_inc(v_a_1303_);
v_a_1304_ = lean_ctor_get(v_u_1302_, 1);
lean_inc(v_a_1304_);
lean_dec_ref_known(v_u_1302_, 2);
v___x_1305_ = lean_box(0);
v___x_1306_ = lean_unsigned_to_nat(0u);
v___x_1307_ = ((lean_object*)(l_Lean_Level_normalize___closed__0));
v_lvls_1308_ = l___private_Lean_Level_0__Lean_Level_getMaxArgsAux___at___00Lean_Level_normalize_spec__0(v_a_1303_, v___x_1300_, v___x_1307_);
v_lvls_1309_ = l___private_Lean_Level_0__Lean_Level_getMaxArgsAux___at___00Lean_Level_normalize_spec__0(v_a_1304_, v___x_1300_, v_lvls_1308_);
v___x_1310_ = lean_unsigned_to_nat(1u);
v___x_1324_ = lean_array_get_size(v_lvls_1309_);
v___x_1329_ = lean_nat_dec_eq(v___x_1324_, v___x_1306_);
if (v___x_1329_ == 0)
{
lean_object* v___x_1330_; lean_object* v___y_1332_; uint8_t v___x_1334_; 
v___x_1330_ = lean_nat_sub(v___x_1324_, v___x_1310_);
v___x_1334_ = lean_nat_dec_le(v___x_1306_, v___x_1330_);
if (v___x_1334_ == 0)
{
lean_inc(v___x_1330_);
v___y_1332_ = v___x_1330_;
goto v___jp_1331_;
}
else
{
v___y_1332_ = v___x_1306_;
goto v___jp_1331_;
}
v___jp_1331_:
{
uint8_t v___x_1333_; 
v___x_1333_ = lean_nat_dec_le(v___y_1332_, v___x_1330_);
if (v___x_1333_ == 0)
{
lean_dec(v___x_1330_);
lean_inc(v___y_1332_);
v___y_1326_ = v___y_1332_;
v___y_1327_ = v___y_1332_;
goto v___jp_1325_;
}
else
{
v___y_1326_ = v___y_1332_;
v___y_1327_ = v___x_1330_;
goto v___jp_1325_;
}
}
}
else
{
v___y_1320_ = v_lvls_1309_;
goto v___jp_1319_;
}
v___jp_1311_:
{
lean_object* v_lvl_u2081_1314_; lean_object* v_prev_1315_; lean_object* v_prevK_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; 
v_lvl_u2081_1314_ = lean_array_get_borrowed(v___x_1305_, v___y_1312_, v___y_1313_);
v_prev_1315_ = l_Lean_Level_getLevelOffset(v_lvl_u2081_1314_);
v_prevK_1316_ = l_Lean_Level_getOffset(v_lvl_u2081_1314_);
v___x_1317_ = lean_nat_add(v___y_1313_, v___x_1310_);
lean_dec(v___y_1313_);
v___x_1318_ = l___private_Lean_Level_0__Lean_Level_mkMaxAux(v___y_1312_, v_k_1301_, v___x_1317_, v_prev_1315_, v_prevK_1316_, v___x_1305_);
lean_dec(v_k_1301_);
lean_dec_ref(v___y_1312_);
return v___x_1318_;
}
v___jp_1319_:
{
lean_object* v_firstNonExplicit_1321_; uint8_t v___x_1322_; 
v_firstNonExplicit_1321_ = l___private_Lean_Level_0__Lean_Level_skipExplicit(v___y_1320_, v___x_1306_);
lean_inc(v_firstNonExplicit_1321_);
v___x_1322_ = l___private_Lean_Level_0__Lean_Level_isExplicitSubsumed(v___y_1320_, v_firstNonExplicit_1321_);
if (v___x_1322_ == 0)
{
lean_object* v___x_1323_; 
v___x_1323_ = lean_nat_sub(v_firstNonExplicit_1321_, v___x_1310_);
lean_dec(v_firstNonExplicit_1321_);
v___y_1312_ = v___y_1320_;
v___y_1313_ = v___x_1323_;
goto v___jp_1311_;
}
else
{
v___y_1312_ = v___y_1320_;
v___y_1313_ = v_firstNonExplicit_1321_;
goto v___jp_1311_;
}
}
v___jp_1325_:
{
lean_object* v___x_1328_; 
v___x_1328_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1___redArg(v___x_1324_, v_lvls_1309_, v___y_1326_, v___y_1327_);
lean_dec(v___y_1327_);
v___y_1320_ = v___x_1328_;
goto v___jp_1319_;
}
}
case 3:
{
lean_object* v_a_1335_; lean_object* v_a_1336_; uint8_t v___x_1337_; 
v_a_1335_ = lean_ctor_get(v_u_1302_, 0);
lean_inc(v_a_1335_);
v_a_1336_ = lean_ctor_get(v_u_1302_, 1);
lean_inc(v_a_1336_);
lean_dec_ref_known(v_u_1302_, 2);
v___x_1337_ = l_Lean_Level_isNeverZero(v_a_1336_);
if (v___x_1337_ == 0)
{
lean_object* v_l_u2081_1338_; lean_object* v_l_u2082_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; 
v_l_u2081_1338_ = l_Lean_Level_normalize(v_a_1335_);
lean_dec(v_a_1335_);
v_l_u2082_1339_ = l_Lean_Level_normalize(v_a_1336_);
lean_dec(v_a_1336_);
v___x_1340_ = l___private_Lean_Level_0__Lean_Level_mkIMaxAux(v_l_u2081_1338_, v_l_u2082_1339_);
v___x_1341_ = l_Lean_Level_addOffsetAux(v_k_1301_, v___x_1340_);
return v___x_1341_;
}
else
{
lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; 
v___x_1342_ = l_Lean_Level_max___override(v_a_1335_, v_a_1336_);
v___x_1343_ = l_Lean_Level_normalize(v___x_1342_);
lean_dec(v___x_1342_);
v___x_1344_ = l_Lean_Level_addOffsetAux(v_k_1301_, v___x_1343_);
return v___x_1344_;
}
}
default: 
{
lean_object* v___x_1345_; lean_object* v___x_1346_; 
lean_dec(v_u_1302_);
lean_dec(v_k_1301_);
v___x_1345_ = lean_obj_once(&l_Lean_Level_normalize___closed__3, &l_Lean_Level_normalize___closed__3_once, _init_l_Lean_Level_normalize___closed__3);
v___x_1346_ = l_panic___at___00Lean_Level_normalize_spec__2(v___x_1345_);
return v___x_1346_;
}
}
}
else
{
lean_inc(v_l_1299_);
return v_l_1299_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_getMaxArgsAux___at___00Lean_Level_normalize_spec__0(lean_object* v_x_1347_, uint8_t v_x_1348_, lean_object* v_x_1349_){
_start:
{
if (lean_obj_tag(v_x_1347_) == 2)
{
lean_object* v_a_1350_; lean_object* v_a_1351_; lean_object* v___x_1352_; 
v_a_1350_ = lean_ctor_get(v_x_1347_, 0);
lean_inc(v_a_1350_);
v_a_1351_ = lean_ctor_get(v_x_1347_, 1);
lean_inc(v_a_1351_);
lean_dec_ref_known(v_x_1347_, 2);
v___x_1352_ = l___private_Lean_Level_0__Lean_Level_getMaxArgsAux___at___00Lean_Level_normalize_spec__0(v_a_1350_, v_x_1348_, v_x_1349_);
v_x_1347_ = v_a_1351_;
v_x_1349_ = v___x_1352_;
goto _start;
}
else
{
if (v_x_1348_ == 0)
{
lean_object* v___x_1354_; uint8_t v___x_1355_; 
v___x_1354_ = l_Lean_Level_normalize(v_x_1347_);
lean_dec(v_x_1347_);
v___x_1355_ = 1;
v_x_1347_ = v___x_1354_;
v_x_1348_ = v___x_1355_;
goto _start;
}
else
{
lean_object* v___x_1357_; 
v___x_1357_ = lean_array_push(v_x_1349_, v_x_1347_);
return v___x_1357_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_getMaxArgsAux___at___00Lean_Level_normalize_spec__0___boxed(lean_object* v_x_1358_, lean_object* v_x_1359_, lean_object* v_x_1360_){
_start:
{
uint8_t v_x_483__boxed_1361_; lean_object* v_res_1362_; 
v_x_483__boxed_1361_ = lean_unbox(v_x_1359_);
v_res_1362_ = l___private_Lean_Level_0__Lean_Level_getMaxArgsAux___at___00Lean_Level_normalize_spec__0(v_x_1358_, v_x_483__boxed_1361_, v_x_1360_);
return v_res_1362_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_normalize___boxed(lean_object* v_l_1363_){
_start:
{
lean_object* v_res_1364_; 
v_res_1364_ = l_Lean_Level_normalize(v_l_1363_);
lean_dec(v_l_1363_);
return v_res_1364_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1(lean_object* v_n_1365_, lean_object* v_as_1366_, lean_object* v_lo_1367_, lean_object* v_hi_1368_, lean_object* v_w_1369_, lean_object* v_hlo_1370_, lean_object* v_hhi_1371_){
_start:
{
lean_object* v___x_1372_; 
v___x_1372_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1___redArg(v_n_1365_, v_as_1366_, v_lo_1367_, v_hi_1368_);
return v___x_1372_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1___boxed(lean_object* v_n_1373_, lean_object* v_as_1374_, lean_object* v_lo_1375_, lean_object* v_hi_1376_, lean_object* v_w_1377_, lean_object* v_hlo_1378_, lean_object* v_hhi_1379_){
_start:
{
lean_object* v_res_1380_; 
v_res_1380_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1(v_n_1373_, v_as_1374_, v_lo_1375_, v_hi_1376_, v_w_1377_, v_hlo_1378_, v_hhi_1379_);
lean_dec(v_hi_1376_);
lean_dec(v_n_1373_);
return v_res_1380_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1_spec__1(lean_object* v_n_1381_, lean_object* v_lo_1382_, lean_object* v_hi_1383_, lean_object* v_hhi_1384_, lean_object* v_pivot_1385_, lean_object* v_as_1386_, lean_object* v_i_1387_, lean_object* v_k_1388_, lean_object* v_ilo_1389_, lean_object* v_ik_1390_, lean_object* v_w_1391_){
_start:
{
lean_object* v___x_1392_; 
v___x_1392_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1_spec__1___redArg(v_hi_1383_, v_pivot_1385_, v_as_1386_, v_i_1387_, v_k_1388_);
return v___x_1392_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1_spec__1___boxed(lean_object* v_n_1393_, lean_object* v_lo_1394_, lean_object* v_hi_1395_, lean_object* v_hhi_1396_, lean_object* v_pivot_1397_, lean_object* v_as_1398_, lean_object* v_i_1399_, lean_object* v_k_1400_, lean_object* v_ilo_1401_, lean_object* v_ik_1402_, lean_object* v_w_1403_){
_start:
{
lean_object* v_res_1404_; 
v_res_1404_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1_spec__1(v_n_1393_, v_lo_1394_, v_hi_1395_, v_hhi_1396_, v_pivot_1397_, v_as_1398_, v_i_1399_, v_k_1400_, v_ilo_1401_, v_ik_1402_, v_w_1403_);
lean_dec(v_pivot_1397_);
lean_dec(v_hi_1395_);
lean_dec(v_lo_1394_);
lean_dec(v_n_1393_);
return v_res_1404_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_isEquiv(lean_object* v_u_1405_, lean_object* v_v_1406_){
_start:
{
uint8_t v___x_1407_; 
v___x_1407_ = lean_level_eq(v_u_1405_, v_v_1406_);
if (v___x_1407_ == 0)
{
lean_object* v___x_1408_; lean_object* v___x_1409_; uint8_t v___x_1410_; 
v___x_1408_ = l_Lean_Level_normalize(v_u_1405_);
v___x_1409_ = l_Lean_Level_normalize(v_v_1406_);
v___x_1410_ = lean_level_eq(v___x_1408_, v___x_1409_);
lean_dec(v___x_1409_);
lean_dec(v___x_1408_);
return v___x_1410_;
}
else
{
return v___x_1407_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_isEquiv___boxed(lean_object* v_u_1411_, lean_object* v_v_1412_){
_start:
{
uint8_t v_res_1413_; lean_object* v_r_1414_; 
v_res_1413_ = l_Lean_Level_isEquiv(v_u_1411_, v_v_1412_);
lean_dec(v_v_1412_);
lean_dec(v_u_1411_);
v_r_1414_ = lean_box(v_res_1413_);
return v_r_1414_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_dec(lean_object* v_x_1415_){
_start:
{
lean_object* v_l_u2081_1417_; lean_object* v_l_u2082_1418_; 
switch(lean_obj_tag(v_x_1415_))
{
case 1:
{
lean_object* v_a_1431_; lean_object* v___x_1432_; 
v_a_1431_ = lean_ctor_get(v_x_1415_, 0);
lean_inc(v_a_1431_);
v___x_1432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1432_, 0, v_a_1431_);
return v___x_1432_;
}
case 2:
{
lean_object* v_a_1433_; lean_object* v_a_1434_; 
v_a_1433_ = lean_ctor_get(v_x_1415_, 0);
v_a_1434_ = lean_ctor_get(v_x_1415_, 1);
v_l_u2081_1417_ = v_a_1433_;
v_l_u2082_1418_ = v_a_1434_;
goto v___jp_1416_;
}
case 3:
{
lean_object* v_a_1435_; lean_object* v_a_1436_; 
v_a_1435_ = lean_ctor_get(v_x_1415_, 0);
v_a_1436_ = lean_ctor_get(v_x_1415_, 1);
v_l_u2081_1417_ = v_a_1435_;
v_l_u2082_1418_ = v_a_1436_;
goto v___jp_1416_;
}
default: 
{
lean_object* v___x_1437_; 
v___x_1437_ = lean_box(0);
return v___x_1437_;
}
}
v___jp_1416_:
{
lean_object* v___x_1419_; 
v___x_1419_ = l_Lean_Level_dec(v_l_u2081_1417_);
if (lean_obj_tag(v___x_1419_) == 0)
{
return v___x_1419_;
}
else
{
lean_object* v_val_1420_; lean_object* v___x_1421_; 
v_val_1420_ = lean_ctor_get(v___x_1419_, 0);
lean_inc(v_val_1420_);
lean_dec_ref_known(v___x_1419_, 1);
v___x_1421_ = l_Lean_Level_dec(v_l_u2082_1418_);
if (lean_obj_tag(v___x_1421_) == 0)
{
lean_dec(v_val_1420_);
return v___x_1421_;
}
else
{
lean_object* v_val_1422_; lean_object* v___x_1424_; uint8_t v_isShared_1425_; uint8_t v_isSharedCheck_1430_; 
v_val_1422_ = lean_ctor_get(v___x_1421_, 0);
v_isSharedCheck_1430_ = !lean_is_exclusive(v___x_1421_);
if (v_isSharedCheck_1430_ == 0)
{
v___x_1424_ = v___x_1421_;
v_isShared_1425_ = v_isSharedCheck_1430_;
goto v_resetjp_1423_;
}
else
{
lean_inc(v_val_1422_);
lean_dec(v___x_1421_);
v___x_1424_ = lean_box(0);
v_isShared_1425_ = v_isSharedCheck_1430_;
goto v_resetjp_1423_;
}
v_resetjp_1423_:
{
lean_object* v___x_1426_; lean_object* v___x_1428_; 
v___x_1426_ = l_Lean_Level_max___override(v_val_1420_, v_val_1422_);
if (v_isShared_1425_ == 0)
{
lean_ctor_set(v___x_1424_, 0, v___x_1426_);
v___x_1428_ = v___x_1424_;
goto v_reusejp_1427_;
}
else
{
lean_object* v_reuseFailAlloc_1429_; 
v_reuseFailAlloc_1429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1429_, 0, v___x_1426_);
v___x_1428_ = v_reuseFailAlloc_1429_;
goto v_reusejp_1427_;
}
v_reusejp_1427_:
{
return v___x_1428_;
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
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_ctorIdx___impl(lean_object* v_x_1440_){
_start:
{
lean_object* v___x_1441_; 
v___x_1441_ = lean_obj_tag_nat(v_x_1440_);
return v___x_1441_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_ctorIdx___impl___boxed(lean_object* v_x_1442_){
_start:
{
lean_object* v_res_1443_; 
v_res_1443_ = l_Lean_Level_PP_Result_ctorIdx___impl(v_x_1442_);
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
v___x_1761_ = l_Array_mkArray0___redArg();
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
v___x_2018_ = lean_unsigned_to_nat(566u);
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
v___x_2039_ = lean_unsigned_to_nat(577u);
v___x_2040_ = ((lean_object*)(l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl___closed__0));
v___x_2041_ = ((lean_object*)(l_Lean_Level_mvarId_x21___closed__0));
v___x_2042_ = l_mkPanicMessageWithDecl(v___x_2041_, v___x_2040_, v___x_2039_, v___x_2038_, v___x_2037_);
return v___x_2042_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl(lean_object* v_lvl_2043_, lean_object* v_newLhs_2044_, lean_object* v_newRhs_2045_){
_start:
{
if (lean_obj_tag(v_lvl_2043_) == 2)
{
lean_object* v_a_2046_; lean_object* v_a_2047_; size_t v___x_2048_; size_t v___x_2049_; uint8_t v___x_2050_; 
v_a_2046_ = lean_ctor_get(v_lvl_2043_, 0);
v_a_2047_ = lean_ctor_get(v_lvl_2043_, 1);
v___x_2048_ = lean_ptr_addr(v_a_2046_);
v___x_2049_ = lean_ptr_addr(v_newLhs_2044_);
v___x_2050_ = lean_usize_dec_eq(v___x_2048_, v___x_2049_);
if (v___x_2050_ == 0)
{
lean_object* v___x_2051_; 
v___x_2051_ = l_Lean_mkLevelMax_x27(v_newLhs_2044_, v_newRhs_2045_);
return v___x_2051_;
}
else
{
size_t v___x_2052_; size_t v___x_2053_; uint8_t v___x_2054_; 
v___x_2052_ = lean_ptr_addr(v_a_2047_);
v___x_2053_ = lean_ptr_addr(v_newRhs_2045_);
v___x_2054_ = lean_usize_dec_eq(v___x_2052_, v___x_2053_);
if (v___x_2054_ == 0)
{
lean_object* v___x_2055_; 
v___x_2055_ = l_Lean_mkLevelMax_x27(v_newLhs_2044_, v_newRhs_2045_);
return v___x_2055_;
}
else
{
lean_object* v___x_2056_; 
v___x_2056_ = l_Lean_simpLevelMax_x27(v_newLhs_2044_, v_newRhs_2045_, v_lvl_2043_);
lean_dec(v_newRhs_2045_);
lean_dec(v_newLhs_2044_);
return v___x_2056_;
}
}
}
else
{
lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; 
lean_dec(v_newRhs_2045_);
lean_dec(v_newLhs_2044_);
v___x_2057_ = lean_box(0);
v___x_2058_ = lean_obj_once(&l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl___closed__2, &l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl___closed__2_once, _init_l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl___closed__2);
v___x_2059_ = l_panic___redArg(v___x_2057_, v___x_2058_);
return v___x_2059_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl___boxed(lean_object* v_lvl_2060_, lean_object* v_newLhs_2061_, lean_object* v_newRhs_2062_){
_start:
{
lean_object* v_res_2063_; 
v_res_2063_ = l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl(v_lvl_2060_, v_newLhs_2061_, v_newRhs_2062_);
lean_dec(v_lvl_2060_);
return v_res_2063_;
}
}
static lean_object* _init_l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl___closed__2(void){
_start:
{
lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; 
v___x_2066_ = ((lean_object*)(l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl___closed__1));
v___x_2067_ = lean_unsigned_to_nat(20u);
v___x_2068_ = lean_unsigned_to_nat(588u);
v___x_2069_ = ((lean_object*)(l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl___closed__0));
v___x_2070_ = ((lean_object*)(l_Lean_Level_mvarId_x21___closed__0));
v___x_2071_ = l_mkPanicMessageWithDecl(v___x_2070_, v___x_2069_, v___x_2068_, v___x_2067_, v___x_2066_);
return v___x_2071_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl(lean_object* v_lvl_2072_, lean_object* v_newLhs_2073_, lean_object* v_newRhs_2074_){
_start:
{
if (lean_obj_tag(v_lvl_2072_) == 3)
{
lean_object* v_a_2075_; lean_object* v_a_2076_; size_t v___x_2077_; size_t v___x_2078_; uint8_t v___x_2079_; 
v_a_2075_ = lean_ctor_get(v_lvl_2072_, 0);
v_a_2076_ = lean_ctor_get(v_lvl_2072_, 1);
v___x_2077_ = lean_ptr_addr(v_a_2075_);
v___x_2078_ = lean_ptr_addr(v_newLhs_2073_);
v___x_2079_ = lean_usize_dec_eq(v___x_2077_, v___x_2078_);
if (v___x_2079_ == 0)
{
lean_object* v___x_2080_; 
v___x_2080_ = l_Lean_mkLevelIMax_x27(v_newLhs_2073_, v_newRhs_2074_);
return v___x_2080_;
}
else
{
size_t v___x_2081_; size_t v___x_2082_; uint8_t v___x_2083_; 
v___x_2081_ = lean_ptr_addr(v_a_2076_);
v___x_2082_ = lean_ptr_addr(v_newRhs_2074_);
v___x_2083_ = lean_usize_dec_eq(v___x_2081_, v___x_2082_);
if (v___x_2083_ == 0)
{
lean_object* v___x_2084_; 
v___x_2084_ = l_Lean_mkLevelIMax_x27(v_newLhs_2073_, v_newRhs_2074_);
return v___x_2084_;
}
else
{
lean_object* v___x_2085_; 
v___x_2085_ = l_Lean_simpLevelIMax_x27(v_newLhs_2073_, v_newRhs_2074_, v_lvl_2072_);
return v___x_2085_;
}
}
}
else
{
lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; 
lean_dec(v_newRhs_2074_);
lean_dec(v_newLhs_2073_);
v___x_2086_ = lean_box(0);
v___x_2087_ = lean_obj_once(&l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl___closed__2, &l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl___closed__2_once, _init_l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl___closed__2);
v___x_2088_ = l_panic___redArg(v___x_2086_, v___x_2087_);
return v___x_2088_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl___boxed(lean_object* v_lvl_2089_, lean_object* v_newLhs_2090_, lean_object* v_newRhs_2091_){
_start:
{
lean_object* v_res_2092_; 
v_res_2092_ = l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl(v_lvl_2089_, v_newLhs_2090_, v_newRhs_2091_);
lean_dec(v_lvl_2089_);
return v_res_2092_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_mkNaryMax(lean_object* v_x_2093_){
_start:
{
if (lean_obj_tag(v_x_2093_) == 0)
{
lean_object* v___x_2094_; 
v___x_2094_ = lean_box(0);
return v___x_2094_;
}
else
{
lean_object* v_tail_2095_; 
v_tail_2095_ = lean_ctor_get(v_x_2093_, 1);
if (lean_obj_tag(v_tail_2095_) == 0)
{
lean_object* v_head_2096_; 
v_head_2096_ = lean_ctor_get(v_x_2093_, 0);
lean_inc(v_head_2096_);
lean_dec_ref_known(v_x_2093_, 2);
return v_head_2096_;
}
else
{
lean_object* v_head_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; 
lean_inc(v_tail_2095_);
v_head_2097_ = lean_ctor_get(v_x_2093_, 0);
lean_inc(v_head_2097_);
lean_dec_ref_known(v_x_2093_, 2);
v___x_2098_ = l_Lean_Level_mkNaryMax(v_tail_2095_);
v___x_2099_ = l_Lean_mkLevelMax_x27(v_head_2097_, v___x_2098_);
return v___x_2099_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_substParams_go(lean_object* v_s_2100_, lean_object* v_u_2101_){
_start:
{
switch(lean_obj_tag(v_u_2101_))
{
case 1:
{
lean_object* v_a_2102_; uint8_t v___x_2103_; 
v_a_2102_ = lean_ctor_get(v_u_2101_, 0);
v___x_2103_ = l_Lean_Level_hasParam(v_u_2101_);
if (v___x_2103_ == 0)
{
lean_dec_ref(v_s_2100_);
return v_u_2101_;
}
else
{
lean_object* v___x_2104_; size_t v___x_2105_; size_t v___x_2106_; uint8_t v___x_2107_; 
lean_inc(v_a_2102_);
v___x_2104_ = l___private_Lean_Level_0__Lean_Level_substParams_go(v_s_2100_, v_a_2102_);
v___x_2105_ = lean_ptr_addr(v_a_2102_);
v___x_2106_ = lean_ptr_addr(v___x_2104_);
v___x_2107_ = lean_usize_dec_eq(v___x_2105_, v___x_2106_);
if (v___x_2107_ == 0)
{
lean_object* v___x_2108_; 
lean_dec_ref_known(v_u_2101_, 1);
v___x_2108_ = l_Lean_Level_succ___override(v___x_2104_);
return v___x_2108_;
}
else
{
lean_dec(v___x_2104_);
return v_u_2101_;
}
}
}
case 2:
{
lean_object* v_a_2109_; lean_object* v_a_2110_; uint8_t v___x_2111_; 
v_a_2109_ = lean_ctor_get(v_u_2101_, 0);
v_a_2110_ = lean_ctor_get(v_u_2101_, 1);
v___x_2111_ = l_Lean_Level_hasParam(v_u_2101_);
if (v___x_2111_ == 0)
{
lean_dec_ref(v_s_2100_);
return v_u_2101_;
}
else
{
lean_object* v___x_2112_; lean_object* v___x_2113_; size_t v___x_2114_; size_t v___x_2115_; uint8_t v___x_2116_; 
lean_inc(v_a_2109_);
lean_inc_ref(v_s_2100_);
v___x_2112_ = l___private_Lean_Level_0__Lean_Level_substParams_go(v_s_2100_, v_a_2109_);
lean_inc(v_a_2110_);
v___x_2113_ = l___private_Lean_Level_0__Lean_Level_substParams_go(v_s_2100_, v_a_2110_);
v___x_2114_ = lean_ptr_addr(v_a_2109_);
v___x_2115_ = lean_ptr_addr(v___x_2112_);
v___x_2116_ = lean_usize_dec_eq(v___x_2114_, v___x_2115_);
if (v___x_2116_ == 0)
{
lean_object* v___x_2117_; 
lean_dec_ref_known(v_u_2101_, 2);
v___x_2117_ = l_Lean_mkLevelMax_x27(v___x_2112_, v___x_2113_);
return v___x_2117_;
}
else
{
size_t v___x_2118_; size_t v___x_2119_; uint8_t v___x_2120_; 
v___x_2118_ = lean_ptr_addr(v_a_2110_);
v___x_2119_ = lean_ptr_addr(v___x_2113_);
v___x_2120_ = lean_usize_dec_eq(v___x_2118_, v___x_2119_);
if (v___x_2120_ == 0)
{
lean_object* v___x_2121_; 
lean_dec_ref_known(v_u_2101_, 2);
v___x_2121_ = l_Lean_mkLevelMax_x27(v___x_2112_, v___x_2113_);
return v___x_2121_;
}
else
{
lean_object* v___x_2122_; 
v___x_2122_ = l_Lean_simpLevelMax_x27(v___x_2112_, v___x_2113_, v_u_2101_);
lean_dec_ref_known(v_u_2101_, 2);
lean_dec(v___x_2113_);
lean_dec(v___x_2112_);
return v___x_2122_;
}
}
}
}
case 3:
{
lean_object* v_a_2123_; lean_object* v_a_2124_; uint8_t v___x_2125_; 
v_a_2123_ = lean_ctor_get(v_u_2101_, 0);
v_a_2124_ = lean_ctor_get(v_u_2101_, 1);
v___x_2125_ = l_Lean_Level_hasParam(v_u_2101_);
if (v___x_2125_ == 0)
{
lean_dec_ref(v_s_2100_);
return v_u_2101_;
}
else
{
lean_object* v___x_2126_; lean_object* v___x_2127_; size_t v___x_2128_; size_t v___x_2129_; uint8_t v___x_2130_; 
lean_inc(v_a_2123_);
lean_inc_ref(v_s_2100_);
v___x_2126_ = l___private_Lean_Level_0__Lean_Level_substParams_go(v_s_2100_, v_a_2123_);
lean_inc(v_a_2124_);
v___x_2127_ = l___private_Lean_Level_0__Lean_Level_substParams_go(v_s_2100_, v_a_2124_);
v___x_2128_ = lean_ptr_addr(v_a_2123_);
v___x_2129_ = lean_ptr_addr(v___x_2126_);
v___x_2130_ = lean_usize_dec_eq(v___x_2128_, v___x_2129_);
if (v___x_2130_ == 0)
{
lean_object* v___x_2131_; 
lean_dec_ref_known(v_u_2101_, 2);
v___x_2131_ = l_Lean_mkLevelIMax_x27(v___x_2126_, v___x_2127_);
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
lean_dec_ref_known(v_u_2101_, 2);
v___x_2135_ = l_Lean_mkLevelIMax_x27(v___x_2126_, v___x_2127_);
return v___x_2135_;
}
else
{
lean_object* v___x_2136_; 
v___x_2136_ = l_Lean_simpLevelIMax_x27(v___x_2126_, v___x_2127_, v_u_2101_);
lean_dec_ref_known(v_u_2101_, 2);
return v___x_2136_;
}
}
}
}
case 4:
{
lean_object* v_a_2137_; lean_object* v___x_2138_; 
v_a_2137_ = lean_ctor_get(v_u_2101_, 0);
lean_inc(v_a_2137_);
v___x_2138_ = lean_apply_1(v_s_2100_, v_a_2137_);
if (lean_obj_tag(v___x_2138_) == 0)
{
return v_u_2101_;
}
else
{
lean_object* v_val_2139_; 
lean_dec_ref_known(v_u_2101_, 1);
v_val_2139_ = lean_ctor_get(v___x_2138_, 0);
lean_inc(v_val_2139_);
lean_dec_ref_known(v___x_2138_, 1);
return v_val_2139_;
}
}
default: 
{
lean_dec_ref(v_s_2100_);
return v_u_2101_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_substParams(lean_object* v_u_2140_, lean_object* v_s_2141_){
_start:
{
lean_object* v___x_2142_; 
v___x_2142_ = l___private_Lean_Level_0__Lean_Level_substParams_go(v_s_2141_, v_u_2140_);
return v___x_2142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_getParamSubst(lean_object* v_x_2143_, lean_object* v_x_2144_, lean_object* v_x_2145_){
_start:
{
if (lean_obj_tag(v_x_2143_) == 1)
{
if (lean_obj_tag(v_x_2144_) == 1)
{
lean_object* v_head_2146_; lean_object* v_tail_2147_; lean_object* v_head_2148_; lean_object* v_tail_2149_; uint8_t v___x_2150_; 
v_head_2146_ = lean_ctor_get(v_x_2143_, 0);
v_tail_2147_ = lean_ctor_get(v_x_2143_, 1);
v_head_2148_ = lean_ctor_get(v_x_2144_, 0);
v_tail_2149_ = lean_ctor_get(v_x_2144_, 1);
v___x_2150_ = lean_name_eq(v_head_2146_, v_x_2145_);
if (v___x_2150_ == 0)
{
v_x_2143_ = v_tail_2147_;
v_x_2144_ = v_tail_2149_;
goto _start;
}
else
{
lean_object* v___x_2152_; 
lean_inc(v_head_2148_);
v___x_2152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2152_, 0, v_head_2148_);
return v___x_2152_;
}
}
else
{
lean_object* v___x_2153_; 
v___x_2153_ = lean_box(0);
return v___x_2153_;
}
}
else
{
lean_object* v___x_2154_; 
v___x_2154_ = lean_box(0);
return v___x_2154_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_getParamSubst___boxed(lean_object* v_x_2155_, lean_object* v_x_2156_, lean_object* v_x_2157_){
_start:
{
lean_object* v_res_2158_; 
v_res_2158_ = l_Lean_Level_getParamSubst(v_x_2155_, v_x_2156_, v_x_2157_);
lean_dec(v_x_2157_);
lean_dec(v_x_2156_);
lean_dec(v_x_2155_);
return v_res_2158_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_instantiateParams(lean_object* v_u_2159_, lean_object* v_paramNames_2160_, lean_object* v_vs_2161_){
_start:
{
lean_object* v___x_2162_; lean_object* v___x_2163_; 
v___x_2162_ = lean_alloc_closure((void*)(l_Lean_Level_getParamSubst___boxed), 3, 2);
lean_closure_set(v___x_2162_, 0, v_paramNames_2160_);
lean_closure_set(v___x_2162_, 1, v_vs_2161_);
v___x_2163_ = l___private_Lean_Level_0__Lean_Level_substParams_go(v___x_2162_, v_u_2159_);
return v___x_2163_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Level_0__Lean_Level_geq_go(lean_object* v_u_2164_, lean_object* v_v_2165_){
_start:
{
uint8_t v___y_2167_; uint8_t v___y_2181_; lean_object* v_u_u2081_2183_; lean_object* v_u_u2082_2184_; lean_object* v_v_2185_; uint8_t v___x_2188_; 
v___x_2188_ = lean_level_eq(v_u_2164_, v_v_2165_);
if (v___x_2188_ == 0)
{
switch(lean_obj_tag(v_v_2165_))
{
case 0:
{
uint8_t v___x_2189_; 
v___x_2189_ = 1;
return v___x_2189_;
}
case 2:
{
lean_object* v_a_2190_; lean_object* v_a_2191_; uint8_t v___x_2192_; 
v_a_2190_ = lean_ctor_get(v_v_2165_, 0);
v_a_2191_ = lean_ctor_get(v_v_2165_, 1);
v___x_2192_ = l___private_Lean_Level_0__Lean_Level_geq_go(v_u_2164_, v_a_2190_);
if (v___x_2192_ == 0)
{
return v___x_2192_;
}
else
{
v_v_2165_ = v_a_2191_;
goto _start;
}
}
case 1:
{
switch(lean_obj_tag(v_u_2164_))
{
case 2:
{
lean_object* v_a_2194_; lean_object* v_a_2195_; 
v_a_2194_ = lean_ctor_get(v_u_2164_, 0);
v_a_2195_ = lean_ctor_get(v_u_2164_, 1);
v_u_u2081_2183_ = v_a_2194_;
v_u_u2082_2184_ = v_a_2195_;
v_v_2185_ = v_v_2165_;
goto v___jp_2182_;
}
case 3:
{
lean_object* v_a_2196_; 
v_a_2196_ = lean_ctor_get(v_u_2164_, 1);
v_u_2164_ = v_a_2196_;
goto _start;
}
case 1:
{
lean_object* v_a_2198_; lean_object* v_a_2199_; 
v_a_2198_ = lean_ctor_get(v_v_2165_, 0);
v_a_2199_ = lean_ctor_get(v_u_2164_, 0);
v_u_2164_ = v_a_2199_;
v_v_2165_ = v_a_2198_;
goto _start;
}
default: 
{
goto v___jp_2171_;
}
}
}
default: 
{
switch(lean_obj_tag(v_u_2164_))
{
case 2:
{
lean_object* v_a_2201_; lean_object* v_a_2202_; 
v_a_2201_ = lean_ctor_get(v_u_2164_, 0);
v_a_2202_ = lean_ctor_get(v_u_2164_, 1);
v_u_u2081_2183_ = v_a_2201_;
v_u_u2082_2184_ = v_a_2202_;
v_v_2185_ = v_v_2165_;
goto v___jp_2182_;
}
case 3:
{
lean_object* v_a_2203_; 
v_a_2203_ = lean_ctor_get(v_u_2164_, 1);
v_u_2164_ = v_a_2203_;
goto _start;
}
default: 
{
goto v___jp_2171_;
}
}
}
}
}
else
{
return v___x_2188_;
}
v___jp_2166_:
{
if (v___y_2167_ == 0)
{
return v___y_2167_;
}
else
{
lean_object* v___x_2168_; lean_object* v___x_2169_; uint8_t v___x_2170_; 
v___x_2168_ = l_Lean_Level_getOffset(v_v_2165_);
v___x_2169_ = l_Lean_Level_getOffset(v_u_2164_);
v___x_2170_ = lean_nat_dec_le(v___x_2168_, v___x_2169_);
lean_dec(v___x_2169_);
lean_dec(v___x_2168_);
return v___x_2170_;
}
}
v___jp_2171_:
{
if (lean_obj_tag(v_v_2165_) == 3)
{
lean_object* v_a_2172_; lean_object* v_a_2173_; uint8_t v___x_2174_; 
v_a_2172_ = lean_ctor_get(v_v_2165_, 0);
v_a_2173_ = lean_ctor_get(v_v_2165_, 1);
v___x_2174_ = l___private_Lean_Level_0__Lean_Level_geq_go(v_u_2164_, v_a_2172_);
if (v___x_2174_ == 0)
{
return v___x_2174_;
}
else
{
v_v_2165_ = v_a_2173_;
goto _start;
}
}
else
{
lean_object* v_v_x27_2176_; lean_object* v___x_2177_; uint8_t v___x_2178_; 
v_v_x27_2176_ = l_Lean_Level_getLevelOffset(v_v_2165_);
v___x_2177_ = l_Lean_Level_getLevelOffset(v_u_2164_);
v___x_2178_ = lean_level_eq(v___x_2177_, v_v_x27_2176_);
lean_dec(v___x_2177_);
if (v___x_2178_ == 0)
{
uint8_t v___x_2179_; 
v___x_2179_ = l_Lean_Level_isZero(v_v_x27_2176_);
lean_dec(v_v_x27_2176_);
v___y_2167_ = v___x_2179_;
goto v___jp_2166_;
}
else
{
lean_dec(v_v_x27_2176_);
v___y_2167_ = v___x_2178_;
goto v___jp_2166_;
}
}
}
v___jp_2180_:
{
if (v___y_2181_ == 0)
{
goto v___jp_2171_;
}
else
{
return v___y_2181_;
}
}
v___jp_2182_:
{
uint8_t v___x_2186_; 
v___x_2186_ = l___private_Lean_Level_0__Lean_Level_geq_go(v_u_u2081_2183_, v_v_2185_);
if (v___x_2186_ == 0)
{
uint8_t v___x_2187_; 
v___x_2187_ = l___private_Lean_Level_0__Lean_Level_geq_go(v_u_u2082_2184_, v_v_2185_);
v___y_2181_ = v___x_2187_;
goto v___jp_2180_;
}
else
{
v___y_2181_ = v___x_2186_;
goto v___jp_2180_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_geq_go___boxed(lean_object* v_u_2205_, lean_object* v_v_2206_){
_start:
{
uint8_t v_res_2207_; lean_object* v_r_2208_; 
v_res_2207_ = l___private_Lean_Level_0__Lean_Level_geq_go(v_u_2205_, v_v_2206_);
lean_dec(v_v_2206_);
lean_dec(v_u_2205_);
v_r_2208_ = lean_box(v_res_2207_);
return v_r_2208_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_geq_go_match__1_splitter___redArg(lean_object* v_u_2209_, lean_object* v_v_2210_, lean_object* v_h__1_2211_, lean_object* v_h__2_2212_, lean_object* v_h__3_2213_, lean_object* v_h__4_2214_, lean_object* v_h__5_2215_, lean_object* v_h__6_2216_){
_start:
{
switch(lean_obj_tag(v_v_2210_))
{
case 0:
{
lean_object* v___x_2217_; 
lean_dec(v_h__6_2216_);
lean_dec(v_h__5_2215_);
lean_dec(v_h__4_2214_);
lean_dec(v_h__3_2213_);
lean_dec(v_h__2_2212_);
v___x_2217_ = lean_apply_1(v_h__1_2211_, v_u_2209_);
return v___x_2217_;
}
case 2:
{
lean_object* v_a_2218_; lean_object* v_a_2219_; lean_object* v___x_2220_; 
lean_dec(v_h__6_2216_);
lean_dec(v_h__5_2215_);
lean_dec(v_h__4_2214_);
lean_dec(v_h__3_2213_);
lean_dec(v_h__1_2211_);
v_a_2218_ = lean_ctor_get(v_v_2210_, 0);
lean_inc(v_a_2218_);
v_a_2219_ = lean_ctor_get(v_v_2210_, 1);
lean_inc(v_a_2219_);
lean_dec_ref_known(v_v_2210_, 2);
v___x_2220_ = lean_apply_3(v_h__2_2212_, v_u_2209_, v_a_2218_, v_a_2219_);
return v___x_2220_;
}
case 1:
{
lean_dec(v_h__2_2212_);
lean_dec(v_h__1_2211_);
switch(lean_obj_tag(v_u_2209_))
{
case 2:
{
lean_object* v_a_2221_; lean_object* v_a_2222_; lean_object* v___x_2223_; 
lean_dec(v_h__6_2216_);
lean_dec(v_h__5_2215_);
lean_dec(v_h__4_2214_);
v_a_2221_ = lean_ctor_get(v_u_2209_, 0);
lean_inc(v_a_2221_);
v_a_2222_ = lean_ctor_get(v_u_2209_, 1);
lean_inc(v_a_2222_);
lean_dec_ref_known(v_u_2209_, 2);
v___x_2223_ = lean_apply_5(v_h__3_2213_, v_a_2221_, v_a_2222_, v_v_2210_, lean_box(0), lean_box(0));
return v___x_2223_;
}
case 3:
{
lean_object* v_a_2224_; lean_object* v_a_2225_; lean_object* v___x_2226_; 
lean_dec(v_h__6_2216_);
lean_dec(v_h__5_2215_);
lean_dec(v_h__3_2213_);
v_a_2224_ = lean_ctor_get(v_u_2209_, 0);
lean_inc(v_a_2224_);
v_a_2225_ = lean_ctor_get(v_u_2209_, 1);
lean_inc(v_a_2225_);
lean_dec_ref_known(v_u_2209_, 2);
v___x_2226_ = lean_apply_5(v_h__4_2214_, v_a_2224_, v_a_2225_, v_v_2210_, lean_box(0), lean_box(0));
return v___x_2226_;
}
case 1:
{
lean_object* v_a_2227_; lean_object* v_a_2228_; lean_object* v___x_2229_; 
lean_dec(v_h__6_2216_);
lean_dec(v_h__4_2214_);
lean_dec(v_h__3_2213_);
v_a_2227_ = lean_ctor_get(v_v_2210_, 0);
lean_inc(v_a_2227_);
lean_dec_ref_known(v_v_2210_, 1);
v_a_2228_ = lean_ctor_get(v_u_2209_, 0);
lean_inc(v_a_2228_);
lean_dec_ref_known(v_u_2209_, 1);
v___x_2229_ = lean_apply_2(v_h__5_2215_, v_a_2228_, v_a_2227_);
return v___x_2229_;
}
default: 
{
lean_object* v___x_2230_; 
lean_dec(v_h__5_2215_);
lean_dec(v_h__4_2214_);
lean_dec(v_h__3_2213_);
v___x_2230_ = lean_apply_7(v_h__6_2216_, v_u_2209_, v_v_2210_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_2230_;
}
}
}
default: 
{
lean_dec(v_h__5_2215_);
lean_dec(v_h__2_2212_);
lean_dec(v_h__1_2211_);
switch(lean_obj_tag(v_u_2209_))
{
case 2:
{
lean_object* v_a_2231_; lean_object* v_a_2232_; lean_object* v___x_2233_; 
lean_dec(v_h__6_2216_);
lean_dec(v_h__4_2214_);
v_a_2231_ = lean_ctor_get(v_u_2209_, 0);
lean_inc(v_a_2231_);
v_a_2232_ = lean_ctor_get(v_u_2209_, 1);
lean_inc(v_a_2232_);
lean_dec_ref_known(v_u_2209_, 2);
v___x_2233_ = lean_apply_5(v_h__3_2213_, v_a_2231_, v_a_2232_, v_v_2210_, lean_box(0), lean_box(0));
return v___x_2233_;
}
case 3:
{
lean_object* v_a_2234_; lean_object* v_a_2235_; lean_object* v___x_2236_; 
lean_dec(v_h__6_2216_);
lean_dec(v_h__3_2213_);
v_a_2234_ = lean_ctor_get(v_u_2209_, 0);
lean_inc(v_a_2234_);
v_a_2235_ = lean_ctor_get(v_u_2209_, 1);
lean_inc(v_a_2235_);
lean_dec_ref_known(v_u_2209_, 2);
v___x_2236_ = lean_apply_5(v_h__4_2214_, v_a_2234_, v_a_2235_, v_v_2210_, lean_box(0), lean_box(0));
return v___x_2236_;
}
default: 
{
lean_object* v___x_2237_; 
lean_dec(v_h__4_2214_);
lean_dec(v_h__3_2213_);
v___x_2237_ = lean_apply_7(v_h__6_2216_, v_u_2209_, v_v_2210_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_2237_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_geq_go_match__1_splitter(lean_object* v_motive_2238_, lean_object* v_u_2239_, lean_object* v_v_2240_, lean_object* v_h__1_2241_, lean_object* v_h__2_2242_, lean_object* v_h__3_2243_, lean_object* v_h__4_2244_, lean_object* v_h__5_2245_, lean_object* v_h__6_2246_){
_start:
{
switch(lean_obj_tag(v_v_2240_))
{
case 0:
{
lean_object* v___x_2247_; 
lean_dec(v_h__6_2246_);
lean_dec(v_h__5_2245_);
lean_dec(v_h__4_2244_);
lean_dec(v_h__3_2243_);
lean_dec(v_h__2_2242_);
v___x_2247_ = lean_apply_1(v_h__1_2241_, v_u_2239_);
return v___x_2247_;
}
case 2:
{
lean_object* v_a_2248_; lean_object* v_a_2249_; lean_object* v___x_2250_; 
lean_dec(v_h__6_2246_);
lean_dec(v_h__5_2245_);
lean_dec(v_h__4_2244_);
lean_dec(v_h__3_2243_);
lean_dec(v_h__1_2241_);
v_a_2248_ = lean_ctor_get(v_v_2240_, 0);
lean_inc(v_a_2248_);
v_a_2249_ = lean_ctor_get(v_v_2240_, 1);
lean_inc(v_a_2249_);
lean_dec_ref_known(v_v_2240_, 2);
v___x_2250_ = lean_apply_3(v_h__2_2242_, v_u_2239_, v_a_2248_, v_a_2249_);
return v___x_2250_;
}
case 1:
{
lean_dec(v_h__2_2242_);
lean_dec(v_h__1_2241_);
switch(lean_obj_tag(v_u_2239_))
{
case 2:
{
lean_object* v_a_2251_; lean_object* v_a_2252_; lean_object* v___x_2253_; 
lean_dec(v_h__6_2246_);
lean_dec(v_h__5_2245_);
lean_dec(v_h__4_2244_);
v_a_2251_ = lean_ctor_get(v_u_2239_, 0);
lean_inc(v_a_2251_);
v_a_2252_ = lean_ctor_get(v_u_2239_, 1);
lean_inc(v_a_2252_);
lean_dec_ref_known(v_u_2239_, 2);
v___x_2253_ = lean_apply_5(v_h__3_2243_, v_a_2251_, v_a_2252_, v_v_2240_, lean_box(0), lean_box(0));
return v___x_2253_;
}
case 3:
{
lean_object* v_a_2254_; lean_object* v_a_2255_; lean_object* v___x_2256_; 
lean_dec(v_h__6_2246_);
lean_dec(v_h__5_2245_);
lean_dec(v_h__3_2243_);
v_a_2254_ = lean_ctor_get(v_u_2239_, 0);
lean_inc(v_a_2254_);
v_a_2255_ = lean_ctor_get(v_u_2239_, 1);
lean_inc(v_a_2255_);
lean_dec_ref_known(v_u_2239_, 2);
v___x_2256_ = lean_apply_5(v_h__4_2244_, v_a_2254_, v_a_2255_, v_v_2240_, lean_box(0), lean_box(0));
return v___x_2256_;
}
case 1:
{
lean_object* v_a_2257_; lean_object* v_a_2258_; lean_object* v___x_2259_; 
lean_dec(v_h__6_2246_);
lean_dec(v_h__4_2244_);
lean_dec(v_h__3_2243_);
v_a_2257_ = lean_ctor_get(v_v_2240_, 0);
lean_inc(v_a_2257_);
lean_dec_ref_known(v_v_2240_, 1);
v_a_2258_ = lean_ctor_get(v_u_2239_, 0);
lean_inc(v_a_2258_);
lean_dec_ref_known(v_u_2239_, 1);
v___x_2259_ = lean_apply_2(v_h__5_2245_, v_a_2258_, v_a_2257_);
return v___x_2259_;
}
default: 
{
lean_object* v___x_2260_; 
lean_dec(v_h__5_2245_);
lean_dec(v_h__4_2244_);
lean_dec(v_h__3_2243_);
v___x_2260_ = lean_apply_7(v_h__6_2246_, v_u_2239_, v_v_2240_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_2260_;
}
}
}
default: 
{
lean_dec(v_h__5_2245_);
lean_dec(v_h__2_2242_);
lean_dec(v_h__1_2241_);
switch(lean_obj_tag(v_u_2239_))
{
case 2:
{
lean_object* v_a_2261_; lean_object* v_a_2262_; lean_object* v___x_2263_; 
lean_dec(v_h__6_2246_);
lean_dec(v_h__4_2244_);
v_a_2261_ = lean_ctor_get(v_u_2239_, 0);
lean_inc(v_a_2261_);
v_a_2262_ = lean_ctor_get(v_u_2239_, 1);
lean_inc(v_a_2262_);
lean_dec_ref_known(v_u_2239_, 2);
v___x_2263_ = lean_apply_5(v_h__3_2243_, v_a_2261_, v_a_2262_, v_v_2240_, lean_box(0), lean_box(0));
return v___x_2263_;
}
case 3:
{
lean_object* v_a_2264_; lean_object* v_a_2265_; lean_object* v___x_2266_; 
lean_dec(v_h__6_2246_);
lean_dec(v_h__3_2243_);
v_a_2264_ = lean_ctor_get(v_u_2239_, 0);
lean_inc(v_a_2264_);
v_a_2265_ = lean_ctor_get(v_u_2239_, 1);
lean_inc(v_a_2265_);
lean_dec_ref_known(v_u_2239_, 2);
v___x_2266_ = lean_apply_5(v_h__4_2244_, v_a_2264_, v_a_2265_, v_v_2240_, lean_box(0), lean_box(0));
return v___x_2266_;
}
default: 
{
lean_object* v___x_2267_; 
lean_dec(v_h__4_2244_);
lean_dec(v_h__3_2243_);
v___x_2267_ = lean_apply_7(v_h__6_2246_, v_u_2239_, v_v_2240_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_2267_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_isIMax_match__1_splitter___redArg(lean_object* v_x_2268_, lean_object* v_h__1_2269_, lean_object* v_h__2_2270_){
_start:
{
if (lean_obj_tag(v_x_2268_) == 3)
{
lean_object* v_a_2271_; lean_object* v_a_2272_; lean_object* v___x_2273_; 
lean_dec(v_h__2_2270_);
v_a_2271_ = lean_ctor_get(v_x_2268_, 0);
lean_inc(v_a_2271_);
v_a_2272_ = lean_ctor_get(v_x_2268_, 1);
lean_inc(v_a_2272_);
lean_dec_ref_known(v_x_2268_, 2);
v___x_2273_ = lean_apply_2(v_h__1_2269_, v_a_2271_, v_a_2272_);
return v___x_2273_;
}
else
{
lean_object* v___x_2274_; 
lean_dec(v_h__1_2269_);
v___x_2274_ = lean_apply_2(v_h__2_2270_, v_x_2268_, lean_box(0));
return v___x_2274_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_isIMax_match__1_splitter(lean_object* v_motive_2275_, lean_object* v_x_2276_, lean_object* v_h__1_2277_, lean_object* v_h__2_2278_){
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
lean_dec_ref_known(v_x_2276_, 2);
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
LEAN_EXPORT uint8_t l_Lean_Level_geq(lean_object* v_u_2283_, lean_object* v_v_2284_){
_start:
{
lean_object* v___x_2285_; lean_object* v___x_2286_; uint8_t v___x_2287_; 
v___x_2285_ = l_Lean_Level_normalize(v_u_2283_);
v___x_2286_ = l_Lean_Level_normalize(v_v_2284_);
v___x_2287_ = l___private_Lean_Level_0__Lean_Level_geq_go(v___x_2285_, v___x_2286_);
lean_dec(v___x_2286_);
lean_dec(v___x_2285_);
return v___x_2287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_geq___boxed(lean_object* v_u_2288_, lean_object* v_v_2289_){
_start:
{
uint8_t v_res_2290_; lean_object* v_r_2291_; 
v_res_2290_ = l_Lean_Level_geq(v_u_2288_, v_v_2289_);
lean_dec(v_v_2289_);
lean_dec(v_u_2288_);
v_r_2291_ = lean_box(v_res_2290_);
return v_r_2291_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Level_collectMVars_spec__1___redArg(lean_object* v_k_2292_, lean_object* v_v_2293_, lean_object* v_t_2294_){
_start:
{
if (lean_obj_tag(v_t_2294_) == 0)
{
lean_object* v_size_2295_; lean_object* v_k_2296_; lean_object* v_v_2297_; lean_object* v_l_2298_; lean_object* v_r_2299_; lean_object* v___x_2301_; uint8_t v_isShared_2302_; uint8_t v_isSharedCheck_2579_; 
v_size_2295_ = lean_ctor_get(v_t_2294_, 0);
v_k_2296_ = lean_ctor_get(v_t_2294_, 1);
v_v_2297_ = lean_ctor_get(v_t_2294_, 2);
v_l_2298_ = lean_ctor_get(v_t_2294_, 3);
v_r_2299_ = lean_ctor_get(v_t_2294_, 4);
v_isSharedCheck_2579_ = !lean_is_exclusive(v_t_2294_);
if (v_isSharedCheck_2579_ == 0)
{
v___x_2301_ = v_t_2294_;
v_isShared_2302_ = v_isSharedCheck_2579_;
goto v_resetjp_2300_;
}
else
{
lean_inc(v_r_2299_);
lean_inc(v_l_2298_);
lean_inc(v_v_2297_);
lean_inc(v_k_2296_);
lean_inc(v_size_2295_);
lean_dec(v_t_2294_);
v___x_2301_ = lean_box(0);
v_isShared_2302_ = v_isSharedCheck_2579_;
goto v_resetjp_2300_;
}
v_resetjp_2300_:
{
uint8_t v___x_2303_; 
v___x_2303_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2292_, v_k_2296_);
switch(v___x_2303_)
{
case 0:
{
lean_object* v_impl_2304_; lean_object* v___x_2305_; 
lean_dec(v_size_2295_);
v_impl_2304_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Level_collectMVars_spec__1___redArg(v_k_2292_, v_v_2293_, v_l_2298_);
v___x_2305_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_2299_) == 0)
{
lean_object* v_size_2306_; lean_object* v_size_2307_; lean_object* v_k_2308_; lean_object* v_v_2309_; lean_object* v_l_2310_; lean_object* v_r_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; uint8_t v___x_2314_; 
v_size_2306_ = lean_ctor_get(v_r_2299_, 0);
v_size_2307_ = lean_ctor_get(v_impl_2304_, 0);
v_k_2308_ = lean_ctor_get(v_impl_2304_, 1);
v_v_2309_ = lean_ctor_get(v_impl_2304_, 2);
v_l_2310_ = lean_ctor_get(v_impl_2304_, 3);
v_r_2311_ = lean_ctor_get(v_impl_2304_, 4);
lean_inc(v_r_2311_);
v___x_2312_ = lean_unsigned_to_nat(3u);
v___x_2313_ = lean_nat_mul(v___x_2312_, v_size_2306_);
v___x_2314_ = lean_nat_dec_lt(v___x_2313_, v_size_2307_);
lean_dec(v___x_2313_);
if (v___x_2314_ == 0)
{
lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2318_; 
lean_dec(v_r_2311_);
v___x_2315_ = lean_nat_add(v___x_2305_, v_size_2307_);
v___x_2316_ = lean_nat_add(v___x_2315_, v_size_2306_);
lean_dec(v___x_2315_);
if (v_isShared_2302_ == 0)
{
lean_ctor_set(v___x_2301_, 3, v_impl_2304_);
lean_ctor_set(v___x_2301_, 0, v___x_2316_);
v___x_2318_ = v___x_2301_;
goto v_reusejp_2317_;
}
else
{
lean_object* v_reuseFailAlloc_2319_; 
v_reuseFailAlloc_2319_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2319_, 0, v___x_2316_);
lean_ctor_set(v_reuseFailAlloc_2319_, 1, v_k_2296_);
lean_ctor_set(v_reuseFailAlloc_2319_, 2, v_v_2297_);
lean_ctor_set(v_reuseFailAlloc_2319_, 3, v_impl_2304_);
lean_ctor_set(v_reuseFailAlloc_2319_, 4, v_r_2299_);
v___x_2318_ = v_reuseFailAlloc_2319_;
goto v_reusejp_2317_;
}
v_reusejp_2317_:
{
return v___x_2318_;
}
}
else
{
lean_object* v___x_2321_; uint8_t v_isShared_2322_; uint8_t v_isSharedCheck_2385_; 
lean_inc(v_l_2310_);
lean_inc(v_v_2309_);
lean_inc(v_k_2308_);
lean_inc(v_size_2307_);
v_isSharedCheck_2385_ = !lean_is_exclusive(v_impl_2304_);
if (v_isSharedCheck_2385_ == 0)
{
lean_object* v_unused_2386_; lean_object* v_unused_2387_; lean_object* v_unused_2388_; lean_object* v_unused_2389_; lean_object* v_unused_2390_; 
v_unused_2386_ = lean_ctor_get(v_impl_2304_, 4);
lean_dec(v_unused_2386_);
v_unused_2387_ = lean_ctor_get(v_impl_2304_, 3);
lean_dec(v_unused_2387_);
v_unused_2388_ = lean_ctor_get(v_impl_2304_, 2);
lean_dec(v_unused_2388_);
v_unused_2389_ = lean_ctor_get(v_impl_2304_, 1);
lean_dec(v_unused_2389_);
v_unused_2390_ = lean_ctor_get(v_impl_2304_, 0);
lean_dec(v_unused_2390_);
v___x_2321_ = v_impl_2304_;
v_isShared_2322_ = v_isSharedCheck_2385_;
goto v_resetjp_2320_;
}
else
{
lean_dec(v_impl_2304_);
v___x_2321_ = lean_box(0);
v_isShared_2322_ = v_isSharedCheck_2385_;
goto v_resetjp_2320_;
}
v_resetjp_2320_:
{
lean_object* v_size_2323_; lean_object* v_size_2324_; lean_object* v_k_2325_; lean_object* v_v_2326_; lean_object* v_l_2327_; lean_object* v_r_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; uint8_t v___x_2331_; 
v_size_2323_ = lean_ctor_get(v_l_2310_, 0);
v_size_2324_ = lean_ctor_get(v_r_2311_, 0);
v_k_2325_ = lean_ctor_get(v_r_2311_, 1);
v_v_2326_ = lean_ctor_get(v_r_2311_, 2);
v_l_2327_ = lean_ctor_get(v_r_2311_, 3);
v_r_2328_ = lean_ctor_get(v_r_2311_, 4);
v___x_2329_ = lean_unsigned_to_nat(2u);
v___x_2330_ = lean_nat_mul(v___x_2329_, v_size_2323_);
v___x_2331_ = lean_nat_dec_lt(v_size_2324_, v___x_2330_);
lean_dec(v___x_2330_);
if (v___x_2331_ == 0)
{
lean_object* v___x_2333_; uint8_t v_isShared_2334_; uint8_t v_isSharedCheck_2360_; 
lean_inc(v_r_2328_);
lean_inc(v_l_2327_);
lean_inc(v_v_2326_);
lean_inc(v_k_2325_);
v_isSharedCheck_2360_ = !lean_is_exclusive(v_r_2311_);
if (v_isSharedCheck_2360_ == 0)
{
lean_object* v_unused_2361_; lean_object* v_unused_2362_; lean_object* v_unused_2363_; lean_object* v_unused_2364_; lean_object* v_unused_2365_; 
v_unused_2361_ = lean_ctor_get(v_r_2311_, 4);
lean_dec(v_unused_2361_);
v_unused_2362_ = lean_ctor_get(v_r_2311_, 3);
lean_dec(v_unused_2362_);
v_unused_2363_ = lean_ctor_get(v_r_2311_, 2);
lean_dec(v_unused_2363_);
v_unused_2364_ = lean_ctor_get(v_r_2311_, 1);
lean_dec(v_unused_2364_);
v_unused_2365_ = lean_ctor_get(v_r_2311_, 0);
lean_dec(v_unused_2365_);
v___x_2333_ = v_r_2311_;
v_isShared_2334_ = v_isSharedCheck_2360_;
goto v_resetjp_2332_;
}
else
{
lean_dec(v_r_2311_);
v___x_2333_ = lean_box(0);
v_isShared_2334_ = v_isSharedCheck_2360_;
goto v_resetjp_2332_;
}
v_resetjp_2332_:
{
lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___y_2338_; lean_object* v___y_2339_; lean_object* v___y_2340_; lean_object* v___x_2348_; lean_object* v___y_2350_; 
v___x_2335_ = lean_nat_add(v___x_2305_, v_size_2307_);
lean_dec(v_size_2307_);
v___x_2336_ = lean_nat_add(v___x_2335_, v_size_2306_);
lean_dec(v___x_2335_);
v___x_2348_ = lean_nat_add(v___x_2305_, v_size_2323_);
if (lean_obj_tag(v_l_2327_) == 0)
{
lean_object* v_size_2358_; 
v_size_2358_ = lean_ctor_get(v_l_2327_, 0);
lean_inc(v_size_2358_);
v___y_2350_ = v_size_2358_;
goto v___jp_2349_;
}
else
{
lean_object* v___x_2359_; 
v___x_2359_ = lean_unsigned_to_nat(0u);
v___y_2350_ = v___x_2359_;
goto v___jp_2349_;
}
v___jp_2337_:
{
lean_object* v___x_2341_; lean_object* v___x_2343_; 
v___x_2341_ = lean_nat_add(v___y_2338_, v___y_2340_);
lean_dec(v___y_2340_);
lean_dec(v___y_2338_);
if (v_isShared_2334_ == 0)
{
lean_ctor_set(v___x_2333_, 4, v_r_2299_);
lean_ctor_set(v___x_2333_, 3, v_r_2328_);
lean_ctor_set(v___x_2333_, 2, v_v_2297_);
lean_ctor_set(v___x_2333_, 1, v_k_2296_);
lean_ctor_set(v___x_2333_, 0, v___x_2341_);
v___x_2343_ = v___x_2333_;
goto v_reusejp_2342_;
}
else
{
lean_object* v_reuseFailAlloc_2347_; 
v_reuseFailAlloc_2347_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2347_, 0, v___x_2341_);
lean_ctor_set(v_reuseFailAlloc_2347_, 1, v_k_2296_);
lean_ctor_set(v_reuseFailAlloc_2347_, 2, v_v_2297_);
lean_ctor_set(v_reuseFailAlloc_2347_, 3, v_r_2328_);
lean_ctor_set(v_reuseFailAlloc_2347_, 4, v_r_2299_);
v___x_2343_ = v_reuseFailAlloc_2347_;
goto v_reusejp_2342_;
}
v_reusejp_2342_:
{
lean_object* v___x_2345_; 
if (v_isShared_2322_ == 0)
{
lean_ctor_set(v___x_2321_, 4, v___x_2343_);
lean_ctor_set(v___x_2321_, 3, v___y_2339_);
lean_ctor_set(v___x_2321_, 2, v_v_2326_);
lean_ctor_set(v___x_2321_, 1, v_k_2325_);
lean_ctor_set(v___x_2321_, 0, v___x_2336_);
v___x_2345_ = v___x_2321_;
goto v_reusejp_2344_;
}
else
{
lean_object* v_reuseFailAlloc_2346_; 
v_reuseFailAlloc_2346_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2346_, 0, v___x_2336_);
lean_ctor_set(v_reuseFailAlloc_2346_, 1, v_k_2325_);
lean_ctor_set(v_reuseFailAlloc_2346_, 2, v_v_2326_);
lean_ctor_set(v_reuseFailAlloc_2346_, 3, v___y_2339_);
lean_ctor_set(v_reuseFailAlloc_2346_, 4, v___x_2343_);
v___x_2345_ = v_reuseFailAlloc_2346_;
goto v_reusejp_2344_;
}
v_reusejp_2344_:
{
return v___x_2345_;
}
}
}
v___jp_2349_:
{
lean_object* v___x_2351_; lean_object* v___x_2353_; 
v___x_2351_ = lean_nat_add(v___x_2348_, v___y_2350_);
lean_dec(v___y_2350_);
lean_dec(v___x_2348_);
if (v_isShared_2302_ == 0)
{
lean_ctor_set(v___x_2301_, 4, v_l_2327_);
lean_ctor_set(v___x_2301_, 3, v_l_2310_);
lean_ctor_set(v___x_2301_, 2, v_v_2309_);
lean_ctor_set(v___x_2301_, 1, v_k_2308_);
lean_ctor_set(v___x_2301_, 0, v___x_2351_);
v___x_2353_ = v___x_2301_;
goto v_reusejp_2352_;
}
else
{
lean_object* v_reuseFailAlloc_2357_; 
v_reuseFailAlloc_2357_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2357_, 0, v___x_2351_);
lean_ctor_set(v_reuseFailAlloc_2357_, 1, v_k_2308_);
lean_ctor_set(v_reuseFailAlloc_2357_, 2, v_v_2309_);
lean_ctor_set(v_reuseFailAlloc_2357_, 3, v_l_2310_);
lean_ctor_set(v_reuseFailAlloc_2357_, 4, v_l_2327_);
v___x_2353_ = v_reuseFailAlloc_2357_;
goto v_reusejp_2352_;
}
v_reusejp_2352_:
{
lean_object* v___x_2354_; 
v___x_2354_ = lean_nat_add(v___x_2305_, v_size_2306_);
if (lean_obj_tag(v_r_2328_) == 0)
{
lean_object* v_size_2355_; 
v_size_2355_ = lean_ctor_get(v_r_2328_, 0);
lean_inc(v_size_2355_);
v___y_2338_ = v___x_2354_;
v___y_2339_ = v___x_2353_;
v___y_2340_ = v_size_2355_;
goto v___jp_2337_;
}
else
{
lean_object* v___x_2356_; 
v___x_2356_ = lean_unsigned_to_nat(0u);
v___y_2338_ = v___x_2354_;
v___y_2339_ = v___x_2353_;
v___y_2340_ = v___x_2356_;
goto v___jp_2337_;
}
}
}
}
}
else
{
lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2371_; 
lean_del_object(v___x_2301_);
v___x_2366_ = lean_nat_add(v___x_2305_, v_size_2307_);
lean_dec(v_size_2307_);
v___x_2367_ = lean_nat_add(v___x_2366_, v_size_2306_);
lean_dec(v___x_2366_);
v___x_2368_ = lean_nat_add(v___x_2305_, v_size_2306_);
v___x_2369_ = lean_nat_add(v___x_2368_, v_size_2324_);
lean_dec(v___x_2368_);
lean_inc_ref(v_r_2299_);
if (v_isShared_2322_ == 0)
{
lean_ctor_set(v___x_2321_, 4, v_r_2299_);
lean_ctor_set(v___x_2321_, 3, v_r_2311_);
lean_ctor_set(v___x_2321_, 2, v_v_2297_);
lean_ctor_set(v___x_2321_, 1, v_k_2296_);
lean_ctor_set(v___x_2321_, 0, v___x_2369_);
v___x_2371_ = v___x_2321_;
goto v_reusejp_2370_;
}
else
{
lean_object* v_reuseFailAlloc_2384_; 
v_reuseFailAlloc_2384_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2384_, 0, v___x_2369_);
lean_ctor_set(v_reuseFailAlloc_2384_, 1, v_k_2296_);
lean_ctor_set(v_reuseFailAlloc_2384_, 2, v_v_2297_);
lean_ctor_set(v_reuseFailAlloc_2384_, 3, v_r_2311_);
lean_ctor_set(v_reuseFailAlloc_2384_, 4, v_r_2299_);
v___x_2371_ = v_reuseFailAlloc_2384_;
goto v_reusejp_2370_;
}
v_reusejp_2370_:
{
lean_object* v___x_2373_; uint8_t v_isShared_2374_; uint8_t v_isSharedCheck_2378_; 
v_isSharedCheck_2378_ = !lean_is_exclusive(v_r_2299_);
if (v_isSharedCheck_2378_ == 0)
{
lean_object* v_unused_2379_; lean_object* v_unused_2380_; lean_object* v_unused_2381_; lean_object* v_unused_2382_; lean_object* v_unused_2383_; 
v_unused_2379_ = lean_ctor_get(v_r_2299_, 4);
lean_dec(v_unused_2379_);
v_unused_2380_ = lean_ctor_get(v_r_2299_, 3);
lean_dec(v_unused_2380_);
v_unused_2381_ = lean_ctor_get(v_r_2299_, 2);
lean_dec(v_unused_2381_);
v_unused_2382_ = lean_ctor_get(v_r_2299_, 1);
lean_dec(v_unused_2382_);
v_unused_2383_ = lean_ctor_get(v_r_2299_, 0);
lean_dec(v_unused_2383_);
v___x_2373_ = v_r_2299_;
v_isShared_2374_ = v_isSharedCheck_2378_;
goto v_resetjp_2372_;
}
else
{
lean_dec(v_r_2299_);
v___x_2373_ = lean_box(0);
v_isShared_2374_ = v_isSharedCheck_2378_;
goto v_resetjp_2372_;
}
v_resetjp_2372_:
{
lean_object* v___x_2376_; 
if (v_isShared_2374_ == 0)
{
lean_ctor_set(v___x_2373_, 4, v___x_2371_);
lean_ctor_set(v___x_2373_, 3, v_l_2310_);
lean_ctor_set(v___x_2373_, 2, v_v_2309_);
lean_ctor_set(v___x_2373_, 1, v_k_2308_);
lean_ctor_set(v___x_2373_, 0, v___x_2367_);
v___x_2376_ = v___x_2373_;
goto v_reusejp_2375_;
}
else
{
lean_object* v_reuseFailAlloc_2377_; 
v_reuseFailAlloc_2377_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2377_, 0, v___x_2367_);
lean_ctor_set(v_reuseFailAlloc_2377_, 1, v_k_2308_);
lean_ctor_set(v_reuseFailAlloc_2377_, 2, v_v_2309_);
lean_ctor_set(v_reuseFailAlloc_2377_, 3, v_l_2310_);
lean_ctor_set(v_reuseFailAlloc_2377_, 4, v___x_2371_);
v___x_2376_ = v_reuseFailAlloc_2377_;
goto v_reusejp_2375_;
}
v_reusejp_2375_:
{
return v___x_2376_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_2391_; 
v_l_2391_ = lean_ctor_get(v_impl_2304_, 3);
if (lean_obj_tag(v_l_2391_) == 0)
{
lean_object* v_r_2392_; lean_object* v_k_2393_; lean_object* v_v_2394_; lean_object* v___x_2396_; uint8_t v_isShared_2397_; uint8_t v_isSharedCheck_2405_; 
lean_inc_ref(v_l_2391_);
v_r_2392_ = lean_ctor_get(v_impl_2304_, 4);
v_k_2393_ = lean_ctor_get(v_impl_2304_, 1);
v_v_2394_ = lean_ctor_get(v_impl_2304_, 2);
v_isSharedCheck_2405_ = !lean_is_exclusive(v_impl_2304_);
if (v_isSharedCheck_2405_ == 0)
{
lean_object* v_unused_2406_; lean_object* v_unused_2407_; 
v_unused_2406_ = lean_ctor_get(v_impl_2304_, 3);
lean_dec(v_unused_2406_);
v_unused_2407_ = lean_ctor_get(v_impl_2304_, 0);
lean_dec(v_unused_2407_);
v___x_2396_ = v_impl_2304_;
v_isShared_2397_ = v_isSharedCheck_2405_;
goto v_resetjp_2395_;
}
else
{
lean_inc(v_r_2392_);
lean_inc(v_v_2394_);
lean_inc(v_k_2393_);
lean_dec(v_impl_2304_);
v___x_2396_ = lean_box(0);
v_isShared_2397_ = v_isSharedCheck_2405_;
goto v_resetjp_2395_;
}
v_resetjp_2395_:
{
lean_object* v___x_2398_; lean_object* v___x_2400_; 
v___x_2398_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_2392_);
if (v_isShared_2397_ == 0)
{
lean_ctor_set(v___x_2396_, 3, v_r_2392_);
lean_ctor_set(v___x_2396_, 2, v_v_2297_);
lean_ctor_set(v___x_2396_, 1, v_k_2296_);
lean_ctor_set(v___x_2396_, 0, v___x_2305_);
v___x_2400_ = v___x_2396_;
goto v_reusejp_2399_;
}
else
{
lean_object* v_reuseFailAlloc_2404_; 
v_reuseFailAlloc_2404_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2404_, 0, v___x_2305_);
lean_ctor_set(v_reuseFailAlloc_2404_, 1, v_k_2296_);
lean_ctor_set(v_reuseFailAlloc_2404_, 2, v_v_2297_);
lean_ctor_set(v_reuseFailAlloc_2404_, 3, v_r_2392_);
lean_ctor_set(v_reuseFailAlloc_2404_, 4, v_r_2392_);
v___x_2400_ = v_reuseFailAlloc_2404_;
goto v_reusejp_2399_;
}
v_reusejp_2399_:
{
lean_object* v___x_2402_; 
if (v_isShared_2302_ == 0)
{
lean_ctor_set(v___x_2301_, 4, v___x_2400_);
lean_ctor_set(v___x_2301_, 3, v_l_2391_);
lean_ctor_set(v___x_2301_, 2, v_v_2394_);
lean_ctor_set(v___x_2301_, 1, v_k_2393_);
lean_ctor_set(v___x_2301_, 0, v___x_2398_);
v___x_2402_ = v___x_2301_;
goto v_reusejp_2401_;
}
else
{
lean_object* v_reuseFailAlloc_2403_; 
v_reuseFailAlloc_2403_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2403_, 0, v___x_2398_);
lean_ctor_set(v_reuseFailAlloc_2403_, 1, v_k_2393_);
lean_ctor_set(v_reuseFailAlloc_2403_, 2, v_v_2394_);
lean_ctor_set(v_reuseFailAlloc_2403_, 3, v_l_2391_);
lean_ctor_set(v_reuseFailAlloc_2403_, 4, v___x_2400_);
v___x_2402_ = v_reuseFailAlloc_2403_;
goto v_reusejp_2401_;
}
v_reusejp_2401_:
{
return v___x_2402_;
}
}
}
}
else
{
lean_object* v_r_2408_; 
v_r_2408_ = lean_ctor_get(v_impl_2304_, 4);
lean_inc(v_r_2408_);
if (lean_obj_tag(v_r_2408_) == 0)
{
lean_object* v_k_2409_; lean_object* v_v_2410_; lean_object* v___x_2412_; uint8_t v_isShared_2413_; uint8_t v_isSharedCheck_2433_; 
lean_inc(v_l_2391_);
v_k_2409_ = lean_ctor_get(v_impl_2304_, 1);
v_v_2410_ = lean_ctor_get(v_impl_2304_, 2);
v_isSharedCheck_2433_ = !lean_is_exclusive(v_impl_2304_);
if (v_isSharedCheck_2433_ == 0)
{
lean_object* v_unused_2434_; lean_object* v_unused_2435_; lean_object* v_unused_2436_; 
v_unused_2434_ = lean_ctor_get(v_impl_2304_, 4);
lean_dec(v_unused_2434_);
v_unused_2435_ = lean_ctor_get(v_impl_2304_, 3);
lean_dec(v_unused_2435_);
v_unused_2436_ = lean_ctor_get(v_impl_2304_, 0);
lean_dec(v_unused_2436_);
v___x_2412_ = v_impl_2304_;
v_isShared_2413_ = v_isSharedCheck_2433_;
goto v_resetjp_2411_;
}
else
{
lean_inc(v_v_2410_);
lean_inc(v_k_2409_);
lean_dec(v_impl_2304_);
v___x_2412_ = lean_box(0);
v_isShared_2413_ = v_isSharedCheck_2433_;
goto v_resetjp_2411_;
}
v_resetjp_2411_:
{
lean_object* v_k_2414_; lean_object* v_v_2415_; lean_object* v___x_2417_; uint8_t v_isShared_2418_; uint8_t v_isSharedCheck_2429_; 
v_k_2414_ = lean_ctor_get(v_r_2408_, 1);
v_v_2415_ = lean_ctor_get(v_r_2408_, 2);
v_isSharedCheck_2429_ = !lean_is_exclusive(v_r_2408_);
if (v_isSharedCheck_2429_ == 0)
{
lean_object* v_unused_2430_; lean_object* v_unused_2431_; lean_object* v_unused_2432_; 
v_unused_2430_ = lean_ctor_get(v_r_2408_, 4);
lean_dec(v_unused_2430_);
v_unused_2431_ = lean_ctor_get(v_r_2408_, 3);
lean_dec(v_unused_2431_);
v_unused_2432_ = lean_ctor_get(v_r_2408_, 0);
lean_dec(v_unused_2432_);
v___x_2417_ = v_r_2408_;
v_isShared_2418_ = v_isSharedCheck_2429_;
goto v_resetjp_2416_;
}
else
{
lean_inc(v_v_2415_);
lean_inc(v_k_2414_);
lean_dec(v_r_2408_);
v___x_2417_ = lean_box(0);
v_isShared_2418_ = v_isSharedCheck_2429_;
goto v_resetjp_2416_;
}
v_resetjp_2416_:
{
lean_object* v___x_2419_; lean_object* v___x_2421_; 
v___x_2419_ = lean_unsigned_to_nat(3u);
if (v_isShared_2418_ == 0)
{
lean_ctor_set(v___x_2417_, 4, v_l_2391_);
lean_ctor_set(v___x_2417_, 3, v_l_2391_);
lean_ctor_set(v___x_2417_, 2, v_v_2410_);
lean_ctor_set(v___x_2417_, 1, v_k_2409_);
lean_ctor_set(v___x_2417_, 0, v___x_2305_);
v___x_2421_ = v___x_2417_;
goto v_reusejp_2420_;
}
else
{
lean_object* v_reuseFailAlloc_2428_; 
v_reuseFailAlloc_2428_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2428_, 0, v___x_2305_);
lean_ctor_set(v_reuseFailAlloc_2428_, 1, v_k_2409_);
lean_ctor_set(v_reuseFailAlloc_2428_, 2, v_v_2410_);
lean_ctor_set(v_reuseFailAlloc_2428_, 3, v_l_2391_);
lean_ctor_set(v_reuseFailAlloc_2428_, 4, v_l_2391_);
v___x_2421_ = v_reuseFailAlloc_2428_;
goto v_reusejp_2420_;
}
v_reusejp_2420_:
{
lean_object* v___x_2423_; 
if (v_isShared_2413_ == 0)
{
lean_ctor_set(v___x_2412_, 4, v_l_2391_);
lean_ctor_set(v___x_2412_, 2, v_v_2297_);
lean_ctor_set(v___x_2412_, 1, v_k_2296_);
lean_ctor_set(v___x_2412_, 0, v___x_2305_);
v___x_2423_ = v___x_2412_;
goto v_reusejp_2422_;
}
else
{
lean_object* v_reuseFailAlloc_2427_; 
v_reuseFailAlloc_2427_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2427_, 0, v___x_2305_);
lean_ctor_set(v_reuseFailAlloc_2427_, 1, v_k_2296_);
lean_ctor_set(v_reuseFailAlloc_2427_, 2, v_v_2297_);
lean_ctor_set(v_reuseFailAlloc_2427_, 3, v_l_2391_);
lean_ctor_set(v_reuseFailAlloc_2427_, 4, v_l_2391_);
v___x_2423_ = v_reuseFailAlloc_2427_;
goto v_reusejp_2422_;
}
v_reusejp_2422_:
{
lean_object* v___x_2425_; 
if (v_isShared_2302_ == 0)
{
lean_ctor_set(v___x_2301_, 4, v___x_2423_);
lean_ctor_set(v___x_2301_, 3, v___x_2421_);
lean_ctor_set(v___x_2301_, 2, v_v_2415_);
lean_ctor_set(v___x_2301_, 1, v_k_2414_);
lean_ctor_set(v___x_2301_, 0, v___x_2419_);
v___x_2425_ = v___x_2301_;
goto v_reusejp_2424_;
}
else
{
lean_object* v_reuseFailAlloc_2426_; 
v_reuseFailAlloc_2426_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2426_, 0, v___x_2419_);
lean_ctor_set(v_reuseFailAlloc_2426_, 1, v_k_2414_);
lean_ctor_set(v_reuseFailAlloc_2426_, 2, v_v_2415_);
lean_ctor_set(v_reuseFailAlloc_2426_, 3, v___x_2421_);
lean_ctor_set(v_reuseFailAlloc_2426_, 4, v___x_2423_);
v___x_2425_ = v_reuseFailAlloc_2426_;
goto v_reusejp_2424_;
}
v_reusejp_2424_:
{
return v___x_2425_;
}
}
}
}
}
}
else
{
lean_object* v___x_2437_; lean_object* v___x_2439_; 
v___x_2437_ = lean_unsigned_to_nat(2u);
if (v_isShared_2302_ == 0)
{
lean_ctor_set(v___x_2301_, 4, v_r_2408_);
lean_ctor_set(v___x_2301_, 3, v_impl_2304_);
lean_ctor_set(v___x_2301_, 0, v___x_2437_);
v___x_2439_ = v___x_2301_;
goto v_reusejp_2438_;
}
else
{
lean_object* v_reuseFailAlloc_2440_; 
v_reuseFailAlloc_2440_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2440_, 0, v___x_2437_);
lean_ctor_set(v_reuseFailAlloc_2440_, 1, v_k_2296_);
lean_ctor_set(v_reuseFailAlloc_2440_, 2, v_v_2297_);
lean_ctor_set(v_reuseFailAlloc_2440_, 3, v_impl_2304_);
lean_ctor_set(v_reuseFailAlloc_2440_, 4, v_r_2408_);
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
case 1:
{
lean_object* v___x_2442_; 
lean_dec(v_v_2297_);
lean_dec(v_k_2296_);
if (v_isShared_2302_ == 0)
{
lean_ctor_set(v___x_2301_, 2, v_v_2293_);
lean_ctor_set(v___x_2301_, 1, v_k_2292_);
v___x_2442_ = v___x_2301_;
goto v_reusejp_2441_;
}
else
{
lean_object* v_reuseFailAlloc_2443_; 
v_reuseFailAlloc_2443_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2443_, 0, v_size_2295_);
lean_ctor_set(v_reuseFailAlloc_2443_, 1, v_k_2292_);
lean_ctor_set(v_reuseFailAlloc_2443_, 2, v_v_2293_);
lean_ctor_set(v_reuseFailAlloc_2443_, 3, v_l_2298_);
lean_ctor_set(v_reuseFailAlloc_2443_, 4, v_r_2299_);
v___x_2442_ = v_reuseFailAlloc_2443_;
goto v_reusejp_2441_;
}
v_reusejp_2441_:
{
return v___x_2442_;
}
}
default: 
{
lean_object* v_impl_2444_; lean_object* v___x_2445_; 
lean_dec(v_size_2295_);
v_impl_2444_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Level_collectMVars_spec__1___redArg(v_k_2292_, v_v_2293_, v_r_2299_);
v___x_2445_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_2298_) == 0)
{
lean_object* v_size_2446_; lean_object* v_size_2447_; lean_object* v_k_2448_; lean_object* v_v_2449_; lean_object* v_l_2450_; lean_object* v_r_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; uint8_t v___x_2454_; 
v_size_2446_ = lean_ctor_get(v_l_2298_, 0);
v_size_2447_ = lean_ctor_get(v_impl_2444_, 0);
v_k_2448_ = lean_ctor_get(v_impl_2444_, 1);
v_v_2449_ = lean_ctor_get(v_impl_2444_, 2);
v_l_2450_ = lean_ctor_get(v_impl_2444_, 3);
lean_inc(v_l_2450_);
v_r_2451_ = lean_ctor_get(v_impl_2444_, 4);
v___x_2452_ = lean_unsigned_to_nat(3u);
v___x_2453_ = lean_nat_mul(v___x_2452_, v_size_2446_);
v___x_2454_ = lean_nat_dec_lt(v___x_2453_, v_size_2447_);
lean_dec(v___x_2453_);
if (v___x_2454_ == 0)
{
lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2458_; 
lean_dec(v_l_2450_);
v___x_2455_ = lean_nat_add(v___x_2445_, v_size_2446_);
v___x_2456_ = lean_nat_add(v___x_2455_, v_size_2447_);
lean_dec(v___x_2455_);
if (v_isShared_2302_ == 0)
{
lean_ctor_set(v___x_2301_, 4, v_impl_2444_);
lean_ctor_set(v___x_2301_, 0, v___x_2456_);
v___x_2458_ = v___x_2301_;
goto v_reusejp_2457_;
}
else
{
lean_object* v_reuseFailAlloc_2459_; 
v_reuseFailAlloc_2459_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2459_, 0, v___x_2456_);
lean_ctor_set(v_reuseFailAlloc_2459_, 1, v_k_2296_);
lean_ctor_set(v_reuseFailAlloc_2459_, 2, v_v_2297_);
lean_ctor_set(v_reuseFailAlloc_2459_, 3, v_l_2298_);
lean_ctor_set(v_reuseFailAlloc_2459_, 4, v_impl_2444_);
v___x_2458_ = v_reuseFailAlloc_2459_;
goto v_reusejp_2457_;
}
v_reusejp_2457_:
{
return v___x_2458_;
}
}
else
{
lean_object* v___x_2461_; uint8_t v_isShared_2462_; uint8_t v_isSharedCheck_2523_; 
lean_inc(v_r_2451_);
lean_inc(v_v_2449_);
lean_inc(v_k_2448_);
lean_inc(v_size_2447_);
v_isSharedCheck_2523_ = !lean_is_exclusive(v_impl_2444_);
if (v_isSharedCheck_2523_ == 0)
{
lean_object* v_unused_2524_; lean_object* v_unused_2525_; lean_object* v_unused_2526_; lean_object* v_unused_2527_; lean_object* v_unused_2528_; 
v_unused_2524_ = lean_ctor_get(v_impl_2444_, 4);
lean_dec(v_unused_2524_);
v_unused_2525_ = lean_ctor_get(v_impl_2444_, 3);
lean_dec(v_unused_2525_);
v_unused_2526_ = lean_ctor_get(v_impl_2444_, 2);
lean_dec(v_unused_2526_);
v_unused_2527_ = lean_ctor_get(v_impl_2444_, 1);
lean_dec(v_unused_2527_);
v_unused_2528_ = lean_ctor_get(v_impl_2444_, 0);
lean_dec(v_unused_2528_);
v___x_2461_ = v_impl_2444_;
v_isShared_2462_ = v_isSharedCheck_2523_;
goto v_resetjp_2460_;
}
else
{
lean_dec(v_impl_2444_);
v___x_2461_ = lean_box(0);
v_isShared_2462_ = v_isSharedCheck_2523_;
goto v_resetjp_2460_;
}
v_resetjp_2460_:
{
lean_object* v_size_2463_; lean_object* v_k_2464_; lean_object* v_v_2465_; lean_object* v_l_2466_; lean_object* v_r_2467_; lean_object* v_size_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; uint8_t v___x_2471_; 
v_size_2463_ = lean_ctor_get(v_l_2450_, 0);
v_k_2464_ = lean_ctor_get(v_l_2450_, 1);
v_v_2465_ = lean_ctor_get(v_l_2450_, 2);
v_l_2466_ = lean_ctor_get(v_l_2450_, 3);
v_r_2467_ = lean_ctor_get(v_l_2450_, 4);
v_size_2468_ = lean_ctor_get(v_r_2451_, 0);
v___x_2469_ = lean_unsigned_to_nat(2u);
v___x_2470_ = lean_nat_mul(v___x_2469_, v_size_2468_);
v___x_2471_ = lean_nat_dec_lt(v_size_2463_, v___x_2470_);
lean_dec(v___x_2470_);
if (v___x_2471_ == 0)
{
lean_object* v___x_2473_; uint8_t v_isShared_2474_; uint8_t v_isSharedCheck_2499_; 
lean_inc(v_r_2467_);
lean_inc(v_l_2466_);
lean_inc(v_v_2465_);
lean_inc(v_k_2464_);
v_isSharedCheck_2499_ = !lean_is_exclusive(v_l_2450_);
if (v_isSharedCheck_2499_ == 0)
{
lean_object* v_unused_2500_; lean_object* v_unused_2501_; lean_object* v_unused_2502_; lean_object* v_unused_2503_; lean_object* v_unused_2504_; 
v_unused_2500_ = lean_ctor_get(v_l_2450_, 4);
lean_dec(v_unused_2500_);
v_unused_2501_ = lean_ctor_get(v_l_2450_, 3);
lean_dec(v_unused_2501_);
v_unused_2502_ = lean_ctor_get(v_l_2450_, 2);
lean_dec(v_unused_2502_);
v_unused_2503_ = lean_ctor_get(v_l_2450_, 1);
lean_dec(v_unused_2503_);
v_unused_2504_ = lean_ctor_get(v_l_2450_, 0);
lean_dec(v_unused_2504_);
v___x_2473_ = v_l_2450_;
v_isShared_2474_ = v_isSharedCheck_2499_;
goto v_resetjp_2472_;
}
else
{
lean_dec(v_l_2450_);
v___x_2473_ = lean_box(0);
v_isShared_2474_ = v_isSharedCheck_2499_;
goto v_resetjp_2472_;
}
v_resetjp_2472_:
{
lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___y_2478_; lean_object* v___y_2479_; lean_object* v___y_2480_; lean_object* v___y_2489_; 
v___x_2475_ = lean_nat_add(v___x_2445_, v_size_2446_);
v___x_2476_ = lean_nat_add(v___x_2475_, v_size_2447_);
lean_dec(v_size_2447_);
if (lean_obj_tag(v_l_2466_) == 0)
{
lean_object* v_size_2497_; 
v_size_2497_ = lean_ctor_get(v_l_2466_, 0);
lean_inc(v_size_2497_);
v___y_2489_ = v_size_2497_;
goto v___jp_2488_;
}
else
{
lean_object* v___x_2498_; 
v___x_2498_ = lean_unsigned_to_nat(0u);
v___y_2489_ = v___x_2498_;
goto v___jp_2488_;
}
v___jp_2477_:
{
lean_object* v___x_2481_; lean_object* v___x_2483_; 
v___x_2481_ = lean_nat_add(v___y_2478_, v___y_2480_);
lean_dec(v___y_2480_);
lean_dec(v___y_2478_);
if (v_isShared_2474_ == 0)
{
lean_ctor_set(v___x_2473_, 4, v_r_2451_);
lean_ctor_set(v___x_2473_, 3, v_r_2467_);
lean_ctor_set(v___x_2473_, 2, v_v_2449_);
lean_ctor_set(v___x_2473_, 1, v_k_2448_);
lean_ctor_set(v___x_2473_, 0, v___x_2481_);
v___x_2483_ = v___x_2473_;
goto v_reusejp_2482_;
}
else
{
lean_object* v_reuseFailAlloc_2487_; 
v_reuseFailAlloc_2487_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2487_, 0, v___x_2481_);
lean_ctor_set(v_reuseFailAlloc_2487_, 1, v_k_2448_);
lean_ctor_set(v_reuseFailAlloc_2487_, 2, v_v_2449_);
lean_ctor_set(v_reuseFailAlloc_2487_, 3, v_r_2467_);
lean_ctor_set(v_reuseFailAlloc_2487_, 4, v_r_2451_);
v___x_2483_ = v_reuseFailAlloc_2487_;
goto v_reusejp_2482_;
}
v_reusejp_2482_:
{
lean_object* v___x_2485_; 
if (v_isShared_2462_ == 0)
{
lean_ctor_set(v___x_2461_, 4, v___x_2483_);
lean_ctor_set(v___x_2461_, 3, v___y_2479_);
lean_ctor_set(v___x_2461_, 2, v_v_2465_);
lean_ctor_set(v___x_2461_, 1, v_k_2464_);
lean_ctor_set(v___x_2461_, 0, v___x_2476_);
v___x_2485_ = v___x_2461_;
goto v_reusejp_2484_;
}
else
{
lean_object* v_reuseFailAlloc_2486_; 
v_reuseFailAlloc_2486_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2486_, 0, v___x_2476_);
lean_ctor_set(v_reuseFailAlloc_2486_, 1, v_k_2464_);
lean_ctor_set(v_reuseFailAlloc_2486_, 2, v_v_2465_);
lean_ctor_set(v_reuseFailAlloc_2486_, 3, v___y_2479_);
lean_ctor_set(v_reuseFailAlloc_2486_, 4, v___x_2483_);
v___x_2485_ = v_reuseFailAlloc_2486_;
goto v_reusejp_2484_;
}
v_reusejp_2484_:
{
return v___x_2485_;
}
}
}
v___jp_2488_:
{
lean_object* v___x_2490_; lean_object* v___x_2492_; 
v___x_2490_ = lean_nat_add(v___x_2475_, v___y_2489_);
lean_dec(v___y_2489_);
lean_dec(v___x_2475_);
if (v_isShared_2302_ == 0)
{
lean_ctor_set(v___x_2301_, 4, v_l_2466_);
lean_ctor_set(v___x_2301_, 0, v___x_2490_);
v___x_2492_ = v___x_2301_;
goto v_reusejp_2491_;
}
else
{
lean_object* v_reuseFailAlloc_2496_; 
v_reuseFailAlloc_2496_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2496_, 0, v___x_2490_);
lean_ctor_set(v_reuseFailAlloc_2496_, 1, v_k_2296_);
lean_ctor_set(v_reuseFailAlloc_2496_, 2, v_v_2297_);
lean_ctor_set(v_reuseFailAlloc_2496_, 3, v_l_2298_);
lean_ctor_set(v_reuseFailAlloc_2496_, 4, v_l_2466_);
v___x_2492_ = v_reuseFailAlloc_2496_;
goto v_reusejp_2491_;
}
v_reusejp_2491_:
{
lean_object* v___x_2493_; 
v___x_2493_ = lean_nat_add(v___x_2445_, v_size_2468_);
if (lean_obj_tag(v_r_2467_) == 0)
{
lean_object* v_size_2494_; 
v_size_2494_ = lean_ctor_get(v_r_2467_, 0);
lean_inc(v_size_2494_);
v___y_2478_ = v___x_2493_;
v___y_2479_ = v___x_2492_;
v___y_2480_ = v_size_2494_;
goto v___jp_2477_;
}
else
{
lean_object* v___x_2495_; 
v___x_2495_ = lean_unsigned_to_nat(0u);
v___y_2478_ = v___x_2493_;
v___y_2479_ = v___x_2492_;
v___y_2480_ = v___x_2495_;
goto v___jp_2477_;
}
}
}
}
}
else
{
lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2509_; 
lean_del_object(v___x_2301_);
v___x_2505_ = lean_nat_add(v___x_2445_, v_size_2446_);
v___x_2506_ = lean_nat_add(v___x_2505_, v_size_2447_);
lean_dec(v_size_2447_);
v___x_2507_ = lean_nat_add(v___x_2505_, v_size_2463_);
lean_dec(v___x_2505_);
lean_inc_ref(v_l_2298_);
if (v_isShared_2462_ == 0)
{
lean_ctor_set(v___x_2461_, 4, v_l_2450_);
lean_ctor_set(v___x_2461_, 3, v_l_2298_);
lean_ctor_set(v___x_2461_, 2, v_v_2297_);
lean_ctor_set(v___x_2461_, 1, v_k_2296_);
lean_ctor_set(v___x_2461_, 0, v___x_2507_);
v___x_2509_ = v___x_2461_;
goto v_reusejp_2508_;
}
else
{
lean_object* v_reuseFailAlloc_2522_; 
v_reuseFailAlloc_2522_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2522_, 0, v___x_2507_);
lean_ctor_set(v_reuseFailAlloc_2522_, 1, v_k_2296_);
lean_ctor_set(v_reuseFailAlloc_2522_, 2, v_v_2297_);
lean_ctor_set(v_reuseFailAlloc_2522_, 3, v_l_2298_);
lean_ctor_set(v_reuseFailAlloc_2522_, 4, v_l_2450_);
v___x_2509_ = v_reuseFailAlloc_2522_;
goto v_reusejp_2508_;
}
v_reusejp_2508_:
{
lean_object* v___x_2511_; uint8_t v_isShared_2512_; uint8_t v_isSharedCheck_2516_; 
v_isSharedCheck_2516_ = !lean_is_exclusive(v_l_2298_);
if (v_isSharedCheck_2516_ == 0)
{
lean_object* v_unused_2517_; lean_object* v_unused_2518_; lean_object* v_unused_2519_; lean_object* v_unused_2520_; lean_object* v_unused_2521_; 
v_unused_2517_ = lean_ctor_get(v_l_2298_, 4);
lean_dec(v_unused_2517_);
v_unused_2518_ = lean_ctor_get(v_l_2298_, 3);
lean_dec(v_unused_2518_);
v_unused_2519_ = lean_ctor_get(v_l_2298_, 2);
lean_dec(v_unused_2519_);
v_unused_2520_ = lean_ctor_get(v_l_2298_, 1);
lean_dec(v_unused_2520_);
v_unused_2521_ = lean_ctor_get(v_l_2298_, 0);
lean_dec(v_unused_2521_);
v___x_2511_ = v_l_2298_;
v_isShared_2512_ = v_isSharedCheck_2516_;
goto v_resetjp_2510_;
}
else
{
lean_dec(v_l_2298_);
v___x_2511_ = lean_box(0);
v_isShared_2512_ = v_isSharedCheck_2516_;
goto v_resetjp_2510_;
}
v_resetjp_2510_:
{
lean_object* v___x_2514_; 
if (v_isShared_2512_ == 0)
{
lean_ctor_set(v___x_2511_, 4, v_r_2451_);
lean_ctor_set(v___x_2511_, 3, v___x_2509_);
lean_ctor_set(v___x_2511_, 2, v_v_2449_);
lean_ctor_set(v___x_2511_, 1, v_k_2448_);
lean_ctor_set(v___x_2511_, 0, v___x_2506_);
v___x_2514_ = v___x_2511_;
goto v_reusejp_2513_;
}
else
{
lean_object* v_reuseFailAlloc_2515_; 
v_reuseFailAlloc_2515_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2515_, 0, v___x_2506_);
lean_ctor_set(v_reuseFailAlloc_2515_, 1, v_k_2448_);
lean_ctor_set(v_reuseFailAlloc_2515_, 2, v_v_2449_);
lean_ctor_set(v_reuseFailAlloc_2515_, 3, v___x_2509_);
lean_ctor_set(v_reuseFailAlloc_2515_, 4, v_r_2451_);
v___x_2514_ = v_reuseFailAlloc_2515_;
goto v_reusejp_2513_;
}
v_reusejp_2513_:
{
return v___x_2514_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_2529_; 
v_l_2529_ = lean_ctor_get(v_impl_2444_, 3);
lean_inc(v_l_2529_);
if (lean_obj_tag(v_l_2529_) == 0)
{
lean_object* v_r_2530_; lean_object* v_k_2531_; lean_object* v_v_2532_; lean_object* v___x_2534_; uint8_t v_isShared_2535_; uint8_t v_isSharedCheck_2555_; 
v_r_2530_ = lean_ctor_get(v_impl_2444_, 4);
v_k_2531_ = lean_ctor_get(v_impl_2444_, 1);
v_v_2532_ = lean_ctor_get(v_impl_2444_, 2);
v_isSharedCheck_2555_ = !lean_is_exclusive(v_impl_2444_);
if (v_isSharedCheck_2555_ == 0)
{
lean_object* v_unused_2556_; lean_object* v_unused_2557_; 
v_unused_2556_ = lean_ctor_get(v_impl_2444_, 3);
lean_dec(v_unused_2556_);
v_unused_2557_ = lean_ctor_get(v_impl_2444_, 0);
lean_dec(v_unused_2557_);
v___x_2534_ = v_impl_2444_;
v_isShared_2535_ = v_isSharedCheck_2555_;
goto v_resetjp_2533_;
}
else
{
lean_inc(v_r_2530_);
lean_inc(v_v_2532_);
lean_inc(v_k_2531_);
lean_dec(v_impl_2444_);
v___x_2534_ = lean_box(0);
v_isShared_2535_ = v_isSharedCheck_2555_;
goto v_resetjp_2533_;
}
v_resetjp_2533_:
{
lean_object* v_k_2536_; lean_object* v_v_2537_; lean_object* v___x_2539_; uint8_t v_isShared_2540_; uint8_t v_isSharedCheck_2551_; 
v_k_2536_ = lean_ctor_get(v_l_2529_, 1);
v_v_2537_ = lean_ctor_get(v_l_2529_, 2);
v_isSharedCheck_2551_ = !lean_is_exclusive(v_l_2529_);
if (v_isSharedCheck_2551_ == 0)
{
lean_object* v_unused_2552_; lean_object* v_unused_2553_; lean_object* v_unused_2554_; 
v_unused_2552_ = lean_ctor_get(v_l_2529_, 4);
lean_dec(v_unused_2552_);
v_unused_2553_ = lean_ctor_get(v_l_2529_, 3);
lean_dec(v_unused_2553_);
v_unused_2554_ = lean_ctor_get(v_l_2529_, 0);
lean_dec(v_unused_2554_);
v___x_2539_ = v_l_2529_;
v_isShared_2540_ = v_isSharedCheck_2551_;
goto v_resetjp_2538_;
}
else
{
lean_inc(v_v_2537_);
lean_inc(v_k_2536_);
lean_dec(v_l_2529_);
v___x_2539_ = lean_box(0);
v_isShared_2540_ = v_isSharedCheck_2551_;
goto v_resetjp_2538_;
}
v_resetjp_2538_:
{
lean_object* v___x_2541_; lean_object* v___x_2543_; 
v___x_2541_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_2530_, 2);
if (v_isShared_2540_ == 0)
{
lean_ctor_set(v___x_2539_, 4, v_r_2530_);
lean_ctor_set(v___x_2539_, 3, v_r_2530_);
lean_ctor_set(v___x_2539_, 2, v_v_2297_);
lean_ctor_set(v___x_2539_, 1, v_k_2296_);
lean_ctor_set(v___x_2539_, 0, v___x_2445_);
v___x_2543_ = v___x_2539_;
goto v_reusejp_2542_;
}
else
{
lean_object* v_reuseFailAlloc_2550_; 
v_reuseFailAlloc_2550_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2550_, 0, v___x_2445_);
lean_ctor_set(v_reuseFailAlloc_2550_, 1, v_k_2296_);
lean_ctor_set(v_reuseFailAlloc_2550_, 2, v_v_2297_);
lean_ctor_set(v_reuseFailAlloc_2550_, 3, v_r_2530_);
lean_ctor_set(v_reuseFailAlloc_2550_, 4, v_r_2530_);
v___x_2543_ = v_reuseFailAlloc_2550_;
goto v_reusejp_2542_;
}
v_reusejp_2542_:
{
lean_object* v___x_2545_; 
lean_inc(v_r_2530_);
if (v_isShared_2535_ == 0)
{
lean_ctor_set(v___x_2534_, 3, v_r_2530_);
lean_ctor_set(v___x_2534_, 0, v___x_2445_);
v___x_2545_ = v___x_2534_;
goto v_reusejp_2544_;
}
else
{
lean_object* v_reuseFailAlloc_2549_; 
v_reuseFailAlloc_2549_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2549_, 0, v___x_2445_);
lean_ctor_set(v_reuseFailAlloc_2549_, 1, v_k_2531_);
lean_ctor_set(v_reuseFailAlloc_2549_, 2, v_v_2532_);
lean_ctor_set(v_reuseFailAlloc_2549_, 3, v_r_2530_);
lean_ctor_set(v_reuseFailAlloc_2549_, 4, v_r_2530_);
v___x_2545_ = v_reuseFailAlloc_2549_;
goto v_reusejp_2544_;
}
v_reusejp_2544_:
{
lean_object* v___x_2547_; 
if (v_isShared_2302_ == 0)
{
lean_ctor_set(v___x_2301_, 4, v___x_2545_);
lean_ctor_set(v___x_2301_, 3, v___x_2543_);
lean_ctor_set(v___x_2301_, 2, v_v_2537_);
lean_ctor_set(v___x_2301_, 1, v_k_2536_);
lean_ctor_set(v___x_2301_, 0, v___x_2541_);
v___x_2547_ = v___x_2301_;
goto v_reusejp_2546_;
}
else
{
lean_object* v_reuseFailAlloc_2548_; 
v_reuseFailAlloc_2548_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2548_, 0, v___x_2541_);
lean_ctor_set(v_reuseFailAlloc_2548_, 1, v_k_2536_);
lean_ctor_set(v_reuseFailAlloc_2548_, 2, v_v_2537_);
lean_ctor_set(v_reuseFailAlloc_2548_, 3, v___x_2543_);
lean_ctor_set(v_reuseFailAlloc_2548_, 4, v___x_2545_);
v___x_2547_ = v_reuseFailAlloc_2548_;
goto v_reusejp_2546_;
}
v_reusejp_2546_:
{
return v___x_2547_;
}
}
}
}
}
}
else
{
lean_object* v_r_2558_; 
v_r_2558_ = lean_ctor_get(v_impl_2444_, 4);
lean_inc(v_r_2558_);
if (lean_obj_tag(v_r_2558_) == 0)
{
lean_object* v_k_2559_; lean_object* v_v_2560_; lean_object* v___x_2562_; uint8_t v_isShared_2563_; uint8_t v_isSharedCheck_2571_; 
v_k_2559_ = lean_ctor_get(v_impl_2444_, 1);
v_v_2560_ = lean_ctor_get(v_impl_2444_, 2);
v_isSharedCheck_2571_ = !lean_is_exclusive(v_impl_2444_);
if (v_isSharedCheck_2571_ == 0)
{
lean_object* v_unused_2572_; lean_object* v_unused_2573_; lean_object* v_unused_2574_; 
v_unused_2572_ = lean_ctor_get(v_impl_2444_, 4);
lean_dec(v_unused_2572_);
v_unused_2573_ = lean_ctor_get(v_impl_2444_, 3);
lean_dec(v_unused_2573_);
v_unused_2574_ = lean_ctor_get(v_impl_2444_, 0);
lean_dec(v_unused_2574_);
v___x_2562_ = v_impl_2444_;
v_isShared_2563_ = v_isSharedCheck_2571_;
goto v_resetjp_2561_;
}
else
{
lean_inc(v_v_2560_);
lean_inc(v_k_2559_);
lean_dec(v_impl_2444_);
v___x_2562_ = lean_box(0);
v_isShared_2563_ = v_isSharedCheck_2571_;
goto v_resetjp_2561_;
}
v_resetjp_2561_:
{
lean_object* v___x_2564_; lean_object* v___x_2566_; 
v___x_2564_ = lean_unsigned_to_nat(3u);
if (v_isShared_2563_ == 0)
{
lean_ctor_set(v___x_2562_, 4, v_l_2529_);
lean_ctor_set(v___x_2562_, 2, v_v_2297_);
lean_ctor_set(v___x_2562_, 1, v_k_2296_);
lean_ctor_set(v___x_2562_, 0, v___x_2445_);
v___x_2566_ = v___x_2562_;
goto v_reusejp_2565_;
}
else
{
lean_object* v_reuseFailAlloc_2570_; 
v_reuseFailAlloc_2570_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2570_, 0, v___x_2445_);
lean_ctor_set(v_reuseFailAlloc_2570_, 1, v_k_2296_);
lean_ctor_set(v_reuseFailAlloc_2570_, 2, v_v_2297_);
lean_ctor_set(v_reuseFailAlloc_2570_, 3, v_l_2529_);
lean_ctor_set(v_reuseFailAlloc_2570_, 4, v_l_2529_);
v___x_2566_ = v_reuseFailAlloc_2570_;
goto v_reusejp_2565_;
}
v_reusejp_2565_:
{
lean_object* v___x_2568_; 
if (v_isShared_2302_ == 0)
{
lean_ctor_set(v___x_2301_, 4, v_r_2558_);
lean_ctor_set(v___x_2301_, 3, v___x_2566_);
lean_ctor_set(v___x_2301_, 2, v_v_2560_);
lean_ctor_set(v___x_2301_, 1, v_k_2559_);
lean_ctor_set(v___x_2301_, 0, v___x_2564_);
v___x_2568_ = v___x_2301_;
goto v_reusejp_2567_;
}
else
{
lean_object* v_reuseFailAlloc_2569_; 
v_reuseFailAlloc_2569_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2569_, 0, v___x_2564_);
lean_ctor_set(v_reuseFailAlloc_2569_, 1, v_k_2559_);
lean_ctor_set(v_reuseFailAlloc_2569_, 2, v_v_2560_);
lean_ctor_set(v_reuseFailAlloc_2569_, 3, v___x_2566_);
lean_ctor_set(v_reuseFailAlloc_2569_, 4, v_r_2558_);
v___x_2568_ = v_reuseFailAlloc_2569_;
goto v_reusejp_2567_;
}
v_reusejp_2567_:
{
return v___x_2568_;
}
}
}
}
else
{
lean_object* v___x_2575_; lean_object* v___x_2577_; 
v___x_2575_ = lean_unsigned_to_nat(2u);
if (v_isShared_2302_ == 0)
{
lean_ctor_set(v___x_2301_, 4, v_impl_2444_);
lean_ctor_set(v___x_2301_, 3, v_r_2558_);
lean_ctor_set(v___x_2301_, 0, v___x_2575_);
v___x_2577_ = v___x_2301_;
goto v_reusejp_2576_;
}
else
{
lean_object* v_reuseFailAlloc_2578_; 
v_reuseFailAlloc_2578_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2578_, 0, v___x_2575_);
lean_ctor_set(v_reuseFailAlloc_2578_, 1, v_k_2296_);
lean_ctor_set(v_reuseFailAlloc_2578_, 2, v_v_2297_);
lean_ctor_set(v_reuseFailAlloc_2578_, 3, v_r_2558_);
lean_ctor_set(v_reuseFailAlloc_2578_, 4, v_impl_2444_);
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
}
}
}
}
else
{
lean_object* v___x_2580_; lean_object* v___x_2581_; 
v___x_2580_ = lean_unsigned_to_nat(1u);
v___x_2581_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2581_, 0, v___x_2580_);
lean_ctor_set(v___x_2581_, 1, v_k_2292_);
lean_ctor_set(v___x_2581_, 2, v_v_2293_);
lean_ctor_set(v___x_2581_, 3, v_t_2294_);
lean_ctor_set(v___x_2581_, 4, v_t_2294_);
return v___x_2581_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Level_collectMVars_spec__0___redArg(lean_object* v_k_2582_, lean_object* v_t_2583_){
_start:
{
if (lean_obj_tag(v_t_2583_) == 0)
{
lean_object* v_k_2584_; lean_object* v_l_2585_; lean_object* v_r_2586_; uint8_t v___x_2587_; 
v_k_2584_ = lean_ctor_get(v_t_2583_, 1);
v_l_2585_ = lean_ctor_get(v_t_2583_, 3);
v_r_2586_ = lean_ctor_get(v_t_2583_, 4);
v___x_2587_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2582_, v_k_2584_);
switch(v___x_2587_)
{
case 0:
{
v_t_2583_ = v_l_2585_;
goto _start;
}
case 1:
{
uint8_t v___x_2589_; 
v___x_2589_ = 1;
return v___x_2589_;
}
default: 
{
v_t_2583_ = v_r_2586_;
goto _start;
}
}
}
else
{
uint8_t v___x_2591_; 
v___x_2591_ = 0;
return v___x_2591_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Level_collectMVars_spec__0___redArg___boxed(lean_object* v_k_2592_, lean_object* v_t_2593_){
_start:
{
uint8_t v_res_2594_; lean_object* v_r_2595_; 
v_res_2594_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Level_collectMVars_spec__0___redArg(v_k_2592_, v_t_2593_);
lean_dec(v_t_2593_);
lean_dec(v_k_2592_);
v_r_2595_ = lean_box(v_res_2594_);
return v_r_2595_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_collectMVars(lean_object* v_u_2596_, lean_object* v_s_2597_){
_start:
{
lean_object* v_u_2599_; lean_object* v_v_2600_; 
switch(lean_obj_tag(v_u_2596_))
{
case 1:
{
lean_object* v_a_2603_; 
v_a_2603_ = lean_ctor_get(v_u_2596_, 0);
lean_inc(v_a_2603_);
lean_dec_ref_known(v_u_2596_, 1);
v_u_2596_ = v_a_2603_;
goto _start;
}
case 2:
{
lean_object* v_a_2605_; lean_object* v_a_2606_; 
v_a_2605_ = lean_ctor_get(v_u_2596_, 0);
lean_inc(v_a_2605_);
v_a_2606_ = lean_ctor_get(v_u_2596_, 1);
lean_inc(v_a_2606_);
lean_dec_ref_known(v_u_2596_, 2);
v_u_2599_ = v_a_2605_;
v_v_2600_ = v_a_2606_;
goto v___jp_2598_;
}
case 3:
{
lean_object* v_a_2607_; lean_object* v_a_2608_; 
v_a_2607_ = lean_ctor_get(v_u_2596_, 0);
lean_inc(v_a_2607_);
v_a_2608_ = lean_ctor_get(v_u_2596_, 1);
lean_inc(v_a_2608_);
lean_dec_ref_known(v_u_2596_, 2);
v_u_2599_ = v_a_2607_;
v_v_2600_ = v_a_2608_;
goto v___jp_2598_;
}
case 5:
{
lean_object* v_a_2609_; uint8_t v___x_2610_; 
v_a_2609_ = lean_ctor_get(v_u_2596_, 0);
lean_inc(v_a_2609_);
lean_dec_ref_known(v_u_2596_, 1);
v___x_2610_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Level_collectMVars_spec__0___redArg(v_a_2609_, v_s_2597_);
if (v___x_2610_ == 0)
{
lean_object* v___x_2611_; lean_object* v___x_2612_; 
v___x_2611_ = lean_box(0);
v___x_2612_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Level_collectMVars_spec__1___redArg(v_a_2609_, v___x_2611_, v_s_2597_);
return v___x_2612_;
}
else
{
lean_dec(v_a_2609_);
return v_s_2597_;
}
}
default: 
{
lean_dec(v_u_2596_);
return v_s_2597_;
}
}
v___jp_2598_:
{
lean_object* v___x_2601_; 
v___x_2601_ = l_Lean_Level_collectMVars(v_v_2600_, v_s_2597_);
v_u_2596_ = v_u_2599_;
v_s_2597_ = v___x_2601_;
goto _start;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Level_collectMVars_spec__0(lean_object* v_00_u03b2_2613_, lean_object* v_k_2614_, lean_object* v_t_2615_){
_start:
{
uint8_t v___x_2616_; 
v___x_2616_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Level_collectMVars_spec__0___redArg(v_k_2614_, v_t_2615_);
return v___x_2616_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Level_collectMVars_spec__0___boxed(lean_object* v_00_u03b2_2617_, lean_object* v_k_2618_, lean_object* v_t_2619_){
_start:
{
uint8_t v_res_2620_; lean_object* v_r_2621_; 
v_res_2620_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Level_collectMVars_spec__0(v_00_u03b2_2617_, v_k_2618_, v_t_2619_);
lean_dec(v_t_2619_);
lean_dec(v_k_2618_);
v_r_2621_ = lean_box(v_res_2620_);
return v_r_2621_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Level_collectMVars_spec__1(lean_object* v_00_u03b2_2622_, lean_object* v_k_2623_, lean_object* v_v_2624_, lean_object* v_t_2625_, lean_object* v_hl_2626_){
_start:
{
lean_object* v___x_2627_; 
v___x_2627_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Level_collectMVars_spec__1___redArg(v_k_2623_, v_v_2624_, v_t_2625_);
return v___x_2627_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_find_x3f_visit(lean_object* v_p_2628_, lean_object* v_u_2629_){
_start:
{
lean_object* v_u_2631_; lean_object* v_v_2632_; lean_object* v___x_2635_; uint8_t v___x_2636_; 
lean_inc_ref(v_p_2628_);
lean_inc(v_u_2629_);
v___x_2635_ = lean_apply_1(v_p_2628_, v_u_2629_);
v___x_2636_ = lean_unbox(v___x_2635_);
if (v___x_2636_ == 0)
{
switch(lean_obj_tag(v_u_2629_))
{
case 1:
{
lean_object* v_a_2637_; 
v_a_2637_ = lean_ctor_get(v_u_2629_, 0);
lean_inc(v_a_2637_);
lean_dec_ref_known(v_u_2629_, 1);
v_u_2629_ = v_a_2637_;
goto _start;
}
case 2:
{
lean_object* v_a_2639_; lean_object* v_a_2640_; 
v_a_2639_ = lean_ctor_get(v_u_2629_, 0);
lean_inc(v_a_2639_);
v_a_2640_ = lean_ctor_get(v_u_2629_, 1);
lean_inc(v_a_2640_);
lean_dec_ref_known(v_u_2629_, 2);
v_u_2631_ = v_a_2639_;
v_v_2632_ = v_a_2640_;
goto v___jp_2630_;
}
case 3:
{
lean_object* v_a_2641_; lean_object* v_a_2642_; 
v_a_2641_ = lean_ctor_get(v_u_2629_, 0);
lean_inc(v_a_2641_);
v_a_2642_ = lean_ctor_get(v_u_2629_, 1);
lean_inc(v_a_2642_);
lean_dec_ref_known(v_u_2629_, 2);
v_u_2631_ = v_a_2641_;
v_v_2632_ = v_a_2642_;
goto v___jp_2630_;
}
default: 
{
lean_object* v___x_2643_; 
lean_dec(v_u_2629_);
lean_dec_ref(v_p_2628_);
v___x_2643_ = lean_box(0);
return v___x_2643_;
}
}
}
else
{
lean_object* v___x_2644_; 
lean_dec_ref(v_p_2628_);
v___x_2644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2644_, 0, v_u_2629_);
return v___x_2644_;
}
v___jp_2630_:
{
lean_object* v___x_2633_; 
lean_inc_ref(v_p_2628_);
v___x_2633_ = l___private_Lean_Level_0__Lean_Level_find_x3f_visit(v_p_2628_, v_u_2631_);
if (lean_obj_tag(v___x_2633_) == 0)
{
v_u_2629_ = v_v_2632_;
goto _start;
}
else
{
lean_dec(v_v_2632_);
lean_dec_ref(v_p_2628_);
return v___x_2633_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_find_x3f(lean_object* v_u_2645_, lean_object* v_p_2646_){
_start:
{
lean_object* v___x_2647_; 
v___x_2647_ = l___private_Lean_Level_0__Lean_Level_find_x3f_visit(v_p_2646_, v_u_2645_);
return v___x_2647_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_any(lean_object* v_u_2648_, lean_object* v_p_2649_){
_start:
{
lean_object* v___x_2650_; 
v___x_2650_ = l___private_Lean_Level_0__Lean_Level_find_x3f_visit(v_p_2649_, v_u_2648_);
if (lean_obj_tag(v___x_2650_) == 0)
{
uint8_t v___x_2651_; 
v___x_2651_ = 0;
return v___x_2651_;
}
else
{
uint8_t v___x_2652_; 
lean_dec_ref_known(v___x_2650_, 1);
v___x_2652_ = 1;
return v___x_2652_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_any___boxed(lean_object* v_u_2653_, lean_object* v_p_2654_){
_start:
{
uint8_t v_res_2655_; lean_object* v_r_2656_; 
v_res_2655_ = l_Lean_Level_any(v_u_2653_, v_p_2654_);
v_r_2656_ = lean_box(v_res_2655_);
return v_r_2656_;
}
}
LEAN_EXPORT lean_object* l_Lean_Nat_toLevel(lean_object* v_n_2657_){
_start:
{
lean_object* v___x_2658_; 
v___x_2658_ = l_Lean_Level_ofNat(v_n_2657_);
return v___x_2658_;
}
}
LEAN_EXPORT lean_object* l_Lean_Nat_toLevel___boxed(lean_object* v_n_2659_){
_start:
{
lean_object* v_res_2660_; 
v_res_2660_ = l_Lean_Nat_toLevel(v_n_2659_);
lean_dec(v_n_2659_);
return v_res_2660_;
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
