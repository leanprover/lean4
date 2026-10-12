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
uint64_t l_Lean_Level_Data_hash(uint64_t v_c_11_){
_start:
{
uint32_t v___x_12_; uint64_t v___x_13_; 
v___x_12_ = lean_uint64_to_uint32(v_c_11_);
v___x_13_ = lean_uint32_to_uint64(v___x_12_);
return v___x_13_;
}
}
LEAN_EXPORT void l_Lean_Level_Data_hash_0interp(lean_interpreter_value* stack)
{
uint64_t v_c_11_ = stack[0].m_num;
uint64_t v_res_14_;
v_res_14_ = l_Lean_Level_Data_hash(v_c_11_);
stack->m_num = v_res_14_;
}
LEAN_EXPORT lean_object* l_Lean_Level_Data_hash___boxed(lean_object* v_c_15_){
_start:
{
uint64_t v_c_boxed_16_; uint64_t v_res_17_; lean_object* v_r_18_; 
v_c_boxed_16_ = lean_unbox_uint64(v_c_15_);
lean_dec_ref(v_c_15_);
v_res_17_ = l_Lean_Level_Data_hash(v_c_boxed_16_);
v_r_18_ = lean_box_uint64(v_res_17_);
return v_r_18_;
}
}
uint32_t l_Lean_Level_Data_depth(uint64_t v_c_21_){
_start:
{
uint64_t v___x_22_; uint64_t v___x_23_; uint32_t v___x_24_; 
v___x_22_ = 40ULL;
v___x_23_ = lean_uint64_shift_right(v_c_21_, v___x_22_);
v___x_24_ = lean_uint64_to_uint32(v___x_23_);
return v___x_24_;
}
}
LEAN_EXPORT void l_Lean_Level_Data_depth_0interp(lean_interpreter_value* stack)
{
uint64_t v_c_21_ = stack[0].m_num;
uint32_t v_res_25_;
v_res_25_ = l_Lean_Level_Data_depth(v_c_21_);
stack->m_num = v_res_25_;
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
uint8_t l_Lean_Level_Data_hasMVar(uint64_t v_c_30_){
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
LEAN_EXPORT void l_Lean_Level_Data_hasMVar_0interp(lean_interpreter_value* stack)
{
uint64_t v_c_30_ = stack[0].m_num;
uint8_t v_res_36_;
v_res_36_ = l_Lean_Level_Data_hasMVar(v_c_30_);
stack->m_num = v_res_36_;
}
LEAN_EXPORT lean_object* l_Lean_Level_Data_hasMVar___boxed(lean_object* v_c_37_){
_start:
{
uint64_t v_c_boxed_38_; uint8_t v_res_39_; lean_object* v_r_40_; 
v_c_boxed_38_ = lean_unbox_uint64(v_c_37_);
lean_dec_ref(v_c_37_);
v_res_39_ = l_Lean_Level_Data_hasMVar(v_c_boxed_38_);
v_r_40_ = lean_box(v_res_39_);
return v_r_40_;
}
}
uint8_t l_Lean_Level_Data_hasParam(uint64_t v_c_41_){
_start:
{
uint64_t v___x_42_; uint64_t v___x_43_; uint64_t v___x_44_; uint64_t v___x_45_; uint8_t v___x_46_; 
v___x_42_ = 33ULL;
v___x_43_ = lean_uint64_shift_right(v_c_41_, v___x_42_);
v___x_44_ = 1ULL;
v___x_45_ = lean_uint64_land(v___x_43_, v___x_44_);
v___x_46_ = lean_uint64_dec_eq(v___x_45_, v___x_44_);
return v___x_46_;
}
}
LEAN_EXPORT void l_Lean_Level_Data_hasParam_0interp(lean_interpreter_value* stack)
{
uint64_t v_c_41_ = stack[0].m_num;
uint8_t v_res_47_;
v_res_47_ = l_Lean_Level_Data_hasParam(v_c_41_);
stack->m_num = v_res_47_;
}
LEAN_EXPORT lean_object* l_Lean_Level_Data_hasParam___boxed(lean_object* v_c_48_){
_start:
{
uint64_t v_c_boxed_49_; uint8_t v_res_50_; lean_object* v_r_51_; 
v_c_boxed_49_ = lean_unbox_uint64(v_c_48_);
lean_dec_ref(v_c_48_);
v_res_50_ = l_Lean_Level_Data_hasParam(v_c_boxed_49_);
v_r_51_ = lean_box(v_res_50_);
return v_r_51_;
}
}
LEAN_EXPORT void l_Lean_Level_mkData_0interp(lean_interpreter_value* stack)
{
uint64_t v_h_52_ = stack[0].m_num;
lean_object* v_depth_53_ = stack[1].m_obj;
uint8_t v_hasMVar_54_ = stack[2].m_num;
uint8_t v_hasParam_55_ = stack[3].m_num;
uint64_t v_res_56_;
v_res_56_ = lean_level_mk_data(v_h_52_, v_depth_53_, v_hasMVar_54_, v_hasParam_55_);
stack->m_num = v_res_56_;
}
LEAN_EXPORT lean_object* l_Lean_Level_mkData___boxed(lean_object* v_h_57_, lean_object* v_depth_58_, lean_object* v_hasMVar_59_, lean_object* v_hasParam_60_){
_start:
{
uint64_t v_h_boxed_61_; uint8_t v_hasMVar_boxed_62_; uint8_t v_hasParam_boxed_63_; uint64_t v_res_64_; lean_object* v_r_65_; 
v_h_boxed_61_ = lean_unbox_uint64(v_h_57_);
lean_dec_ref(v_h_57_);
v_hasMVar_boxed_62_ = lean_unbox(v_hasMVar_59_);
v_hasParam_boxed_63_ = lean_unbox(v_hasParam_60_);
v_res_64_ = lean_level_mk_data(v_h_boxed_61_, v_depth_58_, v_hasMVar_boxed_62_, v_hasParam_boxed_63_);
v_r_65_ = lean_box_uint64(v_res_64_);
return v_r_65_;
}
}
lean_object* l_Lean_instReprData___lam__0(uint64_t v_v_73_, lean_object* v_prec_74_){
_start:
{
lean_object* v_r_76_; lean_object* v___y_80_; lean_object* v___y_81_; lean_object* v_r_86_; lean_object* v___y_93_; lean_object* v___y_94_; lean_object* v_r_99_; lean_object* v___x_105_; uint64_t v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v_r_109_; uint32_t v___x_110_; uint32_t v___x_111_; uint8_t v___x_112_; 
v___x_105_ = ((lean_object*)(l_Lean_instReprData___lam__0___closed__5));
v___x_106_ = l_Lean_Level_Data_hash(v_v_73_);
v___x_107_ = lean_uint64_to_nat(v___x_106_);
v___x_108_ = l_Nat_reprFast(v___x_107_);
v_r_109_ = lean_string_append(v___x_105_, v___x_108_);
lean_dec_ref(v___x_108_);
v___x_110_ = l_Lean_Level_Data_depth(v_v_73_);
v___x_111_ = 0;
v___x_112_ = lean_uint32_dec_eq(v___x_110_, v___x_111_);
if (v___x_112_ == 0)
{
lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v_r_119_; 
v___x_113_ = ((lean_object*)(l_Lean_instReprData___lam__0___closed__6));
v___x_114_ = lean_string_append(v_r_109_, v___x_113_);
v___x_115_ = lean_uint32_to_nat(v___x_110_);
v___x_116_ = l_Nat_reprFast(v___x_115_);
v___x_117_ = lean_string_append(v___x_114_, v___x_116_);
lean_dec_ref(v___x_116_);
v___x_118_ = ((lean_object*)(l_Lean_instReprData___lam__0___closed__0));
v_r_119_ = lean_string_append(v___x_117_, v___x_118_);
v_r_99_ = v_r_119_;
goto v___jp_98_;
}
else
{
v_r_99_ = v_r_109_;
goto v___jp_98_;
}
v___jp_75_:
{
lean_object* v___x_77_; lean_object* v___x_78_; 
v___x_77_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_77_, 0, v_r_76_);
v___x_78_ = l_Repr_addAppParen(v___x_77_, v_prec_74_);
return v___x_78_;
}
v___jp_79_:
{
lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v_r_84_; 
v___x_82_ = lean_string_append(v___y_80_, v___y_81_);
v___x_83_ = ((lean_object*)(l_Lean_instReprData___lam__0___closed__0));
v_r_84_ = lean_string_append(v___x_82_, v___x_83_);
v_r_76_ = v_r_84_;
goto v___jp_75_;
}
v___jp_85_:
{
uint8_t v___x_87_; 
v___x_87_ = l_Lean_Level_Data_hasParam(v_v_73_);
if (v___x_87_ == 0)
{
v_r_76_ = v_r_86_;
goto v___jp_75_;
}
else
{
lean_object* v___x_88_; lean_object* v___x_89_; 
v___x_88_ = ((lean_object*)(l_Lean_instReprData___lam__0___closed__1));
v___x_89_ = lean_string_append(v_r_86_, v___x_88_);
if (v___x_87_ == 0)
{
lean_object* v___x_90_; 
v___x_90_ = ((lean_object*)(l_Lean_instReprData___lam__0___closed__2));
v___y_80_ = v___x_89_;
v___y_81_ = v___x_90_;
goto v___jp_79_;
}
else
{
lean_object* v___x_91_; 
v___x_91_ = ((lean_object*)(l_Lean_instReprData___lam__0___closed__3));
v___y_80_ = v___x_89_;
v___y_81_ = v___x_91_;
goto v___jp_79_;
}
}
}
v___jp_92_:
{
lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v_r_97_; 
v___x_95_ = lean_string_append(v___y_93_, v___y_94_);
v___x_96_ = ((lean_object*)(l_Lean_instReprData___lam__0___closed__0));
v_r_97_ = lean_string_append(v___x_95_, v___x_96_);
v_r_86_ = v_r_97_;
goto v___jp_85_;
}
v___jp_98_:
{
uint8_t v___x_100_; 
v___x_100_ = l_Lean_Level_Data_hasMVar(v_v_73_);
if (v___x_100_ == 0)
{
v_r_86_ = v_r_99_;
goto v___jp_85_;
}
else
{
lean_object* v___x_101_; lean_object* v___x_102_; 
v___x_101_ = ((lean_object*)(l_Lean_instReprData___lam__0___closed__4));
v___x_102_ = lean_string_append(v_r_99_, v___x_101_);
if (v___x_100_ == 0)
{
lean_object* v___x_103_; 
v___x_103_ = ((lean_object*)(l_Lean_instReprData___lam__0___closed__2));
v___y_93_ = v___x_102_;
v___y_94_ = v___x_103_;
goto v___jp_92_;
}
else
{
lean_object* v___x_104_; 
v___x_104_ = ((lean_object*)(l_Lean_instReprData___lam__0___closed__3));
v___y_93_ = v___x_102_;
v___y_94_ = v___x_104_;
goto v___jp_92_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_instReprData___lam__0_0interp(lean_interpreter_value* stack)
{
uint64_t v_v_73_ = stack[0].m_num;
lean_object* v_prec_74_ = stack[1].m_obj;
lean_object* v_res_120_;
v_res_120_ = l_Lean_instReprData___lam__0(v_v_73_, v_prec_74_);
stack->m_obj
 = v_res_120_;
}
LEAN_EXPORT lean_object* l_Lean_instReprData___lam__0___boxed(lean_object* v_v_121_, lean_object* v_prec_122_){
_start:
{
uint64_t v_v_boxed_123_; lean_object* v_res_124_; 
v_v_boxed_123_ = lean_unbox_uint64(v_v_121_);
lean_dec_ref(v_v_121_);
v_res_124_ = l_Lean_instReprData___lam__0(v_v_boxed_123_, v_prec_122_);
lean_dec(v_prec_122_);
return v_res_124_;
}
}
static lean_object* _init_l_Lean_instInhabitedLevelMVarId_default(void){
_start:
{
lean_object* v___x_127_; 
v___x_127_ = lean_box(0);
return v___x_127_;
}
}
static lean_object* _init_l_Lean_instInhabitedLevelMVarId(void){
_start:
{
lean_object* v___x_128_; 
v___x_128_ = lean_box(0);
return v___x_128_;
}
}
uint8_t l_Lean_instBEqLevelMVarId_beq(lean_object* v_x_129_, lean_object* v_x_130_){
_start:
{
uint8_t v___x_131_; 
v___x_131_ = lean_name_eq(v_x_129_, v_x_130_);
return v___x_131_;
}
}
LEAN_EXPORT void l_Lean_instBEqLevelMVarId_beq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_129_ = stack[0].m_obj;
lean_object* v_x_130_ = stack[1].m_obj;
uint8_t v_res_132_;
v_res_132_ = l_Lean_instBEqLevelMVarId_beq(v_x_129_, v_x_130_);
stack->m_num = v_res_132_;
}
LEAN_EXPORT lean_object* l_Lean_instBEqLevelMVarId_beq___boxed(lean_object* v_x_133_, lean_object* v_x_134_){
_start:
{
uint8_t v_res_135_; lean_object* v_r_136_; 
v_res_135_ = l_Lean_instBEqLevelMVarId_beq(v_x_133_, v_x_134_);
lean_dec(v_x_134_);
lean_dec(v_x_133_);
v_r_136_ = lean_box(v_res_135_);
return v_r_136_;
}
}
uint64_t l_Lean_instHashableLevelMVarId_hash(lean_object* v_x_139_){
_start:
{
uint64_t v___x_140_; 
v___x_140_ = 0ULL;
if (lean_obj_tag(v_x_139_) == 0)
{
uint64_t v___x_141_; 
v___x_141_ = 8934034000889494153ULL;
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
LEAN_EXPORT void l_Lean_instHashableLevelMVarId_hash_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_139_ = stack[0].m_obj;
uint64_t v_res_144_;
v_res_144_ = l_Lean_instHashableLevelMVarId_hash(v_x_139_);
stack->m_num = v_res_144_;
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
lean_object* l_Lean_instEmptyCollectionLMVarIdMap___aux__1___redArg(){
_start:
{
lean_object* v___x_245_; 
v___x_245_ = lean_box(1);
return v___x_245_;
}
}
LEAN_EXPORT void l_Lean_instEmptyCollectionLMVarIdMap___aux__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_246_;
v_res_246_ = l_Lean_instEmptyCollectionLMVarIdMap___aux__1___redArg();
stack->m_obj
 = v_res_246_;
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionLMVarIdMap___aux__1___redArg___boxed(lean_object* v___dummy_247_){
_start:
{
lean_object* v_res_248_; 
v_res_248_ = l_Lean_instEmptyCollectionLMVarIdMap___aux__1___redArg();
return v_res_248_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionLMVarIdMap___aux__1(lean_object* v_00_u03b1_249_){
_start:
{
lean_object* v___x_250_; 
v___x_250_ = lean_box(1);
return v___x_250_;
}
}
lean_object* l_Lean_instEmptyCollectionLMVarIdMap___redArg(){
_start:
{
lean_object* v___x_252_; 
v___x_252_ = lean_box(1);
return v___x_252_;
}
}
LEAN_EXPORT void l_Lean_instEmptyCollectionLMVarIdMap___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_253_;
v_res_253_ = l_Lean_instEmptyCollectionLMVarIdMap___redArg();
stack->m_obj
 = v_res_253_;
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionLMVarIdMap___redArg___boxed(lean_object* v___dummy_254_){
_start:
{
lean_object* v_res_255_; 
v_res_255_ = l_Lean_instEmptyCollectionLMVarIdMap___redArg();
return v_res_255_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionLMVarIdMap(lean_object* v_00_u03b1_256_){
_start:
{
lean_object* v___x_257_; 
v___x_257_ = lean_box(1);
return v___x_257_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInLMVarIdMapProdLMVarIdOfMonad___aux__1___redArg___lam__0(lean_object* v_f_258_, lean_object* v_a_259_, lean_object* v_b_260_, lean_object* v_c_261_){
_start:
{
lean_object* v___x_262_; lean_object* v___x_263_; 
v___x_262_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_262_, 0, v_a_259_);
lean_ctor_set(v___x_262_, 1, v_b_260_);
v___x_263_ = lean_apply_2(v_f_258_, v___x_262_, v_c_261_);
return v___x_263_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInLMVarIdMapProdLMVarIdOfMonad___aux__1___redArg(lean_object* v_inst_264_, lean_object* v_m_265_, lean_object* v_init_266_, lean_object* v_f_267_){
_start:
{
lean_object* v_toApplicative_268_; lean_object* v_toBind_269_; lean_object* v_toPure_270_; lean_object* v___f_271_; lean_object* v___x_272_; lean_object* v___f_273_; lean_object* v___x_274_; 
v_toApplicative_268_ = lean_ctor_get(v_inst_264_, 0);
v_toBind_269_ = lean_ctor_get(v_inst_264_, 1);
lean_inc(v_toBind_269_);
v_toPure_270_ = lean_ctor_get(v_toApplicative_268_, 1);
lean_inc(v_toPure_270_);
v___f_271_ = lean_alloc_closure((void*)(l_Lean_instForInLMVarIdMapProdLMVarIdOfMonad___aux__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_271_, 0, v_f_267_);
v___x_272_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_264_, v___f_271_, v_init_266_, v_m_265_);
v___f_273_ = lean_alloc_closure((void*)(l_Lean_instForInLMVarIdSetLMVarIdOfMonad___aux__1___redArg___lam__1), 2, 1);
lean_closure_set(v___f_273_, 0, v_toPure_270_);
v___x_274_ = lean_apply_4(v_toBind_269_, lean_box(0), lean_box(0), v___x_272_, v___f_273_);
return v___x_274_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInLMVarIdMapProdLMVarIdOfMonad___aux__1(lean_object* v_m_275_, lean_object* v_00_u03b1_276_, lean_object* v_inst_277_, lean_object* v_00_u03b2_278_, lean_object* v_m_279_, lean_object* v_init_280_, lean_object* v_f_281_){
_start:
{
lean_object* v_toApplicative_282_; lean_object* v_toBind_283_; lean_object* v_toPure_284_; lean_object* v___f_285_; lean_object* v___x_286_; lean_object* v___f_287_; lean_object* v___x_288_; 
v_toApplicative_282_ = lean_ctor_get(v_inst_277_, 0);
v_toBind_283_ = lean_ctor_get(v_inst_277_, 1);
lean_inc(v_toBind_283_);
v_toPure_284_ = lean_ctor_get(v_toApplicative_282_, 1);
lean_inc(v_toPure_284_);
v___f_285_ = lean_alloc_closure((void*)(l_Lean_instForInLMVarIdMapProdLMVarIdOfMonad___aux__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_285_, 0, v_f_281_);
v___x_286_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_277_, v___f_285_, v_init_280_, v_m_279_);
v___f_287_ = lean_alloc_closure((void*)(l_Lean_instForInLMVarIdSetLMVarIdOfMonad___aux__1___redArg___lam__1), 2, 1);
lean_closure_set(v___f_287_, 0, v_toPure_284_);
v___x_288_ = lean_apply_4(v_toBind_283_, lean_box(0), lean_box(0), v___x_286_, v___f_287_);
return v___x_288_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInLMVarIdMapProdLMVarIdOfMonad___redArg(lean_object* v_inst_289_){
_start:
{
lean_object* v___x_290_; 
v___x_290_ = lean_alloc_closure((void*)(l_Lean_instForInLMVarIdMapProdLMVarIdOfMonad___aux__1), 7, 3);
lean_closure_set(v___x_290_, 0, lean_box(0));
lean_closure_set(v___x_290_, 1, lean_box(0));
lean_closure_set(v___x_290_, 2, v_inst_289_);
return v___x_290_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInLMVarIdMapProdLMVarIdOfMonad(lean_object* v_m_291_, lean_object* v_00_u03b1_292_, lean_object* v_inst_293_){
_start:
{
lean_object* v___x_294_; 
v___x_294_ = lean_alloc_closure((void*)(l_Lean_instForInLMVarIdMapProdLMVarIdOfMonad___aux__1), 7, 3);
lean_closure_set(v___x_294_, 0, lean_box(0));
lean_closure_set(v___x_294_, 1, lean_box(0));
lean_closure_set(v___x_294_, 2, v_inst_293_);
return v___x_294_;
}
}
lean_object* l_Lean_instInhabitedLMVarIdMap___redArg(){
_start:
{
lean_object* v___x_296_; 
v___x_296_ = lean_box(1);
return v___x_296_;
}
}
LEAN_EXPORT void l_Lean_instInhabitedLMVarIdMap___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_297_;
v_res_297_ = l_Lean_instInhabitedLMVarIdMap___redArg();
stack->m_obj
 = v_res_297_;
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedLMVarIdMap___redArg___boxed(lean_object* v___dummy_298_){
_start:
{
lean_object* v_res_299_; 
v_res_299_ = l_Lean_instInhabitedLMVarIdMap___redArg();
return v_res_299_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedLMVarIdMap(lean_object* v_00_u03b1_300_){
_start:
{
lean_object* v___x_301_; 
v___x_301_ = lean_box(1);
return v___x_301_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_ctorIdx___impl(lean_object* v_x_302_){
_start:
{
lean_object* v___x_303_; 
v___x_303_ = lean_obj_tag_nat(v_x_302_);
return v___x_303_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_ctorIdx___impl___boxed(lean_object* v_x_304_){
_start:
{
lean_object* v_res_305_; 
v_res_305_ = l_Lean_Level_ctorIdx___impl(v_x_304_);
lean_dec(v_x_304_);
return v_res_305_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_ctorElim___redArg(lean_object* v_t_306_, lean_object* v_k_307_){
_start:
{
switch(lean_obj_tag(v_t_306_))
{
case 0:
{
return v_k_307_;
}
case 2:
{
lean_object* v_a_308_; lean_object* v_a_309_; lean_object* v___x_310_; 
v_a_308_ = lean_ctor_get(v_t_306_, 0);
lean_inc(v_a_308_);
v_a_309_ = lean_ctor_get(v_t_306_, 1);
lean_inc(v_a_309_);
lean_dec_ref_known(v_t_306_, 2);
v___x_310_ = lean_apply_2(v_k_307_, v_a_308_, v_a_309_);
return v___x_310_;
}
case 3:
{
lean_object* v_a_311_; lean_object* v_a_312_; lean_object* v___x_313_; 
v_a_311_ = lean_ctor_get(v_t_306_, 0);
lean_inc(v_a_311_);
v_a_312_ = lean_ctor_get(v_t_306_, 1);
lean_inc(v_a_312_);
lean_dec_ref_known(v_t_306_, 2);
v___x_313_ = lean_apply_2(v_k_307_, v_a_311_, v_a_312_);
return v___x_313_;
}
default: 
{
lean_object* v_a_314_; lean_object* v___x_315_; 
v_a_314_ = lean_ctor_get(v_t_306_, 0);
lean_inc(v_a_314_);
lean_dec(v_t_306_);
v___x_315_ = lean_apply_1(v_k_307_, v_a_314_);
return v___x_315_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_ctorElim(lean_object* v_motive_316_, lean_object* v_ctorIdx_317_, lean_object* v_t_318_, lean_object* v_h_319_, lean_object* v_k_320_){
_start:
{
lean_object* v___x_321_; 
v___x_321_ = l_Lean_Level_ctorElim___redArg(v_t_318_, v_k_320_);
return v___x_321_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_ctorElim___boxed(lean_object* v_motive_322_, lean_object* v_ctorIdx_323_, lean_object* v_t_324_, lean_object* v_h_325_, lean_object* v_k_326_){
_start:
{
lean_object* v_res_327_; 
v_res_327_ = l_Lean_Level_ctorElim(v_motive_322_, v_ctorIdx_323_, v_t_324_, v_h_325_, v_k_326_);
lean_dec(v_ctorIdx_323_);
return v_res_327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_zero_elim___redArg(lean_object* v_t_328_, lean_object* v_zero_329_){
_start:
{
lean_object* v___x_330_; 
v___x_330_ = l_Lean_Level_ctorElim___redArg(v_t_328_, v_zero_329_);
return v___x_330_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_zero_elim(lean_object* v_motive_331_, lean_object* v_t_332_, lean_object* v_h_333_, lean_object* v_zero_334_){
_start:
{
lean_object* v___x_335_; 
v___x_335_ = l_Lean_Level_ctorElim___redArg(v_t_332_, v_zero_334_);
return v___x_335_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_succ_elim___redArg(lean_object* v_t_336_, lean_object* v_succ_337_){
_start:
{
lean_object* v___x_338_; 
v___x_338_ = l_Lean_Level_ctorElim___redArg(v_t_336_, v_succ_337_);
return v___x_338_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_succ_elim(lean_object* v_motive_339_, lean_object* v_t_340_, lean_object* v_h_341_, lean_object* v_succ_342_){
_start:
{
lean_object* v___x_343_; 
v___x_343_ = l_Lean_Level_ctorElim___redArg(v_t_340_, v_succ_342_);
return v___x_343_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_max_elim___redArg(lean_object* v_t_344_, lean_object* v_max_345_){
_start:
{
lean_object* v___x_346_; 
v___x_346_ = l_Lean_Level_ctorElim___redArg(v_t_344_, v_max_345_);
return v___x_346_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_max_elim(lean_object* v_motive_347_, lean_object* v_t_348_, lean_object* v_h_349_, lean_object* v_max_350_){
_start:
{
lean_object* v___x_351_; 
v___x_351_ = l_Lean_Level_ctorElim___redArg(v_t_348_, v_max_350_);
return v___x_351_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_imax_elim___redArg(lean_object* v_t_352_, lean_object* v_imax_353_){
_start:
{
lean_object* v___x_354_; 
v___x_354_ = l_Lean_Level_ctorElim___redArg(v_t_352_, v_imax_353_);
return v___x_354_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_imax_elim(lean_object* v_motive_355_, lean_object* v_t_356_, lean_object* v_h_357_, lean_object* v_imax_358_){
_start:
{
lean_object* v___x_359_; 
v___x_359_ = l_Lean_Level_ctorElim___redArg(v_t_356_, v_imax_358_);
return v___x_359_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_param_elim___redArg(lean_object* v_t_360_, lean_object* v_param_361_){
_start:
{
lean_object* v___x_362_; 
v___x_362_ = l_Lean_Level_ctorElim___redArg(v_t_360_, v_param_361_);
return v___x_362_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_param_elim(lean_object* v_motive_363_, lean_object* v_t_364_, lean_object* v_h_365_, lean_object* v_param_366_){
_start:
{
lean_object* v___x_367_; 
v___x_367_ = l_Lean_Level_ctorElim___redArg(v_t_364_, v_param_366_);
return v___x_367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_mvar_elim___redArg(lean_object* v_t_368_, lean_object* v_mvar_369_){
_start:
{
lean_object* v___x_370_; 
v___x_370_ = l_Lean_Level_ctorElim___redArg(v_t_368_, v_mvar_369_);
return v___x_370_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_mvar_elim(lean_object* v_motive_371_, lean_object* v_t_372_, lean_object* v_h_373_, lean_object* v_mvar_374_){
_start:
{
lean_object* v___x_375_; 
v___x_375_ = l_Lean_Level_ctorElim___redArg(v_t_372_, v_mvar_374_);
return v___x_375_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_casesOn___override___redArg(lean_object* v_t_376_, lean_object* v_zero_377_, lean_object* v_succ_378_, lean_object* v_max_379_, lean_object* v_imax_380_, lean_object* v_param_381_, lean_object* v_mvar_382_){
_start:
{
switch(lean_obj_tag(v_t_376_))
{
case 0:
{
lean_dec(v_mvar_382_);
lean_dec(v_param_381_);
lean_dec(v_imax_380_);
lean_dec(v_max_379_);
lean_dec(v_succ_378_);
lean_inc(v_zero_377_);
return v_zero_377_;
}
case 1:
{
lean_object* v_a_383_; lean_object* v___x_384_; 
lean_dec(v_mvar_382_);
lean_dec(v_param_381_);
lean_dec(v_imax_380_);
lean_dec(v_max_379_);
v_a_383_ = lean_ctor_get(v_t_376_, 0);
lean_inc(v_a_383_);
lean_dec_ref_known(v_t_376_, 1);
v___x_384_ = lean_apply_1(v_succ_378_, v_a_383_);
return v___x_384_;
}
case 2:
{
lean_object* v_a_385_; lean_object* v_a_386_; lean_object* v___x_387_; 
lean_dec(v_mvar_382_);
lean_dec(v_param_381_);
lean_dec(v_imax_380_);
lean_dec(v_succ_378_);
v_a_385_ = lean_ctor_get(v_t_376_, 0);
lean_inc(v_a_385_);
v_a_386_ = lean_ctor_get(v_t_376_, 1);
lean_inc(v_a_386_);
lean_dec_ref_known(v_t_376_, 2);
v___x_387_ = lean_apply_2(v_max_379_, v_a_385_, v_a_386_);
return v___x_387_;
}
case 3:
{
lean_object* v_a_388_; lean_object* v_a_389_; lean_object* v___x_390_; 
lean_dec(v_mvar_382_);
lean_dec(v_param_381_);
lean_dec(v_max_379_);
lean_dec(v_succ_378_);
v_a_388_ = lean_ctor_get(v_t_376_, 0);
lean_inc(v_a_388_);
v_a_389_ = lean_ctor_get(v_t_376_, 1);
lean_inc(v_a_389_);
lean_dec_ref_known(v_t_376_, 2);
v___x_390_ = lean_apply_2(v_imax_380_, v_a_388_, v_a_389_);
return v___x_390_;
}
case 4:
{
lean_object* v_a_391_; lean_object* v___x_392_; 
lean_dec(v_mvar_382_);
lean_dec(v_imax_380_);
lean_dec(v_max_379_);
lean_dec(v_succ_378_);
v_a_391_ = lean_ctor_get(v_t_376_, 0);
lean_inc(v_a_391_);
lean_dec_ref_known(v_t_376_, 1);
v___x_392_ = lean_apply_1(v_param_381_, v_a_391_);
return v___x_392_;
}
default: 
{
lean_object* v_a_393_; lean_object* v___x_394_; 
lean_dec(v_param_381_);
lean_dec(v_imax_380_);
lean_dec(v_max_379_);
lean_dec(v_succ_378_);
v_a_393_ = lean_ctor_get(v_t_376_, 0);
lean_inc(v_a_393_);
lean_dec_ref_known(v_t_376_, 1);
v___x_394_ = lean_apply_1(v_mvar_382_, v_a_393_);
return v___x_394_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_casesOn___override___redArg___boxed(lean_object* v_t_395_, lean_object* v_zero_396_, lean_object* v_succ_397_, lean_object* v_max_398_, lean_object* v_imax_399_, lean_object* v_param_400_, lean_object* v_mvar_401_){
_start:
{
lean_object* v_res_402_; 
v_res_402_ = l_Lean_Level_casesOn___override___redArg(v_t_395_, v_zero_396_, v_succ_397_, v_max_398_, v_imax_399_, v_param_400_, v_mvar_401_);
lean_dec(v_zero_396_);
return v_res_402_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_casesOn___override(lean_object* v_motive_403_, lean_object* v_t_404_, lean_object* v_zero_405_, lean_object* v_succ_406_, lean_object* v_max_407_, lean_object* v_imax_408_, lean_object* v_param_409_, lean_object* v_mvar_410_){
_start:
{
switch(lean_obj_tag(v_t_404_))
{
case 0:
{
lean_dec(v_mvar_410_);
lean_dec(v_param_409_);
lean_dec(v_imax_408_);
lean_dec(v_max_407_);
lean_dec(v_succ_406_);
lean_inc(v_zero_405_);
return v_zero_405_;
}
case 1:
{
lean_object* v_a_411_; lean_object* v___x_412_; 
lean_dec(v_mvar_410_);
lean_dec(v_param_409_);
lean_dec(v_imax_408_);
lean_dec(v_max_407_);
v_a_411_ = lean_ctor_get(v_t_404_, 0);
lean_inc(v_a_411_);
lean_dec_ref_known(v_t_404_, 1);
v___x_412_ = lean_apply_1(v_succ_406_, v_a_411_);
return v___x_412_;
}
case 2:
{
lean_object* v_a_413_; lean_object* v_a_414_; lean_object* v___x_415_; 
lean_dec(v_mvar_410_);
lean_dec(v_param_409_);
lean_dec(v_imax_408_);
lean_dec(v_succ_406_);
v_a_413_ = lean_ctor_get(v_t_404_, 0);
lean_inc(v_a_413_);
v_a_414_ = lean_ctor_get(v_t_404_, 1);
lean_inc(v_a_414_);
lean_dec_ref_known(v_t_404_, 2);
v___x_415_ = lean_apply_2(v_max_407_, v_a_413_, v_a_414_);
return v___x_415_;
}
case 3:
{
lean_object* v_a_416_; lean_object* v_a_417_; lean_object* v___x_418_; 
lean_dec(v_mvar_410_);
lean_dec(v_param_409_);
lean_dec(v_max_407_);
lean_dec(v_succ_406_);
v_a_416_ = lean_ctor_get(v_t_404_, 0);
lean_inc(v_a_416_);
v_a_417_ = lean_ctor_get(v_t_404_, 1);
lean_inc(v_a_417_);
lean_dec_ref_known(v_t_404_, 2);
v___x_418_ = lean_apply_2(v_imax_408_, v_a_416_, v_a_417_);
return v___x_418_;
}
case 4:
{
lean_object* v_a_419_; lean_object* v___x_420_; 
lean_dec(v_mvar_410_);
lean_dec(v_imax_408_);
lean_dec(v_max_407_);
lean_dec(v_succ_406_);
v_a_419_ = lean_ctor_get(v_t_404_, 0);
lean_inc(v_a_419_);
lean_dec_ref_known(v_t_404_, 1);
v___x_420_ = lean_apply_1(v_param_409_, v_a_419_);
return v___x_420_;
}
default: 
{
lean_object* v_a_421_; lean_object* v___x_422_; 
lean_dec(v_param_409_);
lean_dec(v_imax_408_);
lean_dec(v_max_407_);
lean_dec(v_succ_406_);
v_a_421_ = lean_ctor_get(v_t_404_, 0);
lean_inc(v_a_421_);
lean_dec_ref_known(v_t_404_, 1);
v___x_422_ = lean_apply_1(v_mvar_410_, v_a_421_);
return v___x_422_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_casesOn___override___boxed(lean_object* v_motive_423_, lean_object* v_t_424_, lean_object* v_zero_425_, lean_object* v_succ_426_, lean_object* v_max_427_, lean_object* v_imax_428_, lean_object* v_param_429_, lean_object* v_mvar_430_){
_start:
{
lean_object* v_res_431_; 
v_res_431_ = l_Lean_Level_casesOn___override(v_motive_423_, v_t_424_, v_zero_425_, v_succ_426_, v_max_427_, v_imax_428_, v_param_429_, v_mvar_430_);
lean_dec(v_zero_425_);
return v_res_431_;
}
}
static lean_object* _init_l_Lean_Level_zero___override(void){
_start:
{
lean_object* v___x_432_; 
v___x_432_ = lean_box(0);
return v___x_432_;
}
}
static uint64_t _init_l_Lean_Level_data___override___closed__0(void){
_start:
{
uint8_t v___x_433_; lean_object* v___x_434_; uint64_t v___x_435_; uint64_t v___x_436_; 
v___x_433_ = 0;
v___x_434_ = lean_unsigned_to_nat(0u);
v___x_435_ = 2221ULL;
v___x_436_ = lean_level_mk_data(v___x_435_, v___x_434_, v___x_433_, v___x_433_);
return v___x_436_;
}
}
uint64_t l_Lean_Level_data___override(lean_object* v_x_437_){
_start:
{
switch(lean_obj_tag(v_x_437_))
{
case 0:
{
uint64_t v___x_438_; 
v___x_438_ = lean_uint64_once(&l_Lean_Level_data___override___closed__0, &l_Lean_Level_data___override___closed__0_once, _init_l_Lean_Level_data___override___closed__0);
return v___x_438_;
}
case 2:
{
uint64_t v_data_439_; 
v_data_439_ = lean_ctor_get_uint64(v_x_437_, sizeof(void*)*2);
return v_data_439_;
}
case 3:
{
uint64_t v_data_440_; 
v_data_440_ = lean_ctor_get_uint64(v_x_437_, sizeof(void*)*2);
return v_data_440_;
}
default: 
{
uint64_t v_data_441_; 
v_data_441_ = lean_ctor_get_uint64(v_x_437_, sizeof(void*)*1);
return v_data_441_;
}
}
}
}
LEAN_EXPORT void l_Lean_Level_data___override_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_437_ = stack[0].m_obj;
uint64_t v_res_442_;
v_res_442_ = l_Lean_Level_data___override(v_x_437_);
stack->m_num = v_res_442_;
}
LEAN_EXPORT lean_object* l_Lean_Level_data___override___boxed(lean_object* v_x_443_){
_start:
{
uint64_t v_res_444_; lean_object* v_r_445_; 
v_res_444_ = l_Lean_Level_data___override(v_x_443_);
lean_dec(v_x_443_);
v_r_445_ = lean_box_uint64(v_res_444_);
return v_r_445_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_succ___override(lean_object* v_a_446_){
_start:
{
uint64_t v___x_447_; uint64_t v___x_448_; uint64_t v___x_449_; uint64_t v___x_450_; uint32_t v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; uint8_t v___x_455_; uint8_t v___x_456_; uint64_t v___x_457_; lean_object* v___x_458_; 
v___x_447_ = 2243ULL;
v___x_448_ = l_Lean_Level_data___override(v_a_446_);
v___x_449_ = l_Lean_Level_Data_hash(v___x_448_);
v___x_450_ = lean_uint64_mix_hash(v___x_447_, v___x_449_);
v___x_451_ = l_Lean_Level_Data_depth(v___x_448_);
v___x_452_ = lean_uint32_to_nat(v___x_451_);
v___x_453_ = lean_unsigned_to_nat(1u);
v___x_454_ = lean_nat_add(v___x_452_, v___x_453_);
lean_dec(v___x_452_);
v___x_455_ = l_Lean_Level_Data_hasMVar(v___x_448_);
v___x_456_ = l_Lean_Level_Data_hasParam(v___x_448_);
v___x_457_ = lean_level_mk_data(v___x_450_, v___x_454_, v___x_455_, v___x_456_);
v___x_458_ = lean_alloc_ctor(1, 1, 8);
lean_ctor_set(v___x_458_, 0, v_a_446_);
lean_ctor_set_uint64(v___x_458_, sizeof(void*)*1, v___x_457_);
return v___x_458_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_max___override(lean_object* v_a_459_, lean_object* v_a_460_){
_start:
{
uint64_t v___x_461_; uint64_t v___x_462_; uint64_t v___x_463_; uint64_t v___x_464_; uint64_t v___x_465_; uint64_t v___x_466_; uint64_t v___x_467_; uint8_t v___y_469_; lean_object* v___y_470_; uint8_t v___y_471_; lean_object* v___y_475_; uint8_t v___y_476_; lean_object* v___y_480_; uint32_t v___x_485_; lean_object* v___x_486_; uint32_t v___x_487_; lean_object* v___x_488_; uint8_t v___x_489_; 
v___x_461_ = 2251ULL;
v___x_462_ = l_Lean_Level_data___override(v_a_459_);
v___x_463_ = l_Lean_Level_Data_hash(v___x_462_);
v___x_464_ = l_Lean_Level_data___override(v_a_460_);
v___x_465_ = l_Lean_Level_Data_hash(v___x_464_);
v___x_466_ = lean_uint64_mix_hash(v___x_463_, v___x_465_);
v___x_467_ = lean_uint64_mix_hash(v___x_461_, v___x_466_);
v___x_485_ = l_Lean_Level_Data_depth(v___x_462_);
v___x_486_ = lean_uint32_to_nat(v___x_485_);
v___x_487_ = l_Lean_Level_Data_depth(v___x_464_);
v___x_488_ = lean_uint32_to_nat(v___x_487_);
v___x_489_ = lean_nat_dec_le(v___x_486_, v___x_488_);
if (v___x_489_ == 0)
{
lean_dec(v___x_488_);
v___y_480_ = v___x_486_;
goto v___jp_479_;
}
else
{
lean_dec(v___x_486_);
v___y_480_ = v___x_488_;
goto v___jp_479_;
}
v___jp_468_:
{
uint64_t v___x_472_; lean_object* v___x_473_; 
v___x_472_ = lean_level_mk_data(v___x_467_, v___y_470_, v___y_469_, v___y_471_);
v___x_473_ = lean_alloc_ctor(2, 2, 8);
lean_ctor_set(v___x_473_, 0, v_a_459_);
lean_ctor_set(v___x_473_, 1, v_a_460_);
lean_ctor_set_uint64(v___x_473_, sizeof(void*)*2, v___x_472_);
return v___x_473_;
}
v___jp_474_:
{
uint8_t v___x_477_; 
v___x_477_ = l_Lean_Level_Data_hasParam(v___x_462_);
if (v___x_477_ == 0)
{
uint8_t v___x_478_; 
v___x_478_ = l_Lean_Level_Data_hasParam(v___x_464_);
v___y_469_ = v___y_476_;
v___y_470_ = v___y_475_;
v___y_471_ = v___x_478_;
goto v___jp_468_;
}
else
{
v___y_469_ = v___y_476_;
v___y_470_ = v___y_475_;
v___y_471_ = v___x_477_;
goto v___jp_468_;
}
}
v___jp_479_:
{
lean_object* v___x_481_; lean_object* v___x_482_; uint8_t v___x_483_; 
v___x_481_ = lean_unsigned_to_nat(1u);
v___x_482_ = lean_nat_add(v___y_480_, v___x_481_);
lean_dec(v___y_480_);
v___x_483_ = l_Lean_Level_Data_hasMVar(v___x_462_);
if (v___x_483_ == 0)
{
uint8_t v___x_484_; 
v___x_484_ = l_Lean_Level_Data_hasMVar(v___x_464_);
v___y_475_ = v___x_482_;
v___y_476_ = v___x_484_;
goto v___jp_474_;
}
else
{
v___y_475_ = v___x_482_;
v___y_476_ = v___x_483_;
goto v___jp_474_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_imax___override(lean_object* v_a_490_, lean_object* v_a_491_){
_start:
{
uint64_t v___x_492_; uint64_t v___x_493_; uint64_t v___x_494_; uint64_t v___x_495_; uint64_t v___x_496_; uint64_t v___x_497_; uint64_t v___x_498_; uint8_t v___y_500_; lean_object* v___y_501_; uint8_t v___y_502_; lean_object* v___y_506_; uint8_t v___y_507_; lean_object* v___y_511_; uint32_t v___x_516_; lean_object* v___x_517_; uint32_t v___x_518_; lean_object* v___x_519_; uint8_t v___x_520_; 
v___x_492_ = 2267ULL;
v___x_493_ = l_Lean_Level_data___override(v_a_490_);
v___x_494_ = l_Lean_Level_Data_hash(v___x_493_);
v___x_495_ = l_Lean_Level_data___override(v_a_491_);
v___x_496_ = l_Lean_Level_Data_hash(v___x_495_);
v___x_497_ = lean_uint64_mix_hash(v___x_494_, v___x_496_);
v___x_498_ = lean_uint64_mix_hash(v___x_492_, v___x_497_);
v___x_516_ = l_Lean_Level_Data_depth(v___x_493_);
v___x_517_ = lean_uint32_to_nat(v___x_516_);
v___x_518_ = l_Lean_Level_Data_depth(v___x_495_);
v___x_519_ = lean_uint32_to_nat(v___x_518_);
v___x_520_ = lean_nat_dec_le(v___x_517_, v___x_519_);
if (v___x_520_ == 0)
{
lean_dec(v___x_519_);
v___y_511_ = v___x_517_;
goto v___jp_510_;
}
else
{
lean_dec(v___x_517_);
v___y_511_ = v___x_519_;
goto v___jp_510_;
}
v___jp_499_:
{
uint64_t v___x_503_; lean_object* v___x_504_; 
v___x_503_ = lean_level_mk_data(v___x_498_, v___y_501_, v___y_500_, v___y_502_);
v___x_504_ = lean_alloc_ctor(3, 2, 8);
lean_ctor_set(v___x_504_, 0, v_a_490_);
lean_ctor_set(v___x_504_, 1, v_a_491_);
lean_ctor_set_uint64(v___x_504_, sizeof(void*)*2, v___x_503_);
return v___x_504_;
}
v___jp_505_:
{
uint8_t v___x_508_; 
v___x_508_ = l_Lean_Level_Data_hasParam(v___x_493_);
if (v___x_508_ == 0)
{
uint8_t v___x_509_; 
v___x_509_ = l_Lean_Level_Data_hasParam(v___x_495_);
v___y_500_ = v___y_507_;
v___y_501_ = v___y_506_;
v___y_502_ = v___x_509_;
goto v___jp_499_;
}
else
{
v___y_500_ = v___y_507_;
v___y_501_ = v___y_506_;
v___y_502_ = v___x_508_;
goto v___jp_499_;
}
}
v___jp_510_:
{
lean_object* v___x_512_; lean_object* v___x_513_; uint8_t v___x_514_; 
v___x_512_ = lean_unsigned_to_nat(1u);
v___x_513_ = lean_nat_add(v___y_511_, v___x_512_);
lean_dec(v___y_511_);
v___x_514_ = l_Lean_Level_Data_hasMVar(v___x_493_);
if (v___x_514_ == 0)
{
uint8_t v___x_515_; 
v___x_515_ = l_Lean_Level_Data_hasMVar(v___x_495_);
v___y_506_ = v___x_513_;
v___y_507_ = v___x_515_;
goto v___jp_505_;
}
else
{
v___y_506_ = v___x_513_;
v___y_507_ = v___x_514_;
goto v___jp_505_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_param___override(lean_object* v_a_521_){
_start:
{
uint64_t v___x_522_; uint64_t v___y_524_; 
v___x_522_ = 2239ULL;
if (lean_obj_tag(v_a_521_) == 0)
{
uint64_t v___x_531_; 
v___x_531_ = 1723ULL;
v___y_524_ = v___x_531_;
goto v___jp_523_;
}
else
{
uint64_t v_hash_532_; 
v_hash_532_ = lean_ctor_get_uint64(v_a_521_, sizeof(void*)*2);
v___y_524_ = v_hash_532_;
goto v___jp_523_;
}
v___jp_523_:
{
uint64_t v___x_525_; lean_object* v___x_526_; uint8_t v___x_527_; uint8_t v___x_528_; uint64_t v___x_529_; lean_object* v___x_530_; 
v___x_525_ = lean_uint64_mix_hash(v___x_522_, v___y_524_);
v___x_526_ = lean_unsigned_to_nat(0u);
v___x_527_ = 0;
v___x_528_ = 1;
v___x_529_ = lean_level_mk_data(v___x_525_, v___x_526_, v___x_527_, v___x_528_);
v___x_530_ = lean_alloc_ctor(4, 1, 8);
lean_ctor_set(v___x_530_, 0, v_a_521_);
lean_ctor_set_uint64(v___x_530_, sizeof(void*)*1, v___x_529_);
return v___x_530_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_mvar___override(lean_object* v_a_533_){
_start:
{
uint64_t v___x_534_; uint64_t v___x_535_; uint64_t v___x_536_; lean_object* v___x_537_; uint8_t v___x_538_; uint8_t v___x_539_; uint64_t v___x_540_; lean_object* v___x_541_; 
v___x_534_ = 2237ULL;
v___x_535_ = l_Lean_instHashableLevelMVarId_hash(v_a_533_);
v___x_536_ = lean_uint64_mix_hash(v___x_534_, v___x_535_);
v___x_537_ = lean_unsigned_to_nat(0u);
v___x_538_ = 1;
v___x_539_ = 0;
v___x_540_ = lean_level_mk_data(v___x_536_, v___x_537_, v___x_538_, v___x_539_);
v___x_541_ = lean_alloc_ctor(5, 1, 8);
lean_ctor_set(v___x_541_, 0, v_a_533_);
lean_ctor_set_uint64(v___x_541_, sizeof(void*)*1, v___x_540_);
return v___x_541_;
}
}
static lean_object* _init_l_Lean_instInhabitedLevel_default(void){
_start:
{
lean_object* v___x_542_; 
v___x_542_ = lean_box(0);
return v___x_542_;
}
}
static lean_object* _init_l_Lean_instInhabitedLevel(void){
_start:
{
lean_object* v___x_543_; 
v___x_543_ = lean_box(0);
return v___x_543_;
}
}
static lean_object* _init_l_Lean_instReprLevel_repr___closed__2(void){
_start:
{
lean_object* v___x_547_; lean_object* v___x_548_; 
v___x_547_ = lean_unsigned_to_nat(2u);
v___x_548_ = lean_nat_to_int(v___x_547_);
return v___x_548_;
}
}
static lean_object* _init_l_Lean_instReprLevel_repr___closed__3(void){
_start:
{
lean_object* v___x_549_; lean_object* v___x_550_; 
v___x_549_ = lean_unsigned_to_nat(1u);
v___x_550_ = lean_nat_to_int(v___x_549_);
return v___x_550_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprLevel_repr(lean_object* v_x_581_, lean_object* v_prec_582_){
_start:
{
lean_object* v___y_584_; 
switch(lean_obj_tag(v_x_581_))
{
case 0:
{
lean_object* v___x_590_; uint8_t v___x_591_; 
v___x_590_ = lean_unsigned_to_nat(1024u);
v___x_591_ = lean_nat_dec_le(v___x_590_, v_prec_582_);
if (v___x_591_ == 0)
{
lean_object* v___x_592_; 
v___x_592_ = lean_obj_once(&l_Lean_instReprLevel_repr___closed__2, &l_Lean_instReprLevel_repr___closed__2_once, _init_l_Lean_instReprLevel_repr___closed__2);
v___y_584_ = v___x_592_;
goto v___jp_583_;
}
else
{
lean_object* v___x_593_; 
v___x_593_ = lean_obj_once(&l_Lean_instReprLevel_repr___closed__3, &l_Lean_instReprLevel_repr___closed__3_once, _init_l_Lean_instReprLevel_repr___closed__3);
v___y_584_ = v___x_593_;
goto v___jp_583_;
}
}
case 1:
{
lean_object* v_a_594_; lean_object* v___x_595_; lean_object* v___y_597_; uint8_t v___x_605_; 
v_a_594_ = lean_ctor_get(v_x_581_, 0);
lean_inc(v_a_594_);
lean_dec_ref_known(v_x_581_, 1);
v___x_595_ = lean_unsigned_to_nat(1024u);
v___x_605_ = lean_nat_dec_le(v___x_595_, v_prec_582_);
if (v___x_605_ == 0)
{
lean_object* v___x_606_; 
v___x_606_ = lean_obj_once(&l_Lean_instReprLevel_repr___closed__2, &l_Lean_instReprLevel_repr___closed__2_once, _init_l_Lean_instReprLevel_repr___closed__2);
v___y_597_ = v___x_606_;
goto v___jp_596_;
}
else
{
lean_object* v___x_607_; 
v___x_607_ = lean_obj_once(&l_Lean_instReprLevel_repr___closed__3, &l_Lean_instReprLevel_repr___closed__3_once, _init_l_Lean_instReprLevel_repr___closed__3);
v___y_597_ = v___x_607_;
goto v___jp_596_;
}
v___jp_596_:
{
lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; uint8_t v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; 
v___x_598_ = ((lean_object*)(l_Lean_instReprLevel_repr___closed__6));
v___x_599_ = l_Lean_instReprLevel_repr(v_a_594_, v___x_595_);
v___x_600_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_600_, 0, v___x_598_);
lean_ctor_set(v___x_600_, 1, v___x_599_);
lean_inc(v___y_597_);
v___x_601_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_601_, 0, v___y_597_);
lean_ctor_set(v___x_601_, 1, v___x_600_);
v___x_602_ = 0;
v___x_603_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_603_, 0, v___x_601_);
lean_ctor_set_uint8(v___x_603_, sizeof(void*)*1, v___x_602_);
v___x_604_ = l_Repr_addAppParen(v___x_603_, v_prec_582_);
return v___x_604_;
}
}
case 2:
{
lean_object* v_a_608_; lean_object* v_a_609_; lean_object* v___x_610_; lean_object* v___y_612_; uint8_t v___x_624_; 
v_a_608_ = lean_ctor_get(v_x_581_, 0);
lean_inc(v_a_608_);
v_a_609_ = lean_ctor_get(v_x_581_, 1);
lean_inc(v_a_609_);
lean_dec_ref_known(v_x_581_, 2);
v___x_610_ = lean_unsigned_to_nat(1024u);
v___x_624_ = lean_nat_dec_le(v___x_610_, v_prec_582_);
if (v___x_624_ == 0)
{
lean_object* v___x_625_; 
v___x_625_ = lean_obj_once(&l_Lean_instReprLevel_repr___closed__2, &l_Lean_instReprLevel_repr___closed__2_once, _init_l_Lean_instReprLevel_repr___closed__2);
v___y_612_ = v___x_625_;
goto v___jp_611_;
}
else
{
lean_object* v___x_626_; 
v___x_626_ = lean_obj_once(&l_Lean_instReprLevel_repr___closed__3, &l_Lean_instReprLevel_repr___closed__3_once, _init_l_Lean_instReprLevel_repr___closed__3);
v___y_612_ = v___x_626_;
goto v___jp_611_;
}
v___jp_611_:
{
lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; uint8_t v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; 
v___x_613_ = lean_box(1);
v___x_614_ = ((lean_object*)(l_Lean_instReprLevel_repr___closed__9));
v___x_615_ = l_Lean_instReprLevel_repr(v_a_608_, v___x_610_);
v___x_616_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_616_, 0, v___x_614_);
lean_ctor_set(v___x_616_, 1, v___x_615_);
v___x_617_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_617_, 0, v___x_616_);
lean_ctor_set(v___x_617_, 1, v___x_613_);
v___x_618_ = l_Lean_instReprLevel_repr(v_a_609_, v___x_610_);
v___x_619_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_619_, 0, v___x_617_);
lean_ctor_set(v___x_619_, 1, v___x_618_);
lean_inc(v___y_612_);
v___x_620_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_620_, 0, v___y_612_);
lean_ctor_set(v___x_620_, 1, v___x_619_);
v___x_621_ = 0;
v___x_622_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_622_, 0, v___x_620_);
lean_ctor_set_uint8(v___x_622_, sizeof(void*)*1, v___x_621_);
v___x_623_ = l_Repr_addAppParen(v___x_622_, v_prec_582_);
return v___x_623_;
}
}
case 3:
{
lean_object* v_a_627_; lean_object* v_a_628_; lean_object* v___x_629_; lean_object* v___y_631_; uint8_t v___x_643_; 
v_a_627_ = lean_ctor_get(v_x_581_, 0);
lean_inc(v_a_627_);
v_a_628_ = lean_ctor_get(v_x_581_, 1);
lean_inc(v_a_628_);
lean_dec_ref_known(v_x_581_, 2);
v___x_629_ = lean_unsigned_to_nat(1024u);
v___x_643_ = lean_nat_dec_le(v___x_629_, v_prec_582_);
if (v___x_643_ == 0)
{
lean_object* v___x_644_; 
v___x_644_ = lean_obj_once(&l_Lean_instReprLevel_repr___closed__2, &l_Lean_instReprLevel_repr___closed__2_once, _init_l_Lean_instReprLevel_repr___closed__2);
v___y_631_ = v___x_644_;
goto v___jp_630_;
}
else
{
lean_object* v___x_645_; 
v___x_645_ = lean_obj_once(&l_Lean_instReprLevel_repr___closed__3, &l_Lean_instReprLevel_repr___closed__3_once, _init_l_Lean_instReprLevel_repr___closed__3);
v___y_631_ = v___x_645_;
goto v___jp_630_;
}
v___jp_630_:
{
lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; uint8_t v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; 
v___x_632_ = lean_box(1);
v___x_633_ = ((lean_object*)(l_Lean_instReprLevel_repr___closed__12));
v___x_634_ = l_Lean_instReprLevel_repr(v_a_627_, v___x_629_);
v___x_635_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_635_, 0, v___x_633_);
lean_ctor_set(v___x_635_, 1, v___x_634_);
v___x_636_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_636_, 0, v___x_635_);
lean_ctor_set(v___x_636_, 1, v___x_632_);
v___x_637_ = l_Lean_instReprLevel_repr(v_a_628_, v___x_629_);
v___x_638_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_638_, 0, v___x_636_);
lean_ctor_set(v___x_638_, 1, v___x_637_);
lean_inc(v___y_631_);
v___x_639_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_639_, 0, v___y_631_);
lean_ctor_set(v___x_639_, 1, v___x_638_);
v___x_640_ = 0;
v___x_641_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_641_, 0, v___x_639_);
lean_ctor_set_uint8(v___x_641_, sizeof(void*)*1, v___x_640_);
v___x_642_ = l_Repr_addAppParen(v___x_641_, v_prec_582_);
return v___x_642_;
}
}
case 4:
{
lean_object* v_a_646_; lean_object* v___y_648_; lean_object* v___x_657_; uint8_t v___x_658_; 
v_a_646_ = lean_ctor_get(v_x_581_, 0);
lean_inc(v_a_646_);
lean_dec_ref_known(v_x_581_, 1);
v___x_657_ = lean_unsigned_to_nat(1024u);
v___x_658_ = lean_nat_dec_le(v___x_657_, v_prec_582_);
if (v___x_658_ == 0)
{
lean_object* v___x_659_; 
v___x_659_ = lean_obj_once(&l_Lean_instReprLevel_repr___closed__2, &l_Lean_instReprLevel_repr___closed__2_once, _init_l_Lean_instReprLevel_repr___closed__2);
v___y_648_ = v___x_659_;
goto v___jp_647_;
}
else
{
lean_object* v___x_660_; 
v___x_660_ = lean_obj_once(&l_Lean_instReprLevel_repr___closed__3, &l_Lean_instReprLevel_repr___closed__3_once, _init_l_Lean_instReprLevel_repr___closed__3);
v___y_648_ = v___x_660_;
goto v___jp_647_;
}
v___jp_647_:
{
lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; uint8_t v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; 
v___x_649_ = ((lean_object*)(l_Lean_instReprLevel_repr___closed__15));
v___x_650_ = lean_unsigned_to_nat(1024u);
v___x_651_ = l_Lean_Name_reprPrec(v_a_646_, v___x_650_);
v___x_652_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_652_, 0, v___x_649_);
lean_ctor_set(v___x_652_, 1, v___x_651_);
lean_inc(v___y_648_);
v___x_653_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_653_, 0, v___y_648_);
lean_ctor_set(v___x_653_, 1, v___x_652_);
v___x_654_ = 0;
v___x_655_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_655_, 0, v___x_653_);
lean_ctor_set_uint8(v___x_655_, sizeof(void*)*1, v___x_654_);
v___x_656_ = l_Repr_addAppParen(v___x_655_, v_prec_582_);
return v___x_656_;
}
}
default: 
{
lean_object* v_a_661_; lean_object* v___y_663_; lean_object* v___x_672_; uint8_t v___x_673_; 
v_a_661_ = lean_ctor_get(v_x_581_, 0);
lean_inc(v_a_661_);
lean_dec_ref_known(v_x_581_, 1);
v___x_672_ = lean_unsigned_to_nat(1024u);
v___x_673_ = lean_nat_dec_le(v___x_672_, v_prec_582_);
if (v___x_673_ == 0)
{
lean_object* v___x_674_; 
v___x_674_ = lean_obj_once(&l_Lean_instReprLevel_repr___closed__2, &l_Lean_instReprLevel_repr___closed__2_once, _init_l_Lean_instReprLevel_repr___closed__2);
v___y_663_ = v___x_674_;
goto v___jp_662_;
}
else
{
lean_object* v___x_675_; 
v___x_675_ = lean_obj_once(&l_Lean_instReprLevel_repr___closed__3, &l_Lean_instReprLevel_repr___closed__3_once, _init_l_Lean_instReprLevel_repr___closed__3);
v___y_663_ = v___x_675_;
goto v___jp_662_;
}
v___jp_662_:
{
lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; uint8_t v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; 
v___x_664_ = ((lean_object*)(l_Lean_instReprLevel_repr___closed__18));
v___x_665_ = lean_unsigned_to_nat(1024u);
v___x_666_ = l_Lean_Name_reprPrec(v_a_661_, v___x_665_);
v___x_667_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_667_, 0, v___x_664_);
lean_ctor_set(v___x_667_, 1, v___x_666_);
lean_inc(v___y_663_);
v___x_668_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_668_, 0, v___y_663_);
lean_ctor_set(v___x_668_, 1, v___x_667_);
v___x_669_ = 0;
v___x_670_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_670_, 0, v___x_668_);
lean_ctor_set_uint8(v___x_670_, sizeof(void*)*1, v___x_669_);
v___x_671_ = l_Repr_addAppParen(v___x_670_, v_prec_582_);
return v___x_671_;
}
}
}
v___jp_583_:
{
lean_object* v___x_585_; lean_object* v___x_586_; uint8_t v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; 
v___x_585_ = ((lean_object*)(l_Lean_instReprLevel_repr___closed__1));
lean_inc(v___y_584_);
v___x_586_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_586_, 0, v___y_584_);
lean_ctor_set(v___x_586_, 1, v___x_585_);
v___x_587_ = 0;
v___x_588_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_588_, 0, v___x_586_);
lean_ctor_set_uint8(v___x_588_, sizeof(void*)*1, v___x_587_);
v___x_589_ = l_Repr_addAppParen(v___x_588_, v_prec_582_);
return v___x_589_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instReprLevel_repr___boxed(lean_object* v_x_676_, lean_object* v_prec_677_){
_start:
{
lean_object* v_res_678_; 
v_res_678_ = l_Lean_instReprLevel_repr(v_x_676_, v_prec_677_);
lean_dec(v_prec_677_);
return v_res_678_;
}
}
uint64_t l_Lean_Level_hash(lean_object* v_u_681_){
_start:
{
uint64_t v___x_682_; uint64_t v___x_683_; 
v___x_682_ = l_Lean_Level_data___override(v_u_681_);
v___x_683_ = l_Lean_Level_Data_hash(v___x_682_);
return v___x_683_;
}
}
LEAN_EXPORT void l_Lean_Level_hash_0interp(lean_interpreter_value* stack)
{
lean_object* v_u_681_ = stack[0].m_obj;
uint64_t v_res_684_;
v_res_684_ = l_Lean_Level_hash(v_u_681_);
stack->m_num = v_res_684_;
}
LEAN_EXPORT lean_object* l_Lean_Level_hash___boxed(lean_object* v_u_685_){
_start:
{
uint64_t v_res_686_; lean_object* v_r_687_; 
v_res_686_ = l_Lean_Level_hash(v_u_685_);
lean_dec(v_u_685_);
v_r_687_ = lean_box_uint64(v_res_686_);
return v_r_687_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_depth(lean_object* v_u_690_){
_start:
{
uint64_t v___x_691_; uint32_t v___x_692_; lean_object* v___x_693_; 
v___x_691_ = l_Lean_Level_data___override(v_u_690_);
v___x_692_ = l_Lean_Level_Data_depth(v___x_691_);
v___x_693_ = lean_uint32_to_nat(v___x_692_);
return v___x_693_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_depth___boxed(lean_object* v_u_694_){
_start:
{
lean_object* v_res_695_; 
v_res_695_ = l_Lean_Level_depth(v_u_694_);
lean_dec(v_u_694_);
return v_res_695_;
}
}
uint8_t l_Lean_Level_hasMVar(lean_object* v_u_696_){
_start:
{
uint64_t v___x_697_; uint8_t v___x_698_; 
v___x_697_ = l_Lean_Level_data___override(v_u_696_);
v___x_698_ = l_Lean_Level_Data_hasMVar(v___x_697_);
return v___x_698_;
}
}
LEAN_EXPORT void l_Lean_Level_hasMVar_0interp(lean_interpreter_value* stack)
{
lean_object* v_u_696_ = stack[0].m_obj;
uint8_t v_res_699_;
v_res_699_ = l_Lean_Level_hasMVar(v_u_696_);
stack->m_num = v_res_699_;
}
LEAN_EXPORT lean_object* l_Lean_Level_hasMVar___boxed(lean_object* v_u_700_){
_start:
{
uint8_t v_res_701_; lean_object* v_r_702_; 
v_res_701_ = l_Lean_Level_hasMVar(v_u_700_);
lean_dec(v_u_700_);
v_r_702_ = lean_box(v_res_701_);
return v_r_702_;
}
}
uint8_t l_Lean_Level_hasParam(lean_object* v_u_703_){
_start:
{
uint64_t v___x_704_; uint8_t v___x_705_; 
v___x_704_ = l_Lean_Level_data___override(v_u_703_);
v___x_705_ = l_Lean_Level_Data_hasParam(v___x_704_);
return v___x_705_;
}
}
LEAN_EXPORT void l_Lean_Level_hasParam_0interp(lean_interpreter_value* stack)
{
lean_object* v_u_703_ = stack[0].m_obj;
uint8_t v_res_706_;
v_res_706_ = l_Lean_Level_hasParam(v_u_703_);
stack->m_num = v_res_706_;
}
LEAN_EXPORT lean_object* l_Lean_Level_hasParam___boxed(lean_object* v_u_707_){
_start:
{
uint8_t v_res_708_; lean_object* v_r_709_; 
v_res_708_ = l_Lean_Level_hasParam(v_u_707_);
lean_dec(v_u_707_);
v_r_709_ = lean_box(v_res_708_);
return v_r_709_;
}
}
uint32_t lean_level_hash(lean_object* v_u_710_){
_start:
{
uint64_t v___x_711_; uint32_t v___x_712_; 
v___x_711_ = l_Lean_Level_hash(v_u_710_);
lean_dec(v_u_710_);
v___x_712_ = lean_uint64_to_uint32(v___x_711_);
return v___x_712_;
}
}
LEAN_EXPORT void lean_level_hash_0interp(lean_interpreter_value* stack)
{
lean_object* v_u_710_ = stack[0].m_obj;
uint32_t v_res_713_;
v_res_713_ = lean_level_hash(v_u_710_);
stack->m_num = v_res_713_;
}
LEAN_EXPORT lean_object* l_Lean_Level_hashEx___boxed(lean_object* v_u_714_){
_start:
{
uint32_t v_res_715_; lean_object* v_r_716_; 
v_res_715_ = lean_level_hash(v_u_714_);
v_r_716_ = lean_box_uint32(v_res_715_);
return v_r_716_;
}
}
uint8_t lean_level_has_mvar(lean_object* v_u_717_){
_start:
{
uint8_t v___x_718_; 
v___x_718_ = l_Lean_Level_hasMVar(v_u_717_);
lean_dec(v_u_717_);
return v___x_718_;
}
}
LEAN_EXPORT void lean_level_has_mvar_0interp(lean_interpreter_value* stack)
{
lean_object* v_u_717_ = stack[0].m_obj;
uint8_t v_res_719_;
v_res_719_ = lean_level_has_mvar(v_u_717_);
stack->m_num = v_res_719_;
}
LEAN_EXPORT lean_object* l_Lean_Level_hasMVarEx___boxed(lean_object* v_u_720_){
_start:
{
uint8_t v_res_721_; lean_object* v_r_722_; 
v_res_721_ = lean_level_has_mvar(v_u_720_);
v_r_722_ = lean_box(v_res_721_);
return v_r_722_;
}
}
uint8_t lean_level_has_param(lean_object* v_u_723_){
_start:
{
uint8_t v___x_724_; 
v___x_724_ = l_Lean_Level_hasParam(v_u_723_);
lean_dec(v_u_723_);
return v___x_724_;
}
}
LEAN_EXPORT void lean_level_has_param_0interp(lean_interpreter_value* stack)
{
lean_object* v_u_723_ = stack[0].m_obj;
uint8_t v_res_725_;
v_res_725_ = lean_level_has_param(v_u_723_);
stack->m_num = v_res_725_;
}
LEAN_EXPORT lean_object* l_Lean_Level_hasParamEx___boxed(lean_object* v_u_726_){
_start:
{
uint8_t v_res_727_; lean_object* v_r_728_; 
v_res_727_ = lean_level_has_param(v_u_726_);
v_r_728_ = lean_box(v_res_727_);
return v_r_728_;
}
}
uint32_t lean_level_depth(lean_object* v_u_729_){
_start:
{
uint64_t v___x_730_; uint32_t v___x_731_; 
v___x_730_ = l_Lean_Level_data___override(v_u_729_);
lean_dec(v_u_729_);
v___x_731_ = l_Lean_Level_Data_depth(v___x_730_);
return v___x_731_;
}
}
LEAN_EXPORT void lean_level_depth_0interp(lean_interpreter_value* stack)
{
lean_object* v_u_729_ = stack[0].m_obj;
uint32_t v_res_732_;
v_res_732_ = lean_level_depth(v_u_729_);
stack->m_num = v_res_732_;
}
LEAN_EXPORT lean_object* l_Lean_Level_depthEx___boxed(lean_object* v_u_733_){
_start:
{
uint32_t v_res_734_; lean_object* v_r_735_; 
v_res_734_ = lean_level_depth(v_u_733_);
v_r_735_ = lean_box_uint32(v_res_734_);
return v_r_735_;
}
}
static lean_object* _init_l_Lean_levelZero(void){
_start:
{
lean_object* v___x_736_; 
v___x_736_ = lean_box(0);
return v___x_736_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLevelMVar(lean_object* v_mvarId_737_){
_start:
{
lean_object* v___x_738_; 
v___x_738_ = l_Lean_Level_mvar___override(v_mvarId_737_);
return v___x_738_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLevelParam(lean_object* v_name_739_){
_start:
{
lean_object* v___x_740_; 
v___x_740_ = l_Lean_Level_param___override(v_name_739_);
return v___x_740_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLevelSucc(lean_object* v_u_741_){
_start:
{
lean_object* v___x_742_; 
v___x_742_ = l_Lean_Level_succ___override(v_u_741_);
return v___x_742_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLevelMax(lean_object* v_u_743_, lean_object* v_v_744_){
_start:
{
lean_object* v___x_745_; 
v___x_745_ = l_Lean_Level_max___override(v_u_743_, v_v_744_);
return v___x_745_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLevelIMax(lean_object* v_u_746_, lean_object* v_v_747_){
_start:
{
lean_object* v___x_748_; 
v___x_748_ = l_Lean_Level_imax___override(v_u_746_, v_v_747_);
return v___x_748_;
}
}
static lean_object* _init_l_Lean_Level_one___closed__0(void){
_start:
{
lean_object* v___x_749_; lean_object* v___x_750_; 
v___x_749_ = lean_box(0);
v___x_750_ = l_Lean_Level_succ___override(v___x_749_);
return v___x_750_;
}
}
static lean_object* _init_l_Lean_Level_one(void){
_start:
{
lean_object* v___x_751_; 
v___x_751_ = lean_obj_once(&l_Lean_Level_one___closed__0, &l_Lean_Level_one___closed__0_once, _init_l_Lean_Level_one___closed__0);
return v___x_751_;
}
}
static lean_object* _init_l_Lean_levelOne(void){
_start:
{
lean_object* v___x_752_; 
v___x_752_ = lean_obj_once(&l_Lean_Level_one___closed__0, &l_Lean_Level_one___closed__0_once, _init_l_Lean_Level_one___closed__0);
return v___x_752_;
}
}
lean_object* l_Lean_mkLevelZeroEx___redArg(){
_start:
{
lean_object* v___x_754_; 
v___x_754_ = lean_box(0);
return v___x_754_;
}
}
LEAN_EXPORT void l_Lean_mkLevelZeroEx___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_755_;
v_res_755_ = l_Lean_mkLevelZeroEx___redArg();
stack->m_obj
 = v_res_755_;
}
LEAN_EXPORT lean_object* l_Lean_mkLevelZeroEx___redArg___boxed(lean_object* v___dummy_756_){
_start:
{
lean_object* v_res_757_; 
v_res_757_ = l_Lean_mkLevelZeroEx___redArg();
return v_res_757_;
}
}
LEAN_EXPORT lean_object* lean_level_mk_zero(lean_object* v_x_758_){
_start:
{
lean_object* v___x_759_; 
v___x_759_ = lean_box(0);
return v___x_759_;
}
}
LEAN_EXPORT lean_object* lean_level_mk_succ(lean_object* v_u_760_){
_start:
{
lean_object* v___x_761_; 
v___x_761_ = l_Lean_Level_succ___override(v_u_760_);
return v___x_761_;
}
}
LEAN_EXPORT lean_object* lean_level_mk_param(lean_object* v_name_762_){
_start:
{
lean_object* v___x_763_; 
v___x_763_ = l_Lean_Level_param___override(v_name_762_);
return v___x_763_;
}
}
LEAN_EXPORT lean_object* lean_level_mk_max(lean_object* v_u_764_, lean_object* v_v_765_){
_start:
{
lean_object* v___x_766_; 
v___x_766_ = l_Lean_Level_max___override(v_u_764_, v_v_765_);
return v___x_766_;
}
}
LEAN_EXPORT lean_object* lean_level_mk_imax(lean_object* v_u_767_, lean_object* v_v_768_){
_start:
{
lean_object* v___x_769_; 
v___x_769_ = l_Lean_Level_imax___override(v_u_767_, v_v_768_);
return v___x_769_;
}
}
uint8_t l_Lean_Level_isZero(lean_object* v_x_770_){
_start:
{
if (lean_obj_tag(v_x_770_) == 0)
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
LEAN_EXPORT void l_Lean_Level_isZero_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_770_ = stack[0].m_obj;
uint8_t v_res_773_;
v_res_773_ = l_Lean_Level_isZero(v_x_770_);
stack->m_num = v_res_773_;
}
LEAN_EXPORT lean_object* l_Lean_Level_isZero___boxed(lean_object* v_x_774_){
_start:
{
uint8_t v_res_775_; lean_object* v_r_776_; 
v_res_775_ = l_Lean_Level_isZero(v_x_774_);
lean_dec(v_x_774_);
v_r_776_ = lean_box(v_res_775_);
return v_r_776_;
}
}
uint8_t l_Lean_Level_isSucc(lean_object* v_x_777_){
_start:
{
if (lean_obj_tag(v_x_777_) == 1)
{
uint8_t v___x_778_; 
v___x_778_ = 1;
return v___x_778_;
}
else
{
uint8_t v___x_779_; 
v___x_779_ = 0;
return v___x_779_;
}
}
}
LEAN_EXPORT void l_Lean_Level_isSucc_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_777_ = stack[0].m_obj;
uint8_t v_res_780_;
v_res_780_ = l_Lean_Level_isSucc(v_x_777_);
stack->m_num = v_res_780_;
}
LEAN_EXPORT lean_object* l_Lean_Level_isSucc___boxed(lean_object* v_x_781_){
_start:
{
uint8_t v_res_782_; lean_object* v_r_783_; 
v_res_782_ = l_Lean_Level_isSucc(v_x_781_);
lean_dec(v_x_781_);
v_r_783_ = lean_box(v_res_782_);
return v_r_783_;
}
}
uint8_t l_Lean_Level_isMax(lean_object* v_x_784_){
_start:
{
if (lean_obj_tag(v_x_784_) == 2)
{
uint8_t v___x_785_; 
v___x_785_ = 1;
return v___x_785_;
}
else
{
uint8_t v___x_786_; 
v___x_786_ = 0;
return v___x_786_;
}
}
}
LEAN_EXPORT void l_Lean_Level_isMax_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_784_ = stack[0].m_obj;
uint8_t v_res_787_;
v_res_787_ = l_Lean_Level_isMax(v_x_784_);
stack->m_num = v_res_787_;
}
LEAN_EXPORT lean_object* l_Lean_Level_isMax___boxed(lean_object* v_x_788_){
_start:
{
uint8_t v_res_789_; lean_object* v_r_790_; 
v_res_789_ = l_Lean_Level_isMax(v_x_788_);
lean_dec(v_x_788_);
v_r_790_ = lean_box(v_res_789_);
return v_r_790_;
}
}
uint8_t l_Lean_Level_isIMax(lean_object* v_x_791_){
_start:
{
if (lean_obj_tag(v_x_791_) == 3)
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
LEAN_EXPORT void l_Lean_Level_isIMax_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_791_ = stack[0].m_obj;
uint8_t v_res_794_;
v_res_794_ = l_Lean_Level_isIMax(v_x_791_);
stack->m_num = v_res_794_;
}
LEAN_EXPORT lean_object* l_Lean_Level_isIMax___boxed(lean_object* v_x_795_){
_start:
{
uint8_t v_res_796_; lean_object* v_r_797_; 
v_res_796_ = l_Lean_Level_isIMax(v_x_795_);
lean_dec(v_x_795_);
v_r_797_ = lean_box(v_res_796_);
return v_r_797_;
}
}
uint8_t l_Lean_Level_isMaxIMax(lean_object* v_x_798_){
_start:
{
switch(lean_obj_tag(v_x_798_))
{
case 2:
{
uint8_t v___x_799_; 
v___x_799_ = 1;
return v___x_799_;
}
case 3:
{
uint8_t v___x_800_; 
v___x_800_ = 1;
return v___x_800_;
}
default: 
{
uint8_t v___x_801_; 
v___x_801_ = 0;
return v___x_801_;
}
}
}
}
LEAN_EXPORT void l_Lean_Level_isMaxIMax_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_798_ = stack[0].m_obj;
uint8_t v_res_802_;
v_res_802_ = l_Lean_Level_isMaxIMax(v_x_798_);
stack->m_num = v_res_802_;
}
LEAN_EXPORT lean_object* l_Lean_Level_isMaxIMax___boxed(lean_object* v_x_803_){
_start:
{
uint8_t v_res_804_; lean_object* v_r_805_; 
v_res_804_ = l_Lean_Level_isMaxIMax(v_x_803_);
lean_dec(v_x_803_);
v_r_805_ = lean_box(v_res_804_);
return v_r_805_;
}
}
uint8_t l_Lean_Level_isParam(lean_object* v_x_806_){
_start:
{
if (lean_obj_tag(v_x_806_) == 4)
{
uint8_t v___x_807_; 
v___x_807_ = 1;
return v___x_807_;
}
else
{
uint8_t v___x_808_; 
v___x_808_ = 0;
return v___x_808_;
}
}
}
LEAN_EXPORT void l_Lean_Level_isParam_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_806_ = stack[0].m_obj;
uint8_t v_res_809_;
v_res_809_ = l_Lean_Level_isParam(v_x_806_);
stack->m_num = v_res_809_;
}
LEAN_EXPORT lean_object* l_Lean_Level_isParam___boxed(lean_object* v_x_810_){
_start:
{
uint8_t v_res_811_; lean_object* v_r_812_; 
v_res_811_ = l_Lean_Level_isParam(v_x_810_);
lean_dec(v_x_810_);
v_r_812_ = lean_box(v_res_811_);
return v_r_812_;
}
}
uint8_t l_Lean_Level_isMVar(lean_object* v_x_813_){
_start:
{
if (lean_obj_tag(v_x_813_) == 5)
{
uint8_t v___x_814_; 
v___x_814_ = 1;
return v___x_814_;
}
else
{
uint8_t v___x_815_; 
v___x_815_ = 0;
return v___x_815_;
}
}
}
LEAN_EXPORT void l_Lean_Level_isMVar_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_813_ = stack[0].m_obj;
uint8_t v_res_816_;
v_res_816_ = l_Lean_Level_isMVar(v_x_813_);
stack->m_num = v_res_816_;
}
LEAN_EXPORT lean_object* l_Lean_Level_isMVar___boxed(lean_object* v_x_817_){
_start:
{
uint8_t v_res_818_; lean_object* v_r_819_; 
v_res_818_ = l_Lean_Level_isMVar(v_x_817_);
lean_dec(v_x_817_);
v_r_819_ = lean_box(v_res_818_);
return v_r_819_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Level_mvarId_x21_spec__0(lean_object* v_msg_820_){
_start:
{
lean_object* v___x_821_; lean_object* v___x_822_; 
v___x_821_ = lean_box(0);
v___x_822_ = lean_panic_fn_borrowed(v___x_821_, v_msg_820_);
return v___x_822_;
}
}
static lean_object* _init_l_Lean_Level_mvarId_x21___closed__3(void){
_start:
{
lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; 
v___x_826_ = ((lean_object*)(l_Lean_Level_mvarId_x21___closed__2));
v___x_827_ = lean_unsigned_to_nat(19u);
v___x_828_ = lean_unsigned_to_nat(195u);
v___x_829_ = ((lean_object*)(l_Lean_Level_mvarId_x21___closed__1));
v___x_830_ = ((lean_object*)(l_Lean_Level_mvarId_x21___closed__0));
v___x_831_ = l_mkPanicMessageWithDecl(v___x_830_, v___x_829_, v___x_828_, v___x_827_, v___x_826_);
return v___x_831_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_mvarId_x21(lean_object* v_x_832_){
_start:
{
if (lean_obj_tag(v_x_832_) == 5)
{
lean_object* v_a_833_; 
v_a_833_ = lean_ctor_get(v_x_832_, 0);
lean_inc(v_a_833_);
return v_a_833_;
}
else
{
lean_object* v___x_834_; lean_object* v___x_835_; 
v___x_834_ = lean_obj_once(&l_Lean_Level_mvarId_x21___closed__3, &l_Lean_Level_mvarId_x21___closed__3_once, _init_l_Lean_Level_mvarId_x21___closed__3);
v___x_835_ = l_panic___at___00Lean_Level_mvarId_x21_spec__0(v___x_834_);
return v___x_835_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_mvarId_x21___boxed(lean_object* v_x_836_){
_start:
{
lean_object* v_res_837_; 
v_res_837_ = l_Lean_Level_mvarId_x21(v_x_836_);
lean_dec(v_x_836_);
return v_res_837_;
}
}
uint8_t l_Lean_Level_isNeverZero(lean_object* v_x_838_){
_start:
{
switch(lean_obj_tag(v_x_838_))
{
case 1:
{
uint8_t v___x_839_; 
v___x_839_ = 1;
return v___x_839_;
}
case 2:
{
lean_object* v_a_840_; lean_object* v_a_841_; uint8_t v___x_842_; 
v_a_840_ = lean_ctor_get(v_x_838_, 0);
v_a_841_ = lean_ctor_get(v_x_838_, 1);
v___x_842_ = l_Lean_Level_isNeverZero(v_a_840_);
if (v___x_842_ == 0)
{
v_x_838_ = v_a_841_;
goto _start;
}
else
{
return v___x_842_;
}
}
case 3:
{
lean_object* v_a_844_; 
v_a_844_ = lean_ctor_get(v_x_838_, 1);
v_x_838_ = v_a_844_;
goto _start;
}
default: 
{
uint8_t v___x_846_; 
v___x_846_ = 0;
return v___x_846_;
}
}
}
}
LEAN_EXPORT void l_Lean_Level_isNeverZero_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_838_ = stack[0].m_obj;
uint8_t v_res_847_;
v_res_847_ = l_Lean_Level_isNeverZero(v_x_838_);
stack->m_num = v_res_847_;
}
LEAN_EXPORT lean_object* l_Lean_Level_isNeverZero___boxed(lean_object* v_x_848_){
_start:
{
uint8_t v_res_849_; lean_object* v_r_850_; 
v_res_849_ = l_Lean_Level_isNeverZero(v_x_848_);
lean_dec(v_x_848_);
v_r_850_ = lean_box(v_res_849_);
return v_r_850_;
}
}
uint8_t l_Lean_Level_isAlwaysZero(lean_object* v_x_851_){
_start:
{
switch(lean_obj_tag(v_x_851_))
{
case 0:
{
uint8_t v___x_852_; 
v___x_852_ = 1;
return v___x_852_;
}
case 2:
{
lean_object* v_a_853_; lean_object* v_a_854_; uint8_t v___x_855_; 
v_a_853_ = lean_ctor_get(v_x_851_, 0);
v_a_854_ = lean_ctor_get(v_x_851_, 1);
v___x_855_ = l_Lean_Level_isAlwaysZero(v_a_853_);
if (v___x_855_ == 0)
{
return v___x_855_;
}
else
{
v_x_851_ = v_a_854_;
goto _start;
}
}
case 3:
{
lean_object* v_a_857_; 
v_a_857_ = lean_ctor_get(v_x_851_, 1);
v_x_851_ = v_a_857_;
goto _start;
}
default: 
{
uint8_t v___x_859_; 
v___x_859_ = 0;
return v___x_859_;
}
}
}
}
LEAN_EXPORT void l_Lean_Level_isAlwaysZero_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_851_ = stack[0].m_obj;
uint8_t v_res_860_;
v_res_860_ = l_Lean_Level_isAlwaysZero(v_x_851_);
stack->m_num = v_res_860_;
}
LEAN_EXPORT lean_object* l_Lean_Level_isAlwaysZero___boxed(lean_object* v_x_861_){
_start:
{
uint8_t v_res_862_; lean_object* v_r_863_; 
v_res_862_ = l_Lean_Level_isAlwaysZero(v_x_861_);
lean_dec(v_x_861_);
v_r_863_ = lean_box(v_res_862_);
return v_r_863_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_ofNat(lean_object* v_x_864_){
_start:
{
lean_object* v_zero_865_; uint8_t v_isZero_866_; 
v_zero_865_ = lean_unsigned_to_nat(0u);
v_isZero_866_ = lean_nat_dec_eq(v_x_864_, v_zero_865_);
if (v_isZero_866_ == 1)
{
lean_object* v___x_867_; 
v___x_867_ = lean_box(0);
return v___x_867_;
}
else
{
lean_object* v_one_868_; lean_object* v_n_869_; lean_object* v___x_870_; lean_object* v___x_871_; 
v_one_868_ = lean_unsigned_to_nat(1u);
v_n_869_ = lean_nat_sub(v_x_864_, v_one_868_);
v___x_870_ = l_Lean_Level_ofNat(v_n_869_);
lean_dec(v_n_869_);
v___x_871_ = l_Lean_Level_succ___override(v___x_870_);
return v___x_871_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_ofNat___boxed(lean_object* v_x_872_){
_start:
{
lean_object* v_res_873_; 
v_res_873_ = l_Lean_Level_ofNat(v_x_872_);
lean_dec(v_x_872_);
return v_res_873_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_instOfNat(lean_object* v_n_874_){
_start:
{
lean_object* v___x_875_; 
v___x_875_ = l_Lean_Level_ofNat(v_n_874_);
return v___x_875_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_instOfNat___boxed(lean_object* v_n_876_){
_start:
{
lean_object* v_res_877_; 
v_res_877_ = l_Lean_Level_instOfNat(v_n_876_);
lean_dec(v_n_876_);
return v_res_877_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_addOffsetAux(lean_object* v_x_878_, lean_object* v_x_879_){
_start:
{
lean_object* v_zero_880_; uint8_t v_isZero_881_; 
v_zero_880_ = lean_unsigned_to_nat(0u);
v_isZero_881_ = lean_nat_dec_eq(v_x_878_, v_zero_880_);
if (v_isZero_881_ == 1)
{
lean_dec(v_x_878_);
return v_x_879_;
}
else
{
lean_object* v_one_882_; lean_object* v_n_883_; lean_object* v___x_884_; 
v_one_882_ = lean_unsigned_to_nat(1u);
v_n_883_ = lean_nat_sub(v_x_878_, v_one_882_);
lean_dec(v_x_878_);
v___x_884_ = l_Lean_Level_succ___override(v_x_879_);
v_x_878_ = v_n_883_;
v_x_879_ = v___x_884_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_addOffset(lean_object* v_u_886_, lean_object* v_n_887_){
_start:
{
lean_object* v___x_888_; 
v___x_888_ = l_Lean_Level_addOffsetAux(v_n_887_, v_u_886_);
return v___x_888_;
}
}
uint8_t l_Lean_Level_isExplicit(lean_object* v_x_889_){
_start:
{
switch(lean_obj_tag(v_x_889_))
{
case 0:
{
uint8_t v___x_890_; 
v___x_890_ = 1;
return v___x_890_;
}
case 1:
{
lean_object* v_a_891_; uint8_t v___x_892_; 
v_a_891_ = lean_ctor_get(v_x_889_, 0);
v___x_892_ = l_Lean_Level_hasMVar(v_a_891_);
if (v___x_892_ == 0)
{
uint8_t v___x_893_; 
v___x_893_ = l_Lean_Level_hasParam(v_a_891_);
if (v___x_893_ == 0)
{
v_x_889_ = v_a_891_;
goto _start;
}
else
{
return v___x_892_;
}
}
else
{
uint8_t v___x_895_; 
v___x_895_ = 0;
return v___x_895_;
}
}
default: 
{
uint8_t v___x_896_; 
v___x_896_ = 0;
return v___x_896_;
}
}
}
}
LEAN_EXPORT void l_Lean_Level_isExplicit_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_889_ = stack[0].m_obj;
uint8_t v_res_897_;
v_res_897_ = l_Lean_Level_isExplicit(v_x_889_);
stack->m_num = v_res_897_;
}
LEAN_EXPORT lean_object* l_Lean_Level_isExplicit___boxed(lean_object* v_x_898_){
_start:
{
uint8_t v_res_899_; lean_object* v_r_900_; 
v_res_899_ = l_Lean_Level_isExplicit(v_x_898_);
lean_dec(v_x_898_);
v_r_900_ = lean_box(v_res_899_);
return v_r_900_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_getOffsetAux(lean_object* v_x_901_, lean_object* v_x_902_){
_start:
{
if (lean_obj_tag(v_x_901_) == 1)
{
lean_object* v_a_903_; lean_object* v___x_904_; lean_object* v___x_905_; 
v_a_903_ = lean_ctor_get(v_x_901_, 0);
v___x_904_ = lean_unsigned_to_nat(1u);
v___x_905_ = lean_nat_add(v_x_902_, v___x_904_);
lean_dec(v_x_902_);
v_x_901_ = v_a_903_;
v_x_902_ = v___x_905_;
goto _start;
}
else
{
return v_x_902_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_getOffsetAux___boxed(lean_object* v_x_907_, lean_object* v_x_908_){
_start:
{
lean_object* v_res_909_; 
v_res_909_ = l_Lean_Level_getOffsetAux(v_x_907_, v_x_908_);
lean_dec(v_x_907_);
return v_res_909_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_getOffset(lean_object* v_lvl_910_){
_start:
{
lean_object* v___x_911_; lean_object* v___x_912_; 
v___x_911_ = lean_unsigned_to_nat(0u);
v___x_912_ = l_Lean_Level_getOffsetAux(v_lvl_910_, v___x_911_);
return v___x_912_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_getOffset___boxed(lean_object* v_lvl_913_){
_start:
{
lean_object* v_res_914_; 
v_res_914_ = l_Lean_Level_getOffset(v_lvl_913_);
lean_dec(v_lvl_913_);
return v_res_914_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_getLevelOffset(lean_object* v_x_915_){
_start:
{
if (lean_obj_tag(v_x_915_) == 1)
{
lean_object* v_a_916_; 
v_a_916_ = lean_ctor_get(v_x_915_, 0);
v_x_915_ = v_a_916_;
goto _start;
}
else
{
lean_inc(v_x_915_);
return v_x_915_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_getLevelOffset___boxed(lean_object* v_x_918_){
_start:
{
lean_object* v_res_919_; 
v_res_919_ = l_Lean_Level_getLevelOffset(v_x_918_);
lean_dec(v_x_918_);
return v_res_919_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_toNat(lean_object* v_lvl_920_){
_start:
{
lean_object* v___x_921_; 
v___x_921_ = l_Lean_Level_getLevelOffset(v_lvl_920_);
if (lean_obj_tag(v___x_921_) == 0)
{
lean_object* v___x_922_; lean_object* v___x_923_; 
v___x_922_ = l_Lean_Level_getOffset(v_lvl_920_);
v___x_923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_923_, 0, v___x_922_);
return v___x_923_;
}
else
{
lean_object* v___x_924_; 
lean_dec(v___x_921_);
v___x_924_ = lean_box(0);
return v___x_924_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_toNat___boxed(lean_object* v_lvl_925_){
_start:
{
lean_object* v_res_926_; 
v_res_926_ = l_Lean_Level_toNat(v_lvl_925_);
lean_dec(v_lvl_925_);
return v_res_926_;
}
}
LEAN_EXPORT void l_Lean_Level_beq_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_927_ = stack[0].m_obj;
lean_object* v_b_928_ = stack[1].m_obj;
uint8_t v_res_929_;
v_res_929_ = lean_level_eq(v_a_927_, v_b_928_);
stack->m_num = v_res_929_;
}
LEAN_EXPORT lean_object* l_Lean_Level_beq___boxed(lean_object* v_a_930_, lean_object* v_b_931_){
_start:
{
uint8_t v_res_932_; lean_object* v_r_933_; 
v_res_932_ = lean_level_eq(v_a_930_, v_b_931_);
lean_dec(v_b_931_);
lean_dec(v_a_930_);
v_r_933_ = lean_box(v_res_932_);
return v_r_933_;
}
}
uint8_t l_Lean_Level_occurs(lean_object* v_x_936_, lean_object* v_x_937_){
_start:
{
switch(lean_obj_tag(v_x_937_))
{
case 1:
{
lean_object* v_a_938_; uint8_t v___x_939_; 
v_a_938_ = lean_ctor_get(v_x_937_, 0);
v___x_939_ = lean_level_eq(v_x_936_, v_x_937_);
if (v___x_939_ == 0)
{
v_x_937_ = v_a_938_;
goto _start;
}
else
{
return v___x_939_;
}
}
case 2:
{
lean_object* v_a_941_; lean_object* v_a_942_; uint8_t v___y_944_; uint8_t v___x_946_; 
v_a_941_ = lean_ctor_get(v_x_937_, 0);
v_a_942_ = lean_ctor_get(v_x_937_, 1);
v___x_946_ = lean_level_eq(v_x_936_, v_x_937_);
if (v___x_946_ == 0)
{
uint8_t v___x_947_; 
v___x_947_ = l_Lean_Level_occurs(v_x_936_, v_a_941_);
v___y_944_ = v___x_947_;
goto v___jp_943_;
}
else
{
v___y_944_ = v___x_946_;
goto v___jp_943_;
}
v___jp_943_:
{
if (v___y_944_ == 0)
{
v_x_937_ = v_a_942_;
goto _start;
}
else
{
return v___y_944_;
}
}
}
case 3:
{
lean_object* v_a_948_; lean_object* v_a_949_; uint8_t v___y_951_; uint8_t v___x_953_; 
v_a_948_ = lean_ctor_get(v_x_937_, 0);
v_a_949_ = lean_ctor_get(v_x_937_, 1);
v___x_953_ = lean_level_eq(v_x_936_, v_x_937_);
if (v___x_953_ == 0)
{
uint8_t v___x_954_; 
v___x_954_ = l_Lean_Level_occurs(v_x_936_, v_a_948_);
v___y_951_ = v___x_954_;
goto v___jp_950_;
}
else
{
v___y_951_ = v___x_953_;
goto v___jp_950_;
}
v___jp_950_:
{
if (v___y_951_ == 0)
{
v_x_937_ = v_a_949_;
goto _start;
}
else
{
return v___y_951_;
}
}
}
default: 
{
uint8_t v___x_955_; 
v___x_955_ = lean_level_eq(v_x_936_, v_x_937_);
return v___x_955_;
}
}
}
}
LEAN_EXPORT void l_Lean_Level_occurs_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_936_ = stack[0].m_obj;
lean_object* v_x_937_ = stack[1].m_obj;
uint8_t v_res_956_;
v_res_956_ = l_Lean_Level_occurs(v_x_936_, v_x_937_);
stack->m_num = v_res_956_;
}
LEAN_EXPORT lean_object* l_Lean_Level_occurs___boxed(lean_object* v_x_957_, lean_object* v_x_958_){
_start:
{
uint8_t v_res_959_; lean_object* v_r_960_; 
v_res_959_ = l_Lean_Level_occurs(v_x_957_, v_x_958_);
lean_dec(v_x_958_);
lean_dec(v_x_957_);
v_r_960_ = lean_box(v_res_959_);
return v_r_960_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_ctorToNat(lean_object* v_x_961_){
_start:
{
switch(lean_obj_tag(v_x_961_))
{
case 0:
{
lean_object* v___x_962_; 
v___x_962_ = lean_unsigned_to_nat(0u);
return v___x_962_;
}
case 1:
{
lean_object* v___x_963_; 
v___x_963_ = lean_unsigned_to_nat(3u);
return v___x_963_;
}
case 2:
{
lean_object* v___x_964_; 
v___x_964_ = lean_unsigned_to_nat(4u);
return v___x_964_;
}
case 3:
{
lean_object* v___x_965_; 
v___x_965_ = lean_unsigned_to_nat(5u);
return v___x_965_;
}
case 4:
{
lean_object* v___x_966_; 
v___x_966_ = lean_unsigned_to_nat(1u);
return v___x_966_;
}
default: 
{
lean_object* v___x_967_; 
v___x_967_ = lean_unsigned_to_nat(2u);
return v___x_967_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_ctorToNat___boxed(lean_object* v_x_968_){
_start:
{
lean_object* v_res_969_; 
v_res_969_ = l_Lean_Level_ctorToNat(v_x_968_);
lean_dec(v_x_968_);
return v_res_969_;
}
}
uint8_t l_Lean_Level_normLtAux(lean_object* v_x_970_, lean_object* v_x_971_, lean_object* v_x_972_, lean_object* v_x_973_){
_start:
{
lean_object* v_l_u2081_975_; lean_object* v_k_u2081_976_; lean_object* v_l_u2082_977_; lean_object* v_k_u2082_978_; lean_object* v_l_u2081_983_; lean_object* v_k_u2081_984_; lean_object* v_l_u2082_985_; lean_object* v_k_u2082_986_; 
switch(lean_obj_tag(v_x_970_))
{
case 1:
{
lean_object* v_a_992_; lean_object* v___x_993_; lean_object* v___x_994_; 
v_a_992_ = lean_ctor_get(v_x_970_, 0);
v___x_993_ = lean_unsigned_to_nat(1u);
v___x_994_ = lean_nat_add(v_x_971_, v___x_993_);
lean_dec(v_x_971_);
v_x_970_ = v_a_992_;
v_x_971_ = v___x_994_;
goto _start;
}
case 2:
{
switch(lean_obj_tag(v_x_972_))
{
case 1:
{
lean_object* v_a_996_; 
v_a_996_ = lean_ctor_get(v_x_972_, 0);
v_l_u2081_975_ = v_x_970_;
v_k_u2081_976_ = v_x_971_;
v_l_u2082_977_ = v_a_996_;
v_k_u2082_978_ = v_x_973_;
goto v___jp_974_;
}
case 2:
{
lean_object* v_a_997_; lean_object* v_a_998_; lean_object* v_a_999_; lean_object* v_a_1000_; uint8_t v___x_1004_; 
v_a_997_ = lean_ctor_get(v_x_970_, 0);
v_a_998_ = lean_ctor_get(v_x_970_, 1);
v_a_999_ = lean_ctor_get(v_x_972_, 0);
v_a_1000_ = lean_ctor_get(v_x_972_, 1);
v___x_1004_ = lean_level_eq(v_x_970_, v_x_972_);
if (v___x_1004_ == 0)
{
uint8_t v___x_1005_; 
lean_dec(v_x_973_);
lean_dec(v_x_971_);
v___x_1005_ = lean_level_eq(v_a_997_, v_a_999_);
if (v___x_1005_ == 0)
{
goto v___jp_1001_;
}
else
{
if (v___x_1004_ == 0)
{
lean_object* v___x_1006_; 
v___x_1006_ = lean_unsigned_to_nat(0u);
v_x_970_ = v_a_998_;
v_x_971_ = v___x_1006_;
v_x_972_ = v_a_1000_;
v_x_973_ = v___x_1006_;
goto _start;
}
else
{
goto v___jp_1001_;
}
}
}
else
{
uint8_t v___x_1008_; 
v___x_1008_ = lean_nat_dec_lt(v_x_971_, v_x_973_);
lean_dec(v_x_973_);
lean_dec(v_x_971_);
return v___x_1008_;
}
v___jp_1001_:
{
lean_object* v___x_1002_; 
v___x_1002_ = lean_unsigned_to_nat(0u);
v_x_970_ = v_a_997_;
v_x_971_ = v___x_1002_;
v_x_972_ = v_a_999_;
v_x_973_ = v___x_1002_;
goto _start;
}
}
default: 
{
v_l_u2081_983_ = v_x_970_;
v_k_u2081_984_ = v_x_971_;
v_l_u2082_985_ = v_x_972_;
v_k_u2082_986_ = v_x_973_;
goto v___jp_982_;
}
}
}
case 3:
{
switch(lean_obj_tag(v_x_972_))
{
case 1:
{
lean_object* v_a_1009_; 
v_a_1009_ = lean_ctor_get(v_x_972_, 0);
v_l_u2081_975_ = v_x_970_;
v_k_u2081_976_ = v_x_971_;
v_l_u2082_977_ = v_a_1009_;
v_k_u2082_978_ = v_x_973_;
goto v___jp_974_;
}
case 3:
{
lean_object* v_a_1010_; lean_object* v_a_1011_; lean_object* v_a_1012_; lean_object* v_a_1013_; uint8_t v___x_1017_; 
v_a_1010_ = lean_ctor_get(v_x_970_, 0);
v_a_1011_ = lean_ctor_get(v_x_970_, 1);
v_a_1012_ = lean_ctor_get(v_x_972_, 0);
v_a_1013_ = lean_ctor_get(v_x_972_, 1);
v___x_1017_ = lean_level_eq(v_x_970_, v_x_972_);
if (v___x_1017_ == 0)
{
uint8_t v___x_1018_; 
lean_dec(v_x_973_);
lean_dec(v_x_971_);
v___x_1018_ = lean_level_eq(v_a_1010_, v_a_1012_);
if (v___x_1018_ == 0)
{
goto v___jp_1014_;
}
else
{
if (v___x_1017_ == 0)
{
lean_object* v___x_1019_; 
v___x_1019_ = lean_unsigned_to_nat(0u);
v_x_970_ = v_a_1011_;
v_x_971_ = v___x_1019_;
v_x_972_ = v_a_1013_;
v_x_973_ = v___x_1019_;
goto _start;
}
else
{
goto v___jp_1014_;
}
}
}
else
{
uint8_t v___x_1021_; 
v___x_1021_ = lean_nat_dec_lt(v_x_971_, v_x_973_);
lean_dec(v_x_973_);
lean_dec(v_x_971_);
return v___x_1021_;
}
v___jp_1014_:
{
lean_object* v___x_1015_; 
v___x_1015_ = lean_unsigned_to_nat(0u);
v_x_970_ = v_a_1010_;
v_x_971_ = v___x_1015_;
v_x_972_ = v_a_1012_;
v_x_973_ = v___x_1015_;
goto _start;
}
}
default: 
{
v_l_u2081_983_ = v_x_970_;
v_k_u2081_984_ = v_x_971_;
v_l_u2082_985_ = v_x_972_;
v_k_u2082_986_ = v_x_973_;
goto v___jp_982_;
}
}
}
case 4:
{
switch(lean_obj_tag(v_x_972_))
{
case 1:
{
lean_object* v_a_1022_; 
v_a_1022_ = lean_ctor_get(v_x_972_, 0);
v_l_u2081_975_ = v_x_970_;
v_k_u2081_976_ = v_x_971_;
v_l_u2082_977_ = v_a_1022_;
v_k_u2082_978_ = v_x_973_;
goto v___jp_974_;
}
case 4:
{
lean_object* v_a_1023_; lean_object* v_a_1024_; uint8_t v___x_1025_; 
v_a_1023_ = lean_ctor_get(v_x_970_, 0);
v_a_1024_ = lean_ctor_get(v_x_972_, 0);
v___x_1025_ = lean_name_eq(v_a_1023_, v_a_1024_);
if (v___x_1025_ == 0)
{
uint8_t v___x_1026_; 
lean_dec(v_x_973_);
lean_dec(v_x_971_);
v___x_1026_ = l_Lean_Name_lt(v_a_1023_, v_a_1024_);
return v___x_1026_;
}
else
{
uint8_t v___x_1027_; 
v___x_1027_ = lean_nat_dec_lt(v_x_971_, v_x_973_);
lean_dec(v_x_973_);
lean_dec(v_x_971_);
return v___x_1027_;
}
}
default: 
{
v_l_u2081_983_ = v_x_970_;
v_k_u2081_984_ = v_x_971_;
v_l_u2082_985_ = v_x_972_;
v_k_u2082_986_ = v_x_973_;
goto v___jp_982_;
}
}
}
case 5:
{
switch(lean_obj_tag(v_x_972_))
{
case 1:
{
lean_object* v_a_1028_; 
v_a_1028_ = lean_ctor_get(v_x_972_, 0);
v_l_u2081_975_ = v_x_970_;
v_k_u2081_976_ = v_x_971_;
v_l_u2082_977_ = v_a_1028_;
v_k_u2082_978_ = v_x_973_;
goto v___jp_974_;
}
case 5:
{
lean_object* v_a_1029_; lean_object* v_a_1030_; uint8_t v___x_1031_; 
v_a_1029_ = lean_ctor_get(v_x_970_, 0);
v_a_1030_ = lean_ctor_get(v_x_972_, 0);
v___x_1031_ = lean_name_eq(v_a_1029_, v_a_1030_);
if (v___x_1031_ == 0)
{
uint8_t v___x_1032_; 
lean_dec(v_x_973_);
lean_dec(v_x_971_);
v___x_1032_ = l_Lean_Name_lt(v_a_1029_, v_a_1030_);
return v___x_1032_;
}
else
{
uint8_t v___x_1033_; 
v___x_1033_ = lean_nat_dec_lt(v_x_971_, v_x_973_);
lean_dec(v_x_973_);
lean_dec(v_x_971_);
return v___x_1033_;
}
}
default: 
{
v_l_u2081_983_ = v_x_970_;
v_k_u2081_984_ = v_x_971_;
v_l_u2082_985_ = v_x_972_;
v_k_u2082_986_ = v_x_973_;
goto v___jp_982_;
}
}
}
default: 
{
if (lean_obj_tag(v_x_972_) == 1)
{
lean_object* v_a_1034_; 
v_a_1034_ = lean_ctor_get(v_x_972_, 0);
v_l_u2081_975_ = v_x_970_;
v_k_u2081_976_ = v_x_971_;
v_l_u2082_977_ = v_a_1034_;
v_k_u2082_978_ = v_x_973_;
goto v___jp_974_;
}
else
{
v_l_u2081_983_ = v_x_970_;
v_k_u2081_984_ = v_x_971_;
v_l_u2082_985_ = v_x_972_;
v_k_u2082_986_ = v_x_973_;
goto v___jp_982_;
}
}
}
v___jp_974_:
{
lean_object* v___x_979_; lean_object* v___x_980_; 
v___x_979_ = lean_unsigned_to_nat(1u);
v___x_980_ = lean_nat_add(v_k_u2082_978_, v___x_979_);
lean_dec(v_k_u2082_978_);
v_x_970_ = v_l_u2081_975_;
v_x_971_ = v_k_u2081_976_;
v_x_972_ = v_l_u2082_977_;
v_x_973_ = v___x_980_;
goto _start;
}
v___jp_982_:
{
uint8_t v___x_987_; 
v___x_987_ = lean_level_eq(v_l_u2081_983_, v_l_u2082_985_);
if (v___x_987_ == 0)
{
lean_object* v___x_988_; lean_object* v___x_989_; uint8_t v___x_990_; 
lean_dec(v_k_u2082_986_);
lean_dec(v_k_u2081_984_);
v___x_988_ = l_Lean_Level_ctorToNat(v_l_u2081_983_);
v___x_989_ = l_Lean_Level_ctorToNat(v_l_u2082_985_);
v___x_990_ = lean_nat_dec_lt(v___x_988_, v___x_989_);
lean_dec(v___x_989_);
lean_dec(v___x_988_);
return v___x_990_;
}
else
{
uint8_t v___x_991_; 
v___x_991_ = lean_nat_dec_lt(v_k_u2081_984_, v_k_u2082_986_);
lean_dec(v_k_u2082_986_);
lean_dec(v_k_u2081_984_);
return v___x_991_;
}
}
}
}
LEAN_EXPORT void l_Lean_Level_normLtAux_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_970_ = stack[0].m_obj;
lean_object* v_x_971_ = stack[1].m_obj;
lean_object* v_x_972_ = stack[2].m_obj;
lean_object* v_x_973_ = stack[3].m_obj;
uint8_t v_res_1035_;
v_res_1035_ = l_Lean_Level_normLtAux(v_x_970_, v_x_971_, v_x_972_, v_x_973_);
stack->m_num = v_res_1035_;
}
LEAN_EXPORT lean_object* l_Lean_Level_normLtAux___boxed(lean_object* v_x_1036_, lean_object* v_x_1037_, lean_object* v_x_1038_, lean_object* v_x_1039_){
_start:
{
uint8_t v_res_1040_; lean_object* v_r_1041_; 
v_res_1040_ = l_Lean_Level_normLtAux(v_x_1036_, v_x_1037_, v_x_1038_, v_x_1039_);
lean_dec(v_x_1038_);
lean_dec(v_x_1036_);
v_r_1041_ = lean_box(v_res_1040_);
return v_r_1041_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_normLtAux_match__1_splitter___redArg(lean_object* v_x_1042_, lean_object* v_x_1043_, lean_object* v_x_1044_, lean_object* v_x_1045_, lean_object* v_h__1_1046_, lean_object* v_h__2_1047_, lean_object* v_h__3_1048_, lean_object* v_h__4_1049_, lean_object* v_h__5_1050_, lean_object* v_h__6_1051_, lean_object* v_h__7_1052_){
_start:
{
switch(lean_obj_tag(v_x_1042_))
{
case 1:
{
lean_object* v_a_1053_; lean_object* v___x_1054_; 
lean_dec(v_h__7_1052_);
lean_dec(v_h__6_1051_);
lean_dec(v_h__5_1050_);
lean_dec(v_h__4_1049_);
lean_dec(v_h__3_1048_);
lean_dec(v_h__2_1047_);
v_a_1053_ = lean_ctor_get(v_x_1042_, 0);
lean_inc(v_a_1053_);
lean_dec_ref_known(v_x_1042_, 1);
v___x_1054_ = lean_apply_4(v_h__1_1046_, v_a_1053_, v_x_1043_, v_x_1044_, v_x_1045_);
return v___x_1054_;
}
case 2:
{
lean_dec(v_h__6_1051_);
lean_dec(v_h__5_1050_);
lean_dec(v_h__4_1049_);
lean_dec(v_h__1_1046_);
switch(lean_obj_tag(v_x_1044_))
{
case 1:
{
lean_object* v_a_1055_; lean_object* v___x_1056_; 
lean_dec(v_h__7_1052_);
lean_dec(v_h__3_1048_);
v_a_1055_ = lean_ctor_get(v_x_1044_, 0);
lean_inc(v_a_1055_);
lean_dec_ref_known(v_x_1044_, 1);
v___x_1056_ = lean_apply_5(v_h__2_1047_, v_x_1042_, v_x_1043_, v_a_1055_, v_x_1045_, lean_box(0));
return v___x_1056_;
}
case 2:
{
lean_object* v_a_1057_; lean_object* v_a_1058_; lean_object* v_a_1059_; lean_object* v_a_1060_; lean_object* v___x_1061_; 
lean_dec(v_h__7_1052_);
lean_dec(v_h__2_1047_);
v_a_1057_ = lean_ctor_get(v_x_1042_, 0);
lean_inc(v_a_1057_);
v_a_1058_ = lean_ctor_get(v_x_1042_, 1);
lean_inc(v_a_1058_);
lean_dec_ref_known(v_x_1042_, 2);
v_a_1059_ = lean_ctor_get(v_x_1044_, 0);
lean_inc(v_a_1059_);
v_a_1060_ = lean_ctor_get(v_x_1044_, 1);
lean_inc(v_a_1060_);
lean_dec_ref_known(v_x_1044_, 2);
v___x_1061_ = lean_apply_6(v_h__3_1048_, v_a_1057_, v_a_1058_, v_x_1043_, v_a_1059_, v_a_1060_, v_x_1045_);
return v___x_1061_;
}
default: 
{
lean_object* v___x_1062_; 
lean_dec(v_h__3_1048_);
lean_dec(v_h__2_1047_);
v___x_1062_ = lean_apply_10(v_h__7_1052_, v_x_1042_, v_x_1043_, v_x_1044_, v_x_1045_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_1062_;
}
}
}
case 3:
{
lean_dec(v_h__6_1051_);
lean_dec(v_h__5_1050_);
lean_dec(v_h__3_1048_);
lean_dec(v_h__1_1046_);
switch(lean_obj_tag(v_x_1044_))
{
case 1:
{
lean_object* v_a_1063_; lean_object* v___x_1064_; 
lean_dec(v_h__7_1052_);
lean_dec(v_h__4_1049_);
v_a_1063_ = lean_ctor_get(v_x_1044_, 0);
lean_inc(v_a_1063_);
lean_dec_ref_known(v_x_1044_, 1);
v___x_1064_ = lean_apply_5(v_h__2_1047_, v_x_1042_, v_x_1043_, v_a_1063_, v_x_1045_, lean_box(0));
return v___x_1064_;
}
case 3:
{
lean_object* v_a_1065_; lean_object* v_a_1066_; lean_object* v_a_1067_; lean_object* v_a_1068_; lean_object* v___x_1069_; 
lean_dec(v_h__7_1052_);
lean_dec(v_h__2_1047_);
v_a_1065_ = lean_ctor_get(v_x_1042_, 0);
lean_inc(v_a_1065_);
v_a_1066_ = lean_ctor_get(v_x_1042_, 1);
lean_inc(v_a_1066_);
lean_dec_ref_known(v_x_1042_, 2);
v_a_1067_ = lean_ctor_get(v_x_1044_, 0);
lean_inc(v_a_1067_);
v_a_1068_ = lean_ctor_get(v_x_1044_, 1);
lean_inc(v_a_1068_);
lean_dec_ref_known(v_x_1044_, 2);
v___x_1069_ = lean_apply_6(v_h__4_1049_, v_a_1065_, v_a_1066_, v_x_1043_, v_a_1067_, v_a_1068_, v_x_1045_);
return v___x_1069_;
}
default: 
{
lean_object* v___x_1070_; 
lean_dec(v_h__4_1049_);
lean_dec(v_h__2_1047_);
v___x_1070_ = lean_apply_10(v_h__7_1052_, v_x_1042_, v_x_1043_, v_x_1044_, v_x_1045_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_1070_;
}
}
}
case 4:
{
lean_dec(v_h__6_1051_);
lean_dec(v_h__4_1049_);
lean_dec(v_h__3_1048_);
lean_dec(v_h__1_1046_);
switch(lean_obj_tag(v_x_1044_))
{
case 1:
{
lean_object* v_a_1071_; lean_object* v___x_1072_; 
lean_dec(v_h__7_1052_);
lean_dec(v_h__5_1050_);
v_a_1071_ = lean_ctor_get(v_x_1044_, 0);
lean_inc(v_a_1071_);
lean_dec_ref_known(v_x_1044_, 1);
v___x_1072_ = lean_apply_5(v_h__2_1047_, v_x_1042_, v_x_1043_, v_a_1071_, v_x_1045_, lean_box(0));
return v___x_1072_;
}
case 4:
{
lean_object* v_a_1073_; lean_object* v_a_1074_; lean_object* v___x_1075_; 
lean_dec(v_h__7_1052_);
lean_dec(v_h__2_1047_);
v_a_1073_ = lean_ctor_get(v_x_1042_, 0);
lean_inc(v_a_1073_);
lean_dec_ref_known(v_x_1042_, 1);
v_a_1074_ = lean_ctor_get(v_x_1044_, 0);
lean_inc(v_a_1074_);
lean_dec_ref_known(v_x_1044_, 1);
v___x_1075_ = lean_apply_4(v_h__5_1050_, v_a_1073_, v_x_1043_, v_a_1074_, v_x_1045_);
return v___x_1075_;
}
default: 
{
lean_object* v___x_1076_; 
lean_dec(v_h__5_1050_);
lean_dec(v_h__2_1047_);
v___x_1076_ = lean_apply_10(v_h__7_1052_, v_x_1042_, v_x_1043_, v_x_1044_, v_x_1045_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_1076_;
}
}
}
case 5:
{
lean_dec(v_h__5_1050_);
lean_dec(v_h__4_1049_);
lean_dec(v_h__3_1048_);
lean_dec(v_h__1_1046_);
switch(lean_obj_tag(v_x_1044_))
{
case 1:
{
lean_object* v_a_1077_; lean_object* v___x_1078_; 
lean_dec(v_h__7_1052_);
lean_dec(v_h__6_1051_);
v_a_1077_ = lean_ctor_get(v_x_1044_, 0);
lean_inc(v_a_1077_);
lean_dec_ref_known(v_x_1044_, 1);
v___x_1078_ = lean_apply_5(v_h__2_1047_, v_x_1042_, v_x_1043_, v_a_1077_, v_x_1045_, lean_box(0));
return v___x_1078_;
}
case 5:
{
lean_object* v_a_1079_; lean_object* v_a_1080_; lean_object* v___x_1081_; 
lean_dec(v_h__7_1052_);
lean_dec(v_h__2_1047_);
v_a_1079_ = lean_ctor_get(v_x_1042_, 0);
lean_inc(v_a_1079_);
lean_dec_ref_known(v_x_1042_, 1);
v_a_1080_ = lean_ctor_get(v_x_1044_, 0);
lean_inc(v_a_1080_);
lean_dec_ref_known(v_x_1044_, 1);
v___x_1081_ = lean_apply_4(v_h__6_1051_, v_a_1079_, v_x_1043_, v_a_1080_, v_x_1045_);
return v___x_1081_;
}
default: 
{
lean_object* v___x_1082_; 
lean_dec(v_h__6_1051_);
lean_dec(v_h__2_1047_);
v___x_1082_ = lean_apply_10(v_h__7_1052_, v_x_1042_, v_x_1043_, v_x_1044_, v_x_1045_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_1082_;
}
}
}
default: 
{
lean_dec(v_h__6_1051_);
lean_dec(v_h__5_1050_);
lean_dec(v_h__4_1049_);
lean_dec(v_h__3_1048_);
lean_dec(v_h__1_1046_);
if (lean_obj_tag(v_x_1044_) == 1)
{
lean_object* v_a_1083_; lean_object* v___x_1084_; 
lean_dec(v_h__7_1052_);
v_a_1083_ = lean_ctor_get(v_x_1044_, 0);
lean_inc(v_a_1083_);
lean_dec_ref_known(v_x_1044_, 1);
v___x_1084_ = lean_apply_5(v_h__2_1047_, v_x_1042_, v_x_1043_, v_a_1083_, v_x_1045_, lean_box(0));
return v___x_1084_;
}
else
{
lean_object* v___x_1085_; 
lean_dec(v_h__2_1047_);
v___x_1085_ = lean_apply_10(v_h__7_1052_, v_x_1042_, v_x_1043_, v_x_1044_, v_x_1045_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_1085_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_normLtAux_match__1_splitter(lean_object* v_motive_1086_, lean_object* v_x_1087_, lean_object* v_x_1088_, lean_object* v_x_1089_, lean_object* v_x_1090_, lean_object* v_h__1_1091_, lean_object* v_h__2_1092_, lean_object* v_h__3_1093_, lean_object* v_h__4_1094_, lean_object* v_h__5_1095_, lean_object* v_h__6_1096_, lean_object* v_h__7_1097_){
_start:
{
switch(lean_obj_tag(v_x_1087_))
{
case 1:
{
lean_object* v_a_1098_; lean_object* v___x_1099_; 
lean_dec(v_h__7_1097_);
lean_dec(v_h__6_1096_);
lean_dec(v_h__5_1095_);
lean_dec(v_h__4_1094_);
lean_dec(v_h__3_1093_);
lean_dec(v_h__2_1092_);
v_a_1098_ = lean_ctor_get(v_x_1087_, 0);
lean_inc(v_a_1098_);
lean_dec_ref_known(v_x_1087_, 1);
v___x_1099_ = lean_apply_4(v_h__1_1091_, v_a_1098_, v_x_1088_, v_x_1089_, v_x_1090_);
return v___x_1099_;
}
case 2:
{
lean_dec(v_h__6_1096_);
lean_dec(v_h__5_1095_);
lean_dec(v_h__4_1094_);
lean_dec(v_h__1_1091_);
switch(lean_obj_tag(v_x_1089_))
{
case 1:
{
lean_object* v_a_1100_; lean_object* v___x_1101_; 
lean_dec(v_h__7_1097_);
lean_dec(v_h__3_1093_);
v_a_1100_ = lean_ctor_get(v_x_1089_, 0);
lean_inc(v_a_1100_);
lean_dec_ref_known(v_x_1089_, 1);
v___x_1101_ = lean_apply_5(v_h__2_1092_, v_x_1087_, v_x_1088_, v_a_1100_, v_x_1090_, lean_box(0));
return v___x_1101_;
}
case 2:
{
lean_object* v_a_1102_; lean_object* v_a_1103_; lean_object* v_a_1104_; lean_object* v_a_1105_; lean_object* v___x_1106_; 
lean_dec(v_h__7_1097_);
lean_dec(v_h__2_1092_);
v_a_1102_ = lean_ctor_get(v_x_1087_, 0);
lean_inc(v_a_1102_);
v_a_1103_ = lean_ctor_get(v_x_1087_, 1);
lean_inc(v_a_1103_);
lean_dec_ref_known(v_x_1087_, 2);
v_a_1104_ = lean_ctor_get(v_x_1089_, 0);
lean_inc(v_a_1104_);
v_a_1105_ = lean_ctor_get(v_x_1089_, 1);
lean_inc(v_a_1105_);
lean_dec_ref_known(v_x_1089_, 2);
v___x_1106_ = lean_apply_6(v_h__3_1093_, v_a_1102_, v_a_1103_, v_x_1088_, v_a_1104_, v_a_1105_, v_x_1090_);
return v___x_1106_;
}
default: 
{
lean_object* v___x_1107_; 
lean_dec(v_h__3_1093_);
lean_dec(v_h__2_1092_);
v___x_1107_ = lean_apply_10(v_h__7_1097_, v_x_1087_, v_x_1088_, v_x_1089_, v_x_1090_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_1107_;
}
}
}
case 3:
{
lean_dec(v_h__6_1096_);
lean_dec(v_h__5_1095_);
lean_dec(v_h__3_1093_);
lean_dec(v_h__1_1091_);
switch(lean_obj_tag(v_x_1089_))
{
case 1:
{
lean_object* v_a_1108_; lean_object* v___x_1109_; 
lean_dec(v_h__7_1097_);
lean_dec(v_h__4_1094_);
v_a_1108_ = lean_ctor_get(v_x_1089_, 0);
lean_inc(v_a_1108_);
lean_dec_ref_known(v_x_1089_, 1);
v___x_1109_ = lean_apply_5(v_h__2_1092_, v_x_1087_, v_x_1088_, v_a_1108_, v_x_1090_, lean_box(0));
return v___x_1109_;
}
case 3:
{
lean_object* v_a_1110_; lean_object* v_a_1111_; lean_object* v_a_1112_; lean_object* v_a_1113_; lean_object* v___x_1114_; 
lean_dec(v_h__7_1097_);
lean_dec(v_h__2_1092_);
v_a_1110_ = lean_ctor_get(v_x_1087_, 0);
lean_inc(v_a_1110_);
v_a_1111_ = lean_ctor_get(v_x_1087_, 1);
lean_inc(v_a_1111_);
lean_dec_ref_known(v_x_1087_, 2);
v_a_1112_ = lean_ctor_get(v_x_1089_, 0);
lean_inc(v_a_1112_);
v_a_1113_ = lean_ctor_get(v_x_1089_, 1);
lean_inc(v_a_1113_);
lean_dec_ref_known(v_x_1089_, 2);
v___x_1114_ = lean_apply_6(v_h__4_1094_, v_a_1110_, v_a_1111_, v_x_1088_, v_a_1112_, v_a_1113_, v_x_1090_);
return v___x_1114_;
}
default: 
{
lean_object* v___x_1115_; 
lean_dec(v_h__4_1094_);
lean_dec(v_h__2_1092_);
v___x_1115_ = lean_apply_10(v_h__7_1097_, v_x_1087_, v_x_1088_, v_x_1089_, v_x_1090_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_1115_;
}
}
}
case 4:
{
lean_dec(v_h__6_1096_);
lean_dec(v_h__4_1094_);
lean_dec(v_h__3_1093_);
lean_dec(v_h__1_1091_);
switch(lean_obj_tag(v_x_1089_))
{
case 1:
{
lean_object* v_a_1116_; lean_object* v___x_1117_; 
lean_dec(v_h__7_1097_);
lean_dec(v_h__5_1095_);
v_a_1116_ = lean_ctor_get(v_x_1089_, 0);
lean_inc(v_a_1116_);
lean_dec_ref_known(v_x_1089_, 1);
v___x_1117_ = lean_apply_5(v_h__2_1092_, v_x_1087_, v_x_1088_, v_a_1116_, v_x_1090_, lean_box(0));
return v___x_1117_;
}
case 4:
{
lean_object* v_a_1118_; lean_object* v_a_1119_; lean_object* v___x_1120_; 
lean_dec(v_h__7_1097_);
lean_dec(v_h__2_1092_);
v_a_1118_ = lean_ctor_get(v_x_1087_, 0);
lean_inc(v_a_1118_);
lean_dec_ref_known(v_x_1087_, 1);
v_a_1119_ = lean_ctor_get(v_x_1089_, 0);
lean_inc(v_a_1119_);
lean_dec_ref_known(v_x_1089_, 1);
v___x_1120_ = lean_apply_4(v_h__5_1095_, v_a_1118_, v_x_1088_, v_a_1119_, v_x_1090_);
return v___x_1120_;
}
default: 
{
lean_object* v___x_1121_; 
lean_dec(v_h__5_1095_);
lean_dec(v_h__2_1092_);
v___x_1121_ = lean_apply_10(v_h__7_1097_, v_x_1087_, v_x_1088_, v_x_1089_, v_x_1090_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_1121_;
}
}
}
case 5:
{
lean_dec(v_h__5_1095_);
lean_dec(v_h__4_1094_);
lean_dec(v_h__3_1093_);
lean_dec(v_h__1_1091_);
switch(lean_obj_tag(v_x_1089_))
{
case 1:
{
lean_object* v_a_1122_; lean_object* v___x_1123_; 
lean_dec(v_h__7_1097_);
lean_dec(v_h__6_1096_);
v_a_1122_ = lean_ctor_get(v_x_1089_, 0);
lean_inc(v_a_1122_);
lean_dec_ref_known(v_x_1089_, 1);
v___x_1123_ = lean_apply_5(v_h__2_1092_, v_x_1087_, v_x_1088_, v_a_1122_, v_x_1090_, lean_box(0));
return v___x_1123_;
}
case 5:
{
lean_object* v_a_1124_; lean_object* v_a_1125_; lean_object* v___x_1126_; 
lean_dec(v_h__7_1097_);
lean_dec(v_h__2_1092_);
v_a_1124_ = lean_ctor_get(v_x_1087_, 0);
lean_inc(v_a_1124_);
lean_dec_ref_known(v_x_1087_, 1);
v_a_1125_ = lean_ctor_get(v_x_1089_, 0);
lean_inc(v_a_1125_);
lean_dec_ref_known(v_x_1089_, 1);
v___x_1126_ = lean_apply_4(v_h__6_1096_, v_a_1124_, v_x_1088_, v_a_1125_, v_x_1090_);
return v___x_1126_;
}
default: 
{
lean_object* v___x_1127_; 
lean_dec(v_h__6_1096_);
lean_dec(v_h__2_1092_);
v___x_1127_ = lean_apply_10(v_h__7_1097_, v_x_1087_, v_x_1088_, v_x_1089_, v_x_1090_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_1127_;
}
}
}
default: 
{
lean_dec(v_h__6_1096_);
lean_dec(v_h__5_1095_);
lean_dec(v_h__4_1094_);
lean_dec(v_h__3_1093_);
lean_dec(v_h__1_1091_);
if (lean_obj_tag(v_x_1089_) == 1)
{
lean_object* v_a_1128_; lean_object* v___x_1129_; 
lean_dec(v_h__7_1097_);
v_a_1128_ = lean_ctor_get(v_x_1089_, 0);
lean_inc(v_a_1128_);
lean_dec_ref_known(v_x_1089_, 1);
v___x_1129_ = lean_apply_5(v_h__2_1092_, v_x_1087_, v_x_1088_, v_a_1128_, v_x_1090_, lean_box(0));
return v___x_1129_;
}
else
{
lean_object* v___x_1130_; 
lean_dec(v_h__2_1092_);
v___x_1130_ = lean_apply_10(v_h__7_1097_, v_x_1087_, v_x_1088_, v_x_1089_, v_x_1090_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_1130_;
}
}
}
}
}
uint8_t l_Lean_Level_normLt(lean_object* v_l_u2081_1131_, lean_object* v_l_u2082_1132_){
_start:
{
lean_object* v___x_1133_; uint8_t v___x_1134_; 
v___x_1133_ = lean_unsigned_to_nat(0u);
v___x_1134_ = l_Lean_Level_normLtAux(v_l_u2081_1131_, v___x_1133_, v_l_u2082_1132_, v___x_1133_);
return v___x_1134_;
}
}
LEAN_EXPORT void l_Lean_Level_normLt_0interp(lean_interpreter_value* stack)
{
lean_object* v_l_u2081_1131_ = stack[0].m_obj;
lean_object* v_l_u2082_1132_ = stack[1].m_obj;
uint8_t v_res_1135_;
v_res_1135_ = l_Lean_Level_normLt(v_l_u2081_1131_, v_l_u2082_1132_);
stack->m_num = v_res_1135_;
}
LEAN_EXPORT lean_object* l_Lean_Level_normLt___boxed(lean_object* v_l_u2081_1136_, lean_object* v_l_u2082_1137_){
_start:
{
uint8_t v_res_1138_; lean_object* v_r_1139_; 
v_res_1138_ = l_Lean_Level_normLt(v_l_u2081_1136_, v_l_u2082_1137_);
lean_dec(v_l_u2082_1137_);
lean_dec(v_l_u2081_1136_);
v_r_1139_ = lean_box(v_res_1138_);
return v_r_1139_;
}
}
uint8_t l_Lean_Level_isAlreadyNormalizedCheap(lean_object* v_x_1140_){
_start:
{
switch(lean_obj_tag(v_x_1140_))
{
case 0:
{
uint8_t v___x_1141_; 
v___x_1141_ = 1;
return v___x_1141_;
}
case 4:
{
uint8_t v___x_1142_; 
v___x_1142_ = 1;
return v___x_1142_;
}
case 5:
{
uint8_t v___x_1143_; 
v___x_1143_ = 1;
return v___x_1143_;
}
case 1:
{
lean_object* v_a_1144_; 
v_a_1144_ = lean_ctor_get(v_x_1140_, 0);
v_x_1140_ = v_a_1144_;
goto _start;
}
default: 
{
uint8_t v___x_1146_; 
v___x_1146_ = 0;
return v___x_1146_;
}
}
}
}
LEAN_EXPORT void l_Lean_Level_isAlreadyNormalizedCheap_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1140_ = stack[0].m_obj;
uint8_t v_res_1147_;
v_res_1147_ = l_Lean_Level_isAlreadyNormalizedCheap(v_x_1140_);
stack->m_num = v_res_1147_;
}
LEAN_EXPORT lean_object* l_Lean_Level_isAlreadyNormalizedCheap___boxed(lean_object* v_x_1148_){
_start:
{
uint8_t v_res_1149_; lean_object* v_r_1150_; 
v_res_1149_ = l_Lean_Level_isAlreadyNormalizedCheap(v_x_1148_);
lean_dec(v_x_1148_);
v_r_1150_ = lean_box(v_res_1149_);
return v_r_1150_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_mkIMaxAux(lean_object* v_x_1151_, lean_object* v_x_1152_){
_start:
{
lean_object* v_u_u2081_1154_; lean_object* v_u_u2082_1155_; 
if (lean_obj_tag(v_x_1152_) == 0)
{
lean_dec(v_x_1151_);
return v_x_1152_;
}
else
{
switch(lean_obj_tag(v_x_1151_))
{
case 0:
{
return v_x_1152_;
}
case 1:
{
lean_object* v_a_1158_; 
v_a_1158_ = lean_ctor_get(v_x_1151_, 0);
if (lean_obj_tag(v_a_1158_) == 0)
{
lean_dec_ref_known(v_x_1151_, 1);
return v_x_1152_;
}
else
{
v_u_u2081_1154_ = v_x_1151_;
v_u_u2082_1155_ = v_x_1152_;
goto v___jp_1153_;
}
}
default: 
{
v_u_u2081_1154_ = v_x_1151_;
v_u_u2082_1155_ = v_x_1152_;
goto v___jp_1153_;
}
}
}
v___jp_1153_:
{
uint8_t v___x_1156_; 
v___x_1156_ = lean_level_eq(v_u_u2081_1154_, v_u_u2082_1155_);
if (v___x_1156_ == 0)
{
lean_object* v___x_1157_; 
v___x_1157_ = l_Lean_Level_imax___override(v_u_u2081_1154_, v_u_u2082_1155_);
return v___x_1157_;
}
else
{
lean_dec(v_u_u2082_1155_);
return v_u_u2081_1154_;
}
}
}
}
lean_object* l___private_Lean_Level_0__Lean_Level_getMaxArgsAux(lean_object* v_normalize_1159_, lean_object* v_x_1160_, uint8_t v_x_1161_, lean_object* v_x_1162_){
_start:
{
if (lean_obj_tag(v_x_1160_) == 2)
{
lean_object* v_a_1163_; lean_object* v_a_1164_; lean_object* v___x_1165_; 
v_a_1163_ = lean_ctor_get(v_x_1160_, 0);
lean_inc(v_a_1163_);
v_a_1164_ = lean_ctor_get(v_x_1160_, 1);
lean_inc(v_a_1164_);
lean_dec_ref_known(v_x_1160_, 2);
lean_inc_ref(v_normalize_1159_);
v___x_1165_ = l___private_Lean_Level_0__Lean_Level_getMaxArgsAux(v_normalize_1159_, v_a_1163_, v_x_1161_, v_x_1162_);
v_x_1160_ = v_a_1164_;
v_x_1162_ = v___x_1165_;
goto _start;
}
else
{
if (v_x_1161_ == 0)
{
lean_object* v___x_1167_; uint8_t v___x_1168_; 
lean_inc_ref(v_normalize_1159_);
v___x_1167_ = lean_apply_1(v_normalize_1159_, v_x_1160_);
v___x_1168_ = 1;
v_x_1160_ = v___x_1167_;
v_x_1161_ = v___x_1168_;
goto _start;
}
else
{
lean_object* v___x_1170_; 
lean_dec_ref(v_normalize_1159_);
v___x_1170_ = lean_array_push(v_x_1162_, v_x_1160_);
return v___x_1170_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Level_0__Lean_Level_getMaxArgsAux_0interp(lean_interpreter_value* stack)
{
lean_object* v_normalize_1159_ = stack[0].m_obj;
lean_object* v_x_1160_ = stack[1].m_obj;
uint8_t v_x_1161_ = stack[2].m_num;
lean_object* v_x_1162_ = stack[3].m_obj;
lean_object* v_res_1171_;
v_res_1171_ = l___private_Lean_Level_0__Lean_Level_getMaxArgsAux(v_normalize_1159_, v_x_1160_, v_x_1161_, v_x_1162_);
stack->m_obj
 = v_res_1171_;
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_getMaxArgsAux___boxed(lean_object* v_normalize_1172_, lean_object* v_x_1173_, lean_object* v_x_1174_, lean_object* v_x_1175_){
_start:
{
uint8_t v_x_31__boxed_1176_; lean_object* v_res_1177_; 
v_x_31__boxed_1176_ = lean_unbox(v_x_1174_);
v_res_1177_ = l___private_Lean_Level_0__Lean_Level_getMaxArgsAux(v_normalize_1172_, v_x_1173_, v_x_31__boxed_1176_, v_x_1175_);
return v_res_1177_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_accMax(lean_object* v_result_1178_, lean_object* v_prev_1179_, lean_object* v_offset_1180_){
_start:
{
uint8_t v___x_1181_; 
v___x_1181_ = l_Lean_Level_isZero(v_result_1178_);
if (v___x_1181_ == 0)
{
lean_object* v___x_1182_; lean_object* v___x_1183_; 
v___x_1182_ = l_Lean_Level_addOffsetAux(v_offset_1180_, v_prev_1179_);
v___x_1183_ = l_Lean_Level_max___override(v_result_1178_, v___x_1182_);
return v___x_1183_;
}
else
{
lean_object* v___x_1184_; 
lean_dec(v_result_1178_);
v___x_1184_ = l_Lean_Level_addOffsetAux(v_offset_1180_, v_prev_1179_);
return v___x_1184_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_mkMaxAux(lean_object* v_lvls_1185_, lean_object* v_extraK_1186_, lean_object* v_i_1187_, lean_object* v_prev_1188_, lean_object* v_prevK_1189_, lean_object* v_result_1190_){
_start:
{
lean_object* v___x_1191_; uint8_t v___x_1192_; 
v___x_1191_ = lean_array_get_size(v_lvls_1185_);
v___x_1192_ = lean_nat_dec_lt(v_i_1187_, v___x_1191_);
if (v___x_1192_ == 0)
{
lean_object* v___x_1193_; lean_object* v___x_1194_; 
lean_dec(v_i_1187_);
v___x_1193_ = lean_nat_add(v_extraK_1186_, v_prevK_1189_);
lean_dec(v_prevK_1189_);
v___x_1194_ = l___private_Lean_Level_0__Lean_Level_accMax(v_result_1190_, v_prev_1188_, v___x_1193_);
return v___x_1194_;
}
else
{
lean_object* v_lvl_1195_; lean_object* v_curr_1196_; lean_object* v_currK_1197_; uint8_t v___x_1198_; 
v_lvl_1195_ = lean_array_fget_borrowed(v_lvls_1185_, v_i_1187_);
v_curr_1196_ = l_Lean_Level_getLevelOffset(v_lvl_1195_);
v_currK_1197_ = l_Lean_Level_getOffset(v_lvl_1195_);
v___x_1198_ = lean_level_eq(v_curr_1196_, v_prev_1188_);
if (v___x_1198_ == 0)
{
lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; 
v___x_1199_ = lean_unsigned_to_nat(1u);
v___x_1200_ = lean_nat_add(v_i_1187_, v___x_1199_);
lean_dec(v_i_1187_);
v___x_1201_ = lean_nat_add(v_extraK_1186_, v_prevK_1189_);
lean_dec(v_prevK_1189_);
v___x_1202_ = l___private_Lean_Level_0__Lean_Level_accMax(v_result_1190_, v_prev_1188_, v___x_1201_);
v_i_1187_ = v___x_1200_;
v_prev_1188_ = v_curr_1196_;
v_prevK_1189_ = v_currK_1197_;
v_result_1190_ = v___x_1202_;
goto _start;
}
else
{
lean_object* v___x_1204_; lean_object* v___x_1205_; 
lean_dec(v_prevK_1189_);
lean_dec(v_prev_1188_);
v___x_1204_ = lean_unsigned_to_nat(1u);
v___x_1205_ = lean_nat_add(v_i_1187_, v___x_1204_);
lean_dec(v_i_1187_);
v_i_1187_ = v___x_1205_;
v_prev_1188_ = v_curr_1196_;
v_prevK_1189_ = v_currK_1197_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_mkMaxAux___boxed(lean_object* v_lvls_1207_, lean_object* v_extraK_1208_, lean_object* v_i_1209_, lean_object* v_prev_1210_, lean_object* v_prevK_1211_, lean_object* v_result_1212_){
_start:
{
lean_object* v_res_1213_; 
v_res_1213_ = l___private_Lean_Level_0__Lean_Level_mkMaxAux(v_lvls_1207_, v_extraK_1208_, v_i_1209_, v_prev_1210_, v_prevK_1211_, v_result_1212_);
lean_dec(v_extraK_1208_);
lean_dec_ref(v_lvls_1207_);
return v_res_1213_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_skipExplicit(lean_object* v_lvls_1214_, lean_object* v_i_1215_){
_start:
{
lean_object* v___x_1216_; uint8_t v___x_1217_; 
v___x_1216_ = lean_array_get_size(v_lvls_1214_);
v___x_1217_ = lean_nat_dec_lt(v_i_1215_, v___x_1216_);
if (v___x_1217_ == 0)
{
return v_i_1215_;
}
else
{
lean_object* v_lvl_1218_; lean_object* v___x_1219_; uint8_t v___x_1220_; 
v_lvl_1218_ = lean_array_fget_borrowed(v_lvls_1214_, v_i_1215_);
v___x_1219_ = l_Lean_Level_getLevelOffset(v_lvl_1218_);
v___x_1220_ = l_Lean_Level_isZero(v___x_1219_);
lean_dec(v___x_1219_);
if (v___x_1220_ == 0)
{
return v_i_1215_;
}
else
{
lean_object* v___x_1221_; lean_object* v___x_1222_; 
v___x_1221_ = lean_unsigned_to_nat(1u);
v___x_1222_ = lean_nat_add(v_i_1215_, v___x_1221_);
lean_dec(v_i_1215_);
v_i_1215_ = v___x_1222_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_skipExplicit___boxed(lean_object* v_lvls_1224_, lean_object* v_i_1225_){
_start:
{
lean_object* v_res_1226_; 
v_res_1226_ = l___private_Lean_Level_0__Lean_Level_skipExplicit(v_lvls_1224_, v_i_1225_);
lean_dec_ref(v_lvls_1224_);
return v_res_1226_;
}
}
uint8_t l___private_Lean_Level_0__Lean_Level_isExplicitSubsumedAux(lean_object* v_lvls_1227_, lean_object* v_maxExplicit_1228_, lean_object* v_i_1229_){
_start:
{
lean_object* v___x_1230_; uint8_t v___x_1231_; 
v___x_1230_ = lean_array_get_size(v_lvls_1227_);
v___x_1231_ = lean_nat_dec_lt(v_i_1229_, v___x_1230_);
if (v___x_1231_ == 0)
{
lean_dec(v_i_1229_);
return v___x_1231_;
}
else
{
lean_object* v_lvl_1232_; lean_object* v___x_1233_; uint8_t v___x_1234_; 
v_lvl_1232_ = lean_array_fget_borrowed(v_lvls_1227_, v_i_1229_);
v___x_1233_ = l_Lean_Level_getOffset(v_lvl_1232_);
v___x_1234_ = lean_nat_dec_le(v_maxExplicit_1228_, v___x_1233_);
lean_dec(v___x_1233_);
if (v___x_1234_ == 0)
{
lean_object* v___x_1235_; lean_object* v___x_1236_; 
v___x_1235_ = lean_unsigned_to_nat(1u);
v___x_1236_ = lean_nat_add(v_i_1229_, v___x_1235_);
lean_dec(v_i_1229_);
v_i_1229_ = v___x_1236_;
goto _start;
}
else
{
lean_dec(v_i_1229_);
return v___x_1234_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Level_0__Lean_Level_isExplicitSubsumedAux_0interp(lean_interpreter_value* stack)
{
lean_object* v_lvls_1227_ = stack[0].m_obj;
lean_object* v_maxExplicit_1228_ = stack[1].m_obj;
lean_object* v_i_1229_ = stack[2].m_obj;
uint8_t v_res_1238_;
v_res_1238_ = l___private_Lean_Level_0__Lean_Level_isExplicitSubsumedAux(v_lvls_1227_, v_maxExplicit_1228_, v_i_1229_);
stack->m_num = v_res_1238_;
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_isExplicitSubsumedAux___boxed(lean_object* v_lvls_1239_, lean_object* v_maxExplicit_1240_, lean_object* v_i_1241_){
_start:
{
uint8_t v_res_1242_; lean_object* v_r_1243_; 
v_res_1242_ = l___private_Lean_Level_0__Lean_Level_isExplicitSubsumedAux(v_lvls_1239_, v_maxExplicit_1240_, v_i_1241_);
lean_dec(v_maxExplicit_1240_);
lean_dec_ref(v_lvls_1239_);
v_r_1243_ = lean_box(v_res_1242_);
return v_r_1243_;
}
}
uint8_t l___private_Lean_Level_0__Lean_Level_isExplicitSubsumed(lean_object* v_lvls_1244_, lean_object* v_firstNonExplicit_1245_){
_start:
{
lean_object* v___x_1246_; uint8_t v___x_1247_; 
v___x_1246_ = lean_unsigned_to_nat(0u);
v___x_1247_ = lean_nat_dec_eq(v_firstNonExplicit_1245_, v___x_1246_);
if (v___x_1247_ == 0)
{
lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v_max_1252_; uint8_t v___x_1253_; 
v___x_1248_ = lean_box(0);
v___x_1249_ = lean_unsigned_to_nat(1u);
v___x_1250_ = lean_nat_sub(v_firstNonExplicit_1245_, v___x_1249_);
v___x_1251_ = lean_array_get_borrowed(v___x_1248_, v_lvls_1244_, v___x_1250_);
lean_dec(v___x_1250_);
v_max_1252_ = l_Lean_Level_getOffset(v___x_1251_);
v___x_1253_ = l___private_Lean_Level_0__Lean_Level_isExplicitSubsumedAux(v_lvls_1244_, v_max_1252_, v_firstNonExplicit_1245_);
lean_dec(v_max_1252_);
return v___x_1253_;
}
else
{
uint8_t v___x_1254_; 
lean_dec(v_firstNonExplicit_1245_);
v___x_1254_ = 0;
return v___x_1254_;
}
}
}
LEAN_EXPORT void l___private_Lean_Level_0__Lean_Level_isExplicitSubsumed_0interp(lean_interpreter_value* stack)
{
lean_object* v_lvls_1244_ = stack[0].m_obj;
lean_object* v_firstNonExplicit_1245_ = stack[1].m_obj;
uint8_t v_res_1255_;
v_res_1255_ = l___private_Lean_Level_0__Lean_Level_isExplicitSubsumed(v_lvls_1244_, v_firstNonExplicit_1245_);
stack->m_num = v_res_1255_;
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_isExplicitSubsumed___boxed(lean_object* v_lvls_1256_, lean_object* v_firstNonExplicit_1257_){
_start:
{
uint8_t v_res_1258_; lean_object* v_r_1259_; 
v_res_1258_ = l___private_Lean_Level_0__Lean_Level_isExplicitSubsumed(v_lvls_1256_, v_firstNonExplicit_1257_);
lean_dec_ref(v_lvls_1256_);
v_r_1259_ = lean_box(v_res_1258_);
return v_r_1259_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Level_normalize_spec__2(lean_object* v_msg_1260_){
_start:
{
lean_object* v___x_1261_; lean_object* v___x_1262_; 
v___x_1261_ = lean_box(0);
v___x_1262_ = lean_panic_fn_borrowed(v___x_1261_, v_msg_1260_);
return v___x_1262_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1_spec__1___redArg(lean_object* v_hi_1263_, lean_object* v_pivot_1264_, lean_object* v_as_1265_, lean_object* v_i_1266_, lean_object* v_k_1267_){
_start:
{
uint8_t v___x_1268_; 
v___x_1268_ = lean_nat_dec_lt(v_k_1267_, v_hi_1263_);
if (v___x_1268_ == 0)
{
lean_object* v___x_1269_; lean_object* v___x_1270_; 
lean_dec(v_k_1267_);
v___x_1269_ = lean_array_fswap(v_as_1265_, v_i_1266_, v_hi_1263_);
v___x_1270_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1270_, 0, v_i_1266_);
lean_ctor_set(v___x_1270_, 1, v___x_1269_);
return v___x_1270_;
}
else
{
lean_object* v___x_1271_; uint8_t v___x_1272_; 
v___x_1271_ = lean_array_fget_borrowed(v_as_1265_, v_k_1267_);
v___x_1272_ = l_Lean_Level_normLt(v___x_1271_, v_pivot_1264_);
if (v___x_1272_ == 0)
{
lean_object* v___x_1273_; lean_object* v___x_1274_; 
v___x_1273_ = lean_unsigned_to_nat(1u);
v___x_1274_ = lean_nat_add(v_k_1267_, v___x_1273_);
lean_dec(v_k_1267_);
v_k_1267_ = v___x_1274_;
goto _start;
}
else
{
lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; 
v___x_1276_ = lean_array_fswap(v_as_1265_, v_i_1266_, v_k_1267_);
v___x_1277_ = lean_unsigned_to_nat(1u);
v___x_1278_ = lean_nat_add(v_i_1266_, v___x_1277_);
lean_dec(v_i_1266_);
v___x_1279_ = lean_nat_add(v_k_1267_, v___x_1277_);
lean_dec(v_k_1267_);
v_as_1265_ = v___x_1276_;
v_i_1266_ = v___x_1278_;
v_k_1267_ = v___x_1279_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1_spec__1___redArg___boxed(lean_object* v_hi_1281_, lean_object* v_pivot_1282_, lean_object* v_as_1283_, lean_object* v_i_1284_, lean_object* v_k_1285_){
_start:
{
lean_object* v_res_1286_; 
v_res_1286_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1_spec__1___redArg(v_hi_1281_, v_pivot_1282_, v_as_1283_, v_i_1284_, v_k_1285_);
lean_dec(v_pivot_1282_);
lean_dec(v_hi_1281_);
return v_res_1286_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1___redArg(lean_object* v_n_1287_, lean_object* v_as_1288_, lean_object* v_lo_1289_, lean_object* v_hi_1290_){
_start:
{
lean_object* v___y_1292_; uint8_t v___x_1302_; 
v___x_1302_ = lean_nat_dec_lt(v_lo_1289_, v_hi_1290_);
if (v___x_1302_ == 0)
{
lean_dec(v_lo_1289_);
return v_as_1288_;
}
else
{
lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v_mid_1305_; lean_object* v___y_1307_; lean_object* v___y_1313_; lean_object* v___x_1318_; lean_object* v___x_1319_; uint8_t v___x_1320_; 
v___x_1303_ = lean_nat_add(v_lo_1289_, v_hi_1290_);
v___x_1304_ = lean_unsigned_to_nat(1u);
v_mid_1305_ = lean_nat_shiftr(v___x_1303_, v___x_1304_);
lean_dec(v___x_1303_);
v___x_1318_ = lean_array_fget_borrowed(v_as_1288_, v_mid_1305_);
v___x_1319_ = lean_array_fget_borrowed(v_as_1288_, v_lo_1289_);
v___x_1320_ = l_Lean_Level_normLt(v___x_1318_, v___x_1319_);
if (v___x_1320_ == 0)
{
v___y_1313_ = v_as_1288_;
goto v___jp_1312_;
}
else
{
lean_object* v___x_1321_; 
v___x_1321_ = lean_array_fswap(v_as_1288_, v_lo_1289_, v_mid_1305_);
v___y_1313_ = v___x_1321_;
goto v___jp_1312_;
}
v___jp_1306_:
{
lean_object* v___x_1308_; lean_object* v___x_1309_; uint8_t v___x_1310_; 
v___x_1308_ = lean_array_fget_borrowed(v___y_1307_, v_mid_1305_);
v___x_1309_ = lean_array_fget_borrowed(v___y_1307_, v_hi_1290_);
v___x_1310_ = l_Lean_Level_normLt(v___x_1308_, v___x_1309_);
if (v___x_1310_ == 0)
{
lean_dec(v_mid_1305_);
v___y_1292_ = v___y_1307_;
goto v___jp_1291_;
}
else
{
lean_object* v___x_1311_; 
v___x_1311_ = lean_array_fswap(v___y_1307_, v_mid_1305_, v_hi_1290_);
lean_dec(v_mid_1305_);
v___y_1292_ = v___x_1311_;
goto v___jp_1291_;
}
}
v___jp_1312_:
{
lean_object* v___x_1314_; lean_object* v___x_1315_; uint8_t v___x_1316_; 
v___x_1314_ = lean_array_fget_borrowed(v___y_1313_, v_hi_1290_);
v___x_1315_ = lean_array_fget_borrowed(v___y_1313_, v_lo_1289_);
v___x_1316_ = l_Lean_Level_normLt(v___x_1314_, v___x_1315_);
if (v___x_1316_ == 0)
{
v___y_1307_ = v___y_1313_;
goto v___jp_1306_;
}
else
{
lean_object* v___x_1317_; 
v___x_1317_ = lean_array_fswap(v___y_1313_, v_lo_1289_, v_hi_1290_);
v___y_1307_ = v___x_1317_;
goto v___jp_1306_;
}
}
}
v___jp_1291_:
{
lean_object* v_pivot_1293_; lean_object* v___x_1294_; lean_object* v_fst_1295_; lean_object* v_snd_1296_; uint8_t v___x_1297_; 
v_pivot_1293_ = lean_array_fget(v___y_1292_, v_hi_1290_);
lean_inc_n(v_lo_1289_, 2);
v___x_1294_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1_spec__1___redArg(v_hi_1290_, v_pivot_1293_, v___y_1292_, v_lo_1289_, v_lo_1289_);
lean_dec(v_pivot_1293_);
v_fst_1295_ = lean_ctor_get(v___x_1294_, 0);
lean_inc(v_fst_1295_);
v_snd_1296_ = lean_ctor_get(v___x_1294_, 1);
lean_inc(v_snd_1296_);
lean_dec_ref(v___x_1294_);
v___x_1297_ = lean_nat_dec_le(v_hi_1290_, v_fst_1295_);
if (v___x_1297_ == 0)
{
lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; 
v___x_1298_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1___redArg(v_n_1287_, v_snd_1296_, v_lo_1289_, v_fst_1295_);
v___x_1299_ = lean_unsigned_to_nat(1u);
v___x_1300_ = lean_nat_add(v_fst_1295_, v___x_1299_);
lean_dec(v_fst_1295_);
v_as_1288_ = v___x_1298_;
v_lo_1289_ = v___x_1300_;
goto _start;
}
else
{
lean_dec(v_fst_1295_);
lean_dec(v_lo_1289_);
return v_snd_1296_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1___redArg___boxed(lean_object* v_n_1322_, lean_object* v_as_1323_, lean_object* v_lo_1324_, lean_object* v_hi_1325_){
_start:
{
lean_object* v_res_1326_; 
v_res_1326_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1___redArg(v_n_1322_, v_as_1323_, v_lo_1324_, v_hi_1325_);
lean_dec(v_hi_1325_);
lean_dec(v_n_1322_);
return v_res_1326_;
}
}
static lean_object* _init_l_Lean_Level_normalize___closed__3(void){
_start:
{
lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; 
v___x_1331_ = ((lean_object*)(l_Lean_Level_normalize___closed__2));
v___x_1332_ = lean_unsigned_to_nat(11u);
v___x_1333_ = lean_unsigned_to_nat(403u);
v___x_1334_ = ((lean_object*)(l_Lean_Level_normalize___closed__1));
v___x_1335_ = ((lean_object*)(l_Lean_Level_mvarId_x21___closed__0));
v___x_1336_ = l_mkPanicMessageWithDecl(v___x_1335_, v___x_1334_, v___x_1333_, v___x_1332_, v___x_1331_);
return v___x_1336_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_normalize(lean_object* v_l_1337_){
_start:
{
uint8_t v___x_1338_; 
v___x_1338_ = l_Lean_Level_isAlreadyNormalizedCheap(v_l_1337_);
if (v___x_1338_ == 0)
{
lean_object* v_k_1339_; lean_object* v_u_1340_; 
v_k_1339_ = l_Lean_Level_getOffset(v_l_1337_);
v_u_1340_ = l_Lean_Level_getLevelOffset(v_l_1337_);
switch(lean_obj_tag(v_u_1340_))
{
case 2:
{
lean_object* v_a_1341_; lean_object* v_a_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v_lvls_1346_; lean_object* v_lvls_1347_; lean_object* v___x_1348_; lean_object* v___y_1350_; lean_object* v___y_1351_; lean_object* v___y_1358_; lean_object* v___x_1362_; lean_object* v___y_1364_; lean_object* v___y_1365_; uint8_t v___x_1367_; 
v_a_1341_ = lean_ctor_get(v_u_1340_, 0);
lean_inc(v_a_1341_);
v_a_1342_ = lean_ctor_get(v_u_1340_, 1);
lean_inc(v_a_1342_);
lean_dec_ref_known(v_u_1340_, 2);
v___x_1343_ = lean_box(0);
v___x_1344_ = lean_unsigned_to_nat(0u);
v___x_1345_ = ((lean_object*)(l_Lean_Level_normalize___closed__0));
v_lvls_1346_ = l___private_Lean_Level_0__Lean_Level_getMaxArgsAux___at___00Lean_Level_normalize_spec__0(v_a_1341_, v___x_1338_, v___x_1345_);
v_lvls_1347_ = l___private_Lean_Level_0__Lean_Level_getMaxArgsAux___at___00Lean_Level_normalize_spec__0(v_a_1342_, v___x_1338_, v_lvls_1346_);
v___x_1348_ = lean_unsigned_to_nat(1u);
v___x_1362_ = lean_array_get_size(v_lvls_1347_);
v___x_1367_ = lean_nat_dec_eq(v___x_1362_, v___x_1344_);
if (v___x_1367_ == 0)
{
lean_object* v___x_1368_; lean_object* v___y_1370_; uint8_t v___x_1372_; 
v___x_1368_ = lean_nat_sub(v___x_1362_, v___x_1348_);
v___x_1372_ = lean_nat_dec_le(v___x_1344_, v___x_1368_);
if (v___x_1372_ == 0)
{
lean_inc(v___x_1368_);
v___y_1370_ = v___x_1368_;
goto v___jp_1369_;
}
else
{
v___y_1370_ = v___x_1344_;
goto v___jp_1369_;
}
v___jp_1369_:
{
uint8_t v___x_1371_; 
v___x_1371_ = lean_nat_dec_le(v___y_1370_, v___x_1368_);
if (v___x_1371_ == 0)
{
lean_dec(v___x_1368_);
lean_inc(v___y_1370_);
v___y_1364_ = v___y_1370_;
v___y_1365_ = v___y_1370_;
goto v___jp_1363_;
}
else
{
v___y_1364_ = v___y_1370_;
v___y_1365_ = v___x_1368_;
goto v___jp_1363_;
}
}
}
else
{
v___y_1358_ = v_lvls_1347_;
goto v___jp_1357_;
}
v___jp_1349_:
{
lean_object* v_lvl_u2081_1352_; lean_object* v_prev_1353_; lean_object* v_prevK_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; 
v_lvl_u2081_1352_ = lean_array_get_borrowed(v___x_1343_, v___y_1350_, v___y_1351_);
v_prev_1353_ = l_Lean_Level_getLevelOffset(v_lvl_u2081_1352_);
v_prevK_1354_ = l_Lean_Level_getOffset(v_lvl_u2081_1352_);
v___x_1355_ = lean_nat_add(v___y_1351_, v___x_1348_);
lean_dec(v___y_1351_);
v___x_1356_ = l___private_Lean_Level_0__Lean_Level_mkMaxAux(v___y_1350_, v_k_1339_, v___x_1355_, v_prev_1353_, v_prevK_1354_, v___x_1343_);
lean_dec(v_k_1339_);
lean_dec_ref(v___y_1350_);
return v___x_1356_;
}
v___jp_1357_:
{
lean_object* v_firstNonExplicit_1359_; uint8_t v___x_1360_; 
v_firstNonExplicit_1359_ = l___private_Lean_Level_0__Lean_Level_skipExplicit(v___y_1358_, v___x_1344_);
lean_inc(v_firstNonExplicit_1359_);
v___x_1360_ = l___private_Lean_Level_0__Lean_Level_isExplicitSubsumed(v___y_1358_, v_firstNonExplicit_1359_);
if (v___x_1360_ == 0)
{
lean_object* v___x_1361_; 
v___x_1361_ = lean_nat_sub(v_firstNonExplicit_1359_, v___x_1348_);
lean_dec(v_firstNonExplicit_1359_);
v___y_1350_ = v___y_1358_;
v___y_1351_ = v___x_1361_;
goto v___jp_1349_;
}
else
{
v___y_1350_ = v___y_1358_;
v___y_1351_ = v_firstNonExplicit_1359_;
goto v___jp_1349_;
}
}
v___jp_1363_:
{
lean_object* v___x_1366_; 
v___x_1366_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1___redArg(v___x_1362_, v_lvls_1347_, v___y_1364_, v___y_1365_);
lean_dec(v___y_1365_);
v___y_1358_ = v___x_1366_;
goto v___jp_1357_;
}
}
case 3:
{
lean_object* v_a_1373_; lean_object* v_a_1374_; uint8_t v___x_1375_; 
v_a_1373_ = lean_ctor_get(v_u_1340_, 0);
lean_inc(v_a_1373_);
v_a_1374_ = lean_ctor_get(v_u_1340_, 1);
lean_inc(v_a_1374_);
lean_dec_ref_known(v_u_1340_, 2);
v___x_1375_ = l_Lean_Level_isNeverZero(v_a_1374_);
if (v___x_1375_ == 0)
{
lean_object* v_l_u2081_1376_; lean_object* v_l_u2082_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; 
v_l_u2081_1376_ = l_Lean_Level_normalize(v_a_1373_);
lean_dec(v_a_1373_);
v_l_u2082_1377_ = l_Lean_Level_normalize(v_a_1374_);
lean_dec(v_a_1374_);
v___x_1378_ = l___private_Lean_Level_0__Lean_Level_mkIMaxAux(v_l_u2081_1376_, v_l_u2082_1377_);
v___x_1379_ = l_Lean_Level_addOffsetAux(v_k_1339_, v___x_1378_);
return v___x_1379_;
}
else
{
lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; 
v___x_1380_ = l_Lean_Level_max___override(v_a_1373_, v_a_1374_);
v___x_1381_ = l_Lean_Level_normalize(v___x_1380_);
lean_dec(v___x_1380_);
v___x_1382_ = l_Lean_Level_addOffsetAux(v_k_1339_, v___x_1381_);
return v___x_1382_;
}
}
default: 
{
lean_object* v___x_1383_; lean_object* v___x_1384_; 
lean_dec(v_u_1340_);
lean_dec(v_k_1339_);
v___x_1383_ = lean_obj_once(&l_Lean_Level_normalize___closed__3, &l_Lean_Level_normalize___closed__3_once, _init_l_Lean_Level_normalize___closed__3);
v___x_1384_ = l_panic___at___00Lean_Level_normalize_spec__2(v___x_1383_);
return v___x_1384_;
}
}
}
else
{
lean_inc(v_l_1337_);
return v_l_1337_;
}
}
}
lean_object* l___private_Lean_Level_0__Lean_Level_getMaxArgsAux___at___00Lean_Level_normalize_spec__0(lean_object* v_x_1385_, uint8_t v_x_1386_, lean_object* v_x_1387_){
_start:
{
if (lean_obj_tag(v_x_1385_) == 2)
{
lean_object* v_a_1388_; lean_object* v_a_1389_; lean_object* v___x_1390_; 
v_a_1388_ = lean_ctor_get(v_x_1385_, 0);
lean_inc(v_a_1388_);
v_a_1389_ = lean_ctor_get(v_x_1385_, 1);
lean_inc(v_a_1389_);
lean_dec_ref_known(v_x_1385_, 2);
v___x_1390_ = l___private_Lean_Level_0__Lean_Level_getMaxArgsAux___at___00Lean_Level_normalize_spec__0(v_a_1388_, v_x_1386_, v_x_1387_);
v_x_1385_ = v_a_1389_;
v_x_1387_ = v___x_1390_;
goto _start;
}
else
{
if (v_x_1386_ == 0)
{
lean_object* v___x_1392_; uint8_t v___x_1393_; 
v___x_1392_ = l_Lean_Level_normalize(v_x_1385_);
lean_dec(v_x_1385_);
v___x_1393_ = 1;
v_x_1385_ = v___x_1392_;
v_x_1386_ = v___x_1393_;
goto _start;
}
else
{
lean_object* v___x_1395_; 
v___x_1395_ = lean_array_push(v_x_1387_, v_x_1385_);
return v___x_1395_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Level_0__Lean_Level_getMaxArgsAux___at___00Lean_Level_normalize_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1385_ = stack[0].m_obj;
uint8_t v_x_1386_ = stack[1].m_num;
lean_object* v_x_1387_ = stack[2].m_obj;
lean_object* v_res_1396_;
v_res_1396_ = l___private_Lean_Level_0__Lean_Level_getMaxArgsAux___at___00Lean_Level_normalize_spec__0(v_x_1385_, v_x_1386_, v_x_1387_);
stack->m_obj
 = v_res_1396_;
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_getMaxArgsAux___at___00Lean_Level_normalize_spec__0___boxed(lean_object* v_x_1397_, lean_object* v_x_1398_, lean_object* v_x_1399_){
_start:
{
uint8_t v_x_527__boxed_1400_; lean_object* v_res_1401_; 
v_x_527__boxed_1400_ = lean_unbox(v_x_1398_);
v_res_1401_ = l___private_Lean_Level_0__Lean_Level_getMaxArgsAux___at___00Lean_Level_normalize_spec__0(v_x_1397_, v_x_527__boxed_1400_, v_x_1399_);
return v_res_1401_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_normalize___boxed(lean_object* v_l_1402_){
_start:
{
lean_object* v_res_1403_; 
v_res_1403_ = l_Lean_Level_normalize(v_l_1402_);
lean_dec(v_l_1402_);
return v_res_1403_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1(lean_object* v_n_1404_, lean_object* v_as_1405_, lean_object* v_lo_1406_, lean_object* v_hi_1407_, lean_object* v_w_1408_, lean_object* v_hlo_1409_, lean_object* v_hhi_1410_){
_start:
{
lean_object* v___x_1411_; 
v___x_1411_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1___redArg(v_n_1404_, v_as_1405_, v_lo_1406_, v_hi_1407_);
return v___x_1411_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1___boxed(lean_object* v_n_1412_, lean_object* v_as_1413_, lean_object* v_lo_1414_, lean_object* v_hi_1415_, lean_object* v_w_1416_, lean_object* v_hlo_1417_, lean_object* v_hhi_1418_){
_start:
{
lean_object* v_res_1419_; 
v_res_1419_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1(v_n_1412_, v_as_1413_, v_lo_1414_, v_hi_1415_, v_w_1416_, v_hlo_1417_, v_hhi_1418_);
lean_dec(v_hi_1415_);
lean_dec(v_n_1412_);
return v_res_1419_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1_spec__1(lean_object* v_n_1420_, lean_object* v_lo_1421_, lean_object* v_hi_1422_, lean_object* v_hhi_1423_, lean_object* v_pivot_1424_, lean_object* v_as_1425_, lean_object* v_i_1426_, lean_object* v_k_1427_, lean_object* v_ilo_1428_, lean_object* v_ik_1429_, lean_object* v_w_1430_){
_start:
{
lean_object* v___x_1431_; 
v___x_1431_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1_spec__1___redArg(v_hi_1422_, v_pivot_1424_, v_as_1425_, v_i_1426_, v_k_1427_);
return v___x_1431_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1_spec__1___boxed(lean_object* v_n_1432_, lean_object* v_lo_1433_, lean_object* v_hi_1434_, lean_object* v_hhi_1435_, lean_object* v_pivot_1436_, lean_object* v_as_1437_, lean_object* v_i_1438_, lean_object* v_k_1439_, lean_object* v_ilo_1440_, lean_object* v_ik_1441_, lean_object* v_w_1442_){
_start:
{
lean_object* v_res_1443_; 
v_res_1443_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1_spec__1(v_n_1432_, v_lo_1433_, v_hi_1434_, v_hhi_1435_, v_pivot_1436_, v_as_1437_, v_i_1438_, v_k_1439_, v_ilo_1440_, v_ik_1441_, v_w_1442_);
lean_dec(v_pivot_1436_);
lean_dec(v_hi_1434_);
lean_dec(v_lo_1433_);
lean_dec(v_n_1432_);
return v_res_1443_;
}
}
uint8_t l_Lean_Level_isEquiv(lean_object* v_u_1444_, lean_object* v_v_1445_){
_start:
{
uint8_t v___x_1446_; 
v___x_1446_ = lean_level_eq(v_u_1444_, v_v_1445_);
if (v___x_1446_ == 0)
{
lean_object* v___x_1447_; lean_object* v___x_1448_; uint8_t v___x_1449_; 
v___x_1447_ = l_Lean_Level_normalize(v_u_1444_);
v___x_1448_ = l_Lean_Level_normalize(v_v_1445_);
v___x_1449_ = lean_level_eq(v___x_1447_, v___x_1448_);
lean_dec(v___x_1448_);
lean_dec(v___x_1447_);
return v___x_1449_;
}
else
{
return v___x_1446_;
}
}
}
LEAN_EXPORT void l_Lean_Level_isEquiv_0interp(lean_interpreter_value* stack)
{
lean_object* v_u_1444_ = stack[0].m_obj;
lean_object* v_v_1445_ = stack[1].m_obj;
uint8_t v_res_1450_;
v_res_1450_ = l_Lean_Level_isEquiv(v_u_1444_, v_v_1445_);
stack->m_num = v_res_1450_;
}
LEAN_EXPORT lean_object* l_Lean_Level_isEquiv___boxed(lean_object* v_u_1451_, lean_object* v_v_1452_){
_start:
{
uint8_t v_res_1453_; lean_object* v_r_1454_; 
v_res_1453_ = l_Lean_Level_isEquiv(v_u_1451_, v_v_1452_);
lean_dec(v_v_1452_);
lean_dec(v_u_1451_);
v_r_1454_ = lean_box(v_res_1453_);
return v_r_1454_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_dec(lean_object* v_x_1455_){
_start:
{
lean_object* v_l_u2081_1457_; lean_object* v_l_u2082_1458_; 
switch(lean_obj_tag(v_x_1455_))
{
case 1:
{
lean_object* v_a_1471_; lean_object* v___x_1472_; 
v_a_1471_ = lean_ctor_get(v_x_1455_, 0);
lean_inc(v_a_1471_);
v___x_1472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1472_, 0, v_a_1471_);
return v___x_1472_;
}
case 2:
{
lean_object* v_a_1473_; lean_object* v_a_1474_; 
v_a_1473_ = lean_ctor_get(v_x_1455_, 0);
v_a_1474_ = lean_ctor_get(v_x_1455_, 1);
v_l_u2081_1457_ = v_a_1473_;
v_l_u2082_1458_ = v_a_1474_;
goto v___jp_1456_;
}
case 3:
{
lean_object* v_a_1475_; lean_object* v_a_1476_; 
v_a_1475_ = lean_ctor_get(v_x_1455_, 0);
v_a_1476_ = lean_ctor_get(v_x_1455_, 1);
v_l_u2081_1457_ = v_a_1475_;
v_l_u2082_1458_ = v_a_1476_;
goto v___jp_1456_;
}
default: 
{
lean_object* v___x_1477_; 
v___x_1477_ = lean_box(0);
return v___x_1477_;
}
}
v___jp_1456_:
{
lean_object* v___x_1459_; 
v___x_1459_ = l_Lean_Level_dec(v_l_u2081_1457_);
if (lean_obj_tag(v___x_1459_) == 0)
{
return v___x_1459_;
}
else
{
lean_object* v_val_1460_; lean_object* v___x_1461_; 
v_val_1460_ = lean_ctor_get(v___x_1459_, 0);
lean_inc(v_val_1460_);
lean_dec_ref_known(v___x_1459_, 1);
v___x_1461_ = l_Lean_Level_dec(v_l_u2082_1458_);
if (lean_obj_tag(v___x_1461_) == 0)
{
lean_dec(v_val_1460_);
return v___x_1461_;
}
else
{
lean_object* v_val_1462_; lean_object* v___x_1464_; uint8_t v_isShared_1465_; uint8_t v_isSharedCheck_1470_; 
v_val_1462_ = lean_ctor_get(v___x_1461_, 0);
v_isSharedCheck_1470_ = !lean_is_exclusive(v___x_1461_);
if (v_isSharedCheck_1470_ == 0)
{
v___x_1464_ = v___x_1461_;
v_isShared_1465_ = v_isSharedCheck_1470_;
goto v_resetjp_1463_;
}
else
{
lean_inc(v_val_1462_);
lean_dec(v___x_1461_);
v___x_1464_ = lean_box(0);
v_isShared_1465_ = v_isSharedCheck_1470_;
goto v_resetjp_1463_;
}
v_resetjp_1463_:
{
lean_object* v___x_1466_; lean_object* v___x_1468_; 
v___x_1466_ = l_Lean_Level_max___override(v_val_1460_, v_val_1462_);
if (v_isShared_1465_ == 0)
{
lean_ctor_set(v___x_1464_, 0, v___x_1466_);
v___x_1468_ = v___x_1464_;
goto v_reusejp_1467_;
}
else
{
lean_object* v_reuseFailAlloc_1469_; 
v_reuseFailAlloc_1469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1469_, 0, v___x_1466_);
v___x_1468_ = v_reuseFailAlloc_1469_;
goto v_reusejp_1467_;
}
v_reusejp_1467_:
{
return v___x_1468_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_dec___boxed(lean_object* v_x_1478_){
_start:
{
lean_object* v_res_1479_; 
v_res_1479_ = l_Lean_Level_dec(v_x_1478_);
lean_dec(v_x_1478_);
return v_res_1479_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_ctorIdx___impl(lean_object* v_x_1480_){
_start:
{
lean_object* v___x_1481_; 
v___x_1481_ = lean_obj_tag_nat(v_x_1480_);
return v___x_1481_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_ctorIdx___impl___boxed(lean_object* v_x_1482_){
_start:
{
lean_object* v_res_1483_; 
v_res_1483_ = l_Lean_Level_PP_Result_ctorIdx___impl(v_x_1482_);
lean_dec_ref(v_x_1482_);
return v_res_1483_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_ctorElim___redArg(lean_object* v_t_1484_, lean_object* v_k_1485_){
_start:
{
if (lean_obj_tag(v_t_1484_) == 2)
{
lean_object* v_a_1486_; lean_object* v_a_1487_; lean_object* v___x_1488_; 
v_a_1486_ = lean_ctor_get(v_t_1484_, 0);
lean_inc_ref(v_a_1486_);
v_a_1487_ = lean_ctor_get(v_t_1484_, 1);
lean_inc(v_a_1487_);
lean_dec_ref_known(v_t_1484_, 2);
v___x_1488_ = lean_apply_2(v_k_1485_, v_a_1486_, v_a_1487_);
return v___x_1488_;
}
else
{
lean_object* v_a_1489_; lean_object* v___x_1490_; 
v_a_1489_ = lean_ctor_get(v_t_1484_, 0);
lean_inc(v_a_1489_);
lean_dec_ref(v_t_1484_);
v___x_1490_ = lean_apply_1(v_k_1485_, v_a_1489_);
return v___x_1490_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_ctorElim(lean_object* v_motive__1_1491_, lean_object* v_ctorIdx_1492_, lean_object* v_t_1493_, lean_object* v_h_1494_, lean_object* v_k_1495_){
_start:
{
lean_object* v___x_1496_; 
v___x_1496_ = l_Lean_Level_PP_Result_ctorElim___redArg(v_t_1493_, v_k_1495_);
return v___x_1496_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_ctorElim___boxed(lean_object* v_motive__1_1497_, lean_object* v_ctorIdx_1498_, lean_object* v_t_1499_, lean_object* v_h_1500_, lean_object* v_k_1501_){
_start:
{
lean_object* v_res_1502_; 
v_res_1502_ = l_Lean_Level_PP_Result_ctorElim(v_motive__1_1497_, v_ctorIdx_1498_, v_t_1499_, v_h_1500_, v_k_1501_);
lean_dec(v_ctorIdx_1498_);
return v_res_1502_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_leaf_elim___redArg(lean_object* v_t_1503_, lean_object* v_leaf_1504_){
_start:
{
lean_object* v___x_1505_; 
v___x_1505_ = l_Lean_Level_PP_Result_ctorElim___redArg(v_t_1503_, v_leaf_1504_);
return v___x_1505_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_leaf_elim(lean_object* v_motive__1_1506_, lean_object* v_t_1507_, lean_object* v_h_1508_, lean_object* v_leaf_1509_){
_start:
{
lean_object* v___x_1510_; 
v___x_1510_ = l_Lean_Level_PP_Result_ctorElim___redArg(v_t_1507_, v_leaf_1509_);
return v___x_1510_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_num_elim___redArg(lean_object* v_t_1511_, lean_object* v_num_1512_){
_start:
{
lean_object* v___x_1513_; 
v___x_1513_ = l_Lean_Level_PP_Result_ctorElim___redArg(v_t_1511_, v_num_1512_);
return v___x_1513_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_num_elim(lean_object* v_motive__1_1514_, lean_object* v_t_1515_, lean_object* v_h_1516_, lean_object* v_num_1517_){
_start:
{
lean_object* v___x_1518_; 
v___x_1518_ = l_Lean_Level_PP_Result_ctorElim___redArg(v_t_1515_, v_num_1517_);
return v___x_1518_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_offset_elim___redArg(lean_object* v_t_1519_, lean_object* v_offset_1520_){
_start:
{
lean_object* v___x_1521_; 
v___x_1521_ = l_Lean_Level_PP_Result_ctorElim___redArg(v_t_1519_, v_offset_1520_);
return v___x_1521_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_offset_elim(lean_object* v_motive__1_1522_, lean_object* v_t_1523_, lean_object* v_h_1524_, lean_object* v_offset_1525_){
_start:
{
lean_object* v___x_1526_; 
v___x_1526_ = l_Lean_Level_PP_Result_ctorElim___redArg(v_t_1523_, v_offset_1525_);
return v___x_1526_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_maxNode_elim___redArg(lean_object* v_t_1527_, lean_object* v_maxNode_1528_){
_start:
{
lean_object* v___x_1529_; 
v___x_1529_ = l_Lean_Level_PP_Result_ctorElim___redArg(v_t_1527_, v_maxNode_1528_);
return v___x_1529_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_maxNode_elim(lean_object* v_motive__1_1530_, lean_object* v_t_1531_, lean_object* v_h_1532_, lean_object* v_maxNode_1533_){
_start:
{
lean_object* v___x_1534_; 
v___x_1534_ = l_Lean_Level_PP_Result_ctorElim___redArg(v_t_1531_, v_maxNode_1533_);
return v___x_1534_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_imaxNode_elim___redArg(lean_object* v_t_1535_, lean_object* v_imaxNode_1536_){
_start:
{
lean_object* v___x_1537_; 
v___x_1537_ = l_Lean_Level_PP_Result_ctorElim___redArg(v_t_1535_, v_imaxNode_1536_);
return v___x_1537_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_imaxNode_elim(lean_object* v_motive__1_1538_, lean_object* v_t_1539_, lean_object* v_h_1540_, lean_object* v_imaxNode_1541_){
_start:
{
lean_object* v___x_1542_; 
v___x_1542_ = l_Lean_Level_PP_Result_ctorElim___redArg(v_t_1539_, v_imaxNode_1541_);
return v___x_1542_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_succ(lean_object* v_x_1543_){
_start:
{
switch(lean_obj_tag(v_x_1543_))
{
case 2:
{
lean_object* v_a_1544_; lean_object* v_a_1545_; lean_object* v___x_1547_; uint8_t v_isShared_1548_; uint8_t v_isSharedCheck_1554_; 
v_a_1544_ = lean_ctor_get(v_x_1543_, 0);
v_a_1545_ = lean_ctor_get(v_x_1543_, 1);
v_isSharedCheck_1554_ = !lean_is_exclusive(v_x_1543_);
if (v_isSharedCheck_1554_ == 0)
{
v___x_1547_ = v_x_1543_;
v_isShared_1548_ = v_isSharedCheck_1554_;
goto v_resetjp_1546_;
}
else
{
lean_inc(v_a_1545_);
lean_inc(v_a_1544_);
lean_dec(v_x_1543_);
v___x_1547_ = lean_box(0);
v_isShared_1548_ = v_isSharedCheck_1554_;
goto v_resetjp_1546_;
}
v_resetjp_1546_:
{
lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1552_; 
v___x_1549_ = lean_unsigned_to_nat(1u);
v___x_1550_ = lean_nat_add(v_a_1545_, v___x_1549_);
lean_dec(v_a_1545_);
if (v_isShared_1548_ == 0)
{
lean_ctor_set(v___x_1547_, 1, v___x_1550_);
v___x_1552_ = v___x_1547_;
goto v_reusejp_1551_;
}
else
{
lean_object* v_reuseFailAlloc_1553_; 
v_reuseFailAlloc_1553_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1553_, 0, v_a_1544_);
lean_ctor_set(v_reuseFailAlloc_1553_, 1, v___x_1550_);
v___x_1552_ = v_reuseFailAlloc_1553_;
goto v_reusejp_1551_;
}
v_reusejp_1551_:
{
return v___x_1552_;
}
}
}
case 1:
{
lean_object* v_a_1555_; lean_object* v___x_1557_; uint8_t v_isShared_1558_; uint8_t v_isSharedCheck_1564_; 
v_a_1555_ = lean_ctor_get(v_x_1543_, 0);
v_isSharedCheck_1564_ = !lean_is_exclusive(v_x_1543_);
if (v_isSharedCheck_1564_ == 0)
{
v___x_1557_ = v_x_1543_;
v_isShared_1558_ = v_isSharedCheck_1564_;
goto v_resetjp_1556_;
}
else
{
lean_inc(v_a_1555_);
lean_dec(v_x_1543_);
v___x_1557_ = lean_box(0);
v_isShared_1558_ = v_isSharedCheck_1564_;
goto v_resetjp_1556_;
}
v_resetjp_1556_:
{
lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1562_; 
v___x_1559_ = lean_unsigned_to_nat(1u);
v___x_1560_ = lean_nat_add(v_a_1555_, v___x_1559_);
lean_dec(v_a_1555_);
if (v_isShared_1558_ == 0)
{
lean_ctor_set(v___x_1557_, 0, v___x_1560_);
v___x_1562_ = v___x_1557_;
goto v_reusejp_1561_;
}
else
{
lean_object* v_reuseFailAlloc_1563_; 
v_reuseFailAlloc_1563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1563_, 0, v___x_1560_);
v___x_1562_ = v_reuseFailAlloc_1563_;
goto v_reusejp_1561_;
}
v_reusejp_1561_:
{
return v___x_1562_;
}
}
}
default: 
{
lean_object* v___x_1565_; lean_object* v___x_1566_; 
v___x_1565_ = lean_unsigned_to_nat(1u);
v___x_1566_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1566_, 0, v_x_1543_);
lean_ctor_set(v___x_1566_, 1, v___x_1565_);
return v___x_1566_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_max(lean_object* v_x_1567_, lean_object* v_x_1568_){
_start:
{
if (lean_obj_tag(v_x_1568_) == 3)
{
lean_object* v_a_1569_; lean_object* v___x_1571_; uint8_t v_isShared_1572_; uint8_t v_isSharedCheck_1577_; 
v_a_1569_ = lean_ctor_get(v_x_1568_, 0);
v_isSharedCheck_1577_ = !lean_is_exclusive(v_x_1568_);
if (v_isSharedCheck_1577_ == 0)
{
v___x_1571_ = v_x_1568_;
v_isShared_1572_ = v_isSharedCheck_1577_;
goto v_resetjp_1570_;
}
else
{
lean_inc(v_a_1569_);
lean_dec(v_x_1568_);
v___x_1571_ = lean_box(0);
v_isShared_1572_ = v_isSharedCheck_1577_;
goto v_resetjp_1570_;
}
v_resetjp_1570_:
{
lean_object* v___x_1573_; lean_object* v___x_1575_; 
v___x_1573_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1573_, 0, v_x_1567_);
lean_ctor_set(v___x_1573_, 1, v_a_1569_);
if (v_isShared_1572_ == 0)
{
lean_ctor_set(v___x_1571_, 0, v___x_1573_);
v___x_1575_ = v___x_1571_;
goto v_reusejp_1574_;
}
else
{
lean_object* v_reuseFailAlloc_1576_; 
v_reuseFailAlloc_1576_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1576_, 0, v___x_1573_);
v___x_1575_ = v_reuseFailAlloc_1576_;
goto v_reusejp_1574_;
}
v_reusejp_1574_:
{
return v___x_1575_;
}
}
}
else
{
lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; 
v___x_1578_ = lean_box(0);
v___x_1579_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1579_, 0, v_x_1568_);
lean_ctor_set(v___x_1579_, 1, v___x_1578_);
v___x_1580_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1580_, 0, v_x_1567_);
lean_ctor_set(v___x_1580_, 1, v___x_1579_);
v___x_1581_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1581_, 0, v___x_1580_);
return v___x_1581_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_imax(lean_object* v_x_1582_, lean_object* v_x_1583_){
_start:
{
if (lean_obj_tag(v_x_1583_) == 4)
{
lean_object* v_a_1584_; lean_object* v___x_1586_; uint8_t v_isShared_1587_; uint8_t v_isSharedCheck_1592_; 
v_a_1584_ = lean_ctor_get(v_x_1583_, 0);
v_isSharedCheck_1592_ = !lean_is_exclusive(v_x_1583_);
if (v_isSharedCheck_1592_ == 0)
{
v___x_1586_ = v_x_1583_;
v_isShared_1587_ = v_isSharedCheck_1592_;
goto v_resetjp_1585_;
}
else
{
lean_inc(v_a_1584_);
lean_dec(v_x_1583_);
v___x_1586_ = lean_box(0);
v_isShared_1587_ = v_isSharedCheck_1592_;
goto v_resetjp_1585_;
}
v_resetjp_1585_:
{
lean_object* v___x_1588_; lean_object* v___x_1590_; 
v___x_1588_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1588_, 0, v_x_1582_);
lean_ctor_set(v___x_1588_, 1, v_a_1584_);
if (v_isShared_1587_ == 0)
{
lean_ctor_set(v___x_1586_, 0, v___x_1588_);
v___x_1590_ = v___x_1586_;
goto v_reusejp_1589_;
}
else
{
lean_object* v_reuseFailAlloc_1591_; 
v_reuseFailAlloc_1591_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1591_, 0, v___x_1588_);
v___x_1590_ = v_reuseFailAlloc_1591_;
goto v_reusejp_1589_;
}
v_reusejp_1589_:
{
return v___x_1590_;
}
}
}
else
{
lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; 
v___x_1593_ = lean_box(0);
v___x_1594_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1594_, 0, v_x_1583_);
lean_ctor_set(v___x_1594_, 1, v___x_1593_);
v___x_1595_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1595_, 0, v_x_1582_);
lean_ctor_set(v___x_1595_, 1, v___x_1594_);
v___x_1596_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1596_, 0, v___x_1595_);
return v___x_1596_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_toResult(lean_object* v_l_1615_, lean_object* v_a_1616_){
_start:
{
switch(lean_obj_tag(v_l_1615_))
{
case 0:
{
lean_object* v___x_1617_; 
v___x_1617_ = ((lean_object*)(l_Lean_Level_PP_toResult___closed__0));
return v___x_1617_;
}
case 1:
{
lean_object* v_a_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; 
v_a_1618_ = lean_ctor_get(v_l_1615_, 0);
lean_inc(v_a_1618_);
lean_dec_ref_known(v_l_1615_, 1);
v___x_1619_ = l_Lean_Level_PP_toResult(v_a_1618_, v_a_1616_);
v___x_1620_ = l_Lean_Level_PP_Result_succ(v___x_1619_);
return v___x_1620_;
}
case 2:
{
lean_object* v_a_1621_; lean_object* v_a_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; 
v_a_1621_ = lean_ctor_get(v_l_1615_, 0);
lean_inc(v_a_1621_);
v_a_1622_ = lean_ctor_get(v_l_1615_, 1);
lean_inc(v_a_1622_);
lean_dec_ref_known(v_l_1615_, 2);
v___x_1623_ = l_Lean_Level_PP_toResult(v_a_1621_, v_a_1616_);
v___x_1624_ = l_Lean_Level_PP_toResult(v_a_1622_, v_a_1616_);
v___x_1625_ = l_Lean_Level_PP_Result_max(v___x_1623_, v___x_1624_);
return v___x_1625_;
}
case 3:
{
lean_object* v_a_1626_; lean_object* v_a_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; 
v_a_1626_ = lean_ctor_get(v_l_1615_, 0);
lean_inc(v_a_1626_);
v_a_1627_ = lean_ctor_get(v_l_1615_, 1);
lean_inc(v_a_1627_);
lean_dec_ref_known(v_l_1615_, 2);
v___x_1628_ = l_Lean_Level_PP_toResult(v_a_1626_, v_a_1616_);
v___x_1629_ = l_Lean_Level_PP_toResult(v_a_1627_, v_a_1616_);
v___x_1630_ = l_Lean_Level_PP_Result_imax(v___x_1628_, v___x_1629_);
return v___x_1630_;
}
case 4:
{
lean_object* v_a_1631_; lean_object* v___x_1632_; 
v_a_1631_ = lean_ctor_get(v_l_1615_, 0);
lean_inc(v_a_1631_);
lean_dec_ref_known(v_l_1615_, 1);
v___x_1632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1632_, 0, v_a_1631_);
return v___x_1632_;
}
default: 
{
uint8_t v_mvars_1633_; 
v_mvars_1633_ = lean_ctor_get_uint8(v_a_1616_, sizeof(void*)*1);
if (v_mvars_1633_ == 0)
{
lean_object* v___x_1634_; 
lean_dec_ref_known(v_l_1615_, 1);
v___x_1634_ = ((lean_object*)(l_Lean_Level_PP_toResult___closed__3));
return v___x_1634_;
}
else
{
lean_object* v_a_1635_; lean_object* v_lIndex_x3f_1636_; lean_object* v___x_1637_; 
v_a_1635_ = lean_ctor_get(v_l_1615_, 0);
lean_inc_n(v_a_1635_, 2);
lean_dec_ref_known(v_l_1615_, 1);
v_lIndex_x3f_1636_ = lean_ctor_get(v_a_1616_, 0);
lean_inc_ref(v_lIndex_x3f_1636_);
v___x_1637_ = lean_apply_1(v_lIndex_x3f_1636_, v_a_1635_);
if (lean_obj_tag(v___x_1637_) == 1)
{
lean_object* v_val_1638_; lean_object* v___x_1640_; uint8_t v_isShared_1641_; uint8_t v_isSharedCheck_1649_; 
lean_dec(v_a_1635_);
v_val_1638_ = lean_ctor_get(v___x_1637_, 0);
v_isSharedCheck_1649_ = !lean_is_exclusive(v___x_1637_);
if (v_isSharedCheck_1649_ == 0)
{
v___x_1640_ = v___x_1637_;
v_isShared_1641_ = v_isSharedCheck_1649_;
goto v_resetjp_1639_;
}
else
{
lean_inc(v_val_1638_);
lean_dec(v___x_1637_);
v___x_1640_ = lean_box(0);
v_isShared_1641_ = v_isSharedCheck_1649_;
goto v_resetjp_1639_;
}
v_resetjp_1639_:
{
lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1647_; 
v___x_1642_ = ((lean_object*)(l_Lean_Level_PP_toResult___closed__5));
v___x_1643_ = lean_unsigned_to_nat(1u);
v___x_1644_ = lean_nat_add(v_val_1638_, v___x_1643_);
lean_dec(v_val_1638_);
v___x_1645_ = l_Lean_Name_num___override(v___x_1642_, v___x_1644_);
if (v_isShared_1641_ == 0)
{
lean_ctor_set_tag(v___x_1640_, 0);
lean_ctor_set(v___x_1640_, 0, v___x_1645_);
v___x_1647_ = v___x_1640_;
goto v_reusejp_1646_;
}
else
{
lean_object* v_reuseFailAlloc_1648_; 
v_reuseFailAlloc_1648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1648_, 0, v___x_1645_);
v___x_1647_ = v_reuseFailAlloc_1648_;
goto v_reusejp_1646_;
}
v_reusejp_1646_:
{
return v___x_1647_;
}
}
}
else
{
lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; 
lean_dec(v___x_1637_);
v___x_1650_ = ((lean_object*)(l_Lean_Level_PP_toResult___closed__7));
v___x_1651_ = ((lean_object*)(l_Lean_Level_PP_toResult___closed__9));
v___x_1652_ = l_Lean_Name_replacePrefix(v_a_1635_, v___x_1650_, v___x_1651_);
v___x_1653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1653_, 0, v___x_1652_);
return v___x_1653_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_toResult___boxed(lean_object* v_l_1654_, lean_object* v_a_1655_){
_start:
{
lean_object* v_res_1656_; 
v_res_1656_ = l_Lean_Level_PP_toResult(v_l_1654_, v_a_1655_);
lean_dec_ref(v_a_1655_);
return v_res_1656_;
}
}
static lean_object* _init_l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__1(void){
_start:
{
lean_object* v___x_1658_; lean_object* v___x_1659_; 
v___x_1658_ = ((lean_object*)(l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__0));
v___x_1659_ = lean_string_length(v___x_1658_);
return v___x_1659_;
}
}
static lean_object* _init_l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__2(void){
_start:
{
lean_object* v___x_1660_; lean_object* v___x_1661_; 
v___x_1660_ = lean_obj_once(&l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__1, &l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__1_once, _init_l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__1);
v___x_1661_ = lean_nat_to_int(v___x_1660_);
return v___x_1661_;
}
}
lean_object* l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse(lean_object* v_x_1666_, uint8_t v_x_1667_){
_start:
{
if (v_x_1667_ == 0)
{
lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; uint8_t v___x_1674_; lean_object* v___x_1675_; 
v___x_1668_ = lean_obj_once(&l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__2, &l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__2_once, _init_l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__2);
v___x_1669_ = ((lean_object*)(l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__3));
v___x_1670_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1670_, 0, v___x_1669_);
lean_ctor_set(v___x_1670_, 1, v_x_1666_);
v___x_1671_ = ((lean_object*)(l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__4));
v___x_1672_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1672_, 0, v___x_1670_);
lean_ctor_set(v___x_1672_, 1, v___x_1671_);
v___x_1673_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1673_, 0, v___x_1668_);
lean_ctor_set(v___x_1673_, 1, v___x_1672_);
v___x_1674_ = 0;
v___x_1675_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1675_, 0, v___x_1673_);
lean_ctor_set_uint8(v___x_1675_, sizeof(void*)*1, v___x_1674_);
return v___x_1675_;
}
else
{
return v_x_1666_;
}
}
}
LEAN_EXPORT void l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1666_ = stack[0].m_obj;
uint8_t v_x_1667_ = stack[1].m_num;
lean_object* v_res_1676_;
v_res_1676_ = l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse(v_x_1666_, v_x_1667_);
stack->m_obj
 = v_res_1676_;
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___boxed(lean_object* v_x_1677_, lean_object* v_x_1678_){
_start:
{
uint8_t v_x_57__boxed_1679_; lean_object* v_res_1680_; 
v_x_57__boxed_1679_ = lean_unbox(v_x_1678_);
v_res_1680_ = l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse(v_x_1677_, v_x_57__boxed_1679_);
return v_res_1680_;
}
}
lean_object* l_Lean_Level_PP_Result_format(lean_object* v_x_1690_, uint8_t v_x_1691_){
_start:
{
switch(lean_obj_tag(v_x_1690_))
{
case 0:
{
lean_object* v_a_1692_; lean_object* v___x_1694_; uint8_t v_isShared_1695_; uint8_t v_isSharedCheck_1701_; 
v_a_1692_ = lean_ctor_get(v_x_1690_, 0);
v_isSharedCheck_1701_ = !lean_is_exclusive(v_x_1690_);
if (v_isSharedCheck_1701_ == 0)
{
v___x_1694_ = v_x_1690_;
v_isShared_1695_ = v_isSharedCheck_1701_;
goto v_resetjp_1693_;
}
else
{
lean_inc(v_a_1692_);
lean_dec(v_x_1690_);
v___x_1694_ = lean_box(0);
v_isShared_1695_ = v_isSharedCheck_1701_;
goto v_resetjp_1693_;
}
v_resetjp_1693_:
{
uint8_t v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1699_; 
v___x_1696_ = 1;
v___x_1697_ = l_Lean_Name_toString(v_a_1692_, v___x_1696_);
if (v_isShared_1695_ == 0)
{
lean_ctor_set_tag(v___x_1694_, 3);
lean_ctor_set(v___x_1694_, 0, v___x_1697_);
v___x_1699_ = v___x_1694_;
goto v_reusejp_1698_;
}
else
{
lean_object* v_reuseFailAlloc_1700_; 
v_reuseFailAlloc_1700_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1700_, 0, v___x_1697_);
v___x_1699_ = v_reuseFailAlloc_1700_;
goto v_reusejp_1698_;
}
v_reusejp_1698_:
{
return v___x_1699_;
}
}
}
case 1:
{
lean_object* v_a_1702_; lean_object* v___x_1704_; uint8_t v_isShared_1705_; uint8_t v_isSharedCheck_1710_; 
v_a_1702_ = lean_ctor_get(v_x_1690_, 0);
v_isSharedCheck_1710_ = !lean_is_exclusive(v_x_1690_);
if (v_isSharedCheck_1710_ == 0)
{
v___x_1704_ = v_x_1690_;
v_isShared_1705_ = v_isSharedCheck_1710_;
goto v_resetjp_1703_;
}
else
{
lean_inc(v_a_1702_);
lean_dec(v_x_1690_);
v___x_1704_ = lean_box(0);
v_isShared_1705_ = v_isSharedCheck_1710_;
goto v_resetjp_1703_;
}
v_resetjp_1703_:
{
lean_object* v___x_1706_; lean_object* v___x_1708_; 
v___x_1706_ = l_Nat_reprFast(v_a_1702_);
if (v_isShared_1705_ == 0)
{
lean_ctor_set_tag(v___x_1704_, 3);
lean_ctor_set(v___x_1704_, 0, v___x_1706_);
v___x_1708_ = v___x_1704_;
goto v_reusejp_1707_;
}
else
{
lean_object* v_reuseFailAlloc_1709_; 
v_reuseFailAlloc_1709_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1709_, 0, v___x_1706_);
v___x_1708_ = v_reuseFailAlloc_1709_;
goto v_reusejp_1707_;
}
v_reusejp_1707_:
{
return v___x_1708_;
}
}
}
case 2:
{
lean_object* v_a_1711_; lean_object* v_a_1712_; lean_object* v___x_1714_; uint8_t v_isShared_1715_; uint8_t v_isSharedCheck_1731_; 
v_a_1711_ = lean_ctor_get(v_x_1690_, 0);
v_a_1712_ = lean_ctor_get(v_x_1690_, 1);
v_isSharedCheck_1731_ = !lean_is_exclusive(v_x_1690_);
if (v_isSharedCheck_1731_ == 0)
{
v___x_1714_ = v_x_1690_;
v_isShared_1715_ = v_isSharedCheck_1731_;
goto v_resetjp_1713_;
}
else
{
lean_inc(v_a_1712_);
lean_inc(v_a_1711_);
lean_dec(v_x_1690_);
v___x_1714_ = lean_box(0);
v_isShared_1715_ = v_isSharedCheck_1731_;
goto v_resetjp_1713_;
}
v_resetjp_1713_:
{
lean_object* v_zero_1716_; uint8_t v_isZero_1717_; 
v_zero_1716_ = lean_unsigned_to_nat(0u);
v_isZero_1717_ = lean_nat_dec_eq(v_a_1712_, v_zero_1716_);
if (v_isZero_1717_ == 1)
{
lean_del_object(v___x_1714_);
lean_dec(v_a_1712_);
v_x_1690_ = v_a_1711_;
goto _start;
}
else
{
lean_object* v_one_1719_; lean_object* v_n_1720_; lean_object* v_f_x27_1721_; lean_object* v___x_1722_; lean_object* v___x_1724_; 
v_one_1719_ = lean_unsigned_to_nat(1u);
v_n_1720_ = lean_nat_sub(v_a_1712_, v_one_1719_);
lean_dec(v_a_1712_);
v_f_x27_1721_ = l_Lean_Level_PP_Result_format(v_a_1711_, v_isZero_1717_);
v___x_1722_ = ((lean_object*)(l_Lean_Level_PP_Result_format___closed__1));
if (v_isShared_1715_ == 0)
{
lean_ctor_set_tag(v___x_1714_, 5);
lean_ctor_set(v___x_1714_, 1, v___x_1722_);
lean_ctor_set(v___x_1714_, 0, v_f_x27_1721_);
v___x_1724_ = v___x_1714_;
goto v_reusejp_1723_;
}
else
{
lean_object* v_reuseFailAlloc_1730_; 
v_reuseFailAlloc_1730_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1730_, 0, v_f_x27_1721_);
lean_ctor_set(v_reuseFailAlloc_1730_, 1, v___x_1722_);
v___x_1724_ = v_reuseFailAlloc_1730_;
goto v_reusejp_1723_;
}
v_reusejp_1723_:
{
lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; 
v___x_1725_ = lean_nat_add(v_n_1720_, v_one_1719_);
lean_dec(v_n_1720_);
v___x_1726_ = l_Nat_reprFast(v___x_1725_);
v___x_1727_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1727_, 0, v___x_1726_);
v___x_1728_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1728_, 0, v___x_1724_);
lean_ctor_set(v___x_1728_, 1, v___x_1727_);
v___x_1729_ = l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse(v___x_1728_, v_x_1691_);
return v___x_1729_;
}
}
}
}
case 3:
{
lean_object* v_a_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; uint8_t v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; 
v_a_1732_ = lean_ctor_get(v_x_1690_, 0);
lean_inc(v_a_1732_);
lean_dec_ref_known(v_x_1690_, 1);
v___x_1733_ = ((lean_object*)(l_Lean_Level_PP_Result_format___closed__3));
v___x_1734_ = l___private_Lean_Level_0__Lean_Level_PP_Result_formatLst(v_a_1732_);
v___x_1735_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1735_, 0, v___x_1733_);
lean_ctor_set(v___x_1735_, 1, v___x_1734_);
v___x_1736_ = 0;
v___x_1737_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1737_, 0, v___x_1735_);
lean_ctor_set_uint8(v___x_1737_, sizeof(void*)*1, v___x_1736_);
v___x_1738_ = l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse(v___x_1737_, v_x_1691_);
return v___x_1738_;
}
default: 
{
lean_object* v_a_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; uint8_t v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; 
v_a_1739_ = lean_ctor_get(v_x_1690_, 0);
lean_inc(v_a_1739_);
lean_dec_ref_known(v_x_1690_, 1);
v___x_1740_ = ((lean_object*)(l_Lean_Level_PP_Result_format___closed__5));
v___x_1741_ = l___private_Lean_Level_0__Lean_Level_PP_Result_formatLst(v_a_1739_);
v___x_1742_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1742_, 0, v___x_1740_);
lean_ctor_set(v___x_1742_, 1, v___x_1741_);
v___x_1743_ = 0;
v___x_1744_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1744_, 0, v___x_1742_);
lean_ctor_set_uint8(v___x_1744_, sizeof(void*)*1, v___x_1743_);
v___x_1745_ = l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse(v___x_1744_, v_x_1691_);
return v___x_1745_;
}
}
}
}
LEAN_EXPORT void l_Lean_Level_PP_Result_format_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1690_ = stack[0].m_obj;
uint8_t v_x_1691_ = stack[1].m_num;
lean_object* v_res_1746_;
v_res_1746_ = l_Lean_Level_PP_Result_format(v_x_1690_, v_x_1691_);
stack->m_obj
 = v_res_1746_;
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_PP_Result_formatLst(lean_object* v_x_1747_){
_start:
{
if (lean_obj_tag(v_x_1747_) == 0)
{
lean_object* v___x_1748_; 
v___x_1748_ = lean_box(0);
return v___x_1748_;
}
else
{
lean_object* v_head_1749_; lean_object* v_tail_1750_; lean_object* v___x_1752_; uint8_t v_isShared_1753_; uint8_t v_isSharedCheck_1762_; 
v_head_1749_ = lean_ctor_get(v_x_1747_, 0);
v_tail_1750_ = lean_ctor_get(v_x_1747_, 1);
v_isSharedCheck_1762_ = !lean_is_exclusive(v_x_1747_);
if (v_isSharedCheck_1762_ == 0)
{
v___x_1752_ = v_x_1747_;
v_isShared_1753_ = v_isSharedCheck_1762_;
goto v_resetjp_1751_;
}
else
{
lean_inc(v_tail_1750_);
lean_inc(v_head_1749_);
lean_dec(v_x_1747_);
v___x_1752_ = lean_box(0);
v_isShared_1753_ = v_isSharedCheck_1762_;
goto v_resetjp_1751_;
}
v_resetjp_1751_:
{
lean_object* v___x_1754_; uint8_t v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1758_; 
v___x_1754_ = lean_box(1);
v___x_1755_ = 0;
v___x_1756_ = l_Lean_Level_PP_Result_format(v_head_1749_, v___x_1755_);
if (v_isShared_1753_ == 0)
{
lean_ctor_set_tag(v___x_1752_, 5);
lean_ctor_set(v___x_1752_, 1, v___x_1756_);
lean_ctor_set(v___x_1752_, 0, v___x_1754_);
v___x_1758_ = v___x_1752_;
goto v_reusejp_1757_;
}
else
{
lean_object* v_reuseFailAlloc_1761_; 
v_reuseFailAlloc_1761_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1761_, 0, v___x_1754_);
lean_ctor_set(v_reuseFailAlloc_1761_, 1, v___x_1756_);
v___x_1758_ = v_reuseFailAlloc_1761_;
goto v_reusejp_1757_;
}
v_reusejp_1757_:
{
lean_object* v___x_1759_; lean_object* v___x_1760_; 
v___x_1759_ = l___private_Lean_Level_0__Lean_Level_PP_Result_formatLst(v_tail_1750_);
v___x_1760_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1760_, 0, v___x_1758_);
lean_ctor_set(v___x_1760_, 1, v___x_1759_);
return v___x_1760_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_format___boxed(lean_object* v_x_1763_, lean_object* v_x_1764_){
_start:
{
uint8_t v_x_270__boxed_1765_; lean_object* v_res_1766_; 
v_x_270__boxed_1765_ = lean_unbox(v_x_1764_);
v_res_1766_ = l_Lean_Level_PP_Result_format(v_x_1763_, v_x_270__boxed_1765_);
return v_res_1766_;
}
}
static lean_object* _init_l_Lean_Level_PP_Result_quote___closed__0(void){
_start:
{
uint8_t v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; 
v___x_1767_ = 0;
v___x_1768_ = lean_box(0);
v___x_1769_ = l_Lean_SourceInfo_fromRef(v___x_1768_, v___x_1767_);
return v___x_1769_;
}
}
static lean_object* _init_l_Lean_Level_PP_Result_quote___closed__6(void){
_start:
{
lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; 
v___x_1779_ = ((lean_object*)(l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__0));
v___x_1780_ = lean_obj_once(&l_Lean_Level_PP_Result_quote___closed__0, &l_Lean_Level_PP_Result_quote___closed__0_once, _init_l_Lean_Level_PP_Result_quote___closed__0);
v___x_1781_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1781_, 0, v___x_1780_);
lean_ctor_set(v___x_1781_, 1, v___x_1779_);
return v___x_1781_;
}
}
static lean_object* _init_l_Lean_Level_PP_Result_quote___closed__7(void){
_start:
{
lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; 
v___x_1782_ = ((lean_object*)(l_Lean_instReprData___lam__0___closed__0));
v___x_1783_ = lean_obj_once(&l_Lean_Level_PP_Result_quote___closed__0, &l_Lean_Level_PP_Result_quote___closed__0_once, _init_l_Lean_Level_PP_Result_quote___closed__0);
v___x_1784_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1784_, 0, v___x_1783_);
lean_ctor_set(v___x_1784_, 1, v___x_1782_);
return v___x_1784_;
}
}
static lean_object* _init_l_Lean_Level_PP_Result_quote___closed__12(void){
_start:
{
lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; 
v___x_1797_ = ((lean_object*)(l_Lean_Level_PP_Result_format___closed__2));
v___x_1798_ = lean_obj_once(&l_Lean_Level_PP_Result_quote___closed__0, &l_Lean_Level_PP_Result_quote___closed__0_once, _init_l_Lean_Level_PP_Result_quote___closed__0);
v___x_1799_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1799_, 0, v___x_1798_);
lean_ctor_set(v___x_1799_, 1, v___x_1797_);
return v___x_1799_;
}
}
static lean_object* _init_l_Lean_Level_PP_Result_quote___closed__15(void){
_start:
{
lean_object* v___x_1803_; 
v___x_1803_ = l_Array_mkArray0___redArg();
return v___x_1803_;
}
}
static lean_object* _init_l_Lean_Level_PP_Result_quote___closed__17(void){
_start:
{
lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; 
v___x_1809_ = ((lean_object*)(l_Lean_Level_PP_Result_format___closed__4));
v___x_1810_ = lean_obj_once(&l_Lean_Level_PP_Result_quote___closed__0, &l_Lean_Level_PP_Result_quote___closed__0_once, _init_l_Lean_Level_PP_Result_quote___closed__0);
v___x_1811_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1811_, 0, v___x_1810_);
lean_ctor_set(v___x_1811_, 1, v___x_1809_);
return v___x_1811_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_quote(lean_object* v_r_1812_, lean_object* v_prec_1813_){
_start:
{
lean_object* v_s_1815_; 
switch(lean_obj_tag(v_r_1812_))
{
case 0:
{
lean_object* v_a_1823_; lean_object* v___x_1824_; 
v_a_1823_ = lean_ctor_get(v_r_1812_, 0);
lean_inc(v_a_1823_);
lean_dec_ref_known(v_r_1812_, 1);
v___x_1824_ = l_Lean_mkIdent(v_a_1823_);
return v___x_1824_;
}
case 1:
{
lean_object* v_a_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; 
v_a_1825_ = lean_ctor_get(v_r_1812_, 0);
lean_inc(v_a_1825_);
lean_dec_ref_known(v_r_1812_, 1);
v___x_1826_ = l_Nat_reprFast(v_a_1825_);
v___x_1827_ = lean_box(2);
v___x_1828_ = l_Lean_Syntax_mkNumLit(v___x_1826_, v___x_1827_);
return v___x_1828_;
}
case 2:
{
lean_object* v_a_1829_; lean_object* v_a_1830_; lean_object* v___x_1832_; uint8_t v_isShared_1833_; uint8_t v_isSharedCheck_1853_; 
v_a_1829_ = lean_ctor_get(v_r_1812_, 0);
v_a_1830_ = lean_ctor_get(v_r_1812_, 1);
v_isSharedCheck_1853_ = !lean_is_exclusive(v_r_1812_);
if (v_isSharedCheck_1853_ == 0)
{
v___x_1832_ = v_r_1812_;
v_isShared_1833_ = v_isSharedCheck_1853_;
goto v_resetjp_1831_;
}
else
{
lean_inc(v_a_1830_);
lean_inc(v_a_1829_);
lean_dec(v_r_1812_);
v___x_1832_ = lean_box(0);
v_isShared_1833_ = v_isSharedCheck_1853_;
goto v_resetjp_1831_;
}
v_resetjp_1831_:
{
lean_object* v_zero_1834_; uint8_t v_isZero_1835_; 
v_zero_1834_ = lean_unsigned_to_nat(0u);
v_isZero_1835_ = lean_nat_dec_eq(v_a_1830_, v_zero_1834_);
if (v_isZero_1835_ == 1)
{
lean_del_object(v___x_1832_);
lean_dec(v_a_1830_);
v_r_1812_ = v_a_1829_;
goto _start;
}
else
{
lean_object* v_one_1837_; lean_object* v_n_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1846_; 
v_one_1837_ = lean_unsigned_to_nat(1u);
v_n_1838_ = lean_nat_sub(v_a_1830_, v_one_1837_);
lean_dec(v_a_1830_);
v___x_1839_ = lean_box(0);
v___x_1840_ = l_Lean_SourceInfo_fromRef(v___x_1839_, v_isZero_1835_);
v___x_1841_ = ((lean_object*)(l_Lean_Level_PP_Result_quote___closed__9));
v___x_1842_ = lean_unsigned_to_nat(65u);
v___x_1843_ = l_Lean_Level_PP_Result_quote(v_a_1829_, v___x_1842_);
v___x_1844_ = ((lean_object*)(l_Lean_Level_PP_Result_quote___closed__10));
lean_inc(v___x_1840_);
if (v_isShared_1833_ == 0)
{
lean_ctor_set(v___x_1832_, 1, v___x_1844_);
lean_ctor_set(v___x_1832_, 0, v___x_1840_);
v___x_1846_ = v___x_1832_;
goto v_reusejp_1845_;
}
else
{
lean_object* v_reuseFailAlloc_1852_; 
v_reuseFailAlloc_1852_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1852_, 0, v___x_1840_);
lean_ctor_set(v_reuseFailAlloc_1852_, 1, v___x_1844_);
v___x_1846_ = v_reuseFailAlloc_1852_;
goto v_reusejp_1845_;
}
v_reusejp_1845_:
{
lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; 
v___x_1847_ = lean_nat_add(v_n_1838_, v_one_1837_);
lean_dec(v_n_1838_);
v___x_1848_ = l_Nat_reprFast(v___x_1847_);
v___x_1849_ = lean_box(2);
v___x_1850_ = l_Lean_Syntax_mkNumLit(v___x_1848_, v___x_1849_);
v___x_1851_ = l_Lean_Syntax_node3(v___x_1840_, v___x_1841_, v___x_1843_, v___x_1846_, v___x_1850_);
v_s_1815_ = v___x_1851_;
goto v___jp_1814_;
}
}
}
}
case 3:
{
lean_object* v_a_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; size_t v_sz_1861_; size_t v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; 
v_a_1854_ = lean_ctor_get(v_r_1812_, 0);
lean_inc(v_a_1854_);
lean_dec_ref_known(v_r_1812_, 1);
v___x_1855_ = lean_obj_once(&l_Lean_Level_PP_Result_quote___closed__0, &l_Lean_Level_PP_Result_quote___closed__0_once, _init_l_Lean_Level_PP_Result_quote___closed__0);
v___x_1856_ = ((lean_object*)(l_Lean_Level_PP_Result_quote___closed__11));
v___x_1857_ = lean_obj_once(&l_Lean_Level_PP_Result_quote___closed__12, &l_Lean_Level_PP_Result_quote___closed__12_once, _init_l_Lean_Level_PP_Result_quote___closed__12);
v___x_1858_ = ((lean_object*)(l_Lean_Level_PP_Result_quote___closed__14));
v___x_1859_ = lean_obj_once(&l_Lean_Level_PP_Result_quote___closed__15, &l_Lean_Level_PP_Result_quote___closed__15_once, _init_l_Lean_Level_PP_Result_quote___closed__15);
v___x_1860_ = lean_array_mk(v_a_1854_);
v_sz_1861_ = lean_array_size(v___x_1860_);
v___x_1862_ = ((size_t)0ULL);
v___x_1863_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Level_PP_Result_quote_spec__0(v_sz_1861_, v___x_1862_, v___x_1860_);
v___x_1864_ = l_Array_append___redArg(v___x_1859_, v___x_1863_);
lean_dec_ref(v___x_1863_);
v___x_1865_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1865_, 0, v___x_1855_);
lean_ctor_set(v___x_1865_, 1, v___x_1858_);
lean_ctor_set(v___x_1865_, 2, v___x_1864_);
v___x_1866_ = l_Lean_Syntax_node2(v___x_1855_, v___x_1856_, v___x_1857_, v___x_1865_);
v_s_1815_ = v___x_1866_;
goto v___jp_1814_;
}
default: 
{
lean_object* v_a_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; size_t v_sz_1874_; size_t v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; 
v_a_1867_ = lean_ctor_get(v_r_1812_, 0);
lean_inc(v_a_1867_);
lean_dec_ref_known(v_r_1812_, 1);
v___x_1868_ = lean_obj_once(&l_Lean_Level_PP_Result_quote___closed__0, &l_Lean_Level_PP_Result_quote___closed__0_once, _init_l_Lean_Level_PP_Result_quote___closed__0);
v___x_1869_ = ((lean_object*)(l_Lean_Level_PP_Result_quote___closed__16));
v___x_1870_ = lean_obj_once(&l_Lean_Level_PP_Result_quote___closed__17, &l_Lean_Level_PP_Result_quote___closed__17_once, _init_l_Lean_Level_PP_Result_quote___closed__17);
v___x_1871_ = ((lean_object*)(l_Lean_Level_PP_Result_quote___closed__14));
v___x_1872_ = lean_obj_once(&l_Lean_Level_PP_Result_quote___closed__15, &l_Lean_Level_PP_Result_quote___closed__15_once, _init_l_Lean_Level_PP_Result_quote___closed__15);
v___x_1873_ = lean_array_mk(v_a_1867_);
v_sz_1874_ = lean_array_size(v___x_1873_);
v___x_1875_ = ((size_t)0ULL);
v___x_1876_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Level_PP_Result_quote_spec__0(v_sz_1874_, v___x_1875_, v___x_1873_);
v___x_1877_ = l_Array_append___redArg(v___x_1872_, v___x_1876_);
lean_dec_ref(v___x_1876_);
v___x_1878_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1878_, 0, v___x_1868_);
lean_ctor_set(v___x_1878_, 1, v___x_1871_);
lean_ctor_set(v___x_1878_, 2, v___x_1877_);
v___x_1879_ = l_Lean_Syntax_node2(v___x_1868_, v___x_1869_, v___x_1870_, v___x_1878_);
v_s_1815_ = v___x_1879_;
goto v___jp_1814_;
}
}
v___jp_1814_:
{
lean_object* v___x_1816_; uint8_t v___x_1817_; 
v___x_1816_ = lean_unsigned_to_nat(0u);
v___x_1817_ = lean_nat_dec_lt(v___x_1816_, v_prec_1813_);
if (v___x_1817_ == 0)
{
return v_s_1815_;
}
else
{
lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; 
v___x_1818_ = lean_obj_once(&l_Lean_Level_PP_Result_quote___closed__0, &l_Lean_Level_PP_Result_quote___closed__0_once, _init_l_Lean_Level_PP_Result_quote___closed__0);
v___x_1819_ = ((lean_object*)(l_Lean_Level_PP_Result_quote___closed__5));
v___x_1820_ = lean_obj_once(&l_Lean_Level_PP_Result_quote___closed__6, &l_Lean_Level_PP_Result_quote___closed__6_once, _init_l_Lean_Level_PP_Result_quote___closed__6);
v___x_1821_ = lean_obj_once(&l_Lean_Level_PP_Result_quote___closed__7, &l_Lean_Level_PP_Result_quote___closed__7_once, _init_l_Lean_Level_PP_Result_quote___closed__7);
v___x_1822_ = l_Lean_Syntax_node3(v___x_1818_, v___x_1819_, v___x_1820_, v_s_1815_, v___x_1821_);
return v___x_1822_;
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Level_PP_Result_quote_spec__0(size_t v_sz_1880_, size_t v_i_1881_, lean_object* v_bs_1882_){
_start:
{
uint8_t v___x_1883_; 
v___x_1883_ = lean_usize_dec_lt(v_i_1881_, v_sz_1880_);
if (v___x_1883_ == 0)
{
return v_bs_1882_;
}
else
{
lean_object* v_v_1884_; lean_object* v___x_1885_; lean_object* v_bs_x27_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; size_t v___x_1889_; size_t v___x_1890_; lean_object* v___x_1891_; 
v_v_1884_ = lean_array_uget(v_bs_1882_, v_i_1881_);
v___x_1885_ = lean_unsigned_to_nat(0u);
v_bs_x27_1886_ = lean_array_uset(v_bs_1882_, v_i_1881_, v___x_1885_);
v___x_1887_ = lean_unsigned_to_nat(1024u);
v___x_1888_ = l_Lean_Level_PP_Result_quote(v_v_1884_, v___x_1887_);
v___x_1889_ = ((size_t)1ULL);
v___x_1890_ = lean_usize_add(v_i_1881_, v___x_1889_);
v___x_1891_ = lean_array_uset(v_bs_x27_1886_, v_i_1881_, v___x_1888_);
v_i_1881_ = v___x_1890_;
v_bs_1882_ = v___x_1891_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Level_PP_Result_quote_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_1880_ = stack[0].m_num;
size_t v_i_1881_ = stack[1].m_num;
lean_object* v_bs_1882_ = stack[2].m_obj;
lean_object* v_res_1893_;
v_res_1893_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Level_PP_Result_quote_spec__0(v_sz_1880_, v_i_1881_, v_bs_1882_);
stack->m_obj
 = v_res_1893_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Level_PP_Result_quote_spec__0___boxed(lean_object* v_sz_1894_, lean_object* v_i_1895_, lean_object* v_bs_1896_){
_start:
{
size_t v_sz_boxed_1897_; size_t v_i_boxed_1898_; lean_object* v_res_1899_; 
v_sz_boxed_1897_ = lean_unbox_usize(v_sz_1894_);
lean_dec(v_sz_1894_);
v_i_boxed_1898_ = lean_unbox_usize(v_i_1895_);
lean_dec(v_i_1895_);
v_res_1899_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Level_PP_Result_quote_spec__0(v_sz_boxed_1897_, v_i_boxed_1898_, v_bs_1896_);
return v_res_1899_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_quote___boxed(lean_object* v_r_1900_, lean_object* v_prec_1901_){
_start:
{
lean_object* v_res_1902_; 
v_res_1902_ = l_Lean_Level_PP_Result_quote(v_r_1900_, v_prec_1901_);
lean_dec(v_prec_1901_);
return v_res_1902_;
}
}
lean_object* l_Lean_Level_format(lean_object* v_u_1903_, uint8_t v_mvars_1904_, lean_object* v_lIndex_x3f_1905_){
_start:
{
lean_object* v___x_1906_; lean_object* v___x_1907_; uint8_t v___x_1908_; lean_object* v___x_1909_; 
v___x_1906_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1906_, 0, v_lIndex_x3f_1905_);
lean_ctor_set_uint8(v___x_1906_, sizeof(void*)*1, v_mvars_1904_);
v___x_1907_ = l_Lean_Level_PP_toResult(v_u_1903_, v___x_1906_);
lean_dec_ref_known(v___x_1906_, 1);
v___x_1908_ = 1;
v___x_1909_ = l_Lean_Level_PP_Result_format(v___x_1907_, v___x_1908_);
return v___x_1909_;
}
}
LEAN_EXPORT void l_Lean_Level_format_0interp(lean_interpreter_value* stack)
{
lean_object* v_u_1903_ = stack[0].m_obj;
uint8_t v_mvars_1904_ = stack[1].m_num;
lean_object* v_lIndex_x3f_1905_ = stack[2].m_obj;
lean_object* v_res_1910_;
v_res_1910_ = l_Lean_Level_format(v_u_1903_, v_mvars_1904_, v_lIndex_x3f_1905_);
stack->m_obj
 = v_res_1910_;
}
LEAN_EXPORT lean_object* l_Lean_Level_format___boxed(lean_object* v_u_1911_, lean_object* v_mvars_1912_, lean_object* v_lIndex_x3f_1913_){
_start:
{
uint8_t v_mvars_boxed_1914_; lean_object* v_res_1915_; 
v_mvars_boxed_1914_ = lean_unbox(v_mvars_1912_);
v_res_1915_ = l_Lean_Level_format(v_u_1911_, v_mvars_boxed_1914_, v_lIndex_x3f_1913_);
return v_res_1915_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_instToFormat___lam__0(lean_object* v_x_1916_){
_start:
{
lean_object* v___x_1917_; 
v___x_1917_ = lean_box(0);
return v___x_1917_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_instToFormat___lam__0___boxed(lean_object* v_x_1918_){
_start:
{
lean_object* v_res_1919_; 
v_res_1919_ = l_Lean_Level_instToFormat___lam__0(v_x_1918_);
lean_dec(v_x_1918_);
return v_res_1919_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_instToFormat___lam__1(lean_object* v___f_1920_, lean_object* v_u_1921_){
_start:
{
uint8_t v___x_1922_; lean_object* v___x_1923_; 
v___x_1922_ = 1;
v___x_1923_ = l_Lean_Level_format(v_u_1921_, v___x_1922_, v___f_1920_);
return v___x_1923_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_instToString___lam__1(lean_object* v___f_1928_, lean_object* v_u_1929_){
_start:
{
uint8_t v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; 
v___x_1930_ = 1;
v___x_1931_ = l_Lean_Level_format(v_u_1929_, v___x_1930_, v___f_1928_);
v___x_1932_ = l_Std_Format_defWidth;
v___x_1933_ = lean_unsigned_to_nat(0u);
v___x_1934_ = l_Std_Format_pretty(v___x_1931_, v___x_1932_, v___x_1933_, v___x_1933_);
return v___x_1934_;
}
}
lean_object* l_Lean_Level_quote(lean_object* v_u_1938_, lean_object* v_prec_1939_, uint8_t v_mvars_1940_, lean_object* v_lIndex_x3f_1941_){
_start:
{
lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; 
v___x_1942_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1942_, 0, v_lIndex_x3f_1941_);
lean_ctor_set_uint8(v___x_1942_, sizeof(void*)*1, v_mvars_1940_);
v___x_1943_ = l_Lean_Level_PP_toResult(v_u_1938_, v___x_1942_);
lean_dec_ref_known(v___x_1942_, 1);
v___x_1944_ = l_Lean_Level_PP_Result_quote(v___x_1943_, v_prec_1939_);
return v___x_1944_;
}
}
LEAN_EXPORT void l_Lean_Level_quote_0interp(lean_interpreter_value* stack)
{
lean_object* v_u_1938_ = stack[0].m_obj;
lean_object* v_prec_1939_ = stack[1].m_obj;
uint8_t v_mvars_1940_ = stack[2].m_num;
lean_object* v_lIndex_x3f_1941_ = stack[3].m_obj;
lean_object* v_res_1945_;
v_res_1945_ = l_Lean_Level_quote(v_u_1938_, v_prec_1939_, v_mvars_1940_, v_lIndex_x3f_1941_);
stack->m_obj
 = v_res_1945_;
}
LEAN_EXPORT lean_object* l_Lean_Level_quote___boxed(lean_object* v_u_1946_, lean_object* v_prec_1947_, lean_object* v_mvars_1948_, lean_object* v_lIndex_x3f_1949_){
_start:
{
uint8_t v_mvars_boxed_1950_; lean_object* v_res_1951_; 
v_mvars_boxed_1950_ = lean_unbox(v_mvars_1948_);
v_res_1951_ = l_Lean_Level_quote(v_u_1946_, v_prec_1947_, v_mvars_boxed_1950_, v_lIndex_x3f_1949_);
lean_dec(v_prec_1947_);
return v_res_1951_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_instQuoteMkStr1___lam__1(lean_object* v___f_1952_, lean_object* v_u_1953_){
_start:
{
lean_object* v___x_1954_; uint8_t v___x_1955_; lean_object* v___x_1956_; 
v___x_1954_ = lean_unsigned_to_nat(0u);
v___x_1955_ = 1;
v___x_1956_ = l_Lean_Level_quote(v_u_1953_, v___x_1954_, v___x_1955_, v___f_1952_);
return v___x_1956_;
}
}
uint8_t l___private_Lean_Level_0__Lean_mkLevelMaxCore___lam__0(lean_object* v_u_1960_, lean_object* v_v_1961_){
_start:
{
uint8_t v___y_1963_; uint8_t v___x_1969_; 
v___x_1969_ = l_Lean_Level_isExplicit(v_v_1961_);
if (v___x_1969_ == 0)
{
v___y_1963_ = v___x_1969_;
goto v___jp_1962_;
}
else
{
lean_object* v___x_1970_; lean_object* v___x_1971_; uint8_t v___x_1972_; 
v___x_1970_ = l_Lean_Level_getOffset(v_v_1961_);
v___x_1971_ = l_Lean_Level_getOffset(v_u_1960_);
v___x_1972_ = lean_nat_dec_le(v___x_1970_, v___x_1971_);
lean_dec(v___x_1971_);
lean_dec(v___x_1970_);
v___y_1963_ = v___x_1972_;
goto v___jp_1962_;
}
v___jp_1962_:
{
uint8_t v___x_1964_; 
v___x_1964_ = 1;
if (v___y_1963_ == 0)
{
if (lean_obj_tag(v_u_1960_) == 2)
{
lean_object* v_a_1965_; lean_object* v_a_1966_; uint8_t v___x_1967_; 
v_a_1965_ = lean_ctor_get(v_u_1960_, 0);
v_a_1966_ = lean_ctor_get(v_u_1960_, 1);
v___x_1967_ = lean_level_eq(v_v_1961_, v_a_1965_);
if (v___x_1967_ == 0)
{
uint8_t v___x_1968_; 
v___x_1968_ = lean_level_eq(v_v_1961_, v_a_1966_);
return v___x_1968_;
}
else
{
return v___x_1964_;
}
}
else
{
return v___y_1963_;
}
}
else
{
return v___x_1964_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Level_0__Lean_mkLevelMaxCore___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_u_1960_ = stack[0].m_obj;
lean_object* v_v_1961_ = stack[1].m_obj;
uint8_t v_res_1973_;
v_res_1973_ = l___private_Lean_Level_0__Lean_mkLevelMaxCore___lam__0(v_u_1960_, v_v_1961_);
stack->m_num = v_res_1973_;
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_mkLevelMaxCore___lam__0___boxed(lean_object* v_u_1974_, lean_object* v_v_1975_){
_start:
{
uint8_t v_res_1976_; lean_object* v_r_1977_; 
v_res_1976_ = l___private_Lean_Level_0__Lean_mkLevelMaxCore___lam__0(v_u_1974_, v_v_1975_);
lean_dec(v_v_1975_);
lean_dec(v_u_1974_);
v_r_1977_ = lean_box(v_res_1976_);
return v_r_1977_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_mkLevelMaxCore(lean_object* v_u_1978_, lean_object* v_v_1979_, lean_object* v_elseK_1980_){
_start:
{
uint8_t v___x_1981_; 
v___x_1981_ = lean_level_eq(v_u_1978_, v_v_1979_);
if (v___x_1981_ == 0)
{
uint8_t v___x_1982_; 
v___x_1982_ = l_Lean_Level_isZero(v_u_1978_);
if (v___x_1982_ == 0)
{
uint8_t v___x_1983_; 
v___x_1983_ = l_Lean_Level_isZero(v_v_1979_);
if (v___x_1983_ == 0)
{
uint8_t v___x_1984_; 
v___x_1984_ = l___private_Lean_Level_0__Lean_mkLevelMaxCore___lam__0(v_u_1978_, v_v_1979_);
if (v___x_1984_ == 0)
{
uint8_t v___x_1985_; 
v___x_1985_ = l___private_Lean_Level_0__Lean_mkLevelMaxCore___lam__0(v_v_1979_, v_u_1978_);
if (v___x_1985_ == 0)
{
lean_object* v___x_1986_; lean_object* v___x_1987_; uint8_t v___x_1988_; 
v___x_1986_ = l_Lean_Level_getLevelOffset(v_u_1978_);
v___x_1987_ = l_Lean_Level_getLevelOffset(v_v_1979_);
v___x_1988_ = lean_level_eq(v___x_1986_, v___x_1987_);
lean_dec(v___x_1987_);
lean_dec(v___x_1986_);
if (v___x_1988_ == 0)
{
lean_object* v___x_1989_; lean_object* v___x_1990_; 
v___x_1989_ = lean_box(0);
v___x_1990_ = lean_apply_1(v_elseK_1980_, v___x_1989_);
return v___x_1990_;
}
else
{
lean_object* v___x_1991_; lean_object* v___x_1992_; uint8_t v___x_1993_; 
lean_dec_ref(v_elseK_1980_);
v___x_1991_ = l_Lean_Level_getOffset(v_v_1979_);
v___x_1992_ = l_Lean_Level_getOffset(v_u_1978_);
v___x_1993_ = lean_nat_dec_le(v___x_1991_, v___x_1992_);
lean_dec(v___x_1992_);
lean_dec(v___x_1991_);
if (v___x_1993_ == 0)
{
lean_inc(v_v_1979_);
return v_v_1979_;
}
else
{
lean_inc(v_u_1978_);
return v_u_1978_;
}
}
}
else
{
lean_dec_ref(v_elseK_1980_);
lean_inc(v_v_1979_);
return v_v_1979_;
}
}
else
{
lean_dec_ref(v_elseK_1980_);
lean_inc(v_u_1978_);
return v_u_1978_;
}
}
else
{
lean_dec_ref(v_elseK_1980_);
lean_inc(v_u_1978_);
return v_u_1978_;
}
}
else
{
lean_dec_ref(v_elseK_1980_);
lean_inc(v_v_1979_);
return v_v_1979_;
}
}
else
{
lean_dec_ref(v_elseK_1980_);
lean_inc(v_u_1978_);
return v_u_1978_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_mkLevelMaxCore___boxed(lean_object* v_u_1994_, lean_object* v_v_1995_, lean_object* v_elseK_1996_){
_start:
{
lean_object* v_res_1997_; 
v_res_1997_ = l___private_Lean_Level_0__Lean_mkLevelMaxCore(v_u_1994_, v_v_1995_, v_elseK_1996_);
lean_dec(v_v_1995_);
lean_dec(v_u_1994_);
return v_res_1997_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLevelMax_x27(lean_object* v_u_1998_, lean_object* v_v_1999_){
_start:
{
uint8_t v___x_2000_; 
v___x_2000_ = lean_level_eq(v_u_1998_, v_v_1999_);
if (v___x_2000_ == 0)
{
uint8_t v___x_2001_; 
v___x_2001_ = l_Lean_Level_isZero(v_u_1998_);
if (v___x_2001_ == 0)
{
uint8_t v___x_2002_; 
v___x_2002_ = l_Lean_Level_isZero(v_v_1999_);
if (v___x_2002_ == 0)
{
uint8_t v___x_2003_; 
v___x_2003_ = l___private_Lean_Level_0__Lean_mkLevelMaxCore___lam__0(v_u_1998_, v_v_1999_);
if (v___x_2003_ == 0)
{
uint8_t v___x_2004_; 
v___x_2004_ = l___private_Lean_Level_0__Lean_mkLevelMaxCore___lam__0(v_v_1999_, v_u_1998_);
if (v___x_2004_ == 0)
{
lean_object* v___x_2005_; lean_object* v___x_2006_; uint8_t v___x_2007_; 
v___x_2005_ = l_Lean_Level_getLevelOffset(v_u_1998_);
v___x_2006_ = l_Lean_Level_getLevelOffset(v_v_1999_);
v___x_2007_ = lean_level_eq(v___x_2005_, v___x_2006_);
lean_dec(v___x_2006_);
lean_dec(v___x_2005_);
if (v___x_2007_ == 0)
{
lean_object* v___x_2008_; 
v___x_2008_ = l_Lean_Level_max___override(v_u_1998_, v_v_1999_);
return v___x_2008_;
}
else
{
lean_object* v___x_2009_; lean_object* v___x_2010_; uint8_t v___x_2011_; 
v___x_2009_ = l_Lean_Level_getOffset(v_v_1999_);
v___x_2010_ = l_Lean_Level_getOffset(v_u_1998_);
v___x_2011_ = lean_nat_dec_le(v___x_2009_, v___x_2010_);
lean_dec(v___x_2010_);
lean_dec(v___x_2009_);
if (v___x_2011_ == 0)
{
lean_dec(v_u_1998_);
return v_v_1999_;
}
else
{
lean_dec(v_v_1999_);
return v_u_1998_;
}
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
lean_dec(v_v_1999_);
return v_u_1998_;
}
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
lean_dec(v_v_1999_);
return v_u_1998_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_simpLevelMax_x27(lean_object* v_u_2012_, lean_object* v_v_2013_, lean_object* v_d_2014_){
_start:
{
uint8_t v___x_2015_; 
v___x_2015_ = lean_level_eq(v_u_2012_, v_v_2013_);
if (v___x_2015_ == 0)
{
uint8_t v___x_2016_; 
v___x_2016_ = l_Lean_Level_isZero(v_u_2012_);
if (v___x_2016_ == 0)
{
uint8_t v___x_2017_; 
v___x_2017_ = l_Lean_Level_isZero(v_v_2013_);
if (v___x_2017_ == 0)
{
uint8_t v___x_2018_; 
v___x_2018_ = l___private_Lean_Level_0__Lean_mkLevelMaxCore___lam__0(v_u_2012_, v_v_2013_);
if (v___x_2018_ == 0)
{
uint8_t v___x_2019_; 
v___x_2019_ = l___private_Lean_Level_0__Lean_mkLevelMaxCore___lam__0(v_v_2013_, v_u_2012_);
if (v___x_2019_ == 0)
{
lean_object* v___x_2020_; lean_object* v___x_2021_; uint8_t v___x_2022_; 
v___x_2020_ = l_Lean_Level_getLevelOffset(v_u_2012_);
v___x_2021_ = l_Lean_Level_getLevelOffset(v_v_2013_);
v___x_2022_ = lean_level_eq(v___x_2020_, v___x_2021_);
lean_dec(v___x_2021_);
lean_dec(v___x_2020_);
if (v___x_2022_ == 0)
{
lean_inc(v_d_2014_);
return v_d_2014_;
}
else
{
lean_object* v___x_2023_; lean_object* v___x_2024_; uint8_t v___x_2025_; 
v___x_2023_ = l_Lean_Level_getOffset(v_v_2013_);
v___x_2024_ = l_Lean_Level_getOffset(v_u_2012_);
v___x_2025_ = lean_nat_dec_le(v___x_2023_, v___x_2024_);
lean_dec(v___x_2024_);
lean_dec(v___x_2023_);
if (v___x_2025_ == 0)
{
lean_inc(v_v_2013_);
return v_v_2013_;
}
else
{
lean_inc(v_u_2012_);
return v_u_2012_;
}
}
}
else
{
lean_inc(v_v_2013_);
return v_v_2013_;
}
}
else
{
lean_inc(v_u_2012_);
return v_u_2012_;
}
}
else
{
lean_inc(v_u_2012_);
return v_u_2012_;
}
}
else
{
lean_inc(v_v_2013_);
return v_v_2013_;
}
}
else
{
lean_inc(v_u_2012_);
return v_u_2012_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_simpLevelMax_x27___boxed(lean_object* v_u_2026_, lean_object* v_v_2027_, lean_object* v_d_2028_){
_start:
{
lean_object* v_res_2029_; 
v_res_2029_ = l_Lean_simpLevelMax_x27(v_u_2026_, v_v_2027_, v_d_2028_);
lean_dec(v_d_2028_);
lean_dec(v_v_2027_);
lean_dec(v_u_2026_);
return v_res_2029_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_mkLevelIMaxCore(lean_object* v_u_2030_, lean_object* v_v_2031_, lean_object* v_elseK_2032_){
_start:
{
uint8_t v___x_2033_; 
v___x_2033_ = l_Lean_Level_isNeverZero(v_v_2031_);
if (v___x_2033_ == 0)
{
uint8_t v___x_2034_; 
v___x_2034_ = l_Lean_Level_isZero(v_v_2031_);
if (v___x_2034_ == 0)
{
uint8_t v___x_2035_; 
v___x_2035_ = l_Lean_Level_isZero(v_u_2030_);
if (v___x_2035_ == 0)
{
uint8_t v___x_2036_; 
v___x_2036_ = lean_level_eq(v_u_2030_, v_v_2031_);
lean_dec(v_v_2031_);
if (v___x_2036_ == 0)
{
lean_object* v___x_2037_; lean_object* v___x_2038_; 
lean_dec(v_u_2030_);
v___x_2037_ = lean_box(0);
v___x_2038_ = lean_apply_1(v_elseK_2032_, v___x_2037_);
return v___x_2038_;
}
else
{
lean_dec_ref(v_elseK_2032_);
return v_u_2030_;
}
}
else
{
lean_dec_ref(v_elseK_2032_);
lean_dec(v_u_2030_);
return v_v_2031_;
}
}
else
{
lean_dec_ref(v_elseK_2032_);
lean_dec(v_u_2030_);
return v_v_2031_;
}
}
else
{
lean_object* v___x_2039_; 
lean_dec_ref(v_elseK_2032_);
v___x_2039_ = l_Lean_mkLevelMax_x27(v_u_2030_, v_v_2031_);
return v___x_2039_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkLevelIMax_x27(lean_object* v_u_2040_, lean_object* v_v_2041_){
_start:
{
uint8_t v___x_2042_; 
v___x_2042_ = l_Lean_Level_isNeverZero(v_v_2041_);
if (v___x_2042_ == 0)
{
uint8_t v___x_2043_; 
v___x_2043_ = l_Lean_Level_isZero(v_v_2041_);
if (v___x_2043_ == 0)
{
uint8_t v___x_2044_; 
v___x_2044_ = l_Lean_Level_isZero(v_u_2040_);
if (v___x_2044_ == 0)
{
uint8_t v___x_2045_; 
v___x_2045_ = lean_level_eq(v_u_2040_, v_v_2041_);
if (v___x_2045_ == 0)
{
lean_object* v___x_2046_; 
v___x_2046_ = l_Lean_Level_imax___override(v_u_2040_, v_v_2041_);
return v___x_2046_;
}
else
{
lean_dec(v_v_2041_);
return v_u_2040_;
}
}
else
{
lean_dec(v_u_2040_);
return v_v_2041_;
}
}
else
{
lean_dec(v_u_2040_);
return v_v_2041_;
}
}
else
{
lean_object* v___x_2047_; 
v___x_2047_ = l_Lean_mkLevelMax_x27(v_u_2040_, v_v_2041_);
return v___x_2047_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_simpLevelIMax_x27(lean_object* v_u_2048_, lean_object* v_v_2049_, lean_object* v_d_2050_){
_start:
{
uint8_t v___x_2051_; 
v___x_2051_ = l_Lean_Level_isNeverZero(v_v_2049_);
if (v___x_2051_ == 0)
{
uint8_t v___x_2052_; 
v___x_2052_ = l_Lean_Level_isZero(v_v_2049_);
if (v___x_2052_ == 0)
{
uint8_t v___x_2053_; 
v___x_2053_ = l_Lean_Level_isZero(v_u_2048_);
if (v___x_2053_ == 0)
{
uint8_t v___x_2054_; 
v___x_2054_ = lean_level_eq(v_u_2048_, v_v_2049_);
lean_dec(v_v_2049_);
if (v___x_2054_ == 0)
{
lean_dec(v_u_2048_);
lean_inc(v_d_2050_);
return v_d_2050_;
}
else
{
return v_u_2048_;
}
}
else
{
lean_dec(v_u_2048_);
return v_v_2049_;
}
}
else
{
lean_dec(v_u_2048_);
return v_v_2049_;
}
}
else
{
lean_object* v___x_2055_; 
v___x_2055_ = l_Lean_mkLevelMax_x27(v_u_2048_, v_v_2049_);
return v___x_2055_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_simpLevelIMax_x27___boxed(lean_object* v_u_2056_, lean_object* v_v_2057_, lean_object* v_d_2058_){
_start:
{
lean_object* v_res_2059_; 
v_res_2059_ = l_Lean_simpLevelIMax_x27(v_u_2056_, v_v_2057_, v_d_2058_);
lean_dec(v_d_2058_);
return v_res_2059_;
}
}
static lean_object* _init_l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl___closed__2(void){
_start:
{
lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; 
v___x_2062_ = ((lean_object*)(l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl___closed__1));
v___x_2063_ = lean_unsigned_to_nat(14u);
v___x_2064_ = lean_unsigned_to_nat(566u);
v___x_2065_ = ((lean_object*)(l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl___closed__0));
v___x_2066_ = ((lean_object*)(l_Lean_Level_mvarId_x21___closed__0));
v___x_2067_ = l_mkPanicMessageWithDecl(v___x_2066_, v___x_2065_, v___x_2064_, v___x_2063_, v___x_2062_);
return v___x_2067_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl(lean_object* v_lvl_2068_, lean_object* v_newLvl_2069_){
_start:
{
if (lean_obj_tag(v_lvl_2068_) == 1)
{
lean_object* v_a_2070_; size_t v___x_2071_; size_t v___x_2072_; uint8_t v___x_2073_; 
v_a_2070_ = lean_ctor_get(v_lvl_2068_, 0);
v___x_2071_ = lean_ptr_addr(v_a_2070_);
v___x_2072_ = lean_ptr_addr(v_newLvl_2069_);
v___x_2073_ = lean_usize_dec_eq(v___x_2071_, v___x_2072_);
if (v___x_2073_ == 0)
{
lean_object* v___x_2074_; 
v___x_2074_ = l_Lean_Level_succ___override(v_newLvl_2069_);
return v___x_2074_;
}
else
{
lean_dec(v_newLvl_2069_);
lean_inc_ref(v_lvl_2068_);
return v_lvl_2068_;
}
}
else
{
lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; 
lean_dec(v_newLvl_2069_);
v___x_2075_ = lean_box(0);
v___x_2076_ = lean_obj_once(&l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl___closed__2, &l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl___closed__2_once, _init_l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl___closed__2);
v___x_2077_ = l_panic___redArg(v___x_2075_, v___x_2076_);
return v___x_2077_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl___boxed(lean_object* v_lvl_2078_, lean_object* v_newLvl_2079_){
_start:
{
lean_object* v_res_2080_; 
v_res_2080_ = l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl(v_lvl_2078_, v_newLvl_2079_);
lean_dec(v_lvl_2078_);
return v_res_2080_;
}
}
static lean_object* _init_l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl___closed__2(void){
_start:
{
lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; 
v___x_2083_ = ((lean_object*)(l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl___closed__1));
v___x_2084_ = lean_unsigned_to_nat(19u);
v___x_2085_ = lean_unsigned_to_nat(577u);
v___x_2086_ = ((lean_object*)(l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl___closed__0));
v___x_2087_ = ((lean_object*)(l_Lean_Level_mvarId_x21___closed__0));
v___x_2088_ = l_mkPanicMessageWithDecl(v___x_2087_, v___x_2086_, v___x_2085_, v___x_2084_, v___x_2083_);
return v___x_2088_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl(lean_object* v_lvl_2089_, lean_object* v_newLhs_2090_, lean_object* v_newRhs_2091_){
_start:
{
if (lean_obj_tag(v_lvl_2089_) == 2)
{
lean_object* v_a_2092_; lean_object* v_a_2093_; size_t v___x_2094_; size_t v___x_2095_; uint8_t v___x_2096_; 
v_a_2092_ = lean_ctor_get(v_lvl_2089_, 0);
v_a_2093_ = lean_ctor_get(v_lvl_2089_, 1);
v___x_2094_ = lean_ptr_addr(v_a_2092_);
v___x_2095_ = lean_ptr_addr(v_newLhs_2090_);
v___x_2096_ = lean_usize_dec_eq(v___x_2094_, v___x_2095_);
if (v___x_2096_ == 0)
{
lean_object* v___x_2097_; 
v___x_2097_ = l_Lean_mkLevelMax_x27(v_newLhs_2090_, v_newRhs_2091_);
return v___x_2097_;
}
else
{
size_t v___x_2098_; size_t v___x_2099_; uint8_t v___x_2100_; 
v___x_2098_ = lean_ptr_addr(v_a_2093_);
v___x_2099_ = lean_ptr_addr(v_newRhs_2091_);
v___x_2100_ = lean_usize_dec_eq(v___x_2098_, v___x_2099_);
if (v___x_2100_ == 0)
{
lean_object* v___x_2101_; 
v___x_2101_ = l_Lean_mkLevelMax_x27(v_newLhs_2090_, v_newRhs_2091_);
return v___x_2101_;
}
else
{
lean_object* v___x_2102_; 
v___x_2102_ = l_Lean_simpLevelMax_x27(v_newLhs_2090_, v_newRhs_2091_, v_lvl_2089_);
lean_dec(v_newRhs_2091_);
lean_dec(v_newLhs_2090_);
return v___x_2102_;
}
}
}
else
{
lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; 
lean_dec(v_newRhs_2091_);
lean_dec(v_newLhs_2090_);
v___x_2103_ = lean_box(0);
v___x_2104_ = lean_obj_once(&l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl___closed__2, &l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl___closed__2_once, _init_l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl___closed__2);
v___x_2105_ = l_panic___redArg(v___x_2103_, v___x_2104_);
return v___x_2105_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl___boxed(lean_object* v_lvl_2106_, lean_object* v_newLhs_2107_, lean_object* v_newRhs_2108_){
_start:
{
lean_object* v_res_2109_; 
v_res_2109_ = l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl(v_lvl_2106_, v_newLhs_2107_, v_newRhs_2108_);
lean_dec(v_lvl_2106_);
return v_res_2109_;
}
}
static lean_object* _init_l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl___closed__2(void){
_start:
{
lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; 
v___x_2112_ = ((lean_object*)(l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl___closed__1));
v___x_2113_ = lean_unsigned_to_nat(20u);
v___x_2114_ = lean_unsigned_to_nat(588u);
v___x_2115_ = ((lean_object*)(l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl___closed__0));
v___x_2116_ = ((lean_object*)(l_Lean_Level_mvarId_x21___closed__0));
v___x_2117_ = l_mkPanicMessageWithDecl(v___x_2116_, v___x_2115_, v___x_2114_, v___x_2113_, v___x_2112_);
return v___x_2117_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl(lean_object* v_lvl_2118_, lean_object* v_newLhs_2119_, lean_object* v_newRhs_2120_){
_start:
{
if (lean_obj_tag(v_lvl_2118_) == 3)
{
lean_object* v_a_2121_; lean_object* v_a_2122_; size_t v___x_2123_; size_t v___x_2124_; uint8_t v___x_2125_; 
v_a_2121_ = lean_ctor_get(v_lvl_2118_, 0);
v_a_2122_ = lean_ctor_get(v_lvl_2118_, 1);
v___x_2123_ = lean_ptr_addr(v_a_2121_);
v___x_2124_ = lean_ptr_addr(v_newLhs_2119_);
v___x_2125_ = lean_usize_dec_eq(v___x_2123_, v___x_2124_);
if (v___x_2125_ == 0)
{
lean_object* v___x_2126_; 
v___x_2126_ = l_Lean_mkLevelIMax_x27(v_newLhs_2119_, v_newRhs_2120_);
return v___x_2126_;
}
else
{
size_t v___x_2127_; size_t v___x_2128_; uint8_t v___x_2129_; 
v___x_2127_ = lean_ptr_addr(v_a_2122_);
v___x_2128_ = lean_ptr_addr(v_newRhs_2120_);
v___x_2129_ = lean_usize_dec_eq(v___x_2127_, v___x_2128_);
if (v___x_2129_ == 0)
{
lean_object* v___x_2130_; 
v___x_2130_ = l_Lean_mkLevelIMax_x27(v_newLhs_2119_, v_newRhs_2120_);
return v___x_2130_;
}
else
{
lean_object* v___x_2131_; 
v___x_2131_ = l_Lean_simpLevelIMax_x27(v_newLhs_2119_, v_newRhs_2120_, v_lvl_2118_);
return v___x_2131_;
}
}
}
else
{
lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; 
lean_dec(v_newRhs_2120_);
lean_dec(v_newLhs_2119_);
v___x_2132_ = lean_box(0);
v___x_2133_ = lean_obj_once(&l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl___closed__2, &l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl___closed__2_once, _init_l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl___closed__2);
v___x_2134_ = l_panic___redArg(v___x_2132_, v___x_2133_);
return v___x_2134_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl___boxed(lean_object* v_lvl_2135_, lean_object* v_newLhs_2136_, lean_object* v_newRhs_2137_){
_start:
{
lean_object* v_res_2138_; 
v_res_2138_ = l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl(v_lvl_2135_, v_newLhs_2136_, v_newRhs_2137_);
lean_dec(v_lvl_2135_);
return v_res_2138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_mkNaryMax(lean_object* v_x_2139_){
_start:
{
if (lean_obj_tag(v_x_2139_) == 0)
{
lean_object* v___x_2140_; 
v___x_2140_ = lean_box(0);
return v___x_2140_;
}
else
{
lean_object* v_tail_2141_; 
v_tail_2141_ = lean_ctor_get(v_x_2139_, 1);
if (lean_obj_tag(v_tail_2141_) == 0)
{
lean_object* v_head_2142_; 
v_head_2142_ = lean_ctor_get(v_x_2139_, 0);
lean_inc(v_head_2142_);
lean_dec_ref_known(v_x_2139_, 2);
return v_head_2142_;
}
else
{
lean_object* v_head_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; 
lean_inc(v_tail_2141_);
v_head_2143_ = lean_ctor_get(v_x_2139_, 0);
lean_inc(v_head_2143_);
lean_dec_ref_known(v_x_2139_, 2);
v___x_2144_ = l_Lean_Level_mkNaryMax(v_tail_2141_);
v___x_2145_ = l_Lean_mkLevelMax_x27(v_head_2143_, v___x_2144_);
return v___x_2145_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_substParams_go(lean_object* v_s_2146_, lean_object* v_u_2147_){
_start:
{
switch(lean_obj_tag(v_u_2147_))
{
case 1:
{
lean_object* v_a_2148_; uint8_t v___x_2149_; 
v_a_2148_ = lean_ctor_get(v_u_2147_, 0);
v___x_2149_ = l_Lean_Level_hasParam(v_u_2147_);
if (v___x_2149_ == 0)
{
lean_dec_ref(v_s_2146_);
return v_u_2147_;
}
else
{
lean_object* v___x_2150_; size_t v___x_2151_; size_t v___x_2152_; uint8_t v___x_2153_; 
lean_inc(v_a_2148_);
v___x_2150_ = l___private_Lean_Level_0__Lean_Level_substParams_go(v_s_2146_, v_a_2148_);
v___x_2151_ = lean_ptr_addr(v_a_2148_);
v___x_2152_ = lean_ptr_addr(v___x_2150_);
v___x_2153_ = lean_usize_dec_eq(v___x_2151_, v___x_2152_);
if (v___x_2153_ == 0)
{
lean_object* v___x_2154_; 
lean_dec_ref_known(v_u_2147_, 1);
v___x_2154_ = l_Lean_Level_succ___override(v___x_2150_);
return v___x_2154_;
}
else
{
lean_dec(v___x_2150_);
return v_u_2147_;
}
}
}
case 2:
{
lean_object* v_a_2155_; lean_object* v_a_2156_; uint8_t v___x_2157_; 
v_a_2155_ = lean_ctor_get(v_u_2147_, 0);
v_a_2156_ = lean_ctor_get(v_u_2147_, 1);
v___x_2157_ = l_Lean_Level_hasParam(v_u_2147_);
if (v___x_2157_ == 0)
{
lean_dec_ref(v_s_2146_);
return v_u_2147_;
}
else
{
lean_object* v___x_2158_; lean_object* v___x_2159_; size_t v___x_2160_; size_t v___x_2161_; uint8_t v___x_2162_; 
lean_inc(v_a_2155_);
lean_inc_ref(v_s_2146_);
v___x_2158_ = l___private_Lean_Level_0__Lean_Level_substParams_go(v_s_2146_, v_a_2155_);
lean_inc(v_a_2156_);
v___x_2159_ = l___private_Lean_Level_0__Lean_Level_substParams_go(v_s_2146_, v_a_2156_);
v___x_2160_ = lean_ptr_addr(v_a_2155_);
v___x_2161_ = lean_ptr_addr(v___x_2158_);
v___x_2162_ = lean_usize_dec_eq(v___x_2160_, v___x_2161_);
if (v___x_2162_ == 0)
{
lean_object* v___x_2163_; 
lean_dec_ref_known(v_u_2147_, 2);
v___x_2163_ = l_Lean_mkLevelMax_x27(v___x_2158_, v___x_2159_);
return v___x_2163_;
}
else
{
size_t v___x_2164_; size_t v___x_2165_; uint8_t v___x_2166_; 
v___x_2164_ = lean_ptr_addr(v_a_2156_);
v___x_2165_ = lean_ptr_addr(v___x_2159_);
v___x_2166_ = lean_usize_dec_eq(v___x_2164_, v___x_2165_);
if (v___x_2166_ == 0)
{
lean_object* v___x_2167_; 
lean_dec_ref_known(v_u_2147_, 2);
v___x_2167_ = l_Lean_mkLevelMax_x27(v___x_2158_, v___x_2159_);
return v___x_2167_;
}
else
{
lean_object* v___x_2168_; 
v___x_2168_ = l_Lean_simpLevelMax_x27(v___x_2158_, v___x_2159_, v_u_2147_);
lean_dec_ref_known(v_u_2147_, 2);
lean_dec(v___x_2159_);
lean_dec(v___x_2158_);
return v___x_2168_;
}
}
}
}
case 3:
{
lean_object* v_a_2169_; lean_object* v_a_2170_; uint8_t v___x_2171_; 
v_a_2169_ = lean_ctor_get(v_u_2147_, 0);
v_a_2170_ = lean_ctor_get(v_u_2147_, 1);
v___x_2171_ = l_Lean_Level_hasParam(v_u_2147_);
if (v___x_2171_ == 0)
{
lean_dec_ref(v_s_2146_);
return v_u_2147_;
}
else
{
lean_object* v___x_2172_; lean_object* v___x_2173_; size_t v___x_2174_; size_t v___x_2175_; uint8_t v___x_2176_; 
lean_inc(v_a_2169_);
lean_inc_ref(v_s_2146_);
v___x_2172_ = l___private_Lean_Level_0__Lean_Level_substParams_go(v_s_2146_, v_a_2169_);
lean_inc(v_a_2170_);
v___x_2173_ = l___private_Lean_Level_0__Lean_Level_substParams_go(v_s_2146_, v_a_2170_);
v___x_2174_ = lean_ptr_addr(v_a_2169_);
v___x_2175_ = lean_ptr_addr(v___x_2172_);
v___x_2176_ = lean_usize_dec_eq(v___x_2174_, v___x_2175_);
if (v___x_2176_ == 0)
{
lean_object* v___x_2177_; 
lean_dec_ref_known(v_u_2147_, 2);
v___x_2177_ = l_Lean_mkLevelIMax_x27(v___x_2172_, v___x_2173_);
return v___x_2177_;
}
else
{
size_t v___x_2178_; size_t v___x_2179_; uint8_t v___x_2180_; 
v___x_2178_ = lean_ptr_addr(v_a_2170_);
v___x_2179_ = lean_ptr_addr(v___x_2173_);
v___x_2180_ = lean_usize_dec_eq(v___x_2178_, v___x_2179_);
if (v___x_2180_ == 0)
{
lean_object* v___x_2181_; 
lean_dec_ref_known(v_u_2147_, 2);
v___x_2181_ = l_Lean_mkLevelIMax_x27(v___x_2172_, v___x_2173_);
return v___x_2181_;
}
else
{
lean_object* v___x_2182_; 
v___x_2182_ = l_Lean_simpLevelIMax_x27(v___x_2172_, v___x_2173_, v_u_2147_);
lean_dec_ref_known(v_u_2147_, 2);
return v___x_2182_;
}
}
}
}
case 4:
{
lean_object* v_a_2183_; lean_object* v___x_2184_; 
v_a_2183_ = lean_ctor_get(v_u_2147_, 0);
lean_inc(v_a_2183_);
v___x_2184_ = lean_apply_1(v_s_2146_, v_a_2183_);
if (lean_obj_tag(v___x_2184_) == 0)
{
return v_u_2147_;
}
else
{
lean_object* v_val_2185_; 
lean_dec_ref_known(v_u_2147_, 1);
v_val_2185_ = lean_ctor_get(v___x_2184_, 0);
lean_inc(v_val_2185_);
lean_dec_ref_known(v___x_2184_, 1);
return v_val_2185_;
}
}
default: 
{
lean_dec_ref(v_s_2146_);
return v_u_2147_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_substParams(lean_object* v_u_2186_, lean_object* v_s_2187_){
_start:
{
lean_object* v___x_2188_; 
v___x_2188_ = l___private_Lean_Level_0__Lean_Level_substParams_go(v_s_2187_, v_u_2186_);
return v___x_2188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_getParamSubst(lean_object* v_x_2189_, lean_object* v_x_2190_, lean_object* v_x_2191_){
_start:
{
if (lean_obj_tag(v_x_2189_) == 1)
{
if (lean_obj_tag(v_x_2190_) == 1)
{
lean_object* v_head_2192_; lean_object* v_tail_2193_; lean_object* v_head_2194_; lean_object* v_tail_2195_; uint8_t v___x_2196_; 
v_head_2192_ = lean_ctor_get(v_x_2189_, 0);
v_tail_2193_ = lean_ctor_get(v_x_2189_, 1);
v_head_2194_ = lean_ctor_get(v_x_2190_, 0);
v_tail_2195_ = lean_ctor_get(v_x_2190_, 1);
v___x_2196_ = lean_name_eq(v_head_2192_, v_x_2191_);
if (v___x_2196_ == 0)
{
v_x_2189_ = v_tail_2193_;
v_x_2190_ = v_tail_2195_;
goto _start;
}
else
{
lean_object* v___x_2198_; 
lean_inc(v_head_2194_);
v___x_2198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2198_, 0, v_head_2194_);
return v___x_2198_;
}
}
else
{
lean_object* v___x_2199_; 
v___x_2199_ = lean_box(0);
return v___x_2199_;
}
}
else
{
lean_object* v___x_2200_; 
v___x_2200_ = lean_box(0);
return v___x_2200_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_getParamSubst___boxed(lean_object* v_x_2201_, lean_object* v_x_2202_, lean_object* v_x_2203_){
_start:
{
lean_object* v_res_2204_; 
v_res_2204_ = l_Lean_Level_getParamSubst(v_x_2201_, v_x_2202_, v_x_2203_);
lean_dec(v_x_2203_);
lean_dec(v_x_2202_);
lean_dec(v_x_2201_);
return v_res_2204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_instantiateParams(lean_object* v_u_2205_, lean_object* v_paramNames_2206_, lean_object* v_vs_2207_){
_start:
{
lean_object* v___x_2208_; lean_object* v___x_2209_; 
v___x_2208_ = lean_alloc_closure((void*)(l_Lean_Level_getParamSubst___boxed), 3, 2);
lean_closure_set(v___x_2208_, 0, v_paramNames_2206_);
lean_closure_set(v___x_2208_, 1, v_vs_2207_);
v___x_2209_ = l___private_Lean_Level_0__Lean_Level_substParams_go(v___x_2208_, v_u_2205_);
return v___x_2209_;
}
}
uint8_t l___private_Lean_Level_0__Lean_Level_geq_go(lean_object* v_u_2210_, lean_object* v_v_2211_){
_start:
{
uint8_t v___y_2213_; uint8_t v___y_2227_; lean_object* v_u_u2081_2229_; lean_object* v_u_u2082_2230_; lean_object* v_v_2231_; uint8_t v___x_2234_; 
v___x_2234_ = lean_level_eq(v_u_2210_, v_v_2211_);
if (v___x_2234_ == 0)
{
switch(lean_obj_tag(v_v_2211_))
{
case 0:
{
uint8_t v___x_2235_; 
v___x_2235_ = 1;
return v___x_2235_;
}
case 2:
{
lean_object* v_a_2236_; lean_object* v_a_2237_; uint8_t v___x_2238_; 
v_a_2236_ = lean_ctor_get(v_v_2211_, 0);
v_a_2237_ = lean_ctor_get(v_v_2211_, 1);
v___x_2238_ = l___private_Lean_Level_0__Lean_Level_geq_go(v_u_2210_, v_a_2236_);
if (v___x_2238_ == 0)
{
return v___x_2238_;
}
else
{
v_v_2211_ = v_a_2237_;
goto _start;
}
}
case 1:
{
switch(lean_obj_tag(v_u_2210_))
{
case 2:
{
lean_object* v_a_2240_; lean_object* v_a_2241_; 
v_a_2240_ = lean_ctor_get(v_u_2210_, 0);
v_a_2241_ = lean_ctor_get(v_u_2210_, 1);
v_u_u2081_2229_ = v_a_2240_;
v_u_u2082_2230_ = v_a_2241_;
v_v_2231_ = v_v_2211_;
goto v___jp_2228_;
}
case 3:
{
lean_object* v_a_2242_; 
v_a_2242_ = lean_ctor_get(v_u_2210_, 1);
v_u_2210_ = v_a_2242_;
goto _start;
}
case 1:
{
lean_object* v_a_2244_; lean_object* v_a_2245_; 
v_a_2244_ = lean_ctor_get(v_v_2211_, 0);
v_a_2245_ = lean_ctor_get(v_u_2210_, 0);
v_u_2210_ = v_a_2245_;
v_v_2211_ = v_a_2244_;
goto _start;
}
default: 
{
goto v___jp_2217_;
}
}
}
default: 
{
switch(lean_obj_tag(v_u_2210_))
{
case 2:
{
lean_object* v_a_2247_; lean_object* v_a_2248_; 
v_a_2247_ = lean_ctor_get(v_u_2210_, 0);
v_a_2248_ = lean_ctor_get(v_u_2210_, 1);
v_u_u2081_2229_ = v_a_2247_;
v_u_u2082_2230_ = v_a_2248_;
v_v_2231_ = v_v_2211_;
goto v___jp_2228_;
}
case 3:
{
lean_object* v_a_2249_; 
v_a_2249_ = lean_ctor_get(v_u_2210_, 1);
v_u_2210_ = v_a_2249_;
goto _start;
}
default: 
{
goto v___jp_2217_;
}
}
}
}
}
else
{
return v___x_2234_;
}
v___jp_2212_:
{
if (v___y_2213_ == 0)
{
return v___y_2213_;
}
else
{
lean_object* v___x_2214_; lean_object* v___x_2215_; uint8_t v___x_2216_; 
v___x_2214_ = l_Lean_Level_getOffset(v_v_2211_);
v___x_2215_ = l_Lean_Level_getOffset(v_u_2210_);
v___x_2216_ = lean_nat_dec_le(v___x_2214_, v___x_2215_);
lean_dec(v___x_2215_);
lean_dec(v___x_2214_);
return v___x_2216_;
}
}
v___jp_2217_:
{
if (lean_obj_tag(v_v_2211_) == 3)
{
lean_object* v_a_2218_; lean_object* v_a_2219_; uint8_t v___x_2220_; 
v_a_2218_ = lean_ctor_get(v_v_2211_, 0);
v_a_2219_ = lean_ctor_get(v_v_2211_, 1);
v___x_2220_ = l___private_Lean_Level_0__Lean_Level_geq_go(v_u_2210_, v_a_2218_);
if (v___x_2220_ == 0)
{
return v___x_2220_;
}
else
{
v_v_2211_ = v_a_2219_;
goto _start;
}
}
else
{
lean_object* v_v_x27_2222_; lean_object* v___x_2223_; uint8_t v___x_2224_; 
v_v_x27_2222_ = l_Lean_Level_getLevelOffset(v_v_2211_);
v___x_2223_ = l_Lean_Level_getLevelOffset(v_u_2210_);
v___x_2224_ = lean_level_eq(v___x_2223_, v_v_x27_2222_);
lean_dec(v___x_2223_);
if (v___x_2224_ == 0)
{
uint8_t v___x_2225_; 
v___x_2225_ = l_Lean_Level_isZero(v_v_x27_2222_);
lean_dec(v_v_x27_2222_);
v___y_2213_ = v___x_2225_;
goto v___jp_2212_;
}
else
{
lean_dec(v_v_x27_2222_);
v___y_2213_ = v___x_2224_;
goto v___jp_2212_;
}
}
}
v___jp_2226_:
{
if (v___y_2227_ == 0)
{
goto v___jp_2217_;
}
else
{
return v___y_2227_;
}
}
v___jp_2228_:
{
uint8_t v___x_2232_; 
v___x_2232_ = l___private_Lean_Level_0__Lean_Level_geq_go(v_u_u2081_2229_, v_v_2231_);
if (v___x_2232_ == 0)
{
uint8_t v___x_2233_; 
v___x_2233_ = l___private_Lean_Level_0__Lean_Level_geq_go(v_u_u2082_2230_, v_v_2231_);
v___y_2227_ = v___x_2233_;
goto v___jp_2226_;
}
else
{
v___y_2227_ = v___x_2232_;
goto v___jp_2226_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Level_0__Lean_Level_geq_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_u_2210_ = stack[0].m_obj;
lean_object* v_v_2211_ = stack[1].m_obj;
uint8_t v_res_2251_;
v_res_2251_ = l___private_Lean_Level_0__Lean_Level_geq_go(v_u_2210_, v_v_2211_);
stack->m_num = v_res_2251_;
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_geq_go___boxed(lean_object* v_u_2252_, lean_object* v_v_2253_){
_start:
{
uint8_t v_res_2254_; lean_object* v_r_2255_; 
v_res_2254_ = l___private_Lean_Level_0__Lean_Level_geq_go(v_u_2252_, v_v_2253_);
lean_dec(v_v_2253_);
lean_dec(v_u_2252_);
v_r_2255_ = lean_box(v_res_2254_);
return v_r_2255_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_geq_go_match__1_splitter___redArg(lean_object* v_u_2256_, lean_object* v_v_2257_, lean_object* v_h__1_2258_, lean_object* v_h__2_2259_, lean_object* v_h__3_2260_, lean_object* v_h__4_2261_, lean_object* v_h__5_2262_, lean_object* v_h__6_2263_){
_start:
{
switch(lean_obj_tag(v_v_2257_))
{
case 0:
{
lean_object* v___x_2264_; 
lean_dec(v_h__6_2263_);
lean_dec(v_h__5_2262_);
lean_dec(v_h__4_2261_);
lean_dec(v_h__3_2260_);
lean_dec(v_h__2_2259_);
v___x_2264_ = lean_apply_1(v_h__1_2258_, v_u_2256_);
return v___x_2264_;
}
case 2:
{
lean_object* v_a_2265_; lean_object* v_a_2266_; lean_object* v___x_2267_; 
lean_dec(v_h__6_2263_);
lean_dec(v_h__5_2262_);
lean_dec(v_h__4_2261_);
lean_dec(v_h__3_2260_);
lean_dec(v_h__1_2258_);
v_a_2265_ = lean_ctor_get(v_v_2257_, 0);
lean_inc(v_a_2265_);
v_a_2266_ = lean_ctor_get(v_v_2257_, 1);
lean_inc(v_a_2266_);
lean_dec_ref_known(v_v_2257_, 2);
v___x_2267_ = lean_apply_3(v_h__2_2259_, v_u_2256_, v_a_2265_, v_a_2266_);
return v___x_2267_;
}
case 1:
{
lean_dec(v_h__2_2259_);
lean_dec(v_h__1_2258_);
switch(lean_obj_tag(v_u_2256_))
{
case 2:
{
lean_object* v_a_2268_; lean_object* v_a_2269_; lean_object* v___x_2270_; 
lean_dec(v_h__6_2263_);
lean_dec(v_h__5_2262_);
lean_dec(v_h__4_2261_);
v_a_2268_ = lean_ctor_get(v_u_2256_, 0);
lean_inc(v_a_2268_);
v_a_2269_ = lean_ctor_get(v_u_2256_, 1);
lean_inc(v_a_2269_);
lean_dec_ref_known(v_u_2256_, 2);
v___x_2270_ = lean_apply_5(v_h__3_2260_, v_a_2268_, v_a_2269_, v_v_2257_, lean_box(0), lean_box(0));
return v___x_2270_;
}
case 3:
{
lean_object* v_a_2271_; lean_object* v_a_2272_; lean_object* v___x_2273_; 
lean_dec(v_h__6_2263_);
lean_dec(v_h__5_2262_);
lean_dec(v_h__3_2260_);
v_a_2271_ = lean_ctor_get(v_u_2256_, 0);
lean_inc(v_a_2271_);
v_a_2272_ = lean_ctor_get(v_u_2256_, 1);
lean_inc(v_a_2272_);
lean_dec_ref_known(v_u_2256_, 2);
v___x_2273_ = lean_apply_5(v_h__4_2261_, v_a_2271_, v_a_2272_, v_v_2257_, lean_box(0), lean_box(0));
return v___x_2273_;
}
case 1:
{
lean_object* v_a_2274_; lean_object* v_a_2275_; lean_object* v___x_2276_; 
lean_dec(v_h__6_2263_);
lean_dec(v_h__4_2261_);
lean_dec(v_h__3_2260_);
v_a_2274_ = lean_ctor_get(v_v_2257_, 0);
lean_inc(v_a_2274_);
lean_dec_ref_known(v_v_2257_, 1);
v_a_2275_ = lean_ctor_get(v_u_2256_, 0);
lean_inc(v_a_2275_);
lean_dec_ref_known(v_u_2256_, 1);
v___x_2276_ = lean_apply_2(v_h__5_2262_, v_a_2275_, v_a_2274_);
return v___x_2276_;
}
default: 
{
lean_object* v___x_2277_; 
lean_dec(v_h__5_2262_);
lean_dec(v_h__4_2261_);
lean_dec(v_h__3_2260_);
v___x_2277_ = lean_apply_7(v_h__6_2263_, v_u_2256_, v_v_2257_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_2277_;
}
}
}
default: 
{
lean_dec(v_h__5_2262_);
lean_dec(v_h__2_2259_);
lean_dec(v_h__1_2258_);
switch(lean_obj_tag(v_u_2256_))
{
case 2:
{
lean_object* v_a_2278_; lean_object* v_a_2279_; lean_object* v___x_2280_; 
lean_dec(v_h__6_2263_);
lean_dec(v_h__4_2261_);
v_a_2278_ = lean_ctor_get(v_u_2256_, 0);
lean_inc(v_a_2278_);
v_a_2279_ = lean_ctor_get(v_u_2256_, 1);
lean_inc(v_a_2279_);
lean_dec_ref_known(v_u_2256_, 2);
v___x_2280_ = lean_apply_5(v_h__3_2260_, v_a_2278_, v_a_2279_, v_v_2257_, lean_box(0), lean_box(0));
return v___x_2280_;
}
case 3:
{
lean_object* v_a_2281_; lean_object* v_a_2282_; lean_object* v___x_2283_; 
lean_dec(v_h__6_2263_);
lean_dec(v_h__3_2260_);
v_a_2281_ = lean_ctor_get(v_u_2256_, 0);
lean_inc(v_a_2281_);
v_a_2282_ = lean_ctor_get(v_u_2256_, 1);
lean_inc(v_a_2282_);
lean_dec_ref_known(v_u_2256_, 2);
v___x_2283_ = lean_apply_5(v_h__4_2261_, v_a_2281_, v_a_2282_, v_v_2257_, lean_box(0), lean_box(0));
return v___x_2283_;
}
default: 
{
lean_object* v___x_2284_; 
lean_dec(v_h__4_2261_);
lean_dec(v_h__3_2260_);
v___x_2284_ = lean_apply_7(v_h__6_2263_, v_u_2256_, v_v_2257_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_2284_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_geq_go_match__1_splitter(lean_object* v_motive_2285_, lean_object* v_u_2286_, lean_object* v_v_2287_, lean_object* v_h__1_2288_, lean_object* v_h__2_2289_, lean_object* v_h__3_2290_, lean_object* v_h__4_2291_, lean_object* v_h__5_2292_, lean_object* v_h__6_2293_){
_start:
{
switch(lean_obj_tag(v_v_2287_))
{
case 0:
{
lean_object* v___x_2294_; 
lean_dec(v_h__6_2293_);
lean_dec(v_h__5_2292_);
lean_dec(v_h__4_2291_);
lean_dec(v_h__3_2290_);
lean_dec(v_h__2_2289_);
v___x_2294_ = lean_apply_1(v_h__1_2288_, v_u_2286_);
return v___x_2294_;
}
case 2:
{
lean_object* v_a_2295_; lean_object* v_a_2296_; lean_object* v___x_2297_; 
lean_dec(v_h__6_2293_);
lean_dec(v_h__5_2292_);
lean_dec(v_h__4_2291_);
lean_dec(v_h__3_2290_);
lean_dec(v_h__1_2288_);
v_a_2295_ = lean_ctor_get(v_v_2287_, 0);
lean_inc(v_a_2295_);
v_a_2296_ = lean_ctor_get(v_v_2287_, 1);
lean_inc(v_a_2296_);
lean_dec_ref_known(v_v_2287_, 2);
v___x_2297_ = lean_apply_3(v_h__2_2289_, v_u_2286_, v_a_2295_, v_a_2296_);
return v___x_2297_;
}
case 1:
{
lean_dec(v_h__2_2289_);
lean_dec(v_h__1_2288_);
switch(lean_obj_tag(v_u_2286_))
{
case 2:
{
lean_object* v_a_2298_; lean_object* v_a_2299_; lean_object* v___x_2300_; 
lean_dec(v_h__6_2293_);
lean_dec(v_h__5_2292_);
lean_dec(v_h__4_2291_);
v_a_2298_ = lean_ctor_get(v_u_2286_, 0);
lean_inc(v_a_2298_);
v_a_2299_ = lean_ctor_get(v_u_2286_, 1);
lean_inc(v_a_2299_);
lean_dec_ref_known(v_u_2286_, 2);
v___x_2300_ = lean_apply_5(v_h__3_2290_, v_a_2298_, v_a_2299_, v_v_2287_, lean_box(0), lean_box(0));
return v___x_2300_;
}
case 3:
{
lean_object* v_a_2301_; lean_object* v_a_2302_; lean_object* v___x_2303_; 
lean_dec(v_h__6_2293_);
lean_dec(v_h__5_2292_);
lean_dec(v_h__3_2290_);
v_a_2301_ = lean_ctor_get(v_u_2286_, 0);
lean_inc(v_a_2301_);
v_a_2302_ = lean_ctor_get(v_u_2286_, 1);
lean_inc(v_a_2302_);
lean_dec_ref_known(v_u_2286_, 2);
v___x_2303_ = lean_apply_5(v_h__4_2291_, v_a_2301_, v_a_2302_, v_v_2287_, lean_box(0), lean_box(0));
return v___x_2303_;
}
case 1:
{
lean_object* v_a_2304_; lean_object* v_a_2305_; lean_object* v___x_2306_; 
lean_dec(v_h__6_2293_);
lean_dec(v_h__4_2291_);
lean_dec(v_h__3_2290_);
v_a_2304_ = lean_ctor_get(v_v_2287_, 0);
lean_inc(v_a_2304_);
lean_dec_ref_known(v_v_2287_, 1);
v_a_2305_ = lean_ctor_get(v_u_2286_, 0);
lean_inc(v_a_2305_);
lean_dec_ref_known(v_u_2286_, 1);
v___x_2306_ = lean_apply_2(v_h__5_2292_, v_a_2305_, v_a_2304_);
return v___x_2306_;
}
default: 
{
lean_object* v___x_2307_; 
lean_dec(v_h__5_2292_);
lean_dec(v_h__4_2291_);
lean_dec(v_h__3_2290_);
v___x_2307_ = lean_apply_7(v_h__6_2293_, v_u_2286_, v_v_2287_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_2307_;
}
}
}
default: 
{
lean_dec(v_h__5_2292_);
lean_dec(v_h__2_2289_);
lean_dec(v_h__1_2288_);
switch(lean_obj_tag(v_u_2286_))
{
case 2:
{
lean_object* v_a_2308_; lean_object* v_a_2309_; lean_object* v___x_2310_; 
lean_dec(v_h__6_2293_);
lean_dec(v_h__4_2291_);
v_a_2308_ = lean_ctor_get(v_u_2286_, 0);
lean_inc(v_a_2308_);
v_a_2309_ = lean_ctor_get(v_u_2286_, 1);
lean_inc(v_a_2309_);
lean_dec_ref_known(v_u_2286_, 2);
v___x_2310_ = lean_apply_5(v_h__3_2290_, v_a_2308_, v_a_2309_, v_v_2287_, lean_box(0), lean_box(0));
return v___x_2310_;
}
case 3:
{
lean_object* v_a_2311_; lean_object* v_a_2312_; lean_object* v___x_2313_; 
lean_dec(v_h__6_2293_);
lean_dec(v_h__3_2290_);
v_a_2311_ = lean_ctor_get(v_u_2286_, 0);
lean_inc(v_a_2311_);
v_a_2312_ = lean_ctor_get(v_u_2286_, 1);
lean_inc(v_a_2312_);
lean_dec_ref_known(v_u_2286_, 2);
v___x_2313_ = lean_apply_5(v_h__4_2291_, v_a_2311_, v_a_2312_, v_v_2287_, lean_box(0), lean_box(0));
return v___x_2313_;
}
default: 
{
lean_object* v___x_2314_; 
lean_dec(v_h__4_2291_);
lean_dec(v_h__3_2290_);
v___x_2314_ = lean_apply_7(v_h__6_2293_, v_u_2286_, v_v_2287_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_2314_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_isIMax_match__1_splitter___redArg(lean_object* v_x_2315_, lean_object* v_h__1_2316_, lean_object* v_h__2_2317_){
_start:
{
if (lean_obj_tag(v_x_2315_) == 3)
{
lean_object* v_a_2318_; lean_object* v_a_2319_; lean_object* v___x_2320_; 
lean_dec(v_h__2_2317_);
v_a_2318_ = lean_ctor_get(v_x_2315_, 0);
lean_inc(v_a_2318_);
v_a_2319_ = lean_ctor_get(v_x_2315_, 1);
lean_inc(v_a_2319_);
lean_dec_ref_known(v_x_2315_, 2);
v___x_2320_ = lean_apply_2(v_h__1_2316_, v_a_2318_, v_a_2319_);
return v___x_2320_;
}
else
{
lean_object* v___x_2321_; 
lean_dec(v_h__1_2316_);
v___x_2321_ = lean_apply_2(v_h__2_2317_, v_x_2315_, lean_box(0));
return v___x_2321_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_isIMax_match__1_splitter(lean_object* v_motive_2322_, lean_object* v_x_2323_, lean_object* v_h__1_2324_, lean_object* v_h__2_2325_){
_start:
{
if (lean_obj_tag(v_x_2323_) == 3)
{
lean_object* v_a_2326_; lean_object* v_a_2327_; lean_object* v___x_2328_; 
lean_dec(v_h__2_2325_);
v_a_2326_ = lean_ctor_get(v_x_2323_, 0);
lean_inc(v_a_2326_);
v_a_2327_ = lean_ctor_get(v_x_2323_, 1);
lean_inc(v_a_2327_);
lean_dec_ref_known(v_x_2323_, 2);
v___x_2328_ = lean_apply_2(v_h__1_2324_, v_a_2326_, v_a_2327_);
return v___x_2328_;
}
else
{
lean_object* v___x_2329_; 
lean_dec(v_h__1_2324_);
v___x_2329_ = lean_apply_2(v_h__2_2325_, v_x_2323_, lean_box(0));
return v___x_2329_;
}
}
}
uint8_t l_Lean_Level_geq(lean_object* v_u_2330_, lean_object* v_v_2331_){
_start:
{
lean_object* v___x_2332_; lean_object* v___x_2333_; uint8_t v___x_2334_; 
v___x_2332_ = l_Lean_Level_normalize(v_u_2330_);
v___x_2333_ = l_Lean_Level_normalize(v_v_2331_);
v___x_2334_ = l___private_Lean_Level_0__Lean_Level_geq_go(v___x_2332_, v___x_2333_);
lean_dec(v___x_2333_);
lean_dec(v___x_2332_);
return v___x_2334_;
}
}
LEAN_EXPORT void l_Lean_Level_geq_0interp(lean_interpreter_value* stack)
{
lean_object* v_u_2330_ = stack[0].m_obj;
lean_object* v_v_2331_ = stack[1].m_obj;
uint8_t v_res_2335_;
v_res_2335_ = l_Lean_Level_geq(v_u_2330_, v_v_2331_);
stack->m_num = v_res_2335_;
}
LEAN_EXPORT lean_object* l_Lean_Level_geq___boxed(lean_object* v_u_2336_, lean_object* v_v_2337_){
_start:
{
uint8_t v_res_2338_; lean_object* v_r_2339_; 
v_res_2338_ = l_Lean_Level_geq(v_u_2336_, v_v_2337_);
lean_dec(v_v_2337_);
lean_dec(v_u_2336_);
v_r_2339_ = lean_box(v_res_2338_);
return v_r_2339_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Level_collectMVars_spec__1___redArg(lean_object* v_k_2340_, lean_object* v_v_2341_, lean_object* v_t_2342_){
_start:
{
if (lean_obj_tag(v_t_2342_) == 0)
{
lean_object* v_size_2343_; lean_object* v_k_2344_; lean_object* v_v_2345_; lean_object* v_l_2346_; lean_object* v_r_2347_; lean_object* v___x_2349_; uint8_t v_isShared_2350_; uint8_t v_isSharedCheck_2627_; 
v_size_2343_ = lean_ctor_get(v_t_2342_, 0);
v_k_2344_ = lean_ctor_get(v_t_2342_, 1);
v_v_2345_ = lean_ctor_get(v_t_2342_, 2);
v_l_2346_ = lean_ctor_get(v_t_2342_, 3);
v_r_2347_ = lean_ctor_get(v_t_2342_, 4);
v_isSharedCheck_2627_ = !lean_is_exclusive(v_t_2342_);
if (v_isSharedCheck_2627_ == 0)
{
v___x_2349_ = v_t_2342_;
v_isShared_2350_ = v_isSharedCheck_2627_;
goto v_resetjp_2348_;
}
else
{
lean_inc(v_r_2347_);
lean_inc(v_l_2346_);
lean_inc(v_v_2345_);
lean_inc(v_k_2344_);
lean_inc(v_size_2343_);
lean_dec(v_t_2342_);
v___x_2349_ = lean_box(0);
v_isShared_2350_ = v_isSharedCheck_2627_;
goto v_resetjp_2348_;
}
v_resetjp_2348_:
{
uint8_t v___x_2351_; 
v___x_2351_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2340_, v_k_2344_);
switch(v___x_2351_)
{
case 0:
{
lean_object* v_impl_2352_; lean_object* v___x_2353_; 
lean_dec(v_size_2343_);
v_impl_2352_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Level_collectMVars_spec__1___redArg(v_k_2340_, v_v_2341_, v_l_2346_);
v___x_2353_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_2347_) == 0)
{
lean_object* v_size_2354_; lean_object* v_size_2355_; lean_object* v_k_2356_; lean_object* v_v_2357_; lean_object* v_l_2358_; lean_object* v_r_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; uint8_t v___x_2362_; 
v_size_2354_ = lean_ctor_get(v_r_2347_, 0);
v_size_2355_ = lean_ctor_get(v_impl_2352_, 0);
v_k_2356_ = lean_ctor_get(v_impl_2352_, 1);
v_v_2357_ = lean_ctor_get(v_impl_2352_, 2);
v_l_2358_ = lean_ctor_get(v_impl_2352_, 3);
v_r_2359_ = lean_ctor_get(v_impl_2352_, 4);
lean_inc(v_r_2359_);
v___x_2360_ = lean_unsigned_to_nat(3u);
v___x_2361_ = lean_nat_mul(v___x_2360_, v_size_2354_);
v___x_2362_ = lean_nat_dec_lt(v___x_2361_, v_size_2355_);
lean_dec(v___x_2361_);
if (v___x_2362_ == 0)
{
lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2366_; 
lean_dec(v_r_2359_);
v___x_2363_ = lean_nat_add(v___x_2353_, v_size_2355_);
v___x_2364_ = lean_nat_add(v___x_2363_, v_size_2354_);
lean_dec(v___x_2363_);
if (v_isShared_2350_ == 0)
{
lean_ctor_set(v___x_2349_, 3, v_impl_2352_);
lean_ctor_set(v___x_2349_, 0, v___x_2364_);
v___x_2366_ = v___x_2349_;
goto v_reusejp_2365_;
}
else
{
lean_object* v_reuseFailAlloc_2367_; 
v_reuseFailAlloc_2367_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2367_, 0, v___x_2364_);
lean_ctor_set(v_reuseFailAlloc_2367_, 1, v_k_2344_);
lean_ctor_set(v_reuseFailAlloc_2367_, 2, v_v_2345_);
lean_ctor_set(v_reuseFailAlloc_2367_, 3, v_impl_2352_);
lean_ctor_set(v_reuseFailAlloc_2367_, 4, v_r_2347_);
v___x_2366_ = v_reuseFailAlloc_2367_;
goto v_reusejp_2365_;
}
v_reusejp_2365_:
{
return v___x_2366_;
}
}
else
{
lean_object* v___x_2369_; uint8_t v_isShared_2370_; uint8_t v_isSharedCheck_2433_; 
lean_inc(v_l_2358_);
lean_inc(v_v_2357_);
lean_inc(v_k_2356_);
lean_inc(v_size_2355_);
v_isSharedCheck_2433_ = !lean_is_exclusive(v_impl_2352_);
if (v_isSharedCheck_2433_ == 0)
{
lean_object* v_unused_2434_; lean_object* v_unused_2435_; lean_object* v_unused_2436_; lean_object* v_unused_2437_; lean_object* v_unused_2438_; 
v_unused_2434_ = lean_ctor_get(v_impl_2352_, 4);
lean_dec(v_unused_2434_);
v_unused_2435_ = lean_ctor_get(v_impl_2352_, 3);
lean_dec(v_unused_2435_);
v_unused_2436_ = lean_ctor_get(v_impl_2352_, 2);
lean_dec(v_unused_2436_);
v_unused_2437_ = lean_ctor_get(v_impl_2352_, 1);
lean_dec(v_unused_2437_);
v_unused_2438_ = lean_ctor_get(v_impl_2352_, 0);
lean_dec(v_unused_2438_);
v___x_2369_ = v_impl_2352_;
v_isShared_2370_ = v_isSharedCheck_2433_;
goto v_resetjp_2368_;
}
else
{
lean_dec(v_impl_2352_);
v___x_2369_ = lean_box(0);
v_isShared_2370_ = v_isSharedCheck_2433_;
goto v_resetjp_2368_;
}
v_resetjp_2368_:
{
lean_object* v_size_2371_; lean_object* v_size_2372_; lean_object* v_k_2373_; lean_object* v_v_2374_; lean_object* v_l_2375_; lean_object* v_r_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; uint8_t v___x_2379_; 
v_size_2371_ = lean_ctor_get(v_l_2358_, 0);
v_size_2372_ = lean_ctor_get(v_r_2359_, 0);
v_k_2373_ = lean_ctor_get(v_r_2359_, 1);
v_v_2374_ = lean_ctor_get(v_r_2359_, 2);
v_l_2375_ = lean_ctor_get(v_r_2359_, 3);
v_r_2376_ = lean_ctor_get(v_r_2359_, 4);
v___x_2377_ = lean_unsigned_to_nat(2u);
v___x_2378_ = lean_nat_mul(v___x_2377_, v_size_2371_);
v___x_2379_ = lean_nat_dec_lt(v_size_2372_, v___x_2378_);
lean_dec(v___x_2378_);
if (v___x_2379_ == 0)
{
lean_object* v___x_2381_; uint8_t v_isShared_2382_; uint8_t v_isSharedCheck_2408_; 
lean_inc(v_r_2376_);
lean_inc(v_l_2375_);
lean_inc(v_v_2374_);
lean_inc(v_k_2373_);
v_isSharedCheck_2408_ = !lean_is_exclusive(v_r_2359_);
if (v_isSharedCheck_2408_ == 0)
{
lean_object* v_unused_2409_; lean_object* v_unused_2410_; lean_object* v_unused_2411_; lean_object* v_unused_2412_; lean_object* v_unused_2413_; 
v_unused_2409_ = lean_ctor_get(v_r_2359_, 4);
lean_dec(v_unused_2409_);
v_unused_2410_ = lean_ctor_get(v_r_2359_, 3);
lean_dec(v_unused_2410_);
v_unused_2411_ = lean_ctor_get(v_r_2359_, 2);
lean_dec(v_unused_2411_);
v_unused_2412_ = lean_ctor_get(v_r_2359_, 1);
lean_dec(v_unused_2412_);
v_unused_2413_ = lean_ctor_get(v_r_2359_, 0);
lean_dec(v_unused_2413_);
v___x_2381_ = v_r_2359_;
v_isShared_2382_ = v_isSharedCheck_2408_;
goto v_resetjp_2380_;
}
else
{
lean_dec(v_r_2359_);
v___x_2381_ = lean_box(0);
v_isShared_2382_ = v_isSharedCheck_2408_;
goto v_resetjp_2380_;
}
v_resetjp_2380_:
{
lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___y_2386_; lean_object* v___y_2387_; lean_object* v___y_2388_; lean_object* v___x_2396_; lean_object* v___y_2398_; 
v___x_2383_ = lean_nat_add(v___x_2353_, v_size_2355_);
lean_dec(v_size_2355_);
v___x_2384_ = lean_nat_add(v___x_2383_, v_size_2354_);
lean_dec(v___x_2383_);
v___x_2396_ = lean_nat_add(v___x_2353_, v_size_2371_);
if (lean_obj_tag(v_l_2375_) == 0)
{
lean_object* v_size_2406_; 
v_size_2406_ = lean_ctor_get(v_l_2375_, 0);
lean_inc(v_size_2406_);
v___y_2398_ = v_size_2406_;
goto v___jp_2397_;
}
else
{
lean_object* v___x_2407_; 
v___x_2407_ = lean_unsigned_to_nat(0u);
v___y_2398_ = v___x_2407_;
goto v___jp_2397_;
}
v___jp_2385_:
{
lean_object* v___x_2389_; lean_object* v___x_2391_; 
v___x_2389_ = lean_nat_add(v___y_2387_, v___y_2388_);
lean_dec(v___y_2388_);
lean_dec(v___y_2387_);
if (v_isShared_2382_ == 0)
{
lean_ctor_set(v___x_2381_, 4, v_r_2347_);
lean_ctor_set(v___x_2381_, 3, v_r_2376_);
lean_ctor_set(v___x_2381_, 2, v_v_2345_);
lean_ctor_set(v___x_2381_, 1, v_k_2344_);
lean_ctor_set(v___x_2381_, 0, v___x_2389_);
v___x_2391_ = v___x_2381_;
goto v_reusejp_2390_;
}
else
{
lean_object* v_reuseFailAlloc_2395_; 
v_reuseFailAlloc_2395_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2395_, 0, v___x_2389_);
lean_ctor_set(v_reuseFailAlloc_2395_, 1, v_k_2344_);
lean_ctor_set(v_reuseFailAlloc_2395_, 2, v_v_2345_);
lean_ctor_set(v_reuseFailAlloc_2395_, 3, v_r_2376_);
lean_ctor_set(v_reuseFailAlloc_2395_, 4, v_r_2347_);
v___x_2391_ = v_reuseFailAlloc_2395_;
goto v_reusejp_2390_;
}
v_reusejp_2390_:
{
lean_object* v___x_2393_; 
if (v_isShared_2370_ == 0)
{
lean_ctor_set(v___x_2369_, 4, v___x_2391_);
lean_ctor_set(v___x_2369_, 3, v___y_2386_);
lean_ctor_set(v___x_2369_, 2, v_v_2374_);
lean_ctor_set(v___x_2369_, 1, v_k_2373_);
lean_ctor_set(v___x_2369_, 0, v___x_2384_);
v___x_2393_ = v___x_2369_;
goto v_reusejp_2392_;
}
else
{
lean_object* v_reuseFailAlloc_2394_; 
v_reuseFailAlloc_2394_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2394_, 0, v___x_2384_);
lean_ctor_set(v_reuseFailAlloc_2394_, 1, v_k_2373_);
lean_ctor_set(v_reuseFailAlloc_2394_, 2, v_v_2374_);
lean_ctor_set(v_reuseFailAlloc_2394_, 3, v___y_2386_);
lean_ctor_set(v_reuseFailAlloc_2394_, 4, v___x_2391_);
v___x_2393_ = v_reuseFailAlloc_2394_;
goto v_reusejp_2392_;
}
v_reusejp_2392_:
{
return v___x_2393_;
}
}
}
v___jp_2397_:
{
lean_object* v___x_2399_; lean_object* v___x_2401_; 
v___x_2399_ = lean_nat_add(v___x_2396_, v___y_2398_);
lean_dec(v___y_2398_);
lean_dec(v___x_2396_);
if (v_isShared_2350_ == 0)
{
lean_ctor_set(v___x_2349_, 4, v_l_2375_);
lean_ctor_set(v___x_2349_, 3, v_l_2358_);
lean_ctor_set(v___x_2349_, 2, v_v_2357_);
lean_ctor_set(v___x_2349_, 1, v_k_2356_);
lean_ctor_set(v___x_2349_, 0, v___x_2399_);
v___x_2401_ = v___x_2349_;
goto v_reusejp_2400_;
}
else
{
lean_object* v_reuseFailAlloc_2405_; 
v_reuseFailAlloc_2405_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2405_, 0, v___x_2399_);
lean_ctor_set(v_reuseFailAlloc_2405_, 1, v_k_2356_);
lean_ctor_set(v_reuseFailAlloc_2405_, 2, v_v_2357_);
lean_ctor_set(v_reuseFailAlloc_2405_, 3, v_l_2358_);
lean_ctor_set(v_reuseFailAlloc_2405_, 4, v_l_2375_);
v___x_2401_ = v_reuseFailAlloc_2405_;
goto v_reusejp_2400_;
}
v_reusejp_2400_:
{
lean_object* v___x_2402_; 
v___x_2402_ = lean_nat_add(v___x_2353_, v_size_2354_);
if (lean_obj_tag(v_r_2376_) == 0)
{
lean_object* v_size_2403_; 
v_size_2403_ = lean_ctor_get(v_r_2376_, 0);
lean_inc(v_size_2403_);
v___y_2386_ = v___x_2401_;
v___y_2387_ = v___x_2402_;
v___y_2388_ = v_size_2403_;
goto v___jp_2385_;
}
else
{
lean_object* v___x_2404_; 
v___x_2404_ = lean_unsigned_to_nat(0u);
v___y_2386_ = v___x_2401_;
v___y_2387_ = v___x_2402_;
v___y_2388_ = v___x_2404_;
goto v___jp_2385_;
}
}
}
}
}
else
{
lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2419_; 
lean_del_object(v___x_2349_);
v___x_2414_ = lean_nat_add(v___x_2353_, v_size_2355_);
lean_dec(v_size_2355_);
v___x_2415_ = lean_nat_add(v___x_2414_, v_size_2354_);
lean_dec(v___x_2414_);
v___x_2416_ = lean_nat_add(v___x_2353_, v_size_2354_);
v___x_2417_ = lean_nat_add(v___x_2416_, v_size_2372_);
lean_dec(v___x_2416_);
lean_inc_ref(v_r_2347_);
if (v_isShared_2370_ == 0)
{
lean_ctor_set(v___x_2369_, 4, v_r_2347_);
lean_ctor_set(v___x_2369_, 3, v_r_2359_);
lean_ctor_set(v___x_2369_, 2, v_v_2345_);
lean_ctor_set(v___x_2369_, 1, v_k_2344_);
lean_ctor_set(v___x_2369_, 0, v___x_2417_);
v___x_2419_ = v___x_2369_;
goto v_reusejp_2418_;
}
else
{
lean_object* v_reuseFailAlloc_2432_; 
v_reuseFailAlloc_2432_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2432_, 0, v___x_2417_);
lean_ctor_set(v_reuseFailAlloc_2432_, 1, v_k_2344_);
lean_ctor_set(v_reuseFailAlloc_2432_, 2, v_v_2345_);
lean_ctor_set(v_reuseFailAlloc_2432_, 3, v_r_2359_);
lean_ctor_set(v_reuseFailAlloc_2432_, 4, v_r_2347_);
v___x_2419_ = v_reuseFailAlloc_2432_;
goto v_reusejp_2418_;
}
v_reusejp_2418_:
{
lean_object* v___x_2421_; uint8_t v_isShared_2422_; uint8_t v_isSharedCheck_2426_; 
v_isSharedCheck_2426_ = !lean_is_exclusive(v_r_2347_);
if (v_isSharedCheck_2426_ == 0)
{
lean_object* v_unused_2427_; lean_object* v_unused_2428_; lean_object* v_unused_2429_; lean_object* v_unused_2430_; lean_object* v_unused_2431_; 
v_unused_2427_ = lean_ctor_get(v_r_2347_, 4);
lean_dec(v_unused_2427_);
v_unused_2428_ = lean_ctor_get(v_r_2347_, 3);
lean_dec(v_unused_2428_);
v_unused_2429_ = lean_ctor_get(v_r_2347_, 2);
lean_dec(v_unused_2429_);
v_unused_2430_ = lean_ctor_get(v_r_2347_, 1);
lean_dec(v_unused_2430_);
v_unused_2431_ = lean_ctor_get(v_r_2347_, 0);
lean_dec(v_unused_2431_);
v___x_2421_ = v_r_2347_;
v_isShared_2422_ = v_isSharedCheck_2426_;
goto v_resetjp_2420_;
}
else
{
lean_dec(v_r_2347_);
v___x_2421_ = lean_box(0);
v_isShared_2422_ = v_isSharedCheck_2426_;
goto v_resetjp_2420_;
}
v_resetjp_2420_:
{
lean_object* v___x_2424_; 
if (v_isShared_2422_ == 0)
{
lean_ctor_set(v___x_2421_, 4, v___x_2419_);
lean_ctor_set(v___x_2421_, 3, v_l_2358_);
lean_ctor_set(v___x_2421_, 2, v_v_2357_);
lean_ctor_set(v___x_2421_, 1, v_k_2356_);
lean_ctor_set(v___x_2421_, 0, v___x_2415_);
v___x_2424_ = v___x_2421_;
goto v_reusejp_2423_;
}
else
{
lean_object* v_reuseFailAlloc_2425_; 
v_reuseFailAlloc_2425_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2425_, 0, v___x_2415_);
lean_ctor_set(v_reuseFailAlloc_2425_, 1, v_k_2356_);
lean_ctor_set(v_reuseFailAlloc_2425_, 2, v_v_2357_);
lean_ctor_set(v_reuseFailAlloc_2425_, 3, v_l_2358_);
lean_ctor_set(v_reuseFailAlloc_2425_, 4, v___x_2419_);
v___x_2424_ = v_reuseFailAlloc_2425_;
goto v_reusejp_2423_;
}
v_reusejp_2423_:
{
return v___x_2424_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_2439_; 
v_l_2439_ = lean_ctor_get(v_impl_2352_, 3);
if (lean_obj_tag(v_l_2439_) == 0)
{
lean_object* v_r_2440_; lean_object* v_k_2441_; lean_object* v_v_2442_; lean_object* v___x_2444_; uint8_t v_isShared_2445_; uint8_t v_isSharedCheck_2453_; 
lean_inc_ref(v_l_2439_);
v_r_2440_ = lean_ctor_get(v_impl_2352_, 4);
v_k_2441_ = lean_ctor_get(v_impl_2352_, 1);
v_v_2442_ = lean_ctor_get(v_impl_2352_, 2);
v_isSharedCheck_2453_ = !lean_is_exclusive(v_impl_2352_);
if (v_isSharedCheck_2453_ == 0)
{
lean_object* v_unused_2454_; lean_object* v_unused_2455_; 
v_unused_2454_ = lean_ctor_get(v_impl_2352_, 3);
lean_dec(v_unused_2454_);
v_unused_2455_ = lean_ctor_get(v_impl_2352_, 0);
lean_dec(v_unused_2455_);
v___x_2444_ = v_impl_2352_;
v_isShared_2445_ = v_isSharedCheck_2453_;
goto v_resetjp_2443_;
}
else
{
lean_inc(v_r_2440_);
lean_inc(v_v_2442_);
lean_inc(v_k_2441_);
lean_dec(v_impl_2352_);
v___x_2444_ = lean_box(0);
v_isShared_2445_ = v_isSharedCheck_2453_;
goto v_resetjp_2443_;
}
v_resetjp_2443_:
{
lean_object* v___x_2446_; lean_object* v___x_2448_; 
v___x_2446_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_2440_);
if (v_isShared_2445_ == 0)
{
lean_ctor_set(v___x_2444_, 3, v_r_2440_);
lean_ctor_set(v___x_2444_, 2, v_v_2345_);
lean_ctor_set(v___x_2444_, 1, v_k_2344_);
lean_ctor_set(v___x_2444_, 0, v___x_2353_);
v___x_2448_ = v___x_2444_;
goto v_reusejp_2447_;
}
else
{
lean_object* v_reuseFailAlloc_2452_; 
v_reuseFailAlloc_2452_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2452_, 0, v___x_2353_);
lean_ctor_set(v_reuseFailAlloc_2452_, 1, v_k_2344_);
lean_ctor_set(v_reuseFailAlloc_2452_, 2, v_v_2345_);
lean_ctor_set(v_reuseFailAlloc_2452_, 3, v_r_2440_);
lean_ctor_set(v_reuseFailAlloc_2452_, 4, v_r_2440_);
v___x_2448_ = v_reuseFailAlloc_2452_;
goto v_reusejp_2447_;
}
v_reusejp_2447_:
{
lean_object* v___x_2450_; 
if (v_isShared_2350_ == 0)
{
lean_ctor_set(v___x_2349_, 4, v___x_2448_);
lean_ctor_set(v___x_2349_, 3, v_l_2439_);
lean_ctor_set(v___x_2349_, 2, v_v_2442_);
lean_ctor_set(v___x_2349_, 1, v_k_2441_);
lean_ctor_set(v___x_2349_, 0, v___x_2446_);
v___x_2450_ = v___x_2349_;
goto v_reusejp_2449_;
}
else
{
lean_object* v_reuseFailAlloc_2451_; 
v_reuseFailAlloc_2451_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2451_, 0, v___x_2446_);
lean_ctor_set(v_reuseFailAlloc_2451_, 1, v_k_2441_);
lean_ctor_set(v_reuseFailAlloc_2451_, 2, v_v_2442_);
lean_ctor_set(v_reuseFailAlloc_2451_, 3, v_l_2439_);
lean_ctor_set(v_reuseFailAlloc_2451_, 4, v___x_2448_);
v___x_2450_ = v_reuseFailAlloc_2451_;
goto v_reusejp_2449_;
}
v_reusejp_2449_:
{
return v___x_2450_;
}
}
}
}
else
{
lean_object* v_r_2456_; 
v_r_2456_ = lean_ctor_get(v_impl_2352_, 4);
lean_inc(v_r_2456_);
if (lean_obj_tag(v_r_2456_) == 0)
{
lean_object* v_k_2457_; lean_object* v_v_2458_; lean_object* v___x_2460_; uint8_t v_isShared_2461_; uint8_t v_isSharedCheck_2481_; 
lean_inc(v_l_2439_);
v_k_2457_ = lean_ctor_get(v_impl_2352_, 1);
v_v_2458_ = lean_ctor_get(v_impl_2352_, 2);
v_isSharedCheck_2481_ = !lean_is_exclusive(v_impl_2352_);
if (v_isSharedCheck_2481_ == 0)
{
lean_object* v_unused_2482_; lean_object* v_unused_2483_; lean_object* v_unused_2484_; 
v_unused_2482_ = lean_ctor_get(v_impl_2352_, 4);
lean_dec(v_unused_2482_);
v_unused_2483_ = lean_ctor_get(v_impl_2352_, 3);
lean_dec(v_unused_2483_);
v_unused_2484_ = lean_ctor_get(v_impl_2352_, 0);
lean_dec(v_unused_2484_);
v___x_2460_ = v_impl_2352_;
v_isShared_2461_ = v_isSharedCheck_2481_;
goto v_resetjp_2459_;
}
else
{
lean_inc(v_v_2458_);
lean_inc(v_k_2457_);
lean_dec(v_impl_2352_);
v___x_2460_ = lean_box(0);
v_isShared_2461_ = v_isSharedCheck_2481_;
goto v_resetjp_2459_;
}
v_resetjp_2459_:
{
lean_object* v_k_2462_; lean_object* v_v_2463_; lean_object* v___x_2465_; uint8_t v_isShared_2466_; uint8_t v_isSharedCheck_2477_; 
v_k_2462_ = lean_ctor_get(v_r_2456_, 1);
v_v_2463_ = lean_ctor_get(v_r_2456_, 2);
v_isSharedCheck_2477_ = !lean_is_exclusive(v_r_2456_);
if (v_isSharedCheck_2477_ == 0)
{
lean_object* v_unused_2478_; lean_object* v_unused_2479_; lean_object* v_unused_2480_; 
v_unused_2478_ = lean_ctor_get(v_r_2456_, 4);
lean_dec(v_unused_2478_);
v_unused_2479_ = lean_ctor_get(v_r_2456_, 3);
lean_dec(v_unused_2479_);
v_unused_2480_ = lean_ctor_get(v_r_2456_, 0);
lean_dec(v_unused_2480_);
v___x_2465_ = v_r_2456_;
v_isShared_2466_ = v_isSharedCheck_2477_;
goto v_resetjp_2464_;
}
else
{
lean_inc(v_v_2463_);
lean_inc(v_k_2462_);
lean_dec(v_r_2456_);
v___x_2465_ = lean_box(0);
v_isShared_2466_ = v_isSharedCheck_2477_;
goto v_resetjp_2464_;
}
v_resetjp_2464_:
{
lean_object* v___x_2467_; lean_object* v___x_2469_; 
v___x_2467_ = lean_unsigned_to_nat(3u);
if (v_isShared_2466_ == 0)
{
lean_ctor_set(v___x_2465_, 4, v_l_2439_);
lean_ctor_set(v___x_2465_, 3, v_l_2439_);
lean_ctor_set(v___x_2465_, 2, v_v_2458_);
lean_ctor_set(v___x_2465_, 1, v_k_2457_);
lean_ctor_set(v___x_2465_, 0, v___x_2353_);
v___x_2469_ = v___x_2465_;
goto v_reusejp_2468_;
}
else
{
lean_object* v_reuseFailAlloc_2476_; 
v_reuseFailAlloc_2476_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2476_, 0, v___x_2353_);
lean_ctor_set(v_reuseFailAlloc_2476_, 1, v_k_2457_);
lean_ctor_set(v_reuseFailAlloc_2476_, 2, v_v_2458_);
lean_ctor_set(v_reuseFailAlloc_2476_, 3, v_l_2439_);
lean_ctor_set(v_reuseFailAlloc_2476_, 4, v_l_2439_);
v___x_2469_ = v_reuseFailAlloc_2476_;
goto v_reusejp_2468_;
}
v_reusejp_2468_:
{
lean_object* v___x_2471_; 
if (v_isShared_2461_ == 0)
{
lean_ctor_set(v___x_2460_, 4, v_l_2439_);
lean_ctor_set(v___x_2460_, 2, v_v_2345_);
lean_ctor_set(v___x_2460_, 1, v_k_2344_);
lean_ctor_set(v___x_2460_, 0, v___x_2353_);
v___x_2471_ = v___x_2460_;
goto v_reusejp_2470_;
}
else
{
lean_object* v_reuseFailAlloc_2475_; 
v_reuseFailAlloc_2475_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2475_, 0, v___x_2353_);
lean_ctor_set(v_reuseFailAlloc_2475_, 1, v_k_2344_);
lean_ctor_set(v_reuseFailAlloc_2475_, 2, v_v_2345_);
lean_ctor_set(v_reuseFailAlloc_2475_, 3, v_l_2439_);
lean_ctor_set(v_reuseFailAlloc_2475_, 4, v_l_2439_);
v___x_2471_ = v_reuseFailAlloc_2475_;
goto v_reusejp_2470_;
}
v_reusejp_2470_:
{
lean_object* v___x_2473_; 
if (v_isShared_2350_ == 0)
{
lean_ctor_set(v___x_2349_, 4, v___x_2471_);
lean_ctor_set(v___x_2349_, 3, v___x_2469_);
lean_ctor_set(v___x_2349_, 2, v_v_2463_);
lean_ctor_set(v___x_2349_, 1, v_k_2462_);
lean_ctor_set(v___x_2349_, 0, v___x_2467_);
v___x_2473_ = v___x_2349_;
goto v_reusejp_2472_;
}
else
{
lean_object* v_reuseFailAlloc_2474_; 
v_reuseFailAlloc_2474_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2474_, 0, v___x_2467_);
lean_ctor_set(v_reuseFailAlloc_2474_, 1, v_k_2462_);
lean_ctor_set(v_reuseFailAlloc_2474_, 2, v_v_2463_);
lean_ctor_set(v_reuseFailAlloc_2474_, 3, v___x_2469_);
lean_ctor_set(v_reuseFailAlloc_2474_, 4, v___x_2471_);
v___x_2473_ = v_reuseFailAlloc_2474_;
goto v_reusejp_2472_;
}
v_reusejp_2472_:
{
return v___x_2473_;
}
}
}
}
}
}
else
{
lean_object* v___x_2485_; lean_object* v___x_2487_; 
v___x_2485_ = lean_unsigned_to_nat(2u);
if (v_isShared_2350_ == 0)
{
lean_ctor_set(v___x_2349_, 4, v_r_2456_);
lean_ctor_set(v___x_2349_, 3, v_impl_2352_);
lean_ctor_set(v___x_2349_, 0, v___x_2485_);
v___x_2487_ = v___x_2349_;
goto v_reusejp_2486_;
}
else
{
lean_object* v_reuseFailAlloc_2488_; 
v_reuseFailAlloc_2488_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2488_, 0, v___x_2485_);
lean_ctor_set(v_reuseFailAlloc_2488_, 1, v_k_2344_);
lean_ctor_set(v_reuseFailAlloc_2488_, 2, v_v_2345_);
lean_ctor_set(v_reuseFailAlloc_2488_, 3, v_impl_2352_);
lean_ctor_set(v_reuseFailAlloc_2488_, 4, v_r_2456_);
v___x_2487_ = v_reuseFailAlloc_2488_;
goto v_reusejp_2486_;
}
v_reusejp_2486_:
{
return v___x_2487_;
}
}
}
}
}
case 1:
{
lean_object* v___x_2490_; 
lean_dec(v_v_2345_);
lean_dec(v_k_2344_);
if (v_isShared_2350_ == 0)
{
lean_ctor_set(v___x_2349_, 2, v_v_2341_);
lean_ctor_set(v___x_2349_, 1, v_k_2340_);
v___x_2490_ = v___x_2349_;
goto v_reusejp_2489_;
}
else
{
lean_object* v_reuseFailAlloc_2491_; 
v_reuseFailAlloc_2491_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2491_, 0, v_size_2343_);
lean_ctor_set(v_reuseFailAlloc_2491_, 1, v_k_2340_);
lean_ctor_set(v_reuseFailAlloc_2491_, 2, v_v_2341_);
lean_ctor_set(v_reuseFailAlloc_2491_, 3, v_l_2346_);
lean_ctor_set(v_reuseFailAlloc_2491_, 4, v_r_2347_);
v___x_2490_ = v_reuseFailAlloc_2491_;
goto v_reusejp_2489_;
}
v_reusejp_2489_:
{
return v___x_2490_;
}
}
default: 
{
lean_object* v_impl_2492_; lean_object* v___x_2493_; 
lean_dec(v_size_2343_);
v_impl_2492_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Level_collectMVars_spec__1___redArg(v_k_2340_, v_v_2341_, v_r_2347_);
v___x_2493_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_2346_) == 0)
{
lean_object* v_size_2494_; lean_object* v_size_2495_; lean_object* v_k_2496_; lean_object* v_v_2497_; lean_object* v_l_2498_; lean_object* v_r_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; uint8_t v___x_2502_; 
v_size_2494_ = lean_ctor_get(v_l_2346_, 0);
v_size_2495_ = lean_ctor_get(v_impl_2492_, 0);
v_k_2496_ = lean_ctor_get(v_impl_2492_, 1);
v_v_2497_ = lean_ctor_get(v_impl_2492_, 2);
v_l_2498_ = lean_ctor_get(v_impl_2492_, 3);
lean_inc(v_l_2498_);
v_r_2499_ = lean_ctor_get(v_impl_2492_, 4);
v___x_2500_ = lean_unsigned_to_nat(3u);
v___x_2501_ = lean_nat_mul(v___x_2500_, v_size_2494_);
v___x_2502_ = lean_nat_dec_lt(v___x_2501_, v_size_2495_);
lean_dec(v___x_2501_);
if (v___x_2502_ == 0)
{
lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2506_; 
lean_dec(v_l_2498_);
v___x_2503_ = lean_nat_add(v___x_2493_, v_size_2494_);
v___x_2504_ = lean_nat_add(v___x_2503_, v_size_2495_);
lean_dec(v___x_2503_);
if (v_isShared_2350_ == 0)
{
lean_ctor_set(v___x_2349_, 4, v_impl_2492_);
lean_ctor_set(v___x_2349_, 0, v___x_2504_);
v___x_2506_ = v___x_2349_;
goto v_reusejp_2505_;
}
else
{
lean_object* v_reuseFailAlloc_2507_; 
v_reuseFailAlloc_2507_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2507_, 0, v___x_2504_);
lean_ctor_set(v_reuseFailAlloc_2507_, 1, v_k_2344_);
lean_ctor_set(v_reuseFailAlloc_2507_, 2, v_v_2345_);
lean_ctor_set(v_reuseFailAlloc_2507_, 3, v_l_2346_);
lean_ctor_set(v_reuseFailAlloc_2507_, 4, v_impl_2492_);
v___x_2506_ = v_reuseFailAlloc_2507_;
goto v_reusejp_2505_;
}
v_reusejp_2505_:
{
return v___x_2506_;
}
}
else
{
lean_object* v___x_2509_; uint8_t v_isShared_2510_; uint8_t v_isSharedCheck_2571_; 
lean_inc(v_r_2499_);
lean_inc(v_v_2497_);
lean_inc(v_k_2496_);
lean_inc(v_size_2495_);
v_isSharedCheck_2571_ = !lean_is_exclusive(v_impl_2492_);
if (v_isSharedCheck_2571_ == 0)
{
lean_object* v_unused_2572_; lean_object* v_unused_2573_; lean_object* v_unused_2574_; lean_object* v_unused_2575_; lean_object* v_unused_2576_; 
v_unused_2572_ = lean_ctor_get(v_impl_2492_, 4);
lean_dec(v_unused_2572_);
v_unused_2573_ = lean_ctor_get(v_impl_2492_, 3);
lean_dec(v_unused_2573_);
v_unused_2574_ = lean_ctor_get(v_impl_2492_, 2);
lean_dec(v_unused_2574_);
v_unused_2575_ = lean_ctor_get(v_impl_2492_, 1);
lean_dec(v_unused_2575_);
v_unused_2576_ = lean_ctor_get(v_impl_2492_, 0);
lean_dec(v_unused_2576_);
v___x_2509_ = v_impl_2492_;
v_isShared_2510_ = v_isSharedCheck_2571_;
goto v_resetjp_2508_;
}
else
{
lean_dec(v_impl_2492_);
v___x_2509_ = lean_box(0);
v_isShared_2510_ = v_isSharedCheck_2571_;
goto v_resetjp_2508_;
}
v_resetjp_2508_:
{
lean_object* v_size_2511_; lean_object* v_k_2512_; lean_object* v_v_2513_; lean_object* v_l_2514_; lean_object* v_r_2515_; lean_object* v_size_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; uint8_t v___x_2519_; 
v_size_2511_ = lean_ctor_get(v_l_2498_, 0);
v_k_2512_ = lean_ctor_get(v_l_2498_, 1);
v_v_2513_ = lean_ctor_get(v_l_2498_, 2);
v_l_2514_ = lean_ctor_get(v_l_2498_, 3);
v_r_2515_ = lean_ctor_get(v_l_2498_, 4);
v_size_2516_ = lean_ctor_get(v_r_2499_, 0);
v___x_2517_ = lean_unsigned_to_nat(2u);
v___x_2518_ = lean_nat_mul(v___x_2517_, v_size_2516_);
v___x_2519_ = lean_nat_dec_lt(v_size_2511_, v___x_2518_);
lean_dec(v___x_2518_);
if (v___x_2519_ == 0)
{
lean_object* v___x_2521_; uint8_t v_isShared_2522_; uint8_t v_isSharedCheck_2547_; 
lean_inc(v_r_2515_);
lean_inc(v_l_2514_);
lean_inc(v_v_2513_);
lean_inc(v_k_2512_);
v_isSharedCheck_2547_ = !lean_is_exclusive(v_l_2498_);
if (v_isSharedCheck_2547_ == 0)
{
lean_object* v_unused_2548_; lean_object* v_unused_2549_; lean_object* v_unused_2550_; lean_object* v_unused_2551_; lean_object* v_unused_2552_; 
v_unused_2548_ = lean_ctor_get(v_l_2498_, 4);
lean_dec(v_unused_2548_);
v_unused_2549_ = lean_ctor_get(v_l_2498_, 3);
lean_dec(v_unused_2549_);
v_unused_2550_ = lean_ctor_get(v_l_2498_, 2);
lean_dec(v_unused_2550_);
v_unused_2551_ = lean_ctor_get(v_l_2498_, 1);
lean_dec(v_unused_2551_);
v_unused_2552_ = lean_ctor_get(v_l_2498_, 0);
lean_dec(v_unused_2552_);
v___x_2521_ = v_l_2498_;
v_isShared_2522_ = v_isSharedCheck_2547_;
goto v_resetjp_2520_;
}
else
{
lean_dec(v_l_2498_);
v___x_2521_ = lean_box(0);
v_isShared_2522_ = v_isSharedCheck_2547_;
goto v_resetjp_2520_;
}
v_resetjp_2520_:
{
lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___y_2526_; lean_object* v___y_2527_; lean_object* v___y_2528_; lean_object* v___y_2537_; 
v___x_2523_ = lean_nat_add(v___x_2493_, v_size_2494_);
v___x_2524_ = lean_nat_add(v___x_2523_, v_size_2495_);
lean_dec(v_size_2495_);
if (lean_obj_tag(v_l_2514_) == 0)
{
lean_object* v_size_2545_; 
v_size_2545_ = lean_ctor_get(v_l_2514_, 0);
lean_inc(v_size_2545_);
v___y_2537_ = v_size_2545_;
goto v___jp_2536_;
}
else
{
lean_object* v___x_2546_; 
v___x_2546_ = lean_unsigned_to_nat(0u);
v___y_2537_ = v___x_2546_;
goto v___jp_2536_;
}
v___jp_2525_:
{
lean_object* v___x_2529_; lean_object* v___x_2531_; 
v___x_2529_ = lean_nat_add(v___y_2526_, v___y_2528_);
lean_dec(v___y_2528_);
lean_dec(v___y_2526_);
if (v_isShared_2522_ == 0)
{
lean_ctor_set(v___x_2521_, 4, v_r_2499_);
lean_ctor_set(v___x_2521_, 3, v_r_2515_);
lean_ctor_set(v___x_2521_, 2, v_v_2497_);
lean_ctor_set(v___x_2521_, 1, v_k_2496_);
lean_ctor_set(v___x_2521_, 0, v___x_2529_);
v___x_2531_ = v___x_2521_;
goto v_reusejp_2530_;
}
else
{
lean_object* v_reuseFailAlloc_2535_; 
v_reuseFailAlloc_2535_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2535_, 0, v___x_2529_);
lean_ctor_set(v_reuseFailAlloc_2535_, 1, v_k_2496_);
lean_ctor_set(v_reuseFailAlloc_2535_, 2, v_v_2497_);
lean_ctor_set(v_reuseFailAlloc_2535_, 3, v_r_2515_);
lean_ctor_set(v_reuseFailAlloc_2535_, 4, v_r_2499_);
v___x_2531_ = v_reuseFailAlloc_2535_;
goto v_reusejp_2530_;
}
v_reusejp_2530_:
{
lean_object* v___x_2533_; 
if (v_isShared_2510_ == 0)
{
lean_ctor_set(v___x_2509_, 4, v___x_2531_);
lean_ctor_set(v___x_2509_, 3, v___y_2527_);
lean_ctor_set(v___x_2509_, 2, v_v_2513_);
lean_ctor_set(v___x_2509_, 1, v_k_2512_);
lean_ctor_set(v___x_2509_, 0, v___x_2524_);
v___x_2533_ = v___x_2509_;
goto v_reusejp_2532_;
}
else
{
lean_object* v_reuseFailAlloc_2534_; 
v_reuseFailAlloc_2534_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2534_, 0, v___x_2524_);
lean_ctor_set(v_reuseFailAlloc_2534_, 1, v_k_2512_);
lean_ctor_set(v_reuseFailAlloc_2534_, 2, v_v_2513_);
lean_ctor_set(v_reuseFailAlloc_2534_, 3, v___y_2527_);
lean_ctor_set(v_reuseFailAlloc_2534_, 4, v___x_2531_);
v___x_2533_ = v_reuseFailAlloc_2534_;
goto v_reusejp_2532_;
}
v_reusejp_2532_:
{
return v___x_2533_;
}
}
}
v___jp_2536_:
{
lean_object* v___x_2538_; lean_object* v___x_2540_; 
v___x_2538_ = lean_nat_add(v___x_2523_, v___y_2537_);
lean_dec(v___y_2537_);
lean_dec(v___x_2523_);
if (v_isShared_2350_ == 0)
{
lean_ctor_set(v___x_2349_, 4, v_l_2514_);
lean_ctor_set(v___x_2349_, 0, v___x_2538_);
v___x_2540_ = v___x_2349_;
goto v_reusejp_2539_;
}
else
{
lean_object* v_reuseFailAlloc_2544_; 
v_reuseFailAlloc_2544_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2544_, 0, v___x_2538_);
lean_ctor_set(v_reuseFailAlloc_2544_, 1, v_k_2344_);
lean_ctor_set(v_reuseFailAlloc_2544_, 2, v_v_2345_);
lean_ctor_set(v_reuseFailAlloc_2544_, 3, v_l_2346_);
lean_ctor_set(v_reuseFailAlloc_2544_, 4, v_l_2514_);
v___x_2540_ = v_reuseFailAlloc_2544_;
goto v_reusejp_2539_;
}
v_reusejp_2539_:
{
lean_object* v___x_2541_; 
v___x_2541_ = lean_nat_add(v___x_2493_, v_size_2516_);
if (lean_obj_tag(v_r_2515_) == 0)
{
lean_object* v_size_2542_; 
v_size_2542_ = lean_ctor_get(v_r_2515_, 0);
lean_inc(v_size_2542_);
v___y_2526_ = v___x_2541_;
v___y_2527_ = v___x_2540_;
v___y_2528_ = v_size_2542_;
goto v___jp_2525_;
}
else
{
lean_object* v___x_2543_; 
v___x_2543_ = lean_unsigned_to_nat(0u);
v___y_2526_ = v___x_2541_;
v___y_2527_ = v___x_2540_;
v___y_2528_ = v___x_2543_;
goto v___jp_2525_;
}
}
}
}
}
else
{
lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2557_; 
lean_del_object(v___x_2349_);
v___x_2553_ = lean_nat_add(v___x_2493_, v_size_2494_);
v___x_2554_ = lean_nat_add(v___x_2553_, v_size_2495_);
lean_dec(v_size_2495_);
v___x_2555_ = lean_nat_add(v___x_2553_, v_size_2511_);
lean_dec(v___x_2553_);
lean_inc_ref(v_l_2346_);
if (v_isShared_2510_ == 0)
{
lean_ctor_set(v___x_2509_, 4, v_l_2498_);
lean_ctor_set(v___x_2509_, 3, v_l_2346_);
lean_ctor_set(v___x_2509_, 2, v_v_2345_);
lean_ctor_set(v___x_2509_, 1, v_k_2344_);
lean_ctor_set(v___x_2509_, 0, v___x_2555_);
v___x_2557_ = v___x_2509_;
goto v_reusejp_2556_;
}
else
{
lean_object* v_reuseFailAlloc_2570_; 
v_reuseFailAlloc_2570_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2570_, 0, v___x_2555_);
lean_ctor_set(v_reuseFailAlloc_2570_, 1, v_k_2344_);
lean_ctor_set(v_reuseFailAlloc_2570_, 2, v_v_2345_);
lean_ctor_set(v_reuseFailAlloc_2570_, 3, v_l_2346_);
lean_ctor_set(v_reuseFailAlloc_2570_, 4, v_l_2498_);
v___x_2557_ = v_reuseFailAlloc_2570_;
goto v_reusejp_2556_;
}
v_reusejp_2556_:
{
lean_object* v___x_2559_; uint8_t v_isShared_2560_; uint8_t v_isSharedCheck_2564_; 
v_isSharedCheck_2564_ = !lean_is_exclusive(v_l_2346_);
if (v_isSharedCheck_2564_ == 0)
{
lean_object* v_unused_2565_; lean_object* v_unused_2566_; lean_object* v_unused_2567_; lean_object* v_unused_2568_; lean_object* v_unused_2569_; 
v_unused_2565_ = lean_ctor_get(v_l_2346_, 4);
lean_dec(v_unused_2565_);
v_unused_2566_ = lean_ctor_get(v_l_2346_, 3);
lean_dec(v_unused_2566_);
v_unused_2567_ = lean_ctor_get(v_l_2346_, 2);
lean_dec(v_unused_2567_);
v_unused_2568_ = lean_ctor_get(v_l_2346_, 1);
lean_dec(v_unused_2568_);
v_unused_2569_ = lean_ctor_get(v_l_2346_, 0);
lean_dec(v_unused_2569_);
v___x_2559_ = v_l_2346_;
v_isShared_2560_ = v_isSharedCheck_2564_;
goto v_resetjp_2558_;
}
else
{
lean_dec(v_l_2346_);
v___x_2559_ = lean_box(0);
v_isShared_2560_ = v_isSharedCheck_2564_;
goto v_resetjp_2558_;
}
v_resetjp_2558_:
{
lean_object* v___x_2562_; 
if (v_isShared_2560_ == 0)
{
lean_ctor_set(v___x_2559_, 4, v_r_2499_);
lean_ctor_set(v___x_2559_, 3, v___x_2557_);
lean_ctor_set(v___x_2559_, 2, v_v_2497_);
lean_ctor_set(v___x_2559_, 1, v_k_2496_);
lean_ctor_set(v___x_2559_, 0, v___x_2554_);
v___x_2562_ = v___x_2559_;
goto v_reusejp_2561_;
}
else
{
lean_object* v_reuseFailAlloc_2563_; 
v_reuseFailAlloc_2563_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2563_, 0, v___x_2554_);
lean_ctor_set(v_reuseFailAlloc_2563_, 1, v_k_2496_);
lean_ctor_set(v_reuseFailAlloc_2563_, 2, v_v_2497_);
lean_ctor_set(v_reuseFailAlloc_2563_, 3, v___x_2557_);
lean_ctor_set(v_reuseFailAlloc_2563_, 4, v_r_2499_);
v___x_2562_ = v_reuseFailAlloc_2563_;
goto v_reusejp_2561_;
}
v_reusejp_2561_:
{
return v___x_2562_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_2577_; 
v_l_2577_ = lean_ctor_get(v_impl_2492_, 3);
lean_inc(v_l_2577_);
if (lean_obj_tag(v_l_2577_) == 0)
{
lean_object* v_r_2578_; lean_object* v_k_2579_; lean_object* v_v_2580_; lean_object* v___x_2582_; uint8_t v_isShared_2583_; uint8_t v_isSharedCheck_2603_; 
v_r_2578_ = lean_ctor_get(v_impl_2492_, 4);
v_k_2579_ = lean_ctor_get(v_impl_2492_, 1);
v_v_2580_ = lean_ctor_get(v_impl_2492_, 2);
v_isSharedCheck_2603_ = !lean_is_exclusive(v_impl_2492_);
if (v_isSharedCheck_2603_ == 0)
{
lean_object* v_unused_2604_; lean_object* v_unused_2605_; 
v_unused_2604_ = lean_ctor_get(v_impl_2492_, 3);
lean_dec(v_unused_2604_);
v_unused_2605_ = lean_ctor_get(v_impl_2492_, 0);
lean_dec(v_unused_2605_);
v___x_2582_ = v_impl_2492_;
v_isShared_2583_ = v_isSharedCheck_2603_;
goto v_resetjp_2581_;
}
else
{
lean_inc(v_r_2578_);
lean_inc(v_v_2580_);
lean_inc(v_k_2579_);
lean_dec(v_impl_2492_);
v___x_2582_ = lean_box(0);
v_isShared_2583_ = v_isSharedCheck_2603_;
goto v_resetjp_2581_;
}
v_resetjp_2581_:
{
lean_object* v_k_2584_; lean_object* v_v_2585_; lean_object* v___x_2587_; uint8_t v_isShared_2588_; uint8_t v_isSharedCheck_2599_; 
v_k_2584_ = lean_ctor_get(v_l_2577_, 1);
v_v_2585_ = lean_ctor_get(v_l_2577_, 2);
v_isSharedCheck_2599_ = !lean_is_exclusive(v_l_2577_);
if (v_isSharedCheck_2599_ == 0)
{
lean_object* v_unused_2600_; lean_object* v_unused_2601_; lean_object* v_unused_2602_; 
v_unused_2600_ = lean_ctor_get(v_l_2577_, 4);
lean_dec(v_unused_2600_);
v_unused_2601_ = lean_ctor_get(v_l_2577_, 3);
lean_dec(v_unused_2601_);
v_unused_2602_ = lean_ctor_get(v_l_2577_, 0);
lean_dec(v_unused_2602_);
v___x_2587_ = v_l_2577_;
v_isShared_2588_ = v_isSharedCheck_2599_;
goto v_resetjp_2586_;
}
else
{
lean_inc(v_v_2585_);
lean_inc(v_k_2584_);
lean_dec(v_l_2577_);
v___x_2587_ = lean_box(0);
v_isShared_2588_ = v_isSharedCheck_2599_;
goto v_resetjp_2586_;
}
v_resetjp_2586_:
{
lean_object* v___x_2589_; lean_object* v___x_2591_; 
v___x_2589_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_2578_, 2);
if (v_isShared_2588_ == 0)
{
lean_ctor_set(v___x_2587_, 4, v_r_2578_);
lean_ctor_set(v___x_2587_, 3, v_r_2578_);
lean_ctor_set(v___x_2587_, 2, v_v_2345_);
lean_ctor_set(v___x_2587_, 1, v_k_2344_);
lean_ctor_set(v___x_2587_, 0, v___x_2493_);
v___x_2591_ = v___x_2587_;
goto v_reusejp_2590_;
}
else
{
lean_object* v_reuseFailAlloc_2598_; 
v_reuseFailAlloc_2598_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2598_, 0, v___x_2493_);
lean_ctor_set(v_reuseFailAlloc_2598_, 1, v_k_2344_);
lean_ctor_set(v_reuseFailAlloc_2598_, 2, v_v_2345_);
lean_ctor_set(v_reuseFailAlloc_2598_, 3, v_r_2578_);
lean_ctor_set(v_reuseFailAlloc_2598_, 4, v_r_2578_);
v___x_2591_ = v_reuseFailAlloc_2598_;
goto v_reusejp_2590_;
}
v_reusejp_2590_:
{
lean_object* v___x_2593_; 
lean_inc(v_r_2578_);
if (v_isShared_2583_ == 0)
{
lean_ctor_set(v___x_2582_, 3, v_r_2578_);
lean_ctor_set(v___x_2582_, 0, v___x_2493_);
v___x_2593_ = v___x_2582_;
goto v_reusejp_2592_;
}
else
{
lean_object* v_reuseFailAlloc_2597_; 
v_reuseFailAlloc_2597_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2597_, 0, v___x_2493_);
lean_ctor_set(v_reuseFailAlloc_2597_, 1, v_k_2579_);
lean_ctor_set(v_reuseFailAlloc_2597_, 2, v_v_2580_);
lean_ctor_set(v_reuseFailAlloc_2597_, 3, v_r_2578_);
lean_ctor_set(v_reuseFailAlloc_2597_, 4, v_r_2578_);
v___x_2593_ = v_reuseFailAlloc_2597_;
goto v_reusejp_2592_;
}
v_reusejp_2592_:
{
lean_object* v___x_2595_; 
if (v_isShared_2350_ == 0)
{
lean_ctor_set(v___x_2349_, 4, v___x_2593_);
lean_ctor_set(v___x_2349_, 3, v___x_2591_);
lean_ctor_set(v___x_2349_, 2, v_v_2585_);
lean_ctor_set(v___x_2349_, 1, v_k_2584_);
lean_ctor_set(v___x_2349_, 0, v___x_2589_);
v___x_2595_ = v___x_2349_;
goto v_reusejp_2594_;
}
else
{
lean_object* v_reuseFailAlloc_2596_; 
v_reuseFailAlloc_2596_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2596_, 0, v___x_2589_);
lean_ctor_set(v_reuseFailAlloc_2596_, 1, v_k_2584_);
lean_ctor_set(v_reuseFailAlloc_2596_, 2, v_v_2585_);
lean_ctor_set(v_reuseFailAlloc_2596_, 3, v___x_2591_);
lean_ctor_set(v_reuseFailAlloc_2596_, 4, v___x_2593_);
v___x_2595_ = v_reuseFailAlloc_2596_;
goto v_reusejp_2594_;
}
v_reusejp_2594_:
{
return v___x_2595_;
}
}
}
}
}
}
else
{
lean_object* v_r_2606_; 
v_r_2606_ = lean_ctor_get(v_impl_2492_, 4);
lean_inc(v_r_2606_);
if (lean_obj_tag(v_r_2606_) == 0)
{
lean_object* v_k_2607_; lean_object* v_v_2608_; lean_object* v___x_2610_; uint8_t v_isShared_2611_; uint8_t v_isSharedCheck_2619_; 
v_k_2607_ = lean_ctor_get(v_impl_2492_, 1);
v_v_2608_ = lean_ctor_get(v_impl_2492_, 2);
v_isSharedCheck_2619_ = !lean_is_exclusive(v_impl_2492_);
if (v_isSharedCheck_2619_ == 0)
{
lean_object* v_unused_2620_; lean_object* v_unused_2621_; lean_object* v_unused_2622_; 
v_unused_2620_ = lean_ctor_get(v_impl_2492_, 4);
lean_dec(v_unused_2620_);
v_unused_2621_ = lean_ctor_get(v_impl_2492_, 3);
lean_dec(v_unused_2621_);
v_unused_2622_ = lean_ctor_get(v_impl_2492_, 0);
lean_dec(v_unused_2622_);
v___x_2610_ = v_impl_2492_;
v_isShared_2611_ = v_isSharedCheck_2619_;
goto v_resetjp_2609_;
}
else
{
lean_inc(v_v_2608_);
lean_inc(v_k_2607_);
lean_dec(v_impl_2492_);
v___x_2610_ = lean_box(0);
v_isShared_2611_ = v_isSharedCheck_2619_;
goto v_resetjp_2609_;
}
v_resetjp_2609_:
{
lean_object* v___x_2612_; lean_object* v___x_2614_; 
v___x_2612_ = lean_unsigned_to_nat(3u);
if (v_isShared_2611_ == 0)
{
lean_ctor_set(v___x_2610_, 4, v_l_2577_);
lean_ctor_set(v___x_2610_, 2, v_v_2345_);
lean_ctor_set(v___x_2610_, 1, v_k_2344_);
lean_ctor_set(v___x_2610_, 0, v___x_2493_);
v___x_2614_ = v___x_2610_;
goto v_reusejp_2613_;
}
else
{
lean_object* v_reuseFailAlloc_2618_; 
v_reuseFailAlloc_2618_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2618_, 0, v___x_2493_);
lean_ctor_set(v_reuseFailAlloc_2618_, 1, v_k_2344_);
lean_ctor_set(v_reuseFailAlloc_2618_, 2, v_v_2345_);
lean_ctor_set(v_reuseFailAlloc_2618_, 3, v_l_2577_);
lean_ctor_set(v_reuseFailAlloc_2618_, 4, v_l_2577_);
v___x_2614_ = v_reuseFailAlloc_2618_;
goto v_reusejp_2613_;
}
v_reusejp_2613_:
{
lean_object* v___x_2616_; 
if (v_isShared_2350_ == 0)
{
lean_ctor_set(v___x_2349_, 4, v_r_2606_);
lean_ctor_set(v___x_2349_, 3, v___x_2614_);
lean_ctor_set(v___x_2349_, 2, v_v_2608_);
lean_ctor_set(v___x_2349_, 1, v_k_2607_);
lean_ctor_set(v___x_2349_, 0, v___x_2612_);
v___x_2616_ = v___x_2349_;
goto v_reusejp_2615_;
}
else
{
lean_object* v_reuseFailAlloc_2617_; 
v_reuseFailAlloc_2617_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2617_, 0, v___x_2612_);
lean_ctor_set(v_reuseFailAlloc_2617_, 1, v_k_2607_);
lean_ctor_set(v_reuseFailAlloc_2617_, 2, v_v_2608_);
lean_ctor_set(v_reuseFailAlloc_2617_, 3, v___x_2614_);
lean_ctor_set(v_reuseFailAlloc_2617_, 4, v_r_2606_);
v___x_2616_ = v_reuseFailAlloc_2617_;
goto v_reusejp_2615_;
}
v_reusejp_2615_:
{
return v___x_2616_;
}
}
}
}
else
{
lean_object* v___x_2623_; lean_object* v___x_2625_; 
v___x_2623_ = lean_unsigned_to_nat(2u);
if (v_isShared_2350_ == 0)
{
lean_ctor_set(v___x_2349_, 4, v_impl_2492_);
lean_ctor_set(v___x_2349_, 3, v_r_2606_);
lean_ctor_set(v___x_2349_, 0, v___x_2623_);
v___x_2625_ = v___x_2349_;
goto v_reusejp_2624_;
}
else
{
lean_object* v_reuseFailAlloc_2626_; 
v_reuseFailAlloc_2626_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2626_, 0, v___x_2623_);
lean_ctor_set(v_reuseFailAlloc_2626_, 1, v_k_2344_);
lean_ctor_set(v_reuseFailAlloc_2626_, 2, v_v_2345_);
lean_ctor_set(v_reuseFailAlloc_2626_, 3, v_r_2606_);
lean_ctor_set(v_reuseFailAlloc_2626_, 4, v_impl_2492_);
v___x_2625_ = v_reuseFailAlloc_2626_;
goto v_reusejp_2624_;
}
v_reusejp_2624_:
{
return v___x_2625_;
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
lean_object* v___x_2628_; lean_object* v___x_2629_; 
v___x_2628_ = lean_unsigned_to_nat(1u);
v___x_2629_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2629_, 0, v___x_2628_);
lean_ctor_set(v___x_2629_, 1, v_k_2340_);
lean_ctor_set(v___x_2629_, 2, v_v_2341_);
lean_ctor_set(v___x_2629_, 3, v_t_2342_);
lean_ctor_set(v___x_2629_, 4, v_t_2342_);
return v___x_2629_;
}
}
}
uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Level_collectMVars_spec__0___redArg(lean_object* v_k_2630_, lean_object* v_t_2631_){
_start:
{
if (lean_obj_tag(v_t_2631_) == 0)
{
lean_object* v_k_2632_; lean_object* v_l_2633_; lean_object* v_r_2634_; uint8_t v___x_2635_; 
v_k_2632_ = lean_ctor_get(v_t_2631_, 1);
v_l_2633_ = lean_ctor_get(v_t_2631_, 3);
v_r_2634_ = lean_ctor_get(v_t_2631_, 4);
v___x_2635_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2630_, v_k_2632_);
switch(v___x_2635_)
{
case 0:
{
v_t_2631_ = v_l_2633_;
goto _start;
}
case 1:
{
uint8_t v___x_2637_; 
v___x_2637_ = 1;
return v___x_2637_;
}
default: 
{
v_t_2631_ = v_r_2634_;
goto _start;
}
}
}
else
{
uint8_t v___x_2639_; 
v___x_2639_ = 0;
return v___x_2639_;
}
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Level_collectMVars_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_2630_ = stack[0].m_obj;
lean_object* v_t_2631_ = stack[1].m_obj;
uint8_t v_res_2640_;
v_res_2640_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Level_collectMVars_spec__0___redArg(v_k_2630_, v_t_2631_);
stack->m_num = v_res_2640_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Level_collectMVars_spec__0___redArg___boxed(lean_object* v_k_2641_, lean_object* v_t_2642_){
_start:
{
uint8_t v_res_2643_; lean_object* v_r_2644_; 
v_res_2643_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Level_collectMVars_spec__0___redArg(v_k_2641_, v_t_2642_);
lean_dec(v_t_2642_);
lean_dec(v_k_2641_);
v_r_2644_ = lean_box(v_res_2643_);
return v_r_2644_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_collectMVars(lean_object* v_u_2645_, lean_object* v_s_2646_){
_start:
{
lean_object* v_u_2648_; lean_object* v_v_2649_; 
switch(lean_obj_tag(v_u_2645_))
{
case 1:
{
lean_object* v_a_2652_; 
v_a_2652_ = lean_ctor_get(v_u_2645_, 0);
lean_inc(v_a_2652_);
lean_dec_ref_known(v_u_2645_, 1);
v_u_2645_ = v_a_2652_;
goto _start;
}
case 2:
{
lean_object* v_a_2654_; lean_object* v_a_2655_; 
v_a_2654_ = lean_ctor_get(v_u_2645_, 0);
lean_inc(v_a_2654_);
v_a_2655_ = lean_ctor_get(v_u_2645_, 1);
lean_inc(v_a_2655_);
lean_dec_ref_known(v_u_2645_, 2);
v_u_2648_ = v_a_2654_;
v_v_2649_ = v_a_2655_;
goto v___jp_2647_;
}
case 3:
{
lean_object* v_a_2656_; lean_object* v_a_2657_; 
v_a_2656_ = lean_ctor_get(v_u_2645_, 0);
lean_inc(v_a_2656_);
v_a_2657_ = lean_ctor_get(v_u_2645_, 1);
lean_inc(v_a_2657_);
lean_dec_ref_known(v_u_2645_, 2);
v_u_2648_ = v_a_2656_;
v_v_2649_ = v_a_2657_;
goto v___jp_2647_;
}
case 5:
{
lean_object* v_a_2658_; uint8_t v___x_2659_; 
v_a_2658_ = lean_ctor_get(v_u_2645_, 0);
lean_inc(v_a_2658_);
lean_dec_ref_known(v_u_2645_, 1);
v___x_2659_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Level_collectMVars_spec__0___redArg(v_a_2658_, v_s_2646_);
if (v___x_2659_ == 0)
{
lean_object* v___x_2660_; lean_object* v___x_2661_; 
v___x_2660_ = lean_box(0);
v___x_2661_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Level_collectMVars_spec__1___redArg(v_a_2658_, v___x_2660_, v_s_2646_);
return v___x_2661_;
}
else
{
lean_dec(v_a_2658_);
return v_s_2646_;
}
}
default: 
{
lean_dec(v_u_2645_);
return v_s_2646_;
}
}
v___jp_2647_:
{
lean_object* v___x_2650_; 
v___x_2650_ = l_Lean_Level_collectMVars(v_v_2649_, v_s_2646_);
v_u_2645_ = v_u_2648_;
v_s_2646_ = v___x_2650_;
goto _start;
}
}
}
uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Level_collectMVars_spec__0(lean_object* v_00_u03b2_2662_, lean_object* v_k_2663_, lean_object* v_t_2664_){
_start:
{
uint8_t v___x_2665_; 
v___x_2665_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Level_collectMVars_spec__0___redArg(v_k_2663_, v_t_2664_);
return v___x_2665_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Level_collectMVars_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_2663_ = stack[1].m_obj;
lean_object* v_t_2664_ = stack[2].m_obj;
uint8_t v_res_2666_;
v_res_2666_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Level_collectMVars_spec__0(lean_box(0), v_k_2663_, v_t_2664_);
stack->m_num = v_res_2666_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Level_collectMVars_spec__0___boxed(lean_object* v_00_u03b2_2667_, lean_object* v_k_2668_, lean_object* v_t_2669_){
_start:
{
uint8_t v_res_2670_; lean_object* v_r_2671_; 
v_res_2670_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Level_collectMVars_spec__0(v_00_u03b2_2667_, v_k_2668_, v_t_2669_);
lean_dec(v_t_2669_);
lean_dec(v_k_2668_);
v_r_2671_ = lean_box(v_res_2670_);
return v_r_2671_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Level_collectMVars_spec__1(lean_object* v_00_u03b2_2672_, lean_object* v_k_2673_, lean_object* v_v_2674_, lean_object* v_t_2675_, lean_object* v_hl_2676_){
_start:
{
lean_object* v___x_2677_; 
v___x_2677_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Level_collectMVars_spec__1___redArg(v_k_2673_, v_v_2674_, v_t_2675_);
return v___x_2677_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_find_x3f_visit(lean_object* v_p_2678_, lean_object* v_u_2679_){
_start:
{
lean_object* v_u_2681_; lean_object* v_v_2682_; lean_object* v___x_2685_; uint8_t v___x_2686_; 
lean_inc_ref(v_p_2678_);
lean_inc(v_u_2679_);
v___x_2685_ = lean_apply_1(v_p_2678_, v_u_2679_);
v___x_2686_ = lean_unbox(v___x_2685_);
if (v___x_2686_ == 0)
{
switch(lean_obj_tag(v_u_2679_))
{
case 1:
{
lean_object* v_a_2687_; 
v_a_2687_ = lean_ctor_get(v_u_2679_, 0);
lean_inc(v_a_2687_);
lean_dec_ref_known(v_u_2679_, 1);
v_u_2679_ = v_a_2687_;
goto _start;
}
case 2:
{
lean_object* v_a_2689_; lean_object* v_a_2690_; 
v_a_2689_ = lean_ctor_get(v_u_2679_, 0);
lean_inc(v_a_2689_);
v_a_2690_ = lean_ctor_get(v_u_2679_, 1);
lean_inc(v_a_2690_);
lean_dec_ref_known(v_u_2679_, 2);
v_u_2681_ = v_a_2689_;
v_v_2682_ = v_a_2690_;
goto v___jp_2680_;
}
case 3:
{
lean_object* v_a_2691_; lean_object* v_a_2692_; 
v_a_2691_ = lean_ctor_get(v_u_2679_, 0);
lean_inc(v_a_2691_);
v_a_2692_ = lean_ctor_get(v_u_2679_, 1);
lean_inc(v_a_2692_);
lean_dec_ref_known(v_u_2679_, 2);
v_u_2681_ = v_a_2691_;
v_v_2682_ = v_a_2692_;
goto v___jp_2680_;
}
default: 
{
lean_object* v___x_2693_; 
lean_dec(v_u_2679_);
lean_dec_ref(v_p_2678_);
v___x_2693_ = lean_box(0);
return v___x_2693_;
}
}
}
else
{
lean_object* v___x_2694_; 
lean_dec_ref(v_p_2678_);
v___x_2694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2694_, 0, v_u_2679_);
return v___x_2694_;
}
v___jp_2680_:
{
lean_object* v___x_2683_; 
lean_inc_ref(v_p_2678_);
v___x_2683_ = l___private_Lean_Level_0__Lean_Level_find_x3f_visit(v_p_2678_, v_u_2681_);
if (lean_obj_tag(v___x_2683_) == 0)
{
v_u_2679_ = v_v_2682_;
goto _start;
}
else
{
lean_dec(v_v_2682_);
lean_dec_ref(v_p_2678_);
return v___x_2683_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_find_x3f(lean_object* v_u_2695_, lean_object* v_p_2696_){
_start:
{
lean_object* v___x_2697_; 
v___x_2697_ = l___private_Lean_Level_0__Lean_Level_find_x3f_visit(v_p_2696_, v_u_2695_);
return v___x_2697_;
}
}
uint8_t l_Lean_Level_any(lean_object* v_u_2698_, lean_object* v_p_2699_){
_start:
{
lean_object* v___x_2700_; 
v___x_2700_ = l___private_Lean_Level_0__Lean_Level_find_x3f_visit(v_p_2699_, v_u_2698_);
if (lean_obj_tag(v___x_2700_) == 0)
{
uint8_t v___x_2701_; 
v___x_2701_ = 0;
return v___x_2701_;
}
else
{
uint8_t v___x_2702_; 
lean_dec_ref_known(v___x_2700_, 1);
v___x_2702_ = 1;
return v___x_2702_;
}
}
}
LEAN_EXPORT void l_Lean_Level_any_0interp(lean_interpreter_value* stack)
{
lean_object* v_u_2698_ = stack[0].m_obj;
lean_object* v_p_2699_ = stack[1].m_obj;
uint8_t v_res_2703_;
v_res_2703_ = l_Lean_Level_any(v_u_2698_, v_p_2699_);
stack->m_num = v_res_2703_;
}
LEAN_EXPORT lean_object* l_Lean_Level_any___boxed(lean_object* v_u_2704_, lean_object* v_p_2705_){
_start:
{
uint8_t v_res_2706_; lean_object* v_r_2707_; 
v_res_2706_ = l_Lean_Level_any(v_u_2704_, v_p_2705_);
v_r_2707_ = lean_box(v_res_2706_);
return v_r_2707_;
}
}
LEAN_EXPORT lean_object* l_Lean_Nat_toLevel(lean_object* v_n_2708_){
_start:
{
lean_object* v___x_2709_; 
v___x_2709_ = l_Lean_Level_ofNat(v_n_2708_);
return v___x_2709_;
}
}
LEAN_EXPORT lean_object* l_Lean_Nat_toLevel___boxed(lean_object* v_n_2710_){
_start:
{
lean_object* v_res_2711_; 
v_res_2711_ = l_Lean_Nat_toLevel(v_n_2710_);
lean_dec(v_n_2710_);
return v_res_2711_;
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
