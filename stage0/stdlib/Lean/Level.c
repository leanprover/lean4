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
static const lean_string_object l_Lean_instReprData___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = " (hasParam := "};
static const lean_object* l_Lean_instReprData___lam__0___closed__0 = (const lean_object*)&l_Lean_instReprData___lam__0___closed__0_value;
static const lean_string_object l_Lean_instReprData___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l_Lean_instReprData___lam__0___closed__1 = (const lean_object*)&l_Lean_instReprData___lam__0___closed__1_value;
static const lean_string_object l_Lean_instReprData___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_Lean_instReprData___lam__0___closed__2 = (const lean_object*)&l_Lean_instReprData___lam__0___closed__2_value;
static const lean_string_object l_Lean_instReprData___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = " (hasMVar := "};
static const lean_object* l_Lean_instReprData___lam__0___closed__3 = (const lean_object*)&l_Lean_instReprData___lam__0___closed__3_value;
static const lean_string_object l_Lean_instReprData___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Level.mkData "};
static const lean_object* l_Lean_instReprData___lam__0___closed__4 = (const lean_object*)&l_Lean_instReprData___lam__0___closed__4_value;
static const lean_string_object l_Lean_instReprData___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = " (depth := "};
static const lean_object* l_Lean_instReprData___lam__0___closed__5 = (const lean_object*)&l_Lean_instReprData___lam__0___closed__5_value;
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
static const lean_ctor_object l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprData___lam__0___closed__2_value)}};
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
LEAN_EXPORT lean_object* l_Lean_instReprData___lam__0(uint64_t v_v_67_, lean_object* v_prec_68_){
_start:
{
lean_object* v_r_70_; lean_object* v_r_74_; lean_object* v_r_83_; lean_object* v___x_91_; uint64_t v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v_r_95_; uint32_t v___x_96_; uint32_t v___x_97_; uint8_t v___x_98_; 
v___x_91_ = ((lean_object*)(l_Lean_instReprData___lam__0___closed__4));
v___x_92_ = l_Lean_Level_Data_hash(v_v_67_);
v___x_93_ = lean_uint64_to_nat(v___x_92_);
v___x_94_ = l_Nat_reprFast(v___x_93_);
v_r_95_ = lean_string_append(v___x_91_, v___x_94_);
lean_dec_ref(v___x_94_);
v___x_96_ = l_Lean_Level_Data_depth(v_v_67_);
v___x_97_ = 0;
v___x_98_ = lean_uint32_dec_eq(v___x_96_, v___x_97_);
if (v___x_98_ == 0)
{
lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v_r_105_; 
v___x_99_ = ((lean_object*)(l_Lean_instReprData___lam__0___closed__5));
v___x_100_ = lean_string_append(v_r_95_, v___x_99_);
v___x_101_ = lean_uint32_to_nat(v___x_96_);
v___x_102_ = l_Nat_reprFast(v___x_101_);
v___x_103_ = lean_string_append(v___x_100_, v___x_102_);
lean_dec_ref(v___x_102_);
v___x_104_ = ((lean_object*)(l_Lean_instReprData___lam__0___closed__2));
v_r_105_ = lean_string_append(v___x_103_, v___x_104_);
v_r_83_ = v_r_105_;
goto v___jp_82_;
}
else
{
v_r_83_ = v_r_95_;
goto v___jp_82_;
}
v___jp_69_:
{
lean_object* v___x_71_; lean_object* v___x_72_; 
v___x_71_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_71_, 0, v_r_70_);
v___x_72_ = l_Repr_addAppParen(v___x_71_, v_prec_68_);
return v___x_72_;
}
v___jp_73_:
{
uint8_t v___x_75_; 
v___x_75_ = l_Lean_Level_Data_hasParam(v_v_67_);
if (v___x_75_ == 0)
{
v_r_70_ = v_r_74_;
goto v___jp_69_;
}
else
{
lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v_r_81_; 
v___x_76_ = ((lean_object*)(l_Lean_instReprData___lam__0___closed__0));
v___x_77_ = lean_string_append(v_r_74_, v___x_76_);
v___x_78_ = ((lean_object*)(l_Lean_instReprData___lam__0___closed__1));
v___x_79_ = lean_string_append(v___x_77_, v___x_78_);
v___x_80_ = ((lean_object*)(l_Lean_instReprData___lam__0___closed__2));
v_r_81_ = lean_string_append(v___x_79_, v___x_80_);
v_r_70_ = v_r_81_;
goto v___jp_69_;
}
}
v___jp_82_:
{
uint8_t v___x_84_; 
v___x_84_ = l_Lean_Level_Data_hasMVar(v_v_67_);
if (v___x_84_ == 0)
{
v_r_74_ = v_r_83_;
goto v___jp_73_;
}
else
{
lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v_r_90_; 
v___x_85_ = ((lean_object*)(l_Lean_instReprData___lam__0___closed__3));
v___x_86_ = lean_string_append(v_r_83_, v___x_85_);
v___x_87_ = ((lean_object*)(l_Lean_instReprData___lam__0___closed__1));
v___x_88_ = lean_string_append(v___x_86_, v___x_87_);
v___x_89_ = ((lean_object*)(l_Lean_instReprData___lam__0___closed__2));
v_r_90_ = lean_string_append(v___x_88_, v___x_89_);
v_r_74_ = v_r_90_;
goto v___jp_73_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instReprData___lam__0___boxed(lean_object* v_v_106_, lean_object* v_prec_107_){
_start:
{
uint64_t v_v_boxed_108_; lean_object* v_res_109_; 
v_v_boxed_108_ = lean_unbox_uint64(v_v_106_);
lean_dec_ref(v_v_106_);
v_res_109_ = l_Lean_instReprData___lam__0(v_v_boxed_108_, v_prec_107_);
lean_dec(v_prec_107_);
return v_res_109_;
}
}
static lean_object* _init_l_Lean_instInhabitedLevelMVarId_default(void){
_start:
{
lean_object* v___x_112_; 
v___x_112_ = lean_box(0);
return v___x_112_;
}
}
static lean_object* _init_l_Lean_instInhabitedLevelMVarId(void){
_start:
{
lean_object* v___x_113_; 
v___x_113_ = lean_box(0);
return v___x_113_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqLevelMVarId_beq(lean_object* v_x_114_, lean_object* v_x_115_){
_start:
{
uint8_t v___x_116_; 
v___x_116_ = lean_name_eq(v_x_114_, v_x_115_);
return v___x_116_;
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqLevelMVarId_beq___boxed(lean_object* v_x_117_, lean_object* v_x_118_){
_start:
{
uint8_t v_res_119_; lean_object* v_r_120_; 
v_res_119_ = l_Lean_instBEqLevelMVarId_beq(v_x_117_, v_x_118_);
lean_dec(v_x_118_);
lean_dec(v_x_117_);
v_r_120_ = lean_box(v_res_119_);
return v_r_120_;
}
}
LEAN_EXPORT uint64_t l_Lean_instHashableLevelMVarId_hash(lean_object* v_x_123_){
_start:
{
uint64_t v___x_124_; 
v___x_124_ = 0ULL;
if (lean_obj_tag(v_x_123_) == 0)
{
uint64_t v___x_125_; 
v___x_125_ = 8934034000889494153ULL;
return v___x_125_;
}
else
{
uint64_t v_hash_126_; uint64_t v___x_127_; 
v_hash_126_ = lean_ctor_get_uint64(v_x_123_, sizeof(void*)*2);
v___x_127_ = lean_uint64_mix_hash(v___x_124_, v_hash_126_);
return v___x_127_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instHashableLevelMVarId_hash___boxed(lean_object* v_x_128_){
_start:
{
uint64_t v_res_129_; lean_object* v_r_130_; 
v_res_129_ = l_Lean_instHashableLevelMVarId_hash(v_x_128_);
lean_dec(v_x_128_);
v_r_130_ = lean_box_uint64(v_res_129_);
return v_r_130_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_instReprLevelMVarId_repr_spec__0(lean_object* v_a_133_){
_start:
{
lean_object* v___x_134_; 
v___x_134_ = lean_nat_to_int(v_a_133_);
return v___x_134_;
}
}
static lean_object* _init_l_Lean_instReprLevelMVarId_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_148_; lean_object* v___x_149_; 
v___x_148_ = lean_unsigned_to_nat(8u);
v___x_149_ = lean_nat_to_int(v___x_148_);
return v___x_149_;
}
}
static lean_object* _init_l_Lean_instReprLevelMVarId_repr___redArg___closed__9(void){
_start:
{
lean_object* v___x_151_; lean_object* v___x_152_; 
v___x_151_ = ((lean_object*)(l_Lean_instReprLevelMVarId_repr___redArg___closed__0));
v___x_152_ = lean_string_length(v___x_151_);
return v___x_152_;
}
}
static lean_object* _init_l_Lean_instReprLevelMVarId_repr___redArg___closed__10(void){
_start:
{
lean_object* v___x_153_; lean_object* v___x_154_; 
v___x_153_ = lean_obj_once(&l_Lean_instReprLevelMVarId_repr___redArg___closed__9, &l_Lean_instReprLevelMVarId_repr___redArg___closed__9_once, _init_l_Lean_instReprLevelMVarId_repr___redArg___closed__9);
v___x_154_ = lean_nat_to_int(v___x_153_);
return v___x_154_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprLevelMVarId_repr___redArg(lean_object* v_x_159_){
_start:
{
lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; uint8_t v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; 
v___x_160_ = ((lean_object*)(l_Lean_instReprLevelMVarId_repr___redArg___closed__6));
v___x_161_ = lean_obj_once(&l_Lean_instReprLevelMVarId_repr___redArg___closed__7, &l_Lean_instReprLevelMVarId_repr___redArg___closed__7_once, _init_l_Lean_instReprLevelMVarId_repr___redArg___closed__7);
v___x_162_ = lean_unsigned_to_nat(0u);
v___x_163_ = l_Lean_Name_reprPrec(v_x_159_, v___x_162_);
v___x_164_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_164_, 0, v___x_161_);
lean_ctor_set(v___x_164_, 1, v___x_163_);
v___x_165_ = 0;
v___x_166_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_166_, 0, v___x_164_);
lean_ctor_set_uint8(v___x_166_, sizeof(void*)*1, v___x_165_);
v___x_167_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_167_, 0, v___x_160_);
lean_ctor_set(v___x_167_, 1, v___x_166_);
v___x_168_ = lean_obj_once(&l_Lean_instReprLevelMVarId_repr___redArg___closed__10, &l_Lean_instReprLevelMVarId_repr___redArg___closed__10_once, _init_l_Lean_instReprLevelMVarId_repr___redArg___closed__10);
v___x_169_ = ((lean_object*)(l_Lean_instReprLevelMVarId_repr___redArg___closed__11));
v___x_170_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_170_, 0, v___x_169_);
lean_ctor_set(v___x_170_, 1, v___x_167_);
v___x_171_ = ((lean_object*)(l_Lean_instReprLevelMVarId_repr___redArg___closed__12));
v___x_172_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_172_, 0, v___x_170_);
lean_ctor_set(v___x_172_, 1, v___x_171_);
v___x_173_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_173_, 0, v___x_168_);
lean_ctor_set(v___x_173_, 1, v___x_172_);
v___x_174_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_174_, 0, v___x_173_);
lean_ctor_set_uint8(v___x_174_, sizeof(void*)*1, v___x_165_);
return v___x_174_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprLevelMVarId_repr(lean_object* v_x_175_, lean_object* v_prec_176_){
_start:
{
lean_object* v___x_177_; 
v___x_177_ = l_Lean_instReprLevelMVarId_repr___redArg(v_x_175_);
return v___x_177_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprLevelMVarId_repr___boxed(lean_object* v_x_178_, lean_object* v_prec_179_){
_start:
{
lean_object* v_res_180_; 
v_res_180_ = l_Lean_instReprLevelMVarId_repr(v_x_178_, v_prec_179_);
lean_dec(v_prec_179_);
return v_res_180_;
}
}
static lean_object* _init_l_Lean_instInhabitedLMVarIdSet___aux__1(void){
_start:
{
lean_object* v___x_185_; 
v___x_185_ = lean_box(1);
return v___x_185_;
}
}
static lean_object* _init_l_Lean_instInhabitedLMVarIdSet(void){
_start:
{
lean_object* v___x_186_; 
v___x_186_ = lean_box(1);
return v___x_186_;
}
}
static lean_object* _init_l_Lean_instEmptyCollectionLMVarIdSet___aux__1(void){
_start:
{
lean_object* v___x_187_; 
v___x_187_ = lean_box(1);
return v___x_187_;
}
}
static lean_object* _init_l_Lean_instEmptyCollectionLMVarIdSet(void){
_start:
{
lean_object* v___x_188_; 
v___x_188_ = lean_box(1);
return v___x_188_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInLMVarIdSetLMVarIdOfMonad___aux__1___redArg___lam__0(lean_object* v_f_189_, lean_object* v_a_190_, lean_object* v_b_191_, lean_object* v_c_192_){
_start:
{
lean_object* v___x_193_; 
v___x_193_ = lean_apply_2(v_f_189_, v_a_190_, v_c_192_);
return v___x_193_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInLMVarIdSetLMVarIdOfMonad___aux__1___redArg___lam__1(lean_object* v_toPure_194_, lean_object* v_____do__lift_195_){
_start:
{
lean_object* v_a_196_; lean_object* v___x_197_; 
v_a_196_ = lean_ctor_get(v_____do__lift_195_, 0);
lean_inc(v_a_196_);
lean_dec_ref(v_____do__lift_195_);
v___x_197_ = lean_apply_2(v_toPure_194_, lean_box(0), v_a_196_);
return v___x_197_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInLMVarIdSetLMVarIdOfMonad___aux__1___redArg(lean_object* v_inst_198_, lean_object* v_m_199_, lean_object* v_init_200_, lean_object* v_f_201_){
_start:
{
lean_object* v_toApplicative_202_; lean_object* v_toBind_203_; lean_object* v_toPure_204_; lean_object* v___f_205_; lean_object* v___x_206_; lean_object* v___f_207_; lean_object* v___x_208_; 
v_toApplicative_202_ = lean_ctor_get(v_inst_198_, 0);
v_toBind_203_ = lean_ctor_get(v_inst_198_, 1);
lean_inc(v_toBind_203_);
v_toPure_204_ = lean_ctor_get(v_toApplicative_202_, 1);
lean_inc(v_toPure_204_);
v___f_205_ = lean_alloc_closure((void*)(l_Lean_instForInLMVarIdSetLMVarIdOfMonad___aux__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_205_, 0, v_f_201_);
v___x_206_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_198_, v___f_205_, v_init_200_, v_m_199_);
v___f_207_ = lean_alloc_closure((void*)(l_Lean_instForInLMVarIdSetLMVarIdOfMonad___aux__1___redArg___lam__1), 2, 1);
lean_closure_set(v___f_207_, 0, v_toPure_204_);
v___x_208_ = lean_apply_4(v_toBind_203_, lean_box(0), lean_box(0), v___x_206_, v___f_207_);
return v___x_208_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInLMVarIdSetLMVarIdOfMonad___aux__1(lean_object* v_m_209_, lean_object* v_inst_210_, lean_object* v_00_u03b2_211_, lean_object* v_m_212_, lean_object* v_init_213_, lean_object* v_f_214_){
_start:
{
lean_object* v_toApplicative_215_; lean_object* v_toBind_216_; lean_object* v_toPure_217_; lean_object* v___f_218_; lean_object* v___x_219_; lean_object* v___f_220_; lean_object* v___x_221_; 
v_toApplicative_215_ = lean_ctor_get(v_inst_210_, 0);
v_toBind_216_ = lean_ctor_get(v_inst_210_, 1);
lean_inc(v_toBind_216_);
v_toPure_217_ = lean_ctor_get(v_toApplicative_215_, 1);
lean_inc(v_toPure_217_);
v___f_218_ = lean_alloc_closure((void*)(l_Lean_instForInLMVarIdSetLMVarIdOfMonad___aux__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_218_, 0, v_f_214_);
v___x_219_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_210_, v___f_218_, v_init_213_, v_m_212_);
v___f_220_ = lean_alloc_closure((void*)(l_Lean_instForInLMVarIdSetLMVarIdOfMonad___aux__1___redArg___lam__1), 2, 1);
lean_closure_set(v___f_220_, 0, v_toPure_217_);
v___x_221_ = lean_apply_4(v_toBind_216_, lean_box(0), lean_box(0), v___x_219_, v___f_220_);
return v___x_221_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInLMVarIdSetLMVarIdOfMonad___redArg(lean_object* v_inst_222_){
_start:
{
lean_object* v___x_223_; 
v___x_223_ = lean_alloc_closure((void*)(l_Lean_instForInLMVarIdSetLMVarIdOfMonad___aux__1), 6, 2);
lean_closure_set(v___x_223_, 0, lean_box(0));
lean_closure_set(v___x_223_, 1, v_inst_222_);
return v___x_223_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInLMVarIdSetLMVarIdOfMonad(lean_object* v_m_224_, lean_object* v_inst_225_){
_start:
{
lean_object* v___x_226_; 
v___x_226_ = lean_alloc_closure((void*)(l_Lean_instForInLMVarIdSetLMVarIdOfMonad___aux__1), 6, 2);
lean_closure_set(v___x_226_, 0, lean_box(0));
lean_closure_set(v___x_226_, 1, v_inst_225_);
return v___x_226_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionLMVarIdMap___aux__1___redArg(){
_start:
{
lean_object* v___x_228_; 
v___x_228_ = lean_box(1);
return v___x_228_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionLMVarIdMap___aux__1___redArg___boxed(lean_object* v___dummy_229_){
_start:
{
lean_object* v_res_230_; 
v_res_230_ = l_Lean_instEmptyCollectionLMVarIdMap___aux__1___redArg();
return v_res_230_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionLMVarIdMap___aux__1(lean_object* v_00_u03b1_231_){
_start:
{
lean_object* v___x_232_; 
v___x_232_ = lean_box(1);
return v___x_232_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionLMVarIdMap___redArg(){
_start:
{
lean_object* v___x_234_; 
v___x_234_ = lean_box(1);
return v___x_234_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionLMVarIdMap___redArg___boxed(lean_object* v___dummy_235_){
_start:
{
lean_object* v_res_236_; 
v_res_236_ = l_Lean_instEmptyCollectionLMVarIdMap___redArg();
return v_res_236_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionLMVarIdMap(lean_object* v_00_u03b1_237_){
_start:
{
lean_object* v___x_238_; 
v___x_238_ = lean_box(1);
return v___x_238_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInLMVarIdMapProdLMVarIdOfMonad___aux__1___redArg___lam__0(lean_object* v_f_239_, lean_object* v_a_240_, lean_object* v_b_241_, lean_object* v_c_242_){
_start:
{
lean_object* v___x_243_; lean_object* v___x_244_; 
v___x_243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_243_, 0, v_a_240_);
lean_ctor_set(v___x_243_, 1, v_b_241_);
v___x_244_ = lean_apply_2(v_f_239_, v___x_243_, v_c_242_);
return v___x_244_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInLMVarIdMapProdLMVarIdOfMonad___aux__1___redArg(lean_object* v_inst_245_, lean_object* v_m_246_, lean_object* v_init_247_, lean_object* v_f_248_){
_start:
{
lean_object* v_toApplicative_249_; lean_object* v_toBind_250_; lean_object* v_toPure_251_; lean_object* v___f_252_; lean_object* v___x_253_; lean_object* v___f_254_; lean_object* v___x_255_; 
v_toApplicative_249_ = lean_ctor_get(v_inst_245_, 0);
v_toBind_250_ = lean_ctor_get(v_inst_245_, 1);
lean_inc(v_toBind_250_);
v_toPure_251_ = lean_ctor_get(v_toApplicative_249_, 1);
lean_inc(v_toPure_251_);
v___f_252_ = lean_alloc_closure((void*)(l_Lean_instForInLMVarIdMapProdLMVarIdOfMonad___aux__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_252_, 0, v_f_248_);
v___x_253_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_245_, v___f_252_, v_init_247_, v_m_246_);
v___f_254_ = lean_alloc_closure((void*)(l_Lean_instForInLMVarIdSetLMVarIdOfMonad___aux__1___redArg___lam__1), 2, 1);
lean_closure_set(v___f_254_, 0, v_toPure_251_);
v___x_255_ = lean_apply_4(v_toBind_250_, lean_box(0), lean_box(0), v___x_253_, v___f_254_);
return v___x_255_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInLMVarIdMapProdLMVarIdOfMonad___aux__1(lean_object* v_m_256_, lean_object* v_00_u03b1_257_, lean_object* v_inst_258_, lean_object* v_00_u03b2_259_, lean_object* v_m_260_, lean_object* v_init_261_, lean_object* v_f_262_){
_start:
{
lean_object* v_toApplicative_263_; lean_object* v_toBind_264_; lean_object* v_toPure_265_; lean_object* v___f_266_; lean_object* v___x_267_; lean_object* v___f_268_; lean_object* v___x_269_; 
v_toApplicative_263_ = lean_ctor_get(v_inst_258_, 0);
v_toBind_264_ = lean_ctor_get(v_inst_258_, 1);
lean_inc(v_toBind_264_);
v_toPure_265_ = lean_ctor_get(v_toApplicative_263_, 1);
lean_inc(v_toPure_265_);
v___f_266_ = lean_alloc_closure((void*)(l_Lean_instForInLMVarIdMapProdLMVarIdOfMonad___aux__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_266_, 0, v_f_262_);
v___x_267_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_258_, v___f_266_, v_init_261_, v_m_260_);
v___f_268_ = lean_alloc_closure((void*)(l_Lean_instForInLMVarIdSetLMVarIdOfMonad___aux__1___redArg___lam__1), 2, 1);
lean_closure_set(v___f_268_, 0, v_toPure_265_);
v___x_269_ = lean_apply_4(v_toBind_264_, lean_box(0), lean_box(0), v___x_267_, v___f_268_);
return v___x_269_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInLMVarIdMapProdLMVarIdOfMonad___redArg(lean_object* v_inst_270_){
_start:
{
lean_object* v___x_271_; 
v___x_271_ = lean_alloc_closure((void*)(l_Lean_instForInLMVarIdMapProdLMVarIdOfMonad___aux__1), 7, 3);
lean_closure_set(v___x_271_, 0, lean_box(0));
lean_closure_set(v___x_271_, 1, lean_box(0));
lean_closure_set(v___x_271_, 2, v_inst_270_);
return v___x_271_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInLMVarIdMapProdLMVarIdOfMonad(lean_object* v_m_272_, lean_object* v_00_u03b1_273_, lean_object* v_inst_274_){
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
LEAN_EXPORT lean_object* l_Lean_instInhabitedLMVarIdMap___redArg(){
_start:
{
lean_object* v___x_277_; 
v___x_277_ = lean_box(1);
return v___x_277_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedLMVarIdMap___redArg___boxed(lean_object* v___dummy_278_){
_start:
{
lean_object* v_res_279_; 
v_res_279_ = l_Lean_instInhabitedLMVarIdMap___redArg();
return v_res_279_;
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
LEAN_EXPORT lean_object* l_Lean_Level_ctorIdx___impl(lean_object* v_x_282_){
_start:
{
lean_object* v___x_283_; 
v___x_283_ = lean_obj_tag_nat(v_x_282_);
return v___x_283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_ctorIdx___impl___boxed(lean_object* v_x_284_){
_start:
{
lean_object* v_res_285_; 
v_res_285_ = l_Lean_Level_ctorIdx___impl(v_x_284_);
lean_dec(v_x_284_);
return v_res_285_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_ctorElim___redArg(lean_object* v_t_286_, lean_object* v_k_287_){
_start:
{
switch(lean_obj_tag(v_t_286_))
{
case 0:
{
return v_k_287_;
}
case 2:
{
lean_object* v_a_288_; lean_object* v_a_289_; lean_object* v___x_290_; 
v_a_288_ = lean_ctor_get(v_t_286_, 0);
lean_inc(v_a_288_);
v_a_289_ = lean_ctor_get(v_t_286_, 1);
lean_inc(v_a_289_);
lean_dec_ref_known(v_t_286_, 2);
v___x_290_ = lean_apply_2(v_k_287_, v_a_288_, v_a_289_);
return v___x_290_;
}
case 3:
{
lean_object* v_a_291_; lean_object* v_a_292_; lean_object* v___x_293_; 
v_a_291_ = lean_ctor_get(v_t_286_, 0);
lean_inc(v_a_291_);
v_a_292_ = lean_ctor_get(v_t_286_, 1);
lean_inc(v_a_292_);
lean_dec_ref_known(v_t_286_, 2);
v___x_293_ = lean_apply_2(v_k_287_, v_a_291_, v_a_292_);
return v___x_293_;
}
default: 
{
lean_object* v_a_294_; lean_object* v___x_295_; 
v_a_294_ = lean_ctor_get(v_t_286_, 0);
lean_inc(v_a_294_);
lean_dec(v_t_286_);
v___x_295_ = lean_apply_1(v_k_287_, v_a_294_);
return v___x_295_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_ctorElim(lean_object* v_motive_296_, lean_object* v_ctorIdx_297_, lean_object* v_t_298_, lean_object* v_h_299_, lean_object* v_k_300_){
_start:
{
lean_object* v___x_301_; 
v___x_301_ = l_Lean_Level_ctorElim___redArg(v_t_298_, v_k_300_);
return v___x_301_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_ctorElim___boxed(lean_object* v_motive_302_, lean_object* v_ctorIdx_303_, lean_object* v_t_304_, lean_object* v_h_305_, lean_object* v_k_306_){
_start:
{
lean_object* v_res_307_; 
v_res_307_ = l_Lean_Level_ctorElim(v_motive_302_, v_ctorIdx_303_, v_t_304_, v_h_305_, v_k_306_);
lean_dec(v_ctorIdx_303_);
return v_res_307_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_zero_elim___redArg(lean_object* v_t_308_, lean_object* v_zero_309_){
_start:
{
lean_object* v___x_310_; 
v___x_310_ = l_Lean_Level_ctorElim___redArg(v_t_308_, v_zero_309_);
return v___x_310_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_zero_elim(lean_object* v_motive_311_, lean_object* v_t_312_, lean_object* v_h_313_, lean_object* v_zero_314_){
_start:
{
lean_object* v___x_315_; 
v___x_315_ = l_Lean_Level_ctorElim___redArg(v_t_312_, v_zero_314_);
return v___x_315_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_succ_elim___redArg(lean_object* v_t_316_, lean_object* v_succ_317_){
_start:
{
lean_object* v___x_318_; 
v___x_318_ = l_Lean_Level_ctorElim___redArg(v_t_316_, v_succ_317_);
return v___x_318_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_succ_elim(lean_object* v_motive_319_, lean_object* v_t_320_, lean_object* v_h_321_, lean_object* v_succ_322_){
_start:
{
lean_object* v___x_323_; 
v___x_323_ = l_Lean_Level_ctorElim___redArg(v_t_320_, v_succ_322_);
return v___x_323_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_max_elim___redArg(lean_object* v_t_324_, lean_object* v_max_325_){
_start:
{
lean_object* v___x_326_; 
v___x_326_ = l_Lean_Level_ctorElim___redArg(v_t_324_, v_max_325_);
return v___x_326_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_max_elim(lean_object* v_motive_327_, lean_object* v_t_328_, lean_object* v_h_329_, lean_object* v_max_330_){
_start:
{
lean_object* v___x_331_; 
v___x_331_ = l_Lean_Level_ctorElim___redArg(v_t_328_, v_max_330_);
return v___x_331_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_imax_elim___redArg(lean_object* v_t_332_, lean_object* v_imax_333_){
_start:
{
lean_object* v___x_334_; 
v___x_334_ = l_Lean_Level_ctorElim___redArg(v_t_332_, v_imax_333_);
return v___x_334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_imax_elim(lean_object* v_motive_335_, lean_object* v_t_336_, lean_object* v_h_337_, lean_object* v_imax_338_){
_start:
{
lean_object* v___x_339_; 
v___x_339_ = l_Lean_Level_ctorElim___redArg(v_t_336_, v_imax_338_);
return v___x_339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_param_elim___redArg(lean_object* v_t_340_, lean_object* v_param_341_){
_start:
{
lean_object* v___x_342_; 
v___x_342_ = l_Lean_Level_ctorElim___redArg(v_t_340_, v_param_341_);
return v___x_342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_param_elim(lean_object* v_motive_343_, lean_object* v_t_344_, lean_object* v_h_345_, lean_object* v_param_346_){
_start:
{
lean_object* v___x_347_; 
v___x_347_ = l_Lean_Level_ctorElim___redArg(v_t_344_, v_param_346_);
return v___x_347_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_mvar_elim___redArg(lean_object* v_t_348_, lean_object* v_mvar_349_){
_start:
{
lean_object* v___x_350_; 
v___x_350_ = l_Lean_Level_ctorElim___redArg(v_t_348_, v_mvar_349_);
return v___x_350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_mvar_elim(lean_object* v_motive_351_, lean_object* v_t_352_, lean_object* v_h_353_, lean_object* v_mvar_354_){
_start:
{
lean_object* v___x_355_; 
v___x_355_ = l_Lean_Level_ctorElim___redArg(v_t_352_, v_mvar_354_);
return v___x_355_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_casesOn___override___redArg(lean_object* v_t_356_, lean_object* v_zero_357_, lean_object* v_succ_358_, lean_object* v_max_359_, lean_object* v_imax_360_, lean_object* v_param_361_, lean_object* v_mvar_362_){
_start:
{
switch(lean_obj_tag(v_t_356_))
{
case 0:
{
lean_dec(v_mvar_362_);
lean_dec(v_param_361_);
lean_dec(v_imax_360_);
lean_dec(v_max_359_);
lean_dec(v_succ_358_);
lean_inc(v_zero_357_);
return v_zero_357_;
}
case 1:
{
lean_object* v_a_363_; lean_object* v___x_364_; 
lean_dec(v_mvar_362_);
lean_dec(v_param_361_);
lean_dec(v_imax_360_);
lean_dec(v_max_359_);
v_a_363_ = lean_ctor_get(v_t_356_, 0);
lean_inc(v_a_363_);
lean_dec_ref_known(v_t_356_, 1);
v___x_364_ = lean_apply_1(v_succ_358_, v_a_363_);
return v___x_364_;
}
case 2:
{
lean_object* v_a_365_; lean_object* v_a_366_; lean_object* v___x_367_; 
lean_dec(v_mvar_362_);
lean_dec(v_param_361_);
lean_dec(v_imax_360_);
lean_dec(v_succ_358_);
v_a_365_ = lean_ctor_get(v_t_356_, 0);
lean_inc(v_a_365_);
v_a_366_ = lean_ctor_get(v_t_356_, 1);
lean_inc(v_a_366_);
lean_dec_ref_known(v_t_356_, 2);
v___x_367_ = lean_apply_2(v_max_359_, v_a_365_, v_a_366_);
return v___x_367_;
}
case 3:
{
lean_object* v_a_368_; lean_object* v_a_369_; lean_object* v___x_370_; 
lean_dec(v_mvar_362_);
lean_dec(v_param_361_);
lean_dec(v_max_359_);
lean_dec(v_succ_358_);
v_a_368_ = lean_ctor_get(v_t_356_, 0);
lean_inc(v_a_368_);
v_a_369_ = lean_ctor_get(v_t_356_, 1);
lean_inc(v_a_369_);
lean_dec_ref_known(v_t_356_, 2);
v___x_370_ = lean_apply_2(v_imax_360_, v_a_368_, v_a_369_);
return v___x_370_;
}
case 4:
{
lean_object* v_a_371_; lean_object* v___x_372_; 
lean_dec(v_mvar_362_);
lean_dec(v_imax_360_);
lean_dec(v_max_359_);
lean_dec(v_succ_358_);
v_a_371_ = lean_ctor_get(v_t_356_, 0);
lean_inc(v_a_371_);
lean_dec_ref_known(v_t_356_, 1);
v___x_372_ = lean_apply_1(v_param_361_, v_a_371_);
return v___x_372_;
}
default: 
{
lean_object* v_a_373_; lean_object* v___x_374_; 
lean_dec(v_param_361_);
lean_dec(v_imax_360_);
lean_dec(v_max_359_);
lean_dec(v_succ_358_);
v_a_373_ = lean_ctor_get(v_t_356_, 0);
lean_inc(v_a_373_);
lean_dec_ref_known(v_t_356_, 1);
v___x_374_ = lean_apply_1(v_mvar_362_, v_a_373_);
return v___x_374_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_casesOn___override___redArg___boxed(lean_object* v_t_375_, lean_object* v_zero_376_, lean_object* v_succ_377_, lean_object* v_max_378_, lean_object* v_imax_379_, lean_object* v_param_380_, lean_object* v_mvar_381_){
_start:
{
lean_object* v_res_382_; 
v_res_382_ = l_Lean_Level_casesOn___override___redArg(v_t_375_, v_zero_376_, v_succ_377_, v_max_378_, v_imax_379_, v_param_380_, v_mvar_381_);
lean_dec(v_zero_376_);
return v_res_382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_casesOn___override(lean_object* v_motive_383_, lean_object* v_t_384_, lean_object* v_zero_385_, lean_object* v_succ_386_, lean_object* v_max_387_, lean_object* v_imax_388_, lean_object* v_param_389_, lean_object* v_mvar_390_){
_start:
{
switch(lean_obj_tag(v_t_384_))
{
case 0:
{
lean_dec(v_mvar_390_);
lean_dec(v_param_389_);
lean_dec(v_imax_388_);
lean_dec(v_max_387_);
lean_dec(v_succ_386_);
lean_inc(v_zero_385_);
return v_zero_385_;
}
case 1:
{
lean_object* v_a_391_; lean_object* v___x_392_; 
lean_dec(v_mvar_390_);
lean_dec(v_param_389_);
lean_dec(v_imax_388_);
lean_dec(v_max_387_);
v_a_391_ = lean_ctor_get(v_t_384_, 0);
lean_inc(v_a_391_);
lean_dec_ref_known(v_t_384_, 1);
v___x_392_ = lean_apply_1(v_succ_386_, v_a_391_);
return v___x_392_;
}
case 2:
{
lean_object* v_a_393_; lean_object* v_a_394_; lean_object* v___x_395_; 
lean_dec(v_mvar_390_);
lean_dec(v_param_389_);
lean_dec(v_imax_388_);
lean_dec(v_succ_386_);
v_a_393_ = lean_ctor_get(v_t_384_, 0);
lean_inc(v_a_393_);
v_a_394_ = lean_ctor_get(v_t_384_, 1);
lean_inc(v_a_394_);
lean_dec_ref_known(v_t_384_, 2);
v___x_395_ = lean_apply_2(v_max_387_, v_a_393_, v_a_394_);
return v___x_395_;
}
case 3:
{
lean_object* v_a_396_; lean_object* v_a_397_; lean_object* v___x_398_; 
lean_dec(v_mvar_390_);
lean_dec(v_param_389_);
lean_dec(v_max_387_);
lean_dec(v_succ_386_);
v_a_396_ = lean_ctor_get(v_t_384_, 0);
lean_inc(v_a_396_);
v_a_397_ = lean_ctor_get(v_t_384_, 1);
lean_inc(v_a_397_);
lean_dec_ref_known(v_t_384_, 2);
v___x_398_ = lean_apply_2(v_imax_388_, v_a_396_, v_a_397_);
return v___x_398_;
}
case 4:
{
lean_object* v_a_399_; lean_object* v___x_400_; 
lean_dec(v_mvar_390_);
lean_dec(v_imax_388_);
lean_dec(v_max_387_);
lean_dec(v_succ_386_);
v_a_399_ = lean_ctor_get(v_t_384_, 0);
lean_inc(v_a_399_);
lean_dec_ref_known(v_t_384_, 1);
v___x_400_ = lean_apply_1(v_param_389_, v_a_399_);
return v___x_400_;
}
default: 
{
lean_object* v_a_401_; lean_object* v___x_402_; 
lean_dec(v_param_389_);
lean_dec(v_imax_388_);
lean_dec(v_max_387_);
lean_dec(v_succ_386_);
v_a_401_ = lean_ctor_get(v_t_384_, 0);
lean_inc(v_a_401_);
lean_dec_ref_known(v_t_384_, 1);
v___x_402_ = lean_apply_1(v_mvar_390_, v_a_401_);
return v___x_402_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_casesOn___override___boxed(lean_object* v_motive_403_, lean_object* v_t_404_, lean_object* v_zero_405_, lean_object* v_succ_406_, lean_object* v_max_407_, lean_object* v_imax_408_, lean_object* v_param_409_, lean_object* v_mvar_410_){
_start:
{
lean_object* v_res_411_; 
v_res_411_ = l_Lean_Level_casesOn___override(v_motive_403_, v_t_404_, v_zero_405_, v_succ_406_, v_max_407_, v_imax_408_, v_param_409_, v_mvar_410_);
lean_dec(v_zero_405_);
return v_res_411_;
}
}
static lean_object* _init_l_Lean_Level_zero___override(void){
_start:
{
lean_object* v___x_412_; 
v___x_412_ = lean_box(0);
return v___x_412_;
}
}
static uint64_t _init_l_Lean_Level_data___override___closed__0(void){
_start:
{
uint8_t v___x_413_; lean_object* v___x_414_; uint64_t v___x_415_; uint64_t v___x_416_; 
v___x_413_ = 0;
v___x_414_ = lean_unsigned_to_nat(0u);
v___x_415_ = 2221ULL;
v___x_416_ = lean_level_mk_data(v___x_415_, v___x_414_, v___x_413_, v___x_413_);
return v___x_416_;
}
}
LEAN_EXPORT uint64_t l_Lean_Level_data___override(lean_object* v_x_417_){
_start:
{
switch(lean_obj_tag(v_x_417_))
{
case 0:
{
uint64_t v___x_418_; 
v___x_418_ = lean_uint64_once(&l_Lean_Level_data___override___closed__0, &l_Lean_Level_data___override___closed__0_once, _init_l_Lean_Level_data___override___closed__0);
return v___x_418_;
}
case 2:
{
uint64_t v_data_419_; 
v_data_419_ = lean_ctor_get_uint64(v_x_417_, sizeof(void*)*2);
return v_data_419_;
}
case 3:
{
uint64_t v_data_420_; 
v_data_420_ = lean_ctor_get_uint64(v_x_417_, sizeof(void*)*2);
return v_data_420_;
}
default: 
{
uint64_t v_data_421_; 
v_data_421_ = lean_ctor_get_uint64(v_x_417_, sizeof(void*)*1);
return v_data_421_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_data___override___boxed(lean_object* v_x_422_){
_start:
{
uint64_t v_res_423_; lean_object* v_r_424_; 
v_res_423_ = l_Lean_Level_data___override(v_x_422_);
lean_dec(v_x_422_);
v_r_424_ = lean_box_uint64(v_res_423_);
return v_r_424_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_succ___override(lean_object* v_a_425_){
_start:
{
uint64_t v___x_426_; uint64_t v___x_427_; uint64_t v___x_428_; uint64_t v___x_429_; uint32_t v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; uint8_t v___x_434_; uint8_t v___x_435_; uint64_t v___x_436_; lean_object* v___x_437_; 
v___x_426_ = 2243ULL;
v___x_427_ = l_Lean_Level_data___override(v_a_425_);
v___x_428_ = l_Lean_Level_Data_hash(v___x_427_);
v___x_429_ = lean_uint64_mix_hash(v___x_426_, v___x_428_);
v___x_430_ = l_Lean_Level_Data_depth(v___x_427_);
v___x_431_ = lean_uint32_to_nat(v___x_430_);
v___x_432_ = lean_unsigned_to_nat(1u);
v___x_433_ = lean_nat_add(v___x_431_, v___x_432_);
lean_dec(v___x_431_);
v___x_434_ = l_Lean_Level_Data_hasMVar(v___x_427_);
v___x_435_ = l_Lean_Level_Data_hasParam(v___x_427_);
v___x_436_ = lean_level_mk_data(v___x_429_, v___x_433_, v___x_434_, v___x_435_);
v___x_437_ = lean_alloc_ctor(1, 1, 8);
lean_ctor_set(v___x_437_, 0, v_a_425_);
lean_ctor_set_uint64(v___x_437_, sizeof(void*)*1, v___x_436_);
return v___x_437_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_max___override(lean_object* v_a_438_, lean_object* v_a_439_){
_start:
{
uint64_t v___x_440_; uint64_t v___x_441_; uint64_t v___x_442_; uint64_t v___x_443_; uint64_t v___x_444_; uint64_t v___x_445_; uint64_t v___x_446_; uint8_t v___y_448_; lean_object* v___y_449_; uint8_t v___y_450_; lean_object* v___y_454_; uint8_t v___y_455_; lean_object* v___y_459_; uint32_t v___x_464_; lean_object* v___x_465_; uint32_t v___x_466_; lean_object* v___x_467_; uint8_t v___x_468_; 
v___x_440_ = 2251ULL;
v___x_441_ = l_Lean_Level_data___override(v_a_438_);
v___x_442_ = l_Lean_Level_Data_hash(v___x_441_);
v___x_443_ = l_Lean_Level_data___override(v_a_439_);
v___x_444_ = l_Lean_Level_Data_hash(v___x_443_);
v___x_445_ = lean_uint64_mix_hash(v___x_442_, v___x_444_);
v___x_446_ = lean_uint64_mix_hash(v___x_440_, v___x_445_);
v___x_464_ = l_Lean_Level_Data_depth(v___x_441_);
v___x_465_ = lean_uint32_to_nat(v___x_464_);
v___x_466_ = l_Lean_Level_Data_depth(v___x_443_);
v___x_467_ = lean_uint32_to_nat(v___x_466_);
v___x_468_ = lean_nat_dec_le(v___x_465_, v___x_467_);
if (v___x_468_ == 0)
{
lean_dec(v___x_467_);
v___y_459_ = v___x_465_;
goto v___jp_458_;
}
else
{
lean_dec(v___x_465_);
v___y_459_ = v___x_467_;
goto v___jp_458_;
}
v___jp_447_:
{
uint64_t v___x_451_; lean_object* v___x_452_; 
v___x_451_ = lean_level_mk_data(v___x_446_, v___y_449_, v___y_448_, v___y_450_);
v___x_452_ = lean_alloc_ctor(2, 2, 8);
lean_ctor_set(v___x_452_, 0, v_a_438_);
lean_ctor_set(v___x_452_, 1, v_a_439_);
lean_ctor_set_uint64(v___x_452_, sizeof(void*)*2, v___x_451_);
return v___x_452_;
}
v___jp_453_:
{
uint8_t v___x_456_; 
v___x_456_ = l_Lean_Level_Data_hasParam(v___x_441_);
if (v___x_456_ == 0)
{
uint8_t v___x_457_; 
v___x_457_ = l_Lean_Level_Data_hasParam(v___x_443_);
v___y_448_ = v___y_455_;
v___y_449_ = v___y_454_;
v___y_450_ = v___x_457_;
goto v___jp_447_;
}
else
{
v___y_448_ = v___y_455_;
v___y_449_ = v___y_454_;
v___y_450_ = v___x_456_;
goto v___jp_447_;
}
}
v___jp_458_:
{
lean_object* v___x_460_; lean_object* v___x_461_; uint8_t v___x_462_; 
v___x_460_ = lean_unsigned_to_nat(1u);
v___x_461_ = lean_nat_add(v___y_459_, v___x_460_);
lean_dec(v___y_459_);
v___x_462_ = l_Lean_Level_Data_hasMVar(v___x_441_);
if (v___x_462_ == 0)
{
uint8_t v___x_463_; 
v___x_463_ = l_Lean_Level_Data_hasMVar(v___x_443_);
v___y_454_ = v___x_461_;
v___y_455_ = v___x_463_;
goto v___jp_453_;
}
else
{
v___y_454_ = v___x_461_;
v___y_455_ = v___x_462_;
goto v___jp_453_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_imax___override(lean_object* v_a_469_, lean_object* v_a_470_){
_start:
{
uint64_t v___x_471_; uint64_t v___x_472_; uint64_t v___x_473_; uint64_t v___x_474_; uint64_t v___x_475_; uint64_t v___x_476_; uint64_t v___x_477_; lean_object* v___y_479_; uint8_t v___y_480_; uint8_t v___y_481_; lean_object* v___y_485_; uint8_t v___y_486_; lean_object* v___y_490_; uint32_t v___x_495_; lean_object* v___x_496_; uint32_t v___x_497_; lean_object* v___x_498_; uint8_t v___x_499_; 
v___x_471_ = 2267ULL;
v___x_472_ = l_Lean_Level_data___override(v_a_469_);
v___x_473_ = l_Lean_Level_Data_hash(v___x_472_);
v___x_474_ = l_Lean_Level_data___override(v_a_470_);
v___x_475_ = l_Lean_Level_Data_hash(v___x_474_);
v___x_476_ = lean_uint64_mix_hash(v___x_473_, v___x_475_);
v___x_477_ = lean_uint64_mix_hash(v___x_471_, v___x_476_);
v___x_495_ = l_Lean_Level_Data_depth(v___x_472_);
v___x_496_ = lean_uint32_to_nat(v___x_495_);
v___x_497_ = l_Lean_Level_Data_depth(v___x_474_);
v___x_498_ = lean_uint32_to_nat(v___x_497_);
v___x_499_ = lean_nat_dec_le(v___x_496_, v___x_498_);
if (v___x_499_ == 0)
{
lean_dec(v___x_498_);
v___y_490_ = v___x_496_;
goto v___jp_489_;
}
else
{
lean_dec(v___x_496_);
v___y_490_ = v___x_498_;
goto v___jp_489_;
}
v___jp_478_:
{
uint64_t v___x_482_; lean_object* v___x_483_; 
v___x_482_ = lean_level_mk_data(v___x_477_, v___y_479_, v___y_480_, v___y_481_);
v___x_483_ = lean_alloc_ctor(3, 2, 8);
lean_ctor_set(v___x_483_, 0, v_a_469_);
lean_ctor_set(v___x_483_, 1, v_a_470_);
lean_ctor_set_uint64(v___x_483_, sizeof(void*)*2, v___x_482_);
return v___x_483_;
}
v___jp_484_:
{
uint8_t v___x_487_; 
v___x_487_ = l_Lean_Level_Data_hasParam(v___x_472_);
if (v___x_487_ == 0)
{
uint8_t v___x_488_; 
v___x_488_ = l_Lean_Level_Data_hasParam(v___x_474_);
v___y_479_ = v___y_485_;
v___y_480_ = v___y_486_;
v___y_481_ = v___x_488_;
goto v___jp_478_;
}
else
{
v___y_479_ = v___y_485_;
v___y_480_ = v___y_486_;
v___y_481_ = v___x_487_;
goto v___jp_478_;
}
}
v___jp_489_:
{
lean_object* v___x_491_; lean_object* v___x_492_; uint8_t v___x_493_; 
v___x_491_ = lean_unsigned_to_nat(1u);
v___x_492_ = lean_nat_add(v___y_490_, v___x_491_);
lean_dec(v___y_490_);
v___x_493_ = l_Lean_Level_Data_hasMVar(v___x_472_);
if (v___x_493_ == 0)
{
uint8_t v___x_494_; 
v___x_494_ = l_Lean_Level_Data_hasMVar(v___x_474_);
v___y_485_ = v___x_492_;
v___y_486_ = v___x_494_;
goto v___jp_484_;
}
else
{
v___y_485_ = v___x_492_;
v___y_486_ = v___x_493_;
goto v___jp_484_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_param___override(lean_object* v_a_500_){
_start:
{
uint64_t v___x_501_; uint64_t v___y_503_; 
v___x_501_ = 2239ULL;
if (lean_obj_tag(v_a_500_) == 0)
{
uint64_t v___x_510_; 
v___x_510_ = 1723ULL;
v___y_503_ = v___x_510_;
goto v___jp_502_;
}
else
{
uint64_t v_hash_511_; 
v_hash_511_ = lean_ctor_get_uint64(v_a_500_, sizeof(void*)*2);
v___y_503_ = v_hash_511_;
goto v___jp_502_;
}
v___jp_502_:
{
uint64_t v___x_504_; lean_object* v___x_505_; uint8_t v___x_506_; uint8_t v___x_507_; uint64_t v___x_508_; lean_object* v___x_509_; 
v___x_504_ = lean_uint64_mix_hash(v___x_501_, v___y_503_);
v___x_505_ = lean_unsigned_to_nat(0u);
v___x_506_ = 0;
v___x_507_ = 1;
v___x_508_ = lean_level_mk_data(v___x_504_, v___x_505_, v___x_506_, v___x_507_);
v___x_509_ = lean_alloc_ctor(4, 1, 8);
lean_ctor_set(v___x_509_, 0, v_a_500_);
lean_ctor_set_uint64(v___x_509_, sizeof(void*)*1, v___x_508_);
return v___x_509_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_mvar___override(lean_object* v_a_512_){
_start:
{
uint64_t v___x_513_; uint64_t v___x_514_; uint64_t v___x_515_; lean_object* v___x_516_; uint8_t v___x_517_; uint8_t v___x_518_; uint64_t v___x_519_; lean_object* v___x_520_; 
v___x_513_ = 2237ULL;
v___x_514_ = l_Lean_instHashableLevelMVarId_hash(v_a_512_);
v___x_515_ = lean_uint64_mix_hash(v___x_513_, v___x_514_);
v___x_516_ = lean_unsigned_to_nat(0u);
v___x_517_ = 1;
v___x_518_ = 0;
v___x_519_ = lean_level_mk_data(v___x_515_, v___x_516_, v___x_517_, v___x_518_);
v___x_520_ = lean_alloc_ctor(5, 1, 8);
lean_ctor_set(v___x_520_, 0, v_a_512_);
lean_ctor_set_uint64(v___x_520_, sizeof(void*)*1, v___x_519_);
return v___x_520_;
}
}
static lean_object* _init_l_Lean_instInhabitedLevel_default(void){
_start:
{
lean_object* v___x_521_; 
v___x_521_ = lean_box(0);
return v___x_521_;
}
}
static lean_object* _init_l_Lean_instInhabitedLevel(void){
_start:
{
lean_object* v___x_522_; 
v___x_522_ = lean_box(0);
return v___x_522_;
}
}
static lean_object* _init_l_Lean_instReprLevel_repr___closed__2(void){
_start:
{
lean_object* v___x_526_; lean_object* v___x_527_; 
v___x_526_ = lean_unsigned_to_nat(2u);
v___x_527_ = lean_nat_to_int(v___x_526_);
return v___x_527_;
}
}
static lean_object* _init_l_Lean_instReprLevel_repr___closed__3(void){
_start:
{
lean_object* v___x_528_; lean_object* v___x_529_; 
v___x_528_ = lean_unsigned_to_nat(1u);
v___x_529_ = lean_nat_to_int(v___x_528_);
return v___x_529_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprLevel_repr(lean_object* v_x_560_, lean_object* v_prec_561_){
_start:
{
lean_object* v___y_563_; 
switch(lean_obj_tag(v_x_560_))
{
case 0:
{
lean_object* v___x_569_; uint8_t v___x_570_; 
v___x_569_ = lean_unsigned_to_nat(1024u);
v___x_570_ = lean_nat_dec_le(v___x_569_, v_prec_561_);
if (v___x_570_ == 0)
{
lean_object* v___x_571_; 
v___x_571_ = lean_obj_once(&l_Lean_instReprLevel_repr___closed__2, &l_Lean_instReprLevel_repr___closed__2_once, _init_l_Lean_instReprLevel_repr___closed__2);
v___y_563_ = v___x_571_;
goto v___jp_562_;
}
else
{
lean_object* v___x_572_; 
v___x_572_ = lean_obj_once(&l_Lean_instReprLevel_repr___closed__3, &l_Lean_instReprLevel_repr___closed__3_once, _init_l_Lean_instReprLevel_repr___closed__3);
v___y_563_ = v___x_572_;
goto v___jp_562_;
}
}
case 1:
{
lean_object* v_a_573_; lean_object* v___x_574_; lean_object* v___y_576_; uint8_t v___x_584_; 
v_a_573_ = lean_ctor_get(v_x_560_, 0);
lean_inc(v_a_573_);
lean_dec_ref_known(v_x_560_, 1);
v___x_574_ = lean_unsigned_to_nat(1024u);
v___x_584_ = lean_nat_dec_le(v___x_574_, v_prec_561_);
if (v___x_584_ == 0)
{
lean_object* v___x_585_; 
v___x_585_ = lean_obj_once(&l_Lean_instReprLevel_repr___closed__2, &l_Lean_instReprLevel_repr___closed__2_once, _init_l_Lean_instReprLevel_repr___closed__2);
v___y_576_ = v___x_585_;
goto v___jp_575_;
}
else
{
lean_object* v___x_586_; 
v___x_586_ = lean_obj_once(&l_Lean_instReprLevel_repr___closed__3, &l_Lean_instReprLevel_repr___closed__3_once, _init_l_Lean_instReprLevel_repr___closed__3);
v___y_576_ = v___x_586_;
goto v___jp_575_;
}
v___jp_575_:
{
lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; uint8_t v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; 
v___x_577_ = ((lean_object*)(l_Lean_instReprLevel_repr___closed__6));
v___x_578_ = l_Lean_instReprLevel_repr(v_a_573_, v___x_574_);
v___x_579_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_579_, 0, v___x_577_);
lean_ctor_set(v___x_579_, 1, v___x_578_);
lean_inc(v___y_576_);
v___x_580_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_580_, 0, v___y_576_);
lean_ctor_set(v___x_580_, 1, v___x_579_);
v___x_581_ = 0;
v___x_582_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_582_, 0, v___x_580_);
lean_ctor_set_uint8(v___x_582_, sizeof(void*)*1, v___x_581_);
v___x_583_ = l_Repr_addAppParen(v___x_582_, v_prec_561_);
return v___x_583_;
}
}
case 2:
{
lean_object* v_a_587_; lean_object* v_a_588_; lean_object* v___x_589_; lean_object* v___y_591_; uint8_t v___x_603_; 
v_a_587_ = lean_ctor_get(v_x_560_, 0);
lean_inc(v_a_587_);
v_a_588_ = lean_ctor_get(v_x_560_, 1);
lean_inc(v_a_588_);
lean_dec_ref_known(v_x_560_, 2);
v___x_589_ = lean_unsigned_to_nat(1024u);
v___x_603_ = lean_nat_dec_le(v___x_589_, v_prec_561_);
if (v___x_603_ == 0)
{
lean_object* v___x_604_; 
v___x_604_ = lean_obj_once(&l_Lean_instReprLevel_repr___closed__2, &l_Lean_instReprLevel_repr___closed__2_once, _init_l_Lean_instReprLevel_repr___closed__2);
v___y_591_ = v___x_604_;
goto v___jp_590_;
}
else
{
lean_object* v___x_605_; 
v___x_605_ = lean_obj_once(&l_Lean_instReprLevel_repr___closed__3, &l_Lean_instReprLevel_repr___closed__3_once, _init_l_Lean_instReprLevel_repr___closed__3);
v___y_591_ = v___x_605_;
goto v___jp_590_;
}
v___jp_590_:
{
lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; uint8_t v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; 
v___x_592_ = lean_box(1);
v___x_593_ = ((lean_object*)(l_Lean_instReprLevel_repr___closed__9));
v___x_594_ = l_Lean_instReprLevel_repr(v_a_587_, v___x_589_);
v___x_595_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_595_, 0, v___x_593_);
lean_ctor_set(v___x_595_, 1, v___x_594_);
v___x_596_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_596_, 0, v___x_595_);
lean_ctor_set(v___x_596_, 1, v___x_592_);
v___x_597_ = l_Lean_instReprLevel_repr(v_a_588_, v___x_589_);
v___x_598_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_598_, 0, v___x_596_);
lean_ctor_set(v___x_598_, 1, v___x_597_);
lean_inc(v___y_591_);
v___x_599_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_599_, 0, v___y_591_);
lean_ctor_set(v___x_599_, 1, v___x_598_);
v___x_600_ = 0;
v___x_601_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_601_, 0, v___x_599_);
lean_ctor_set_uint8(v___x_601_, sizeof(void*)*1, v___x_600_);
v___x_602_ = l_Repr_addAppParen(v___x_601_, v_prec_561_);
return v___x_602_;
}
}
case 3:
{
lean_object* v_a_606_; lean_object* v_a_607_; lean_object* v___x_608_; lean_object* v___y_610_; uint8_t v___x_622_; 
v_a_606_ = lean_ctor_get(v_x_560_, 0);
lean_inc(v_a_606_);
v_a_607_ = lean_ctor_get(v_x_560_, 1);
lean_inc(v_a_607_);
lean_dec_ref_known(v_x_560_, 2);
v___x_608_ = lean_unsigned_to_nat(1024u);
v___x_622_ = lean_nat_dec_le(v___x_608_, v_prec_561_);
if (v___x_622_ == 0)
{
lean_object* v___x_623_; 
v___x_623_ = lean_obj_once(&l_Lean_instReprLevel_repr___closed__2, &l_Lean_instReprLevel_repr___closed__2_once, _init_l_Lean_instReprLevel_repr___closed__2);
v___y_610_ = v___x_623_;
goto v___jp_609_;
}
else
{
lean_object* v___x_624_; 
v___x_624_ = lean_obj_once(&l_Lean_instReprLevel_repr___closed__3, &l_Lean_instReprLevel_repr___closed__3_once, _init_l_Lean_instReprLevel_repr___closed__3);
v___y_610_ = v___x_624_;
goto v___jp_609_;
}
v___jp_609_:
{
lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; uint8_t v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; 
v___x_611_ = lean_box(1);
v___x_612_ = ((lean_object*)(l_Lean_instReprLevel_repr___closed__12));
v___x_613_ = l_Lean_instReprLevel_repr(v_a_606_, v___x_608_);
v___x_614_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_614_, 0, v___x_612_);
lean_ctor_set(v___x_614_, 1, v___x_613_);
v___x_615_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_615_, 0, v___x_614_);
lean_ctor_set(v___x_615_, 1, v___x_611_);
v___x_616_ = l_Lean_instReprLevel_repr(v_a_607_, v___x_608_);
v___x_617_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_617_, 0, v___x_615_);
lean_ctor_set(v___x_617_, 1, v___x_616_);
lean_inc(v___y_610_);
v___x_618_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_618_, 0, v___y_610_);
lean_ctor_set(v___x_618_, 1, v___x_617_);
v___x_619_ = 0;
v___x_620_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_620_, 0, v___x_618_);
lean_ctor_set_uint8(v___x_620_, sizeof(void*)*1, v___x_619_);
v___x_621_ = l_Repr_addAppParen(v___x_620_, v_prec_561_);
return v___x_621_;
}
}
case 4:
{
lean_object* v_a_625_; lean_object* v___y_627_; lean_object* v___x_636_; uint8_t v___x_637_; 
v_a_625_ = lean_ctor_get(v_x_560_, 0);
lean_inc(v_a_625_);
lean_dec_ref_known(v_x_560_, 1);
v___x_636_ = lean_unsigned_to_nat(1024u);
v___x_637_ = lean_nat_dec_le(v___x_636_, v_prec_561_);
if (v___x_637_ == 0)
{
lean_object* v___x_638_; 
v___x_638_ = lean_obj_once(&l_Lean_instReprLevel_repr___closed__2, &l_Lean_instReprLevel_repr___closed__2_once, _init_l_Lean_instReprLevel_repr___closed__2);
v___y_627_ = v___x_638_;
goto v___jp_626_;
}
else
{
lean_object* v___x_639_; 
v___x_639_ = lean_obj_once(&l_Lean_instReprLevel_repr___closed__3, &l_Lean_instReprLevel_repr___closed__3_once, _init_l_Lean_instReprLevel_repr___closed__3);
v___y_627_ = v___x_639_;
goto v___jp_626_;
}
v___jp_626_:
{
lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; uint8_t v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; 
v___x_628_ = ((lean_object*)(l_Lean_instReprLevel_repr___closed__15));
v___x_629_ = lean_unsigned_to_nat(1024u);
v___x_630_ = l_Lean_Name_reprPrec(v_a_625_, v___x_629_);
v___x_631_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_631_, 0, v___x_628_);
lean_ctor_set(v___x_631_, 1, v___x_630_);
lean_inc(v___y_627_);
v___x_632_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_632_, 0, v___y_627_);
lean_ctor_set(v___x_632_, 1, v___x_631_);
v___x_633_ = 0;
v___x_634_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_634_, 0, v___x_632_);
lean_ctor_set_uint8(v___x_634_, sizeof(void*)*1, v___x_633_);
v___x_635_ = l_Repr_addAppParen(v___x_634_, v_prec_561_);
return v___x_635_;
}
}
default: 
{
lean_object* v_a_640_; lean_object* v___y_642_; lean_object* v___x_651_; uint8_t v___x_652_; 
v_a_640_ = lean_ctor_get(v_x_560_, 0);
lean_inc(v_a_640_);
lean_dec_ref_known(v_x_560_, 1);
v___x_651_ = lean_unsigned_to_nat(1024u);
v___x_652_ = lean_nat_dec_le(v___x_651_, v_prec_561_);
if (v___x_652_ == 0)
{
lean_object* v___x_653_; 
v___x_653_ = lean_obj_once(&l_Lean_instReprLevel_repr___closed__2, &l_Lean_instReprLevel_repr___closed__2_once, _init_l_Lean_instReprLevel_repr___closed__2);
v___y_642_ = v___x_653_;
goto v___jp_641_;
}
else
{
lean_object* v___x_654_; 
v___x_654_ = lean_obj_once(&l_Lean_instReprLevel_repr___closed__3, &l_Lean_instReprLevel_repr___closed__3_once, _init_l_Lean_instReprLevel_repr___closed__3);
v___y_642_ = v___x_654_;
goto v___jp_641_;
}
v___jp_641_:
{
lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; uint8_t v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; 
v___x_643_ = ((lean_object*)(l_Lean_instReprLevel_repr___closed__18));
v___x_644_ = lean_unsigned_to_nat(1024u);
v___x_645_ = l_Lean_Name_reprPrec(v_a_640_, v___x_644_);
v___x_646_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_646_, 0, v___x_643_);
lean_ctor_set(v___x_646_, 1, v___x_645_);
lean_inc(v___y_642_);
v___x_647_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_647_, 0, v___y_642_);
lean_ctor_set(v___x_647_, 1, v___x_646_);
v___x_648_ = 0;
v___x_649_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_649_, 0, v___x_647_);
lean_ctor_set_uint8(v___x_649_, sizeof(void*)*1, v___x_648_);
v___x_650_ = l_Repr_addAppParen(v___x_649_, v_prec_561_);
return v___x_650_;
}
}
}
v___jp_562_:
{
lean_object* v___x_564_; lean_object* v___x_565_; uint8_t v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; 
v___x_564_ = ((lean_object*)(l_Lean_instReprLevel_repr___closed__1));
lean_inc(v___y_563_);
v___x_565_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_565_, 0, v___y_563_);
lean_ctor_set(v___x_565_, 1, v___x_564_);
v___x_566_ = 0;
v___x_567_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_567_, 0, v___x_565_);
lean_ctor_set_uint8(v___x_567_, sizeof(void*)*1, v___x_566_);
v___x_568_ = l_Repr_addAppParen(v___x_567_, v_prec_561_);
return v___x_568_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instReprLevel_repr___boxed(lean_object* v_x_655_, lean_object* v_prec_656_){
_start:
{
lean_object* v_res_657_; 
v_res_657_ = l_Lean_instReprLevel_repr(v_x_655_, v_prec_656_);
lean_dec(v_prec_656_);
return v_res_657_;
}
}
LEAN_EXPORT uint64_t l_Lean_Level_hash(lean_object* v_u_660_){
_start:
{
uint64_t v___x_661_; uint64_t v___x_662_; 
v___x_661_ = l_Lean_Level_data___override(v_u_660_);
v___x_662_ = l_Lean_Level_Data_hash(v___x_661_);
return v___x_662_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_hash___boxed(lean_object* v_u_663_){
_start:
{
uint64_t v_res_664_; lean_object* v_r_665_; 
v_res_664_ = l_Lean_Level_hash(v_u_663_);
lean_dec(v_u_663_);
v_r_665_ = lean_box_uint64(v_res_664_);
return v_r_665_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_depth(lean_object* v_u_668_){
_start:
{
uint64_t v___x_669_; uint32_t v___x_670_; lean_object* v___x_671_; 
v___x_669_ = l_Lean_Level_data___override(v_u_668_);
v___x_670_ = l_Lean_Level_Data_depth(v___x_669_);
v___x_671_ = lean_uint32_to_nat(v___x_670_);
return v___x_671_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_depth___boxed(lean_object* v_u_672_){
_start:
{
lean_object* v_res_673_; 
v_res_673_ = l_Lean_Level_depth(v_u_672_);
lean_dec(v_u_672_);
return v_res_673_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_hasMVar(lean_object* v_u_674_){
_start:
{
uint64_t v___x_675_; uint8_t v___x_676_; 
v___x_675_ = l_Lean_Level_data___override(v_u_674_);
v___x_676_ = l_Lean_Level_Data_hasMVar(v___x_675_);
return v___x_676_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_hasMVar___boxed(lean_object* v_u_677_){
_start:
{
uint8_t v_res_678_; lean_object* v_r_679_; 
v_res_678_ = l_Lean_Level_hasMVar(v_u_677_);
lean_dec(v_u_677_);
v_r_679_ = lean_box(v_res_678_);
return v_r_679_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_hasParam(lean_object* v_u_680_){
_start:
{
uint64_t v___x_681_; uint8_t v___x_682_; 
v___x_681_ = l_Lean_Level_data___override(v_u_680_);
v___x_682_ = l_Lean_Level_Data_hasParam(v___x_681_);
return v___x_682_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_hasParam___boxed(lean_object* v_u_683_){
_start:
{
uint8_t v_res_684_; lean_object* v_r_685_; 
v_res_684_ = l_Lean_Level_hasParam(v_u_683_);
lean_dec(v_u_683_);
v_r_685_ = lean_box(v_res_684_);
return v_r_685_;
}
}
LEAN_EXPORT uint32_t lean_level_hash(lean_object* v_u_686_){
_start:
{
uint64_t v___x_687_; uint32_t v___x_688_; 
v___x_687_ = l_Lean_Level_hash(v_u_686_);
lean_dec(v_u_686_);
v___x_688_ = lean_uint64_to_uint32(v___x_687_);
return v___x_688_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_hashEx___boxed(lean_object* v_u_689_){
_start:
{
uint32_t v_res_690_; lean_object* v_r_691_; 
v_res_690_ = lean_level_hash(v_u_689_);
v_r_691_ = lean_box_uint32(v_res_690_);
return v_r_691_;
}
}
LEAN_EXPORT uint8_t lean_level_has_mvar(lean_object* v_u_692_){
_start:
{
uint8_t v___x_693_; 
v___x_693_ = l_Lean_Level_hasMVar(v_u_692_);
lean_dec(v_u_692_);
return v___x_693_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_hasMVarEx___boxed(lean_object* v_u_694_){
_start:
{
uint8_t v_res_695_; lean_object* v_r_696_; 
v_res_695_ = lean_level_has_mvar(v_u_694_);
v_r_696_ = lean_box(v_res_695_);
return v_r_696_;
}
}
LEAN_EXPORT uint8_t lean_level_has_param(lean_object* v_u_697_){
_start:
{
uint8_t v___x_698_; 
v___x_698_ = l_Lean_Level_hasParam(v_u_697_);
lean_dec(v_u_697_);
return v___x_698_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_hasParamEx___boxed(lean_object* v_u_699_){
_start:
{
uint8_t v_res_700_; lean_object* v_r_701_; 
v_res_700_ = lean_level_has_param(v_u_699_);
v_r_701_ = lean_box(v_res_700_);
return v_r_701_;
}
}
LEAN_EXPORT uint32_t lean_level_depth(lean_object* v_u_702_){
_start:
{
uint64_t v___x_703_; uint32_t v___x_704_; 
v___x_703_ = l_Lean_Level_data___override(v_u_702_);
lean_dec(v_u_702_);
v___x_704_ = l_Lean_Level_Data_depth(v___x_703_);
return v___x_704_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_depthEx___boxed(lean_object* v_u_705_){
_start:
{
uint32_t v_res_706_; lean_object* v_r_707_; 
v_res_706_ = lean_level_depth(v_u_705_);
v_r_707_ = lean_box_uint32(v_res_706_);
return v_r_707_;
}
}
static lean_object* _init_l_Lean_levelZero(void){
_start:
{
lean_object* v___x_708_; 
v___x_708_ = lean_box(0);
return v___x_708_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLevelMVar(lean_object* v_mvarId_709_){
_start:
{
lean_object* v___x_710_; 
v___x_710_ = l_Lean_Level_mvar___override(v_mvarId_709_);
return v___x_710_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLevelParam(lean_object* v_name_711_){
_start:
{
lean_object* v___x_712_; 
v___x_712_ = l_Lean_Level_param___override(v_name_711_);
return v___x_712_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLevelSucc(lean_object* v_u_713_){
_start:
{
lean_object* v___x_714_; 
v___x_714_ = l_Lean_Level_succ___override(v_u_713_);
return v___x_714_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLevelMax(lean_object* v_u_715_, lean_object* v_v_716_){
_start:
{
lean_object* v___x_717_; 
v___x_717_ = l_Lean_Level_max___override(v_u_715_, v_v_716_);
return v___x_717_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLevelIMax(lean_object* v_u_718_, lean_object* v_v_719_){
_start:
{
lean_object* v___x_720_; 
v___x_720_ = l_Lean_Level_imax___override(v_u_718_, v_v_719_);
return v___x_720_;
}
}
static lean_object* _init_l_Lean_Level_one___closed__0(void){
_start:
{
lean_object* v___x_721_; lean_object* v___x_722_; 
v___x_721_ = lean_box(0);
v___x_722_ = l_Lean_Level_succ___override(v___x_721_);
return v___x_722_;
}
}
static lean_object* _init_l_Lean_Level_one(void){
_start:
{
lean_object* v___x_723_; 
v___x_723_ = lean_obj_once(&l_Lean_Level_one___closed__0, &l_Lean_Level_one___closed__0_once, _init_l_Lean_Level_one___closed__0);
return v___x_723_;
}
}
static lean_object* _init_l_Lean_levelOne(void){
_start:
{
lean_object* v___x_724_; 
v___x_724_ = lean_obj_once(&l_Lean_Level_one___closed__0, &l_Lean_Level_one___closed__0_once, _init_l_Lean_Level_one___closed__0);
return v___x_724_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLevelZeroEx___redArg(){
_start:
{
lean_object* v___x_726_; 
v___x_726_ = lean_box(0);
return v___x_726_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLevelZeroEx___redArg___boxed(lean_object* v___dummy_727_){
_start:
{
lean_object* v_res_728_; 
v_res_728_ = l_Lean_mkLevelZeroEx___redArg();
return v_res_728_;
}
}
LEAN_EXPORT lean_object* lean_level_mk_zero(lean_object* v_x_729_){
_start:
{
lean_object* v___x_730_; 
v___x_730_ = lean_box(0);
return v___x_730_;
}
}
LEAN_EXPORT lean_object* lean_level_mk_succ(lean_object* v_u_731_){
_start:
{
lean_object* v___x_732_; 
v___x_732_ = l_Lean_Level_succ___override(v_u_731_);
return v___x_732_;
}
}
LEAN_EXPORT lean_object* lean_level_mk_param(lean_object* v_name_733_){
_start:
{
lean_object* v___x_734_; 
v___x_734_ = l_Lean_Level_param___override(v_name_733_);
return v___x_734_;
}
}
LEAN_EXPORT lean_object* lean_level_mk_max(lean_object* v_u_735_, lean_object* v_v_736_){
_start:
{
lean_object* v___x_737_; 
v___x_737_ = l_Lean_Level_max___override(v_u_735_, v_v_736_);
return v___x_737_;
}
}
LEAN_EXPORT lean_object* lean_level_mk_imax(lean_object* v_u_738_, lean_object* v_v_739_){
_start:
{
lean_object* v___x_740_; 
v___x_740_ = l_Lean_Level_imax___override(v_u_738_, v_v_739_);
return v___x_740_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_isZero(lean_object* v_x_741_){
_start:
{
if (lean_obj_tag(v_x_741_) == 0)
{
uint8_t v___x_742_; 
v___x_742_ = 1;
return v___x_742_;
}
else
{
uint8_t v___x_743_; 
v___x_743_ = 0;
return v___x_743_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_isZero___boxed(lean_object* v_x_744_){
_start:
{
uint8_t v_res_745_; lean_object* v_r_746_; 
v_res_745_ = l_Lean_Level_isZero(v_x_744_);
lean_dec(v_x_744_);
v_r_746_ = lean_box(v_res_745_);
return v_r_746_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_isSucc(lean_object* v_x_747_){
_start:
{
if (lean_obj_tag(v_x_747_) == 1)
{
uint8_t v___x_748_; 
v___x_748_ = 1;
return v___x_748_;
}
else
{
uint8_t v___x_749_; 
v___x_749_ = 0;
return v___x_749_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_isSucc___boxed(lean_object* v_x_750_){
_start:
{
uint8_t v_res_751_; lean_object* v_r_752_; 
v_res_751_ = l_Lean_Level_isSucc(v_x_750_);
lean_dec(v_x_750_);
v_r_752_ = lean_box(v_res_751_);
return v_r_752_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_isMax(lean_object* v_x_753_){
_start:
{
if (lean_obj_tag(v_x_753_) == 2)
{
uint8_t v___x_754_; 
v___x_754_ = 1;
return v___x_754_;
}
else
{
uint8_t v___x_755_; 
v___x_755_ = 0;
return v___x_755_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_isMax___boxed(lean_object* v_x_756_){
_start:
{
uint8_t v_res_757_; lean_object* v_r_758_; 
v_res_757_ = l_Lean_Level_isMax(v_x_756_);
lean_dec(v_x_756_);
v_r_758_ = lean_box(v_res_757_);
return v_r_758_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_isIMax(lean_object* v_x_759_){
_start:
{
if (lean_obj_tag(v_x_759_) == 3)
{
uint8_t v___x_760_; 
v___x_760_ = 1;
return v___x_760_;
}
else
{
uint8_t v___x_761_; 
v___x_761_ = 0;
return v___x_761_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_isIMax___boxed(lean_object* v_x_762_){
_start:
{
uint8_t v_res_763_; lean_object* v_r_764_; 
v_res_763_ = l_Lean_Level_isIMax(v_x_762_);
lean_dec(v_x_762_);
v_r_764_ = lean_box(v_res_763_);
return v_r_764_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_isMaxIMax(lean_object* v_x_765_){
_start:
{
switch(lean_obj_tag(v_x_765_))
{
case 2:
{
uint8_t v___x_766_; 
v___x_766_ = 1;
return v___x_766_;
}
case 3:
{
uint8_t v___x_767_; 
v___x_767_ = 1;
return v___x_767_;
}
default: 
{
uint8_t v___x_768_; 
v___x_768_ = 0;
return v___x_768_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_isMaxIMax___boxed(lean_object* v_x_769_){
_start:
{
uint8_t v_res_770_; lean_object* v_r_771_; 
v_res_770_ = l_Lean_Level_isMaxIMax(v_x_769_);
lean_dec(v_x_769_);
v_r_771_ = lean_box(v_res_770_);
return v_r_771_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_isParam(lean_object* v_x_772_){
_start:
{
if (lean_obj_tag(v_x_772_) == 4)
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
LEAN_EXPORT lean_object* l_Lean_Level_isParam___boxed(lean_object* v_x_775_){
_start:
{
uint8_t v_res_776_; lean_object* v_r_777_; 
v_res_776_ = l_Lean_Level_isParam(v_x_775_);
lean_dec(v_x_775_);
v_r_777_ = lean_box(v_res_776_);
return v_r_777_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_isMVar(lean_object* v_x_778_){
_start:
{
if (lean_obj_tag(v_x_778_) == 5)
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
LEAN_EXPORT lean_object* l_Lean_Level_isMVar___boxed(lean_object* v_x_781_){
_start:
{
uint8_t v_res_782_; lean_object* v_r_783_; 
v_res_782_ = l_Lean_Level_isMVar(v_x_781_);
lean_dec(v_x_781_);
v_r_783_ = lean_box(v_res_782_);
return v_r_783_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Level_mvarId_x21_spec__0(lean_object* v_msg_784_){
_start:
{
lean_object* v___x_785_; lean_object* v___x_786_; 
v___x_785_ = lean_box(0);
v___x_786_ = lean_panic_fn_borrowed(v___x_785_, v_msg_784_);
return v___x_786_;
}
}
static lean_object* _init_l_Lean_Level_mvarId_x21___closed__3(void){
_start:
{
lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; 
v___x_790_ = ((lean_object*)(l_Lean_Level_mvarId_x21___closed__2));
v___x_791_ = lean_unsigned_to_nat(19u);
v___x_792_ = lean_unsigned_to_nat(195u);
v___x_793_ = ((lean_object*)(l_Lean_Level_mvarId_x21___closed__1));
v___x_794_ = ((lean_object*)(l_Lean_Level_mvarId_x21___closed__0));
v___x_795_ = l_mkPanicMessageWithDecl(v___x_794_, v___x_793_, v___x_792_, v___x_791_, v___x_790_);
return v___x_795_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_mvarId_x21(lean_object* v_x_796_){
_start:
{
if (lean_obj_tag(v_x_796_) == 5)
{
lean_object* v_a_797_; 
v_a_797_ = lean_ctor_get(v_x_796_, 0);
lean_inc(v_a_797_);
return v_a_797_;
}
else
{
lean_object* v___x_798_; lean_object* v___x_799_; 
v___x_798_ = lean_obj_once(&l_Lean_Level_mvarId_x21___closed__3, &l_Lean_Level_mvarId_x21___closed__3_once, _init_l_Lean_Level_mvarId_x21___closed__3);
v___x_799_ = l_panic___at___00Lean_Level_mvarId_x21_spec__0(v___x_798_);
return v___x_799_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_mvarId_x21___boxed(lean_object* v_x_800_){
_start:
{
lean_object* v_res_801_; 
v_res_801_ = l_Lean_Level_mvarId_x21(v_x_800_);
lean_dec(v_x_800_);
return v_res_801_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_isNeverZero(lean_object* v_x_802_){
_start:
{
switch(lean_obj_tag(v_x_802_))
{
case 1:
{
uint8_t v___x_803_; 
v___x_803_ = 1;
return v___x_803_;
}
case 2:
{
lean_object* v_a_804_; lean_object* v_a_805_; uint8_t v___x_806_; 
v_a_804_ = lean_ctor_get(v_x_802_, 0);
v_a_805_ = lean_ctor_get(v_x_802_, 1);
v___x_806_ = l_Lean_Level_isNeverZero(v_a_804_);
if (v___x_806_ == 0)
{
v_x_802_ = v_a_805_;
goto _start;
}
else
{
return v___x_806_;
}
}
case 3:
{
lean_object* v_a_808_; 
v_a_808_ = lean_ctor_get(v_x_802_, 1);
v_x_802_ = v_a_808_;
goto _start;
}
default: 
{
uint8_t v___x_810_; 
v___x_810_ = 0;
return v___x_810_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_isNeverZero___boxed(lean_object* v_x_811_){
_start:
{
uint8_t v_res_812_; lean_object* v_r_813_; 
v_res_812_ = l_Lean_Level_isNeverZero(v_x_811_);
lean_dec(v_x_811_);
v_r_813_ = lean_box(v_res_812_);
return v_r_813_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_isAlwaysZero(lean_object* v_x_814_){
_start:
{
switch(lean_obj_tag(v_x_814_))
{
case 0:
{
uint8_t v___x_815_; 
v___x_815_ = 1;
return v___x_815_;
}
case 2:
{
lean_object* v_a_816_; lean_object* v_a_817_; uint8_t v___x_818_; 
v_a_816_ = lean_ctor_get(v_x_814_, 0);
v_a_817_ = lean_ctor_get(v_x_814_, 1);
v___x_818_ = l_Lean_Level_isAlwaysZero(v_a_816_);
if (v___x_818_ == 0)
{
return v___x_818_;
}
else
{
v_x_814_ = v_a_817_;
goto _start;
}
}
case 3:
{
lean_object* v_a_820_; 
v_a_820_ = lean_ctor_get(v_x_814_, 1);
v_x_814_ = v_a_820_;
goto _start;
}
default: 
{
uint8_t v___x_822_; 
v___x_822_ = 0;
return v___x_822_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_isAlwaysZero___boxed(lean_object* v_x_823_){
_start:
{
uint8_t v_res_824_; lean_object* v_r_825_; 
v_res_824_ = l_Lean_Level_isAlwaysZero(v_x_823_);
lean_dec(v_x_823_);
v_r_825_ = lean_box(v_res_824_);
return v_r_825_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_ofNat(lean_object* v_x_826_){
_start:
{
lean_object* v_zero_827_; uint8_t v_isZero_828_; 
v_zero_827_ = lean_unsigned_to_nat(0u);
v_isZero_828_ = lean_nat_dec_eq(v_x_826_, v_zero_827_);
if (v_isZero_828_ == 1)
{
lean_object* v___x_829_; 
v___x_829_ = lean_box(0);
return v___x_829_;
}
else
{
lean_object* v_one_830_; lean_object* v_n_831_; lean_object* v___x_832_; lean_object* v___x_833_; 
v_one_830_ = lean_unsigned_to_nat(1u);
v_n_831_ = lean_nat_sub(v_x_826_, v_one_830_);
v___x_832_ = l_Lean_Level_ofNat(v_n_831_);
lean_dec(v_n_831_);
v___x_833_ = l_Lean_Level_succ___override(v___x_832_);
return v___x_833_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_ofNat___boxed(lean_object* v_x_834_){
_start:
{
lean_object* v_res_835_; 
v_res_835_ = l_Lean_Level_ofNat(v_x_834_);
lean_dec(v_x_834_);
return v_res_835_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_instOfNat(lean_object* v_n_836_){
_start:
{
lean_object* v___x_837_; 
v___x_837_ = l_Lean_Level_ofNat(v_n_836_);
return v___x_837_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_instOfNat___boxed(lean_object* v_n_838_){
_start:
{
lean_object* v_res_839_; 
v_res_839_ = l_Lean_Level_instOfNat(v_n_838_);
lean_dec(v_n_838_);
return v_res_839_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_addOffsetAux(lean_object* v_x_840_, lean_object* v_x_841_){
_start:
{
lean_object* v_zero_842_; uint8_t v_isZero_843_; 
v_zero_842_ = lean_unsigned_to_nat(0u);
v_isZero_843_ = lean_nat_dec_eq(v_x_840_, v_zero_842_);
if (v_isZero_843_ == 1)
{
lean_dec(v_x_840_);
return v_x_841_;
}
else
{
lean_object* v_one_844_; lean_object* v_n_845_; lean_object* v___x_846_; 
v_one_844_ = lean_unsigned_to_nat(1u);
v_n_845_ = lean_nat_sub(v_x_840_, v_one_844_);
lean_dec(v_x_840_);
v___x_846_ = l_Lean_Level_succ___override(v_x_841_);
v_x_840_ = v_n_845_;
v_x_841_ = v___x_846_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_addOffset(lean_object* v_u_848_, lean_object* v_n_849_){
_start:
{
lean_object* v___x_850_; 
v___x_850_ = l_Lean_Level_addOffsetAux(v_n_849_, v_u_848_);
return v___x_850_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_isExplicit(lean_object* v_x_851_){
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
case 1:
{
lean_object* v_a_853_; uint8_t v___x_854_; 
v_a_853_ = lean_ctor_get(v_x_851_, 0);
v___x_854_ = l_Lean_Level_hasMVar(v_a_853_);
if (v___x_854_ == 0)
{
uint8_t v___x_855_; 
v___x_855_ = l_Lean_Level_hasParam(v_a_853_);
if (v___x_855_ == 0)
{
v_x_851_ = v_a_853_;
goto _start;
}
else
{
return v___x_854_;
}
}
else
{
uint8_t v___x_857_; 
v___x_857_ = 0;
return v___x_857_;
}
}
default: 
{
uint8_t v___x_858_; 
v___x_858_ = 0;
return v___x_858_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_isExplicit___boxed(lean_object* v_x_859_){
_start:
{
uint8_t v_res_860_; lean_object* v_r_861_; 
v_res_860_ = l_Lean_Level_isExplicit(v_x_859_);
lean_dec(v_x_859_);
v_r_861_ = lean_box(v_res_860_);
return v_r_861_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_getOffsetAux(lean_object* v_x_862_, lean_object* v_x_863_){
_start:
{
if (lean_obj_tag(v_x_862_) == 1)
{
lean_object* v_a_864_; lean_object* v___x_865_; lean_object* v___x_866_; 
v_a_864_ = lean_ctor_get(v_x_862_, 0);
v___x_865_ = lean_unsigned_to_nat(1u);
v___x_866_ = lean_nat_add(v_x_863_, v___x_865_);
lean_dec(v_x_863_);
v_x_862_ = v_a_864_;
v_x_863_ = v___x_866_;
goto _start;
}
else
{
return v_x_863_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_getOffsetAux___boxed(lean_object* v_x_868_, lean_object* v_x_869_){
_start:
{
lean_object* v_res_870_; 
v_res_870_ = l_Lean_Level_getOffsetAux(v_x_868_, v_x_869_);
lean_dec(v_x_868_);
return v_res_870_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_getOffset(lean_object* v_lvl_871_){
_start:
{
lean_object* v___x_872_; lean_object* v___x_873_; 
v___x_872_ = lean_unsigned_to_nat(0u);
v___x_873_ = l_Lean_Level_getOffsetAux(v_lvl_871_, v___x_872_);
return v___x_873_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_getOffset___boxed(lean_object* v_lvl_874_){
_start:
{
lean_object* v_res_875_; 
v_res_875_ = l_Lean_Level_getOffset(v_lvl_874_);
lean_dec(v_lvl_874_);
return v_res_875_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_getLevelOffset(lean_object* v_x_876_){
_start:
{
if (lean_obj_tag(v_x_876_) == 1)
{
lean_object* v_a_877_; 
v_a_877_ = lean_ctor_get(v_x_876_, 0);
v_x_876_ = v_a_877_;
goto _start;
}
else
{
lean_inc(v_x_876_);
return v_x_876_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_getLevelOffset___boxed(lean_object* v_x_879_){
_start:
{
lean_object* v_res_880_; 
v_res_880_ = l_Lean_Level_getLevelOffset(v_x_879_);
lean_dec(v_x_879_);
return v_res_880_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_toNat(lean_object* v_lvl_881_){
_start:
{
lean_object* v___x_882_; 
v___x_882_ = l_Lean_Level_getLevelOffset(v_lvl_881_);
if (lean_obj_tag(v___x_882_) == 0)
{
lean_object* v___x_883_; lean_object* v___x_884_; 
v___x_883_ = l_Lean_Level_getOffset(v_lvl_881_);
v___x_884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_884_, 0, v___x_883_);
return v___x_884_;
}
else
{
lean_object* v___x_885_; 
lean_dec(v___x_882_);
v___x_885_ = lean_box(0);
return v___x_885_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_toNat___boxed(lean_object* v_lvl_886_){
_start:
{
lean_object* v_res_887_; 
v_res_887_ = l_Lean_Level_toNat(v_lvl_886_);
lean_dec(v_lvl_886_);
return v_res_887_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_beq___boxed(lean_object* v_a_890_, lean_object* v_b_891_){
_start:
{
uint8_t v_res_892_; lean_object* v_r_893_; 
v_res_892_ = lean_level_eq(v_a_890_, v_b_891_);
lean_dec(v_b_891_);
lean_dec(v_a_890_);
v_r_893_ = lean_box(v_res_892_);
return v_r_893_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_occurs(lean_object* v_x_896_, lean_object* v_x_897_){
_start:
{
switch(lean_obj_tag(v_x_897_))
{
case 1:
{
lean_object* v_a_898_; uint8_t v___x_899_; 
v_a_898_ = lean_ctor_get(v_x_897_, 0);
v___x_899_ = lean_level_eq(v_x_896_, v_x_897_);
if (v___x_899_ == 0)
{
v_x_897_ = v_a_898_;
goto _start;
}
else
{
return v___x_899_;
}
}
case 2:
{
lean_object* v_a_901_; lean_object* v_a_902_; uint8_t v___x_903_; 
v_a_901_ = lean_ctor_get(v_x_897_, 0);
v_a_902_ = lean_ctor_get(v_x_897_, 1);
v___x_903_ = lean_level_eq(v_x_896_, v_x_897_);
if (v___x_903_ == 0)
{
uint8_t v___x_904_; 
v___x_904_ = l_Lean_Level_occurs(v_x_896_, v_a_901_);
if (v___x_904_ == 0)
{
v_x_897_ = v_a_902_;
goto _start;
}
else
{
return v___x_904_;
}
}
else
{
return v___x_903_;
}
}
case 3:
{
lean_object* v_a_906_; lean_object* v_a_907_; uint8_t v___x_908_; 
v_a_906_ = lean_ctor_get(v_x_897_, 0);
v_a_907_ = lean_ctor_get(v_x_897_, 1);
v___x_908_ = lean_level_eq(v_x_896_, v_x_897_);
if (v___x_908_ == 0)
{
uint8_t v___x_909_; 
v___x_909_ = l_Lean_Level_occurs(v_x_896_, v_a_906_);
if (v___x_909_ == 0)
{
v_x_897_ = v_a_907_;
goto _start;
}
else
{
return v___x_909_;
}
}
else
{
return v___x_908_;
}
}
default: 
{
uint8_t v___x_911_; 
v___x_911_ = lean_level_eq(v_x_896_, v_x_897_);
return v___x_911_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_occurs___boxed(lean_object* v_x_912_, lean_object* v_x_913_){
_start:
{
uint8_t v_res_914_; lean_object* v_r_915_; 
v_res_914_ = l_Lean_Level_occurs(v_x_912_, v_x_913_);
lean_dec(v_x_913_);
lean_dec(v_x_912_);
v_r_915_ = lean_box(v_res_914_);
return v_r_915_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_ctorToNat(lean_object* v_x_916_){
_start:
{
switch(lean_obj_tag(v_x_916_))
{
case 0:
{
lean_object* v___x_917_; 
v___x_917_ = lean_unsigned_to_nat(0u);
return v___x_917_;
}
case 1:
{
lean_object* v___x_918_; 
v___x_918_ = lean_unsigned_to_nat(3u);
return v___x_918_;
}
case 2:
{
lean_object* v___x_919_; 
v___x_919_ = lean_unsigned_to_nat(4u);
return v___x_919_;
}
case 3:
{
lean_object* v___x_920_; 
v___x_920_ = lean_unsigned_to_nat(5u);
return v___x_920_;
}
case 4:
{
lean_object* v___x_921_; 
v___x_921_ = lean_unsigned_to_nat(1u);
return v___x_921_;
}
default: 
{
lean_object* v___x_922_; 
v___x_922_ = lean_unsigned_to_nat(2u);
return v___x_922_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_ctorToNat___boxed(lean_object* v_x_923_){
_start:
{
lean_object* v_res_924_; 
v_res_924_ = l_Lean_Level_ctorToNat(v_x_923_);
lean_dec(v_x_923_);
return v_res_924_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_normLtAux(lean_object* v_x_925_, lean_object* v_x_926_, lean_object* v_x_927_, lean_object* v_x_928_){
_start:
{
lean_object* v_l_u2081_930_; lean_object* v_k_u2081_931_; lean_object* v_l_u2082_932_; lean_object* v_k_u2082_933_; lean_object* v_l_u2081_938_; lean_object* v_k_u2081_939_; lean_object* v_l_u2082_940_; lean_object* v_k_u2082_941_; 
switch(lean_obj_tag(v_x_925_))
{
case 1:
{
lean_object* v_a_947_; lean_object* v___x_948_; lean_object* v___x_949_; 
v_a_947_ = lean_ctor_get(v_x_925_, 0);
v___x_948_ = lean_unsigned_to_nat(1u);
v___x_949_ = lean_nat_add(v_x_926_, v___x_948_);
lean_dec(v_x_926_);
v_x_925_ = v_a_947_;
v_x_926_ = v___x_949_;
goto _start;
}
case 2:
{
switch(lean_obj_tag(v_x_927_))
{
case 1:
{
lean_object* v_a_951_; 
v_a_951_ = lean_ctor_get(v_x_927_, 0);
v_l_u2081_930_ = v_x_925_;
v_k_u2081_931_ = v_x_926_;
v_l_u2082_932_ = v_a_951_;
v_k_u2082_933_ = v_x_928_;
goto v___jp_929_;
}
case 2:
{
lean_object* v_a_952_; lean_object* v_a_953_; lean_object* v_a_954_; lean_object* v_a_955_; uint8_t v___x_956_; 
v_a_952_ = lean_ctor_get(v_x_925_, 0);
v_a_953_ = lean_ctor_get(v_x_925_, 1);
v_a_954_ = lean_ctor_get(v_x_927_, 0);
v_a_955_ = lean_ctor_get(v_x_927_, 1);
v___x_956_ = lean_level_eq(v_x_925_, v_x_927_);
if (v___x_956_ == 0)
{
uint8_t v___x_957_; 
lean_dec(v_x_928_);
lean_dec(v_x_926_);
v___x_957_ = lean_level_eq(v_a_952_, v_a_954_);
if (v___x_957_ == 0)
{
lean_object* v___x_958_; 
v___x_958_ = lean_unsigned_to_nat(0u);
v_x_925_ = v_a_952_;
v_x_926_ = v___x_958_;
v_x_927_ = v_a_954_;
v_x_928_ = v___x_958_;
goto _start;
}
else
{
lean_object* v___x_960_; 
v___x_960_ = lean_unsigned_to_nat(0u);
v_x_925_ = v_a_953_;
v_x_926_ = v___x_960_;
v_x_927_ = v_a_955_;
v_x_928_ = v___x_960_;
goto _start;
}
}
else
{
uint8_t v___x_962_; 
v___x_962_ = lean_nat_dec_lt(v_x_926_, v_x_928_);
lean_dec(v_x_928_);
lean_dec(v_x_926_);
return v___x_962_;
}
}
default: 
{
v_l_u2081_938_ = v_x_925_;
v_k_u2081_939_ = v_x_926_;
v_l_u2082_940_ = v_x_927_;
v_k_u2082_941_ = v_x_928_;
goto v___jp_937_;
}
}
}
case 3:
{
switch(lean_obj_tag(v_x_927_))
{
case 1:
{
lean_object* v_a_963_; 
v_a_963_ = lean_ctor_get(v_x_927_, 0);
v_l_u2081_930_ = v_x_925_;
v_k_u2081_931_ = v_x_926_;
v_l_u2082_932_ = v_a_963_;
v_k_u2082_933_ = v_x_928_;
goto v___jp_929_;
}
case 3:
{
lean_object* v_a_964_; lean_object* v_a_965_; lean_object* v_a_966_; lean_object* v_a_967_; uint8_t v___x_968_; 
v_a_964_ = lean_ctor_get(v_x_925_, 0);
v_a_965_ = lean_ctor_get(v_x_925_, 1);
v_a_966_ = lean_ctor_get(v_x_927_, 0);
v_a_967_ = lean_ctor_get(v_x_927_, 1);
v___x_968_ = lean_level_eq(v_x_925_, v_x_927_);
if (v___x_968_ == 0)
{
uint8_t v___x_969_; 
lean_dec(v_x_928_);
lean_dec(v_x_926_);
v___x_969_ = lean_level_eq(v_a_964_, v_a_966_);
if (v___x_969_ == 0)
{
lean_object* v___x_970_; 
v___x_970_ = lean_unsigned_to_nat(0u);
v_x_925_ = v_a_964_;
v_x_926_ = v___x_970_;
v_x_927_ = v_a_966_;
v_x_928_ = v___x_970_;
goto _start;
}
else
{
lean_object* v___x_972_; 
v___x_972_ = lean_unsigned_to_nat(0u);
v_x_925_ = v_a_965_;
v_x_926_ = v___x_972_;
v_x_927_ = v_a_967_;
v_x_928_ = v___x_972_;
goto _start;
}
}
else
{
uint8_t v___x_974_; 
v___x_974_ = lean_nat_dec_lt(v_x_926_, v_x_928_);
lean_dec(v_x_928_);
lean_dec(v_x_926_);
return v___x_974_;
}
}
default: 
{
v_l_u2081_938_ = v_x_925_;
v_k_u2081_939_ = v_x_926_;
v_l_u2082_940_ = v_x_927_;
v_k_u2082_941_ = v_x_928_;
goto v___jp_937_;
}
}
}
case 4:
{
switch(lean_obj_tag(v_x_927_))
{
case 1:
{
lean_object* v_a_975_; 
v_a_975_ = lean_ctor_get(v_x_927_, 0);
v_l_u2081_930_ = v_x_925_;
v_k_u2081_931_ = v_x_926_;
v_l_u2082_932_ = v_a_975_;
v_k_u2082_933_ = v_x_928_;
goto v___jp_929_;
}
case 4:
{
lean_object* v_a_976_; lean_object* v_a_977_; uint8_t v___x_978_; 
v_a_976_ = lean_ctor_get(v_x_925_, 0);
v_a_977_ = lean_ctor_get(v_x_927_, 0);
v___x_978_ = lean_name_eq(v_a_976_, v_a_977_);
if (v___x_978_ == 0)
{
uint8_t v___x_979_; 
lean_dec(v_x_928_);
lean_dec(v_x_926_);
v___x_979_ = l_Lean_Name_lt(v_a_976_, v_a_977_);
return v___x_979_;
}
else
{
uint8_t v___x_980_; 
v___x_980_ = lean_nat_dec_lt(v_x_926_, v_x_928_);
lean_dec(v_x_928_);
lean_dec(v_x_926_);
return v___x_980_;
}
}
default: 
{
v_l_u2081_938_ = v_x_925_;
v_k_u2081_939_ = v_x_926_;
v_l_u2082_940_ = v_x_927_;
v_k_u2082_941_ = v_x_928_;
goto v___jp_937_;
}
}
}
case 5:
{
switch(lean_obj_tag(v_x_927_))
{
case 1:
{
lean_object* v_a_981_; 
v_a_981_ = lean_ctor_get(v_x_927_, 0);
v_l_u2081_930_ = v_x_925_;
v_k_u2081_931_ = v_x_926_;
v_l_u2082_932_ = v_a_981_;
v_k_u2082_933_ = v_x_928_;
goto v___jp_929_;
}
case 5:
{
lean_object* v_a_982_; lean_object* v_a_983_; uint8_t v___x_984_; 
v_a_982_ = lean_ctor_get(v_x_925_, 0);
v_a_983_ = lean_ctor_get(v_x_927_, 0);
v___x_984_ = lean_name_eq(v_a_982_, v_a_983_);
if (v___x_984_ == 0)
{
uint8_t v___x_985_; 
lean_dec(v_x_928_);
lean_dec(v_x_926_);
v___x_985_ = l_Lean_Name_lt(v_a_982_, v_a_983_);
return v___x_985_;
}
else
{
uint8_t v___x_986_; 
v___x_986_ = lean_nat_dec_lt(v_x_926_, v_x_928_);
lean_dec(v_x_928_);
lean_dec(v_x_926_);
return v___x_986_;
}
}
default: 
{
v_l_u2081_938_ = v_x_925_;
v_k_u2081_939_ = v_x_926_;
v_l_u2082_940_ = v_x_927_;
v_k_u2082_941_ = v_x_928_;
goto v___jp_937_;
}
}
}
default: 
{
if (lean_obj_tag(v_x_927_) == 1)
{
lean_object* v_a_987_; 
v_a_987_ = lean_ctor_get(v_x_927_, 0);
v_l_u2081_930_ = v_x_925_;
v_k_u2081_931_ = v_x_926_;
v_l_u2082_932_ = v_a_987_;
v_k_u2082_933_ = v_x_928_;
goto v___jp_929_;
}
else
{
v_l_u2081_938_ = v_x_925_;
v_k_u2081_939_ = v_x_926_;
v_l_u2082_940_ = v_x_927_;
v_k_u2082_941_ = v_x_928_;
goto v___jp_937_;
}
}
}
v___jp_929_:
{
lean_object* v___x_934_; lean_object* v___x_935_; 
v___x_934_ = lean_unsigned_to_nat(1u);
v___x_935_ = lean_nat_add(v_k_u2082_933_, v___x_934_);
lean_dec(v_k_u2082_933_);
v_x_925_ = v_l_u2081_930_;
v_x_926_ = v_k_u2081_931_;
v_x_927_ = v_l_u2082_932_;
v_x_928_ = v___x_935_;
goto _start;
}
v___jp_937_:
{
uint8_t v___x_942_; 
v___x_942_ = lean_level_eq(v_l_u2081_938_, v_l_u2082_940_);
if (v___x_942_ == 0)
{
lean_object* v___x_943_; lean_object* v___x_944_; uint8_t v___x_945_; 
lean_dec(v_k_u2082_941_);
lean_dec(v_k_u2081_939_);
v___x_943_ = l_Lean_Level_ctorToNat(v_l_u2081_938_);
v___x_944_ = l_Lean_Level_ctorToNat(v_l_u2082_940_);
v___x_945_ = lean_nat_dec_lt(v___x_943_, v___x_944_);
lean_dec(v___x_944_);
lean_dec(v___x_943_);
return v___x_945_;
}
else
{
uint8_t v___x_946_; 
v___x_946_ = lean_nat_dec_lt(v_k_u2081_939_, v_k_u2082_941_);
lean_dec(v_k_u2082_941_);
lean_dec(v_k_u2081_939_);
return v___x_946_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_normLtAux___boxed(lean_object* v_x_988_, lean_object* v_x_989_, lean_object* v_x_990_, lean_object* v_x_991_){
_start:
{
uint8_t v_res_992_; lean_object* v_r_993_; 
v_res_992_ = l_Lean_Level_normLtAux(v_x_988_, v_x_989_, v_x_990_, v_x_991_);
lean_dec(v_x_990_);
lean_dec(v_x_988_);
v_r_993_ = lean_box(v_res_992_);
return v_r_993_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_normLtAux_match__1_splitter___redArg(lean_object* v_x_994_, lean_object* v_x_995_, lean_object* v_x_996_, lean_object* v_x_997_, lean_object* v_h__1_998_, lean_object* v_h__2_999_, lean_object* v_h__3_1000_, lean_object* v_h__4_1001_, lean_object* v_h__5_1002_, lean_object* v_h__6_1003_, lean_object* v_h__7_1004_){
_start:
{
switch(lean_obj_tag(v_x_994_))
{
case 1:
{
lean_object* v_a_1005_; lean_object* v___x_1006_; 
lean_dec(v_h__7_1004_);
lean_dec(v_h__6_1003_);
lean_dec(v_h__5_1002_);
lean_dec(v_h__4_1001_);
lean_dec(v_h__3_1000_);
lean_dec(v_h__2_999_);
v_a_1005_ = lean_ctor_get(v_x_994_, 0);
lean_inc(v_a_1005_);
lean_dec_ref_known(v_x_994_, 1);
v___x_1006_ = lean_apply_4(v_h__1_998_, v_a_1005_, v_x_995_, v_x_996_, v_x_997_);
return v___x_1006_;
}
case 2:
{
lean_dec(v_h__6_1003_);
lean_dec(v_h__5_1002_);
lean_dec(v_h__4_1001_);
lean_dec(v_h__1_998_);
switch(lean_obj_tag(v_x_996_))
{
case 1:
{
lean_object* v_a_1007_; lean_object* v___x_1008_; 
lean_dec(v_h__7_1004_);
lean_dec(v_h__3_1000_);
v_a_1007_ = lean_ctor_get(v_x_996_, 0);
lean_inc(v_a_1007_);
lean_dec_ref_known(v_x_996_, 1);
v___x_1008_ = lean_apply_5(v_h__2_999_, v_x_994_, v_x_995_, v_a_1007_, v_x_997_, lean_box(0));
return v___x_1008_;
}
case 2:
{
lean_object* v_a_1009_; lean_object* v_a_1010_; lean_object* v_a_1011_; lean_object* v_a_1012_; lean_object* v___x_1013_; 
lean_dec(v_h__7_1004_);
lean_dec(v_h__2_999_);
v_a_1009_ = lean_ctor_get(v_x_994_, 0);
lean_inc(v_a_1009_);
v_a_1010_ = lean_ctor_get(v_x_994_, 1);
lean_inc(v_a_1010_);
lean_dec_ref_known(v_x_994_, 2);
v_a_1011_ = lean_ctor_get(v_x_996_, 0);
lean_inc(v_a_1011_);
v_a_1012_ = lean_ctor_get(v_x_996_, 1);
lean_inc(v_a_1012_);
lean_dec_ref_known(v_x_996_, 2);
v___x_1013_ = lean_apply_6(v_h__3_1000_, v_a_1009_, v_a_1010_, v_x_995_, v_a_1011_, v_a_1012_, v_x_997_);
return v___x_1013_;
}
default: 
{
lean_object* v___x_1014_; 
lean_dec(v_h__3_1000_);
lean_dec(v_h__2_999_);
v___x_1014_ = lean_apply_10(v_h__7_1004_, v_x_994_, v_x_995_, v_x_996_, v_x_997_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_1014_;
}
}
}
case 3:
{
lean_dec(v_h__6_1003_);
lean_dec(v_h__5_1002_);
lean_dec(v_h__3_1000_);
lean_dec(v_h__1_998_);
switch(lean_obj_tag(v_x_996_))
{
case 1:
{
lean_object* v_a_1015_; lean_object* v___x_1016_; 
lean_dec(v_h__7_1004_);
lean_dec(v_h__4_1001_);
v_a_1015_ = lean_ctor_get(v_x_996_, 0);
lean_inc(v_a_1015_);
lean_dec_ref_known(v_x_996_, 1);
v___x_1016_ = lean_apply_5(v_h__2_999_, v_x_994_, v_x_995_, v_a_1015_, v_x_997_, lean_box(0));
return v___x_1016_;
}
case 3:
{
lean_object* v_a_1017_; lean_object* v_a_1018_; lean_object* v_a_1019_; lean_object* v_a_1020_; lean_object* v___x_1021_; 
lean_dec(v_h__7_1004_);
lean_dec(v_h__2_999_);
v_a_1017_ = lean_ctor_get(v_x_994_, 0);
lean_inc(v_a_1017_);
v_a_1018_ = lean_ctor_get(v_x_994_, 1);
lean_inc(v_a_1018_);
lean_dec_ref_known(v_x_994_, 2);
v_a_1019_ = lean_ctor_get(v_x_996_, 0);
lean_inc(v_a_1019_);
v_a_1020_ = lean_ctor_get(v_x_996_, 1);
lean_inc(v_a_1020_);
lean_dec_ref_known(v_x_996_, 2);
v___x_1021_ = lean_apply_6(v_h__4_1001_, v_a_1017_, v_a_1018_, v_x_995_, v_a_1019_, v_a_1020_, v_x_997_);
return v___x_1021_;
}
default: 
{
lean_object* v___x_1022_; 
lean_dec(v_h__4_1001_);
lean_dec(v_h__2_999_);
v___x_1022_ = lean_apply_10(v_h__7_1004_, v_x_994_, v_x_995_, v_x_996_, v_x_997_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_1022_;
}
}
}
case 4:
{
lean_dec(v_h__6_1003_);
lean_dec(v_h__4_1001_);
lean_dec(v_h__3_1000_);
lean_dec(v_h__1_998_);
switch(lean_obj_tag(v_x_996_))
{
case 1:
{
lean_object* v_a_1023_; lean_object* v___x_1024_; 
lean_dec(v_h__7_1004_);
lean_dec(v_h__5_1002_);
v_a_1023_ = lean_ctor_get(v_x_996_, 0);
lean_inc(v_a_1023_);
lean_dec_ref_known(v_x_996_, 1);
v___x_1024_ = lean_apply_5(v_h__2_999_, v_x_994_, v_x_995_, v_a_1023_, v_x_997_, lean_box(0));
return v___x_1024_;
}
case 4:
{
lean_object* v_a_1025_; lean_object* v_a_1026_; lean_object* v___x_1027_; 
lean_dec(v_h__7_1004_);
lean_dec(v_h__2_999_);
v_a_1025_ = lean_ctor_get(v_x_994_, 0);
lean_inc(v_a_1025_);
lean_dec_ref_known(v_x_994_, 1);
v_a_1026_ = lean_ctor_get(v_x_996_, 0);
lean_inc(v_a_1026_);
lean_dec_ref_known(v_x_996_, 1);
v___x_1027_ = lean_apply_4(v_h__5_1002_, v_a_1025_, v_x_995_, v_a_1026_, v_x_997_);
return v___x_1027_;
}
default: 
{
lean_object* v___x_1028_; 
lean_dec(v_h__5_1002_);
lean_dec(v_h__2_999_);
v___x_1028_ = lean_apply_10(v_h__7_1004_, v_x_994_, v_x_995_, v_x_996_, v_x_997_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_1028_;
}
}
}
case 5:
{
lean_dec(v_h__5_1002_);
lean_dec(v_h__4_1001_);
lean_dec(v_h__3_1000_);
lean_dec(v_h__1_998_);
switch(lean_obj_tag(v_x_996_))
{
case 1:
{
lean_object* v_a_1029_; lean_object* v___x_1030_; 
lean_dec(v_h__7_1004_);
lean_dec(v_h__6_1003_);
v_a_1029_ = lean_ctor_get(v_x_996_, 0);
lean_inc(v_a_1029_);
lean_dec_ref_known(v_x_996_, 1);
v___x_1030_ = lean_apply_5(v_h__2_999_, v_x_994_, v_x_995_, v_a_1029_, v_x_997_, lean_box(0));
return v___x_1030_;
}
case 5:
{
lean_object* v_a_1031_; lean_object* v_a_1032_; lean_object* v___x_1033_; 
lean_dec(v_h__7_1004_);
lean_dec(v_h__2_999_);
v_a_1031_ = lean_ctor_get(v_x_994_, 0);
lean_inc(v_a_1031_);
lean_dec_ref_known(v_x_994_, 1);
v_a_1032_ = lean_ctor_get(v_x_996_, 0);
lean_inc(v_a_1032_);
lean_dec_ref_known(v_x_996_, 1);
v___x_1033_ = lean_apply_4(v_h__6_1003_, v_a_1031_, v_x_995_, v_a_1032_, v_x_997_);
return v___x_1033_;
}
default: 
{
lean_object* v___x_1034_; 
lean_dec(v_h__6_1003_);
lean_dec(v_h__2_999_);
v___x_1034_ = lean_apply_10(v_h__7_1004_, v_x_994_, v_x_995_, v_x_996_, v_x_997_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_1034_;
}
}
}
default: 
{
lean_dec(v_h__6_1003_);
lean_dec(v_h__5_1002_);
lean_dec(v_h__4_1001_);
lean_dec(v_h__3_1000_);
lean_dec(v_h__1_998_);
if (lean_obj_tag(v_x_996_) == 1)
{
lean_object* v_a_1035_; lean_object* v___x_1036_; 
lean_dec(v_h__7_1004_);
v_a_1035_ = lean_ctor_get(v_x_996_, 0);
lean_inc(v_a_1035_);
lean_dec_ref_known(v_x_996_, 1);
v___x_1036_ = lean_apply_5(v_h__2_999_, v_x_994_, v_x_995_, v_a_1035_, v_x_997_, lean_box(0));
return v___x_1036_;
}
else
{
lean_object* v___x_1037_; 
lean_dec(v_h__2_999_);
v___x_1037_ = lean_apply_10(v_h__7_1004_, v_x_994_, v_x_995_, v_x_996_, v_x_997_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_1037_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_normLtAux_match__1_splitter(lean_object* v_motive_1038_, lean_object* v_x_1039_, lean_object* v_x_1040_, lean_object* v_x_1041_, lean_object* v_x_1042_, lean_object* v_h__1_1043_, lean_object* v_h__2_1044_, lean_object* v_h__3_1045_, lean_object* v_h__4_1046_, lean_object* v_h__5_1047_, lean_object* v_h__6_1048_, lean_object* v_h__7_1049_){
_start:
{
switch(lean_obj_tag(v_x_1039_))
{
case 1:
{
lean_object* v_a_1050_; lean_object* v___x_1051_; 
lean_dec(v_h__7_1049_);
lean_dec(v_h__6_1048_);
lean_dec(v_h__5_1047_);
lean_dec(v_h__4_1046_);
lean_dec(v_h__3_1045_);
lean_dec(v_h__2_1044_);
v_a_1050_ = lean_ctor_get(v_x_1039_, 0);
lean_inc(v_a_1050_);
lean_dec_ref_known(v_x_1039_, 1);
v___x_1051_ = lean_apply_4(v_h__1_1043_, v_a_1050_, v_x_1040_, v_x_1041_, v_x_1042_);
return v___x_1051_;
}
case 2:
{
lean_dec(v_h__6_1048_);
lean_dec(v_h__5_1047_);
lean_dec(v_h__4_1046_);
lean_dec(v_h__1_1043_);
switch(lean_obj_tag(v_x_1041_))
{
case 1:
{
lean_object* v_a_1052_; lean_object* v___x_1053_; 
lean_dec(v_h__7_1049_);
lean_dec(v_h__3_1045_);
v_a_1052_ = lean_ctor_get(v_x_1041_, 0);
lean_inc(v_a_1052_);
lean_dec_ref_known(v_x_1041_, 1);
v___x_1053_ = lean_apply_5(v_h__2_1044_, v_x_1039_, v_x_1040_, v_a_1052_, v_x_1042_, lean_box(0));
return v___x_1053_;
}
case 2:
{
lean_object* v_a_1054_; lean_object* v_a_1055_; lean_object* v_a_1056_; lean_object* v_a_1057_; lean_object* v___x_1058_; 
lean_dec(v_h__7_1049_);
lean_dec(v_h__2_1044_);
v_a_1054_ = lean_ctor_get(v_x_1039_, 0);
lean_inc(v_a_1054_);
v_a_1055_ = lean_ctor_get(v_x_1039_, 1);
lean_inc(v_a_1055_);
lean_dec_ref_known(v_x_1039_, 2);
v_a_1056_ = lean_ctor_get(v_x_1041_, 0);
lean_inc(v_a_1056_);
v_a_1057_ = lean_ctor_get(v_x_1041_, 1);
lean_inc(v_a_1057_);
lean_dec_ref_known(v_x_1041_, 2);
v___x_1058_ = lean_apply_6(v_h__3_1045_, v_a_1054_, v_a_1055_, v_x_1040_, v_a_1056_, v_a_1057_, v_x_1042_);
return v___x_1058_;
}
default: 
{
lean_object* v___x_1059_; 
lean_dec(v_h__3_1045_);
lean_dec(v_h__2_1044_);
v___x_1059_ = lean_apply_10(v_h__7_1049_, v_x_1039_, v_x_1040_, v_x_1041_, v_x_1042_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_1059_;
}
}
}
case 3:
{
lean_dec(v_h__6_1048_);
lean_dec(v_h__5_1047_);
lean_dec(v_h__3_1045_);
lean_dec(v_h__1_1043_);
switch(lean_obj_tag(v_x_1041_))
{
case 1:
{
lean_object* v_a_1060_; lean_object* v___x_1061_; 
lean_dec(v_h__7_1049_);
lean_dec(v_h__4_1046_);
v_a_1060_ = lean_ctor_get(v_x_1041_, 0);
lean_inc(v_a_1060_);
lean_dec_ref_known(v_x_1041_, 1);
v___x_1061_ = lean_apply_5(v_h__2_1044_, v_x_1039_, v_x_1040_, v_a_1060_, v_x_1042_, lean_box(0));
return v___x_1061_;
}
case 3:
{
lean_object* v_a_1062_; lean_object* v_a_1063_; lean_object* v_a_1064_; lean_object* v_a_1065_; lean_object* v___x_1066_; 
lean_dec(v_h__7_1049_);
lean_dec(v_h__2_1044_);
v_a_1062_ = lean_ctor_get(v_x_1039_, 0);
lean_inc(v_a_1062_);
v_a_1063_ = lean_ctor_get(v_x_1039_, 1);
lean_inc(v_a_1063_);
lean_dec_ref_known(v_x_1039_, 2);
v_a_1064_ = lean_ctor_get(v_x_1041_, 0);
lean_inc(v_a_1064_);
v_a_1065_ = lean_ctor_get(v_x_1041_, 1);
lean_inc(v_a_1065_);
lean_dec_ref_known(v_x_1041_, 2);
v___x_1066_ = lean_apply_6(v_h__4_1046_, v_a_1062_, v_a_1063_, v_x_1040_, v_a_1064_, v_a_1065_, v_x_1042_);
return v___x_1066_;
}
default: 
{
lean_object* v___x_1067_; 
lean_dec(v_h__4_1046_);
lean_dec(v_h__2_1044_);
v___x_1067_ = lean_apply_10(v_h__7_1049_, v_x_1039_, v_x_1040_, v_x_1041_, v_x_1042_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_1067_;
}
}
}
case 4:
{
lean_dec(v_h__6_1048_);
lean_dec(v_h__4_1046_);
lean_dec(v_h__3_1045_);
lean_dec(v_h__1_1043_);
switch(lean_obj_tag(v_x_1041_))
{
case 1:
{
lean_object* v_a_1068_; lean_object* v___x_1069_; 
lean_dec(v_h__7_1049_);
lean_dec(v_h__5_1047_);
v_a_1068_ = lean_ctor_get(v_x_1041_, 0);
lean_inc(v_a_1068_);
lean_dec_ref_known(v_x_1041_, 1);
v___x_1069_ = lean_apply_5(v_h__2_1044_, v_x_1039_, v_x_1040_, v_a_1068_, v_x_1042_, lean_box(0));
return v___x_1069_;
}
case 4:
{
lean_object* v_a_1070_; lean_object* v_a_1071_; lean_object* v___x_1072_; 
lean_dec(v_h__7_1049_);
lean_dec(v_h__2_1044_);
v_a_1070_ = lean_ctor_get(v_x_1039_, 0);
lean_inc(v_a_1070_);
lean_dec_ref_known(v_x_1039_, 1);
v_a_1071_ = lean_ctor_get(v_x_1041_, 0);
lean_inc(v_a_1071_);
lean_dec_ref_known(v_x_1041_, 1);
v___x_1072_ = lean_apply_4(v_h__5_1047_, v_a_1070_, v_x_1040_, v_a_1071_, v_x_1042_);
return v___x_1072_;
}
default: 
{
lean_object* v___x_1073_; 
lean_dec(v_h__5_1047_);
lean_dec(v_h__2_1044_);
v___x_1073_ = lean_apply_10(v_h__7_1049_, v_x_1039_, v_x_1040_, v_x_1041_, v_x_1042_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_1073_;
}
}
}
case 5:
{
lean_dec(v_h__5_1047_);
lean_dec(v_h__4_1046_);
lean_dec(v_h__3_1045_);
lean_dec(v_h__1_1043_);
switch(lean_obj_tag(v_x_1041_))
{
case 1:
{
lean_object* v_a_1074_; lean_object* v___x_1075_; 
lean_dec(v_h__7_1049_);
lean_dec(v_h__6_1048_);
v_a_1074_ = lean_ctor_get(v_x_1041_, 0);
lean_inc(v_a_1074_);
lean_dec_ref_known(v_x_1041_, 1);
v___x_1075_ = lean_apply_5(v_h__2_1044_, v_x_1039_, v_x_1040_, v_a_1074_, v_x_1042_, lean_box(0));
return v___x_1075_;
}
case 5:
{
lean_object* v_a_1076_; lean_object* v_a_1077_; lean_object* v___x_1078_; 
lean_dec(v_h__7_1049_);
lean_dec(v_h__2_1044_);
v_a_1076_ = lean_ctor_get(v_x_1039_, 0);
lean_inc(v_a_1076_);
lean_dec_ref_known(v_x_1039_, 1);
v_a_1077_ = lean_ctor_get(v_x_1041_, 0);
lean_inc(v_a_1077_);
lean_dec_ref_known(v_x_1041_, 1);
v___x_1078_ = lean_apply_4(v_h__6_1048_, v_a_1076_, v_x_1040_, v_a_1077_, v_x_1042_);
return v___x_1078_;
}
default: 
{
lean_object* v___x_1079_; 
lean_dec(v_h__6_1048_);
lean_dec(v_h__2_1044_);
v___x_1079_ = lean_apply_10(v_h__7_1049_, v_x_1039_, v_x_1040_, v_x_1041_, v_x_1042_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_1079_;
}
}
}
default: 
{
lean_dec(v_h__6_1048_);
lean_dec(v_h__5_1047_);
lean_dec(v_h__4_1046_);
lean_dec(v_h__3_1045_);
lean_dec(v_h__1_1043_);
if (lean_obj_tag(v_x_1041_) == 1)
{
lean_object* v_a_1080_; lean_object* v___x_1081_; 
lean_dec(v_h__7_1049_);
v_a_1080_ = lean_ctor_get(v_x_1041_, 0);
lean_inc(v_a_1080_);
lean_dec_ref_known(v_x_1041_, 1);
v___x_1081_ = lean_apply_5(v_h__2_1044_, v_x_1039_, v_x_1040_, v_a_1080_, v_x_1042_, lean_box(0));
return v___x_1081_;
}
else
{
lean_object* v___x_1082_; 
lean_dec(v_h__2_1044_);
v___x_1082_ = lean_apply_10(v_h__7_1049_, v_x_1039_, v_x_1040_, v_x_1041_, v_x_1042_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_1082_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Level_normLt(lean_object* v_l_u2081_1083_, lean_object* v_l_u2082_1084_){
_start:
{
lean_object* v___x_1085_; uint8_t v___x_1086_; 
v___x_1085_ = lean_unsigned_to_nat(0u);
v___x_1086_ = l_Lean_Level_normLtAux(v_l_u2081_1083_, v___x_1085_, v_l_u2082_1084_, v___x_1085_);
return v___x_1086_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_normLt___boxed(lean_object* v_l_u2081_1087_, lean_object* v_l_u2082_1088_){
_start:
{
uint8_t v_res_1089_; lean_object* v_r_1090_; 
v_res_1089_ = l_Lean_Level_normLt(v_l_u2081_1087_, v_l_u2082_1088_);
lean_dec(v_l_u2082_1088_);
lean_dec(v_l_u2081_1087_);
v_r_1090_ = lean_box(v_res_1089_);
return v_r_1090_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_isAlreadyNormalizedCheap(lean_object* v_x_1091_){
_start:
{
switch(lean_obj_tag(v_x_1091_))
{
case 0:
{
uint8_t v___x_1092_; 
v___x_1092_ = 1;
return v___x_1092_;
}
case 4:
{
uint8_t v___x_1093_; 
v___x_1093_ = 1;
return v___x_1093_;
}
case 5:
{
uint8_t v___x_1094_; 
v___x_1094_ = 1;
return v___x_1094_;
}
case 1:
{
lean_object* v_a_1095_; 
v_a_1095_ = lean_ctor_get(v_x_1091_, 0);
v_x_1091_ = v_a_1095_;
goto _start;
}
default: 
{
uint8_t v___x_1097_; 
v___x_1097_ = 0;
return v___x_1097_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_isAlreadyNormalizedCheap___boxed(lean_object* v_x_1098_){
_start:
{
uint8_t v_res_1099_; lean_object* v_r_1100_; 
v_res_1099_ = l_Lean_Level_isAlreadyNormalizedCheap(v_x_1098_);
lean_dec(v_x_1098_);
v_r_1100_ = lean_box(v_res_1099_);
return v_r_1100_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_mkIMaxAux(lean_object* v_x_1101_, lean_object* v_x_1102_){
_start:
{
lean_object* v_u_u2081_1104_; lean_object* v_u_u2082_1105_; 
if (lean_obj_tag(v_x_1102_) == 0)
{
lean_dec(v_x_1101_);
return v_x_1102_;
}
else
{
switch(lean_obj_tag(v_x_1101_))
{
case 0:
{
return v_x_1102_;
}
case 1:
{
lean_object* v_a_1108_; 
v_a_1108_ = lean_ctor_get(v_x_1101_, 0);
if (lean_obj_tag(v_a_1108_) == 0)
{
lean_dec_ref_known(v_x_1101_, 1);
return v_x_1102_;
}
else
{
v_u_u2081_1104_ = v_x_1101_;
v_u_u2082_1105_ = v_x_1102_;
goto v___jp_1103_;
}
}
default: 
{
v_u_u2081_1104_ = v_x_1101_;
v_u_u2082_1105_ = v_x_1102_;
goto v___jp_1103_;
}
}
}
v___jp_1103_:
{
uint8_t v___x_1106_; 
v___x_1106_ = lean_level_eq(v_u_u2081_1104_, v_u_u2082_1105_);
if (v___x_1106_ == 0)
{
lean_object* v___x_1107_; 
v___x_1107_ = l_Lean_Level_imax___override(v_u_u2081_1104_, v_u_u2082_1105_);
return v___x_1107_;
}
else
{
lean_dec(v_u_u2082_1105_);
return v_u_u2081_1104_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_getMaxArgsAux(lean_object* v_normalize_1109_, lean_object* v_x_1110_, uint8_t v_x_1111_, lean_object* v_x_1112_){
_start:
{
if (lean_obj_tag(v_x_1110_) == 2)
{
lean_object* v_a_1113_; lean_object* v_a_1114_; lean_object* v___x_1115_; 
v_a_1113_ = lean_ctor_get(v_x_1110_, 0);
lean_inc(v_a_1113_);
v_a_1114_ = lean_ctor_get(v_x_1110_, 1);
lean_inc(v_a_1114_);
lean_dec_ref_known(v_x_1110_, 2);
lean_inc_ref(v_normalize_1109_);
v___x_1115_ = l___private_Lean_Level_0__Lean_Level_getMaxArgsAux(v_normalize_1109_, v_a_1113_, v_x_1111_, v_x_1112_);
v_x_1110_ = v_a_1114_;
v_x_1112_ = v___x_1115_;
goto _start;
}
else
{
if (v_x_1111_ == 0)
{
lean_object* v___x_1117_; uint8_t v___x_1118_; 
lean_inc_ref(v_normalize_1109_);
v___x_1117_ = lean_apply_1(v_normalize_1109_, v_x_1110_);
v___x_1118_ = 1;
v_x_1110_ = v___x_1117_;
v_x_1111_ = v___x_1118_;
goto _start;
}
else
{
lean_object* v___x_1120_; 
lean_dec_ref(v_normalize_1109_);
v___x_1120_ = lean_array_push(v_x_1112_, v_x_1110_);
return v___x_1120_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_getMaxArgsAux___boxed(lean_object* v_normalize_1121_, lean_object* v_x_1122_, lean_object* v_x_1123_, lean_object* v_x_1124_){
_start:
{
uint8_t v_x_31__boxed_1125_; lean_object* v_res_1126_; 
v_x_31__boxed_1125_ = lean_unbox(v_x_1123_);
v_res_1126_ = l___private_Lean_Level_0__Lean_Level_getMaxArgsAux(v_normalize_1121_, v_x_1122_, v_x_31__boxed_1125_, v_x_1124_);
return v_res_1126_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_accMax(lean_object* v_result_1127_, lean_object* v_prev_1128_, lean_object* v_offset_1129_){
_start:
{
uint8_t v___x_1130_; 
v___x_1130_ = l_Lean_Level_isZero(v_result_1127_);
if (v___x_1130_ == 0)
{
lean_object* v___x_1131_; lean_object* v___x_1132_; 
v___x_1131_ = l_Lean_Level_addOffsetAux(v_offset_1129_, v_prev_1128_);
v___x_1132_ = l_Lean_Level_max___override(v_result_1127_, v___x_1131_);
return v___x_1132_;
}
else
{
lean_object* v___x_1133_; 
lean_dec(v_result_1127_);
v___x_1133_ = l_Lean_Level_addOffsetAux(v_offset_1129_, v_prev_1128_);
return v___x_1133_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_mkMaxAux(lean_object* v_lvls_1134_, lean_object* v_extraK_1135_, lean_object* v_i_1136_, lean_object* v_prev_1137_, lean_object* v_prevK_1138_, lean_object* v_result_1139_){
_start:
{
lean_object* v___x_1140_; uint8_t v___x_1141_; 
v___x_1140_ = lean_array_get_size(v_lvls_1134_);
v___x_1141_ = lean_nat_dec_lt(v_i_1136_, v___x_1140_);
if (v___x_1141_ == 0)
{
lean_object* v___x_1142_; lean_object* v___x_1143_; 
lean_dec(v_i_1136_);
v___x_1142_ = lean_nat_add(v_extraK_1135_, v_prevK_1138_);
lean_dec(v_prevK_1138_);
v___x_1143_ = l___private_Lean_Level_0__Lean_Level_accMax(v_result_1139_, v_prev_1137_, v___x_1142_);
return v___x_1143_;
}
else
{
lean_object* v_lvl_1144_; lean_object* v_curr_1145_; lean_object* v_currK_1146_; uint8_t v___x_1147_; 
v_lvl_1144_ = lean_array_fget_borrowed(v_lvls_1134_, v_i_1136_);
v_curr_1145_ = l_Lean_Level_getLevelOffset(v_lvl_1144_);
v_currK_1146_ = l_Lean_Level_getOffset(v_lvl_1144_);
v___x_1147_ = lean_level_eq(v_curr_1145_, v_prev_1137_);
if (v___x_1147_ == 0)
{
lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; 
v___x_1148_ = lean_unsigned_to_nat(1u);
v___x_1149_ = lean_nat_add(v_i_1136_, v___x_1148_);
lean_dec(v_i_1136_);
v___x_1150_ = lean_nat_add(v_extraK_1135_, v_prevK_1138_);
lean_dec(v_prevK_1138_);
v___x_1151_ = l___private_Lean_Level_0__Lean_Level_accMax(v_result_1139_, v_prev_1137_, v___x_1150_);
v_i_1136_ = v___x_1149_;
v_prev_1137_ = v_curr_1145_;
v_prevK_1138_ = v_currK_1146_;
v_result_1139_ = v___x_1151_;
goto _start;
}
else
{
lean_object* v___x_1153_; lean_object* v___x_1154_; 
lean_dec(v_prevK_1138_);
lean_dec(v_prev_1137_);
v___x_1153_ = lean_unsigned_to_nat(1u);
v___x_1154_ = lean_nat_add(v_i_1136_, v___x_1153_);
lean_dec(v_i_1136_);
v_i_1136_ = v___x_1154_;
v_prev_1137_ = v_curr_1145_;
v_prevK_1138_ = v_currK_1146_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_mkMaxAux___boxed(lean_object* v_lvls_1156_, lean_object* v_extraK_1157_, lean_object* v_i_1158_, lean_object* v_prev_1159_, lean_object* v_prevK_1160_, lean_object* v_result_1161_){
_start:
{
lean_object* v_res_1162_; 
v_res_1162_ = l___private_Lean_Level_0__Lean_Level_mkMaxAux(v_lvls_1156_, v_extraK_1157_, v_i_1158_, v_prev_1159_, v_prevK_1160_, v_result_1161_);
lean_dec(v_extraK_1157_);
lean_dec_ref(v_lvls_1156_);
return v_res_1162_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_skipExplicit(lean_object* v_lvls_1163_, lean_object* v_i_1164_){
_start:
{
lean_object* v___x_1165_; uint8_t v___x_1166_; 
v___x_1165_ = lean_array_get_size(v_lvls_1163_);
v___x_1166_ = lean_nat_dec_lt(v_i_1164_, v___x_1165_);
if (v___x_1166_ == 0)
{
return v_i_1164_;
}
else
{
lean_object* v_lvl_1167_; lean_object* v___x_1168_; uint8_t v___x_1169_; 
v_lvl_1167_ = lean_array_fget_borrowed(v_lvls_1163_, v_i_1164_);
v___x_1168_ = l_Lean_Level_getLevelOffset(v_lvl_1167_);
v___x_1169_ = l_Lean_Level_isZero(v___x_1168_);
lean_dec(v___x_1168_);
if (v___x_1169_ == 0)
{
return v_i_1164_;
}
else
{
lean_object* v___x_1170_; lean_object* v___x_1171_; 
v___x_1170_ = lean_unsigned_to_nat(1u);
v___x_1171_ = lean_nat_add(v_i_1164_, v___x_1170_);
lean_dec(v_i_1164_);
v_i_1164_ = v___x_1171_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_skipExplicit___boxed(lean_object* v_lvls_1173_, lean_object* v_i_1174_){
_start:
{
lean_object* v_res_1175_; 
v_res_1175_ = l___private_Lean_Level_0__Lean_Level_skipExplicit(v_lvls_1173_, v_i_1174_);
lean_dec_ref(v_lvls_1173_);
return v_res_1175_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Level_0__Lean_Level_isExplicitSubsumedAux(lean_object* v_lvls_1176_, lean_object* v_maxExplicit_1177_, lean_object* v_i_1178_){
_start:
{
lean_object* v___x_1179_; uint8_t v___x_1180_; 
v___x_1179_ = lean_array_get_size(v_lvls_1176_);
v___x_1180_ = lean_nat_dec_lt(v_i_1178_, v___x_1179_);
if (v___x_1180_ == 0)
{
lean_dec(v_i_1178_);
return v___x_1180_;
}
else
{
lean_object* v_lvl_1181_; lean_object* v___x_1182_; uint8_t v___x_1183_; 
v_lvl_1181_ = lean_array_fget_borrowed(v_lvls_1176_, v_i_1178_);
v___x_1182_ = l_Lean_Level_getOffset(v_lvl_1181_);
v___x_1183_ = lean_nat_dec_le(v_maxExplicit_1177_, v___x_1182_);
lean_dec(v___x_1182_);
if (v___x_1183_ == 0)
{
lean_object* v___x_1184_; lean_object* v___x_1185_; 
v___x_1184_ = lean_unsigned_to_nat(1u);
v___x_1185_ = lean_nat_add(v_i_1178_, v___x_1184_);
lean_dec(v_i_1178_);
v_i_1178_ = v___x_1185_;
goto _start;
}
else
{
lean_dec(v_i_1178_);
return v___x_1183_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_isExplicitSubsumedAux___boxed(lean_object* v_lvls_1187_, lean_object* v_maxExplicit_1188_, lean_object* v_i_1189_){
_start:
{
uint8_t v_res_1190_; lean_object* v_r_1191_; 
v_res_1190_ = l___private_Lean_Level_0__Lean_Level_isExplicitSubsumedAux(v_lvls_1187_, v_maxExplicit_1188_, v_i_1189_);
lean_dec(v_maxExplicit_1188_);
lean_dec_ref(v_lvls_1187_);
v_r_1191_ = lean_box(v_res_1190_);
return v_r_1191_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Level_0__Lean_Level_isExplicitSubsumed(lean_object* v_lvls_1192_, lean_object* v_firstNonExplicit_1193_){
_start:
{
lean_object* v___x_1194_; uint8_t v___x_1195_; 
v___x_1194_ = lean_unsigned_to_nat(0u);
v___x_1195_ = lean_nat_dec_eq(v_firstNonExplicit_1193_, v___x_1194_);
if (v___x_1195_ == 0)
{
lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v_max_1200_; uint8_t v___x_1201_; 
v___x_1196_ = lean_box(0);
v___x_1197_ = lean_unsigned_to_nat(1u);
v___x_1198_ = lean_nat_sub(v_firstNonExplicit_1193_, v___x_1197_);
v___x_1199_ = lean_array_get_borrowed(v___x_1196_, v_lvls_1192_, v___x_1198_);
lean_dec(v___x_1198_);
v_max_1200_ = l_Lean_Level_getOffset(v___x_1199_);
v___x_1201_ = l___private_Lean_Level_0__Lean_Level_isExplicitSubsumedAux(v_lvls_1192_, v_max_1200_, v_firstNonExplicit_1193_);
lean_dec(v_max_1200_);
return v___x_1201_;
}
else
{
uint8_t v___x_1202_; 
lean_dec(v_firstNonExplicit_1193_);
v___x_1202_ = 0;
return v___x_1202_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_isExplicitSubsumed___boxed(lean_object* v_lvls_1203_, lean_object* v_firstNonExplicit_1204_){
_start:
{
uint8_t v_res_1205_; lean_object* v_r_1206_; 
v_res_1205_ = l___private_Lean_Level_0__Lean_Level_isExplicitSubsumed(v_lvls_1203_, v_firstNonExplicit_1204_);
lean_dec_ref(v_lvls_1203_);
v_r_1206_ = lean_box(v_res_1205_);
return v_r_1206_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Level_normalize_spec__2(lean_object* v_msg_1207_){
_start:
{
lean_object* v___x_1208_; lean_object* v___x_1209_; 
v___x_1208_ = lean_box(0);
v___x_1209_ = lean_panic_fn_borrowed(v___x_1208_, v_msg_1207_);
return v___x_1209_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1_spec__1___redArg(lean_object* v_hi_1210_, lean_object* v_pivot_1211_, lean_object* v_as_1212_, lean_object* v_i_1213_, lean_object* v_k_1214_){
_start:
{
uint8_t v___x_1215_; 
v___x_1215_ = lean_nat_dec_lt(v_k_1214_, v_hi_1210_);
if (v___x_1215_ == 0)
{
lean_object* v___x_1216_; lean_object* v___x_1217_; 
lean_dec(v_k_1214_);
v___x_1216_ = lean_array_fswap(v_as_1212_, v_i_1213_, v_hi_1210_);
v___x_1217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1217_, 0, v_i_1213_);
lean_ctor_set(v___x_1217_, 1, v___x_1216_);
return v___x_1217_;
}
else
{
lean_object* v___x_1218_; uint8_t v___x_1219_; 
v___x_1218_ = lean_array_fget_borrowed(v_as_1212_, v_k_1214_);
v___x_1219_ = l_Lean_Level_normLt(v___x_1218_, v_pivot_1211_);
if (v___x_1219_ == 0)
{
lean_object* v___x_1220_; lean_object* v___x_1221_; 
v___x_1220_ = lean_unsigned_to_nat(1u);
v___x_1221_ = lean_nat_add(v_k_1214_, v___x_1220_);
lean_dec(v_k_1214_);
v_k_1214_ = v___x_1221_;
goto _start;
}
else
{
lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; 
v___x_1223_ = lean_array_fswap(v_as_1212_, v_i_1213_, v_k_1214_);
v___x_1224_ = lean_unsigned_to_nat(1u);
v___x_1225_ = lean_nat_add(v_i_1213_, v___x_1224_);
lean_dec(v_i_1213_);
v___x_1226_ = lean_nat_add(v_k_1214_, v___x_1224_);
lean_dec(v_k_1214_);
v_as_1212_ = v___x_1223_;
v_i_1213_ = v___x_1225_;
v_k_1214_ = v___x_1226_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1_spec__1___redArg___boxed(lean_object* v_hi_1228_, lean_object* v_pivot_1229_, lean_object* v_as_1230_, lean_object* v_i_1231_, lean_object* v_k_1232_){
_start:
{
lean_object* v_res_1233_; 
v_res_1233_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1_spec__1___redArg(v_hi_1228_, v_pivot_1229_, v_as_1230_, v_i_1231_, v_k_1232_);
lean_dec(v_pivot_1229_);
lean_dec(v_hi_1228_);
return v_res_1233_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1___redArg(lean_object* v_n_1234_, lean_object* v_as_1235_, lean_object* v_lo_1236_, lean_object* v_hi_1237_){
_start:
{
lean_object* v___y_1239_; uint8_t v___x_1249_; 
v___x_1249_ = lean_nat_dec_lt(v_lo_1236_, v_hi_1237_);
if (v___x_1249_ == 0)
{
lean_dec(v_lo_1236_);
return v_as_1235_;
}
else
{
lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v_mid_1252_; lean_object* v___y_1254_; lean_object* v___y_1260_; lean_object* v___x_1265_; lean_object* v___x_1266_; uint8_t v___x_1267_; 
v___x_1250_ = lean_nat_add(v_lo_1236_, v_hi_1237_);
v___x_1251_ = lean_unsigned_to_nat(1u);
v_mid_1252_ = lean_nat_shiftr(v___x_1250_, v___x_1251_);
lean_dec(v___x_1250_);
v___x_1265_ = lean_array_fget_borrowed(v_as_1235_, v_mid_1252_);
v___x_1266_ = lean_array_fget_borrowed(v_as_1235_, v_lo_1236_);
v___x_1267_ = l_Lean_Level_normLt(v___x_1265_, v___x_1266_);
if (v___x_1267_ == 0)
{
v___y_1260_ = v_as_1235_;
goto v___jp_1259_;
}
else
{
lean_object* v___x_1268_; 
v___x_1268_ = lean_array_fswap(v_as_1235_, v_lo_1236_, v_mid_1252_);
v___y_1260_ = v___x_1268_;
goto v___jp_1259_;
}
v___jp_1253_:
{
lean_object* v___x_1255_; lean_object* v___x_1256_; uint8_t v___x_1257_; 
v___x_1255_ = lean_array_fget_borrowed(v___y_1254_, v_mid_1252_);
v___x_1256_ = lean_array_fget_borrowed(v___y_1254_, v_hi_1237_);
v___x_1257_ = l_Lean_Level_normLt(v___x_1255_, v___x_1256_);
if (v___x_1257_ == 0)
{
lean_dec(v_mid_1252_);
v___y_1239_ = v___y_1254_;
goto v___jp_1238_;
}
else
{
lean_object* v___x_1258_; 
v___x_1258_ = lean_array_fswap(v___y_1254_, v_mid_1252_, v_hi_1237_);
lean_dec(v_mid_1252_);
v___y_1239_ = v___x_1258_;
goto v___jp_1238_;
}
}
v___jp_1259_:
{
lean_object* v___x_1261_; lean_object* v___x_1262_; uint8_t v___x_1263_; 
v___x_1261_ = lean_array_fget_borrowed(v___y_1260_, v_hi_1237_);
v___x_1262_ = lean_array_fget_borrowed(v___y_1260_, v_lo_1236_);
v___x_1263_ = l_Lean_Level_normLt(v___x_1261_, v___x_1262_);
if (v___x_1263_ == 0)
{
v___y_1254_ = v___y_1260_;
goto v___jp_1253_;
}
else
{
lean_object* v___x_1264_; 
v___x_1264_ = lean_array_fswap(v___y_1260_, v_lo_1236_, v_hi_1237_);
v___y_1254_ = v___x_1264_;
goto v___jp_1253_;
}
}
}
v___jp_1238_:
{
lean_object* v_pivot_1240_; lean_object* v___x_1241_; lean_object* v_fst_1242_; lean_object* v_snd_1243_; uint8_t v___x_1244_; 
v_pivot_1240_ = lean_array_fget(v___y_1239_, v_hi_1237_);
lean_inc_n(v_lo_1236_, 2);
v___x_1241_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1_spec__1___redArg(v_hi_1237_, v_pivot_1240_, v___y_1239_, v_lo_1236_, v_lo_1236_);
lean_dec(v_pivot_1240_);
v_fst_1242_ = lean_ctor_get(v___x_1241_, 0);
lean_inc(v_fst_1242_);
v_snd_1243_ = lean_ctor_get(v___x_1241_, 1);
lean_inc(v_snd_1243_);
lean_dec_ref(v___x_1241_);
v___x_1244_ = lean_nat_dec_le(v_hi_1237_, v_fst_1242_);
if (v___x_1244_ == 0)
{
lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; 
v___x_1245_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1___redArg(v_n_1234_, v_snd_1243_, v_lo_1236_, v_fst_1242_);
v___x_1246_ = lean_unsigned_to_nat(1u);
v___x_1247_ = lean_nat_add(v_fst_1242_, v___x_1246_);
lean_dec(v_fst_1242_);
v_as_1235_ = v___x_1245_;
v_lo_1236_ = v___x_1247_;
goto _start;
}
else
{
lean_dec(v_fst_1242_);
lean_dec(v_lo_1236_);
return v_snd_1243_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1___redArg___boxed(lean_object* v_n_1269_, lean_object* v_as_1270_, lean_object* v_lo_1271_, lean_object* v_hi_1272_){
_start:
{
lean_object* v_res_1273_; 
v_res_1273_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1___redArg(v_n_1269_, v_as_1270_, v_lo_1271_, v_hi_1272_);
lean_dec(v_hi_1272_);
lean_dec(v_n_1269_);
return v_res_1273_;
}
}
static lean_object* _init_l_Lean_Level_normalize___closed__3(void){
_start:
{
lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; 
v___x_1278_ = ((lean_object*)(l_Lean_Level_normalize___closed__2));
v___x_1279_ = lean_unsigned_to_nat(11u);
v___x_1280_ = lean_unsigned_to_nat(403u);
v___x_1281_ = ((lean_object*)(l_Lean_Level_normalize___closed__1));
v___x_1282_ = ((lean_object*)(l_Lean_Level_mvarId_x21___closed__0));
v___x_1283_ = l_mkPanicMessageWithDecl(v___x_1282_, v___x_1281_, v___x_1280_, v___x_1279_, v___x_1278_);
return v___x_1283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_normalize(lean_object* v_l_1284_){
_start:
{
uint8_t v___x_1285_; 
v___x_1285_ = l_Lean_Level_isAlreadyNormalizedCheap(v_l_1284_);
if (v___x_1285_ == 0)
{
lean_object* v_k_1286_; lean_object* v_u_1287_; 
v_k_1286_ = l_Lean_Level_getOffset(v_l_1284_);
v_u_1287_ = l_Lean_Level_getLevelOffset(v_l_1284_);
switch(lean_obj_tag(v_u_1287_))
{
case 2:
{
lean_object* v_a_1288_; lean_object* v_a_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v_lvls_1293_; lean_object* v_lvls_1294_; lean_object* v___x_1295_; lean_object* v___y_1297_; lean_object* v___y_1298_; lean_object* v___y_1305_; lean_object* v___x_1309_; lean_object* v___y_1311_; lean_object* v___y_1312_; uint8_t v___x_1314_; 
v_a_1288_ = lean_ctor_get(v_u_1287_, 0);
lean_inc(v_a_1288_);
v_a_1289_ = lean_ctor_get(v_u_1287_, 1);
lean_inc(v_a_1289_);
lean_dec_ref_known(v_u_1287_, 2);
v___x_1290_ = lean_box(0);
v___x_1291_ = lean_unsigned_to_nat(0u);
v___x_1292_ = ((lean_object*)(l_Lean_Level_normalize___closed__0));
v_lvls_1293_ = l___private_Lean_Level_0__Lean_Level_getMaxArgsAux___at___00Lean_Level_normalize_spec__0(v_a_1288_, v___x_1285_, v___x_1292_);
v_lvls_1294_ = l___private_Lean_Level_0__Lean_Level_getMaxArgsAux___at___00Lean_Level_normalize_spec__0(v_a_1289_, v___x_1285_, v_lvls_1293_);
v___x_1295_ = lean_unsigned_to_nat(1u);
v___x_1309_ = lean_array_get_size(v_lvls_1294_);
v___x_1314_ = lean_nat_dec_eq(v___x_1309_, v___x_1291_);
if (v___x_1314_ == 0)
{
lean_object* v___x_1315_; lean_object* v___y_1317_; uint8_t v___x_1319_; 
v___x_1315_ = lean_nat_sub(v___x_1309_, v___x_1295_);
v___x_1319_ = lean_nat_dec_le(v___x_1291_, v___x_1315_);
if (v___x_1319_ == 0)
{
lean_inc(v___x_1315_);
v___y_1317_ = v___x_1315_;
goto v___jp_1316_;
}
else
{
v___y_1317_ = v___x_1291_;
goto v___jp_1316_;
}
v___jp_1316_:
{
uint8_t v___x_1318_; 
v___x_1318_ = lean_nat_dec_le(v___y_1317_, v___x_1315_);
if (v___x_1318_ == 0)
{
lean_dec(v___x_1315_);
lean_inc(v___y_1317_);
v___y_1311_ = v___y_1317_;
v___y_1312_ = v___y_1317_;
goto v___jp_1310_;
}
else
{
v___y_1311_ = v___y_1317_;
v___y_1312_ = v___x_1315_;
goto v___jp_1310_;
}
}
}
else
{
v___y_1305_ = v_lvls_1294_;
goto v___jp_1304_;
}
v___jp_1296_:
{
lean_object* v_lvl_u2081_1299_; lean_object* v_prev_1300_; lean_object* v_prevK_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; 
v_lvl_u2081_1299_ = lean_array_get_borrowed(v___x_1290_, v___y_1297_, v___y_1298_);
v_prev_1300_ = l_Lean_Level_getLevelOffset(v_lvl_u2081_1299_);
v_prevK_1301_ = l_Lean_Level_getOffset(v_lvl_u2081_1299_);
v___x_1302_ = lean_nat_add(v___y_1298_, v___x_1295_);
lean_dec(v___y_1298_);
v___x_1303_ = l___private_Lean_Level_0__Lean_Level_mkMaxAux(v___y_1297_, v_k_1286_, v___x_1302_, v_prev_1300_, v_prevK_1301_, v___x_1290_);
lean_dec(v_k_1286_);
lean_dec_ref(v___y_1297_);
return v___x_1303_;
}
v___jp_1304_:
{
lean_object* v_firstNonExplicit_1306_; uint8_t v___x_1307_; 
v_firstNonExplicit_1306_ = l___private_Lean_Level_0__Lean_Level_skipExplicit(v___y_1305_, v___x_1291_);
lean_inc(v_firstNonExplicit_1306_);
v___x_1307_ = l___private_Lean_Level_0__Lean_Level_isExplicitSubsumed(v___y_1305_, v_firstNonExplicit_1306_);
if (v___x_1307_ == 0)
{
lean_object* v___x_1308_; 
v___x_1308_ = lean_nat_sub(v_firstNonExplicit_1306_, v___x_1295_);
lean_dec(v_firstNonExplicit_1306_);
v___y_1297_ = v___y_1305_;
v___y_1298_ = v___x_1308_;
goto v___jp_1296_;
}
else
{
v___y_1297_ = v___y_1305_;
v___y_1298_ = v_firstNonExplicit_1306_;
goto v___jp_1296_;
}
}
v___jp_1310_:
{
lean_object* v___x_1313_; 
v___x_1313_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1___redArg(v___x_1309_, v_lvls_1294_, v___y_1311_, v___y_1312_);
lean_dec(v___y_1312_);
v___y_1305_ = v___x_1313_;
goto v___jp_1304_;
}
}
case 3:
{
lean_object* v_a_1320_; lean_object* v_a_1321_; uint8_t v___x_1322_; 
v_a_1320_ = lean_ctor_get(v_u_1287_, 0);
lean_inc(v_a_1320_);
v_a_1321_ = lean_ctor_get(v_u_1287_, 1);
lean_inc(v_a_1321_);
lean_dec_ref_known(v_u_1287_, 2);
v___x_1322_ = l_Lean_Level_isNeverZero(v_a_1321_);
if (v___x_1322_ == 0)
{
lean_object* v_l_u2081_1323_; lean_object* v_l_u2082_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; 
v_l_u2081_1323_ = l_Lean_Level_normalize(v_a_1320_);
lean_dec(v_a_1320_);
v_l_u2082_1324_ = l_Lean_Level_normalize(v_a_1321_);
lean_dec(v_a_1321_);
v___x_1325_ = l___private_Lean_Level_0__Lean_Level_mkIMaxAux(v_l_u2081_1323_, v_l_u2082_1324_);
v___x_1326_ = l_Lean_Level_addOffsetAux(v_k_1286_, v___x_1325_);
return v___x_1326_;
}
else
{
lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; 
v___x_1327_ = l_Lean_Level_max___override(v_a_1320_, v_a_1321_);
v___x_1328_ = l_Lean_Level_normalize(v___x_1327_);
lean_dec(v___x_1327_);
v___x_1329_ = l_Lean_Level_addOffsetAux(v_k_1286_, v___x_1328_);
return v___x_1329_;
}
}
default: 
{
lean_object* v___x_1330_; lean_object* v___x_1331_; 
lean_dec(v_u_1287_);
lean_dec(v_k_1286_);
v___x_1330_ = lean_obj_once(&l_Lean_Level_normalize___closed__3, &l_Lean_Level_normalize___closed__3_once, _init_l_Lean_Level_normalize___closed__3);
v___x_1331_ = l_panic___at___00Lean_Level_normalize_spec__2(v___x_1330_);
return v___x_1331_;
}
}
}
else
{
lean_inc(v_l_1284_);
return v_l_1284_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_getMaxArgsAux___at___00Lean_Level_normalize_spec__0(lean_object* v_x_1332_, uint8_t v_x_1333_, lean_object* v_x_1334_){
_start:
{
if (lean_obj_tag(v_x_1332_) == 2)
{
lean_object* v_a_1335_; lean_object* v_a_1336_; lean_object* v___x_1337_; 
v_a_1335_ = lean_ctor_get(v_x_1332_, 0);
lean_inc(v_a_1335_);
v_a_1336_ = lean_ctor_get(v_x_1332_, 1);
lean_inc(v_a_1336_);
lean_dec_ref_known(v_x_1332_, 2);
v___x_1337_ = l___private_Lean_Level_0__Lean_Level_getMaxArgsAux___at___00Lean_Level_normalize_spec__0(v_a_1335_, v_x_1333_, v_x_1334_);
v_x_1332_ = v_a_1336_;
v_x_1334_ = v___x_1337_;
goto _start;
}
else
{
if (v_x_1333_ == 0)
{
lean_object* v___x_1339_; uint8_t v___x_1340_; 
v___x_1339_ = l_Lean_Level_normalize(v_x_1332_);
lean_dec(v_x_1332_);
v___x_1340_ = 1;
v_x_1332_ = v___x_1339_;
v_x_1333_ = v___x_1340_;
goto _start;
}
else
{
lean_object* v___x_1342_; 
v___x_1342_ = lean_array_push(v_x_1334_, v_x_1332_);
return v___x_1342_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_getMaxArgsAux___at___00Lean_Level_normalize_spec__0___boxed(lean_object* v_x_1343_, lean_object* v_x_1344_, lean_object* v_x_1345_){
_start:
{
uint8_t v_x_483__boxed_1346_; lean_object* v_res_1347_; 
v_x_483__boxed_1346_ = lean_unbox(v_x_1344_);
v_res_1347_ = l___private_Lean_Level_0__Lean_Level_getMaxArgsAux___at___00Lean_Level_normalize_spec__0(v_x_1343_, v_x_483__boxed_1346_, v_x_1345_);
return v_res_1347_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_normalize___boxed(lean_object* v_l_1348_){
_start:
{
lean_object* v_res_1349_; 
v_res_1349_ = l_Lean_Level_normalize(v_l_1348_);
lean_dec(v_l_1348_);
return v_res_1349_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1(lean_object* v_n_1350_, lean_object* v_as_1351_, lean_object* v_lo_1352_, lean_object* v_hi_1353_, lean_object* v_w_1354_, lean_object* v_hlo_1355_, lean_object* v_hhi_1356_){
_start:
{
lean_object* v___x_1357_; 
v___x_1357_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1___redArg(v_n_1350_, v_as_1351_, v_lo_1352_, v_hi_1353_);
return v___x_1357_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1___boxed(lean_object* v_n_1358_, lean_object* v_as_1359_, lean_object* v_lo_1360_, lean_object* v_hi_1361_, lean_object* v_w_1362_, lean_object* v_hlo_1363_, lean_object* v_hhi_1364_){
_start:
{
lean_object* v_res_1365_; 
v_res_1365_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1(v_n_1358_, v_as_1359_, v_lo_1360_, v_hi_1361_, v_w_1362_, v_hlo_1363_, v_hhi_1364_);
lean_dec(v_hi_1361_);
lean_dec(v_n_1358_);
return v_res_1365_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1_spec__1(lean_object* v_n_1366_, lean_object* v_lo_1367_, lean_object* v_hi_1368_, lean_object* v_hhi_1369_, lean_object* v_pivot_1370_, lean_object* v_as_1371_, lean_object* v_i_1372_, lean_object* v_k_1373_, lean_object* v_ilo_1374_, lean_object* v_ik_1375_, lean_object* v_w_1376_){
_start:
{
lean_object* v___x_1377_; 
v___x_1377_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1_spec__1___redArg(v_hi_1368_, v_pivot_1370_, v_as_1371_, v_i_1372_, v_k_1373_);
return v___x_1377_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1_spec__1___boxed(lean_object* v_n_1378_, lean_object* v_lo_1379_, lean_object* v_hi_1380_, lean_object* v_hhi_1381_, lean_object* v_pivot_1382_, lean_object* v_as_1383_, lean_object* v_i_1384_, lean_object* v_k_1385_, lean_object* v_ilo_1386_, lean_object* v_ik_1387_, lean_object* v_w_1388_){
_start:
{
lean_object* v_res_1389_; 
v_res_1389_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1_spec__1(v_n_1378_, v_lo_1379_, v_hi_1380_, v_hhi_1381_, v_pivot_1382_, v_as_1383_, v_i_1384_, v_k_1385_, v_ilo_1386_, v_ik_1387_, v_w_1388_);
lean_dec(v_pivot_1382_);
lean_dec(v_hi_1380_);
lean_dec(v_lo_1379_);
lean_dec(v_n_1378_);
return v_res_1389_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_isEquiv(lean_object* v_u_1390_, lean_object* v_v_1391_){
_start:
{
uint8_t v___x_1392_; 
v___x_1392_ = lean_level_eq(v_u_1390_, v_v_1391_);
if (v___x_1392_ == 0)
{
lean_object* v___x_1393_; lean_object* v___x_1394_; uint8_t v___x_1395_; 
v___x_1393_ = l_Lean_Level_normalize(v_u_1390_);
v___x_1394_ = l_Lean_Level_normalize(v_v_1391_);
v___x_1395_ = lean_level_eq(v___x_1393_, v___x_1394_);
lean_dec(v___x_1394_);
lean_dec(v___x_1393_);
return v___x_1395_;
}
else
{
return v___x_1392_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_isEquiv___boxed(lean_object* v_u_1396_, lean_object* v_v_1397_){
_start:
{
uint8_t v_res_1398_; lean_object* v_r_1399_; 
v_res_1398_ = l_Lean_Level_isEquiv(v_u_1396_, v_v_1397_);
lean_dec(v_v_1397_);
lean_dec(v_u_1396_);
v_r_1399_ = lean_box(v_res_1398_);
return v_r_1399_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_dec(lean_object* v_x_1400_){
_start:
{
lean_object* v_l_u2081_1402_; lean_object* v_l_u2082_1403_; 
switch(lean_obj_tag(v_x_1400_))
{
case 1:
{
lean_object* v_a_1416_; lean_object* v___x_1417_; 
v_a_1416_ = lean_ctor_get(v_x_1400_, 0);
lean_inc(v_a_1416_);
v___x_1417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1417_, 0, v_a_1416_);
return v___x_1417_;
}
case 2:
{
lean_object* v_a_1418_; lean_object* v_a_1419_; 
v_a_1418_ = lean_ctor_get(v_x_1400_, 0);
v_a_1419_ = lean_ctor_get(v_x_1400_, 1);
v_l_u2081_1402_ = v_a_1418_;
v_l_u2082_1403_ = v_a_1419_;
goto v___jp_1401_;
}
case 3:
{
lean_object* v_a_1420_; lean_object* v_a_1421_; 
v_a_1420_ = lean_ctor_get(v_x_1400_, 0);
v_a_1421_ = lean_ctor_get(v_x_1400_, 1);
v_l_u2081_1402_ = v_a_1420_;
v_l_u2082_1403_ = v_a_1421_;
goto v___jp_1401_;
}
default: 
{
lean_object* v___x_1422_; 
v___x_1422_ = lean_box(0);
return v___x_1422_;
}
}
v___jp_1401_:
{
lean_object* v___x_1404_; 
v___x_1404_ = l_Lean_Level_dec(v_l_u2081_1402_);
if (lean_obj_tag(v___x_1404_) == 0)
{
return v___x_1404_;
}
else
{
lean_object* v_val_1405_; lean_object* v___x_1406_; 
v_val_1405_ = lean_ctor_get(v___x_1404_, 0);
lean_inc(v_val_1405_);
lean_dec_ref_known(v___x_1404_, 1);
v___x_1406_ = l_Lean_Level_dec(v_l_u2082_1403_);
if (lean_obj_tag(v___x_1406_) == 0)
{
lean_dec(v_val_1405_);
return v___x_1406_;
}
else
{
lean_object* v_val_1407_; lean_object* v___x_1409_; uint8_t v_isShared_1410_; uint8_t v_isSharedCheck_1415_; 
v_val_1407_ = lean_ctor_get(v___x_1406_, 0);
v_isSharedCheck_1415_ = !lean_is_exclusive(v___x_1406_);
if (v_isSharedCheck_1415_ == 0)
{
v___x_1409_ = v___x_1406_;
v_isShared_1410_ = v_isSharedCheck_1415_;
goto v_resetjp_1408_;
}
else
{
lean_inc(v_val_1407_);
lean_dec(v___x_1406_);
v___x_1409_ = lean_box(0);
v_isShared_1410_ = v_isSharedCheck_1415_;
goto v_resetjp_1408_;
}
v_resetjp_1408_:
{
lean_object* v___x_1411_; lean_object* v___x_1413_; 
v___x_1411_ = l_Lean_Level_max___override(v_val_1405_, v_val_1407_);
if (v_isShared_1410_ == 0)
{
lean_ctor_set(v___x_1409_, 0, v___x_1411_);
v___x_1413_ = v___x_1409_;
goto v_reusejp_1412_;
}
else
{
lean_object* v_reuseFailAlloc_1414_; 
v_reuseFailAlloc_1414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1414_, 0, v___x_1411_);
v___x_1413_ = v_reuseFailAlloc_1414_;
goto v_reusejp_1412_;
}
v_reusejp_1412_:
{
return v___x_1413_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_dec___boxed(lean_object* v_x_1423_){
_start:
{
lean_object* v_res_1424_; 
v_res_1424_ = l_Lean_Level_dec(v_x_1423_);
lean_dec(v_x_1423_);
return v_res_1424_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_ctorIdx___impl(lean_object* v_x_1425_){
_start:
{
lean_object* v___x_1426_; 
v___x_1426_ = lean_obj_tag_nat(v_x_1425_);
return v___x_1426_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_ctorIdx___impl___boxed(lean_object* v_x_1427_){
_start:
{
lean_object* v_res_1428_; 
v_res_1428_ = l_Lean_Level_PP_Result_ctorIdx___impl(v_x_1427_);
lean_dec_ref(v_x_1427_);
return v_res_1428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_ctorElim___redArg(lean_object* v_t_1429_, lean_object* v_k_1430_){
_start:
{
if (lean_obj_tag(v_t_1429_) == 2)
{
lean_object* v_a_1431_; lean_object* v_a_1432_; lean_object* v___x_1433_; 
v_a_1431_ = lean_ctor_get(v_t_1429_, 0);
lean_inc_ref(v_a_1431_);
v_a_1432_ = lean_ctor_get(v_t_1429_, 1);
lean_inc(v_a_1432_);
lean_dec_ref_known(v_t_1429_, 2);
v___x_1433_ = lean_apply_2(v_k_1430_, v_a_1431_, v_a_1432_);
return v___x_1433_;
}
else
{
lean_object* v_a_1434_; lean_object* v___x_1435_; 
v_a_1434_ = lean_ctor_get(v_t_1429_, 0);
lean_inc(v_a_1434_);
lean_dec_ref(v_t_1429_);
v___x_1435_ = lean_apply_1(v_k_1430_, v_a_1434_);
return v___x_1435_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_ctorElim(lean_object* v_motive__1_1436_, lean_object* v_ctorIdx_1437_, lean_object* v_t_1438_, lean_object* v_h_1439_, lean_object* v_k_1440_){
_start:
{
lean_object* v___x_1441_; 
v___x_1441_ = l_Lean_Level_PP_Result_ctorElim___redArg(v_t_1438_, v_k_1440_);
return v___x_1441_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_ctorElim___boxed(lean_object* v_motive__1_1442_, lean_object* v_ctorIdx_1443_, lean_object* v_t_1444_, lean_object* v_h_1445_, lean_object* v_k_1446_){
_start:
{
lean_object* v_res_1447_; 
v_res_1447_ = l_Lean_Level_PP_Result_ctorElim(v_motive__1_1442_, v_ctorIdx_1443_, v_t_1444_, v_h_1445_, v_k_1446_);
lean_dec(v_ctorIdx_1443_);
return v_res_1447_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_leaf_elim___redArg(lean_object* v_t_1448_, lean_object* v_leaf_1449_){
_start:
{
lean_object* v___x_1450_; 
v___x_1450_ = l_Lean_Level_PP_Result_ctorElim___redArg(v_t_1448_, v_leaf_1449_);
return v___x_1450_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_leaf_elim(lean_object* v_motive__1_1451_, lean_object* v_t_1452_, lean_object* v_h_1453_, lean_object* v_leaf_1454_){
_start:
{
lean_object* v___x_1455_; 
v___x_1455_ = l_Lean_Level_PP_Result_ctorElim___redArg(v_t_1452_, v_leaf_1454_);
return v___x_1455_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_num_elim___redArg(lean_object* v_t_1456_, lean_object* v_num_1457_){
_start:
{
lean_object* v___x_1458_; 
v___x_1458_ = l_Lean_Level_PP_Result_ctorElim___redArg(v_t_1456_, v_num_1457_);
return v___x_1458_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_num_elim(lean_object* v_motive__1_1459_, lean_object* v_t_1460_, lean_object* v_h_1461_, lean_object* v_num_1462_){
_start:
{
lean_object* v___x_1463_; 
v___x_1463_ = l_Lean_Level_PP_Result_ctorElim___redArg(v_t_1460_, v_num_1462_);
return v___x_1463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_offset_elim___redArg(lean_object* v_t_1464_, lean_object* v_offset_1465_){
_start:
{
lean_object* v___x_1466_; 
v___x_1466_ = l_Lean_Level_PP_Result_ctorElim___redArg(v_t_1464_, v_offset_1465_);
return v___x_1466_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_offset_elim(lean_object* v_motive__1_1467_, lean_object* v_t_1468_, lean_object* v_h_1469_, lean_object* v_offset_1470_){
_start:
{
lean_object* v___x_1471_; 
v___x_1471_ = l_Lean_Level_PP_Result_ctorElim___redArg(v_t_1468_, v_offset_1470_);
return v___x_1471_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_maxNode_elim___redArg(lean_object* v_t_1472_, lean_object* v_maxNode_1473_){
_start:
{
lean_object* v___x_1474_; 
v___x_1474_ = l_Lean_Level_PP_Result_ctorElim___redArg(v_t_1472_, v_maxNode_1473_);
return v___x_1474_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_maxNode_elim(lean_object* v_motive__1_1475_, lean_object* v_t_1476_, lean_object* v_h_1477_, lean_object* v_maxNode_1478_){
_start:
{
lean_object* v___x_1479_; 
v___x_1479_ = l_Lean_Level_PP_Result_ctorElim___redArg(v_t_1476_, v_maxNode_1478_);
return v___x_1479_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_imaxNode_elim___redArg(lean_object* v_t_1480_, lean_object* v_imaxNode_1481_){
_start:
{
lean_object* v___x_1482_; 
v___x_1482_ = l_Lean_Level_PP_Result_ctorElim___redArg(v_t_1480_, v_imaxNode_1481_);
return v___x_1482_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_imaxNode_elim(lean_object* v_motive__1_1483_, lean_object* v_t_1484_, lean_object* v_h_1485_, lean_object* v_imaxNode_1486_){
_start:
{
lean_object* v___x_1487_; 
v___x_1487_ = l_Lean_Level_PP_Result_ctorElim___redArg(v_t_1484_, v_imaxNode_1486_);
return v___x_1487_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_succ(lean_object* v_x_1488_){
_start:
{
switch(lean_obj_tag(v_x_1488_))
{
case 2:
{
lean_object* v_a_1489_; lean_object* v_a_1490_; lean_object* v___x_1492_; uint8_t v_isShared_1493_; uint8_t v_isSharedCheck_1499_; 
v_a_1489_ = lean_ctor_get(v_x_1488_, 0);
v_a_1490_ = lean_ctor_get(v_x_1488_, 1);
v_isSharedCheck_1499_ = !lean_is_exclusive(v_x_1488_);
if (v_isSharedCheck_1499_ == 0)
{
v___x_1492_ = v_x_1488_;
v_isShared_1493_ = v_isSharedCheck_1499_;
goto v_resetjp_1491_;
}
else
{
lean_inc(v_a_1490_);
lean_inc(v_a_1489_);
lean_dec(v_x_1488_);
v___x_1492_ = lean_box(0);
v_isShared_1493_ = v_isSharedCheck_1499_;
goto v_resetjp_1491_;
}
v_resetjp_1491_:
{
lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1497_; 
v___x_1494_ = lean_unsigned_to_nat(1u);
v___x_1495_ = lean_nat_add(v_a_1490_, v___x_1494_);
lean_dec(v_a_1490_);
if (v_isShared_1493_ == 0)
{
lean_ctor_set(v___x_1492_, 1, v___x_1495_);
v___x_1497_ = v___x_1492_;
goto v_reusejp_1496_;
}
else
{
lean_object* v_reuseFailAlloc_1498_; 
v_reuseFailAlloc_1498_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1498_, 0, v_a_1489_);
lean_ctor_set(v_reuseFailAlloc_1498_, 1, v___x_1495_);
v___x_1497_ = v_reuseFailAlloc_1498_;
goto v_reusejp_1496_;
}
v_reusejp_1496_:
{
return v___x_1497_;
}
}
}
case 1:
{
lean_object* v_a_1500_; lean_object* v___x_1502_; uint8_t v_isShared_1503_; uint8_t v_isSharedCheck_1509_; 
v_a_1500_ = lean_ctor_get(v_x_1488_, 0);
v_isSharedCheck_1509_ = !lean_is_exclusive(v_x_1488_);
if (v_isSharedCheck_1509_ == 0)
{
v___x_1502_ = v_x_1488_;
v_isShared_1503_ = v_isSharedCheck_1509_;
goto v_resetjp_1501_;
}
else
{
lean_inc(v_a_1500_);
lean_dec(v_x_1488_);
v___x_1502_ = lean_box(0);
v_isShared_1503_ = v_isSharedCheck_1509_;
goto v_resetjp_1501_;
}
v_resetjp_1501_:
{
lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1507_; 
v___x_1504_ = lean_unsigned_to_nat(1u);
v___x_1505_ = lean_nat_add(v_a_1500_, v___x_1504_);
lean_dec(v_a_1500_);
if (v_isShared_1503_ == 0)
{
lean_ctor_set(v___x_1502_, 0, v___x_1505_);
v___x_1507_ = v___x_1502_;
goto v_reusejp_1506_;
}
else
{
lean_object* v_reuseFailAlloc_1508_; 
v_reuseFailAlloc_1508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1508_, 0, v___x_1505_);
v___x_1507_ = v_reuseFailAlloc_1508_;
goto v_reusejp_1506_;
}
v_reusejp_1506_:
{
return v___x_1507_;
}
}
}
default: 
{
lean_object* v___x_1510_; lean_object* v___x_1511_; 
v___x_1510_ = lean_unsigned_to_nat(1u);
v___x_1511_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1511_, 0, v_x_1488_);
lean_ctor_set(v___x_1511_, 1, v___x_1510_);
return v___x_1511_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_max(lean_object* v_x_1512_, lean_object* v_x_1513_){
_start:
{
if (lean_obj_tag(v_x_1513_) == 3)
{
lean_object* v_a_1514_; lean_object* v___x_1516_; uint8_t v_isShared_1517_; uint8_t v_isSharedCheck_1522_; 
v_a_1514_ = lean_ctor_get(v_x_1513_, 0);
v_isSharedCheck_1522_ = !lean_is_exclusive(v_x_1513_);
if (v_isSharedCheck_1522_ == 0)
{
v___x_1516_ = v_x_1513_;
v_isShared_1517_ = v_isSharedCheck_1522_;
goto v_resetjp_1515_;
}
else
{
lean_inc(v_a_1514_);
lean_dec(v_x_1513_);
v___x_1516_ = lean_box(0);
v_isShared_1517_ = v_isSharedCheck_1522_;
goto v_resetjp_1515_;
}
v_resetjp_1515_:
{
lean_object* v___x_1518_; lean_object* v___x_1520_; 
v___x_1518_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1518_, 0, v_x_1512_);
lean_ctor_set(v___x_1518_, 1, v_a_1514_);
if (v_isShared_1517_ == 0)
{
lean_ctor_set(v___x_1516_, 0, v___x_1518_);
v___x_1520_ = v___x_1516_;
goto v_reusejp_1519_;
}
else
{
lean_object* v_reuseFailAlloc_1521_; 
v_reuseFailAlloc_1521_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1521_, 0, v___x_1518_);
v___x_1520_ = v_reuseFailAlloc_1521_;
goto v_reusejp_1519_;
}
v_reusejp_1519_:
{
return v___x_1520_;
}
}
}
else
{
lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; 
v___x_1523_ = lean_box(0);
v___x_1524_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1524_, 0, v_x_1513_);
lean_ctor_set(v___x_1524_, 1, v___x_1523_);
v___x_1525_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1525_, 0, v_x_1512_);
lean_ctor_set(v___x_1525_, 1, v___x_1524_);
v___x_1526_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1526_, 0, v___x_1525_);
return v___x_1526_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_imax(lean_object* v_x_1527_, lean_object* v_x_1528_){
_start:
{
if (lean_obj_tag(v_x_1528_) == 4)
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
v_reuseFailAlloc_1536_ = lean_alloc_ctor(4, 1, 0);
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
v___x_1541_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1541_, 0, v___x_1540_);
return v___x_1541_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_toResult(lean_object* v_l_1560_, lean_object* v_a_1561_){
_start:
{
switch(lean_obj_tag(v_l_1560_))
{
case 0:
{
lean_object* v___x_1562_; 
v___x_1562_ = ((lean_object*)(l_Lean_Level_PP_toResult___closed__0));
return v___x_1562_;
}
case 1:
{
lean_object* v_a_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; 
v_a_1563_ = lean_ctor_get(v_l_1560_, 0);
lean_inc(v_a_1563_);
lean_dec_ref_known(v_l_1560_, 1);
v___x_1564_ = l_Lean_Level_PP_toResult(v_a_1563_, v_a_1561_);
v___x_1565_ = l_Lean_Level_PP_Result_succ(v___x_1564_);
return v___x_1565_;
}
case 2:
{
lean_object* v_a_1566_; lean_object* v_a_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; 
v_a_1566_ = lean_ctor_get(v_l_1560_, 0);
lean_inc(v_a_1566_);
v_a_1567_ = lean_ctor_get(v_l_1560_, 1);
lean_inc(v_a_1567_);
lean_dec_ref_known(v_l_1560_, 2);
v___x_1568_ = l_Lean_Level_PP_toResult(v_a_1566_, v_a_1561_);
v___x_1569_ = l_Lean_Level_PP_toResult(v_a_1567_, v_a_1561_);
v___x_1570_ = l_Lean_Level_PP_Result_max(v___x_1568_, v___x_1569_);
return v___x_1570_;
}
case 3:
{
lean_object* v_a_1571_; lean_object* v_a_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; 
v_a_1571_ = lean_ctor_get(v_l_1560_, 0);
lean_inc(v_a_1571_);
v_a_1572_ = lean_ctor_get(v_l_1560_, 1);
lean_inc(v_a_1572_);
lean_dec_ref_known(v_l_1560_, 2);
v___x_1573_ = l_Lean_Level_PP_toResult(v_a_1571_, v_a_1561_);
v___x_1574_ = l_Lean_Level_PP_toResult(v_a_1572_, v_a_1561_);
v___x_1575_ = l_Lean_Level_PP_Result_imax(v___x_1573_, v___x_1574_);
return v___x_1575_;
}
case 4:
{
lean_object* v_a_1576_; lean_object* v___x_1577_; 
v_a_1576_ = lean_ctor_get(v_l_1560_, 0);
lean_inc(v_a_1576_);
lean_dec_ref_known(v_l_1560_, 1);
v___x_1577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1577_, 0, v_a_1576_);
return v___x_1577_;
}
default: 
{
uint8_t v_mvars_1578_; 
v_mvars_1578_ = lean_ctor_get_uint8(v_a_1561_, sizeof(void*)*1);
if (v_mvars_1578_ == 0)
{
lean_object* v___x_1579_; 
lean_dec_ref_known(v_l_1560_, 1);
v___x_1579_ = ((lean_object*)(l_Lean_Level_PP_toResult___closed__3));
return v___x_1579_;
}
else
{
lean_object* v_a_1580_; lean_object* v_lIndex_x3f_1581_; lean_object* v___x_1582_; 
v_a_1580_ = lean_ctor_get(v_l_1560_, 0);
lean_inc_n(v_a_1580_, 2);
lean_dec_ref_known(v_l_1560_, 1);
v_lIndex_x3f_1581_ = lean_ctor_get(v_a_1561_, 0);
lean_inc_ref(v_lIndex_x3f_1581_);
v___x_1582_ = lean_apply_1(v_lIndex_x3f_1581_, v_a_1580_);
if (lean_obj_tag(v___x_1582_) == 1)
{
lean_object* v_val_1583_; lean_object* v___x_1585_; uint8_t v_isShared_1586_; uint8_t v_isSharedCheck_1594_; 
lean_dec(v_a_1580_);
v_val_1583_ = lean_ctor_get(v___x_1582_, 0);
v_isSharedCheck_1594_ = !lean_is_exclusive(v___x_1582_);
if (v_isSharedCheck_1594_ == 0)
{
v___x_1585_ = v___x_1582_;
v_isShared_1586_ = v_isSharedCheck_1594_;
goto v_resetjp_1584_;
}
else
{
lean_inc(v_val_1583_);
lean_dec(v___x_1582_);
v___x_1585_ = lean_box(0);
v_isShared_1586_ = v_isSharedCheck_1594_;
goto v_resetjp_1584_;
}
v_resetjp_1584_:
{
lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1592_; 
v___x_1587_ = ((lean_object*)(l_Lean_Level_PP_toResult___closed__5));
v___x_1588_ = lean_unsigned_to_nat(1u);
v___x_1589_ = lean_nat_add(v_val_1583_, v___x_1588_);
lean_dec(v_val_1583_);
v___x_1590_ = l_Lean_Name_num___override(v___x_1587_, v___x_1589_);
if (v_isShared_1586_ == 0)
{
lean_ctor_set_tag(v___x_1585_, 0);
lean_ctor_set(v___x_1585_, 0, v___x_1590_);
v___x_1592_ = v___x_1585_;
goto v_reusejp_1591_;
}
else
{
lean_object* v_reuseFailAlloc_1593_; 
v_reuseFailAlloc_1593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1593_, 0, v___x_1590_);
v___x_1592_ = v_reuseFailAlloc_1593_;
goto v_reusejp_1591_;
}
v_reusejp_1591_:
{
return v___x_1592_;
}
}
}
else
{
lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; 
lean_dec(v___x_1582_);
v___x_1595_ = ((lean_object*)(l_Lean_Level_PP_toResult___closed__7));
v___x_1596_ = ((lean_object*)(l_Lean_Level_PP_toResult___closed__9));
v___x_1597_ = l_Lean_Name_replacePrefix(v_a_1580_, v___x_1595_, v___x_1596_);
v___x_1598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1598_, 0, v___x_1597_);
return v___x_1598_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_toResult___boxed(lean_object* v_l_1599_, lean_object* v_a_1600_){
_start:
{
lean_object* v_res_1601_; 
v_res_1601_ = l_Lean_Level_PP_toResult(v_l_1599_, v_a_1600_);
lean_dec_ref(v_a_1600_);
return v_res_1601_;
}
}
static lean_object* _init_l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__1(void){
_start:
{
lean_object* v___x_1603_; lean_object* v___x_1604_; 
v___x_1603_ = ((lean_object*)(l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__0));
v___x_1604_ = lean_string_length(v___x_1603_);
return v___x_1604_;
}
}
static lean_object* _init_l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__2(void){
_start:
{
lean_object* v___x_1605_; lean_object* v___x_1606_; 
v___x_1605_ = lean_obj_once(&l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__1, &l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__1_once, _init_l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__1);
v___x_1606_ = lean_nat_to_int(v___x_1605_);
return v___x_1606_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse(lean_object* v_x_1611_, uint8_t v_x_1612_){
_start:
{
if (v_x_1612_ == 0)
{
lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; uint8_t v___x_1619_; lean_object* v___x_1620_; 
v___x_1613_ = lean_obj_once(&l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__2, &l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__2_once, _init_l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__2);
v___x_1614_ = ((lean_object*)(l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__3));
v___x_1615_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1615_, 0, v___x_1614_);
lean_ctor_set(v___x_1615_, 1, v_x_1611_);
v___x_1616_ = ((lean_object*)(l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__4));
v___x_1617_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1617_, 0, v___x_1615_);
lean_ctor_set(v___x_1617_, 1, v___x_1616_);
v___x_1618_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1618_, 0, v___x_1613_);
lean_ctor_set(v___x_1618_, 1, v___x_1617_);
v___x_1619_ = 0;
v___x_1620_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1620_, 0, v___x_1618_);
lean_ctor_set_uint8(v___x_1620_, sizeof(void*)*1, v___x_1619_);
return v___x_1620_;
}
else
{
return v_x_1611_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___boxed(lean_object* v_x_1621_, lean_object* v_x_1622_){
_start:
{
uint8_t v_x_57__boxed_1623_; lean_object* v_res_1624_; 
v_x_57__boxed_1623_ = lean_unbox(v_x_1622_);
v_res_1624_ = l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse(v_x_1621_, v_x_57__boxed_1623_);
return v_res_1624_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_format(lean_object* v_x_1634_, uint8_t v_x_1635_){
_start:
{
switch(lean_obj_tag(v_x_1634_))
{
case 0:
{
lean_object* v_a_1636_; lean_object* v___x_1638_; uint8_t v_isShared_1639_; uint8_t v_isSharedCheck_1645_; 
v_a_1636_ = lean_ctor_get(v_x_1634_, 0);
v_isSharedCheck_1645_ = !lean_is_exclusive(v_x_1634_);
if (v_isSharedCheck_1645_ == 0)
{
v___x_1638_ = v_x_1634_;
v_isShared_1639_ = v_isSharedCheck_1645_;
goto v_resetjp_1637_;
}
else
{
lean_inc(v_a_1636_);
lean_dec(v_x_1634_);
v___x_1638_ = lean_box(0);
v_isShared_1639_ = v_isSharedCheck_1645_;
goto v_resetjp_1637_;
}
v_resetjp_1637_:
{
uint8_t v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1643_; 
v___x_1640_ = 1;
v___x_1641_ = l_Lean_Name_toString(v_a_1636_, v___x_1640_);
if (v_isShared_1639_ == 0)
{
lean_ctor_set_tag(v___x_1638_, 3);
lean_ctor_set(v___x_1638_, 0, v___x_1641_);
v___x_1643_ = v___x_1638_;
goto v_reusejp_1642_;
}
else
{
lean_object* v_reuseFailAlloc_1644_; 
v_reuseFailAlloc_1644_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1644_, 0, v___x_1641_);
v___x_1643_ = v_reuseFailAlloc_1644_;
goto v_reusejp_1642_;
}
v_reusejp_1642_:
{
return v___x_1643_;
}
}
}
case 1:
{
lean_object* v_a_1646_; lean_object* v___x_1648_; uint8_t v_isShared_1649_; uint8_t v_isSharedCheck_1654_; 
v_a_1646_ = lean_ctor_get(v_x_1634_, 0);
v_isSharedCheck_1654_ = !lean_is_exclusive(v_x_1634_);
if (v_isSharedCheck_1654_ == 0)
{
v___x_1648_ = v_x_1634_;
v_isShared_1649_ = v_isSharedCheck_1654_;
goto v_resetjp_1647_;
}
else
{
lean_inc(v_a_1646_);
lean_dec(v_x_1634_);
v___x_1648_ = lean_box(0);
v_isShared_1649_ = v_isSharedCheck_1654_;
goto v_resetjp_1647_;
}
v_resetjp_1647_:
{
lean_object* v___x_1650_; lean_object* v___x_1652_; 
v___x_1650_ = l_Nat_reprFast(v_a_1646_);
if (v_isShared_1649_ == 0)
{
lean_ctor_set_tag(v___x_1648_, 3);
lean_ctor_set(v___x_1648_, 0, v___x_1650_);
v___x_1652_ = v___x_1648_;
goto v_reusejp_1651_;
}
else
{
lean_object* v_reuseFailAlloc_1653_; 
v_reuseFailAlloc_1653_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1653_, 0, v___x_1650_);
v___x_1652_ = v_reuseFailAlloc_1653_;
goto v_reusejp_1651_;
}
v_reusejp_1651_:
{
return v___x_1652_;
}
}
}
case 2:
{
lean_object* v_a_1655_; lean_object* v_a_1656_; lean_object* v___x_1658_; uint8_t v_isShared_1659_; uint8_t v_isSharedCheck_1675_; 
v_a_1655_ = lean_ctor_get(v_x_1634_, 0);
v_a_1656_ = lean_ctor_get(v_x_1634_, 1);
v_isSharedCheck_1675_ = !lean_is_exclusive(v_x_1634_);
if (v_isSharedCheck_1675_ == 0)
{
v___x_1658_ = v_x_1634_;
v_isShared_1659_ = v_isSharedCheck_1675_;
goto v_resetjp_1657_;
}
else
{
lean_inc(v_a_1656_);
lean_inc(v_a_1655_);
lean_dec(v_x_1634_);
v___x_1658_ = lean_box(0);
v_isShared_1659_ = v_isSharedCheck_1675_;
goto v_resetjp_1657_;
}
v_resetjp_1657_:
{
lean_object* v_zero_1660_; uint8_t v_isZero_1661_; 
v_zero_1660_ = lean_unsigned_to_nat(0u);
v_isZero_1661_ = lean_nat_dec_eq(v_a_1656_, v_zero_1660_);
if (v_isZero_1661_ == 1)
{
lean_del_object(v___x_1658_);
lean_dec(v_a_1656_);
v_x_1634_ = v_a_1655_;
goto _start;
}
else
{
lean_object* v_one_1663_; lean_object* v_n_1664_; lean_object* v_f_x27_1665_; lean_object* v___x_1666_; lean_object* v___x_1668_; 
v_one_1663_ = lean_unsigned_to_nat(1u);
v_n_1664_ = lean_nat_sub(v_a_1656_, v_one_1663_);
lean_dec(v_a_1656_);
v_f_x27_1665_ = l_Lean_Level_PP_Result_format(v_a_1655_, v_isZero_1661_);
v___x_1666_ = ((lean_object*)(l_Lean_Level_PP_Result_format___closed__1));
if (v_isShared_1659_ == 0)
{
lean_ctor_set_tag(v___x_1658_, 5);
lean_ctor_set(v___x_1658_, 1, v___x_1666_);
lean_ctor_set(v___x_1658_, 0, v_f_x27_1665_);
v___x_1668_ = v___x_1658_;
goto v_reusejp_1667_;
}
else
{
lean_object* v_reuseFailAlloc_1674_; 
v_reuseFailAlloc_1674_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1674_, 0, v_f_x27_1665_);
lean_ctor_set(v_reuseFailAlloc_1674_, 1, v___x_1666_);
v___x_1668_ = v_reuseFailAlloc_1674_;
goto v_reusejp_1667_;
}
v_reusejp_1667_:
{
lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; 
v___x_1669_ = lean_nat_add(v_n_1664_, v_one_1663_);
lean_dec(v_n_1664_);
v___x_1670_ = l_Nat_reprFast(v___x_1669_);
v___x_1671_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1671_, 0, v___x_1670_);
v___x_1672_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1672_, 0, v___x_1668_);
lean_ctor_set(v___x_1672_, 1, v___x_1671_);
v___x_1673_ = l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse(v___x_1672_, v_x_1635_);
return v___x_1673_;
}
}
}
}
case 3:
{
lean_object* v_a_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; uint8_t v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; 
v_a_1676_ = lean_ctor_get(v_x_1634_, 0);
lean_inc(v_a_1676_);
lean_dec_ref_known(v_x_1634_, 1);
v___x_1677_ = ((lean_object*)(l_Lean_Level_PP_Result_format___closed__3));
v___x_1678_ = l___private_Lean_Level_0__Lean_Level_PP_Result_formatLst(v_a_1676_);
v___x_1679_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1679_, 0, v___x_1677_);
lean_ctor_set(v___x_1679_, 1, v___x_1678_);
v___x_1680_ = 0;
v___x_1681_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1681_, 0, v___x_1679_);
lean_ctor_set_uint8(v___x_1681_, sizeof(void*)*1, v___x_1680_);
v___x_1682_ = l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse(v___x_1681_, v_x_1635_);
return v___x_1682_;
}
default: 
{
lean_object* v_a_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; uint8_t v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; 
v_a_1683_ = lean_ctor_get(v_x_1634_, 0);
lean_inc(v_a_1683_);
lean_dec_ref_known(v_x_1634_, 1);
v___x_1684_ = ((lean_object*)(l_Lean_Level_PP_Result_format___closed__5));
v___x_1685_ = l___private_Lean_Level_0__Lean_Level_PP_Result_formatLst(v_a_1683_);
v___x_1686_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1686_, 0, v___x_1684_);
lean_ctor_set(v___x_1686_, 1, v___x_1685_);
v___x_1687_ = 0;
v___x_1688_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1688_, 0, v___x_1686_);
lean_ctor_set_uint8(v___x_1688_, sizeof(void*)*1, v___x_1687_);
v___x_1689_ = l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse(v___x_1688_, v_x_1635_);
return v___x_1689_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_PP_Result_formatLst(lean_object* v_x_1690_){
_start:
{
if (lean_obj_tag(v_x_1690_) == 0)
{
lean_object* v___x_1691_; 
v___x_1691_ = lean_box(0);
return v___x_1691_;
}
else
{
lean_object* v_head_1692_; lean_object* v_tail_1693_; lean_object* v___x_1695_; uint8_t v_isShared_1696_; uint8_t v_isSharedCheck_1705_; 
v_head_1692_ = lean_ctor_get(v_x_1690_, 0);
v_tail_1693_ = lean_ctor_get(v_x_1690_, 1);
v_isSharedCheck_1705_ = !lean_is_exclusive(v_x_1690_);
if (v_isSharedCheck_1705_ == 0)
{
v___x_1695_ = v_x_1690_;
v_isShared_1696_ = v_isSharedCheck_1705_;
goto v_resetjp_1694_;
}
else
{
lean_inc(v_tail_1693_);
lean_inc(v_head_1692_);
lean_dec(v_x_1690_);
v___x_1695_ = lean_box(0);
v_isShared_1696_ = v_isSharedCheck_1705_;
goto v_resetjp_1694_;
}
v_resetjp_1694_:
{
lean_object* v___x_1697_; uint8_t v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1701_; 
v___x_1697_ = lean_box(1);
v___x_1698_ = 0;
v___x_1699_ = l_Lean_Level_PP_Result_format(v_head_1692_, v___x_1698_);
if (v_isShared_1696_ == 0)
{
lean_ctor_set_tag(v___x_1695_, 5);
lean_ctor_set(v___x_1695_, 1, v___x_1699_);
lean_ctor_set(v___x_1695_, 0, v___x_1697_);
v___x_1701_ = v___x_1695_;
goto v_reusejp_1700_;
}
else
{
lean_object* v_reuseFailAlloc_1704_; 
v_reuseFailAlloc_1704_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1704_, 0, v___x_1697_);
lean_ctor_set(v_reuseFailAlloc_1704_, 1, v___x_1699_);
v___x_1701_ = v_reuseFailAlloc_1704_;
goto v_reusejp_1700_;
}
v_reusejp_1700_:
{
lean_object* v___x_1702_; lean_object* v___x_1703_; 
v___x_1702_ = l___private_Lean_Level_0__Lean_Level_PP_Result_formatLst(v_tail_1693_);
v___x_1703_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1703_, 0, v___x_1701_);
lean_ctor_set(v___x_1703_, 1, v___x_1702_);
return v___x_1703_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_format___boxed(lean_object* v_x_1706_, lean_object* v_x_1707_){
_start:
{
uint8_t v_x_270__boxed_1708_; lean_object* v_res_1709_; 
v_x_270__boxed_1708_ = lean_unbox(v_x_1707_);
v_res_1709_ = l_Lean_Level_PP_Result_format(v_x_1706_, v_x_270__boxed_1708_);
return v_res_1709_;
}
}
static lean_object* _init_l_Lean_Level_PP_Result_quote___closed__0(void){
_start:
{
uint8_t v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; 
v___x_1710_ = 0;
v___x_1711_ = lean_box(0);
v___x_1712_ = l_Lean_SourceInfo_fromRef(v___x_1711_, v___x_1710_);
return v___x_1712_;
}
}
static lean_object* _init_l_Lean_Level_PP_Result_quote___closed__6(void){
_start:
{
lean_object* v___x_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; 
v___x_1722_ = ((lean_object*)(l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__0));
v___x_1723_ = lean_obj_once(&l_Lean_Level_PP_Result_quote___closed__0, &l_Lean_Level_PP_Result_quote___closed__0_once, _init_l_Lean_Level_PP_Result_quote___closed__0);
v___x_1724_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1724_, 0, v___x_1723_);
lean_ctor_set(v___x_1724_, 1, v___x_1722_);
return v___x_1724_;
}
}
static lean_object* _init_l_Lean_Level_PP_Result_quote___closed__7(void){
_start:
{
lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; 
v___x_1725_ = ((lean_object*)(l_Lean_instReprData___lam__0___closed__2));
v___x_1726_ = lean_obj_once(&l_Lean_Level_PP_Result_quote___closed__0, &l_Lean_Level_PP_Result_quote___closed__0_once, _init_l_Lean_Level_PP_Result_quote___closed__0);
v___x_1727_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1727_, 0, v___x_1726_);
lean_ctor_set(v___x_1727_, 1, v___x_1725_);
return v___x_1727_;
}
}
static lean_object* _init_l_Lean_Level_PP_Result_quote___closed__12(void){
_start:
{
lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; 
v___x_1740_ = ((lean_object*)(l_Lean_Level_PP_Result_format___closed__2));
v___x_1741_ = lean_obj_once(&l_Lean_Level_PP_Result_quote___closed__0, &l_Lean_Level_PP_Result_quote___closed__0_once, _init_l_Lean_Level_PP_Result_quote___closed__0);
v___x_1742_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1742_, 0, v___x_1741_);
lean_ctor_set(v___x_1742_, 1, v___x_1740_);
return v___x_1742_;
}
}
static lean_object* _init_l_Lean_Level_PP_Result_quote___closed__15(void){
_start:
{
lean_object* v___x_1746_; 
v___x_1746_ = l_Array_mkArray0___redArg();
return v___x_1746_;
}
}
static lean_object* _init_l_Lean_Level_PP_Result_quote___closed__17(void){
_start:
{
lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; 
v___x_1752_ = ((lean_object*)(l_Lean_Level_PP_Result_format___closed__4));
v___x_1753_ = lean_obj_once(&l_Lean_Level_PP_Result_quote___closed__0, &l_Lean_Level_PP_Result_quote___closed__0_once, _init_l_Lean_Level_PP_Result_quote___closed__0);
v___x_1754_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1754_, 0, v___x_1753_);
lean_ctor_set(v___x_1754_, 1, v___x_1752_);
return v___x_1754_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_quote(lean_object* v_r_1755_, lean_object* v_prec_1756_){
_start:
{
lean_object* v_s_1758_; 
switch(lean_obj_tag(v_r_1755_))
{
case 0:
{
lean_object* v_a_1766_; lean_object* v___x_1767_; 
v_a_1766_ = lean_ctor_get(v_r_1755_, 0);
lean_inc(v_a_1766_);
lean_dec_ref_known(v_r_1755_, 1);
v___x_1767_ = l_Lean_mkIdent(v_a_1766_);
return v___x_1767_;
}
case 1:
{
lean_object* v_a_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; 
v_a_1768_ = lean_ctor_get(v_r_1755_, 0);
lean_inc(v_a_1768_);
lean_dec_ref_known(v_r_1755_, 1);
v___x_1769_ = l_Nat_reprFast(v_a_1768_);
v___x_1770_ = lean_box(2);
v___x_1771_ = l_Lean_Syntax_mkNumLit(v___x_1769_, v___x_1770_);
return v___x_1771_;
}
case 2:
{
lean_object* v_a_1772_; lean_object* v_a_1773_; lean_object* v___x_1775_; uint8_t v_isShared_1776_; uint8_t v_isSharedCheck_1796_; 
v_a_1772_ = lean_ctor_get(v_r_1755_, 0);
v_a_1773_ = lean_ctor_get(v_r_1755_, 1);
v_isSharedCheck_1796_ = !lean_is_exclusive(v_r_1755_);
if (v_isSharedCheck_1796_ == 0)
{
v___x_1775_ = v_r_1755_;
v_isShared_1776_ = v_isSharedCheck_1796_;
goto v_resetjp_1774_;
}
else
{
lean_inc(v_a_1773_);
lean_inc(v_a_1772_);
lean_dec(v_r_1755_);
v___x_1775_ = lean_box(0);
v_isShared_1776_ = v_isSharedCheck_1796_;
goto v_resetjp_1774_;
}
v_resetjp_1774_:
{
lean_object* v_zero_1777_; uint8_t v_isZero_1778_; 
v_zero_1777_ = lean_unsigned_to_nat(0u);
v_isZero_1778_ = lean_nat_dec_eq(v_a_1773_, v_zero_1777_);
if (v_isZero_1778_ == 1)
{
lean_del_object(v___x_1775_);
lean_dec(v_a_1773_);
v_r_1755_ = v_a_1772_;
goto _start;
}
else
{
lean_object* v_one_1780_; lean_object* v_n_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1789_; 
v_one_1780_ = lean_unsigned_to_nat(1u);
v_n_1781_ = lean_nat_sub(v_a_1773_, v_one_1780_);
lean_dec(v_a_1773_);
v___x_1782_ = lean_box(0);
v___x_1783_ = l_Lean_SourceInfo_fromRef(v___x_1782_, v_isZero_1778_);
v___x_1784_ = ((lean_object*)(l_Lean_Level_PP_Result_quote___closed__9));
v___x_1785_ = lean_unsigned_to_nat(65u);
v___x_1786_ = l_Lean_Level_PP_Result_quote(v_a_1772_, v___x_1785_);
v___x_1787_ = ((lean_object*)(l_Lean_Level_PP_Result_quote___closed__10));
lean_inc(v___x_1783_);
if (v_isShared_1776_ == 0)
{
lean_ctor_set(v___x_1775_, 1, v___x_1787_);
lean_ctor_set(v___x_1775_, 0, v___x_1783_);
v___x_1789_ = v___x_1775_;
goto v_reusejp_1788_;
}
else
{
lean_object* v_reuseFailAlloc_1795_; 
v_reuseFailAlloc_1795_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1795_, 0, v___x_1783_);
lean_ctor_set(v_reuseFailAlloc_1795_, 1, v___x_1787_);
v___x_1789_ = v_reuseFailAlloc_1795_;
goto v_reusejp_1788_;
}
v_reusejp_1788_:
{
lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; 
v___x_1790_ = lean_nat_add(v_n_1781_, v_one_1780_);
lean_dec(v_n_1781_);
v___x_1791_ = l_Nat_reprFast(v___x_1790_);
v___x_1792_ = lean_box(2);
v___x_1793_ = l_Lean_Syntax_mkNumLit(v___x_1791_, v___x_1792_);
v___x_1794_ = l_Lean_Syntax_node3(v___x_1783_, v___x_1784_, v___x_1786_, v___x_1789_, v___x_1793_);
v_s_1758_ = v___x_1794_;
goto v___jp_1757_;
}
}
}
}
case 3:
{
lean_object* v_a_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; size_t v_sz_1804_; size_t v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; 
v_a_1797_ = lean_ctor_get(v_r_1755_, 0);
lean_inc(v_a_1797_);
lean_dec_ref_known(v_r_1755_, 1);
v___x_1798_ = lean_obj_once(&l_Lean_Level_PP_Result_quote___closed__0, &l_Lean_Level_PP_Result_quote___closed__0_once, _init_l_Lean_Level_PP_Result_quote___closed__0);
v___x_1799_ = ((lean_object*)(l_Lean_Level_PP_Result_quote___closed__11));
v___x_1800_ = lean_obj_once(&l_Lean_Level_PP_Result_quote___closed__12, &l_Lean_Level_PP_Result_quote___closed__12_once, _init_l_Lean_Level_PP_Result_quote___closed__12);
v___x_1801_ = ((lean_object*)(l_Lean_Level_PP_Result_quote___closed__14));
v___x_1802_ = lean_obj_once(&l_Lean_Level_PP_Result_quote___closed__15, &l_Lean_Level_PP_Result_quote___closed__15_once, _init_l_Lean_Level_PP_Result_quote___closed__15);
v___x_1803_ = lean_array_mk(v_a_1797_);
v_sz_1804_ = lean_array_size(v___x_1803_);
v___x_1805_ = ((size_t)0ULL);
v___x_1806_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Level_PP_Result_quote_spec__0(v_sz_1804_, v___x_1805_, v___x_1803_);
v___x_1807_ = l_Array_append___redArg(v___x_1802_, v___x_1806_);
lean_dec_ref(v___x_1806_);
v___x_1808_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1808_, 0, v___x_1798_);
lean_ctor_set(v___x_1808_, 1, v___x_1801_);
lean_ctor_set(v___x_1808_, 2, v___x_1807_);
v___x_1809_ = l_Lean_Syntax_node2(v___x_1798_, v___x_1799_, v___x_1800_, v___x_1808_);
v_s_1758_ = v___x_1809_;
goto v___jp_1757_;
}
default: 
{
lean_object* v_a_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; size_t v_sz_1817_; size_t v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; 
v_a_1810_ = lean_ctor_get(v_r_1755_, 0);
lean_inc(v_a_1810_);
lean_dec_ref_known(v_r_1755_, 1);
v___x_1811_ = lean_obj_once(&l_Lean_Level_PP_Result_quote___closed__0, &l_Lean_Level_PP_Result_quote___closed__0_once, _init_l_Lean_Level_PP_Result_quote___closed__0);
v___x_1812_ = ((lean_object*)(l_Lean_Level_PP_Result_quote___closed__16));
v___x_1813_ = lean_obj_once(&l_Lean_Level_PP_Result_quote___closed__17, &l_Lean_Level_PP_Result_quote___closed__17_once, _init_l_Lean_Level_PP_Result_quote___closed__17);
v___x_1814_ = ((lean_object*)(l_Lean_Level_PP_Result_quote___closed__14));
v___x_1815_ = lean_obj_once(&l_Lean_Level_PP_Result_quote___closed__15, &l_Lean_Level_PP_Result_quote___closed__15_once, _init_l_Lean_Level_PP_Result_quote___closed__15);
v___x_1816_ = lean_array_mk(v_a_1810_);
v_sz_1817_ = lean_array_size(v___x_1816_);
v___x_1818_ = ((size_t)0ULL);
v___x_1819_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Level_PP_Result_quote_spec__0(v_sz_1817_, v___x_1818_, v___x_1816_);
v___x_1820_ = l_Array_append___redArg(v___x_1815_, v___x_1819_);
lean_dec_ref(v___x_1819_);
v___x_1821_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1821_, 0, v___x_1811_);
lean_ctor_set(v___x_1821_, 1, v___x_1814_);
lean_ctor_set(v___x_1821_, 2, v___x_1820_);
v___x_1822_ = l_Lean_Syntax_node2(v___x_1811_, v___x_1812_, v___x_1813_, v___x_1821_);
v_s_1758_ = v___x_1822_;
goto v___jp_1757_;
}
}
v___jp_1757_:
{
lean_object* v___x_1759_; uint8_t v___x_1760_; 
v___x_1759_ = lean_unsigned_to_nat(0u);
v___x_1760_ = lean_nat_dec_lt(v___x_1759_, v_prec_1756_);
if (v___x_1760_ == 0)
{
return v_s_1758_;
}
else
{
lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; 
v___x_1761_ = lean_obj_once(&l_Lean_Level_PP_Result_quote___closed__0, &l_Lean_Level_PP_Result_quote___closed__0_once, _init_l_Lean_Level_PP_Result_quote___closed__0);
v___x_1762_ = ((lean_object*)(l_Lean_Level_PP_Result_quote___closed__5));
v___x_1763_ = lean_obj_once(&l_Lean_Level_PP_Result_quote___closed__6, &l_Lean_Level_PP_Result_quote___closed__6_once, _init_l_Lean_Level_PP_Result_quote___closed__6);
v___x_1764_ = lean_obj_once(&l_Lean_Level_PP_Result_quote___closed__7, &l_Lean_Level_PP_Result_quote___closed__7_once, _init_l_Lean_Level_PP_Result_quote___closed__7);
v___x_1765_ = l_Lean_Syntax_node3(v___x_1761_, v___x_1762_, v___x_1763_, v_s_1758_, v___x_1764_);
return v___x_1765_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Level_PP_Result_quote_spec__0(size_t v_sz_1823_, size_t v_i_1824_, lean_object* v_bs_1825_){
_start:
{
uint8_t v___x_1826_; 
v___x_1826_ = lean_usize_dec_lt(v_i_1824_, v_sz_1823_);
if (v___x_1826_ == 0)
{
return v_bs_1825_;
}
else
{
lean_object* v_v_1827_; lean_object* v___x_1828_; lean_object* v_bs_x27_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; size_t v___x_1832_; size_t v___x_1833_; lean_object* v___x_1834_; 
v_v_1827_ = lean_array_uget(v_bs_1825_, v_i_1824_);
v___x_1828_ = lean_unsigned_to_nat(0u);
v_bs_x27_1829_ = lean_array_uset(v_bs_1825_, v_i_1824_, v___x_1828_);
v___x_1830_ = lean_unsigned_to_nat(1024u);
v___x_1831_ = l_Lean_Level_PP_Result_quote(v_v_1827_, v___x_1830_);
v___x_1832_ = ((size_t)1ULL);
v___x_1833_ = lean_usize_add(v_i_1824_, v___x_1832_);
v___x_1834_ = lean_array_uset(v_bs_x27_1829_, v_i_1824_, v___x_1831_);
v_i_1824_ = v___x_1833_;
v_bs_1825_ = v___x_1834_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Level_PP_Result_quote_spec__0___boxed(lean_object* v_sz_1836_, lean_object* v_i_1837_, lean_object* v_bs_1838_){
_start:
{
size_t v_sz_boxed_1839_; size_t v_i_boxed_1840_; lean_object* v_res_1841_; 
v_sz_boxed_1839_ = lean_unbox_usize(v_sz_1836_);
lean_dec(v_sz_1836_);
v_i_boxed_1840_ = lean_unbox_usize(v_i_1837_);
lean_dec(v_i_1837_);
v_res_1841_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Level_PP_Result_quote_spec__0(v_sz_boxed_1839_, v_i_boxed_1840_, v_bs_1838_);
return v_res_1841_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_quote___boxed(lean_object* v_r_1842_, lean_object* v_prec_1843_){
_start:
{
lean_object* v_res_1844_; 
v_res_1844_ = l_Lean_Level_PP_Result_quote(v_r_1842_, v_prec_1843_);
lean_dec(v_prec_1843_);
return v_res_1844_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_format(lean_object* v_u_1845_, uint8_t v_mvars_1846_, lean_object* v_lIndex_x3f_1847_){
_start:
{
lean_object* v___x_1848_; lean_object* v___x_1849_; uint8_t v___x_1850_; lean_object* v___x_1851_; 
v___x_1848_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1848_, 0, v_lIndex_x3f_1847_);
lean_ctor_set_uint8(v___x_1848_, sizeof(void*)*1, v_mvars_1846_);
v___x_1849_ = l_Lean_Level_PP_toResult(v_u_1845_, v___x_1848_);
lean_dec_ref_known(v___x_1848_, 1);
v___x_1850_ = 1;
v___x_1851_ = l_Lean_Level_PP_Result_format(v___x_1849_, v___x_1850_);
return v___x_1851_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_format___boxed(lean_object* v_u_1852_, lean_object* v_mvars_1853_, lean_object* v_lIndex_x3f_1854_){
_start:
{
uint8_t v_mvars_boxed_1855_; lean_object* v_res_1856_; 
v_mvars_boxed_1855_ = lean_unbox(v_mvars_1853_);
v_res_1856_ = l_Lean_Level_format(v_u_1852_, v_mvars_boxed_1855_, v_lIndex_x3f_1854_);
return v_res_1856_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_instToFormat___lam__0(lean_object* v_x_1857_){
_start:
{
lean_object* v___x_1858_; 
v___x_1858_ = lean_box(0);
return v___x_1858_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_instToFormat___lam__0___boxed(lean_object* v_x_1859_){
_start:
{
lean_object* v_res_1860_; 
v_res_1860_ = l_Lean_Level_instToFormat___lam__0(v_x_1859_);
lean_dec(v_x_1859_);
return v_res_1860_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_instToFormat___lam__1(lean_object* v___f_1861_, lean_object* v_u_1862_){
_start:
{
uint8_t v___x_1863_; lean_object* v___x_1864_; 
v___x_1863_ = 1;
v___x_1864_ = l_Lean_Level_format(v_u_1862_, v___x_1863_, v___f_1861_);
return v___x_1864_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_instToString___lam__1(lean_object* v___f_1869_, lean_object* v_u_1870_){
_start:
{
uint8_t v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; 
v___x_1871_ = 1;
v___x_1872_ = l_Lean_Level_format(v_u_1870_, v___x_1871_, v___f_1869_);
v___x_1873_ = l_Std_Format_defWidth;
v___x_1874_ = lean_unsigned_to_nat(0u);
v___x_1875_ = l_Std_Format_pretty(v___x_1872_, v___x_1873_, v___x_1874_, v___x_1874_);
return v___x_1875_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_quote(lean_object* v_u_1879_, lean_object* v_prec_1880_, uint8_t v_mvars_1881_, lean_object* v_lIndex_x3f_1882_){
_start:
{
lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; 
v___x_1883_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1883_, 0, v_lIndex_x3f_1882_);
lean_ctor_set_uint8(v___x_1883_, sizeof(void*)*1, v_mvars_1881_);
v___x_1884_ = l_Lean_Level_PP_toResult(v_u_1879_, v___x_1883_);
lean_dec_ref_known(v___x_1883_, 1);
v___x_1885_ = l_Lean_Level_PP_Result_quote(v___x_1884_, v_prec_1880_);
return v___x_1885_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_quote___boxed(lean_object* v_u_1886_, lean_object* v_prec_1887_, lean_object* v_mvars_1888_, lean_object* v_lIndex_x3f_1889_){
_start:
{
uint8_t v_mvars_boxed_1890_; lean_object* v_res_1891_; 
v_mvars_boxed_1890_ = lean_unbox(v_mvars_1888_);
v_res_1891_ = l_Lean_Level_quote(v_u_1886_, v_prec_1887_, v_mvars_boxed_1890_, v_lIndex_x3f_1889_);
lean_dec(v_prec_1887_);
return v_res_1891_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_instQuoteMkStr1___lam__1(lean_object* v___f_1892_, lean_object* v_u_1893_){
_start:
{
lean_object* v___x_1894_; uint8_t v___x_1895_; lean_object* v___x_1896_; 
v___x_1894_ = lean_unsigned_to_nat(0u);
v___x_1895_ = 1;
v___x_1896_ = l_Lean_Level_quote(v_u_1893_, v___x_1894_, v___x_1895_, v___f_1892_);
return v___x_1896_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Level_0__Lean_mkLevelMaxCore___lam__0(lean_object* v_u_1900_, lean_object* v_v_1901_){
_start:
{
uint8_t v___y_1903_; uint8_t v___x_1908_; 
v___x_1908_ = l_Lean_Level_isExplicit(v_v_1901_);
if (v___x_1908_ == 0)
{
v___y_1903_ = v___x_1908_;
goto v___jp_1902_;
}
else
{
lean_object* v___x_1909_; lean_object* v___x_1910_; uint8_t v___x_1911_; 
v___x_1909_ = l_Lean_Level_getOffset(v_v_1901_);
v___x_1910_ = l_Lean_Level_getOffset(v_u_1900_);
v___x_1911_ = lean_nat_dec_le(v___x_1909_, v___x_1910_);
lean_dec(v___x_1910_);
lean_dec(v___x_1909_);
if (v___x_1911_ == 0)
{
v___y_1903_ = v___x_1911_;
goto v___jp_1902_;
}
else
{
return v___x_1908_;
}
}
v___jp_1902_:
{
if (lean_obj_tag(v_u_1900_) == 2)
{
lean_object* v_a_1904_; lean_object* v_a_1905_; uint8_t v___x_1906_; 
v_a_1904_ = lean_ctor_get(v_u_1900_, 0);
v_a_1905_ = lean_ctor_get(v_u_1900_, 1);
v___x_1906_ = lean_level_eq(v_v_1901_, v_a_1904_);
if (v___x_1906_ == 0)
{
uint8_t v___x_1907_; 
v___x_1907_ = lean_level_eq(v_v_1901_, v_a_1905_);
return v___x_1907_;
}
else
{
return v___x_1906_;
}
}
else
{
return v___y_1903_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_mkLevelMaxCore___lam__0___boxed(lean_object* v_u_1912_, lean_object* v_v_1913_){
_start:
{
uint8_t v_res_1914_; lean_object* v_r_1915_; 
v_res_1914_ = l___private_Lean_Level_0__Lean_mkLevelMaxCore___lam__0(v_u_1912_, v_v_1913_);
lean_dec(v_v_1913_);
lean_dec(v_u_1912_);
v_r_1915_ = lean_box(v_res_1914_);
return v_r_1915_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_mkLevelMaxCore(lean_object* v_u_1916_, lean_object* v_v_1917_, lean_object* v_elseK_1918_){
_start:
{
uint8_t v___x_1919_; 
v___x_1919_ = lean_level_eq(v_u_1916_, v_v_1917_);
if (v___x_1919_ == 0)
{
uint8_t v___x_1920_; 
v___x_1920_ = l_Lean_Level_isZero(v_u_1916_);
if (v___x_1920_ == 0)
{
uint8_t v___x_1921_; 
v___x_1921_ = l_Lean_Level_isZero(v_v_1917_);
if (v___x_1921_ == 0)
{
uint8_t v___x_1922_; 
v___x_1922_ = l___private_Lean_Level_0__Lean_mkLevelMaxCore___lam__0(v_u_1916_, v_v_1917_);
if (v___x_1922_ == 0)
{
uint8_t v___x_1923_; 
v___x_1923_ = l___private_Lean_Level_0__Lean_mkLevelMaxCore___lam__0(v_v_1917_, v_u_1916_);
if (v___x_1923_ == 0)
{
lean_object* v___x_1924_; lean_object* v___x_1925_; uint8_t v___x_1926_; 
v___x_1924_ = l_Lean_Level_getLevelOffset(v_u_1916_);
v___x_1925_ = l_Lean_Level_getLevelOffset(v_v_1917_);
v___x_1926_ = lean_level_eq(v___x_1924_, v___x_1925_);
lean_dec(v___x_1925_);
lean_dec(v___x_1924_);
if (v___x_1926_ == 0)
{
lean_object* v___x_1927_; lean_object* v___x_1928_; 
v___x_1927_ = lean_box(0);
v___x_1928_ = lean_apply_1(v_elseK_1918_, v___x_1927_);
return v___x_1928_;
}
else
{
lean_object* v___x_1929_; lean_object* v___x_1930_; uint8_t v___x_1931_; 
lean_dec_ref(v_elseK_1918_);
v___x_1929_ = l_Lean_Level_getOffset(v_v_1917_);
v___x_1930_ = l_Lean_Level_getOffset(v_u_1916_);
v___x_1931_ = lean_nat_dec_le(v___x_1929_, v___x_1930_);
lean_dec(v___x_1930_);
lean_dec(v___x_1929_);
if (v___x_1931_ == 0)
{
lean_inc(v_v_1917_);
return v_v_1917_;
}
else
{
lean_inc(v_u_1916_);
return v_u_1916_;
}
}
}
else
{
lean_dec_ref(v_elseK_1918_);
lean_inc(v_v_1917_);
return v_v_1917_;
}
}
else
{
lean_dec_ref(v_elseK_1918_);
lean_inc(v_u_1916_);
return v_u_1916_;
}
}
else
{
lean_dec_ref(v_elseK_1918_);
lean_inc(v_u_1916_);
return v_u_1916_;
}
}
else
{
lean_dec_ref(v_elseK_1918_);
lean_inc(v_v_1917_);
return v_v_1917_;
}
}
else
{
lean_dec_ref(v_elseK_1918_);
lean_inc(v_u_1916_);
return v_u_1916_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_mkLevelMaxCore___boxed(lean_object* v_u_1932_, lean_object* v_v_1933_, lean_object* v_elseK_1934_){
_start:
{
lean_object* v_res_1935_; 
v_res_1935_ = l___private_Lean_Level_0__Lean_mkLevelMaxCore(v_u_1932_, v_v_1933_, v_elseK_1934_);
lean_dec(v_v_1933_);
lean_dec(v_u_1932_);
return v_res_1935_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLevelMax_x27(lean_object* v_u_1936_, lean_object* v_v_1937_){
_start:
{
uint8_t v___x_1938_; 
v___x_1938_ = lean_level_eq(v_u_1936_, v_v_1937_);
if (v___x_1938_ == 0)
{
uint8_t v___x_1939_; 
v___x_1939_ = l_Lean_Level_isZero(v_u_1936_);
if (v___x_1939_ == 0)
{
uint8_t v___x_1940_; 
v___x_1940_ = l_Lean_Level_isZero(v_v_1937_);
if (v___x_1940_ == 0)
{
uint8_t v___x_1941_; 
v___x_1941_ = l___private_Lean_Level_0__Lean_mkLevelMaxCore___lam__0(v_u_1936_, v_v_1937_);
if (v___x_1941_ == 0)
{
uint8_t v___x_1942_; 
v___x_1942_ = l___private_Lean_Level_0__Lean_mkLevelMaxCore___lam__0(v_v_1937_, v_u_1936_);
if (v___x_1942_ == 0)
{
lean_object* v___x_1943_; lean_object* v___x_1944_; uint8_t v___x_1945_; 
v___x_1943_ = l_Lean_Level_getLevelOffset(v_u_1936_);
v___x_1944_ = l_Lean_Level_getLevelOffset(v_v_1937_);
v___x_1945_ = lean_level_eq(v___x_1943_, v___x_1944_);
lean_dec(v___x_1944_);
lean_dec(v___x_1943_);
if (v___x_1945_ == 0)
{
lean_object* v___x_1946_; 
v___x_1946_ = l_Lean_Level_max___override(v_u_1936_, v_v_1937_);
return v___x_1946_;
}
else
{
lean_object* v___x_1947_; lean_object* v___x_1948_; uint8_t v___x_1949_; 
v___x_1947_ = l_Lean_Level_getOffset(v_v_1937_);
v___x_1948_ = l_Lean_Level_getOffset(v_u_1936_);
v___x_1949_ = lean_nat_dec_le(v___x_1947_, v___x_1948_);
lean_dec(v___x_1948_);
lean_dec(v___x_1947_);
if (v___x_1949_ == 0)
{
lean_dec(v_u_1936_);
return v_v_1937_;
}
else
{
lean_dec(v_v_1937_);
return v_u_1936_;
}
}
}
else
{
lean_dec(v_u_1936_);
return v_v_1937_;
}
}
else
{
lean_dec(v_v_1937_);
return v_u_1936_;
}
}
else
{
lean_dec(v_v_1937_);
return v_u_1936_;
}
}
else
{
lean_dec(v_u_1936_);
return v_v_1937_;
}
}
else
{
lean_dec(v_v_1937_);
return v_u_1936_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_simpLevelMax_x27(lean_object* v_u_1950_, lean_object* v_v_1951_, lean_object* v_d_1952_){
_start:
{
uint8_t v___x_1953_; 
v___x_1953_ = lean_level_eq(v_u_1950_, v_v_1951_);
if (v___x_1953_ == 0)
{
uint8_t v___x_1954_; 
v___x_1954_ = l_Lean_Level_isZero(v_u_1950_);
if (v___x_1954_ == 0)
{
uint8_t v___x_1955_; 
v___x_1955_ = l_Lean_Level_isZero(v_v_1951_);
if (v___x_1955_ == 0)
{
uint8_t v___x_1956_; 
v___x_1956_ = l___private_Lean_Level_0__Lean_mkLevelMaxCore___lam__0(v_u_1950_, v_v_1951_);
if (v___x_1956_ == 0)
{
uint8_t v___x_1957_; 
v___x_1957_ = l___private_Lean_Level_0__Lean_mkLevelMaxCore___lam__0(v_v_1951_, v_u_1950_);
if (v___x_1957_ == 0)
{
lean_object* v___x_1958_; lean_object* v___x_1959_; uint8_t v___x_1960_; 
v___x_1958_ = l_Lean_Level_getLevelOffset(v_u_1950_);
v___x_1959_ = l_Lean_Level_getLevelOffset(v_v_1951_);
v___x_1960_ = lean_level_eq(v___x_1958_, v___x_1959_);
lean_dec(v___x_1959_);
lean_dec(v___x_1958_);
if (v___x_1960_ == 0)
{
lean_inc(v_d_1952_);
return v_d_1952_;
}
else
{
lean_object* v___x_1961_; lean_object* v___x_1962_; uint8_t v___x_1963_; 
v___x_1961_ = l_Lean_Level_getOffset(v_v_1951_);
v___x_1962_ = l_Lean_Level_getOffset(v_u_1950_);
v___x_1963_ = lean_nat_dec_le(v___x_1961_, v___x_1962_);
lean_dec(v___x_1962_);
lean_dec(v___x_1961_);
if (v___x_1963_ == 0)
{
lean_inc(v_v_1951_);
return v_v_1951_;
}
else
{
lean_inc(v_u_1950_);
return v_u_1950_;
}
}
}
else
{
lean_inc(v_v_1951_);
return v_v_1951_;
}
}
else
{
lean_inc(v_u_1950_);
return v_u_1950_;
}
}
else
{
lean_inc(v_u_1950_);
return v_u_1950_;
}
}
else
{
lean_inc(v_v_1951_);
return v_v_1951_;
}
}
else
{
lean_inc(v_u_1950_);
return v_u_1950_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_simpLevelMax_x27___boxed(lean_object* v_u_1964_, lean_object* v_v_1965_, lean_object* v_d_1966_){
_start:
{
lean_object* v_res_1967_; 
v_res_1967_ = l_Lean_simpLevelMax_x27(v_u_1964_, v_v_1965_, v_d_1966_);
lean_dec(v_d_1966_);
lean_dec(v_v_1965_);
lean_dec(v_u_1964_);
return v_res_1967_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_mkLevelIMaxCore(lean_object* v_u_1968_, lean_object* v_v_1969_, lean_object* v_elseK_1970_){
_start:
{
uint8_t v___x_1971_; 
v___x_1971_ = l_Lean_Level_isNeverZero(v_v_1969_);
if (v___x_1971_ == 0)
{
uint8_t v___x_1972_; 
v___x_1972_ = l_Lean_Level_isZero(v_v_1969_);
if (v___x_1972_ == 0)
{
uint8_t v___x_1973_; 
v___x_1973_ = l_Lean_Level_isZero(v_u_1968_);
if (v___x_1973_ == 0)
{
uint8_t v___x_1974_; 
v___x_1974_ = lean_level_eq(v_u_1968_, v_v_1969_);
lean_dec(v_v_1969_);
if (v___x_1974_ == 0)
{
lean_object* v___x_1975_; lean_object* v___x_1976_; 
lean_dec(v_u_1968_);
v___x_1975_ = lean_box(0);
v___x_1976_ = lean_apply_1(v_elseK_1970_, v___x_1975_);
return v___x_1976_;
}
else
{
lean_dec_ref(v_elseK_1970_);
return v_u_1968_;
}
}
else
{
lean_dec_ref(v_elseK_1970_);
lean_dec(v_u_1968_);
return v_v_1969_;
}
}
else
{
lean_dec_ref(v_elseK_1970_);
lean_dec(v_u_1968_);
return v_v_1969_;
}
}
else
{
lean_object* v___x_1977_; 
lean_dec_ref(v_elseK_1970_);
v___x_1977_ = l_Lean_mkLevelMax_x27(v_u_1968_, v_v_1969_);
return v___x_1977_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkLevelIMax_x27(lean_object* v_u_1978_, lean_object* v_v_1979_){
_start:
{
uint8_t v___x_1980_; 
v___x_1980_ = l_Lean_Level_isNeverZero(v_v_1979_);
if (v___x_1980_ == 0)
{
uint8_t v___x_1981_; 
v___x_1981_ = l_Lean_Level_isZero(v_v_1979_);
if (v___x_1981_ == 0)
{
uint8_t v___x_1982_; 
v___x_1982_ = l_Lean_Level_isZero(v_u_1978_);
if (v___x_1982_ == 0)
{
uint8_t v___x_1983_; 
v___x_1983_ = lean_level_eq(v_u_1978_, v_v_1979_);
if (v___x_1983_ == 0)
{
lean_object* v___x_1984_; 
v___x_1984_ = l_Lean_Level_imax___override(v_u_1978_, v_v_1979_);
return v___x_1984_;
}
else
{
lean_dec(v_v_1979_);
return v_u_1978_;
}
}
else
{
lean_dec(v_u_1978_);
return v_v_1979_;
}
}
else
{
lean_dec(v_u_1978_);
return v_v_1979_;
}
}
else
{
lean_object* v___x_1985_; 
v___x_1985_ = l_Lean_mkLevelMax_x27(v_u_1978_, v_v_1979_);
return v___x_1985_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_simpLevelIMax_x27(lean_object* v_u_1986_, lean_object* v_v_1987_, lean_object* v_d_1988_){
_start:
{
uint8_t v___x_1989_; 
v___x_1989_ = l_Lean_Level_isNeverZero(v_v_1987_);
if (v___x_1989_ == 0)
{
uint8_t v___x_1990_; 
v___x_1990_ = l_Lean_Level_isZero(v_v_1987_);
if (v___x_1990_ == 0)
{
uint8_t v___x_1991_; 
v___x_1991_ = l_Lean_Level_isZero(v_u_1986_);
if (v___x_1991_ == 0)
{
uint8_t v___x_1992_; 
v___x_1992_ = lean_level_eq(v_u_1986_, v_v_1987_);
lean_dec(v_v_1987_);
if (v___x_1992_ == 0)
{
lean_dec(v_u_1986_);
lean_inc(v_d_1988_);
return v_d_1988_;
}
else
{
return v_u_1986_;
}
}
else
{
lean_dec(v_u_1986_);
return v_v_1987_;
}
}
else
{
lean_dec(v_u_1986_);
return v_v_1987_;
}
}
else
{
lean_object* v___x_1993_; 
v___x_1993_ = l_Lean_mkLevelMax_x27(v_u_1986_, v_v_1987_);
return v___x_1993_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_simpLevelIMax_x27___boxed(lean_object* v_u_1994_, lean_object* v_v_1995_, lean_object* v_d_1996_){
_start:
{
lean_object* v_res_1997_; 
v_res_1997_ = l_Lean_simpLevelIMax_x27(v_u_1994_, v_v_1995_, v_d_1996_);
lean_dec(v_d_1996_);
return v_res_1997_;
}
}
static lean_object* _init_l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl___closed__2(void){
_start:
{
lean_object* v___x_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; 
v___x_2000_ = ((lean_object*)(l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl___closed__1));
v___x_2001_ = lean_unsigned_to_nat(14u);
v___x_2002_ = lean_unsigned_to_nat(566u);
v___x_2003_ = ((lean_object*)(l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl___closed__0));
v___x_2004_ = ((lean_object*)(l_Lean_Level_mvarId_x21___closed__0));
v___x_2005_ = l_mkPanicMessageWithDecl(v___x_2004_, v___x_2003_, v___x_2002_, v___x_2001_, v___x_2000_);
return v___x_2005_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl(lean_object* v_lvl_2006_, lean_object* v_newLvl_2007_){
_start:
{
if (lean_obj_tag(v_lvl_2006_) == 1)
{
lean_object* v_a_2008_; size_t v___x_2009_; size_t v___x_2010_; uint8_t v___x_2011_; 
v_a_2008_ = lean_ctor_get(v_lvl_2006_, 0);
v___x_2009_ = lean_ptr_addr(v_a_2008_);
v___x_2010_ = lean_ptr_addr(v_newLvl_2007_);
v___x_2011_ = lean_usize_dec_eq(v___x_2009_, v___x_2010_);
if (v___x_2011_ == 0)
{
lean_object* v___x_2012_; 
v___x_2012_ = l_Lean_Level_succ___override(v_newLvl_2007_);
return v___x_2012_;
}
else
{
lean_dec(v_newLvl_2007_);
lean_inc_ref(v_lvl_2006_);
return v_lvl_2006_;
}
}
else
{
lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; 
lean_dec(v_newLvl_2007_);
v___x_2013_ = lean_box(0);
v___x_2014_ = lean_obj_once(&l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl___closed__2, &l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl___closed__2_once, _init_l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl___closed__2);
v___x_2015_ = l_panic___redArg(v___x_2013_, v___x_2014_);
return v___x_2015_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl___boxed(lean_object* v_lvl_2016_, lean_object* v_newLvl_2017_){
_start:
{
lean_object* v_res_2018_; 
v_res_2018_ = l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl(v_lvl_2016_, v_newLvl_2017_);
lean_dec(v_lvl_2016_);
return v_res_2018_;
}
}
static lean_object* _init_l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl___closed__2(void){
_start:
{
lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; 
v___x_2021_ = ((lean_object*)(l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl___closed__1));
v___x_2022_ = lean_unsigned_to_nat(19u);
v___x_2023_ = lean_unsigned_to_nat(577u);
v___x_2024_ = ((lean_object*)(l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl___closed__0));
v___x_2025_ = ((lean_object*)(l_Lean_Level_mvarId_x21___closed__0));
v___x_2026_ = l_mkPanicMessageWithDecl(v___x_2025_, v___x_2024_, v___x_2023_, v___x_2022_, v___x_2021_);
return v___x_2026_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl(lean_object* v_lvl_2027_, lean_object* v_newLhs_2028_, lean_object* v_newRhs_2029_){
_start:
{
if (lean_obj_tag(v_lvl_2027_) == 2)
{
lean_object* v_a_2030_; lean_object* v_a_2031_; size_t v___x_2032_; size_t v___x_2033_; uint8_t v___x_2034_; 
v_a_2030_ = lean_ctor_get(v_lvl_2027_, 0);
v_a_2031_ = lean_ctor_get(v_lvl_2027_, 1);
v___x_2032_ = lean_ptr_addr(v_a_2030_);
v___x_2033_ = lean_ptr_addr(v_newLhs_2028_);
v___x_2034_ = lean_usize_dec_eq(v___x_2032_, v___x_2033_);
if (v___x_2034_ == 0)
{
lean_object* v___x_2035_; 
v___x_2035_ = l_Lean_mkLevelMax_x27(v_newLhs_2028_, v_newRhs_2029_);
return v___x_2035_;
}
else
{
size_t v___x_2036_; size_t v___x_2037_; uint8_t v___x_2038_; 
v___x_2036_ = lean_ptr_addr(v_a_2031_);
v___x_2037_ = lean_ptr_addr(v_newRhs_2029_);
v___x_2038_ = lean_usize_dec_eq(v___x_2036_, v___x_2037_);
if (v___x_2038_ == 0)
{
lean_object* v___x_2039_; 
v___x_2039_ = l_Lean_mkLevelMax_x27(v_newLhs_2028_, v_newRhs_2029_);
return v___x_2039_;
}
else
{
lean_object* v___x_2040_; 
v___x_2040_ = l_Lean_simpLevelMax_x27(v_newLhs_2028_, v_newRhs_2029_, v_lvl_2027_);
lean_dec(v_newRhs_2029_);
lean_dec(v_newLhs_2028_);
return v___x_2040_;
}
}
}
else
{
lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; 
lean_dec(v_newRhs_2029_);
lean_dec(v_newLhs_2028_);
v___x_2041_ = lean_box(0);
v___x_2042_ = lean_obj_once(&l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl___closed__2, &l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl___closed__2_once, _init_l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl___closed__2);
v___x_2043_ = l_panic___redArg(v___x_2041_, v___x_2042_);
return v___x_2043_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl___boxed(lean_object* v_lvl_2044_, lean_object* v_newLhs_2045_, lean_object* v_newRhs_2046_){
_start:
{
lean_object* v_res_2047_; 
v_res_2047_ = l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl(v_lvl_2044_, v_newLhs_2045_, v_newRhs_2046_);
lean_dec(v_lvl_2044_);
return v_res_2047_;
}
}
static lean_object* _init_l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl___closed__2(void){
_start:
{
lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; 
v___x_2050_ = ((lean_object*)(l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl___closed__1));
v___x_2051_ = lean_unsigned_to_nat(20u);
v___x_2052_ = lean_unsigned_to_nat(588u);
v___x_2053_ = ((lean_object*)(l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl___closed__0));
v___x_2054_ = ((lean_object*)(l_Lean_Level_mvarId_x21___closed__0));
v___x_2055_ = l_mkPanicMessageWithDecl(v___x_2054_, v___x_2053_, v___x_2052_, v___x_2051_, v___x_2050_);
return v___x_2055_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl(lean_object* v_lvl_2056_, lean_object* v_newLhs_2057_, lean_object* v_newRhs_2058_){
_start:
{
if (lean_obj_tag(v_lvl_2056_) == 3)
{
lean_object* v_a_2059_; lean_object* v_a_2060_; size_t v___x_2061_; size_t v___x_2062_; uint8_t v___x_2063_; 
v_a_2059_ = lean_ctor_get(v_lvl_2056_, 0);
v_a_2060_ = lean_ctor_get(v_lvl_2056_, 1);
v___x_2061_ = lean_ptr_addr(v_a_2059_);
v___x_2062_ = lean_ptr_addr(v_newLhs_2057_);
v___x_2063_ = lean_usize_dec_eq(v___x_2061_, v___x_2062_);
if (v___x_2063_ == 0)
{
lean_object* v___x_2064_; 
v___x_2064_ = l_Lean_mkLevelIMax_x27(v_newLhs_2057_, v_newRhs_2058_);
return v___x_2064_;
}
else
{
size_t v___x_2065_; size_t v___x_2066_; uint8_t v___x_2067_; 
v___x_2065_ = lean_ptr_addr(v_a_2060_);
v___x_2066_ = lean_ptr_addr(v_newRhs_2058_);
v___x_2067_ = lean_usize_dec_eq(v___x_2065_, v___x_2066_);
if (v___x_2067_ == 0)
{
lean_object* v___x_2068_; 
v___x_2068_ = l_Lean_mkLevelIMax_x27(v_newLhs_2057_, v_newRhs_2058_);
return v___x_2068_;
}
else
{
lean_object* v___x_2069_; 
v___x_2069_ = l_Lean_simpLevelIMax_x27(v_newLhs_2057_, v_newRhs_2058_, v_lvl_2056_);
return v___x_2069_;
}
}
}
else
{
lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; 
lean_dec(v_newRhs_2058_);
lean_dec(v_newLhs_2057_);
v___x_2070_ = lean_box(0);
v___x_2071_ = lean_obj_once(&l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl___closed__2, &l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl___closed__2_once, _init_l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl___closed__2);
v___x_2072_ = l_panic___redArg(v___x_2070_, v___x_2071_);
return v___x_2072_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl___boxed(lean_object* v_lvl_2073_, lean_object* v_newLhs_2074_, lean_object* v_newRhs_2075_){
_start:
{
lean_object* v_res_2076_; 
v_res_2076_ = l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl(v_lvl_2073_, v_newLhs_2074_, v_newRhs_2075_);
lean_dec(v_lvl_2073_);
return v_res_2076_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_mkNaryMax(lean_object* v_x_2077_){
_start:
{
if (lean_obj_tag(v_x_2077_) == 0)
{
lean_object* v___x_2078_; 
v___x_2078_ = lean_box(0);
return v___x_2078_;
}
else
{
lean_object* v_tail_2079_; 
v_tail_2079_ = lean_ctor_get(v_x_2077_, 1);
if (lean_obj_tag(v_tail_2079_) == 0)
{
lean_object* v_head_2080_; 
v_head_2080_ = lean_ctor_get(v_x_2077_, 0);
lean_inc(v_head_2080_);
lean_dec_ref_known(v_x_2077_, 2);
return v_head_2080_;
}
else
{
lean_object* v_head_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; 
lean_inc(v_tail_2079_);
v_head_2081_ = lean_ctor_get(v_x_2077_, 0);
lean_inc(v_head_2081_);
lean_dec_ref_known(v_x_2077_, 2);
v___x_2082_ = l_Lean_Level_mkNaryMax(v_tail_2079_);
v___x_2083_ = l_Lean_mkLevelMax_x27(v_head_2081_, v___x_2082_);
return v___x_2083_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_substParams_go(lean_object* v_s_2084_, lean_object* v_u_2085_){
_start:
{
switch(lean_obj_tag(v_u_2085_))
{
case 1:
{
lean_object* v_a_2086_; uint8_t v___x_2087_; 
v_a_2086_ = lean_ctor_get(v_u_2085_, 0);
v___x_2087_ = l_Lean_Level_hasParam(v_u_2085_);
if (v___x_2087_ == 0)
{
lean_dec_ref(v_s_2084_);
return v_u_2085_;
}
else
{
lean_object* v___x_2088_; size_t v___x_2089_; size_t v___x_2090_; uint8_t v___x_2091_; 
lean_inc(v_a_2086_);
v___x_2088_ = l___private_Lean_Level_0__Lean_Level_substParams_go(v_s_2084_, v_a_2086_);
v___x_2089_ = lean_ptr_addr(v_a_2086_);
v___x_2090_ = lean_ptr_addr(v___x_2088_);
v___x_2091_ = lean_usize_dec_eq(v___x_2089_, v___x_2090_);
if (v___x_2091_ == 0)
{
lean_object* v___x_2092_; 
lean_dec_ref_known(v_u_2085_, 1);
v___x_2092_ = l_Lean_Level_succ___override(v___x_2088_);
return v___x_2092_;
}
else
{
lean_dec(v___x_2088_);
return v_u_2085_;
}
}
}
case 2:
{
lean_object* v_a_2093_; lean_object* v_a_2094_; uint8_t v___x_2095_; 
v_a_2093_ = lean_ctor_get(v_u_2085_, 0);
v_a_2094_ = lean_ctor_get(v_u_2085_, 1);
v___x_2095_ = l_Lean_Level_hasParam(v_u_2085_);
if (v___x_2095_ == 0)
{
lean_dec_ref(v_s_2084_);
return v_u_2085_;
}
else
{
lean_object* v___x_2096_; lean_object* v___x_2097_; size_t v___x_2098_; size_t v___x_2099_; uint8_t v___x_2100_; 
lean_inc(v_a_2093_);
lean_inc_ref(v_s_2084_);
v___x_2096_ = l___private_Lean_Level_0__Lean_Level_substParams_go(v_s_2084_, v_a_2093_);
lean_inc(v_a_2094_);
v___x_2097_ = l___private_Lean_Level_0__Lean_Level_substParams_go(v_s_2084_, v_a_2094_);
v___x_2098_ = lean_ptr_addr(v_a_2093_);
v___x_2099_ = lean_ptr_addr(v___x_2096_);
v___x_2100_ = lean_usize_dec_eq(v___x_2098_, v___x_2099_);
if (v___x_2100_ == 0)
{
lean_object* v___x_2101_; 
lean_dec_ref_known(v_u_2085_, 2);
v___x_2101_ = l_Lean_mkLevelMax_x27(v___x_2096_, v___x_2097_);
return v___x_2101_;
}
else
{
size_t v___x_2102_; size_t v___x_2103_; uint8_t v___x_2104_; 
v___x_2102_ = lean_ptr_addr(v_a_2094_);
v___x_2103_ = lean_ptr_addr(v___x_2097_);
v___x_2104_ = lean_usize_dec_eq(v___x_2102_, v___x_2103_);
if (v___x_2104_ == 0)
{
lean_object* v___x_2105_; 
lean_dec_ref_known(v_u_2085_, 2);
v___x_2105_ = l_Lean_mkLevelMax_x27(v___x_2096_, v___x_2097_);
return v___x_2105_;
}
else
{
lean_object* v___x_2106_; 
v___x_2106_ = l_Lean_simpLevelMax_x27(v___x_2096_, v___x_2097_, v_u_2085_);
lean_dec_ref_known(v_u_2085_, 2);
lean_dec(v___x_2097_);
lean_dec(v___x_2096_);
return v___x_2106_;
}
}
}
}
case 3:
{
lean_object* v_a_2107_; lean_object* v_a_2108_; uint8_t v___x_2109_; 
v_a_2107_ = lean_ctor_get(v_u_2085_, 0);
v_a_2108_ = lean_ctor_get(v_u_2085_, 1);
v___x_2109_ = l_Lean_Level_hasParam(v_u_2085_);
if (v___x_2109_ == 0)
{
lean_dec_ref(v_s_2084_);
return v_u_2085_;
}
else
{
lean_object* v___x_2110_; lean_object* v___x_2111_; size_t v___x_2112_; size_t v___x_2113_; uint8_t v___x_2114_; 
lean_inc(v_a_2107_);
lean_inc_ref(v_s_2084_);
v___x_2110_ = l___private_Lean_Level_0__Lean_Level_substParams_go(v_s_2084_, v_a_2107_);
lean_inc(v_a_2108_);
v___x_2111_ = l___private_Lean_Level_0__Lean_Level_substParams_go(v_s_2084_, v_a_2108_);
v___x_2112_ = lean_ptr_addr(v_a_2107_);
v___x_2113_ = lean_ptr_addr(v___x_2110_);
v___x_2114_ = lean_usize_dec_eq(v___x_2112_, v___x_2113_);
if (v___x_2114_ == 0)
{
lean_object* v___x_2115_; 
lean_dec_ref_known(v_u_2085_, 2);
v___x_2115_ = l_Lean_mkLevelIMax_x27(v___x_2110_, v___x_2111_);
return v___x_2115_;
}
else
{
size_t v___x_2116_; size_t v___x_2117_; uint8_t v___x_2118_; 
v___x_2116_ = lean_ptr_addr(v_a_2108_);
v___x_2117_ = lean_ptr_addr(v___x_2111_);
v___x_2118_ = lean_usize_dec_eq(v___x_2116_, v___x_2117_);
if (v___x_2118_ == 0)
{
lean_object* v___x_2119_; 
lean_dec_ref_known(v_u_2085_, 2);
v___x_2119_ = l_Lean_mkLevelIMax_x27(v___x_2110_, v___x_2111_);
return v___x_2119_;
}
else
{
lean_object* v___x_2120_; 
v___x_2120_ = l_Lean_simpLevelIMax_x27(v___x_2110_, v___x_2111_, v_u_2085_);
lean_dec_ref_known(v_u_2085_, 2);
return v___x_2120_;
}
}
}
}
case 4:
{
lean_object* v_a_2121_; lean_object* v___x_2122_; 
v_a_2121_ = lean_ctor_get(v_u_2085_, 0);
lean_inc(v_a_2121_);
v___x_2122_ = lean_apply_1(v_s_2084_, v_a_2121_);
if (lean_obj_tag(v___x_2122_) == 0)
{
return v_u_2085_;
}
else
{
lean_object* v_val_2123_; 
lean_dec_ref_known(v_u_2085_, 1);
v_val_2123_ = lean_ctor_get(v___x_2122_, 0);
lean_inc(v_val_2123_);
lean_dec_ref_known(v___x_2122_, 1);
return v_val_2123_;
}
}
default: 
{
lean_dec_ref(v_s_2084_);
return v_u_2085_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_substParams(lean_object* v_u_2124_, lean_object* v_s_2125_){
_start:
{
lean_object* v___x_2126_; 
v___x_2126_ = l___private_Lean_Level_0__Lean_Level_substParams_go(v_s_2125_, v_u_2124_);
return v___x_2126_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_getParamSubst(lean_object* v_x_2127_, lean_object* v_x_2128_, lean_object* v_x_2129_){
_start:
{
if (lean_obj_tag(v_x_2127_) == 1)
{
if (lean_obj_tag(v_x_2128_) == 1)
{
lean_object* v_head_2130_; lean_object* v_tail_2131_; lean_object* v_head_2132_; lean_object* v_tail_2133_; uint8_t v___x_2134_; 
v_head_2130_ = lean_ctor_get(v_x_2127_, 0);
v_tail_2131_ = lean_ctor_get(v_x_2127_, 1);
v_head_2132_ = lean_ctor_get(v_x_2128_, 0);
v_tail_2133_ = lean_ctor_get(v_x_2128_, 1);
v___x_2134_ = lean_name_eq(v_head_2130_, v_x_2129_);
if (v___x_2134_ == 0)
{
v_x_2127_ = v_tail_2131_;
v_x_2128_ = v_tail_2133_;
goto _start;
}
else
{
lean_object* v___x_2136_; 
lean_inc(v_head_2132_);
v___x_2136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2136_, 0, v_head_2132_);
return v___x_2136_;
}
}
else
{
lean_object* v___x_2137_; 
v___x_2137_ = lean_box(0);
return v___x_2137_;
}
}
else
{
lean_object* v___x_2138_; 
v___x_2138_ = lean_box(0);
return v___x_2138_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_getParamSubst___boxed(lean_object* v_x_2139_, lean_object* v_x_2140_, lean_object* v_x_2141_){
_start:
{
lean_object* v_res_2142_; 
v_res_2142_ = l_Lean_Level_getParamSubst(v_x_2139_, v_x_2140_, v_x_2141_);
lean_dec(v_x_2141_);
lean_dec(v_x_2140_);
lean_dec(v_x_2139_);
return v_res_2142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_instantiateParams(lean_object* v_u_2143_, lean_object* v_paramNames_2144_, lean_object* v_vs_2145_){
_start:
{
lean_object* v___x_2146_; lean_object* v___x_2147_; 
v___x_2146_ = lean_alloc_closure((void*)(l_Lean_Level_getParamSubst___boxed), 3, 2);
lean_closure_set(v___x_2146_, 0, v_paramNames_2144_);
lean_closure_set(v___x_2146_, 1, v_vs_2145_);
v___x_2147_ = l___private_Lean_Level_0__Lean_Level_substParams_go(v___x_2146_, v_u_2143_);
return v___x_2147_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Level_0__Lean_Level_geq_go(lean_object* v_u_2148_, lean_object* v_v_2149_){
_start:
{
lean_object* v_u_u2081_2164_; lean_object* v_u_u2082_2165_; lean_object* v_v_2166_; uint8_t v___x_2169_; 
v___x_2169_ = lean_level_eq(v_u_2148_, v_v_2149_);
if (v___x_2169_ == 0)
{
switch(lean_obj_tag(v_v_2149_))
{
case 0:
{
uint8_t v___x_2170_; 
v___x_2170_ = 1;
return v___x_2170_;
}
case 2:
{
lean_object* v_a_2171_; lean_object* v_a_2172_; uint8_t v___x_2173_; 
v_a_2171_ = lean_ctor_get(v_v_2149_, 0);
v_a_2172_ = lean_ctor_get(v_v_2149_, 1);
v___x_2173_ = l___private_Lean_Level_0__Lean_Level_geq_go(v_u_2148_, v_a_2171_);
if (v___x_2173_ == 0)
{
return v___x_2173_;
}
else
{
v_v_2149_ = v_a_2172_;
goto _start;
}
}
case 1:
{
switch(lean_obj_tag(v_u_2148_))
{
case 2:
{
lean_object* v_a_2175_; lean_object* v_a_2176_; 
v_a_2175_ = lean_ctor_get(v_u_2148_, 0);
v_a_2176_ = lean_ctor_get(v_u_2148_, 1);
v_u_u2081_2164_ = v_a_2175_;
v_u_u2082_2165_ = v_a_2176_;
v_v_2166_ = v_v_2149_;
goto v___jp_2163_;
}
case 3:
{
lean_object* v_a_2177_; 
v_a_2177_ = lean_ctor_get(v_u_2148_, 1);
v_u_2148_ = v_a_2177_;
goto _start;
}
case 1:
{
lean_object* v_a_2179_; lean_object* v_a_2180_; 
v_a_2179_ = lean_ctor_get(v_v_2149_, 0);
v_a_2180_ = lean_ctor_get(v_u_2148_, 0);
v_u_2148_ = v_a_2180_;
v_v_2149_ = v_a_2179_;
goto _start;
}
default: 
{
goto v___jp_2154_;
}
}
}
default: 
{
switch(lean_obj_tag(v_u_2148_))
{
case 2:
{
lean_object* v_a_2182_; lean_object* v_a_2183_; 
v_a_2182_ = lean_ctor_get(v_u_2148_, 0);
v_a_2183_ = lean_ctor_get(v_u_2148_, 1);
v_u_u2081_2164_ = v_a_2182_;
v_u_u2082_2165_ = v_a_2183_;
v_v_2166_ = v_v_2149_;
goto v___jp_2163_;
}
case 3:
{
lean_object* v_a_2184_; 
v_a_2184_ = lean_ctor_get(v_u_2148_, 1);
v_u_2148_ = v_a_2184_;
goto _start;
}
default: 
{
goto v___jp_2154_;
}
}
}
}
}
else
{
return v___x_2169_;
}
v___jp_2150_:
{
lean_object* v___x_2151_; lean_object* v___x_2152_; uint8_t v___x_2153_; 
v___x_2151_ = l_Lean_Level_getOffset(v_v_2149_);
v___x_2152_ = l_Lean_Level_getOffset(v_u_2148_);
v___x_2153_ = lean_nat_dec_le(v___x_2151_, v___x_2152_);
lean_dec(v___x_2152_);
lean_dec(v___x_2151_);
return v___x_2153_;
}
v___jp_2154_:
{
if (lean_obj_tag(v_v_2149_) == 3)
{
lean_object* v_a_2155_; lean_object* v_a_2156_; uint8_t v___x_2157_; 
v_a_2155_ = lean_ctor_get(v_v_2149_, 0);
v_a_2156_ = lean_ctor_get(v_v_2149_, 1);
v___x_2157_ = l___private_Lean_Level_0__Lean_Level_geq_go(v_u_2148_, v_a_2155_);
if (v___x_2157_ == 0)
{
return v___x_2157_;
}
else
{
v_v_2149_ = v_a_2156_;
goto _start;
}
}
else
{
lean_object* v_v_x27_2159_; lean_object* v___x_2160_; uint8_t v___x_2161_; 
v_v_x27_2159_ = l_Lean_Level_getLevelOffset(v_v_2149_);
v___x_2160_ = l_Lean_Level_getLevelOffset(v_u_2148_);
v___x_2161_ = lean_level_eq(v___x_2160_, v_v_x27_2159_);
lean_dec(v___x_2160_);
if (v___x_2161_ == 0)
{
uint8_t v___x_2162_; 
v___x_2162_ = l_Lean_Level_isZero(v_v_x27_2159_);
lean_dec(v_v_x27_2159_);
if (v___x_2162_ == 0)
{
return v___x_2162_;
}
else
{
goto v___jp_2150_;
}
}
else
{
lean_dec(v_v_x27_2159_);
goto v___jp_2150_;
}
}
}
v___jp_2163_:
{
uint8_t v___x_2167_; 
v___x_2167_ = l___private_Lean_Level_0__Lean_Level_geq_go(v_u_u2081_2164_, v_v_2166_);
if (v___x_2167_ == 0)
{
uint8_t v___x_2168_; 
v___x_2168_ = l___private_Lean_Level_0__Lean_Level_geq_go(v_u_u2082_2165_, v_v_2166_);
if (v___x_2168_ == 0)
{
goto v___jp_2154_;
}
else
{
return v___x_2168_;
}
}
else
{
return v___x_2167_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_geq_go___boxed(lean_object* v_u_2186_, lean_object* v_v_2187_){
_start:
{
uint8_t v_res_2188_; lean_object* v_r_2189_; 
v_res_2188_ = l___private_Lean_Level_0__Lean_Level_geq_go(v_u_2186_, v_v_2187_);
lean_dec(v_v_2187_);
lean_dec(v_u_2186_);
v_r_2189_ = lean_box(v_res_2188_);
return v_r_2189_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_geq_go_match__1_splitter___redArg(lean_object* v_u_2190_, lean_object* v_v_2191_, lean_object* v_h__1_2192_, lean_object* v_h__2_2193_, lean_object* v_h__3_2194_, lean_object* v_h__4_2195_, lean_object* v_h__5_2196_, lean_object* v_h__6_2197_){
_start:
{
switch(lean_obj_tag(v_v_2191_))
{
case 0:
{
lean_object* v___x_2198_; 
lean_dec(v_h__6_2197_);
lean_dec(v_h__5_2196_);
lean_dec(v_h__4_2195_);
lean_dec(v_h__3_2194_);
lean_dec(v_h__2_2193_);
v___x_2198_ = lean_apply_1(v_h__1_2192_, v_u_2190_);
return v___x_2198_;
}
case 2:
{
lean_object* v_a_2199_; lean_object* v_a_2200_; lean_object* v___x_2201_; 
lean_dec(v_h__6_2197_);
lean_dec(v_h__5_2196_);
lean_dec(v_h__4_2195_);
lean_dec(v_h__3_2194_);
lean_dec(v_h__1_2192_);
v_a_2199_ = lean_ctor_get(v_v_2191_, 0);
lean_inc(v_a_2199_);
v_a_2200_ = lean_ctor_get(v_v_2191_, 1);
lean_inc(v_a_2200_);
lean_dec_ref_known(v_v_2191_, 2);
v___x_2201_ = lean_apply_3(v_h__2_2193_, v_u_2190_, v_a_2199_, v_a_2200_);
return v___x_2201_;
}
case 1:
{
lean_dec(v_h__2_2193_);
lean_dec(v_h__1_2192_);
switch(lean_obj_tag(v_u_2190_))
{
case 2:
{
lean_object* v_a_2202_; lean_object* v_a_2203_; lean_object* v___x_2204_; 
lean_dec(v_h__6_2197_);
lean_dec(v_h__5_2196_);
lean_dec(v_h__4_2195_);
v_a_2202_ = lean_ctor_get(v_u_2190_, 0);
lean_inc(v_a_2202_);
v_a_2203_ = lean_ctor_get(v_u_2190_, 1);
lean_inc(v_a_2203_);
lean_dec_ref_known(v_u_2190_, 2);
v___x_2204_ = lean_apply_5(v_h__3_2194_, v_a_2202_, v_a_2203_, v_v_2191_, lean_box(0), lean_box(0));
return v___x_2204_;
}
case 3:
{
lean_object* v_a_2205_; lean_object* v_a_2206_; lean_object* v___x_2207_; 
lean_dec(v_h__6_2197_);
lean_dec(v_h__5_2196_);
lean_dec(v_h__3_2194_);
v_a_2205_ = lean_ctor_get(v_u_2190_, 0);
lean_inc(v_a_2205_);
v_a_2206_ = lean_ctor_get(v_u_2190_, 1);
lean_inc(v_a_2206_);
lean_dec_ref_known(v_u_2190_, 2);
v___x_2207_ = lean_apply_5(v_h__4_2195_, v_a_2205_, v_a_2206_, v_v_2191_, lean_box(0), lean_box(0));
return v___x_2207_;
}
case 1:
{
lean_object* v_a_2208_; lean_object* v_a_2209_; lean_object* v___x_2210_; 
lean_dec(v_h__6_2197_);
lean_dec(v_h__4_2195_);
lean_dec(v_h__3_2194_);
v_a_2208_ = lean_ctor_get(v_v_2191_, 0);
lean_inc(v_a_2208_);
lean_dec_ref_known(v_v_2191_, 1);
v_a_2209_ = lean_ctor_get(v_u_2190_, 0);
lean_inc(v_a_2209_);
lean_dec_ref_known(v_u_2190_, 1);
v___x_2210_ = lean_apply_2(v_h__5_2196_, v_a_2209_, v_a_2208_);
return v___x_2210_;
}
default: 
{
lean_object* v___x_2211_; 
lean_dec(v_h__5_2196_);
lean_dec(v_h__4_2195_);
lean_dec(v_h__3_2194_);
v___x_2211_ = lean_apply_7(v_h__6_2197_, v_u_2190_, v_v_2191_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_2211_;
}
}
}
default: 
{
lean_dec(v_h__5_2196_);
lean_dec(v_h__2_2193_);
lean_dec(v_h__1_2192_);
switch(lean_obj_tag(v_u_2190_))
{
case 2:
{
lean_object* v_a_2212_; lean_object* v_a_2213_; lean_object* v___x_2214_; 
lean_dec(v_h__6_2197_);
lean_dec(v_h__4_2195_);
v_a_2212_ = lean_ctor_get(v_u_2190_, 0);
lean_inc(v_a_2212_);
v_a_2213_ = lean_ctor_get(v_u_2190_, 1);
lean_inc(v_a_2213_);
lean_dec_ref_known(v_u_2190_, 2);
v___x_2214_ = lean_apply_5(v_h__3_2194_, v_a_2212_, v_a_2213_, v_v_2191_, lean_box(0), lean_box(0));
return v___x_2214_;
}
case 3:
{
lean_object* v_a_2215_; lean_object* v_a_2216_; lean_object* v___x_2217_; 
lean_dec(v_h__6_2197_);
lean_dec(v_h__3_2194_);
v_a_2215_ = lean_ctor_get(v_u_2190_, 0);
lean_inc(v_a_2215_);
v_a_2216_ = lean_ctor_get(v_u_2190_, 1);
lean_inc(v_a_2216_);
lean_dec_ref_known(v_u_2190_, 2);
v___x_2217_ = lean_apply_5(v_h__4_2195_, v_a_2215_, v_a_2216_, v_v_2191_, lean_box(0), lean_box(0));
return v___x_2217_;
}
default: 
{
lean_object* v___x_2218_; 
lean_dec(v_h__4_2195_);
lean_dec(v_h__3_2194_);
v___x_2218_ = lean_apply_7(v_h__6_2197_, v_u_2190_, v_v_2191_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_2218_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_geq_go_match__1_splitter(lean_object* v_motive_2219_, lean_object* v_u_2220_, lean_object* v_v_2221_, lean_object* v_h__1_2222_, lean_object* v_h__2_2223_, lean_object* v_h__3_2224_, lean_object* v_h__4_2225_, lean_object* v_h__5_2226_, lean_object* v_h__6_2227_){
_start:
{
switch(lean_obj_tag(v_v_2221_))
{
case 0:
{
lean_object* v___x_2228_; 
lean_dec(v_h__6_2227_);
lean_dec(v_h__5_2226_);
lean_dec(v_h__4_2225_);
lean_dec(v_h__3_2224_);
lean_dec(v_h__2_2223_);
v___x_2228_ = lean_apply_1(v_h__1_2222_, v_u_2220_);
return v___x_2228_;
}
case 2:
{
lean_object* v_a_2229_; lean_object* v_a_2230_; lean_object* v___x_2231_; 
lean_dec(v_h__6_2227_);
lean_dec(v_h__5_2226_);
lean_dec(v_h__4_2225_);
lean_dec(v_h__3_2224_);
lean_dec(v_h__1_2222_);
v_a_2229_ = lean_ctor_get(v_v_2221_, 0);
lean_inc(v_a_2229_);
v_a_2230_ = lean_ctor_get(v_v_2221_, 1);
lean_inc(v_a_2230_);
lean_dec_ref_known(v_v_2221_, 2);
v___x_2231_ = lean_apply_3(v_h__2_2223_, v_u_2220_, v_a_2229_, v_a_2230_);
return v___x_2231_;
}
case 1:
{
lean_dec(v_h__2_2223_);
lean_dec(v_h__1_2222_);
switch(lean_obj_tag(v_u_2220_))
{
case 2:
{
lean_object* v_a_2232_; lean_object* v_a_2233_; lean_object* v___x_2234_; 
lean_dec(v_h__6_2227_);
lean_dec(v_h__5_2226_);
lean_dec(v_h__4_2225_);
v_a_2232_ = lean_ctor_get(v_u_2220_, 0);
lean_inc(v_a_2232_);
v_a_2233_ = lean_ctor_get(v_u_2220_, 1);
lean_inc(v_a_2233_);
lean_dec_ref_known(v_u_2220_, 2);
v___x_2234_ = lean_apply_5(v_h__3_2224_, v_a_2232_, v_a_2233_, v_v_2221_, lean_box(0), lean_box(0));
return v___x_2234_;
}
case 3:
{
lean_object* v_a_2235_; lean_object* v_a_2236_; lean_object* v___x_2237_; 
lean_dec(v_h__6_2227_);
lean_dec(v_h__5_2226_);
lean_dec(v_h__3_2224_);
v_a_2235_ = lean_ctor_get(v_u_2220_, 0);
lean_inc(v_a_2235_);
v_a_2236_ = lean_ctor_get(v_u_2220_, 1);
lean_inc(v_a_2236_);
lean_dec_ref_known(v_u_2220_, 2);
v___x_2237_ = lean_apply_5(v_h__4_2225_, v_a_2235_, v_a_2236_, v_v_2221_, lean_box(0), lean_box(0));
return v___x_2237_;
}
case 1:
{
lean_object* v_a_2238_; lean_object* v_a_2239_; lean_object* v___x_2240_; 
lean_dec(v_h__6_2227_);
lean_dec(v_h__4_2225_);
lean_dec(v_h__3_2224_);
v_a_2238_ = lean_ctor_get(v_v_2221_, 0);
lean_inc(v_a_2238_);
lean_dec_ref_known(v_v_2221_, 1);
v_a_2239_ = lean_ctor_get(v_u_2220_, 0);
lean_inc(v_a_2239_);
lean_dec_ref_known(v_u_2220_, 1);
v___x_2240_ = lean_apply_2(v_h__5_2226_, v_a_2239_, v_a_2238_);
return v___x_2240_;
}
default: 
{
lean_object* v___x_2241_; 
lean_dec(v_h__5_2226_);
lean_dec(v_h__4_2225_);
lean_dec(v_h__3_2224_);
v___x_2241_ = lean_apply_7(v_h__6_2227_, v_u_2220_, v_v_2221_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_2241_;
}
}
}
default: 
{
lean_dec(v_h__5_2226_);
lean_dec(v_h__2_2223_);
lean_dec(v_h__1_2222_);
switch(lean_obj_tag(v_u_2220_))
{
case 2:
{
lean_object* v_a_2242_; lean_object* v_a_2243_; lean_object* v___x_2244_; 
lean_dec(v_h__6_2227_);
lean_dec(v_h__4_2225_);
v_a_2242_ = lean_ctor_get(v_u_2220_, 0);
lean_inc(v_a_2242_);
v_a_2243_ = lean_ctor_get(v_u_2220_, 1);
lean_inc(v_a_2243_);
lean_dec_ref_known(v_u_2220_, 2);
v___x_2244_ = lean_apply_5(v_h__3_2224_, v_a_2242_, v_a_2243_, v_v_2221_, lean_box(0), lean_box(0));
return v___x_2244_;
}
case 3:
{
lean_object* v_a_2245_; lean_object* v_a_2246_; lean_object* v___x_2247_; 
lean_dec(v_h__6_2227_);
lean_dec(v_h__3_2224_);
v_a_2245_ = lean_ctor_get(v_u_2220_, 0);
lean_inc(v_a_2245_);
v_a_2246_ = lean_ctor_get(v_u_2220_, 1);
lean_inc(v_a_2246_);
lean_dec_ref_known(v_u_2220_, 2);
v___x_2247_ = lean_apply_5(v_h__4_2225_, v_a_2245_, v_a_2246_, v_v_2221_, lean_box(0), lean_box(0));
return v___x_2247_;
}
default: 
{
lean_object* v___x_2248_; 
lean_dec(v_h__4_2225_);
lean_dec(v_h__3_2224_);
v___x_2248_ = lean_apply_7(v_h__6_2227_, v_u_2220_, v_v_2221_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_2248_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_isIMax_match__1_splitter___redArg(lean_object* v_x_2249_, lean_object* v_h__1_2250_, lean_object* v_h__2_2251_){
_start:
{
if (lean_obj_tag(v_x_2249_) == 3)
{
lean_object* v_a_2252_; lean_object* v_a_2253_; lean_object* v___x_2254_; 
lean_dec(v_h__2_2251_);
v_a_2252_ = lean_ctor_get(v_x_2249_, 0);
lean_inc(v_a_2252_);
v_a_2253_ = lean_ctor_get(v_x_2249_, 1);
lean_inc(v_a_2253_);
lean_dec_ref_known(v_x_2249_, 2);
v___x_2254_ = lean_apply_2(v_h__1_2250_, v_a_2252_, v_a_2253_);
return v___x_2254_;
}
else
{
lean_object* v___x_2255_; 
lean_dec(v_h__1_2250_);
v___x_2255_ = lean_apply_2(v_h__2_2251_, v_x_2249_, lean_box(0));
return v___x_2255_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_isIMax_match__1_splitter(lean_object* v_motive_2256_, lean_object* v_x_2257_, lean_object* v_h__1_2258_, lean_object* v_h__2_2259_){
_start:
{
if (lean_obj_tag(v_x_2257_) == 3)
{
lean_object* v_a_2260_; lean_object* v_a_2261_; lean_object* v___x_2262_; 
lean_dec(v_h__2_2259_);
v_a_2260_ = lean_ctor_get(v_x_2257_, 0);
lean_inc(v_a_2260_);
v_a_2261_ = lean_ctor_get(v_x_2257_, 1);
lean_inc(v_a_2261_);
lean_dec_ref_known(v_x_2257_, 2);
v___x_2262_ = lean_apply_2(v_h__1_2258_, v_a_2260_, v_a_2261_);
return v___x_2262_;
}
else
{
lean_object* v___x_2263_; 
lean_dec(v_h__1_2258_);
v___x_2263_ = lean_apply_2(v_h__2_2259_, v_x_2257_, lean_box(0));
return v___x_2263_;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Level_geq(lean_object* v_u_2264_, lean_object* v_v_2265_){
_start:
{
lean_object* v___x_2266_; lean_object* v___x_2267_; uint8_t v___x_2268_; 
v___x_2266_ = l_Lean_Level_normalize(v_u_2264_);
v___x_2267_ = l_Lean_Level_normalize(v_v_2265_);
v___x_2268_ = l___private_Lean_Level_0__Lean_Level_geq_go(v___x_2266_, v___x_2267_);
lean_dec(v___x_2267_);
lean_dec(v___x_2266_);
return v___x_2268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_geq___boxed(lean_object* v_u_2269_, lean_object* v_v_2270_){
_start:
{
uint8_t v_res_2271_; lean_object* v_r_2272_; 
v_res_2271_ = l_Lean_Level_geq(v_u_2269_, v_v_2270_);
lean_dec(v_v_2270_);
lean_dec(v_u_2269_);
v_r_2272_ = lean_box(v_res_2271_);
return v_r_2272_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Level_collectMVars_spec__1___redArg(lean_object* v_k_2273_, lean_object* v_v_2274_, lean_object* v_t_2275_){
_start:
{
if (lean_obj_tag(v_t_2275_) == 0)
{
lean_object* v_size_2276_; lean_object* v_k_2277_; lean_object* v_v_2278_; lean_object* v_l_2279_; lean_object* v_r_2280_; lean_object* v___x_2282_; uint8_t v_isShared_2283_; uint8_t v_isSharedCheck_2560_; 
v_size_2276_ = lean_ctor_get(v_t_2275_, 0);
v_k_2277_ = lean_ctor_get(v_t_2275_, 1);
v_v_2278_ = lean_ctor_get(v_t_2275_, 2);
v_l_2279_ = lean_ctor_get(v_t_2275_, 3);
v_r_2280_ = lean_ctor_get(v_t_2275_, 4);
v_isSharedCheck_2560_ = !lean_is_exclusive(v_t_2275_);
if (v_isSharedCheck_2560_ == 0)
{
v___x_2282_ = v_t_2275_;
v_isShared_2283_ = v_isSharedCheck_2560_;
goto v_resetjp_2281_;
}
else
{
lean_inc(v_r_2280_);
lean_inc(v_l_2279_);
lean_inc(v_v_2278_);
lean_inc(v_k_2277_);
lean_inc(v_size_2276_);
lean_dec(v_t_2275_);
v___x_2282_ = lean_box(0);
v_isShared_2283_ = v_isSharedCheck_2560_;
goto v_resetjp_2281_;
}
v_resetjp_2281_:
{
uint8_t v___x_2284_; 
v___x_2284_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2273_, v_k_2277_);
switch(v___x_2284_)
{
case 0:
{
lean_object* v_impl_2285_; lean_object* v___x_2286_; 
lean_dec(v_size_2276_);
v_impl_2285_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Level_collectMVars_spec__1___redArg(v_k_2273_, v_v_2274_, v_l_2279_);
v___x_2286_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_2280_) == 0)
{
lean_object* v_size_2287_; lean_object* v_size_2288_; lean_object* v_k_2289_; lean_object* v_v_2290_; lean_object* v_l_2291_; lean_object* v_r_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; uint8_t v___x_2295_; 
v_size_2287_ = lean_ctor_get(v_r_2280_, 0);
v_size_2288_ = lean_ctor_get(v_impl_2285_, 0);
v_k_2289_ = lean_ctor_get(v_impl_2285_, 1);
v_v_2290_ = lean_ctor_get(v_impl_2285_, 2);
v_l_2291_ = lean_ctor_get(v_impl_2285_, 3);
v_r_2292_ = lean_ctor_get(v_impl_2285_, 4);
lean_inc(v_r_2292_);
v___x_2293_ = lean_unsigned_to_nat(3u);
v___x_2294_ = lean_nat_mul(v___x_2293_, v_size_2287_);
v___x_2295_ = lean_nat_dec_lt(v___x_2294_, v_size_2288_);
lean_dec(v___x_2294_);
if (v___x_2295_ == 0)
{
lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2299_; 
lean_dec(v_r_2292_);
v___x_2296_ = lean_nat_add(v___x_2286_, v_size_2288_);
v___x_2297_ = lean_nat_add(v___x_2296_, v_size_2287_);
lean_dec(v___x_2296_);
if (v_isShared_2283_ == 0)
{
lean_ctor_set(v___x_2282_, 3, v_impl_2285_);
lean_ctor_set(v___x_2282_, 0, v___x_2297_);
v___x_2299_ = v___x_2282_;
goto v_reusejp_2298_;
}
else
{
lean_object* v_reuseFailAlloc_2300_; 
v_reuseFailAlloc_2300_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2300_, 0, v___x_2297_);
lean_ctor_set(v_reuseFailAlloc_2300_, 1, v_k_2277_);
lean_ctor_set(v_reuseFailAlloc_2300_, 2, v_v_2278_);
lean_ctor_set(v_reuseFailAlloc_2300_, 3, v_impl_2285_);
lean_ctor_set(v_reuseFailAlloc_2300_, 4, v_r_2280_);
v___x_2299_ = v_reuseFailAlloc_2300_;
goto v_reusejp_2298_;
}
v_reusejp_2298_:
{
return v___x_2299_;
}
}
else
{
lean_object* v___x_2302_; uint8_t v_isShared_2303_; uint8_t v_isSharedCheck_2366_; 
lean_inc(v_l_2291_);
lean_inc(v_v_2290_);
lean_inc(v_k_2289_);
lean_inc(v_size_2288_);
v_isSharedCheck_2366_ = !lean_is_exclusive(v_impl_2285_);
if (v_isSharedCheck_2366_ == 0)
{
lean_object* v_unused_2367_; lean_object* v_unused_2368_; lean_object* v_unused_2369_; lean_object* v_unused_2370_; lean_object* v_unused_2371_; 
v_unused_2367_ = lean_ctor_get(v_impl_2285_, 4);
lean_dec(v_unused_2367_);
v_unused_2368_ = lean_ctor_get(v_impl_2285_, 3);
lean_dec(v_unused_2368_);
v_unused_2369_ = lean_ctor_get(v_impl_2285_, 2);
lean_dec(v_unused_2369_);
v_unused_2370_ = lean_ctor_get(v_impl_2285_, 1);
lean_dec(v_unused_2370_);
v_unused_2371_ = lean_ctor_get(v_impl_2285_, 0);
lean_dec(v_unused_2371_);
v___x_2302_ = v_impl_2285_;
v_isShared_2303_ = v_isSharedCheck_2366_;
goto v_resetjp_2301_;
}
else
{
lean_dec(v_impl_2285_);
v___x_2302_ = lean_box(0);
v_isShared_2303_ = v_isSharedCheck_2366_;
goto v_resetjp_2301_;
}
v_resetjp_2301_:
{
lean_object* v_size_2304_; lean_object* v_size_2305_; lean_object* v_k_2306_; lean_object* v_v_2307_; lean_object* v_l_2308_; lean_object* v_r_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; uint8_t v___x_2312_; 
v_size_2304_ = lean_ctor_get(v_l_2291_, 0);
v_size_2305_ = lean_ctor_get(v_r_2292_, 0);
v_k_2306_ = lean_ctor_get(v_r_2292_, 1);
v_v_2307_ = lean_ctor_get(v_r_2292_, 2);
v_l_2308_ = lean_ctor_get(v_r_2292_, 3);
v_r_2309_ = lean_ctor_get(v_r_2292_, 4);
v___x_2310_ = lean_unsigned_to_nat(2u);
v___x_2311_ = lean_nat_mul(v___x_2310_, v_size_2304_);
v___x_2312_ = lean_nat_dec_lt(v_size_2305_, v___x_2311_);
lean_dec(v___x_2311_);
if (v___x_2312_ == 0)
{
lean_object* v___x_2314_; uint8_t v_isShared_2315_; uint8_t v_isSharedCheck_2341_; 
lean_inc(v_r_2309_);
lean_inc(v_l_2308_);
lean_inc(v_v_2307_);
lean_inc(v_k_2306_);
v_isSharedCheck_2341_ = !lean_is_exclusive(v_r_2292_);
if (v_isSharedCheck_2341_ == 0)
{
lean_object* v_unused_2342_; lean_object* v_unused_2343_; lean_object* v_unused_2344_; lean_object* v_unused_2345_; lean_object* v_unused_2346_; 
v_unused_2342_ = lean_ctor_get(v_r_2292_, 4);
lean_dec(v_unused_2342_);
v_unused_2343_ = lean_ctor_get(v_r_2292_, 3);
lean_dec(v_unused_2343_);
v_unused_2344_ = lean_ctor_get(v_r_2292_, 2);
lean_dec(v_unused_2344_);
v_unused_2345_ = lean_ctor_get(v_r_2292_, 1);
lean_dec(v_unused_2345_);
v_unused_2346_ = lean_ctor_get(v_r_2292_, 0);
lean_dec(v_unused_2346_);
v___x_2314_ = v_r_2292_;
v_isShared_2315_ = v_isSharedCheck_2341_;
goto v_resetjp_2313_;
}
else
{
lean_dec(v_r_2292_);
v___x_2314_ = lean_box(0);
v_isShared_2315_ = v_isSharedCheck_2341_;
goto v_resetjp_2313_;
}
v_resetjp_2313_:
{
lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___y_2319_; lean_object* v___y_2320_; lean_object* v___y_2321_; lean_object* v___x_2329_; lean_object* v___y_2331_; 
v___x_2316_ = lean_nat_add(v___x_2286_, v_size_2288_);
lean_dec(v_size_2288_);
v___x_2317_ = lean_nat_add(v___x_2316_, v_size_2287_);
lean_dec(v___x_2316_);
v___x_2329_ = lean_nat_add(v___x_2286_, v_size_2304_);
if (lean_obj_tag(v_l_2308_) == 0)
{
lean_object* v_size_2339_; 
v_size_2339_ = lean_ctor_get(v_l_2308_, 0);
lean_inc(v_size_2339_);
v___y_2331_ = v_size_2339_;
goto v___jp_2330_;
}
else
{
lean_object* v___x_2340_; 
v___x_2340_ = lean_unsigned_to_nat(0u);
v___y_2331_ = v___x_2340_;
goto v___jp_2330_;
}
v___jp_2318_:
{
lean_object* v___x_2322_; lean_object* v___x_2324_; 
v___x_2322_ = lean_nat_add(v___y_2319_, v___y_2321_);
lean_dec(v___y_2321_);
lean_dec(v___y_2319_);
if (v_isShared_2315_ == 0)
{
lean_ctor_set(v___x_2314_, 4, v_r_2280_);
lean_ctor_set(v___x_2314_, 3, v_r_2309_);
lean_ctor_set(v___x_2314_, 2, v_v_2278_);
lean_ctor_set(v___x_2314_, 1, v_k_2277_);
lean_ctor_set(v___x_2314_, 0, v___x_2322_);
v___x_2324_ = v___x_2314_;
goto v_reusejp_2323_;
}
else
{
lean_object* v_reuseFailAlloc_2328_; 
v_reuseFailAlloc_2328_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2328_, 0, v___x_2322_);
lean_ctor_set(v_reuseFailAlloc_2328_, 1, v_k_2277_);
lean_ctor_set(v_reuseFailAlloc_2328_, 2, v_v_2278_);
lean_ctor_set(v_reuseFailAlloc_2328_, 3, v_r_2309_);
lean_ctor_set(v_reuseFailAlloc_2328_, 4, v_r_2280_);
v___x_2324_ = v_reuseFailAlloc_2328_;
goto v_reusejp_2323_;
}
v_reusejp_2323_:
{
lean_object* v___x_2326_; 
if (v_isShared_2303_ == 0)
{
lean_ctor_set(v___x_2302_, 4, v___x_2324_);
lean_ctor_set(v___x_2302_, 3, v___y_2320_);
lean_ctor_set(v___x_2302_, 2, v_v_2307_);
lean_ctor_set(v___x_2302_, 1, v_k_2306_);
lean_ctor_set(v___x_2302_, 0, v___x_2317_);
v___x_2326_ = v___x_2302_;
goto v_reusejp_2325_;
}
else
{
lean_object* v_reuseFailAlloc_2327_; 
v_reuseFailAlloc_2327_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2327_, 0, v___x_2317_);
lean_ctor_set(v_reuseFailAlloc_2327_, 1, v_k_2306_);
lean_ctor_set(v_reuseFailAlloc_2327_, 2, v_v_2307_);
lean_ctor_set(v_reuseFailAlloc_2327_, 3, v___y_2320_);
lean_ctor_set(v_reuseFailAlloc_2327_, 4, v___x_2324_);
v___x_2326_ = v_reuseFailAlloc_2327_;
goto v_reusejp_2325_;
}
v_reusejp_2325_:
{
return v___x_2326_;
}
}
}
v___jp_2330_:
{
lean_object* v___x_2332_; lean_object* v___x_2334_; 
v___x_2332_ = lean_nat_add(v___x_2329_, v___y_2331_);
lean_dec(v___y_2331_);
lean_dec(v___x_2329_);
if (v_isShared_2283_ == 0)
{
lean_ctor_set(v___x_2282_, 4, v_l_2308_);
lean_ctor_set(v___x_2282_, 3, v_l_2291_);
lean_ctor_set(v___x_2282_, 2, v_v_2290_);
lean_ctor_set(v___x_2282_, 1, v_k_2289_);
lean_ctor_set(v___x_2282_, 0, v___x_2332_);
v___x_2334_ = v___x_2282_;
goto v_reusejp_2333_;
}
else
{
lean_object* v_reuseFailAlloc_2338_; 
v_reuseFailAlloc_2338_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2338_, 0, v___x_2332_);
lean_ctor_set(v_reuseFailAlloc_2338_, 1, v_k_2289_);
lean_ctor_set(v_reuseFailAlloc_2338_, 2, v_v_2290_);
lean_ctor_set(v_reuseFailAlloc_2338_, 3, v_l_2291_);
lean_ctor_set(v_reuseFailAlloc_2338_, 4, v_l_2308_);
v___x_2334_ = v_reuseFailAlloc_2338_;
goto v_reusejp_2333_;
}
v_reusejp_2333_:
{
lean_object* v___x_2335_; 
v___x_2335_ = lean_nat_add(v___x_2286_, v_size_2287_);
if (lean_obj_tag(v_r_2309_) == 0)
{
lean_object* v_size_2336_; 
v_size_2336_ = lean_ctor_get(v_r_2309_, 0);
lean_inc(v_size_2336_);
v___y_2319_ = v___x_2335_;
v___y_2320_ = v___x_2334_;
v___y_2321_ = v_size_2336_;
goto v___jp_2318_;
}
else
{
lean_object* v___x_2337_; 
v___x_2337_ = lean_unsigned_to_nat(0u);
v___y_2319_ = v___x_2335_;
v___y_2320_ = v___x_2334_;
v___y_2321_ = v___x_2337_;
goto v___jp_2318_;
}
}
}
}
}
else
{
lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2352_; 
lean_del_object(v___x_2282_);
v___x_2347_ = lean_nat_add(v___x_2286_, v_size_2288_);
lean_dec(v_size_2288_);
v___x_2348_ = lean_nat_add(v___x_2347_, v_size_2287_);
lean_dec(v___x_2347_);
v___x_2349_ = lean_nat_add(v___x_2286_, v_size_2287_);
v___x_2350_ = lean_nat_add(v___x_2349_, v_size_2305_);
lean_dec(v___x_2349_);
lean_inc_ref(v_r_2280_);
if (v_isShared_2303_ == 0)
{
lean_ctor_set(v___x_2302_, 4, v_r_2280_);
lean_ctor_set(v___x_2302_, 3, v_r_2292_);
lean_ctor_set(v___x_2302_, 2, v_v_2278_);
lean_ctor_set(v___x_2302_, 1, v_k_2277_);
lean_ctor_set(v___x_2302_, 0, v___x_2350_);
v___x_2352_ = v___x_2302_;
goto v_reusejp_2351_;
}
else
{
lean_object* v_reuseFailAlloc_2365_; 
v_reuseFailAlloc_2365_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2365_, 0, v___x_2350_);
lean_ctor_set(v_reuseFailAlloc_2365_, 1, v_k_2277_);
lean_ctor_set(v_reuseFailAlloc_2365_, 2, v_v_2278_);
lean_ctor_set(v_reuseFailAlloc_2365_, 3, v_r_2292_);
lean_ctor_set(v_reuseFailAlloc_2365_, 4, v_r_2280_);
v___x_2352_ = v_reuseFailAlloc_2365_;
goto v_reusejp_2351_;
}
v_reusejp_2351_:
{
lean_object* v___x_2354_; uint8_t v_isShared_2355_; uint8_t v_isSharedCheck_2359_; 
v_isSharedCheck_2359_ = !lean_is_exclusive(v_r_2280_);
if (v_isSharedCheck_2359_ == 0)
{
lean_object* v_unused_2360_; lean_object* v_unused_2361_; lean_object* v_unused_2362_; lean_object* v_unused_2363_; lean_object* v_unused_2364_; 
v_unused_2360_ = lean_ctor_get(v_r_2280_, 4);
lean_dec(v_unused_2360_);
v_unused_2361_ = lean_ctor_get(v_r_2280_, 3);
lean_dec(v_unused_2361_);
v_unused_2362_ = lean_ctor_get(v_r_2280_, 2);
lean_dec(v_unused_2362_);
v_unused_2363_ = lean_ctor_get(v_r_2280_, 1);
lean_dec(v_unused_2363_);
v_unused_2364_ = lean_ctor_get(v_r_2280_, 0);
lean_dec(v_unused_2364_);
v___x_2354_ = v_r_2280_;
v_isShared_2355_ = v_isSharedCheck_2359_;
goto v_resetjp_2353_;
}
else
{
lean_dec(v_r_2280_);
v___x_2354_ = lean_box(0);
v_isShared_2355_ = v_isSharedCheck_2359_;
goto v_resetjp_2353_;
}
v_resetjp_2353_:
{
lean_object* v___x_2357_; 
if (v_isShared_2355_ == 0)
{
lean_ctor_set(v___x_2354_, 4, v___x_2352_);
lean_ctor_set(v___x_2354_, 3, v_l_2291_);
lean_ctor_set(v___x_2354_, 2, v_v_2290_);
lean_ctor_set(v___x_2354_, 1, v_k_2289_);
lean_ctor_set(v___x_2354_, 0, v___x_2348_);
v___x_2357_ = v___x_2354_;
goto v_reusejp_2356_;
}
else
{
lean_object* v_reuseFailAlloc_2358_; 
v_reuseFailAlloc_2358_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2358_, 0, v___x_2348_);
lean_ctor_set(v_reuseFailAlloc_2358_, 1, v_k_2289_);
lean_ctor_set(v_reuseFailAlloc_2358_, 2, v_v_2290_);
lean_ctor_set(v_reuseFailAlloc_2358_, 3, v_l_2291_);
lean_ctor_set(v_reuseFailAlloc_2358_, 4, v___x_2352_);
v___x_2357_ = v_reuseFailAlloc_2358_;
goto v_reusejp_2356_;
}
v_reusejp_2356_:
{
return v___x_2357_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_2372_; 
v_l_2372_ = lean_ctor_get(v_impl_2285_, 3);
if (lean_obj_tag(v_l_2372_) == 0)
{
lean_object* v_r_2373_; lean_object* v_k_2374_; lean_object* v_v_2375_; lean_object* v___x_2377_; uint8_t v_isShared_2378_; uint8_t v_isSharedCheck_2386_; 
lean_inc_ref(v_l_2372_);
v_r_2373_ = lean_ctor_get(v_impl_2285_, 4);
v_k_2374_ = lean_ctor_get(v_impl_2285_, 1);
v_v_2375_ = lean_ctor_get(v_impl_2285_, 2);
v_isSharedCheck_2386_ = !lean_is_exclusive(v_impl_2285_);
if (v_isSharedCheck_2386_ == 0)
{
lean_object* v_unused_2387_; lean_object* v_unused_2388_; 
v_unused_2387_ = lean_ctor_get(v_impl_2285_, 3);
lean_dec(v_unused_2387_);
v_unused_2388_ = lean_ctor_get(v_impl_2285_, 0);
lean_dec(v_unused_2388_);
v___x_2377_ = v_impl_2285_;
v_isShared_2378_ = v_isSharedCheck_2386_;
goto v_resetjp_2376_;
}
else
{
lean_inc(v_r_2373_);
lean_inc(v_v_2375_);
lean_inc(v_k_2374_);
lean_dec(v_impl_2285_);
v___x_2377_ = lean_box(0);
v_isShared_2378_ = v_isSharedCheck_2386_;
goto v_resetjp_2376_;
}
v_resetjp_2376_:
{
lean_object* v___x_2379_; lean_object* v___x_2381_; 
v___x_2379_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_2373_);
if (v_isShared_2378_ == 0)
{
lean_ctor_set(v___x_2377_, 3, v_r_2373_);
lean_ctor_set(v___x_2377_, 2, v_v_2278_);
lean_ctor_set(v___x_2377_, 1, v_k_2277_);
lean_ctor_set(v___x_2377_, 0, v___x_2286_);
v___x_2381_ = v___x_2377_;
goto v_reusejp_2380_;
}
else
{
lean_object* v_reuseFailAlloc_2385_; 
v_reuseFailAlloc_2385_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2385_, 0, v___x_2286_);
lean_ctor_set(v_reuseFailAlloc_2385_, 1, v_k_2277_);
lean_ctor_set(v_reuseFailAlloc_2385_, 2, v_v_2278_);
lean_ctor_set(v_reuseFailAlloc_2385_, 3, v_r_2373_);
lean_ctor_set(v_reuseFailAlloc_2385_, 4, v_r_2373_);
v___x_2381_ = v_reuseFailAlloc_2385_;
goto v_reusejp_2380_;
}
v_reusejp_2380_:
{
lean_object* v___x_2383_; 
if (v_isShared_2283_ == 0)
{
lean_ctor_set(v___x_2282_, 4, v___x_2381_);
lean_ctor_set(v___x_2282_, 3, v_l_2372_);
lean_ctor_set(v___x_2282_, 2, v_v_2375_);
lean_ctor_set(v___x_2282_, 1, v_k_2374_);
lean_ctor_set(v___x_2282_, 0, v___x_2379_);
v___x_2383_ = v___x_2282_;
goto v_reusejp_2382_;
}
else
{
lean_object* v_reuseFailAlloc_2384_; 
v_reuseFailAlloc_2384_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2384_, 0, v___x_2379_);
lean_ctor_set(v_reuseFailAlloc_2384_, 1, v_k_2374_);
lean_ctor_set(v_reuseFailAlloc_2384_, 2, v_v_2375_);
lean_ctor_set(v_reuseFailAlloc_2384_, 3, v_l_2372_);
lean_ctor_set(v_reuseFailAlloc_2384_, 4, v___x_2381_);
v___x_2383_ = v_reuseFailAlloc_2384_;
goto v_reusejp_2382_;
}
v_reusejp_2382_:
{
return v___x_2383_;
}
}
}
}
else
{
lean_object* v_r_2389_; 
v_r_2389_ = lean_ctor_get(v_impl_2285_, 4);
lean_inc(v_r_2389_);
if (lean_obj_tag(v_r_2389_) == 0)
{
lean_object* v_k_2390_; lean_object* v_v_2391_; lean_object* v___x_2393_; uint8_t v_isShared_2394_; uint8_t v_isSharedCheck_2414_; 
lean_inc(v_l_2372_);
v_k_2390_ = lean_ctor_get(v_impl_2285_, 1);
v_v_2391_ = lean_ctor_get(v_impl_2285_, 2);
v_isSharedCheck_2414_ = !lean_is_exclusive(v_impl_2285_);
if (v_isSharedCheck_2414_ == 0)
{
lean_object* v_unused_2415_; lean_object* v_unused_2416_; lean_object* v_unused_2417_; 
v_unused_2415_ = lean_ctor_get(v_impl_2285_, 4);
lean_dec(v_unused_2415_);
v_unused_2416_ = lean_ctor_get(v_impl_2285_, 3);
lean_dec(v_unused_2416_);
v_unused_2417_ = lean_ctor_get(v_impl_2285_, 0);
lean_dec(v_unused_2417_);
v___x_2393_ = v_impl_2285_;
v_isShared_2394_ = v_isSharedCheck_2414_;
goto v_resetjp_2392_;
}
else
{
lean_inc(v_v_2391_);
lean_inc(v_k_2390_);
lean_dec(v_impl_2285_);
v___x_2393_ = lean_box(0);
v_isShared_2394_ = v_isSharedCheck_2414_;
goto v_resetjp_2392_;
}
v_resetjp_2392_:
{
lean_object* v_k_2395_; lean_object* v_v_2396_; lean_object* v___x_2398_; uint8_t v_isShared_2399_; uint8_t v_isSharedCheck_2410_; 
v_k_2395_ = lean_ctor_get(v_r_2389_, 1);
v_v_2396_ = lean_ctor_get(v_r_2389_, 2);
v_isSharedCheck_2410_ = !lean_is_exclusive(v_r_2389_);
if (v_isSharedCheck_2410_ == 0)
{
lean_object* v_unused_2411_; lean_object* v_unused_2412_; lean_object* v_unused_2413_; 
v_unused_2411_ = lean_ctor_get(v_r_2389_, 4);
lean_dec(v_unused_2411_);
v_unused_2412_ = lean_ctor_get(v_r_2389_, 3);
lean_dec(v_unused_2412_);
v_unused_2413_ = lean_ctor_get(v_r_2389_, 0);
lean_dec(v_unused_2413_);
v___x_2398_ = v_r_2389_;
v_isShared_2399_ = v_isSharedCheck_2410_;
goto v_resetjp_2397_;
}
else
{
lean_inc(v_v_2396_);
lean_inc(v_k_2395_);
lean_dec(v_r_2389_);
v___x_2398_ = lean_box(0);
v_isShared_2399_ = v_isSharedCheck_2410_;
goto v_resetjp_2397_;
}
v_resetjp_2397_:
{
lean_object* v___x_2400_; lean_object* v___x_2402_; 
v___x_2400_ = lean_unsigned_to_nat(3u);
if (v_isShared_2399_ == 0)
{
lean_ctor_set(v___x_2398_, 4, v_l_2372_);
lean_ctor_set(v___x_2398_, 3, v_l_2372_);
lean_ctor_set(v___x_2398_, 2, v_v_2391_);
lean_ctor_set(v___x_2398_, 1, v_k_2390_);
lean_ctor_set(v___x_2398_, 0, v___x_2286_);
v___x_2402_ = v___x_2398_;
goto v_reusejp_2401_;
}
else
{
lean_object* v_reuseFailAlloc_2409_; 
v_reuseFailAlloc_2409_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2409_, 0, v___x_2286_);
lean_ctor_set(v_reuseFailAlloc_2409_, 1, v_k_2390_);
lean_ctor_set(v_reuseFailAlloc_2409_, 2, v_v_2391_);
lean_ctor_set(v_reuseFailAlloc_2409_, 3, v_l_2372_);
lean_ctor_set(v_reuseFailAlloc_2409_, 4, v_l_2372_);
v___x_2402_ = v_reuseFailAlloc_2409_;
goto v_reusejp_2401_;
}
v_reusejp_2401_:
{
lean_object* v___x_2404_; 
if (v_isShared_2394_ == 0)
{
lean_ctor_set(v___x_2393_, 4, v_l_2372_);
lean_ctor_set(v___x_2393_, 2, v_v_2278_);
lean_ctor_set(v___x_2393_, 1, v_k_2277_);
lean_ctor_set(v___x_2393_, 0, v___x_2286_);
v___x_2404_ = v___x_2393_;
goto v_reusejp_2403_;
}
else
{
lean_object* v_reuseFailAlloc_2408_; 
v_reuseFailAlloc_2408_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2408_, 0, v___x_2286_);
lean_ctor_set(v_reuseFailAlloc_2408_, 1, v_k_2277_);
lean_ctor_set(v_reuseFailAlloc_2408_, 2, v_v_2278_);
lean_ctor_set(v_reuseFailAlloc_2408_, 3, v_l_2372_);
lean_ctor_set(v_reuseFailAlloc_2408_, 4, v_l_2372_);
v___x_2404_ = v_reuseFailAlloc_2408_;
goto v_reusejp_2403_;
}
v_reusejp_2403_:
{
lean_object* v___x_2406_; 
if (v_isShared_2283_ == 0)
{
lean_ctor_set(v___x_2282_, 4, v___x_2404_);
lean_ctor_set(v___x_2282_, 3, v___x_2402_);
lean_ctor_set(v___x_2282_, 2, v_v_2396_);
lean_ctor_set(v___x_2282_, 1, v_k_2395_);
lean_ctor_set(v___x_2282_, 0, v___x_2400_);
v___x_2406_ = v___x_2282_;
goto v_reusejp_2405_;
}
else
{
lean_object* v_reuseFailAlloc_2407_; 
v_reuseFailAlloc_2407_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2407_, 0, v___x_2400_);
lean_ctor_set(v_reuseFailAlloc_2407_, 1, v_k_2395_);
lean_ctor_set(v_reuseFailAlloc_2407_, 2, v_v_2396_);
lean_ctor_set(v_reuseFailAlloc_2407_, 3, v___x_2402_);
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
}
}
else
{
lean_object* v___x_2418_; lean_object* v___x_2420_; 
v___x_2418_ = lean_unsigned_to_nat(2u);
if (v_isShared_2283_ == 0)
{
lean_ctor_set(v___x_2282_, 4, v_r_2389_);
lean_ctor_set(v___x_2282_, 3, v_impl_2285_);
lean_ctor_set(v___x_2282_, 0, v___x_2418_);
v___x_2420_ = v___x_2282_;
goto v_reusejp_2419_;
}
else
{
lean_object* v_reuseFailAlloc_2421_; 
v_reuseFailAlloc_2421_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2421_, 0, v___x_2418_);
lean_ctor_set(v_reuseFailAlloc_2421_, 1, v_k_2277_);
lean_ctor_set(v_reuseFailAlloc_2421_, 2, v_v_2278_);
lean_ctor_set(v_reuseFailAlloc_2421_, 3, v_impl_2285_);
lean_ctor_set(v_reuseFailAlloc_2421_, 4, v_r_2389_);
v___x_2420_ = v_reuseFailAlloc_2421_;
goto v_reusejp_2419_;
}
v_reusejp_2419_:
{
return v___x_2420_;
}
}
}
}
}
case 1:
{
lean_object* v___x_2423_; 
lean_dec(v_v_2278_);
lean_dec(v_k_2277_);
if (v_isShared_2283_ == 0)
{
lean_ctor_set(v___x_2282_, 2, v_v_2274_);
lean_ctor_set(v___x_2282_, 1, v_k_2273_);
v___x_2423_ = v___x_2282_;
goto v_reusejp_2422_;
}
else
{
lean_object* v_reuseFailAlloc_2424_; 
v_reuseFailAlloc_2424_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2424_, 0, v_size_2276_);
lean_ctor_set(v_reuseFailAlloc_2424_, 1, v_k_2273_);
lean_ctor_set(v_reuseFailAlloc_2424_, 2, v_v_2274_);
lean_ctor_set(v_reuseFailAlloc_2424_, 3, v_l_2279_);
lean_ctor_set(v_reuseFailAlloc_2424_, 4, v_r_2280_);
v___x_2423_ = v_reuseFailAlloc_2424_;
goto v_reusejp_2422_;
}
v_reusejp_2422_:
{
return v___x_2423_;
}
}
default: 
{
lean_object* v_impl_2425_; lean_object* v___x_2426_; 
lean_dec(v_size_2276_);
v_impl_2425_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Level_collectMVars_spec__1___redArg(v_k_2273_, v_v_2274_, v_r_2280_);
v___x_2426_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_2279_) == 0)
{
lean_object* v_size_2427_; lean_object* v_size_2428_; lean_object* v_k_2429_; lean_object* v_v_2430_; lean_object* v_l_2431_; lean_object* v_r_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; uint8_t v___x_2435_; 
v_size_2427_ = lean_ctor_get(v_l_2279_, 0);
v_size_2428_ = lean_ctor_get(v_impl_2425_, 0);
v_k_2429_ = lean_ctor_get(v_impl_2425_, 1);
v_v_2430_ = lean_ctor_get(v_impl_2425_, 2);
v_l_2431_ = lean_ctor_get(v_impl_2425_, 3);
lean_inc(v_l_2431_);
v_r_2432_ = lean_ctor_get(v_impl_2425_, 4);
v___x_2433_ = lean_unsigned_to_nat(3u);
v___x_2434_ = lean_nat_mul(v___x_2433_, v_size_2427_);
v___x_2435_ = lean_nat_dec_lt(v___x_2434_, v_size_2428_);
lean_dec(v___x_2434_);
if (v___x_2435_ == 0)
{
lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2439_; 
lean_dec(v_l_2431_);
v___x_2436_ = lean_nat_add(v___x_2426_, v_size_2427_);
v___x_2437_ = lean_nat_add(v___x_2436_, v_size_2428_);
lean_dec(v___x_2436_);
if (v_isShared_2283_ == 0)
{
lean_ctor_set(v___x_2282_, 4, v_impl_2425_);
lean_ctor_set(v___x_2282_, 0, v___x_2437_);
v___x_2439_ = v___x_2282_;
goto v_reusejp_2438_;
}
else
{
lean_object* v_reuseFailAlloc_2440_; 
v_reuseFailAlloc_2440_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2440_, 0, v___x_2437_);
lean_ctor_set(v_reuseFailAlloc_2440_, 1, v_k_2277_);
lean_ctor_set(v_reuseFailAlloc_2440_, 2, v_v_2278_);
lean_ctor_set(v_reuseFailAlloc_2440_, 3, v_l_2279_);
lean_ctor_set(v_reuseFailAlloc_2440_, 4, v_impl_2425_);
v___x_2439_ = v_reuseFailAlloc_2440_;
goto v_reusejp_2438_;
}
v_reusejp_2438_:
{
return v___x_2439_;
}
}
else
{
lean_object* v___x_2442_; uint8_t v_isShared_2443_; uint8_t v_isSharedCheck_2504_; 
lean_inc(v_r_2432_);
lean_inc(v_v_2430_);
lean_inc(v_k_2429_);
lean_inc(v_size_2428_);
v_isSharedCheck_2504_ = !lean_is_exclusive(v_impl_2425_);
if (v_isSharedCheck_2504_ == 0)
{
lean_object* v_unused_2505_; lean_object* v_unused_2506_; lean_object* v_unused_2507_; lean_object* v_unused_2508_; lean_object* v_unused_2509_; 
v_unused_2505_ = lean_ctor_get(v_impl_2425_, 4);
lean_dec(v_unused_2505_);
v_unused_2506_ = lean_ctor_get(v_impl_2425_, 3);
lean_dec(v_unused_2506_);
v_unused_2507_ = lean_ctor_get(v_impl_2425_, 2);
lean_dec(v_unused_2507_);
v_unused_2508_ = lean_ctor_get(v_impl_2425_, 1);
lean_dec(v_unused_2508_);
v_unused_2509_ = lean_ctor_get(v_impl_2425_, 0);
lean_dec(v_unused_2509_);
v___x_2442_ = v_impl_2425_;
v_isShared_2443_ = v_isSharedCheck_2504_;
goto v_resetjp_2441_;
}
else
{
lean_dec(v_impl_2425_);
v___x_2442_ = lean_box(0);
v_isShared_2443_ = v_isSharedCheck_2504_;
goto v_resetjp_2441_;
}
v_resetjp_2441_:
{
lean_object* v_size_2444_; lean_object* v_k_2445_; lean_object* v_v_2446_; lean_object* v_l_2447_; lean_object* v_r_2448_; lean_object* v_size_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; uint8_t v___x_2452_; 
v_size_2444_ = lean_ctor_get(v_l_2431_, 0);
v_k_2445_ = lean_ctor_get(v_l_2431_, 1);
v_v_2446_ = lean_ctor_get(v_l_2431_, 2);
v_l_2447_ = lean_ctor_get(v_l_2431_, 3);
v_r_2448_ = lean_ctor_get(v_l_2431_, 4);
v_size_2449_ = lean_ctor_get(v_r_2432_, 0);
v___x_2450_ = lean_unsigned_to_nat(2u);
v___x_2451_ = lean_nat_mul(v___x_2450_, v_size_2449_);
v___x_2452_ = lean_nat_dec_lt(v_size_2444_, v___x_2451_);
lean_dec(v___x_2451_);
if (v___x_2452_ == 0)
{
lean_object* v___x_2454_; uint8_t v_isShared_2455_; uint8_t v_isSharedCheck_2480_; 
lean_inc(v_r_2448_);
lean_inc(v_l_2447_);
lean_inc(v_v_2446_);
lean_inc(v_k_2445_);
v_isSharedCheck_2480_ = !lean_is_exclusive(v_l_2431_);
if (v_isSharedCheck_2480_ == 0)
{
lean_object* v_unused_2481_; lean_object* v_unused_2482_; lean_object* v_unused_2483_; lean_object* v_unused_2484_; lean_object* v_unused_2485_; 
v_unused_2481_ = lean_ctor_get(v_l_2431_, 4);
lean_dec(v_unused_2481_);
v_unused_2482_ = lean_ctor_get(v_l_2431_, 3);
lean_dec(v_unused_2482_);
v_unused_2483_ = lean_ctor_get(v_l_2431_, 2);
lean_dec(v_unused_2483_);
v_unused_2484_ = lean_ctor_get(v_l_2431_, 1);
lean_dec(v_unused_2484_);
v_unused_2485_ = lean_ctor_get(v_l_2431_, 0);
lean_dec(v_unused_2485_);
v___x_2454_ = v_l_2431_;
v_isShared_2455_ = v_isSharedCheck_2480_;
goto v_resetjp_2453_;
}
else
{
lean_dec(v_l_2431_);
v___x_2454_ = lean_box(0);
v_isShared_2455_ = v_isSharedCheck_2480_;
goto v_resetjp_2453_;
}
v_resetjp_2453_:
{
lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___y_2459_; lean_object* v___y_2460_; lean_object* v___y_2461_; lean_object* v___y_2470_; 
v___x_2456_ = lean_nat_add(v___x_2426_, v_size_2427_);
v___x_2457_ = lean_nat_add(v___x_2456_, v_size_2428_);
lean_dec(v_size_2428_);
if (lean_obj_tag(v_l_2447_) == 0)
{
lean_object* v_size_2478_; 
v_size_2478_ = lean_ctor_get(v_l_2447_, 0);
lean_inc(v_size_2478_);
v___y_2470_ = v_size_2478_;
goto v___jp_2469_;
}
else
{
lean_object* v___x_2479_; 
v___x_2479_ = lean_unsigned_to_nat(0u);
v___y_2470_ = v___x_2479_;
goto v___jp_2469_;
}
v___jp_2458_:
{
lean_object* v___x_2462_; lean_object* v___x_2464_; 
v___x_2462_ = lean_nat_add(v___y_2460_, v___y_2461_);
lean_dec(v___y_2461_);
lean_dec(v___y_2460_);
if (v_isShared_2455_ == 0)
{
lean_ctor_set(v___x_2454_, 4, v_r_2432_);
lean_ctor_set(v___x_2454_, 3, v_r_2448_);
lean_ctor_set(v___x_2454_, 2, v_v_2430_);
lean_ctor_set(v___x_2454_, 1, v_k_2429_);
lean_ctor_set(v___x_2454_, 0, v___x_2462_);
v___x_2464_ = v___x_2454_;
goto v_reusejp_2463_;
}
else
{
lean_object* v_reuseFailAlloc_2468_; 
v_reuseFailAlloc_2468_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2468_, 0, v___x_2462_);
lean_ctor_set(v_reuseFailAlloc_2468_, 1, v_k_2429_);
lean_ctor_set(v_reuseFailAlloc_2468_, 2, v_v_2430_);
lean_ctor_set(v_reuseFailAlloc_2468_, 3, v_r_2448_);
lean_ctor_set(v_reuseFailAlloc_2468_, 4, v_r_2432_);
v___x_2464_ = v_reuseFailAlloc_2468_;
goto v_reusejp_2463_;
}
v_reusejp_2463_:
{
lean_object* v___x_2466_; 
if (v_isShared_2443_ == 0)
{
lean_ctor_set(v___x_2442_, 4, v___x_2464_);
lean_ctor_set(v___x_2442_, 3, v___y_2459_);
lean_ctor_set(v___x_2442_, 2, v_v_2446_);
lean_ctor_set(v___x_2442_, 1, v_k_2445_);
lean_ctor_set(v___x_2442_, 0, v___x_2457_);
v___x_2466_ = v___x_2442_;
goto v_reusejp_2465_;
}
else
{
lean_object* v_reuseFailAlloc_2467_; 
v_reuseFailAlloc_2467_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2467_, 0, v___x_2457_);
lean_ctor_set(v_reuseFailAlloc_2467_, 1, v_k_2445_);
lean_ctor_set(v_reuseFailAlloc_2467_, 2, v_v_2446_);
lean_ctor_set(v_reuseFailAlloc_2467_, 3, v___y_2459_);
lean_ctor_set(v_reuseFailAlloc_2467_, 4, v___x_2464_);
v___x_2466_ = v_reuseFailAlloc_2467_;
goto v_reusejp_2465_;
}
v_reusejp_2465_:
{
return v___x_2466_;
}
}
}
v___jp_2469_:
{
lean_object* v___x_2471_; lean_object* v___x_2473_; 
v___x_2471_ = lean_nat_add(v___x_2456_, v___y_2470_);
lean_dec(v___y_2470_);
lean_dec(v___x_2456_);
if (v_isShared_2283_ == 0)
{
lean_ctor_set(v___x_2282_, 4, v_l_2447_);
lean_ctor_set(v___x_2282_, 0, v___x_2471_);
v___x_2473_ = v___x_2282_;
goto v_reusejp_2472_;
}
else
{
lean_object* v_reuseFailAlloc_2477_; 
v_reuseFailAlloc_2477_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2477_, 0, v___x_2471_);
lean_ctor_set(v_reuseFailAlloc_2477_, 1, v_k_2277_);
lean_ctor_set(v_reuseFailAlloc_2477_, 2, v_v_2278_);
lean_ctor_set(v_reuseFailAlloc_2477_, 3, v_l_2279_);
lean_ctor_set(v_reuseFailAlloc_2477_, 4, v_l_2447_);
v___x_2473_ = v_reuseFailAlloc_2477_;
goto v_reusejp_2472_;
}
v_reusejp_2472_:
{
lean_object* v___x_2474_; 
v___x_2474_ = lean_nat_add(v___x_2426_, v_size_2449_);
if (lean_obj_tag(v_r_2448_) == 0)
{
lean_object* v_size_2475_; 
v_size_2475_ = lean_ctor_get(v_r_2448_, 0);
lean_inc(v_size_2475_);
v___y_2459_ = v___x_2473_;
v___y_2460_ = v___x_2474_;
v___y_2461_ = v_size_2475_;
goto v___jp_2458_;
}
else
{
lean_object* v___x_2476_; 
v___x_2476_ = lean_unsigned_to_nat(0u);
v___y_2459_ = v___x_2473_;
v___y_2460_ = v___x_2474_;
v___y_2461_ = v___x_2476_;
goto v___jp_2458_;
}
}
}
}
}
else
{
lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2490_; 
lean_del_object(v___x_2282_);
v___x_2486_ = lean_nat_add(v___x_2426_, v_size_2427_);
v___x_2487_ = lean_nat_add(v___x_2486_, v_size_2428_);
lean_dec(v_size_2428_);
v___x_2488_ = lean_nat_add(v___x_2486_, v_size_2444_);
lean_dec(v___x_2486_);
lean_inc_ref(v_l_2279_);
if (v_isShared_2443_ == 0)
{
lean_ctor_set(v___x_2442_, 4, v_l_2431_);
lean_ctor_set(v___x_2442_, 3, v_l_2279_);
lean_ctor_set(v___x_2442_, 2, v_v_2278_);
lean_ctor_set(v___x_2442_, 1, v_k_2277_);
lean_ctor_set(v___x_2442_, 0, v___x_2488_);
v___x_2490_ = v___x_2442_;
goto v_reusejp_2489_;
}
else
{
lean_object* v_reuseFailAlloc_2503_; 
v_reuseFailAlloc_2503_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2503_, 0, v___x_2488_);
lean_ctor_set(v_reuseFailAlloc_2503_, 1, v_k_2277_);
lean_ctor_set(v_reuseFailAlloc_2503_, 2, v_v_2278_);
lean_ctor_set(v_reuseFailAlloc_2503_, 3, v_l_2279_);
lean_ctor_set(v_reuseFailAlloc_2503_, 4, v_l_2431_);
v___x_2490_ = v_reuseFailAlloc_2503_;
goto v_reusejp_2489_;
}
v_reusejp_2489_:
{
lean_object* v___x_2492_; uint8_t v_isShared_2493_; uint8_t v_isSharedCheck_2497_; 
v_isSharedCheck_2497_ = !lean_is_exclusive(v_l_2279_);
if (v_isSharedCheck_2497_ == 0)
{
lean_object* v_unused_2498_; lean_object* v_unused_2499_; lean_object* v_unused_2500_; lean_object* v_unused_2501_; lean_object* v_unused_2502_; 
v_unused_2498_ = lean_ctor_get(v_l_2279_, 4);
lean_dec(v_unused_2498_);
v_unused_2499_ = lean_ctor_get(v_l_2279_, 3);
lean_dec(v_unused_2499_);
v_unused_2500_ = lean_ctor_get(v_l_2279_, 2);
lean_dec(v_unused_2500_);
v_unused_2501_ = lean_ctor_get(v_l_2279_, 1);
lean_dec(v_unused_2501_);
v_unused_2502_ = lean_ctor_get(v_l_2279_, 0);
lean_dec(v_unused_2502_);
v___x_2492_ = v_l_2279_;
v_isShared_2493_ = v_isSharedCheck_2497_;
goto v_resetjp_2491_;
}
else
{
lean_dec(v_l_2279_);
v___x_2492_ = lean_box(0);
v_isShared_2493_ = v_isSharedCheck_2497_;
goto v_resetjp_2491_;
}
v_resetjp_2491_:
{
lean_object* v___x_2495_; 
if (v_isShared_2493_ == 0)
{
lean_ctor_set(v___x_2492_, 4, v_r_2432_);
lean_ctor_set(v___x_2492_, 3, v___x_2490_);
lean_ctor_set(v___x_2492_, 2, v_v_2430_);
lean_ctor_set(v___x_2492_, 1, v_k_2429_);
lean_ctor_set(v___x_2492_, 0, v___x_2487_);
v___x_2495_ = v___x_2492_;
goto v_reusejp_2494_;
}
else
{
lean_object* v_reuseFailAlloc_2496_; 
v_reuseFailAlloc_2496_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2496_, 0, v___x_2487_);
lean_ctor_set(v_reuseFailAlloc_2496_, 1, v_k_2429_);
lean_ctor_set(v_reuseFailAlloc_2496_, 2, v_v_2430_);
lean_ctor_set(v_reuseFailAlloc_2496_, 3, v___x_2490_);
lean_ctor_set(v_reuseFailAlloc_2496_, 4, v_r_2432_);
v___x_2495_ = v_reuseFailAlloc_2496_;
goto v_reusejp_2494_;
}
v_reusejp_2494_:
{
return v___x_2495_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_2510_; 
v_l_2510_ = lean_ctor_get(v_impl_2425_, 3);
lean_inc(v_l_2510_);
if (lean_obj_tag(v_l_2510_) == 0)
{
lean_object* v_r_2511_; lean_object* v_k_2512_; lean_object* v_v_2513_; lean_object* v___x_2515_; uint8_t v_isShared_2516_; uint8_t v_isSharedCheck_2536_; 
v_r_2511_ = lean_ctor_get(v_impl_2425_, 4);
v_k_2512_ = lean_ctor_get(v_impl_2425_, 1);
v_v_2513_ = lean_ctor_get(v_impl_2425_, 2);
v_isSharedCheck_2536_ = !lean_is_exclusive(v_impl_2425_);
if (v_isSharedCheck_2536_ == 0)
{
lean_object* v_unused_2537_; lean_object* v_unused_2538_; 
v_unused_2537_ = lean_ctor_get(v_impl_2425_, 3);
lean_dec(v_unused_2537_);
v_unused_2538_ = lean_ctor_get(v_impl_2425_, 0);
lean_dec(v_unused_2538_);
v___x_2515_ = v_impl_2425_;
v_isShared_2516_ = v_isSharedCheck_2536_;
goto v_resetjp_2514_;
}
else
{
lean_inc(v_r_2511_);
lean_inc(v_v_2513_);
lean_inc(v_k_2512_);
lean_dec(v_impl_2425_);
v___x_2515_ = lean_box(0);
v_isShared_2516_ = v_isSharedCheck_2536_;
goto v_resetjp_2514_;
}
v_resetjp_2514_:
{
lean_object* v_k_2517_; lean_object* v_v_2518_; lean_object* v___x_2520_; uint8_t v_isShared_2521_; uint8_t v_isSharedCheck_2532_; 
v_k_2517_ = lean_ctor_get(v_l_2510_, 1);
v_v_2518_ = lean_ctor_get(v_l_2510_, 2);
v_isSharedCheck_2532_ = !lean_is_exclusive(v_l_2510_);
if (v_isSharedCheck_2532_ == 0)
{
lean_object* v_unused_2533_; lean_object* v_unused_2534_; lean_object* v_unused_2535_; 
v_unused_2533_ = lean_ctor_get(v_l_2510_, 4);
lean_dec(v_unused_2533_);
v_unused_2534_ = lean_ctor_get(v_l_2510_, 3);
lean_dec(v_unused_2534_);
v_unused_2535_ = lean_ctor_get(v_l_2510_, 0);
lean_dec(v_unused_2535_);
v___x_2520_ = v_l_2510_;
v_isShared_2521_ = v_isSharedCheck_2532_;
goto v_resetjp_2519_;
}
else
{
lean_inc(v_v_2518_);
lean_inc(v_k_2517_);
lean_dec(v_l_2510_);
v___x_2520_ = lean_box(0);
v_isShared_2521_ = v_isSharedCheck_2532_;
goto v_resetjp_2519_;
}
v_resetjp_2519_:
{
lean_object* v___x_2522_; lean_object* v___x_2524_; 
v___x_2522_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_2511_, 2);
if (v_isShared_2521_ == 0)
{
lean_ctor_set(v___x_2520_, 4, v_r_2511_);
lean_ctor_set(v___x_2520_, 3, v_r_2511_);
lean_ctor_set(v___x_2520_, 2, v_v_2278_);
lean_ctor_set(v___x_2520_, 1, v_k_2277_);
lean_ctor_set(v___x_2520_, 0, v___x_2426_);
v___x_2524_ = v___x_2520_;
goto v_reusejp_2523_;
}
else
{
lean_object* v_reuseFailAlloc_2531_; 
v_reuseFailAlloc_2531_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2531_, 0, v___x_2426_);
lean_ctor_set(v_reuseFailAlloc_2531_, 1, v_k_2277_);
lean_ctor_set(v_reuseFailAlloc_2531_, 2, v_v_2278_);
lean_ctor_set(v_reuseFailAlloc_2531_, 3, v_r_2511_);
lean_ctor_set(v_reuseFailAlloc_2531_, 4, v_r_2511_);
v___x_2524_ = v_reuseFailAlloc_2531_;
goto v_reusejp_2523_;
}
v_reusejp_2523_:
{
lean_object* v___x_2526_; 
lean_inc(v_r_2511_);
if (v_isShared_2516_ == 0)
{
lean_ctor_set(v___x_2515_, 3, v_r_2511_);
lean_ctor_set(v___x_2515_, 0, v___x_2426_);
v___x_2526_ = v___x_2515_;
goto v_reusejp_2525_;
}
else
{
lean_object* v_reuseFailAlloc_2530_; 
v_reuseFailAlloc_2530_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2530_, 0, v___x_2426_);
lean_ctor_set(v_reuseFailAlloc_2530_, 1, v_k_2512_);
lean_ctor_set(v_reuseFailAlloc_2530_, 2, v_v_2513_);
lean_ctor_set(v_reuseFailAlloc_2530_, 3, v_r_2511_);
lean_ctor_set(v_reuseFailAlloc_2530_, 4, v_r_2511_);
v___x_2526_ = v_reuseFailAlloc_2530_;
goto v_reusejp_2525_;
}
v_reusejp_2525_:
{
lean_object* v___x_2528_; 
if (v_isShared_2283_ == 0)
{
lean_ctor_set(v___x_2282_, 4, v___x_2526_);
lean_ctor_set(v___x_2282_, 3, v___x_2524_);
lean_ctor_set(v___x_2282_, 2, v_v_2518_);
lean_ctor_set(v___x_2282_, 1, v_k_2517_);
lean_ctor_set(v___x_2282_, 0, v___x_2522_);
v___x_2528_ = v___x_2282_;
goto v_reusejp_2527_;
}
else
{
lean_object* v_reuseFailAlloc_2529_; 
v_reuseFailAlloc_2529_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2529_, 0, v___x_2522_);
lean_ctor_set(v_reuseFailAlloc_2529_, 1, v_k_2517_);
lean_ctor_set(v_reuseFailAlloc_2529_, 2, v_v_2518_);
lean_ctor_set(v_reuseFailAlloc_2529_, 3, v___x_2524_);
lean_ctor_set(v_reuseFailAlloc_2529_, 4, v___x_2526_);
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
else
{
lean_object* v_r_2539_; 
v_r_2539_ = lean_ctor_get(v_impl_2425_, 4);
lean_inc(v_r_2539_);
if (lean_obj_tag(v_r_2539_) == 0)
{
lean_object* v_k_2540_; lean_object* v_v_2541_; lean_object* v___x_2543_; uint8_t v_isShared_2544_; uint8_t v_isSharedCheck_2552_; 
v_k_2540_ = lean_ctor_get(v_impl_2425_, 1);
v_v_2541_ = lean_ctor_get(v_impl_2425_, 2);
v_isSharedCheck_2552_ = !lean_is_exclusive(v_impl_2425_);
if (v_isSharedCheck_2552_ == 0)
{
lean_object* v_unused_2553_; lean_object* v_unused_2554_; lean_object* v_unused_2555_; 
v_unused_2553_ = lean_ctor_get(v_impl_2425_, 4);
lean_dec(v_unused_2553_);
v_unused_2554_ = lean_ctor_get(v_impl_2425_, 3);
lean_dec(v_unused_2554_);
v_unused_2555_ = lean_ctor_get(v_impl_2425_, 0);
lean_dec(v_unused_2555_);
v___x_2543_ = v_impl_2425_;
v_isShared_2544_ = v_isSharedCheck_2552_;
goto v_resetjp_2542_;
}
else
{
lean_inc(v_v_2541_);
lean_inc(v_k_2540_);
lean_dec(v_impl_2425_);
v___x_2543_ = lean_box(0);
v_isShared_2544_ = v_isSharedCheck_2552_;
goto v_resetjp_2542_;
}
v_resetjp_2542_:
{
lean_object* v___x_2545_; lean_object* v___x_2547_; 
v___x_2545_ = lean_unsigned_to_nat(3u);
if (v_isShared_2544_ == 0)
{
lean_ctor_set(v___x_2543_, 4, v_l_2510_);
lean_ctor_set(v___x_2543_, 2, v_v_2278_);
lean_ctor_set(v___x_2543_, 1, v_k_2277_);
lean_ctor_set(v___x_2543_, 0, v___x_2426_);
v___x_2547_ = v___x_2543_;
goto v_reusejp_2546_;
}
else
{
lean_object* v_reuseFailAlloc_2551_; 
v_reuseFailAlloc_2551_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2551_, 0, v___x_2426_);
lean_ctor_set(v_reuseFailAlloc_2551_, 1, v_k_2277_);
lean_ctor_set(v_reuseFailAlloc_2551_, 2, v_v_2278_);
lean_ctor_set(v_reuseFailAlloc_2551_, 3, v_l_2510_);
lean_ctor_set(v_reuseFailAlloc_2551_, 4, v_l_2510_);
v___x_2547_ = v_reuseFailAlloc_2551_;
goto v_reusejp_2546_;
}
v_reusejp_2546_:
{
lean_object* v___x_2549_; 
if (v_isShared_2283_ == 0)
{
lean_ctor_set(v___x_2282_, 4, v_r_2539_);
lean_ctor_set(v___x_2282_, 3, v___x_2547_);
lean_ctor_set(v___x_2282_, 2, v_v_2541_);
lean_ctor_set(v___x_2282_, 1, v_k_2540_);
lean_ctor_set(v___x_2282_, 0, v___x_2545_);
v___x_2549_ = v___x_2282_;
goto v_reusejp_2548_;
}
else
{
lean_object* v_reuseFailAlloc_2550_; 
v_reuseFailAlloc_2550_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2550_, 0, v___x_2545_);
lean_ctor_set(v_reuseFailAlloc_2550_, 1, v_k_2540_);
lean_ctor_set(v_reuseFailAlloc_2550_, 2, v_v_2541_);
lean_ctor_set(v_reuseFailAlloc_2550_, 3, v___x_2547_);
lean_ctor_set(v_reuseFailAlloc_2550_, 4, v_r_2539_);
v___x_2549_ = v_reuseFailAlloc_2550_;
goto v_reusejp_2548_;
}
v_reusejp_2548_:
{
return v___x_2549_;
}
}
}
}
else
{
lean_object* v___x_2556_; lean_object* v___x_2558_; 
v___x_2556_ = lean_unsigned_to_nat(2u);
if (v_isShared_2283_ == 0)
{
lean_ctor_set(v___x_2282_, 4, v_impl_2425_);
lean_ctor_set(v___x_2282_, 3, v_r_2539_);
lean_ctor_set(v___x_2282_, 0, v___x_2556_);
v___x_2558_ = v___x_2282_;
goto v_reusejp_2557_;
}
else
{
lean_object* v_reuseFailAlloc_2559_; 
v_reuseFailAlloc_2559_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2559_, 0, v___x_2556_);
lean_ctor_set(v_reuseFailAlloc_2559_, 1, v_k_2277_);
lean_ctor_set(v_reuseFailAlloc_2559_, 2, v_v_2278_);
lean_ctor_set(v_reuseFailAlloc_2559_, 3, v_r_2539_);
lean_ctor_set(v_reuseFailAlloc_2559_, 4, v_impl_2425_);
v___x_2558_ = v_reuseFailAlloc_2559_;
goto v_reusejp_2557_;
}
v_reusejp_2557_:
{
return v___x_2558_;
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
lean_object* v___x_2561_; lean_object* v___x_2562_; 
v___x_2561_ = lean_unsigned_to_nat(1u);
v___x_2562_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2562_, 0, v___x_2561_);
lean_ctor_set(v___x_2562_, 1, v_k_2273_);
lean_ctor_set(v___x_2562_, 2, v_v_2274_);
lean_ctor_set(v___x_2562_, 3, v_t_2275_);
lean_ctor_set(v___x_2562_, 4, v_t_2275_);
return v___x_2562_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Level_collectMVars_spec__0___redArg(lean_object* v_k_2563_, lean_object* v_t_2564_){
_start:
{
if (lean_obj_tag(v_t_2564_) == 0)
{
lean_object* v_k_2565_; lean_object* v_l_2566_; lean_object* v_r_2567_; uint8_t v___x_2568_; 
v_k_2565_ = lean_ctor_get(v_t_2564_, 1);
v_l_2566_ = lean_ctor_get(v_t_2564_, 3);
v_r_2567_ = lean_ctor_get(v_t_2564_, 4);
v___x_2568_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2563_, v_k_2565_);
switch(v___x_2568_)
{
case 0:
{
v_t_2564_ = v_l_2566_;
goto _start;
}
case 1:
{
uint8_t v___x_2570_; 
v___x_2570_ = 1;
return v___x_2570_;
}
default: 
{
v_t_2564_ = v_r_2567_;
goto _start;
}
}
}
else
{
uint8_t v___x_2572_; 
v___x_2572_ = 0;
return v___x_2572_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Level_collectMVars_spec__0___redArg___boxed(lean_object* v_k_2573_, lean_object* v_t_2574_){
_start:
{
uint8_t v_res_2575_; lean_object* v_r_2576_; 
v_res_2575_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Level_collectMVars_spec__0___redArg(v_k_2573_, v_t_2574_);
lean_dec(v_t_2574_);
lean_dec(v_k_2573_);
v_r_2576_ = lean_box(v_res_2575_);
return v_r_2576_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_collectMVars(lean_object* v_u_2577_, lean_object* v_s_2578_){
_start:
{
lean_object* v_u_2580_; lean_object* v_v_2581_; 
switch(lean_obj_tag(v_u_2577_))
{
case 1:
{
lean_object* v_a_2584_; 
v_a_2584_ = lean_ctor_get(v_u_2577_, 0);
lean_inc(v_a_2584_);
lean_dec_ref_known(v_u_2577_, 1);
v_u_2577_ = v_a_2584_;
goto _start;
}
case 2:
{
lean_object* v_a_2586_; lean_object* v_a_2587_; 
v_a_2586_ = lean_ctor_get(v_u_2577_, 0);
lean_inc(v_a_2586_);
v_a_2587_ = lean_ctor_get(v_u_2577_, 1);
lean_inc(v_a_2587_);
lean_dec_ref_known(v_u_2577_, 2);
v_u_2580_ = v_a_2586_;
v_v_2581_ = v_a_2587_;
goto v___jp_2579_;
}
case 3:
{
lean_object* v_a_2588_; lean_object* v_a_2589_; 
v_a_2588_ = lean_ctor_get(v_u_2577_, 0);
lean_inc(v_a_2588_);
v_a_2589_ = lean_ctor_get(v_u_2577_, 1);
lean_inc(v_a_2589_);
lean_dec_ref_known(v_u_2577_, 2);
v_u_2580_ = v_a_2588_;
v_v_2581_ = v_a_2589_;
goto v___jp_2579_;
}
case 5:
{
lean_object* v_a_2590_; uint8_t v___x_2591_; 
v_a_2590_ = lean_ctor_get(v_u_2577_, 0);
lean_inc(v_a_2590_);
lean_dec_ref_known(v_u_2577_, 1);
v___x_2591_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Level_collectMVars_spec__0___redArg(v_a_2590_, v_s_2578_);
if (v___x_2591_ == 0)
{
lean_object* v___x_2592_; lean_object* v___x_2593_; 
v___x_2592_ = lean_box(0);
v___x_2593_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Level_collectMVars_spec__1___redArg(v_a_2590_, v___x_2592_, v_s_2578_);
return v___x_2593_;
}
else
{
lean_dec(v_a_2590_);
return v_s_2578_;
}
}
default: 
{
lean_dec(v_u_2577_);
return v_s_2578_;
}
}
v___jp_2579_:
{
lean_object* v___x_2582_; 
v___x_2582_ = l_Lean_Level_collectMVars(v_v_2581_, v_s_2578_);
v_u_2577_ = v_u_2580_;
v_s_2578_ = v___x_2582_;
goto _start;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Level_collectMVars_spec__0(lean_object* v_00_u03b2_2594_, lean_object* v_k_2595_, lean_object* v_t_2596_){
_start:
{
uint8_t v___x_2597_; 
v___x_2597_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Level_collectMVars_spec__0___redArg(v_k_2595_, v_t_2596_);
return v___x_2597_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Level_collectMVars_spec__0___boxed(lean_object* v_00_u03b2_2598_, lean_object* v_k_2599_, lean_object* v_t_2600_){
_start:
{
uint8_t v_res_2601_; lean_object* v_r_2602_; 
v_res_2601_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Level_collectMVars_spec__0(v_00_u03b2_2598_, v_k_2599_, v_t_2600_);
lean_dec(v_t_2600_);
lean_dec(v_k_2599_);
v_r_2602_ = lean_box(v_res_2601_);
return v_r_2602_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Level_collectMVars_spec__1(lean_object* v_00_u03b2_2603_, lean_object* v_k_2604_, lean_object* v_v_2605_, lean_object* v_t_2606_, lean_object* v_hl_2607_){
_start:
{
lean_object* v___x_2608_; 
v___x_2608_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Level_collectMVars_spec__1___redArg(v_k_2604_, v_v_2605_, v_t_2606_);
return v___x_2608_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_find_x3f_visit(lean_object* v_p_2609_, lean_object* v_u_2610_){
_start:
{
lean_object* v_u_2612_; lean_object* v_v_2613_; lean_object* v___x_2616_; uint8_t v___x_2617_; 
lean_inc_ref(v_p_2609_);
lean_inc(v_u_2610_);
v___x_2616_ = lean_apply_1(v_p_2609_, v_u_2610_);
v___x_2617_ = lean_unbox(v___x_2616_);
if (v___x_2617_ == 0)
{
switch(lean_obj_tag(v_u_2610_))
{
case 1:
{
lean_object* v_a_2618_; 
v_a_2618_ = lean_ctor_get(v_u_2610_, 0);
lean_inc(v_a_2618_);
lean_dec_ref_known(v_u_2610_, 1);
v_u_2610_ = v_a_2618_;
goto _start;
}
case 2:
{
lean_object* v_a_2620_; lean_object* v_a_2621_; 
v_a_2620_ = lean_ctor_get(v_u_2610_, 0);
lean_inc(v_a_2620_);
v_a_2621_ = lean_ctor_get(v_u_2610_, 1);
lean_inc(v_a_2621_);
lean_dec_ref_known(v_u_2610_, 2);
v_u_2612_ = v_a_2620_;
v_v_2613_ = v_a_2621_;
goto v___jp_2611_;
}
case 3:
{
lean_object* v_a_2622_; lean_object* v_a_2623_; 
v_a_2622_ = lean_ctor_get(v_u_2610_, 0);
lean_inc(v_a_2622_);
v_a_2623_ = lean_ctor_get(v_u_2610_, 1);
lean_inc(v_a_2623_);
lean_dec_ref_known(v_u_2610_, 2);
v_u_2612_ = v_a_2622_;
v_v_2613_ = v_a_2623_;
goto v___jp_2611_;
}
default: 
{
lean_object* v___x_2624_; 
lean_dec(v_u_2610_);
lean_dec_ref(v_p_2609_);
v___x_2624_ = lean_box(0);
return v___x_2624_;
}
}
}
else
{
lean_object* v___x_2625_; 
lean_dec_ref(v_p_2609_);
v___x_2625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2625_, 0, v_u_2610_);
return v___x_2625_;
}
v___jp_2611_:
{
lean_object* v___x_2614_; 
lean_inc_ref(v_p_2609_);
v___x_2614_ = l___private_Lean_Level_0__Lean_Level_find_x3f_visit(v_p_2609_, v_u_2612_);
if (lean_obj_tag(v___x_2614_) == 0)
{
v_u_2610_ = v_v_2613_;
goto _start;
}
else
{
lean_dec(v_v_2613_);
lean_dec_ref(v_p_2609_);
return v___x_2614_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_find_x3f(lean_object* v_u_2626_, lean_object* v_p_2627_){
_start:
{
lean_object* v___x_2628_; 
v___x_2628_ = l___private_Lean_Level_0__Lean_Level_find_x3f_visit(v_p_2627_, v_u_2626_);
return v___x_2628_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_any(lean_object* v_u_2629_, lean_object* v_p_2630_){
_start:
{
lean_object* v___x_2631_; 
v___x_2631_ = l___private_Lean_Level_0__Lean_Level_find_x3f_visit(v_p_2630_, v_u_2629_);
if (lean_obj_tag(v___x_2631_) == 0)
{
uint8_t v___x_2632_; 
v___x_2632_ = 0;
return v___x_2632_;
}
else
{
uint8_t v___x_2633_; 
lean_dec_ref_known(v___x_2631_, 1);
v___x_2633_ = 1;
return v___x_2633_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_any___boxed(lean_object* v_u_2634_, lean_object* v_p_2635_){
_start:
{
uint8_t v_res_2636_; lean_object* v_r_2637_; 
v_res_2636_ = l_Lean_Level_any(v_u_2634_, v_p_2635_);
v_r_2637_ = lean_box(v_res_2636_);
return v_r_2637_;
}
}
LEAN_EXPORT lean_object* l_Lean_Nat_toLevel(lean_object* v_n_2638_){
_start:
{
lean_object* v___x_2639_; 
v___x_2639_ = l_Lean_Level_ofNat(v_n_2638_);
return v___x_2639_;
}
}
LEAN_EXPORT lean_object* l_Lean_Nat_toLevel___boxed(lean_object* v_n_2640_){
_start:
{
lean_object* v_res_2641_; 
v_res_2641_ = l_Lean_Nat_toLevel(v_n_2640_);
lean_dec(v_n_2640_);
return v_res_2641_;
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
