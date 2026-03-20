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
uint8_t l_Lean_Name_lt(lean_object*, lean_object*);
lean_object* l_Array_qpartition___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Name_reprPrec(lean_object*, lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
extern uint64_t l_instInhabitedUInt64;
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* l_Std_TreeSet_instForInOfMonad___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_uint64_to_nat(uint64_t);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* l_Std_TreeMap_instForInProdOfMonad___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_reprPrec___boxed(lean_object*, lean_object*);
lean_object* l_UInt64_decEq___boxed(lean_object*, lean_object*);
extern lean_object* l_Std_Format_defWidth;
lean_object* l_Std_Format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_imax(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_imax___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_instInhabitedLMVarIdSet;
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionLMVarIdSet;
LEAN_EXPORT lean_object* l_Lean_instForInLMVarIdSetLMVarIdOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instForInLMVarIdSetLMVarIdOfMonad(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionLMVarIdMap(lean_object*);
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
static const lean_closure_object l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Level_normLt___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_Level_PP_toResult___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "_uniq"};
static const lean_object* l_Lean_Level_PP_toResult___closed__4 = (const lean_object*)&l_Lean_Level_PP_toResult___closed__4_value;
static const lean_ctor_object l_Lean_Level_PP_toResult___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Level_PP_toResult___closed__4_value),LEAN_SCALAR_PTR_LITERAL(237, 141, 162, 170, 202, 74, 55, 55)}};
static const lean_object* l_Lean_Level_PP_toResult___closed__5 = (const lean_object*)&l_Lean_Level_PP_toResult___closed__5_value;
static const lean_string_object l_Lean_Level_PP_toResult___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "\?u"};
static const lean_object* l_Lean_Level_PP_toResult___closed__6 = (const lean_object*)&l_Lean_Level_PP_toResult___closed__6_value;
static const lean_ctor_object l_Lean_Level_PP_toResult___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Level_PP_toResult___closed__6_value),LEAN_SCALAR_PTR_LITERAL(228, 117, 157, 98, 226, 186, 76, 191)}};
static const lean_object* l_Lean_Level_PP_toResult___closed__7 = (const lean_object*)&l_Lean_Level_PP_toResult___closed__7_value;
LEAN_EXPORT lean_object* l_Lean_Level_PP_toResult(lean_object*, uint8_t);
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
static const lean_string_object l_Lean_Level_PP_Result_format___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "+"};
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
static const lean_ctor_object l_Lean_Level_PP_Result_quote___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Level_PP_Result_quote___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Level_PP_Result_quote___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Level_PP_Result_quote___closed__10_value_aux_0),((lean_object*)&l_Lean_Level_PP_Result_quote___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Level_PP_Result_quote___closed__10_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Level_PP_Result_quote___closed__10_value_aux_1),((lean_object*)&l_Lean_Level_PP_Result_quote___closed__3_value),LEAN_SCALAR_PTR_LITERAL(176, 210, 143, 23, 235, 250, 136, 158)}};
static const lean_ctor_object l_Lean_Level_PP_Result_quote___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Level_PP_Result_quote___closed__10_value_aux_2),((lean_object*)&l_Lean_Level_PP_Result_format___closed__2_value),LEAN_SCALAR_PTR_LITERAL(106, 181, 1, 145, 170, 142, 100, 97)}};
static const lean_object* l_Lean_Level_PP_Result_quote___closed__10 = (const lean_object*)&l_Lean_Level_PP_Result_quote___closed__10_value;
static lean_once_cell_t l_Lean_Level_PP_Result_quote___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Level_PP_Result_quote___closed__11;
static const lean_string_object l_Lean_Level_PP_Result_quote___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_Level_PP_Result_quote___closed__12 = (const lean_object*)&l_Lean_Level_PP_Result_quote___closed__12_value;
static const lean_ctor_object l_Lean_Level_PP_Result_quote___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Level_PP_Result_quote___closed__12_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean_Level_PP_Result_quote___closed__13 = (const lean_object*)&l_Lean_Level_PP_Result_quote___closed__13_value;
static lean_once_cell_t l_Lean_Level_PP_Result_quote___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Level_PP_Result_quote___closed__14;
static const lean_ctor_object l_Lean_Level_PP_Result_quote___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Level_PP_Result_quote___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Level_PP_Result_quote___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Level_PP_Result_quote___closed__15_value_aux_0),((lean_object*)&l_Lean_Level_PP_Result_quote___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Level_PP_Result_quote___closed__15_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Level_PP_Result_quote___closed__15_value_aux_1),((lean_object*)&l_Lean_Level_PP_Result_quote___closed__3_value),LEAN_SCALAR_PTR_LITERAL(176, 210, 143, 23, 235, 250, 136, 158)}};
static const lean_ctor_object l_Lean_Level_PP_Result_quote___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Level_PP_Result_quote___closed__15_value_aux_2),((lean_object*)&l_Lean_Level_PP_Result_format___closed__4_value),LEAN_SCALAR_PTR_LITERAL(124, 169, 176, 27, 219, 169, 119, 28)}};
static const lean_object* l_Lean_Level_PP_Result_quote___closed__15 = (const lean_object*)&l_Lean_Level_PP_Result_quote___closed__15_value;
static lean_once_cell_t l_Lean_Level_PP_Result_quote___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Level_PP_Result_quote___closed__16;
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_quote(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Level_PP_Result_quote_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Level_PP_Result_quote_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_quote___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_format(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Level_format___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_instToFormat___lam__0(lean_object*);
static const lean_closure_object l_Lean_Level_instToFormat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Level_instToFormat___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Level_instToFormat___closed__0 = (const lean_object*)&l_Lean_Level_instToFormat___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Level_instToFormat = (const lean_object*)&l_Lean_Level_instToFormat___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Level_instToString___lam__0(lean_object*);
static const lean_closure_object l_Lean_Level_instToString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Level_instToString___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Level_instToString___closed__0 = (const lean_object*)&l_Lean_Level_instToString___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Level_instToString = (const lean_object*)&l_Lean_Level_instToString___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Level_quote(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Level_quote___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_instQuoteMkStr1___lam__0(lean_object*);
static const lean_closure_object l_Lean_Level_instQuoteMkStr1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Level_instQuoteMkStr1___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
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
static uint64_t _init_l_Lean_instInhabitedData(void){
_start:
{
uint64_t v___x_9_; 
v___x_9_ = l_instInhabitedUInt64;
return v___x_9_;
}
}
LEAN_EXPORT uint64_t l_Lean_Level_Data_hash(uint64_t v_c_10_){
_start:
{
uint32_t v___x_11_; uint64_t v___x_12_; 
v___x_11_ = lean_uint64_to_uint32(v_c_10_);
v___x_12_ = lean_uint32_to_uint64(v___x_11_);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_Data_hash___boxed(lean_object* v_c_13_){
_start:
{
uint64_t v_c_boxed_14_; uint64_t v_res_15_; lean_object* v_r_16_; 
v_c_boxed_14_ = lean_unbox_uint64(v_c_13_);
lean_dec_ref(v_c_13_);
v_res_15_ = l_Lean_Level_Data_hash(v_c_boxed_14_);
v_r_16_ = lean_box_uint64(v_res_15_);
return v_r_16_;
}
}
LEAN_EXPORT uint32_t l_Lean_Level_Data_depth(uint64_t v_c_19_){
_start:
{
uint64_t v___x_20_; uint64_t v___x_21_; uint32_t v___x_22_; 
v___x_20_ = 40ULL;
v___x_21_ = lean_uint64_shift_right(v_c_19_, v___x_20_);
v___x_22_ = lean_uint64_to_uint32(v___x_21_);
return v___x_22_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_Data_depth___boxed(lean_object* v_c_23_){
_start:
{
uint64_t v_c_boxed_24_; uint32_t v_res_25_; lean_object* v_r_26_; 
v_c_boxed_24_ = lean_unbox_uint64(v_c_23_);
lean_dec_ref(v_c_23_);
v_res_25_ = l_Lean_Level_Data_depth(v_c_boxed_24_);
v_r_26_ = lean_box_uint32(v_res_25_);
return v_r_26_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_Data_hasMVar(uint64_t v_c_27_){
_start:
{
uint64_t v___x_28_; uint64_t v___x_29_; uint64_t v___x_30_; uint64_t v___x_31_; uint8_t v___x_32_; 
v___x_28_ = 32ULL;
v___x_29_ = lean_uint64_shift_right(v_c_27_, v___x_28_);
v___x_30_ = 1ULL;
v___x_31_ = lean_uint64_land(v___x_29_, v___x_30_);
v___x_32_ = lean_uint64_dec_eq(v___x_31_, v___x_30_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_Data_hasMVar___boxed(lean_object* v_c_33_){
_start:
{
uint64_t v_c_boxed_34_; uint8_t v_res_35_; lean_object* v_r_36_; 
v_c_boxed_34_ = lean_unbox_uint64(v_c_33_);
lean_dec_ref(v_c_33_);
v_res_35_ = l_Lean_Level_Data_hasMVar(v_c_boxed_34_);
v_r_36_ = lean_box(v_res_35_);
return v_r_36_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_Data_hasParam(uint64_t v_c_37_){
_start:
{
uint64_t v___x_38_; uint64_t v___x_39_; uint64_t v___x_40_; uint64_t v___x_41_; uint8_t v___x_42_; 
v___x_38_ = 33ULL;
v___x_39_ = lean_uint64_shift_right(v_c_37_, v___x_38_);
v___x_40_ = 1ULL;
v___x_41_ = lean_uint64_land(v___x_39_, v___x_40_);
v___x_42_ = lean_uint64_dec_eq(v___x_41_, v___x_40_);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_Data_hasParam___boxed(lean_object* v_c_43_){
_start:
{
uint64_t v_c_boxed_44_; uint8_t v_res_45_; lean_object* v_r_46_; 
v_c_boxed_44_ = lean_unbox_uint64(v_c_43_);
lean_dec_ref(v_c_43_);
v_res_45_ = l_Lean_Level_Data_hasParam(v_c_boxed_44_);
v_r_46_ = lean_box(v_res_45_);
return v_r_46_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_mkData___boxed(lean_object* v_h_51_, lean_object* v_depth_52_, lean_object* v_hasMVar_53_, lean_object* v_hasParam_54_){
_start:
{
uint64_t v_h_boxed_55_; uint8_t v_hasMVar_boxed_56_; uint8_t v_hasParam_boxed_57_; uint64_t v_res_58_; lean_object* v_r_59_; 
v_h_boxed_55_ = lean_unbox_uint64(v_h_51_);
lean_dec_ref(v_h_51_);
v_hasMVar_boxed_56_ = lean_unbox(v_hasMVar_53_);
v_hasParam_boxed_57_ = lean_unbox(v_hasParam_54_);
v_res_58_ = lean_level_mk_data(v_h_boxed_55_, v_depth_52_, v_hasMVar_boxed_56_, v_hasParam_boxed_57_);
v_r_59_ = lean_box_uint64(v_res_58_);
return v_r_59_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprData___lam__0(uint64_t v_v_67_, lean_object* v_prec_68_){
_start:
{
lean_object* v_r_70_; lean_object* v___y_74_; lean_object* v___y_75_; lean_object* v_r_80_; lean_object* v___y_87_; lean_object* v___y_88_; lean_object* v_r_93_; lean_object* v___x_99_; uint64_t v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v_r_103_; uint32_t v___x_104_; uint32_t v___x_105_; uint8_t v___x_106_; 
v___x_99_ = ((lean_object*)(l_Lean_instReprData___lam__0___closed__5));
v___x_100_ = l_Lean_Level_Data_hash(v_v_67_);
v___x_101_ = lean_uint64_to_nat(v___x_100_);
v___x_102_ = l_Nat_reprFast(v___x_101_);
v_r_103_ = lean_string_append(v___x_99_, v___x_102_);
lean_dec_ref(v___x_102_);
v___x_104_ = l_Lean_Level_Data_depth(v_v_67_);
v___x_105_ = 0;
v___x_106_ = lean_uint32_dec_eq(v___x_104_, v___x_105_);
if (v___x_106_ == 0)
{
lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v_r_113_; 
v___x_107_ = ((lean_object*)(l_Lean_instReprData___lam__0___closed__6));
v___x_108_ = lean_string_append(v_r_103_, v___x_107_);
v___x_109_ = lean_uint32_to_nat(v___x_104_);
v___x_110_ = l_Nat_reprFast(v___x_109_);
v___x_111_ = lean_string_append(v___x_108_, v___x_110_);
lean_dec_ref(v___x_110_);
v___x_112_ = ((lean_object*)(l_Lean_instReprData___lam__0___closed__0));
v_r_113_ = lean_string_append(v___x_111_, v___x_112_);
v_r_93_ = v_r_113_;
goto v___jp_92_;
}
else
{
v_r_93_ = v_r_103_;
goto v___jp_92_;
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
lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v_r_78_; 
v___x_76_ = lean_string_append(v___y_74_, v___y_75_);
lean_dec_ref(v___y_75_);
v___x_77_ = ((lean_object*)(l_Lean_instReprData___lam__0___closed__0));
v_r_78_ = lean_string_append(v___x_76_, v___x_77_);
v_r_70_ = v_r_78_;
goto v___jp_69_;
}
v___jp_79_:
{
uint8_t v___x_81_; 
v___x_81_ = l_Lean_Level_Data_hasParam(v_v_67_);
if (v___x_81_ == 0)
{
v_r_70_ = v_r_80_;
goto v___jp_69_;
}
else
{
lean_object* v___x_82_; lean_object* v___x_83_; 
v___x_82_ = ((lean_object*)(l_Lean_instReprData___lam__0___closed__1));
v___x_83_ = lean_string_append(v_r_80_, v___x_82_);
if (v___x_81_ == 0)
{
lean_object* v___x_84_; 
v___x_84_ = ((lean_object*)(l_Lean_instReprData___lam__0___closed__2));
v___y_74_ = v___x_83_;
v___y_75_ = v___x_84_;
goto v___jp_73_;
}
else
{
lean_object* v___x_85_; 
v___x_85_ = ((lean_object*)(l_Lean_instReprData___lam__0___closed__3));
v___y_74_ = v___x_83_;
v___y_75_ = v___x_85_;
goto v___jp_73_;
}
}
}
v___jp_86_:
{
lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v_r_91_; 
v___x_89_ = lean_string_append(v___y_87_, v___y_88_);
lean_dec_ref(v___y_88_);
v___x_90_ = ((lean_object*)(l_Lean_instReprData___lam__0___closed__0));
v_r_91_ = lean_string_append(v___x_89_, v___x_90_);
v_r_80_ = v_r_91_;
goto v___jp_79_;
}
v___jp_92_:
{
uint8_t v___x_94_; 
v___x_94_ = l_Lean_Level_Data_hasMVar(v_v_67_);
if (v___x_94_ == 0)
{
v_r_80_ = v_r_93_;
goto v___jp_79_;
}
else
{
lean_object* v___x_95_; lean_object* v___x_96_; 
v___x_95_ = ((lean_object*)(l_Lean_instReprData___lam__0___closed__4));
v___x_96_ = lean_string_append(v_r_93_, v___x_95_);
if (v___x_94_ == 0)
{
lean_object* v___x_97_; 
v___x_97_ = ((lean_object*)(l_Lean_instReprData___lam__0___closed__2));
v___y_87_ = v___x_96_;
v___y_88_ = v___x_97_;
goto v___jp_86_;
}
else
{
lean_object* v___x_98_; 
v___x_98_ = ((lean_object*)(l_Lean_instReprData___lam__0___closed__3));
v___y_87_ = v___x_96_;
v___y_88_ = v___x_98_;
goto v___jp_86_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instReprData___lam__0___boxed(lean_object* v_v_114_, lean_object* v_prec_115_){
_start:
{
uint64_t v_v_boxed_116_; lean_object* v_res_117_; 
v_v_boxed_116_ = lean_unbox_uint64(v_v_114_);
lean_dec_ref(v_v_114_);
v_res_117_ = l_Lean_instReprData___lam__0(v_v_boxed_116_, v_prec_115_);
lean_dec(v_prec_115_);
return v_res_117_;
}
}
static lean_object* _init_l_Lean_instInhabitedLevelMVarId_default(void){
_start:
{
lean_object* v___x_120_; 
v___x_120_ = lean_box(0);
return v___x_120_;
}
}
static lean_object* _init_l_Lean_instInhabitedLevelMVarId(void){
_start:
{
lean_object* v___x_121_; 
v___x_121_ = lean_box(0);
return v___x_121_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqLevelMVarId_beq(lean_object* v_x_122_, lean_object* v_x_123_){
_start:
{
uint8_t v___x_124_; 
v___x_124_ = lean_name_eq(v_x_122_, v_x_123_);
return v___x_124_;
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqLevelMVarId_beq___boxed(lean_object* v_x_125_, lean_object* v_x_126_){
_start:
{
uint8_t v_res_127_; lean_object* v_r_128_; 
v_res_127_ = l_Lean_instBEqLevelMVarId_beq(v_x_125_, v_x_126_);
lean_dec(v_x_126_);
lean_dec(v_x_125_);
v_r_128_ = lean_box(v_res_127_);
return v_r_128_;
}
}
static uint64_t _init_l_Lean_instHashableLevelMVarId_hash___closed__0(void){
_start:
{
lean_object* v___x_131_; uint64_t v___x_132_; 
v___x_131_ = lean_unsigned_to_nat(1723u);
v___x_132_ = lean_uint64_of_nat(v___x_131_);
return v___x_132_;
}
}
static uint64_t _init_l_Lean_instHashableLevelMVarId_hash___closed__1(void){
_start:
{
uint64_t v___x_133_; uint64_t v___x_134_; uint64_t v___x_135_; 
v___x_133_ = lean_uint64_once(&l_Lean_instHashableLevelMVarId_hash___closed__0, &l_Lean_instHashableLevelMVarId_hash___closed__0_once, _init_l_Lean_instHashableLevelMVarId_hash___closed__0);
v___x_134_ = 0ULL;
v___x_135_ = lean_uint64_mix_hash(v___x_134_, v___x_133_);
return v___x_135_;
}
}
LEAN_EXPORT uint64_t l_Lean_instHashableLevelMVarId_hash(lean_object* v_x_136_){
_start:
{
uint64_t v___x_137_; 
v___x_137_ = 0ULL;
if (lean_obj_tag(v_x_136_) == 0)
{
uint64_t v___x_138_; 
v___x_138_ = lean_uint64_once(&l_Lean_instHashableLevelMVarId_hash___closed__1, &l_Lean_instHashableLevelMVarId_hash___closed__1_once, _init_l_Lean_instHashableLevelMVarId_hash___closed__1);
return v___x_138_;
}
else
{
uint64_t v_hash_139_; uint64_t v___x_140_; 
v_hash_139_ = lean_ctor_get_uint64(v_x_136_, sizeof(void*)*2);
v___x_140_ = lean_uint64_mix_hash(v___x_137_, v_hash_139_);
return v___x_140_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instHashableLevelMVarId_hash___boxed(lean_object* v_x_141_){
_start:
{
uint64_t v_res_142_; lean_object* v_r_143_; 
v_res_142_ = l_Lean_instHashableLevelMVarId_hash(v_x_141_);
lean_dec(v_x_141_);
v_r_143_ = lean_box_uint64(v_res_142_);
return v_r_143_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_instReprLevelMVarId_repr_spec__0(lean_object* v_a_146_){
_start:
{
lean_object* v___x_147_; 
v___x_147_ = lean_nat_to_int(v_a_146_);
return v___x_147_;
}
}
static lean_object* _init_l_Lean_instReprLevelMVarId_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_161_; lean_object* v___x_162_; 
v___x_161_ = lean_unsigned_to_nat(8u);
v___x_162_ = lean_nat_to_int(v___x_161_);
return v___x_162_;
}
}
static lean_object* _init_l_Lean_instReprLevelMVarId_repr___redArg___closed__9(void){
_start:
{
lean_object* v___x_164_; lean_object* v___x_165_; 
v___x_164_ = ((lean_object*)(l_Lean_instReprLevelMVarId_repr___redArg___closed__0));
v___x_165_ = lean_string_length(v___x_164_);
return v___x_165_;
}
}
static lean_object* _init_l_Lean_instReprLevelMVarId_repr___redArg___closed__10(void){
_start:
{
lean_object* v___x_166_; lean_object* v___x_167_; 
v___x_166_ = lean_obj_once(&l_Lean_instReprLevelMVarId_repr___redArg___closed__9, &l_Lean_instReprLevelMVarId_repr___redArg___closed__9_once, _init_l_Lean_instReprLevelMVarId_repr___redArg___closed__9);
v___x_167_ = lean_nat_to_int(v___x_166_);
return v___x_167_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprLevelMVarId_repr___redArg(lean_object* v_x_172_){
_start:
{
lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; uint8_t v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; 
v___x_173_ = ((lean_object*)(l_Lean_instReprLevelMVarId_repr___redArg___closed__6));
v___x_174_ = lean_obj_once(&l_Lean_instReprLevelMVarId_repr___redArg___closed__7, &l_Lean_instReprLevelMVarId_repr___redArg___closed__7_once, _init_l_Lean_instReprLevelMVarId_repr___redArg___closed__7);
v___x_175_ = lean_unsigned_to_nat(0u);
v___x_176_ = l_Lean_Name_reprPrec(v_x_172_, v___x_175_);
v___x_177_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_177_, 0, v___x_174_);
lean_ctor_set(v___x_177_, 1, v___x_176_);
v___x_178_ = 0;
v___x_179_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_179_, 0, v___x_177_);
lean_ctor_set_uint8(v___x_179_, sizeof(void*)*1, v___x_178_);
v___x_180_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_180_, 0, v___x_173_);
lean_ctor_set(v___x_180_, 1, v___x_179_);
v___x_181_ = lean_obj_once(&l_Lean_instReprLevelMVarId_repr___redArg___closed__10, &l_Lean_instReprLevelMVarId_repr___redArg___closed__10_once, _init_l_Lean_instReprLevelMVarId_repr___redArg___closed__10);
v___x_182_ = ((lean_object*)(l_Lean_instReprLevelMVarId_repr___redArg___closed__11));
v___x_183_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_183_, 0, v___x_182_);
lean_ctor_set(v___x_183_, 1, v___x_180_);
v___x_184_ = ((lean_object*)(l_Lean_instReprLevelMVarId_repr___redArg___closed__12));
v___x_185_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_185_, 0, v___x_183_);
lean_ctor_set(v___x_185_, 1, v___x_184_);
v___x_186_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_186_, 0, v___x_181_);
lean_ctor_set(v___x_186_, 1, v___x_185_);
v___x_187_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_187_, 0, v___x_186_);
lean_ctor_set_uint8(v___x_187_, sizeof(void*)*1, v___x_178_);
return v___x_187_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprLevelMVarId_repr(lean_object* v_x_188_, lean_object* v_prec_189_){
_start:
{
lean_object* v___x_190_; 
v___x_190_ = l_Lean_instReprLevelMVarId_repr___redArg(v_x_188_);
return v___x_190_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprLevelMVarId_repr___boxed(lean_object* v_x_191_, lean_object* v_prec_192_){
_start:
{
lean_object* v_res_193_; 
v_res_193_ = l_Lean_instReprLevelMVarId_repr(v_x_191_, v_prec_192_);
lean_dec(v_prec_192_);
return v_res_193_;
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
static lean_object* _init_l_Lean_instEmptyCollectionLMVarIdSet(void){
_start:
{
lean_object* v___x_199_; 
v___x_199_ = lean_box(1);
return v___x_199_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInLMVarIdSetLMVarIdOfMonad___redArg(lean_object* v_inst_200_){
_start:
{
lean_object* v___f_201_; 
v___f_201_ = lean_alloc_closure((void*)(l_Std_TreeSet_instForInOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_201_, 0, v_inst_200_);
return v___f_201_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInLMVarIdSetLMVarIdOfMonad(lean_object* v_m_202_, lean_object* v_inst_203_){
_start:
{
lean_object* v___f_204_; 
v___f_204_ = lean_alloc_closure((void*)(l_Std_TreeSet_instForInOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_204_, 0, v_inst_203_);
return v___f_204_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionLMVarIdMap(lean_object* v_00_u03b1_205_){
_start:
{
lean_object* v___x_206_; 
v___x_206_ = lean_box(1);
return v___x_206_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInLMVarIdMapProdLMVarIdOfMonad___redArg(lean_object* v_inst_207_){
_start:
{
lean_object* v___f_208_; 
v___f_208_ = lean_alloc_closure((void*)(l_Std_TreeMap_instForInProdOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_208_, 0, v_inst_207_);
return v___f_208_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInLMVarIdMapProdLMVarIdOfMonad(lean_object* v_m_209_, lean_object* v_00_u03b1_210_, lean_object* v_inst_211_){
_start:
{
lean_object* v___f_212_; 
v___f_212_ = lean_alloc_closure((void*)(l_Std_TreeMap_instForInProdOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_212_, 0, v_inst_211_);
return v___f_212_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedLMVarIdMap(lean_object* v_00_u03b1_213_){
_start:
{
lean_object* v___x_214_; 
v___x_214_ = lean_box(1);
return v___x_214_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_ctorIdx(lean_object* v_x_215_){
_start:
{
switch(lean_obj_tag(v_x_215_))
{
case 0:
{
lean_object* v___x_216_; 
v___x_216_ = lean_unsigned_to_nat(0u);
return v___x_216_;
}
case 1:
{
lean_object* v___x_217_; 
v___x_217_ = lean_unsigned_to_nat(1u);
return v___x_217_;
}
case 2:
{
lean_object* v___x_218_; 
v___x_218_ = lean_unsigned_to_nat(2u);
return v___x_218_;
}
case 3:
{
lean_object* v___x_219_; 
v___x_219_ = lean_unsigned_to_nat(3u);
return v___x_219_;
}
case 4:
{
lean_object* v___x_220_; 
v___x_220_ = lean_unsigned_to_nat(4u);
return v___x_220_;
}
default: 
{
lean_object* v___x_221_; 
v___x_221_ = lean_unsigned_to_nat(5u);
return v___x_221_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_ctorIdx___boxed(lean_object* v_x_222_){
_start:
{
lean_object* v_res_223_; 
v_res_223_ = l_Lean_Level_ctorIdx(v_x_222_);
lean_dec(v_x_222_);
return v_res_223_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_ctorElim___redArg(lean_object* v_t_224_, lean_object* v_k_225_){
_start:
{
switch(lean_obj_tag(v_t_224_))
{
case 0:
{
return v_k_225_;
}
case 2:
{
lean_object* v_a_226_; lean_object* v_a_227_; lean_object* v___x_228_; 
v_a_226_ = lean_ctor_get(v_t_224_, 0);
lean_inc(v_a_226_);
v_a_227_ = lean_ctor_get(v_t_224_, 1);
lean_inc(v_a_227_);
lean_dec_ref(v_t_224_);
v___x_228_ = lean_apply_2(v_k_225_, v_a_226_, v_a_227_);
return v___x_228_;
}
case 3:
{
lean_object* v_a_229_; lean_object* v_a_230_; lean_object* v___x_231_; 
v_a_229_ = lean_ctor_get(v_t_224_, 0);
lean_inc(v_a_229_);
v_a_230_ = lean_ctor_get(v_t_224_, 1);
lean_inc(v_a_230_);
lean_dec_ref(v_t_224_);
v___x_231_ = lean_apply_2(v_k_225_, v_a_229_, v_a_230_);
return v___x_231_;
}
default: 
{
lean_object* v_a_232_; lean_object* v___x_233_; 
v_a_232_ = lean_ctor_get(v_t_224_, 0);
lean_inc(v_a_232_);
lean_dec(v_t_224_);
v___x_233_ = lean_apply_1(v_k_225_, v_a_232_);
return v___x_233_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_ctorElim(lean_object* v_motive_234_, lean_object* v_ctorIdx_235_, lean_object* v_t_236_, lean_object* v_h_237_, lean_object* v_k_238_){
_start:
{
lean_object* v___x_239_; 
v___x_239_ = l_Lean_Level_ctorElim___redArg(v_t_236_, v_k_238_);
return v___x_239_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_ctorElim___boxed(lean_object* v_motive_240_, lean_object* v_ctorIdx_241_, lean_object* v_t_242_, lean_object* v_h_243_, lean_object* v_k_244_){
_start:
{
lean_object* v_res_245_; 
v_res_245_ = l_Lean_Level_ctorElim(v_motive_240_, v_ctorIdx_241_, v_t_242_, v_h_243_, v_k_244_);
lean_dec(v_ctorIdx_241_);
return v_res_245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_zero_elim___redArg(lean_object* v_t_246_, lean_object* v_zero_247_){
_start:
{
lean_object* v___x_248_; 
v___x_248_ = l_Lean_Level_ctorElim___redArg(v_t_246_, v_zero_247_);
return v___x_248_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_zero_elim(lean_object* v_motive_249_, lean_object* v_t_250_, lean_object* v_h_251_, lean_object* v_zero_252_){
_start:
{
lean_object* v___x_253_; 
v___x_253_ = l_Lean_Level_ctorElim___redArg(v_t_250_, v_zero_252_);
return v___x_253_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_succ_elim___redArg(lean_object* v_t_254_, lean_object* v_succ_255_){
_start:
{
lean_object* v___x_256_; 
v___x_256_ = l_Lean_Level_ctorElim___redArg(v_t_254_, v_succ_255_);
return v___x_256_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_succ_elim(lean_object* v_motive_257_, lean_object* v_t_258_, lean_object* v_h_259_, lean_object* v_succ_260_){
_start:
{
lean_object* v___x_261_; 
v___x_261_ = l_Lean_Level_ctorElim___redArg(v_t_258_, v_succ_260_);
return v___x_261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_max_elim___redArg(lean_object* v_t_262_, lean_object* v_max_263_){
_start:
{
lean_object* v___x_264_; 
v___x_264_ = l_Lean_Level_ctorElim___redArg(v_t_262_, v_max_263_);
return v___x_264_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_max_elim(lean_object* v_motive_265_, lean_object* v_t_266_, lean_object* v_h_267_, lean_object* v_max_268_){
_start:
{
lean_object* v___x_269_; 
v___x_269_ = l_Lean_Level_ctorElim___redArg(v_t_266_, v_max_268_);
return v___x_269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_imax_elim___redArg(lean_object* v_t_270_, lean_object* v_imax_271_){
_start:
{
lean_object* v___x_272_; 
v___x_272_ = l_Lean_Level_ctorElim___redArg(v_t_270_, v_imax_271_);
return v___x_272_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_imax_elim(lean_object* v_motive_273_, lean_object* v_t_274_, lean_object* v_h_275_, lean_object* v_imax_276_){
_start:
{
lean_object* v___x_277_; 
v___x_277_ = l_Lean_Level_ctorElim___redArg(v_t_274_, v_imax_276_);
return v___x_277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_param_elim___redArg(lean_object* v_t_278_, lean_object* v_param_279_){
_start:
{
lean_object* v___x_280_; 
v___x_280_ = l_Lean_Level_ctorElim___redArg(v_t_278_, v_param_279_);
return v___x_280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_param_elim(lean_object* v_motive_281_, lean_object* v_t_282_, lean_object* v_h_283_, lean_object* v_param_284_){
_start:
{
lean_object* v___x_285_; 
v___x_285_ = l_Lean_Level_ctorElim___redArg(v_t_282_, v_param_284_);
return v___x_285_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_mvar_elim___redArg(lean_object* v_t_286_, lean_object* v_mvar_287_){
_start:
{
lean_object* v___x_288_; 
v___x_288_ = l_Lean_Level_ctorElim___redArg(v_t_286_, v_mvar_287_);
return v___x_288_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_mvar_elim(lean_object* v_motive_289_, lean_object* v_t_290_, lean_object* v_h_291_, lean_object* v_mvar_292_){
_start:
{
lean_object* v___x_293_; 
v___x_293_ = l_Lean_Level_ctorElim___redArg(v_t_290_, v_mvar_292_);
return v___x_293_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_casesOn___override___redArg(lean_object* v_t_294_, lean_object* v_zero_295_, lean_object* v_succ_296_, lean_object* v_max_297_, lean_object* v_imax_298_, lean_object* v_param_299_, lean_object* v_mvar_300_){
_start:
{
switch(lean_obj_tag(v_t_294_))
{
case 0:
{
lean_dec(v_mvar_300_);
lean_dec(v_param_299_);
lean_dec(v_imax_298_);
lean_dec(v_max_297_);
lean_dec(v_succ_296_);
lean_inc(v_zero_295_);
return v_zero_295_;
}
case 1:
{
lean_object* v_a_301_; lean_object* v___x_302_; 
lean_dec(v_mvar_300_);
lean_dec(v_param_299_);
lean_dec(v_imax_298_);
lean_dec(v_max_297_);
v_a_301_ = lean_ctor_get(v_t_294_, 0);
lean_inc(v_a_301_);
lean_dec_ref(v_t_294_);
v___x_302_ = lean_apply_1(v_succ_296_, v_a_301_);
return v___x_302_;
}
case 2:
{
lean_object* v_a_303_; lean_object* v_a_304_; lean_object* v___x_305_; 
lean_dec(v_mvar_300_);
lean_dec(v_param_299_);
lean_dec(v_imax_298_);
lean_dec(v_succ_296_);
v_a_303_ = lean_ctor_get(v_t_294_, 0);
lean_inc(v_a_303_);
v_a_304_ = lean_ctor_get(v_t_294_, 1);
lean_inc(v_a_304_);
lean_dec_ref(v_t_294_);
v___x_305_ = lean_apply_2(v_max_297_, v_a_303_, v_a_304_);
return v___x_305_;
}
case 3:
{
lean_object* v_a_306_; lean_object* v_a_307_; lean_object* v___x_308_; 
lean_dec(v_mvar_300_);
lean_dec(v_param_299_);
lean_dec(v_max_297_);
lean_dec(v_succ_296_);
v_a_306_ = lean_ctor_get(v_t_294_, 0);
lean_inc(v_a_306_);
v_a_307_ = lean_ctor_get(v_t_294_, 1);
lean_inc(v_a_307_);
lean_dec_ref(v_t_294_);
v___x_308_ = lean_apply_2(v_imax_298_, v_a_306_, v_a_307_);
return v___x_308_;
}
case 4:
{
lean_object* v_a_309_; lean_object* v___x_310_; 
lean_dec(v_mvar_300_);
lean_dec(v_imax_298_);
lean_dec(v_max_297_);
lean_dec(v_succ_296_);
v_a_309_ = lean_ctor_get(v_t_294_, 0);
lean_inc(v_a_309_);
lean_dec_ref(v_t_294_);
v___x_310_ = lean_apply_1(v_param_299_, v_a_309_);
return v___x_310_;
}
default: 
{
lean_object* v_a_311_; lean_object* v___x_312_; 
lean_dec(v_param_299_);
lean_dec(v_imax_298_);
lean_dec(v_max_297_);
lean_dec(v_succ_296_);
v_a_311_ = lean_ctor_get(v_t_294_, 0);
lean_inc(v_a_311_);
lean_dec_ref(v_t_294_);
v___x_312_ = lean_apply_1(v_mvar_300_, v_a_311_);
return v___x_312_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_casesOn___override___redArg___boxed(lean_object* v_t_313_, lean_object* v_zero_314_, lean_object* v_succ_315_, lean_object* v_max_316_, lean_object* v_imax_317_, lean_object* v_param_318_, lean_object* v_mvar_319_){
_start:
{
lean_object* v_res_320_; 
v_res_320_ = l_Lean_Level_casesOn___override___redArg(v_t_313_, v_zero_314_, v_succ_315_, v_max_316_, v_imax_317_, v_param_318_, v_mvar_319_);
lean_dec(v_zero_314_);
return v_res_320_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_casesOn___override(lean_object* v_motive_321_, lean_object* v_t_322_, lean_object* v_zero_323_, lean_object* v_succ_324_, lean_object* v_max_325_, lean_object* v_imax_326_, lean_object* v_param_327_, lean_object* v_mvar_328_){
_start:
{
switch(lean_obj_tag(v_t_322_))
{
case 0:
{
lean_dec(v_mvar_328_);
lean_dec(v_param_327_);
lean_dec(v_imax_326_);
lean_dec(v_max_325_);
lean_dec(v_succ_324_);
lean_inc(v_zero_323_);
return v_zero_323_;
}
case 1:
{
lean_object* v_a_329_; lean_object* v___x_330_; 
lean_dec(v_mvar_328_);
lean_dec(v_param_327_);
lean_dec(v_imax_326_);
lean_dec(v_max_325_);
v_a_329_ = lean_ctor_get(v_t_322_, 0);
lean_inc(v_a_329_);
lean_dec_ref(v_t_322_);
v___x_330_ = lean_apply_1(v_succ_324_, v_a_329_);
return v___x_330_;
}
case 2:
{
lean_object* v_a_331_; lean_object* v_a_332_; lean_object* v___x_333_; 
lean_dec(v_mvar_328_);
lean_dec(v_param_327_);
lean_dec(v_imax_326_);
lean_dec(v_succ_324_);
v_a_331_ = lean_ctor_get(v_t_322_, 0);
lean_inc(v_a_331_);
v_a_332_ = lean_ctor_get(v_t_322_, 1);
lean_inc(v_a_332_);
lean_dec_ref(v_t_322_);
v___x_333_ = lean_apply_2(v_max_325_, v_a_331_, v_a_332_);
return v___x_333_;
}
case 3:
{
lean_object* v_a_334_; lean_object* v_a_335_; lean_object* v___x_336_; 
lean_dec(v_mvar_328_);
lean_dec(v_param_327_);
lean_dec(v_max_325_);
lean_dec(v_succ_324_);
v_a_334_ = lean_ctor_get(v_t_322_, 0);
lean_inc(v_a_334_);
v_a_335_ = lean_ctor_get(v_t_322_, 1);
lean_inc(v_a_335_);
lean_dec_ref(v_t_322_);
v___x_336_ = lean_apply_2(v_imax_326_, v_a_334_, v_a_335_);
return v___x_336_;
}
case 4:
{
lean_object* v_a_337_; lean_object* v___x_338_; 
lean_dec(v_mvar_328_);
lean_dec(v_imax_326_);
lean_dec(v_max_325_);
lean_dec(v_succ_324_);
v_a_337_ = lean_ctor_get(v_t_322_, 0);
lean_inc(v_a_337_);
lean_dec_ref(v_t_322_);
v___x_338_ = lean_apply_1(v_param_327_, v_a_337_);
return v___x_338_;
}
default: 
{
lean_object* v_a_339_; lean_object* v___x_340_; 
lean_dec(v_param_327_);
lean_dec(v_imax_326_);
lean_dec(v_max_325_);
lean_dec(v_succ_324_);
v_a_339_ = lean_ctor_get(v_t_322_, 0);
lean_inc(v_a_339_);
lean_dec_ref(v_t_322_);
v___x_340_ = lean_apply_1(v_mvar_328_, v_a_339_);
return v___x_340_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_casesOn___override___boxed(lean_object* v_motive_341_, lean_object* v_t_342_, lean_object* v_zero_343_, lean_object* v_succ_344_, lean_object* v_max_345_, lean_object* v_imax_346_, lean_object* v_param_347_, lean_object* v_mvar_348_){
_start:
{
lean_object* v_res_349_; 
v_res_349_ = l_Lean_Level_casesOn___override(v_motive_341_, v_t_342_, v_zero_343_, v_succ_344_, v_max_345_, v_imax_346_, v_param_347_, v_mvar_348_);
lean_dec(v_zero_343_);
return v_res_349_;
}
}
static lean_object* _init_l_Lean_Level_zero___override(void){
_start:
{
lean_object* v___x_350_; 
v___x_350_ = lean_box(0);
return v___x_350_;
}
}
static uint64_t _init_l_Lean_Level_data___override___closed__0(void){
_start:
{
uint8_t v___x_351_; lean_object* v___x_352_; uint64_t v___x_353_; uint64_t v___x_354_; 
v___x_351_ = 0;
v___x_352_ = lean_unsigned_to_nat(0u);
v___x_353_ = 2221ULL;
v___x_354_ = lean_level_mk_data(v___x_353_, v___x_352_, v___x_351_, v___x_351_);
return v___x_354_;
}
}
LEAN_EXPORT uint64_t l_Lean_Level_data___override(lean_object* v_x_355_){
_start:
{
switch(lean_obj_tag(v_x_355_))
{
case 0:
{
uint64_t v___x_356_; 
v___x_356_ = lean_uint64_once(&l_Lean_Level_data___override___closed__0, &l_Lean_Level_data___override___closed__0_once, _init_l_Lean_Level_data___override___closed__0);
return v___x_356_;
}
case 2:
{
uint64_t v_data_357_; 
v_data_357_ = lean_ctor_get_uint64(v_x_355_, sizeof(void*)*2);
return v_data_357_;
}
case 3:
{
uint64_t v_data_358_; 
v_data_358_ = lean_ctor_get_uint64(v_x_355_, sizeof(void*)*2);
return v_data_358_;
}
default: 
{
uint64_t v_data_359_; 
v_data_359_ = lean_ctor_get_uint64(v_x_355_, sizeof(void*)*1);
return v_data_359_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_data___override___boxed(lean_object* v_x_360_){
_start:
{
uint64_t v_res_361_; lean_object* v_r_362_; 
v_res_361_ = l_Lean_Level_data___override(v_x_360_);
lean_dec(v_x_360_);
v_r_362_ = lean_box_uint64(v_res_361_);
return v_r_362_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_succ___override(lean_object* v_a_363_){
_start:
{
uint64_t v___x_364_; uint64_t v___x_365_; uint64_t v___x_366_; uint64_t v___x_367_; uint32_t v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; uint8_t v___x_372_; uint8_t v___x_373_; uint64_t v___x_374_; lean_object* v___x_375_; 
v___x_364_ = 2243ULL;
v___x_365_ = l_Lean_Level_data___override(v_a_363_);
v___x_366_ = l_Lean_Level_Data_hash(v___x_365_);
v___x_367_ = lean_uint64_mix_hash(v___x_364_, v___x_366_);
v___x_368_ = l_Lean_Level_Data_depth(v___x_365_);
v___x_369_ = lean_uint32_to_nat(v___x_368_);
v___x_370_ = lean_unsigned_to_nat(1u);
v___x_371_ = lean_nat_add(v___x_369_, v___x_370_);
lean_dec(v___x_369_);
v___x_372_ = l_Lean_Level_Data_hasMVar(v___x_365_);
v___x_373_ = l_Lean_Level_Data_hasParam(v___x_365_);
v___x_374_ = lean_level_mk_data(v___x_367_, v___x_371_, v___x_372_, v___x_373_);
v___x_375_ = lean_alloc_ctor(1, 1, 8);
lean_ctor_set(v___x_375_, 0, v_a_363_);
lean_ctor_set_uint64(v___x_375_, sizeof(void*)*1, v___x_374_);
return v___x_375_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_max___override(lean_object* v_a_376_, lean_object* v_a_377_){
_start:
{
uint64_t v___x_378_; uint64_t v___x_379_; uint64_t v___x_380_; uint64_t v___x_381_; uint64_t v___x_382_; uint64_t v___x_383_; uint64_t v___x_384_; lean_object* v___y_386_; uint8_t v___y_387_; uint8_t v___y_388_; lean_object* v___y_392_; uint8_t v___y_393_; lean_object* v___y_397_; uint32_t v___x_402_; lean_object* v___x_403_; uint32_t v___x_404_; lean_object* v___x_405_; uint8_t v___x_406_; 
v___x_378_ = 2251ULL;
v___x_379_ = l_Lean_Level_data___override(v_a_376_);
v___x_380_ = l_Lean_Level_Data_hash(v___x_379_);
v___x_381_ = l_Lean_Level_data___override(v_a_377_);
v___x_382_ = l_Lean_Level_Data_hash(v___x_381_);
v___x_383_ = lean_uint64_mix_hash(v___x_380_, v___x_382_);
v___x_384_ = lean_uint64_mix_hash(v___x_378_, v___x_383_);
v___x_402_ = l_Lean_Level_Data_depth(v___x_379_);
v___x_403_ = lean_uint32_to_nat(v___x_402_);
v___x_404_ = l_Lean_Level_Data_depth(v___x_381_);
v___x_405_ = lean_uint32_to_nat(v___x_404_);
v___x_406_ = lean_nat_dec_le(v___x_403_, v___x_405_);
if (v___x_406_ == 0)
{
lean_dec(v___x_405_);
v___y_397_ = v___x_403_;
goto v___jp_396_;
}
else
{
lean_dec(v___x_403_);
v___y_397_ = v___x_405_;
goto v___jp_396_;
}
v___jp_385_:
{
uint64_t v___x_389_; lean_object* v___x_390_; 
v___x_389_ = lean_level_mk_data(v___x_384_, v___y_386_, v___y_387_, v___y_388_);
v___x_390_ = lean_alloc_ctor(2, 2, 8);
lean_ctor_set(v___x_390_, 0, v_a_376_);
lean_ctor_set(v___x_390_, 1, v_a_377_);
lean_ctor_set_uint64(v___x_390_, sizeof(void*)*2, v___x_389_);
return v___x_390_;
}
v___jp_391_:
{
uint8_t v___x_394_; 
v___x_394_ = l_Lean_Level_Data_hasParam(v___x_379_);
if (v___x_394_ == 0)
{
uint8_t v___x_395_; 
v___x_395_ = l_Lean_Level_Data_hasParam(v___x_381_);
v___y_386_ = v___y_392_;
v___y_387_ = v___y_393_;
v___y_388_ = v___x_395_;
goto v___jp_385_;
}
else
{
v___y_386_ = v___y_392_;
v___y_387_ = v___y_393_;
v___y_388_ = v___x_394_;
goto v___jp_385_;
}
}
v___jp_396_:
{
lean_object* v___x_398_; lean_object* v___x_399_; uint8_t v___x_400_; 
v___x_398_ = lean_unsigned_to_nat(1u);
v___x_399_ = lean_nat_add(v___y_397_, v___x_398_);
lean_dec(v___y_397_);
v___x_400_ = l_Lean_Level_Data_hasMVar(v___x_379_);
if (v___x_400_ == 0)
{
uint8_t v___x_401_; 
v___x_401_ = l_Lean_Level_Data_hasMVar(v___x_381_);
v___y_392_ = v___x_399_;
v___y_393_ = v___x_401_;
goto v___jp_391_;
}
else
{
v___y_392_ = v___x_399_;
v___y_393_ = v___x_400_;
goto v___jp_391_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_imax___override(lean_object* v_a_407_, lean_object* v_a_408_){
_start:
{
uint64_t v___x_409_; uint64_t v___x_410_; uint64_t v___x_411_; uint64_t v___x_412_; uint64_t v___x_413_; uint64_t v___x_414_; uint64_t v___x_415_; lean_object* v___y_417_; uint8_t v___y_418_; uint8_t v___y_419_; lean_object* v___y_423_; uint8_t v___y_424_; lean_object* v___y_428_; uint32_t v___x_433_; lean_object* v___x_434_; uint32_t v___x_435_; lean_object* v___x_436_; uint8_t v___x_437_; 
v___x_409_ = 2267ULL;
v___x_410_ = l_Lean_Level_data___override(v_a_407_);
v___x_411_ = l_Lean_Level_Data_hash(v___x_410_);
v___x_412_ = l_Lean_Level_data___override(v_a_408_);
v___x_413_ = l_Lean_Level_Data_hash(v___x_412_);
v___x_414_ = lean_uint64_mix_hash(v___x_411_, v___x_413_);
v___x_415_ = lean_uint64_mix_hash(v___x_409_, v___x_414_);
v___x_433_ = l_Lean_Level_Data_depth(v___x_410_);
v___x_434_ = lean_uint32_to_nat(v___x_433_);
v___x_435_ = l_Lean_Level_Data_depth(v___x_412_);
v___x_436_ = lean_uint32_to_nat(v___x_435_);
v___x_437_ = lean_nat_dec_le(v___x_434_, v___x_436_);
if (v___x_437_ == 0)
{
lean_dec(v___x_436_);
v___y_428_ = v___x_434_;
goto v___jp_427_;
}
else
{
lean_dec(v___x_434_);
v___y_428_ = v___x_436_;
goto v___jp_427_;
}
v___jp_416_:
{
uint64_t v___x_420_; lean_object* v___x_421_; 
v___x_420_ = lean_level_mk_data(v___x_415_, v___y_417_, v___y_418_, v___y_419_);
v___x_421_ = lean_alloc_ctor(3, 2, 8);
lean_ctor_set(v___x_421_, 0, v_a_407_);
lean_ctor_set(v___x_421_, 1, v_a_408_);
lean_ctor_set_uint64(v___x_421_, sizeof(void*)*2, v___x_420_);
return v___x_421_;
}
v___jp_422_:
{
uint8_t v___x_425_; 
v___x_425_ = l_Lean_Level_Data_hasParam(v___x_410_);
if (v___x_425_ == 0)
{
uint8_t v___x_426_; 
v___x_426_ = l_Lean_Level_Data_hasParam(v___x_412_);
v___y_417_ = v___y_423_;
v___y_418_ = v___y_424_;
v___y_419_ = v___x_426_;
goto v___jp_416_;
}
else
{
v___y_417_ = v___y_423_;
v___y_418_ = v___y_424_;
v___y_419_ = v___x_425_;
goto v___jp_416_;
}
}
v___jp_427_:
{
lean_object* v___x_429_; lean_object* v___x_430_; uint8_t v___x_431_; 
v___x_429_ = lean_unsigned_to_nat(1u);
v___x_430_ = lean_nat_add(v___y_428_, v___x_429_);
lean_dec(v___y_428_);
v___x_431_ = l_Lean_Level_Data_hasMVar(v___x_410_);
if (v___x_431_ == 0)
{
uint8_t v___x_432_; 
v___x_432_ = l_Lean_Level_Data_hasMVar(v___x_412_);
v___y_423_ = v___x_430_;
v___y_424_ = v___x_432_;
goto v___jp_422_;
}
else
{
v___y_423_ = v___x_430_;
v___y_424_ = v___x_431_;
goto v___jp_422_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_param___override(lean_object* v_a_438_){
_start:
{
uint64_t v___x_439_; uint64_t v___y_441_; 
v___x_439_ = 2239ULL;
if (lean_obj_tag(v_a_438_) == 0)
{
uint64_t v___x_448_; 
v___x_448_ = lean_uint64_once(&l_Lean_instHashableLevelMVarId_hash___closed__0, &l_Lean_instHashableLevelMVarId_hash___closed__0_once, _init_l_Lean_instHashableLevelMVarId_hash___closed__0);
v___y_441_ = v___x_448_;
goto v___jp_440_;
}
else
{
uint64_t v_hash_449_; 
v_hash_449_ = lean_ctor_get_uint64(v_a_438_, sizeof(void*)*2);
v___y_441_ = v_hash_449_;
goto v___jp_440_;
}
v___jp_440_:
{
uint64_t v___x_442_; lean_object* v___x_443_; uint8_t v___x_444_; uint8_t v___x_445_; uint64_t v___x_446_; lean_object* v___x_447_; 
v___x_442_ = lean_uint64_mix_hash(v___x_439_, v___y_441_);
v___x_443_ = lean_unsigned_to_nat(0u);
v___x_444_ = 0;
v___x_445_ = 1;
v___x_446_ = lean_level_mk_data(v___x_442_, v___x_443_, v___x_444_, v___x_445_);
v___x_447_ = lean_alloc_ctor(4, 1, 8);
lean_ctor_set(v___x_447_, 0, v_a_438_);
lean_ctor_set_uint64(v___x_447_, sizeof(void*)*1, v___x_446_);
return v___x_447_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_mvar___override(lean_object* v_a_450_){
_start:
{
uint64_t v___x_451_; uint64_t v___x_452_; uint64_t v___x_453_; lean_object* v___x_454_; uint8_t v___x_455_; uint8_t v___x_456_; uint64_t v___x_457_; lean_object* v___x_458_; 
v___x_451_ = 2237ULL;
v___x_452_ = l_Lean_instHashableLevelMVarId_hash(v_a_450_);
v___x_453_ = lean_uint64_mix_hash(v___x_451_, v___x_452_);
v___x_454_ = lean_unsigned_to_nat(0u);
v___x_455_ = 1;
v___x_456_ = 0;
v___x_457_ = lean_level_mk_data(v___x_453_, v___x_454_, v___x_455_, v___x_456_);
v___x_458_ = lean_alloc_ctor(5, 1, 8);
lean_ctor_set(v___x_458_, 0, v_a_450_);
lean_ctor_set_uint64(v___x_458_, sizeof(void*)*1, v___x_457_);
return v___x_458_;
}
}
static lean_object* _init_l_Lean_instInhabitedLevel_default(void){
_start:
{
lean_object* v___x_459_; 
v___x_459_ = lean_box(0);
return v___x_459_;
}
}
static lean_object* _init_l_Lean_instInhabitedLevel(void){
_start:
{
lean_object* v___x_460_; 
v___x_460_ = lean_box(0);
return v___x_460_;
}
}
static lean_object* _init_l_Lean_instReprLevel_repr___closed__2(void){
_start:
{
lean_object* v___x_464_; lean_object* v___x_465_; 
v___x_464_ = lean_unsigned_to_nat(2u);
v___x_465_ = lean_nat_to_int(v___x_464_);
return v___x_465_;
}
}
static lean_object* _init_l_Lean_instReprLevel_repr___closed__3(void){
_start:
{
lean_object* v___x_466_; lean_object* v___x_467_; 
v___x_466_ = lean_unsigned_to_nat(1u);
v___x_467_ = lean_nat_to_int(v___x_466_);
return v___x_467_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprLevel_repr(lean_object* v_x_498_, lean_object* v_prec_499_){
_start:
{
lean_object* v___y_501_; 
switch(lean_obj_tag(v_x_498_))
{
case 0:
{
lean_object* v___x_507_; uint8_t v___x_508_; 
v___x_507_ = lean_unsigned_to_nat(1024u);
v___x_508_ = lean_nat_dec_le(v___x_507_, v_prec_499_);
if (v___x_508_ == 0)
{
lean_object* v___x_509_; 
v___x_509_ = lean_obj_once(&l_Lean_instReprLevel_repr___closed__2, &l_Lean_instReprLevel_repr___closed__2_once, _init_l_Lean_instReprLevel_repr___closed__2);
v___y_501_ = v___x_509_;
goto v___jp_500_;
}
else
{
lean_object* v___x_510_; 
v___x_510_ = lean_obj_once(&l_Lean_instReprLevel_repr___closed__3, &l_Lean_instReprLevel_repr___closed__3_once, _init_l_Lean_instReprLevel_repr___closed__3);
v___y_501_ = v___x_510_;
goto v___jp_500_;
}
}
case 1:
{
lean_object* v_a_511_; lean_object* v___x_512_; lean_object* v___y_514_; uint8_t v___x_522_; 
v_a_511_ = lean_ctor_get(v_x_498_, 0);
lean_inc(v_a_511_);
lean_dec_ref(v_x_498_);
v___x_512_ = lean_unsigned_to_nat(1024u);
v___x_522_ = lean_nat_dec_le(v___x_512_, v_prec_499_);
if (v___x_522_ == 0)
{
lean_object* v___x_523_; 
v___x_523_ = lean_obj_once(&l_Lean_instReprLevel_repr___closed__2, &l_Lean_instReprLevel_repr___closed__2_once, _init_l_Lean_instReprLevel_repr___closed__2);
v___y_514_ = v___x_523_;
goto v___jp_513_;
}
else
{
lean_object* v___x_524_; 
v___x_524_ = lean_obj_once(&l_Lean_instReprLevel_repr___closed__3, &l_Lean_instReprLevel_repr___closed__3_once, _init_l_Lean_instReprLevel_repr___closed__3);
v___y_514_ = v___x_524_;
goto v___jp_513_;
}
v___jp_513_:
{
lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; uint8_t v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; 
v___x_515_ = ((lean_object*)(l_Lean_instReprLevel_repr___closed__6));
v___x_516_ = l_Lean_instReprLevel_repr(v_a_511_, v___x_512_);
v___x_517_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_517_, 0, v___x_515_);
lean_ctor_set(v___x_517_, 1, v___x_516_);
v___x_518_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_518_, 0, v___y_514_);
lean_ctor_set(v___x_518_, 1, v___x_517_);
v___x_519_ = 0;
v___x_520_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_520_, 0, v___x_518_);
lean_ctor_set_uint8(v___x_520_, sizeof(void*)*1, v___x_519_);
v___x_521_ = l_Repr_addAppParen(v___x_520_, v_prec_499_);
return v___x_521_;
}
}
case 2:
{
lean_object* v_a_525_; lean_object* v_a_526_; lean_object* v___x_527_; lean_object* v___y_529_; uint8_t v___x_541_; 
v_a_525_ = lean_ctor_get(v_x_498_, 0);
lean_inc(v_a_525_);
v_a_526_ = lean_ctor_get(v_x_498_, 1);
lean_inc(v_a_526_);
lean_dec_ref(v_x_498_);
v___x_527_ = lean_unsigned_to_nat(1024u);
v___x_541_ = lean_nat_dec_le(v___x_527_, v_prec_499_);
if (v___x_541_ == 0)
{
lean_object* v___x_542_; 
v___x_542_ = lean_obj_once(&l_Lean_instReprLevel_repr___closed__2, &l_Lean_instReprLevel_repr___closed__2_once, _init_l_Lean_instReprLevel_repr___closed__2);
v___y_529_ = v___x_542_;
goto v___jp_528_;
}
else
{
lean_object* v___x_543_; 
v___x_543_ = lean_obj_once(&l_Lean_instReprLevel_repr___closed__3, &l_Lean_instReprLevel_repr___closed__3_once, _init_l_Lean_instReprLevel_repr___closed__3);
v___y_529_ = v___x_543_;
goto v___jp_528_;
}
v___jp_528_:
{
lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; uint8_t v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; 
v___x_530_ = lean_box(1);
v___x_531_ = ((lean_object*)(l_Lean_instReprLevel_repr___closed__9));
v___x_532_ = l_Lean_instReprLevel_repr(v_a_525_, v___x_527_);
v___x_533_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_533_, 0, v___x_531_);
lean_ctor_set(v___x_533_, 1, v___x_532_);
v___x_534_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_534_, 0, v___x_533_);
lean_ctor_set(v___x_534_, 1, v___x_530_);
v___x_535_ = l_Lean_instReprLevel_repr(v_a_526_, v___x_527_);
v___x_536_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_536_, 0, v___x_534_);
lean_ctor_set(v___x_536_, 1, v___x_535_);
v___x_537_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_537_, 0, v___y_529_);
lean_ctor_set(v___x_537_, 1, v___x_536_);
v___x_538_ = 0;
v___x_539_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_539_, 0, v___x_537_);
lean_ctor_set_uint8(v___x_539_, sizeof(void*)*1, v___x_538_);
v___x_540_ = l_Repr_addAppParen(v___x_539_, v_prec_499_);
return v___x_540_;
}
}
case 3:
{
lean_object* v_a_544_; lean_object* v_a_545_; lean_object* v___x_546_; lean_object* v___y_548_; uint8_t v___x_560_; 
v_a_544_ = lean_ctor_get(v_x_498_, 0);
lean_inc(v_a_544_);
v_a_545_ = lean_ctor_get(v_x_498_, 1);
lean_inc(v_a_545_);
lean_dec_ref(v_x_498_);
v___x_546_ = lean_unsigned_to_nat(1024u);
v___x_560_ = lean_nat_dec_le(v___x_546_, v_prec_499_);
if (v___x_560_ == 0)
{
lean_object* v___x_561_; 
v___x_561_ = lean_obj_once(&l_Lean_instReprLevel_repr___closed__2, &l_Lean_instReprLevel_repr___closed__2_once, _init_l_Lean_instReprLevel_repr___closed__2);
v___y_548_ = v___x_561_;
goto v___jp_547_;
}
else
{
lean_object* v___x_562_; 
v___x_562_ = lean_obj_once(&l_Lean_instReprLevel_repr___closed__3, &l_Lean_instReprLevel_repr___closed__3_once, _init_l_Lean_instReprLevel_repr___closed__3);
v___y_548_ = v___x_562_;
goto v___jp_547_;
}
v___jp_547_:
{
lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; uint8_t v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; 
v___x_549_ = lean_box(1);
v___x_550_ = ((lean_object*)(l_Lean_instReprLevel_repr___closed__12));
v___x_551_ = l_Lean_instReprLevel_repr(v_a_544_, v___x_546_);
v___x_552_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_552_, 0, v___x_550_);
lean_ctor_set(v___x_552_, 1, v___x_551_);
v___x_553_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_553_, 0, v___x_552_);
lean_ctor_set(v___x_553_, 1, v___x_549_);
v___x_554_ = l_Lean_instReprLevel_repr(v_a_545_, v___x_546_);
v___x_555_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_555_, 0, v___x_553_);
lean_ctor_set(v___x_555_, 1, v___x_554_);
v___x_556_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_556_, 0, v___y_548_);
lean_ctor_set(v___x_556_, 1, v___x_555_);
v___x_557_ = 0;
v___x_558_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_558_, 0, v___x_556_);
lean_ctor_set_uint8(v___x_558_, sizeof(void*)*1, v___x_557_);
v___x_559_ = l_Repr_addAppParen(v___x_558_, v_prec_499_);
return v___x_559_;
}
}
case 4:
{
lean_object* v_a_563_; lean_object* v___y_565_; lean_object* v___x_574_; uint8_t v___x_575_; 
v_a_563_ = lean_ctor_get(v_x_498_, 0);
lean_inc(v_a_563_);
lean_dec_ref(v_x_498_);
v___x_574_ = lean_unsigned_to_nat(1024u);
v___x_575_ = lean_nat_dec_le(v___x_574_, v_prec_499_);
if (v___x_575_ == 0)
{
lean_object* v___x_576_; 
v___x_576_ = lean_obj_once(&l_Lean_instReprLevel_repr___closed__2, &l_Lean_instReprLevel_repr___closed__2_once, _init_l_Lean_instReprLevel_repr___closed__2);
v___y_565_ = v___x_576_;
goto v___jp_564_;
}
else
{
lean_object* v___x_577_; 
v___x_577_ = lean_obj_once(&l_Lean_instReprLevel_repr___closed__3, &l_Lean_instReprLevel_repr___closed__3_once, _init_l_Lean_instReprLevel_repr___closed__3);
v___y_565_ = v___x_577_;
goto v___jp_564_;
}
v___jp_564_:
{
lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; uint8_t v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; 
v___x_566_ = ((lean_object*)(l_Lean_instReprLevel_repr___closed__15));
v___x_567_ = lean_unsigned_to_nat(1024u);
v___x_568_ = l_Lean_Name_reprPrec(v_a_563_, v___x_567_);
v___x_569_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_569_, 0, v___x_566_);
lean_ctor_set(v___x_569_, 1, v___x_568_);
v___x_570_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_570_, 0, v___y_565_);
lean_ctor_set(v___x_570_, 1, v___x_569_);
v___x_571_ = 0;
v___x_572_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_572_, 0, v___x_570_);
lean_ctor_set_uint8(v___x_572_, sizeof(void*)*1, v___x_571_);
v___x_573_ = l_Repr_addAppParen(v___x_572_, v_prec_499_);
return v___x_573_;
}
}
default: 
{
lean_object* v_a_578_; lean_object* v___y_580_; lean_object* v___x_589_; uint8_t v___x_590_; 
v_a_578_ = lean_ctor_get(v_x_498_, 0);
lean_inc(v_a_578_);
lean_dec_ref(v_x_498_);
v___x_589_ = lean_unsigned_to_nat(1024u);
v___x_590_ = lean_nat_dec_le(v___x_589_, v_prec_499_);
if (v___x_590_ == 0)
{
lean_object* v___x_591_; 
v___x_591_ = lean_obj_once(&l_Lean_instReprLevel_repr___closed__2, &l_Lean_instReprLevel_repr___closed__2_once, _init_l_Lean_instReprLevel_repr___closed__2);
v___y_580_ = v___x_591_;
goto v___jp_579_;
}
else
{
lean_object* v___x_592_; 
v___x_592_ = lean_obj_once(&l_Lean_instReprLevel_repr___closed__3, &l_Lean_instReprLevel_repr___closed__3_once, _init_l_Lean_instReprLevel_repr___closed__3);
v___y_580_ = v___x_592_;
goto v___jp_579_;
}
v___jp_579_:
{
lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; uint8_t v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; 
v___x_581_ = ((lean_object*)(l_Lean_instReprLevel_repr___closed__18));
v___x_582_ = lean_unsigned_to_nat(1024u);
v___x_583_ = l_Lean_Name_reprPrec(v_a_578_, v___x_582_);
v___x_584_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_584_, 0, v___x_581_);
lean_ctor_set(v___x_584_, 1, v___x_583_);
v___x_585_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_585_, 0, v___y_580_);
lean_ctor_set(v___x_585_, 1, v___x_584_);
v___x_586_ = 0;
v___x_587_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_587_, 0, v___x_585_);
lean_ctor_set_uint8(v___x_587_, sizeof(void*)*1, v___x_586_);
v___x_588_ = l_Repr_addAppParen(v___x_587_, v_prec_499_);
return v___x_588_;
}
}
}
v___jp_500_:
{
lean_object* v___x_502_; lean_object* v___x_503_; uint8_t v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; 
v___x_502_ = ((lean_object*)(l_Lean_instReprLevel_repr___closed__1));
v___x_503_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_503_, 0, v___y_501_);
lean_ctor_set(v___x_503_, 1, v___x_502_);
v___x_504_ = 0;
v___x_505_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_505_, 0, v___x_503_);
lean_ctor_set_uint8(v___x_505_, sizeof(void*)*1, v___x_504_);
v___x_506_ = l_Repr_addAppParen(v___x_505_, v_prec_499_);
return v___x_506_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instReprLevel_repr___boxed(lean_object* v_x_593_, lean_object* v_prec_594_){
_start:
{
lean_object* v_res_595_; 
v_res_595_ = l_Lean_instReprLevel_repr(v_x_593_, v_prec_594_);
lean_dec(v_prec_594_);
return v_res_595_;
}
}
LEAN_EXPORT uint64_t l_Lean_Level_hash(lean_object* v_u_598_){
_start:
{
uint64_t v___x_599_; uint64_t v___x_600_; 
v___x_599_ = l_Lean_Level_data___override(v_u_598_);
v___x_600_ = l_Lean_Level_Data_hash(v___x_599_);
return v___x_600_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_hash___boxed(lean_object* v_u_601_){
_start:
{
uint64_t v_res_602_; lean_object* v_r_603_; 
v_res_602_ = l_Lean_Level_hash(v_u_601_);
lean_dec(v_u_601_);
v_r_603_ = lean_box_uint64(v_res_602_);
return v_r_603_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_depth(lean_object* v_u_606_){
_start:
{
uint64_t v___x_607_; uint32_t v___x_608_; lean_object* v___x_609_; 
v___x_607_ = l_Lean_Level_data___override(v_u_606_);
v___x_608_ = l_Lean_Level_Data_depth(v___x_607_);
v___x_609_ = lean_uint32_to_nat(v___x_608_);
return v___x_609_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_depth___boxed(lean_object* v_u_610_){
_start:
{
lean_object* v_res_611_; 
v_res_611_ = l_Lean_Level_depth(v_u_610_);
lean_dec(v_u_610_);
return v_res_611_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_hasMVar(lean_object* v_u_612_){
_start:
{
uint64_t v___x_613_; uint8_t v___x_614_; 
v___x_613_ = l_Lean_Level_data___override(v_u_612_);
v___x_614_ = l_Lean_Level_Data_hasMVar(v___x_613_);
return v___x_614_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_hasMVar___boxed(lean_object* v_u_615_){
_start:
{
uint8_t v_res_616_; lean_object* v_r_617_; 
v_res_616_ = l_Lean_Level_hasMVar(v_u_615_);
lean_dec(v_u_615_);
v_r_617_ = lean_box(v_res_616_);
return v_r_617_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_hasParam(lean_object* v_u_618_){
_start:
{
uint64_t v___x_619_; uint8_t v___x_620_; 
v___x_619_ = l_Lean_Level_data___override(v_u_618_);
v___x_620_ = l_Lean_Level_Data_hasParam(v___x_619_);
return v___x_620_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_hasParam___boxed(lean_object* v_u_621_){
_start:
{
uint8_t v_res_622_; lean_object* v_r_623_; 
v_res_622_ = l_Lean_Level_hasParam(v_u_621_);
lean_dec(v_u_621_);
v_r_623_ = lean_box(v_res_622_);
return v_r_623_;
}
}
LEAN_EXPORT uint32_t lean_level_hash(lean_object* v_u_624_){
_start:
{
uint64_t v___x_625_; uint32_t v___x_626_; 
v___x_625_ = l_Lean_Level_hash(v_u_624_);
lean_dec(v_u_624_);
v___x_626_ = lean_uint64_to_uint32(v___x_625_);
return v___x_626_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_hashEx___boxed(lean_object* v_u_627_){
_start:
{
uint32_t v_res_628_; lean_object* v_r_629_; 
v_res_628_ = lean_level_hash(v_u_627_);
v_r_629_ = lean_box_uint32(v_res_628_);
return v_r_629_;
}
}
LEAN_EXPORT uint8_t lean_level_has_mvar(lean_object* v_u_630_){
_start:
{
uint8_t v___x_631_; 
v___x_631_ = l_Lean_Level_hasMVar(v_u_630_);
lean_dec(v_u_630_);
return v___x_631_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_hasMVarEx___boxed(lean_object* v_u_632_){
_start:
{
uint8_t v_res_633_; lean_object* v_r_634_; 
v_res_633_ = lean_level_has_mvar(v_u_632_);
v_r_634_ = lean_box(v_res_633_);
return v_r_634_;
}
}
LEAN_EXPORT uint8_t lean_level_has_param(lean_object* v_u_635_){
_start:
{
uint8_t v___x_636_; 
v___x_636_ = l_Lean_Level_hasParam(v_u_635_);
lean_dec(v_u_635_);
return v___x_636_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_hasParamEx___boxed(lean_object* v_u_637_){
_start:
{
uint8_t v_res_638_; lean_object* v_r_639_; 
v_res_638_ = lean_level_has_param(v_u_637_);
v_r_639_ = lean_box(v_res_638_);
return v_r_639_;
}
}
LEAN_EXPORT uint32_t lean_level_depth(lean_object* v_u_640_){
_start:
{
uint64_t v___x_641_; uint32_t v___x_642_; 
v___x_641_ = l_Lean_Level_data___override(v_u_640_);
lean_dec(v_u_640_);
v___x_642_ = l_Lean_Level_Data_depth(v___x_641_);
return v___x_642_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_depthEx___boxed(lean_object* v_u_643_){
_start:
{
uint32_t v_res_644_; lean_object* v_r_645_; 
v_res_644_ = lean_level_depth(v_u_643_);
v_r_645_ = lean_box_uint32(v_res_644_);
return v_r_645_;
}
}
static lean_object* _init_l_Lean_levelZero(void){
_start:
{
lean_object* v___x_646_; 
v___x_646_ = lean_box(0);
return v___x_646_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLevelMVar(lean_object* v_mvarId_647_){
_start:
{
lean_object* v___x_648_; 
v___x_648_ = l_Lean_Level_mvar___override(v_mvarId_647_);
return v___x_648_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLevelParam(lean_object* v_name_649_){
_start:
{
lean_object* v___x_650_; 
v___x_650_ = l_Lean_Level_param___override(v_name_649_);
return v___x_650_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLevelSucc(lean_object* v_u_651_){
_start:
{
lean_object* v___x_652_; 
v___x_652_ = l_Lean_Level_succ___override(v_u_651_);
return v___x_652_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLevelMax(lean_object* v_u_653_, lean_object* v_v_654_){
_start:
{
lean_object* v___x_655_; 
v___x_655_ = l_Lean_Level_max___override(v_u_653_, v_v_654_);
return v___x_655_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLevelIMax(lean_object* v_u_656_, lean_object* v_v_657_){
_start:
{
lean_object* v___x_658_; 
v___x_658_ = l_Lean_Level_imax___override(v_u_656_, v_v_657_);
return v___x_658_;
}
}
static lean_object* _init_l_Lean_Level_one___closed__0(void){
_start:
{
lean_object* v___x_659_; lean_object* v___x_660_; 
v___x_659_ = lean_box(0);
v___x_660_ = l_Lean_Level_succ___override(v___x_659_);
return v___x_660_;
}
}
static lean_object* _init_l_Lean_Level_one(void){
_start:
{
lean_object* v___x_661_; 
v___x_661_ = lean_obj_once(&l_Lean_Level_one___closed__0, &l_Lean_Level_one___closed__0_once, _init_l_Lean_Level_one___closed__0);
return v___x_661_;
}
}
static lean_object* _init_l_Lean_levelOne(void){
_start:
{
lean_object* v___x_662_; 
v___x_662_ = lean_obj_once(&l_Lean_Level_one___closed__0, &l_Lean_Level_one___closed__0_once, _init_l_Lean_Level_one___closed__0);
return v___x_662_;
}
}
LEAN_EXPORT lean_object* lean_level_mk_zero(lean_object* v_x_663_){
_start:
{
lean_object* v___x_664_; 
v___x_664_ = lean_box(0);
return v___x_664_;
}
}
LEAN_EXPORT lean_object* lean_level_mk_succ(lean_object* v_u_665_){
_start:
{
lean_object* v___x_666_; 
v___x_666_ = l_Lean_Level_succ___override(v_u_665_);
return v___x_666_;
}
}
LEAN_EXPORT lean_object* lean_level_mk_mvar(lean_object* v_mvarId_667_){
_start:
{
lean_object* v___x_668_; 
v___x_668_ = l_Lean_Level_mvar___override(v_mvarId_667_);
return v___x_668_;
}
}
LEAN_EXPORT lean_object* lean_level_mk_param(lean_object* v_name_669_){
_start:
{
lean_object* v___x_670_; 
v___x_670_ = l_Lean_Level_param___override(v_name_669_);
return v___x_670_;
}
}
LEAN_EXPORT lean_object* lean_level_mk_max(lean_object* v_u_671_, lean_object* v_v_672_){
_start:
{
lean_object* v___x_673_; 
v___x_673_ = l_Lean_Level_max___override(v_u_671_, v_v_672_);
return v___x_673_;
}
}
LEAN_EXPORT lean_object* lean_level_mk_imax(lean_object* v_u_674_, lean_object* v_v_675_){
_start:
{
lean_object* v___x_676_; 
v___x_676_ = l_Lean_Level_imax___override(v_u_674_, v_v_675_);
return v___x_676_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_isZero(lean_object* v_x_677_){
_start:
{
if (lean_obj_tag(v_x_677_) == 0)
{
uint8_t v___x_678_; 
v___x_678_ = 1;
return v___x_678_;
}
else
{
uint8_t v___x_679_; 
v___x_679_ = 0;
return v___x_679_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_isZero___boxed(lean_object* v_x_680_){
_start:
{
uint8_t v_res_681_; lean_object* v_r_682_; 
v_res_681_ = l_Lean_Level_isZero(v_x_680_);
lean_dec(v_x_680_);
v_r_682_ = lean_box(v_res_681_);
return v_r_682_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_isSucc(lean_object* v_x_683_){
_start:
{
if (lean_obj_tag(v_x_683_) == 1)
{
uint8_t v___x_684_; 
v___x_684_ = 1;
return v___x_684_;
}
else
{
uint8_t v___x_685_; 
v___x_685_ = 0;
return v___x_685_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_isSucc___boxed(lean_object* v_x_686_){
_start:
{
uint8_t v_res_687_; lean_object* v_r_688_; 
v_res_687_ = l_Lean_Level_isSucc(v_x_686_);
lean_dec(v_x_686_);
v_r_688_ = lean_box(v_res_687_);
return v_r_688_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_isMax(lean_object* v_x_689_){
_start:
{
if (lean_obj_tag(v_x_689_) == 2)
{
uint8_t v___x_690_; 
v___x_690_ = 1;
return v___x_690_;
}
else
{
uint8_t v___x_691_; 
v___x_691_ = 0;
return v___x_691_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_isMax___boxed(lean_object* v_x_692_){
_start:
{
uint8_t v_res_693_; lean_object* v_r_694_; 
v_res_693_ = l_Lean_Level_isMax(v_x_692_);
lean_dec(v_x_692_);
v_r_694_ = lean_box(v_res_693_);
return v_r_694_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_isIMax(lean_object* v_x_695_){
_start:
{
if (lean_obj_tag(v_x_695_) == 3)
{
uint8_t v___x_696_; 
v___x_696_ = 1;
return v___x_696_;
}
else
{
uint8_t v___x_697_; 
v___x_697_ = 0;
return v___x_697_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_isIMax___boxed(lean_object* v_x_698_){
_start:
{
uint8_t v_res_699_; lean_object* v_r_700_; 
v_res_699_ = l_Lean_Level_isIMax(v_x_698_);
lean_dec(v_x_698_);
v_r_700_ = lean_box(v_res_699_);
return v_r_700_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_isMaxIMax(lean_object* v_x_701_){
_start:
{
switch(lean_obj_tag(v_x_701_))
{
case 2:
{
uint8_t v___x_702_; 
v___x_702_ = 1;
return v___x_702_;
}
case 3:
{
uint8_t v___x_703_; 
v___x_703_ = 1;
return v___x_703_;
}
default: 
{
uint8_t v___x_704_; 
v___x_704_ = 0;
return v___x_704_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_isMaxIMax___boxed(lean_object* v_x_705_){
_start:
{
uint8_t v_res_706_; lean_object* v_r_707_; 
v_res_706_ = l_Lean_Level_isMaxIMax(v_x_705_);
lean_dec(v_x_705_);
v_r_707_ = lean_box(v_res_706_);
return v_r_707_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_isParam(lean_object* v_x_708_){
_start:
{
if (lean_obj_tag(v_x_708_) == 4)
{
uint8_t v___x_709_; 
v___x_709_ = 1;
return v___x_709_;
}
else
{
uint8_t v___x_710_; 
v___x_710_ = 0;
return v___x_710_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_isParam___boxed(lean_object* v_x_711_){
_start:
{
uint8_t v_res_712_; lean_object* v_r_713_; 
v_res_712_ = l_Lean_Level_isParam(v_x_711_);
lean_dec(v_x_711_);
v_r_713_ = lean_box(v_res_712_);
return v_r_713_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_isMVar(lean_object* v_x_714_){
_start:
{
if (lean_obj_tag(v_x_714_) == 5)
{
uint8_t v___x_715_; 
v___x_715_ = 1;
return v___x_715_;
}
else
{
uint8_t v___x_716_; 
v___x_716_ = 0;
return v___x_716_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_isMVar___boxed(lean_object* v_x_717_){
_start:
{
uint8_t v_res_718_; lean_object* v_r_719_; 
v_res_718_ = l_Lean_Level_isMVar(v_x_717_);
lean_dec(v_x_717_);
v_r_719_ = lean_box(v_res_718_);
return v_r_719_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Level_mvarId_x21_spec__0(lean_object* v_msg_720_){
_start:
{
lean_object* v___x_721_; lean_object* v___x_722_; 
v___x_721_ = lean_box(0);
v___x_722_ = lean_panic_fn(v___x_721_, v_msg_720_);
return v___x_722_;
}
}
static lean_object* _init_l_Lean_Level_mvarId_x21___closed__3(void){
_start:
{
lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; 
v___x_726_ = ((lean_object*)(l_Lean_Level_mvarId_x21___closed__2));
v___x_727_ = lean_unsigned_to_nat(19u);
v___x_728_ = lean_unsigned_to_nat(195u);
v___x_729_ = ((lean_object*)(l_Lean_Level_mvarId_x21___closed__1));
v___x_730_ = ((lean_object*)(l_Lean_Level_mvarId_x21___closed__0));
v___x_731_ = l_mkPanicMessageWithDecl(v___x_730_, v___x_729_, v___x_728_, v___x_727_, v___x_726_);
return v___x_731_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_mvarId_x21(lean_object* v_x_732_){
_start:
{
if (lean_obj_tag(v_x_732_) == 5)
{
lean_object* v_a_733_; 
v_a_733_ = lean_ctor_get(v_x_732_, 0);
lean_inc(v_a_733_);
return v_a_733_;
}
else
{
lean_object* v___x_734_; lean_object* v___x_735_; 
v___x_734_ = lean_obj_once(&l_Lean_Level_mvarId_x21___closed__3, &l_Lean_Level_mvarId_x21___closed__3_once, _init_l_Lean_Level_mvarId_x21___closed__3);
v___x_735_ = l_panic___at___00Lean_Level_mvarId_x21_spec__0(v___x_734_);
return v___x_735_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_mvarId_x21___boxed(lean_object* v_x_736_){
_start:
{
lean_object* v_res_737_; 
v_res_737_ = l_Lean_Level_mvarId_x21(v_x_736_);
lean_dec(v_x_736_);
return v_res_737_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_isNeverZero(lean_object* v_x_738_){
_start:
{
switch(lean_obj_tag(v_x_738_))
{
case 0:
{
uint8_t v___x_739_; 
v___x_739_ = 0;
return v___x_739_;
}
case 1:
{
uint8_t v___x_740_; 
v___x_740_ = 1;
return v___x_740_;
}
case 2:
{
lean_object* v_a_741_; lean_object* v_a_742_; uint8_t v___x_743_; 
v_a_741_ = lean_ctor_get(v_x_738_, 0);
v_a_742_ = lean_ctor_get(v_x_738_, 1);
v___x_743_ = l_Lean_Level_isNeverZero(v_a_741_);
if (v___x_743_ == 0)
{
v_x_738_ = v_a_742_;
goto _start;
}
else
{
return v___x_743_;
}
}
case 3:
{
lean_object* v_a_745_; 
v_a_745_ = lean_ctor_get(v_x_738_, 1);
v_x_738_ = v_a_745_;
goto _start;
}
default: 
{
uint8_t v___x_747_; 
v___x_747_ = 0;
return v___x_747_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_isNeverZero___boxed(lean_object* v_x_748_){
_start:
{
uint8_t v_res_749_; lean_object* v_r_750_; 
v_res_749_ = l_Lean_Level_isNeverZero(v_x_748_);
lean_dec(v_x_748_);
v_r_750_ = lean_box(v_res_749_);
return v_r_750_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_isAlwaysZero(lean_object* v_x_751_){
_start:
{
switch(lean_obj_tag(v_x_751_))
{
case 0:
{
uint8_t v___x_752_; 
v___x_752_ = 1;
return v___x_752_;
}
case 2:
{
lean_object* v_a_753_; lean_object* v_a_754_; uint8_t v___x_755_; 
v_a_753_ = lean_ctor_get(v_x_751_, 0);
v_a_754_ = lean_ctor_get(v_x_751_, 1);
v___x_755_ = l_Lean_Level_isAlwaysZero(v_a_753_);
if (v___x_755_ == 0)
{
return v___x_755_;
}
else
{
v_x_751_ = v_a_754_;
goto _start;
}
}
case 3:
{
lean_object* v_a_757_; 
v_a_757_ = lean_ctor_get(v_x_751_, 1);
v_x_751_ = v_a_757_;
goto _start;
}
default: 
{
uint8_t v___x_759_; 
v___x_759_ = 0;
return v___x_759_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_isAlwaysZero___boxed(lean_object* v_x_760_){
_start:
{
uint8_t v_res_761_; lean_object* v_r_762_; 
v_res_761_ = l_Lean_Level_isAlwaysZero(v_x_760_);
lean_dec(v_x_760_);
v_r_762_ = lean_box(v_res_761_);
return v_r_762_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_ofNat(lean_object* v_x_763_){
_start:
{
lean_object* v_zero_764_; uint8_t v_isZero_765_; 
v_zero_764_ = lean_unsigned_to_nat(0u);
v_isZero_765_ = lean_nat_dec_eq(v_x_763_, v_zero_764_);
if (v_isZero_765_ == 1)
{
lean_object* v___x_766_; 
v___x_766_ = lean_box(0);
return v___x_766_;
}
else
{
lean_object* v_one_767_; lean_object* v_n_768_; lean_object* v___x_769_; lean_object* v___x_770_; 
v_one_767_ = lean_unsigned_to_nat(1u);
v_n_768_ = lean_nat_sub(v_x_763_, v_one_767_);
v___x_769_ = l_Lean_Level_ofNat(v_n_768_);
lean_dec(v_n_768_);
v___x_770_ = l_Lean_Level_succ___override(v___x_769_);
return v___x_770_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_ofNat___boxed(lean_object* v_x_771_){
_start:
{
lean_object* v_res_772_; 
v_res_772_ = l_Lean_Level_ofNat(v_x_771_);
lean_dec(v_x_771_);
return v_res_772_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_instOfNat(lean_object* v_n_773_){
_start:
{
lean_object* v___x_774_; 
v___x_774_ = l_Lean_Level_ofNat(v_n_773_);
return v___x_774_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_instOfNat___boxed(lean_object* v_n_775_){
_start:
{
lean_object* v_res_776_; 
v_res_776_ = l_Lean_Level_instOfNat(v_n_775_);
lean_dec(v_n_775_);
return v_res_776_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_addOffsetAux(lean_object* v_x_777_, lean_object* v_x_778_){
_start:
{
lean_object* v_zero_779_; uint8_t v_isZero_780_; 
v_zero_779_ = lean_unsigned_to_nat(0u);
v_isZero_780_ = lean_nat_dec_eq(v_x_777_, v_zero_779_);
if (v_isZero_780_ == 1)
{
lean_dec(v_x_777_);
return v_x_778_;
}
else
{
lean_object* v_one_781_; lean_object* v_n_782_; lean_object* v___x_783_; 
v_one_781_ = lean_unsigned_to_nat(1u);
v_n_782_ = lean_nat_sub(v_x_777_, v_one_781_);
lean_dec(v_x_777_);
v___x_783_ = l_Lean_Level_succ___override(v_x_778_);
v_x_777_ = v_n_782_;
v_x_778_ = v___x_783_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_addOffset(lean_object* v_u_785_, lean_object* v_n_786_){
_start:
{
lean_object* v___x_787_; 
v___x_787_ = l_Lean_Level_addOffsetAux(v_n_786_, v_u_785_);
return v___x_787_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_isExplicit(lean_object* v_x_788_){
_start:
{
switch(lean_obj_tag(v_x_788_))
{
case 0:
{
uint8_t v___x_789_; 
v___x_789_ = 1;
return v___x_789_;
}
case 1:
{
lean_object* v_a_790_; uint8_t v___x_791_; 
v_a_790_ = lean_ctor_get(v_x_788_, 0);
v___x_791_ = l_Lean_Level_hasMVar(v_a_790_);
if (v___x_791_ == 0)
{
uint8_t v___x_792_; 
v___x_792_ = l_Lean_Level_hasParam(v_a_790_);
if (v___x_792_ == 0)
{
v_x_788_ = v_a_790_;
goto _start;
}
else
{
return v___x_791_;
}
}
else
{
uint8_t v___x_794_; 
v___x_794_ = 0;
return v___x_794_;
}
}
default: 
{
uint8_t v___x_795_; 
v___x_795_ = 0;
return v___x_795_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_isExplicit___boxed(lean_object* v_x_796_){
_start:
{
uint8_t v_res_797_; lean_object* v_r_798_; 
v_res_797_ = l_Lean_Level_isExplicit(v_x_796_);
lean_dec(v_x_796_);
v_r_798_ = lean_box(v_res_797_);
return v_r_798_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_getOffsetAux(lean_object* v_x_799_, lean_object* v_x_800_){
_start:
{
if (lean_obj_tag(v_x_799_) == 1)
{
lean_object* v_a_801_; lean_object* v___x_802_; lean_object* v___x_803_; 
v_a_801_ = lean_ctor_get(v_x_799_, 0);
v___x_802_ = lean_unsigned_to_nat(1u);
v___x_803_ = lean_nat_add(v_x_800_, v___x_802_);
lean_dec(v_x_800_);
v_x_799_ = v_a_801_;
v_x_800_ = v___x_803_;
goto _start;
}
else
{
return v_x_800_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_getOffsetAux___boxed(lean_object* v_x_805_, lean_object* v_x_806_){
_start:
{
lean_object* v_res_807_; 
v_res_807_ = l_Lean_Level_getOffsetAux(v_x_805_, v_x_806_);
lean_dec(v_x_805_);
return v_res_807_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_getOffset(lean_object* v_lvl_808_){
_start:
{
lean_object* v___x_809_; lean_object* v___x_810_; 
v___x_809_ = lean_unsigned_to_nat(0u);
v___x_810_ = l_Lean_Level_getOffsetAux(v_lvl_808_, v___x_809_);
return v___x_810_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_getOffset___boxed(lean_object* v_lvl_811_){
_start:
{
lean_object* v_res_812_; 
v_res_812_ = l_Lean_Level_getOffset(v_lvl_811_);
lean_dec(v_lvl_811_);
return v_res_812_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_getLevelOffset(lean_object* v_x_813_){
_start:
{
if (lean_obj_tag(v_x_813_) == 1)
{
lean_object* v_a_814_; 
v_a_814_ = lean_ctor_get(v_x_813_, 0);
v_x_813_ = v_a_814_;
goto _start;
}
else
{
lean_inc(v_x_813_);
return v_x_813_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_getLevelOffset___boxed(lean_object* v_x_816_){
_start:
{
lean_object* v_res_817_; 
v_res_817_ = l_Lean_Level_getLevelOffset(v_x_816_);
lean_dec(v_x_816_);
return v_res_817_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_toNat(lean_object* v_lvl_818_){
_start:
{
lean_object* v___x_819_; 
v___x_819_ = l_Lean_Level_getLevelOffset(v_lvl_818_);
if (lean_obj_tag(v___x_819_) == 0)
{
lean_object* v___x_820_; lean_object* v___x_821_; 
v___x_820_ = l_Lean_Level_getOffset(v_lvl_818_);
v___x_821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_821_, 0, v___x_820_);
return v___x_821_;
}
else
{
lean_object* v___x_822_; 
lean_dec(v___x_819_);
v___x_822_ = lean_box(0);
return v___x_822_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_toNat___boxed(lean_object* v_lvl_823_){
_start:
{
lean_object* v_res_824_; 
v_res_824_ = l_Lean_Level_toNat(v_lvl_823_);
lean_dec(v_lvl_823_);
return v_res_824_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_beq___boxed(lean_object* v_a_827_, lean_object* v_b_828_){
_start:
{
uint8_t v_res_829_; lean_object* v_r_830_; 
v_res_829_ = lean_level_eq(v_a_827_, v_b_828_);
lean_dec(v_b_828_);
lean_dec(v_a_827_);
v_r_830_ = lean_box(v_res_829_);
return v_r_830_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_occurs(lean_object* v_x_833_, lean_object* v_x_834_){
_start:
{
switch(lean_obj_tag(v_x_834_))
{
case 1:
{
lean_object* v_a_835_; uint8_t v___x_836_; 
v_a_835_ = lean_ctor_get(v_x_834_, 0);
v___x_836_ = lean_level_eq(v_x_833_, v_x_834_);
if (v___x_836_ == 0)
{
v_x_834_ = v_a_835_;
goto _start;
}
else
{
return v___x_836_;
}
}
case 2:
{
lean_object* v_a_838_; lean_object* v_a_839_; uint8_t v___y_841_; uint8_t v___x_843_; 
v_a_838_ = lean_ctor_get(v_x_834_, 0);
v_a_839_ = lean_ctor_get(v_x_834_, 1);
v___x_843_ = lean_level_eq(v_x_833_, v_x_834_);
if (v___x_843_ == 0)
{
uint8_t v___x_844_; 
v___x_844_ = l_Lean_Level_occurs(v_x_833_, v_a_838_);
v___y_841_ = v___x_844_;
goto v___jp_840_;
}
else
{
v___y_841_ = v___x_843_;
goto v___jp_840_;
}
v___jp_840_:
{
if (v___y_841_ == 0)
{
v_x_834_ = v_a_839_;
goto _start;
}
else
{
return v___y_841_;
}
}
}
case 3:
{
lean_object* v_a_845_; lean_object* v_a_846_; uint8_t v___y_848_; uint8_t v___x_850_; 
v_a_845_ = lean_ctor_get(v_x_834_, 0);
v_a_846_ = lean_ctor_get(v_x_834_, 1);
v___x_850_ = lean_level_eq(v_x_833_, v_x_834_);
if (v___x_850_ == 0)
{
uint8_t v___x_851_; 
v___x_851_ = l_Lean_Level_occurs(v_x_833_, v_a_845_);
v___y_848_ = v___x_851_;
goto v___jp_847_;
}
else
{
v___y_848_ = v___x_850_;
goto v___jp_847_;
}
v___jp_847_:
{
if (v___y_848_ == 0)
{
v_x_834_ = v_a_846_;
goto _start;
}
else
{
return v___y_848_;
}
}
}
default: 
{
uint8_t v___x_852_; 
v___x_852_ = lean_level_eq(v_x_833_, v_x_834_);
return v___x_852_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_occurs___boxed(lean_object* v_x_853_, lean_object* v_x_854_){
_start:
{
uint8_t v_res_855_; lean_object* v_r_856_; 
v_res_855_ = l_Lean_Level_occurs(v_x_853_, v_x_854_);
lean_dec(v_x_854_);
lean_dec(v_x_853_);
v_r_856_ = lean_box(v_res_855_);
return v_r_856_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_ctorToNat(lean_object* v_x_857_){
_start:
{
switch(lean_obj_tag(v_x_857_))
{
case 0:
{
lean_object* v___x_858_; 
v___x_858_ = lean_unsigned_to_nat(0u);
return v___x_858_;
}
case 1:
{
lean_object* v___x_859_; 
v___x_859_ = lean_unsigned_to_nat(3u);
return v___x_859_;
}
case 2:
{
lean_object* v___x_860_; 
v___x_860_ = lean_unsigned_to_nat(4u);
return v___x_860_;
}
case 3:
{
lean_object* v___x_861_; 
v___x_861_ = lean_unsigned_to_nat(5u);
return v___x_861_;
}
case 4:
{
lean_object* v___x_862_; 
v___x_862_ = lean_unsigned_to_nat(1u);
return v___x_862_;
}
default: 
{
lean_object* v___x_863_; 
v___x_863_ = lean_unsigned_to_nat(2u);
return v___x_863_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_ctorToNat___boxed(lean_object* v_x_864_){
_start:
{
lean_object* v_res_865_; 
v_res_865_ = l_Lean_Level_ctorToNat(v_x_864_);
lean_dec(v_x_864_);
return v_res_865_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_normLtAux(lean_object* v_x_866_, lean_object* v_x_867_, lean_object* v_x_868_, lean_object* v_x_869_){
_start:
{
lean_object* v_l_u2081_871_; lean_object* v_k_u2081_872_; lean_object* v_l_u2082_873_; lean_object* v_k_u2082_874_; lean_object* v_l_u2081_879_; lean_object* v_k_u2081_880_; lean_object* v_l_u2082_881_; lean_object* v_k_u2082_882_; 
switch(lean_obj_tag(v_x_866_))
{
case 1:
{
lean_object* v_a_888_; lean_object* v___x_889_; lean_object* v___x_890_; 
v_a_888_ = lean_ctor_get(v_x_866_, 0);
v___x_889_ = lean_unsigned_to_nat(1u);
v___x_890_ = lean_nat_add(v_x_867_, v___x_889_);
lean_dec(v_x_867_);
v_x_866_ = v_a_888_;
v_x_867_ = v___x_890_;
goto _start;
}
case 2:
{
switch(lean_obj_tag(v_x_868_))
{
case 1:
{
lean_object* v_a_892_; 
v_a_892_ = lean_ctor_get(v_x_868_, 0);
v_l_u2081_871_ = v_x_866_;
v_k_u2081_872_ = v_x_867_;
v_l_u2082_873_ = v_a_892_;
v_k_u2082_874_ = v_x_869_;
goto v___jp_870_;
}
case 2:
{
lean_object* v_a_893_; lean_object* v_a_894_; lean_object* v_a_895_; lean_object* v_a_896_; uint8_t v___x_900_; 
v_a_893_ = lean_ctor_get(v_x_866_, 0);
v_a_894_ = lean_ctor_get(v_x_866_, 1);
v_a_895_ = lean_ctor_get(v_x_868_, 0);
v_a_896_ = lean_ctor_get(v_x_868_, 1);
v___x_900_ = lean_level_eq(v_x_866_, v_x_868_);
if (v___x_900_ == 0)
{
uint8_t v___x_901_; 
lean_dec(v_x_869_);
lean_dec(v_x_867_);
v___x_901_ = lean_level_eq(v_a_893_, v_a_895_);
if (v___x_901_ == 0)
{
goto v___jp_897_;
}
else
{
if (v___x_900_ == 0)
{
lean_object* v___x_902_; 
v___x_902_ = lean_unsigned_to_nat(0u);
v_x_866_ = v_a_894_;
v_x_867_ = v___x_902_;
v_x_868_ = v_a_896_;
v_x_869_ = v___x_902_;
goto _start;
}
else
{
goto v___jp_897_;
}
}
}
else
{
uint8_t v___x_904_; 
v___x_904_ = lean_nat_dec_lt(v_x_867_, v_x_869_);
lean_dec(v_x_869_);
lean_dec(v_x_867_);
return v___x_904_;
}
v___jp_897_:
{
lean_object* v___x_898_; 
v___x_898_ = lean_unsigned_to_nat(0u);
v_x_866_ = v_a_893_;
v_x_867_ = v___x_898_;
v_x_868_ = v_a_895_;
v_x_869_ = v___x_898_;
goto _start;
}
}
default: 
{
v_l_u2081_879_ = v_x_866_;
v_k_u2081_880_ = v_x_867_;
v_l_u2082_881_ = v_x_868_;
v_k_u2082_882_ = v_x_869_;
goto v___jp_878_;
}
}
}
case 3:
{
switch(lean_obj_tag(v_x_868_))
{
case 1:
{
lean_object* v_a_905_; 
v_a_905_ = lean_ctor_get(v_x_868_, 0);
v_l_u2081_871_ = v_x_866_;
v_k_u2081_872_ = v_x_867_;
v_l_u2082_873_ = v_a_905_;
v_k_u2082_874_ = v_x_869_;
goto v___jp_870_;
}
case 3:
{
lean_object* v_a_906_; lean_object* v_a_907_; lean_object* v_a_908_; lean_object* v_a_909_; uint8_t v___x_913_; 
v_a_906_ = lean_ctor_get(v_x_866_, 0);
v_a_907_ = lean_ctor_get(v_x_866_, 1);
v_a_908_ = lean_ctor_get(v_x_868_, 0);
v_a_909_ = lean_ctor_get(v_x_868_, 1);
v___x_913_ = lean_level_eq(v_x_866_, v_x_868_);
if (v___x_913_ == 0)
{
uint8_t v___x_914_; 
lean_dec(v_x_869_);
lean_dec(v_x_867_);
v___x_914_ = lean_level_eq(v_a_906_, v_a_908_);
if (v___x_914_ == 0)
{
goto v___jp_910_;
}
else
{
if (v___x_913_ == 0)
{
lean_object* v___x_915_; 
v___x_915_ = lean_unsigned_to_nat(0u);
v_x_866_ = v_a_907_;
v_x_867_ = v___x_915_;
v_x_868_ = v_a_909_;
v_x_869_ = v___x_915_;
goto _start;
}
else
{
goto v___jp_910_;
}
}
}
else
{
uint8_t v___x_917_; 
v___x_917_ = lean_nat_dec_lt(v_x_867_, v_x_869_);
lean_dec(v_x_869_);
lean_dec(v_x_867_);
return v___x_917_;
}
v___jp_910_:
{
lean_object* v___x_911_; 
v___x_911_ = lean_unsigned_to_nat(0u);
v_x_866_ = v_a_906_;
v_x_867_ = v___x_911_;
v_x_868_ = v_a_908_;
v_x_869_ = v___x_911_;
goto _start;
}
}
default: 
{
v_l_u2081_879_ = v_x_866_;
v_k_u2081_880_ = v_x_867_;
v_l_u2082_881_ = v_x_868_;
v_k_u2082_882_ = v_x_869_;
goto v___jp_878_;
}
}
}
case 4:
{
switch(lean_obj_tag(v_x_868_))
{
case 1:
{
lean_object* v_a_918_; 
v_a_918_ = lean_ctor_get(v_x_868_, 0);
v_l_u2081_871_ = v_x_866_;
v_k_u2081_872_ = v_x_867_;
v_l_u2082_873_ = v_a_918_;
v_k_u2082_874_ = v_x_869_;
goto v___jp_870_;
}
case 4:
{
lean_object* v_a_919_; lean_object* v_a_920_; uint8_t v___x_921_; 
v_a_919_ = lean_ctor_get(v_x_866_, 0);
v_a_920_ = lean_ctor_get(v_x_868_, 0);
v___x_921_ = lean_name_eq(v_a_919_, v_a_920_);
if (v___x_921_ == 0)
{
uint8_t v___x_922_; 
lean_dec(v_x_869_);
lean_dec(v_x_867_);
v___x_922_ = l_Lean_Name_lt(v_a_919_, v_a_920_);
return v___x_922_;
}
else
{
uint8_t v___x_923_; 
v___x_923_ = lean_nat_dec_lt(v_x_867_, v_x_869_);
lean_dec(v_x_869_);
lean_dec(v_x_867_);
return v___x_923_;
}
}
default: 
{
v_l_u2081_879_ = v_x_866_;
v_k_u2081_880_ = v_x_867_;
v_l_u2082_881_ = v_x_868_;
v_k_u2082_882_ = v_x_869_;
goto v___jp_878_;
}
}
}
case 5:
{
switch(lean_obj_tag(v_x_868_))
{
case 1:
{
lean_object* v_a_924_; 
v_a_924_ = lean_ctor_get(v_x_868_, 0);
v_l_u2081_871_ = v_x_866_;
v_k_u2081_872_ = v_x_867_;
v_l_u2082_873_ = v_a_924_;
v_k_u2082_874_ = v_x_869_;
goto v___jp_870_;
}
case 5:
{
lean_object* v_a_925_; lean_object* v_a_926_; uint8_t v___x_927_; 
v_a_925_ = lean_ctor_get(v_x_866_, 0);
v_a_926_ = lean_ctor_get(v_x_868_, 0);
v___x_927_ = lean_name_eq(v_a_925_, v_a_926_);
if (v___x_927_ == 0)
{
uint8_t v___x_928_; 
lean_dec(v_x_869_);
lean_dec(v_x_867_);
v___x_928_ = l_Lean_Name_lt(v_a_925_, v_a_926_);
return v___x_928_;
}
else
{
uint8_t v___x_929_; 
v___x_929_ = lean_nat_dec_lt(v_x_867_, v_x_869_);
lean_dec(v_x_869_);
lean_dec(v_x_867_);
return v___x_929_;
}
}
default: 
{
v_l_u2081_879_ = v_x_866_;
v_k_u2081_880_ = v_x_867_;
v_l_u2082_881_ = v_x_868_;
v_k_u2082_882_ = v_x_869_;
goto v___jp_878_;
}
}
}
default: 
{
if (lean_obj_tag(v_x_868_) == 1)
{
lean_object* v_a_930_; 
v_a_930_ = lean_ctor_get(v_x_868_, 0);
v_l_u2081_871_ = v_x_866_;
v_k_u2081_872_ = v_x_867_;
v_l_u2082_873_ = v_a_930_;
v_k_u2082_874_ = v_x_869_;
goto v___jp_870_;
}
else
{
v_l_u2081_879_ = v_x_866_;
v_k_u2081_880_ = v_x_867_;
v_l_u2082_881_ = v_x_868_;
v_k_u2082_882_ = v_x_869_;
goto v___jp_878_;
}
}
}
v___jp_870_:
{
lean_object* v___x_875_; lean_object* v___x_876_; 
v___x_875_ = lean_unsigned_to_nat(1u);
v___x_876_ = lean_nat_add(v_k_u2082_874_, v___x_875_);
lean_dec(v_k_u2082_874_);
v_x_866_ = v_l_u2081_871_;
v_x_867_ = v_k_u2081_872_;
v_x_868_ = v_l_u2082_873_;
v_x_869_ = v___x_876_;
goto _start;
}
v___jp_878_:
{
uint8_t v___x_883_; 
v___x_883_ = lean_level_eq(v_l_u2081_879_, v_l_u2082_881_);
if (v___x_883_ == 0)
{
lean_object* v___x_884_; lean_object* v___x_885_; uint8_t v___x_886_; 
lean_dec(v_k_u2082_882_);
lean_dec(v_k_u2081_880_);
v___x_884_ = l_Lean_Level_ctorToNat(v_l_u2081_879_);
v___x_885_ = l_Lean_Level_ctorToNat(v_l_u2082_881_);
v___x_886_ = lean_nat_dec_lt(v___x_884_, v___x_885_);
lean_dec(v___x_885_);
lean_dec(v___x_884_);
return v___x_886_;
}
else
{
uint8_t v___x_887_; 
v___x_887_ = lean_nat_dec_lt(v_k_u2081_880_, v_k_u2082_882_);
lean_dec(v_k_u2082_882_);
lean_dec(v_k_u2081_880_);
return v___x_887_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_normLtAux___boxed(lean_object* v_x_931_, lean_object* v_x_932_, lean_object* v_x_933_, lean_object* v_x_934_){
_start:
{
uint8_t v_res_935_; lean_object* v_r_936_; 
v_res_935_ = l_Lean_Level_normLtAux(v_x_931_, v_x_932_, v_x_933_, v_x_934_);
lean_dec(v_x_933_);
lean_dec(v_x_931_);
v_r_936_ = lean_box(v_res_935_);
return v_r_936_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_normLtAux_match__1_splitter___redArg(lean_object* v_x_937_, lean_object* v_x_938_, lean_object* v_x_939_, lean_object* v_x_940_, lean_object* v_h__1_941_, lean_object* v_h__2_942_, lean_object* v_h__3_943_, lean_object* v_h__4_944_, lean_object* v_h__5_945_, lean_object* v_h__6_946_, lean_object* v_h__7_947_){
_start:
{
switch(lean_obj_tag(v_x_937_))
{
case 1:
{
lean_object* v_a_948_; lean_object* v___x_949_; 
lean_dec(v_h__7_947_);
lean_dec(v_h__6_946_);
lean_dec(v_h__5_945_);
lean_dec(v_h__4_944_);
lean_dec(v_h__3_943_);
lean_dec(v_h__2_942_);
v_a_948_ = lean_ctor_get(v_x_937_, 0);
lean_inc(v_a_948_);
lean_dec_ref(v_x_937_);
v___x_949_ = lean_apply_4(v_h__1_941_, v_a_948_, v_x_938_, v_x_939_, v_x_940_);
return v___x_949_;
}
case 2:
{
lean_dec(v_h__6_946_);
lean_dec(v_h__5_945_);
lean_dec(v_h__4_944_);
lean_dec(v_h__1_941_);
switch(lean_obj_tag(v_x_939_))
{
case 1:
{
lean_object* v_a_950_; lean_object* v___x_951_; 
lean_dec(v_h__7_947_);
lean_dec(v_h__3_943_);
v_a_950_ = lean_ctor_get(v_x_939_, 0);
lean_inc(v_a_950_);
lean_dec_ref(v_x_939_);
v___x_951_ = lean_apply_5(v_h__2_942_, v_x_937_, v_x_938_, v_a_950_, v_x_940_, lean_box(0));
return v___x_951_;
}
case 2:
{
lean_object* v_a_952_; lean_object* v_a_953_; lean_object* v_a_954_; lean_object* v_a_955_; lean_object* v___x_956_; 
lean_dec(v_h__7_947_);
lean_dec(v_h__2_942_);
v_a_952_ = lean_ctor_get(v_x_937_, 0);
lean_inc(v_a_952_);
v_a_953_ = lean_ctor_get(v_x_937_, 1);
lean_inc(v_a_953_);
lean_dec_ref(v_x_937_);
v_a_954_ = lean_ctor_get(v_x_939_, 0);
lean_inc(v_a_954_);
v_a_955_ = lean_ctor_get(v_x_939_, 1);
lean_inc(v_a_955_);
lean_dec_ref(v_x_939_);
v___x_956_ = lean_apply_6(v_h__3_943_, v_a_952_, v_a_953_, v_x_938_, v_a_954_, v_a_955_, v_x_940_);
return v___x_956_;
}
default: 
{
lean_object* v___x_957_; 
lean_dec(v_h__3_943_);
lean_dec(v_h__2_942_);
v___x_957_ = lean_apply_10(v_h__7_947_, v_x_937_, v_x_938_, v_x_939_, v_x_940_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_957_;
}
}
}
case 3:
{
lean_dec(v_h__6_946_);
lean_dec(v_h__5_945_);
lean_dec(v_h__3_943_);
lean_dec(v_h__1_941_);
switch(lean_obj_tag(v_x_939_))
{
case 1:
{
lean_object* v_a_958_; lean_object* v___x_959_; 
lean_dec(v_h__7_947_);
lean_dec(v_h__4_944_);
v_a_958_ = lean_ctor_get(v_x_939_, 0);
lean_inc(v_a_958_);
lean_dec_ref(v_x_939_);
v___x_959_ = lean_apply_5(v_h__2_942_, v_x_937_, v_x_938_, v_a_958_, v_x_940_, lean_box(0));
return v___x_959_;
}
case 3:
{
lean_object* v_a_960_; lean_object* v_a_961_; lean_object* v_a_962_; lean_object* v_a_963_; lean_object* v___x_964_; 
lean_dec(v_h__7_947_);
lean_dec(v_h__2_942_);
v_a_960_ = lean_ctor_get(v_x_937_, 0);
lean_inc(v_a_960_);
v_a_961_ = lean_ctor_get(v_x_937_, 1);
lean_inc(v_a_961_);
lean_dec_ref(v_x_937_);
v_a_962_ = lean_ctor_get(v_x_939_, 0);
lean_inc(v_a_962_);
v_a_963_ = lean_ctor_get(v_x_939_, 1);
lean_inc(v_a_963_);
lean_dec_ref(v_x_939_);
v___x_964_ = lean_apply_6(v_h__4_944_, v_a_960_, v_a_961_, v_x_938_, v_a_962_, v_a_963_, v_x_940_);
return v___x_964_;
}
default: 
{
lean_object* v___x_965_; 
lean_dec(v_h__4_944_);
lean_dec(v_h__2_942_);
v___x_965_ = lean_apply_10(v_h__7_947_, v_x_937_, v_x_938_, v_x_939_, v_x_940_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_965_;
}
}
}
case 4:
{
lean_dec(v_h__6_946_);
lean_dec(v_h__4_944_);
lean_dec(v_h__3_943_);
lean_dec(v_h__1_941_);
switch(lean_obj_tag(v_x_939_))
{
case 1:
{
lean_object* v_a_966_; lean_object* v___x_967_; 
lean_dec(v_h__7_947_);
lean_dec(v_h__5_945_);
v_a_966_ = lean_ctor_get(v_x_939_, 0);
lean_inc(v_a_966_);
lean_dec_ref(v_x_939_);
v___x_967_ = lean_apply_5(v_h__2_942_, v_x_937_, v_x_938_, v_a_966_, v_x_940_, lean_box(0));
return v___x_967_;
}
case 4:
{
lean_object* v_a_968_; lean_object* v_a_969_; lean_object* v___x_970_; 
lean_dec(v_h__7_947_);
lean_dec(v_h__2_942_);
v_a_968_ = lean_ctor_get(v_x_937_, 0);
lean_inc(v_a_968_);
lean_dec_ref(v_x_937_);
v_a_969_ = lean_ctor_get(v_x_939_, 0);
lean_inc(v_a_969_);
lean_dec_ref(v_x_939_);
v___x_970_ = lean_apply_4(v_h__5_945_, v_a_968_, v_x_938_, v_a_969_, v_x_940_);
return v___x_970_;
}
default: 
{
lean_object* v___x_971_; 
lean_dec(v_h__5_945_);
lean_dec(v_h__2_942_);
v___x_971_ = lean_apply_10(v_h__7_947_, v_x_937_, v_x_938_, v_x_939_, v_x_940_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_971_;
}
}
}
case 5:
{
lean_dec(v_h__5_945_);
lean_dec(v_h__4_944_);
lean_dec(v_h__3_943_);
lean_dec(v_h__1_941_);
switch(lean_obj_tag(v_x_939_))
{
case 1:
{
lean_object* v_a_972_; lean_object* v___x_973_; 
lean_dec(v_h__7_947_);
lean_dec(v_h__6_946_);
v_a_972_ = lean_ctor_get(v_x_939_, 0);
lean_inc(v_a_972_);
lean_dec_ref(v_x_939_);
v___x_973_ = lean_apply_5(v_h__2_942_, v_x_937_, v_x_938_, v_a_972_, v_x_940_, lean_box(0));
return v___x_973_;
}
case 5:
{
lean_object* v_a_974_; lean_object* v_a_975_; lean_object* v___x_976_; 
lean_dec(v_h__7_947_);
lean_dec(v_h__2_942_);
v_a_974_ = lean_ctor_get(v_x_937_, 0);
lean_inc(v_a_974_);
lean_dec_ref(v_x_937_);
v_a_975_ = lean_ctor_get(v_x_939_, 0);
lean_inc(v_a_975_);
lean_dec_ref(v_x_939_);
v___x_976_ = lean_apply_4(v_h__6_946_, v_a_974_, v_x_938_, v_a_975_, v_x_940_);
return v___x_976_;
}
default: 
{
lean_object* v___x_977_; 
lean_dec(v_h__6_946_);
lean_dec(v_h__2_942_);
v___x_977_ = lean_apply_10(v_h__7_947_, v_x_937_, v_x_938_, v_x_939_, v_x_940_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_977_;
}
}
}
default: 
{
lean_dec(v_h__6_946_);
lean_dec(v_h__5_945_);
lean_dec(v_h__4_944_);
lean_dec(v_h__3_943_);
lean_dec(v_h__1_941_);
if (lean_obj_tag(v_x_939_) == 1)
{
lean_object* v_a_978_; lean_object* v___x_979_; 
lean_dec(v_h__7_947_);
v_a_978_ = lean_ctor_get(v_x_939_, 0);
lean_inc(v_a_978_);
lean_dec_ref(v_x_939_);
v___x_979_ = lean_apply_5(v_h__2_942_, v_x_937_, v_x_938_, v_a_978_, v_x_940_, lean_box(0));
return v___x_979_;
}
else
{
lean_object* v___x_980_; 
lean_dec(v_h__2_942_);
v___x_980_ = lean_apply_10(v_h__7_947_, v_x_937_, v_x_938_, v_x_939_, v_x_940_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_980_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_normLtAux_match__1_splitter(lean_object* v_motive_981_, lean_object* v_x_982_, lean_object* v_x_983_, lean_object* v_x_984_, lean_object* v_x_985_, lean_object* v_h__1_986_, lean_object* v_h__2_987_, lean_object* v_h__3_988_, lean_object* v_h__4_989_, lean_object* v_h__5_990_, lean_object* v_h__6_991_, lean_object* v_h__7_992_){
_start:
{
switch(lean_obj_tag(v_x_982_))
{
case 1:
{
lean_object* v_a_993_; lean_object* v___x_994_; 
lean_dec(v_h__7_992_);
lean_dec(v_h__6_991_);
lean_dec(v_h__5_990_);
lean_dec(v_h__4_989_);
lean_dec(v_h__3_988_);
lean_dec(v_h__2_987_);
v_a_993_ = lean_ctor_get(v_x_982_, 0);
lean_inc(v_a_993_);
lean_dec_ref(v_x_982_);
v___x_994_ = lean_apply_4(v_h__1_986_, v_a_993_, v_x_983_, v_x_984_, v_x_985_);
return v___x_994_;
}
case 2:
{
lean_dec(v_h__6_991_);
lean_dec(v_h__5_990_);
lean_dec(v_h__4_989_);
lean_dec(v_h__1_986_);
switch(lean_obj_tag(v_x_984_))
{
case 1:
{
lean_object* v_a_995_; lean_object* v___x_996_; 
lean_dec(v_h__7_992_);
lean_dec(v_h__3_988_);
v_a_995_ = lean_ctor_get(v_x_984_, 0);
lean_inc(v_a_995_);
lean_dec_ref(v_x_984_);
v___x_996_ = lean_apply_5(v_h__2_987_, v_x_982_, v_x_983_, v_a_995_, v_x_985_, lean_box(0));
return v___x_996_;
}
case 2:
{
lean_object* v_a_997_; lean_object* v_a_998_; lean_object* v_a_999_; lean_object* v_a_1000_; lean_object* v___x_1001_; 
lean_dec(v_h__7_992_);
lean_dec(v_h__2_987_);
v_a_997_ = lean_ctor_get(v_x_982_, 0);
lean_inc(v_a_997_);
v_a_998_ = lean_ctor_get(v_x_982_, 1);
lean_inc(v_a_998_);
lean_dec_ref(v_x_982_);
v_a_999_ = lean_ctor_get(v_x_984_, 0);
lean_inc(v_a_999_);
v_a_1000_ = lean_ctor_get(v_x_984_, 1);
lean_inc(v_a_1000_);
lean_dec_ref(v_x_984_);
v___x_1001_ = lean_apply_6(v_h__3_988_, v_a_997_, v_a_998_, v_x_983_, v_a_999_, v_a_1000_, v_x_985_);
return v___x_1001_;
}
default: 
{
lean_object* v___x_1002_; 
lean_dec(v_h__3_988_);
lean_dec(v_h__2_987_);
v___x_1002_ = lean_apply_10(v_h__7_992_, v_x_982_, v_x_983_, v_x_984_, v_x_985_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_1002_;
}
}
}
case 3:
{
lean_dec(v_h__6_991_);
lean_dec(v_h__5_990_);
lean_dec(v_h__3_988_);
lean_dec(v_h__1_986_);
switch(lean_obj_tag(v_x_984_))
{
case 1:
{
lean_object* v_a_1003_; lean_object* v___x_1004_; 
lean_dec(v_h__7_992_);
lean_dec(v_h__4_989_);
v_a_1003_ = lean_ctor_get(v_x_984_, 0);
lean_inc(v_a_1003_);
lean_dec_ref(v_x_984_);
v___x_1004_ = lean_apply_5(v_h__2_987_, v_x_982_, v_x_983_, v_a_1003_, v_x_985_, lean_box(0));
return v___x_1004_;
}
case 3:
{
lean_object* v_a_1005_; lean_object* v_a_1006_; lean_object* v_a_1007_; lean_object* v_a_1008_; lean_object* v___x_1009_; 
lean_dec(v_h__7_992_);
lean_dec(v_h__2_987_);
v_a_1005_ = lean_ctor_get(v_x_982_, 0);
lean_inc(v_a_1005_);
v_a_1006_ = lean_ctor_get(v_x_982_, 1);
lean_inc(v_a_1006_);
lean_dec_ref(v_x_982_);
v_a_1007_ = lean_ctor_get(v_x_984_, 0);
lean_inc(v_a_1007_);
v_a_1008_ = lean_ctor_get(v_x_984_, 1);
lean_inc(v_a_1008_);
lean_dec_ref(v_x_984_);
v___x_1009_ = lean_apply_6(v_h__4_989_, v_a_1005_, v_a_1006_, v_x_983_, v_a_1007_, v_a_1008_, v_x_985_);
return v___x_1009_;
}
default: 
{
lean_object* v___x_1010_; 
lean_dec(v_h__4_989_);
lean_dec(v_h__2_987_);
v___x_1010_ = lean_apply_10(v_h__7_992_, v_x_982_, v_x_983_, v_x_984_, v_x_985_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_1010_;
}
}
}
case 4:
{
lean_dec(v_h__6_991_);
lean_dec(v_h__4_989_);
lean_dec(v_h__3_988_);
lean_dec(v_h__1_986_);
switch(lean_obj_tag(v_x_984_))
{
case 1:
{
lean_object* v_a_1011_; lean_object* v___x_1012_; 
lean_dec(v_h__7_992_);
lean_dec(v_h__5_990_);
v_a_1011_ = lean_ctor_get(v_x_984_, 0);
lean_inc(v_a_1011_);
lean_dec_ref(v_x_984_);
v___x_1012_ = lean_apply_5(v_h__2_987_, v_x_982_, v_x_983_, v_a_1011_, v_x_985_, lean_box(0));
return v___x_1012_;
}
case 4:
{
lean_object* v_a_1013_; lean_object* v_a_1014_; lean_object* v___x_1015_; 
lean_dec(v_h__7_992_);
lean_dec(v_h__2_987_);
v_a_1013_ = lean_ctor_get(v_x_982_, 0);
lean_inc(v_a_1013_);
lean_dec_ref(v_x_982_);
v_a_1014_ = lean_ctor_get(v_x_984_, 0);
lean_inc(v_a_1014_);
lean_dec_ref(v_x_984_);
v___x_1015_ = lean_apply_4(v_h__5_990_, v_a_1013_, v_x_983_, v_a_1014_, v_x_985_);
return v___x_1015_;
}
default: 
{
lean_object* v___x_1016_; 
lean_dec(v_h__5_990_);
lean_dec(v_h__2_987_);
v___x_1016_ = lean_apply_10(v_h__7_992_, v_x_982_, v_x_983_, v_x_984_, v_x_985_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_1016_;
}
}
}
case 5:
{
lean_dec(v_h__5_990_);
lean_dec(v_h__4_989_);
lean_dec(v_h__3_988_);
lean_dec(v_h__1_986_);
switch(lean_obj_tag(v_x_984_))
{
case 1:
{
lean_object* v_a_1017_; lean_object* v___x_1018_; 
lean_dec(v_h__7_992_);
lean_dec(v_h__6_991_);
v_a_1017_ = lean_ctor_get(v_x_984_, 0);
lean_inc(v_a_1017_);
lean_dec_ref(v_x_984_);
v___x_1018_ = lean_apply_5(v_h__2_987_, v_x_982_, v_x_983_, v_a_1017_, v_x_985_, lean_box(0));
return v___x_1018_;
}
case 5:
{
lean_object* v_a_1019_; lean_object* v_a_1020_; lean_object* v___x_1021_; 
lean_dec(v_h__7_992_);
lean_dec(v_h__2_987_);
v_a_1019_ = lean_ctor_get(v_x_982_, 0);
lean_inc(v_a_1019_);
lean_dec_ref(v_x_982_);
v_a_1020_ = lean_ctor_get(v_x_984_, 0);
lean_inc(v_a_1020_);
lean_dec_ref(v_x_984_);
v___x_1021_ = lean_apply_4(v_h__6_991_, v_a_1019_, v_x_983_, v_a_1020_, v_x_985_);
return v___x_1021_;
}
default: 
{
lean_object* v___x_1022_; 
lean_dec(v_h__6_991_);
lean_dec(v_h__2_987_);
v___x_1022_ = lean_apply_10(v_h__7_992_, v_x_982_, v_x_983_, v_x_984_, v_x_985_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_1022_;
}
}
}
default: 
{
lean_dec(v_h__6_991_);
lean_dec(v_h__5_990_);
lean_dec(v_h__4_989_);
lean_dec(v_h__3_988_);
lean_dec(v_h__1_986_);
if (lean_obj_tag(v_x_984_) == 1)
{
lean_object* v_a_1023_; lean_object* v___x_1024_; 
lean_dec(v_h__7_992_);
v_a_1023_ = lean_ctor_get(v_x_984_, 0);
lean_inc(v_a_1023_);
lean_dec_ref(v_x_984_);
v___x_1024_ = lean_apply_5(v_h__2_987_, v_x_982_, v_x_983_, v_a_1023_, v_x_985_, lean_box(0));
return v___x_1024_;
}
else
{
lean_object* v___x_1025_; 
lean_dec(v_h__2_987_);
v___x_1025_ = lean_apply_10(v_h__7_992_, v_x_982_, v_x_983_, v_x_984_, v_x_985_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_1025_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Level_normLt(lean_object* v_l_u2081_1026_, lean_object* v_l_u2082_1027_){
_start:
{
lean_object* v___x_1028_; uint8_t v___x_1029_; 
v___x_1028_ = lean_unsigned_to_nat(0u);
v___x_1029_ = l_Lean_Level_normLtAux(v_l_u2081_1026_, v___x_1028_, v_l_u2082_1027_, v___x_1028_);
return v___x_1029_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_normLt___boxed(lean_object* v_l_u2081_1030_, lean_object* v_l_u2082_1031_){
_start:
{
uint8_t v_res_1032_; lean_object* v_r_1033_; 
v_res_1032_ = l_Lean_Level_normLt(v_l_u2081_1030_, v_l_u2082_1031_);
lean_dec(v_l_u2082_1031_);
lean_dec(v_l_u2081_1030_);
v_r_1033_ = lean_box(v_res_1032_);
return v_r_1033_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_isAlreadyNormalizedCheap(lean_object* v_x_1034_){
_start:
{
switch(lean_obj_tag(v_x_1034_))
{
case 0:
{
uint8_t v___x_1035_; 
v___x_1035_ = 1;
return v___x_1035_;
}
case 4:
{
uint8_t v___x_1036_; 
v___x_1036_ = 1;
return v___x_1036_;
}
case 5:
{
uint8_t v___x_1037_; 
v___x_1037_ = 1;
return v___x_1037_;
}
case 1:
{
lean_object* v_a_1038_; 
v_a_1038_ = lean_ctor_get(v_x_1034_, 0);
v_x_1034_ = v_a_1038_;
goto _start;
}
default: 
{
uint8_t v___x_1040_; 
v___x_1040_ = 0;
return v___x_1040_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_isAlreadyNormalizedCheap___boxed(lean_object* v_x_1041_){
_start:
{
uint8_t v_res_1042_; lean_object* v_r_1043_; 
v_res_1042_ = l_Lean_Level_isAlreadyNormalizedCheap(v_x_1041_);
lean_dec(v_x_1041_);
v_r_1043_ = lean_box(v_res_1042_);
return v_r_1043_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_mkIMaxAux(lean_object* v_x_1044_, lean_object* v_x_1045_){
_start:
{
lean_object* v_u_u2081_1047_; lean_object* v_u_u2082_1048_; 
if (lean_obj_tag(v_x_1045_) == 0)
{
lean_dec(v_x_1044_);
return v_x_1045_;
}
else
{
switch(lean_obj_tag(v_x_1044_))
{
case 0:
{
return v_x_1045_;
}
case 1:
{
lean_object* v_a_1051_; 
v_a_1051_ = lean_ctor_get(v_x_1044_, 0);
if (lean_obj_tag(v_a_1051_) == 0)
{
lean_dec_ref(v_x_1044_);
return v_x_1045_;
}
else
{
v_u_u2081_1047_ = v_x_1044_;
v_u_u2082_1048_ = v_x_1045_;
goto v___jp_1046_;
}
}
default: 
{
v_u_u2081_1047_ = v_x_1044_;
v_u_u2082_1048_ = v_x_1045_;
goto v___jp_1046_;
}
}
}
v___jp_1046_:
{
uint8_t v___x_1049_; 
v___x_1049_ = lean_level_eq(v_u_u2081_1047_, v_u_u2082_1048_);
if (v___x_1049_ == 0)
{
lean_object* v___x_1050_; 
v___x_1050_ = l_Lean_Level_imax___override(v_u_u2081_1047_, v_u_u2082_1048_);
return v___x_1050_;
}
else
{
lean_dec(v_u_u2082_1048_);
return v_u_u2081_1047_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_getMaxArgsAux(lean_object* v_normalize_1052_, lean_object* v_x_1053_, uint8_t v_x_1054_, lean_object* v_x_1055_){
_start:
{
if (lean_obj_tag(v_x_1053_) == 2)
{
lean_object* v_a_1056_; lean_object* v_a_1057_; lean_object* v___x_1058_; 
v_a_1056_ = lean_ctor_get(v_x_1053_, 0);
lean_inc(v_a_1056_);
v_a_1057_ = lean_ctor_get(v_x_1053_, 1);
lean_inc(v_a_1057_);
lean_dec_ref(v_x_1053_);
lean_inc_ref(v_normalize_1052_);
v___x_1058_ = l___private_Lean_Level_0__Lean_Level_getMaxArgsAux(v_normalize_1052_, v_a_1056_, v_x_1054_, v_x_1055_);
v_x_1053_ = v_a_1057_;
v_x_1055_ = v___x_1058_;
goto _start;
}
else
{
if (v_x_1054_ == 0)
{
lean_object* v___x_1060_; uint8_t v___x_1061_; 
lean_inc_ref(v_normalize_1052_);
v___x_1060_ = lean_apply_1(v_normalize_1052_, v_x_1053_);
v___x_1061_ = 1;
v_x_1053_ = v___x_1060_;
v_x_1054_ = v___x_1061_;
goto _start;
}
else
{
lean_object* v___x_1063_; 
lean_dec_ref(v_normalize_1052_);
v___x_1063_ = lean_array_push(v_x_1055_, v_x_1053_);
return v___x_1063_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_getMaxArgsAux___boxed(lean_object* v_normalize_1064_, lean_object* v_x_1065_, lean_object* v_x_1066_, lean_object* v_x_1067_){
_start:
{
uint8_t v_x_36__boxed_1068_; lean_object* v_res_1069_; 
v_x_36__boxed_1068_ = lean_unbox(v_x_1066_);
v_res_1069_ = l___private_Lean_Level_0__Lean_Level_getMaxArgsAux(v_normalize_1064_, v_x_1065_, v_x_36__boxed_1068_, v_x_1067_);
return v_res_1069_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_accMax(lean_object* v_result_1070_, lean_object* v_prev_1071_, lean_object* v_offset_1072_){
_start:
{
uint8_t v___x_1073_; 
v___x_1073_ = l_Lean_Level_isZero(v_result_1070_);
if (v___x_1073_ == 0)
{
lean_object* v___x_1074_; lean_object* v___x_1075_; 
v___x_1074_ = l_Lean_Level_addOffsetAux(v_offset_1072_, v_prev_1071_);
v___x_1075_ = l_Lean_Level_max___override(v_result_1070_, v___x_1074_);
return v___x_1075_;
}
else
{
lean_object* v___x_1076_; 
lean_dec(v_result_1070_);
v___x_1076_ = l_Lean_Level_addOffsetAux(v_offset_1072_, v_prev_1071_);
return v___x_1076_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_mkMaxAux(lean_object* v_lvls_1077_, lean_object* v_extraK_1078_, lean_object* v_i_1079_, lean_object* v_prev_1080_, lean_object* v_prevK_1081_, lean_object* v_result_1082_){
_start:
{
lean_object* v___x_1083_; uint8_t v___x_1084_; 
v___x_1083_ = lean_array_get_size(v_lvls_1077_);
v___x_1084_ = lean_nat_dec_lt(v_i_1079_, v___x_1083_);
if (v___x_1084_ == 0)
{
lean_object* v___x_1085_; lean_object* v___x_1086_; 
lean_dec(v_i_1079_);
v___x_1085_ = lean_nat_add(v_extraK_1078_, v_prevK_1081_);
lean_dec(v_prevK_1081_);
v___x_1086_ = l___private_Lean_Level_0__Lean_Level_accMax(v_result_1082_, v_prev_1080_, v___x_1085_);
return v___x_1086_;
}
else
{
lean_object* v_lvl_1087_; lean_object* v_curr_1088_; lean_object* v_currK_1089_; uint8_t v___x_1090_; 
v_lvl_1087_ = lean_array_fget_borrowed(v_lvls_1077_, v_i_1079_);
v_curr_1088_ = l_Lean_Level_getLevelOffset(v_lvl_1087_);
v_currK_1089_ = l_Lean_Level_getOffset(v_lvl_1087_);
v___x_1090_ = lean_level_eq(v_curr_1088_, v_prev_1080_);
if (v___x_1090_ == 0)
{
lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; 
v___x_1091_ = lean_unsigned_to_nat(1u);
v___x_1092_ = lean_nat_add(v_i_1079_, v___x_1091_);
lean_dec(v_i_1079_);
v___x_1093_ = lean_nat_add(v_extraK_1078_, v_prevK_1081_);
lean_dec(v_prevK_1081_);
v___x_1094_ = l___private_Lean_Level_0__Lean_Level_accMax(v_result_1082_, v_prev_1080_, v___x_1093_);
v_i_1079_ = v___x_1092_;
v_prev_1080_ = v_curr_1088_;
v_prevK_1081_ = v_currK_1089_;
v_result_1082_ = v___x_1094_;
goto _start;
}
else
{
lean_object* v___x_1096_; lean_object* v___x_1097_; 
lean_dec(v_prevK_1081_);
lean_dec(v_prev_1080_);
v___x_1096_ = lean_unsigned_to_nat(1u);
v___x_1097_ = lean_nat_add(v_i_1079_, v___x_1096_);
lean_dec(v_i_1079_);
v_i_1079_ = v___x_1097_;
v_prev_1080_ = v_curr_1088_;
v_prevK_1081_ = v_currK_1089_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_mkMaxAux___boxed(lean_object* v_lvls_1099_, lean_object* v_extraK_1100_, lean_object* v_i_1101_, lean_object* v_prev_1102_, lean_object* v_prevK_1103_, lean_object* v_result_1104_){
_start:
{
lean_object* v_res_1105_; 
v_res_1105_ = l___private_Lean_Level_0__Lean_Level_mkMaxAux(v_lvls_1099_, v_extraK_1100_, v_i_1101_, v_prev_1102_, v_prevK_1103_, v_result_1104_);
lean_dec(v_extraK_1100_);
lean_dec_ref(v_lvls_1099_);
return v_res_1105_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_skipExplicit(lean_object* v_lvls_1106_, lean_object* v_i_1107_){
_start:
{
lean_object* v___x_1108_; uint8_t v___x_1109_; 
v___x_1108_ = lean_array_get_size(v_lvls_1106_);
v___x_1109_ = lean_nat_dec_lt(v_i_1107_, v___x_1108_);
if (v___x_1109_ == 0)
{
return v_i_1107_;
}
else
{
lean_object* v_lvl_1110_; lean_object* v___x_1111_; uint8_t v___x_1112_; 
v_lvl_1110_ = lean_array_fget_borrowed(v_lvls_1106_, v_i_1107_);
v___x_1111_ = l_Lean_Level_getLevelOffset(v_lvl_1110_);
v___x_1112_ = l_Lean_Level_isZero(v___x_1111_);
lean_dec(v___x_1111_);
if (v___x_1112_ == 0)
{
return v_i_1107_;
}
else
{
lean_object* v___x_1113_; lean_object* v___x_1114_; 
v___x_1113_ = lean_unsigned_to_nat(1u);
v___x_1114_ = lean_nat_add(v_i_1107_, v___x_1113_);
lean_dec(v_i_1107_);
v_i_1107_ = v___x_1114_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_skipExplicit___boxed(lean_object* v_lvls_1116_, lean_object* v_i_1117_){
_start:
{
lean_object* v_res_1118_; 
v_res_1118_ = l___private_Lean_Level_0__Lean_Level_skipExplicit(v_lvls_1116_, v_i_1117_);
lean_dec_ref(v_lvls_1116_);
return v_res_1118_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Level_0__Lean_Level_isExplicitSubsumedAux(lean_object* v_lvls_1119_, lean_object* v_maxExplicit_1120_, lean_object* v_i_1121_){
_start:
{
lean_object* v___x_1122_; uint8_t v___x_1123_; 
v___x_1122_ = lean_array_get_size(v_lvls_1119_);
v___x_1123_ = lean_nat_dec_lt(v_i_1121_, v___x_1122_);
if (v___x_1123_ == 0)
{
lean_dec(v_i_1121_);
return v___x_1123_;
}
else
{
lean_object* v_lvl_1124_; lean_object* v___x_1125_; uint8_t v___x_1126_; 
v_lvl_1124_ = lean_array_fget_borrowed(v_lvls_1119_, v_i_1121_);
v___x_1125_ = l_Lean_Level_getOffset(v_lvl_1124_);
v___x_1126_ = lean_nat_dec_le(v_maxExplicit_1120_, v___x_1125_);
lean_dec(v___x_1125_);
if (v___x_1126_ == 0)
{
lean_object* v___x_1127_; lean_object* v___x_1128_; 
v___x_1127_ = lean_unsigned_to_nat(1u);
v___x_1128_ = lean_nat_add(v_i_1121_, v___x_1127_);
lean_dec(v_i_1121_);
v_i_1121_ = v___x_1128_;
goto _start;
}
else
{
lean_dec(v_i_1121_);
return v___x_1126_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_isExplicitSubsumedAux___boxed(lean_object* v_lvls_1130_, lean_object* v_maxExplicit_1131_, lean_object* v_i_1132_){
_start:
{
uint8_t v_res_1133_; lean_object* v_r_1134_; 
v_res_1133_ = l___private_Lean_Level_0__Lean_Level_isExplicitSubsumedAux(v_lvls_1130_, v_maxExplicit_1131_, v_i_1132_);
lean_dec(v_maxExplicit_1131_);
lean_dec_ref(v_lvls_1130_);
v_r_1134_ = lean_box(v_res_1133_);
return v_r_1134_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Level_0__Lean_Level_isExplicitSubsumed(lean_object* v_lvls_1135_, lean_object* v_firstNonExplicit_1136_){
_start:
{
lean_object* v___x_1137_; uint8_t v___x_1138_; 
v___x_1137_ = lean_unsigned_to_nat(0u);
v___x_1138_ = lean_nat_dec_eq(v_firstNonExplicit_1136_, v___x_1137_);
if (v___x_1138_ == 0)
{
lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v_max_1143_; uint8_t v___x_1144_; 
v___x_1139_ = lean_box(0);
v___x_1140_ = lean_unsigned_to_nat(1u);
v___x_1141_ = lean_nat_sub(v_firstNonExplicit_1136_, v___x_1140_);
v___x_1142_ = lean_array_get_borrowed(v___x_1139_, v_lvls_1135_, v___x_1141_);
lean_dec(v___x_1141_);
v_max_1143_ = l_Lean_Level_getOffset(v___x_1142_);
v___x_1144_ = l___private_Lean_Level_0__Lean_Level_isExplicitSubsumedAux(v_lvls_1135_, v_max_1143_, v_firstNonExplicit_1136_);
lean_dec(v_max_1143_);
return v___x_1144_;
}
else
{
uint8_t v___x_1145_; 
lean_dec(v_firstNonExplicit_1136_);
v___x_1145_ = 0;
return v___x_1145_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_isExplicitSubsumed___boxed(lean_object* v_lvls_1146_, lean_object* v_firstNonExplicit_1147_){
_start:
{
uint8_t v_res_1148_; lean_object* v_r_1149_; 
v_res_1148_ = l___private_Lean_Level_0__Lean_Level_isExplicitSubsumed(v_lvls_1146_, v_firstNonExplicit_1147_);
lean_dec_ref(v_lvls_1146_);
v_r_1149_ = lean_box(v_res_1148_);
return v_r_1149_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Level_normalize_spec__2(lean_object* v_msg_1150_){
_start:
{
lean_object* v___x_1151_; lean_object* v___x_1152_; 
v___x_1151_ = lean_box(0);
v___x_1152_ = lean_panic_fn(v___x_1151_, v_msg_1150_);
return v___x_1152_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1___redArg(lean_object* v_as_1154_, lean_object* v_lo_1155_, lean_object* v_hi_1156_){
_start:
{
uint8_t v___x_1157_; 
v___x_1157_ = lean_nat_dec_lt(v_lo_1155_, v_hi_1156_);
if (v___x_1157_ == 0)
{
lean_dec(v_lo_1155_);
return v_as_1154_;
}
else
{
lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v_fst_1160_; lean_object* v_snd_1161_; uint8_t v___x_1162_; 
v___x_1158_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1___redArg___closed__0));
lean_inc(v_lo_1155_);
v___x_1159_ = l_Array_qpartition___redArg(v_as_1154_, v___x_1158_, v_lo_1155_, v_hi_1156_);
v_fst_1160_ = lean_ctor_get(v___x_1159_, 0);
lean_inc(v_fst_1160_);
v_snd_1161_ = lean_ctor_get(v___x_1159_, 1);
lean_inc(v_snd_1161_);
lean_dec_ref(v___x_1159_);
v___x_1162_ = lean_nat_dec_le(v_hi_1156_, v_fst_1160_);
if (v___x_1162_ == 0)
{
lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; 
v___x_1163_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1___redArg(v_snd_1161_, v_lo_1155_, v_fst_1160_);
v___x_1164_ = lean_unsigned_to_nat(1u);
v___x_1165_ = lean_nat_add(v_fst_1160_, v___x_1164_);
lean_dec(v_fst_1160_);
v_as_1154_ = v___x_1163_;
v_lo_1155_ = v___x_1165_;
goto _start;
}
else
{
lean_dec(v_fst_1160_);
lean_dec(v_lo_1155_);
return v_snd_1161_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1___redArg___boxed(lean_object* v_as_1167_, lean_object* v_lo_1168_, lean_object* v_hi_1169_){
_start:
{
lean_object* v_res_1170_; 
v_res_1170_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1___redArg(v_as_1167_, v_lo_1168_, v_hi_1169_);
lean_dec(v_hi_1169_);
return v_res_1170_;
}
}
static lean_object* _init_l_Lean_Level_normalize___closed__3(void){
_start:
{
lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; 
v___x_1175_ = ((lean_object*)(l_Lean_Level_normalize___closed__2));
v___x_1176_ = lean_unsigned_to_nat(11u);
v___x_1177_ = lean_unsigned_to_nat(401u);
v___x_1178_ = ((lean_object*)(l_Lean_Level_normalize___closed__1));
v___x_1179_ = ((lean_object*)(l_Lean_Level_mvarId_x21___closed__0));
v___x_1180_ = l_mkPanicMessageWithDecl(v___x_1179_, v___x_1178_, v___x_1177_, v___x_1176_, v___x_1175_);
return v___x_1180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_normalize(lean_object* v_l_1181_){
_start:
{
uint8_t v___x_1182_; 
v___x_1182_ = l_Lean_Level_isAlreadyNormalizedCheap(v_l_1181_);
if (v___x_1182_ == 0)
{
lean_object* v_k_1183_; lean_object* v_u_1184_; 
v_k_1183_ = l_Lean_Level_getOffset(v_l_1181_);
v_u_1184_ = l_Lean_Level_getLevelOffset(v_l_1181_);
switch(lean_obj_tag(v_u_1184_))
{
case 2:
{
lean_object* v_a_1185_; lean_object* v_a_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v_lvls_1189_; lean_object* v_lvls_1190_; lean_object* v___x_1191_; lean_object* v___y_1193_; lean_object* v___y_1194_; lean_object* v___y_1202_; lean_object* v___y_1207_; lean_object* v___y_1208_; lean_object* v___x_1210_; uint8_t v___x_1211_; 
v_a_1185_ = lean_ctor_get(v_u_1184_, 0);
lean_inc(v_a_1185_);
v_a_1186_ = lean_ctor_get(v_u_1184_, 1);
lean_inc(v_a_1186_);
lean_dec_ref(v_u_1184_);
v___x_1187_ = lean_unsigned_to_nat(0u);
v___x_1188_ = ((lean_object*)(l_Lean_Level_normalize___closed__0));
v_lvls_1189_ = l___private_Lean_Level_0__Lean_Level_getMaxArgsAux___at___00Lean_Level_normalize_spec__0(v_a_1185_, v___x_1182_, v___x_1188_);
v_lvls_1190_ = l___private_Lean_Level_0__Lean_Level_getMaxArgsAux___at___00Lean_Level_normalize_spec__0(v_a_1186_, v___x_1182_, v_lvls_1189_);
v___x_1191_ = lean_unsigned_to_nat(1u);
v___x_1210_ = lean_array_get_size(v_lvls_1190_);
v___x_1211_ = lean_nat_dec_eq(v___x_1210_, v___x_1187_);
if (v___x_1211_ == 0)
{
lean_object* v___x_1212_; lean_object* v___y_1214_; uint8_t v___x_1216_; 
v___x_1212_ = lean_nat_sub(v___x_1210_, v___x_1191_);
v___x_1216_ = lean_nat_dec_le(v___x_1187_, v___x_1212_);
if (v___x_1216_ == 0)
{
lean_inc(v___x_1212_);
v___y_1214_ = v___x_1212_;
goto v___jp_1213_;
}
else
{
v___y_1214_ = v___x_1187_;
goto v___jp_1213_;
}
v___jp_1213_:
{
uint8_t v___x_1215_; 
v___x_1215_ = lean_nat_dec_le(v___y_1214_, v___x_1212_);
if (v___x_1215_ == 0)
{
lean_dec(v___x_1212_);
lean_inc(v___y_1214_);
v___y_1207_ = v___y_1214_;
v___y_1208_ = v___y_1214_;
goto v___jp_1206_;
}
else
{
v___y_1207_ = v___y_1214_;
v___y_1208_ = v___x_1212_;
goto v___jp_1206_;
}
}
}
else
{
v___y_1202_ = v_lvls_1190_;
goto v___jp_1201_;
}
v___jp_1192_:
{
lean_object* v___x_1195_; lean_object* v_lvl_u2081_1196_; lean_object* v_prev_1197_; lean_object* v_prevK_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; 
v___x_1195_ = lean_box(0);
v_lvl_u2081_1196_ = lean_array_get_borrowed(v___x_1195_, v___y_1193_, v___y_1194_);
v_prev_1197_ = l_Lean_Level_getLevelOffset(v_lvl_u2081_1196_);
v_prevK_1198_ = l_Lean_Level_getOffset(v_lvl_u2081_1196_);
v___x_1199_ = lean_nat_add(v___y_1194_, v___x_1191_);
lean_dec(v___y_1194_);
v___x_1200_ = l___private_Lean_Level_0__Lean_Level_mkMaxAux(v___y_1193_, v_k_1183_, v___x_1199_, v_prev_1197_, v_prevK_1198_, v___x_1195_);
lean_dec(v_k_1183_);
lean_dec_ref(v___y_1193_);
return v___x_1200_;
}
v___jp_1201_:
{
lean_object* v_firstNonExplicit_1203_; uint8_t v___x_1204_; 
v_firstNonExplicit_1203_ = l___private_Lean_Level_0__Lean_Level_skipExplicit(v___y_1202_, v___x_1187_);
lean_inc(v_firstNonExplicit_1203_);
v___x_1204_ = l___private_Lean_Level_0__Lean_Level_isExplicitSubsumed(v___y_1202_, v_firstNonExplicit_1203_);
if (v___x_1204_ == 0)
{
lean_object* v___x_1205_; 
v___x_1205_ = lean_nat_sub(v_firstNonExplicit_1203_, v___x_1191_);
lean_dec(v_firstNonExplicit_1203_);
v___y_1193_ = v___y_1202_;
v___y_1194_ = v___x_1205_;
goto v___jp_1192_;
}
else
{
v___y_1193_ = v___y_1202_;
v___y_1194_ = v_firstNonExplicit_1203_;
goto v___jp_1192_;
}
}
v___jp_1206_:
{
lean_object* v___x_1209_; 
v___x_1209_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1___redArg(v_lvls_1190_, v___y_1207_, v___y_1208_);
lean_dec(v___y_1208_);
v___y_1202_ = v___x_1209_;
goto v___jp_1201_;
}
}
case 3:
{
lean_object* v_a_1217_; lean_object* v_a_1218_; uint8_t v___x_1219_; 
v_a_1217_ = lean_ctor_get(v_u_1184_, 0);
lean_inc(v_a_1217_);
v_a_1218_ = lean_ctor_get(v_u_1184_, 1);
lean_inc(v_a_1218_);
lean_dec_ref(v_u_1184_);
v___x_1219_ = l_Lean_Level_isNeverZero(v_a_1218_);
if (v___x_1219_ == 0)
{
lean_object* v_l_u2081_1220_; lean_object* v_l_u2082_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; 
v_l_u2081_1220_ = l_Lean_Level_normalize(v_a_1217_);
lean_dec(v_a_1217_);
v_l_u2082_1221_ = l_Lean_Level_normalize(v_a_1218_);
lean_dec(v_a_1218_);
v___x_1222_ = l___private_Lean_Level_0__Lean_Level_mkIMaxAux(v_l_u2081_1220_, v_l_u2082_1221_);
v___x_1223_ = l_Lean_Level_addOffsetAux(v_k_1183_, v___x_1222_);
return v___x_1223_;
}
else
{
lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; 
v___x_1224_ = l_Lean_Level_max___override(v_a_1217_, v_a_1218_);
v___x_1225_ = l_Lean_Level_normalize(v___x_1224_);
lean_dec(v___x_1224_);
v___x_1226_ = l_Lean_Level_addOffsetAux(v_k_1183_, v___x_1225_);
return v___x_1226_;
}
}
default: 
{
lean_object* v___x_1227_; lean_object* v___x_1228_; 
lean_dec(v_u_1184_);
lean_dec(v_k_1183_);
v___x_1227_ = lean_obj_once(&l_Lean_Level_normalize___closed__3, &l_Lean_Level_normalize___closed__3_once, _init_l_Lean_Level_normalize___closed__3);
v___x_1228_ = l_panic___at___00Lean_Level_normalize_spec__2(v___x_1227_);
return v___x_1228_;
}
}
}
else
{
lean_inc(v_l_1181_);
return v_l_1181_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_getMaxArgsAux___at___00Lean_Level_normalize_spec__0(lean_object* v_x_1229_, uint8_t v_x_1230_, lean_object* v_x_1231_){
_start:
{
if (lean_obj_tag(v_x_1229_) == 2)
{
lean_object* v_a_1232_; lean_object* v_a_1233_; lean_object* v___x_1234_; 
v_a_1232_ = lean_ctor_get(v_x_1229_, 0);
lean_inc(v_a_1232_);
v_a_1233_ = lean_ctor_get(v_x_1229_, 1);
lean_inc(v_a_1233_);
lean_dec_ref(v_x_1229_);
v___x_1234_ = l___private_Lean_Level_0__Lean_Level_getMaxArgsAux___at___00Lean_Level_normalize_spec__0(v_a_1232_, v_x_1230_, v_x_1231_);
v_x_1229_ = v_a_1233_;
v_x_1231_ = v___x_1234_;
goto _start;
}
else
{
if (v_x_1230_ == 0)
{
lean_object* v___x_1236_; uint8_t v___x_1237_; 
v___x_1236_ = l_Lean_Level_normalize(v_x_1229_);
lean_dec(v_x_1229_);
v___x_1237_ = 1;
v_x_1229_ = v___x_1236_;
v_x_1230_ = v___x_1237_;
goto _start;
}
else
{
lean_object* v___x_1239_; 
v___x_1239_ = lean_array_push(v_x_1231_, v_x_1229_);
return v___x_1239_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_getMaxArgsAux___at___00Lean_Level_normalize_spec__0___boxed(lean_object* v_x_1240_, lean_object* v_x_1241_, lean_object* v_x_1242_){
_start:
{
uint8_t v_x_522__boxed_1243_; lean_object* v_res_1244_; 
v_x_522__boxed_1243_ = lean_unbox(v_x_1241_);
v_res_1244_ = l___private_Lean_Level_0__Lean_Level_getMaxArgsAux___at___00Lean_Level_normalize_spec__0(v_x_1240_, v_x_522__boxed_1243_, v_x_1242_);
return v_res_1244_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_normalize___boxed(lean_object* v_l_1245_){
_start:
{
lean_object* v_res_1246_; 
v_res_1246_ = l_Lean_Level_normalize(v_l_1245_);
lean_dec(v_l_1245_);
return v_res_1246_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1(lean_object* v_n_1247_, lean_object* v_as_1248_, lean_object* v_lo_1249_, lean_object* v_hi_1250_, lean_object* v_w_1251_, lean_object* v_hlo_1252_, lean_object* v_hhi_1253_){
_start:
{
lean_object* v___x_1254_; 
v___x_1254_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1___redArg(v_as_1248_, v_lo_1249_, v_hi_1250_);
return v___x_1254_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1___boxed(lean_object* v_n_1255_, lean_object* v_as_1256_, lean_object* v_lo_1257_, lean_object* v_hi_1258_, lean_object* v_w_1259_, lean_object* v_hlo_1260_, lean_object* v_hhi_1261_){
_start:
{
lean_object* v_res_1262_; 
v_res_1262_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1(v_n_1255_, v_as_1256_, v_lo_1257_, v_hi_1258_, v_w_1259_, v_hlo_1260_, v_hhi_1261_);
lean_dec(v_hi_1258_);
lean_dec(v_n_1255_);
return v_res_1262_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_isEquiv(lean_object* v_u_1263_, lean_object* v_v_1264_){
_start:
{
uint8_t v___x_1265_; 
v___x_1265_ = lean_level_eq(v_u_1263_, v_v_1264_);
if (v___x_1265_ == 0)
{
lean_object* v___x_1266_; lean_object* v___x_1267_; uint8_t v___x_1268_; 
v___x_1266_ = l_Lean_Level_normalize(v_u_1263_);
v___x_1267_ = l_Lean_Level_normalize(v_v_1264_);
v___x_1268_ = lean_level_eq(v___x_1266_, v___x_1267_);
lean_dec(v___x_1267_);
lean_dec(v___x_1266_);
return v___x_1268_;
}
else
{
return v___x_1265_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_isEquiv___boxed(lean_object* v_u_1269_, lean_object* v_v_1270_){
_start:
{
uint8_t v_res_1271_; lean_object* v_r_1272_; 
v_res_1271_ = l_Lean_Level_isEquiv(v_u_1269_, v_v_1270_);
lean_dec(v_v_1270_);
lean_dec(v_u_1269_);
v_r_1272_ = lean_box(v_res_1271_);
return v_r_1272_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_dec(lean_object* v_x_1273_){
_start:
{
lean_object* v_l_u2081_1275_; lean_object* v_l_u2082_1276_; 
switch(lean_obj_tag(v_x_1273_))
{
case 0:
{
lean_object* v___x_1289_; 
v___x_1289_ = lean_box(0);
return v___x_1289_;
}
case 1:
{
lean_object* v_a_1290_; lean_object* v___x_1291_; 
v_a_1290_ = lean_ctor_get(v_x_1273_, 0);
lean_inc(v_a_1290_);
v___x_1291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1291_, 0, v_a_1290_);
return v___x_1291_;
}
case 2:
{
lean_object* v_a_1292_; lean_object* v_a_1293_; 
v_a_1292_ = lean_ctor_get(v_x_1273_, 0);
v_a_1293_ = lean_ctor_get(v_x_1273_, 1);
v_l_u2081_1275_ = v_a_1292_;
v_l_u2082_1276_ = v_a_1293_;
goto v___jp_1274_;
}
case 3:
{
lean_object* v_a_1294_; lean_object* v_a_1295_; 
v_a_1294_ = lean_ctor_get(v_x_1273_, 0);
v_a_1295_ = lean_ctor_get(v_x_1273_, 1);
v_l_u2081_1275_ = v_a_1294_;
v_l_u2082_1276_ = v_a_1295_;
goto v___jp_1274_;
}
default: 
{
lean_object* v___x_1296_; 
v___x_1296_ = lean_box(0);
return v___x_1296_;
}
}
v___jp_1274_:
{
lean_object* v___x_1277_; 
v___x_1277_ = l_Lean_Level_dec(v_l_u2081_1275_);
if (lean_obj_tag(v___x_1277_) == 0)
{
return v___x_1277_;
}
else
{
lean_object* v_val_1278_; lean_object* v___x_1279_; 
v_val_1278_ = lean_ctor_get(v___x_1277_, 0);
lean_inc(v_val_1278_);
lean_dec_ref(v___x_1277_);
v___x_1279_ = l_Lean_Level_dec(v_l_u2082_1276_);
if (lean_obj_tag(v___x_1279_) == 0)
{
lean_dec(v_val_1278_);
return v___x_1279_;
}
else
{
lean_object* v_val_1280_; lean_object* v___x_1282_; uint8_t v_isShared_1283_; uint8_t v_isSharedCheck_1288_; 
v_val_1280_ = lean_ctor_get(v___x_1279_, 0);
v_isSharedCheck_1288_ = !lean_is_exclusive(v___x_1279_);
if (v_isSharedCheck_1288_ == 0)
{
v___x_1282_ = v___x_1279_;
v_isShared_1283_ = v_isSharedCheck_1288_;
goto v_resetjp_1281_;
}
else
{
lean_inc(v_val_1280_);
lean_dec(v___x_1279_);
v___x_1282_ = lean_box(0);
v_isShared_1283_ = v_isSharedCheck_1288_;
goto v_resetjp_1281_;
}
v_resetjp_1281_:
{
lean_object* v___x_1284_; lean_object* v___x_1286_; 
v___x_1284_ = l_Lean_Level_max___override(v_val_1278_, v_val_1280_);
if (v_isShared_1283_ == 0)
{
lean_ctor_set(v___x_1282_, 0, v___x_1284_);
v___x_1286_ = v___x_1282_;
goto v_reusejp_1285_;
}
else
{
lean_object* v_reuseFailAlloc_1287_; 
v_reuseFailAlloc_1287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1287_, 0, v___x_1284_);
v___x_1286_ = v_reuseFailAlloc_1287_;
goto v_reusejp_1285_;
}
v_reusejp_1285_:
{
return v___x_1286_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_dec___boxed(lean_object* v_x_1297_){
_start:
{
lean_object* v_res_1298_; 
v_res_1298_ = l_Lean_Level_dec(v_x_1297_);
lean_dec(v_x_1297_);
return v_res_1298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_ctorIdx(lean_object* v_x_1299_){
_start:
{
switch(lean_obj_tag(v_x_1299_))
{
case 0:
{
lean_object* v___x_1300_; 
v___x_1300_ = lean_unsigned_to_nat(0u);
return v___x_1300_;
}
case 1:
{
lean_object* v___x_1301_; 
v___x_1301_ = lean_unsigned_to_nat(1u);
return v___x_1301_;
}
case 2:
{
lean_object* v___x_1302_; 
v___x_1302_ = lean_unsigned_to_nat(2u);
return v___x_1302_;
}
case 3:
{
lean_object* v___x_1303_; 
v___x_1303_ = lean_unsigned_to_nat(3u);
return v___x_1303_;
}
default: 
{
lean_object* v___x_1304_; 
v___x_1304_ = lean_unsigned_to_nat(4u);
return v___x_1304_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_ctorIdx___boxed(lean_object* v_x_1305_){
_start:
{
lean_object* v_res_1306_; 
v_res_1306_ = l_Lean_Level_PP_Result_ctorIdx(v_x_1305_);
lean_dec_ref(v_x_1305_);
return v_res_1306_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_ctorElim___redArg(lean_object* v_t_1307_, lean_object* v_k_1308_){
_start:
{
if (lean_obj_tag(v_t_1307_) == 2)
{
lean_object* v_a_1309_; lean_object* v_a_1310_; lean_object* v___x_1311_; 
v_a_1309_ = lean_ctor_get(v_t_1307_, 0);
lean_inc_ref(v_a_1309_);
v_a_1310_ = lean_ctor_get(v_t_1307_, 1);
lean_inc(v_a_1310_);
lean_dec_ref(v_t_1307_);
v___x_1311_ = lean_apply_2(v_k_1308_, v_a_1309_, v_a_1310_);
return v___x_1311_;
}
else
{
lean_object* v_a_1312_; lean_object* v___x_1313_; 
v_a_1312_ = lean_ctor_get(v_t_1307_, 0);
lean_inc(v_a_1312_);
lean_dec_ref(v_t_1307_);
v___x_1313_ = lean_apply_1(v_k_1308_, v_a_1312_);
return v___x_1313_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_ctorElim(lean_object* v_motive__1_1314_, lean_object* v_ctorIdx_1315_, lean_object* v_t_1316_, lean_object* v_h_1317_, lean_object* v_k_1318_){
_start:
{
lean_object* v___x_1319_; 
v___x_1319_ = l_Lean_Level_PP_Result_ctorElim___redArg(v_t_1316_, v_k_1318_);
return v___x_1319_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_ctorElim___boxed(lean_object* v_motive__1_1320_, lean_object* v_ctorIdx_1321_, lean_object* v_t_1322_, lean_object* v_h_1323_, lean_object* v_k_1324_){
_start:
{
lean_object* v_res_1325_; 
v_res_1325_ = l_Lean_Level_PP_Result_ctorElim(v_motive__1_1320_, v_ctorIdx_1321_, v_t_1322_, v_h_1323_, v_k_1324_);
lean_dec(v_ctorIdx_1321_);
return v_res_1325_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_leaf_elim___redArg(lean_object* v_t_1326_, lean_object* v_leaf_1327_){
_start:
{
lean_object* v___x_1328_; 
v___x_1328_ = l_Lean_Level_PP_Result_ctorElim___redArg(v_t_1326_, v_leaf_1327_);
return v___x_1328_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_leaf_elim(lean_object* v_motive__1_1329_, lean_object* v_t_1330_, lean_object* v_h_1331_, lean_object* v_leaf_1332_){
_start:
{
lean_object* v___x_1333_; 
v___x_1333_ = l_Lean_Level_PP_Result_ctorElim___redArg(v_t_1330_, v_leaf_1332_);
return v___x_1333_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_num_elim___redArg(lean_object* v_t_1334_, lean_object* v_num_1335_){
_start:
{
lean_object* v___x_1336_; 
v___x_1336_ = l_Lean_Level_PP_Result_ctorElim___redArg(v_t_1334_, v_num_1335_);
return v___x_1336_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_num_elim(lean_object* v_motive__1_1337_, lean_object* v_t_1338_, lean_object* v_h_1339_, lean_object* v_num_1340_){
_start:
{
lean_object* v___x_1341_; 
v___x_1341_ = l_Lean_Level_PP_Result_ctorElim___redArg(v_t_1338_, v_num_1340_);
return v___x_1341_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_offset_elim___redArg(lean_object* v_t_1342_, lean_object* v_offset_1343_){
_start:
{
lean_object* v___x_1344_; 
v___x_1344_ = l_Lean_Level_PP_Result_ctorElim___redArg(v_t_1342_, v_offset_1343_);
return v___x_1344_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_offset_elim(lean_object* v_motive__1_1345_, lean_object* v_t_1346_, lean_object* v_h_1347_, lean_object* v_offset_1348_){
_start:
{
lean_object* v___x_1349_; 
v___x_1349_ = l_Lean_Level_PP_Result_ctorElim___redArg(v_t_1346_, v_offset_1348_);
return v___x_1349_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_maxNode_elim___redArg(lean_object* v_t_1350_, lean_object* v_maxNode_1351_){
_start:
{
lean_object* v___x_1352_; 
v___x_1352_ = l_Lean_Level_PP_Result_ctorElim___redArg(v_t_1350_, v_maxNode_1351_);
return v___x_1352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_maxNode_elim(lean_object* v_motive__1_1353_, lean_object* v_t_1354_, lean_object* v_h_1355_, lean_object* v_maxNode_1356_){
_start:
{
lean_object* v___x_1357_; 
v___x_1357_ = l_Lean_Level_PP_Result_ctorElim___redArg(v_t_1354_, v_maxNode_1356_);
return v___x_1357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_imaxNode_elim___redArg(lean_object* v_t_1358_, lean_object* v_imaxNode_1359_){
_start:
{
lean_object* v___x_1360_; 
v___x_1360_ = l_Lean_Level_PP_Result_ctorElim___redArg(v_t_1358_, v_imaxNode_1359_);
return v___x_1360_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_imaxNode_elim(lean_object* v_motive__1_1361_, lean_object* v_t_1362_, lean_object* v_h_1363_, lean_object* v_imaxNode_1364_){
_start:
{
lean_object* v___x_1365_; 
v___x_1365_ = l_Lean_Level_PP_Result_ctorElim___redArg(v_t_1362_, v_imaxNode_1364_);
return v___x_1365_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_succ(lean_object* v_x_1366_){
_start:
{
switch(lean_obj_tag(v_x_1366_))
{
case 2:
{
lean_object* v_a_1367_; lean_object* v_a_1368_; lean_object* v___x_1370_; uint8_t v_isShared_1371_; uint8_t v_isSharedCheck_1377_; 
v_a_1367_ = lean_ctor_get(v_x_1366_, 0);
v_a_1368_ = lean_ctor_get(v_x_1366_, 1);
v_isSharedCheck_1377_ = !lean_is_exclusive(v_x_1366_);
if (v_isSharedCheck_1377_ == 0)
{
v___x_1370_ = v_x_1366_;
v_isShared_1371_ = v_isSharedCheck_1377_;
goto v_resetjp_1369_;
}
else
{
lean_inc(v_a_1368_);
lean_inc(v_a_1367_);
lean_dec(v_x_1366_);
v___x_1370_ = lean_box(0);
v_isShared_1371_ = v_isSharedCheck_1377_;
goto v_resetjp_1369_;
}
v_resetjp_1369_:
{
lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1375_; 
v___x_1372_ = lean_unsigned_to_nat(1u);
v___x_1373_ = lean_nat_add(v_a_1368_, v___x_1372_);
lean_dec(v_a_1368_);
if (v_isShared_1371_ == 0)
{
lean_ctor_set(v___x_1370_, 1, v___x_1373_);
v___x_1375_ = v___x_1370_;
goto v_reusejp_1374_;
}
else
{
lean_object* v_reuseFailAlloc_1376_; 
v_reuseFailAlloc_1376_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1376_, 0, v_a_1367_);
lean_ctor_set(v_reuseFailAlloc_1376_, 1, v___x_1373_);
v___x_1375_ = v_reuseFailAlloc_1376_;
goto v_reusejp_1374_;
}
v_reusejp_1374_:
{
return v___x_1375_;
}
}
}
case 1:
{
lean_object* v_a_1378_; lean_object* v___x_1380_; uint8_t v_isShared_1381_; uint8_t v_isSharedCheck_1387_; 
v_a_1378_ = lean_ctor_get(v_x_1366_, 0);
v_isSharedCheck_1387_ = !lean_is_exclusive(v_x_1366_);
if (v_isSharedCheck_1387_ == 0)
{
v___x_1380_ = v_x_1366_;
v_isShared_1381_ = v_isSharedCheck_1387_;
goto v_resetjp_1379_;
}
else
{
lean_inc(v_a_1378_);
lean_dec(v_x_1366_);
v___x_1380_ = lean_box(0);
v_isShared_1381_ = v_isSharedCheck_1387_;
goto v_resetjp_1379_;
}
v_resetjp_1379_:
{
lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1385_; 
v___x_1382_ = lean_unsigned_to_nat(1u);
v___x_1383_ = lean_nat_add(v_a_1378_, v___x_1382_);
lean_dec(v_a_1378_);
if (v_isShared_1381_ == 0)
{
lean_ctor_set(v___x_1380_, 0, v___x_1383_);
v___x_1385_ = v___x_1380_;
goto v_reusejp_1384_;
}
else
{
lean_object* v_reuseFailAlloc_1386_; 
v_reuseFailAlloc_1386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1386_, 0, v___x_1383_);
v___x_1385_ = v_reuseFailAlloc_1386_;
goto v_reusejp_1384_;
}
v_reusejp_1384_:
{
return v___x_1385_;
}
}
}
default: 
{
lean_object* v___x_1388_; lean_object* v___x_1389_; 
v___x_1388_ = lean_unsigned_to_nat(1u);
v___x_1389_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1389_, 0, v_x_1366_);
lean_ctor_set(v___x_1389_, 1, v___x_1388_);
return v___x_1389_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_max(lean_object* v_x_1390_, lean_object* v_x_1391_){
_start:
{
if (lean_obj_tag(v_x_1391_) == 3)
{
lean_object* v_a_1392_; lean_object* v___x_1394_; uint8_t v_isShared_1395_; uint8_t v_isSharedCheck_1400_; 
v_a_1392_ = lean_ctor_get(v_x_1391_, 0);
v_isSharedCheck_1400_ = !lean_is_exclusive(v_x_1391_);
if (v_isSharedCheck_1400_ == 0)
{
v___x_1394_ = v_x_1391_;
v_isShared_1395_ = v_isSharedCheck_1400_;
goto v_resetjp_1393_;
}
else
{
lean_inc(v_a_1392_);
lean_dec(v_x_1391_);
v___x_1394_ = lean_box(0);
v_isShared_1395_ = v_isSharedCheck_1400_;
goto v_resetjp_1393_;
}
v_resetjp_1393_:
{
lean_object* v___x_1396_; lean_object* v___x_1398_; 
v___x_1396_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1396_, 0, v_x_1390_);
lean_ctor_set(v___x_1396_, 1, v_a_1392_);
if (v_isShared_1395_ == 0)
{
lean_ctor_set(v___x_1394_, 0, v___x_1396_);
v___x_1398_ = v___x_1394_;
goto v_reusejp_1397_;
}
else
{
lean_object* v_reuseFailAlloc_1399_; 
v_reuseFailAlloc_1399_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1399_, 0, v___x_1396_);
v___x_1398_ = v_reuseFailAlloc_1399_;
goto v_reusejp_1397_;
}
v_reusejp_1397_:
{
return v___x_1398_;
}
}
}
else
{
lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; 
v___x_1401_ = lean_box(0);
v___x_1402_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1402_, 0, v_x_1391_);
lean_ctor_set(v___x_1402_, 1, v___x_1401_);
v___x_1403_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1403_, 0, v_x_1390_);
lean_ctor_set(v___x_1403_, 1, v___x_1402_);
v___x_1404_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1404_, 0, v___x_1403_);
return v___x_1404_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_imax(lean_object* v_x_1405_, lean_object* v_x_1406_){
_start:
{
if (lean_obj_tag(v_x_1406_) == 4)
{
lean_object* v_a_1407_; lean_object* v___x_1409_; uint8_t v_isShared_1410_; uint8_t v_isSharedCheck_1415_; 
v_a_1407_ = lean_ctor_get(v_x_1406_, 0);
v_isSharedCheck_1415_ = !lean_is_exclusive(v_x_1406_);
if (v_isSharedCheck_1415_ == 0)
{
v___x_1409_ = v_x_1406_;
v_isShared_1410_ = v_isSharedCheck_1415_;
goto v_resetjp_1408_;
}
else
{
lean_inc(v_a_1407_);
lean_dec(v_x_1406_);
v___x_1409_ = lean_box(0);
v_isShared_1410_ = v_isSharedCheck_1415_;
goto v_resetjp_1408_;
}
v_resetjp_1408_:
{
lean_object* v___x_1411_; lean_object* v___x_1413_; 
v___x_1411_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1411_, 0, v_x_1405_);
lean_ctor_set(v___x_1411_, 1, v_a_1407_);
if (v_isShared_1410_ == 0)
{
lean_ctor_set(v___x_1409_, 0, v___x_1411_);
v___x_1413_ = v___x_1409_;
goto v_reusejp_1412_;
}
else
{
lean_object* v_reuseFailAlloc_1414_; 
v_reuseFailAlloc_1414_ = lean_alloc_ctor(4, 1, 0);
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
else
{
lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; 
v___x_1416_ = lean_box(0);
v___x_1417_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1417_, 0, v_x_1406_);
lean_ctor_set(v___x_1417_, 1, v___x_1416_);
v___x_1418_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1418_, 0, v_x_1405_);
lean_ctor_set(v___x_1418_, 1, v___x_1417_);
v___x_1419_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1419_, 0, v___x_1418_);
return v___x_1419_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_toResult(lean_object* v_l_1434_, uint8_t v_mvars_1435_){
_start:
{
switch(lean_obj_tag(v_l_1434_))
{
case 0:
{
lean_object* v___x_1436_; 
v___x_1436_ = ((lean_object*)(l_Lean_Level_PP_toResult___closed__0));
return v___x_1436_;
}
case 1:
{
lean_object* v_a_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; 
v_a_1437_ = lean_ctor_get(v_l_1434_, 0);
lean_inc(v_a_1437_);
lean_dec_ref(v_l_1434_);
v___x_1438_ = l_Lean_Level_PP_toResult(v_a_1437_, v_mvars_1435_);
v___x_1439_ = l_Lean_Level_PP_Result_succ(v___x_1438_);
return v___x_1439_;
}
case 2:
{
lean_object* v_a_1440_; lean_object* v_a_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; 
v_a_1440_ = lean_ctor_get(v_l_1434_, 0);
lean_inc(v_a_1440_);
v_a_1441_ = lean_ctor_get(v_l_1434_, 1);
lean_inc(v_a_1441_);
lean_dec_ref(v_l_1434_);
v___x_1442_ = l_Lean_Level_PP_toResult(v_a_1440_, v_mvars_1435_);
v___x_1443_ = l_Lean_Level_PP_toResult(v_a_1441_, v_mvars_1435_);
v___x_1444_ = l_Lean_Level_PP_Result_max(v___x_1442_, v___x_1443_);
return v___x_1444_;
}
case 3:
{
lean_object* v_a_1445_; lean_object* v_a_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; 
v_a_1445_ = lean_ctor_get(v_l_1434_, 0);
lean_inc(v_a_1445_);
v_a_1446_ = lean_ctor_get(v_l_1434_, 1);
lean_inc(v_a_1446_);
lean_dec_ref(v_l_1434_);
v___x_1447_ = l_Lean_Level_PP_toResult(v_a_1445_, v_mvars_1435_);
v___x_1448_ = l_Lean_Level_PP_toResult(v_a_1446_, v_mvars_1435_);
v___x_1449_ = l_Lean_Level_PP_Result_imax(v___x_1447_, v___x_1448_);
return v___x_1449_;
}
case 4:
{
lean_object* v_a_1450_; lean_object* v___x_1451_; 
v_a_1450_ = lean_ctor_get(v_l_1434_, 0);
lean_inc(v_a_1450_);
lean_dec_ref(v_l_1434_);
v___x_1451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1451_, 0, v_a_1450_);
return v___x_1451_;
}
default: 
{
if (v_mvars_1435_ == 0)
{
lean_object* v___x_1452_; 
lean_dec_ref(v_l_1434_);
v___x_1452_ = ((lean_object*)(l_Lean_Level_PP_toResult___closed__3));
return v___x_1452_;
}
else
{
lean_object* v_a_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; 
v_a_1453_ = lean_ctor_get(v_l_1434_, 0);
lean_inc(v_a_1453_);
lean_dec_ref(v_l_1434_);
v___x_1454_ = ((lean_object*)(l_Lean_Level_PP_toResult___closed__5));
v___x_1455_ = ((lean_object*)(l_Lean_Level_PP_toResult___closed__7));
v___x_1456_ = l_Lean_Name_replacePrefix(v_a_1453_, v___x_1454_, v___x_1455_);
v___x_1457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1457_, 0, v___x_1456_);
return v___x_1457_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_toResult___boxed(lean_object* v_l_1458_, lean_object* v_mvars_1459_){
_start:
{
uint8_t v_mvars_boxed_1460_; lean_object* v_res_1461_; 
v_mvars_boxed_1460_ = lean_unbox(v_mvars_1459_);
v_res_1461_ = l_Lean_Level_PP_toResult(v_l_1458_, v_mvars_boxed_1460_);
return v_res_1461_;
}
}
static lean_object* _init_l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__1(void){
_start:
{
lean_object* v___x_1463_; lean_object* v___x_1464_; 
v___x_1463_ = ((lean_object*)(l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__0));
v___x_1464_ = lean_string_length(v___x_1463_);
return v___x_1464_;
}
}
static lean_object* _init_l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__2(void){
_start:
{
lean_object* v___x_1465_; lean_object* v___x_1466_; 
v___x_1465_ = lean_obj_once(&l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__1, &l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__1_once, _init_l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__1);
v___x_1466_ = lean_nat_to_int(v___x_1465_);
return v___x_1466_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse(lean_object* v_x_1471_, uint8_t v_x_1472_){
_start:
{
if (v_x_1472_ == 0)
{
lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; uint8_t v___x_1479_; lean_object* v___x_1480_; 
v___x_1473_ = lean_obj_once(&l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__2, &l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__2_once, _init_l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__2);
v___x_1474_ = ((lean_object*)(l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__3));
v___x_1475_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1475_, 0, v___x_1474_);
lean_ctor_set(v___x_1475_, 1, v_x_1471_);
v___x_1476_ = ((lean_object*)(l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__4));
v___x_1477_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1477_, 0, v___x_1475_);
lean_ctor_set(v___x_1477_, 1, v___x_1476_);
v___x_1478_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1478_, 0, v___x_1473_);
lean_ctor_set(v___x_1478_, 1, v___x_1477_);
v___x_1479_ = 0;
v___x_1480_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1480_, 0, v___x_1478_);
lean_ctor_set_uint8(v___x_1480_, sizeof(void*)*1, v___x_1479_);
return v___x_1480_;
}
else
{
return v_x_1471_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___boxed(lean_object* v_x_1481_, lean_object* v_x_1482_){
_start:
{
uint8_t v_x_57__boxed_1483_; lean_object* v_res_1484_; 
v_x_57__boxed_1483_ = lean_unbox(v_x_1482_);
v_res_1484_ = l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse(v_x_1481_, v_x_57__boxed_1483_);
return v_res_1484_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_format(lean_object* v_x_1494_, uint8_t v_x_1495_){
_start:
{
switch(lean_obj_tag(v_x_1494_))
{
case 0:
{
lean_object* v_a_1496_; lean_object* v___x_1498_; uint8_t v_isShared_1499_; uint8_t v_isSharedCheck_1505_; 
v_a_1496_ = lean_ctor_get(v_x_1494_, 0);
v_isSharedCheck_1505_ = !lean_is_exclusive(v_x_1494_);
if (v_isSharedCheck_1505_ == 0)
{
v___x_1498_ = v_x_1494_;
v_isShared_1499_ = v_isSharedCheck_1505_;
goto v_resetjp_1497_;
}
else
{
lean_inc(v_a_1496_);
lean_dec(v_x_1494_);
v___x_1498_ = lean_box(0);
v_isShared_1499_ = v_isSharedCheck_1505_;
goto v_resetjp_1497_;
}
v_resetjp_1497_:
{
uint8_t v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1503_; 
v___x_1500_ = 1;
v___x_1501_ = l_Lean_Name_toString(v_a_1496_, v___x_1500_);
if (v_isShared_1499_ == 0)
{
lean_ctor_set_tag(v___x_1498_, 3);
lean_ctor_set(v___x_1498_, 0, v___x_1501_);
v___x_1503_ = v___x_1498_;
goto v_reusejp_1502_;
}
else
{
lean_object* v_reuseFailAlloc_1504_; 
v_reuseFailAlloc_1504_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1504_, 0, v___x_1501_);
v___x_1503_ = v_reuseFailAlloc_1504_;
goto v_reusejp_1502_;
}
v_reusejp_1502_:
{
return v___x_1503_;
}
}
}
case 1:
{
lean_object* v_a_1506_; lean_object* v___x_1508_; uint8_t v_isShared_1509_; uint8_t v_isSharedCheck_1514_; 
v_a_1506_ = lean_ctor_get(v_x_1494_, 0);
v_isSharedCheck_1514_ = !lean_is_exclusive(v_x_1494_);
if (v_isSharedCheck_1514_ == 0)
{
v___x_1508_ = v_x_1494_;
v_isShared_1509_ = v_isSharedCheck_1514_;
goto v_resetjp_1507_;
}
else
{
lean_inc(v_a_1506_);
lean_dec(v_x_1494_);
v___x_1508_ = lean_box(0);
v_isShared_1509_ = v_isSharedCheck_1514_;
goto v_resetjp_1507_;
}
v_resetjp_1507_:
{
lean_object* v___x_1510_; lean_object* v___x_1512_; 
v___x_1510_ = l_Nat_reprFast(v_a_1506_);
if (v_isShared_1509_ == 0)
{
lean_ctor_set_tag(v___x_1508_, 3);
lean_ctor_set(v___x_1508_, 0, v___x_1510_);
v___x_1512_ = v___x_1508_;
goto v_reusejp_1511_;
}
else
{
lean_object* v_reuseFailAlloc_1513_; 
v_reuseFailAlloc_1513_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1513_, 0, v___x_1510_);
v___x_1512_ = v_reuseFailAlloc_1513_;
goto v_reusejp_1511_;
}
v_reusejp_1511_:
{
return v___x_1512_;
}
}
}
case 2:
{
lean_object* v_a_1515_; lean_object* v_a_1516_; lean_object* v___x_1518_; uint8_t v_isShared_1519_; uint8_t v_isSharedCheck_1535_; 
v_a_1515_ = lean_ctor_get(v_x_1494_, 0);
v_a_1516_ = lean_ctor_get(v_x_1494_, 1);
v_isSharedCheck_1535_ = !lean_is_exclusive(v_x_1494_);
if (v_isSharedCheck_1535_ == 0)
{
v___x_1518_ = v_x_1494_;
v_isShared_1519_ = v_isSharedCheck_1535_;
goto v_resetjp_1517_;
}
else
{
lean_inc(v_a_1516_);
lean_inc(v_a_1515_);
lean_dec(v_x_1494_);
v___x_1518_ = lean_box(0);
v_isShared_1519_ = v_isSharedCheck_1535_;
goto v_resetjp_1517_;
}
v_resetjp_1517_:
{
lean_object* v_zero_1520_; uint8_t v_isZero_1521_; 
v_zero_1520_ = lean_unsigned_to_nat(0u);
v_isZero_1521_ = lean_nat_dec_eq(v_a_1516_, v_zero_1520_);
if (v_isZero_1521_ == 1)
{
lean_del_object(v___x_1518_);
lean_dec(v_a_1516_);
v_x_1494_ = v_a_1515_;
goto _start;
}
else
{
lean_object* v_one_1523_; lean_object* v_n_1524_; lean_object* v_f_x27_1525_; lean_object* v___x_1526_; lean_object* v___x_1528_; 
v_one_1523_ = lean_unsigned_to_nat(1u);
v_n_1524_ = lean_nat_sub(v_a_1516_, v_one_1523_);
lean_dec(v_a_1516_);
v_f_x27_1525_ = l_Lean_Level_PP_Result_format(v_a_1515_, v_isZero_1521_);
v___x_1526_ = ((lean_object*)(l_Lean_Level_PP_Result_format___closed__1));
if (v_isShared_1519_ == 0)
{
lean_ctor_set_tag(v___x_1518_, 5);
lean_ctor_set(v___x_1518_, 1, v___x_1526_);
lean_ctor_set(v___x_1518_, 0, v_f_x27_1525_);
v___x_1528_ = v___x_1518_;
goto v_reusejp_1527_;
}
else
{
lean_object* v_reuseFailAlloc_1534_; 
v_reuseFailAlloc_1534_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1534_, 0, v_f_x27_1525_);
lean_ctor_set(v_reuseFailAlloc_1534_, 1, v___x_1526_);
v___x_1528_ = v_reuseFailAlloc_1534_;
goto v_reusejp_1527_;
}
v_reusejp_1527_:
{
lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; 
v___x_1529_ = lean_nat_add(v_n_1524_, v_one_1523_);
lean_dec(v_n_1524_);
v___x_1530_ = l_Nat_reprFast(v___x_1529_);
v___x_1531_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1531_, 0, v___x_1530_);
v___x_1532_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1532_, 0, v___x_1528_);
lean_ctor_set(v___x_1532_, 1, v___x_1531_);
v___x_1533_ = l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse(v___x_1532_, v_x_1495_);
return v___x_1533_;
}
}
}
}
case 3:
{
lean_object* v_a_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; uint8_t v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; 
v_a_1536_ = lean_ctor_get(v_x_1494_, 0);
lean_inc(v_a_1536_);
lean_dec_ref(v_x_1494_);
v___x_1537_ = ((lean_object*)(l_Lean_Level_PP_Result_format___closed__3));
v___x_1538_ = l___private_Lean_Level_0__Lean_Level_PP_Result_formatLst(v_a_1536_);
v___x_1539_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1539_, 0, v___x_1537_);
lean_ctor_set(v___x_1539_, 1, v___x_1538_);
v___x_1540_ = 0;
v___x_1541_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1541_, 0, v___x_1539_);
lean_ctor_set_uint8(v___x_1541_, sizeof(void*)*1, v___x_1540_);
v___x_1542_ = l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse(v___x_1541_, v_x_1495_);
return v___x_1542_;
}
default: 
{
lean_object* v_a_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; uint8_t v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; 
v_a_1543_ = lean_ctor_get(v_x_1494_, 0);
lean_inc(v_a_1543_);
lean_dec_ref(v_x_1494_);
v___x_1544_ = ((lean_object*)(l_Lean_Level_PP_Result_format___closed__5));
v___x_1545_ = l___private_Lean_Level_0__Lean_Level_PP_Result_formatLst(v_a_1543_);
v___x_1546_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1546_, 0, v___x_1544_);
lean_ctor_set(v___x_1546_, 1, v___x_1545_);
v___x_1547_ = 0;
v___x_1548_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1548_, 0, v___x_1546_);
lean_ctor_set_uint8(v___x_1548_, sizeof(void*)*1, v___x_1547_);
v___x_1549_ = l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse(v___x_1548_, v_x_1495_);
return v___x_1549_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_PP_Result_formatLst(lean_object* v_x_1550_){
_start:
{
if (lean_obj_tag(v_x_1550_) == 0)
{
lean_object* v___x_1551_; 
v___x_1551_ = lean_box(0);
return v___x_1551_;
}
else
{
lean_object* v_head_1552_; lean_object* v_tail_1553_; lean_object* v___x_1555_; uint8_t v_isShared_1556_; uint8_t v_isSharedCheck_1565_; 
v_head_1552_ = lean_ctor_get(v_x_1550_, 0);
v_tail_1553_ = lean_ctor_get(v_x_1550_, 1);
v_isSharedCheck_1565_ = !lean_is_exclusive(v_x_1550_);
if (v_isSharedCheck_1565_ == 0)
{
v___x_1555_ = v_x_1550_;
v_isShared_1556_ = v_isSharedCheck_1565_;
goto v_resetjp_1554_;
}
else
{
lean_inc(v_tail_1553_);
lean_inc(v_head_1552_);
lean_dec(v_x_1550_);
v___x_1555_ = lean_box(0);
v_isShared_1556_ = v_isSharedCheck_1565_;
goto v_resetjp_1554_;
}
v_resetjp_1554_:
{
lean_object* v___x_1557_; uint8_t v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1561_; 
v___x_1557_ = lean_box(1);
v___x_1558_ = 0;
v___x_1559_ = l_Lean_Level_PP_Result_format(v_head_1552_, v___x_1558_);
if (v_isShared_1556_ == 0)
{
lean_ctor_set_tag(v___x_1555_, 5);
lean_ctor_set(v___x_1555_, 1, v___x_1559_);
lean_ctor_set(v___x_1555_, 0, v___x_1557_);
v___x_1561_ = v___x_1555_;
goto v_reusejp_1560_;
}
else
{
lean_object* v_reuseFailAlloc_1564_; 
v_reuseFailAlloc_1564_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1564_, 0, v___x_1557_);
lean_ctor_set(v_reuseFailAlloc_1564_, 1, v___x_1559_);
v___x_1561_ = v_reuseFailAlloc_1564_;
goto v_reusejp_1560_;
}
v_reusejp_1560_:
{
lean_object* v___x_1562_; lean_object* v___x_1563_; 
v___x_1562_ = l___private_Lean_Level_0__Lean_Level_PP_Result_formatLst(v_tail_1553_);
v___x_1563_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1563_, 0, v___x_1561_);
lean_ctor_set(v___x_1563_, 1, v___x_1562_);
return v___x_1563_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_format___boxed(lean_object* v_x_1566_, lean_object* v_x_1567_){
_start:
{
uint8_t v_x_270__boxed_1568_; lean_object* v_res_1569_; 
v_x_270__boxed_1568_ = lean_unbox(v_x_1567_);
v_res_1569_ = l_Lean_Level_PP_Result_format(v_x_1566_, v_x_270__boxed_1568_);
return v_res_1569_;
}
}
static lean_object* _init_l_Lean_Level_PP_Result_quote___closed__0(void){
_start:
{
uint8_t v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; 
v___x_1570_ = 0;
v___x_1571_ = lean_box(0);
v___x_1572_ = l_Lean_SourceInfo_fromRef(v___x_1571_, v___x_1570_);
return v___x_1572_;
}
}
static lean_object* _init_l_Lean_Level_PP_Result_quote___closed__6(void){
_start:
{
lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; 
v___x_1582_ = ((lean_object*)(l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__0));
v___x_1583_ = lean_obj_once(&l_Lean_Level_PP_Result_quote___closed__0, &l_Lean_Level_PP_Result_quote___closed__0_once, _init_l_Lean_Level_PP_Result_quote___closed__0);
v___x_1584_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1584_, 0, v___x_1583_);
lean_ctor_set(v___x_1584_, 1, v___x_1582_);
return v___x_1584_;
}
}
static lean_object* _init_l_Lean_Level_PP_Result_quote___closed__7(void){
_start:
{
lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; 
v___x_1585_ = ((lean_object*)(l_Lean_instReprData___lam__0___closed__0));
v___x_1586_ = lean_obj_once(&l_Lean_Level_PP_Result_quote___closed__0, &l_Lean_Level_PP_Result_quote___closed__0_once, _init_l_Lean_Level_PP_Result_quote___closed__0);
v___x_1587_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1587_, 0, v___x_1586_);
lean_ctor_set(v___x_1587_, 1, v___x_1585_);
return v___x_1587_;
}
}
static lean_object* _init_l_Lean_Level_PP_Result_quote___closed__11(void){
_start:
{
lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; 
v___x_1599_ = ((lean_object*)(l_Lean_Level_PP_Result_format___closed__2));
v___x_1600_ = lean_obj_once(&l_Lean_Level_PP_Result_quote___closed__0, &l_Lean_Level_PP_Result_quote___closed__0_once, _init_l_Lean_Level_PP_Result_quote___closed__0);
v___x_1601_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1601_, 0, v___x_1600_);
lean_ctor_set(v___x_1601_, 1, v___x_1599_);
return v___x_1601_;
}
}
static lean_object* _init_l_Lean_Level_PP_Result_quote___closed__14(void){
_start:
{
lean_object* v___x_1605_; 
v___x_1605_ = l_Array_mkArray0(lean_box(0));
return v___x_1605_;
}
}
static lean_object* _init_l_Lean_Level_PP_Result_quote___closed__16(void){
_start:
{
lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; 
v___x_1611_ = ((lean_object*)(l_Lean_Level_PP_Result_format___closed__4));
v___x_1612_ = lean_obj_once(&l_Lean_Level_PP_Result_quote___closed__0, &l_Lean_Level_PP_Result_quote___closed__0_once, _init_l_Lean_Level_PP_Result_quote___closed__0);
v___x_1613_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1613_, 0, v___x_1612_);
lean_ctor_set(v___x_1613_, 1, v___x_1611_);
return v___x_1613_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_quote(lean_object* v_r_1614_, lean_object* v_prec_1615_){
_start:
{
lean_object* v_s_1617_; 
switch(lean_obj_tag(v_r_1614_))
{
case 0:
{
lean_object* v_a_1625_; lean_object* v___x_1626_; 
v_a_1625_ = lean_ctor_get(v_r_1614_, 0);
lean_inc(v_a_1625_);
lean_dec_ref(v_r_1614_);
v___x_1626_ = lean_mk_syntax_ident(v_a_1625_);
return v___x_1626_;
}
case 1:
{
lean_object* v_a_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; 
v_a_1627_ = lean_ctor_get(v_r_1614_, 0);
lean_inc(v_a_1627_);
lean_dec_ref(v_r_1614_);
v___x_1628_ = l_Nat_reprFast(v_a_1627_);
v___x_1629_ = lean_box(2);
v___x_1630_ = l_Lean_Syntax_mkNumLit(v___x_1628_, v___x_1629_);
return v___x_1630_;
}
case 2:
{
lean_object* v_a_1631_; lean_object* v_a_1632_; lean_object* v___x_1634_; uint8_t v_isShared_1635_; uint8_t v_isSharedCheck_1655_; 
v_a_1631_ = lean_ctor_get(v_r_1614_, 0);
v_a_1632_ = lean_ctor_get(v_r_1614_, 1);
v_isSharedCheck_1655_ = !lean_is_exclusive(v_r_1614_);
if (v_isSharedCheck_1655_ == 0)
{
v___x_1634_ = v_r_1614_;
v_isShared_1635_ = v_isSharedCheck_1655_;
goto v_resetjp_1633_;
}
else
{
lean_inc(v_a_1632_);
lean_inc(v_a_1631_);
lean_dec(v_r_1614_);
v___x_1634_ = lean_box(0);
v_isShared_1635_ = v_isSharedCheck_1655_;
goto v_resetjp_1633_;
}
v_resetjp_1633_:
{
lean_object* v_zero_1636_; uint8_t v_isZero_1637_; 
v_zero_1636_ = lean_unsigned_to_nat(0u);
v_isZero_1637_ = lean_nat_dec_eq(v_a_1632_, v_zero_1636_);
if (v_isZero_1637_ == 1)
{
lean_del_object(v___x_1634_);
lean_dec(v_a_1632_);
v_r_1614_ = v_a_1631_;
goto _start;
}
else
{
lean_object* v_one_1639_; lean_object* v_n_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1648_; 
v_one_1639_ = lean_unsigned_to_nat(1u);
v_n_1640_ = lean_nat_sub(v_a_1632_, v_one_1639_);
lean_dec(v_a_1632_);
v___x_1641_ = lean_box(0);
v___x_1642_ = l_Lean_SourceInfo_fromRef(v___x_1641_, v_isZero_1637_);
v___x_1643_ = ((lean_object*)(l_Lean_Level_PP_Result_quote___closed__9));
v___x_1644_ = lean_unsigned_to_nat(65u);
v___x_1645_ = l_Lean_Level_PP_Result_quote(v_a_1631_, v___x_1644_);
v___x_1646_ = ((lean_object*)(l_Lean_Level_PP_Result_format___closed__0));
lean_inc(v___x_1642_);
if (v_isShared_1635_ == 0)
{
lean_ctor_set(v___x_1634_, 1, v___x_1646_);
lean_ctor_set(v___x_1634_, 0, v___x_1642_);
v___x_1648_ = v___x_1634_;
goto v_reusejp_1647_;
}
else
{
lean_object* v_reuseFailAlloc_1654_; 
v_reuseFailAlloc_1654_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1654_, 0, v___x_1642_);
lean_ctor_set(v_reuseFailAlloc_1654_, 1, v___x_1646_);
v___x_1648_ = v_reuseFailAlloc_1654_;
goto v_reusejp_1647_;
}
v_reusejp_1647_:
{
lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; 
v___x_1649_ = lean_nat_add(v_n_1640_, v_one_1639_);
lean_dec(v_n_1640_);
v___x_1650_ = l_Nat_reprFast(v___x_1649_);
v___x_1651_ = lean_box(2);
v___x_1652_ = l_Lean_Syntax_mkNumLit(v___x_1650_, v___x_1651_);
v___x_1653_ = l_Lean_Syntax_node3(v___x_1642_, v___x_1643_, v___x_1645_, v___x_1648_, v___x_1652_);
v_s_1617_ = v___x_1653_;
goto v___jp_1616_;
}
}
}
}
case 3:
{
lean_object* v_a_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; size_t v_sz_1663_; size_t v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; 
v_a_1656_ = lean_ctor_get(v_r_1614_, 0);
lean_inc(v_a_1656_);
lean_dec_ref(v_r_1614_);
v___x_1657_ = lean_obj_once(&l_Lean_Level_PP_Result_quote___closed__0, &l_Lean_Level_PP_Result_quote___closed__0_once, _init_l_Lean_Level_PP_Result_quote___closed__0);
v___x_1658_ = ((lean_object*)(l_Lean_Level_PP_Result_quote___closed__10));
v___x_1659_ = lean_obj_once(&l_Lean_Level_PP_Result_quote___closed__11, &l_Lean_Level_PP_Result_quote___closed__11_once, _init_l_Lean_Level_PP_Result_quote___closed__11);
v___x_1660_ = ((lean_object*)(l_Lean_Level_PP_Result_quote___closed__13));
v___x_1661_ = lean_obj_once(&l_Lean_Level_PP_Result_quote___closed__14, &l_Lean_Level_PP_Result_quote___closed__14_once, _init_l_Lean_Level_PP_Result_quote___closed__14);
v___x_1662_ = lean_array_mk(v_a_1656_);
v_sz_1663_ = lean_array_size(v___x_1662_);
v___x_1664_ = ((size_t)0ULL);
v___x_1665_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Level_PP_Result_quote_spec__0(v_sz_1663_, v___x_1664_, v___x_1662_);
v___x_1666_ = l_Array_append___redArg(v___x_1661_, v___x_1665_);
lean_dec_ref(v___x_1665_);
v___x_1667_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1667_, 0, v___x_1657_);
lean_ctor_set(v___x_1667_, 1, v___x_1660_);
lean_ctor_set(v___x_1667_, 2, v___x_1666_);
v___x_1668_ = l_Lean_Syntax_node2(v___x_1657_, v___x_1658_, v___x_1659_, v___x_1667_);
v_s_1617_ = v___x_1668_;
goto v___jp_1616_;
}
default: 
{
lean_object* v_a_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; size_t v_sz_1676_; size_t v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; 
v_a_1669_ = lean_ctor_get(v_r_1614_, 0);
lean_inc(v_a_1669_);
lean_dec_ref(v_r_1614_);
v___x_1670_ = lean_obj_once(&l_Lean_Level_PP_Result_quote___closed__0, &l_Lean_Level_PP_Result_quote___closed__0_once, _init_l_Lean_Level_PP_Result_quote___closed__0);
v___x_1671_ = ((lean_object*)(l_Lean_Level_PP_Result_quote___closed__15));
v___x_1672_ = lean_obj_once(&l_Lean_Level_PP_Result_quote___closed__16, &l_Lean_Level_PP_Result_quote___closed__16_once, _init_l_Lean_Level_PP_Result_quote___closed__16);
v___x_1673_ = ((lean_object*)(l_Lean_Level_PP_Result_quote___closed__13));
v___x_1674_ = lean_obj_once(&l_Lean_Level_PP_Result_quote___closed__14, &l_Lean_Level_PP_Result_quote___closed__14_once, _init_l_Lean_Level_PP_Result_quote___closed__14);
v___x_1675_ = lean_array_mk(v_a_1669_);
v_sz_1676_ = lean_array_size(v___x_1675_);
v___x_1677_ = ((size_t)0ULL);
v___x_1678_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Level_PP_Result_quote_spec__0(v_sz_1676_, v___x_1677_, v___x_1675_);
v___x_1679_ = l_Array_append___redArg(v___x_1674_, v___x_1678_);
lean_dec_ref(v___x_1678_);
v___x_1680_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1680_, 0, v___x_1670_);
lean_ctor_set(v___x_1680_, 1, v___x_1673_);
lean_ctor_set(v___x_1680_, 2, v___x_1679_);
v___x_1681_ = l_Lean_Syntax_node2(v___x_1670_, v___x_1671_, v___x_1672_, v___x_1680_);
v_s_1617_ = v___x_1681_;
goto v___jp_1616_;
}
}
v___jp_1616_:
{
lean_object* v___x_1618_; uint8_t v___x_1619_; 
v___x_1618_ = lean_unsigned_to_nat(0u);
v___x_1619_ = lean_nat_dec_lt(v___x_1618_, v_prec_1615_);
if (v___x_1619_ == 0)
{
return v_s_1617_;
}
else
{
lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; 
v___x_1620_ = lean_obj_once(&l_Lean_Level_PP_Result_quote___closed__0, &l_Lean_Level_PP_Result_quote___closed__0_once, _init_l_Lean_Level_PP_Result_quote___closed__0);
v___x_1621_ = ((lean_object*)(l_Lean_Level_PP_Result_quote___closed__5));
v___x_1622_ = lean_obj_once(&l_Lean_Level_PP_Result_quote___closed__6, &l_Lean_Level_PP_Result_quote___closed__6_once, _init_l_Lean_Level_PP_Result_quote___closed__6);
v___x_1623_ = lean_obj_once(&l_Lean_Level_PP_Result_quote___closed__7, &l_Lean_Level_PP_Result_quote___closed__7_once, _init_l_Lean_Level_PP_Result_quote___closed__7);
v___x_1624_ = l_Lean_Syntax_node3(v___x_1620_, v___x_1621_, v___x_1622_, v_s_1617_, v___x_1623_);
return v___x_1624_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Level_PP_Result_quote_spec__0(size_t v_sz_1682_, size_t v_i_1683_, lean_object* v_bs_1684_){
_start:
{
uint8_t v___x_1685_; 
v___x_1685_ = lean_usize_dec_lt(v_i_1683_, v_sz_1682_);
if (v___x_1685_ == 0)
{
return v_bs_1684_;
}
else
{
lean_object* v_v_1686_; lean_object* v___x_1687_; lean_object* v_bs_x27_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; size_t v___x_1691_; size_t v___x_1692_; lean_object* v___x_1693_; 
v_v_1686_ = lean_array_uget(v_bs_1684_, v_i_1683_);
v___x_1687_ = lean_unsigned_to_nat(0u);
v_bs_x27_1688_ = lean_array_uset(v_bs_1684_, v_i_1683_, v___x_1687_);
v___x_1689_ = lean_unsigned_to_nat(1024u);
v___x_1690_ = l_Lean_Level_PP_Result_quote(v_v_1686_, v___x_1689_);
v___x_1691_ = ((size_t)1ULL);
v___x_1692_ = lean_usize_add(v_i_1683_, v___x_1691_);
v___x_1693_ = lean_array_uset(v_bs_x27_1688_, v_i_1683_, v___x_1690_);
v_i_1683_ = v___x_1692_;
v_bs_1684_ = v___x_1693_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Level_PP_Result_quote_spec__0___boxed(lean_object* v_sz_1695_, lean_object* v_i_1696_, lean_object* v_bs_1697_){
_start:
{
size_t v_sz_boxed_1698_; size_t v_i_boxed_1699_; lean_object* v_res_1700_; 
v_sz_boxed_1698_ = lean_unbox_usize(v_sz_1695_);
lean_dec(v_sz_1695_);
v_i_boxed_1699_ = lean_unbox_usize(v_i_1696_);
lean_dec(v_i_1696_);
v_res_1700_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Level_PP_Result_quote_spec__0(v_sz_boxed_1698_, v_i_boxed_1699_, v_bs_1697_);
return v_res_1700_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_quote___boxed(lean_object* v_r_1701_, lean_object* v_prec_1702_){
_start:
{
lean_object* v_res_1703_; 
v_res_1703_ = l_Lean_Level_PP_Result_quote(v_r_1701_, v_prec_1702_);
lean_dec(v_prec_1702_);
return v_res_1703_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_format(lean_object* v_u_1704_, uint8_t v_mvars_1705_){
_start:
{
lean_object* v___x_1706_; uint8_t v___x_1707_; lean_object* v___x_1708_; 
v___x_1706_ = l_Lean_Level_PP_toResult(v_u_1704_, v_mvars_1705_);
v___x_1707_ = 1;
v___x_1708_ = l_Lean_Level_PP_Result_format(v___x_1706_, v___x_1707_);
return v___x_1708_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_format___boxed(lean_object* v_u_1709_, lean_object* v_mvars_1710_){
_start:
{
uint8_t v_mvars_boxed_1711_; lean_object* v_res_1712_; 
v_mvars_boxed_1711_ = lean_unbox(v_mvars_1710_);
v_res_1712_ = l_Lean_Level_format(v_u_1709_, v_mvars_boxed_1711_);
return v_res_1712_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_instToFormat___lam__0(lean_object* v_u_1713_){
_start:
{
uint8_t v___x_1714_; lean_object* v___x_1715_; 
v___x_1714_ = 1;
v___x_1715_ = l_Lean_Level_format(v_u_1713_, v___x_1714_);
return v___x_1715_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_instToString___lam__0(lean_object* v_u_1718_){
_start:
{
uint8_t v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; 
v___x_1719_ = 1;
v___x_1720_ = l_Lean_Level_format(v_u_1718_, v___x_1719_);
v___x_1721_ = l_Std_Format_defWidth;
v___x_1722_ = lean_unsigned_to_nat(0u);
v___x_1723_ = l_Std_Format_pretty(v___x_1720_, v___x_1721_, v___x_1722_, v___x_1722_);
return v___x_1723_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_quote(lean_object* v_u_1726_, lean_object* v_prec_1727_, uint8_t v_mvars_1728_){
_start:
{
lean_object* v___x_1729_; lean_object* v___x_1730_; 
v___x_1729_ = l_Lean_Level_PP_toResult(v_u_1726_, v_mvars_1728_);
v___x_1730_ = l_Lean_Level_PP_Result_quote(v___x_1729_, v_prec_1727_);
return v___x_1730_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_quote___boxed(lean_object* v_u_1731_, lean_object* v_prec_1732_, lean_object* v_mvars_1733_){
_start:
{
uint8_t v_mvars_boxed_1734_; lean_object* v_res_1735_; 
v_mvars_boxed_1734_ = lean_unbox(v_mvars_1733_);
v_res_1735_ = l_Lean_Level_quote(v_u_1731_, v_prec_1732_, v_mvars_boxed_1734_);
lean_dec(v_prec_1732_);
return v_res_1735_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_instQuoteMkStr1___lam__0(lean_object* v_u_1736_){
_start:
{
lean_object* v___x_1737_; uint8_t v___x_1738_; lean_object* v___x_1739_; 
v___x_1737_ = lean_unsigned_to_nat(0u);
v___x_1738_ = 1;
v___x_1739_ = l_Lean_Level_quote(v_u_1736_, v___x_1737_, v___x_1738_);
return v___x_1739_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Level_0__Lean_mkLevelMaxCore___lam__0(lean_object* v_u_1742_, lean_object* v_v_1743_){
_start:
{
uint8_t v___y_1745_; uint8_t v___x_1751_; 
v___x_1751_ = l_Lean_Level_isExplicit(v_v_1743_);
if (v___x_1751_ == 0)
{
v___y_1745_ = v___x_1751_;
goto v___jp_1744_;
}
else
{
lean_object* v___x_1752_; lean_object* v___x_1753_; uint8_t v___x_1754_; 
v___x_1752_ = l_Lean_Level_getOffset(v_v_1743_);
v___x_1753_ = l_Lean_Level_getOffset(v_u_1742_);
v___x_1754_ = lean_nat_dec_le(v___x_1752_, v___x_1753_);
lean_dec(v___x_1753_);
lean_dec(v___x_1752_);
v___y_1745_ = v___x_1754_;
goto v___jp_1744_;
}
v___jp_1744_:
{
uint8_t v___x_1746_; 
v___x_1746_ = 1;
if (v___y_1745_ == 0)
{
if (lean_obj_tag(v_u_1742_) == 2)
{
lean_object* v_a_1747_; lean_object* v_a_1748_; uint8_t v___x_1749_; 
v_a_1747_ = lean_ctor_get(v_u_1742_, 0);
v_a_1748_ = lean_ctor_get(v_u_1742_, 1);
v___x_1749_ = lean_level_eq(v_v_1743_, v_a_1747_);
if (v___x_1749_ == 0)
{
uint8_t v___x_1750_; 
v___x_1750_ = lean_level_eq(v_v_1743_, v_a_1748_);
return v___x_1750_;
}
else
{
return v___x_1746_;
}
}
else
{
return v___y_1745_;
}
}
else
{
return v___x_1746_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_mkLevelMaxCore___lam__0___boxed(lean_object* v_u_1755_, lean_object* v_v_1756_){
_start:
{
uint8_t v_res_1757_; lean_object* v_r_1758_; 
v_res_1757_ = l___private_Lean_Level_0__Lean_mkLevelMaxCore___lam__0(v_u_1755_, v_v_1756_);
lean_dec(v_v_1756_);
lean_dec(v_u_1755_);
v_r_1758_ = lean_box(v_res_1757_);
return v_r_1758_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_mkLevelMaxCore(lean_object* v_u_1759_, lean_object* v_v_1760_, lean_object* v_elseK_1761_){
_start:
{
uint8_t v___x_1762_; 
v___x_1762_ = lean_level_eq(v_u_1759_, v_v_1760_);
if (v___x_1762_ == 0)
{
uint8_t v___x_1763_; 
v___x_1763_ = l_Lean_Level_isZero(v_u_1759_);
if (v___x_1763_ == 0)
{
uint8_t v___x_1764_; 
v___x_1764_ = l_Lean_Level_isZero(v_v_1760_);
if (v___x_1764_ == 0)
{
uint8_t v___x_1765_; 
v___x_1765_ = l___private_Lean_Level_0__Lean_mkLevelMaxCore___lam__0(v_u_1759_, v_v_1760_);
if (v___x_1765_ == 0)
{
uint8_t v___x_1766_; 
v___x_1766_ = l___private_Lean_Level_0__Lean_mkLevelMaxCore___lam__0(v_v_1760_, v_u_1759_);
if (v___x_1766_ == 0)
{
lean_object* v___x_1767_; lean_object* v___x_1768_; uint8_t v___x_1769_; 
v___x_1767_ = l_Lean_Level_getLevelOffset(v_u_1759_);
v___x_1768_ = l_Lean_Level_getLevelOffset(v_v_1760_);
v___x_1769_ = lean_level_eq(v___x_1767_, v___x_1768_);
lean_dec(v___x_1768_);
lean_dec(v___x_1767_);
if (v___x_1769_ == 0)
{
lean_object* v___x_1770_; lean_object* v___x_1771_; 
v___x_1770_ = lean_box(0);
v___x_1771_ = lean_apply_1(v_elseK_1761_, v___x_1770_);
return v___x_1771_;
}
else
{
lean_object* v___x_1772_; lean_object* v___x_1773_; uint8_t v___x_1774_; 
lean_dec_ref(v_elseK_1761_);
v___x_1772_ = l_Lean_Level_getOffset(v_v_1760_);
v___x_1773_ = l_Lean_Level_getOffset(v_u_1759_);
v___x_1774_ = lean_nat_dec_le(v___x_1772_, v___x_1773_);
lean_dec(v___x_1773_);
lean_dec(v___x_1772_);
if (v___x_1774_ == 0)
{
lean_inc(v_v_1760_);
return v_v_1760_;
}
else
{
lean_inc(v_u_1759_);
return v_u_1759_;
}
}
}
else
{
lean_dec_ref(v_elseK_1761_);
lean_inc(v_v_1760_);
return v_v_1760_;
}
}
else
{
lean_dec_ref(v_elseK_1761_);
lean_inc(v_u_1759_);
return v_u_1759_;
}
}
else
{
lean_dec_ref(v_elseK_1761_);
lean_inc(v_u_1759_);
return v_u_1759_;
}
}
else
{
lean_dec_ref(v_elseK_1761_);
lean_inc(v_v_1760_);
return v_v_1760_;
}
}
else
{
lean_dec_ref(v_elseK_1761_);
lean_inc(v_u_1759_);
return v_u_1759_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_mkLevelMaxCore___boxed(lean_object* v_u_1775_, lean_object* v_v_1776_, lean_object* v_elseK_1777_){
_start:
{
lean_object* v_res_1778_; 
v_res_1778_ = l___private_Lean_Level_0__Lean_mkLevelMaxCore(v_u_1775_, v_v_1776_, v_elseK_1777_);
lean_dec(v_v_1776_);
lean_dec(v_u_1775_);
return v_res_1778_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLevelMax_x27(lean_object* v_u_1779_, lean_object* v_v_1780_){
_start:
{
uint8_t v___x_1781_; 
v___x_1781_ = lean_level_eq(v_u_1779_, v_v_1780_);
if (v___x_1781_ == 0)
{
uint8_t v___x_1782_; 
v___x_1782_ = l_Lean_Level_isZero(v_u_1779_);
if (v___x_1782_ == 0)
{
uint8_t v___x_1783_; 
v___x_1783_ = l_Lean_Level_isZero(v_v_1780_);
if (v___x_1783_ == 0)
{
uint8_t v___x_1784_; 
v___x_1784_ = l___private_Lean_Level_0__Lean_mkLevelMaxCore___lam__0(v_u_1779_, v_v_1780_);
if (v___x_1784_ == 0)
{
uint8_t v___x_1785_; 
v___x_1785_ = l___private_Lean_Level_0__Lean_mkLevelMaxCore___lam__0(v_v_1780_, v_u_1779_);
if (v___x_1785_ == 0)
{
lean_object* v___x_1786_; lean_object* v___x_1787_; uint8_t v___x_1788_; 
v___x_1786_ = l_Lean_Level_getLevelOffset(v_u_1779_);
v___x_1787_ = l_Lean_Level_getLevelOffset(v_v_1780_);
v___x_1788_ = lean_level_eq(v___x_1786_, v___x_1787_);
lean_dec(v___x_1787_);
lean_dec(v___x_1786_);
if (v___x_1788_ == 0)
{
lean_object* v___x_1789_; 
v___x_1789_ = l_Lean_Level_max___override(v_u_1779_, v_v_1780_);
return v___x_1789_;
}
else
{
lean_object* v___x_1790_; lean_object* v___x_1791_; uint8_t v___x_1792_; 
v___x_1790_ = l_Lean_Level_getOffset(v_v_1780_);
v___x_1791_ = l_Lean_Level_getOffset(v_u_1779_);
v___x_1792_ = lean_nat_dec_le(v___x_1790_, v___x_1791_);
lean_dec(v___x_1791_);
lean_dec(v___x_1790_);
if (v___x_1792_ == 0)
{
lean_dec(v_u_1779_);
return v_v_1780_;
}
else
{
lean_dec(v_v_1780_);
return v_u_1779_;
}
}
}
else
{
lean_dec(v_u_1779_);
return v_v_1780_;
}
}
else
{
lean_dec(v_v_1780_);
return v_u_1779_;
}
}
else
{
lean_dec(v_v_1780_);
return v_u_1779_;
}
}
else
{
lean_dec(v_u_1779_);
return v_v_1780_;
}
}
else
{
lean_dec(v_v_1780_);
return v_u_1779_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_simpLevelMax_x27(lean_object* v_u_1793_, lean_object* v_v_1794_, lean_object* v_d_1795_){
_start:
{
uint8_t v___x_1796_; 
v___x_1796_ = lean_level_eq(v_u_1793_, v_v_1794_);
if (v___x_1796_ == 0)
{
uint8_t v___x_1797_; 
v___x_1797_ = l_Lean_Level_isZero(v_u_1793_);
if (v___x_1797_ == 0)
{
uint8_t v___x_1798_; 
v___x_1798_ = l_Lean_Level_isZero(v_v_1794_);
if (v___x_1798_ == 0)
{
uint8_t v___x_1799_; 
v___x_1799_ = l___private_Lean_Level_0__Lean_mkLevelMaxCore___lam__0(v_u_1793_, v_v_1794_);
if (v___x_1799_ == 0)
{
uint8_t v___x_1800_; 
v___x_1800_ = l___private_Lean_Level_0__Lean_mkLevelMaxCore___lam__0(v_v_1794_, v_u_1793_);
if (v___x_1800_ == 0)
{
lean_object* v___x_1801_; lean_object* v___x_1802_; uint8_t v___x_1803_; 
v___x_1801_ = l_Lean_Level_getLevelOffset(v_u_1793_);
v___x_1802_ = l_Lean_Level_getLevelOffset(v_v_1794_);
v___x_1803_ = lean_level_eq(v___x_1801_, v___x_1802_);
lean_dec(v___x_1802_);
lean_dec(v___x_1801_);
if (v___x_1803_ == 0)
{
lean_inc(v_d_1795_);
return v_d_1795_;
}
else
{
lean_object* v___x_1804_; lean_object* v___x_1805_; uint8_t v___x_1806_; 
v___x_1804_ = l_Lean_Level_getOffset(v_v_1794_);
v___x_1805_ = l_Lean_Level_getOffset(v_u_1793_);
v___x_1806_ = lean_nat_dec_le(v___x_1804_, v___x_1805_);
lean_dec(v___x_1805_);
lean_dec(v___x_1804_);
if (v___x_1806_ == 0)
{
lean_inc(v_v_1794_);
return v_v_1794_;
}
else
{
lean_inc(v_u_1793_);
return v_u_1793_;
}
}
}
else
{
lean_inc(v_v_1794_);
return v_v_1794_;
}
}
else
{
lean_inc(v_u_1793_);
return v_u_1793_;
}
}
else
{
lean_inc(v_u_1793_);
return v_u_1793_;
}
}
else
{
lean_inc(v_v_1794_);
return v_v_1794_;
}
}
else
{
lean_inc(v_u_1793_);
return v_u_1793_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_simpLevelMax_x27___boxed(lean_object* v_u_1807_, lean_object* v_v_1808_, lean_object* v_d_1809_){
_start:
{
lean_object* v_res_1810_; 
v_res_1810_ = l_Lean_simpLevelMax_x27(v_u_1807_, v_v_1808_, v_d_1809_);
lean_dec(v_d_1809_);
lean_dec(v_v_1808_);
lean_dec(v_u_1807_);
return v_res_1810_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_mkLevelIMaxCore(lean_object* v_u_1811_, lean_object* v_v_1812_, lean_object* v_elseK_1813_){
_start:
{
uint8_t v___x_1814_; 
v___x_1814_ = l_Lean_Level_isNeverZero(v_v_1812_);
if (v___x_1814_ == 0)
{
uint8_t v___x_1815_; 
v___x_1815_ = l_Lean_Level_isZero(v_v_1812_);
if (v___x_1815_ == 0)
{
uint8_t v___x_1816_; 
v___x_1816_ = l_Lean_Level_isZero(v_u_1811_);
if (v___x_1816_ == 0)
{
uint8_t v___x_1817_; 
v___x_1817_ = lean_level_eq(v_u_1811_, v_v_1812_);
lean_dec(v_v_1812_);
if (v___x_1817_ == 0)
{
lean_object* v___x_1818_; lean_object* v___x_1819_; 
lean_dec(v_u_1811_);
v___x_1818_ = lean_box(0);
v___x_1819_ = lean_apply_1(v_elseK_1813_, v___x_1818_);
return v___x_1819_;
}
else
{
lean_dec_ref(v_elseK_1813_);
return v_u_1811_;
}
}
else
{
lean_dec_ref(v_elseK_1813_);
lean_dec(v_u_1811_);
return v_v_1812_;
}
}
else
{
lean_dec_ref(v_elseK_1813_);
lean_dec(v_u_1811_);
return v_v_1812_;
}
}
else
{
lean_object* v___x_1820_; 
lean_dec_ref(v_elseK_1813_);
v___x_1820_ = l_Lean_mkLevelMax_x27(v_u_1811_, v_v_1812_);
return v___x_1820_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkLevelIMax_x27(lean_object* v_u_1821_, lean_object* v_v_1822_){
_start:
{
uint8_t v___x_1823_; 
v___x_1823_ = l_Lean_Level_isNeverZero(v_v_1822_);
if (v___x_1823_ == 0)
{
uint8_t v___x_1824_; 
v___x_1824_ = l_Lean_Level_isZero(v_v_1822_);
if (v___x_1824_ == 0)
{
uint8_t v___x_1825_; 
v___x_1825_ = l_Lean_Level_isZero(v_u_1821_);
if (v___x_1825_ == 0)
{
uint8_t v___x_1826_; 
v___x_1826_ = lean_level_eq(v_u_1821_, v_v_1822_);
if (v___x_1826_ == 0)
{
lean_object* v___x_1827_; 
v___x_1827_ = l_Lean_Level_imax___override(v_u_1821_, v_v_1822_);
return v___x_1827_;
}
else
{
lean_dec(v_v_1822_);
return v_u_1821_;
}
}
else
{
lean_dec(v_u_1821_);
return v_v_1822_;
}
}
else
{
lean_dec(v_u_1821_);
return v_v_1822_;
}
}
else
{
lean_object* v___x_1828_; 
v___x_1828_ = l_Lean_mkLevelMax_x27(v_u_1821_, v_v_1822_);
return v___x_1828_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_simpLevelIMax_x27(lean_object* v_u_1829_, lean_object* v_v_1830_, lean_object* v_d_1831_){
_start:
{
uint8_t v___x_1832_; 
v___x_1832_ = l_Lean_Level_isNeverZero(v_v_1830_);
if (v___x_1832_ == 0)
{
uint8_t v___x_1833_; 
v___x_1833_ = l_Lean_Level_isZero(v_v_1830_);
if (v___x_1833_ == 0)
{
uint8_t v___x_1834_; 
v___x_1834_ = l_Lean_Level_isZero(v_u_1829_);
if (v___x_1834_ == 0)
{
uint8_t v___x_1835_; 
v___x_1835_ = lean_level_eq(v_u_1829_, v_v_1830_);
lean_dec(v_v_1830_);
if (v___x_1835_ == 0)
{
lean_dec(v_u_1829_);
lean_inc(v_d_1831_);
return v_d_1831_;
}
else
{
return v_u_1829_;
}
}
else
{
lean_dec(v_u_1829_);
return v_v_1830_;
}
}
else
{
lean_dec(v_u_1829_);
return v_v_1830_;
}
}
else
{
lean_object* v___x_1836_; 
v___x_1836_ = l_Lean_mkLevelMax_x27(v_u_1829_, v_v_1830_);
return v___x_1836_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_simpLevelIMax_x27___boxed(lean_object* v_u_1837_, lean_object* v_v_1838_, lean_object* v_d_1839_){
_start:
{
lean_object* v_res_1840_; 
v_res_1840_ = l_Lean_simpLevelIMax_x27(v_u_1837_, v_v_1838_, v_d_1839_);
lean_dec(v_d_1839_);
return v_res_1840_;
}
}
static lean_object* _init_l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl___closed__2(void){
_start:
{
lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; 
v___x_1843_ = ((lean_object*)(l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl___closed__1));
v___x_1844_ = lean_unsigned_to_nat(14u);
v___x_1845_ = lean_unsigned_to_nat(555u);
v___x_1846_ = ((lean_object*)(l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl___closed__0));
v___x_1847_ = ((lean_object*)(l_Lean_Level_mvarId_x21___closed__0));
v___x_1848_ = l_mkPanicMessageWithDecl(v___x_1847_, v___x_1846_, v___x_1845_, v___x_1844_, v___x_1843_);
return v___x_1848_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl(lean_object* v_lvl_1849_, lean_object* v_newLvl_1850_){
_start:
{
if (lean_obj_tag(v_lvl_1849_) == 1)
{
lean_object* v_a_1851_; size_t v___x_1852_; size_t v___x_1853_; uint8_t v___x_1854_; 
v_a_1851_ = lean_ctor_get(v_lvl_1849_, 0);
v___x_1852_ = lean_ptr_addr(v_a_1851_);
v___x_1853_ = lean_ptr_addr(v_newLvl_1850_);
v___x_1854_ = lean_usize_dec_eq(v___x_1852_, v___x_1853_);
if (v___x_1854_ == 0)
{
lean_object* v___x_1855_; 
v___x_1855_ = l_Lean_Level_succ___override(v_newLvl_1850_);
return v___x_1855_;
}
else
{
lean_dec(v_newLvl_1850_);
lean_inc_ref(v_lvl_1849_);
return v_lvl_1849_;
}
}
else
{
lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; 
lean_dec(v_newLvl_1850_);
v___x_1856_ = lean_box(0);
v___x_1857_ = lean_obj_once(&l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl___closed__2, &l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl___closed__2_once, _init_l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl___closed__2);
v___x_1858_ = l_panic___redArg(v___x_1856_, v___x_1857_);
return v___x_1858_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl___boxed(lean_object* v_lvl_1859_, lean_object* v_newLvl_1860_){
_start:
{
lean_object* v_res_1861_; 
v_res_1861_ = l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl(v_lvl_1859_, v_newLvl_1860_);
lean_dec(v_lvl_1859_);
return v_res_1861_;
}
}
static lean_object* _init_l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl___closed__2(void){
_start:
{
lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; 
v___x_1864_ = ((lean_object*)(l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl___closed__1));
v___x_1865_ = lean_unsigned_to_nat(19u);
v___x_1866_ = lean_unsigned_to_nat(566u);
v___x_1867_ = ((lean_object*)(l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl___closed__0));
v___x_1868_ = ((lean_object*)(l_Lean_Level_mvarId_x21___closed__0));
v___x_1869_ = l_mkPanicMessageWithDecl(v___x_1868_, v___x_1867_, v___x_1866_, v___x_1865_, v___x_1864_);
return v___x_1869_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl(lean_object* v_lvl_1870_, lean_object* v_newLhs_1871_, lean_object* v_newRhs_1872_){
_start:
{
uint8_t v___y_1874_; 
if (lean_obj_tag(v_lvl_1870_) == 2)
{
lean_object* v_a_1877_; lean_object* v_a_1878_; size_t v___x_1879_; size_t v___x_1880_; uint8_t v___x_1881_; 
v_a_1877_ = lean_ctor_get(v_lvl_1870_, 0);
v_a_1878_ = lean_ctor_get(v_lvl_1870_, 1);
v___x_1879_ = lean_ptr_addr(v_a_1877_);
v___x_1880_ = lean_ptr_addr(v_newLhs_1871_);
v___x_1881_ = lean_usize_dec_eq(v___x_1879_, v___x_1880_);
if (v___x_1881_ == 0)
{
v___y_1874_ = v___x_1881_;
goto v___jp_1873_;
}
else
{
size_t v___x_1882_; size_t v___x_1883_; uint8_t v___x_1884_; 
v___x_1882_ = lean_ptr_addr(v_a_1878_);
v___x_1883_ = lean_ptr_addr(v_newRhs_1872_);
v___x_1884_ = lean_usize_dec_eq(v___x_1882_, v___x_1883_);
v___y_1874_ = v___x_1884_;
goto v___jp_1873_;
}
}
else
{
lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; 
lean_dec(v_newRhs_1872_);
lean_dec(v_newLhs_1871_);
v___x_1885_ = lean_box(0);
v___x_1886_ = lean_obj_once(&l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl___closed__2, &l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl___closed__2_once, _init_l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl___closed__2);
v___x_1887_ = l_panic___redArg(v___x_1885_, v___x_1886_);
return v___x_1887_;
}
v___jp_1873_:
{
if (v___y_1874_ == 0)
{
lean_object* v___x_1875_; 
v___x_1875_ = l_Lean_mkLevelMax_x27(v_newLhs_1871_, v_newRhs_1872_);
return v___x_1875_;
}
else
{
lean_object* v___x_1876_; 
v___x_1876_ = l_Lean_simpLevelMax_x27(v_newLhs_1871_, v_newRhs_1872_, v_lvl_1870_);
lean_dec(v_newRhs_1872_);
lean_dec(v_newLhs_1871_);
return v___x_1876_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl___boxed(lean_object* v_lvl_1888_, lean_object* v_newLhs_1889_, lean_object* v_newRhs_1890_){
_start:
{
lean_object* v_res_1891_; 
v_res_1891_ = l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl(v_lvl_1888_, v_newLhs_1889_, v_newRhs_1890_);
lean_dec(v_lvl_1888_);
return v_res_1891_;
}
}
static lean_object* _init_l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl___closed__2(void){
_start:
{
lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; 
v___x_1894_ = ((lean_object*)(l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl___closed__1));
v___x_1895_ = lean_unsigned_to_nat(20u);
v___x_1896_ = lean_unsigned_to_nat(577u);
v___x_1897_ = ((lean_object*)(l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl___closed__0));
v___x_1898_ = ((lean_object*)(l_Lean_Level_mvarId_x21___closed__0));
v___x_1899_ = l_mkPanicMessageWithDecl(v___x_1898_, v___x_1897_, v___x_1896_, v___x_1895_, v___x_1894_);
return v___x_1899_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl(lean_object* v_lvl_1900_, lean_object* v_newLhs_1901_, lean_object* v_newRhs_1902_){
_start:
{
uint8_t v___y_1904_; 
if (lean_obj_tag(v_lvl_1900_) == 3)
{
lean_object* v_a_1907_; lean_object* v_a_1908_; size_t v___x_1909_; size_t v___x_1910_; uint8_t v___x_1911_; 
v_a_1907_ = lean_ctor_get(v_lvl_1900_, 0);
v_a_1908_ = lean_ctor_get(v_lvl_1900_, 1);
v___x_1909_ = lean_ptr_addr(v_a_1907_);
v___x_1910_ = lean_ptr_addr(v_newLhs_1901_);
v___x_1911_ = lean_usize_dec_eq(v___x_1909_, v___x_1910_);
if (v___x_1911_ == 0)
{
v___y_1904_ = v___x_1911_;
goto v___jp_1903_;
}
else
{
size_t v___x_1912_; size_t v___x_1913_; uint8_t v___x_1914_; 
v___x_1912_ = lean_ptr_addr(v_a_1908_);
v___x_1913_ = lean_ptr_addr(v_newRhs_1902_);
v___x_1914_ = lean_usize_dec_eq(v___x_1912_, v___x_1913_);
v___y_1904_ = v___x_1914_;
goto v___jp_1903_;
}
}
else
{
lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; 
lean_dec(v_newRhs_1902_);
lean_dec(v_newLhs_1901_);
v___x_1915_ = lean_box(0);
v___x_1916_ = lean_obj_once(&l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl___closed__2, &l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl___closed__2_once, _init_l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl___closed__2);
v___x_1917_ = l_panic___redArg(v___x_1915_, v___x_1916_);
return v___x_1917_;
}
v___jp_1903_:
{
if (v___y_1904_ == 0)
{
lean_object* v___x_1905_; 
v___x_1905_ = l_Lean_mkLevelIMax_x27(v_newLhs_1901_, v_newRhs_1902_);
return v___x_1905_;
}
else
{
lean_object* v___x_1906_; 
v___x_1906_ = l_Lean_simpLevelIMax_x27(v_newLhs_1901_, v_newRhs_1902_, v_lvl_1900_);
return v___x_1906_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl___boxed(lean_object* v_lvl_1918_, lean_object* v_newLhs_1919_, lean_object* v_newRhs_1920_){
_start:
{
lean_object* v_res_1921_; 
v_res_1921_ = l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl(v_lvl_1918_, v_newLhs_1919_, v_newRhs_1920_);
lean_dec(v_lvl_1918_);
return v_res_1921_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_mkNaryMax(lean_object* v_x_1922_){
_start:
{
if (lean_obj_tag(v_x_1922_) == 0)
{
lean_object* v___x_1923_; 
v___x_1923_ = lean_box(0);
return v___x_1923_;
}
else
{
lean_object* v_tail_1924_; 
v_tail_1924_ = lean_ctor_get(v_x_1922_, 1);
if (lean_obj_tag(v_tail_1924_) == 0)
{
lean_object* v_head_1925_; 
v_head_1925_ = lean_ctor_get(v_x_1922_, 0);
lean_inc(v_head_1925_);
lean_dec_ref(v_x_1922_);
return v_head_1925_;
}
else
{
lean_object* v_head_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; 
lean_inc(v_tail_1924_);
v_head_1926_ = lean_ctor_get(v_x_1922_, 0);
lean_inc(v_head_1926_);
lean_dec_ref(v_x_1922_);
v___x_1927_ = l_Lean_Level_mkNaryMax(v_tail_1924_);
v___x_1928_ = l_Lean_mkLevelMax_x27(v_head_1926_, v___x_1927_);
return v___x_1928_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_substParams_go(lean_object* v_s_1929_, lean_object* v_u_1930_){
_start:
{
switch(lean_obj_tag(v_u_1930_))
{
case 0:
{
lean_dec_ref(v_s_1929_);
return v_u_1930_;
}
case 1:
{
lean_object* v_a_1931_; uint8_t v___x_1932_; 
v_a_1931_ = lean_ctor_get(v_u_1930_, 0);
v___x_1932_ = l_Lean_Level_hasParam(v_u_1930_);
if (v___x_1932_ == 0)
{
lean_dec_ref(v_s_1929_);
return v_u_1930_;
}
else
{
lean_object* v___x_1933_; size_t v___x_1934_; size_t v___x_1935_; uint8_t v___x_1936_; 
lean_inc(v_a_1931_);
v___x_1933_ = l___private_Lean_Level_0__Lean_Level_substParams_go(v_s_1929_, v_a_1931_);
v___x_1934_ = lean_ptr_addr(v_a_1931_);
v___x_1935_ = lean_ptr_addr(v___x_1933_);
v___x_1936_ = lean_usize_dec_eq(v___x_1934_, v___x_1935_);
if (v___x_1936_ == 0)
{
lean_object* v___x_1937_; 
lean_dec_ref(v_u_1930_);
v___x_1937_ = l_Lean_Level_succ___override(v___x_1933_);
return v___x_1937_;
}
else
{
lean_dec(v___x_1933_);
return v_u_1930_;
}
}
}
case 2:
{
lean_object* v_a_1938_; lean_object* v_a_1939_; uint8_t v___x_1940_; 
v_a_1938_ = lean_ctor_get(v_u_1930_, 0);
v_a_1939_ = lean_ctor_get(v_u_1930_, 1);
v___x_1940_ = l_Lean_Level_hasParam(v_u_1930_);
if (v___x_1940_ == 0)
{
lean_dec_ref(v_s_1929_);
return v_u_1930_;
}
else
{
lean_object* v___x_1941_; lean_object* v___x_1942_; uint8_t v___y_1944_; size_t v___x_1947_; size_t v___x_1948_; uint8_t v___x_1949_; 
lean_inc(v_a_1938_);
lean_inc_ref(v_s_1929_);
v___x_1941_ = l___private_Lean_Level_0__Lean_Level_substParams_go(v_s_1929_, v_a_1938_);
lean_inc(v_a_1939_);
v___x_1942_ = l___private_Lean_Level_0__Lean_Level_substParams_go(v_s_1929_, v_a_1939_);
v___x_1947_ = lean_ptr_addr(v_a_1938_);
v___x_1948_ = lean_ptr_addr(v___x_1941_);
v___x_1949_ = lean_usize_dec_eq(v___x_1947_, v___x_1948_);
if (v___x_1949_ == 0)
{
v___y_1944_ = v___x_1949_;
goto v___jp_1943_;
}
else
{
size_t v___x_1950_; size_t v___x_1951_; uint8_t v___x_1952_; 
v___x_1950_ = lean_ptr_addr(v_a_1939_);
v___x_1951_ = lean_ptr_addr(v___x_1942_);
v___x_1952_ = lean_usize_dec_eq(v___x_1950_, v___x_1951_);
v___y_1944_ = v___x_1952_;
goto v___jp_1943_;
}
v___jp_1943_:
{
if (v___y_1944_ == 0)
{
lean_object* v___x_1945_; 
lean_dec_ref(v_u_1930_);
v___x_1945_ = l_Lean_mkLevelMax_x27(v___x_1941_, v___x_1942_);
return v___x_1945_;
}
else
{
lean_object* v___x_1946_; 
v___x_1946_ = l_Lean_simpLevelMax_x27(v___x_1941_, v___x_1942_, v_u_1930_);
lean_dec_ref(v_u_1930_);
lean_dec(v___x_1942_);
lean_dec(v___x_1941_);
return v___x_1946_;
}
}
}
}
case 3:
{
lean_object* v_a_1953_; lean_object* v_a_1954_; uint8_t v___x_1955_; 
v_a_1953_ = lean_ctor_get(v_u_1930_, 0);
v_a_1954_ = lean_ctor_get(v_u_1930_, 1);
v___x_1955_ = l_Lean_Level_hasParam(v_u_1930_);
if (v___x_1955_ == 0)
{
lean_dec_ref(v_s_1929_);
return v_u_1930_;
}
else
{
lean_object* v___x_1956_; lean_object* v___x_1957_; uint8_t v___y_1959_; size_t v___x_1962_; size_t v___x_1963_; uint8_t v___x_1964_; 
lean_inc(v_a_1953_);
lean_inc_ref(v_s_1929_);
v___x_1956_ = l___private_Lean_Level_0__Lean_Level_substParams_go(v_s_1929_, v_a_1953_);
lean_inc(v_a_1954_);
v___x_1957_ = l___private_Lean_Level_0__Lean_Level_substParams_go(v_s_1929_, v_a_1954_);
v___x_1962_ = lean_ptr_addr(v_a_1953_);
v___x_1963_ = lean_ptr_addr(v___x_1956_);
v___x_1964_ = lean_usize_dec_eq(v___x_1962_, v___x_1963_);
if (v___x_1964_ == 0)
{
v___y_1959_ = v___x_1964_;
goto v___jp_1958_;
}
else
{
size_t v___x_1965_; size_t v___x_1966_; uint8_t v___x_1967_; 
v___x_1965_ = lean_ptr_addr(v_a_1954_);
v___x_1966_ = lean_ptr_addr(v___x_1957_);
v___x_1967_ = lean_usize_dec_eq(v___x_1965_, v___x_1966_);
v___y_1959_ = v___x_1967_;
goto v___jp_1958_;
}
v___jp_1958_:
{
if (v___y_1959_ == 0)
{
lean_object* v___x_1960_; 
lean_dec_ref(v_u_1930_);
v___x_1960_ = l_Lean_mkLevelIMax_x27(v___x_1956_, v___x_1957_);
return v___x_1960_;
}
else
{
lean_object* v___x_1961_; 
v___x_1961_ = l_Lean_simpLevelIMax_x27(v___x_1956_, v___x_1957_, v_u_1930_);
lean_dec_ref(v_u_1930_);
return v___x_1961_;
}
}
}
}
case 4:
{
lean_object* v_a_1968_; lean_object* v___x_1969_; 
v_a_1968_ = lean_ctor_get(v_u_1930_, 0);
lean_inc(v_a_1968_);
v___x_1969_ = lean_apply_1(v_s_1929_, v_a_1968_);
if (lean_obj_tag(v___x_1969_) == 0)
{
return v_u_1930_;
}
else
{
lean_object* v_val_1970_; 
lean_dec_ref(v_u_1930_);
v_val_1970_ = lean_ctor_get(v___x_1969_, 0);
lean_inc(v_val_1970_);
lean_dec_ref(v___x_1969_);
return v_val_1970_;
}
}
default: 
{
lean_dec_ref(v_s_1929_);
return v_u_1930_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_substParams(lean_object* v_u_1971_, lean_object* v_s_1972_){
_start:
{
lean_object* v___x_1973_; 
v___x_1973_ = l___private_Lean_Level_0__Lean_Level_substParams_go(v_s_1972_, v_u_1971_);
return v___x_1973_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_getParamSubst(lean_object* v_x_1974_, lean_object* v_x_1975_, lean_object* v_x_1976_){
_start:
{
if (lean_obj_tag(v_x_1974_) == 1)
{
if (lean_obj_tag(v_x_1975_) == 1)
{
lean_object* v_head_1977_; lean_object* v_tail_1978_; lean_object* v_head_1979_; lean_object* v_tail_1980_; uint8_t v___x_1981_; 
v_head_1977_ = lean_ctor_get(v_x_1974_, 0);
v_tail_1978_ = lean_ctor_get(v_x_1974_, 1);
v_head_1979_ = lean_ctor_get(v_x_1975_, 0);
v_tail_1980_ = lean_ctor_get(v_x_1975_, 1);
v___x_1981_ = lean_name_eq(v_head_1977_, v_x_1976_);
if (v___x_1981_ == 0)
{
v_x_1974_ = v_tail_1978_;
v_x_1975_ = v_tail_1980_;
goto _start;
}
else
{
lean_object* v___x_1983_; 
lean_inc(v_head_1979_);
v___x_1983_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1983_, 0, v_head_1979_);
return v___x_1983_;
}
}
else
{
lean_object* v___x_1984_; 
v___x_1984_ = lean_box(0);
return v___x_1984_;
}
}
else
{
lean_object* v___x_1985_; 
v___x_1985_ = lean_box(0);
return v___x_1985_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_getParamSubst___boxed(lean_object* v_x_1986_, lean_object* v_x_1987_, lean_object* v_x_1988_){
_start:
{
lean_object* v_res_1989_; 
v_res_1989_ = l_Lean_Level_getParamSubst(v_x_1986_, v_x_1987_, v_x_1988_);
lean_dec(v_x_1988_);
lean_dec(v_x_1987_);
lean_dec(v_x_1986_);
return v_res_1989_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_instantiateParams(lean_object* v_u_1990_, lean_object* v_paramNames_1991_, lean_object* v_vs_1992_){
_start:
{
lean_object* v___x_1993_; lean_object* v___x_1994_; 
v___x_1993_ = lean_alloc_closure((void*)(l_Lean_Level_getParamSubst___boxed), 3, 2);
lean_closure_set(v___x_1993_, 0, v_paramNames_1991_);
lean_closure_set(v___x_1993_, 1, v_vs_1992_);
v___x_1994_ = l___private_Lean_Level_0__Lean_Level_substParams_go(v___x_1993_, v_u_1990_);
return v___x_1994_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Level_0__Lean_Level_geq_go(lean_object* v_u_1995_, lean_object* v_v_1996_){
_start:
{
uint8_t v___y_1998_; uint8_t v___y_2012_; lean_object* v_u_u2081_2014_; lean_object* v_u_u2082_2015_; lean_object* v_v_2016_; uint8_t v___x_2019_; 
v___x_2019_ = lean_level_eq(v_u_1995_, v_v_1996_);
if (v___x_2019_ == 0)
{
switch(lean_obj_tag(v_v_1996_))
{
case 0:
{
uint8_t v___x_2020_; 
v___x_2020_ = 1;
return v___x_2020_;
}
case 2:
{
lean_object* v_a_2021_; lean_object* v_a_2022_; uint8_t v___x_2023_; 
v_a_2021_ = lean_ctor_get(v_v_1996_, 0);
v_a_2022_ = lean_ctor_get(v_v_1996_, 1);
v___x_2023_ = l___private_Lean_Level_0__Lean_Level_geq_go(v_u_1995_, v_a_2021_);
if (v___x_2023_ == 0)
{
return v___x_2023_;
}
else
{
v_v_1996_ = v_a_2022_;
goto _start;
}
}
case 1:
{
switch(lean_obj_tag(v_u_1995_))
{
case 2:
{
lean_object* v_a_2025_; lean_object* v_a_2026_; 
v_a_2025_ = lean_ctor_get(v_u_1995_, 0);
v_a_2026_ = lean_ctor_get(v_u_1995_, 1);
v_u_u2081_2014_ = v_a_2025_;
v_u_u2082_2015_ = v_a_2026_;
v_v_2016_ = v_v_1996_;
goto v___jp_2013_;
}
case 3:
{
lean_object* v_a_2027_; 
v_a_2027_ = lean_ctor_get(v_u_1995_, 1);
v_u_1995_ = v_a_2027_;
goto _start;
}
case 1:
{
lean_object* v_a_2029_; lean_object* v_a_2030_; 
v_a_2029_ = lean_ctor_get(v_v_1996_, 0);
v_a_2030_ = lean_ctor_get(v_u_1995_, 0);
v_u_1995_ = v_a_2030_;
v_v_1996_ = v_a_2029_;
goto _start;
}
default: 
{
goto v___jp_2002_;
}
}
}
default: 
{
switch(lean_obj_tag(v_u_1995_))
{
case 2:
{
lean_object* v_a_2032_; lean_object* v_a_2033_; 
v_a_2032_ = lean_ctor_get(v_u_1995_, 0);
v_a_2033_ = lean_ctor_get(v_u_1995_, 1);
v_u_u2081_2014_ = v_a_2032_;
v_u_u2082_2015_ = v_a_2033_;
v_v_2016_ = v_v_1996_;
goto v___jp_2013_;
}
case 3:
{
lean_object* v_a_2034_; 
v_a_2034_ = lean_ctor_get(v_u_1995_, 1);
v_u_1995_ = v_a_2034_;
goto _start;
}
default: 
{
goto v___jp_2002_;
}
}
}
}
}
else
{
return v___x_2019_;
}
v___jp_1997_:
{
if (v___y_1998_ == 0)
{
return v___y_1998_;
}
else
{
lean_object* v___x_1999_; lean_object* v___x_2000_; uint8_t v___x_2001_; 
v___x_1999_ = l_Lean_Level_getOffset(v_v_1996_);
v___x_2000_ = l_Lean_Level_getOffset(v_u_1995_);
v___x_2001_ = lean_nat_dec_le(v___x_1999_, v___x_2000_);
lean_dec(v___x_2000_);
lean_dec(v___x_1999_);
return v___x_2001_;
}
}
v___jp_2002_:
{
if (lean_obj_tag(v_v_1996_) == 3)
{
lean_object* v_a_2003_; lean_object* v_a_2004_; uint8_t v___x_2005_; 
v_a_2003_ = lean_ctor_get(v_v_1996_, 0);
v_a_2004_ = lean_ctor_get(v_v_1996_, 1);
v___x_2005_ = l___private_Lean_Level_0__Lean_Level_geq_go(v_u_1995_, v_a_2003_);
if (v___x_2005_ == 0)
{
return v___x_2005_;
}
else
{
v_v_1996_ = v_a_2004_;
goto _start;
}
}
else
{
lean_object* v_v_x27_2007_; lean_object* v___x_2008_; uint8_t v___x_2009_; 
v_v_x27_2007_ = l_Lean_Level_getLevelOffset(v_v_1996_);
v___x_2008_ = l_Lean_Level_getLevelOffset(v_u_1995_);
v___x_2009_ = lean_level_eq(v___x_2008_, v_v_x27_2007_);
lean_dec(v___x_2008_);
if (v___x_2009_ == 0)
{
uint8_t v___x_2010_; 
v___x_2010_ = l_Lean_Level_isZero(v_v_x27_2007_);
lean_dec(v_v_x27_2007_);
v___y_1998_ = v___x_2010_;
goto v___jp_1997_;
}
else
{
lean_dec(v_v_x27_2007_);
v___y_1998_ = v___x_2009_;
goto v___jp_1997_;
}
}
}
v___jp_2011_:
{
if (v___y_2012_ == 0)
{
goto v___jp_2002_;
}
else
{
return v___y_2012_;
}
}
v___jp_2013_:
{
uint8_t v___x_2017_; 
v___x_2017_ = l___private_Lean_Level_0__Lean_Level_geq_go(v_u_u2081_2014_, v_v_2016_);
if (v___x_2017_ == 0)
{
uint8_t v___x_2018_; 
v___x_2018_ = l___private_Lean_Level_0__Lean_Level_geq_go(v_u_u2082_2015_, v_v_2016_);
v___y_2012_ = v___x_2018_;
goto v___jp_2011_;
}
else
{
v___y_2012_ = v___x_2017_;
goto v___jp_2011_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_geq_go___boxed(lean_object* v_u_2036_, lean_object* v_v_2037_){
_start:
{
uint8_t v_res_2038_; lean_object* v_r_2039_; 
v_res_2038_ = l___private_Lean_Level_0__Lean_Level_geq_go(v_u_2036_, v_v_2037_);
lean_dec(v_v_2037_);
lean_dec(v_u_2036_);
v_r_2039_ = lean_box(v_res_2038_);
return v_r_2039_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_geq_go_match__1_splitter___redArg(lean_object* v_u_2040_, lean_object* v_v_2041_, lean_object* v_h__1_2042_, lean_object* v_h__2_2043_, lean_object* v_h__3_2044_, lean_object* v_h__4_2045_, lean_object* v_h__5_2046_, lean_object* v_h__6_2047_){
_start:
{
switch(lean_obj_tag(v_v_2041_))
{
case 0:
{
lean_object* v___x_2048_; 
lean_dec(v_h__6_2047_);
lean_dec(v_h__5_2046_);
lean_dec(v_h__4_2045_);
lean_dec(v_h__3_2044_);
lean_dec(v_h__2_2043_);
v___x_2048_ = lean_apply_1(v_h__1_2042_, v_u_2040_);
return v___x_2048_;
}
case 2:
{
lean_object* v_a_2049_; lean_object* v_a_2050_; lean_object* v___x_2051_; 
lean_dec(v_h__6_2047_);
lean_dec(v_h__5_2046_);
lean_dec(v_h__4_2045_);
lean_dec(v_h__3_2044_);
lean_dec(v_h__1_2042_);
v_a_2049_ = lean_ctor_get(v_v_2041_, 0);
lean_inc(v_a_2049_);
v_a_2050_ = lean_ctor_get(v_v_2041_, 1);
lean_inc(v_a_2050_);
lean_dec_ref(v_v_2041_);
v___x_2051_ = lean_apply_3(v_h__2_2043_, v_u_2040_, v_a_2049_, v_a_2050_);
return v___x_2051_;
}
case 1:
{
lean_dec(v_h__2_2043_);
lean_dec(v_h__1_2042_);
switch(lean_obj_tag(v_u_2040_))
{
case 2:
{
lean_object* v_a_2052_; lean_object* v_a_2053_; lean_object* v___x_2054_; 
lean_dec(v_h__6_2047_);
lean_dec(v_h__5_2046_);
lean_dec(v_h__4_2045_);
v_a_2052_ = lean_ctor_get(v_u_2040_, 0);
lean_inc(v_a_2052_);
v_a_2053_ = lean_ctor_get(v_u_2040_, 1);
lean_inc(v_a_2053_);
lean_dec_ref(v_u_2040_);
v___x_2054_ = lean_apply_5(v_h__3_2044_, v_a_2052_, v_a_2053_, v_v_2041_, lean_box(0), lean_box(0));
return v___x_2054_;
}
case 3:
{
lean_object* v_a_2055_; lean_object* v_a_2056_; lean_object* v___x_2057_; 
lean_dec(v_h__6_2047_);
lean_dec(v_h__5_2046_);
lean_dec(v_h__3_2044_);
v_a_2055_ = lean_ctor_get(v_u_2040_, 0);
lean_inc(v_a_2055_);
v_a_2056_ = lean_ctor_get(v_u_2040_, 1);
lean_inc(v_a_2056_);
lean_dec_ref(v_u_2040_);
v___x_2057_ = lean_apply_5(v_h__4_2045_, v_a_2055_, v_a_2056_, v_v_2041_, lean_box(0), lean_box(0));
return v___x_2057_;
}
case 1:
{
lean_object* v_a_2058_; lean_object* v_a_2059_; lean_object* v___x_2060_; 
lean_dec(v_h__6_2047_);
lean_dec(v_h__4_2045_);
lean_dec(v_h__3_2044_);
v_a_2058_ = lean_ctor_get(v_v_2041_, 0);
lean_inc(v_a_2058_);
lean_dec_ref(v_v_2041_);
v_a_2059_ = lean_ctor_get(v_u_2040_, 0);
lean_inc(v_a_2059_);
lean_dec_ref(v_u_2040_);
v___x_2060_ = lean_apply_2(v_h__5_2046_, v_a_2059_, v_a_2058_);
return v___x_2060_;
}
default: 
{
lean_object* v___x_2061_; 
lean_dec(v_h__5_2046_);
lean_dec(v_h__4_2045_);
lean_dec(v_h__3_2044_);
v___x_2061_ = lean_apply_7(v_h__6_2047_, v_u_2040_, v_v_2041_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_2061_;
}
}
}
default: 
{
lean_dec(v_h__5_2046_);
lean_dec(v_h__2_2043_);
lean_dec(v_h__1_2042_);
switch(lean_obj_tag(v_u_2040_))
{
case 2:
{
lean_object* v_a_2062_; lean_object* v_a_2063_; lean_object* v___x_2064_; 
lean_dec(v_h__6_2047_);
lean_dec(v_h__4_2045_);
v_a_2062_ = lean_ctor_get(v_u_2040_, 0);
lean_inc(v_a_2062_);
v_a_2063_ = lean_ctor_get(v_u_2040_, 1);
lean_inc(v_a_2063_);
lean_dec_ref(v_u_2040_);
v___x_2064_ = lean_apply_5(v_h__3_2044_, v_a_2062_, v_a_2063_, v_v_2041_, lean_box(0), lean_box(0));
return v___x_2064_;
}
case 3:
{
lean_object* v_a_2065_; lean_object* v_a_2066_; lean_object* v___x_2067_; 
lean_dec(v_h__6_2047_);
lean_dec(v_h__3_2044_);
v_a_2065_ = lean_ctor_get(v_u_2040_, 0);
lean_inc(v_a_2065_);
v_a_2066_ = lean_ctor_get(v_u_2040_, 1);
lean_inc(v_a_2066_);
lean_dec_ref(v_u_2040_);
v___x_2067_ = lean_apply_5(v_h__4_2045_, v_a_2065_, v_a_2066_, v_v_2041_, lean_box(0), lean_box(0));
return v___x_2067_;
}
default: 
{
lean_object* v___x_2068_; 
lean_dec(v_h__4_2045_);
lean_dec(v_h__3_2044_);
v___x_2068_ = lean_apply_7(v_h__6_2047_, v_u_2040_, v_v_2041_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_2068_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_geq_go_match__1_splitter(lean_object* v_motive_2069_, lean_object* v_u_2070_, lean_object* v_v_2071_, lean_object* v_h__1_2072_, lean_object* v_h__2_2073_, lean_object* v_h__3_2074_, lean_object* v_h__4_2075_, lean_object* v_h__5_2076_, lean_object* v_h__6_2077_){
_start:
{
switch(lean_obj_tag(v_v_2071_))
{
case 0:
{
lean_object* v___x_2078_; 
lean_dec(v_h__6_2077_);
lean_dec(v_h__5_2076_);
lean_dec(v_h__4_2075_);
lean_dec(v_h__3_2074_);
lean_dec(v_h__2_2073_);
v___x_2078_ = lean_apply_1(v_h__1_2072_, v_u_2070_);
return v___x_2078_;
}
case 2:
{
lean_object* v_a_2079_; lean_object* v_a_2080_; lean_object* v___x_2081_; 
lean_dec(v_h__6_2077_);
lean_dec(v_h__5_2076_);
lean_dec(v_h__4_2075_);
lean_dec(v_h__3_2074_);
lean_dec(v_h__1_2072_);
v_a_2079_ = lean_ctor_get(v_v_2071_, 0);
lean_inc(v_a_2079_);
v_a_2080_ = lean_ctor_get(v_v_2071_, 1);
lean_inc(v_a_2080_);
lean_dec_ref(v_v_2071_);
v___x_2081_ = lean_apply_3(v_h__2_2073_, v_u_2070_, v_a_2079_, v_a_2080_);
return v___x_2081_;
}
case 1:
{
lean_dec(v_h__2_2073_);
lean_dec(v_h__1_2072_);
switch(lean_obj_tag(v_u_2070_))
{
case 2:
{
lean_object* v_a_2082_; lean_object* v_a_2083_; lean_object* v___x_2084_; 
lean_dec(v_h__6_2077_);
lean_dec(v_h__5_2076_);
lean_dec(v_h__4_2075_);
v_a_2082_ = lean_ctor_get(v_u_2070_, 0);
lean_inc(v_a_2082_);
v_a_2083_ = lean_ctor_get(v_u_2070_, 1);
lean_inc(v_a_2083_);
lean_dec_ref(v_u_2070_);
v___x_2084_ = lean_apply_5(v_h__3_2074_, v_a_2082_, v_a_2083_, v_v_2071_, lean_box(0), lean_box(0));
return v___x_2084_;
}
case 3:
{
lean_object* v_a_2085_; lean_object* v_a_2086_; lean_object* v___x_2087_; 
lean_dec(v_h__6_2077_);
lean_dec(v_h__5_2076_);
lean_dec(v_h__3_2074_);
v_a_2085_ = lean_ctor_get(v_u_2070_, 0);
lean_inc(v_a_2085_);
v_a_2086_ = lean_ctor_get(v_u_2070_, 1);
lean_inc(v_a_2086_);
lean_dec_ref(v_u_2070_);
v___x_2087_ = lean_apply_5(v_h__4_2075_, v_a_2085_, v_a_2086_, v_v_2071_, lean_box(0), lean_box(0));
return v___x_2087_;
}
case 1:
{
lean_object* v_a_2088_; lean_object* v_a_2089_; lean_object* v___x_2090_; 
lean_dec(v_h__6_2077_);
lean_dec(v_h__4_2075_);
lean_dec(v_h__3_2074_);
v_a_2088_ = lean_ctor_get(v_v_2071_, 0);
lean_inc(v_a_2088_);
lean_dec_ref(v_v_2071_);
v_a_2089_ = lean_ctor_get(v_u_2070_, 0);
lean_inc(v_a_2089_);
lean_dec_ref(v_u_2070_);
v___x_2090_ = lean_apply_2(v_h__5_2076_, v_a_2089_, v_a_2088_);
return v___x_2090_;
}
default: 
{
lean_object* v___x_2091_; 
lean_dec(v_h__5_2076_);
lean_dec(v_h__4_2075_);
lean_dec(v_h__3_2074_);
v___x_2091_ = lean_apply_7(v_h__6_2077_, v_u_2070_, v_v_2071_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_2091_;
}
}
}
default: 
{
lean_dec(v_h__5_2076_);
lean_dec(v_h__2_2073_);
lean_dec(v_h__1_2072_);
switch(lean_obj_tag(v_u_2070_))
{
case 2:
{
lean_object* v_a_2092_; lean_object* v_a_2093_; lean_object* v___x_2094_; 
lean_dec(v_h__6_2077_);
lean_dec(v_h__4_2075_);
v_a_2092_ = lean_ctor_get(v_u_2070_, 0);
lean_inc(v_a_2092_);
v_a_2093_ = lean_ctor_get(v_u_2070_, 1);
lean_inc(v_a_2093_);
lean_dec_ref(v_u_2070_);
v___x_2094_ = lean_apply_5(v_h__3_2074_, v_a_2092_, v_a_2093_, v_v_2071_, lean_box(0), lean_box(0));
return v___x_2094_;
}
case 3:
{
lean_object* v_a_2095_; lean_object* v_a_2096_; lean_object* v___x_2097_; 
lean_dec(v_h__6_2077_);
lean_dec(v_h__3_2074_);
v_a_2095_ = lean_ctor_get(v_u_2070_, 0);
lean_inc(v_a_2095_);
v_a_2096_ = lean_ctor_get(v_u_2070_, 1);
lean_inc(v_a_2096_);
lean_dec_ref(v_u_2070_);
v___x_2097_ = lean_apply_5(v_h__4_2075_, v_a_2095_, v_a_2096_, v_v_2071_, lean_box(0), lean_box(0));
return v___x_2097_;
}
default: 
{
lean_object* v___x_2098_; 
lean_dec(v_h__4_2075_);
lean_dec(v_h__3_2074_);
v___x_2098_ = lean_apply_7(v_h__6_2077_, v_u_2070_, v_v_2071_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_2098_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_isIMax_match__1_splitter___redArg(lean_object* v_x_2099_, lean_object* v_h__1_2100_, lean_object* v_h__2_2101_){
_start:
{
if (lean_obj_tag(v_x_2099_) == 3)
{
lean_object* v_a_2102_; lean_object* v_a_2103_; lean_object* v___x_2104_; 
lean_dec(v_h__2_2101_);
v_a_2102_ = lean_ctor_get(v_x_2099_, 0);
lean_inc(v_a_2102_);
v_a_2103_ = lean_ctor_get(v_x_2099_, 1);
lean_inc(v_a_2103_);
lean_dec_ref(v_x_2099_);
v___x_2104_ = lean_apply_2(v_h__1_2100_, v_a_2102_, v_a_2103_);
return v___x_2104_;
}
else
{
lean_object* v___x_2105_; 
lean_dec(v_h__1_2100_);
v___x_2105_ = lean_apply_2(v_h__2_2101_, v_x_2099_, lean_box(0));
return v___x_2105_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_isIMax_match__1_splitter(lean_object* v_motive_2106_, lean_object* v_x_2107_, lean_object* v_h__1_2108_, lean_object* v_h__2_2109_){
_start:
{
if (lean_obj_tag(v_x_2107_) == 3)
{
lean_object* v_a_2110_; lean_object* v_a_2111_; lean_object* v___x_2112_; 
lean_dec(v_h__2_2109_);
v_a_2110_ = lean_ctor_get(v_x_2107_, 0);
lean_inc(v_a_2110_);
v_a_2111_ = lean_ctor_get(v_x_2107_, 1);
lean_inc(v_a_2111_);
lean_dec_ref(v_x_2107_);
v___x_2112_ = lean_apply_2(v_h__1_2108_, v_a_2110_, v_a_2111_);
return v___x_2112_;
}
else
{
lean_object* v___x_2113_; 
lean_dec(v_h__1_2108_);
v___x_2113_ = lean_apply_2(v_h__2_2109_, v_x_2107_, lean_box(0));
return v___x_2113_;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Level_geq(lean_object* v_u_2114_, lean_object* v_v_2115_){
_start:
{
lean_object* v___x_2116_; lean_object* v___x_2117_; uint8_t v___x_2118_; 
v___x_2116_ = l_Lean_Level_normalize(v_u_2114_);
v___x_2117_ = l_Lean_Level_normalize(v_v_2115_);
v___x_2118_ = l___private_Lean_Level_0__Lean_Level_geq_go(v___x_2116_, v___x_2117_);
lean_dec(v___x_2117_);
lean_dec(v___x_2116_);
return v___x_2118_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_geq___boxed(lean_object* v_u_2119_, lean_object* v_v_2120_){
_start:
{
uint8_t v_res_2121_; lean_object* v_r_2122_; 
v_res_2121_ = l_Lean_Level_geq(v_u_2119_, v_v_2120_);
lean_dec(v_v_2120_);
lean_dec(v_u_2119_);
v_r_2122_ = lean_box(v_res_2121_);
return v_r_2122_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Level_collectMVars_spec__1___redArg(lean_object* v_k_2123_, lean_object* v_v_2124_, lean_object* v_t_2125_){
_start:
{
if (lean_obj_tag(v_t_2125_) == 0)
{
lean_object* v_size_2126_; lean_object* v_k_2127_; lean_object* v_v_2128_; lean_object* v_l_2129_; lean_object* v_r_2130_; lean_object* v___x_2132_; uint8_t v_isShared_2133_; uint8_t v_isSharedCheck_2410_; 
v_size_2126_ = lean_ctor_get(v_t_2125_, 0);
v_k_2127_ = lean_ctor_get(v_t_2125_, 1);
v_v_2128_ = lean_ctor_get(v_t_2125_, 2);
v_l_2129_ = lean_ctor_get(v_t_2125_, 3);
v_r_2130_ = lean_ctor_get(v_t_2125_, 4);
v_isSharedCheck_2410_ = !lean_is_exclusive(v_t_2125_);
if (v_isSharedCheck_2410_ == 0)
{
v___x_2132_ = v_t_2125_;
v_isShared_2133_ = v_isSharedCheck_2410_;
goto v_resetjp_2131_;
}
else
{
lean_inc(v_r_2130_);
lean_inc(v_l_2129_);
lean_inc(v_v_2128_);
lean_inc(v_k_2127_);
lean_inc(v_size_2126_);
lean_dec(v_t_2125_);
v___x_2132_ = lean_box(0);
v_isShared_2133_ = v_isSharedCheck_2410_;
goto v_resetjp_2131_;
}
v_resetjp_2131_:
{
uint8_t v___x_2134_; 
v___x_2134_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2123_, v_k_2127_);
switch(v___x_2134_)
{
case 0:
{
lean_object* v_impl_2135_; lean_object* v___x_2136_; 
lean_dec(v_size_2126_);
v_impl_2135_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Level_collectMVars_spec__1___redArg(v_k_2123_, v_v_2124_, v_l_2129_);
v___x_2136_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_2130_) == 0)
{
lean_object* v_size_2137_; lean_object* v_size_2138_; lean_object* v_k_2139_; lean_object* v_v_2140_; lean_object* v_l_2141_; lean_object* v_r_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; uint8_t v___x_2145_; 
v_size_2137_ = lean_ctor_get(v_r_2130_, 0);
v_size_2138_ = lean_ctor_get(v_impl_2135_, 0);
lean_inc(v_size_2138_);
v_k_2139_ = lean_ctor_get(v_impl_2135_, 1);
lean_inc(v_k_2139_);
v_v_2140_ = lean_ctor_get(v_impl_2135_, 2);
lean_inc(v_v_2140_);
v_l_2141_ = lean_ctor_get(v_impl_2135_, 3);
lean_inc(v_l_2141_);
v_r_2142_ = lean_ctor_get(v_impl_2135_, 4);
lean_inc(v_r_2142_);
v___x_2143_ = lean_unsigned_to_nat(3u);
v___x_2144_ = lean_nat_mul(v___x_2143_, v_size_2137_);
v___x_2145_ = lean_nat_dec_lt(v___x_2144_, v_size_2138_);
lean_dec(v___x_2144_);
if (v___x_2145_ == 0)
{
lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2149_; 
lean_dec(v_r_2142_);
lean_dec(v_l_2141_);
lean_dec(v_v_2140_);
lean_dec(v_k_2139_);
v___x_2146_ = lean_nat_add(v___x_2136_, v_size_2138_);
lean_dec(v_size_2138_);
v___x_2147_ = lean_nat_add(v___x_2146_, v_size_2137_);
lean_dec(v___x_2146_);
if (v_isShared_2133_ == 0)
{
lean_ctor_set(v___x_2132_, 3, v_impl_2135_);
lean_ctor_set(v___x_2132_, 0, v___x_2147_);
v___x_2149_ = v___x_2132_;
goto v_reusejp_2148_;
}
else
{
lean_object* v_reuseFailAlloc_2150_; 
v_reuseFailAlloc_2150_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2150_, 0, v___x_2147_);
lean_ctor_set(v_reuseFailAlloc_2150_, 1, v_k_2127_);
lean_ctor_set(v_reuseFailAlloc_2150_, 2, v_v_2128_);
lean_ctor_set(v_reuseFailAlloc_2150_, 3, v_impl_2135_);
lean_ctor_set(v_reuseFailAlloc_2150_, 4, v_r_2130_);
v___x_2149_ = v_reuseFailAlloc_2150_;
goto v_reusejp_2148_;
}
v_reusejp_2148_:
{
return v___x_2149_;
}
}
else
{
lean_object* v___x_2152_; uint8_t v_isShared_2153_; uint8_t v_isSharedCheck_2216_; 
v_isSharedCheck_2216_ = !lean_is_exclusive(v_impl_2135_);
if (v_isSharedCheck_2216_ == 0)
{
lean_object* v_unused_2217_; lean_object* v_unused_2218_; lean_object* v_unused_2219_; lean_object* v_unused_2220_; lean_object* v_unused_2221_; 
v_unused_2217_ = lean_ctor_get(v_impl_2135_, 4);
lean_dec(v_unused_2217_);
v_unused_2218_ = lean_ctor_get(v_impl_2135_, 3);
lean_dec(v_unused_2218_);
v_unused_2219_ = lean_ctor_get(v_impl_2135_, 2);
lean_dec(v_unused_2219_);
v_unused_2220_ = lean_ctor_get(v_impl_2135_, 1);
lean_dec(v_unused_2220_);
v_unused_2221_ = lean_ctor_get(v_impl_2135_, 0);
lean_dec(v_unused_2221_);
v___x_2152_ = v_impl_2135_;
v_isShared_2153_ = v_isSharedCheck_2216_;
goto v_resetjp_2151_;
}
else
{
lean_dec(v_impl_2135_);
v___x_2152_ = lean_box(0);
v_isShared_2153_ = v_isSharedCheck_2216_;
goto v_resetjp_2151_;
}
v_resetjp_2151_:
{
lean_object* v_size_2154_; lean_object* v_size_2155_; lean_object* v_k_2156_; lean_object* v_v_2157_; lean_object* v_l_2158_; lean_object* v_r_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; uint8_t v___x_2162_; 
v_size_2154_ = lean_ctor_get(v_l_2141_, 0);
v_size_2155_ = lean_ctor_get(v_r_2142_, 0);
v_k_2156_ = lean_ctor_get(v_r_2142_, 1);
v_v_2157_ = lean_ctor_get(v_r_2142_, 2);
v_l_2158_ = lean_ctor_get(v_r_2142_, 3);
v_r_2159_ = lean_ctor_get(v_r_2142_, 4);
v___x_2160_ = lean_unsigned_to_nat(2u);
v___x_2161_ = lean_nat_mul(v___x_2160_, v_size_2154_);
v___x_2162_ = lean_nat_dec_lt(v_size_2155_, v___x_2161_);
lean_dec(v___x_2161_);
if (v___x_2162_ == 0)
{
lean_object* v___x_2164_; uint8_t v_isShared_2165_; uint8_t v_isSharedCheck_2191_; 
lean_inc(v_r_2159_);
lean_inc(v_l_2158_);
lean_inc(v_v_2157_);
lean_inc(v_k_2156_);
v_isSharedCheck_2191_ = !lean_is_exclusive(v_r_2142_);
if (v_isSharedCheck_2191_ == 0)
{
lean_object* v_unused_2192_; lean_object* v_unused_2193_; lean_object* v_unused_2194_; lean_object* v_unused_2195_; lean_object* v_unused_2196_; 
v_unused_2192_ = lean_ctor_get(v_r_2142_, 4);
lean_dec(v_unused_2192_);
v_unused_2193_ = lean_ctor_get(v_r_2142_, 3);
lean_dec(v_unused_2193_);
v_unused_2194_ = lean_ctor_get(v_r_2142_, 2);
lean_dec(v_unused_2194_);
v_unused_2195_ = lean_ctor_get(v_r_2142_, 1);
lean_dec(v_unused_2195_);
v_unused_2196_ = lean_ctor_get(v_r_2142_, 0);
lean_dec(v_unused_2196_);
v___x_2164_ = v_r_2142_;
v_isShared_2165_ = v_isSharedCheck_2191_;
goto v_resetjp_2163_;
}
else
{
lean_dec(v_r_2142_);
v___x_2164_ = lean_box(0);
v_isShared_2165_ = v_isSharedCheck_2191_;
goto v_resetjp_2163_;
}
v_resetjp_2163_:
{
lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___y_2169_; lean_object* v___y_2170_; lean_object* v___y_2171_; lean_object* v___x_2179_; lean_object* v___y_2181_; 
v___x_2166_ = lean_nat_add(v___x_2136_, v_size_2138_);
lean_dec(v_size_2138_);
v___x_2167_ = lean_nat_add(v___x_2166_, v_size_2137_);
lean_dec(v___x_2166_);
v___x_2179_ = lean_nat_add(v___x_2136_, v_size_2154_);
if (lean_obj_tag(v_l_2158_) == 0)
{
lean_object* v_size_2189_; 
v_size_2189_ = lean_ctor_get(v_l_2158_, 0);
lean_inc(v_size_2189_);
v___y_2181_ = v_size_2189_;
goto v___jp_2180_;
}
else
{
lean_object* v___x_2190_; 
v___x_2190_ = lean_unsigned_to_nat(0u);
v___y_2181_ = v___x_2190_;
goto v___jp_2180_;
}
v___jp_2168_:
{
lean_object* v___x_2172_; lean_object* v___x_2174_; 
v___x_2172_ = lean_nat_add(v___y_2169_, v___y_2171_);
lean_dec(v___y_2171_);
lean_dec(v___y_2169_);
if (v_isShared_2165_ == 0)
{
lean_ctor_set(v___x_2164_, 4, v_r_2130_);
lean_ctor_set(v___x_2164_, 3, v_r_2159_);
lean_ctor_set(v___x_2164_, 2, v_v_2128_);
lean_ctor_set(v___x_2164_, 1, v_k_2127_);
lean_ctor_set(v___x_2164_, 0, v___x_2172_);
v___x_2174_ = v___x_2164_;
goto v_reusejp_2173_;
}
else
{
lean_object* v_reuseFailAlloc_2178_; 
v_reuseFailAlloc_2178_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2178_, 0, v___x_2172_);
lean_ctor_set(v_reuseFailAlloc_2178_, 1, v_k_2127_);
lean_ctor_set(v_reuseFailAlloc_2178_, 2, v_v_2128_);
lean_ctor_set(v_reuseFailAlloc_2178_, 3, v_r_2159_);
lean_ctor_set(v_reuseFailAlloc_2178_, 4, v_r_2130_);
v___x_2174_ = v_reuseFailAlloc_2178_;
goto v_reusejp_2173_;
}
v_reusejp_2173_:
{
lean_object* v___x_2176_; 
if (v_isShared_2153_ == 0)
{
lean_ctor_set(v___x_2152_, 4, v___x_2174_);
lean_ctor_set(v___x_2152_, 3, v___y_2170_);
lean_ctor_set(v___x_2152_, 2, v_v_2157_);
lean_ctor_set(v___x_2152_, 1, v_k_2156_);
lean_ctor_set(v___x_2152_, 0, v___x_2167_);
v___x_2176_ = v___x_2152_;
goto v_reusejp_2175_;
}
else
{
lean_object* v_reuseFailAlloc_2177_; 
v_reuseFailAlloc_2177_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2177_, 0, v___x_2167_);
lean_ctor_set(v_reuseFailAlloc_2177_, 1, v_k_2156_);
lean_ctor_set(v_reuseFailAlloc_2177_, 2, v_v_2157_);
lean_ctor_set(v_reuseFailAlloc_2177_, 3, v___y_2170_);
lean_ctor_set(v_reuseFailAlloc_2177_, 4, v___x_2174_);
v___x_2176_ = v_reuseFailAlloc_2177_;
goto v_reusejp_2175_;
}
v_reusejp_2175_:
{
return v___x_2176_;
}
}
}
v___jp_2180_:
{
lean_object* v___x_2182_; lean_object* v___x_2184_; 
v___x_2182_ = lean_nat_add(v___x_2179_, v___y_2181_);
lean_dec(v___y_2181_);
lean_dec(v___x_2179_);
if (v_isShared_2133_ == 0)
{
lean_ctor_set(v___x_2132_, 4, v_l_2158_);
lean_ctor_set(v___x_2132_, 3, v_l_2141_);
lean_ctor_set(v___x_2132_, 2, v_v_2140_);
lean_ctor_set(v___x_2132_, 1, v_k_2139_);
lean_ctor_set(v___x_2132_, 0, v___x_2182_);
v___x_2184_ = v___x_2132_;
goto v_reusejp_2183_;
}
else
{
lean_object* v_reuseFailAlloc_2188_; 
v_reuseFailAlloc_2188_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2188_, 0, v___x_2182_);
lean_ctor_set(v_reuseFailAlloc_2188_, 1, v_k_2139_);
lean_ctor_set(v_reuseFailAlloc_2188_, 2, v_v_2140_);
lean_ctor_set(v_reuseFailAlloc_2188_, 3, v_l_2141_);
lean_ctor_set(v_reuseFailAlloc_2188_, 4, v_l_2158_);
v___x_2184_ = v_reuseFailAlloc_2188_;
goto v_reusejp_2183_;
}
v_reusejp_2183_:
{
lean_object* v___x_2185_; 
v___x_2185_ = lean_nat_add(v___x_2136_, v_size_2137_);
if (lean_obj_tag(v_r_2159_) == 0)
{
lean_object* v_size_2186_; 
v_size_2186_ = lean_ctor_get(v_r_2159_, 0);
lean_inc(v_size_2186_);
v___y_2169_ = v___x_2185_;
v___y_2170_ = v___x_2184_;
v___y_2171_ = v_size_2186_;
goto v___jp_2168_;
}
else
{
lean_object* v___x_2187_; 
v___x_2187_ = lean_unsigned_to_nat(0u);
v___y_2169_ = v___x_2185_;
v___y_2170_ = v___x_2184_;
v___y_2171_ = v___x_2187_;
goto v___jp_2168_;
}
}
}
}
}
else
{
lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2202_; 
lean_del_object(v___x_2132_);
v___x_2197_ = lean_nat_add(v___x_2136_, v_size_2138_);
lean_dec(v_size_2138_);
v___x_2198_ = lean_nat_add(v___x_2197_, v_size_2137_);
lean_dec(v___x_2197_);
v___x_2199_ = lean_nat_add(v___x_2136_, v_size_2137_);
v___x_2200_ = lean_nat_add(v___x_2199_, v_size_2155_);
lean_dec(v___x_2199_);
lean_inc_ref(v_r_2130_);
if (v_isShared_2153_ == 0)
{
lean_ctor_set(v___x_2152_, 4, v_r_2130_);
lean_ctor_set(v___x_2152_, 3, v_r_2142_);
lean_ctor_set(v___x_2152_, 2, v_v_2128_);
lean_ctor_set(v___x_2152_, 1, v_k_2127_);
lean_ctor_set(v___x_2152_, 0, v___x_2200_);
v___x_2202_ = v___x_2152_;
goto v_reusejp_2201_;
}
else
{
lean_object* v_reuseFailAlloc_2215_; 
v_reuseFailAlloc_2215_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2215_, 0, v___x_2200_);
lean_ctor_set(v_reuseFailAlloc_2215_, 1, v_k_2127_);
lean_ctor_set(v_reuseFailAlloc_2215_, 2, v_v_2128_);
lean_ctor_set(v_reuseFailAlloc_2215_, 3, v_r_2142_);
lean_ctor_set(v_reuseFailAlloc_2215_, 4, v_r_2130_);
v___x_2202_ = v_reuseFailAlloc_2215_;
goto v_reusejp_2201_;
}
v_reusejp_2201_:
{
lean_object* v___x_2204_; uint8_t v_isShared_2205_; uint8_t v_isSharedCheck_2209_; 
v_isSharedCheck_2209_ = !lean_is_exclusive(v_r_2130_);
if (v_isSharedCheck_2209_ == 0)
{
lean_object* v_unused_2210_; lean_object* v_unused_2211_; lean_object* v_unused_2212_; lean_object* v_unused_2213_; lean_object* v_unused_2214_; 
v_unused_2210_ = lean_ctor_get(v_r_2130_, 4);
lean_dec(v_unused_2210_);
v_unused_2211_ = lean_ctor_get(v_r_2130_, 3);
lean_dec(v_unused_2211_);
v_unused_2212_ = lean_ctor_get(v_r_2130_, 2);
lean_dec(v_unused_2212_);
v_unused_2213_ = lean_ctor_get(v_r_2130_, 1);
lean_dec(v_unused_2213_);
v_unused_2214_ = lean_ctor_get(v_r_2130_, 0);
lean_dec(v_unused_2214_);
v___x_2204_ = v_r_2130_;
v_isShared_2205_ = v_isSharedCheck_2209_;
goto v_resetjp_2203_;
}
else
{
lean_dec(v_r_2130_);
v___x_2204_ = lean_box(0);
v_isShared_2205_ = v_isSharedCheck_2209_;
goto v_resetjp_2203_;
}
v_resetjp_2203_:
{
lean_object* v___x_2207_; 
if (v_isShared_2205_ == 0)
{
lean_ctor_set(v___x_2204_, 4, v___x_2202_);
lean_ctor_set(v___x_2204_, 3, v_l_2141_);
lean_ctor_set(v___x_2204_, 2, v_v_2140_);
lean_ctor_set(v___x_2204_, 1, v_k_2139_);
lean_ctor_set(v___x_2204_, 0, v___x_2198_);
v___x_2207_ = v___x_2204_;
goto v_reusejp_2206_;
}
else
{
lean_object* v_reuseFailAlloc_2208_; 
v_reuseFailAlloc_2208_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2208_, 0, v___x_2198_);
lean_ctor_set(v_reuseFailAlloc_2208_, 1, v_k_2139_);
lean_ctor_set(v_reuseFailAlloc_2208_, 2, v_v_2140_);
lean_ctor_set(v_reuseFailAlloc_2208_, 3, v_l_2141_);
lean_ctor_set(v_reuseFailAlloc_2208_, 4, v___x_2202_);
v___x_2207_ = v_reuseFailAlloc_2208_;
goto v_reusejp_2206_;
}
v_reusejp_2206_:
{
return v___x_2207_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_2222_; 
v_l_2222_ = lean_ctor_get(v_impl_2135_, 3);
lean_inc(v_l_2222_);
if (lean_obj_tag(v_l_2222_) == 0)
{
lean_object* v_r_2223_; lean_object* v_k_2224_; lean_object* v_v_2225_; lean_object* v___x_2227_; uint8_t v_isShared_2228_; uint8_t v_isSharedCheck_2236_; 
v_r_2223_ = lean_ctor_get(v_impl_2135_, 4);
v_k_2224_ = lean_ctor_get(v_impl_2135_, 1);
v_v_2225_ = lean_ctor_get(v_impl_2135_, 2);
v_isSharedCheck_2236_ = !lean_is_exclusive(v_impl_2135_);
if (v_isSharedCheck_2236_ == 0)
{
lean_object* v_unused_2237_; lean_object* v_unused_2238_; 
v_unused_2237_ = lean_ctor_get(v_impl_2135_, 3);
lean_dec(v_unused_2237_);
v_unused_2238_ = lean_ctor_get(v_impl_2135_, 0);
lean_dec(v_unused_2238_);
v___x_2227_ = v_impl_2135_;
v_isShared_2228_ = v_isSharedCheck_2236_;
goto v_resetjp_2226_;
}
else
{
lean_inc(v_r_2223_);
lean_inc(v_v_2225_);
lean_inc(v_k_2224_);
lean_dec(v_impl_2135_);
v___x_2227_ = lean_box(0);
v_isShared_2228_ = v_isSharedCheck_2236_;
goto v_resetjp_2226_;
}
v_resetjp_2226_:
{
lean_object* v___x_2229_; lean_object* v___x_2231_; 
v___x_2229_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_2223_);
if (v_isShared_2228_ == 0)
{
lean_ctor_set(v___x_2227_, 3, v_r_2223_);
lean_ctor_set(v___x_2227_, 2, v_v_2128_);
lean_ctor_set(v___x_2227_, 1, v_k_2127_);
lean_ctor_set(v___x_2227_, 0, v___x_2136_);
v___x_2231_ = v___x_2227_;
goto v_reusejp_2230_;
}
else
{
lean_object* v_reuseFailAlloc_2235_; 
v_reuseFailAlloc_2235_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2235_, 0, v___x_2136_);
lean_ctor_set(v_reuseFailAlloc_2235_, 1, v_k_2127_);
lean_ctor_set(v_reuseFailAlloc_2235_, 2, v_v_2128_);
lean_ctor_set(v_reuseFailAlloc_2235_, 3, v_r_2223_);
lean_ctor_set(v_reuseFailAlloc_2235_, 4, v_r_2223_);
v___x_2231_ = v_reuseFailAlloc_2235_;
goto v_reusejp_2230_;
}
v_reusejp_2230_:
{
lean_object* v___x_2233_; 
if (v_isShared_2133_ == 0)
{
lean_ctor_set(v___x_2132_, 4, v___x_2231_);
lean_ctor_set(v___x_2132_, 3, v_l_2222_);
lean_ctor_set(v___x_2132_, 2, v_v_2225_);
lean_ctor_set(v___x_2132_, 1, v_k_2224_);
lean_ctor_set(v___x_2132_, 0, v___x_2229_);
v___x_2233_ = v___x_2132_;
goto v_reusejp_2232_;
}
else
{
lean_object* v_reuseFailAlloc_2234_; 
v_reuseFailAlloc_2234_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2234_, 0, v___x_2229_);
lean_ctor_set(v_reuseFailAlloc_2234_, 1, v_k_2224_);
lean_ctor_set(v_reuseFailAlloc_2234_, 2, v_v_2225_);
lean_ctor_set(v_reuseFailAlloc_2234_, 3, v_l_2222_);
lean_ctor_set(v_reuseFailAlloc_2234_, 4, v___x_2231_);
v___x_2233_ = v_reuseFailAlloc_2234_;
goto v_reusejp_2232_;
}
v_reusejp_2232_:
{
return v___x_2233_;
}
}
}
}
else
{
lean_object* v_r_2239_; 
v_r_2239_ = lean_ctor_get(v_impl_2135_, 4);
lean_inc(v_r_2239_);
if (lean_obj_tag(v_r_2239_) == 0)
{
lean_object* v_k_2240_; lean_object* v_v_2241_; lean_object* v___x_2243_; uint8_t v_isShared_2244_; uint8_t v_isSharedCheck_2264_; 
v_k_2240_ = lean_ctor_get(v_impl_2135_, 1);
v_v_2241_ = lean_ctor_get(v_impl_2135_, 2);
v_isSharedCheck_2264_ = !lean_is_exclusive(v_impl_2135_);
if (v_isSharedCheck_2264_ == 0)
{
lean_object* v_unused_2265_; lean_object* v_unused_2266_; lean_object* v_unused_2267_; 
v_unused_2265_ = lean_ctor_get(v_impl_2135_, 4);
lean_dec(v_unused_2265_);
v_unused_2266_ = lean_ctor_get(v_impl_2135_, 3);
lean_dec(v_unused_2266_);
v_unused_2267_ = lean_ctor_get(v_impl_2135_, 0);
lean_dec(v_unused_2267_);
v___x_2243_ = v_impl_2135_;
v_isShared_2244_ = v_isSharedCheck_2264_;
goto v_resetjp_2242_;
}
else
{
lean_inc(v_v_2241_);
lean_inc(v_k_2240_);
lean_dec(v_impl_2135_);
v___x_2243_ = lean_box(0);
v_isShared_2244_ = v_isSharedCheck_2264_;
goto v_resetjp_2242_;
}
v_resetjp_2242_:
{
lean_object* v_k_2245_; lean_object* v_v_2246_; lean_object* v___x_2248_; uint8_t v_isShared_2249_; uint8_t v_isSharedCheck_2260_; 
v_k_2245_ = lean_ctor_get(v_r_2239_, 1);
v_v_2246_ = lean_ctor_get(v_r_2239_, 2);
v_isSharedCheck_2260_ = !lean_is_exclusive(v_r_2239_);
if (v_isSharedCheck_2260_ == 0)
{
lean_object* v_unused_2261_; lean_object* v_unused_2262_; lean_object* v_unused_2263_; 
v_unused_2261_ = lean_ctor_get(v_r_2239_, 4);
lean_dec(v_unused_2261_);
v_unused_2262_ = lean_ctor_get(v_r_2239_, 3);
lean_dec(v_unused_2262_);
v_unused_2263_ = lean_ctor_get(v_r_2239_, 0);
lean_dec(v_unused_2263_);
v___x_2248_ = v_r_2239_;
v_isShared_2249_ = v_isSharedCheck_2260_;
goto v_resetjp_2247_;
}
else
{
lean_inc(v_v_2246_);
lean_inc(v_k_2245_);
lean_dec(v_r_2239_);
v___x_2248_ = lean_box(0);
v_isShared_2249_ = v_isSharedCheck_2260_;
goto v_resetjp_2247_;
}
v_resetjp_2247_:
{
lean_object* v___x_2250_; lean_object* v___x_2252_; 
v___x_2250_ = lean_unsigned_to_nat(3u);
if (v_isShared_2249_ == 0)
{
lean_ctor_set(v___x_2248_, 4, v_l_2222_);
lean_ctor_set(v___x_2248_, 3, v_l_2222_);
lean_ctor_set(v___x_2248_, 2, v_v_2241_);
lean_ctor_set(v___x_2248_, 1, v_k_2240_);
lean_ctor_set(v___x_2248_, 0, v___x_2136_);
v___x_2252_ = v___x_2248_;
goto v_reusejp_2251_;
}
else
{
lean_object* v_reuseFailAlloc_2259_; 
v_reuseFailAlloc_2259_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2259_, 0, v___x_2136_);
lean_ctor_set(v_reuseFailAlloc_2259_, 1, v_k_2240_);
lean_ctor_set(v_reuseFailAlloc_2259_, 2, v_v_2241_);
lean_ctor_set(v_reuseFailAlloc_2259_, 3, v_l_2222_);
lean_ctor_set(v_reuseFailAlloc_2259_, 4, v_l_2222_);
v___x_2252_ = v_reuseFailAlloc_2259_;
goto v_reusejp_2251_;
}
v_reusejp_2251_:
{
lean_object* v___x_2254_; 
if (v_isShared_2244_ == 0)
{
lean_ctor_set(v___x_2243_, 4, v_l_2222_);
lean_ctor_set(v___x_2243_, 2, v_v_2128_);
lean_ctor_set(v___x_2243_, 1, v_k_2127_);
lean_ctor_set(v___x_2243_, 0, v___x_2136_);
v___x_2254_ = v___x_2243_;
goto v_reusejp_2253_;
}
else
{
lean_object* v_reuseFailAlloc_2258_; 
v_reuseFailAlloc_2258_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2258_, 0, v___x_2136_);
lean_ctor_set(v_reuseFailAlloc_2258_, 1, v_k_2127_);
lean_ctor_set(v_reuseFailAlloc_2258_, 2, v_v_2128_);
lean_ctor_set(v_reuseFailAlloc_2258_, 3, v_l_2222_);
lean_ctor_set(v_reuseFailAlloc_2258_, 4, v_l_2222_);
v___x_2254_ = v_reuseFailAlloc_2258_;
goto v_reusejp_2253_;
}
v_reusejp_2253_:
{
lean_object* v___x_2256_; 
if (v_isShared_2133_ == 0)
{
lean_ctor_set(v___x_2132_, 4, v___x_2254_);
lean_ctor_set(v___x_2132_, 3, v___x_2252_);
lean_ctor_set(v___x_2132_, 2, v_v_2246_);
lean_ctor_set(v___x_2132_, 1, v_k_2245_);
lean_ctor_set(v___x_2132_, 0, v___x_2250_);
v___x_2256_ = v___x_2132_;
goto v_reusejp_2255_;
}
else
{
lean_object* v_reuseFailAlloc_2257_; 
v_reuseFailAlloc_2257_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2257_, 0, v___x_2250_);
lean_ctor_set(v_reuseFailAlloc_2257_, 1, v_k_2245_);
lean_ctor_set(v_reuseFailAlloc_2257_, 2, v_v_2246_);
lean_ctor_set(v_reuseFailAlloc_2257_, 3, v___x_2252_);
lean_ctor_set(v_reuseFailAlloc_2257_, 4, v___x_2254_);
v___x_2256_ = v_reuseFailAlloc_2257_;
goto v_reusejp_2255_;
}
v_reusejp_2255_:
{
return v___x_2256_;
}
}
}
}
}
}
else
{
lean_object* v___x_2268_; lean_object* v___x_2270_; 
v___x_2268_ = lean_unsigned_to_nat(2u);
if (v_isShared_2133_ == 0)
{
lean_ctor_set(v___x_2132_, 4, v_r_2239_);
lean_ctor_set(v___x_2132_, 3, v_impl_2135_);
lean_ctor_set(v___x_2132_, 0, v___x_2268_);
v___x_2270_ = v___x_2132_;
goto v_reusejp_2269_;
}
else
{
lean_object* v_reuseFailAlloc_2271_; 
v_reuseFailAlloc_2271_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2271_, 0, v___x_2268_);
lean_ctor_set(v_reuseFailAlloc_2271_, 1, v_k_2127_);
lean_ctor_set(v_reuseFailAlloc_2271_, 2, v_v_2128_);
lean_ctor_set(v_reuseFailAlloc_2271_, 3, v_impl_2135_);
lean_ctor_set(v_reuseFailAlloc_2271_, 4, v_r_2239_);
v___x_2270_ = v_reuseFailAlloc_2271_;
goto v_reusejp_2269_;
}
v_reusejp_2269_:
{
return v___x_2270_;
}
}
}
}
}
case 1:
{
lean_object* v___x_2273_; 
lean_dec(v_v_2128_);
lean_dec(v_k_2127_);
if (v_isShared_2133_ == 0)
{
lean_ctor_set(v___x_2132_, 2, v_v_2124_);
lean_ctor_set(v___x_2132_, 1, v_k_2123_);
v___x_2273_ = v___x_2132_;
goto v_reusejp_2272_;
}
else
{
lean_object* v_reuseFailAlloc_2274_; 
v_reuseFailAlloc_2274_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2274_, 0, v_size_2126_);
lean_ctor_set(v_reuseFailAlloc_2274_, 1, v_k_2123_);
lean_ctor_set(v_reuseFailAlloc_2274_, 2, v_v_2124_);
lean_ctor_set(v_reuseFailAlloc_2274_, 3, v_l_2129_);
lean_ctor_set(v_reuseFailAlloc_2274_, 4, v_r_2130_);
v___x_2273_ = v_reuseFailAlloc_2274_;
goto v_reusejp_2272_;
}
v_reusejp_2272_:
{
return v___x_2273_;
}
}
default: 
{
lean_object* v_impl_2275_; lean_object* v___x_2276_; 
lean_dec(v_size_2126_);
v_impl_2275_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Level_collectMVars_spec__1___redArg(v_k_2123_, v_v_2124_, v_r_2130_);
v___x_2276_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_2129_) == 0)
{
lean_object* v_size_2277_; lean_object* v_size_2278_; lean_object* v_k_2279_; lean_object* v_v_2280_; lean_object* v_l_2281_; lean_object* v_r_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; uint8_t v___x_2285_; 
v_size_2277_ = lean_ctor_get(v_l_2129_, 0);
v_size_2278_ = lean_ctor_get(v_impl_2275_, 0);
lean_inc(v_size_2278_);
v_k_2279_ = lean_ctor_get(v_impl_2275_, 1);
lean_inc(v_k_2279_);
v_v_2280_ = lean_ctor_get(v_impl_2275_, 2);
lean_inc(v_v_2280_);
v_l_2281_ = lean_ctor_get(v_impl_2275_, 3);
lean_inc(v_l_2281_);
v_r_2282_ = lean_ctor_get(v_impl_2275_, 4);
lean_inc(v_r_2282_);
v___x_2283_ = lean_unsigned_to_nat(3u);
v___x_2284_ = lean_nat_mul(v___x_2283_, v_size_2277_);
v___x_2285_ = lean_nat_dec_lt(v___x_2284_, v_size_2278_);
lean_dec(v___x_2284_);
if (v___x_2285_ == 0)
{
lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2289_; 
lean_dec(v_r_2282_);
lean_dec(v_l_2281_);
lean_dec(v_v_2280_);
lean_dec(v_k_2279_);
v___x_2286_ = lean_nat_add(v___x_2276_, v_size_2277_);
v___x_2287_ = lean_nat_add(v___x_2286_, v_size_2278_);
lean_dec(v_size_2278_);
lean_dec(v___x_2286_);
if (v_isShared_2133_ == 0)
{
lean_ctor_set(v___x_2132_, 4, v_impl_2275_);
lean_ctor_set(v___x_2132_, 0, v___x_2287_);
v___x_2289_ = v___x_2132_;
goto v_reusejp_2288_;
}
else
{
lean_object* v_reuseFailAlloc_2290_; 
v_reuseFailAlloc_2290_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2290_, 0, v___x_2287_);
lean_ctor_set(v_reuseFailAlloc_2290_, 1, v_k_2127_);
lean_ctor_set(v_reuseFailAlloc_2290_, 2, v_v_2128_);
lean_ctor_set(v_reuseFailAlloc_2290_, 3, v_l_2129_);
lean_ctor_set(v_reuseFailAlloc_2290_, 4, v_impl_2275_);
v___x_2289_ = v_reuseFailAlloc_2290_;
goto v_reusejp_2288_;
}
v_reusejp_2288_:
{
return v___x_2289_;
}
}
else
{
lean_object* v___x_2292_; uint8_t v_isShared_2293_; uint8_t v_isSharedCheck_2354_; 
v_isSharedCheck_2354_ = !lean_is_exclusive(v_impl_2275_);
if (v_isSharedCheck_2354_ == 0)
{
lean_object* v_unused_2355_; lean_object* v_unused_2356_; lean_object* v_unused_2357_; lean_object* v_unused_2358_; lean_object* v_unused_2359_; 
v_unused_2355_ = lean_ctor_get(v_impl_2275_, 4);
lean_dec(v_unused_2355_);
v_unused_2356_ = lean_ctor_get(v_impl_2275_, 3);
lean_dec(v_unused_2356_);
v_unused_2357_ = lean_ctor_get(v_impl_2275_, 2);
lean_dec(v_unused_2357_);
v_unused_2358_ = lean_ctor_get(v_impl_2275_, 1);
lean_dec(v_unused_2358_);
v_unused_2359_ = lean_ctor_get(v_impl_2275_, 0);
lean_dec(v_unused_2359_);
v___x_2292_ = v_impl_2275_;
v_isShared_2293_ = v_isSharedCheck_2354_;
goto v_resetjp_2291_;
}
else
{
lean_dec(v_impl_2275_);
v___x_2292_ = lean_box(0);
v_isShared_2293_ = v_isSharedCheck_2354_;
goto v_resetjp_2291_;
}
v_resetjp_2291_:
{
lean_object* v_size_2294_; lean_object* v_k_2295_; lean_object* v_v_2296_; lean_object* v_l_2297_; lean_object* v_r_2298_; lean_object* v_size_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; uint8_t v___x_2302_; 
v_size_2294_ = lean_ctor_get(v_l_2281_, 0);
v_k_2295_ = lean_ctor_get(v_l_2281_, 1);
v_v_2296_ = lean_ctor_get(v_l_2281_, 2);
v_l_2297_ = lean_ctor_get(v_l_2281_, 3);
v_r_2298_ = lean_ctor_get(v_l_2281_, 4);
v_size_2299_ = lean_ctor_get(v_r_2282_, 0);
v___x_2300_ = lean_unsigned_to_nat(2u);
v___x_2301_ = lean_nat_mul(v___x_2300_, v_size_2299_);
v___x_2302_ = lean_nat_dec_lt(v_size_2294_, v___x_2301_);
lean_dec(v___x_2301_);
if (v___x_2302_ == 0)
{
lean_object* v___x_2304_; uint8_t v_isShared_2305_; uint8_t v_isSharedCheck_2330_; 
lean_inc(v_r_2298_);
lean_inc(v_l_2297_);
lean_inc(v_v_2296_);
lean_inc(v_k_2295_);
v_isSharedCheck_2330_ = !lean_is_exclusive(v_l_2281_);
if (v_isSharedCheck_2330_ == 0)
{
lean_object* v_unused_2331_; lean_object* v_unused_2332_; lean_object* v_unused_2333_; lean_object* v_unused_2334_; lean_object* v_unused_2335_; 
v_unused_2331_ = lean_ctor_get(v_l_2281_, 4);
lean_dec(v_unused_2331_);
v_unused_2332_ = lean_ctor_get(v_l_2281_, 3);
lean_dec(v_unused_2332_);
v_unused_2333_ = lean_ctor_get(v_l_2281_, 2);
lean_dec(v_unused_2333_);
v_unused_2334_ = lean_ctor_get(v_l_2281_, 1);
lean_dec(v_unused_2334_);
v_unused_2335_ = lean_ctor_get(v_l_2281_, 0);
lean_dec(v_unused_2335_);
v___x_2304_ = v_l_2281_;
v_isShared_2305_ = v_isSharedCheck_2330_;
goto v_resetjp_2303_;
}
else
{
lean_dec(v_l_2281_);
v___x_2304_ = lean_box(0);
v_isShared_2305_ = v_isSharedCheck_2330_;
goto v_resetjp_2303_;
}
v_resetjp_2303_:
{
lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___y_2309_; lean_object* v___y_2310_; lean_object* v___y_2311_; lean_object* v___y_2320_; 
v___x_2306_ = lean_nat_add(v___x_2276_, v_size_2277_);
v___x_2307_ = lean_nat_add(v___x_2306_, v_size_2278_);
lean_dec(v_size_2278_);
if (lean_obj_tag(v_l_2297_) == 0)
{
lean_object* v_size_2328_; 
v_size_2328_ = lean_ctor_get(v_l_2297_, 0);
lean_inc(v_size_2328_);
v___y_2320_ = v_size_2328_;
goto v___jp_2319_;
}
else
{
lean_object* v___x_2329_; 
v___x_2329_ = lean_unsigned_to_nat(0u);
v___y_2320_ = v___x_2329_;
goto v___jp_2319_;
}
v___jp_2308_:
{
lean_object* v___x_2312_; lean_object* v___x_2314_; 
v___x_2312_ = lean_nat_add(v___y_2310_, v___y_2311_);
lean_dec(v___y_2311_);
lean_dec(v___y_2310_);
if (v_isShared_2305_ == 0)
{
lean_ctor_set(v___x_2304_, 4, v_r_2282_);
lean_ctor_set(v___x_2304_, 3, v_r_2298_);
lean_ctor_set(v___x_2304_, 2, v_v_2280_);
lean_ctor_set(v___x_2304_, 1, v_k_2279_);
lean_ctor_set(v___x_2304_, 0, v___x_2312_);
v___x_2314_ = v___x_2304_;
goto v_reusejp_2313_;
}
else
{
lean_object* v_reuseFailAlloc_2318_; 
v_reuseFailAlloc_2318_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2318_, 0, v___x_2312_);
lean_ctor_set(v_reuseFailAlloc_2318_, 1, v_k_2279_);
lean_ctor_set(v_reuseFailAlloc_2318_, 2, v_v_2280_);
lean_ctor_set(v_reuseFailAlloc_2318_, 3, v_r_2298_);
lean_ctor_set(v_reuseFailAlloc_2318_, 4, v_r_2282_);
v___x_2314_ = v_reuseFailAlloc_2318_;
goto v_reusejp_2313_;
}
v_reusejp_2313_:
{
lean_object* v___x_2316_; 
if (v_isShared_2293_ == 0)
{
lean_ctor_set(v___x_2292_, 4, v___x_2314_);
lean_ctor_set(v___x_2292_, 3, v___y_2309_);
lean_ctor_set(v___x_2292_, 2, v_v_2296_);
lean_ctor_set(v___x_2292_, 1, v_k_2295_);
lean_ctor_set(v___x_2292_, 0, v___x_2307_);
v___x_2316_ = v___x_2292_;
goto v_reusejp_2315_;
}
else
{
lean_object* v_reuseFailAlloc_2317_; 
v_reuseFailAlloc_2317_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2317_, 0, v___x_2307_);
lean_ctor_set(v_reuseFailAlloc_2317_, 1, v_k_2295_);
lean_ctor_set(v_reuseFailAlloc_2317_, 2, v_v_2296_);
lean_ctor_set(v_reuseFailAlloc_2317_, 3, v___y_2309_);
lean_ctor_set(v_reuseFailAlloc_2317_, 4, v___x_2314_);
v___x_2316_ = v_reuseFailAlloc_2317_;
goto v_reusejp_2315_;
}
v_reusejp_2315_:
{
return v___x_2316_;
}
}
}
v___jp_2319_:
{
lean_object* v___x_2321_; lean_object* v___x_2323_; 
v___x_2321_ = lean_nat_add(v___x_2306_, v___y_2320_);
lean_dec(v___y_2320_);
lean_dec(v___x_2306_);
if (v_isShared_2133_ == 0)
{
lean_ctor_set(v___x_2132_, 4, v_l_2297_);
lean_ctor_set(v___x_2132_, 0, v___x_2321_);
v___x_2323_ = v___x_2132_;
goto v_reusejp_2322_;
}
else
{
lean_object* v_reuseFailAlloc_2327_; 
v_reuseFailAlloc_2327_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2327_, 0, v___x_2321_);
lean_ctor_set(v_reuseFailAlloc_2327_, 1, v_k_2127_);
lean_ctor_set(v_reuseFailAlloc_2327_, 2, v_v_2128_);
lean_ctor_set(v_reuseFailAlloc_2327_, 3, v_l_2129_);
lean_ctor_set(v_reuseFailAlloc_2327_, 4, v_l_2297_);
v___x_2323_ = v_reuseFailAlloc_2327_;
goto v_reusejp_2322_;
}
v_reusejp_2322_:
{
lean_object* v___x_2324_; 
v___x_2324_ = lean_nat_add(v___x_2276_, v_size_2299_);
if (lean_obj_tag(v_r_2298_) == 0)
{
lean_object* v_size_2325_; 
v_size_2325_ = lean_ctor_get(v_r_2298_, 0);
lean_inc(v_size_2325_);
v___y_2309_ = v___x_2323_;
v___y_2310_ = v___x_2324_;
v___y_2311_ = v_size_2325_;
goto v___jp_2308_;
}
else
{
lean_object* v___x_2326_; 
v___x_2326_ = lean_unsigned_to_nat(0u);
v___y_2309_ = v___x_2323_;
v___y_2310_ = v___x_2324_;
v___y_2311_ = v___x_2326_;
goto v___jp_2308_;
}
}
}
}
}
else
{
lean_object* v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2340_; 
lean_del_object(v___x_2132_);
v___x_2336_ = lean_nat_add(v___x_2276_, v_size_2277_);
v___x_2337_ = lean_nat_add(v___x_2336_, v_size_2278_);
lean_dec(v_size_2278_);
v___x_2338_ = lean_nat_add(v___x_2336_, v_size_2294_);
lean_dec(v___x_2336_);
lean_inc_ref(v_l_2129_);
if (v_isShared_2293_ == 0)
{
lean_ctor_set(v___x_2292_, 4, v_l_2281_);
lean_ctor_set(v___x_2292_, 3, v_l_2129_);
lean_ctor_set(v___x_2292_, 2, v_v_2128_);
lean_ctor_set(v___x_2292_, 1, v_k_2127_);
lean_ctor_set(v___x_2292_, 0, v___x_2338_);
v___x_2340_ = v___x_2292_;
goto v_reusejp_2339_;
}
else
{
lean_object* v_reuseFailAlloc_2353_; 
v_reuseFailAlloc_2353_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2353_, 0, v___x_2338_);
lean_ctor_set(v_reuseFailAlloc_2353_, 1, v_k_2127_);
lean_ctor_set(v_reuseFailAlloc_2353_, 2, v_v_2128_);
lean_ctor_set(v_reuseFailAlloc_2353_, 3, v_l_2129_);
lean_ctor_set(v_reuseFailAlloc_2353_, 4, v_l_2281_);
v___x_2340_ = v_reuseFailAlloc_2353_;
goto v_reusejp_2339_;
}
v_reusejp_2339_:
{
lean_object* v___x_2342_; uint8_t v_isShared_2343_; uint8_t v_isSharedCheck_2347_; 
v_isSharedCheck_2347_ = !lean_is_exclusive(v_l_2129_);
if (v_isSharedCheck_2347_ == 0)
{
lean_object* v_unused_2348_; lean_object* v_unused_2349_; lean_object* v_unused_2350_; lean_object* v_unused_2351_; lean_object* v_unused_2352_; 
v_unused_2348_ = lean_ctor_get(v_l_2129_, 4);
lean_dec(v_unused_2348_);
v_unused_2349_ = lean_ctor_get(v_l_2129_, 3);
lean_dec(v_unused_2349_);
v_unused_2350_ = lean_ctor_get(v_l_2129_, 2);
lean_dec(v_unused_2350_);
v_unused_2351_ = lean_ctor_get(v_l_2129_, 1);
lean_dec(v_unused_2351_);
v_unused_2352_ = lean_ctor_get(v_l_2129_, 0);
lean_dec(v_unused_2352_);
v___x_2342_ = v_l_2129_;
v_isShared_2343_ = v_isSharedCheck_2347_;
goto v_resetjp_2341_;
}
else
{
lean_dec(v_l_2129_);
v___x_2342_ = lean_box(0);
v_isShared_2343_ = v_isSharedCheck_2347_;
goto v_resetjp_2341_;
}
v_resetjp_2341_:
{
lean_object* v___x_2345_; 
if (v_isShared_2343_ == 0)
{
lean_ctor_set(v___x_2342_, 4, v_r_2282_);
lean_ctor_set(v___x_2342_, 3, v___x_2340_);
lean_ctor_set(v___x_2342_, 2, v_v_2280_);
lean_ctor_set(v___x_2342_, 1, v_k_2279_);
lean_ctor_set(v___x_2342_, 0, v___x_2337_);
v___x_2345_ = v___x_2342_;
goto v_reusejp_2344_;
}
else
{
lean_object* v_reuseFailAlloc_2346_; 
v_reuseFailAlloc_2346_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2346_, 0, v___x_2337_);
lean_ctor_set(v_reuseFailAlloc_2346_, 1, v_k_2279_);
lean_ctor_set(v_reuseFailAlloc_2346_, 2, v_v_2280_);
lean_ctor_set(v_reuseFailAlloc_2346_, 3, v___x_2340_);
lean_ctor_set(v_reuseFailAlloc_2346_, 4, v_r_2282_);
v___x_2345_ = v_reuseFailAlloc_2346_;
goto v_reusejp_2344_;
}
v_reusejp_2344_:
{
return v___x_2345_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_2360_; 
v_l_2360_ = lean_ctor_get(v_impl_2275_, 3);
lean_inc(v_l_2360_);
if (lean_obj_tag(v_l_2360_) == 0)
{
lean_object* v_r_2361_; lean_object* v_k_2362_; lean_object* v_v_2363_; lean_object* v___x_2365_; uint8_t v_isShared_2366_; uint8_t v_isSharedCheck_2386_; 
v_r_2361_ = lean_ctor_get(v_impl_2275_, 4);
v_k_2362_ = lean_ctor_get(v_impl_2275_, 1);
v_v_2363_ = lean_ctor_get(v_impl_2275_, 2);
v_isSharedCheck_2386_ = !lean_is_exclusive(v_impl_2275_);
if (v_isSharedCheck_2386_ == 0)
{
lean_object* v_unused_2387_; lean_object* v_unused_2388_; 
v_unused_2387_ = lean_ctor_get(v_impl_2275_, 3);
lean_dec(v_unused_2387_);
v_unused_2388_ = lean_ctor_get(v_impl_2275_, 0);
lean_dec(v_unused_2388_);
v___x_2365_ = v_impl_2275_;
v_isShared_2366_ = v_isSharedCheck_2386_;
goto v_resetjp_2364_;
}
else
{
lean_inc(v_r_2361_);
lean_inc(v_v_2363_);
lean_inc(v_k_2362_);
lean_dec(v_impl_2275_);
v___x_2365_ = lean_box(0);
v_isShared_2366_ = v_isSharedCheck_2386_;
goto v_resetjp_2364_;
}
v_resetjp_2364_:
{
lean_object* v_k_2367_; lean_object* v_v_2368_; lean_object* v___x_2370_; uint8_t v_isShared_2371_; uint8_t v_isSharedCheck_2382_; 
v_k_2367_ = lean_ctor_get(v_l_2360_, 1);
v_v_2368_ = lean_ctor_get(v_l_2360_, 2);
v_isSharedCheck_2382_ = !lean_is_exclusive(v_l_2360_);
if (v_isSharedCheck_2382_ == 0)
{
lean_object* v_unused_2383_; lean_object* v_unused_2384_; lean_object* v_unused_2385_; 
v_unused_2383_ = lean_ctor_get(v_l_2360_, 4);
lean_dec(v_unused_2383_);
v_unused_2384_ = lean_ctor_get(v_l_2360_, 3);
lean_dec(v_unused_2384_);
v_unused_2385_ = lean_ctor_get(v_l_2360_, 0);
lean_dec(v_unused_2385_);
v___x_2370_ = v_l_2360_;
v_isShared_2371_ = v_isSharedCheck_2382_;
goto v_resetjp_2369_;
}
else
{
lean_inc(v_v_2368_);
lean_inc(v_k_2367_);
lean_dec(v_l_2360_);
v___x_2370_ = lean_box(0);
v_isShared_2371_ = v_isSharedCheck_2382_;
goto v_resetjp_2369_;
}
v_resetjp_2369_:
{
lean_object* v___x_2372_; lean_object* v___x_2374_; 
v___x_2372_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_2361_, 2);
if (v_isShared_2371_ == 0)
{
lean_ctor_set(v___x_2370_, 4, v_r_2361_);
lean_ctor_set(v___x_2370_, 3, v_r_2361_);
lean_ctor_set(v___x_2370_, 2, v_v_2128_);
lean_ctor_set(v___x_2370_, 1, v_k_2127_);
lean_ctor_set(v___x_2370_, 0, v___x_2276_);
v___x_2374_ = v___x_2370_;
goto v_reusejp_2373_;
}
else
{
lean_object* v_reuseFailAlloc_2381_; 
v_reuseFailAlloc_2381_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2381_, 0, v___x_2276_);
lean_ctor_set(v_reuseFailAlloc_2381_, 1, v_k_2127_);
lean_ctor_set(v_reuseFailAlloc_2381_, 2, v_v_2128_);
lean_ctor_set(v_reuseFailAlloc_2381_, 3, v_r_2361_);
lean_ctor_set(v_reuseFailAlloc_2381_, 4, v_r_2361_);
v___x_2374_ = v_reuseFailAlloc_2381_;
goto v_reusejp_2373_;
}
v_reusejp_2373_:
{
lean_object* v___x_2376_; 
lean_inc(v_r_2361_);
if (v_isShared_2366_ == 0)
{
lean_ctor_set(v___x_2365_, 3, v_r_2361_);
lean_ctor_set(v___x_2365_, 0, v___x_2276_);
v___x_2376_ = v___x_2365_;
goto v_reusejp_2375_;
}
else
{
lean_object* v_reuseFailAlloc_2380_; 
v_reuseFailAlloc_2380_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2380_, 0, v___x_2276_);
lean_ctor_set(v_reuseFailAlloc_2380_, 1, v_k_2362_);
lean_ctor_set(v_reuseFailAlloc_2380_, 2, v_v_2363_);
lean_ctor_set(v_reuseFailAlloc_2380_, 3, v_r_2361_);
lean_ctor_set(v_reuseFailAlloc_2380_, 4, v_r_2361_);
v___x_2376_ = v_reuseFailAlloc_2380_;
goto v_reusejp_2375_;
}
v_reusejp_2375_:
{
lean_object* v___x_2378_; 
if (v_isShared_2133_ == 0)
{
lean_ctor_set(v___x_2132_, 4, v___x_2376_);
lean_ctor_set(v___x_2132_, 3, v___x_2374_);
lean_ctor_set(v___x_2132_, 2, v_v_2368_);
lean_ctor_set(v___x_2132_, 1, v_k_2367_);
lean_ctor_set(v___x_2132_, 0, v___x_2372_);
v___x_2378_ = v___x_2132_;
goto v_reusejp_2377_;
}
else
{
lean_object* v_reuseFailAlloc_2379_; 
v_reuseFailAlloc_2379_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2379_, 0, v___x_2372_);
lean_ctor_set(v_reuseFailAlloc_2379_, 1, v_k_2367_);
lean_ctor_set(v_reuseFailAlloc_2379_, 2, v_v_2368_);
lean_ctor_set(v_reuseFailAlloc_2379_, 3, v___x_2374_);
lean_ctor_set(v_reuseFailAlloc_2379_, 4, v___x_2376_);
v___x_2378_ = v_reuseFailAlloc_2379_;
goto v_reusejp_2377_;
}
v_reusejp_2377_:
{
return v___x_2378_;
}
}
}
}
}
}
else
{
lean_object* v_r_2389_; 
v_r_2389_ = lean_ctor_get(v_impl_2275_, 4);
lean_inc(v_r_2389_);
if (lean_obj_tag(v_r_2389_) == 0)
{
lean_object* v_k_2390_; lean_object* v_v_2391_; lean_object* v___x_2393_; uint8_t v_isShared_2394_; uint8_t v_isSharedCheck_2402_; 
v_k_2390_ = lean_ctor_get(v_impl_2275_, 1);
v_v_2391_ = lean_ctor_get(v_impl_2275_, 2);
v_isSharedCheck_2402_ = !lean_is_exclusive(v_impl_2275_);
if (v_isSharedCheck_2402_ == 0)
{
lean_object* v_unused_2403_; lean_object* v_unused_2404_; lean_object* v_unused_2405_; 
v_unused_2403_ = lean_ctor_get(v_impl_2275_, 4);
lean_dec(v_unused_2403_);
v_unused_2404_ = lean_ctor_get(v_impl_2275_, 3);
lean_dec(v_unused_2404_);
v_unused_2405_ = lean_ctor_get(v_impl_2275_, 0);
lean_dec(v_unused_2405_);
v___x_2393_ = v_impl_2275_;
v_isShared_2394_ = v_isSharedCheck_2402_;
goto v_resetjp_2392_;
}
else
{
lean_inc(v_v_2391_);
lean_inc(v_k_2390_);
lean_dec(v_impl_2275_);
v___x_2393_ = lean_box(0);
v_isShared_2394_ = v_isSharedCheck_2402_;
goto v_resetjp_2392_;
}
v_resetjp_2392_:
{
lean_object* v___x_2395_; lean_object* v___x_2397_; 
v___x_2395_ = lean_unsigned_to_nat(3u);
if (v_isShared_2394_ == 0)
{
lean_ctor_set(v___x_2393_, 4, v_l_2360_);
lean_ctor_set(v___x_2393_, 2, v_v_2128_);
lean_ctor_set(v___x_2393_, 1, v_k_2127_);
lean_ctor_set(v___x_2393_, 0, v___x_2276_);
v___x_2397_ = v___x_2393_;
goto v_reusejp_2396_;
}
else
{
lean_object* v_reuseFailAlloc_2401_; 
v_reuseFailAlloc_2401_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2401_, 0, v___x_2276_);
lean_ctor_set(v_reuseFailAlloc_2401_, 1, v_k_2127_);
lean_ctor_set(v_reuseFailAlloc_2401_, 2, v_v_2128_);
lean_ctor_set(v_reuseFailAlloc_2401_, 3, v_l_2360_);
lean_ctor_set(v_reuseFailAlloc_2401_, 4, v_l_2360_);
v___x_2397_ = v_reuseFailAlloc_2401_;
goto v_reusejp_2396_;
}
v_reusejp_2396_:
{
lean_object* v___x_2399_; 
if (v_isShared_2133_ == 0)
{
lean_ctor_set(v___x_2132_, 4, v_r_2389_);
lean_ctor_set(v___x_2132_, 3, v___x_2397_);
lean_ctor_set(v___x_2132_, 2, v_v_2391_);
lean_ctor_set(v___x_2132_, 1, v_k_2390_);
lean_ctor_set(v___x_2132_, 0, v___x_2395_);
v___x_2399_ = v___x_2132_;
goto v_reusejp_2398_;
}
else
{
lean_object* v_reuseFailAlloc_2400_; 
v_reuseFailAlloc_2400_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2400_, 0, v___x_2395_);
lean_ctor_set(v_reuseFailAlloc_2400_, 1, v_k_2390_);
lean_ctor_set(v_reuseFailAlloc_2400_, 2, v_v_2391_);
lean_ctor_set(v_reuseFailAlloc_2400_, 3, v___x_2397_);
lean_ctor_set(v_reuseFailAlloc_2400_, 4, v_r_2389_);
v___x_2399_ = v_reuseFailAlloc_2400_;
goto v_reusejp_2398_;
}
v_reusejp_2398_:
{
return v___x_2399_;
}
}
}
}
else
{
lean_object* v___x_2406_; lean_object* v___x_2408_; 
v___x_2406_ = lean_unsigned_to_nat(2u);
if (v_isShared_2133_ == 0)
{
lean_ctor_set(v___x_2132_, 4, v_impl_2275_);
lean_ctor_set(v___x_2132_, 3, v_r_2389_);
lean_ctor_set(v___x_2132_, 0, v___x_2406_);
v___x_2408_ = v___x_2132_;
goto v_reusejp_2407_;
}
else
{
lean_object* v_reuseFailAlloc_2409_; 
v_reuseFailAlloc_2409_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2409_, 0, v___x_2406_);
lean_ctor_set(v_reuseFailAlloc_2409_, 1, v_k_2127_);
lean_ctor_set(v_reuseFailAlloc_2409_, 2, v_v_2128_);
lean_ctor_set(v_reuseFailAlloc_2409_, 3, v_r_2389_);
lean_ctor_set(v_reuseFailAlloc_2409_, 4, v_impl_2275_);
v___x_2408_ = v_reuseFailAlloc_2409_;
goto v_reusejp_2407_;
}
v_reusejp_2407_:
{
return v___x_2408_;
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
lean_object* v___x_2411_; lean_object* v___x_2412_; 
v___x_2411_ = lean_unsigned_to_nat(1u);
v___x_2412_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2412_, 0, v___x_2411_);
lean_ctor_set(v___x_2412_, 1, v_k_2123_);
lean_ctor_set(v___x_2412_, 2, v_v_2124_);
lean_ctor_set(v___x_2412_, 3, v_t_2125_);
lean_ctor_set(v___x_2412_, 4, v_t_2125_);
return v___x_2412_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Level_collectMVars_spec__0___redArg(lean_object* v_k_2413_, lean_object* v_t_2414_){
_start:
{
if (lean_obj_tag(v_t_2414_) == 0)
{
lean_object* v_k_2415_; lean_object* v_l_2416_; lean_object* v_r_2417_; uint8_t v___x_2418_; 
v_k_2415_ = lean_ctor_get(v_t_2414_, 1);
v_l_2416_ = lean_ctor_get(v_t_2414_, 3);
v_r_2417_ = lean_ctor_get(v_t_2414_, 4);
v___x_2418_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2413_, v_k_2415_);
switch(v___x_2418_)
{
case 0:
{
v_t_2414_ = v_l_2416_;
goto _start;
}
case 1:
{
uint8_t v___x_2420_; 
v___x_2420_ = 1;
return v___x_2420_;
}
default: 
{
v_t_2414_ = v_r_2417_;
goto _start;
}
}
}
else
{
uint8_t v___x_2422_; 
v___x_2422_ = 0;
return v___x_2422_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Level_collectMVars_spec__0___redArg___boxed(lean_object* v_k_2423_, lean_object* v_t_2424_){
_start:
{
uint8_t v_res_2425_; lean_object* v_r_2426_; 
v_res_2425_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Level_collectMVars_spec__0___redArg(v_k_2423_, v_t_2424_);
lean_dec(v_t_2424_);
lean_dec(v_k_2423_);
v_r_2426_ = lean_box(v_res_2425_);
return v_r_2426_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_collectMVars(lean_object* v_u_2427_, lean_object* v_s_2428_){
_start:
{
lean_object* v_u_2430_; lean_object* v_v_2431_; 
switch(lean_obj_tag(v_u_2427_))
{
case 1:
{
lean_object* v_a_2434_; 
v_a_2434_ = lean_ctor_get(v_u_2427_, 0);
lean_inc(v_a_2434_);
lean_dec_ref(v_u_2427_);
v_u_2427_ = v_a_2434_;
goto _start;
}
case 2:
{
lean_object* v_a_2436_; lean_object* v_a_2437_; 
v_a_2436_ = lean_ctor_get(v_u_2427_, 0);
lean_inc(v_a_2436_);
v_a_2437_ = lean_ctor_get(v_u_2427_, 1);
lean_inc(v_a_2437_);
lean_dec_ref(v_u_2427_);
v_u_2430_ = v_a_2436_;
v_v_2431_ = v_a_2437_;
goto v___jp_2429_;
}
case 3:
{
lean_object* v_a_2438_; lean_object* v_a_2439_; 
v_a_2438_ = lean_ctor_get(v_u_2427_, 0);
lean_inc(v_a_2438_);
v_a_2439_ = lean_ctor_get(v_u_2427_, 1);
lean_inc(v_a_2439_);
lean_dec_ref(v_u_2427_);
v_u_2430_ = v_a_2438_;
v_v_2431_ = v_a_2439_;
goto v___jp_2429_;
}
case 5:
{
lean_object* v_a_2440_; uint8_t v___x_2441_; 
v_a_2440_ = lean_ctor_get(v_u_2427_, 0);
lean_inc(v_a_2440_);
lean_dec_ref(v_u_2427_);
v___x_2441_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Level_collectMVars_spec__0___redArg(v_a_2440_, v_s_2428_);
if (v___x_2441_ == 0)
{
lean_object* v___x_2442_; lean_object* v___x_2443_; 
v___x_2442_ = lean_box(0);
v___x_2443_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Level_collectMVars_spec__1___redArg(v_a_2440_, v___x_2442_, v_s_2428_);
return v___x_2443_;
}
else
{
lean_dec(v_a_2440_);
return v_s_2428_;
}
}
default: 
{
lean_dec(v_u_2427_);
return v_s_2428_;
}
}
v___jp_2429_:
{
lean_object* v___x_2432_; 
v___x_2432_ = l_Lean_Level_collectMVars(v_v_2431_, v_s_2428_);
v_u_2427_ = v_u_2430_;
v_s_2428_ = v___x_2432_;
goto _start;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Level_collectMVars_spec__0(lean_object* v_00_u03b2_2444_, lean_object* v_k_2445_, lean_object* v_t_2446_){
_start:
{
uint8_t v___x_2447_; 
v___x_2447_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Level_collectMVars_spec__0___redArg(v_k_2445_, v_t_2446_);
return v___x_2447_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Level_collectMVars_spec__0___boxed(lean_object* v_00_u03b2_2448_, lean_object* v_k_2449_, lean_object* v_t_2450_){
_start:
{
uint8_t v_res_2451_; lean_object* v_r_2452_; 
v_res_2451_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Level_collectMVars_spec__0(v_00_u03b2_2448_, v_k_2449_, v_t_2450_);
lean_dec(v_t_2450_);
lean_dec(v_k_2449_);
v_r_2452_ = lean_box(v_res_2451_);
return v_r_2452_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Level_collectMVars_spec__1(lean_object* v_00_u03b2_2453_, lean_object* v_k_2454_, lean_object* v_v_2455_, lean_object* v_t_2456_, lean_object* v_hl_2457_){
_start:
{
lean_object* v___x_2458_; 
v___x_2458_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Level_collectMVars_spec__1___redArg(v_k_2454_, v_v_2455_, v_t_2456_);
return v___x_2458_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_find_x3f_visit(lean_object* v_p_2459_, lean_object* v_u_2460_){
_start:
{
lean_object* v_u_2462_; lean_object* v_v_2463_; lean_object* v___x_2466_; uint8_t v___x_2467_; 
lean_inc_ref(v_p_2459_);
lean_inc(v_u_2460_);
v___x_2466_ = lean_apply_1(v_p_2459_, v_u_2460_);
v___x_2467_ = lean_unbox(v___x_2466_);
if (v___x_2467_ == 0)
{
switch(lean_obj_tag(v_u_2460_))
{
case 1:
{
lean_object* v_a_2468_; 
v_a_2468_ = lean_ctor_get(v_u_2460_, 0);
lean_inc(v_a_2468_);
lean_dec_ref(v_u_2460_);
v_u_2460_ = v_a_2468_;
goto _start;
}
case 2:
{
lean_object* v_a_2470_; lean_object* v_a_2471_; 
v_a_2470_ = lean_ctor_get(v_u_2460_, 0);
lean_inc(v_a_2470_);
v_a_2471_ = lean_ctor_get(v_u_2460_, 1);
lean_inc(v_a_2471_);
lean_dec_ref(v_u_2460_);
v_u_2462_ = v_a_2470_;
v_v_2463_ = v_a_2471_;
goto v___jp_2461_;
}
case 3:
{
lean_object* v_a_2472_; lean_object* v_a_2473_; 
v_a_2472_ = lean_ctor_get(v_u_2460_, 0);
lean_inc(v_a_2472_);
v_a_2473_ = lean_ctor_get(v_u_2460_, 1);
lean_inc(v_a_2473_);
lean_dec_ref(v_u_2460_);
v_u_2462_ = v_a_2472_;
v_v_2463_ = v_a_2473_;
goto v___jp_2461_;
}
default: 
{
lean_object* v___x_2474_; 
lean_dec(v_u_2460_);
lean_dec_ref(v_p_2459_);
v___x_2474_ = lean_box(0);
return v___x_2474_;
}
}
}
else
{
lean_object* v___x_2475_; 
lean_dec_ref(v_p_2459_);
v___x_2475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2475_, 0, v_u_2460_);
return v___x_2475_;
}
v___jp_2461_:
{
lean_object* v___x_2464_; 
lean_inc_ref(v_p_2459_);
v___x_2464_ = l___private_Lean_Level_0__Lean_Level_find_x3f_visit(v_p_2459_, v_u_2462_);
if (lean_obj_tag(v___x_2464_) == 0)
{
v_u_2460_ = v_v_2463_;
goto _start;
}
else
{
lean_dec(v_v_2463_);
lean_dec_ref(v_p_2459_);
return v___x_2464_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_find_x3f(lean_object* v_u_2476_, lean_object* v_p_2477_){
_start:
{
lean_object* v___x_2478_; 
v___x_2478_ = l___private_Lean_Level_0__Lean_Level_find_x3f_visit(v_p_2477_, v_u_2476_);
return v___x_2478_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_any(lean_object* v_u_2479_, lean_object* v_p_2480_){
_start:
{
lean_object* v___x_2481_; 
v___x_2481_ = l___private_Lean_Level_0__Lean_Level_find_x3f_visit(v_p_2480_, v_u_2479_);
if (lean_obj_tag(v___x_2481_) == 0)
{
uint8_t v___x_2482_; 
v___x_2482_ = 0;
return v___x_2482_;
}
else
{
uint8_t v___x_2483_; 
lean_dec_ref(v___x_2481_);
v___x_2483_ = 1;
return v___x_2483_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_any___boxed(lean_object* v_u_2484_, lean_object* v_p_2485_){
_start:
{
uint8_t v_res_2486_; lean_object* v_r_2487_; 
v_res_2486_ = l_Lean_Level_any(v_u_2484_, v_p_2485_);
v_r_2487_ = lean_box(v_res_2486_);
return v_r_2487_;
}
}
LEAN_EXPORT lean_object* l_Nat_toLevel(lean_object* v_n_2488_){
_start:
{
lean_object* v___x_2489_; 
v___x_2489_ = l_Lean_Level_ofNat(v_n_2488_);
return v___x_2489_;
}
}
LEAN_EXPORT lean_object* l_Nat_toLevel___boxed(lean_object* v_n_2490_){
_start:
{
lean_object* v_res_2491_; 
v_res_2491_ = l_Nat_toLevel(v_n_2490_);
lean_dec(v_n_2490_);
return v_res_2491_;
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
l_Lean_instInhabitedData = _init_l_Lean_instInhabitedData();
l_Lean_instInhabitedLevelMVarId_default = _init_l_Lean_instInhabitedLevelMVarId_default();
lean_mark_persistent(l_Lean_instInhabitedLevelMVarId_default);
l_Lean_instInhabitedLevelMVarId = _init_l_Lean_instInhabitedLevelMVarId();
lean_mark_persistent(l_Lean_instInhabitedLevelMVarId);
l_Lean_instInhabitedLMVarIdSet = _init_l_Lean_instInhabitedLMVarIdSet();
lean_mark_persistent(l_Lean_instInhabitedLMVarIdSet);
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
