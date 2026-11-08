// Lean compiler output
// Module: Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Substructure
// Imports: public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Pred import Init.Omega
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
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Bool_toNat(uint8_t);
lean_object* lean_nat_lor(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t l_Std_Tactic_BVDecide_instHashableBVBit_hash(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
uint64_t l_Std_Sat_AIG_instHashableFanin_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Std_Tactic_BVDecide_instDecidableEqBVBit___boxed(lean_object*, lean_object*);
uint8_t l_Std_Sat_AIG_instDecidableEqDecl_decEq___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t l_Std_Tactic_BVDecide_BVLogicalExpr_decEq(lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_instHashable___lam__0___boxed(lean_object*);
lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_decEq___boxed(lean_object*, lean_object*);
lean_object* l_instBEqOfDecidableEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lean_nat_land(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Std_Tactic_BVDecide_BVPred_bitblast(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Std_Tactic_BVDecide_BVLogicalExpr_Cache_empty___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_Cache_empty___redArg___closed__0;
static lean_once_cell_t l_Std_Tactic_BVDecide_BVLogicalExpr_Cache_empty___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_Cache_empty___redArg___closed__1;
static lean_once_cell_t l_Std_Tactic_BVDecide_BVLogicalExpr_Cache_empty___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_Cache_empty___redArg___closed__2;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_Cache_empty___redArg();
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_Cache_empty___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_Cache_empty(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_Cache_empty___boxed(lean_object*);
static const lean_closure_object l_Std_Tactic_BVDecide_BVLogicalExpr_Cache_insert___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Tactic_BVDecide_BVLogicalExpr_instHashable___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_Cache_insert___redArg___closed__0 = (const lean_object*)&l_Std_Tactic_BVDecide_BVLogicalExpr_Cache_insert___redArg___closed__0_value;
static const lean_closure_object l_Std_Tactic_BVDecide_BVLogicalExpr_Cache_insert___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Tactic_BVDecide_BVLogicalExpr_decEq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_Cache_insert___redArg___closed__1 = (const lean_object*)&l_Std_Tactic_BVDecide_BVLogicalExpr_Cache_insert___redArg___closed__1_value;
static const lean_closure_object l_Std_Tactic_BVDecide_BVLogicalExpr_Cache_insert___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instBEqOfDecidableEq___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Tactic_BVDecide_BVLogicalExpr_Cache_insert___redArg___closed__1_value)} };
static const lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_Cache_insert___redArg___closed__2 = (const lean_object*)&l_Std_Tactic_BVDecide_BVLogicalExpr_Cache_insert___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_Cache_insert___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_Cache_insert___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_Cache_insert(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_Cache_insert___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_Cache_get_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_Cache_get_x3f___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_Cache_get_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_Cache_get_x3f___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_Cache_cast___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_Cache_cast(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_Cache_cast___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__3_spec__7_spec__11_spec__21___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Std_Sat_AIG_instHashableDecl_hash___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__3_spec__7_spec__9_spec__15(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instHashableDecl_hash___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__3_spec__7_spec__9_spec__15___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__3_spec__7_spec__11_spec__19___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__3_spec__7_spec__11_spec__19___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__3_spec__7_spec__11_spec__20_spec__21_spec__22___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__3_spec__7_spec__11_spec__20_spec__21___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__3_spec__7_spec__11_spec__20___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__3_spec__7_spec__11___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_getConstant___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__3_spec__7_spec__10(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_getConstant___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__3_spec__7_spec__10___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__3_spec__7_spec__9_spec__16___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__3_spec__7_spec__9___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__3_spec__7_spec__9___redArg___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__3_spec__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__3_spec__7___closed__0 = (const lean_object*)&l_Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__3_spec__7___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__3_spec__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkOrCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkIfCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkBEqCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkXorCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_goCache_spec__1_spec__3_spec__5_spec__11___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_goCache_spec__1_spec__3_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_goCache_spec__1_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_goCache_spec__1_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_goCache_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_goCache_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_goCache_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_goCache_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_goCache_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_goCache_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_goCache_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_goCache(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_goCache_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_goCache_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_goCache_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_goCache_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_goCache_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_goCache_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_goCache_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_goCache_spec__1_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_goCache_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_goCache_spec__1_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__3_spec__7_spec__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__3_spec__7_spec__9___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__3_spec__7_spec__11(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_goCache_spec__1_spec__3_spec__5_spec__11(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__3_spec__7_spec__9_spec__16(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__3_spec__7_spec__11_spec__19(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__3_spec__7_spec__11_spec__19___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__3_spec__7_spec__11_spec__20(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__3_spec__7_spec__11_spec__21(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__3_spec__7_spec__11_spec__20_spec__21(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__3_spec__7_spec__11_spec__20_spec__21_spec__22(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_goCache_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_goCache_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_goCache_match__3_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_goCache_match__1_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_goCache_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_goCache_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_match__7_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_match__7_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_match__1_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_match__3_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_match__3_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_match__5_splitter___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_match__5_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_match__5_splitter(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_match__5_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache(lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__0 = (const lean_object*)&l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__0_value;
static lean_once_cell_t l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__1;
static lean_once_cell_t l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__2;
static lean_once_cell_t l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__3;
LEAN_EXPORT lean_object* l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast(lean_object*);
static lean_object* _init_l_Std_Tactic_BVDecide_BVLogicalExpr_Cache_empty___redArg___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_1_ = lean_box(0);
v___x_2_ = lean_unsigned_to_nat(16u);
v___x_3_ = lean_mk_array(v___x_2_, v___x_1_);
return v___x_3_;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_BVLogicalExpr_Cache_empty___redArg___closed__1(void){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_4_ = lean_obj_once(&l_Std_Tactic_BVDecide_BVLogicalExpr_Cache_empty___redArg___closed__0, &l_Std_Tactic_BVDecide_BVLogicalExpr_Cache_empty___redArg___closed__0_once, _init_l_Std_Tactic_BVDecide_BVLogicalExpr_Cache_empty___redArg___closed__0);
v___x_5_ = lean_unsigned_to_nat(0u);
v___x_6_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6_, 0, v___x_5_);
lean_ctor_set(v___x_6_, 1, v___x_4_);
return v___x_6_;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_BVLogicalExpr_Cache_empty___redArg___closed__2(void){
_start:
{
lean_object* v___x_7_; lean_object* v___x_8_; 
v___x_7_ = lean_obj_once(&l_Std_Tactic_BVDecide_BVLogicalExpr_Cache_empty___redArg___closed__1, &l_Std_Tactic_BVDecide_BVLogicalExpr_Cache_empty___redArg___closed__1_once, _init_l_Std_Tactic_BVDecide_BVLogicalExpr_Cache_empty___redArg___closed__1);
v___x_8_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_8_, 0, v___x_7_);
lean_ctor_set(v___x_8_, 1, v___x_7_);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_Cache_empty___redArg(){
_start:
{
lean_object* v___x_10_; 
v___x_10_ = lean_obj_once(&l_Std_Tactic_BVDecide_BVLogicalExpr_Cache_empty___redArg___closed__2, &l_Std_Tactic_BVDecide_BVLogicalExpr_Cache_empty___redArg___closed__2_once, _init_l_Std_Tactic_BVDecide_BVLogicalExpr_Cache_empty___redArg___closed__2);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_Cache_empty___redArg___boxed(lean_object* v___dummy_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = l_Std_Tactic_BVDecide_BVLogicalExpr_Cache_empty___redArg();
return v_res_12_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_Cache_empty(lean_object* v_aig_13_){
_start:
{
lean_object* v___x_14_; 
v___x_14_ = lean_obj_once(&l_Std_Tactic_BVDecide_BVLogicalExpr_Cache_empty___redArg___closed__2, &l_Std_Tactic_BVDecide_BVLogicalExpr_Cache_empty___redArg___closed__2_once, _init_l_Std_Tactic_BVDecide_BVLogicalExpr_Cache_empty___redArg___closed__2);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_Cache_empty___boxed(lean_object* v_aig_15_){
_start:
{
lean_object* v_res_16_; 
v_res_16_ = l_Std_Tactic_BVDecide_BVLogicalExpr_Cache_empty(v_aig_15_);
lean_dec_ref(v_aig_15_);
return v_res_16_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_Cache_insert___redArg(lean_object* v_cache_21_, lean_object* v_expr_22_, lean_object* v_ref_23_){
_start:
{
lean_object* v_exprs_24_; lean_object* v_map_25_; lean_object* v___x_27_; uint8_t v_isShared_28_; uint8_t v_isSharedCheck_41_; 
v_exprs_24_ = lean_ctor_get(v_cache_21_, 0);
v_map_25_ = lean_ctor_get(v_cache_21_, 1);
v_isSharedCheck_41_ = !lean_is_exclusive(v_cache_21_);
if (v_isSharedCheck_41_ == 0)
{
v___x_27_ = v_cache_21_;
v_isShared_28_ = v_isSharedCheck_41_;
goto v_resetjp_26_;
}
else
{
lean_inc(v_map_25_);
lean_inc(v_exprs_24_);
lean_dec(v_cache_21_);
v___x_27_ = lean_box(0);
v_isShared_28_ = v_isSharedCheck_41_;
goto v_resetjp_26_;
}
v_resetjp_26_:
{
lean_object* v_gate_29_; uint8_t v_invert_30_; lean_object* v___f_31_; lean_object* v___f_32_; lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_39_; 
v_gate_29_ = lean_ctor_get(v_ref_23_, 0);
v_invert_30_ = lean_ctor_get_uint8(v_ref_23_, sizeof(void*)*1);
v___f_31_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVLogicalExpr_Cache_insert___redArg___closed__0));
v___f_32_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVLogicalExpr_Cache_insert___redArg___closed__2));
v___x_33_ = lean_unsigned_to_nat(2u);
v___x_34_ = lean_nat_mul(v_gate_29_, v___x_33_);
v___x_35_ = l_Bool_toNat(v_invert_30_);
v___x_36_ = lean_nat_lor(v___x_34_, v___x_35_);
lean_dec(v___x_35_);
lean_dec(v___x_34_);
v___x_37_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___f_32_, v___f_31_, v_map_25_, v_expr_22_, v___x_36_);
if (v_isShared_28_ == 0)
{
lean_ctor_set(v___x_27_, 1, v___x_37_);
v___x_39_ = v___x_27_;
goto v_reusejp_38_;
}
else
{
lean_object* v_reuseFailAlloc_40_; 
v_reuseFailAlloc_40_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_40_, 0, v_exprs_24_);
lean_ctor_set(v_reuseFailAlloc_40_, 1, v___x_37_);
v___x_39_ = v_reuseFailAlloc_40_;
goto v_reusejp_38_;
}
v_reusejp_38_:
{
return v___x_39_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_Cache_insert___redArg___boxed(lean_object* v_cache_42_, lean_object* v_expr_43_, lean_object* v_ref_44_){
_start:
{
lean_object* v_res_45_; 
v_res_45_ = l_Std_Tactic_BVDecide_BVLogicalExpr_Cache_insert___redArg(v_cache_42_, v_expr_43_, v_ref_44_);
lean_dec_ref(v_ref_44_);
return v_res_45_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_Cache_insert(lean_object* v_aig_46_, lean_object* v_cache_47_, lean_object* v_expr_48_, lean_object* v_ref_49_){
_start:
{
lean_object* v_exprs_50_; lean_object* v_map_51_; lean_object* v___x_53_; uint8_t v_isShared_54_; uint8_t v_isSharedCheck_67_; 
v_exprs_50_ = lean_ctor_get(v_cache_47_, 0);
v_map_51_ = lean_ctor_get(v_cache_47_, 1);
v_isSharedCheck_67_ = !lean_is_exclusive(v_cache_47_);
if (v_isSharedCheck_67_ == 0)
{
v___x_53_ = v_cache_47_;
v_isShared_54_ = v_isSharedCheck_67_;
goto v_resetjp_52_;
}
else
{
lean_inc(v_map_51_);
lean_inc(v_exprs_50_);
lean_dec(v_cache_47_);
v___x_53_ = lean_box(0);
v_isShared_54_ = v_isSharedCheck_67_;
goto v_resetjp_52_;
}
v_resetjp_52_:
{
lean_object* v_gate_55_; uint8_t v_invert_56_; lean_object* v___f_57_; lean_object* v___f_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_65_; 
v_gate_55_ = lean_ctor_get(v_ref_49_, 0);
v_invert_56_ = lean_ctor_get_uint8(v_ref_49_, sizeof(void*)*1);
v___f_57_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVLogicalExpr_Cache_insert___redArg___closed__0));
v___f_58_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVLogicalExpr_Cache_insert___redArg___closed__2));
v___x_59_ = lean_unsigned_to_nat(2u);
v___x_60_ = lean_nat_mul(v_gate_55_, v___x_59_);
v___x_61_ = l_Bool_toNat(v_invert_56_);
v___x_62_ = lean_nat_lor(v___x_60_, v___x_61_);
lean_dec(v___x_61_);
lean_dec(v___x_60_);
v___x_63_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___f_58_, v___f_57_, v_map_51_, v_expr_48_, v___x_62_);
if (v_isShared_54_ == 0)
{
lean_ctor_set(v___x_53_, 1, v___x_63_);
v___x_65_ = v___x_53_;
goto v_reusejp_64_;
}
else
{
lean_object* v_reuseFailAlloc_66_; 
v_reuseFailAlloc_66_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_66_, 0, v_exprs_50_);
lean_ctor_set(v_reuseFailAlloc_66_, 1, v___x_63_);
v___x_65_ = v_reuseFailAlloc_66_;
goto v_reusejp_64_;
}
v_reusejp_64_:
{
return v___x_65_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_Cache_insert___boxed(lean_object* v_aig_68_, lean_object* v_cache_69_, lean_object* v_expr_70_, lean_object* v_ref_71_){
_start:
{
lean_object* v_res_72_; 
v_res_72_ = l_Std_Tactic_BVDecide_BVLogicalExpr_Cache_insert(v_aig_68_, v_cache_69_, v_expr_70_, v_ref_71_);
lean_dec_ref(v_ref_71_);
lean_dec_ref(v_aig_68_);
return v_res_72_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_Cache_get_x3f___redArg(lean_object* v_cache_73_, lean_object* v_expr_74_){
_start:
{
lean_object* v_map_75_; lean_object* v___f_76_; lean_object* v___f_77_; lean_object* v___x_78_; 
v_map_75_ = lean_ctor_get(v_cache_73_, 1);
v___f_76_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVLogicalExpr_Cache_insert___redArg___closed__0));
v___f_77_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVLogicalExpr_Cache_insert___redArg___closed__2));
v___x_78_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___f_77_, v___f_76_, v_map_75_, v_expr_74_);
if (lean_obj_tag(v___x_78_) == 0)
{
lean_object* v___x_79_; 
v___x_79_ = lean_box(0);
return v___x_79_;
}
else
{
lean_object* v_val_80_; lean_object* v___x_82_; uint8_t v_isShared_83_; uint8_t v_isSharedCheck_97_; 
v_val_80_ = lean_ctor_get(v___x_78_, 0);
v_isSharedCheck_97_ = !lean_is_exclusive(v___x_78_);
if (v_isSharedCheck_97_ == 0)
{
v___x_82_ = v___x_78_;
v_isShared_83_ = v_isSharedCheck_97_;
goto v_resetjp_81_;
}
else
{
lean_inc(v_val_80_);
lean_dec(v___x_78_);
v___x_82_ = lean_box(0);
v_isShared_83_ = v_isSharedCheck_97_;
goto v_resetjp_81_;
}
v_resetjp_81_:
{
lean_object* v___x_84_; lean_object* v___x_85_; uint8_t v___y_87_; lean_object* v___x_92_; lean_object* v___x_93_; uint8_t v___x_94_; 
v___x_84_ = lean_unsigned_to_nat(1u);
v___x_85_ = lean_nat_shiftr(v_val_80_, v___x_84_);
v___x_92_ = lean_nat_land(v___x_84_, v_val_80_);
lean_dec(v_val_80_);
v___x_93_ = lean_unsigned_to_nat(0u);
v___x_94_ = lean_nat_dec_eq(v___x_92_, v___x_93_);
lean_dec(v___x_92_);
if (v___x_94_ == 0)
{
uint8_t v___x_95_; 
v___x_95_ = 1;
v___y_87_ = v___x_95_;
goto v___jp_86_;
}
else
{
uint8_t v___x_96_; 
v___x_96_ = 0;
v___y_87_ = v___x_96_;
goto v___jp_86_;
}
v___jp_86_:
{
lean_object* v___x_88_; lean_object* v___x_90_; 
v___x_88_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_88_, 0, v___x_85_);
lean_ctor_set_uint8(v___x_88_, sizeof(void*)*1, v___y_87_);
if (v_isShared_83_ == 0)
{
lean_ctor_set(v___x_82_, 0, v___x_88_);
v___x_90_ = v___x_82_;
goto v_reusejp_89_;
}
else
{
lean_object* v_reuseFailAlloc_91_; 
v_reuseFailAlloc_91_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_91_, 0, v___x_88_);
v___x_90_ = v_reuseFailAlloc_91_;
goto v_reusejp_89_;
}
v_reusejp_89_:
{
return v___x_90_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_Cache_get_x3f___redArg___boxed(lean_object* v_cache_98_, lean_object* v_expr_99_){
_start:
{
lean_object* v_res_100_; 
v_res_100_ = l_Std_Tactic_BVDecide_BVLogicalExpr_Cache_get_x3f___redArg(v_cache_98_, v_expr_99_);
lean_dec_ref(v_cache_98_);
return v_res_100_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_Cache_get_x3f(lean_object* v_aig_101_, lean_object* v_cache_102_, lean_object* v_expr_103_){
_start:
{
lean_object* v_map_104_; lean_object* v___f_105_; lean_object* v___f_106_; lean_object* v___x_107_; 
v_map_104_ = lean_ctor_get(v_cache_102_, 1);
v___f_105_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVLogicalExpr_Cache_insert___redArg___closed__0));
v___f_106_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVLogicalExpr_Cache_insert___redArg___closed__2));
v___x_107_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___f_106_, v___f_105_, v_map_104_, v_expr_103_);
if (lean_obj_tag(v___x_107_) == 0)
{
lean_object* v___x_108_; 
v___x_108_ = lean_box(0);
return v___x_108_;
}
else
{
lean_object* v_val_109_; lean_object* v___x_111_; uint8_t v_isShared_112_; uint8_t v_isSharedCheck_126_; 
v_val_109_ = lean_ctor_get(v___x_107_, 0);
v_isSharedCheck_126_ = !lean_is_exclusive(v___x_107_);
if (v_isSharedCheck_126_ == 0)
{
v___x_111_ = v___x_107_;
v_isShared_112_ = v_isSharedCheck_126_;
goto v_resetjp_110_;
}
else
{
lean_inc(v_val_109_);
lean_dec(v___x_107_);
v___x_111_ = lean_box(0);
v_isShared_112_ = v_isSharedCheck_126_;
goto v_resetjp_110_;
}
v_resetjp_110_:
{
lean_object* v___x_113_; lean_object* v___x_114_; uint8_t v___y_116_; lean_object* v___x_121_; lean_object* v___x_122_; uint8_t v___x_123_; 
v___x_113_ = lean_unsigned_to_nat(1u);
v___x_114_ = lean_nat_shiftr(v_val_109_, v___x_113_);
v___x_121_ = lean_nat_land(v___x_113_, v_val_109_);
lean_dec(v_val_109_);
v___x_122_ = lean_unsigned_to_nat(0u);
v___x_123_ = lean_nat_dec_eq(v___x_121_, v___x_122_);
lean_dec(v___x_121_);
if (v___x_123_ == 0)
{
uint8_t v___x_124_; 
v___x_124_ = 1;
v___y_116_ = v___x_124_;
goto v___jp_115_;
}
else
{
uint8_t v___x_125_; 
v___x_125_ = 0;
v___y_116_ = v___x_125_;
goto v___jp_115_;
}
v___jp_115_:
{
lean_object* v___x_117_; lean_object* v___x_119_; 
v___x_117_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_117_, 0, v___x_114_);
lean_ctor_set_uint8(v___x_117_, sizeof(void*)*1, v___y_116_);
if (v_isShared_112_ == 0)
{
lean_ctor_set(v___x_111_, 0, v___x_117_);
v___x_119_ = v___x_111_;
goto v_reusejp_118_;
}
else
{
lean_object* v_reuseFailAlloc_120_; 
v_reuseFailAlloc_120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_120_, 0, v___x_117_);
v___x_119_ = v_reuseFailAlloc_120_;
goto v_reusejp_118_;
}
v_reusejp_118_:
{
return v___x_119_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_Cache_get_x3f___boxed(lean_object* v_aig_127_, lean_object* v_cache_128_, lean_object* v_expr_129_){
_start:
{
lean_object* v_res_130_; 
v_res_130_ = l_Std_Tactic_BVDecide_BVLogicalExpr_Cache_get_x3f(v_aig_127_, v_cache_128_, v_expr_129_);
lean_dec_ref(v_cache_128_);
lean_dec_ref(v_aig_127_);
return v_res_130_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_Cache_cast___redArg(lean_object* v_cache_131_){
_start:
{
lean_object* v_exprs_132_; lean_object* v_map_133_; lean_object* v___x_135_; uint8_t v_isShared_136_; uint8_t v_isSharedCheck_140_; 
v_exprs_132_ = lean_ctor_get(v_cache_131_, 0);
v_map_133_ = lean_ctor_get(v_cache_131_, 1);
v_isSharedCheck_140_ = !lean_is_exclusive(v_cache_131_);
if (v_isSharedCheck_140_ == 0)
{
v___x_135_ = v_cache_131_;
v_isShared_136_ = v_isSharedCheck_140_;
goto v_resetjp_134_;
}
else
{
lean_inc(v_map_133_);
lean_inc(v_exprs_132_);
lean_dec(v_cache_131_);
v___x_135_ = lean_box(0);
v_isShared_136_ = v_isSharedCheck_140_;
goto v_resetjp_134_;
}
v_resetjp_134_:
{
lean_object* v___x_138_; 
if (v_isShared_136_ == 0)
{
v___x_138_ = v___x_135_;
goto v_reusejp_137_;
}
else
{
lean_object* v_reuseFailAlloc_139_; 
v_reuseFailAlloc_139_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_139_, 0, v_exprs_132_);
lean_ctor_set(v_reuseFailAlloc_139_, 1, v_map_133_);
v___x_138_ = v_reuseFailAlloc_139_;
goto v_reusejp_137_;
}
v_reusejp_137_:
{
return v___x_138_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_Cache_cast(lean_object* v_aig1_141_, lean_object* v_aig2_142_, lean_object* v_cache_143_, lean_object* v_h_144_){
_start:
{
lean_object* v_exprs_145_; lean_object* v_map_146_; lean_object* v___x_148_; uint8_t v_isShared_149_; uint8_t v_isSharedCheck_153_; 
v_exprs_145_ = lean_ctor_get(v_cache_143_, 0);
v_map_146_ = lean_ctor_get(v_cache_143_, 1);
v_isSharedCheck_153_ = !lean_is_exclusive(v_cache_143_);
if (v_isSharedCheck_153_ == 0)
{
v___x_148_ = v_cache_143_;
v_isShared_149_ = v_isSharedCheck_153_;
goto v_resetjp_147_;
}
else
{
lean_inc(v_map_146_);
lean_inc(v_exprs_145_);
lean_dec(v_cache_143_);
v___x_148_ = lean_box(0);
v_isShared_149_ = v_isSharedCheck_153_;
goto v_resetjp_147_;
}
v_resetjp_147_:
{
lean_object* v___x_151_; 
if (v_isShared_149_ == 0)
{
v___x_151_ = v___x_148_;
goto v_reusejp_150_;
}
else
{
lean_object* v_reuseFailAlloc_152_; 
v_reuseFailAlloc_152_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_152_, 0, v_exprs_145_);
lean_ctor_set(v_reuseFailAlloc_152_, 1, v_map_146_);
v___x_151_ = v_reuseFailAlloc_152_;
goto v_reusejp_150_;
}
v_reusejp_150_:
{
return v___x_151_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_Cache_cast___boxed(lean_object* v_aig1_154_, lean_object* v_aig2_155_, lean_object* v_cache_156_, lean_object* v_h_157_){
_start:
{
lean_object* v_res_158_; 
v_res_158_ = l_Std_Tactic_BVDecide_BVLogicalExpr_Cache_cast(v_aig1_154_, v_aig2_155_, v_cache_156_, v_h_157_);
lean_dec_ref(v_aig2_155_);
lean_dec_ref(v_aig1_154_);
return v_res_158_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__3_spec__7_spec__11_spec__21___redArg(lean_object* v_a_159_, lean_object* v_b_160_, lean_object* v_x_161_){
_start:
{
if (lean_obj_tag(v_x_161_) == 0)
{
lean_dec(v_b_160_);
lean_dec(v_a_159_);
return v_x_161_;
}
else
{
lean_object* v_key_162_; lean_object* v_value_163_; lean_object* v_tail_164_; lean_object* v___x_166_; uint8_t v_isShared_167_; uint8_t v_isSharedCheck_177_; 
v_key_162_ = lean_ctor_get(v_x_161_, 0);
v_value_163_ = lean_ctor_get(v_x_161_, 1);
v_tail_164_ = lean_ctor_get(v_x_161_, 2);
v_isSharedCheck_177_ = !lean_is_exclusive(v_x_161_);
if (v_isSharedCheck_177_ == 0)
{
v___x_166_ = v_x_161_;
v_isShared_167_ = v_isSharedCheck_177_;
goto v_resetjp_165_;
}
else
{
lean_inc(v_tail_164_);
lean_inc(v_value_163_);
lean_inc(v_key_162_);
lean_dec(v_x_161_);
v___x_166_ = lean_box(0);
v_isShared_167_ = v_isSharedCheck_177_;
goto v_resetjp_165_;
}
v_resetjp_165_:
{
lean_object* v___x_168_; uint8_t v___x_169_; 
v___x_168_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_instDecidableEqBVBit___boxed), 2, 0);
lean_inc(v_a_159_);
lean_inc(v_key_162_);
v___x_169_ = l_Std_Sat_AIG_instDecidableEqDecl_decEq___redArg(v___x_168_, v_key_162_, v_a_159_);
if (v___x_169_ == 0)
{
lean_object* v___x_170_; lean_object* v___x_172_; 
v___x_170_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__3_spec__7_spec__11_spec__21___redArg(v_a_159_, v_b_160_, v_tail_164_);
if (v_isShared_167_ == 0)
{
lean_ctor_set(v___x_166_, 2, v___x_170_);
v___x_172_ = v___x_166_;
goto v_reusejp_171_;
}
else
{
lean_object* v_reuseFailAlloc_173_; 
v_reuseFailAlloc_173_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_173_, 0, v_key_162_);
lean_ctor_set(v_reuseFailAlloc_173_, 1, v_value_163_);
lean_ctor_set(v_reuseFailAlloc_173_, 2, v___x_170_);
v___x_172_ = v_reuseFailAlloc_173_;
goto v_reusejp_171_;
}
v_reusejp_171_:
{
return v___x_172_;
}
}
else
{
lean_object* v___x_175_; 
lean_dec(v_value_163_);
lean_dec(v_key_162_);
if (v_isShared_167_ == 0)
{
lean_ctor_set(v___x_166_, 1, v_b_160_);
lean_ctor_set(v___x_166_, 0, v_a_159_);
v___x_175_ = v___x_166_;
goto v_reusejp_174_;
}
else
{
lean_object* v_reuseFailAlloc_176_; 
v_reuseFailAlloc_176_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_176_, 0, v_a_159_);
lean_ctor_set(v_reuseFailAlloc_176_, 1, v_b_160_);
lean_ctor_set(v_reuseFailAlloc_176_, 2, v_tail_164_);
v___x_175_ = v_reuseFailAlloc_176_;
goto v_reusejp_174_;
}
v_reusejp_174_:
{
return v___x_175_;
}
}
}
}
}
}
LEAN_EXPORT uint64_t l_Std_Sat_AIG_instHashableDecl_hash___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__3_spec__7_spec__9_spec__15(lean_object* v_x_178_){
_start:
{
switch(lean_obj_tag(v_x_178_))
{
case 0:
{
uint64_t v___x_179_; 
v___x_179_ = 0ULL;
return v___x_179_;
}
case 1:
{
lean_object* v_idx_180_; uint64_t v___x_181_; uint64_t v___x_182_; uint64_t v___x_183_; 
v_idx_180_ = lean_ctor_get(v_x_178_, 0);
v___x_181_ = 1ULL;
v___x_182_ = l_Std_Tactic_BVDecide_instHashableBVBit_hash(v_idx_180_);
v___x_183_ = lean_uint64_mix_hash(v___x_181_, v___x_182_);
return v___x_183_;
}
default: 
{
lean_object* v_l_184_; lean_object* v_r_185_; uint64_t v___x_186_; uint64_t v___x_187_; uint64_t v___x_188_; uint64_t v___x_189_; uint64_t v___x_190_; 
v_l_184_ = lean_ctor_get(v_x_178_, 0);
v_r_185_ = lean_ctor_get(v_x_178_, 1);
v___x_186_ = 2ULL;
v___x_187_ = l_Std_Sat_AIG_instHashableFanin_hash(v_l_184_);
v___x_188_ = lean_uint64_mix_hash(v___x_186_, v___x_187_);
v___x_189_ = l_Std_Sat_AIG_instHashableFanin_hash(v_r_185_);
v___x_190_ = lean_uint64_mix_hash(v___x_188_, v___x_189_);
return v___x_190_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instHashableDecl_hash___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__3_spec__7_spec__9_spec__15___boxed(lean_object* v_x_191_){
_start:
{
uint64_t v_res_192_; lean_object* v_r_193_; 
v_res_192_ = l_Std_Sat_AIG_instHashableDecl_hash___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__3_spec__7_spec__9_spec__15(v_x_191_);
lean_dec(v_x_191_);
v_r_193_ = lean_box_uint64(v_res_192_);
return v_r_193_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__3_spec__7_spec__11_spec__19___redArg(lean_object* v_a_194_, lean_object* v_x_195_){
_start:
{
if (lean_obj_tag(v_x_195_) == 0)
{
uint8_t v___x_196_; 
lean_dec(v_a_194_);
v___x_196_ = 0;
return v___x_196_;
}
else
{
lean_object* v_key_197_; lean_object* v_tail_198_; lean_object* v___x_199_; uint8_t v___x_200_; 
v_key_197_ = lean_ctor_get(v_x_195_, 0);
lean_inc(v_key_197_);
v_tail_198_ = lean_ctor_get(v_x_195_, 2);
lean_inc(v_tail_198_);
lean_dec_ref_known(v_x_195_, 3);
v___x_199_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_instDecidableEqBVBit___boxed), 2, 0);
lean_inc(v_a_194_);
v___x_200_ = l_Std_Sat_AIG_instDecidableEqDecl_decEq___redArg(v___x_199_, v_key_197_, v_a_194_);
if (v___x_200_ == 0)
{
v_x_195_ = v_tail_198_;
goto _start;
}
else
{
lean_dec(v_tail_198_);
lean_dec(v_a_194_);
return v___x_200_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__3_spec__7_spec__11_spec__19___redArg___boxed(lean_object* v_a_202_, lean_object* v_x_203_){
_start:
{
uint8_t v_res_204_; lean_object* v_r_205_; 
v_res_204_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__3_spec__7_spec__11_spec__19___redArg(v_a_202_, v_x_203_);
v_r_205_ = lean_box(v_res_204_);
return v_r_205_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__3_spec__7_spec__11_spec__20_spec__21_spec__22___redArg(lean_object* v_x_206_, lean_object* v_x_207_){
_start:
{
if (lean_obj_tag(v_x_207_) == 0)
{
return v_x_206_;
}
else
{
lean_object* v_key_208_; lean_object* v_value_209_; lean_object* v_tail_210_; lean_object* v___x_212_; uint8_t v_isShared_213_; uint8_t v_isSharedCheck_233_; 
v_key_208_ = lean_ctor_get(v_x_207_, 0);
v_value_209_ = lean_ctor_get(v_x_207_, 1);
v_tail_210_ = lean_ctor_get(v_x_207_, 2);
v_isSharedCheck_233_ = !lean_is_exclusive(v_x_207_);
if (v_isSharedCheck_233_ == 0)
{
v___x_212_ = v_x_207_;
v_isShared_213_ = v_isSharedCheck_233_;
goto v_resetjp_211_;
}
else
{
lean_inc(v_tail_210_);
lean_inc(v_value_209_);
lean_inc(v_key_208_);
lean_dec(v_x_207_);
v___x_212_ = lean_box(0);
v_isShared_213_ = v_isSharedCheck_233_;
goto v_resetjp_211_;
}
v_resetjp_211_:
{
lean_object* v___x_214_; uint64_t v___x_215_; uint64_t v___x_216_; uint64_t v___x_217_; uint64_t v_fold_218_; uint64_t v___x_219_; uint64_t v___x_220_; uint64_t v___x_221_; size_t v___x_222_; size_t v___x_223_; size_t v___x_224_; size_t v___x_225_; size_t v___x_226_; lean_object* v___x_227_; lean_object* v___x_229_; 
v___x_214_ = lean_array_get_size(v_x_206_);
v___x_215_ = l_Std_Sat_AIG_instHashableDecl_hash___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__3_spec__7_spec__9_spec__15(v_key_208_);
v___x_216_ = 32ULL;
v___x_217_ = lean_uint64_shift_right(v___x_215_, v___x_216_);
v_fold_218_ = lean_uint64_xor(v___x_215_, v___x_217_);
v___x_219_ = 16ULL;
v___x_220_ = lean_uint64_shift_right(v_fold_218_, v___x_219_);
v___x_221_ = lean_uint64_xor(v_fold_218_, v___x_220_);
v___x_222_ = lean_uint64_to_usize(v___x_221_);
v___x_223_ = lean_usize_of_nat(v___x_214_);
v___x_224_ = ((size_t)1ULL);
v___x_225_ = lean_usize_sub(v___x_223_, v___x_224_);
v___x_226_ = lean_usize_land(v___x_222_, v___x_225_);
v___x_227_ = lean_array_uget_borrowed(v_x_206_, v___x_226_);
lean_inc(v___x_227_);
if (v_isShared_213_ == 0)
{
lean_ctor_set(v___x_212_, 2, v___x_227_);
v___x_229_ = v___x_212_;
goto v_reusejp_228_;
}
else
{
lean_object* v_reuseFailAlloc_232_; 
v_reuseFailAlloc_232_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_232_, 0, v_key_208_);
lean_ctor_set(v_reuseFailAlloc_232_, 1, v_value_209_);
lean_ctor_set(v_reuseFailAlloc_232_, 2, v___x_227_);
v___x_229_ = v_reuseFailAlloc_232_;
goto v_reusejp_228_;
}
v_reusejp_228_:
{
lean_object* v___x_230_; 
v___x_230_ = lean_array_uset(v_x_206_, v___x_226_, v___x_229_);
v_x_206_ = v___x_230_;
v_x_207_ = v_tail_210_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__3_spec__7_spec__11_spec__20_spec__21___redArg(lean_object* v_i_234_, lean_object* v_source_235_, lean_object* v_target_236_){
_start:
{
lean_object* v___x_237_; uint8_t v___x_238_; 
v___x_237_ = lean_array_get_size(v_source_235_);
v___x_238_ = lean_nat_dec_lt(v_i_234_, v___x_237_);
if (v___x_238_ == 0)
{
lean_dec_ref(v_source_235_);
lean_dec(v_i_234_);
return v_target_236_;
}
else
{
lean_object* v_es_239_; lean_object* v___x_240_; lean_object* v_source_241_; lean_object* v_target_242_; lean_object* v___x_243_; lean_object* v___x_244_; 
v_es_239_ = lean_array_fget(v_source_235_, v_i_234_);
v___x_240_ = lean_box(0);
v_source_241_ = lean_array_fset(v_source_235_, v_i_234_, v___x_240_);
v_target_242_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__3_spec__7_spec__11_spec__20_spec__21_spec__22___redArg(v_target_236_, v_es_239_);
v___x_243_ = lean_unsigned_to_nat(1u);
v___x_244_ = lean_nat_add(v_i_234_, v___x_243_);
lean_dec(v_i_234_);
v_i_234_ = v___x_244_;
v_source_235_ = v_source_241_;
v_target_236_ = v_target_242_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__3_spec__7_spec__11_spec__20___redArg(lean_object* v_data_246_){
_start:
{
lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v_nbuckets_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; 
v___x_247_ = lean_array_get_size(v_data_246_);
v___x_248_ = lean_unsigned_to_nat(2u);
v_nbuckets_249_ = lean_nat_mul(v___x_247_, v___x_248_);
v___x_250_ = lean_unsigned_to_nat(0u);
v___x_251_ = lean_box(0);
v___x_252_ = lean_mk_array(v_nbuckets_249_, v___x_251_);
v___x_253_ = lean_array_propagate_mark(v_data_246_, v___x_252_);
v___x_254_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__3_spec__7_spec__11_spec__20_spec__21___redArg(v___x_250_, v_data_246_, v___x_253_);
return v___x_254_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__3_spec__7_spec__11___redArg(lean_object* v_m_255_, lean_object* v_a_256_, lean_object* v_b_257_){
_start:
{
lean_object* v_size_258_; lean_object* v_buckets_259_; lean_object* v___x_261_; uint8_t v_isShared_262_; uint8_t v_isSharedCheck_302_; 
v_size_258_ = lean_ctor_get(v_m_255_, 0);
v_buckets_259_ = lean_ctor_get(v_m_255_, 1);
v_isSharedCheck_302_ = !lean_is_exclusive(v_m_255_);
if (v_isSharedCheck_302_ == 0)
{
v___x_261_ = v_m_255_;
v_isShared_262_ = v_isSharedCheck_302_;
goto v_resetjp_260_;
}
else
{
lean_inc(v_buckets_259_);
lean_inc(v_size_258_);
lean_dec(v_m_255_);
v___x_261_ = lean_box(0);
v_isShared_262_ = v_isSharedCheck_302_;
goto v_resetjp_260_;
}
v_resetjp_260_:
{
lean_object* v___x_263_; uint64_t v___x_264_; uint64_t v___x_265_; uint64_t v___x_266_; uint64_t v_fold_267_; uint64_t v___x_268_; uint64_t v___x_269_; uint64_t v___x_270_; size_t v___x_271_; size_t v___x_272_; size_t v___x_273_; size_t v___x_274_; size_t v___x_275_; lean_object* v_bkt_276_; uint8_t v___x_277_; 
v___x_263_ = lean_array_get_size(v_buckets_259_);
v___x_264_ = l_Std_Sat_AIG_instHashableDecl_hash___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__3_spec__7_spec__9_spec__15(v_a_256_);
v___x_265_ = 32ULL;
v___x_266_ = lean_uint64_shift_right(v___x_264_, v___x_265_);
v_fold_267_ = lean_uint64_xor(v___x_264_, v___x_266_);
v___x_268_ = 16ULL;
v___x_269_ = lean_uint64_shift_right(v_fold_267_, v___x_268_);
v___x_270_ = lean_uint64_xor(v_fold_267_, v___x_269_);
v___x_271_ = lean_uint64_to_usize(v___x_270_);
v___x_272_ = lean_usize_of_nat(v___x_263_);
v___x_273_ = ((size_t)1ULL);
v___x_274_ = lean_usize_sub(v___x_272_, v___x_273_);
v___x_275_ = lean_usize_land(v___x_271_, v___x_274_);
v_bkt_276_ = lean_array_uget_borrowed(v_buckets_259_, v___x_275_);
lean_inc(v_bkt_276_);
lean_inc(v_a_256_);
v___x_277_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__3_spec__7_spec__11_spec__19___redArg(v_a_256_, v_bkt_276_);
if (v___x_277_ == 0)
{
lean_object* v___x_278_; lean_object* v_size_x27_279_; lean_object* v___x_280_; lean_object* v_buckets_x27_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; uint8_t v___x_287_; 
v___x_278_ = lean_unsigned_to_nat(1u);
v_size_x27_279_ = lean_nat_add(v_size_258_, v___x_278_);
lean_dec(v_size_258_);
lean_inc(v_bkt_276_);
v___x_280_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_280_, 0, v_a_256_);
lean_ctor_set(v___x_280_, 1, v_b_257_);
lean_ctor_set(v___x_280_, 2, v_bkt_276_);
v_buckets_x27_281_ = lean_array_uset(v_buckets_259_, v___x_275_, v___x_280_);
v___x_282_ = lean_unsigned_to_nat(4u);
v___x_283_ = lean_nat_mul(v_size_x27_279_, v___x_282_);
v___x_284_ = lean_unsigned_to_nat(3u);
v___x_285_ = lean_nat_div(v___x_283_, v___x_284_);
lean_dec(v___x_283_);
v___x_286_ = lean_array_get_size(v_buckets_x27_281_);
v___x_287_ = lean_nat_dec_le(v___x_285_, v___x_286_);
lean_dec(v___x_285_);
if (v___x_287_ == 0)
{
lean_object* v_val_288_; lean_object* v___x_290_; 
v_val_288_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__3_spec__7_spec__11_spec__20___redArg(v_buckets_x27_281_);
if (v_isShared_262_ == 0)
{
lean_ctor_set(v___x_261_, 1, v_val_288_);
lean_ctor_set(v___x_261_, 0, v_size_x27_279_);
v___x_290_ = v___x_261_;
goto v_reusejp_289_;
}
else
{
lean_object* v_reuseFailAlloc_291_; 
v_reuseFailAlloc_291_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_291_, 0, v_size_x27_279_);
lean_ctor_set(v_reuseFailAlloc_291_, 1, v_val_288_);
v___x_290_ = v_reuseFailAlloc_291_;
goto v_reusejp_289_;
}
v_reusejp_289_:
{
return v___x_290_;
}
}
else
{
lean_object* v___x_293_; 
if (v_isShared_262_ == 0)
{
lean_ctor_set(v___x_261_, 1, v_buckets_x27_281_);
lean_ctor_set(v___x_261_, 0, v_size_x27_279_);
v___x_293_ = v___x_261_;
goto v_reusejp_292_;
}
else
{
lean_object* v_reuseFailAlloc_294_; 
v_reuseFailAlloc_294_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_294_, 0, v_size_x27_279_);
lean_ctor_set(v_reuseFailAlloc_294_, 1, v_buckets_x27_281_);
v___x_293_ = v_reuseFailAlloc_294_;
goto v_reusejp_292_;
}
v_reusejp_292_:
{
return v___x_293_;
}
}
}
else
{
lean_object* v___x_295_; lean_object* v_buckets_x27_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_300_; 
lean_inc(v_bkt_276_);
v___x_295_ = lean_box(0);
v_buckets_x27_296_ = lean_array_uset(v_buckets_259_, v___x_275_, v___x_295_);
v___x_297_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__3_spec__7_spec__11_spec__21___redArg(v_a_256_, v_b_257_, v_bkt_276_);
v___x_298_ = lean_array_uset(v_buckets_x27_296_, v___x_275_, v___x_297_);
if (v_isShared_262_ == 0)
{
lean_ctor_set(v___x_261_, 1, v___x_298_);
v___x_300_ = v___x_261_;
goto v_reusejp_299_;
}
else
{
lean_object* v_reuseFailAlloc_301_; 
v_reuseFailAlloc_301_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_301_, 0, v_size_258_);
lean_ctor_set(v_reuseFailAlloc_301_, 1, v___x_298_);
v___x_300_ = v_reuseFailAlloc_301_;
goto v_reusejp_299_;
}
v_reusejp_299_:
{
return v___x_300_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_getConstant___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__3_spec__7_spec__10(lean_object* v_aig_303_, lean_object* v_ref_304_){
_start:
{
lean_object* v_gate_305_; uint8_t v_invert_306_; lean_object* v_decls_307_; lean_object* v_decl_308_; 
v_gate_305_ = lean_ctor_get(v_ref_304_, 0);
v_invert_306_ = lean_ctor_get_uint8(v_ref_304_, sizeof(void*)*1);
v_decls_307_ = lean_ctor_get(v_aig_303_, 0);
v_decl_308_ = lean_array_fget_borrowed(v_decls_307_, v_gate_305_);
if (lean_obj_tag(v_decl_308_) == 0)
{
lean_object* v___x_309_; lean_object* v___x_310_; 
v___x_309_ = lean_box(v_invert_306_);
v___x_310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_310_, 0, v___x_309_);
return v___x_310_;
}
else
{
lean_object* v___x_311_; 
v___x_311_ = lean_box(0);
return v___x_311_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_getConstant___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__3_spec__7_spec__10___boxed(lean_object* v_aig_312_, lean_object* v_ref_313_){
_start:
{
lean_object* v_res_314_; 
v_res_314_ = l_Std_Sat_AIG_getConstant___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__3_spec__7_spec__10(v_aig_312_, v_ref_313_);
lean_dec_ref(v_ref_313_);
lean_dec_ref(v_aig_312_);
return v_res_314_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__3_spec__7_spec__9_spec__16___redArg(lean_object* v_a_315_, lean_object* v_x_316_){
_start:
{
if (lean_obj_tag(v_x_316_) == 0)
{
lean_object* v___x_317_; 
lean_dec(v_a_315_);
v___x_317_ = lean_box(0);
return v___x_317_;
}
else
{
lean_object* v_key_318_; lean_object* v_value_319_; lean_object* v_tail_320_; lean_object* v___x_321_; uint8_t v___x_322_; 
v_key_318_ = lean_ctor_get(v_x_316_, 0);
lean_inc(v_key_318_);
v_value_319_ = lean_ctor_get(v_x_316_, 1);
lean_inc(v_value_319_);
v_tail_320_ = lean_ctor_get(v_x_316_, 2);
lean_inc(v_tail_320_);
lean_dec_ref_known(v_x_316_, 3);
v___x_321_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_instDecidableEqBVBit___boxed), 2, 0);
lean_inc(v_a_315_);
v___x_322_ = l_Std_Sat_AIG_instDecidableEqDecl_decEq___redArg(v___x_321_, v_key_318_, v_a_315_);
if (v___x_322_ == 0)
{
lean_dec(v_value_319_);
v_x_316_ = v_tail_320_;
goto _start;
}
else
{
lean_object* v___x_324_; 
lean_dec(v_tail_320_);
lean_dec(v_a_315_);
v___x_324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_324_, 0, v_value_319_);
return v___x_324_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__3_spec__7_spec__9___redArg(lean_object* v_m_325_, lean_object* v_a_326_){
_start:
{
lean_object* v_buckets_327_; lean_object* v___x_328_; uint64_t v___x_329_; uint64_t v___x_330_; uint64_t v___x_331_; uint64_t v_fold_332_; uint64_t v___x_333_; uint64_t v___x_334_; uint64_t v___x_335_; size_t v___x_336_; size_t v___x_337_; size_t v___x_338_; size_t v___x_339_; size_t v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; 
v_buckets_327_ = lean_ctor_get(v_m_325_, 1);
v___x_328_ = lean_array_get_size(v_buckets_327_);
v___x_329_ = l_Std_Sat_AIG_instHashableDecl_hash___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__3_spec__7_spec__9_spec__15(v_a_326_);
v___x_330_ = 32ULL;
v___x_331_ = lean_uint64_shift_right(v___x_329_, v___x_330_);
v_fold_332_ = lean_uint64_xor(v___x_329_, v___x_331_);
v___x_333_ = 16ULL;
v___x_334_ = lean_uint64_shift_right(v_fold_332_, v___x_333_);
v___x_335_ = lean_uint64_xor(v_fold_332_, v___x_334_);
v___x_336_ = lean_uint64_to_usize(v___x_335_);
v___x_337_ = lean_usize_of_nat(v___x_328_);
v___x_338_ = ((size_t)1ULL);
v___x_339_ = lean_usize_sub(v___x_337_, v___x_338_);
v___x_340_ = lean_usize_land(v___x_336_, v___x_339_);
v___x_341_ = lean_array_uget_borrowed(v_buckets_327_, v___x_340_);
lean_inc(v___x_341_);
v___x_342_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__3_spec__7_spec__9_spec__16___redArg(v_a_326_, v___x_341_);
return v___x_342_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__3_spec__7_spec__9___redArg___boxed(lean_object* v_m_343_, lean_object* v_a_344_){
_start:
{
lean_object* v_res_345_; 
v_res_345_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__3_spec__7_spec__9___redArg(v_m_343_, v_a_344_);
lean_dec_ref(v_m_343_);
return v_res_345_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__3_spec__7(lean_object* v_aig_349_, lean_object* v_input_350_){
_start:
{
lean_object* v_lhs_351_; lean_object* v_rhs_352_; lean_object* v___x_354_; uint8_t v_isShared_355_; uint8_t v_isSharedCheck_434_; 
v_lhs_351_ = lean_ctor_get(v_input_350_, 0);
v_rhs_352_ = lean_ctor_get(v_input_350_, 1);
v_isSharedCheck_434_ = !lean_is_exclusive(v_input_350_);
if (v_isSharedCheck_434_ == 0)
{
v___x_354_ = v_input_350_;
v_isShared_355_ = v_isSharedCheck_434_;
goto v_resetjp_353_;
}
else
{
lean_inc(v_rhs_352_);
lean_inc(v_lhs_351_);
lean_dec(v_input_350_);
v___x_354_ = lean_box(0);
v_isShared_355_ = v_isSharedCheck_434_;
goto v_resetjp_353_;
}
v_resetjp_353_:
{
lean_object* v_decls_356_; lean_object* v_cache_357_; lean_object* v___x_359_; uint8_t v_isShared_360_; uint8_t v_isSharedCheck_433_; 
v_decls_356_ = lean_ctor_get(v_aig_349_, 0);
v_cache_357_ = lean_ctor_get(v_aig_349_, 1);
v_isSharedCheck_433_ = !lean_is_exclusive(v_aig_349_);
if (v_isSharedCheck_433_ == 0)
{
v___x_359_ = v_aig_349_;
v_isShared_360_ = v_isSharedCheck_433_;
goto v_resetjp_358_;
}
else
{
lean_inc(v_cache_357_);
lean_inc(v_decls_356_);
lean_dec(v_aig_349_);
v___x_359_ = lean_box(0);
v_isShared_360_ = v_isSharedCheck_433_;
goto v_resetjp_358_;
}
v_resetjp_358_:
{
lean_object* v_gate_361_; uint8_t v_invert_362_; lean_object* v_gate_363_; uint8_t v_invert_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v_decl_373_; 
v_gate_361_ = lean_ctor_get(v_lhs_351_, 0);
lean_inc(v_gate_361_);
v_invert_362_ = lean_ctor_get_uint8(v_lhs_351_, sizeof(void*)*1);
v_gate_363_ = lean_ctor_get(v_rhs_352_, 0);
v_invert_364_ = lean_ctor_get_uint8(v_rhs_352_, sizeof(void*)*1);
v___x_365_ = lean_unsigned_to_nat(2u);
v___x_366_ = lean_nat_mul(v_gate_361_, v___x_365_);
v___x_367_ = l_Bool_toNat(v_invert_362_);
v___x_368_ = lean_nat_lor(v___x_366_, v___x_367_);
lean_dec(v___x_367_);
lean_dec(v___x_366_);
v___x_369_ = lean_nat_mul(v_gate_363_, v___x_365_);
v___x_370_ = l_Bool_toNat(v_invert_364_);
v___x_371_ = lean_nat_lor(v___x_369_, v___x_370_);
lean_dec(v___x_370_);
lean_dec(v___x_369_);
if (v_isShared_355_ == 0)
{
lean_ctor_set_tag(v___x_354_, 2);
lean_ctor_set(v___x_354_, 1, v___x_371_);
lean_ctor_set(v___x_354_, 0, v___x_368_);
v_decl_373_ = v___x_354_;
goto v_reusejp_372_;
}
else
{
lean_object* v_reuseFailAlloc_432_; 
v_reuseFailAlloc_432_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_432_, 0, v___x_368_);
lean_ctor_set(v_reuseFailAlloc_432_, 1, v___x_371_);
v_decl_373_ = v_reuseFailAlloc_432_;
goto v_reusejp_372_;
}
v_reusejp_372_:
{
lean_object* v___x_374_; 
lean_inc_ref(v_decl_373_);
v___x_374_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__3_spec__7_spec__9___redArg(v_cache_357_, v_decl_373_);
if (lean_obj_tag(v___x_374_) == 0)
{
lean_object* v___x_376_; 
lean_inc(v_gate_363_);
lean_inc_ref(v_cache_357_);
lean_inc_ref(v_decls_356_);
if (v_isShared_360_ == 0)
{
v___x_376_ = v___x_359_;
goto v_reusejp_375_;
}
else
{
lean_object* v_reuseFailAlloc_417_; 
v_reuseFailAlloc_417_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_417_, 0, v_decls_356_);
lean_ctor_set(v_reuseFailAlloc_417_, 1, v_cache_357_);
v___x_376_ = v_reuseFailAlloc_417_;
goto v_reusejp_375_;
}
v_reusejp_375_:
{
uint8_t v___y_378_; lean_object* v_lhsVal_391_; lean_object* v_rhsVal_392_; lean_object* v___x_394_; uint8_t v_isShared_395_; uint8_t v_isSharedCheck_415_; 
v_lhsVal_391_ = l_Std_Sat_AIG_getConstant___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__3_spec__7_spec__10(v___x_376_, v_lhs_351_);
lean_dec_ref(v_lhs_351_);
v_rhsVal_392_ = l_Std_Sat_AIG_getConstant___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__3_spec__7_spec__10(v___x_376_, v_rhs_352_);
v_isSharedCheck_415_ = !lean_is_exclusive(v_rhs_352_);
if (v_isSharedCheck_415_ == 0)
{
lean_object* v_unused_416_; 
v_unused_416_ = lean_ctor_get(v_rhs_352_, 0);
lean_dec(v_unused_416_);
v___x_394_ = v_rhs_352_;
v_isShared_395_ = v_isSharedCheck_415_;
goto v_resetjp_393_;
}
else
{
lean_dec(v_rhs_352_);
v___x_394_ = lean_box(0);
v_isShared_395_ = v_isSharedCheck_415_;
goto v_resetjp_393_;
}
v___jp_377_:
{
lean_object* v___x_379_; lean_object* v_ref_380_; lean_object* v___x_381_; 
v___x_379_ = lean_unsigned_to_nat(0u);
v_ref_380_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_ref_380_, 0, v___x_379_);
lean_ctor_set_uint8(v_ref_380_, sizeof(void*)*1, v___y_378_);
v___x_381_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_381_, 0, v___x_376_);
lean_ctor_set(v___x_381_, 1, v_ref_380_);
return v___x_381_;
}
v___jp_382_:
{
lean_object* v___x_383_; lean_object* v___x_384_; 
v___x_383_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_383_, 0, v_gate_361_);
lean_ctor_set_uint8(v___x_383_, sizeof(void*)*1, v_invert_362_);
v___x_384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_384_, 0, v___x_376_);
lean_ctor_set(v___x_384_, 1, v___x_383_);
return v___x_384_;
}
v___jp_385_:
{
lean_object* v___x_386_; lean_object* v___x_387_; 
v___x_386_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_386_, 0, v_gate_363_);
lean_ctor_set_uint8(v___x_386_, sizeof(void*)*1, v_invert_364_);
v___x_387_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_387_, 0, v___x_376_);
lean_ctor_set(v___x_387_, 1, v___x_386_);
return v___x_387_;
}
v___jp_388_:
{
lean_object* v_ref_389_; lean_object* v___x_390_; 
v_ref_389_ = ((lean_object*)(l_Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__3_spec__7___closed__0));
v___x_390_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_390_, 0, v___x_376_);
lean_ctor_set(v___x_390_, 1, v_ref_389_);
return v___x_390_;
}
v_resetjp_393_:
{
if (lean_obj_tag(v_lhsVal_391_) == 1)
{
lean_object* v_val_396_; uint8_t v___x_397_; 
lean_del_object(v___x_394_);
lean_dec_ref(v_decl_373_);
lean_dec(v_gate_361_);
lean_dec_ref(v_cache_357_);
lean_dec_ref(v_decls_356_);
v_val_396_ = lean_ctor_get(v_lhsVal_391_, 0);
lean_inc(v_val_396_);
lean_dec_ref_known(v_lhsVal_391_, 1);
v___x_397_ = lean_unbox(v_val_396_);
lean_dec(v_val_396_);
if (v___x_397_ == 0)
{
lean_dec(v_rhsVal_392_);
lean_dec(v_gate_363_);
goto v___jp_388_;
}
else
{
if (lean_obj_tag(v_rhsVal_392_) == 1)
{
lean_object* v_val_398_; uint8_t v___x_399_; 
v_val_398_ = lean_ctor_get(v_rhsVal_392_, 0);
lean_inc(v_val_398_);
lean_dec_ref_known(v_rhsVal_392_, 1);
v___x_399_ = lean_unbox(v_val_398_);
lean_dec(v_val_398_);
if (v___x_399_ == 0)
{
lean_dec(v_gate_363_);
goto v___jp_388_;
}
else
{
goto v___jp_385_;
}
}
else
{
lean_dec(v_rhsVal_392_);
goto v___jp_385_;
}
}
}
else
{
lean_dec(v_lhsVal_391_);
if (lean_obj_tag(v_rhsVal_392_) == 1)
{
lean_object* v_val_400_; uint8_t v___x_401_; 
lean_dec_ref(v_decl_373_);
lean_dec(v_gate_363_);
lean_dec_ref(v_cache_357_);
lean_dec_ref(v_decls_356_);
v_val_400_ = lean_ctor_get(v_rhsVal_392_, 0);
lean_inc(v_val_400_);
lean_dec_ref_known(v_rhsVal_392_, 1);
v___x_401_ = lean_unbox(v_val_400_);
lean_dec(v_val_400_);
if (v___x_401_ == 0)
{
lean_del_object(v___x_394_);
lean_dec(v_gate_361_);
goto v___jp_388_;
}
else
{
lean_object* v___x_403_; 
if (v_isShared_395_ == 0)
{
lean_ctor_set(v___x_394_, 0, v_gate_361_);
v___x_403_ = v___x_394_;
goto v_reusejp_402_;
}
else
{
lean_object* v_reuseFailAlloc_405_; 
v_reuseFailAlloc_405_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_405_, 0, v_gate_361_);
v___x_403_ = v_reuseFailAlloc_405_;
goto v_reusejp_402_;
}
v_reusejp_402_:
{
lean_object* v___x_404_; 
lean_ctor_set_uint8(v___x_403_, sizeof(void*)*1, v_invert_362_);
v___x_404_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_404_, 0, v___x_376_);
lean_ctor_set(v___x_404_, 1, v___x_403_);
return v___x_404_;
}
}
}
else
{
uint8_t v___x_406_; 
lean_dec(v_rhsVal_392_);
v___x_406_ = lean_nat_dec_eq(v_gate_361_, v_gate_363_);
lean_dec(v_gate_363_);
if (v___x_406_ == 0)
{
lean_object* v_g_407_; lean_object* v_cache_408_; lean_object* v_decls_409_; lean_object* v___x_410_; lean_object* v___x_412_; 
lean_dec_ref(v___x_376_);
lean_dec(v_gate_361_);
v_g_407_ = lean_array_get_size(v_decls_356_);
lean_inc_ref(v_decl_373_);
v_cache_408_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__3_spec__7_spec__11___redArg(v_cache_357_, v_decl_373_, v_g_407_);
v_decls_409_ = lean_array_push(v_decls_356_, v_decl_373_);
v___x_410_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_410_, 0, v_decls_409_);
lean_ctor_set(v___x_410_, 1, v_cache_408_);
if (v_isShared_395_ == 0)
{
lean_ctor_set(v___x_394_, 0, v_g_407_);
v___x_412_ = v___x_394_;
goto v_reusejp_411_;
}
else
{
lean_object* v_reuseFailAlloc_414_; 
v_reuseFailAlloc_414_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_414_, 0, v_g_407_);
v___x_412_ = v_reuseFailAlloc_414_;
goto v_reusejp_411_;
}
v_reusejp_411_:
{
lean_object* v___x_413_; 
lean_ctor_set_uint8(v___x_412_, sizeof(void*)*1, v___x_406_);
v___x_413_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_413_, 0, v___x_410_);
lean_ctor_set(v___x_413_, 1, v___x_412_);
return v___x_413_;
}
}
else
{
lean_del_object(v___x_394_);
lean_dec_ref(v_decl_373_);
lean_dec_ref(v_cache_357_);
lean_dec_ref(v_decls_356_);
if (v_invert_364_ == 0)
{
if (v_invert_362_ == 0)
{
goto v___jp_382_;
}
else
{
lean_dec(v_gate_361_);
v___y_378_ = v_invert_364_;
goto v___jp_377_;
}
}
else
{
if (v_invert_362_ == 0)
{
lean_dec(v_gate_361_);
v___y_378_ = v_invert_362_;
goto v___jp_377_;
}
else
{
goto v___jp_382_;
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
lean_object* v___x_419_; uint8_t v_isShared_420_; uint8_t v_isSharedCheck_430_; 
lean_dec_ref(v_decl_373_);
lean_dec(v_gate_361_);
lean_dec_ref(v_lhs_351_);
v_isSharedCheck_430_ = !lean_is_exclusive(v_rhs_352_);
if (v_isSharedCheck_430_ == 0)
{
lean_object* v_unused_431_; 
v_unused_431_ = lean_ctor_get(v_rhs_352_, 0);
lean_dec(v_unused_431_);
v___x_419_ = v_rhs_352_;
v_isShared_420_ = v_isSharedCheck_430_;
goto v_resetjp_418_;
}
else
{
lean_dec(v_rhs_352_);
v___x_419_ = lean_box(0);
v_isShared_420_ = v_isSharedCheck_430_;
goto v_resetjp_418_;
}
v_resetjp_418_:
{
lean_object* v_val_421_; lean_object* v___x_423_; 
v_val_421_ = lean_ctor_get(v___x_374_, 0);
lean_inc(v_val_421_);
lean_dec_ref_known(v___x_374_, 1);
if (v_isShared_360_ == 0)
{
v___x_423_ = v___x_359_;
goto v_reusejp_422_;
}
else
{
lean_object* v_reuseFailAlloc_429_; 
v_reuseFailAlloc_429_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_429_, 0, v_decls_356_);
lean_ctor_set(v_reuseFailAlloc_429_, 1, v_cache_357_);
v___x_423_ = v_reuseFailAlloc_429_;
goto v_reusejp_422_;
}
v_reusejp_422_:
{
uint8_t v___x_424_; lean_object* v___x_426_; 
v___x_424_ = 0;
if (v_isShared_420_ == 0)
{
lean_ctor_set(v___x_419_, 0, v_val_421_);
v___x_426_ = v___x_419_;
goto v_reusejp_425_;
}
else
{
lean_object* v_reuseFailAlloc_428_; 
v_reuseFailAlloc_428_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_428_, 0, v_val_421_);
v___x_426_ = v_reuseFailAlloc_428_;
goto v_reusejp_425_;
}
v_reusejp_425_:
{
lean_object* v___x_427_; 
lean_ctor_set_uint8(v___x_426_, sizeof(void*)*1, v___x_424_);
v___x_427_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_427_, 0, v___x_423_);
lean_ctor_set(v___x_427_, 1, v___x_426_);
return v___x_427_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__3(lean_object* v_aig_435_, lean_object* v_input_436_){
_start:
{
lean_object* v_lhs_437_; lean_object* v_rhs_438_; lean_object* v___x_440_; uint8_t v_isShared_441_; uint8_t v_isSharedCheck_453_; 
v_lhs_437_ = lean_ctor_get(v_input_436_, 0);
v_rhs_438_ = lean_ctor_get(v_input_436_, 1);
v_isSharedCheck_453_ = !lean_is_exclusive(v_input_436_);
if (v_isSharedCheck_453_ == 0)
{
v___x_440_ = v_input_436_;
v_isShared_441_ = v_isSharedCheck_453_;
goto v_resetjp_439_;
}
else
{
lean_inc(v_rhs_438_);
lean_inc(v_lhs_437_);
lean_dec(v_input_436_);
v___x_440_ = lean_box(0);
v_isShared_441_ = v_isSharedCheck_453_;
goto v_resetjp_439_;
}
v_resetjp_439_:
{
lean_object* v_gate_442_; lean_object* v_gate_443_; uint8_t v___x_444_; 
v_gate_442_ = lean_ctor_get(v_lhs_437_, 0);
v_gate_443_ = lean_ctor_get(v_rhs_438_, 0);
v___x_444_ = lean_nat_dec_lt(v_gate_442_, v_gate_443_);
if (v___x_444_ == 0)
{
lean_object* v___x_446_; 
if (v_isShared_441_ == 0)
{
lean_ctor_set(v___x_440_, 1, v_lhs_437_);
lean_ctor_set(v___x_440_, 0, v_rhs_438_);
v___x_446_ = v___x_440_;
goto v_reusejp_445_;
}
else
{
lean_object* v_reuseFailAlloc_448_; 
v_reuseFailAlloc_448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_448_, 0, v_rhs_438_);
lean_ctor_set(v_reuseFailAlloc_448_, 1, v_lhs_437_);
v___x_446_ = v_reuseFailAlloc_448_;
goto v_reusejp_445_;
}
v_reusejp_445_:
{
lean_object* v___x_447_; 
v___x_447_ = l_Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__3_spec__7(v_aig_435_, v___x_446_);
return v___x_447_;
}
}
else
{
lean_object* v___x_450_; 
if (v_isShared_441_ == 0)
{
v___x_450_ = v___x_440_;
goto v_reusejp_449_;
}
else
{
lean_object* v_reuseFailAlloc_452_; 
v_reuseFailAlloc_452_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_452_, 0, v_lhs_437_);
lean_ctor_set(v_reuseFailAlloc_452_, 1, v_rhs_438_);
v___x_450_ = v_reuseFailAlloc_452_;
goto v_reusejp_449_;
}
v_reusejp_449_:
{
lean_object* v___x_451_; 
v___x_451_ = l_Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__3_spec__7(v_aig_435_, v___x_450_);
return v___x_451_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkOrCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__6(lean_object* v_aig_454_, lean_object* v_input_455_){
_start:
{
lean_object* v___y_457_; lean_object* v_lhs_497_; lean_object* v_rhs_498_; lean_object* v___x_500_; uint8_t v_isShared_501_; uint8_t v_isSharedCheck_542_; 
v_lhs_497_ = lean_ctor_get(v_input_455_, 0);
v_rhs_498_ = lean_ctor_get(v_input_455_, 1);
v_isSharedCheck_542_ = !lean_is_exclusive(v_input_455_);
if (v_isSharedCheck_542_ == 0)
{
v___x_500_ = v_input_455_;
v_isShared_501_ = v_isSharedCheck_542_;
goto v_resetjp_499_;
}
else
{
lean_inc(v_rhs_498_);
lean_inc(v_lhs_497_);
lean_dec(v_input_455_);
v___x_500_ = lean_box(0);
v_isShared_501_ = v_isSharedCheck_542_;
goto v_resetjp_499_;
}
v___jp_456_:
{
lean_object* v_res_458_; lean_object* v_ref_459_; uint8_t v_invert_460_; 
v_res_458_ = l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__3(v_aig_454_, v___y_457_);
v_ref_459_ = lean_ctor_get(v_res_458_, 1);
lean_inc_ref(v_ref_459_);
v_invert_460_ = lean_ctor_get_uint8(v_ref_459_, sizeof(void*)*1);
if (v_invert_460_ == 0)
{
lean_object* v_aig_461_; lean_object* v___x_463_; uint8_t v_isShared_464_; uint8_t v_isSharedCheck_477_; 
v_aig_461_ = lean_ctor_get(v_res_458_, 0);
v_isSharedCheck_477_ = !lean_is_exclusive(v_res_458_);
if (v_isSharedCheck_477_ == 0)
{
lean_object* v_unused_478_; 
v_unused_478_ = lean_ctor_get(v_res_458_, 1);
lean_dec(v_unused_478_);
v___x_463_ = v_res_458_;
v_isShared_464_ = v_isSharedCheck_477_;
goto v_resetjp_462_;
}
else
{
lean_inc(v_aig_461_);
lean_dec(v_res_458_);
v___x_463_ = lean_box(0);
v_isShared_464_ = v_isSharedCheck_477_;
goto v_resetjp_462_;
}
v_resetjp_462_:
{
lean_object* v_gate_465_; lean_object* v___x_467_; uint8_t v_isShared_468_; uint8_t v_isSharedCheck_476_; 
v_gate_465_ = lean_ctor_get(v_ref_459_, 0);
v_isSharedCheck_476_ = !lean_is_exclusive(v_ref_459_);
if (v_isSharedCheck_476_ == 0)
{
v___x_467_ = v_ref_459_;
v_isShared_468_ = v_isSharedCheck_476_;
goto v_resetjp_466_;
}
else
{
lean_inc(v_gate_465_);
lean_dec(v_ref_459_);
v___x_467_ = lean_box(0);
v_isShared_468_ = v_isSharedCheck_476_;
goto v_resetjp_466_;
}
v_resetjp_466_:
{
uint8_t v___x_469_; lean_object* v___x_471_; 
v___x_469_ = 1;
if (v_isShared_468_ == 0)
{
v___x_471_ = v___x_467_;
goto v_reusejp_470_;
}
else
{
lean_object* v_reuseFailAlloc_475_; 
v_reuseFailAlloc_475_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_475_, 0, v_gate_465_);
v___x_471_ = v_reuseFailAlloc_475_;
goto v_reusejp_470_;
}
v_reusejp_470_:
{
lean_object* v___x_473_; 
lean_ctor_set_uint8(v___x_471_, sizeof(void*)*1, v___x_469_);
if (v_isShared_464_ == 0)
{
lean_ctor_set(v___x_463_, 1, v___x_471_);
v___x_473_ = v___x_463_;
goto v_reusejp_472_;
}
else
{
lean_object* v_reuseFailAlloc_474_; 
v_reuseFailAlloc_474_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_474_, 0, v_aig_461_);
lean_ctor_set(v_reuseFailAlloc_474_, 1, v___x_471_);
v___x_473_ = v_reuseFailAlloc_474_;
goto v_reusejp_472_;
}
v_reusejp_472_:
{
return v___x_473_;
}
}
}
}
}
else
{
lean_object* v_aig_479_; lean_object* v___x_481_; uint8_t v_isShared_482_; uint8_t v_isSharedCheck_495_; 
v_aig_479_ = lean_ctor_get(v_res_458_, 0);
v_isSharedCheck_495_ = !lean_is_exclusive(v_res_458_);
if (v_isSharedCheck_495_ == 0)
{
lean_object* v_unused_496_; 
v_unused_496_ = lean_ctor_get(v_res_458_, 1);
lean_dec(v_unused_496_);
v___x_481_ = v_res_458_;
v_isShared_482_ = v_isSharedCheck_495_;
goto v_resetjp_480_;
}
else
{
lean_inc(v_aig_479_);
lean_dec(v_res_458_);
v___x_481_ = lean_box(0);
v_isShared_482_ = v_isSharedCheck_495_;
goto v_resetjp_480_;
}
v_resetjp_480_:
{
lean_object* v_gate_483_; lean_object* v___x_485_; uint8_t v_isShared_486_; uint8_t v_isSharedCheck_494_; 
v_gate_483_ = lean_ctor_get(v_ref_459_, 0);
v_isSharedCheck_494_ = !lean_is_exclusive(v_ref_459_);
if (v_isSharedCheck_494_ == 0)
{
v___x_485_ = v_ref_459_;
v_isShared_486_ = v_isSharedCheck_494_;
goto v_resetjp_484_;
}
else
{
lean_inc(v_gate_483_);
lean_dec(v_ref_459_);
v___x_485_ = lean_box(0);
v_isShared_486_ = v_isSharedCheck_494_;
goto v_resetjp_484_;
}
v_resetjp_484_:
{
uint8_t v___x_487_; lean_object* v___x_489_; 
v___x_487_ = 0;
if (v_isShared_486_ == 0)
{
v___x_489_ = v___x_485_;
goto v_reusejp_488_;
}
else
{
lean_object* v_reuseFailAlloc_493_; 
v_reuseFailAlloc_493_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_493_, 0, v_gate_483_);
v___x_489_ = v_reuseFailAlloc_493_;
goto v_reusejp_488_;
}
v_reusejp_488_:
{
lean_object* v___x_491_; 
lean_ctor_set_uint8(v___x_489_, sizeof(void*)*1, v___x_487_);
if (v_isShared_482_ == 0)
{
lean_ctor_set(v___x_481_, 1, v___x_489_);
v___x_491_ = v___x_481_;
goto v_reusejp_490_;
}
else
{
lean_object* v_reuseFailAlloc_492_; 
v_reuseFailAlloc_492_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_492_, 0, v_aig_479_);
lean_ctor_set(v_reuseFailAlloc_492_, 1, v___x_489_);
v___x_491_ = v_reuseFailAlloc_492_;
goto v_reusejp_490_;
}
v_reusejp_490_:
{
return v___x_491_;
}
}
}
}
}
}
v_resetjp_499_:
{
lean_object* v_gate_502_; uint8_t v_invert_503_; lean_object* v___x_505_; uint8_t v_isShared_506_; uint8_t v_isSharedCheck_541_; 
v_gate_502_ = lean_ctor_get(v_lhs_497_, 0);
v_invert_503_ = lean_ctor_get_uint8(v_lhs_497_, sizeof(void*)*1);
v_isSharedCheck_541_ = !lean_is_exclusive(v_lhs_497_);
if (v_isSharedCheck_541_ == 0)
{
v___x_505_ = v_lhs_497_;
v_isShared_506_ = v_isSharedCheck_541_;
goto v_resetjp_504_;
}
else
{
lean_inc(v_gate_502_);
lean_dec(v_lhs_497_);
v___x_505_ = lean_box(0);
v_isShared_506_ = v_isSharedCheck_541_;
goto v_resetjp_504_;
}
v_resetjp_504_:
{
uint8_t v___x_507_; lean_object* v___y_509_; 
v___x_507_ = 1;
if (v_invert_503_ == 0)
{
lean_object* v___x_535_; 
if (v_isShared_506_ == 0)
{
v___x_535_ = v___x_505_;
goto v_reusejp_534_;
}
else
{
lean_object* v_reuseFailAlloc_536_; 
v_reuseFailAlloc_536_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_536_, 0, v_gate_502_);
v___x_535_ = v_reuseFailAlloc_536_;
goto v_reusejp_534_;
}
v_reusejp_534_:
{
lean_ctor_set_uint8(v___x_535_, sizeof(void*)*1, v___x_507_);
v___y_509_ = v___x_535_;
goto v___jp_508_;
}
}
else
{
uint8_t v___x_537_; lean_object* v___x_539_; 
v___x_537_ = 0;
if (v_isShared_506_ == 0)
{
v___x_539_ = v___x_505_;
goto v_reusejp_538_;
}
else
{
lean_object* v_reuseFailAlloc_540_; 
v_reuseFailAlloc_540_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_540_, 0, v_gate_502_);
v___x_539_ = v_reuseFailAlloc_540_;
goto v_reusejp_538_;
}
v_reusejp_538_:
{
lean_ctor_set_uint8(v___x_539_, sizeof(void*)*1, v___x_537_);
v___y_509_ = v___x_539_;
goto v___jp_508_;
}
}
v___jp_508_:
{
uint8_t v_invert_510_; 
v_invert_510_ = lean_ctor_get_uint8(v_rhs_498_, sizeof(void*)*1);
if (v_invert_510_ == 0)
{
lean_object* v_gate_511_; lean_object* v___x_513_; uint8_t v_isShared_514_; uint8_t v_isSharedCheck_521_; 
v_gate_511_ = lean_ctor_get(v_rhs_498_, 0);
v_isSharedCheck_521_ = !lean_is_exclusive(v_rhs_498_);
if (v_isSharedCheck_521_ == 0)
{
v___x_513_ = v_rhs_498_;
v_isShared_514_ = v_isSharedCheck_521_;
goto v_resetjp_512_;
}
else
{
lean_inc(v_gate_511_);
lean_dec(v_rhs_498_);
v___x_513_ = lean_box(0);
v_isShared_514_ = v_isSharedCheck_521_;
goto v_resetjp_512_;
}
v_resetjp_512_:
{
lean_object* v___x_516_; 
if (v_isShared_514_ == 0)
{
v___x_516_ = v___x_513_;
goto v_reusejp_515_;
}
else
{
lean_object* v_reuseFailAlloc_520_; 
v_reuseFailAlloc_520_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_520_, 0, v_gate_511_);
v___x_516_ = v_reuseFailAlloc_520_;
goto v_reusejp_515_;
}
v_reusejp_515_:
{
lean_object* v___x_518_; 
lean_ctor_set_uint8(v___x_516_, sizeof(void*)*1, v___x_507_);
if (v_isShared_501_ == 0)
{
lean_ctor_set(v___x_500_, 1, v___x_516_);
lean_ctor_set(v___x_500_, 0, v___y_509_);
v___x_518_ = v___x_500_;
goto v_reusejp_517_;
}
else
{
lean_object* v_reuseFailAlloc_519_; 
v_reuseFailAlloc_519_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_519_, 0, v___y_509_);
lean_ctor_set(v_reuseFailAlloc_519_, 1, v___x_516_);
v___x_518_ = v_reuseFailAlloc_519_;
goto v_reusejp_517_;
}
v_reusejp_517_:
{
v___y_457_ = v___x_518_;
goto v___jp_456_;
}
}
}
}
else
{
lean_object* v_gate_522_; lean_object* v___x_524_; uint8_t v_isShared_525_; uint8_t v_isSharedCheck_533_; 
v_gate_522_ = lean_ctor_get(v_rhs_498_, 0);
v_isSharedCheck_533_ = !lean_is_exclusive(v_rhs_498_);
if (v_isSharedCheck_533_ == 0)
{
v___x_524_ = v_rhs_498_;
v_isShared_525_ = v_isSharedCheck_533_;
goto v_resetjp_523_;
}
else
{
lean_inc(v_gate_522_);
lean_dec(v_rhs_498_);
v___x_524_ = lean_box(0);
v_isShared_525_ = v_isSharedCheck_533_;
goto v_resetjp_523_;
}
v_resetjp_523_:
{
uint8_t v___x_526_; lean_object* v___x_528_; 
v___x_526_ = 0;
if (v_isShared_525_ == 0)
{
v___x_528_ = v___x_524_;
goto v_reusejp_527_;
}
else
{
lean_object* v_reuseFailAlloc_532_; 
v_reuseFailAlloc_532_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_532_, 0, v_gate_522_);
v___x_528_ = v_reuseFailAlloc_532_;
goto v_reusejp_527_;
}
v_reusejp_527_:
{
lean_object* v___x_530_; 
lean_ctor_set_uint8(v___x_528_, sizeof(void*)*1, v___x_526_);
if (v_isShared_501_ == 0)
{
lean_ctor_set(v___x_500_, 1, v___x_528_);
lean_ctor_set(v___x_500_, 0, v___y_509_);
v___x_530_ = v___x_500_;
goto v_reusejp_529_;
}
else
{
lean_object* v_reuseFailAlloc_531_; 
v_reuseFailAlloc_531_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_531_, 0, v___y_509_);
lean_ctor_set(v_reuseFailAlloc_531_, 1, v___x_528_);
v___x_530_ = v_reuseFailAlloc_531_;
goto v_reusejp_529_;
}
v_reusejp_529_:
{
v___y_457_ = v___x_530_;
goto v___jp_456_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkIfCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__7(lean_object* v_aig_543_, lean_object* v_input_544_){
_start:
{
lean_object* v_discr_545_; lean_object* v_lhs_546_; lean_object* v_rhs_547_; lean_object* v___x_548_; lean_object* v_res_549_; lean_object* v_aig_550_; lean_object* v_ref_551_; lean_object* v___x_553_; uint8_t v_isShared_554_; uint8_t v_isSharedCheck_604_; 
v_discr_545_ = lean_ctor_get(v_input_544_, 0);
lean_inc_ref_n(v_discr_545_, 2);
v_lhs_546_ = lean_ctor_get(v_input_544_, 1);
lean_inc_ref(v_lhs_546_);
v_rhs_547_ = lean_ctor_get(v_input_544_, 2);
lean_inc_ref(v_rhs_547_);
lean_dec_ref(v_input_544_);
v___x_548_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_548_, 0, v_discr_545_);
lean_ctor_set(v___x_548_, 1, v_lhs_546_);
v_res_549_ = l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__3(v_aig_543_, v___x_548_);
v_aig_550_ = lean_ctor_get(v_res_549_, 0);
v_ref_551_ = lean_ctor_get(v_res_549_, 1);
v_isSharedCheck_604_ = !lean_is_exclusive(v_res_549_);
if (v_isSharedCheck_604_ == 0)
{
v___x_553_ = v_res_549_;
v_isShared_554_ = v_isSharedCheck_604_;
goto v_resetjp_552_;
}
else
{
lean_inc(v_ref_551_);
lean_inc(v_aig_550_);
lean_dec(v_res_549_);
v___x_553_ = lean_box(0);
v_isShared_554_ = v_isSharedCheck_604_;
goto v_resetjp_552_;
}
v_resetjp_552_:
{
lean_object* v_gate_555_; uint8_t v_invert_556_; lean_object* v___x_558_; uint8_t v_isShared_559_; uint8_t v_isSharedCheck_603_; 
v_gate_555_ = lean_ctor_get(v_discr_545_, 0);
v_invert_556_ = lean_ctor_get_uint8(v_discr_545_, sizeof(void*)*1);
v_isSharedCheck_603_ = !lean_is_exclusive(v_discr_545_);
if (v_isSharedCheck_603_ == 0)
{
v___x_558_ = v_discr_545_;
v_isShared_559_ = v_isSharedCheck_603_;
goto v_resetjp_557_;
}
else
{
lean_inc(v_gate_555_);
lean_dec(v_discr_545_);
v___x_558_ = lean_box(0);
v_isShared_559_ = v_isSharedCheck_603_;
goto v_resetjp_557_;
}
v_resetjp_557_:
{
lean_object* v_gate_560_; uint8_t v_invert_561_; lean_object* v___x_563_; uint8_t v_isShared_564_; uint8_t v_isSharedCheck_602_; 
v_gate_560_ = lean_ctor_get(v_rhs_547_, 0);
v_invert_561_ = lean_ctor_get_uint8(v_rhs_547_, sizeof(void*)*1);
v_isSharedCheck_602_ = !lean_is_exclusive(v_rhs_547_);
if (v_isSharedCheck_602_ == 0)
{
v___x_563_ = v_rhs_547_;
v_isShared_564_ = v_isSharedCheck_602_;
goto v_resetjp_562_;
}
else
{
lean_inc(v_gate_560_);
lean_dec(v_rhs_547_);
v___x_563_ = lean_box(0);
v_isShared_564_ = v_isSharedCheck_602_;
goto v_resetjp_562_;
}
v_resetjp_562_:
{
lean_object* v_aig_566_; lean_object* v_ref_567_; 
if (v_invert_556_ == 0)
{
uint8_t v___x_594_; lean_object* v___x_596_; 
v___x_594_ = 1;
if (v_isShared_559_ == 0)
{
v___x_596_ = v___x_558_;
goto v_reusejp_595_;
}
else
{
lean_object* v_reuseFailAlloc_597_; 
v_reuseFailAlloc_597_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_597_, 0, v_gate_555_);
v___x_596_ = v_reuseFailAlloc_597_;
goto v_reusejp_595_;
}
v_reusejp_595_:
{
lean_ctor_set_uint8(v___x_596_, sizeof(void*)*1, v___x_594_);
v_aig_566_ = v_aig_550_;
v_ref_567_ = v___x_596_;
goto v___jp_565_;
}
}
else
{
uint8_t v___x_598_; lean_object* v___x_600_; 
v___x_598_ = 0;
if (v_isShared_559_ == 0)
{
v___x_600_ = v___x_558_;
goto v_reusejp_599_;
}
else
{
lean_object* v_reuseFailAlloc_601_; 
v_reuseFailAlloc_601_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_601_, 0, v_gate_555_);
v___x_600_ = v_reuseFailAlloc_601_;
goto v_reusejp_599_;
}
v_reusejp_599_:
{
lean_ctor_set_uint8(v___x_600_, sizeof(void*)*1, v___x_598_);
v_aig_566_ = v_aig_550_;
v_ref_567_ = v___x_600_;
goto v___jp_565_;
}
}
v___jp_565_:
{
lean_object* v___x_569_; 
if (v_isShared_564_ == 0)
{
v___x_569_ = v___x_563_;
goto v_reusejp_568_;
}
else
{
lean_object* v_reuseFailAlloc_593_; 
v_reuseFailAlloc_593_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_593_, 0, v_gate_560_);
lean_ctor_set_uint8(v_reuseFailAlloc_593_, sizeof(void*)*1, v_invert_561_);
v___x_569_ = v_reuseFailAlloc_593_;
goto v_reusejp_568_;
}
v_reusejp_568_:
{
lean_object* v___x_571_; 
if (v_isShared_554_ == 0)
{
lean_ctor_set(v___x_553_, 1, v___x_569_);
lean_ctor_set(v___x_553_, 0, v_ref_567_);
v___x_571_ = v___x_553_;
goto v_reusejp_570_;
}
else
{
lean_object* v_reuseFailAlloc_592_; 
v_reuseFailAlloc_592_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_592_, 0, v_ref_567_);
lean_ctor_set(v_reuseFailAlloc_592_, 1, v___x_569_);
v___x_571_ = v_reuseFailAlloc_592_;
goto v_reusejp_570_;
}
v_reusejp_570_:
{
lean_object* v_res_572_; lean_object* v_aig_573_; lean_object* v_ref_574_; lean_object* v___x_576_; uint8_t v_isShared_577_; uint8_t v_isSharedCheck_591_; 
v_res_572_ = l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__3(v_aig_566_, v___x_571_);
v_aig_573_ = lean_ctor_get(v_res_572_, 0);
v_ref_574_ = lean_ctor_get(v_res_572_, 1);
v_isSharedCheck_591_ = !lean_is_exclusive(v_res_572_);
if (v_isSharedCheck_591_ == 0)
{
v___x_576_ = v_res_572_;
v_isShared_577_ = v_isSharedCheck_591_;
goto v_resetjp_575_;
}
else
{
lean_inc(v_ref_574_);
lean_inc(v_aig_573_);
lean_dec(v_res_572_);
v___x_576_ = lean_box(0);
v_isShared_577_ = v_isSharedCheck_591_;
goto v_resetjp_575_;
}
v_resetjp_575_:
{
lean_object* v_gate_578_; uint8_t v_invert_579_; lean_object* v___x_581_; uint8_t v_isShared_582_; uint8_t v_isSharedCheck_590_; 
v_gate_578_ = lean_ctor_get(v_ref_551_, 0);
v_invert_579_ = lean_ctor_get_uint8(v_ref_551_, sizeof(void*)*1);
v_isSharedCheck_590_ = !lean_is_exclusive(v_ref_551_);
if (v_isSharedCheck_590_ == 0)
{
v___x_581_ = v_ref_551_;
v_isShared_582_ = v_isSharedCheck_590_;
goto v_resetjp_580_;
}
else
{
lean_inc(v_gate_578_);
lean_dec(v_ref_551_);
v___x_581_ = lean_box(0);
v_isShared_582_ = v_isSharedCheck_590_;
goto v_resetjp_580_;
}
v_resetjp_580_:
{
lean_object* v_lhsRef_584_; 
if (v_isShared_582_ == 0)
{
v_lhsRef_584_ = v___x_581_;
goto v_reusejp_583_;
}
else
{
lean_object* v_reuseFailAlloc_589_; 
v_reuseFailAlloc_589_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_589_, 0, v_gate_578_);
lean_ctor_set_uint8(v_reuseFailAlloc_589_, sizeof(void*)*1, v_invert_579_);
v_lhsRef_584_ = v_reuseFailAlloc_589_;
goto v_reusejp_583_;
}
v_reusejp_583_:
{
lean_object* v___x_586_; 
if (v_isShared_577_ == 0)
{
lean_ctor_set(v___x_576_, 0, v_lhsRef_584_);
v___x_586_ = v___x_576_;
goto v_reusejp_585_;
}
else
{
lean_object* v_reuseFailAlloc_588_; 
v_reuseFailAlloc_588_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_588_, 0, v_lhsRef_584_);
lean_ctor_set(v_reuseFailAlloc_588_, 1, v_ref_574_);
v___x_586_ = v_reuseFailAlloc_588_;
goto v_reusejp_585_;
}
v_reusejp_585_:
{
lean_object* v___x_587_; 
v___x_587_ = l_Std_Sat_AIG_mkOrCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__6(v_aig_573_, v___x_586_);
return v___x_587_;
}
}
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkBEqCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__5(lean_object* v_aig_605_, lean_object* v_input_606_){
_start:
{
lean_object* v___y_608_; lean_object* v___y_609_; lean_object* v___y_610_; lean_object* v_lhs_613_; lean_object* v_rhs_614_; lean_object* v___x_616_; uint8_t v_isShared_617_; uint8_t v_isSharedCheck_727_; 
v_lhs_613_ = lean_ctor_get(v_input_606_, 0);
v_rhs_614_ = lean_ctor_get(v_input_606_, 1);
v_isSharedCheck_727_ = !lean_is_exclusive(v_input_606_);
if (v_isSharedCheck_727_ == 0)
{
v___x_616_ = v_input_606_;
v_isShared_617_ = v_isSharedCheck_727_;
goto v_resetjp_615_;
}
else
{
lean_inc(v_rhs_614_);
lean_inc(v_lhs_613_);
lean_dec(v_input_606_);
v___x_616_ = lean_box(0);
v_isShared_617_ = v_isSharedCheck_727_;
goto v_resetjp_615_;
}
v___jp_607_:
{
lean_object* v___x_611_; lean_object* v___x_612_; 
v___x_611_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_611_, 0, v___y_608_);
lean_ctor_set(v___x_611_, 1, v___y_610_);
v___x_612_ = l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__3(v___y_609_, v___x_611_);
return v___x_612_;
}
v_resetjp_615_:
{
lean_object* v_gate_618_; uint8_t v_invert_619_; lean_object* v___x_621_; uint8_t v_isShared_622_; uint8_t v_isSharedCheck_726_; 
v_gate_618_ = lean_ctor_get(v_lhs_613_, 0);
v_invert_619_ = lean_ctor_get_uint8(v_lhs_613_, sizeof(void*)*1);
v_isSharedCheck_726_ = !lean_is_exclusive(v_lhs_613_);
if (v_isSharedCheck_726_ == 0)
{
v___x_621_ = v_lhs_613_;
v_isShared_622_ = v_isSharedCheck_726_;
goto v_resetjp_620_;
}
else
{
lean_inc(v_gate_618_);
lean_dec(v_lhs_613_);
v___x_621_ = lean_box(0);
v_isShared_622_ = v_isSharedCheck_726_;
goto v_resetjp_620_;
}
v_resetjp_620_:
{
uint8_t v___x_623_; uint8_t v___x_624_; lean_object* v___y_626_; lean_object* v___y_627_; lean_object* v___y_628_; lean_object* v___y_647_; lean_object* v___y_648_; lean_object* v___y_649_; lean_object* v___y_673_; lean_object* v___y_674_; uint8_t v___y_675_; lean_object* v___y_676_; lean_object* v___y_677_; lean_object* v___y_691_; lean_object* v___y_716_; 
v___x_623_ = 0;
v___x_624_ = 1;
if (v_invert_619_ == 0)
{
lean_object* v___x_724_; 
lean_inc(v_gate_618_);
v___x_724_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_724_, 0, v_gate_618_);
lean_ctor_set_uint8(v___x_724_, sizeof(void*)*1, v___x_623_);
v___y_716_ = v___x_724_;
goto v___jp_715_;
}
else
{
lean_object* v___x_725_; 
lean_inc(v_gate_618_);
v___x_725_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_725_, 0, v_gate_618_);
lean_ctor_set_uint8(v___x_725_, sizeof(void*)*1, v___x_624_);
v___y_716_ = v___x_725_;
goto v___jp_715_;
}
v___jp_625_:
{
uint8_t v_invert_629_; 
v_invert_629_ = lean_ctor_get_uint8(v___y_626_, sizeof(void*)*1);
if (v_invert_629_ == 0)
{
lean_object* v_gate_630_; lean_object* v___x_632_; uint8_t v_isShared_633_; uint8_t v_isSharedCheck_637_; 
v_gate_630_ = lean_ctor_get(v___y_626_, 0);
v_isSharedCheck_637_ = !lean_is_exclusive(v___y_626_);
if (v_isSharedCheck_637_ == 0)
{
v___x_632_ = v___y_626_;
v_isShared_633_ = v_isSharedCheck_637_;
goto v_resetjp_631_;
}
else
{
lean_inc(v_gate_630_);
lean_dec(v___y_626_);
v___x_632_ = lean_box(0);
v_isShared_633_ = v_isSharedCheck_637_;
goto v_resetjp_631_;
}
v_resetjp_631_:
{
lean_object* v___x_635_; 
if (v_isShared_633_ == 0)
{
v___x_635_ = v___x_632_;
goto v_reusejp_634_;
}
else
{
lean_object* v_reuseFailAlloc_636_; 
v_reuseFailAlloc_636_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_636_, 0, v_gate_630_);
v___x_635_ = v_reuseFailAlloc_636_;
goto v_reusejp_634_;
}
v_reusejp_634_:
{
lean_ctor_set_uint8(v___x_635_, sizeof(void*)*1, v___x_624_);
v___y_608_ = v___y_628_;
v___y_609_ = v___y_627_;
v___y_610_ = v___x_635_;
goto v___jp_607_;
}
}
}
else
{
lean_object* v_gate_638_; lean_object* v___x_640_; uint8_t v_isShared_641_; uint8_t v_isSharedCheck_645_; 
v_gate_638_ = lean_ctor_get(v___y_626_, 0);
v_isSharedCheck_645_ = !lean_is_exclusive(v___y_626_);
if (v_isSharedCheck_645_ == 0)
{
v___x_640_ = v___y_626_;
v_isShared_641_ = v_isSharedCheck_645_;
goto v_resetjp_639_;
}
else
{
lean_inc(v_gate_638_);
lean_dec(v___y_626_);
v___x_640_ = lean_box(0);
v_isShared_641_ = v_isSharedCheck_645_;
goto v_resetjp_639_;
}
v_resetjp_639_:
{
lean_object* v___x_643_; 
if (v_isShared_641_ == 0)
{
v___x_643_ = v___x_640_;
goto v_reusejp_642_;
}
else
{
lean_object* v_reuseFailAlloc_644_; 
v_reuseFailAlloc_644_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_644_, 0, v_gate_638_);
v___x_643_ = v_reuseFailAlloc_644_;
goto v_reusejp_642_;
}
v_reusejp_642_:
{
lean_ctor_set_uint8(v___x_643_, sizeof(void*)*1, v___x_623_);
v___y_608_ = v___y_628_;
v___y_609_ = v___y_627_;
v___y_610_ = v___x_643_;
goto v___jp_607_;
}
}
}
}
v___jp_646_:
{
lean_object* v_res_650_; uint8_t v_invert_651_; 
v_res_650_ = l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__3(v___y_648_, v___y_649_);
v_invert_651_ = lean_ctor_get_uint8(v___y_647_, sizeof(void*)*1);
if (v_invert_651_ == 0)
{
lean_object* v_aig_652_; lean_object* v_ref_653_; lean_object* v_gate_654_; lean_object* v___x_656_; uint8_t v_isShared_657_; uint8_t v_isSharedCheck_661_; 
v_aig_652_ = lean_ctor_get(v_res_650_, 0);
lean_inc_ref(v_aig_652_);
v_ref_653_ = lean_ctor_get(v_res_650_, 1);
lean_inc_ref(v_ref_653_);
lean_dec_ref(v_res_650_);
v_gate_654_ = lean_ctor_get(v___y_647_, 0);
v_isSharedCheck_661_ = !lean_is_exclusive(v___y_647_);
if (v_isSharedCheck_661_ == 0)
{
v___x_656_ = v___y_647_;
v_isShared_657_ = v_isSharedCheck_661_;
goto v_resetjp_655_;
}
else
{
lean_inc(v_gate_654_);
lean_dec(v___y_647_);
v___x_656_ = lean_box(0);
v_isShared_657_ = v_isSharedCheck_661_;
goto v_resetjp_655_;
}
v_resetjp_655_:
{
lean_object* v___x_659_; 
if (v_isShared_657_ == 0)
{
v___x_659_ = v___x_656_;
goto v_reusejp_658_;
}
else
{
lean_object* v_reuseFailAlloc_660_; 
v_reuseFailAlloc_660_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_660_, 0, v_gate_654_);
v___x_659_ = v_reuseFailAlloc_660_;
goto v_reusejp_658_;
}
v_reusejp_658_:
{
lean_ctor_set_uint8(v___x_659_, sizeof(void*)*1, v___x_624_);
v___y_626_ = v_ref_653_;
v___y_627_ = v_aig_652_;
v___y_628_ = v___x_659_;
goto v___jp_625_;
}
}
}
else
{
lean_object* v_aig_662_; lean_object* v_ref_663_; lean_object* v_gate_664_; lean_object* v___x_666_; uint8_t v_isShared_667_; uint8_t v_isSharedCheck_671_; 
v_aig_662_ = lean_ctor_get(v_res_650_, 0);
lean_inc_ref(v_aig_662_);
v_ref_663_ = lean_ctor_get(v_res_650_, 1);
lean_inc_ref(v_ref_663_);
lean_dec_ref(v_res_650_);
v_gate_664_ = lean_ctor_get(v___y_647_, 0);
v_isSharedCheck_671_ = !lean_is_exclusive(v___y_647_);
if (v_isSharedCheck_671_ == 0)
{
v___x_666_ = v___y_647_;
v_isShared_667_ = v_isSharedCheck_671_;
goto v_resetjp_665_;
}
else
{
lean_inc(v_gate_664_);
lean_dec(v___y_647_);
v___x_666_ = lean_box(0);
v_isShared_667_ = v_isSharedCheck_671_;
goto v_resetjp_665_;
}
v_resetjp_665_:
{
lean_object* v___x_669_; 
if (v_isShared_667_ == 0)
{
v___x_669_ = v___x_666_;
goto v_reusejp_668_;
}
else
{
lean_object* v_reuseFailAlloc_670_; 
v_reuseFailAlloc_670_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_670_, 0, v_gate_664_);
v___x_669_ = v_reuseFailAlloc_670_;
goto v_reusejp_668_;
}
v_reusejp_668_:
{
lean_ctor_set_uint8(v___x_669_, sizeof(void*)*1, v___x_623_);
v___y_626_ = v_ref_663_;
v___y_627_ = v_aig_662_;
v___y_628_ = v___x_669_;
goto v___jp_625_;
}
}
}
}
v___jp_672_:
{
if (v___y_675_ == 0)
{
lean_object* v___x_679_; 
if (v_isShared_622_ == 0)
{
lean_ctor_set(v___x_621_, 0, v___y_674_);
v___x_679_ = v___x_621_;
goto v_reusejp_678_;
}
else
{
lean_object* v_reuseFailAlloc_683_; 
v_reuseFailAlloc_683_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_683_, 0, v___y_674_);
v___x_679_ = v_reuseFailAlloc_683_;
goto v_reusejp_678_;
}
v_reusejp_678_:
{
lean_object* v___x_681_; 
lean_ctor_set_uint8(v___x_679_, sizeof(void*)*1, v___x_623_);
if (v_isShared_617_ == 0)
{
lean_ctor_set(v___x_616_, 1, v___x_679_);
lean_ctor_set(v___x_616_, 0, v___y_677_);
v___x_681_ = v___x_616_;
goto v_reusejp_680_;
}
else
{
lean_object* v_reuseFailAlloc_682_; 
v_reuseFailAlloc_682_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_682_, 0, v___y_677_);
lean_ctor_set(v_reuseFailAlloc_682_, 1, v___x_679_);
v___x_681_ = v_reuseFailAlloc_682_;
goto v_reusejp_680_;
}
v_reusejp_680_:
{
v___y_647_ = v___y_673_;
v___y_648_ = v___y_676_;
v___y_649_ = v___x_681_;
goto v___jp_646_;
}
}
}
else
{
lean_object* v___x_685_; 
if (v_isShared_622_ == 0)
{
lean_ctor_set(v___x_621_, 0, v___y_674_);
v___x_685_ = v___x_621_;
goto v_reusejp_684_;
}
else
{
lean_object* v_reuseFailAlloc_689_; 
v_reuseFailAlloc_689_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_689_, 0, v___y_674_);
v___x_685_ = v_reuseFailAlloc_689_;
goto v_reusejp_684_;
}
v_reusejp_684_:
{
lean_object* v___x_687_; 
lean_ctor_set_uint8(v___x_685_, sizeof(void*)*1, v___x_624_);
if (v_isShared_617_ == 0)
{
lean_ctor_set(v___x_616_, 1, v___x_685_);
lean_ctor_set(v___x_616_, 0, v___y_677_);
v___x_687_ = v___x_616_;
goto v_reusejp_686_;
}
else
{
lean_object* v_reuseFailAlloc_688_; 
v_reuseFailAlloc_688_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_688_, 0, v___y_677_);
lean_ctor_set(v_reuseFailAlloc_688_, 1, v___x_685_);
v___x_687_ = v_reuseFailAlloc_688_;
goto v_reusejp_686_;
}
v_reusejp_686_:
{
v___y_647_ = v___y_673_;
v___y_648_ = v___y_676_;
v___y_649_ = v___x_687_;
goto v___jp_646_;
}
}
}
}
v___jp_690_:
{
lean_object* v_res_692_; 
v_res_692_ = l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__3(v_aig_605_, v___y_691_);
if (v_invert_619_ == 0)
{
lean_object* v_aig_693_; lean_object* v_ref_694_; lean_object* v_gate_695_; uint8_t v_invert_696_; lean_object* v___x_698_; uint8_t v_isShared_699_; uint8_t v_isSharedCheck_703_; 
v_aig_693_ = lean_ctor_get(v_res_692_, 0);
lean_inc_ref(v_aig_693_);
v_ref_694_ = lean_ctor_get(v_res_692_, 1);
lean_inc_ref(v_ref_694_);
lean_dec_ref(v_res_692_);
v_gate_695_ = lean_ctor_get(v_rhs_614_, 0);
v_invert_696_ = lean_ctor_get_uint8(v_rhs_614_, sizeof(void*)*1);
v_isSharedCheck_703_ = !lean_is_exclusive(v_rhs_614_);
if (v_isSharedCheck_703_ == 0)
{
v___x_698_ = v_rhs_614_;
v_isShared_699_ = v_isSharedCheck_703_;
goto v_resetjp_697_;
}
else
{
lean_inc(v_gate_695_);
lean_dec(v_rhs_614_);
v___x_698_ = lean_box(0);
v_isShared_699_ = v_isSharedCheck_703_;
goto v_resetjp_697_;
}
v_resetjp_697_:
{
lean_object* v___x_701_; 
if (v_isShared_699_ == 0)
{
lean_ctor_set(v___x_698_, 0, v_gate_618_);
v___x_701_ = v___x_698_;
goto v_reusejp_700_;
}
else
{
lean_object* v_reuseFailAlloc_702_; 
v_reuseFailAlloc_702_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_702_, 0, v_gate_618_);
v___x_701_ = v_reuseFailAlloc_702_;
goto v_reusejp_700_;
}
v_reusejp_700_:
{
lean_ctor_set_uint8(v___x_701_, sizeof(void*)*1, v___x_624_);
v___y_673_ = v_ref_694_;
v___y_674_ = v_gate_695_;
v___y_675_ = v_invert_696_;
v___y_676_ = v_aig_693_;
v___y_677_ = v___x_701_;
goto v___jp_672_;
}
}
}
else
{
lean_object* v_aig_704_; lean_object* v_ref_705_; lean_object* v_gate_706_; uint8_t v_invert_707_; lean_object* v___x_709_; uint8_t v_isShared_710_; uint8_t v_isSharedCheck_714_; 
v_aig_704_ = lean_ctor_get(v_res_692_, 0);
lean_inc_ref(v_aig_704_);
v_ref_705_ = lean_ctor_get(v_res_692_, 1);
lean_inc_ref(v_ref_705_);
lean_dec_ref(v_res_692_);
v_gate_706_ = lean_ctor_get(v_rhs_614_, 0);
v_invert_707_ = lean_ctor_get_uint8(v_rhs_614_, sizeof(void*)*1);
v_isSharedCheck_714_ = !lean_is_exclusive(v_rhs_614_);
if (v_isSharedCheck_714_ == 0)
{
v___x_709_ = v_rhs_614_;
v_isShared_710_ = v_isSharedCheck_714_;
goto v_resetjp_708_;
}
else
{
lean_inc(v_gate_706_);
lean_dec(v_rhs_614_);
v___x_709_ = lean_box(0);
v_isShared_710_ = v_isSharedCheck_714_;
goto v_resetjp_708_;
}
v_resetjp_708_:
{
lean_object* v___x_712_; 
if (v_isShared_710_ == 0)
{
lean_ctor_set(v___x_709_, 0, v_gate_618_);
v___x_712_ = v___x_709_;
goto v_reusejp_711_;
}
else
{
lean_object* v_reuseFailAlloc_713_; 
v_reuseFailAlloc_713_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_713_, 0, v_gate_618_);
v___x_712_ = v_reuseFailAlloc_713_;
goto v_reusejp_711_;
}
v_reusejp_711_:
{
lean_ctor_set_uint8(v___x_712_, sizeof(void*)*1, v___x_623_);
v___y_673_ = v_ref_705_;
v___y_674_ = v_gate_706_;
v___y_675_ = v_invert_707_;
v___y_676_ = v_aig_704_;
v___y_677_ = v___x_712_;
goto v___jp_672_;
}
}
}
}
v___jp_715_:
{
uint8_t v_invert_717_; 
v_invert_717_ = lean_ctor_get_uint8(v_rhs_614_, sizeof(void*)*1);
if (v_invert_717_ == 0)
{
lean_object* v_gate_718_; lean_object* v___x_719_; lean_object* v___x_720_; 
v_gate_718_ = lean_ctor_get(v_rhs_614_, 0);
lean_inc(v_gate_718_);
v___x_719_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_719_, 0, v_gate_718_);
lean_ctor_set_uint8(v___x_719_, sizeof(void*)*1, v___x_624_);
v___x_720_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_720_, 0, v___y_716_);
lean_ctor_set(v___x_720_, 1, v___x_719_);
v___y_691_ = v___x_720_;
goto v___jp_690_;
}
else
{
lean_object* v_gate_721_; lean_object* v___x_722_; lean_object* v___x_723_; 
v_gate_721_ = lean_ctor_get(v_rhs_614_, 0);
lean_inc(v_gate_721_);
v___x_722_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_722_, 0, v_gate_721_);
lean_ctor_set_uint8(v___x_722_, sizeof(void*)*1, v___x_623_);
v___x_723_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_723_, 0, v___y_716_);
lean_ctor_set(v___x_723_, 1, v___x_722_);
v___y_691_ = v___x_723_;
goto v___jp_690_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkXorCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__4(lean_object* v_aig_728_, lean_object* v_input_729_){
_start:
{
lean_object* v___y_731_; lean_object* v___y_732_; lean_object* v___y_733_; lean_object* v___y_737_; lean_object* v___y_738_; lean_object* v___y_739_; lean_object* v_res_759_; lean_object* v_aig_760_; lean_object* v_ref_761_; lean_object* v___y_763_; lean_object* v_lhs_788_; lean_object* v_rhs_789_; lean_object* v___x_791_; uint8_t v_isShared_792_; uint8_t v_isSharedCheck_828_; 
lean_inc_ref(v_input_729_);
v_res_759_ = l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__3(v_aig_728_, v_input_729_);
v_aig_760_ = lean_ctor_get(v_res_759_, 0);
lean_inc_ref(v_aig_760_);
v_ref_761_ = lean_ctor_get(v_res_759_, 1);
lean_inc_ref(v_ref_761_);
lean_dec_ref(v_res_759_);
v_lhs_788_ = lean_ctor_get(v_input_729_, 0);
v_rhs_789_ = lean_ctor_get(v_input_729_, 1);
v_isSharedCheck_828_ = !lean_is_exclusive(v_input_729_);
if (v_isSharedCheck_828_ == 0)
{
v___x_791_ = v_input_729_;
v_isShared_792_ = v_isSharedCheck_828_;
goto v_resetjp_790_;
}
else
{
lean_inc(v_rhs_789_);
lean_inc(v_lhs_788_);
lean_dec(v_input_729_);
v___x_791_ = lean_box(0);
v_isShared_792_ = v_isSharedCheck_828_;
goto v_resetjp_790_;
}
v___jp_730_:
{
lean_object* v___x_734_; lean_object* v___x_735_; 
v___x_734_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_734_, 0, v___y_731_);
lean_ctor_set(v___x_734_, 1, v___y_733_);
v___x_735_ = l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__3(v___y_732_, v___x_734_);
return v___x_735_;
}
v___jp_736_:
{
uint8_t v_invert_740_; 
v_invert_740_ = lean_ctor_get_uint8(v___y_738_, sizeof(void*)*1);
if (v_invert_740_ == 0)
{
lean_object* v_gate_741_; lean_object* v___x_743_; uint8_t v_isShared_744_; uint8_t v_isSharedCheck_749_; 
v_gate_741_ = lean_ctor_get(v___y_738_, 0);
v_isSharedCheck_749_ = !lean_is_exclusive(v___y_738_);
if (v_isSharedCheck_749_ == 0)
{
v___x_743_ = v___y_738_;
v_isShared_744_ = v_isSharedCheck_749_;
goto v_resetjp_742_;
}
else
{
lean_inc(v_gate_741_);
lean_dec(v___y_738_);
v___x_743_ = lean_box(0);
v_isShared_744_ = v_isSharedCheck_749_;
goto v_resetjp_742_;
}
v_resetjp_742_:
{
uint8_t v___x_745_; lean_object* v___x_747_; 
v___x_745_ = 1;
if (v_isShared_744_ == 0)
{
v___x_747_ = v___x_743_;
goto v_reusejp_746_;
}
else
{
lean_object* v_reuseFailAlloc_748_; 
v_reuseFailAlloc_748_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_748_, 0, v_gate_741_);
v___x_747_ = v_reuseFailAlloc_748_;
goto v_reusejp_746_;
}
v_reusejp_746_:
{
lean_ctor_set_uint8(v___x_747_, sizeof(void*)*1, v___x_745_);
v___y_731_ = v___y_739_;
v___y_732_ = v___y_737_;
v___y_733_ = v___x_747_;
goto v___jp_730_;
}
}
}
else
{
lean_object* v_gate_750_; lean_object* v___x_752_; uint8_t v_isShared_753_; uint8_t v_isSharedCheck_758_; 
v_gate_750_ = lean_ctor_get(v___y_738_, 0);
v_isSharedCheck_758_ = !lean_is_exclusive(v___y_738_);
if (v_isSharedCheck_758_ == 0)
{
v___x_752_ = v___y_738_;
v_isShared_753_ = v_isSharedCheck_758_;
goto v_resetjp_751_;
}
else
{
lean_inc(v_gate_750_);
lean_dec(v___y_738_);
v___x_752_ = lean_box(0);
v_isShared_753_ = v_isSharedCheck_758_;
goto v_resetjp_751_;
}
v_resetjp_751_:
{
uint8_t v___x_754_; lean_object* v___x_756_; 
v___x_754_ = 0;
if (v_isShared_753_ == 0)
{
v___x_756_ = v___x_752_;
goto v_reusejp_755_;
}
else
{
lean_object* v_reuseFailAlloc_757_; 
v_reuseFailAlloc_757_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_757_, 0, v_gate_750_);
v___x_756_ = v_reuseFailAlloc_757_;
goto v_reusejp_755_;
}
v_reusejp_755_:
{
lean_ctor_set_uint8(v___x_756_, sizeof(void*)*1, v___x_754_);
v___y_731_ = v___y_739_;
v___y_732_ = v___y_737_;
v___y_733_ = v___x_756_;
goto v___jp_730_;
}
}
}
}
v___jp_762_:
{
lean_object* v_res_764_; uint8_t v_invert_765_; 
v_res_764_ = l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__3(v_aig_760_, v___y_763_);
v_invert_765_ = lean_ctor_get_uint8(v_ref_761_, sizeof(void*)*1);
if (v_invert_765_ == 0)
{
lean_object* v_aig_766_; lean_object* v_ref_767_; lean_object* v_gate_768_; lean_object* v___x_770_; uint8_t v_isShared_771_; uint8_t v_isSharedCheck_776_; 
v_aig_766_ = lean_ctor_get(v_res_764_, 0);
lean_inc_ref(v_aig_766_);
v_ref_767_ = lean_ctor_get(v_res_764_, 1);
lean_inc_ref(v_ref_767_);
lean_dec_ref(v_res_764_);
v_gate_768_ = lean_ctor_get(v_ref_761_, 0);
v_isSharedCheck_776_ = !lean_is_exclusive(v_ref_761_);
if (v_isSharedCheck_776_ == 0)
{
v___x_770_ = v_ref_761_;
v_isShared_771_ = v_isSharedCheck_776_;
goto v_resetjp_769_;
}
else
{
lean_inc(v_gate_768_);
lean_dec(v_ref_761_);
v___x_770_ = lean_box(0);
v_isShared_771_ = v_isSharedCheck_776_;
goto v_resetjp_769_;
}
v_resetjp_769_:
{
uint8_t v___x_772_; lean_object* v___x_774_; 
v___x_772_ = 1;
if (v_isShared_771_ == 0)
{
v___x_774_ = v___x_770_;
goto v_reusejp_773_;
}
else
{
lean_object* v_reuseFailAlloc_775_; 
v_reuseFailAlloc_775_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_775_, 0, v_gate_768_);
v___x_774_ = v_reuseFailAlloc_775_;
goto v_reusejp_773_;
}
v_reusejp_773_:
{
lean_ctor_set_uint8(v___x_774_, sizeof(void*)*1, v___x_772_);
v___y_737_ = v_aig_766_;
v___y_738_ = v_ref_767_;
v___y_739_ = v___x_774_;
goto v___jp_736_;
}
}
}
else
{
lean_object* v_aig_777_; lean_object* v_ref_778_; lean_object* v_gate_779_; lean_object* v___x_781_; uint8_t v_isShared_782_; uint8_t v_isSharedCheck_787_; 
v_aig_777_ = lean_ctor_get(v_res_764_, 0);
lean_inc_ref(v_aig_777_);
v_ref_778_ = lean_ctor_get(v_res_764_, 1);
lean_inc_ref(v_ref_778_);
lean_dec_ref(v_res_764_);
v_gate_779_ = lean_ctor_get(v_ref_761_, 0);
v_isSharedCheck_787_ = !lean_is_exclusive(v_ref_761_);
if (v_isSharedCheck_787_ == 0)
{
v___x_781_ = v_ref_761_;
v_isShared_782_ = v_isSharedCheck_787_;
goto v_resetjp_780_;
}
else
{
lean_inc(v_gate_779_);
lean_dec(v_ref_761_);
v___x_781_ = lean_box(0);
v_isShared_782_ = v_isSharedCheck_787_;
goto v_resetjp_780_;
}
v_resetjp_780_:
{
uint8_t v___x_783_; lean_object* v___x_785_; 
v___x_783_ = 0;
if (v_isShared_782_ == 0)
{
v___x_785_ = v___x_781_;
goto v_reusejp_784_;
}
else
{
lean_object* v_reuseFailAlloc_786_; 
v_reuseFailAlloc_786_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_786_, 0, v_gate_779_);
v___x_785_ = v_reuseFailAlloc_786_;
goto v_reusejp_784_;
}
v_reusejp_784_:
{
lean_ctor_set_uint8(v___x_785_, sizeof(void*)*1, v___x_783_);
v___y_737_ = v_aig_777_;
v___y_738_ = v_ref_778_;
v___y_739_ = v___x_785_;
goto v___jp_736_;
}
}
}
}
v_resetjp_790_:
{
lean_object* v_gate_793_; uint8_t v_invert_794_; lean_object* v___x_796_; uint8_t v_isShared_797_; uint8_t v_isSharedCheck_827_; 
v_gate_793_ = lean_ctor_get(v_lhs_788_, 0);
v_invert_794_ = lean_ctor_get_uint8(v_lhs_788_, sizeof(void*)*1);
v_isSharedCheck_827_ = !lean_is_exclusive(v_lhs_788_);
if (v_isSharedCheck_827_ == 0)
{
v___x_796_ = v_lhs_788_;
v_isShared_797_ = v_isSharedCheck_827_;
goto v_resetjp_795_;
}
else
{
lean_inc(v_gate_793_);
lean_dec(v_lhs_788_);
v___x_796_ = lean_box(0);
v_isShared_797_ = v_isSharedCheck_827_;
goto v_resetjp_795_;
}
v_resetjp_795_:
{
lean_object* v_gate_798_; uint8_t v_invert_799_; lean_object* v___x_801_; uint8_t v_isShared_802_; uint8_t v_isSharedCheck_826_; 
v_gate_798_ = lean_ctor_get(v_rhs_789_, 0);
v_invert_799_ = lean_ctor_get_uint8(v_rhs_789_, sizeof(void*)*1);
v_isSharedCheck_826_ = !lean_is_exclusive(v_rhs_789_);
if (v_isSharedCheck_826_ == 0)
{
v___x_801_ = v_rhs_789_;
v_isShared_802_ = v_isSharedCheck_826_;
goto v_resetjp_800_;
}
else
{
lean_inc(v_gate_798_);
lean_dec(v_rhs_789_);
v___x_801_ = lean_box(0);
v_isShared_802_ = v_isSharedCheck_826_;
goto v_resetjp_800_;
}
v_resetjp_800_:
{
uint8_t v___x_803_; lean_object* v___y_805_; 
v___x_803_ = 1;
if (v_invert_794_ == 0)
{
lean_object* v___x_820_; 
if (v_isShared_797_ == 0)
{
v___x_820_ = v___x_796_;
goto v_reusejp_819_;
}
else
{
lean_object* v_reuseFailAlloc_821_; 
v_reuseFailAlloc_821_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_821_, 0, v_gate_793_);
v___x_820_ = v_reuseFailAlloc_821_;
goto v_reusejp_819_;
}
v_reusejp_819_:
{
lean_ctor_set_uint8(v___x_820_, sizeof(void*)*1, v___x_803_);
v___y_805_ = v___x_820_;
goto v___jp_804_;
}
}
else
{
uint8_t v___x_822_; lean_object* v___x_824_; 
v___x_822_ = 0;
if (v_isShared_797_ == 0)
{
v___x_824_ = v___x_796_;
goto v_reusejp_823_;
}
else
{
lean_object* v_reuseFailAlloc_825_; 
v_reuseFailAlloc_825_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_825_, 0, v_gate_793_);
v___x_824_ = v_reuseFailAlloc_825_;
goto v_reusejp_823_;
}
v_reusejp_823_:
{
lean_ctor_set_uint8(v___x_824_, sizeof(void*)*1, v___x_822_);
v___y_805_ = v___x_824_;
goto v___jp_804_;
}
}
v___jp_804_:
{
if (v_invert_799_ == 0)
{
lean_object* v___x_807_; 
if (v_isShared_802_ == 0)
{
v___x_807_ = v___x_801_;
goto v_reusejp_806_;
}
else
{
lean_object* v_reuseFailAlloc_811_; 
v_reuseFailAlloc_811_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_811_, 0, v_gate_798_);
v___x_807_ = v_reuseFailAlloc_811_;
goto v_reusejp_806_;
}
v_reusejp_806_:
{
lean_object* v___x_809_; 
lean_ctor_set_uint8(v___x_807_, sizeof(void*)*1, v___x_803_);
if (v_isShared_792_ == 0)
{
lean_ctor_set(v___x_791_, 1, v___x_807_);
lean_ctor_set(v___x_791_, 0, v___y_805_);
v___x_809_ = v___x_791_;
goto v_reusejp_808_;
}
else
{
lean_object* v_reuseFailAlloc_810_; 
v_reuseFailAlloc_810_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_810_, 0, v___y_805_);
lean_ctor_set(v_reuseFailAlloc_810_, 1, v___x_807_);
v___x_809_ = v_reuseFailAlloc_810_;
goto v_reusejp_808_;
}
v_reusejp_808_:
{
v___y_763_ = v___x_809_;
goto v___jp_762_;
}
}
}
else
{
uint8_t v___x_812_; lean_object* v___x_814_; 
v___x_812_ = 0;
if (v_isShared_802_ == 0)
{
v___x_814_ = v___x_801_;
goto v_reusejp_813_;
}
else
{
lean_object* v_reuseFailAlloc_818_; 
v_reuseFailAlloc_818_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_818_, 0, v_gate_798_);
v___x_814_ = v_reuseFailAlloc_818_;
goto v_reusejp_813_;
}
v_reusejp_813_:
{
lean_object* v___x_816_; 
lean_ctor_set_uint8(v___x_814_, sizeof(void*)*1, v___x_812_);
if (v_isShared_792_ == 0)
{
lean_ctor_set(v___x_791_, 1, v___x_814_);
lean_ctor_set(v___x_791_, 0, v___y_805_);
v___x_816_ = v___x_791_;
goto v_reusejp_815_;
}
else
{
lean_object* v_reuseFailAlloc_817_; 
v_reuseFailAlloc_817_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_817_, 0, v___y_805_);
lean_ctor_set(v_reuseFailAlloc_817_, 1, v___x_814_);
v___x_816_ = v_reuseFailAlloc_817_;
goto v_reusejp_815_;
}
v_reusejp_815_:
{
v___y_763_ = v___x_816_;
goto v___jp_762_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_goCache_spec__1_spec__3_spec__5_spec__11___redArg(lean_object* v_x_829_, lean_object* v_x_830_){
_start:
{
if (lean_obj_tag(v_x_830_) == 0)
{
return v_x_829_;
}
else
{
lean_object* v_key_831_; lean_object* v_value_832_; lean_object* v_tail_833_; lean_object* v___x_835_; uint8_t v_isShared_836_; uint8_t v_isSharedCheck_861_; 
v_key_831_ = lean_ctor_get(v_x_830_, 0);
v_value_832_ = lean_ctor_get(v_x_830_, 1);
v_tail_833_ = lean_ctor_get(v_x_830_, 2);
v_isSharedCheck_861_ = !lean_is_exclusive(v_x_830_);
if (v_isSharedCheck_861_ == 0)
{
v___x_835_ = v_x_830_;
v_isShared_836_ = v_isSharedCheck_861_;
goto v_resetjp_834_;
}
else
{
lean_inc(v_tail_833_);
lean_inc(v_value_832_);
lean_inc(v_key_831_);
lean_dec(v_x_830_);
v___x_835_ = lean_box(0);
v_isShared_836_ = v_isSharedCheck_861_;
goto v_resetjp_834_;
}
v_resetjp_834_:
{
lean_object* v___x_837_; uint64_t v___y_839_; 
v___x_837_ = lean_array_get_size(v_x_829_);
switch(lean_obj_tag(v_key_831_))
{
case 1:
{
uint64_t v_hashCode_857_; 
v_hashCode_857_ = lean_ctor_get_uint64(v_key_831_, 0);
v___y_839_ = v_hashCode_857_;
goto v___jp_838_;
}
case 3:
{
uint64_t v_hashCode_858_; 
v_hashCode_858_ = lean_ctor_get_uint64(v_key_831_, sizeof(void*)*2);
v___y_839_ = v_hashCode_858_;
goto v___jp_838_;
}
case 4:
{
uint64_t v_hashCode_859_; 
v_hashCode_859_ = lean_ctor_get_uint64(v_key_831_, sizeof(void*)*3);
v___y_839_ = v_hashCode_859_;
goto v___jp_838_;
}
default: 
{
uint64_t v_hashCode_860_; 
v_hashCode_860_ = lean_ctor_get_uint64(v_key_831_, sizeof(void*)*1);
v___y_839_ = v_hashCode_860_;
goto v___jp_838_;
}
}
v___jp_838_:
{
uint64_t v___x_840_; uint64_t v___x_841_; uint64_t v_fold_842_; uint64_t v___x_843_; uint64_t v___x_844_; uint64_t v___x_845_; size_t v___x_846_; size_t v___x_847_; size_t v___x_848_; size_t v___x_849_; size_t v___x_850_; lean_object* v___x_851_; lean_object* v___x_853_; 
v___x_840_ = 32ULL;
v___x_841_ = lean_uint64_shift_right(v___y_839_, v___x_840_);
v_fold_842_ = lean_uint64_xor(v___y_839_, v___x_841_);
v___x_843_ = 16ULL;
v___x_844_ = lean_uint64_shift_right(v_fold_842_, v___x_843_);
v___x_845_ = lean_uint64_xor(v_fold_842_, v___x_844_);
v___x_846_ = lean_uint64_to_usize(v___x_845_);
v___x_847_ = lean_usize_of_nat(v___x_837_);
v___x_848_ = ((size_t)1ULL);
v___x_849_ = lean_usize_sub(v___x_847_, v___x_848_);
v___x_850_ = lean_usize_land(v___x_846_, v___x_849_);
v___x_851_ = lean_array_uget_borrowed(v_x_829_, v___x_850_);
lean_inc(v___x_851_);
if (v_isShared_836_ == 0)
{
lean_ctor_set(v___x_835_, 2, v___x_851_);
v___x_853_ = v___x_835_;
goto v_reusejp_852_;
}
else
{
lean_object* v_reuseFailAlloc_856_; 
v_reuseFailAlloc_856_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_856_, 0, v_key_831_);
lean_ctor_set(v_reuseFailAlloc_856_, 1, v_value_832_);
lean_ctor_set(v_reuseFailAlloc_856_, 2, v___x_851_);
v___x_853_ = v_reuseFailAlloc_856_;
goto v_reusejp_852_;
}
v_reusejp_852_:
{
lean_object* v___x_854_; 
v___x_854_ = lean_array_uset(v_x_829_, v___x_850_, v___x_853_);
v_x_829_ = v___x_854_;
v_x_830_ = v_tail_833_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_goCache_spec__1_spec__3_spec__5___redArg(lean_object* v_i_862_, lean_object* v_source_863_, lean_object* v_target_864_){
_start:
{
lean_object* v___x_865_; uint8_t v___x_866_; 
v___x_865_ = lean_array_get_size(v_source_863_);
v___x_866_ = lean_nat_dec_lt(v_i_862_, v___x_865_);
if (v___x_866_ == 0)
{
lean_dec_ref(v_source_863_);
lean_dec(v_i_862_);
return v_target_864_;
}
else
{
lean_object* v_es_867_; lean_object* v___x_868_; lean_object* v_source_869_; lean_object* v_target_870_; lean_object* v___x_871_; lean_object* v___x_872_; 
v_es_867_ = lean_array_fget(v_source_863_, v_i_862_);
v___x_868_ = lean_box(0);
v_source_869_ = lean_array_fset(v_source_863_, v_i_862_, v___x_868_);
v_target_870_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_goCache_spec__1_spec__3_spec__5_spec__11___redArg(v_target_864_, v_es_867_);
v___x_871_ = lean_unsigned_to_nat(1u);
v___x_872_ = lean_nat_add(v_i_862_, v___x_871_);
lean_dec(v_i_862_);
v_i_862_ = v___x_872_;
v_source_863_ = v_source_869_;
v_target_864_ = v_target_870_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_goCache_spec__1_spec__3___redArg(lean_object* v_data_874_){
_start:
{
lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v_nbuckets_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; 
v___x_875_ = lean_array_get_size(v_data_874_);
v___x_876_ = lean_unsigned_to_nat(2u);
v_nbuckets_877_ = lean_nat_mul(v___x_875_, v___x_876_);
v___x_878_ = lean_unsigned_to_nat(0u);
v___x_879_ = lean_box(0);
v___x_880_ = lean_mk_array(v_nbuckets_877_, v___x_879_);
v___x_881_ = lean_array_propagate_mark(v_data_874_, v___x_880_);
v___x_882_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_goCache_spec__1_spec__3_spec__5___redArg(v___x_878_, v_data_874_, v___x_881_);
return v___x_882_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_goCache_spec__1_spec__4___redArg(lean_object* v_a_883_, lean_object* v_b_884_, lean_object* v_x_885_){
_start:
{
if (lean_obj_tag(v_x_885_) == 0)
{
lean_dec(v_b_884_);
lean_dec_ref(v_a_883_);
return v_x_885_;
}
else
{
lean_object* v_key_886_; lean_object* v_value_887_; lean_object* v_tail_888_; lean_object* v___x_890_; uint8_t v_isShared_891_; uint8_t v_isSharedCheck_900_; 
v_key_886_ = lean_ctor_get(v_x_885_, 0);
v_value_887_ = lean_ctor_get(v_x_885_, 1);
v_tail_888_ = lean_ctor_get(v_x_885_, 2);
v_isSharedCheck_900_ = !lean_is_exclusive(v_x_885_);
if (v_isSharedCheck_900_ == 0)
{
v___x_890_ = v_x_885_;
v_isShared_891_ = v_isSharedCheck_900_;
goto v_resetjp_889_;
}
else
{
lean_inc(v_tail_888_);
lean_inc(v_value_887_);
lean_inc(v_key_886_);
lean_dec(v_x_885_);
v___x_890_ = lean_box(0);
v_isShared_891_ = v_isSharedCheck_900_;
goto v_resetjp_889_;
}
v_resetjp_889_:
{
uint8_t v___x_892_; 
v___x_892_ = l_Std_Tactic_BVDecide_BVLogicalExpr_decEq(v_key_886_, v_a_883_);
if (v___x_892_ == 0)
{
lean_object* v___x_893_; lean_object* v___x_895_; 
v___x_893_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_goCache_spec__1_spec__4___redArg(v_a_883_, v_b_884_, v_tail_888_);
if (v_isShared_891_ == 0)
{
lean_ctor_set(v___x_890_, 2, v___x_893_);
v___x_895_ = v___x_890_;
goto v_reusejp_894_;
}
else
{
lean_object* v_reuseFailAlloc_896_; 
v_reuseFailAlloc_896_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_896_, 0, v_key_886_);
lean_ctor_set(v_reuseFailAlloc_896_, 1, v_value_887_);
lean_ctor_set(v_reuseFailAlloc_896_, 2, v___x_893_);
v___x_895_ = v_reuseFailAlloc_896_;
goto v_reusejp_894_;
}
v_reusejp_894_:
{
return v___x_895_;
}
}
else
{
lean_object* v___x_898_; 
lean_dec(v_value_887_);
lean_dec(v_key_886_);
if (v_isShared_891_ == 0)
{
lean_ctor_set(v___x_890_, 1, v_b_884_);
lean_ctor_set(v___x_890_, 0, v_a_883_);
v___x_898_ = v___x_890_;
goto v_reusejp_897_;
}
else
{
lean_object* v_reuseFailAlloc_899_; 
v_reuseFailAlloc_899_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_899_, 0, v_a_883_);
lean_ctor_set(v_reuseFailAlloc_899_, 1, v_b_884_);
lean_ctor_set(v_reuseFailAlloc_899_, 2, v_tail_888_);
v___x_898_ = v_reuseFailAlloc_899_;
goto v_reusejp_897_;
}
v_reusejp_897_:
{
return v___x_898_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_goCache_spec__1_spec__2___redArg(lean_object* v_a_901_, lean_object* v_x_902_){
_start:
{
if (lean_obj_tag(v_x_902_) == 0)
{
uint8_t v___x_903_; 
v___x_903_ = 0;
return v___x_903_;
}
else
{
lean_object* v_key_904_; lean_object* v_tail_905_; uint8_t v___x_906_; 
v_key_904_ = lean_ctor_get(v_x_902_, 0);
v_tail_905_ = lean_ctor_get(v_x_902_, 2);
v___x_906_ = l_Std_Tactic_BVDecide_BVLogicalExpr_decEq(v_key_904_, v_a_901_);
if (v___x_906_ == 0)
{
v_x_902_ = v_tail_905_;
goto _start;
}
else
{
return v___x_906_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_goCache_spec__1_spec__2___redArg___boxed(lean_object* v_a_908_, lean_object* v_x_909_){
_start:
{
uint8_t v_res_910_; lean_object* v_r_911_; 
v_res_910_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_goCache_spec__1_spec__2___redArg(v_a_908_, v_x_909_);
lean_dec(v_x_909_);
lean_dec_ref(v_a_908_);
v_r_911_ = lean_box(v_res_910_);
return v_r_911_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_goCache_spec__1___redArg(lean_object* v_m_912_, lean_object* v_a_913_, lean_object* v_b_914_){
_start:
{
lean_object* v_size_915_; lean_object* v_buckets_916_; lean_object* v___x_918_; uint8_t v_isShared_919_; uint8_t v_isSharedCheck_964_; 
v_size_915_ = lean_ctor_get(v_m_912_, 0);
v_buckets_916_ = lean_ctor_get(v_m_912_, 1);
v_isSharedCheck_964_ = !lean_is_exclusive(v_m_912_);
if (v_isSharedCheck_964_ == 0)
{
v___x_918_ = v_m_912_;
v_isShared_919_ = v_isSharedCheck_964_;
goto v_resetjp_917_;
}
else
{
lean_inc(v_buckets_916_);
lean_inc(v_size_915_);
lean_dec(v_m_912_);
v___x_918_ = lean_box(0);
v_isShared_919_ = v_isSharedCheck_964_;
goto v_resetjp_917_;
}
v_resetjp_917_:
{
lean_object* v___x_920_; uint64_t v___y_922_; 
v___x_920_ = lean_array_get_size(v_buckets_916_);
switch(lean_obj_tag(v_a_913_))
{
case 1:
{
uint64_t v_hashCode_960_; 
v_hashCode_960_ = lean_ctor_get_uint64(v_a_913_, 0);
v___y_922_ = v_hashCode_960_;
goto v___jp_921_;
}
case 3:
{
uint64_t v_hashCode_961_; 
v_hashCode_961_ = lean_ctor_get_uint64(v_a_913_, sizeof(void*)*2);
v___y_922_ = v_hashCode_961_;
goto v___jp_921_;
}
case 4:
{
uint64_t v_hashCode_962_; 
v_hashCode_962_ = lean_ctor_get_uint64(v_a_913_, sizeof(void*)*3);
v___y_922_ = v_hashCode_962_;
goto v___jp_921_;
}
default: 
{
uint64_t v_hashCode_963_; 
v_hashCode_963_ = lean_ctor_get_uint64(v_a_913_, sizeof(void*)*1);
v___y_922_ = v_hashCode_963_;
goto v___jp_921_;
}
}
v___jp_921_:
{
uint64_t v___x_923_; uint64_t v___x_924_; uint64_t v_fold_925_; uint64_t v___x_926_; uint64_t v___x_927_; uint64_t v___x_928_; size_t v___x_929_; size_t v___x_930_; size_t v___x_931_; size_t v___x_932_; size_t v___x_933_; lean_object* v_bkt_934_; uint8_t v___x_935_; 
v___x_923_ = 32ULL;
v___x_924_ = lean_uint64_shift_right(v___y_922_, v___x_923_);
v_fold_925_ = lean_uint64_xor(v___y_922_, v___x_924_);
v___x_926_ = 16ULL;
v___x_927_ = lean_uint64_shift_right(v_fold_925_, v___x_926_);
v___x_928_ = lean_uint64_xor(v_fold_925_, v___x_927_);
v___x_929_ = lean_uint64_to_usize(v___x_928_);
v___x_930_ = lean_usize_of_nat(v___x_920_);
v___x_931_ = ((size_t)1ULL);
v___x_932_ = lean_usize_sub(v___x_930_, v___x_931_);
v___x_933_ = lean_usize_land(v___x_929_, v___x_932_);
v_bkt_934_ = lean_array_uget_borrowed(v_buckets_916_, v___x_933_);
v___x_935_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_goCache_spec__1_spec__2___redArg(v_a_913_, v_bkt_934_);
if (v___x_935_ == 0)
{
lean_object* v___x_936_; lean_object* v_size_x27_937_; lean_object* v___x_938_; lean_object* v_buckets_x27_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; uint8_t v___x_945_; 
v___x_936_ = lean_unsigned_to_nat(1u);
v_size_x27_937_ = lean_nat_add(v_size_915_, v___x_936_);
lean_dec(v_size_915_);
lean_inc(v_bkt_934_);
v___x_938_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_938_, 0, v_a_913_);
lean_ctor_set(v___x_938_, 1, v_b_914_);
lean_ctor_set(v___x_938_, 2, v_bkt_934_);
v_buckets_x27_939_ = lean_array_uset(v_buckets_916_, v___x_933_, v___x_938_);
v___x_940_ = lean_unsigned_to_nat(4u);
v___x_941_ = lean_nat_mul(v_size_x27_937_, v___x_940_);
v___x_942_ = lean_unsigned_to_nat(3u);
v___x_943_ = lean_nat_div(v___x_941_, v___x_942_);
lean_dec(v___x_941_);
v___x_944_ = lean_array_get_size(v_buckets_x27_939_);
v___x_945_ = lean_nat_dec_le(v___x_943_, v___x_944_);
lean_dec(v___x_943_);
if (v___x_945_ == 0)
{
lean_object* v_val_946_; lean_object* v___x_948_; 
v_val_946_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_goCache_spec__1_spec__3___redArg(v_buckets_x27_939_);
if (v_isShared_919_ == 0)
{
lean_ctor_set(v___x_918_, 1, v_val_946_);
lean_ctor_set(v___x_918_, 0, v_size_x27_937_);
v___x_948_ = v___x_918_;
goto v_reusejp_947_;
}
else
{
lean_object* v_reuseFailAlloc_949_; 
v_reuseFailAlloc_949_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_949_, 0, v_size_x27_937_);
lean_ctor_set(v_reuseFailAlloc_949_, 1, v_val_946_);
v___x_948_ = v_reuseFailAlloc_949_;
goto v_reusejp_947_;
}
v_reusejp_947_:
{
return v___x_948_;
}
}
else
{
lean_object* v___x_951_; 
if (v_isShared_919_ == 0)
{
lean_ctor_set(v___x_918_, 1, v_buckets_x27_939_);
lean_ctor_set(v___x_918_, 0, v_size_x27_937_);
v___x_951_ = v___x_918_;
goto v_reusejp_950_;
}
else
{
lean_object* v_reuseFailAlloc_952_; 
v_reuseFailAlloc_952_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_952_, 0, v_size_x27_937_);
lean_ctor_set(v_reuseFailAlloc_952_, 1, v_buckets_x27_939_);
v___x_951_ = v_reuseFailAlloc_952_;
goto v_reusejp_950_;
}
v_reusejp_950_:
{
return v___x_951_;
}
}
}
else
{
lean_object* v___x_953_; lean_object* v_buckets_x27_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_958_; 
lean_inc(v_bkt_934_);
v___x_953_ = lean_box(0);
v_buckets_x27_954_ = lean_array_uset(v_buckets_916_, v___x_933_, v___x_953_);
v___x_955_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_goCache_spec__1_spec__4___redArg(v_a_913_, v_b_914_, v_bkt_934_);
v___x_956_ = lean_array_uset(v_buckets_x27_954_, v___x_933_, v___x_955_);
if (v_isShared_919_ == 0)
{
lean_ctor_set(v___x_918_, 1, v___x_956_);
v___x_958_ = v___x_918_;
goto v_reusejp_957_;
}
else
{
lean_object* v_reuseFailAlloc_959_; 
v_reuseFailAlloc_959_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_959_, 0, v_size_915_);
lean_ctor_set(v_reuseFailAlloc_959_, 1, v___x_956_);
v___x_958_ = v_reuseFailAlloc_959_;
goto v_reusejp_957_;
}
v_reusejp_957_:
{
return v___x_958_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_goCache_spec__0_spec__0___redArg(lean_object* v_a_965_, lean_object* v_x_966_){
_start:
{
if (lean_obj_tag(v_x_966_) == 0)
{
lean_object* v___x_967_; 
v___x_967_ = lean_box(0);
return v___x_967_;
}
else
{
lean_object* v_key_968_; lean_object* v_value_969_; lean_object* v_tail_970_; uint8_t v___x_971_; 
v_key_968_ = lean_ctor_get(v_x_966_, 0);
v_value_969_ = lean_ctor_get(v_x_966_, 1);
v_tail_970_ = lean_ctor_get(v_x_966_, 2);
v___x_971_ = l_Std_Tactic_BVDecide_BVLogicalExpr_decEq(v_key_968_, v_a_965_);
if (v___x_971_ == 0)
{
v_x_966_ = v_tail_970_;
goto _start;
}
else
{
lean_object* v___x_973_; 
lean_inc(v_value_969_);
v___x_973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_973_, 0, v_value_969_);
return v___x_973_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_goCache_spec__0_spec__0___redArg___boxed(lean_object* v_a_974_, lean_object* v_x_975_){
_start:
{
lean_object* v_res_976_; 
v_res_976_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_goCache_spec__0_spec__0___redArg(v_a_974_, v_x_975_);
lean_dec(v_x_975_);
lean_dec_ref(v_a_974_);
return v_res_976_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_goCache_spec__0___redArg(lean_object* v_m_977_, lean_object* v_a_978_){
_start:
{
lean_object* v_buckets_979_; lean_object* v___x_980_; uint64_t v___y_982_; 
v_buckets_979_ = lean_ctor_get(v_m_977_, 1);
v___x_980_ = lean_array_get_size(v_buckets_979_);
switch(lean_obj_tag(v_a_978_))
{
case 1:
{
uint64_t v_hashCode_996_; 
v_hashCode_996_ = lean_ctor_get_uint64(v_a_978_, 0);
v___y_982_ = v_hashCode_996_;
goto v___jp_981_;
}
case 3:
{
uint64_t v_hashCode_997_; 
v_hashCode_997_ = lean_ctor_get_uint64(v_a_978_, sizeof(void*)*2);
v___y_982_ = v_hashCode_997_;
goto v___jp_981_;
}
case 4:
{
uint64_t v_hashCode_998_; 
v_hashCode_998_ = lean_ctor_get_uint64(v_a_978_, sizeof(void*)*3);
v___y_982_ = v_hashCode_998_;
goto v___jp_981_;
}
default: 
{
uint64_t v_hashCode_999_; 
v_hashCode_999_ = lean_ctor_get_uint64(v_a_978_, sizeof(void*)*1);
v___y_982_ = v_hashCode_999_;
goto v___jp_981_;
}
}
v___jp_981_:
{
uint64_t v___x_983_; uint64_t v___x_984_; uint64_t v_fold_985_; uint64_t v___x_986_; uint64_t v___x_987_; uint64_t v___x_988_; size_t v___x_989_; size_t v___x_990_; size_t v___x_991_; size_t v___x_992_; size_t v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; 
v___x_983_ = 32ULL;
v___x_984_ = lean_uint64_shift_right(v___y_982_, v___x_983_);
v_fold_985_ = lean_uint64_xor(v___y_982_, v___x_984_);
v___x_986_ = 16ULL;
v___x_987_ = lean_uint64_shift_right(v_fold_985_, v___x_986_);
v___x_988_ = lean_uint64_xor(v_fold_985_, v___x_987_);
v___x_989_ = lean_uint64_to_usize(v___x_988_);
v___x_990_ = lean_usize_of_nat(v___x_980_);
v___x_991_ = ((size_t)1ULL);
v___x_992_ = lean_usize_sub(v___x_990_, v___x_991_);
v___x_993_ = lean_usize_land(v___x_989_, v___x_992_);
v___x_994_ = lean_array_uget_borrowed(v_buckets_979_, v___x_993_);
v___x_995_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_goCache_spec__0_spec__0___redArg(v_a_978_, v___x_994_);
return v___x_995_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_goCache_spec__0___redArg___boxed(lean_object* v_m_1000_, lean_object* v_a_1001_){
_start:
{
lean_object* v_res_1002_; 
v_res_1002_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_goCache_spec__0___redArg(v_m_1000_, v_a_1001_);
lean_dec_ref(v_a_1001_);
lean_dec_ref(v_m_1000_);
return v_res_1002_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go(lean_object* v_aig_1003_, lean_object* v_expr_1004_, lean_object* v_cache_1005_){
_start:
{
switch(lean_obj_tag(v_expr_1004_))
{
case 0:
{
lean_object* v_a_1006_; lean_object* v_exprs_1007_; lean_object* v_map_1008_; lean_object* v___x_1010_; uint8_t v_isShared_1011_; uint8_t v_isSharedCheck_1035_; 
v_a_1006_ = lean_ctor_get(v_expr_1004_, 0);
lean_inc_ref(v_a_1006_);
lean_dec_ref_known(v_expr_1004_, 1);
v_exprs_1007_ = lean_ctor_get(v_cache_1005_, 0);
v_map_1008_ = lean_ctor_get(v_cache_1005_, 1);
v_isSharedCheck_1035_ = !lean_is_exclusive(v_cache_1005_);
if (v_isSharedCheck_1035_ == 0)
{
v___x_1010_ = v_cache_1005_;
v_isShared_1011_ = v_isSharedCheck_1035_;
goto v_resetjp_1009_;
}
else
{
lean_inc(v_map_1008_);
lean_inc(v_exprs_1007_);
lean_dec(v_cache_1005_);
v___x_1010_ = lean_box(0);
v_isShared_1011_ = v_isSharedCheck_1035_;
goto v_resetjp_1009_;
}
v_resetjp_1009_:
{
lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v_result_1014_; lean_object* v_cache_1015_; lean_object* v___x_1017_; uint8_t v_isShared_1018_; uint8_t v_isSharedCheck_1034_; 
v___x_1012_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1012_, 0, v_a_1006_);
lean_ctor_set(v___x_1012_, 1, v_exprs_1007_);
v___x_1013_ = l_Std_Tactic_BVDecide_BVPred_bitblast(v_aig_1003_, v___x_1012_);
v_result_1014_ = lean_ctor_get(v___x_1013_, 0);
v_cache_1015_ = lean_ctor_get(v___x_1013_, 1);
v_isSharedCheck_1034_ = !lean_is_exclusive(v___x_1013_);
if (v_isSharedCheck_1034_ == 0)
{
v___x_1017_ = v___x_1013_;
v_isShared_1018_ = v_isSharedCheck_1034_;
goto v_resetjp_1016_;
}
else
{
lean_inc(v_cache_1015_);
lean_inc(v_result_1014_);
lean_dec(v___x_1013_);
v___x_1017_ = lean_box(0);
v_isShared_1018_ = v_isSharedCheck_1034_;
goto v_resetjp_1016_;
}
v_resetjp_1016_:
{
lean_object* v_aig_1019_; lean_object* v_ref_1020_; lean_object* v___x_1022_; uint8_t v_isShared_1023_; uint8_t v_isSharedCheck_1033_; 
v_aig_1019_ = lean_ctor_get(v_result_1014_, 0);
v_ref_1020_ = lean_ctor_get(v_result_1014_, 1);
v_isSharedCheck_1033_ = !lean_is_exclusive(v_result_1014_);
if (v_isSharedCheck_1033_ == 0)
{
v___x_1022_ = v_result_1014_;
v_isShared_1023_ = v_isSharedCheck_1033_;
goto v_resetjp_1021_;
}
else
{
lean_inc(v_ref_1020_);
lean_inc(v_aig_1019_);
lean_dec(v_result_1014_);
v___x_1022_ = lean_box(0);
v_isShared_1023_ = v_isSharedCheck_1033_;
goto v_resetjp_1021_;
}
v_resetjp_1021_:
{
lean_object* v___x_1025_; 
if (v_isShared_1023_ == 0)
{
v___x_1025_ = v___x_1022_;
goto v_reusejp_1024_;
}
else
{
lean_object* v_reuseFailAlloc_1032_; 
v_reuseFailAlloc_1032_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1032_, 0, v_aig_1019_);
lean_ctor_set(v_reuseFailAlloc_1032_, 1, v_ref_1020_);
v___x_1025_ = v_reuseFailAlloc_1032_;
goto v_reusejp_1024_;
}
v_reusejp_1024_:
{
lean_object* v___x_1027_; 
if (v_isShared_1011_ == 0)
{
lean_ctor_set(v___x_1010_, 0, v_cache_1015_);
v___x_1027_ = v___x_1010_;
goto v_reusejp_1026_;
}
else
{
lean_object* v_reuseFailAlloc_1031_; 
v_reuseFailAlloc_1031_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1031_, 0, v_cache_1015_);
lean_ctor_set(v_reuseFailAlloc_1031_, 1, v_map_1008_);
v___x_1027_ = v_reuseFailAlloc_1031_;
goto v_reusejp_1026_;
}
v_reusejp_1026_:
{
lean_object* v___x_1029_; 
if (v_isShared_1018_ == 0)
{
lean_ctor_set(v___x_1017_, 1, v___x_1027_);
lean_ctor_set(v___x_1017_, 0, v___x_1025_);
v___x_1029_ = v___x_1017_;
goto v_reusejp_1028_;
}
else
{
lean_object* v_reuseFailAlloc_1030_; 
v_reuseFailAlloc_1030_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1030_, 0, v___x_1025_);
lean_ctor_set(v_reuseFailAlloc_1030_, 1, v___x_1027_);
v___x_1029_ = v_reuseFailAlloc_1030_;
goto v_reusejp_1028_;
}
v_reusejp_1028_:
{
return v___x_1029_;
}
}
}
}
}
}
}
case 1:
{
uint8_t v_a_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; 
v_a_1036_ = lean_ctor_get_uint8(v_expr_1004_, 8);
lean_dec_ref_known(v_expr_1004_, 0);
v___x_1037_ = lean_unsigned_to_nat(0u);
v___x_1038_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1038_, 0, v___x_1037_);
lean_ctor_set_uint8(v___x_1038_, sizeof(void*)*1, v_a_1036_);
v___x_1039_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1039_, 0, v_aig_1003_);
lean_ctor_set(v___x_1039_, 1, v___x_1038_);
v___x_1040_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1040_, 0, v___x_1039_);
lean_ctor_set(v___x_1040_, 1, v_cache_1005_);
return v___x_1040_;
}
case 2:
{
lean_object* v_a_1041_; lean_object* v___x_1042_; lean_object* v_result_1043_; lean_object* v_cache_1044_; lean_object* v___x_1046_; uint8_t v_isShared_1047_; uint8_t v_isSharedCheck_1100_; 
v_a_1041_ = lean_ctor_get(v_expr_1004_, 0);
lean_inc_ref(v_a_1041_);
lean_dec_ref_known(v_expr_1004_, 1);
v___x_1042_ = l_Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_goCache(v_aig_1003_, v_a_1041_, v_cache_1005_);
v_result_1043_ = lean_ctor_get(v___x_1042_, 0);
v_cache_1044_ = lean_ctor_get(v___x_1042_, 1);
v_isSharedCheck_1100_ = !lean_is_exclusive(v___x_1042_);
if (v_isSharedCheck_1100_ == 0)
{
v___x_1046_ = v___x_1042_;
v_isShared_1047_ = v_isSharedCheck_1100_;
goto v_resetjp_1045_;
}
else
{
lean_inc(v_cache_1044_);
lean_inc(v_result_1043_);
lean_dec(v___x_1042_);
v___x_1046_ = lean_box(0);
v_isShared_1047_ = v_isSharedCheck_1100_;
goto v_resetjp_1045_;
}
v_resetjp_1045_:
{
lean_object* v___y_1049_; lean_object* v_ref_1062_; uint8_t v_invert_1063_; 
v_ref_1062_ = lean_ctor_get(v_result_1043_, 1);
lean_inc_ref(v_ref_1062_);
v_invert_1063_ = lean_ctor_get_uint8(v_ref_1062_, sizeof(void*)*1);
if (v_invert_1063_ == 0)
{
lean_object* v_aig_1064_; lean_object* v___x_1066_; uint8_t v_isShared_1067_; uint8_t v_isSharedCheck_1080_; 
v_aig_1064_ = lean_ctor_get(v_result_1043_, 0);
v_isSharedCheck_1080_ = !lean_is_exclusive(v_result_1043_);
if (v_isSharedCheck_1080_ == 0)
{
lean_object* v_unused_1081_; 
v_unused_1081_ = lean_ctor_get(v_result_1043_, 1);
lean_dec(v_unused_1081_);
v___x_1066_ = v_result_1043_;
v_isShared_1067_ = v_isSharedCheck_1080_;
goto v_resetjp_1065_;
}
else
{
lean_inc(v_aig_1064_);
lean_dec(v_result_1043_);
v___x_1066_ = lean_box(0);
v_isShared_1067_ = v_isSharedCheck_1080_;
goto v_resetjp_1065_;
}
v_resetjp_1065_:
{
lean_object* v_gate_1068_; lean_object* v___x_1070_; uint8_t v_isShared_1071_; uint8_t v_isSharedCheck_1079_; 
v_gate_1068_ = lean_ctor_get(v_ref_1062_, 0);
v_isSharedCheck_1079_ = !lean_is_exclusive(v_ref_1062_);
if (v_isSharedCheck_1079_ == 0)
{
v___x_1070_ = v_ref_1062_;
v_isShared_1071_ = v_isSharedCheck_1079_;
goto v_resetjp_1069_;
}
else
{
lean_inc(v_gate_1068_);
lean_dec(v_ref_1062_);
v___x_1070_ = lean_box(0);
v_isShared_1071_ = v_isSharedCheck_1079_;
goto v_resetjp_1069_;
}
v_resetjp_1069_:
{
uint8_t v___x_1072_; lean_object* v___x_1074_; 
v___x_1072_ = 1;
if (v_isShared_1071_ == 0)
{
v___x_1074_ = v___x_1070_;
goto v_reusejp_1073_;
}
else
{
lean_object* v_reuseFailAlloc_1078_; 
v_reuseFailAlloc_1078_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1078_, 0, v_gate_1068_);
v___x_1074_ = v_reuseFailAlloc_1078_;
goto v_reusejp_1073_;
}
v_reusejp_1073_:
{
lean_object* v___x_1076_; 
lean_ctor_set_uint8(v___x_1074_, sizeof(void*)*1, v___x_1072_);
if (v_isShared_1067_ == 0)
{
lean_ctor_set(v___x_1066_, 1, v___x_1074_);
v___x_1076_ = v___x_1066_;
goto v_reusejp_1075_;
}
else
{
lean_object* v_reuseFailAlloc_1077_; 
v_reuseFailAlloc_1077_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1077_, 0, v_aig_1064_);
lean_ctor_set(v_reuseFailAlloc_1077_, 1, v___x_1074_);
v___x_1076_ = v_reuseFailAlloc_1077_;
goto v_reusejp_1075_;
}
v_reusejp_1075_:
{
v___y_1049_ = v___x_1076_;
goto v___jp_1048_;
}
}
}
}
}
else
{
lean_object* v_aig_1082_; lean_object* v___x_1084_; uint8_t v_isShared_1085_; uint8_t v_isSharedCheck_1098_; 
v_aig_1082_ = lean_ctor_get(v_result_1043_, 0);
v_isSharedCheck_1098_ = !lean_is_exclusive(v_result_1043_);
if (v_isSharedCheck_1098_ == 0)
{
lean_object* v_unused_1099_; 
v_unused_1099_ = lean_ctor_get(v_result_1043_, 1);
lean_dec(v_unused_1099_);
v___x_1084_ = v_result_1043_;
v_isShared_1085_ = v_isSharedCheck_1098_;
goto v_resetjp_1083_;
}
else
{
lean_inc(v_aig_1082_);
lean_dec(v_result_1043_);
v___x_1084_ = lean_box(0);
v_isShared_1085_ = v_isSharedCheck_1098_;
goto v_resetjp_1083_;
}
v_resetjp_1083_:
{
lean_object* v_gate_1086_; lean_object* v___x_1088_; uint8_t v_isShared_1089_; uint8_t v_isSharedCheck_1097_; 
v_gate_1086_ = lean_ctor_get(v_ref_1062_, 0);
v_isSharedCheck_1097_ = !lean_is_exclusive(v_ref_1062_);
if (v_isSharedCheck_1097_ == 0)
{
v___x_1088_ = v_ref_1062_;
v_isShared_1089_ = v_isSharedCheck_1097_;
goto v_resetjp_1087_;
}
else
{
lean_inc(v_gate_1086_);
lean_dec(v_ref_1062_);
v___x_1088_ = lean_box(0);
v_isShared_1089_ = v_isSharedCheck_1097_;
goto v_resetjp_1087_;
}
v_resetjp_1087_:
{
uint8_t v___x_1090_; lean_object* v___x_1092_; 
v___x_1090_ = 0;
if (v_isShared_1089_ == 0)
{
v___x_1092_ = v___x_1088_;
goto v_reusejp_1091_;
}
else
{
lean_object* v_reuseFailAlloc_1096_; 
v_reuseFailAlloc_1096_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1096_, 0, v_gate_1086_);
v___x_1092_ = v_reuseFailAlloc_1096_;
goto v_reusejp_1091_;
}
v_reusejp_1091_:
{
lean_object* v___x_1094_; 
lean_ctor_set_uint8(v___x_1092_, sizeof(void*)*1, v___x_1090_);
if (v_isShared_1085_ == 0)
{
lean_ctor_set(v___x_1084_, 1, v___x_1092_);
v___x_1094_ = v___x_1084_;
goto v_reusejp_1093_;
}
else
{
lean_object* v_reuseFailAlloc_1095_; 
v_reuseFailAlloc_1095_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1095_, 0, v_aig_1082_);
lean_ctor_set(v_reuseFailAlloc_1095_, 1, v___x_1092_);
v___x_1094_ = v_reuseFailAlloc_1095_;
goto v_reusejp_1093_;
}
v_reusejp_1093_:
{
v___y_1049_ = v___x_1094_;
goto v___jp_1048_;
}
}
}
}
}
v___jp_1048_:
{
lean_object* v_exprs_1050_; lean_object* v_map_1051_; lean_object* v___x_1053_; uint8_t v_isShared_1054_; uint8_t v_isSharedCheck_1061_; 
v_exprs_1050_ = lean_ctor_get(v_cache_1044_, 0);
v_map_1051_ = lean_ctor_get(v_cache_1044_, 1);
v_isSharedCheck_1061_ = !lean_is_exclusive(v_cache_1044_);
if (v_isSharedCheck_1061_ == 0)
{
v___x_1053_ = v_cache_1044_;
v_isShared_1054_ = v_isSharedCheck_1061_;
goto v_resetjp_1052_;
}
else
{
lean_inc(v_map_1051_);
lean_inc(v_exprs_1050_);
lean_dec(v_cache_1044_);
v___x_1053_ = lean_box(0);
v_isShared_1054_ = v_isSharedCheck_1061_;
goto v_resetjp_1052_;
}
v_resetjp_1052_:
{
lean_object* v_cache_1056_; 
if (v_isShared_1054_ == 0)
{
v_cache_1056_ = v___x_1053_;
goto v_reusejp_1055_;
}
else
{
lean_object* v_reuseFailAlloc_1060_; 
v_reuseFailAlloc_1060_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1060_, 0, v_exprs_1050_);
lean_ctor_set(v_reuseFailAlloc_1060_, 1, v_map_1051_);
v_cache_1056_ = v_reuseFailAlloc_1060_;
goto v_reusejp_1055_;
}
v_reusejp_1055_:
{
lean_object* v___x_1058_; 
if (v_isShared_1047_ == 0)
{
lean_ctor_set(v___x_1046_, 1, v_cache_1056_);
lean_ctor_set(v___x_1046_, 0, v___y_1049_);
v___x_1058_ = v___x_1046_;
goto v_reusejp_1057_;
}
else
{
lean_object* v_reuseFailAlloc_1059_; 
v_reuseFailAlloc_1059_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1059_, 0, v___y_1049_);
lean_ctor_set(v_reuseFailAlloc_1059_, 1, v_cache_1056_);
v___x_1058_ = v_reuseFailAlloc_1059_;
goto v_reusejp_1057_;
}
v_reusejp_1057_:
{
return v___x_1058_;
}
}
}
}
}
}
case 3:
{
uint8_t v_a_1101_; lean_object* v_a_1102_; lean_object* v_a_1103_; lean_object* v___x_1104_; lean_object* v_result_1105_; lean_object* v_cache_1106_; lean_object* v_aig_1107_; lean_object* v_ref_1108_; lean_object* v___x_1109_; lean_object* v_result_1110_; lean_object* v_cache_1111_; lean_object* v___x_1113_; uint8_t v_isShared_1114_; uint8_t v_isSharedCheck_1185_; 
v_a_1101_ = lean_ctor_get_uint8(v_expr_1004_, sizeof(void*)*2 + 8);
v_a_1102_ = lean_ctor_get(v_expr_1004_, 0);
lean_inc_ref(v_a_1102_);
v_a_1103_ = lean_ctor_get(v_expr_1004_, 1);
lean_inc_ref(v_a_1103_);
lean_dec_ref_known(v_expr_1004_, 2);
v___x_1104_ = l_Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_goCache(v_aig_1003_, v_a_1102_, v_cache_1005_);
v_result_1105_ = lean_ctor_get(v___x_1104_, 0);
lean_inc_ref(v_result_1105_);
v_cache_1106_ = lean_ctor_get(v___x_1104_, 1);
lean_inc_ref(v_cache_1106_);
lean_dec_ref(v___x_1104_);
v_aig_1107_ = lean_ctor_get(v_result_1105_, 0);
lean_inc_ref(v_aig_1107_);
v_ref_1108_ = lean_ctor_get(v_result_1105_, 1);
lean_inc_ref(v_ref_1108_);
lean_dec_ref(v_result_1105_);
v___x_1109_ = l_Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_goCache(v_aig_1107_, v_a_1103_, v_cache_1106_);
v_result_1110_ = lean_ctor_get(v___x_1109_, 0);
v_cache_1111_ = lean_ctor_get(v___x_1109_, 1);
v_isSharedCheck_1185_ = !lean_is_exclusive(v___x_1109_);
if (v_isSharedCheck_1185_ == 0)
{
v___x_1113_ = v___x_1109_;
v_isShared_1114_ = v_isSharedCheck_1185_;
goto v_resetjp_1112_;
}
else
{
lean_inc(v_cache_1111_);
lean_inc(v_result_1110_);
lean_dec(v___x_1109_);
v___x_1113_ = lean_box(0);
v_isShared_1114_ = v_isSharedCheck_1185_;
goto v_resetjp_1112_;
}
v_resetjp_1112_:
{
lean_object* v_aig_1115_; lean_object* v_ref_1116_; lean_object* v___x_1118_; uint8_t v_isShared_1119_; uint8_t v_isSharedCheck_1184_; 
v_aig_1115_ = lean_ctor_get(v_result_1110_, 0);
v_ref_1116_ = lean_ctor_get(v_result_1110_, 1);
v_isSharedCheck_1184_ = !lean_is_exclusive(v_result_1110_);
if (v_isSharedCheck_1184_ == 0)
{
v___x_1118_ = v_result_1110_;
v_isShared_1119_ = v_isSharedCheck_1184_;
goto v_resetjp_1117_;
}
else
{
lean_inc(v_ref_1116_);
lean_inc(v_aig_1115_);
lean_dec(v_result_1110_);
v___x_1118_ = lean_box(0);
v_isShared_1119_ = v_isSharedCheck_1184_;
goto v_resetjp_1117_;
}
v_resetjp_1117_:
{
lean_object* v_gate_1120_; uint8_t v_invert_1121_; lean_object* v___x_1123_; uint8_t v_isShared_1124_; uint8_t v_isSharedCheck_1183_; 
v_gate_1120_ = lean_ctor_get(v_ref_1108_, 0);
v_invert_1121_ = lean_ctor_get_uint8(v_ref_1108_, sizeof(void*)*1);
v_isSharedCheck_1183_ = !lean_is_exclusive(v_ref_1108_);
if (v_isSharedCheck_1183_ == 0)
{
v___x_1123_ = v_ref_1108_;
v_isShared_1124_ = v_isSharedCheck_1183_;
goto v_resetjp_1122_;
}
else
{
lean_inc(v_gate_1120_);
lean_dec(v_ref_1108_);
v___x_1123_ = lean_box(0);
v_isShared_1124_ = v_isSharedCheck_1183_;
goto v_resetjp_1122_;
}
v_resetjp_1122_:
{
lean_object* v_lhsRef_1126_; 
if (v_isShared_1124_ == 0)
{
v_lhsRef_1126_ = v___x_1123_;
goto v_reusejp_1125_;
}
else
{
lean_object* v_reuseFailAlloc_1182_; 
v_reuseFailAlloc_1182_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1182_, 0, v_gate_1120_);
lean_ctor_set_uint8(v_reuseFailAlloc_1182_, sizeof(void*)*1, v_invert_1121_);
v_lhsRef_1126_ = v_reuseFailAlloc_1182_;
goto v_reusejp_1125_;
}
v_reusejp_1125_:
{
lean_object* v_input_1128_; 
if (v_isShared_1119_ == 0)
{
lean_ctor_set(v___x_1118_, 0, v_lhsRef_1126_);
v_input_1128_ = v___x_1118_;
goto v_reusejp_1127_;
}
else
{
lean_object* v_reuseFailAlloc_1181_; 
v_reuseFailAlloc_1181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1181_, 0, v_lhsRef_1126_);
lean_ctor_set(v_reuseFailAlloc_1181_, 1, v_ref_1116_);
v_input_1128_ = v_reuseFailAlloc_1181_;
goto v_reusejp_1127_;
}
v_reusejp_1127_:
{
switch(v_a_1101_)
{
case 0:
{
lean_object* v_exprs_1129_; lean_object* v_map_1130_; lean_object* v___x_1132_; uint8_t v_isShared_1133_; uint8_t v_isSharedCheck_1141_; 
v_exprs_1129_ = lean_ctor_get(v_cache_1111_, 0);
v_map_1130_ = lean_ctor_get(v_cache_1111_, 1);
v_isSharedCheck_1141_ = !lean_is_exclusive(v_cache_1111_);
if (v_isSharedCheck_1141_ == 0)
{
v___x_1132_ = v_cache_1111_;
v_isShared_1133_ = v_isSharedCheck_1141_;
goto v_resetjp_1131_;
}
else
{
lean_inc(v_map_1130_);
lean_inc(v_exprs_1129_);
lean_dec(v_cache_1111_);
v___x_1132_ = lean_box(0);
v_isShared_1133_ = v_isSharedCheck_1141_;
goto v_resetjp_1131_;
}
v_resetjp_1131_:
{
lean_object* v_ret_1134_; lean_object* v_cache_1136_; 
v_ret_1134_ = l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__3(v_aig_1115_, v_input_1128_);
if (v_isShared_1133_ == 0)
{
v_cache_1136_ = v___x_1132_;
goto v_reusejp_1135_;
}
else
{
lean_object* v_reuseFailAlloc_1140_; 
v_reuseFailAlloc_1140_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1140_, 0, v_exprs_1129_);
lean_ctor_set(v_reuseFailAlloc_1140_, 1, v_map_1130_);
v_cache_1136_ = v_reuseFailAlloc_1140_;
goto v_reusejp_1135_;
}
v_reusejp_1135_:
{
lean_object* v___x_1138_; 
if (v_isShared_1114_ == 0)
{
lean_ctor_set(v___x_1113_, 1, v_cache_1136_);
lean_ctor_set(v___x_1113_, 0, v_ret_1134_);
v___x_1138_ = v___x_1113_;
goto v_reusejp_1137_;
}
else
{
lean_object* v_reuseFailAlloc_1139_; 
v_reuseFailAlloc_1139_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1139_, 0, v_ret_1134_);
lean_ctor_set(v_reuseFailAlloc_1139_, 1, v_cache_1136_);
v___x_1138_ = v_reuseFailAlloc_1139_;
goto v_reusejp_1137_;
}
v_reusejp_1137_:
{
return v___x_1138_;
}
}
}
}
case 1:
{
lean_object* v_exprs_1142_; lean_object* v_map_1143_; lean_object* v___x_1145_; uint8_t v_isShared_1146_; uint8_t v_isSharedCheck_1154_; 
v_exprs_1142_ = lean_ctor_get(v_cache_1111_, 0);
v_map_1143_ = lean_ctor_get(v_cache_1111_, 1);
v_isSharedCheck_1154_ = !lean_is_exclusive(v_cache_1111_);
if (v_isSharedCheck_1154_ == 0)
{
v___x_1145_ = v_cache_1111_;
v_isShared_1146_ = v_isSharedCheck_1154_;
goto v_resetjp_1144_;
}
else
{
lean_inc(v_map_1143_);
lean_inc(v_exprs_1142_);
lean_dec(v_cache_1111_);
v___x_1145_ = lean_box(0);
v_isShared_1146_ = v_isSharedCheck_1154_;
goto v_resetjp_1144_;
}
v_resetjp_1144_:
{
lean_object* v_ret_1147_; lean_object* v_cache_1149_; 
v_ret_1147_ = l_Std_Sat_AIG_mkXorCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__4(v_aig_1115_, v_input_1128_);
if (v_isShared_1146_ == 0)
{
v_cache_1149_ = v___x_1145_;
goto v_reusejp_1148_;
}
else
{
lean_object* v_reuseFailAlloc_1153_; 
v_reuseFailAlloc_1153_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1153_, 0, v_exprs_1142_);
lean_ctor_set(v_reuseFailAlloc_1153_, 1, v_map_1143_);
v_cache_1149_ = v_reuseFailAlloc_1153_;
goto v_reusejp_1148_;
}
v_reusejp_1148_:
{
lean_object* v___x_1151_; 
if (v_isShared_1114_ == 0)
{
lean_ctor_set(v___x_1113_, 1, v_cache_1149_);
lean_ctor_set(v___x_1113_, 0, v_ret_1147_);
v___x_1151_ = v___x_1113_;
goto v_reusejp_1150_;
}
else
{
lean_object* v_reuseFailAlloc_1152_; 
v_reuseFailAlloc_1152_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1152_, 0, v_ret_1147_);
lean_ctor_set(v_reuseFailAlloc_1152_, 1, v_cache_1149_);
v___x_1151_ = v_reuseFailAlloc_1152_;
goto v_reusejp_1150_;
}
v_reusejp_1150_:
{
return v___x_1151_;
}
}
}
}
case 2:
{
lean_object* v_exprs_1155_; lean_object* v_map_1156_; lean_object* v___x_1158_; uint8_t v_isShared_1159_; uint8_t v_isSharedCheck_1167_; 
v_exprs_1155_ = lean_ctor_get(v_cache_1111_, 0);
v_map_1156_ = lean_ctor_get(v_cache_1111_, 1);
v_isSharedCheck_1167_ = !lean_is_exclusive(v_cache_1111_);
if (v_isSharedCheck_1167_ == 0)
{
v___x_1158_ = v_cache_1111_;
v_isShared_1159_ = v_isSharedCheck_1167_;
goto v_resetjp_1157_;
}
else
{
lean_inc(v_map_1156_);
lean_inc(v_exprs_1155_);
lean_dec(v_cache_1111_);
v___x_1158_ = lean_box(0);
v_isShared_1159_ = v_isSharedCheck_1167_;
goto v_resetjp_1157_;
}
v_resetjp_1157_:
{
lean_object* v_ret_1160_; lean_object* v_cache_1162_; 
v_ret_1160_ = l_Std_Sat_AIG_mkBEqCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__5(v_aig_1115_, v_input_1128_);
if (v_isShared_1159_ == 0)
{
v_cache_1162_ = v___x_1158_;
goto v_reusejp_1161_;
}
else
{
lean_object* v_reuseFailAlloc_1166_; 
v_reuseFailAlloc_1166_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1166_, 0, v_exprs_1155_);
lean_ctor_set(v_reuseFailAlloc_1166_, 1, v_map_1156_);
v_cache_1162_ = v_reuseFailAlloc_1166_;
goto v_reusejp_1161_;
}
v_reusejp_1161_:
{
lean_object* v___x_1164_; 
if (v_isShared_1114_ == 0)
{
lean_ctor_set(v___x_1113_, 1, v_cache_1162_);
lean_ctor_set(v___x_1113_, 0, v_ret_1160_);
v___x_1164_ = v___x_1113_;
goto v_reusejp_1163_;
}
else
{
lean_object* v_reuseFailAlloc_1165_; 
v_reuseFailAlloc_1165_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1165_, 0, v_ret_1160_);
lean_ctor_set(v_reuseFailAlloc_1165_, 1, v_cache_1162_);
v___x_1164_ = v_reuseFailAlloc_1165_;
goto v_reusejp_1163_;
}
v_reusejp_1163_:
{
return v___x_1164_;
}
}
}
}
default: 
{
lean_object* v_exprs_1168_; lean_object* v_map_1169_; lean_object* v___x_1171_; uint8_t v_isShared_1172_; uint8_t v_isSharedCheck_1180_; 
v_exprs_1168_ = lean_ctor_get(v_cache_1111_, 0);
v_map_1169_ = lean_ctor_get(v_cache_1111_, 1);
v_isSharedCheck_1180_ = !lean_is_exclusive(v_cache_1111_);
if (v_isSharedCheck_1180_ == 0)
{
v___x_1171_ = v_cache_1111_;
v_isShared_1172_ = v_isSharedCheck_1180_;
goto v_resetjp_1170_;
}
else
{
lean_inc(v_map_1169_);
lean_inc(v_exprs_1168_);
lean_dec(v_cache_1111_);
v___x_1171_ = lean_box(0);
v_isShared_1172_ = v_isSharedCheck_1180_;
goto v_resetjp_1170_;
}
v_resetjp_1170_:
{
lean_object* v_ret_1173_; lean_object* v_cache_1175_; 
v_ret_1173_ = l_Std_Sat_AIG_mkOrCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__6(v_aig_1115_, v_input_1128_);
if (v_isShared_1172_ == 0)
{
v_cache_1175_ = v___x_1171_;
goto v_reusejp_1174_;
}
else
{
lean_object* v_reuseFailAlloc_1179_; 
v_reuseFailAlloc_1179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1179_, 0, v_exprs_1168_);
lean_ctor_set(v_reuseFailAlloc_1179_, 1, v_map_1169_);
v_cache_1175_ = v_reuseFailAlloc_1179_;
goto v_reusejp_1174_;
}
v_reusejp_1174_:
{
lean_object* v___x_1177_; 
if (v_isShared_1114_ == 0)
{
lean_ctor_set(v___x_1113_, 1, v_cache_1175_);
lean_ctor_set(v___x_1113_, 0, v_ret_1173_);
v___x_1177_ = v___x_1113_;
goto v_reusejp_1176_;
}
else
{
lean_object* v_reuseFailAlloc_1178_; 
v_reuseFailAlloc_1178_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1178_, 0, v_ret_1173_);
lean_ctor_set(v_reuseFailAlloc_1178_, 1, v_cache_1175_);
v___x_1177_ = v_reuseFailAlloc_1178_;
goto v_reusejp_1176_;
}
v_reusejp_1176_:
{
return v___x_1177_;
}
}
}
}
}
}
}
}
}
}
}
default: 
{
lean_object* v_a_1186_; lean_object* v_a_1187_; lean_object* v_a_1188_; lean_object* v___x_1189_; lean_object* v_result_1190_; lean_object* v_cache_1191_; lean_object* v_aig_1192_; lean_object* v_ref_1193_; lean_object* v___x_1194_; lean_object* v_result_1195_; lean_object* v_cache_1196_; lean_object* v_aig_1197_; lean_object* v_ref_1198_; lean_object* v___x_1199_; lean_object* v_result_1200_; lean_object* v_cache_1201_; lean_object* v___x_1203_; uint8_t v_isShared_1204_; uint8_t v_isSharedCheck_1239_; 
v_a_1186_ = lean_ctor_get(v_expr_1004_, 0);
lean_inc_ref(v_a_1186_);
v_a_1187_ = lean_ctor_get(v_expr_1004_, 1);
lean_inc_ref(v_a_1187_);
v_a_1188_ = lean_ctor_get(v_expr_1004_, 2);
lean_inc_ref(v_a_1188_);
lean_dec_ref_known(v_expr_1004_, 3);
v___x_1189_ = l_Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_goCache(v_aig_1003_, v_a_1186_, v_cache_1005_);
v_result_1190_ = lean_ctor_get(v___x_1189_, 0);
lean_inc_ref(v_result_1190_);
v_cache_1191_ = lean_ctor_get(v___x_1189_, 1);
lean_inc_ref(v_cache_1191_);
lean_dec_ref(v___x_1189_);
v_aig_1192_ = lean_ctor_get(v_result_1190_, 0);
lean_inc_ref(v_aig_1192_);
v_ref_1193_ = lean_ctor_get(v_result_1190_, 1);
lean_inc_ref(v_ref_1193_);
lean_dec_ref(v_result_1190_);
v___x_1194_ = l_Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_goCache(v_aig_1192_, v_a_1187_, v_cache_1191_);
v_result_1195_ = lean_ctor_get(v___x_1194_, 0);
lean_inc_ref(v_result_1195_);
v_cache_1196_ = lean_ctor_get(v___x_1194_, 1);
lean_inc_ref(v_cache_1196_);
lean_dec_ref(v___x_1194_);
v_aig_1197_ = lean_ctor_get(v_result_1195_, 0);
lean_inc_ref(v_aig_1197_);
v_ref_1198_ = lean_ctor_get(v_result_1195_, 1);
lean_inc_ref(v_ref_1198_);
lean_dec_ref(v_result_1195_);
v___x_1199_ = l_Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_goCache(v_aig_1197_, v_a_1188_, v_cache_1196_);
v_result_1200_ = lean_ctor_get(v___x_1199_, 0);
v_cache_1201_ = lean_ctor_get(v___x_1199_, 1);
v_isSharedCheck_1239_ = !lean_is_exclusive(v___x_1199_);
if (v_isSharedCheck_1239_ == 0)
{
v___x_1203_ = v___x_1199_;
v_isShared_1204_ = v_isSharedCheck_1239_;
goto v_resetjp_1202_;
}
else
{
lean_inc(v_cache_1201_);
lean_inc(v_result_1200_);
lean_dec(v___x_1199_);
v___x_1203_ = lean_box(0);
v_isShared_1204_ = v_isSharedCheck_1239_;
goto v_resetjp_1202_;
}
v_resetjp_1202_:
{
lean_object* v_aig_1205_; lean_object* v_ref_1206_; lean_object* v_gate_1207_; uint8_t v_invert_1208_; lean_object* v___x_1210_; uint8_t v_isShared_1211_; uint8_t v_isSharedCheck_1238_; 
v_aig_1205_ = lean_ctor_get(v_result_1200_, 0);
lean_inc_ref(v_aig_1205_);
v_ref_1206_ = lean_ctor_get(v_result_1200_, 1);
lean_inc_ref(v_ref_1206_);
lean_dec_ref(v_result_1200_);
v_gate_1207_ = lean_ctor_get(v_ref_1193_, 0);
v_invert_1208_ = lean_ctor_get_uint8(v_ref_1193_, sizeof(void*)*1);
v_isSharedCheck_1238_ = !lean_is_exclusive(v_ref_1193_);
if (v_isSharedCheck_1238_ == 0)
{
v___x_1210_ = v_ref_1193_;
v_isShared_1211_ = v_isSharedCheck_1238_;
goto v_resetjp_1209_;
}
else
{
lean_inc(v_gate_1207_);
lean_dec(v_ref_1193_);
v___x_1210_ = lean_box(0);
v_isShared_1211_ = v_isSharedCheck_1238_;
goto v_resetjp_1209_;
}
v_resetjp_1209_:
{
lean_object* v_gate_1212_; uint8_t v_invert_1213_; lean_object* v___x_1215_; uint8_t v_isShared_1216_; uint8_t v_isSharedCheck_1237_; 
v_gate_1212_ = lean_ctor_get(v_ref_1198_, 0);
v_invert_1213_ = lean_ctor_get_uint8(v_ref_1198_, sizeof(void*)*1);
v_isSharedCheck_1237_ = !lean_is_exclusive(v_ref_1198_);
if (v_isSharedCheck_1237_ == 0)
{
v___x_1215_ = v_ref_1198_;
v_isShared_1216_ = v_isSharedCheck_1237_;
goto v_resetjp_1214_;
}
else
{
lean_inc(v_gate_1212_);
lean_dec(v_ref_1198_);
v___x_1215_ = lean_box(0);
v_isShared_1216_ = v_isSharedCheck_1237_;
goto v_resetjp_1214_;
}
v_resetjp_1214_:
{
lean_object* v_exprs_1217_; lean_object* v_map_1218_; lean_object* v___x_1220_; uint8_t v_isShared_1221_; uint8_t v_isSharedCheck_1236_; 
v_exprs_1217_ = lean_ctor_get(v_cache_1201_, 0);
v_map_1218_ = lean_ctor_get(v_cache_1201_, 1);
v_isSharedCheck_1236_ = !lean_is_exclusive(v_cache_1201_);
if (v_isSharedCheck_1236_ == 0)
{
v___x_1220_ = v_cache_1201_;
v_isShared_1221_ = v_isSharedCheck_1236_;
goto v_resetjp_1219_;
}
else
{
lean_inc(v_map_1218_);
lean_inc(v_exprs_1217_);
lean_dec(v_cache_1201_);
v___x_1220_ = lean_box(0);
v_isShared_1221_ = v_isSharedCheck_1236_;
goto v_resetjp_1219_;
}
v_resetjp_1219_:
{
lean_object* v_discrRef_1223_; 
if (v_isShared_1216_ == 0)
{
lean_ctor_set(v___x_1215_, 0, v_gate_1207_);
v_discrRef_1223_ = v___x_1215_;
goto v_reusejp_1222_;
}
else
{
lean_object* v_reuseFailAlloc_1235_; 
v_reuseFailAlloc_1235_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1235_, 0, v_gate_1207_);
v_discrRef_1223_ = v_reuseFailAlloc_1235_;
goto v_reusejp_1222_;
}
v_reusejp_1222_:
{
lean_object* v_lhsRef_1225_; 
lean_ctor_set_uint8(v_discrRef_1223_, sizeof(void*)*1, v_invert_1208_);
if (v_isShared_1211_ == 0)
{
lean_ctor_set(v___x_1210_, 0, v_gate_1212_);
v_lhsRef_1225_ = v___x_1210_;
goto v_reusejp_1224_;
}
else
{
lean_object* v_reuseFailAlloc_1234_; 
v_reuseFailAlloc_1234_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1234_, 0, v_gate_1212_);
v_lhsRef_1225_ = v_reuseFailAlloc_1234_;
goto v_reusejp_1224_;
}
v_reusejp_1224_:
{
lean_object* v_input_1226_; lean_object* v_ret_1227_; lean_object* v_cache_1229_; 
lean_ctor_set_uint8(v_lhsRef_1225_, sizeof(void*)*1, v_invert_1213_);
v_input_1226_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_input_1226_, 0, v_discrRef_1223_);
lean_ctor_set(v_input_1226_, 1, v_lhsRef_1225_);
lean_ctor_set(v_input_1226_, 2, v_ref_1206_);
v_ret_1227_ = l_Std_Sat_AIG_mkIfCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__7(v_aig_1205_, v_input_1226_);
if (v_isShared_1221_ == 0)
{
v_cache_1229_ = v___x_1220_;
goto v_reusejp_1228_;
}
else
{
lean_object* v_reuseFailAlloc_1233_; 
v_reuseFailAlloc_1233_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1233_, 0, v_exprs_1217_);
lean_ctor_set(v_reuseFailAlloc_1233_, 1, v_map_1218_);
v_cache_1229_ = v_reuseFailAlloc_1233_;
goto v_reusejp_1228_;
}
v_reusejp_1228_:
{
lean_object* v___x_1231_; 
if (v_isShared_1204_ == 0)
{
lean_ctor_set(v___x_1203_, 1, v_cache_1229_);
lean_ctor_set(v___x_1203_, 0, v_ret_1227_);
v___x_1231_ = v___x_1203_;
goto v_reusejp_1230_;
}
else
{
lean_object* v_reuseFailAlloc_1232_; 
v_reuseFailAlloc_1232_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1232_, 0, v_ret_1227_);
lean_ctor_set(v_reuseFailAlloc_1232_, 1, v_cache_1229_);
v___x_1231_ = v_reuseFailAlloc_1232_;
goto v_reusejp_1230_;
}
v_reusejp_1230_:
{
return v___x_1231_;
}
}
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_goCache(lean_object* v_aig_1240_, lean_object* v_expr_1241_, lean_object* v_cache_1242_){
_start:
{
lean_object* v_map_1243_; lean_object* v___x_1244_; 
v_map_1243_ = lean_ctor_get(v_cache_1242_, 1);
v___x_1244_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_goCache_spec__0___redArg(v_map_1243_, v_expr_1241_);
if (lean_obj_tag(v___x_1244_) == 0)
{
lean_object* v___x_1245_; lean_object* v_cache_1246_; lean_object* v_result_1247_; lean_object* v___x_1249_; uint8_t v_isShared_1250_; uint8_t v_isSharedCheck_1271_; 
lean_inc_ref(v_expr_1241_);
v___x_1245_ = l_Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go(v_aig_1240_, v_expr_1241_, v_cache_1242_);
v_cache_1246_ = lean_ctor_get(v___x_1245_, 1);
v_result_1247_ = lean_ctor_get(v___x_1245_, 0);
v_isSharedCheck_1271_ = !lean_is_exclusive(v___x_1245_);
if (v_isSharedCheck_1271_ == 0)
{
v___x_1249_ = v___x_1245_;
v_isShared_1250_ = v_isSharedCheck_1271_;
goto v_resetjp_1248_;
}
else
{
lean_inc(v_cache_1246_);
lean_inc(v_result_1247_);
lean_dec(v___x_1245_);
v___x_1249_ = lean_box(0);
v_isShared_1250_ = v_isSharedCheck_1271_;
goto v_resetjp_1248_;
}
v_resetjp_1248_:
{
lean_object* v_ref_1251_; lean_object* v_exprs_1252_; lean_object* v_map_1253_; lean_object* v___x_1255_; uint8_t v_isShared_1256_; uint8_t v_isSharedCheck_1270_; 
v_ref_1251_ = lean_ctor_get(v_result_1247_, 1);
v_exprs_1252_ = lean_ctor_get(v_cache_1246_, 0);
v_map_1253_ = lean_ctor_get(v_cache_1246_, 1);
v_isSharedCheck_1270_ = !lean_is_exclusive(v_cache_1246_);
if (v_isSharedCheck_1270_ == 0)
{
v___x_1255_ = v_cache_1246_;
v_isShared_1256_ = v_isSharedCheck_1270_;
goto v_resetjp_1254_;
}
else
{
lean_inc(v_map_1253_);
lean_inc(v_exprs_1252_);
lean_dec(v_cache_1246_);
v___x_1255_ = lean_box(0);
v_isShared_1256_ = v_isSharedCheck_1270_;
goto v_resetjp_1254_;
}
v_resetjp_1254_:
{
lean_object* v_gate_1257_; uint8_t v_invert_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1265_; 
v_gate_1257_ = lean_ctor_get(v_ref_1251_, 0);
v_invert_1258_ = lean_ctor_get_uint8(v_ref_1251_, sizeof(void*)*1);
v___x_1259_ = lean_unsigned_to_nat(2u);
v___x_1260_ = lean_nat_mul(v_gate_1257_, v___x_1259_);
v___x_1261_ = l_Bool_toNat(v_invert_1258_);
v___x_1262_ = lean_nat_lor(v___x_1260_, v___x_1261_);
lean_dec(v___x_1261_);
lean_dec(v___x_1260_);
v___x_1263_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_goCache_spec__1___redArg(v_map_1253_, v_expr_1241_, v___x_1262_);
if (v_isShared_1256_ == 0)
{
lean_ctor_set(v___x_1255_, 1, v___x_1263_);
v___x_1265_ = v___x_1255_;
goto v_reusejp_1264_;
}
else
{
lean_object* v_reuseFailAlloc_1269_; 
v_reuseFailAlloc_1269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1269_, 0, v_exprs_1252_);
lean_ctor_set(v_reuseFailAlloc_1269_, 1, v___x_1263_);
v___x_1265_ = v_reuseFailAlloc_1269_;
goto v_reusejp_1264_;
}
v_reusejp_1264_:
{
lean_object* v___x_1267_; 
if (v_isShared_1250_ == 0)
{
lean_ctor_set(v___x_1249_, 1, v___x_1265_);
v___x_1267_ = v___x_1249_;
goto v_reusejp_1266_;
}
else
{
lean_object* v_reuseFailAlloc_1268_; 
v_reuseFailAlloc_1268_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1268_, 0, v_result_1247_);
lean_ctor_set(v_reuseFailAlloc_1268_, 1, v___x_1265_);
v___x_1267_ = v_reuseFailAlloc_1268_;
goto v_reusejp_1266_;
}
v_reusejp_1266_:
{
return v___x_1267_;
}
}
}
}
}
else
{
lean_object* v_val_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; uint8_t v___y_1276_; lean_object* v___x_1280_; lean_object* v___x_1281_; uint8_t v___x_1282_; 
lean_dec_ref(v_expr_1241_);
v_val_1272_ = lean_ctor_get(v___x_1244_, 0);
lean_inc(v_val_1272_);
lean_dec_ref_known(v___x_1244_, 1);
v___x_1273_ = lean_unsigned_to_nat(1u);
v___x_1274_ = lean_nat_shiftr(v_val_1272_, v___x_1273_);
v___x_1280_ = lean_nat_land(v___x_1273_, v_val_1272_);
lean_dec(v_val_1272_);
v___x_1281_ = lean_unsigned_to_nat(0u);
v___x_1282_ = lean_nat_dec_eq(v___x_1280_, v___x_1281_);
lean_dec(v___x_1280_);
if (v___x_1282_ == 0)
{
uint8_t v___x_1283_; 
v___x_1283_ = 1;
v___y_1276_ = v___x_1283_;
goto v___jp_1275_;
}
else
{
uint8_t v___x_1284_; 
v___x_1284_ = 0;
v___y_1276_ = v___x_1284_;
goto v___jp_1275_;
}
v___jp_1275_:
{
lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; 
v___x_1277_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1277_, 0, v___x_1274_);
lean_ctor_set_uint8(v___x_1277_, sizeof(void*)*1, v___y_1276_);
v___x_1278_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1278_, 0, v_aig_1240_);
lean_ctor_set(v___x_1278_, 1, v___x_1277_);
v___x_1279_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1279_, 0, v___x_1278_);
lean_ctor_set(v___x_1279_, 1, v_cache_1242_);
return v___x_1279_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_goCache_spec__0(lean_object* v_00_u03b2_1285_, lean_object* v_m_1286_, lean_object* v_a_1287_){
_start:
{
lean_object* v___x_1288_; 
v___x_1288_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_goCache_spec__0___redArg(v_m_1286_, v_a_1287_);
return v___x_1288_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_goCache_spec__0___boxed(lean_object* v_00_u03b2_1289_, lean_object* v_m_1290_, lean_object* v_a_1291_){
_start:
{
lean_object* v_res_1292_; 
v_res_1292_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_goCache_spec__0(v_00_u03b2_1289_, v_m_1290_, v_a_1291_);
lean_dec_ref(v_a_1291_);
lean_dec_ref(v_m_1290_);
return v_res_1292_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_goCache_spec__1(lean_object* v_00_u03b2_1293_, lean_object* v_m_1294_, lean_object* v_a_1295_, lean_object* v_b_1296_){
_start:
{
lean_object* v___x_1297_; 
v___x_1297_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_goCache_spec__1___redArg(v_m_1294_, v_a_1295_, v_b_1296_);
return v___x_1297_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_goCache_spec__0_spec__0(lean_object* v_00_u03b2_1298_, lean_object* v_a_1299_, lean_object* v_x_1300_){
_start:
{
lean_object* v___x_1301_; 
v___x_1301_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_goCache_spec__0_spec__0___redArg(v_a_1299_, v_x_1300_);
return v___x_1301_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_goCache_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1302_, lean_object* v_a_1303_, lean_object* v_x_1304_){
_start:
{
lean_object* v_res_1305_; 
v_res_1305_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_goCache_spec__0_spec__0(v_00_u03b2_1302_, v_a_1303_, v_x_1304_);
lean_dec(v_x_1304_);
lean_dec_ref(v_a_1303_);
return v_res_1305_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_goCache_spec__1_spec__2(lean_object* v_00_u03b2_1306_, lean_object* v_a_1307_, lean_object* v_x_1308_){
_start:
{
uint8_t v___x_1309_; 
v___x_1309_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_goCache_spec__1_spec__2___redArg(v_a_1307_, v_x_1308_);
return v___x_1309_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_goCache_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1310_, lean_object* v_a_1311_, lean_object* v_x_1312_){
_start:
{
uint8_t v_res_1313_; lean_object* v_r_1314_; 
v_res_1313_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_goCache_spec__1_spec__2(v_00_u03b2_1310_, v_a_1311_, v_x_1312_);
lean_dec(v_x_1312_);
lean_dec_ref(v_a_1311_);
v_r_1314_ = lean_box(v_res_1313_);
return v_r_1314_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_goCache_spec__1_spec__3(lean_object* v_00_u03b2_1315_, lean_object* v_data_1316_){
_start:
{
lean_object* v___x_1317_; 
v___x_1317_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_goCache_spec__1_spec__3___redArg(v_data_1316_);
return v___x_1317_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_goCache_spec__1_spec__4(lean_object* v_00_u03b2_1318_, lean_object* v_a_1319_, lean_object* v_b_1320_, lean_object* v_x_1321_){
_start:
{
lean_object* v___x_1322_; 
v___x_1322_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_goCache_spec__1_spec__4___redArg(v_a_1319_, v_b_1320_, v_x_1321_);
return v___x_1322_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_goCache_spec__1_spec__3_spec__5(lean_object* v_00_u03b2_1323_, lean_object* v_i_1324_, lean_object* v_source_1325_, lean_object* v_target_1326_){
_start:
{
lean_object* v___x_1327_; 
v___x_1327_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_goCache_spec__1_spec__3_spec__5___redArg(v_i_1324_, v_source_1325_, v_target_1326_);
return v___x_1327_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__3_spec__7_spec__9(lean_object* v_00_u03b2_1328_, lean_object* v_m_1329_, lean_object* v_a_1330_){
_start:
{
lean_object* v___x_1331_; 
v___x_1331_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__3_spec__7_spec__9___redArg(v_m_1329_, v_a_1330_);
return v___x_1331_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__3_spec__7_spec__9___boxed(lean_object* v_00_u03b2_1332_, lean_object* v_m_1333_, lean_object* v_a_1334_){
_start:
{
lean_object* v_res_1335_; 
v_res_1335_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__3_spec__7_spec__9(v_00_u03b2_1332_, v_m_1333_, v_a_1334_);
lean_dec_ref(v_m_1333_);
return v_res_1335_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__3_spec__7_spec__11(lean_object* v_00_u03b2_1336_, lean_object* v_m_1337_, lean_object* v_a_1338_, lean_object* v_b_1339_){
_start:
{
lean_object* v___x_1340_; 
v___x_1340_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__3_spec__7_spec__11___redArg(v_m_1337_, v_a_1338_, v_b_1339_);
return v___x_1340_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_goCache_spec__1_spec__3_spec__5_spec__11(lean_object* v_00_u03b2_1341_, lean_object* v_x_1342_, lean_object* v_x_1343_){
_start:
{
lean_object* v___x_1344_; 
v___x_1344_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_goCache_spec__1_spec__3_spec__5_spec__11___redArg(v_x_1342_, v_x_1343_);
return v___x_1344_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__3_spec__7_spec__9_spec__16(lean_object* v_00_u03b2_1345_, lean_object* v_a_1346_, lean_object* v_x_1347_){
_start:
{
lean_object* v___x_1348_; 
v___x_1348_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__3_spec__7_spec__9_spec__16___redArg(v_a_1346_, v_x_1347_);
return v___x_1348_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__3_spec__7_spec__11_spec__19(lean_object* v_00_u03b2_1349_, lean_object* v_a_1350_, lean_object* v_x_1351_){
_start:
{
uint8_t v___x_1352_; 
v___x_1352_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__3_spec__7_spec__11_spec__19___redArg(v_a_1350_, v_x_1351_);
return v___x_1352_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__3_spec__7_spec__11_spec__19___boxed(lean_object* v_00_u03b2_1353_, lean_object* v_a_1354_, lean_object* v_x_1355_){
_start:
{
uint8_t v_res_1356_; lean_object* v_r_1357_; 
v_res_1356_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__3_spec__7_spec__11_spec__19(v_00_u03b2_1353_, v_a_1354_, v_x_1355_);
v_r_1357_ = lean_box(v_res_1356_);
return v_r_1357_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__3_spec__7_spec__11_spec__20(lean_object* v_00_u03b2_1358_, lean_object* v_data_1359_){
_start:
{
lean_object* v___x_1360_; 
v___x_1360_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__3_spec__7_spec__11_spec__20___redArg(v_data_1359_);
return v___x_1360_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__3_spec__7_spec__11_spec__21(lean_object* v_00_u03b2_1361_, lean_object* v_a_1362_, lean_object* v_b_1363_, lean_object* v_x_1364_){
_start:
{
lean_object* v___x_1365_; 
v___x_1365_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__3_spec__7_spec__11_spec__21___redArg(v_a_1362_, v_b_1363_, v_x_1364_);
return v___x_1365_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__3_spec__7_spec__11_spec__20_spec__21(lean_object* v_00_u03b2_1366_, lean_object* v_i_1367_, lean_object* v_source_1368_, lean_object* v_target_1369_){
_start:
{
lean_object* v___x_1370_; 
v___x_1370_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__3_spec__7_spec__11_spec__20_spec__21___redArg(v_i_1367_, v_source_1368_, v_target_1369_);
return v___x_1370_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__3_spec__7_spec__11_spec__20_spec__21_spec__22(lean_object* v_00_u03b2_1371_, lean_object* v_x_1372_, lean_object* v_x_1373_){
_start:
{
lean_object* v___x_1374_; 
v___x_1374_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_spec__3_spec__7_spec__11_spec__20_spec__21_spec__22___redArg(v_x_1372_, v_x_1373_);
return v___x_1374_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_goCache_match__3_splitter___redArg(lean_object* v_x_1375_, lean_object* v_h__1_1376_, lean_object* v_h__2_1377_){
_start:
{
if (lean_obj_tag(v_x_1375_) == 0)
{
lean_object* v___x_1378_; lean_object* v___x_1379_; 
lean_dec(v_h__1_1376_);
v___x_1378_ = lean_box(0);
v___x_1379_ = lean_apply_1(v_h__2_1377_, v___x_1378_);
return v___x_1379_;
}
else
{
lean_object* v_val_1380_; lean_object* v___x_1381_; 
lean_dec(v_h__2_1377_);
v_val_1380_ = lean_ctor_get(v_x_1375_, 0);
lean_inc(v_val_1380_);
lean_dec_ref_known(v_x_1375_, 1);
v___x_1381_ = lean_apply_1(v_h__1_1376_, v_val_1380_);
return v___x_1381_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_goCache_match__3_splitter(lean_object* v_aig_1382_, lean_object* v_motive_1383_, lean_object* v_x_1384_, lean_object* v_h__1_1385_, lean_object* v_h__2_1386_){
_start:
{
if (lean_obj_tag(v_x_1384_) == 0)
{
lean_object* v___x_1387_; lean_object* v___x_1388_; 
lean_dec(v_h__1_1385_);
v___x_1387_ = lean_box(0);
v___x_1388_ = lean_apply_1(v_h__2_1386_, v___x_1387_);
return v___x_1388_;
}
else
{
lean_object* v_val_1389_; lean_object* v___x_1390_; 
lean_dec(v_h__2_1386_);
v_val_1389_ = lean_ctor_get(v_x_1384_, 0);
lean_inc(v_val_1389_);
lean_dec_ref_known(v_x_1384_, 1);
v___x_1390_ = lean_apply_1(v_h__1_1385_, v_val_1389_);
return v___x_1390_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_goCache_match__3_splitter___boxed(lean_object* v_aig_1391_, lean_object* v_motive_1392_, lean_object* v_x_1393_, lean_object* v_h__1_1394_, lean_object* v_h__2_1395_){
_start:
{
lean_object* v_res_1396_; 
v_res_1396_ = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_goCache_match__3_splitter(v_aig_1391_, v_motive_1392_, v_x_1393_, v_h__1_1394_, v_h__2_1395_);
lean_dec_ref(v_aig_1391_);
return v_res_1396_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_goCache_match__1_splitter___redArg(lean_object* v_x_1397_, lean_object* v_h__1_1398_){
_start:
{
lean_object* v_result_1399_; lean_object* v_cache_1400_; lean_object* v___x_1401_; 
v_result_1399_ = lean_ctor_get(v_x_1397_, 0);
lean_inc_ref(v_result_1399_);
v_cache_1400_ = lean_ctor_get(v_x_1397_, 1);
lean_inc_ref(v_cache_1400_);
lean_dec_ref(v_x_1397_);
v___x_1401_ = lean_apply_2(v_h__1_1398_, v_result_1399_, v_cache_1400_);
return v___x_1401_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_goCache_match__1_splitter(lean_object* v_aig_1402_, lean_object* v_motive_1403_, lean_object* v_x_1404_, lean_object* v_h__1_1405_){
_start:
{
lean_object* v_result_1406_; lean_object* v_cache_1407_; lean_object* v___x_1408_; 
v_result_1406_ = lean_ctor_get(v_x_1404_, 0);
lean_inc_ref(v_result_1406_);
v_cache_1407_ = lean_ctor_get(v_x_1404_, 1);
lean_inc_ref(v_cache_1407_);
lean_dec_ref(v_x_1404_);
v___x_1408_ = lean_apply_2(v_h__1_1405_, v_result_1406_, v_cache_1407_);
return v___x_1408_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_goCache_match__1_splitter___boxed(lean_object* v_aig_1409_, lean_object* v_motive_1410_, lean_object* v_x_1411_, lean_object* v_h__1_1412_){
_start:
{
lean_object* v_res_1413_; 
v_res_1413_ = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_goCache_match__1_splitter(v_aig_1409_, v_motive_1410_, v_x_1411_, v_h__1_1412_);
lean_dec_ref(v_aig_1409_);
return v_res_1413_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_match__7_splitter___redArg(lean_object* v_expr_1414_, lean_object* v_h__1_1415_, lean_object* v_h__2_1416_, lean_object* v_h__3_1417_, lean_object* v_h__4_1418_, lean_object* v_h__5_1419_){
_start:
{
switch(lean_obj_tag(v_expr_1414_))
{
case 0:
{
lean_object* v_a_1420_; lean_object* v___x_1421_; 
lean_dec(v_h__5_1419_);
lean_dec(v_h__4_1418_);
lean_dec(v_h__3_1417_);
lean_dec(v_h__2_1416_);
v_a_1420_ = lean_ctor_get(v_expr_1414_, 0);
lean_inc_ref(v_a_1420_);
lean_dec_ref_known(v_expr_1414_, 1);
v___x_1421_ = lean_apply_1(v_h__1_1415_, v_a_1420_);
return v___x_1421_;
}
case 1:
{
uint8_t v_a_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; 
lean_dec(v_h__5_1419_);
lean_dec(v_h__4_1418_);
lean_dec(v_h__3_1417_);
lean_dec(v_h__1_1415_);
v_a_1422_ = lean_ctor_get_uint8(v_expr_1414_, 8);
lean_dec_ref_known(v_expr_1414_, 0);
v___x_1423_ = lean_box(v_a_1422_);
v___x_1424_ = lean_apply_1(v_h__2_1416_, v___x_1423_);
return v___x_1424_;
}
case 2:
{
lean_object* v_a_1425_; lean_object* v___x_1426_; 
lean_dec(v_h__5_1419_);
lean_dec(v_h__4_1418_);
lean_dec(v_h__2_1416_);
lean_dec(v_h__1_1415_);
v_a_1425_ = lean_ctor_get(v_expr_1414_, 0);
lean_inc_ref(v_a_1425_);
lean_dec_ref_known(v_expr_1414_, 1);
v___x_1426_ = lean_apply_1(v_h__3_1417_, v_a_1425_);
return v___x_1426_;
}
case 3:
{
uint8_t v_a_1427_; lean_object* v_a_1428_; lean_object* v_a_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; 
lean_dec(v_h__4_1418_);
lean_dec(v_h__3_1417_);
lean_dec(v_h__2_1416_);
lean_dec(v_h__1_1415_);
v_a_1427_ = lean_ctor_get_uint8(v_expr_1414_, sizeof(void*)*2 + 8);
v_a_1428_ = lean_ctor_get(v_expr_1414_, 0);
lean_inc_ref(v_a_1428_);
v_a_1429_ = lean_ctor_get(v_expr_1414_, 1);
lean_inc_ref(v_a_1429_);
lean_dec_ref_known(v_expr_1414_, 2);
v___x_1430_ = lean_box(v_a_1427_);
v___x_1431_ = lean_apply_3(v_h__5_1419_, v___x_1430_, v_a_1428_, v_a_1429_);
return v___x_1431_;
}
default: 
{
lean_object* v_a_1432_; lean_object* v_a_1433_; lean_object* v_a_1434_; lean_object* v___x_1435_; 
lean_dec(v_h__5_1419_);
lean_dec(v_h__3_1417_);
lean_dec(v_h__2_1416_);
lean_dec(v_h__1_1415_);
v_a_1432_ = lean_ctor_get(v_expr_1414_, 0);
lean_inc_ref(v_a_1432_);
v_a_1433_ = lean_ctor_get(v_expr_1414_, 1);
lean_inc_ref(v_a_1433_);
v_a_1434_ = lean_ctor_get(v_expr_1414_, 2);
lean_inc_ref(v_a_1434_);
lean_dec_ref_known(v_expr_1414_, 3);
v___x_1435_ = lean_apply_3(v_h__4_1418_, v_a_1432_, v_a_1433_, v_a_1434_);
return v___x_1435_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_match__7_splitter(lean_object* v_motive_1436_, lean_object* v_expr_1437_, lean_object* v_h__1_1438_, lean_object* v_h__2_1439_, lean_object* v_h__3_1440_, lean_object* v_h__4_1441_, lean_object* v_h__5_1442_){
_start:
{
switch(lean_obj_tag(v_expr_1437_))
{
case 0:
{
lean_object* v_a_1443_; lean_object* v___x_1444_; 
lean_dec(v_h__5_1442_);
lean_dec(v_h__4_1441_);
lean_dec(v_h__3_1440_);
lean_dec(v_h__2_1439_);
v_a_1443_ = lean_ctor_get(v_expr_1437_, 0);
lean_inc_ref(v_a_1443_);
lean_dec_ref_known(v_expr_1437_, 1);
v___x_1444_ = lean_apply_1(v_h__1_1438_, v_a_1443_);
return v___x_1444_;
}
case 1:
{
uint8_t v_a_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; 
lean_dec(v_h__5_1442_);
lean_dec(v_h__4_1441_);
lean_dec(v_h__3_1440_);
lean_dec(v_h__1_1438_);
v_a_1445_ = lean_ctor_get_uint8(v_expr_1437_, 8);
lean_dec_ref_known(v_expr_1437_, 0);
v___x_1446_ = lean_box(v_a_1445_);
v___x_1447_ = lean_apply_1(v_h__2_1439_, v___x_1446_);
return v___x_1447_;
}
case 2:
{
lean_object* v_a_1448_; lean_object* v___x_1449_; 
lean_dec(v_h__5_1442_);
lean_dec(v_h__4_1441_);
lean_dec(v_h__2_1439_);
lean_dec(v_h__1_1438_);
v_a_1448_ = lean_ctor_get(v_expr_1437_, 0);
lean_inc_ref(v_a_1448_);
lean_dec_ref_known(v_expr_1437_, 1);
v___x_1449_ = lean_apply_1(v_h__3_1440_, v_a_1448_);
return v___x_1449_;
}
case 3:
{
uint8_t v_a_1450_; lean_object* v_a_1451_; lean_object* v_a_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; 
lean_dec(v_h__4_1441_);
lean_dec(v_h__3_1440_);
lean_dec(v_h__2_1439_);
lean_dec(v_h__1_1438_);
v_a_1450_ = lean_ctor_get_uint8(v_expr_1437_, sizeof(void*)*2 + 8);
v_a_1451_ = lean_ctor_get(v_expr_1437_, 0);
lean_inc_ref(v_a_1451_);
v_a_1452_ = lean_ctor_get(v_expr_1437_, 1);
lean_inc_ref(v_a_1452_);
lean_dec_ref_known(v_expr_1437_, 2);
v___x_1453_ = lean_box(v_a_1450_);
v___x_1454_ = lean_apply_3(v_h__5_1442_, v___x_1453_, v_a_1451_, v_a_1452_);
return v___x_1454_;
}
default: 
{
lean_object* v_a_1455_; lean_object* v_a_1456_; lean_object* v_a_1457_; lean_object* v___x_1458_; 
lean_dec(v_h__5_1442_);
lean_dec(v_h__3_1440_);
lean_dec(v_h__2_1439_);
lean_dec(v_h__1_1438_);
v_a_1455_ = lean_ctor_get(v_expr_1437_, 0);
lean_inc_ref(v_a_1455_);
v_a_1456_ = lean_ctor_get(v_expr_1437_, 1);
lean_inc_ref(v_a_1456_);
v_a_1457_ = lean_ctor_get(v_expr_1437_, 2);
lean_inc_ref(v_a_1457_);
lean_dec_ref_known(v_expr_1437_, 3);
v___x_1458_ = lean_apply_3(v_h__4_1441_, v_a_1455_, v_a_1456_, v_a_1457_);
return v___x_1458_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_match__1_splitter___redArg(lean_object* v_x_1459_, lean_object* v_h__1_1460_){
_start:
{
lean_object* v_result_1461_; lean_object* v_cache_1462_; lean_object* v_aig_1463_; lean_object* v_ref_1464_; lean_object* v___x_1465_; 
v_result_1461_ = lean_ctor_get(v_x_1459_, 0);
lean_inc_ref(v_result_1461_);
v_cache_1462_ = lean_ctor_get(v_x_1459_, 1);
lean_inc_ref(v_cache_1462_);
lean_dec_ref(v_x_1459_);
v_aig_1463_ = lean_ctor_get(v_result_1461_, 0);
lean_inc_ref(v_aig_1463_);
v_ref_1464_ = lean_ctor_get(v_result_1461_, 1);
lean_inc_ref(v_ref_1464_);
lean_dec_ref(v_result_1461_);
v___x_1465_ = lean_apply_4(v_h__1_1460_, v_aig_1463_, v_ref_1464_, lean_box(0), v_cache_1462_);
return v___x_1465_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_match__1_splitter(lean_object* v_aig_1466_, lean_object* v_motive_1467_, lean_object* v_x_1468_, lean_object* v_h__1_1469_){
_start:
{
lean_object* v_result_1470_; lean_object* v_cache_1471_; lean_object* v_aig_1472_; lean_object* v_ref_1473_; lean_object* v___x_1474_; 
v_result_1470_ = lean_ctor_get(v_x_1468_, 0);
lean_inc_ref(v_result_1470_);
v_cache_1471_ = lean_ctor_get(v_x_1468_, 1);
lean_inc_ref(v_cache_1471_);
lean_dec_ref(v_x_1468_);
v_aig_1472_ = lean_ctor_get(v_result_1470_, 0);
lean_inc_ref(v_aig_1472_);
v_ref_1473_ = lean_ctor_get(v_result_1470_, 1);
lean_inc_ref(v_ref_1473_);
lean_dec_ref(v_result_1470_);
v___x_1474_ = lean_apply_4(v_h__1_1469_, v_aig_1472_, v_ref_1473_, lean_box(0), v_cache_1471_);
return v___x_1474_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_match__1_splitter___boxed(lean_object* v_aig_1475_, lean_object* v_motive_1476_, lean_object* v_x_1477_, lean_object* v_h__1_1478_){
_start:
{
lean_object* v_res_1479_; 
v_res_1479_ = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_match__1_splitter(v_aig_1475_, v_motive_1476_, v_x_1477_, v_h__1_1478_);
lean_dec_ref(v_aig_1475_);
return v_res_1479_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_match__3_splitter___redArg(lean_object* v_x_1480_, lean_object* v_h__1_1481_){
_start:
{
lean_object* v_result_1482_; lean_object* v_cache_1483_; lean_object* v_aig_1484_; lean_object* v_ref_1485_; lean_object* v___x_1486_; 
v_result_1482_ = lean_ctor_get(v_x_1480_, 0);
lean_inc_ref(v_result_1482_);
v_cache_1483_ = lean_ctor_get(v_x_1480_, 1);
lean_inc_ref(v_cache_1483_);
lean_dec_ref(v_x_1480_);
v_aig_1484_ = lean_ctor_get(v_result_1482_, 0);
lean_inc_ref(v_aig_1484_);
v_ref_1485_ = lean_ctor_get(v_result_1482_, 1);
lean_inc_ref(v_ref_1485_);
lean_dec_ref(v_result_1482_);
v___x_1486_ = lean_apply_4(v_h__1_1481_, v_aig_1484_, v_ref_1485_, lean_box(0), v_cache_1483_);
return v___x_1486_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_match__3_splitter(lean_object* v_aig_1487_, lean_object* v_motive_1488_, lean_object* v_x_1489_, lean_object* v_h__1_1490_){
_start:
{
lean_object* v_result_1491_; lean_object* v_cache_1492_; lean_object* v_aig_1493_; lean_object* v_ref_1494_; lean_object* v___x_1495_; 
v_result_1491_ = lean_ctor_get(v_x_1489_, 0);
lean_inc_ref(v_result_1491_);
v_cache_1492_ = lean_ctor_get(v_x_1489_, 1);
lean_inc_ref(v_cache_1492_);
lean_dec_ref(v_x_1489_);
v_aig_1493_ = lean_ctor_get(v_result_1491_, 0);
lean_inc_ref(v_aig_1493_);
v_ref_1494_ = lean_ctor_get(v_result_1491_, 1);
lean_inc_ref(v_ref_1494_);
lean_dec_ref(v_result_1491_);
v___x_1495_ = lean_apply_4(v_h__1_1490_, v_aig_1493_, v_ref_1494_, lean_box(0), v_cache_1492_);
return v___x_1495_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_match__3_splitter___boxed(lean_object* v_aig_1496_, lean_object* v_motive_1497_, lean_object* v_x_1498_, lean_object* v_h__1_1499_){
_start:
{
lean_object* v_res_1500_; 
v_res_1500_ = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_match__3_splitter(v_aig_1496_, v_motive_1497_, v_x_1498_, v_h__1_1499_);
lean_dec_ref(v_aig_1496_);
return v_res_1500_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_match__5_splitter___redArg(uint8_t v_g_1501_, lean_object* v_h__1_1502_, lean_object* v_h__2_1503_, lean_object* v_h__3_1504_, lean_object* v_h__4_1505_){
_start:
{
switch(v_g_1501_)
{
case 0:
{
lean_object* v___x_1506_; lean_object* v___x_1507_; 
lean_dec(v_h__4_1505_);
lean_dec(v_h__3_1504_);
lean_dec(v_h__2_1503_);
v___x_1506_ = lean_box(0);
v___x_1507_ = lean_apply_1(v_h__1_1502_, v___x_1506_);
return v___x_1507_;
}
case 1:
{
lean_object* v___x_1508_; lean_object* v___x_1509_; 
lean_dec(v_h__4_1505_);
lean_dec(v_h__3_1504_);
lean_dec(v_h__1_1502_);
v___x_1508_ = lean_box(0);
v___x_1509_ = lean_apply_1(v_h__2_1503_, v___x_1508_);
return v___x_1509_;
}
case 2:
{
lean_object* v___x_1510_; lean_object* v___x_1511_; 
lean_dec(v_h__4_1505_);
lean_dec(v_h__2_1503_);
lean_dec(v_h__1_1502_);
v___x_1510_ = lean_box(0);
v___x_1511_ = lean_apply_1(v_h__3_1504_, v___x_1510_);
return v___x_1511_;
}
default: 
{
lean_object* v___x_1512_; lean_object* v___x_1513_; 
lean_dec(v_h__3_1504_);
lean_dec(v_h__2_1503_);
lean_dec(v_h__1_1502_);
v___x_1512_ = lean_box(0);
v___x_1513_ = lean_apply_1(v_h__4_1505_, v___x_1512_);
return v___x_1513_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_match__5_splitter___redArg___boxed(lean_object* v_g_1514_, lean_object* v_h__1_1515_, lean_object* v_h__2_1516_, lean_object* v_h__3_1517_, lean_object* v_h__4_1518_){
_start:
{
uint8_t v_g_42__boxed_1519_; lean_object* v_res_1520_; 
v_g_42__boxed_1519_ = lean_unbox(v_g_1514_);
v_res_1520_ = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_match__5_splitter___redArg(v_g_42__boxed_1519_, v_h__1_1515_, v_h__2_1516_, v_h__3_1517_, v_h__4_1518_);
return v_res_1520_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_match__5_splitter(lean_object* v_motive_1521_, uint8_t v_g_1522_, lean_object* v_h__1_1523_, lean_object* v_h__2_1524_, lean_object* v_h__3_1525_, lean_object* v_h__4_1526_){
_start:
{
switch(v_g_1522_)
{
case 0:
{
lean_object* v___x_1527_; lean_object* v___x_1528_; 
lean_dec(v_h__4_1526_);
lean_dec(v_h__3_1525_);
lean_dec(v_h__2_1524_);
v___x_1527_ = lean_box(0);
v___x_1528_ = lean_apply_1(v_h__1_1523_, v___x_1527_);
return v___x_1528_;
}
case 1:
{
lean_object* v___x_1529_; lean_object* v___x_1530_; 
lean_dec(v_h__4_1526_);
lean_dec(v_h__3_1525_);
lean_dec(v_h__1_1523_);
v___x_1529_ = lean_box(0);
v___x_1530_ = lean_apply_1(v_h__2_1524_, v___x_1529_);
return v___x_1530_;
}
case 2:
{
lean_object* v___x_1531_; lean_object* v___x_1532_; 
lean_dec(v_h__4_1526_);
lean_dec(v_h__2_1524_);
lean_dec(v_h__1_1523_);
v___x_1531_ = lean_box(0);
v___x_1532_ = lean_apply_1(v_h__3_1525_, v___x_1531_);
return v___x_1532_;
}
default: 
{
lean_object* v___x_1533_; lean_object* v___x_1534_; 
lean_dec(v_h__3_1525_);
lean_dec(v_h__2_1524_);
lean_dec(v_h__1_1523_);
v___x_1533_ = lean_box(0);
v___x_1534_ = lean_apply_1(v_h__4_1526_, v___x_1533_);
return v___x_1534_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_match__5_splitter___boxed(lean_object* v_motive_1535_, lean_object* v_g_1536_, lean_object* v_h__1_1537_, lean_object* v_h__2_1538_, lean_object* v_h__3_1539_, lean_object* v_h__4_1540_){
_start:
{
uint8_t v_g_61__boxed_1541_; lean_object* v_res_1542_; 
v_g_61__boxed_1541_ = lean_unbox(v_g_1536_);
v_res_1542_ = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go_match__5_splitter(v_motive_1535_, v_g_61__boxed_1541_, v_h__1_1537_, v_h__2_1538_, v_h__3_1539_, v_h__4_1540_);
return v_res_1542_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache(lean_object* v_expr_1543_, lean_object* v_aig_1544_, lean_object* v_cache_1545_){
_start:
{
lean_object* v___x_1546_; 
v___x_1546_ = l_Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_goCache(v_aig_1544_, v_expr_1543_, v_cache_1545_);
return v___x_1546_;
}
}
static lean_object* _init_l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; 
v___x_1551_ = lean_box(0);
v___x_1552_ = lean_unsigned_to_nat(16u);
v___x_1553_ = lean_mk_array(v___x_1552_, v___x_1551_);
return v___x_1553_;
}
}
static lean_object* _init_l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__2(void){
_start:
{
lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; 
v___x_1554_ = lean_obj_once(&l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__1, &l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__1_once, _init_l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__1);
v___x_1555_ = lean_unsigned_to_nat(0u);
v___x_1556_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1556_, 0, v___x_1555_);
lean_ctor_set(v___x_1556_, 1, v___x_1554_);
return v___x_1556_;
}
}
static lean_object* _init_l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; 
v___x_1557_ = lean_obj_once(&l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__2, &l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__2_once, _init_l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__2);
v___x_1558_ = ((lean_object*)(l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__0));
v___x_1559_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1559_, 0, v___x_1558_);
lean_ctor_set(v___x_1559_, 1, v___x_1557_);
return v___x_1559_;
}
}
static lean_object* _init_l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0(void){
_start:
{
lean_object* v___x_1560_; 
v___x_1560_ = lean_obj_once(&l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__3, &l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__3_once, _init_l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__3);
return v___x_1560_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast(lean_object* v_expr_1561_){
_start:
{
lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v_result_1565_; 
v___x_1562_ = l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0;
v___x_1563_ = lean_obj_once(&l_Std_Tactic_BVDecide_BVLogicalExpr_Cache_empty___redArg___closed__2, &l_Std_Tactic_BVDecide_BVLogicalExpr_Cache_empty___redArg___closed__2_once, _init_l_Std_Tactic_BVDecide_BVLogicalExpr_Cache_empty___redArg___closed__2);
v___x_1564_ = l_Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_goCache(v___x_1562_, v_expr_1561_, v___x_1563_);
v_result_1565_ = lean_ctor_get(v___x_1564_, 0);
lean_inc_ref(v_result_1565_);
lean_dec_ref(v___x_1564_);
return v_result_1565_;
}
}
lean_object* runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Pred(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Pred(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0 = _init_l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0();
lean_mark_persistent(l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Pred(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Pred(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure(builtin);
}
#ifdef __cplusplus
}
#endif
