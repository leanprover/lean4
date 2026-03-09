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
lean_object* l_Std_Tactic_BVDecide_instDecidableEqBVBit___boxed(lean_object*, lean_object*);
uint8_t l_Std_Sat_AIG_instDecidableEqDecl_decEq___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__12___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__10___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__10___redArg___boxed(lean_object*, lean_object*);
uint64_t l_Std_Tactic_BVDecide_instHashableBVBit_hash(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
uint64_t l_Std_Sat_AIG_instHashableFanin_hash(lean_object*);
LEAN_EXPORT uint64_t l_Std_Sat_AIG_instHashableDecl_hash___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__1_spec__6(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instHashableDecl_hash___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__1_spec__6___boxed(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__11_spec__12___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__11___redArg(lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_getConstant___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_getConstant___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__1_spec__7___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0___closed__0 = (const lean_object*)&l_Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0___closed__0_value;
lean_object* l_Bool_toNat(uint8_t);
lean_object* lean_nat_lor(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkBEqCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkOrCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkIfCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkXorCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__1(lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_BVPred_bitblast(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__1_spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__10___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__11(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__12(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__11_spec__12(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static const lean_array_object l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__0 = (const lean_object*)&l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__0_value;
static lean_once_cell_t l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__1;
static lean_once_cell_t l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__2;
static lean_once_cell_t l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__3;
LEAN_EXPORT lean_object* l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0;
static lean_once_cell_t l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___closed__0;
static lean_once_cell_t l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___closed__1;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_match__5_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_match__5_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_match__1_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_match__3_splitter___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_match__3_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_match__3_splitter(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_match__3_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__12___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_19; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_3, 1);
x_6 = lean_ctor_get(x_3, 2);
x_19 = !lean_is_exclusive(x_3);
if (x_19 == 0)
{
x_7 = x_3;
x_8 = x_19;
goto block_18;
}
else
{
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_dec(x_3);
x_7 = lean_box(0);
x_8 = x_19;
goto block_18;
}
block_18:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_instDecidableEqBVBit___boxed), 2, 0);
lean_inc(x_1);
lean_inc(x_4);
x_10 = l_Std_Sat_AIG_instDecidableEqDecl_decEq___redArg(x_9, x_4, x_1);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__12___redArg(x_1, x_2, x_6);
if (x_8 == 0)
{
lean_ctor_set(x_7, 2, x_11);
x_12 = x_7;
goto block_13;
}
else
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_14, 0, x_4);
lean_ctor_set(x_14, 1, x_5);
lean_ctor_set(x_14, 2, x_11);
x_12 = x_14;
goto block_13;
}
block_13:
{
return x_12;
}
}
else
{
lean_object* x_15; 
lean_dec(x_5);
lean_dec(x_4);
if (x_8 == 0)
{
lean_ctor_set(x_7, 1, x_2);
lean_ctor_set(x_7, 0, x_1);
x_15 = x_7;
goto block_16;
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_2);
lean_ctor_set(x_17, 2, x_6);
x_15 = x_17;
goto block_16;
}
block_16:
{
return x_15;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__10___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
lean_dec(x_1);
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
lean_dec_ref(x_2);
x_6 = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_instDecidableEqBVBit___boxed), 2, 0);
lean_inc(x_1);
x_7 = l_Std_Sat_AIG_instDecidableEqDecl_decEq___redArg(x_6, x_4, x_1);
if (x_7 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
lean_dec(x_5);
lean_dec(x_1);
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__10___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__10___redArg(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint64_t l_Std_Sat_AIG_instHashableDecl_hash___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__1_spec__6(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
uint64_t x_2; 
x_2 = 0;
return x_2;
}
case 1:
{
lean_object* x_3; uint64_t x_4; uint64_t x_5; uint64_t x_6; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = 1;
x_5 = l_Std_Tactic_BVDecide_instHashableBVBit_hash(x_3);
x_6 = lean_uint64_mix_hash(x_4, x_5);
return x_6;
}
default: 
{
lean_object* x_7; lean_object* x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
x_9 = 2;
x_10 = l_Std_Sat_AIG_instHashableFanin_hash(x_7);
x_11 = lean_uint64_mix_hash(x_9, x_10);
x_12 = l_Std_Sat_AIG_instHashableFanin_hash(x_8);
x_13 = lean_uint64_mix_hash(x_11, x_12);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instHashableDecl_hash___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__1_spec__6___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l_Std_Sat_AIG_instHashableDecl_hash___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__1_spec__6(x_1);
lean_dec(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_28; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_2, 2);
x_28 = !lean_is_exclusive(x_2);
if (x_28 == 0)
{
x_6 = x_2;
x_7 = x_28;
goto block_27;
}
else
{
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_dec(x_2);
x_6 = lean_box(0);
x_7 = x_28;
goto block_27;
}
block_27:
{
lean_object* x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; size_t x_16; size_t x_17; size_t x_18; size_t x_19; size_t x_20; lean_object* x_21; lean_object* x_22; 
x_8 = lean_array_get_size(x_1);
x_9 = l_Std_Sat_AIG_instHashableDecl_hash___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__1_spec__6(x_3);
x_10 = 32;
x_11 = lean_uint64_shift_right(x_9, x_10);
x_12 = lean_uint64_xor(x_9, x_11);
x_13 = 16;
x_14 = lean_uint64_shift_right(x_12, x_13);
x_15 = lean_uint64_xor(x_12, x_14);
x_16 = lean_uint64_to_usize(x_15);
x_17 = lean_usize_of_nat(x_8);
x_18 = 1;
x_19 = lean_usize_sub(x_17, x_18);
x_20 = lean_usize_land(x_16, x_19);
x_21 = lean_array_uget_borrowed(x_1, x_20);
lean_inc(x_21);
if (x_7 == 0)
{
lean_ctor_set(x_6, 2, x_21);
x_22 = x_6;
goto block_25;
}
else
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_26, 0, x_3);
lean_ctor_set(x_26, 1, x_4);
lean_ctor_set(x_26, 2, x_21);
x_22 = x_26;
goto block_25;
}
block_25:
{
lean_object* x_23; 
x_23 = lean_array_uset(x_1, x_20, x_22);
x_1 = x_23;
x_2 = x_5;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__11_spec__12___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_1, x_4);
if (x_5 == 0)
{
lean_dec_ref(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean_box(0);
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg(x_3, x_6);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_1, x_10);
lean_dec(x_1);
x_1 = x_11;
x_2 = x_8;
x_3 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__11___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(2u);
x_4 = lean_nat_mul(x_2, x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_box(0);
x_7 = lean_mk_array(x_4, x_6);
x_8 = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__11_spec__12___redArg(x_5, x_1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_48; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_48 = !lean_is_exclusive(x_1);
if (x_48 == 0)
{
x_6 = x_1;
x_7 = x_48;
goto block_47;
}
else
{
lean_inc(x_5);
lean_inc(x_4);
lean_dec(x_1);
x_6 = lean_box(0);
x_7 = x_48;
goto block_47;
}
block_47:
{
lean_object* x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; size_t x_16; size_t x_17; size_t x_18; size_t x_19; size_t x_20; lean_object* x_21; uint8_t x_22; 
x_8 = lean_array_get_size(x_5);
x_9 = l_Std_Sat_AIG_instHashableDecl_hash___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__1_spec__6(x_2);
x_10 = 32;
x_11 = lean_uint64_shift_right(x_9, x_10);
x_12 = lean_uint64_xor(x_9, x_11);
x_13 = 16;
x_14 = lean_uint64_shift_right(x_12, x_13);
x_15 = lean_uint64_xor(x_12, x_14);
x_16 = lean_uint64_to_usize(x_15);
x_17 = lean_usize_of_nat(x_8);
x_18 = 1;
x_19 = lean_usize_sub(x_17, x_18);
x_20 = lean_usize_land(x_16, x_19);
x_21 = lean_array_uget_borrowed(x_5, x_20);
lean_inc(x_21);
lean_inc(x_2);
x_22 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__10___redArg(x_2, x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_4, x_23);
lean_dec(x_4);
lean_inc(x_21);
x_25 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_25, 0, x_2);
lean_ctor_set(x_25, 1, x_3);
lean_ctor_set(x_25, 2, x_21);
x_26 = lean_array_uset(x_5, x_20, x_25);
x_27 = lean_unsigned_to_nat(4u);
x_28 = lean_nat_mul(x_24, x_27);
x_29 = lean_unsigned_to_nat(3u);
x_30 = lean_nat_div(x_28, x_29);
lean_dec(x_28);
x_31 = lean_array_get_size(x_26);
x_32 = lean_nat_dec_le(x_30, x_31);
lean_dec(x_30);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__11___redArg(x_26);
if (x_7 == 0)
{
lean_ctor_set(x_6, 1, x_33);
lean_ctor_set(x_6, 0, x_24);
x_34 = x_6;
goto block_35;
}
else
{
lean_object* x_36; 
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_24);
lean_ctor_set(x_36, 1, x_33);
x_34 = x_36;
goto block_35;
}
block_35:
{
return x_34;
}
}
else
{
lean_object* x_37; 
if (x_7 == 0)
{
lean_ctor_set(x_6, 1, x_26);
lean_ctor_set(x_6, 0, x_24);
x_37 = x_6;
goto block_38;
}
else
{
lean_object* x_39; 
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_24);
lean_ctor_set(x_39, 1, x_26);
x_37 = x_39;
goto block_38;
}
block_38:
{
return x_37;
}
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_inc(x_21);
x_40 = lean_box(0);
x_41 = lean_array_uset(x_5, x_20, x_40);
x_42 = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__12___redArg(x_2, x_3, x_21);
x_43 = lean_array_uset(x_41, x_20, x_42);
if (x_7 == 0)
{
lean_ctor_set(x_6, 1, x_43);
x_44 = x_6;
goto block_45;
}
else
{
lean_object* x_46; 
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_4);
lean_ctor_set(x_46, 1, x_43);
x_44 = x_46;
goto block_45;
}
block_45:
{
return x_44;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_getConstant___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get_uint8(x_2, sizeof(void*)*1);
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_array_fget_borrowed(x_5, x_3);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_box(x_4);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
else
{
lean_object* x_9; 
x_9 = lean_box(0);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_getConstant___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Sat_AIG_getConstant___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__2(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__1_spec__7___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
lean_dec(x_1);
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 2);
lean_inc(x_6);
lean_dec_ref(x_2);
x_7 = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_instDecidableEqBVBit___boxed), 2, 0);
lean_inc(x_1);
x_8 = l_Std_Sat_AIG_instDecidableEqDecl_decEq___redArg(x_7, x_4, x_1);
if (x_8 == 0)
{
lean_dec(x_5);
x_2 = x_6;
goto _start;
}
else
{
lean_object* x_10; 
lean_dec(x_6);
lean_dec(x_1);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_5);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__1___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint64_t x_5; uint64_t x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; size_t x_12; size_t x_13; size_t x_14; size_t x_15; size_t x_16; lean_object* x_17; lean_object* x_18; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = l_Std_Sat_AIG_instHashableDecl_hash___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__1_spec__6(x_2);
x_6 = 32;
x_7 = lean_uint64_shift_right(x_5, x_6);
x_8 = lean_uint64_xor(x_5, x_7);
x_9 = 16;
x_10 = lean_uint64_shift_right(x_8, x_9);
x_11 = lean_uint64_xor(x_8, x_10);
x_12 = lean_uint64_to_usize(x_11);
x_13 = lean_usize_of_nat(x_4);
x_14 = 1;
x_15 = lean_usize_sub(x_13, x_14);
x_16 = lean_usize_land(x_12, x_15);
x_17 = lean_array_uget_borrowed(x_3, x_16);
lean_inc(x_17);
x_18 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__1_spec__7___redArg(x_2, x_17);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__1___redArg(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_87; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_87 = !lean_is_exclusive(x_2);
if (x_87 == 0)
{
x_5 = x_2;
x_6 = x_87;
goto block_86;
}
else
{
lean_inc(x_4);
lean_inc(x_3);
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = x_87;
goto block_86;
}
block_86:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_85; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
x_85 = !lean_is_exclusive(x_1);
if (x_85 == 0)
{
x_9 = x_1;
x_10 = x_85;
goto block_84;
}
else
{
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_1);
x_9 = lean_box(0);
x_10 = x_85;
goto block_84;
}
block_84:
{
lean_object* x_11; uint8_t x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_11 = lean_ctor_get(x_3, 0);
lean_inc(x_11);
x_12 = lean_ctor_get_uint8(x_3, sizeof(void*)*1);
x_13 = lean_ctor_get(x_4, 0);
x_14 = lean_ctor_get_uint8(x_4, sizeof(void*)*1);
x_15 = lean_unsigned_to_nat(2u);
x_16 = lean_nat_mul(x_11, x_15);
x_17 = l_Bool_toNat(x_12);
x_18 = lean_nat_lor(x_16, x_17);
lean_dec(x_17);
lean_dec(x_16);
x_19 = lean_nat_mul(x_13, x_15);
x_20 = l_Bool_toNat(x_14);
x_21 = lean_nat_lor(x_19, x_20);
lean_dec(x_20);
lean_dec(x_19);
if (x_6 == 0)
{
lean_ctor_set_tag(x_5, 2);
lean_ctor_set(x_5, 1, x_21);
lean_ctor_set(x_5, 0, x_18);
x_22 = x_5;
goto block_82;
}
else
{
lean_object* x_83; 
x_83 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_83, 0, x_18);
lean_ctor_set(x_83, 1, x_21);
x_22 = x_83;
goto block_82;
}
block_82:
{
lean_object* x_23; 
lean_inc_ref(x_22);
x_23 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__1___redArg(x_8, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; 
lean_inc(x_13);
lean_inc_ref(x_8);
lean_inc_ref(x_7);
if (x_10 == 0)
{
x_24 = x_9;
goto block_66;
}
else
{
lean_object* x_67; 
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_7);
lean_ctor_set(x_67, 1, x_8);
x_24 = x_67;
goto block_66;
}
block_66:
{
uint8_t x_25; uint8_t x_30; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; uint8_t x_64; 
x_40 = l_Std_Sat_AIG_getConstant___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__2(x_24, x_3);
lean_dec_ref(x_3);
x_41 = l_Std_Sat_AIG_getConstant___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__2(x_24, x_4);
x_64 = !lean_is_exclusive(x_4);
if (x_64 == 0)
{
lean_object* x_65; 
x_65 = lean_ctor_get(x_4, 0);
lean_dec(x_65);
x_42 = x_4;
x_43 = x_64;
goto block_63;
}
else
{
lean_dec(x_4);
x_42 = lean_box(0);
x_43 = x_64;
goto block_63;
}
block_29:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_unsigned_to_nat(0u);
x_27 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set_uint8(x_27, sizeof(void*)*1, x_25);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_24);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
block_33:
{
if (x_30 == 0)
{
lean_dec(x_11);
x_25 = x_30;
goto block_29;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_31, 0, x_11);
lean_ctor_set_uint8(x_31, sizeof(void*)*1, x_12);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_24);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
block_36:
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_34, 0, x_13);
lean_ctor_set_uint8(x_34, sizeof(void*)*1, x_14);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_24);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
block_39:
{
lean_object* x_37; lean_object* x_38; 
x_37 = ((lean_object*)(l_Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0___closed__0));
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_24);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
block_63:
{
if (lean_obj_tag(x_40) == 1)
{
lean_object* x_44; uint8_t x_45; 
lean_del_object(x_42);
lean_dec_ref(x_22);
lean_dec(x_11);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
x_44 = lean_ctor_get(x_40, 0);
lean_inc(x_44);
lean_dec_ref(x_40);
x_45 = lean_unbox(x_44);
lean_dec(x_44);
if (x_45 == 0)
{
lean_dec(x_41);
lean_dec(x_13);
goto block_39;
}
else
{
if (lean_obj_tag(x_41) == 1)
{
lean_object* x_46; uint8_t x_47; 
x_46 = lean_ctor_get(x_41, 0);
lean_inc(x_46);
lean_dec_ref(x_41);
x_47 = lean_unbox(x_46);
lean_dec(x_46);
if (x_47 == 0)
{
lean_dec(x_13);
goto block_39;
}
else
{
goto block_36;
}
}
else
{
lean_dec(x_41);
goto block_36;
}
}
}
else
{
lean_dec(x_40);
if (lean_obj_tag(x_41) == 1)
{
lean_object* x_48; uint8_t x_49; 
lean_dec_ref(x_22);
lean_dec(x_13);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
x_48 = lean_ctor_get(x_41, 0);
lean_inc(x_48);
lean_dec_ref(x_41);
x_49 = lean_unbox(x_48);
lean_dec(x_48);
if (x_49 == 0)
{
lean_del_object(x_42);
lean_dec(x_11);
goto block_39;
}
else
{
lean_object* x_50; 
if (x_43 == 0)
{
lean_ctor_set(x_42, 0, x_11);
x_50 = x_42;
goto block_52;
}
else
{
lean_object* x_53; 
x_53 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_53, 0, x_11);
x_50 = x_53;
goto block_52;
}
block_52:
{
lean_object* x_51; 
lean_ctor_set_uint8(x_50, sizeof(void*)*1, x_12);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_24);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
else
{
uint8_t x_54; 
lean_dec(x_41);
x_54 = lean_nat_dec_eq(x_11, x_13);
lean_dec(x_13);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec_ref(x_24);
lean_dec(x_11);
x_55 = lean_array_get_size(x_7);
lean_inc_ref(x_22);
x_56 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3___redArg(x_8, x_22, x_55);
x_57 = lean_array_push(x_7, x_22);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_56);
if (x_43 == 0)
{
lean_ctor_set(x_42, 0, x_55);
x_59 = x_42;
goto block_61;
}
else
{
lean_object* x_62; 
x_62 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_62, 0, x_55);
x_59 = x_62;
goto block_61;
}
block_61:
{
lean_object* x_60; 
lean_ctor_set_uint8(x_59, sizeof(void*)*1, x_54);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
else
{
lean_del_object(x_42);
lean_dec_ref(x_22);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
if (x_12 == 0)
{
if (x_14 == 0)
{
x_30 = x_54;
goto block_33;
}
else
{
lean_dec(x_11);
x_25 = x_12;
goto block_29;
}
}
else
{
x_30 = x_14;
goto block_33;
}
}
}
}
}
}
}
else
{
lean_object* x_68; uint8_t x_69; uint8_t x_80; 
lean_dec_ref(x_22);
lean_dec(x_11);
lean_dec_ref(x_3);
x_80 = !lean_is_exclusive(x_4);
if (x_80 == 0)
{
lean_object* x_81; 
x_81 = lean_ctor_get(x_4, 0);
lean_dec(x_81);
x_68 = x_4;
x_69 = x_80;
goto block_79;
}
else
{
lean_dec(x_4);
x_68 = lean_box(0);
x_69 = x_80;
goto block_79;
}
block_79:
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_23, 0);
lean_inc(x_70);
lean_dec_ref(x_23);
if (x_10 == 0)
{
x_71 = x_9;
goto block_77;
}
else
{
lean_object* x_78; 
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_7);
lean_ctor_set(x_78, 1, x_8);
x_71 = x_78;
goto block_77;
}
block_77:
{
uint8_t x_72; lean_object* x_73; 
x_72 = 0;
if (x_69 == 0)
{
lean_ctor_set(x_68, 0, x_70);
x_73 = x_68;
goto block_75;
}
else
{
lean_object* x_76; 
x_76 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_76, 0, x_70);
x_73 = x_76;
goto block_75;
}
block_75:
{
lean_object* x_74; 
lean_ctor_set_uint8(x_73, sizeof(void*)*1, x_72);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_71);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_19; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_19 = !lean_is_exclusive(x_2);
if (x_19 == 0)
{
x_5 = x_2;
x_6 = x_19;
goto block_18;
}
else
{
lean_inc(x_4);
lean_inc(x_3);
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = x_19;
goto block_18;
}
block_18:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_3, 0);
x_8 = lean_ctor_get(x_4, 0);
x_9 = lean_nat_dec_lt(x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; 
if (x_6 == 0)
{
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 0, x_4);
x_10 = x_5;
goto block_12;
}
else
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_4);
lean_ctor_set(x_13, 1, x_3);
x_10 = x_13;
goto block_12;
}
block_12:
{
lean_object* x_11; 
x_11 = l_Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0(x_1, x_10);
return x_11;
}
}
else
{
lean_object* x_14; 
if (x_6 == 0)
{
x_14 = x_5;
goto block_16;
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_3);
lean_ctor_set(x_17, 1, x_4);
x_14 = x_17;
goto block_16;
}
block_16:
{
lean_object* x_15; 
x_15 = l_Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0(x_1, x_14);
return x_15;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkBEqCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; uint8_t x_109; 
x_64 = lean_ctor_get(x_2, 0);
x_65 = lean_ctor_get(x_2, 1);
x_109 = !lean_is_exclusive(x_2);
if (x_109 == 0)
{
x_66 = x_2;
x_67 = x_109;
goto block_108;
}
else
{
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_2);
x_66 = lean_box(0);
x_67 = x_109;
goto block_108;
}
block_8:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
x_7 = l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0(x_3, x_6);
return x_7;
}
block_31:
{
uint8_t x_12; 
x_12 = lean_ctor_get_uint8(x_10, sizeof(void*)*1);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_21; 
x_13 = lean_ctor_get(x_10, 0);
x_21 = !lean_is_exclusive(x_10);
if (x_21 == 0)
{
x_14 = x_10;
x_15 = x_21;
goto block_20;
}
else
{
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_box(0);
x_15 = x_21;
goto block_20;
}
block_20:
{
uint8_t x_16; lean_object* x_17; 
x_16 = 1;
if (x_15 == 0)
{
x_17 = x_14;
goto block_18;
}
else
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_19, 0, x_13);
x_17 = x_19;
goto block_18;
}
block_18:
{
lean_ctor_set_uint8(x_17, sizeof(void*)*1, x_16);
x_3 = x_9;
x_4 = x_11;
x_5 = x_17;
goto block_8;
}
}
}
else
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_30; 
x_22 = lean_ctor_get(x_10, 0);
x_30 = !lean_is_exclusive(x_10);
if (x_30 == 0)
{
x_23 = x_10;
x_24 = x_30;
goto block_29;
}
else
{
lean_inc(x_22);
lean_dec(x_10);
x_23 = lean_box(0);
x_24 = x_30;
goto block_29;
}
block_29:
{
uint8_t x_25; lean_object* x_26; 
x_25 = 0;
if (x_24 == 0)
{
x_26 = x_23;
goto block_27;
}
else
{
lean_object* x_28; 
x_28 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_28, 0, x_22);
x_26 = x_28;
goto block_27;
}
block_27:
{
lean_ctor_set_uint8(x_26, sizeof(void*)*1, x_25);
x_3 = x_9;
x_4 = x_11;
x_5 = x_26;
goto block_8;
}
}
}
}
block_63:
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_37 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_37, 0, x_33);
lean_ctor_set_uint8(x_37, sizeof(void*)*1, x_34);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_39 = l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0(x_35, x_38);
x_40 = lean_ctor_get_uint8(x_32, sizeof(void*)*1);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; uint8_t x_51; 
x_41 = lean_ctor_get(x_39, 0);
lean_inc_ref(x_41);
x_42 = lean_ctor_get(x_39, 1);
lean_inc_ref(x_42);
lean_dec_ref(x_39);
x_43 = lean_ctor_get(x_32, 0);
x_51 = !lean_is_exclusive(x_32);
if (x_51 == 0)
{
x_44 = x_32;
x_45 = x_51;
goto block_50;
}
else
{
lean_inc(x_43);
lean_dec(x_32);
x_44 = lean_box(0);
x_45 = x_51;
goto block_50;
}
block_50:
{
uint8_t x_46; lean_object* x_47; 
x_46 = 1;
if (x_45 == 0)
{
x_47 = x_44;
goto block_48;
}
else
{
lean_object* x_49; 
x_49 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_49, 0, x_43);
x_47 = x_49;
goto block_48;
}
block_48:
{
lean_ctor_set_uint8(x_47, sizeof(void*)*1, x_46);
x_9 = x_41;
x_10 = x_42;
x_11 = x_47;
goto block_31;
}
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; uint8_t x_62; 
x_52 = lean_ctor_get(x_39, 0);
lean_inc_ref(x_52);
x_53 = lean_ctor_get(x_39, 1);
lean_inc_ref(x_53);
lean_dec_ref(x_39);
x_54 = lean_ctor_get(x_32, 0);
x_62 = !lean_is_exclusive(x_32);
if (x_62 == 0)
{
x_55 = x_32;
x_56 = x_62;
goto block_61;
}
else
{
lean_inc(x_54);
lean_dec(x_32);
x_55 = lean_box(0);
x_56 = x_62;
goto block_61;
}
block_61:
{
uint8_t x_57; lean_object* x_58; 
x_57 = 0;
if (x_56 == 0)
{
x_58 = x_55;
goto block_59;
}
else
{
lean_object* x_60; 
x_60 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_60, 0, x_54);
x_58 = x_60;
goto block_59;
}
block_59:
{
lean_ctor_set_uint8(x_58, sizeof(void*)*1, x_57);
x_9 = x_52;
x_10 = x_53;
x_11 = x_58;
goto block_31;
}
}
}
}
block_108:
{
lean_object* x_68; uint8_t x_69; lean_object* x_70; uint8_t x_71; uint8_t x_107; 
x_68 = lean_ctor_get(x_64, 0);
x_69 = lean_ctor_get_uint8(x_64, sizeof(void*)*1);
x_107 = !lean_is_exclusive(x_64);
if (x_107 == 0)
{
x_70 = x_64;
x_71 = x_107;
goto block_106;
}
else
{
lean_inc(x_68);
lean_dec(x_64);
x_70 = lean_box(0);
x_71 = x_107;
goto block_106;
}
block_106:
{
lean_object* x_72; uint8_t x_73; lean_object* x_74; uint8_t x_75; uint8_t x_105; 
x_72 = lean_ctor_get(x_65, 0);
x_73 = lean_ctor_get_uint8(x_65, sizeof(void*)*1);
x_105 = !lean_is_exclusive(x_65);
if (x_105 == 0)
{
x_74 = x_65;
x_75 = x_105;
goto block_104;
}
else
{
lean_inc(x_72);
lean_dec(x_65);
x_74 = lean_box(0);
x_75 = x_105;
goto block_104;
}
block_104:
{
lean_object* x_76; lean_object* x_91; 
lean_inc(x_68);
if (x_71 == 0)
{
x_91 = x_70;
goto block_102;
}
else
{
lean_object* x_103; 
x_103 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_103, 0, x_68);
lean_ctor_set_uint8(x_103, sizeof(void*)*1, x_69);
x_91 = x_103;
goto block_102;
}
block_90:
{
lean_object* x_77; 
x_77 = l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0(x_1, x_76);
if (x_69 == 0)
{
lean_object* x_78; lean_object* x_79; uint8_t x_80; lean_object* x_81; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc_ref(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc_ref(x_79);
lean_dec_ref(x_77);
x_80 = 1;
if (x_75 == 0)
{
lean_ctor_set(x_74, 0, x_68);
x_81 = x_74;
goto block_82;
}
else
{
lean_object* x_83; 
x_83 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_83, 0, x_68);
x_81 = x_83;
goto block_82;
}
block_82:
{
lean_ctor_set_uint8(x_81, sizeof(void*)*1, x_80);
x_32 = x_79;
x_33 = x_72;
x_34 = x_73;
x_35 = x_78;
x_36 = x_81;
goto block_63;
}
}
else
{
lean_object* x_84; lean_object* x_85; uint8_t x_86; lean_object* x_87; 
x_84 = lean_ctor_get(x_77, 0);
lean_inc_ref(x_84);
x_85 = lean_ctor_get(x_77, 1);
lean_inc_ref(x_85);
lean_dec_ref(x_77);
x_86 = 0;
if (x_75 == 0)
{
lean_ctor_set(x_74, 0, x_68);
x_87 = x_74;
goto block_88;
}
else
{
lean_object* x_89; 
x_89 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_89, 0, x_68);
x_87 = x_89;
goto block_88;
}
block_88:
{
lean_ctor_set_uint8(x_87, sizeof(void*)*1, x_86);
x_32 = x_85;
x_33 = x_72;
x_34 = x_73;
x_35 = x_84;
x_36 = x_87;
goto block_63;
}
}
}
block_102:
{
if (x_73 == 0)
{
uint8_t x_92; lean_object* x_93; lean_object* x_94; 
x_92 = 1;
lean_inc(x_72);
x_93 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_93, 0, x_72);
lean_ctor_set_uint8(x_93, sizeof(void*)*1, x_92);
if (x_67 == 0)
{
lean_ctor_set(x_66, 1, x_93);
lean_ctor_set(x_66, 0, x_91);
x_94 = x_66;
goto block_95;
}
else
{
lean_object* x_96; 
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_91);
lean_ctor_set(x_96, 1, x_93);
x_94 = x_96;
goto block_95;
}
block_95:
{
x_76 = x_94;
goto block_90;
}
}
else
{
uint8_t x_97; lean_object* x_98; lean_object* x_99; 
x_97 = 0;
lean_inc(x_72);
x_98 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_98, 0, x_72);
lean_ctor_set_uint8(x_98, sizeof(void*)*1, x_97);
if (x_67 == 0)
{
lean_ctor_set(x_66, 1, x_98);
lean_ctor_set(x_66, 0, x_91);
x_99 = x_66;
goto block_100;
}
else
{
lean_object* x_101; 
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_91);
lean_ctor_set(x_101, 1, x_98);
x_99 = x_101;
goto block_100;
}
block_100:
{
x_76 = x_99;
goto block_90;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkOrCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; uint8_t x_95; 
x_44 = lean_ctor_get(x_2, 0);
x_45 = lean_ctor_get(x_2, 1);
x_95 = !lean_is_exclusive(x_2);
if (x_95 == 0)
{
x_46 = x_2;
x_47 = x_95;
goto block_94;
}
else
{
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_2);
x_46 = lean_box(0);
x_47 = x_95;
goto block_94;
}
block_43:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0(x_1, x_3);
x_5 = lean_ctor_get(x_4, 1);
lean_inc_ref(x_5);
x_6 = lean_ctor_get_uint8(x_5, sizeof(void*)*1);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_23; 
x_7 = lean_ctor_get(x_4, 0);
x_23 = !lean_is_exclusive(x_4);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_4, 1);
lean_dec(x_24);
x_8 = x_4;
x_9 = x_23;
goto block_22;
}
else
{
lean_inc(x_7);
lean_dec(x_4);
x_8 = lean_box(0);
x_9 = x_23;
goto block_22;
}
block_22:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_21; 
x_10 = lean_ctor_get(x_5, 0);
x_21 = !lean_is_exclusive(x_5);
if (x_21 == 0)
{
x_11 = x_5;
x_12 = x_21;
goto block_20;
}
else
{
lean_inc(x_10);
lean_dec(x_5);
x_11 = lean_box(0);
x_12 = x_21;
goto block_20;
}
block_20:
{
uint8_t x_13; lean_object* x_14; 
x_13 = 1;
if (x_12 == 0)
{
x_14 = x_11;
goto block_18;
}
else
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_19, 0, x_10);
x_14 = x_19;
goto block_18;
}
block_18:
{
lean_object* x_15; 
lean_ctor_set_uint8(x_14, sizeof(void*)*1, x_13);
if (x_9 == 0)
{
lean_ctor_set(x_8, 1, x_14);
x_15 = x_8;
goto block_16;
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_7);
lean_ctor_set(x_17, 1, x_14);
x_15 = x_17;
goto block_16;
}
block_16:
{
return x_15;
}
}
}
}
}
else
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_41; 
x_25 = lean_ctor_get(x_4, 0);
x_41 = !lean_is_exclusive(x_4);
if (x_41 == 0)
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_4, 1);
lean_dec(x_42);
x_26 = x_4;
x_27 = x_41;
goto block_40;
}
else
{
lean_inc(x_25);
lean_dec(x_4);
x_26 = lean_box(0);
x_27 = x_41;
goto block_40;
}
block_40:
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; uint8_t x_39; 
x_28 = lean_ctor_get(x_5, 0);
x_39 = !lean_is_exclusive(x_5);
if (x_39 == 0)
{
x_29 = x_5;
x_30 = x_39;
goto block_38;
}
else
{
lean_inc(x_28);
lean_dec(x_5);
x_29 = lean_box(0);
x_30 = x_39;
goto block_38;
}
block_38:
{
uint8_t x_31; lean_object* x_32; 
x_31 = 0;
if (x_30 == 0)
{
x_32 = x_29;
goto block_36;
}
else
{
lean_object* x_37; 
x_37 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_37, 0, x_28);
x_32 = x_37;
goto block_36;
}
block_36:
{
lean_object* x_33; 
lean_ctor_set_uint8(x_32, sizeof(void*)*1, x_31);
if (x_27 == 0)
{
lean_ctor_set(x_26, 1, x_32);
x_33 = x_26;
goto block_34;
}
else
{
lean_object* x_35; 
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_25);
lean_ctor_set(x_35, 1, x_32);
x_33 = x_35;
goto block_34;
}
block_34:
{
return x_33;
}
}
}
}
}
}
block_94:
{
lean_object* x_48; uint8_t x_75; 
x_75 = lean_ctor_get_uint8(x_44, sizeof(void*)*1);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; uint8_t x_78; uint8_t x_84; 
x_76 = lean_ctor_get(x_44, 0);
x_84 = !lean_is_exclusive(x_44);
if (x_84 == 0)
{
x_77 = x_44;
x_78 = x_84;
goto block_83;
}
else
{
lean_inc(x_76);
lean_dec(x_44);
x_77 = lean_box(0);
x_78 = x_84;
goto block_83;
}
block_83:
{
uint8_t x_79; lean_object* x_80; 
x_79 = 1;
if (x_78 == 0)
{
x_80 = x_77;
goto block_81;
}
else
{
lean_object* x_82; 
x_82 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_82, 0, x_76);
x_80 = x_82;
goto block_81;
}
block_81:
{
lean_ctor_set_uint8(x_80, sizeof(void*)*1, x_79);
x_48 = x_80;
goto block_74;
}
}
}
else
{
lean_object* x_85; lean_object* x_86; uint8_t x_87; uint8_t x_93; 
x_85 = lean_ctor_get(x_44, 0);
x_93 = !lean_is_exclusive(x_44);
if (x_93 == 0)
{
x_86 = x_44;
x_87 = x_93;
goto block_92;
}
else
{
lean_inc(x_85);
lean_dec(x_44);
x_86 = lean_box(0);
x_87 = x_93;
goto block_92;
}
block_92:
{
uint8_t x_88; lean_object* x_89; 
x_88 = 0;
if (x_87 == 0)
{
x_89 = x_86;
goto block_90;
}
else
{
lean_object* x_91; 
x_91 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_91, 0, x_85);
x_89 = x_91;
goto block_90;
}
block_90:
{
lean_ctor_set_uint8(x_89, sizeof(void*)*1, x_88);
x_48 = x_89;
goto block_74;
}
}
}
block_74:
{
uint8_t x_49; 
x_49 = lean_ctor_get_uint8(x_45, sizeof(void*)*1);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; uint8_t x_52; uint8_t x_61; 
x_50 = lean_ctor_get(x_45, 0);
x_61 = !lean_is_exclusive(x_45);
if (x_61 == 0)
{
x_51 = x_45;
x_52 = x_61;
goto block_60;
}
else
{
lean_inc(x_50);
lean_dec(x_45);
x_51 = lean_box(0);
x_52 = x_61;
goto block_60;
}
block_60:
{
uint8_t x_53; lean_object* x_54; 
x_53 = 1;
if (x_52 == 0)
{
x_54 = x_51;
goto block_58;
}
else
{
lean_object* x_59; 
x_59 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_59, 0, x_50);
x_54 = x_59;
goto block_58;
}
block_58:
{
lean_object* x_55; 
lean_ctor_set_uint8(x_54, sizeof(void*)*1, x_53);
if (x_47 == 0)
{
lean_ctor_set(x_46, 1, x_54);
lean_ctor_set(x_46, 0, x_48);
x_55 = x_46;
goto block_56;
}
else
{
lean_object* x_57; 
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_48);
lean_ctor_set(x_57, 1, x_54);
x_55 = x_57;
goto block_56;
}
block_56:
{
x_3 = x_55;
goto block_43;
}
}
}
}
else
{
lean_object* x_62; lean_object* x_63; uint8_t x_64; uint8_t x_73; 
x_62 = lean_ctor_get(x_45, 0);
x_73 = !lean_is_exclusive(x_45);
if (x_73 == 0)
{
x_63 = x_45;
x_64 = x_73;
goto block_72;
}
else
{
lean_inc(x_62);
lean_dec(x_45);
x_63 = lean_box(0);
x_64 = x_73;
goto block_72;
}
block_72:
{
uint8_t x_65; lean_object* x_66; 
x_65 = 0;
if (x_64 == 0)
{
x_66 = x_63;
goto block_70;
}
else
{
lean_object* x_71; 
x_71 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_71, 0, x_62);
x_66 = x_71;
goto block_70;
}
block_70:
{
lean_object* x_67; 
lean_ctor_set_uint8(x_66, sizeof(void*)*1, x_65);
if (x_47 == 0)
{
lean_ctor_set(x_46, 1, x_66);
lean_ctor_set(x_46, 0, x_48);
x_67 = x_46;
goto block_68;
}
else
{
lean_object* x_69; 
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_48);
lean_ctor_set(x_69, 1, x_66);
x_67 = x_69;
goto block_68;
}
block_68:
{
x_3 = x_67;
goto block_43;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkIfCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_62; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_4);
x_5 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_5);
lean_dec_ref(x_2);
lean_inc_ref(x_3);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_4);
x_7 = l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0(x_1, x_6);
x_8 = lean_ctor_get(x_7, 0);
x_9 = lean_ctor_get(x_7, 1);
x_62 = !lean_is_exclusive(x_7);
if (x_62 == 0)
{
x_10 = x_7;
x_11 = x_62;
goto block_61;
}
else
{
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_7);
x_10 = lean_box(0);
x_11 = x_62;
goto block_61;
}
block_61:
{
lean_object* x_12; uint8_t x_13; lean_object* x_14; uint8_t x_15; uint8_t x_60; 
x_12 = lean_ctor_get(x_3, 0);
x_13 = lean_ctor_get_uint8(x_3, sizeof(void*)*1);
x_60 = !lean_is_exclusive(x_3);
if (x_60 == 0)
{
x_14 = x_3;
x_15 = x_60;
goto block_59;
}
else
{
lean_inc(x_12);
lean_dec(x_3);
x_14 = lean_box(0);
x_15 = x_60;
goto block_59;
}
block_59:
{
lean_object* x_16; uint8_t x_17; lean_object* x_18; uint8_t x_19; uint8_t x_58; 
x_16 = lean_ctor_get(x_5, 0);
x_17 = lean_ctor_get_uint8(x_5, sizeof(void*)*1);
x_58 = !lean_is_exclusive(x_5);
if (x_58 == 0)
{
x_18 = x_5;
x_19 = x_58;
goto block_57;
}
else
{
lean_inc(x_16);
lean_dec(x_5);
x_18 = lean_box(0);
x_19 = x_58;
goto block_57;
}
block_57:
{
lean_object* x_20; lean_object* x_21; 
if (x_13 == 0)
{
uint8_t x_49; lean_object* x_50; 
x_49 = 1;
if (x_15 == 0)
{
x_50 = x_14;
goto block_51;
}
else
{
lean_object* x_52; 
x_52 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_52, 0, x_12);
x_50 = x_52;
goto block_51;
}
block_51:
{
lean_ctor_set_uint8(x_50, sizeof(void*)*1, x_49);
x_20 = x_8;
x_21 = x_50;
goto block_48;
}
}
else
{
uint8_t x_53; lean_object* x_54; 
x_53 = 0;
if (x_15 == 0)
{
x_54 = x_14;
goto block_55;
}
else
{
lean_object* x_56; 
x_56 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_56, 0, x_12);
x_54 = x_56;
goto block_55;
}
block_55:
{
lean_ctor_set_uint8(x_54, sizeof(void*)*1, x_53);
x_20 = x_8;
x_21 = x_54;
goto block_48;
}
}
block_48:
{
lean_object* x_22; 
if (x_19 == 0)
{
x_22 = x_18;
goto block_46;
}
else
{
lean_object* x_47; 
x_47 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_47, 0, x_16);
lean_ctor_set_uint8(x_47, sizeof(void*)*1, x_17);
x_22 = x_47;
goto block_46;
}
block_46:
{
lean_object* x_23; 
if (x_11 == 0)
{
lean_ctor_set(x_10, 1, x_22);
lean_ctor_set(x_10, 0, x_21);
x_23 = x_10;
goto block_44;
}
else
{
lean_object* x_45; 
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_21);
lean_ctor_set(x_45, 1, x_22);
x_23 = x_45;
goto block_44;
}
block_44:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_43; 
x_24 = l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0(x_20, x_23);
x_25 = lean_ctor_get(x_24, 0);
x_26 = lean_ctor_get(x_24, 1);
x_43 = !lean_is_exclusive(x_24);
if (x_43 == 0)
{
x_27 = x_24;
x_28 = x_43;
goto block_42;
}
else
{
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_24);
x_27 = lean_box(0);
x_28 = x_43;
goto block_42;
}
block_42:
{
lean_object* x_29; uint8_t x_30; lean_object* x_31; uint8_t x_32; uint8_t x_41; 
x_29 = lean_ctor_get(x_9, 0);
x_30 = lean_ctor_get_uint8(x_9, sizeof(void*)*1);
x_41 = !lean_is_exclusive(x_9);
if (x_41 == 0)
{
x_31 = x_9;
x_32 = x_41;
goto block_40;
}
else
{
lean_inc(x_29);
lean_dec(x_9);
x_31 = lean_box(0);
x_32 = x_41;
goto block_40;
}
block_40:
{
lean_object* x_33; 
if (x_32 == 0)
{
x_33 = x_31;
goto block_38;
}
else
{
lean_object* x_39; 
x_39 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_39, 0, x_29);
lean_ctor_set_uint8(x_39, sizeof(void*)*1, x_30);
x_33 = x_39;
goto block_38;
}
block_38:
{
lean_object* x_34; 
if (x_28 == 0)
{
lean_ctor_set(x_27, 0, x_33);
x_34 = x_27;
goto block_36;
}
else
{
lean_object* x_37; 
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_33);
lean_ctor_set(x_37, 1, x_26);
x_34 = x_37;
goto block_36;
}
block_36:
{
lean_object* x_35; 
x_35 = l_Std_Sat_AIG_mkOrCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__3(x_25, x_34);
return x_35;
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
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkXorCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; uint8_t x_102; 
lean_inc_ref(x_2);
x_32 = l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0(x_1, x_2);
x_33 = lean_ctor_get(x_32, 0);
lean_inc_ref(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc_ref(x_34);
lean_dec_ref(x_32);
x_61 = lean_ctor_get(x_2, 0);
x_62 = lean_ctor_get(x_2, 1);
x_102 = !lean_is_exclusive(x_2);
if (x_102 == 0)
{
x_63 = x_2;
x_64 = x_102;
goto block_101;
}
else
{
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_2);
x_63 = lean_box(0);
x_64 = x_102;
goto block_101;
}
block_8:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
x_7 = l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0(x_3, x_6);
return x_7;
}
block_31:
{
uint8_t x_12; 
x_12 = lean_ctor_get_uint8(x_10, sizeof(void*)*1);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_21; 
x_13 = lean_ctor_get(x_10, 0);
x_21 = !lean_is_exclusive(x_10);
if (x_21 == 0)
{
x_14 = x_10;
x_15 = x_21;
goto block_20;
}
else
{
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_box(0);
x_15 = x_21;
goto block_20;
}
block_20:
{
uint8_t x_16; lean_object* x_17; 
x_16 = 1;
if (x_15 == 0)
{
x_17 = x_14;
goto block_18;
}
else
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_19, 0, x_13);
x_17 = x_19;
goto block_18;
}
block_18:
{
lean_ctor_set_uint8(x_17, sizeof(void*)*1, x_16);
x_3 = x_9;
x_4 = x_11;
x_5 = x_17;
goto block_8;
}
}
}
else
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_30; 
x_22 = lean_ctor_get(x_10, 0);
x_30 = !lean_is_exclusive(x_10);
if (x_30 == 0)
{
x_23 = x_10;
x_24 = x_30;
goto block_29;
}
else
{
lean_inc(x_22);
lean_dec(x_10);
x_23 = lean_box(0);
x_24 = x_30;
goto block_29;
}
block_29:
{
uint8_t x_25; lean_object* x_26; 
x_25 = 0;
if (x_24 == 0)
{
x_26 = x_23;
goto block_27;
}
else
{
lean_object* x_28; 
x_28 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_28, 0, x_22);
x_26 = x_28;
goto block_27;
}
block_27:
{
lean_ctor_set_uint8(x_26, sizeof(void*)*1, x_25);
x_3 = x_9;
x_4 = x_11;
x_5 = x_26;
goto block_8;
}
}
}
}
block_60:
{
lean_object* x_36; uint8_t x_37; 
x_36 = l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0(x_33, x_35);
x_37 = lean_ctor_get_uint8(x_34, sizeof(void*)*1);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; uint8_t x_48; 
x_38 = lean_ctor_get(x_36, 0);
lean_inc_ref(x_38);
x_39 = lean_ctor_get(x_36, 1);
lean_inc_ref(x_39);
lean_dec_ref(x_36);
x_40 = lean_ctor_get(x_34, 0);
x_48 = !lean_is_exclusive(x_34);
if (x_48 == 0)
{
x_41 = x_34;
x_42 = x_48;
goto block_47;
}
else
{
lean_inc(x_40);
lean_dec(x_34);
x_41 = lean_box(0);
x_42 = x_48;
goto block_47;
}
block_47:
{
uint8_t x_43; lean_object* x_44; 
x_43 = 1;
if (x_42 == 0)
{
x_44 = x_41;
goto block_45;
}
else
{
lean_object* x_46; 
x_46 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_46, 0, x_40);
x_44 = x_46;
goto block_45;
}
block_45:
{
lean_ctor_set_uint8(x_44, sizeof(void*)*1, x_43);
x_9 = x_38;
x_10 = x_39;
x_11 = x_44;
goto block_31;
}
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; uint8_t x_59; 
x_49 = lean_ctor_get(x_36, 0);
lean_inc_ref(x_49);
x_50 = lean_ctor_get(x_36, 1);
lean_inc_ref(x_50);
lean_dec_ref(x_36);
x_51 = lean_ctor_get(x_34, 0);
x_59 = !lean_is_exclusive(x_34);
if (x_59 == 0)
{
x_52 = x_34;
x_53 = x_59;
goto block_58;
}
else
{
lean_inc(x_51);
lean_dec(x_34);
x_52 = lean_box(0);
x_53 = x_59;
goto block_58;
}
block_58:
{
uint8_t x_54; lean_object* x_55; 
x_54 = 0;
if (x_53 == 0)
{
x_55 = x_52;
goto block_56;
}
else
{
lean_object* x_57; 
x_57 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_57, 0, x_51);
x_55 = x_57;
goto block_56;
}
block_56:
{
lean_ctor_set_uint8(x_55, sizeof(void*)*1, x_54);
x_9 = x_49;
x_10 = x_50;
x_11 = x_55;
goto block_31;
}
}
}
}
block_101:
{
lean_object* x_65; uint8_t x_66; lean_object* x_67; uint8_t x_68; uint8_t x_100; 
x_65 = lean_ctor_get(x_61, 0);
x_66 = lean_ctor_get_uint8(x_61, sizeof(void*)*1);
x_100 = !lean_is_exclusive(x_61);
if (x_100 == 0)
{
x_67 = x_61;
x_68 = x_100;
goto block_99;
}
else
{
lean_inc(x_65);
lean_dec(x_61);
x_67 = lean_box(0);
x_68 = x_100;
goto block_99;
}
block_99:
{
lean_object* x_69; uint8_t x_70; lean_object* x_71; uint8_t x_72; uint8_t x_98; 
x_69 = lean_ctor_get(x_62, 0);
x_70 = lean_ctor_get_uint8(x_62, sizeof(void*)*1);
x_98 = !lean_is_exclusive(x_62);
if (x_98 == 0)
{
x_71 = x_62;
x_72 = x_98;
goto block_97;
}
else
{
lean_inc(x_69);
lean_dec(x_62);
x_71 = lean_box(0);
x_72 = x_98;
goto block_97;
}
block_97:
{
lean_object* x_73; 
if (x_66 == 0)
{
uint8_t x_89; lean_object* x_90; 
x_89 = 1;
if (x_68 == 0)
{
x_90 = x_67;
goto block_91;
}
else
{
lean_object* x_92; 
x_92 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_92, 0, x_65);
x_90 = x_92;
goto block_91;
}
block_91:
{
lean_ctor_set_uint8(x_90, sizeof(void*)*1, x_89);
x_73 = x_90;
goto block_88;
}
}
else
{
uint8_t x_93; lean_object* x_94; 
x_93 = 0;
if (x_68 == 0)
{
x_94 = x_67;
goto block_95;
}
else
{
lean_object* x_96; 
x_96 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_96, 0, x_65);
x_94 = x_96;
goto block_95;
}
block_95:
{
lean_ctor_set_uint8(x_94, sizeof(void*)*1, x_93);
x_73 = x_94;
goto block_88;
}
}
block_88:
{
if (x_70 == 0)
{
uint8_t x_74; lean_object* x_75; 
x_74 = 1;
if (x_72 == 0)
{
x_75 = x_71;
goto block_79;
}
else
{
lean_object* x_80; 
x_80 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_80, 0, x_69);
x_75 = x_80;
goto block_79;
}
block_79:
{
lean_object* x_76; 
lean_ctor_set_uint8(x_75, sizeof(void*)*1, x_74);
if (x_64 == 0)
{
lean_ctor_set(x_63, 1, x_75);
lean_ctor_set(x_63, 0, x_73);
x_76 = x_63;
goto block_77;
}
else
{
lean_object* x_78; 
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_73);
lean_ctor_set(x_78, 1, x_75);
x_76 = x_78;
goto block_77;
}
block_77:
{
x_35 = x_76;
goto block_60;
}
}
}
else
{
uint8_t x_81; lean_object* x_82; 
x_81 = 0;
if (x_72 == 0)
{
x_82 = x_71;
goto block_86;
}
else
{
lean_object* x_87; 
x_87 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_87, 0, x_69);
x_82 = x_87;
goto block_86;
}
block_86:
{
lean_object* x_83; 
lean_ctor_set_uint8(x_82, sizeof(void*)*1, x_81);
if (x_64 == 0)
{
lean_ctor_set(x_63, 1, x_82);
lean_ctor_set(x_63, 0, x_73);
x_83 = x_63;
goto block_84;
}
else
{
lean_object* x_85; 
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_73);
lean_ctor_set(x_85, 1, x_82);
x_83 = x_85;
goto block_84;
}
block_84:
{
x_35 = x_83;
goto block_60;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec_ref(x_2);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
x_6 = l_Std_Tactic_BVDecide_BVPred_bitblast(x_1, x_5);
return x_6;
}
case 1:
{
uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get_uint8(x_2, 0);
lean_dec_ref(x_2);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set_uint8(x_9, sizeof(void*)*1, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_3);
return x_11;
}
case 2:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_12);
lean_dec_ref(x_2);
x_13 = l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go(x_1, x_12, x_3);
x_14 = lean_ctor_get(x_13, 0);
lean_inc_ref(x_14);
x_15 = lean_ctor_get(x_14, 1);
lean_inc_ref(x_15);
x_16 = lean_ctor_get_uint8(x_15, sizeof(void*)*1);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_42; 
x_17 = lean_ctor_get(x_13, 1);
x_42 = !lean_is_exclusive(x_13);
if (x_42 == 0)
{
lean_object* x_43; 
x_43 = lean_ctor_get(x_13, 0);
lean_dec(x_43);
x_18 = x_13;
x_19 = x_42;
goto block_41;
}
else
{
lean_inc(x_17);
lean_dec(x_13);
x_18 = lean_box(0);
x_19 = x_42;
goto block_41;
}
block_41:
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_39; 
x_20 = lean_ctor_get(x_14, 0);
x_39 = !lean_is_exclusive(x_14);
if (x_39 == 0)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_14, 1);
lean_dec(x_40);
x_21 = x_14;
x_22 = x_39;
goto block_38;
}
else
{
lean_inc(x_20);
lean_dec(x_14);
x_21 = lean_box(0);
x_22 = x_39;
goto block_38;
}
block_38:
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; uint8_t x_37; 
x_23 = lean_ctor_get(x_15, 0);
x_37 = !lean_is_exclusive(x_15);
if (x_37 == 0)
{
x_24 = x_15;
x_25 = x_37;
goto block_36;
}
else
{
lean_inc(x_23);
lean_dec(x_15);
x_24 = lean_box(0);
x_25 = x_37;
goto block_36;
}
block_36:
{
uint8_t x_26; lean_object* x_27; 
x_26 = 1;
if (x_25 == 0)
{
x_27 = x_24;
goto block_34;
}
else
{
lean_object* x_35; 
x_35 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_35, 0, x_23);
x_27 = x_35;
goto block_34;
}
block_34:
{
lean_object* x_28; 
lean_ctor_set_uint8(x_27, sizeof(void*)*1, x_26);
if (x_22 == 0)
{
lean_ctor_set(x_21, 1, x_27);
x_28 = x_21;
goto block_32;
}
else
{
lean_object* x_33; 
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_20);
lean_ctor_set(x_33, 1, x_27);
x_28 = x_33;
goto block_32;
}
block_32:
{
lean_object* x_29; 
if (x_19 == 0)
{
lean_ctor_set(x_18, 0, x_28);
x_29 = x_18;
goto block_30;
}
else
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_28);
lean_ctor_set(x_31, 1, x_17);
x_29 = x_31;
goto block_30;
}
block_30:
{
return x_29;
}
}
}
}
}
}
}
else
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; uint8_t x_69; 
x_44 = lean_ctor_get(x_13, 1);
x_69 = !lean_is_exclusive(x_13);
if (x_69 == 0)
{
lean_object* x_70; 
x_70 = lean_ctor_get(x_13, 0);
lean_dec(x_70);
x_45 = x_13;
x_46 = x_69;
goto block_68;
}
else
{
lean_inc(x_44);
lean_dec(x_13);
x_45 = lean_box(0);
x_46 = x_69;
goto block_68;
}
block_68:
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; uint8_t x_66; 
x_47 = lean_ctor_get(x_14, 0);
x_66 = !lean_is_exclusive(x_14);
if (x_66 == 0)
{
lean_object* x_67; 
x_67 = lean_ctor_get(x_14, 1);
lean_dec(x_67);
x_48 = x_14;
x_49 = x_66;
goto block_65;
}
else
{
lean_inc(x_47);
lean_dec(x_14);
x_48 = lean_box(0);
x_49 = x_66;
goto block_65;
}
block_65:
{
lean_object* x_50; lean_object* x_51; uint8_t x_52; uint8_t x_64; 
x_50 = lean_ctor_get(x_15, 0);
x_64 = !lean_is_exclusive(x_15);
if (x_64 == 0)
{
x_51 = x_15;
x_52 = x_64;
goto block_63;
}
else
{
lean_inc(x_50);
lean_dec(x_15);
x_51 = lean_box(0);
x_52 = x_64;
goto block_63;
}
block_63:
{
uint8_t x_53; lean_object* x_54; 
x_53 = 0;
if (x_52 == 0)
{
x_54 = x_51;
goto block_61;
}
else
{
lean_object* x_62; 
x_62 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_62, 0, x_50);
x_54 = x_62;
goto block_61;
}
block_61:
{
lean_object* x_55; 
lean_ctor_set_uint8(x_54, sizeof(void*)*1, x_53);
if (x_49 == 0)
{
lean_ctor_set(x_48, 1, x_54);
x_55 = x_48;
goto block_59;
}
else
{
lean_object* x_60; 
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_47);
lean_ctor_set(x_60, 1, x_54);
x_55 = x_60;
goto block_59;
}
block_59:
{
lean_object* x_56; 
if (x_46 == 0)
{
lean_ctor_set(x_45, 0, x_55);
x_56 = x_45;
goto block_57;
}
else
{
lean_object* x_58; 
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_55);
lean_ctor_set(x_58, 1, x_44);
x_56 = x_58;
goto block_57;
}
block_57:
{
return x_56;
}
}
}
}
}
}
}
}
case 3:
{
uint8_t x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; uint8_t x_119; 
x_71 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
x_72 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_72);
x_73 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_73);
lean_dec_ref(x_2);
x_74 = l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go(x_1, x_72, x_3);
x_75 = lean_ctor_get(x_74, 0);
lean_inc_ref(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc_ref(x_76);
lean_dec_ref(x_74);
x_77 = lean_ctor_get(x_75, 0);
lean_inc_ref(x_77);
x_78 = lean_ctor_get(x_75, 1);
lean_inc_ref(x_78);
lean_dec_ref(x_75);
x_79 = l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go(x_77, x_73, x_76);
x_80 = lean_ctor_get(x_79, 0);
x_81 = lean_ctor_get(x_79, 1);
x_119 = !lean_is_exclusive(x_79);
if (x_119 == 0)
{
x_82 = x_79;
x_83 = x_119;
goto block_118;
}
else
{
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_79);
x_82 = lean_box(0);
x_83 = x_119;
goto block_118;
}
block_118:
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; uint8_t x_117; 
x_84 = lean_ctor_get(x_80, 0);
x_85 = lean_ctor_get(x_80, 1);
x_117 = !lean_is_exclusive(x_80);
if (x_117 == 0)
{
x_86 = x_80;
x_87 = x_117;
goto block_116;
}
else
{
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_80);
x_86 = lean_box(0);
x_87 = x_117;
goto block_116;
}
block_116:
{
lean_object* x_88; uint8_t x_89; lean_object* x_90; uint8_t x_91; uint8_t x_115; 
x_88 = lean_ctor_get(x_78, 0);
x_89 = lean_ctor_get_uint8(x_78, sizeof(void*)*1);
x_115 = !lean_is_exclusive(x_78);
if (x_115 == 0)
{
x_90 = x_78;
x_91 = x_115;
goto block_114;
}
else
{
lean_inc(x_88);
lean_dec(x_78);
x_90 = lean_box(0);
x_91 = x_115;
goto block_114;
}
block_114:
{
lean_object* x_92; 
if (x_91 == 0)
{
x_92 = x_90;
goto block_112;
}
else
{
lean_object* x_113; 
x_113 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_113, 0, x_88);
lean_ctor_set_uint8(x_113, sizeof(void*)*1, x_89);
x_92 = x_113;
goto block_112;
}
block_112:
{
lean_object* x_93; 
if (x_87 == 0)
{
lean_ctor_set(x_86, 0, x_92);
x_93 = x_86;
goto block_110;
}
else
{
lean_object* x_111; 
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_92);
lean_ctor_set(x_111, 1, x_85);
x_93 = x_111;
goto block_110;
}
block_110:
{
switch (x_71) {
case 0:
{
lean_object* x_94; lean_object* x_95; 
x_94 = l_Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0(x_84, x_93);
if (x_83 == 0)
{
lean_ctor_set(x_82, 0, x_94);
x_95 = x_82;
goto block_96;
}
else
{
lean_object* x_97; 
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_94);
lean_ctor_set(x_97, 1, x_81);
x_95 = x_97;
goto block_96;
}
block_96:
{
return x_95;
}
}
case 1:
{
lean_object* x_98; lean_object* x_99; 
x_98 = l_Std_Sat_AIG_mkXorCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__1(x_84, x_93);
if (x_83 == 0)
{
lean_ctor_set(x_82, 0, x_98);
x_99 = x_82;
goto block_100;
}
else
{
lean_object* x_101; 
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_98);
lean_ctor_set(x_101, 1, x_81);
x_99 = x_101;
goto block_100;
}
block_100:
{
return x_99;
}
}
case 2:
{
lean_object* x_102; lean_object* x_103; 
x_102 = l_Std_Sat_AIG_mkBEqCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__2(x_84, x_93);
if (x_83 == 0)
{
lean_ctor_set(x_82, 0, x_102);
x_103 = x_82;
goto block_104;
}
else
{
lean_object* x_105; 
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_102);
lean_ctor_set(x_105, 1, x_81);
x_103 = x_105;
goto block_104;
}
block_104:
{
return x_103;
}
}
default: 
{
lean_object* x_106; lean_object* x_107; 
x_106 = l_Std_Sat_AIG_mkOrCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__3(x_84, x_93);
if (x_83 == 0)
{
lean_ctor_set(x_82, 0, x_106);
x_107 = x_82;
goto block_108;
}
else
{
lean_object* x_109; 
x_109 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_109, 0, x_106);
lean_ctor_set(x_109, 1, x_81);
x_107 = x_109;
goto block_108;
}
block_108:
{
return x_107;
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
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; uint8_t x_124; uint8_t x_170; 
x_120 = lean_ctor_get(x_2, 0);
x_121 = lean_ctor_get(x_2, 1);
x_122 = lean_ctor_get(x_2, 2);
x_170 = !lean_is_exclusive(x_2);
if (x_170 == 0)
{
x_123 = x_2;
x_124 = x_170;
goto block_169;
}
else
{
lean_inc(x_122);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_2);
x_123 = lean_box(0);
x_124 = x_170;
goto block_169;
}
block_169:
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; uint8_t x_139; uint8_t x_168; 
x_125 = l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go(x_1, x_120, x_3);
x_126 = lean_ctor_get(x_125, 0);
lean_inc_ref(x_126);
x_127 = lean_ctor_get(x_125, 1);
lean_inc_ref(x_127);
lean_dec_ref(x_125);
x_128 = lean_ctor_get(x_126, 0);
lean_inc_ref(x_128);
x_129 = lean_ctor_get(x_126, 1);
lean_inc_ref(x_129);
lean_dec_ref(x_126);
x_130 = l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go(x_128, x_121, x_127);
x_131 = lean_ctor_get(x_130, 0);
lean_inc_ref(x_131);
x_132 = lean_ctor_get(x_130, 1);
lean_inc_ref(x_132);
lean_dec_ref(x_130);
x_133 = lean_ctor_get(x_131, 0);
lean_inc_ref(x_133);
x_134 = lean_ctor_get(x_131, 1);
lean_inc_ref(x_134);
lean_dec_ref(x_131);
x_135 = l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go(x_133, x_122, x_132);
x_136 = lean_ctor_get(x_135, 0);
x_137 = lean_ctor_get(x_135, 1);
x_168 = !lean_is_exclusive(x_135);
if (x_168 == 0)
{
x_138 = x_135;
x_139 = x_168;
goto block_167;
}
else
{
lean_inc(x_137);
lean_inc(x_136);
lean_dec(x_135);
x_138 = lean_box(0);
x_139 = x_168;
goto block_167;
}
block_167:
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; uint8_t x_143; lean_object* x_144; uint8_t x_145; uint8_t x_166; 
x_140 = lean_ctor_get(x_136, 0);
lean_inc_ref(x_140);
x_141 = lean_ctor_get(x_136, 1);
lean_inc_ref(x_141);
lean_dec_ref(x_136);
x_142 = lean_ctor_get(x_129, 0);
x_143 = lean_ctor_get_uint8(x_129, sizeof(void*)*1);
x_166 = !lean_is_exclusive(x_129);
if (x_166 == 0)
{
x_144 = x_129;
x_145 = x_166;
goto block_165;
}
else
{
lean_inc(x_142);
lean_dec(x_129);
x_144 = lean_box(0);
x_145 = x_166;
goto block_165;
}
block_165:
{
lean_object* x_146; uint8_t x_147; lean_object* x_148; uint8_t x_149; uint8_t x_164; 
x_146 = lean_ctor_get(x_134, 0);
x_147 = lean_ctor_get_uint8(x_134, sizeof(void*)*1);
x_164 = !lean_is_exclusive(x_134);
if (x_164 == 0)
{
x_148 = x_134;
x_149 = x_164;
goto block_163;
}
else
{
lean_inc(x_146);
lean_dec(x_134);
x_148 = lean_box(0);
x_149 = x_164;
goto block_163;
}
block_163:
{
lean_object* x_150; 
if (x_149 == 0)
{
lean_ctor_set(x_148, 0, x_142);
x_150 = x_148;
goto block_161;
}
else
{
lean_object* x_162; 
x_162 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_162, 0, x_142);
x_150 = x_162;
goto block_161;
}
block_161:
{
lean_object* x_151; 
lean_ctor_set_uint8(x_150, sizeof(void*)*1, x_143);
if (x_145 == 0)
{
lean_ctor_set(x_144, 0, x_146);
x_151 = x_144;
goto block_159;
}
else
{
lean_object* x_160; 
x_160 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_160, 0, x_146);
x_151 = x_160;
goto block_159;
}
block_159:
{
lean_object* x_152; 
lean_ctor_set_uint8(x_151, sizeof(void*)*1, x_147);
if (x_124 == 0)
{
lean_ctor_set_tag(x_123, 0);
lean_ctor_set(x_123, 2, x_141);
lean_ctor_set(x_123, 1, x_151);
lean_ctor_set(x_123, 0, x_150);
x_152 = x_123;
goto block_157;
}
else
{
lean_object* x_158; 
x_158 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_158, 0, x_150);
lean_ctor_set(x_158, 1, x_151);
lean_ctor_set(x_158, 2, x_141);
x_152 = x_158;
goto block_157;
}
block_157:
{
lean_object* x_153; lean_object* x_154; 
x_153 = l_Std_Sat_AIG_mkIfCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__4(x_140, x_152);
if (x_139 == 0)
{
lean_ctor_set(x_138, 0, x_153);
x_154 = x_138;
goto block_155;
}
else
{
lean_object* x_156; 
x_156 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_156, 0, x_153);
lean_ctor_set(x_156, 1, x_137);
x_154 = x_156;
goto block_155;
}
block_155:
{
return x_154;
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__1___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__1(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__1_spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__1_spec__7___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__10___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__10(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__11(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__11___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__12(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__12___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__11_spec__12(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__11_spec__12___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkGateCached_go___at___00Std_Sat_AIG_mkGateCached___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg(x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_unsigned_to_nat(16u);
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__1, &l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__1_once, _init_l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__1);
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__2, &l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__2_once, _init_l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__2);
x_2 = ((lean_object*)(l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__0));
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_obj_once(&l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__3, &l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__3_once, _init_l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__3);
return x_1;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_unsigned_to_nat(16u);
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___closed__0, &l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___closed__0_once, _init_l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___closed__0);
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Std_Sat_AIG_empty___at___00Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0;
x_3 = lean_obj_once(&l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___closed__1, &l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___closed__1_once, _init_l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___closed__1);
x_4 = l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go(x_2, x_1, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_5);
lean_dec_ref(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_match__5_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec_ref(x_1);
x_8 = lean_apply_1(x_2, x_7);
return x_8;
}
case 1:
{
uint8_t x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_9 = lean_ctor_get_uint8(x_1, 0);
lean_dec_ref(x_1);
x_10 = lean_box(x_9);
x_11 = lean_apply_1(x_3, x_10);
return x_11;
}
case 2:
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_12 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_12);
lean_dec_ref(x_1);
x_13 = lean_apply_1(x_4, x_12);
return x_13;
}
case 3:
{
uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_14 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
x_15 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_15);
x_16 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_16);
lean_dec_ref(x_1);
x_17 = lean_box(x_14);
x_18 = lean_apply_3(x_6, x_17, x_15, x_16);
return x_18;
}
default: 
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_19 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_19);
x_20 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_20);
x_21 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_21);
lean_dec_ref(x_1);
x_22 = lean_apply_3(x_5, x_19, x_20, x_21);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_match__5_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_match__5_splitter___redArg(x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_4);
lean_dec_ref(x_1);
x_5 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_6);
lean_dec_ref(x_3);
x_7 = lean_apply_4(x_2, x_5, x_6, lean_box(0), x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_match__1_splitter___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_match__1_splitter(x_1, x_2, x_3, x_4);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_match__3_splitter___redArg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_6 = lean_box(0);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
case 1:
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_8 = lean_box(0);
x_9 = lean_apply_1(x_3, x_8);
return x_9;
}
case 2:
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_10 = lean_box(0);
x_11 = lean_apply_1(x_4, x_10);
return x_11;
}
default: 
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_12 = lean_box(0);
x_13 = lean_apply_1(x_5, x_12);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_match__3_splitter___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
x_7 = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_match__3_splitter___redArg(x_6, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_match__3_splitter(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_match__3_splitter___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_match__3_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_2);
x_8 = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_match__3_splitter(x_1, x_7, x_3, x_4, x_5, x_6);
return x_8;
}
}
lean_object* runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Pred(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Pred(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin)
;
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
res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Pred(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure(builtin);
}
#ifdef __cplusplus
}
#endif
