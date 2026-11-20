// Lean compiler output
// Module: Lean.Meta.Tactic.BVDecide.EPR.Basic
// Imports: public import Lean.Meta.Sym.SymM public import Lean.Meta.Tactic.BVDecide.Normalize.Hyp
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
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Expr_getForallBodyMaxDepth(lean_object*, lean_object*);
lean_object* lean_expr_instantiate_rev(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp_default;
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_string_length(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Array_instInhabited___redArg();
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedSortId_default;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedSortId;
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Meta_Tactic_BVDecide_EPR_instReprSortId_repr_spec__0(lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_EPR_instReprSortId_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "{ "};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_instReprSortId_repr___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_EPR_instReprSortId_repr___redArg___closed__0_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_EPR_instReprSortId_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "idx"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_instReprSortId_repr___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_EPR_instReprSortId_repr___redArg___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_EPR_instReprSortId_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_EPR_instReprSortId_repr___redArg___closed__1_value)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_instReprSortId_repr___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_EPR_instReprSortId_repr___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_EPR_instReprSortId_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_EPR_instReprSortId_repr___redArg___closed__2_value)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_instReprSortId_repr___redArg___closed__3 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_EPR_instReprSortId_repr___redArg___closed__3_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_EPR_instReprSortId_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_instReprSortId_repr___redArg___closed__4 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_EPR_instReprSortId_repr___redArg___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_EPR_instReprSortId_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_EPR_instReprSortId_repr___redArg___closed__4_value)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_instReprSortId_repr___redArg___closed__5 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_EPR_instReprSortId_repr___redArg___closed__5_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_EPR_instReprSortId_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_EPR_instReprSortId_repr___redArg___closed__3_value),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_EPR_instReprSortId_repr___redArg___closed__5_value)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_instReprSortId_repr___redArg___closed__6 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_EPR_instReprSortId_repr___redArg___closed__6_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_EPR_instReprSortId_repr___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_instReprSortId_repr___redArg___closed__7;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_EPR_instReprSortId_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " }"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_instReprSortId_repr___redArg___closed__8 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_EPR_instReprSortId_repr___redArg___closed__8_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_EPR_instReprSortId_repr___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_instReprSortId_repr___redArg___closed__9;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_EPR_instReprSortId_repr___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_instReprSortId_repr___redArg___closed__10;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_EPR_instReprSortId_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_EPR_instReprSortId_repr___redArg___closed__0_value)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_instReprSortId_repr___redArg___closed__11 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_EPR_instReprSortId_repr___redArg___closed__11_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_EPR_instReprSortId_repr___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_EPR_instReprSortId_repr___redArg___closed__8_value)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_instReprSortId_repr___redArg___closed__12 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_EPR_instReprSortId_repr___redArg___closed__12_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_instReprSortId_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_instReprSortId_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_instReprSortId_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_EPR_instReprSortId___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_EPR_instReprSortId_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_instReprSortId___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_EPR_instReprSortId___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_instReprSortId = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_EPR_instReprSortId___closed__0_value;
LEAN_EXPORT uint64_t l_Lean_Meta_Tactic_BVDecide_EPR_instHashableSortId_hash(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_instHashableSortId_hash___boxed(lean_object*);
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_EPR_instHashableSortId___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_EPR_instHashableSortId_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_instHashableSortId___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_EPR_instHashableSortId___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_instHashableSortId = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_EPR_instHashableSortId___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_BVDecide_EPR_instDecidableEqSortId_decEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_instDecidableEqSortId_decEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_BVDecide_EPR_instDecidableEqSortId(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_instDecidableEqSortId___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedSortInfo_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "_inhabitedExprDummy"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedSortInfo_default___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedSortInfo_default___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedSortInfo_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedSortInfo_default___closed__0_value),LEAN_SCALAR_PTR_LITERAL(37, 247, 56, 151, 29, 116, 116, 243)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedSortInfo_default___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedSortInfo_default___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedSortInfo_default___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedSortInfo_default___closed__2;
static const lean_array_object l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedSortInfo_default___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedSortInfo_default___closed__3 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedSortInfo_default___closed__3_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedSortInfo_default___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedSortInfo_default___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedSortInfo_default;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedSortInfo;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_SortInfo_card(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_SortInfo_card___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_SortInfo_cardExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_SortInfo_cardExpr___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_SortInfo_default(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_SortInfo_default___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_PredEncoding_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_PredEncoding_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_PredEncoding_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_PredEncoding_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_PredEncoding_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_PredEncoding_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_PredEncoding_prop_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_PredEncoding_prop_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_PredEncoding_prop_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_PredEncoding_prop_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_PredEncoding_bool_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_PredEncoding_bool_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_PredEncoding_bool_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_PredEncoding_bool_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedPredEncoding_default;
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedPredEncoding;
LEAN_EXPORT uint64_t l_Lean_Meta_Tactic_BVDecide_EPR_instHashablePredEncoding_hash(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_instHashablePredEncoding_hash___boxed(lean_object*);
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_EPR_instHashablePredEncoding___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_EPR_instHashablePredEncoding_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_instHashablePredEncoding___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_EPR_instHashablePredEncoding___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_instHashablePredEncoding = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_EPR_instHashablePredEncoding___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_BVDecide_EPR_PredEncoding_ofNat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_PredEncoding_ofNat___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_BVDecide_EPR_instDecidableEqPredEncoding(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_instDecidableEqPredEncoding___boxed(lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedPredInfo_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedPredInfo_default___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedPredInfo_default___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedPredInfo_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedPredInfo_default___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedPredInfo_default___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedPredInfo_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedPredInfo_default = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedPredInfo_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedPredInfo = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedPredInfo_default___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedQuantifiedFact_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedQuantifiedFact_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedQuantifiedFact_default;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedQuantifiedFact;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_QuantifiedFact_instantiateType(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_QuantifiedFact_instantiateType___boxed(lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00Lean_Meta_Tactic_BVDecide_EPR_QuantifiedFact_instantiateParts_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_Tactic_BVDecide_EPR_QuantifiedFact_instantiateParts_spec__1___closed__0 = (const lean_object*)&l_panic___at___00Lean_Meta_Tactic_BVDecide_EPR_QuantifiedFact_instantiateParts_spec__1___closed__0_value;
static const lean_closure_object l_panic___at___00Lean_Meta_Tactic_BVDecide_EPR_QuantifiedFact_instantiateParts_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_Tactic_BVDecide_EPR_QuantifiedFact_instantiateParts_spec__1___closed__1 = (const lean_object*)&l_panic___at___00Lean_Meta_Tactic_BVDecide_EPR_QuantifiedFact_instantiateParts_spec__1___closed__1_value;
static const lean_closure_object l_panic___at___00Lean_Meta_Tactic_BVDecide_EPR_QuantifiedFact_instantiateParts_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_Tactic_BVDecide_EPR_QuantifiedFact_instantiateParts_spec__1___closed__2 = (const lean_object*)&l_panic___at___00Lean_Meta_Tactic_BVDecide_EPR_QuantifiedFact_instantiateParts_spec__1___closed__2_value;
static const lean_closure_object l_panic___at___00Lean_Meta_Tactic_BVDecide_EPR_QuantifiedFact_instantiateParts_spec__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_Tactic_BVDecide_EPR_QuantifiedFact_instantiateParts_spec__1___closed__3 = (const lean_object*)&l_panic___at___00Lean_Meta_Tactic_BVDecide_EPR_QuantifiedFact_instantiateParts_spec__1___closed__3_value;
static const lean_closure_object l_panic___at___00Lean_Meta_Tactic_BVDecide_EPR_QuantifiedFact_instantiateParts_spec__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_Tactic_BVDecide_EPR_QuantifiedFact_instantiateParts_spec__1___closed__4 = (const lean_object*)&l_panic___at___00Lean_Meta_Tactic_BVDecide_EPR_QuantifiedFact_instantiateParts_spec__1___closed__4_value;
static const lean_closure_object l_panic___at___00Lean_Meta_Tactic_BVDecide_EPR_QuantifiedFact_instantiateParts_spec__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_Tactic_BVDecide_EPR_QuantifiedFact_instantiateParts_spec__1___closed__5 = (const lean_object*)&l_panic___at___00Lean_Meta_Tactic_BVDecide_EPR_QuantifiedFact_instantiateParts_spec__1___closed__5_value;
static const lean_closure_object l_panic___at___00Lean_Meta_Tactic_BVDecide_EPR_QuantifiedFact_instantiateParts_spec__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_Tactic_BVDecide_EPR_QuantifiedFact_instantiateParts_spec__1___closed__6 = (const lean_object*)&l_panic___at___00Lean_Meta_Tactic_BVDecide_EPR_QuantifiedFact_instantiateParts_spec__1___closed__6_value;
static lean_once_cell_t l_panic___at___00Lean_Meta_Tactic_BVDecide_EPR_QuantifiedFact_instantiateParts_spec__1___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_Meta_Tactic_BVDecide_EPR_QuantifiedFact_instantiateParts_spec__1___closed__7;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Tactic_BVDecide_EPR_QuantifiedFact_instantiateParts_spec__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_EPR_QuantifiedFact_instantiateParts_spec__0___redArg(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_EPR_QuantifiedFact_instantiateParts_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_EPR_QuantifiedFact_instantiateParts___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "Lean.Meta.Tactic.BVDecide.EPR.Basic"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_QuantifiedFact_instantiateParts___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_EPR_QuantifiedFact_instantiateParts___closed__0_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_EPR_QuantifiedFact_instantiateParts___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 62, .m_capacity = 62, .m_length = 61, .m_data = "Lean.Meta.Tactic.BVDecide.EPR.QuantifiedFact.instantiateParts"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_QuantifiedFact_instantiateParts___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_EPR_QuantifiedFact_instantiateParts___closed__1_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_EPR_QuantifiedFact_instantiateParts___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "assertion violation: !type.hasLooseBVars\n  "};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_QuantifiedFact_instantiateParts___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_EPR_QuantifiedFact_instantiateParts___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_EPR_QuantifiedFact_instantiateParts___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_QuantifiedFact_instantiateParts___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_QuantifiedFact_instantiateParts(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_QuantifiedFact_instantiateParts___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_EPR_QuantifiedFact_instantiateParts_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_EPR_QuantifiedFact_instantiateParts_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_EPR_QuantifiedFact_instantiate___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "inst"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_QuantifiedFact_instantiate___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_EPR_QuantifiedFact_instantiate___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_EPR_QuantifiedFact_instantiate___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_EPR_QuantifiedFact_instantiate___closed__0_value),LEAN_SCALAR_PTR_LITERAL(170, 188, 240, 205, 110, 63, 170, 91)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_QuantifiedFact_instantiate___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_EPR_QuantifiedFact_instantiate___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_QuantifiedFact_instantiate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_QuantifiedFact_instantiate___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedEprProblem_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedEprProblem_default___closed__0;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedEprProblem_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedEprProblem_default___closed__1;
static const lean_array_object l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedEprProblem_default___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedEprProblem_default___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedEprProblem_default___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedEprProblem_default___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedEprProblem_default___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedEprProblem_default;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedEprProblem;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedBvSortInfo_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedBvSortInfo_default___closed__0;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedBvSortInfo_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedBvSortInfo_default___closed__1;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedBvSortInfo_default___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedBvSortInfo_default___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedBvSortInfo_default;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedBvSortInfo;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_EPR_BvSortInfo_bvType___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "BitVec"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_BvSortInfo_bvType___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_EPR_BvSortInfo_bvType___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_EPR_BvSortInfo_bvType___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_EPR_BvSortInfo_bvType___closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_BvSortInfo_bvType___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_EPR_BvSortInfo_bvType___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_EPR_BvSortInfo_bvType___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_BvSortInfo_bvType___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_BvSortInfo_bvType(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_BvSortInfo_appToBv(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedBvPredInfo_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedBvPredInfo_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedBvPredInfo_default;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedBvPredInfo;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedEprBvProblem_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedEprBvProblem_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedEprBvProblem_default;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedEprBvProblem;
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedSortId_default(void){
_start:
{
lean_object* v___x_1_; 
v___x_1_ = lean_unsigned_to_nat(0u);
return v___x_1_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedSortId(void){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Meta_Tactic_BVDecide_EPR_instReprSortId_repr_spec__0(lean_object* v_a_3_){
_start:
{
lean_object* v___x_4_; 
v___x_4_ = lean_nat_to_int(v_a_3_);
return v___x_4_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_EPR_instReprSortId_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_18_; lean_object* v___x_19_; 
v___x_18_ = lean_unsigned_to_nat(7u);
v___x_19_ = lean_nat_to_int(v___x_18_);
return v___x_19_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_EPR_instReprSortId_repr___redArg___closed__9(void){
_start:
{
lean_object* v___x_21_; lean_object* v___x_22_; 
v___x_21_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_EPR_instReprSortId_repr___redArg___closed__0));
v___x_22_ = lean_string_length(v___x_21_);
return v___x_22_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_EPR_instReprSortId_repr___redArg___closed__10(void){
_start:
{
lean_object* v___x_23_; lean_object* v___x_24_; 
v___x_23_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_EPR_instReprSortId_repr___redArg___closed__9, &l_Lean_Meta_Tactic_BVDecide_EPR_instReprSortId_repr___redArg___closed__9_once, _init_l_Lean_Meta_Tactic_BVDecide_EPR_instReprSortId_repr___redArg___closed__9);
v___x_24_ = lean_nat_to_int(v___x_23_);
return v___x_24_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_instReprSortId_repr___redArg(lean_object* v_x_29_){
_start:
{
lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; uint8_t v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; 
v___x_30_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_EPR_instReprSortId_repr___redArg___closed__6));
v___x_31_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_EPR_instReprSortId_repr___redArg___closed__7, &l_Lean_Meta_Tactic_BVDecide_EPR_instReprSortId_repr___redArg___closed__7_once, _init_l_Lean_Meta_Tactic_BVDecide_EPR_instReprSortId_repr___redArg___closed__7);
v___x_32_ = l_Nat_reprFast(v_x_29_);
v___x_33_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_33_, 0, v___x_32_);
v___x_34_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_34_, 0, v___x_31_);
lean_ctor_set(v___x_34_, 1, v___x_33_);
v___x_35_ = 0;
v___x_36_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_36_, 0, v___x_34_);
lean_ctor_set_uint8(v___x_36_, sizeof(void*)*1, v___x_35_);
v___x_37_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_37_, 0, v___x_30_);
lean_ctor_set(v___x_37_, 1, v___x_36_);
v___x_38_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_EPR_instReprSortId_repr___redArg___closed__10, &l_Lean_Meta_Tactic_BVDecide_EPR_instReprSortId_repr___redArg___closed__10_once, _init_l_Lean_Meta_Tactic_BVDecide_EPR_instReprSortId_repr___redArg___closed__10);
v___x_39_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_EPR_instReprSortId_repr___redArg___closed__11));
v___x_40_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_40_, 0, v___x_39_);
lean_ctor_set(v___x_40_, 1, v___x_37_);
v___x_41_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_EPR_instReprSortId_repr___redArg___closed__12));
v___x_42_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_42_, 0, v___x_40_);
lean_ctor_set(v___x_42_, 1, v___x_41_);
v___x_43_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_43_, 0, v___x_38_);
lean_ctor_set(v___x_43_, 1, v___x_42_);
v___x_44_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_44_, 0, v___x_43_);
lean_ctor_set_uint8(v___x_44_, sizeof(void*)*1, v___x_35_);
return v___x_44_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_instReprSortId_repr(lean_object* v_x_45_, lean_object* v_prec_46_){
_start:
{
lean_object* v___x_47_; 
v___x_47_ = l_Lean_Meta_Tactic_BVDecide_EPR_instReprSortId_repr___redArg(v_x_45_);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_instReprSortId_repr___boxed(lean_object* v_x_48_, lean_object* v_prec_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = l_Lean_Meta_Tactic_BVDecide_EPR_instReprSortId_repr(v_x_48_, v_prec_49_);
lean_dec(v_prec_49_);
return v_res_50_;
}
}
LEAN_EXPORT uint64_t l_Lean_Meta_Tactic_BVDecide_EPR_instHashableSortId_hash(lean_object* v_x_53_){
_start:
{
uint64_t v___x_54_; uint64_t v___x_55_; uint64_t v___x_56_; 
v___x_54_ = 0ULL;
v___x_55_ = lean_uint64_of_nat(v_x_53_);
v___x_56_ = lean_uint64_mix_hash(v___x_54_, v___x_55_);
return v___x_56_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_instHashableSortId_hash___boxed(lean_object* v_x_57_){
_start:
{
uint64_t v_res_58_; lean_object* v_r_59_; 
v_res_58_ = l_Lean_Meta_Tactic_BVDecide_EPR_instHashableSortId_hash(v_x_57_);
lean_dec(v_x_57_);
v_r_59_ = lean_box_uint64(v_res_58_);
return v_r_59_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_BVDecide_EPR_instDecidableEqSortId_decEq(lean_object* v_x_62_, lean_object* v_x_63_){
_start:
{
uint8_t v___x_64_; 
v___x_64_ = lean_nat_dec_eq(v_x_62_, v_x_63_);
return v___x_64_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_instDecidableEqSortId_decEq___boxed(lean_object* v_x_65_, lean_object* v_x_66_){
_start:
{
uint8_t v_res_67_; lean_object* v_r_68_; 
v_res_67_ = l_Lean_Meta_Tactic_BVDecide_EPR_instDecidableEqSortId_decEq(v_x_65_, v_x_66_);
lean_dec(v_x_66_);
lean_dec(v_x_65_);
v_r_68_ = lean_box(v_res_67_);
return v_r_68_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_BVDecide_EPR_instDecidableEqSortId(lean_object* v_x_69_, lean_object* v_x_70_){
_start:
{
uint8_t v___x_71_; 
v___x_71_ = lean_nat_dec_eq(v_x_69_, v_x_70_);
return v___x_71_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_instDecidableEqSortId___boxed(lean_object* v_x_72_, lean_object* v_x_73_){
_start:
{
uint8_t v_res_74_; lean_object* v_r_75_; 
v_res_74_ = l_Lean_Meta_Tactic_BVDecide_EPR_instDecidableEqSortId(v_x_72_, v_x_73_);
lean_dec(v_x_73_);
lean_dec(v_x_72_);
v_r_75_ = lean_box(v_res_74_);
return v_r_75_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedSortInfo_default___closed__2(void){
_start:
{
lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; 
v___x_79_ = lean_box(0);
v___x_80_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedSortInfo_default___closed__1));
v___x_81_ = l_Lean_Expr_const___override(v___x_80_, v___x_79_);
return v___x_81_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedSortInfo_default___closed__4(void){
_start:
{
lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; 
v___x_84_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedSortInfo_default___closed__3));
v___x_85_ = lean_box(0);
v___x_86_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedSortInfo_default___closed__2, &l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedSortInfo_default___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedSortInfo_default___closed__2);
v___x_87_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_87_, 0, v___x_86_);
lean_ctor_set(v___x_87_, 1, v___x_85_);
lean_ctor_set(v___x_87_, 2, v___x_84_);
return v___x_87_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedSortInfo_default(void){
_start:
{
lean_object* v___x_88_; 
v___x_88_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedSortInfo_default___closed__4, &l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedSortInfo_default___closed__4_once, _init_l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedSortInfo_default___closed__4);
return v___x_88_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedSortInfo(void){
_start:
{
lean_object* v___x_89_; 
v___x_89_ = l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedSortInfo_default;
return v___x_89_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_SortInfo_card(lean_object* v_info_90_){
_start:
{
lean_object* v_elements_91_; lean_object* v___x_92_; 
v_elements_91_ = lean_ctor_get(v_info_90_, 2);
v___x_92_ = lean_array_get_size(v_elements_91_);
return v___x_92_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_SortInfo_card___boxed(lean_object* v_info_93_){
_start:
{
lean_object* v_res_94_; 
v_res_94_ = l_Lean_Meta_Tactic_BVDecide_EPR_SortInfo_card(v_info_93_);
lean_dec_ref(v_info_93_);
return v_res_94_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_SortInfo_cardExpr(lean_object* v_info_95_){
_start:
{
lean_object* v_elements_96_; lean_object* v___x_97_; lean_object* v___x_98_; 
v_elements_96_ = lean_ctor_get(v_info_95_, 2);
v___x_97_ = lean_array_get_size(v_elements_96_);
v___x_98_ = l_Lean_mkNatLit(v___x_97_);
return v___x_98_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_SortInfo_cardExpr___boxed(lean_object* v_info_99_){
_start:
{
lean_object* v_res_100_; 
v_res_100_ = l_Lean_Meta_Tactic_BVDecide_EPR_SortInfo_cardExpr(v_info_99_);
lean_dec_ref(v_info_99_);
return v_res_100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_SortInfo_default(lean_object* v_info_101_){
_start:
{
lean_object* v_elements_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; 
v_elements_102_ = lean_ctor_get(v_info_101_, 2);
v___x_103_ = l_Lean_instInhabitedExpr;
v___x_104_ = lean_unsigned_to_nat(0u);
v___x_105_ = lean_array_get_borrowed(v___x_103_, v_elements_102_, v___x_104_);
lean_inc(v___x_105_);
return v___x_105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_SortInfo_default___boxed(lean_object* v_info_106_){
_start:
{
lean_object* v_res_107_; 
v_res_107_ = l_Lean_Meta_Tactic_BVDecide_EPR_SortInfo_default(v_info_106_);
lean_dec_ref(v_info_106_);
return v_res_107_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_PredEncoding_ctorIdx___impl(uint8_t v_x_108_){
_start:
{
lean_object* v___x_109_; lean_object* v___x_110_; 
v___x_109_ = lean_box(v_x_108_);
v___x_110_ = lean_obj_tag_nat(v___x_109_);
lean_dec(v___x_109_);
return v___x_110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_PredEncoding_ctorIdx___impl___boxed(lean_object* v_x_111_){
_start:
{
uint8_t v_x_4__boxed_112_; lean_object* v_res_113_; 
v_x_4__boxed_112_ = lean_unbox(v_x_111_);
v_res_113_ = l_Lean_Meta_Tactic_BVDecide_EPR_PredEncoding_ctorIdx___impl(v_x_4__boxed_112_);
return v_res_113_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_PredEncoding_ctorElim___redArg(lean_object* v_k_114_){
_start:
{
lean_inc(v_k_114_);
return v_k_114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_PredEncoding_ctorElim___redArg___boxed(lean_object* v_k_115_){
_start:
{
lean_object* v_res_116_; 
v_res_116_ = l_Lean_Meta_Tactic_BVDecide_EPR_PredEncoding_ctorElim___redArg(v_k_115_);
lean_dec(v_k_115_);
return v_res_116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_PredEncoding_ctorElim(lean_object* v_motive_117_, lean_object* v_ctorIdx_118_, uint8_t v_t_119_, lean_object* v_h_120_, lean_object* v_k_121_){
_start:
{
lean_inc(v_k_121_);
return v_k_121_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_PredEncoding_ctorElim___boxed(lean_object* v_motive_122_, lean_object* v_ctorIdx_123_, lean_object* v_t_124_, lean_object* v_h_125_, lean_object* v_k_126_){
_start:
{
uint8_t v_t_boxed_127_; lean_object* v_res_128_; 
v_t_boxed_127_ = lean_unbox(v_t_124_);
v_res_128_ = l_Lean_Meta_Tactic_BVDecide_EPR_PredEncoding_ctorElim(v_motive_122_, v_ctorIdx_123_, v_t_boxed_127_, v_h_125_, v_k_126_);
lean_dec(v_k_126_);
lean_dec(v_ctorIdx_123_);
return v_res_128_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_PredEncoding_prop_elim___redArg(lean_object* v_prop_129_){
_start:
{
lean_inc(v_prop_129_);
return v_prop_129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_PredEncoding_prop_elim___redArg___boxed(lean_object* v_prop_130_){
_start:
{
lean_object* v_res_131_; 
v_res_131_ = l_Lean_Meta_Tactic_BVDecide_EPR_PredEncoding_prop_elim___redArg(v_prop_130_);
lean_dec(v_prop_130_);
return v_res_131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_PredEncoding_prop_elim(lean_object* v_motive_132_, uint8_t v_t_133_, lean_object* v_h_134_, lean_object* v_prop_135_){
_start:
{
lean_inc(v_prop_135_);
return v_prop_135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_PredEncoding_prop_elim___boxed(lean_object* v_motive_136_, lean_object* v_t_137_, lean_object* v_h_138_, lean_object* v_prop_139_){
_start:
{
uint8_t v_t_boxed_140_; lean_object* v_res_141_; 
v_t_boxed_140_ = lean_unbox(v_t_137_);
v_res_141_ = l_Lean_Meta_Tactic_BVDecide_EPR_PredEncoding_prop_elim(v_motive_136_, v_t_boxed_140_, v_h_138_, v_prop_139_);
lean_dec(v_prop_139_);
return v_res_141_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_PredEncoding_bool_elim___redArg(lean_object* v_bool_142_){
_start:
{
lean_inc(v_bool_142_);
return v_bool_142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_PredEncoding_bool_elim___redArg___boxed(lean_object* v_bool_143_){
_start:
{
lean_object* v_res_144_; 
v_res_144_ = l_Lean_Meta_Tactic_BVDecide_EPR_PredEncoding_bool_elim___redArg(v_bool_143_);
lean_dec(v_bool_143_);
return v_res_144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_PredEncoding_bool_elim(lean_object* v_motive_145_, uint8_t v_t_146_, lean_object* v_h_147_, lean_object* v_bool_148_){
_start:
{
lean_inc(v_bool_148_);
return v_bool_148_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_PredEncoding_bool_elim___boxed(lean_object* v_motive_149_, lean_object* v_t_150_, lean_object* v_h_151_, lean_object* v_bool_152_){
_start:
{
uint8_t v_t_boxed_153_; lean_object* v_res_154_; 
v_t_boxed_153_ = lean_unbox(v_t_150_);
v_res_154_ = l_Lean_Meta_Tactic_BVDecide_EPR_PredEncoding_bool_elim(v_motive_149_, v_t_boxed_153_, v_h_151_, v_bool_152_);
lean_dec(v_bool_152_);
return v_res_154_;
}
}
static uint8_t _init_l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedPredEncoding_default(void){
_start:
{
uint8_t v___x_155_; 
v___x_155_ = 0;
return v___x_155_;
}
}
static uint8_t _init_l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedPredEncoding(void){
_start:
{
uint8_t v___x_156_; 
v___x_156_ = 0;
return v___x_156_;
}
}
LEAN_EXPORT uint64_t l_Lean_Meta_Tactic_BVDecide_EPR_instHashablePredEncoding_hash(uint8_t v_x_157_){
_start:
{
if (v_x_157_ == 0)
{
uint64_t v___x_158_; 
v___x_158_ = 0ULL;
return v___x_158_;
}
else
{
uint64_t v___x_159_; 
v___x_159_ = 1ULL;
return v___x_159_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_instHashablePredEncoding_hash___boxed(lean_object* v_x_160_){
_start:
{
uint8_t v_x_28__boxed_161_; uint64_t v_res_162_; lean_object* v_r_163_; 
v_x_28__boxed_161_ = lean_unbox(v_x_160_);
v_res_162_ = l_Lean_Meta_Tactic_BVDecide_EPR_instHashablePredEncoding_hash(v_x_28__boxed_161_);
v_r_163_ = lean_box_uint64(v_res_162_);
return v_r_163_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_BVDecide_EPR_PredEncoding_ofNat(lean_object* v_n_166_){
_start:
{
lean_object* v___x_167_; uint8_t v___x_168_; 
v___x_167_ = lean_unsigned_to_nat(0u);
v___x_168_ = lean_nat_dec_le(v_n_166_, v___x_167_);
if (v___x_168_ == 0)
{
uint8_t v___x_169_; 
v___x_169_ = 1;
return v___x_169_;
}
else
{
uint8_t v___x_170_; 
v___x_170_ = 0;
return v___x_170_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_PredEncoding_ofNat___boxed(lean_object* v_n_171_){
_start:
{
uint8_t v_res_172_; lean_object* v_r_173_; 
v_res_172_ = l_Lean_Meta_Tactic_BVDecide_EPR_PredEncoding_ofNat(v_n_171_);
lean_dec(v_n_171_);
v_r_173_ = lean_box(v_res_172_);
return v_r_173_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_BVDecide_EPR_instDecidableEqPredEncoding(uint8_t v_x_174_, uint8_t v_y_175_){
_start:
{
lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; uint8_t v___x_180_; 
v___x_176_ = lean_box(v_x_174_);
v___x_177_ = lean_obj_tag_nat(v___x_176_);
lean_dec(v___x_176_);
v___x_178_ = lean_box(v_y_175_);
v___x_179_ = lean_obj_tag_nat(v___x_178_);
lean_dec(v___x_178_);
v___x_180_ = lean_nat_dec_eq(v___x_177_, v___x_179_);
return v___x_180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_instDecidableEqPredEncoding___boxed(lean_object* v_x_181_, lean_object* v_y_182_){
_start:
{
uint8_t v_x_23__boxed_183_; uint8_t v_y_24__boxed_184_; uint8_t v_res_185_; lean_object* v_r_186_; 
v_x_23__boxed_183_ = lean_unbox(v_x_181_);
v_y_24__boxed_184_ = lean_unbox(v_y_182_);
v_res_185_ = l_Lean_Meta_Tactic_BVDecide_EPR_instDecidableEqPredEncoding(v_x_23__boxed_183_, v_y_24__boxed_184_);
v_r_186_ = lean_box(v_res_185_);
return v_r_186_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedQuantifiedFact_default___closed__0(void){
_start:
{
lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; 
v___x_194_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedPredInfo_default___closed__0));
v___x_195_ = l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp_default;
v___x_196_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_196_, 0, v___x_195_);
lean_ctor_set(v___x_196_, 1, v___x_194_);
return v___x_196_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedQuantifiedFact_default(void){
_start:
{
lean_object* v___x_197_; 
v___x_197_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedQuantifiedFact_default___closed__0, &l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedQuantifiedFact_default___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedQuantifiedFact_default___closed__0);
return v___x_197_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedQuantifiedFact(void){
_start:
{
lean_object* v___x_198_; 
v___x_198_ = l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedQuantifiedFact_default;
return v___x_198_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_QuantifiedFact_instantiateType(lean_object* v_fact_199_, lean_object* v_args_200_){
_start:
{
lean_object* v_hyp_201_; lean_object* v_boundSorts_202_; lean_object* v_type_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; 
v_hyp_201_ = lean_ctor_get(v_fact_199_, 0);
v_boundSorts_202_ = lean_ctor_get(v_fact_199_, 1);
v_type_203_ = lean_ctor_get(v_hyp_201_, 1);
v___x_204_ = lean_array_get_size(v_boundSorts_202_);
v___x_205_ = l_Lean_Expr_getForallBodyMaxDepth(v___x_204_, v_type_203_);
v___x_206_ = lean_expr_instantiate_rev(v___x_205_, v_args_200_);
lean_dec_ref(v___x_205_);
return v___x_206_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_QuantifiedFact_instantiateType___boxed(lean_object* v_fact_207_, lean_object* v_args_208_){
_start:
{
lean_object* v_res_209_; 
v_res_209_ = l_Lean_Meta_Tactic_BVDecide_EPR_QuantifiedFact_instantiateType(v_fact_207_, v_args_208_);
lean_dec_ref(v_args_208_);
lean_dec_ref(v_fact_207_);
return v_res_209_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_Tactic_BVDecide_EPR_QuantifiedFact_instantiateParts_spec__1___closed__7(void){
_start:
{
lean_object* v___x_217_; 
v___x_217_ = l_Array_instInhabited___redArg();
return v___x_217_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Tactic_BVDecide_EPR_QuantifiedFact_instantiateParts_spec__1(lean_object* v_msg_218_){
_start:
{
lean_object* v___f_219_; lean_object* v___f_220_; lean_object* v___f_221_; lean_object* v___f_222_; lean_object* v___f_223_; lean_object* v___f_224_; lean_object* v___f_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; 
v___f_219_ = ((lean_object*)(l_panic___at___00Lean_Meta_Tactic_BVDecide_EPR_QuantifiedFact_instantiateParts_spec__1___closed__0));
v___f_220_ = ((lean_object*)(l_panic___at___00Lean_Meta_Tactic_BVDecide_EPR_QuantifiedFact_instantiateParts_spec__1___closed__1));
v___f_221_ = ((lean_object*)(l_panic___at___00Lean_Meta_Tactic_BVDecide_EPR_QuantifiedFact_instantiateParts_spec__1___closed__2));
v___f_222_ = ((lean_object*)(l_panic___at___00Lean_Meta_Tactic_BVDecide_EPR_QuantifiedFact_instantiateParts_spec__1___closed__3));
v___f_223_ = ((lean_object*)(l_panic___at___00Lean_Meta_Tactic_BVDecide_EPR_QuantifiedFact_instantiateParts_spec__1___closed__4));
v___f_224_ = ((lean_object*)(l_panic___at___00Lean_Meta_Tactic_BVDecide_EPR_QuantifiedFact_instantiateParts_spec__1___closed__5));
v___f_225_ = ((lean_object*)(l_panic___at___00Lean_Meta_Tactic_BVDecide_EPR_QuantifiedFact_instantiateParts_spec__1___closed__6));
v___x_226_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_226_, 0, v___f_219_);
lean_ctor_set(v___x_226_, 1, v___f_220_);
v___x_227_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_227_, 0, v___x_226_);
lean_ctor_set(v___x_227_, 1, v___f_221_);
lean_ctor_set(v___x_227_, 2, v___f_222_);
lean_ctor_set(v___x_227_, 3, v___f_223_);
lean_ctor_set(v___x_227_, 4, v___f_224_);
v___x_228_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_228_, 0, v___x_227_);
lean_ctor_set(v___x_228_, 1, v___f_225_);
v___x_229_ = lean_obj_once(&l_panic___at___00Lean_Meta_Tactic_BVDecide_EPR_QuantifiedFact_instantiateParts_spec__1___closed__7, &l_panic___at___00Lean_Meta_Tactic_BVDecide_EPR_QuantifiedFact_instantiateParts_spec__1___closed__7_once, _init_l_panic___at___00Lean_Meta_Tactic_BVDecide_EPR_QuantifiedFact_instantiateParts_spec__1___closed__7);
v___x_230_ = l_Lean_instInhabitedExpr;
v___x_231_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_231_, 0, v___x_229_);
lean_ctor_set(v___x_231_, 1, v___x_230_);
v___x_232_ = l_instInhabitedOfMonad___redArg(v___x_228_, v___x_231_);
v___x_233_ = lean_panic_fn_borrowed(v___x_232_, v_msg_218_);
lean_dec(v___x_232_);
return v___x_233_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_EPR_QuantifiedFact_instantiateParts_spec__0___redArg(size_t v_sz_234_, size_t v_i_235_, lean_object* v_b_236_){
_start:
{
uint8_t v___x_237_; 
v___x_237_ = lean_usize_dec_lt(v_i_235_, v_sz_234_);
if (v___x_237_ == 0)
{
return v_b_236_;
}
else
{
lean_object* v_fst_238_; 
v_fst_238_ = lean_ctor_get(v_b_236_, 0);
lean_inc(v_fst_238_);
if (lean_obj_tag(v_fst_238_) == 7)
{
lean_object* v_snd_239_; lean_object* v___x_241_; uint8_t v_isShared_242_; uint8_t v_isSharedCheck_252_; 
v_snd_239_ = lean_ctor_get(v_b_236_, 1);
v_isSharedCheck_252_ = !lean_is_exclusive(v_b_236_);
if (v_isSharedCheck_252_ == 0)
{
lean_object* v_unused_253_; 
v_unused_253_ = lean_ctor_get(v_b_236_, 0);
lean_dec(v_unused_253_);
v___x_241_ = v_b_236_;
v_isShared_242_ = v_isSharedCheck_252_;
goto v_resetjp_240_;
}
else
{
lean_inc(v_snd_239_);
lean_dec(v_b_236_);
v___x_241_ = lean_box(0);
v_isShared_242_ = v_isSharedCheck_252_;
goto v_resetjp_240_;
}
v_resetjp_240_:
{
lean_object* v_binderType_243_; lean_object* v_body_244_; lean_object* v___x_245_; lean_object* v___x_247_; 
v_binderType_243_ = lean_ctor_get(v_fst_238_, 1);
lean_inc_ref(v_binderType_243_);
v_body_244_ = lean_ctor_get(v_fst_238_, 2);
lean_inc_ref(v_body_244_);
lean_dec_ref_known(v_fst_238_, 3);
v___x_245_ = lean_array_push(v_snd_239_, v_binderType_243_);
if (v_isShared_242_ == 0)
{
lean_ctor_set(v___x_241_, 1, v___x_245_);
lean_ctor_set(v___x_241_, 0, v_body_244_);
v___x_247_ = v___x_241_;
goto v_reusejp_246_;
}
else
{
lean_object* v_reuseFailAlloc_251_; 
v_reuseFailAlloc_251_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_251_, 0, v_body_244_);
lean_ctor_set(v_reuseFailAlloc_251_, 1, v___x_245_);
v___x_247_ = v_reuseFailAlloc_251_;
goto v_reusejp_246_;
}
v_reusejp_246_:
{
size_t v___x_248_; size_t v___x_249_; 
v___x_248_ = ((size_t)1ULL);
v___x_249_ = lean_usize_add(v_i_235_, v___x_248_);
v_i_235_ = v___x_249_;
v_b_236_ = v___x_247_;
goto _start;
}
}
}
else
{
lean_object* v_snd_254_; lean_object* v___x_256_; uint8_t v_isShared_257_; uint8_t v_isSharedCheck_261_; 
v_snd_254_ = lean_ctor_get(v_b_236_, 1);
v_isSharedCheck_261_ = !lean_is_exclusive(v_b_236_);
if (v_isSharedCheck_261_ == 0)
{
lean_object* v_unused_262_; 
v_unused_262_ = lean_ctor_get(v_b_236_, 0);
lean_dec(v_unused_262_);
v___x_256_ = v_b_236_;
v_isShared_257_ = v_isSharedCheck_261_;
goto v_resetjp_255_;
}
else
{
lean_inc(v_snd_254_);
lean_dec(v_b_236_);
v___x_256_ = lean_box(0);
v_isShared_257_ = v_isSharedCheck_261_;
goto v_resetjp_255_;
}
v_resetjp_255_:
{
lean_object* v___x_259_; 
if (v_isShared_257_ == 0)
{
v___x_259_ = v___x_256_;
goto v_reusejp_258_;
}
else
{
lean_object* v_reuseFailAlloc_260_; 
v_reuseFailAlloc_260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_260_, 0, v_fst_238_);
lean_ctor_set(v_reuseFailAlloc_260_, 1, v_snd_254_);
v___x_259_ = v_reuseFailAlloc_260_;
goto v_reusejp_258_;
}
v_reusejp_258_:
{
return v___x_259_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_EPR_QuantifiedFact_instantiateParts_spec__0___redArg___boxed(lean_object* v_sz_263_, lean_object* v_i_264_, lean_object* v_b_265_){
_start:
{
size_t v_sz_boxed_266_; size_t v_i_boxed_267_; lean_object* v_res_268_; 
v_sz_boxed_266_ = lean_unbox_usize(v_sz_263_);
lean_dec(v_sz_263_);
v_i_boxed_267_ = lean_unbox_usize(v_i_264_);
lean_dec(v_i_264_);
v_res_268_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_EPR_QuantifiedFact_instantiateParts_spec__0___redArg(v_sz_boxed_266_, v_i_boxed_267_, v_b_265_);
return v_res_268_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_EPR_QuantifiedFact_instantiateParts___closed__3(void){
_start:
{
lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; 
v___x_272_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_EPR_QuantifiedFact_instantiateParts___closed__2));
v___x_273_ = lean_unsigned_to_nat(2u);
v___x_274_ = lean_unsigned_to_nat(109u);
v___x_275_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_EPR_QuantifiedFact_instantiateParts___closed__1));
v___x_276_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_EPR_QuantifiedFact_instantiateParts___closed__0));
v___x_277_ = l_mkPanicMessageWithDecl(v___x_276_, v___x_275_, v___x_274_, v___x_273_, v___x_272_);
return v___x_277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_QuantifiedFact_instantiateParts(lean_object* v_fact_278_, lean_object* v_args_279_){
_start:
{
lean_object* v_type_280_; lean_object* v___x_281_; lean_object* v_guards_282_; lean_object* v___x_283_; size_t v_sz_284_; size_t v___x_285_; lean_object* v___x_286_; lean_object* v_fst_287_; lean_object* v_snd_288_; lean_object* v___x_290_; uint8_t v_isShared_291_; uint8_t v_isSharedCheck_298_; 
v_type_280_ = l_Lean_Meta_Tactic_BVDecide_EPR_QuantifiedFact_instantiateType(v_fact_278_, v_args_279_);
v___x_281_ = lean_array_get_size(v_args_279_);
v_guards_282_ = lean_mk_empty_array_with_capacity(v___x_281_);
v___x_283_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_283_, 0, v_type_280_);
lean_ctor_set(v___x_283_, 1, v_guards_282_);
v_sz_284_ = lean_array_size(v_args_279_);
v___x_285_ = ((size_t)0ULL);
v___x_286_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_EPR_QuantifiedFact_instantiateParts_spec__0___redArg(v_sz_284_, v___x_285_, v___x_283_);
v_fst_287_ = lean_ctor_get(v___x_286_, 0);
v_snd_288_ = lean_ctor_get(v___x_286_, 1);
v_isSharedCheck_298_ = !lean_is_exclusive(v___x_286_);
if (v_isSharedCheck_298_ == 0)
{
v___x_290_ = v___x_286_;
v_isShared_291_ = v_isSharedCheck_298_;
goto v_resetjp_289_;
}
else
{
lean_inc(v_snd_288_);
lean_inc(v_fst_287_);
lean_dec(v___x_286_);
v___x_290_ = lean_box(0);
v_isShared_291_ = v_isSharedCheck_298_;
goto v_resetjp_289_;
}
v_resetjp_289_:
{
uint8_t v___x_292_; 
v___x_292_ = l_Lean_Expr_hasLooseBVars(v_fst_287_);
if (v___x_292_ == 0)
{
lean_object* v___x_294_; 
if (v_isShared_291_ == 0)
{
lean_ctor_set(v___x_290_, 1, v_fst_287_);
lean_ctor_set(v___x_290_, 0, v_snd_288_);
v___x_294_ = v___x_290_;
goto v_reusejp_293_;
}
else
{
lean_object* v_reuseFailAlloc_295_; 
v_reuseFailAlloc_295_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_295_, 0, v_snd_288_);
lean_ctor_set(v_reuseFailAlloc_295_, 1, v_fst_287_);
v___x_294_ = v_reuseFailAlloc_295_;
goto v_reusejp_293_;
}
v_reusejp_293_:
{
return v___x_294_;
}
}
else
{
lean_object* v___x_296_; lean_object* v___x_297_; 
lean_del_object(v___x_290_);
lean_dec(v_snd_288_);
lean_dec(v_fst_287_);
v___x_296_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_EPR_QuantifiedFact_instantiateParts___closed__3, &l_Lean_Meta_Tactic_BVDecide_EPR_QuantifiedFact_instantiateParts___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_EPR_QuantifiedFact_instantiateParts___closed__3);
v___x_297_ = l_panic___at___00Lean_Meta_Tactic_BVDecide_EPR_QuantifiedFact_instantiateParts_spec__1(v___x_296_);
return v___x_297_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_QuantifiedFact_instantiateParts___boxed(lean_object* v_fact_299_, lean_object* v_args_300_){
_start:
{
lean_object* v_res_301_; 
v_res_301_ = l_Lean_Meta_Tactic_BVDecide_EPR_QuantifiedFact_instantiateParts(v_fact_299_, v_args_300_);
lean_dec_ref(v_args_300_);
lean_dec_ref(v_fact_299_);
return v_res_301_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_EPR_QuantifiedFact_instantiateParts_spec__0(lean_object* v_as_302_, size_t v_sz_303_, size_t v_i_304_, lean_object* v_b_305_){
_start:
{
lean_object* v___x_306_; 
v___x_306_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_EPR_QuantifiedFact_instantiateParts_spec__0___redArg(v_sz_303_, v_i_304_, v_b_305_);
return v___x_306_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_EPR_QuantifiedFact_instantiateParts_spec__0___boxed(lean_object* v_as_307_, lean_object* v_sz_308_, lean_object* v_i_309_, lean_object* v_b_310_){
_start:
{
size_t v_sz_boxed_311_; size_t v_i_boxed_312_; lean_object* v_res_313_; 
v_sz_boxed_311_ = lean_unbox_usize(v_sz_308_);
lean_dec(v_sz_308_);
v_i_boxed_312_ = lean_unbox_usize(v_i_309_);
lean_dec(v_i_309_);
v_res_313_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_EPR_QuantifiedFact_instantiateParts_spec__0(v_as_307_, v_sz_boxed_311_, v_i_boxed_312_, v_b_310_);
lean_dec_ref(v_as_307_);
return v_res_313_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_QuantifiedFact_instantiate(lean_object* v_fact_317_, lean_object* v_args_318_, lean_object* v_a_319_, lean_object* v_a_320_, lean_object* v_a_321_, lean_object* v_a_322_, lean_object* v_a_323_, lean_object* v_a_324_){
_start:
{
lean_object* v___x_326_; lean_object* v___x_327_; 
v___x_326_ = l_Lean_Meta_Tactic_BVDecide_EPR_QuantifiedFact_instantiateType(v_fact_317_, v_args_318_);
v___x_327_ = l_Lean_Meta_Sym_shareCommon(v___x_326_, v_a_319_, v_a_320_, v_a_321_, v_a_322_, v_a_323_, v_a_324_);
if (lean_obj_tag(v___x_327_) == 0)
{
lean_object* v_hyp_328_; lean_object* v_a_329_; lean_object* v___x_331_; uint8_t v_isShared_332_; uint8_t v_isSharedCheck_350_; 
v_hyp_328_ = lean_ctor_get(v_fact_317_, 0);
lean_inc_ref(v_hyp_328_);
lean_dec_ref(v_fact_317_);
v_a_329_ = lean_ctor_get(v___x_327_, 0);
v_isSharedCheck_350_ = !lean_is_exclusive(v___x_327_);
if (v_isSharedCheck_350_ == 0)
{
v___x_331_ = v___x_327_;
v_isShared_332_ = v_isSharedCheck_350_;
goto v_resetjp_330_;
}
else
{
lean_inc(v_a_329_);
lean_dec(v___x_327_);
v___x_331_ = lean_box(0);
v_isShared_332_ = v_isSharedCheck_350_;
goto v_resetjp_330_;
}
v_resetjp_330_:
{
lean_object* v_name_333_; lean_object* v_value_334_; lean_object* v_source_335_; lean_object* v___x_337_; uint8_t v_isShared_338_; uint8_t v_isSharedCheck_348_; 
v_name_333_ = lean_ctor_get(v_hyp_328_, 0);
v_value_334_ = lean_ctor_get(v_hyp_328_, 2);
v_source_335_ = lean_ctor_get(v_hyp_328_, 3);
v_isSharedCheck_348_ = !lean_is_exclusive(v_hyp_328_);
if (v_isSharedCheck_348_ == 0)
{
lean_object* v_unused_349_; 
v_unused_349_ = lean_ctor_get(v_hyp_328_, 1);
lean_dec(v_unused_349_);
v___x_337_ = v_hyp_328_;
v_isShared_338_ = v_isSharedCheck_348_;
goto v_resetjp_336_;
}
else
{
lean_inc(v_source_335_);
lean_inc(v_value_334_);
lean_inc(v_name_333_);
lean_dec(v_hyp_328_);
v___x_337_ = lean_box(0);
v_isShared_338_ = v_isSharedCheck_348_;
goto v_resetjp_336_;
}
v_resetjp_336_:
{
lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_343_; 
v___x_339_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_EPR_QuantifiedFact_instantiate___closed__1));
v___x_340_ = l_Lean_Name_append(v_name_333_, v___x_339_);
v___x_341_ = l_Lean_mkAppN(v_value_334_, v_args_318_);
if (v_isShared_338_ == 0)
{
lean_ctor_set(v___x_337_, 2, v___x_341_);
lean_ctor_set(v___x_337_, 1, v_a_329_);
lean_ctor_set(v___x_337_, 0, v___x_340_);
v___x_343_ = v___x_337_;
goto v_reusejp_342_;
}
else
{
lean_object* v_reuseFailAlloc_347_; 
v_reuseFailAlloc_347_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_347_, 0, v___x_340_);
lean_ctor_set(v_reuseFailAlloc_347_, 1, v_a_329_);
lean_ctor_set(v_reuseFailAlloc_347_, 2, v___x_341_);
lean_ctor_set(v_reuseFailAlloc_347_, 3, v_source_335_);
v___x_343_ = v_reuseFailAlloc_347_;
goto v_reusejp_342_;
}
v_reusejp_342_:
{
lean_object* v___x_345_; 
if (v_isShared_332_ == 0)
{
lean_ctor_set(v___x_331_, 0, v___x_343_);
v___x_345_ = v___x_331_;
goto v_reusejp_344_;
}
else
{
lean_object* v_reuseFailAlloc_346_; 
v_reuseFailAlloc_346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_346_, 0, v___x_343_);
v___x_345_ = v_reuseFailAlloc_346_;
goto v_reusejp_344_;
}
v_reusejp_344_:
{
return v___x_345_;
}
}
}
}
}
else
{
lean_object* v_a_351_; lean_object* v___x_353_; uint8_t v_isShared_354_; uint8_t v_isSharedCheck_358_; 
lean_dec_ref(v_fact_317_);
v_a_351_ = lean_ctor_get(v___x_327_, 0);
v_isSharedCheck_358_ = !lean_is_exclusive(v___x_327_);
if (v_isSharedCheck_358_ == 0)
{
v___x_353_ = v___x_327_;
v_isShared_354_ = v_isSharedCheck_358_;
goto v_resetjp_352_;
}
else
{
lean_inc(v_a_351_);
lean_dec(v___x_327_);
v___x_353_ = lean_box(0);
v_isShared_354_ = v_isSharedCheck_358_;
goto v_resetjp_352_;
}
v_resetjp_352_:
{
lean_object* v___x_356_; 
if (v_isShared_354_ == 0)
{
v___x_356_ = v___x_353_;
goto v_reusejp_355_;
}
else
{
lean_object* v_reuseFailAlloc_357_; 
v_reuseFailAlloc_357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_357_, 0, v_a_351_);
v___x_356_ = v_reuseFailAlloc_357_;
goto v_reusejp_355_;
}
v_reusejp_355_:
{
return v___x_356_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_QuantifiedFact_instantiate___boxed(lean_object* v_fact_359_, lean_object* v_args_360_, lean_object* v_a_361_, lean_object* v_a_362_, lean_object* v_a_363_, lean_object* v_a_364_, lean_object* v_a_365_, lean_object* v_a_366_, lean_object* v_a_367_){
_start:
{
lean_object* v_res_368_; 
v_res_368_ = l_Lean_Meta_Tactic_BVDecide_EPR_QuantifiedFact_instantiate(v_fact_359_, v_args_360_, v_a_361_, v_a_362_, v_a_363_, v_a_364_, v_a_365_, v_a_366_);
lean_dec(v_a_366_);
lean_dec_ref(v_a_365_);
lean_dec(v_a_364_);
lean_dec_ref(v_a_363_);
lean_dec(v_a_362_);
lean_dec_ref(v_a_361_);
lean_dec_ref(v_args_360_);
return v_res_368_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedEprProblem_default___closed__0(void){
_start:
{
lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; 
v___x_369_ = lean_box(0);
v___x_370_ = lean_unsigned_to_nat(16u);
v___x_371_ = lean_mk_array(v___x_370_, v___x_369_);
return v___x_371_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedEprProblem_default___closed__1(void){
_start:
{
lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; 
v___x_372_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedEprProblem_default___closed__0, &l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedEprProblem_default___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedEprProblem_default___closed__0);
v___x_373_ = lean_unsigned_to_nat(0u);
v___x_374_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_374_, 0, v___x_373_);
lean_ctor_set(v___x_374_, 1, v___x_372_);
return v___x_374_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedEprProblem_default___closed__3(void){
_start:
{
lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; 
v___x_377_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedEprProblem_default___closed__2));
v___x_378_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedEprProblem_default___closed__1, &l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedEprProblem_default___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedEprProblem_default___closed__1);
v___x_379_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_379_, 0, v___x_378_);
lean_ctor_set(v___x_379_, 1, v___x_378_);
lean_ctor_set(v___x_379_, 2, v___x_378_);
lean_ctor_set(v___x_379_, 3, v___x_377_);
lean_ctor_set(v___x_379_, 4, v___x_377_);
return v___x_379_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedEprProblem_default(void){
_start:
{
lean_object* v___x_380_; 
v___x_380_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedEprProblem_default___closed__3, &l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedEprProblem_default___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedEprProblem_default___closed__3);
return v___x_380_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedEprProblem(void){
_start:
{
lean_object* v___x_381_; 
v___x_381_ = l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedEprProblem_default;
return v___x_381_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedBvSortInfo_default___closed__0(void){
_start:
{
lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; 
v___x_382_ = lean_box(0);
v___x_383_ = lean_unsigned_to_nat(16u);
v___x_384_ = lean_mk_array(v___x_383_, v___x_382_);
return v___x_384_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedBvSortInfo_default___closed__1(void){
_start:
{
lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; 
v___x_385_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedBvSortInfo_default___closed__0, &l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedBvSortInfo_default___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedBvSortInfo_default___closed__0);
v___x_386_ = lean_unsigned_to_nat(0u);
v___x_387_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_387_, 0, v___x_386_);
lean_ctor_set(v___x_387_, 1, v___x_385_);
return v___x_387_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedBvSortInfo_default___closed__2(void){
_start:
{
lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; 
v___x_388_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedBvSortInfo_default___closed__1, &l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedBvSortInfo_default___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedBvSortInfo_default___closed__1);
v___x_389_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedSortInfo_default___closed__2, &l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedSortInfo_default___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedSortInfo_default___closed__2);
v___x_390_ = lean_unsigned_to_nat(0u);
v___x_391_ = l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedSortInfo_default;
v___x_392_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_392_, 0, v___x_391_);
lean_ctor_set(v___x_392_, 1, v___x_390_);
lean_ctor_set(v___x_392_, 2, v___x_389_);
lean_ctor_set(v___x_392_, 3, v___x_389_);
lean_ctor_set(v___x_392_, 4, v___x_389_);
lean_ctor_set(v___x_392_, 5, v___x_389_);
lean_ctor_set(v___x_392_, 6, v___x_388_);
return v___x_392_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedBvSortInfo_default(void){
_start:
{
lean_object* v___x_393_; 
v___x_393_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedBvSortInfo_default___closed__2, &l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedBvSortInfo_default___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedBvSortInfo_default___closed__2);
return v___x_393_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedBvSortInfo(void){
_start:
{
lean_object* v___x_394_; 
v___x_394_ = l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedBvSortInfo_default;
return v___x_394_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_EPR_BvSortInfo_bvType___closed__2(void){
_start:
{
lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; 
v___x_398_ = lean_box(0);
v___x_399_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_EPR_BvSortInfo_bvType___closed__1));
v___x_400_ = l_Lean_mkConst(v___x_399_, v___x_398_);
return v___x_400_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_BvSortInfo_bvType(lean_object* v_info_401_){
_start:
{
lean_object* v_width_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; 
v_width_402_ = lean_ctor_get(v_info_401_, 1);
lean_inc(v_width_402_);
lean_dec_ref(v_info_401_);
v___x_403_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_EPR_BvSortInfo_bvType___closed__2, &l_Lean_Meta_Tactic_BVDecide_EPR_BvSortInfo_bvType___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_EPR_BvSortInfo_bvType___closed__2);
v___x_404_ = l_Lean_mkNatLit(v_width_402_);
v___x_405_ = l_Lean_Expr_app___override(v___x_403_, v___x_404_);
return v___x_405_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_BvSortInfo_appToBv(lean_object* v_info_406_, lean_object* v_e_407_){
_start:
{
lean_object* v_toBv_408_; lean_object* v___x_409_; 
v_toBv_408_ = lean_ctor_get(v_info_406_, 2);
lean_inc_ref(v_toBv_408_);
lean_dec_ref(v_info_406_);
v___x_409_ = l_Lean_Expr_app___override(v_toBv_408_, v_e_407_);
return v___x_409_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedBvPredInfo_default___closed__0(void){
_start:
{
lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; 
v___x_410_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedSortInfo_default___closed__2, &l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedSortInfo_default___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedSortInfo_default___closed__2);
v___x_411_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedPredInfo_default));
v___x_412_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_412_, 0, v___x_411_);
lean_ctor_set(v___x_412_, 1, v___x_410_);
lean_ctor_set(v___x_412_, 2, v___x_410_);
return v___x_412_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedBvPredInfo_default(void){
_start:
{
lean_object* v___x_413_; 
v___x_413_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedBvPredInfo_default___closed__0, &l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedBvPredInfo_default___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedBvPredInfo_default___closed__0);
return v___x_413_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedBvPredInfo(void){
_start:
{
lean_object* v___x_414_; 
v___x_414_ = l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedBvPredInfo_default;
return v___x_414_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedEprBvProblem_default___closed__0(void){
_start:
{
lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; 
v___x_415_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedEprProblem_default___closed__2));
v___x_416_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedEprProblem_default___closed__1, &l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedEprProblem_default___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedEprProblem_default___closed__1);
v___x_417_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_417_, 0, v___x_416_);
lean_ctor_set(v___x_417_, 1, v___x_416_);
lean_ctor_set(v___x_417_, 2, v___x_416_);
lean_ctor_set(v___x_417_, 3, v___x_415_);
lean_ctor_set(v___x_417_, 4, v___x_415_);
return v___x_417_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedEprBvProblem_default(void){
_start:
{
lean_object* v___x_418_; 
v___x_418_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedEprBvProblem_default___closed__0, &l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedEprBvProblem_default___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedEprBvProblem_default___closed__0);
return v___x_418_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedEprBvProblem(void){
_start:
{
lean_object* v___x_419_; 
v___x_419_ = l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedEprBvProblem_default;
return v___x_419_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_SymM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Hyp(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_EPR_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Sym_SymM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Hyp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedSortId_default = _init_l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedSortId_default();
lean_mark_persistent(l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedSortId_default);
l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedSortId = _init_l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedSortId();
lean_mark_persistent(l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedSortId);
l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedSortInfo_default = _init_l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedSortInfo_default();
lean_mark_persistent(l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedSortInfo_default);
l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedSortInfo = _init_l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedSortInfo();
lean_mark_persistent(l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedSortInfo);
l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedPredEncoding_default = _init_l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedPredEncoding_default();
l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedPredEncoding = _init_l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedPredEncoding();
l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedQuantifiedFact_default = _init_l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedQuantifiedFact_default();
lean_mark_persistent(l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedQuantifiedFact_default);
l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedQuantifiedFact = _init_l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedQuantifiedFact();
lean_mark_persistent(l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedQuantifiedFact);
l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedEprProblem_default = _init_l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedEprProblem_default();
lean_mark_persistent(l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedEprProblem_default);
l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedEprProblem = _init_l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedEprProblem();
lean_mark_persistent(l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedEprProblem);
l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedBvSortInfo_default = _init_l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedBvSortInfo_default();
lean_mark_persistent(l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedBvSortInfo_default);
l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedBvSortInfo = _init_l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedBvSortInfo();
lean_mark_persistent(l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedBvSortInfo);
l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedBvPredInfo_default = _init_l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedBvPredInfo_default();
lean_mark_persistent(l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedBvPredInfo_default);
l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedBvPredInfo = _init_l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedBvPredInfo();
lean_mark_persistent(l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedBvPredInfo);
l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedEprBvProblem_default = _init_l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedEprBvProblem_default();
lean_mark_persistent(l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedEprBvProblem_default);
l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedEprBvProblem = _init_l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedEprBvProblem();
lean_mark_persistent(l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedEprBvProblem);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_BVDecide_EPR_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Sym_SymM(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_BVDecide_Normalize_Hyp(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_BVDecide_EPR_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Sym_SymM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_BVDecide_Normalize_Hyp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_EPR_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_BVDecide_EPR_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_BVDecide_EPR_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
