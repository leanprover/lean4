// Lean compiler output
// Module: Lean.Elab.Tactic.VCGen.LatticeOp
// Imports: public import Lean.Meta.Sym.Apply public import Std.Internal.Order.Heyting public import Lean.Elab.Tactic.VCGen.FrameProc import Std.Internal.Order.FrameClosure import Lean.Meta.Sym.Simp.Rewrite import Lean.Meta.AppBuilder import Lean.Meta.AbstractMVars
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
lean_object* l_Lean_Meta_mkConstWithFreshMVarLevels(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallMetaTelescope(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAppM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_List_getLast_x21___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAppOptM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* lean_array_pop(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_noption_is_some(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_noption_get(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_SimpM_run_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_mkEqTrans(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Raw_setEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVar(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Meta_forallMetaTelescopeReducing(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Expr_constName_x3f(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_Meta_abstractMVars(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_mkBackwardRuleFromExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_extract___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_dischargeNone___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_Theorems_rewrite___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_mkTheoremFromDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_Theorems_insert(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkCongrArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqSymm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Order"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meet"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__2_value),LEAN_SCALAR_PTR_LITERAL(194, 193, 63, 6, 53, 61, 199, 176)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__3_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "meet_apply"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__5_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__5_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__4_value),LEAN_SCALAR_PTR_LITERAL(99, 197, 244, 134, 174, 130, 207, 233)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__5_value;
static const lean_array_object l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__5_value)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__6_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "le_meet"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__7_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__8_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__8_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__7_value),LEAN_SCALAR_PTR_LITERAL(190, 114, 168, 215, 244, 74, 160, 2)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__8_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__8_value)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__9 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__9_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__3_value),((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__6_value),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__9_value)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__10 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__10_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_meet = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__10_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_LatticeOp_himp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "himp"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_himp___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_himp___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_himp___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_himp___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_himp___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_himp___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_himp___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_himp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(173, 29, 48, 122, 5, 158, 45, 140)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_himp___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_himp___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_LatticeOp_himp___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "himp_apply"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_himp___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_himp___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_himp___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_himp___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_himp___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_himp___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_himp___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_himp___closed__2_value),LEAN_SCALAR_PTR_LITERAL(185, 113, 71, 38, 245, 240, 32, 111)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_himp___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_himp___closed__3_value;
static const lean_array_object l_Lean_Elab_Tactic_VCGen_LatticeOp_himp___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_himp___closed__3_value)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_himp___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_himp___closed__4_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_LatticeOp_himp___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "le_himp"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_himp___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_himp___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_himp___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_himp___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_himp___closed__6_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_himp___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_himp___closed__6_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_himp___closed__5_value),LEAN_SCALAR_PTR_LITERAL(34, 1, 31, 114, 210, 147, 30, 159)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_himp___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_himp___closed__6_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_himp___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_himp___closed__6_value)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_himp___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_himp___closed__7_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_himp___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_himp___closed__1_value),((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_himp___closed__4_value),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_himp___closed__7_value)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_himp___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_himp___closed__8_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_himp = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_himp___closed__8_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_LatticeOp_ofProp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "CompleteLattice"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_ofProp___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_ofProp___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_LatticeOp_ofProp___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "ofProp"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_ofProp___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_ofProp___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_ofProp___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_ofProp___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_ofProp___closed__2_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_ofProp___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_ofProp___closed__2_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_ofProp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(239, 140, 127, 117, 148, 144, 166, 107)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_ofProp___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_ofProp___closed__2_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_ofProp___closed__1_value),LEAN_SCALAR_PTR_LITERAL(51, 160, 150, 32, 134, 96, 114, 42)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_ofProp___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_ofProp___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_LatticeOp_ofProp___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "ofProp_apply"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_ofProp___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_ofProp___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_ofProp___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_ofProp___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_ofProp___closed__4_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_ofProp___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_ofProp___closed__4_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_ofProp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(239, 140, 127, 117, 148, 144, 166, 107)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_ofProp___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_ofProp___closed__4_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_ofProp___closed__3_value),LEAN_SCALAR_PTR_LITERAL(43, 0, 38, 134, 51, 116, 27, 243)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_ofProp___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_ofProp___closed__4_value;
static const lean_array_object l_Lean_Elab_Tactic_VCGen_LatticeOp_ofProp___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_ofProp___closed__4_value)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_ofProp___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_ofProp___closed__5_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_LatticeOp_ofProp___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "top_le_ofProp"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_ofProp___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_ofProp___closed__6_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_ofProp___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_ofProp___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_ofProp___closed__7_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_ofProp___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_ofProp___closed__7_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_ofProp___closed__6_value),LEAN_SCALAR_PTR_LITERAL(240, 115, 147, 236, 50, 105, 134, 105)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_ofProp___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_ofProp___closed__7_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_ofProp___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_ofProp___closed__7_value)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_ofProp___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_ofProp___closed__8_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_ofProp___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_ofProp___closed__2_value),((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_ofProp___closed__5_value),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_ofProp___closed__8_value)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_ofProp___closed__9 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_ofProp___closed__9_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_ofProp = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_ofProp___closed__9_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_LatticeOp_top___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "top"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_top___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_top___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_top___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_top___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_top___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_top___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_top___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_top___closed__0_value),LEAN_SCALAR_PTR_LITERAL(219, 33, 148, 124, 218, 91, 248, 169)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_top___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_top___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_LatticeOp_top___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "top_apply"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_top___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_top___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_top___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_top___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_top___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_top___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_top___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_top___closed__2_value),LEAN_SCALAR_PTR_LITERAL(230, 219, 32, 190, 96, 78, 240, 61)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_top___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_top___closed__3_value;
static const lean_array_object l_Lean_Elab_Tactic_VCGen_LatticeOp_top___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_top___closed__3_value)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_top___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_top___closed__4_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_LatticeOp_top___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "le_top"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_top___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_top___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_top___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_top___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_top___closed__6_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_top___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_top___closed__6_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_top___closed__5_value),LEAN_SCALAR_PTR_LITERAL(236, 200, 120, 191, 69, 224, 183, 155)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_top___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_top___closed__6_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_top___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_top___closed__6_value)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_top___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_top___closed__7_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_top___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_top___closed__1_value),((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_top___closed__4_value),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_top___closed__7_value)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_top___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_top___closed__8_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_top = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_top___closed__8_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "PreservesSup"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "upperAdjoint"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__2_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__2_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__0_value),LEAN_SCALAR_PTR_LITERAL(184, 207, 242, 99, 37, 43, 114, 21)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__2_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__1_value),LEAN_SCALAR_PTR_LITERAL(196, 52, 128, 160, 100, 147, 237, 166)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__2_value;
static const lean_array_object l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__3_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "le_upperAdjoint"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__5_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__5_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__0_value),LEAN_SCALAR_PTR_LITERAL(184, 207, 242, 99, 37, 43, 114, 21)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__5_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__4_value),LEAN_SCALAR_PTR_LITERAL(28, 162, 178, 118, 193, 187, 169, 14)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__5_value)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__6_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__2_value),((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__3_value),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__6_value)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__7_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__7_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_LatticeOp_iInf___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "iInf"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_iInf___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_iInf___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_iInf___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_iInf___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_iInf___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_iInf___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_iInf___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_iInf___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 96, 105, 10, 16, 194, 128, 157)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_iInf___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_iInf___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_LatticeOp_iInf___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "iInf_apply"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_iInf___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_iInf___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_iInf___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_iInf___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_iInf___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_iInf___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_iInf___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_iInf___closed__2_value),LEAN_SCALAR_PTR_LITERAL(13, 69, 58, 252, 126, 189, 121, 48)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_iInf___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_iInf___closed__3_value;
static const lean_array_object l_Lean_Elab_Tactic_VCGen_LatticeOp_iInf___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_iInf___closed__3_value)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_iInf___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_iInf___closed__4_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_LatticeOp_iInf___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "le_iInf"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_iInf___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_iInf___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_iInf___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_iInf___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_iInf___closed__6_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_iInf___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_iInf___closed__6_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_iInf___closed__5_value),LEAN_SCALAR_PTR_LITERAL(137, 155, 79, 233, 132, 15, 131, 19)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_iInf___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_iInf___closed__6_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_iInf___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_iInf___closed__6_value)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_iInf___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_iInf___closed__7_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_iInf___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_iInf___closed__1_value),((lean_object*)(((size_t)(3) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_iInf___closed__4_value),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_iInf___closed__7_value)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_iInf___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_iInf___closed__8_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_iInf = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_iInf___closed__8_value;
static const lean_array_object l_Lean_Elab_Tactic_VCGen_builtinLatticeOps___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*6, .m_other = 0, .m_tag = 246}, .m_size = 6, .m_capacity = 6, .m_data = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__10_value),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_himp___closed__8_value),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_ofProp___closed__9_value),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_top___closed__8_value),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__7_value),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_iInf___closed__8_value)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_builtinLatticeOps___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_builtinLatticeOps___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_Tactic_VCGen_builtinLatticeOps = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_builtinLatticeOps___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__1_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__1___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_Tactic_VCGen_latticeOps___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_VCGen_latticeOps___closed__0;
static lean_once_cell_t l_Lean_Elab_Tactic_VCGen_latticeOps___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_VCGen_latticeOps___closed__1;
static lean_once_cell_t l_Lean_Elab_Tactic_VCGen_latticeOps___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_VCGen_latticeOps___closed__2;
static lean_once_cell_t l_Lean_Elab_Tactic_VCGen_latticeOps___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_VCGen_latticeOps___closed__3;
static lean_once_cell_t l_Lean_Elab_Tactic_VCGen_latticeOps___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Lean_Elab_Tactic_VCGen_latticeOps___closed__4;
static lean_once_cell_t l_Lean_Elab_Tactic_VCGen_latticeOps___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Lean_Elab_Tactic_VCGen_latticeOps___closed__5;
static lean_once_cell_t l_Lean_Elab_Tactic_VCGen_latticeOps___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_Elab_Tactic_VCGen_latticeOps___closed__6;
static lean_once_cell_t l_Lean_Elab_Tactic_VCGen_latticeOps___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_VCGen_latticeOps___closed__7;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_latticeOps;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__1_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "PartialOrder"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "rel"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__1_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__2_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__2_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(179, 3, 218, 237, 219, 72, 94, 177)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__2_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__1_value),LEAN_SCALAR_PTR_LITERAL(41, 174, 7, 105, 99, 77, 97, 125)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "lattice terminal "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__3_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__4;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 33, .m_data = " does not conclude a `⊑` relation"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__5_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__6;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 56, .m_capacity = 56, .m_length = 55, .m_data = " has no head constant on its conclusion right-hand side"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__7 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__7_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__8;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals___closed__0;
static lean_once_cell_t l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_go___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_go___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_go_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_go_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 83, .m_capacity = 83, .m_length = 82, .m_data = "lattice saturation did not terminate; the rewrite set is likely non-terminating on"};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_go___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_go___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_go___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_go___closed__1;
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_go___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(100000) << 1) | 1)),((lean_object*)(((size_t)(2) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_go___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_go___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_Simp_dischargeNone___boxed, .m_arity = 11, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp___closed__1;
static lean_once_cell_t l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply_spec__0_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply_spec__0_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply_spec__0_spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = " does not conclude "};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply___closed__1;
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "u"};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply___closed__2_value),LEAN_SCALAR_PTR_LITERAL(232, 178, 247, 241, 102, 42, 87, 174)}};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply___closed__3_value;
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "le_apply_of_point_meet_le"};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply___closed__5_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply___closed__5_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply___closed__4_value),LEAN_SCALAR_PTR_LITERAL(147, 15, 136, 52, 94, 223, 161, 163)}};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply___closed__5_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply_spec__0_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__0___redArg(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__1_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__1___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__2___closed__0 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__2___closed__0_value;
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "mp"};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__2___closed__1 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__2___closed__1_value;
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__2___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__2___closed__2_value_aux_0),((lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__2___closed__1_value),LEAN_SCALAR_PTR_LITERAL(183, 66, 254, 161, 210, 133, 94, 78)}};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__2___closed__2 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__2___closed__2_value;
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "lattice operator `"};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__2___closed__3 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__2___closed__3_value;
static lean_once_cell_t l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__2___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__2___closed__4;
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__2___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 86, .m_capacity = 86, .m_length = 85, .m_data = "` neither reduces nor has a registered terminal; its split rule would be the identity"};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__2___closed__5 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__2___closed__5_value;
static lean_once_cell_t l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__2___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__2___closed__6;
static lean_once_cell_t l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__2___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__2___closed__7;
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__4(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__3(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_Tactic_VCGen_mkLatticeOpRule___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_VCGen_mkLatticeOpRule___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_mkLatticeOpRule(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_mkLatticeOpRule___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0_spec__0___redArg(lean_object* v_m_179_, lean_object* v_query_180_, lean_object* v_x_181_, lean_object* v_x_182_, lean_object* v_x_183_){
_start:
{
lean_object* v_zero_184_; uint8_t v_isZero_185_; 
v_zero_184_ = lean_unsigned_to_nat(0u);
v_isZero_185_ = lean_nat_dec_eq(v_x_182_, v_zero_184_);
if (v_isZero_185_ == 1)
{
lean_dec(v_x_183_);
lean_dec(v_x_182_);
if (lean_obj_tag(v_x_181_) == 0)
{
lean_object* v___x_186_; 
v___x_186_ = lean_box(2);
return v___x_186_;
}
else
{
lean_object* v_val_187_; lean_object* v___x_189_; uint8_t v_isShared_190_; uint8_t v_isSharedCheck_194_; 
v_val_187_ = lean_ctor_get(v_x_181_, 0);
v_isSharedCheck_194_ = !lean_is_exclusive(v_x_181_);
if (v_isSharedCheck_194_ == 0)
{
v___x_189_ = v_x_181_;
v_isShared_190_ = v_isSharedCheck_194_;
goto v_resetjp_188_;
}
else
{
lean_inc(v_val_187_);
lean_dec(v_x_181_);
v___x_189_ = lean_box(0);
v_isShared_190_ = v_isSharedCheck_194_;
goto v_resetjp_188_;
}
v_resetjp_188_:
{
lean_object* v___x_192_; 
if (v_isShared_190_ == 0)
{
v___x_192_ = v___x_189_;
goto v_reusejp_191_;
}
else
{
lean_object* v_reuseFailAlloc_193_; 
v_reuseFailAlloc_193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_193_, 0, v_val_187_);
v___x_192_ = v_reuseFailAlloc_193_;
goto v_reusejp_191_;
}
v_reusejp_191_:
{
return v___x_192_;
}
}
}
}
else
{
lean_object* v_keyArray_195_; lean_object* v_valueArray_196_; lean_object* v___x_197_; uint8_t v_isSome_198_; 
v_keyArray_195_ = lean_ctor_get(v_m_179_, 1);
v_valueArray_196_ = lean_ctor_get(v_m_179_, 2);
v___x_197_ = lean_array_fget_borrowed(v_keyArray_195_, v_x_183_);
v_isSome_198_ = lean_noption_is_some(v___x_197_);
if (v_isSome_198_ == 0)
{
lean_dec(v_x_182_);
if (lean_obj_tag(v_x_181_) == 0)
{
lean_object* v___x_199_; 
v___x_199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_199_, 0, v_x_183_);
return v___x_199_;
}
else
{
lean_object* v_val_200_; lean_object* v___x_202_; uint8_t v_isShared_203_; uint8_t v_isSharedCheck_207_; 
lean_dec(v_x_183_);
v_val_200_ = lean_ctor_get(v_x_181_, 0);
v_isSharedCheck_207_ = !lean_is_exclusive(v_x_181_);
if (v_isSharedCheck_207_ == 0)
{
v___x_202_ = v_x_181_;
v_isShared_203_ = v_isSharedCheck_207_;
goto v_resetjp_201_;
}
else
{
lean_inc(v_val_200_);
lean_dec(v_x_181_);
v___x_202_ = lean_box(0);
v_isShared_203_ = v_isSharedCheck_207_;
goto v_resetjp_201_;
}
v_resetjp_201_:
{
lean_object* v___x_205_; 
if (v_isShared_203_ == 0)
{
v___x_205_ = v___x_202_;
goto v_reusejp_204_;
}
else
{
lean_object* v_reuseFailAlloc_206_; 
v_reuseFailAlloc_206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_206_, 0, v_val_200_);
v___x_205_ = v_reuseFailAlloc_206_;
goto v_reusejp_204_;
}
v_reusejp_204_:
{
return v___x_205_;
}
}
}
}
else
{
lean_object* v_one_208_; lean_object* v_n_209_; lean_object* v___y_211_; 
v_one_208_ = lean_unsigned_to_nat(1u);
v_n_209_ = lean_nat_sub(v_x_182_, v_one_208_);
lean_dec(v_x_182_);
if (v_isSome_198_ == 0)
{
goto v___jp_217_;
}
else
{
lean_object* v___x_219_; uint8_t v_isSome_220_; 
v___x_219_ = lean_array_fget_borrowed(v_valueArray_196_, v_x_183_);
v_isSome_220_ = lean_noption_is_some(v___x_219_);
if (v_isSome_220_ == 0)
{
goto v___jp_217_;
}
else
{
lean_object* v_val_221_; uint8_t v___x_222_; 
lean_inc(v___x_197_);
v_val_221_ = lean_noption_get(v___x_197_);
v___x_222_ = lean_name_eq(v_val_221_, v_query_180_);
if (v___x_222_ == 0)
{
lean_object* v___x_223_; lean_object* v___x_224_; uint8_t v___x_225_; 
lean_dec(v_val_221_);
v___x_223_ = lean_array_get_size(v_keyArray_195_);
v___x_224_ = lean_nat_add(v_x_183_, v_one_208_);
lean_dec(v_x_183_);
v___x_225_ = lean_nat_dec_lt(v___x_224_, v___x_223_);
if (v___x_225_ == 0)
{
lean_dec(v___x_224_);
v_x_182_ = v_n_209_;
v_x_183_ = v_zero_184_;
goto _start;
}
else
{
v_x_182_ = v_n_209_;
v_x_183_ = v___x_224_;
goto _start;
}
}
else
{
lean_object* v_val_228_; lean_object* v___x_229_; 
lean_dec(v_n_209_);
lean_dec(v_x_181_);
lean_inc(v___x_219_);
v_val_228_ = lean_noption_get(v___x_219_);
v___x_229_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_229_, 0, v_x_183_);
lean_ctor_set(v___x_229_, 1, v_val_221_);
lean_ctor_set(v___x_229_, 2, v_val_228_);
return v___x_229_;
}
}
}
v___jp_210_:
{
lean_object* v___x_212_; lean_object* v___x_213_; uint8_t v___x_214_; 
v___x_212_ = lean_array_get_size(v_keyArray_195_);
v___x_213_ = lean_nat_add(v_x_183_, v_one_208_);
lean_dec(v_x_183_);
v___x_214_ = lean_nat_dec_lt(v___x_213_, v___x_212_);
if (v___x_214_ == 0)
{
lean_dec(v___x_213_);
v_x_181_ = v___y_211_;
v_x_182_ = v_n_209_;
v_x_183_ = v_zero_184_;
goto _start;
}
else
{
v_x_181_ = v___y_211_;
v_x_182_ = v_n_209_;
v_x_183_ = v___x_213_;
goto _start;
}
}
v___jp_217_:
{
if (lean_obj_tag(v_x_181_) == 0)
{
lean_object* v___x_218_; 
lean_inc(v_x_183_);
v___x_218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_218_, 0, v_x_183_);
v___y_211_ = v___x_218_;
goto v___jp_210_;
}
else
{
v___y_211_ = v_x_181_;
goto v___jp_210_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0_spec__0___redArg___boxed(lean_object* v_m_230_, lean_object* v_query_231_, lean_object* v_x_232_, lean_object* v_x_233_, lean_object* v_x_234_){
_start:
{
lean_object* v_res_235_; 
v_res_235_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0_spec__0___redArg(v_m_230_, v_query_231_, v_x_232_, v_x_233_, v_x_234_);
lean_dec(v_query_231_);
lean_dec_ref(v_m_230_);
return v_res_235_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0___redArg(lean_object* v_m_236_, lean_object* v_query_237_){
_start:
{
lean_object* v_keyArray_238_; lean_object* v___x_239_; uint64_t v___y_241_; 
v_keyArray_238_ = lean_ctor_get(v_m_236_, 1);
v___x_239_ = lean_array_get_size(v_keyArray_238_);
if (lean_obj_tag(v_query_237_) == 0)
{
uint64_t v___x_256_; 
v___x_256_ = 1723ULL;
v___y_241_ = v___x_256_;
goto v___jp_240_;
}
else
{
uint64_t v_hash_257_; 
v_hash_257_ = lean_ctor_get_uint64(v_query_237_, sizeof(void*)*2);
v___y_241_ = v_hash_257_;
goto v___jp_240_;
}
v___jp_240_:
{
uint64_t v___x_242_; uint64_t v___x_243_; uint64_t v_fold_244_; uint64_t v___x_245_; uint64_t v___x_246_; uint64_t v___x_247_; size_t v___x_248_; size_t v___x_249_; size_t v___x_250_; size_t v___x_251_; size_t v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; 
v___x_242_ = 32ULL;
v___x_243_ = lean_uint64_shift_right(v___y_241_, v___x_242_);
v_fold_244_ = lean_uint64_xor(v___y_241_, v___x_243_);
v___x_245_ = 16ULL;
v___x_246_ = lean_uint64_shift_right(v_fold_244_, v___x_245_);
v___x_247_ = lean_uint64_xor(v_fold_244_, v___x_246_);
v___x_248_ = lean_uint64_to_usize(v___x_247_);
v___x_249_ = lean_usize_of_nat(v___x_239_);
v___x_250_ = ((size_t)1ULL);
v___x_251_ = lean_usize_sub(v___x_249_, v___x_250_);
v___x_252_ = lean_usize_land(v___x_248_, v___x_251_);
v___x_253_ = lean_usize_to_nat(v___x_252_);
v___x_254_ = lean_box(0);
v___x_255_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0_spec__0___redArg(v_m_236_, v_query_237_, v___x_254_, v___x_239_, v___x_253_);
return v___x_255_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0___redArg___boxed(lean_object* v_m_258_, lean_object* v_query_259_){
_start:
{
lean_object* v_res_260_; 
v_res_260_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0___redArg(v_m_258_, v_query_259_);
lean_dec(v_query_259_);
lean_dec_ref(v_m_258_);
return v_res_260_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__1_spec__2_spec__3___redArg(lean_object* v_b_261_, lean_object* v_acc_262_, lean_object* v_i_263_){
_start:
{
lean_object* v___y_265_; lean_object* v_keyArray_273_; lean_object* v_valueArray_274_; lean_object* v___x_275_; uint8_t v___x_276_; 
v_keyArray_273_ = lean_ctor_get(v_b_261_, 1);
v_valueArray_274_ = lean_ctor_get(v_b_261_, 2);
v___x_275_ = lean_array_get_size(v_keyArray_273_);
v___x_276_ = lean_nat_dec_lt(v_i_263_, v___x_275_);
if (v___x_276_ == 0)
{
lean_dec(v_i_263_);
return v_acc_262_;
}
else
{
lean_object* v___x_277_; uint8_t v_isSome_278_; 
v___x_277_ = lean_array_fget_borrowed(v_keyArray_273_, v_i_263_);
v_isSome_278_ = lean_noption_is_some(v___x_277_);
if (v_isSome_278_ == 0)
{
goto v___jp_269_;
}
else
{
lean_object* v___x_279_; uint8_t v_isSome_280_; 
v___x_279_ = lean_array_fget_borrowed(v_valueArray_274_, v_i_263_);
v_isSome_280_ = lean_noption_is_some(v___x_279_);
if (v_isSome_280_ == 0)
{
goto v___jp_269_;
}
else
{
lean_object* v_val_281_; lean_object* v_val_282_; lean_object* v_i_284_; lean_object* v___x_289_; 
lean_inc(v___x_277_);
v_val_281_ = lean_noption_get(v___x_277_);
lean_inc(v___x_279_);
v_val_282_ = lean_noption_get(v___x_279_);
v___x_289_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0___redArg(v_acc_262_, v_val_281_);
switch(lean_obj_tag(v___x_289_))
{
case 0:
{
lean_object* v_index_290_; lean_object* v_size_291_; lean_object* v___x_292_; 
v_index_290_ = lean_ctor_get(v___x_289_, 0);
lean_inc(v_index_290_);
lean_dec_ref_known(v___x_289_, 3);
v_size_291_ = lean_ctor_get(v_acc_262_, 0);
lean_inc(v_size_291_);
v___x_292_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_262_, v_size_291_, v_index_290_, v_val_281_, v_val_282_);
lean_dec(v_index_290_);
v___y_265_ = v___x_292_;
goto v___jp_264_;
}
case 1:
{
lean_object* v_index_293_; 
v_index_293_ = lean_ctor_get(v___x_289_, 0);
lean_inc(v_index_293_);
lean_dec_ref_known(v___x_289_, 1);
v_i_284_ = v_index_293_;
goto v___jp_283_;
}
default: 
{
lean_object* v___x_294_; lean_object* v___x_295_; 
v___x_294_ = lean_unsigned_to_nat(0u);
v___x_295_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_262_, v___x_294_);
if (lean_obj_tag(v___x_295_) == 0)
{
lean_object* v_index_296_; 
v_index_296_ = lean_ctor_get(v___x_295_, 0);
lean_inc(v_index_296_);
lean_dec_ref_known(v___x_295_, 1);
v_i_284_ = v_index_296_;
goto v___jp_283_;
}
else
{
lean_dec(v_val_282_);
lean_dec(v_val_281_);
v___y_265_ = v_acc_262_;
goto v___jp_264_;
}
}
}
v___jp_283_:
{
lean_object* v_size_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; 
v_size_285_ = lean_ctor_get(v_acc_262_, 0);
v___x_286_ = lean_unsigned_to_nat(1u);
v___x_287_ = lean_nat_add(v_size_285_, v___x_286_);
v___x_288_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_262_, v___x_287_, v_i_284_, v_val_281_, v_val_282_);
lean_dec(v_i_284_);
v___y_265_ = v___x_288_;
goto v___jp_264_;
}
}
}
}
v___jp_264_:
{
lean_object* v___x_266_; lean_object* v___x_267_; 
v___x_266_ = lean_unsigned_to_nat(1u);
v___x_267_ = lean_nat_add(v_i_263_, v___x_266_);
lean_dec(v_i_263_);
v_acc_262_ = v___y_265_;
v_i_263_ = v___x_267_;
goto _start;
}
v___jp_269_:
{
lean_object* v___x_270_; lean_object* v___x_271_; 
v___x_270_ = lean_unsigned_to_nat(1u);
v___x_271_ = lean_nat_add(v_i_263_, v___x_270_);
lean_dec(v_i_263_);
v_i_263_ = v___x_271_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_b_297_, lean_object* v_acc_298_, lean_object* v_i_299_){
_start:
{
lean_object* v_res_300_; 
v_res_300_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__1_spec__2_spec__3___redArg(v_b_297_, v_acc_298_, v_i_299_);
lean_dec_ref(v_b_297_);
return v_res_300_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__1_spec__2___redArg(lean_object* v_init_301_, lean_object* v_b_302_){
_start:
{
lean_object* v___x_303_; lean_object* v___x_304_; 
v___x_303_ = lean_unsigned_to_nat(0u);
v___x_304_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__1_spec__2_spec__3___redArg(v_b_302_, v_init_301_, v___x_303_);
return v___x_304_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__1_spec__2___redArg___boxed(lean_object* v_init_305_, lean_object* v_b_306_){
_start:
{
lean_object* v_res_307_; 
v_res_307_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__1_spec__2___redArg(v_init_305_, v_b_306_);
lean_dec_ref(v_b_306_);
return v_res_307_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__1___redArg(lean_object* v_m_308_){
_start:
{
lean_object* v_keyArray_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v_cellCount_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v_target_316_; lean_object* v___x_317_; 
v_keyArray_309_ = lean_ctor_get(v_m_308_, 1);
v___x_310_ = lean_array_get_size(v_keyArray_309_);
v___x_311_ = lean_unsigned_to_nat(2u);
v_cellCount_312_ = lean_nat_mul(v___x_310_, v___x_311_);
v___x_313_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_312_);
v___x_314_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_312_);
v___x_315_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_312_);
v_target_316_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_316_, 0, v___x_313_);
lean_ctor_set(v_target_316_, 1, v___x_314_);
lean_ctor_set(v_target_316_, 2, v___x_315_);
v___x_317_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__1_spec__2___redArg(v_target_316_, v_m_308_);
return v___x_317_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__1___redArg___boxed(lean_object* v_m_318_){
_start:
{
lean_object* v_res_319_; 
v_res_319_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__1___redArg(v_m_318_);
lean_dec_ref(v_m_318_);
return v_res_319_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__2(lean_object* v_as_320_, size_t v_i_321_, size_t v_stop_322_, lean_object* v_b_323_){
_start:
{
lean_object* v___y_325_; uint8_t v___x_329_; 
v___x_329_ = lean_usize_dec_eq(v_i_321_, v_stop_322_);
if (v___x_329_ == 0)
{
lean_object* v___x_330_; lean_object* v_head_331_; lean_object* v___y_333_; lean_object* v_i_334_; lean_object* v___y_340_; lean_object* v___y_350_; lean_object* v_i_351_; lean_object* v___x_366_; 
v___x_330_ = lean_array_uget_borrowed(v_as_320_, v_i_321_);
v_head_331_ = lean_ctor_get(v___x_330_, 0);
v___x_366_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0___redArg(v_b_323_, v_head_331_);
switch(lean_obj_tag(v___x_366_))
{
case 0:
{
lean_object* v_index_367_; lean_object* v_size_368_; lean_object* v___x_369_; 
v_index_367_ = lean_ctor_get(v___x_366_, 0);
lean_inc(v_index_367_);
lean_dec_ref_known(v___x_366_, 3);
v_size_368_ = lean_ctor_get(v_b_323_, 0);
lean_inc(v_size_368_);
lean_inc(v___x_330_);
lean_inc(v_head_331_);
v___x_369_ = l_Std_DHashMap_Raw_setEntry___redArg(v_b_323_, v_size_368_, v_index_367_, v_head_331_, v___x_330_);
lean_dec(v_index_367_);
v___y_325_ = v___x_369_;
goto v___jp_324_;
}
case 1:
{
lean_object* v_index_370_; lean_object* v_size_371_; lean_object* v_keyArray_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; uint8_t v___x_376_; 
v_index_370_ = lean_ctor_get(v___x_366_, 0);
lean_inc(v_index_370_);
lean_dec_ref_known(v___x_366_, 1);
v_size_371_ = lean_ctor_get(v_b_323_, 0);
v_keyArray_372_ = lean_ctor_get(v_b_323_, 1);
v___x_373_ = lean_unsigned_to_nat(1u);
v___x_374_ = lean_nat_add(v_size_371_, v___x_373_);
v___x_375_ = lean_array_get_size(v_keyArray_372_);
v___x_376_ = lean_nat_dec_lt(v___x_374_, v___x_375_);
if (v___x_376_ == 0)
{
lean_dec(v___x_374_);
lean_dec(v_index_370_);
goto v___jp_356_;
}
else
{
lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; uint8_t v___x_381_; 
v___x_377_ = lean_unsigned_to_nat(4u);
v___x_378_ = lean_nat_mul(v___x_374_, v___x_377_);
v___x_379_ = lean_unsigned_to_nat(3u);
v___x_380_ = lean_nat_mul(v___x_375_, v___x_379_);
v___x_381_ = lean_nat_dec_le(v___x_378_, v___x_380_);
lean_dec(v___x_380_);
lean_dec(v___x_378_);
if (v___x_381_ == 0)
{
lean_dec(v___x_374_);
lean_dec(v_index_370_);
goto v___jp_356_;
}
else
{
lean_object* v___x_382_; 
lean_inc(v___x_330_);
lean_inc(v_head_331_);
v___x_382_ = l_Std_DHashMap_Raw_setEntry___redArg(v_b_323_, v___x_374_, v_index_370_, v_head_331_, v___x_330_);
lean_dec(v_index_370_);
v___y_325_ = v___x_382_;
goto v___jp_324_;
}
}
}
default: 
{
lean_object* v_size_383_; lean_object* v_keyArray_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; uint8_t v___x_388_; 
v_size_383_ = lean_ctor_get(v_b_323_, 0);
v_keyArray_384_ = lean_ctor_get(v_b_323_, 1);
v___x_385_ = lean_unsigned_to_nat(1u);
v___x_386_ = lean_nat_add(v_size_383_, v___x_385_);
v___x_387_ = lean_array_get_size(v_keyArray_384_);
v___x_388_ = lean_nat_dec_lt(v___x_386_, v___x_387_);
if (v___x_388_ == 0)
{
lean_object* v___x_389_; 
lean_dec(v___x_386_);
v___x_389_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__1___redArg(v_b_323_);
lean_dec_ref(v_b_323_);
v___y_340_ = v___x_389_;
goto v___jp_339_;
}
else
{
lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; uint8_t v___x_394_; 
v___x_390_ = lean_unsigned_to_nat(4u);
v___x_391_ = lean_nat_mul(v___x_386_, v___x_390_);
lean_dec(v___x_386_);
v___x_392_ = lean_unsigned_to_nat(3u);
v___x_393_ = lean_nat_mul(v___x_387_, v___x_392_);
v___x_394_ = lean_nat_dec_le(v___x_391_, v___x_393_);
lean_dec(v___x_393_);
lean_dec(v___x_391_);
if (v___x_394_ == 0)
{
lean_object* v___x_395_; 
v___x_395_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__1___redArg(v_b_323_);
lean_dec_ref(v_b_323_);
v___y_340_ = v___x_395_;
goto v___jp_339_;
}
else
{
v___y_340_ = v_b_323_;
goto v___jp_339_;
}
}
}
}
v___jp_332_:
{
lean_object* v_size_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; 
v_size_335_ = lean_ctor_get(v___y_333_, 0);
v___x_336_ = lean_unsigned_to_nat(1u);
v___x_337_ = lean_nat_add(v_size_335_, v___x_336_);
lean_inc(v___x_330_);
lean_inc(v_head_331_);
v___x_338_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_333_, v___x_337_, v_i_334_, v_head_331_, v___x_330_);
lean_dec(v_i_334_);
v___y_325_ = v___x_338_;
goto v___jp_324_;
}
v___jp_339_:
{
lean_object* v___x_341_; 
v___x_341_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0___redArg(v___y_340_, v_head_331_);
switch(lean_obj_tag(v___x_341_))
{
case 0:
{
lean_object* v_index_342_; lean_object* v_size_343_; lean_object* v___x_344_; 
v_index_342_ = lean_ctor_get(v___x_341_, 0);
lean_inc(v_index_342_);
lean_dec_ref_known(v___x_341_, 3);
v_size_343_ = lean_ctor_get(v___y_340_, 0);
lean_inc(v_size_343_);
lean_inc(v___x_330_);
lean_inc(v_head_331_);
v___x_344_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_340_, v_size_343_, v_index_342_, v_head_331_, v___x_330_);
lean_dec(v_index_342_);
v___y_325_ = v___x_344_;
goto v___jp_324_;
}
case 1:
{
lean_object* v_index_345_; 
v_index_345_ = lean_ctor_get(v___x_341_, 0);
lean_inc(v_index_345_);
lean_dec_ref_known(v___x_341_, 1);
v___y_333_ = v___y_340_;
v_i_334_ = v_index_345_;
goto v___jp_332_;
}
default: 
{
lean_object* v___x_346_; lean_object* v___x_347_; 
v___x_346_ = lean_unsigned_to_nat(0u);
v___x_347_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_340_, v___x_346_);
if (lean_obj_tag(v___x_347_) == 0)
{
lean_object* v_index_348_; 
v_index_348_ = lean_ctor_get(v___x_347_, 0);
lean_inc(v_index_348_);
lean_dec_ref_known(v___x_347_, 1);
v___y_333_ = v___y_340_;
v_i_334_ = v_index_348_;
goto v___jp_332_;
}
else
{
v___y_325_ = v___y_340_;
goto v___jp_324_;
}
}
}
}
v___jp_349_:
{
lean_object* v_size_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; 
v_size_352_ = lean_ctor_get(v___y_350_, 0);
v___x_353_ = lean_unsigned_to_nat(1u);
v___x_354_ = lean_nat_add(v_size_352_, v___x_353_);
lean_inc(v___x_330_);
lean_inc(v_head_331_);
v___x_355_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_350_, v___x_354_, v_i_351_, v_head_331_, v___x_330_);
lean_dec(v_i_351_);
v___y_325_ = v___x_355_;
goto v___jp_324_;
}
v___jp_356_:
{
lean_object* v___x_357_; lean_object* v___x_358_; 
v___x_357_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__1___redArg(v_b_323_);
lean_dec_ref(v_b_323_);
v___x_358_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0___redArg(v___x_357_, v_head_331_);
switch(lean_obj_tag(v___x_358_))
{
case 0:
{
lean_object* v_index_359_; lean_object* v_size_360_; lean_object* v___x_361_; 
v_index_359_ = lean_ctor_get(v___x_358_, 0);
lean_inc(v_index_359_);
lean_dec_ref_known(v___x_358_, 3);
v_size_360_ = lean_ctor_get(v___x_357_, 0);
lean_inc(v_size_360_);
lean_inc(v___x_330_);
lean_inc(v_head_331_);
v___x_361_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_357_, v_size_360_, v_index_359_, v_head_331_, v___x_330_);
lean_dec(v_index_359_);
v___y_325_ = v___x_361_;
goto v___jp_324_;
}
case 1:
{
lean_object* v_index_362_; 
v_index_362_ = lean_ctor_get(v___x_358_, 0);
lean_inc(v_index_362_);
lean_dec_ref_known(v___x_358_, 1);
v___y_350_ = v___x_357_;
v_i_351_ = v_index_362_;
goto v___jp_349_;
}
default: 
{
lean_object* v___x_363_; lean_object* v___x_364_; 
v___x_363_ = lean_unsigned_to_nat(0u);
v___x_364_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_357_, v___x_363_);
if (lean_obj_tag(v___x_364_) == 0)
{
lean_object* v_index_365_; 
v_index_365_ = lean_ctor_get(v___x_364_, 0);
lean_inc(v_index_365_);
lean_dec_ref_known(v___x_364_, 1);
v___y_350_ = v___x_357_;
v_i_351_ = v_index_365_;
goto v___jp_349_;
}
else
{
v___y_325_ = v___x_357_;
goto v___jp_324_;
}
}
}
}
}
else
{
return v_b_323_;
}
v___jp_324_:
{
size_t v___x_326_; size_t v___x_327_; 
v___x_326_ = ((size_t)1ULL);
v___x_327_ = lean_usize_add(v_i_321_, v___x_326_);
v_i_321_ = v___x_327_;
v_b_323_ = v___y_325_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__2___boxed(lean_object* v_as_396_, lean_object* v_i_397_, lean_object* v_stop_398_, lean_object* v_b_399_){
_start:
{
size_t v_i_boxed_400_; size_t v_stop_boxed_401_; lean_object* v_res_402_; 
v_i_boxed_400_ = lean_unbox_usize(v_i_397_);
lean_dec(v_i_397_);
v_stop_boxed_401_ = lean_unbox_usize(v_stop_398_);
lean_dec(v_stop_398_);
v_res_402_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__2(v_as_396_, v_i_boxed_400_, v_stop_boxed_401_, v_b_399_);
lean_dec_ref(v_as_396_);
return v_res_402_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_latticeOps___closed__0(void){
_start:
{
lean_object* v_cellCount_403_; lean_object* v___x_404_; 
v_cellCount_403_ = lean_unsigned_to_nat(16u);
v___x_404_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_403_);
return v___x_404_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_latticeOps___closed__1(void){
_start:
{
lean_object* v_cellCount_405_; lean_object* v___x_406_; 
v_cellCount_405_ = lean_unsigned_to_nat(16u);
v___x_406_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_405_);
return v___x_406_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_latticeOps___closed__2(void){
_start:
{
lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; 
v___x_407_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_latticeOps___closed__1, &l_Lean_Elab_Tactic_VCGen_latticeOps___closed__1_once, _init_l_Lean_Elab_Tactic_VCGen_latticeOps___closed__1);
v___x_408_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_latticeOps___closed__0, &l_Lean_Elab_Tactic_VCGen_latticeOps___closed__0_once, _init_l_Lean_Elab_Tactic_VCGen_latticeOps___closed__0);
v___x_409_ = lean_unsigned_to_nat(0u);
v___x_410_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_410_, 0, v___x_409_);
lean_ctor_set(v___x_410_, 1, v___x_408_);
lean_ctor_set(v___x_410_, 2, v___x_407_);
return v___x_410_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_latticeOps___closed__3(void){
_start:
{
lean_object* v___x_411_; lean_object* v___x_412_; 
v___x_411_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_builtinLatticeOps));
v___x_412_ = lean_array_get_size(v___x_411_);
return v___x_412_;
}
}
static uint8_t _init_l_Lean_Elab_Tactic_VCGen_latticeOps___closed__4(void){
_start:
{
lean_object* v___x_413_; lean_object* v___x_414_; uint8_t v___x_415_; 
v___x_413_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_latticeOps___closed__3, &l_Lean_Elab_Tactic_VCGen_latticeOps___closed__3_once, _init_l_Lean_Elab_Tactic_VCGen_latticeOps___closed__3);
v___x_414_ = lean_unsigned_to_nat(0u);
v___x_415_ = lean_nat_dec_lt(v___x_414_, v___x_413_);
return v___x_415_;
}
}
static uint8_t _init_l_Lean_Elab_Tactic_VCGen_latticeOps___closed__5(void){
_start:
{
lean_object* v___x_416_; uint8_t v___x_417_; 
v___x_416_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_latticeOps___closed__3, &l_Lean_Elab_Tactic_VCGen_latticeOps___closed__3_once, _init_l_Lean_Elab_Tactic_VCGen_latticeOps___closed__3);
v___x_417_ = lean_nat_dec_le(v___x_416_, v___x_416_);
return v___x_417_;
}
}
static size_t _init_l_Lean_Elab_Tactic_VCGen_latticeOps___closed__6(void){
_start:
{
lean_object* v___x_418_; size_t v___x_419_; 
v___x_418_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_latticeOps___closed__3, &l_Lean_Elab_Tactic_VCGen_latticeOps___closed__3_once, _init_l_Lean_Elab_Tactic_VCGen_latticeOps___closed__3);
v___x_419_ = lean_usize_of_nat(v___x_418_);
return v___x_419_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_latticeOps___closed__7(void){
_start:
{
lean_object* v___x_420_; size_t v___x_421_; size_t v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; 
v___x_420_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_latticeOps___closed__2, &l_Lean_Elab_Tactic_VCGen_latticeOps___closed__2_once, _init_l_Lean_Elab_Tactic_VCGen_latticeOps___closed__2);
v___x_421_ = lean_usize_once(&l_Lean_Elab_Tactic_VCGen_latticeOps___closed__6, &l_Lean_Elab_Tactic_VCGen_latticeOps___closed__6_once, _init_l_Lean_Elab_Tactic_VCGen_latticeOps___closed__6);
v___x_422_ = ((size_t)0ULL);
v___x_423_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_builtinLatticeOps));
v___x_424_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__2(v___x_423_, v___x_422_, v___x_421_, v___x_420_);
return v___x_424_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_latticeOps(void){
_start:
{
lean_object* v___x_425_; uint8_t v___x_426_; 
v___x_425_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_latticeOps___closed__2, &l_Lean_Elab_Tactic_VCGen_latticeOps___closed__2_once, _init_l_Lean_Elab_Tactic_VCGen_latticeOps___closed__2);
v___x_426_ = lean_uint8_once(&l_Lean_Elab_Tactic_VCGen_latticeOps___closed__4, &l_Lean_Elab_Tactic_VCGen_latticeOps___closed__4_once, _init_l_Lean_Elab_Tactic_VCGen_latticeOps___closed__4);
if (v___x_426_ == 0)
{
return v___x_425_;
}
else
{
uint8_t v___x_427_; 
v___x_427_ = lean_uint8_once(&l_Lean_Elab_Tactic_VCGen_latticeOps___closed__5, &l_Lean_Elab_Tactic_VCGen_latticeOps___closed__5_once, _init_l_Lean_Elab_Tactic_VCGen_latticeOps___closed__5);
if (v___x_427_ == 0)
{
if (v___x_426_ == 0)
{
return v___x_425_;
}
else
{
lean_object* v___x_428_; 
v___x_428_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_latticeOps___closed__7, &l_Lean_Elab_Tactic_VCGen_latticeOps___closed__7_once, _init_l_Lean_Elab_Tactic_VCGen_latticeOps___closed__7);
return v___x_428_;
}
}
else
{
lean_object* v___x_429_; 
v___x_429_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_latticeOps___closed__7, &l_Lean_Elab_Tactic_VCGen_latticeOps___closed__7_once, _init_l_Lean_Elab_Tactic_VCGen_latticeOps___closed__7);
return v___x_429_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0(lean_object* v_00_u03b2_430_, lean_object* v_m_431_, lean_object* v_query_432_){
_start:
{
lean_object* v___x_433_; 
v___x_433_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0___redArg(v_m_431_, v_query_432_);
return v___x_433_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0___boxed(lean_object* v_00_u03b2_434_, lean_object* v_m_435_, lean_object* v_query_436_){
_start:
{
lean_object* v_res_437_; 
v_res_437_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0(v_00_u03b2_434_, v_m_435_, v_query_436_);
lean_dec(v_query_436_);
lean_dec_ref(v_m_435_);
return v_res_437_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__1(lean_object* v_00_u03b2_438_, lean_object* v_m_439_){
_start:
{
lean_object* v___x_440_; 
v___x_440_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__1___redArg(v_m_439_);
return v___x_440_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__1___boxed(lean_object* v_00_u03b2_441_, lean_object* v_m_442_){
_start:
{
lean_object* v_res_443_; 
v_res_443_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__1(v_00_u03b2_441_, v_m_442_);
lean_dec_ref(v_m_442_);
return v_res_443_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0_spec__0(lean_object* v_00_u03b2_444_, lean_object* v_m_445_, lean_object* v_query_446_, lean_object* v_x_447_, lean_object* v_x_448_, lean_object* v_x_449_, lean_object* v_x_450_){
_start:
{
lean_object* v___x_451_; 
v___x_451_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0_spec__0___redArg(v_m_445_, v_query_446_, v_x_447_, v_x_448_, v_x_449_);
return v___x_451_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0_spec__0___boxed(lean_object* v_00_u03b2_452_, lean_object* v_m_453_, lean_object* v_query_454_, lean_object* v_x_455_, lean_object* v_x_456_, lean_object* v_x_457_, lean_object* v_x_458_){
_start:
{
lean_object* v_res_459_; 
v_res_459_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0_spec__0(v_00_u03b2_452_, v_m_453_, v_query_454_, v_x_455_, v_x_456_, v_x_457_, v_x_458_);
lean_dec(v_query_454_);
lean_dec_ref(v_m_453_);
return v_res_459_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__1_spec__2(lean_object* v_00_u03b2_460_, lean_object* v_init_461_, lean_object* v_b_462_){
_start:
{
lean_object* v___x_463_; 
v___x_463_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__1_spec__2___redArg(v_init_461_, v_b_462_);
return v___x_463_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__1_spec__2___boxed(lean_object* v_00_u03b2_464_, lean_object* v_init_465_, lean_object* v_b_466_){
_start:
{
lean_object* v_res_467_; 
v_res_467_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__1_spec__2(v_00_u03b2_464_, v_init_465_, v_b_466_);
lean_dec_ref(v_b_466_);
return v_res_467_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_468_, lean_object* v_b_469_, lean_object* v_acc_470_, lean_object* v_i_471_){
_start:
{
lean_object* v___x_472_; 
v___x_472_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__1_spec__2_spec__3___redArg(v_b_469_, v_acc_470_, v_i_471_);
return v___x_472_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__1_spec__2_spec__3___boxed(lean_object* v_00_u03b2_473_, lean_object* v_b_474_, lean_object* v_acc_475_, lean_object* v_i_476_){
_start:
{
lean_object* v_res_477_; 
v_res_477_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__1_spec__2_spec__3(v_00_u03b2_473_, v_b_474_, v_acc_475_, v_i_476_);
lean_dec_ref(v_b_474_);
return v_res_477_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__0___redArg(lean_object* v_e_478_, lean_object* v___y_479_){
_start:
{
uint8_t v___x_481_; 
v___x_481_ = l_Lean_Expr_hasMVar(v_e_478_);
if (v___x_481_ == 0)
{
lean_object* v___x_482_; 
v___x_482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_482_, 0, v_e_478_);
return v___x_482_;
}
else
{
lean_object* v___x_483_; lean_object* v_mctx_484_; lean_object* v___x_485_; lean_object* v_fst_486_; lean_object* v_snd_487_; lean_object* v___x_488_; lean_object* v_cache_489_; lean_object* v_zetaDeltaFVarIds_490_; lean_object* v_postponed_491_; lean_object* v_diag_492_; lean_object* v___x_494_; uint8_t v_isShared_495_; uint8_t v_isSharedCheck_501_; 
v___x_483_ = lean_st_ref_get(v___y_479_);
v_mctx_484_ = lean_ctor_get(v___x_483_, 0);
lean_inc_ref(v_mctx_484_);
lean_dec(v___x_483_);
v___x_485_ = l_Lean_instantiateMVarsCore(v_mctx_484_, v_e_478_);
v_fst_486_ = lean_ctor_get(v___x_485_, 0);
lean_inc(v_fst_486_);
v_snd_487_ = lean_ctor_get(v___x_485_, 1);
lean_inc(v_snd_487_);
lean_dec_ref(v___x_485_);
v___x_488_ = lean_st_ref_take(v___y_479_);
v_cache_489_ = lean_ctor_get(v___x_488_, 1);
v_zetaDeltaFVarIds_490_ = lean_ctor_get(v___x_488_, 2);
v_postponed_491_ = lean_ctor_get(v___x_488_, 3);
v_diag_492_ = lean_ctor_get(v___x_488_, 4);
v_isSharedCheck_501_ = !lean_is_exclusive(v___x_488_);
if (v_isSharedCheck_501_ == 0)
{
lean_object* v_unused_502_; 
v_unused_502_ = lean_ctor_get(v___x_488_, 0);
lean_dec(v_unused_502_);
v___x_494_ = v___x_488_;
v_isShared_495_ = v_isSharedCheck_501_;
goto v_resetjp_493_;
}
else
{
lean_inc(v_diag_492_);
lean_inc(v_postponed_491_);
lean_inc(v_zetaDeltaFVarIds_490_);
lean_inc(v_cache_489_);
lean_dec(v___x_488_);
v___x_494_ = lean_box(0);
v_isShared_495_ = v_isSharedCheck_501_;
goto v_resetjp_493_;
}
v_resetjp_493_:
{
lean_object* v___x_497_; 
if (v_isShared_495_ == 0)
{
lean_ctor_set(v___x_494_, 0, v_snd_487_);
v___x_497_ = v___x_494_;
goto v_reusejp_496_;
}
else
{
lean_object* v_reuseFailAlloc_500_; 
v_reuseFailAlloc_500_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_500_, 0, v_snd_487_);
lean_ctor_set(v_reuseFailAlloc_500_, 1, v_cache_489_);
lean_ctor_set(v_reuseFailAlloc_500_, 2, v_zetaDeltaFVarIds_490_);
lean_ctor_set(v_reuseFailAlloc_500_, 3, v_postponed_491_);
lean_ctor_set(v_reuseFailAlloc_500_, 4, v_diag_492_);
v___x_497_ = v_reuseFailAlloc_500_;
goto v_reusejp_496_;
}
v_reusejp_496_:
{
lean_object* v___x_498_; lean_object* v___x_499_; 
v___x_498_ = lean_st_ref_put(v___y_479_, v___x_497_);
v___x_499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_499_, 0, v_fst_486_);
return v___x_499_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__0___redArg___boxed(lean_object* v_e_503_, lean_object* v___y_504_, lean_object* v___y_505_){
_start:
{
lean_object* v_res_506_; 
v_res_506_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__0___redArg(v_e_503_, v___y_504_);
lean_dec(v___y_504_);
return v_res_506_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__0(lean_object* v_e_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_){
_start:
{
lean_object* v___x_513_; 
v___x_513_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__0___redArg(v_e_507_, v___y_509_);
return v___x_513_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__0___boxed(lean_object* v_e_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_){
_start:
{
lean_object* v_res_520_; 
v_res_520_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__0(v_e_514_, v___y_515_, v___y_516_, v___y_517_, v___y_518_);
lean_dec(v___y_518_);
lean_dec_ref(v___y_517_);
lean_dec(v___y_516_);
lean_dec_ref(v___y_515_);
return v_res_520_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__1_spec__1(lean_object* v_msgData_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_){
_start:
{
lean_object* v___x_527_; lean_object* v_env_528_; lean_object* v___x_529_; lean_object* v_mctx_530_; lean_object* v_lctx_531_; lean_object* v_options_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; 
v___x_527_ = lean_st_ref_get(v___y_525_);
v_env_528_ = lean_ctor_get(v___x_527_, 0);
lean_inc_ref(v_env_528_);
lean_dec(v___x_527_);
v___x_529_ = lean_st_ref_get(v___y_523_);
v_mctx_530_ = lean_ctor_get(v___x_529_, 0);
lean_inc_ref(v_mctx_530_);
lean_dec(v___x_529_);
v_lctx_531_ = lean_ctor_get(v___y_522_, 2);
v_options_532_ = lean_ctor_get(v___y_524_, 2);
lean_inc_ref(v_options_532_);
lean_inc_ref(v_lctx_531_);
v___x_533_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_533_, 0, v_env_528_);
lean_ctor_set(v___x_533_, 1, v_mctx_530_);
lean_ctor_set(v___x_533_, 2, v_lctx_531_);
lean_ctor_set(v___x_533_, 3, v_options_532_);
v___x_534_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_534_, 0, v___x_533_);
lean_ctor_set(v___x_534_, 1, v_msgData_521_);
v___x_535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_535_, 0, v___x_534_);
return v___x_535_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__1_spec__1___boxed(lean_object* v_msgData_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_){
_start:
{
lean_object* v_res_542_; 
v_res_542_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__1_spec__1(v_msgData_536_, v___y_537_, v___y_538_, v___y_539_, v___y_540_);
lean_dec(v___y_540_);
lean_dec_ref(v___y_539_);
lean_dec(v___y_538_);
lean_dec_ref(v___y_537_);
return v_res_542_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__1___redArg(lean_object* v_msg_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_){
_start:
{
lean_object* v_ref_549_; lean_object* v___x_550_; lean_object* v_a_551_; lean_object* v___x_553_; uint8_t v_isShared_554_; uint8_t v_isSharedCheck_559_; 
v_ref_549_ = lean_ctor_get(v___y_546_, 5);
v___x_550_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__1_spec__1(v_msg_543_, v___y_544_, v___y_545_, v___y_546_, v___y_547_);
v_a_551_ = lean_ctor_get(v___x_550_, 0);
v_isSharedCheck_559_ = !lean_is_exclusive(v___x_550_);
if (v_isSharedCheck_559_ == 0)
{
v___x_553_ = v___x_550_;
v_isShared_554_ = v_isSharedCheck_559_;
goto v_resetjp_552_;
}
else
{
lean_inc(v_a_551_);
lean_dec(v___x_550_);
v___x_553_ = lean_box(0);
v_isShared_554_ = v_isSharedCheck_559_;
goto v_resetjp_552_;
}
v_resetjp_552_:
{
lean_object* v___x_555_; lean_object* v___x_557_; 
lean_inc(v_ref_549_);
v___x_555_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_555_, 0, v_ref_549_);
lean_ctor_set(v___x_555_, 1, v_a_551_);
if (v_isShared_554_ == 0)
{
lean_ctor_set_tag(v___x_553_, 1);
lean_ctor_set(v___x_553_, 0, v___x_555_);
v___x_557_ = v___x_553_;
goto v_reusejp_556_;
}
else
{
lean_object* v_reuseFailAlloc_558_; 
v_reuseFailAlloc_558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_558_, 0, v___x_555_);
v___x_557_ = v_reuseFailAlloc_558_;
goto v_reusejp_556_;
}
v_reusejp_556_:
{
return v___x_557_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__1___redArg___boxed(lean_object* v_msg_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_){
_start:
{
lean_object* v_res_566_; 
v_res_566_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__1___redArg(v_msg_560_, v___y_561_, v___y_562_, v___y_563_, v___y_564_);
lean_dec(v___y_564_);
lean_dec_ref(v___y_563_);
lean_dec(v___y_562_);
lean_dec_ref(v___y_561_);
return v_res_566_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__4(void){
_start:
{
lean_object* v___x_575_; lean_object* v___x_576_; 
v___x_575_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__3));
v___x_576_ = l_Lean_stringToMessageData(v___x_575_);
return v___x_576_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__6(void){
_start:
{
lean_object* v___x_578_; lean_object* v___x_579_; 
v___x_578_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__5));
v___x_579_ = l_Lean_stringToMessageData(v___x_578_);
return v___x_579_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__8(void){
_start:
{
lean_object* v___x_581_; lean_object* v___x_582_; 
v___x_581_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__7));
v___x_582_ = l_Lean_stringToMessageData(v___x_581_);
return v___x_582_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2(lean_object* v_as_583_, size_t v_sz_584_, size_t v_i_585_, lean_object* v_b_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_){
_start:
{
lean_object* v_a_593_; uint8_t v___x_597_; 
v___x_597_ = lean_usize_dec_lt(v_i_585_, v_sz_584_);
if (v___x_597_ == 0)
{
lean_object* v___x_598_; 
v___x_598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_598_, 0, v_b_586_);
return v___x_598_;
}
else
{
lean_object* v_a_599_; lean_object* v___x_600_; 
v_a_599_ = lean_array_uget_borrowed(v_as_583_, v_i_585_);
lean_inc(v_a_599_);
v___x_600_ = l_Lean_Meta_mkConstWithFreshMVarLevels(v_a_599_, v___y_587_, v___y_588_, v___y_589_, v___y_590_);
if (lean_obj_tag(v___x_600_) == 0)
{
lean_object* v_a_601_; lean_object* v___x_602_; 
v_a_601_ = lean_ctor_get(v___x_600_, 0);
lean_inc(v_a_601_);
lean_dec_ref_known(v___x_600_, 1);
lean_inc(v___y_590_);
lean_inc_ref(v___y_589_);
lean_inc(v___y_588_);
lean_inc_ref(v___y_587_);
v___x_602_ = lean_infer_type(v_a_601_, v___y_587_, v___y_588_, v___y_589_, v___y_590_);
if (lean_obj_tag(v___x_602_) == 0)
{
lean_object* v_a_603_; lean_object* v___x_604_; uint8_t v___x_605_; lean_object* v___x_606_; 
v_a_603_ = lean_ctor_get(v___x_602_, 0);
lean_inc(v_a_603_);
lean_dec_ref_known(v___x_602_, 1);
v___x_604_ = lean_box(0);
v___x_605_ = 0;
v___x_606_ = l_Lean_Meta_forallMetaTelescopeReducing(v_a_603_, v___x_604_, v___x_605_, v___y_587_, v___y_588_, v___y_589_, v___y_590_);
if (lean_obj_tag(v___x_606_) == 0)
{
lean_object* v_a_607_; lean_object* v_snd_608_; lean_object* v___x_610_; uint8_t v_isShared_611_; uint8_t v_isSharedCheck_733_; 
v_a_607_ = lean_ctor_get(v___x_606_, 0);
lean_inc(v_a_607_);
lean_dec_ref_known(v___x_606_, 1);
v_snd_608_ = lean_ctor_get(v_a_607_, 1);
v_isSharedCheck_733_ = !lean_is_exclusive(v_a_607_);
if (v_isSharedCheck_733_ == 0)
{
lean_object* v_unused_734_; 
v_unused_734_ = lean_ctor_get(v_a_607_, 0);
lean_dec(v_unused_734_);
v___x_610_ = v_a_607_;
v_isShared_611_ = v_isSharedCheck_733_;
goto v_resetjp_609_;
}
else
{
lean_inc(v_snd_608_);
lean_dec(v_a_607_);
v___x_610_ = lean_box(0);
v_isShared_611_ = v_isSharedCheck_733_;
goto v_resetjp_609_;
}
v_resetjp_609_:
{
lean_object* v_snd_612_; lean_object* v___x_614_; uint8_t v_isShared_615_; uint8_t v_isSharedCheck_731_; 
v_snd_612_ = lean_ctor_get(v_snd_608_, 1);
v_isSharedCheck_731_ = !lean_is_exclusive(v_snd_608_);
if (v_isSharedCheck_731_ == 0)
{
lean_object* v_unused_732_; 
v_unused_732_ = lean_ctor_get(v_snd_608_, 0);
lean_dec(v_unused_732_);
v___x_614_ = v_snd_608_;
v_isShared_615_ = v_isSharedCheck_731_;
goto v_resetjp_613_;
}
else
{
lean_inc(v_snd_612_);
lean_dec(v_snd_608_);
v___x_614_ = lean_box(0);
v_isShared_615_ = v_isSharedCheck_731_;
goto v_resetjp_613_;
}
v_resetjp_613_:
{
lean_object* v___x_616_; 
v___x_616_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__0___redArg(v_snd_612_, v___y_588_);
if (lean_obj_tag(v___x_616_) == 0)
{
lean_object* v_a_617_; lean_object* v___x_618_; lean_object* v___x_619_; uint8_t v___x_620_; 
v_a_617_ = lean_ctor_get(v___x_616_, 0);
lean_inc(v_a_617_);
lean_dec_ref_known(v___x_616_, 1);
v___x_618_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__2));
v___x_619_ = lean_unsigned_to_nat(4u);
v___x_620_ = l_Lean_Expr_isAppOfArity(v_a_617_, v___x_618_, v___x_619_);
if (v___x_620_ == 0)
{
lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_624_; 
lean_dec(v_a_617_);
lean_del_object(v___x_614_);
v___x_621_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__4);
lean_inc(v_a_599_);
v___x_622_ = l_Lean_MessageData_ofName(v_a_599_);
if (v_isShared_611_ == 0)
{
lean_ctor_set_tag(v___x_610_, 7);
lean_ctor_set(v___x_610_, 1, v___x_622_);
lean_ctor_set(v___x_610_, 0, v___x_621_);
v___x_624_ = v___x_610_;
goto v_reusejp_623_;
}
else
{
lean_object* v_reuseFailAlloc_636_; 
v_reuseFailAlloc_636_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_636_, 0, v___x_621_);
lean_ctor_set(v_reuseFailAlloc_636_, 1, v___x_622_);
v___x_624_ = v_reuseFailAlloc_636_;
goto v_reusejp_623_;
}
v_reusejp_623_:
{
lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; 
v___x_625_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__6);
v___x_626_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_626_, 0, v___x_624_);
lean_ctor_set(v___x_626_, 1, v___x_625_);
v___x_627_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__1___redArg(v___x_626_, v___y_587_, v___y_588_, v___y_589_, v___y_590_);
if (lean_obj_tag(v___x_627_) == 0)
{
lean_dec_ref_known(v___x_627_, 1);
v_a_593_ = v_b_586_;
goto v___jp_592_;
}
else
{
lean_object* v_a_628_; lean_object* v___x_630_; uint8_t v_isShared_631_; uint8_t v_isSharedCheck_635_; 
lean_dec_ref(v_b_586_);
v_a_628_ = lean_ctor_get(v___x_627_, 0);
v_isSharedCheck_635_ = !lean_is_exclusive(v___x_627_);
if (v_isSharedCheck_635_ == 0)
{
v___x_630_ = v___x_627_;
v_isShared_631_ = v_isSharedCheck_635_;
goto v_resetjp_629_;
}
else
{
lean_inc(v_a_628_);
lean_dec(v___x_627_);
v___x_630_ = lean_box(0);
v_isShared_631_ = v_isSharedCheck_635_;
goto v_resetjp_629_;
}
v_resetjp_629_:
{
lean_object* v___x_633_; 
if (v_isShared_631_ == 0)
{
v___x_633_ = v___x_630_;
goto v_reusejp_632_;
}
else
{
lean_object* v_reuseFailAlloc_634_; 
v_reuseFailAlloc_634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_634_, 0, v_a_628_);
v___x_633_ = v_reuseFailAlloc_634_;
goto v_reusejp_632_;
}
v_reusejp_632_:
{
return v___x_633_;
}
}
}
}
}
else
{
lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; 
v___x_637_ = l_Lean_Expr_appArg_x21(v_a_617_);
lean_dec(v_a_617_);
v___x_638_ = l_Lean_Expr_getAppFn(v___x_637_);
v___x_639_ = l_Lean_Expr_constName_x3f(v___x_638_);
lean_dec_ref(v___x_638_);
if (lean_obj_tag(v___x_639_) == 1)
{
lean_object* v_val_640_; lean_object* v___x_641_; lean_object* v___x_643_; 
lean_del_object(v___x_610_);
v_val_640_ = lean_ctor_get(v___x_639_, 0);
lean_inc(v_val_640_);
lean_dec_ref_known(v___x_639_, 1);
v___x_641_ = l_Lean_Expr_getAppNumArgs(v___x_637_);
lean_dec_ref(v___x_637_);
lean_inc(v_a_599_);
if (v_isShared_615_ == 0)
{
lean_ctor_set(v___x_614_, 1, v___x_641_);
lean_ctor_set(v___x_614_, 0, v_a_599_);
v___x_643_ = v___x_614_;
goto v_reusejp_642_;
}
else
{
lean_object* v_reuseFailAlloc_706_; 
v_reuseFailAlloc_706_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_706_, 0, v_a_599_);
lean_ctor_set(v_reuseFailAlloc_706_, 1, v___x_641_);
v___x_643_ = v_reuseFailAlloc_706_;
goto v_reusejp_642_;
}
v_reusejp_642_:
{
lean_object* v___y_645_; lean_object* v_i_646_; lean_object* v___y_652_; lean_object* v___y_662_; lean_object* v_i_663_; lean_object* v___x_678_; 
v___x_678_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0___redArg(v_b_586_, v_val_640_);
switch(lean_obj_tag(v___x_678_))
{
case 0:
{
lean_object* v_index_679_; lean_object* v_size_680_; lean_object* v___x_681_; 
v_index_679_ = lean_ctor_get(v___x_678_, 0);
lean_inc(v_index_679_);
lean_dec_ref_known(v___x_678_, 3);
v_size_680_ = lean_ctor_get(v_b_586_, 0);
lean_inc(v_size_680_);
v___x_681_ = l_Std_DHashMap_Raw_setEntry___redArg(v_b_586_, v_size_680_, v_index_679_, v_val_640_, v___x_643_);
lean_dec(v_index_679_);
v_a_593_ = v___x_681_;
goto v___jp_592_;
}
case 1:
{
lean_object* v_index_682_; lean_object* v_size_683_; lean_object* v_keyArray_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; uint8_t v___x_688_; 
v_index_682_ = lean_ctor_get(v___x_678_, 0);
lean_inc(v_index_682_);
lean_dec_ref_known(v___x_678_, 1);
v_size_683_ = lean_ctor_get(v_b_586_, 0);
v_keyArray_684_ = lean_ctor_get(v_b_586_, 1);
v___x_685_ = lean_unsigned_to_nat(1u);
v___x_686_ = lean_nat_add(v_size_683_, v___x_685_);
v___x_687_ = lean_array_get_size(v_keyArray_684_);
v___x_688_ = lean_nat_dec_lt(v___x_686_, v___x_687_);
if (v___x_688_ == 0)
{
lean_dec(v___x_686_);
lean_dec(v_index_682_);
goto v___jp_668_;
}
else
{
lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; uint8_t v___x_692_; 
v___x_689_ = lean_nat_mul(v___x_686_, v___x_619_);
v___x_690_ = lean_unsigned_to_nat(3u);
v___x_691_ = lean_nat_mul(v___x_687_, v___x_690_);
v___x_692_ = lean_nat_dec_le(v___x_689_, v___x_691_);
lean_dec(v___x_691_);
lean_dec(v___x_689_);
if (v___x_692_ == 0)
{
lean_dec(v___x_686_);
lean_dec(v_index_682_);
goto v___jp_668_;
}
else
{
lean_object* v___x_693_; 
v___x_693_ = l_Std_DHashMap_Raw_setEntry___redArg(v_b_586_, v___x_686_, v_index_682_, v_val_640_, v___x_643_);
lean_dec(v_index_682_);
v_a_593_ = v___x_693_;
goto v___jp_592_;
}
}
}
default: 
{
lean_object* v_size_694_; lean_object* v_keyArray_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; uint8_t v___x_699_; 
v_size_694_ = lean_ctor_get(v_b_586_, 0);
v_keyArray_695_ = lean_ctor_get(v_b_586_, 1);
v___x_696_ = lean_unsigned_to_nat(1u);
v___x_697_ = lean_nat_add(v_size_694_, v___x_696_);
v___x_698_ = lean_array_get_size(v_keyArray_695_);
v___x_699_ = lean_nat_dec_lt(v___x_697_, v___x_698_);
if (v___x_699_ == 0)
{
lean_object* v___x_700_; 
lean_dec(v___x_697_);
v___x_700_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__1___redArg(v_b_586_);
lean_dec_ref(v_b_586_);
v___y_652_ = v___x_700_;
goto v___jp_651_;
}
else
{
lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; uint8_t v___x_704_; 
v___x_701_ = lean_nat_mul(v___x_697_, v___x_619_);
lean_dec(v___x_697_);
v___x_702_ = lean_unsigned_to_nat(3u);
v___x_703_ = lean_nat_mul(v___x_698_, v___x_702_);
v___x_704_ = lean_nat_dec_le(v___x_701_, v___x_703_);
lean_dec(v___x_703_);
lean_dec(v___x_701_);
if (v___x_704_ == 0)
{
lean_object* v___x_705_; 
v___x_705_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__1___redArg(v_b_586_);
lean_dec_ref(v_b_586_);
v___y_652_ = v___x_705_;
goto v___jp_651_;
}
else
{
v___y_652_ = v_b_586_;
goto v___jp_651_;
}
}
}
}
v___jp_644_:
{
lean_object* v_size_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; 
v_size_647_ = lean_ctor_get(v___y_645_, 0);
v___x_648_ = lean_unsigned_to_nat(1u);
v___x_649_ = lean_nat_add(v_size_647_, v___x_648_);
v___x_650_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_645_, v___x_649_, v_i_646_, v_val_640_, v___x_643_);
lean_dec(v_i_646_);
v_a_593_ = v___x_650_;
goto v___jp_592_;
}
v___jp_651_:
{
lean_object* v___x_653_; 
v___x_653_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0___redArg(v___y_652_, v_val_640_);
switch(lean_obj_tag(v___x_653_))
{
case 0:
{
lean_object* v_index_654_; lean_object* v_size_655_; lean_object* v___x_656_; 
v_index_654_ = lean_ctor_get(v___x_653_, 0);
lean_inc(v_index_654_);
lean_dec_ref_known(v___x_653_, 3);
v_size_655_ = lean_ctor_get(v___y_652_, 0);
lean_inc(v_size_655_);
v___x_656_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_652_, v_size_655_, v_index_654_, v_val_640_, v___x_643_);
lean_dec(v_index_654_);
v_a_593_ = v___x_656_;
goto v___jp_592_;
}
case 1:
{
lean_object* v_index_657_; 
v_index_657_ = lean_ctor_get(v___x_653_, 0);
lean_inc(v_index_657_);
lean_dec_ref_known(v___x_653_, 1);
v___y_645_ = v___y_652_;
v_i_646_ = v_index_657_;
goto v___jp_644_;
}
default: 
{
lean_object* v___x_658_; lean_object* v___x_659_; 
v___x_658_ = lean_unsigned_to_nat(0u);
v___x_659_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_652_, v___x_658_);
if (lean_obj_tag(v___x_659_) == 0)
{
lean_object* v_index_660_; 
v_index_660_ = lean_ctor_get(v___x_659_, 0);
lean_inc(v_index_660_);
lean_dec_ref_known(v___x_659_, 1);
v___y_645_ = v___y_652_;
v_i_646_ = v_index_660_;
goto v___jp_644_;
}
else
{
lean_dec_ref(v___x_643_);
lean_dec(v_val_640_);
v_a_593_ = v___y_652_;
goto v___jp_592_;
}
}
}
}
v___jp_661_:
{
lean_object* v_size_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; 
v_size_664_ = lean_ctor_get(v___y_662_, 0);
v___x_665_ = lean_unsigned_to_nat(1u);
v___x_666_ = lean_nat_add(v_size_664_, v___x_665_);
v___x_667_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_662_, v___x_666_, v_i_663_, v_val_640_, v___x_643_);
lean_dec(v_i_663_);
v_a_593_ = v___x_667_;
goto v___jp_592_;
}
v___jp_668_:
{
lean_object* v___x_669_; lean_object* v___x_670_; 
v___x_669_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__1___redArg(v_b_586_);
lean_dec_ref(v_b_586_);
v___x_670_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0___redArg(v___x_669_, v_val_640_);
switch(lean_obj_tag(v___x_670_))
{
case 0:
{
lean_object* v_index_671_; lean_object* v_size_672_; lean_object* v___x_673_; 
v_index_671_ = lean_ctor_get(v___x_670_, 0);
lean_inc(v_index_671_);
lean_dec_ref_known(v___x_670_, 3);
v_size_672_ = lean_ctor_get(v___x_669_, 0);
lean_inc(v_size_672_);
v___x_673_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_669_, v_size_672_, v_index_671_, v_val_640_, v___x_643_);
lean_dec(v_index_671_);
v_a_593_ = v___x_673_;
goto v___jp_592_;
}
case 1:
{
lean_object* v_index_674_; 
v_index_674_ = lean_ctor_get(v___x_670_, 0);
lean_inc(v_index_674_);
lean_dec_ref_known(v___x_670_, 1);
v___y_662_ = v___x_669_;
v_i_663_ = v_index_674_;
goto v___jp_661_;
}
default: 
{
lean_object* v___x_675_; lean_object* v___x_676_; 
v___x_675_ = lean_unsigned_to_nat(0u);
v___x_676_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_669_, v___x_675_);
if (lean_obj_tag(v___x_676_) == 0)
{
lean_object* v_index_677_; 
v_index_677_ = lean_ctor_get(v___x_676_, 0);
lean_inc(v_index_677_);
lean_dec_ref_known(v___x_676_, 1);
v___y_662_ = v___x_669_;
v_i_663_ = v_index_677_;
goto v___jp_661_;
}
else
{
lean_dec_ref(v___x_643_);
lean_dec(v_val_640_);
v_a_593_ = v___x_669_;
goto v___jp_592_;
}
}
}
}
}
}
else
{
lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_710_; 
lean_dec(v___x_639_);
lean_dec_ref(v___x_637_);
lean_del_object(v___x_614_);
v___x_707_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__4);
lean_inc(v_a_599_);
v___x_708_ = l_Lean_MessageData_ofName(v_a_599_);
if (v_isShared_611_ == 0)
{
lean_ctor_set_tag(v___x_610_, 7);
lean_ctor_set(v___x_610_, 1, v___x_708_);
lean_ctor_set(v___x_610_, 0, v___x_707_);
v___x_710_ = v___x_610_;
goto v_reusejp_709_;
}
else
{
lean_object* v_reuseFailAlloc_722_; 
v_reuseFailAlloc_722_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_722_, 0, v___x_707_);
lean_ctor_set(v_reuseFailAlloc_722_, 1, v___x_708_);
v___x_710_ = v_reuseFailAlloc_722_;
goto v_reusejp_709_;
}
v_reusejp_709_:
{
lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; 
v___x_711_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__8);
v___x_712_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_712_, 0, v___x_710_);
lean_ctor_set(v___x_712_, 1, v___x_711_);
v___x_713_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__1___redArg(v___x_712_, v___y_587_, v___y_588_, v___y_589_, v___y_590_);
if (lean_obj_tag(v___x_713_) == 0)
{
lean_dec_ref_known(v___x_713_, 1);
v_a_593_ = v_b_586_;
goto v___jp_592_;
}
else
{
lean_object* v_a_714_; lean_object* v___x_716_; uint8_t v_isShared_717_; uint8_t v_isSharedCheck_721_; 
lean_dec_ref(v_b_586_);
v_a_714_ = lean_ctor_get(v___x_713_, 0);
v_isSharedCheck_721_ = !lean_is_exclusive(v___x_713_);
if (v_isSharedCheck_721_ == 0)
{
v___x_716_ = v___x_713_;
v_isShared_717_ = v_isSharedCheck_721_;
goto v_resetjp_715_;
}
else
{
lean_inc(v_a_714_);
lean_dec(v___x_713_);
v___x_716_ = lean_box(0);
v_isShared_717_ = v_isSharedCheck_721_;
goto v_resetjp_715_;
}
v_resetjp_715_:
{
lean_object* v___x_719_; 
if (v_isShared_717_ == 0)
{
v___x_719_ = v___x_716_;
goto v_reusejp_718_;
}
else
{
lean_object* v_reuseFailAlloc_720_; 
v_reuseFailAlloc_720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_720_, 0, v_a_714_);
v___x_719_ = v_reuseFailAlloc_720_;
goto v_reusejp_718_;
}
v_reusejp_718_:
{
return v___x_719_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_723_; lean_object* v___x_725_; uint8_t v_isShared_726_; uint8_t v_isSharedCheck_730_; 
lean_del_object(v___x_614_);
lean_del_object(v___x_610_);
lean_dec_ref(v_b_586_);
v_a_723_ = lean_ctor_get(v___x_616_, 0);
v_isSharedCheck_730_ = !lean_is_exclusive(v___x_616_);
if (v_isSharedCheck_730_ == 0)
{
v___x_725_ = v___x_616_;
v_isShared_726_ = v_isSharedCheck_730_;
goto v_resetjp_724_;
}
else
{
lean_inc(v_a_723_);
lean_dec(v___x_616_);
v___x_725_ = lean_box(0);
v_isShared_726_ = v_isSharedCheck_730_;
goto v_resetjp_724_;
}
v_resetjp_724_:
{
lean_object* v___x_728_; 
if (v_isShared_726_ == 0)
{
v___x_728_ = v___x_725_;
goto v_reusejp_727_;
}
else
{
lean_object* v_reuseFailAlloc_729_; 
v_reuseFailAlloc_729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_729_, 0, v_a_723_);
v___x_728_ = v_reuseFailAlloc_729_;
goto v_reusejp_727_;
}
v_reusejp_727_:
{
return v___x_728_;
}
}
}
}
}
}
else
{
lean_object* v_a_735_; lean_object* v___x_737_; uint8_t v_isShared_738_; uint8_t v_isSharedCheck_742_; 
lean_dec_ref(v_b_586_);
v_a_735_ = lean_ctor_get(v___x_606_, 0);
v_isSharedCheck_742_ = !lean_is_exclusive(v___x_606_);
if (v_isSharedCheck_742_ == 0)
{
v___x_737_ = v___x_606_;
v_isShared_738_ = v_isSharedCheck_742_;
goto v_resetjp_736_;
}
else
{
lean_inc(v_a_735_);
lean_dec(v___x_606_);
v___x_737_ = lean_box(0);
v_isShared_738_ = v_isSharedCheck_742_;
goto v_resetjp_736_;
}
v_resetjp_736_:
{
lean_object* v___x_740_; 
if (v_isShared_738_ == 0)
{
v___x_740_ = v___x_737_;
goto v_reusejp_739_;
}
else
{
lean_object* v_reuseFailAlloc_741_; 
v_reuseFailAlloc_741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_741_, 0, v_a_735_);
v___x_740_ = v_reuseFailAlloc_741_;
goto v_reusejp_739_;
}
v_reusejp_739_:
{
return v___x_740_;
}
}
}
}
else
{
lean_object* v_a_743_; lean_object* v___x_745_; uint8_t v_isShared_746_; uint8_t v_isSharedCheck_750_; 
lean_dec_ref(v_b_586_);
v_a_743_ = lean_ctor_get(v___x_602_, 0);
v_isSharedCheck_750_ = !lean_is_exclusive(v___x_602_);
if (v_isSharedCheck_750_ == 0)
{
v___x_745_ = v___x_602_;
v_isShared_746_ = v_isSharedCheck_750_;
goto v_resetjp_744_;
}
else
{
lean_inc(v_a_743_);
lean_dec(v___x_602_);
v___x_745_ = lean_box(0);
v_isShared_746_ = v_isSharedCheck_750_;
goto v_resetjp_744_;
}
v_resetjp_744_:
{
lean_object* v___x_748_; 
if (v_isShared_746_ == 0)
{
v___x_748_ = v___x_745_;
goto v_reusejp_747_;
}
else
{
lean_object* v_reuseFailAlloc_749_; 
v_reuseFailAlloc_749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_749_, 0, v_a_743_);
v___x_748_ = v_reuseFailAlloc_749_;
goto v_reusejp_747_;
}
v_reusejp_747_:
{
return v___x_748_;
}
}
}
}
else
{
lean_object* v_a_751_; lean_object* v___x_753_; uint8_t v_isShared_754_; uint8_t v_isSharedCheck_758_; 
lean_dec_ref(v_b_586_);
v_a_751_ = lean_ctor_get(v___x_600_, 0);
v_isSharedCheck_758_ = !lean_is_exclusive(v___x_600_);
if (v_isSharedCheck_758_ == 0)
{
v___x_753_ = v___x_600_;
v_isShared_754_ = v_isSharedCheck_758_;
goto v_resetjp_752_;
}
else
{
lean_inc(v_a_751_);
lean_dec(v___x_600_);
v___x_753_ = lean_box(0);
v_isShared_754_ = v_isSharedCheck_758_;
goto v_resetjp_752_;
}
v_resetjp_752_:
{
lean_object* v___x_756_; 
if (v_isShared_754_ == 0)
{
v___x_756_ = v___x_753_;
goto v_reusejp_755_;
}
else
{
lean_object* v_reuseFailAlloc_757_; 
v_reuseFailAlloc_757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_757_, 0, v_a_751_);
v___x_756_ = v_reuseFailAlloc_757_;
goto v_reusejp_755_;
}
v_reusejp_755_:
{
return v___x_756_;
}
}
}
}
v___jp_592_:
{
size_t v___x_594_; size_t v___x_595_; 
v___x_594_ = ((size_t)1ULL);
v___x_595_ = lean_usize_add(v_i_585_, v___x_594_);
v_i_585_ = v___x_595_;
v_b_586_ = v_a_593_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___boxed(lean_object* v_as_759_, lean_object* v_sz_760_, lean_object* v_i_761_, lean_object* v_b_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_){
_start:
{
size_t v_sz_boxed_768_; size_t v_i_boxed_769_; lean_object* v_res_770_; 
v_sz_boxed_768_ = lean_unbox_usize(v_sz_760_);
lean_dec(v_sz_760_);
v_i_boxed_769_ = lean_unbox_usize(v_i_761_);
lean_dec(v_i_761_);
v_res_770_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2(v_as_759_, v_sz_boxed_768_, v_i_boxed_769_, v_b_762_, v___y_763_, v___y_764_, v___y_765_, v___y_766_);
lean_dec(v___y_766_);
lean_dec_ref(v___y_765_);
lean_dec(v___y_764_);
lean_dec_ref(v___y_763_);
lean_dec_ref(v_as_759_);
return v_res_770_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals___closed__0(void){
_start:
{
lean_object* v_cellCount_771_; lean_object* v___x_772_; 
v_cellCount_771_ = lean_unsigned_to_nat(16u);
v___x_772_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_771_);
return v___x_772_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals___closed__1(void){
_start:
{
lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v_m_776_; 
v___x_773_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals___closed__0, &l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals___closed__0_once, _init_l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals___closed__0);
v___x_774_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_latticeOps___closed__0, &l_Lean_Elab_Tactic_VCGen_latticeOps___closed__0_once, _init_l_Lean_Elab_Tactic_VCGen_latticeOps___closed__0);
v___x_775_ = lean_unsigned_to_nat(0u);
v_m_776_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_m_776_, 0, v___x_775_);
lean_ctor_set(v_m_776_, 1, v___x_774_);
lean_ctor_set(v_m_776_, 2, v___x_773_);
return v_m_776_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals(lean_object* v_names_777_, lean_object* v_a_778_, lean_object* v_a_779_, lean_object* v_a_780_, lean_object* v_a_781_){
_start:
{
lean_object* v_m_783_; size_t v_sz_784_; size_t v___x_785_; lean_object* v___x_786_; 
v_m_783_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals___closed__1, &l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals___closed__1_once, _init_l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals___closed__1);
v_sz_784_ = lean_array_size(v_names_777_);
v___x_785_ = ((size_t)0ULL);
v___x_786_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2(v_names_777_, v_sz_784_, v___x_785_, v_m_783_, v_a_778_, v_a_779_, v_a_780_, v_a_781_);
return v___x_786_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals___boxed(lean_object* v_names_787_, lean_object* v_a_788_, lean_object* v_a_789_, lean_object* v_a_790_, lean_object* v_a_791_, lean_object* v_a_792_){
_start:
{
lean_object* v_res_793_; 
v_res_793_ = l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals(v_names_787_, v_a_788_, v_a_789_, v_a_790_, v_a_791_);
lean_dec(v_a_791_);
lean_dec_ref(v_a_790_);
lean_dec(v_a_789_);
lean_dec_ref(v_a_788_);
lean_dec_ref(v_names_787_);
return v_res_793_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__1(lean_object* v_00_u03b1_794_, lean_object* v_msg_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_){
_start:
{
lean_object* v___x_801_; 
v___x_801_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__1___redArg(v_msg_795_, v___y_796_, v___y_797_, v___y_798_, v___y_799_);
return v___x_801_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__1___boxed(lean_object* v_00_u03b1_802_, lean_object* v_msg_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_){
_start:
{
lean_object* v_res_809_; 
v_res_809_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__1(v_00_u03b1_802_, v_msg_803_, v___y_804_, v___y_805_, v___y_806_, v___y_807_);
lean_dec(v___y_807_);
lean_dec_ref(v___y_806_);
lean_dec(v___y_805_);
lean_dec_ref(v___y_804_);
return v_res_809_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_go___lam__0(uint8_t v_isZero_810_, lean_object* v_x_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_, lean_object* v___y_820_){
_start:
{
lean_object* v___x_822_; lean_object* v___x_823_; 
v___x_822_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_822_, 0, v_isZero_810_);
lean_ctor_set_uint8(v___x_822_, 1, v_isZero_810_);
v___x_823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_823_, 0, v___x_822_);
return v___x_823_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_go___lam__0___boxed(lean_object* v_isZero_824_, lean_object* v_x_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_){
_start:
{
uint8_t v_isZero_boxed_836_; lean_object* v_res_837_; 
v_isZero_boxed_836_ = lean_unbox(v_isZero_824_);
v_res_837_ = l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_go___lam__0(v_isZero_boxed_836_, v_x_825_, v___y_826_, v___y_827_, v___y_828_, v___y_829_, v___y_830_, v___y_831_, v___y_832_, v___y_833_, v___y_834_);
lean_dec(v___y_834_);
lean_dec_ref(v___y_833_);
lean_dec(v___y_832_);
lean_dec_ref(v___y_831_);
lean_dec(v___y_830_);
lean_dec_ref(v___y_829_);
lean_dec(v___y_828_);
lean_dec_ref(v___y_827_);
lean_dec(v___y_826_);
lean_dec_ref(v_x_825_);
return v_res_837_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_go_spec__0___redArg(lean_object* v_msg_838_, lean_object* v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_){
_start:
{
lean_object* v_ref_844_; lean_object* v___x_845_; lean_object* v_a_846_; lean_object* v___x_848_; uint8_t v_isShared_849_; uint8_t v_isSharedCheck_854_; 
v_ref_844_ = lean_ctor_get(v___y_841_, 5);
v___x_845_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__1_spec__1(v_msg_838_, v___y_839_, v___y_840_, v___y_841_, v___y_842_);
v_a_846_ = lean_ctor_get(v___x_845_, 0);
v_isSharedCheck_854_ = !lean_is_exclusive(v___x_845_);
if (v_isSharedCheck_854_ == 0)
{
v___x_848_ = v___x_845_;
v_isShared_849_ = v_isSharedCheck_854_;
goto v_resetjp_847_;
}
else
{
lean_inc(v_a_846_);
lean_dec(v___x_845_);
v___x_848_ = lean_box(0);
v_isShared_849_ = v_isSharedCheck_854_;
goto v_resetjp_847_;
}
v_resetjp_847_:
{
lean_object* v___x_850_; lean_object* v___x_852_; 
lean_inc(v_ref_844_);
v___x_850_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_850_, 0, v_ref_844_);
lean_ctor_set(v___x_850_, 1, v_a_846_);
if (v_isShared_849_ == 0)
{
lean_ctor_set_tag(v___x_848_, 1);
lean_ctor_set(v___x_848_, 0, v___x_850_);
v___x_852_ = v___x_848_;
goto v_reusejp_851_;
}
else
{
lean_object* v_reuseFailAlloc_853_; 
v_reuseFailAlloc_853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_853_, 0, v___x_850_);
v___x_852_ = v_reuseFailAlloc_853_;
goto v_reusejp_851_;
}
v_reusejp_851_:
{
return v___x_852_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_go_spec__0___redArg___boxed(lean_object* v_msg_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_){
_start:
{
lean_object* v_res_861_; 
v_res_861_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_go_spec__0___redArg(v_msg_855_, v___y_856_, v___y_857_, v___y_858_, v___y_859_);
lean_dec(v___y_859_);
lean_dec_ref(v___y_858_);
lean_dec(v___y_857_);
lean_dec_ref(v___y_856_);
return v_res_861_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_go___closed__1(void){
_start:
{
lean_object* v___x_863_; lean_object* v___x_864_; 
v___x_863_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_go___closed__0));
v___x_864_ = l_Lean_stringToMessageData(v___x_863_);
return v___x_864_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_go(lean_object* v_step_868_, lean_object* v_e_u2080_869_, lean_object* v_cur_870_, lean_object* v_proof_x3f_871_, lean_object* v_a_872_, lean_object* v_a_873_, lean_object* v_a_874_, lean_object* v_a_875_, lean_object* v_a_876_, lean_object* v_a_877_, lean_object* v_a_878_){
_start:
{
lean_object* v_zero_880_; uint8_t v_isZero_881_; 
v_zero_880_ = lean_unsigned_to_nat(0u);
v_isZero_881_ = lean_nat_dec_eq(v_a_872_, v_zero_880_);
if (v_isZero_881_ == 1)
{
lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; 
lean_dec(v_a_872_);
lean_dec(v_proof_x3f_871_);
lean_dec_ref(v_e_u2080_869_);
lean_dec_ref(v_step_868_);
v___x_882_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_go___closed__1, &l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_go___closed__1_once, _init_l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_go___closed__1);
v___x_883_ = l_Lean_indentExpr(v_cur_870_);
v___x_884_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_884_, 0, v___x_882_);
lean_ctor_set(v___x_884_, 1, v___x_883_);
v___x_885_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_go_spec__0___redArg(v___x_884_, v_a_875_, v_a_876_, v_a_877_, v_a_878_);
return v___x_885_;
}
else
{
lean_object* v___x_886_; lean_object* v___f_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; 
v___x_886_ = lean_box(v_isZero_881_);
v___f_887_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_go___lam__0___boxed), 12, 1);
lean_closure_set(v___f_887_, 0, v___x_886_);
lean_inc_ref(v_step_868_);
lean_inc_ref(v_cur_870_);
v___x_888_ = lean_apply_1(v_step_868_, v_cur_870_);
lean_inc_ref(v___f_887_);
v___x_889_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_889_, 0, v___f_887_);
lean_ctor_set(v___x_889_, 1, v___f_887_);
v___x_890_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_go___closed__2));
v___x_891_ = l_Lean_Meta_Sym_Simp_SimpM_run_x27___redArg(v___x_888_, v___x_889_, v___x_890_, v_a_873_, v_a_874_, v_a_875_, v_a_876_, v_a_877_, v_a_878_);
if (lean_obj_tag(v___x_891_) == 0)
{
lean_object* v_a_892_; lean_object* v___x_894_; uint8_t v_isShared_895_; uint8_t v_isSharedCheck_925_; 
v_a_892_ = lean_ctor_get(v___x_891_, 0);
v_isSharedCheck_925_ = !lean_is_exclusive(v___x_891_);
if (v_isSharedCheck_925_ == 0)
{
v___x_894_ = v___x_891_;
v_isShared_895_ = v_isSharedCheck_925_;
goto v_resetjp_893_;
}
else
{
lean_inc(v_a_892_);
lean_dec(v___x_891_);
v___x_894_ = lean_box(0);
v_isShared_895_ = v_isSharedCheck_925_;
goto v_resetjp_893_;
}
v_resetjp_893_:
{
if (lean_obj_tag(v_a_892_) == 0)
{
lean_object* v___x_896_; lean_object* v___x_898_; 
lean_dec_ref_known(v_a_892_, 0);
lean_dec(v_a_872_);
lean_dec_ref(v_e_u2080_869_);
lean_dec_ref(v_step_868_);
v___x_896_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_896_, 0, v_cur_870_);
lean_ctor_set(v___x_896_, 1, v_proof_x3f_871_);
if (v_isShared_895_ == 0)
{
lean_ctor_set(v___x_894_, 0, v___x_896_);
v___x_898_ = v___x_894_;
goto v_reusejp_897_;
}
else
{
lean_object* v_reuseFailAlloc_899_; 
v_reuseFailAlloc_899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_899_, 0, v___x_896_);
v___x_898_ = v_reuseFailAlloc_899_;
goto v_reusejp_897_;
}
v_reusejp_897_:
{
return v___x_898_;
}
}
else
{
lean_object* v_e_x27_900_; lean_object* v_proof_901_; lean_object* v_one_902_; lean_object* v_n_903_; lean_object* v_proof_905_; lean_object* v___y_906_; lean_object* v___y_907_; lean_object* v___y_908_; lean_object* v___y_909_; lean_object* v___y_910_; lean_object* v___y_911_; 
lean_del_object(v___x_894_);
v_e_x27_900_ = lean_ctor_get(v_a_892_, 0);
lean_inc_ref(v_e_x27_900_);
v_proof_901_ = lean_ctor_get(v_a_892_, 1);
lean_inc_ref(v_proof_901_);
lean_dec_ref_known(v_a_892_, 2);
v_one_902_ = lean_unsigned_to_nat(1u);
v_n_903_ = lean_nat_sub(v_a_872_, v_one_902_);
lean_dec(v_a_872_);
if (lean_obj_tag(v_proof_x3f_871_) == 0)
{
lean_dec_ref(v_cur_870_);
v_proof_905_ = v_proof_901_;
v___y_906_ = v_a_873_;
v___y_907_ = v_a_874_;
v___y_908_ = v_a_875_;
v___y_909_ = v_a_876_;
v___y_910_ = v_a_877_;
v___y_911_ = v_a_878_;
goto v___jp_904_;
}
else
{
lean_object* v_val_914_; lean_object* v___x_915_; 
v_val_914_ = lean_ctor_get(v_proof_x3f_871_, 0);
lean_inc(v_val_914_);
lean_dec_ref_known(v_proof_x3f_871_, 1);
lean_inc_ref(v_e_x27_900_);
lean_inc_ref(v_e_u2080_869_);
v___x_915_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v_e_u2080_869_, v_cur_870_, v_val_914_, v_e_x27_900_, v_proof_901_, v_a_873_, v_a_874_, v_a_875_, v_a_876_, v_a_877_, v_a_878_);
if (lean_obj_tag(v___x_915_) == 0)
{
lean_object* v_a_916_; 
v_a_916_ = lean_ctor_get(v___x_915_, 0);
lean_inc(v_a_916_);
lean_dec_ref_known(v___x_915_, 1);
v_proof_905_ = v_a_916_;
v___y_906_ = v_a_873_;
v___y_907_ = v_a_874_;
v___y_908_ = v_a_875_;
v___y_909_ = v_a_876_;
v___y_910_ = v_a_877_;
v___y_911_ = v_a_878_;
goto v___jp_904_;
}
else
{
lean_object* v_a_917_; lean_object* v___x_919_; uint8_t v_isShared_920_; uint8_t v_isSharedCheck_924_; 
lean_dec(v_n_903_);
lean_dec_ref(v_e_x27_900_);
lean_dec_ref(v_e_u2080_869_);
lean_dec_ref(v_step_868_);
v_a_917_ = lean_ctor_get(v___x_915_, 0);
v_isSharedCheck_924_ = !lean_is_exclusive(v___x_915_);
if (v_isSharedCheck_924_ == 0)
{
v___x_919_ = v___x_915_;
v_isShared_920_ = v_isSharedCheck_924_;
goto v_resetjp_918_;
}
else
{
lean_inc(v_a_917_);
lean_dec(v___x_915_);
v___x_919_ = lean_box(0);
v_isShared_920_ = v_isSharedCheck_924_;
goto v_resetjp_918_;
}
v_resetjp_918_:
{
lean_object* v___x_922_; 
if (v_isShared_920_ == 0)
{
v___x_922_ = v___x_919_;
goto v_reusejp_921_;
}
else
{
lean_object* v_reuseFailAlloc_923_; 
v_reuseFailAlloc_923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_923_, 0, v_a_917_);
v___x_922_ = v_reuseFailAlloc_923_;
goto v_reusejp_921_;
}
v_reusejp_921_:
{
return v___x_922_;
}
}
}
}
v___jp_904_:
{
lean_object* v___x_912_; 
v___x_912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_912_, 0, v_proof_905_);
v_cur_870_ = v_e_x27_900_;
v_proof_x3f_871_ = v___x_912_;
v_a_872_ = v_n_903_;
v_a_873_ = v___y_906_;
v_a_874_ = v___y_907_;
v_a_875_ = v___y_908_;
v_a_876_ = v___y_909_;
v_a_877_ = v___y_910_;
v_a_878_ = v___y_911_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_926_; lean_object* v___x_928_; uint8_t v_isShared_929_; uint8_t v_isSharedCheck_933_; 
lean_dec(v_a_872_);
lean_dec(v_proof_x3f_871_);
lean_dec_ref(v_cur_870_);
lean_dec_ref(v_e_u2080_869_);
lean_dec_ref(v_step_868_);
v_a_926_ = lean_ctor_get(v___x_891_, 0);
v_isSharedCheck_933_ = !lean_is_exclusive(v___x_891_);
if (v_isSharedCheck_933_ == 0)
{
v___x_928_ = v___x_891_;
v_isShared_929_ = v_isSharedCheck_933_;
goto v_resetjp_927_;
}
else
{
lean_inc(v_a_926_);
lean_dec(v___x_891_);
v___x_928_ = lean_box(0);
v_isShared_929_ = v_isSharedCheck_933_;
goto v_resetjp_927_;
}
v_resetjp_927_:
{
lean_object* v___x_931_; 
if (v_isShared_929_ == 0)
{
v___x_931_ = v___x_928_;
goto v_reusejp_930_;
}
else
{
lean_object* v_reuseFailAlloc_932_; 
v_reuseFailAlloc_932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_932_, 0, v_a_926_);
v___x_931_ = v_reuseFailAlloc_932_;
goto v_reusejp_930_;
}
v_reusejp_930_:
{
return v___x_931_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_go___boxed(lean_object* v_step_934_, lean_object* v_e_u2080_935_, lean_object* v_cur_936_, lean_object* v_proof_x3f_937_, lean_object* v_a_938_, lean_object* v_a_939_, lean_object* v_a_940_, lean_object* v_a_941_, lean_object* v_a_942_, lean_object* v_a_943_, lean_object* v_a_944_, lean_object* v_a_945_){
_start:
{
lean_object* v_res_946_; 
v_res_946_ = l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_go(v_step_934_, v_e_u2080_935_, v_cur_936_, v_proof_x3f_937_, v_a_938_, v_a_939_, v_a_940_, v_a_941_, v_a_942_, v_a_943_, v_a_944_);
lean_dec(v_a_944_);
lean_dec_ref(v_a_943_);
lean_dec(v_a_942_);
lean_dec_ref(v_a_941_);
lean_dec(v_a_940_);
lean_dec_ref(v_a_939_);
return v_res_946_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_go_spec__0(lean_object* v_00_u03b1_947_, lean_object* v_msg_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_){
_start:
{
lean_object* v___x_956_; 
v___x_956_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_go_spec__0___redArg(v_msg_948_, v___y_951_, v___y_952_, v___y_953_, v___y_954_);
return v___x_956_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_go_spec__0___boxed(lean_object* v_00_u03b1_957_, lean_object* v_msg_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_){
_start:
{
lean_object* v_res_966_; 
v_res_966_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_go_spec__0(v_00_u03b1_957_, v_msg_958_, v___y_959_, v___y_960_, v___y_961_, v___y_962_, v___y_963_, v___y_964_);
lean_dec(v___y_964_);
lean_dec_ref(v___y_963_);
lean_dec(v___y_962_);
lean_dec_ref(v___y_961_);
lean_dec(v___y_960_);
lean_dec_ref(v___y_959_);
return v_res_966_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_spec__0___redArg(lean_object* v_as_967_, size_t v_i_968_, size_t v_stop_969_, lean_object* v_b_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_){
_start:
{
uint8_t v___x_976_; 
v___x_976_ = lean_usize_dec_eq(v_i_968_, v_stop_969_);
if (v___x_976_ == 0)
{
lean_object* v___x_977_; lean_object* v___x_978_; 
v___x_977_ = lean_array_uget_borrowed(v_as_967_, v_i_968_);
lean_inc(v___x_977_);
v___x_978_ = l_Lean_Meta_Sym_Simp_mkTheoremFromDecl(v___x_977_, v___y_971_, v___y_972_, v___y_973_, v___y_974_);
if (lean_obj_tag(v___x_978_) == 0)
{
lean_object* v_a_979_; lean_object* v___x_980_; size_t v___x_981_; size_t v___x_982_; 
v_a_979_ = lean_ctor_get(v___x_978_, 0);
lean_inc(v_a_979_);
lean_dec_ref_known(v___x_978_, 1);
v___x_980_ = l_Lean_Meta_Sym_Simp_Theorems_insert(v_b_970_, v_a_979_);
v___x_981_ = ((size_t)1ULL);
v___x_982_ = lean_usize_add(v_i_968_, v___x_981_);
v_i_968_ = v___x_982_;
v_b_970_ = v___x_980_;
goto _start;
}
else
{
lean_object* v_a_984_; lean_object* v___x_986_; uint8_t v_isShared_987_; uint8_t v_isSharedCheck_991_; 
lean_dec_ref(v_b_970_);
v_a_984_ = lean_ctor_get(v___x_978_, 0);
v_isSharedCheck_991_ = !lean_is_exclusive(v___x_978_);
if (v_isSharedCheck_991_ == 0)
{
v___x_986_ = v___x_978_;
v_isShared_987_ = v_isSharedCheck_991_;
goto v_resetjp_985_;
}
else
{
lean_inc(v_a_984_);
lean_dec(v___x_978_);
v___x_986_ = lean_box(0);
v_isShared_987_ = v_isSharedCheck_991_;
goto v_resetjp_985_;
}
v_resetjp_985_:
{
lean_object* v___x_989_; 
if (v_isShared_987_ == 0)
{
v___x_989_ = v___x_986_;
goto v_reusejp_988_;
}
else
{
lean_object* v_reuseFailAlloc_990_; 
v_reuseFailAlloc_990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_990_, 0, v_a_984_);
v___x_989_ = v_reuseFailAlloc_990_;
goto v_reusejp_988_;
}
v_reusejp_988_:
{
return v___x_989_;
}
}
}
}
else
{
lean_object* v___x_992_; 
v___x_992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_992_, 0, v_b_970_);
return v___x_992_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_spec__0___redArg___boxed(lean_object* v_as_993_, lean_object* v_i_994_, lean_object* v_stop_995_, lean_object* v_b_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_){
_start:
{
size_t v_i_boxed_1002_; size_t v_stop_boxed_1003_; lean_object* v_res_1004_; 
v_i_boxed_1002_ = lean_unbox_usize(v_i_994_);
lean_dec(v_i_994_);
v_stop_boxed_1003_ = lean_unbox_usize(v_stop_995_);
lean_dec(v_stop_995_);
v_res_1004_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_spec__0___redArg(v_as_993_, v_i_boxed_1002_, v_stop_boxed_1003_, v_b_996_, v___y_997_, v___y_998_, v___y_999_, v___y_1000_);
lean_dec(v___y_1000_);
lean_dec_ref(v___y_999_);
lean_dec(v___y_998_);
lean_dec_ref(v___y_997_);
lean_dec_ref(v_as_993_);
return v_res_1004_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp___closed__1(void){
_start:
{
lean_object* v___x_1006_; 
v___x_1006_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1006_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp___closed__2(void){
_start:
{
lean_object* v___x_1007_; lean_object* v___x_1008_; 
v___x_1007_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp___closed__1, &l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp___closed__1_once, _init_l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp___closed__1);
v___x_1008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1008_, 0, v___x_1007_);
return v___x_1008_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp(lean_object* v_rewrites_1009_, lean_object* v_e_1010_, lean_object* v_fuel_1011_, lean_object* v_a_1012_, lean_object* v_a_1013_, lean_object* v_a_1014_, lean_object* v_a_1015_, lean_object* v_a_1016_, lean_object* v_a_1017_){
_start:
{
lean_object* v_a_1020_; lean_object* v___y_1036_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; uint8_t v___x_1049_; 
v___x_1046_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp___closed__2, &l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp___closed__2_once, _init_l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp___closed__2);
v___x_1047_ = lean_unsigned_to_nat(0u);
v___x_1048_ = lean_array_get_size(v_rewrites_1009_);
v___x_1049_ = lean_nat_dec_lt(v___x_1047_, v___x_1048_);
if (v___x_1049_ == 0)
{
v_a_1020_ = v___x_1046_;
goto v___jp_1019_;
}
else
{
uint8_t v___x_1050_; 
v___x_1050_ = lean_nat_dec_le(v___x_1048_, v___x_1048_);
if (v___x_1050_ == 0)
{
if (v___x_1049_ == 0)
{
v_a_1020_ = v___x_1046_;
goto v___jp_1019_;
}
else
{
size_t v___x_1051_; size_t v___x_1052_; lean_object* v___x_1053_; 
v___x_1051_ = ((size_t)0ULL);
v___x_1052_ = lean_usize_of_nat(v___x_1048_);
v___x_1053_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_spec__0___redArg(v_rewrites_1009_, v___x_1051_, v___x_1052_, v___x_1046_, v_a_1014_, v_a_1015_, v_a_1016_, v_a_1017_);
v___y_1036_ = v___x_1053_;
goto v___jp_1035_;
}
}
else
{
size_t v___x_1054_; size_t v___x_1055_; lean_object* v___x_1056_; 
v___x_1054_ = ((size_t)0ULL);
v___x_1055_ = lean_usize_of_nat(v___x_1048_);
v___x_1056_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_spec__0___redArg(v_rewrites_1009_, v___x_1054_, v___x_1055_, v___x_1046_, v_a_1014_, v_a_1015_, v_a_1016_, v_a_1017_);
v___y_1036_ = v___x_1056_;
goto v___jp_1035_;
}
}
v___jp_1019_:
{
lean_object* v___x_1021_; 
v___x_1021_ = l_Lean_Meta_Sym_shareCommon(v_e_1010_, v_a_1012_, v_a_1013_, v_a_1014_, v_a_1015_, v_a_1016_, v_a_1017_);
if (lean_obj_tag(v___x_1021_) == 0)
{
lean_object* v_a_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; 
v_a_1022_ = lean_ctor_get(v___x_1021_, 0);
lean_inc_n(v_a_1022_, 2);
lean_dec_ref_known(v___x_1021_, 1);
v___x_1023_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp___closed__0));
v___x_1024_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Simp_Theorems_rewrite___boxed), 13, 2);
lean_closure_set(v___x_1024_, 0, v_a_1020_);
lean_closure_set(v___x_1024_, 1, v___x_1023_);
v___x_1025_ = lean_box(0);
v___x_1026_ = l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_go(v___x_1024_, v_a_1022_, v_a_1022_, v___x_1025_, v_fuel_1011_, v_a_1012_, v_a_1013_, v_a_1014_, v_a_1015_, v_a_1016_, v_a_1017_);
return v___x_1026_;
}
else
{
lean_object* v_a_1027_; lean_object* v___x_1029_; uint8_t v_isShared_1030_; uint8_t v_isSharedCheck_1034_; 
lean_dec_ref(v_a_1020_);
lean_dec(v_fuel_1011_);
v_a_1027_ = lean_ctor_get(v___x_1021_, 0);
v_isSharedCheck_1034_ = !lean_is_exclusive(v___x_1021_);
if (v_isSharedCheck_1034_ == 0)
{
v___x_1029_ = v___x_1021_;
v_isShared_1030_ = v_isSharedCheck_1034_;
goto v_resetjp_1028_;
}
else
{
lean_inc(v_a_1027_);
lean_dec(v___x_1021_);
v___x_1029_ = lean_box(0);
v_isShared_1030_ = v_isSharedCheck_1034_;
goto v_resetjp_1028_;
}
v_resetjp_1028_:
{
lean_object* v___x_1032_; 
if (v_isShared_1030_ == 0)
{
v___x_1032_ = v___x_1029_;
goto v_reusejp_1031_;
}
else
{
lean_object* v_reuseFailAlloc_1033_; 
v_reuseFailAlloc_1033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1033_, 0, v_a_1027_);
v___x_1032_ = v_reuseFailAlloc_1033_;
goto v_reusejp_1031_;
}
v_reusejp_1031_:
{
return v___x_1032_;
}
}
}
}
v___jp_1035_:
{
if (lean_obj_tag(v___y_1036_) == 0)
{
lean_object* v_a_1037_; 
v_a_1037_ = lean_ctor_get(v___y_1036_, 0);
lean_inc(v_a_1037_);
lean_dec_ref_known(v___y_1036_, 1);
v_a_1020_ = v_a_1037_;
goto v___jp_1019_;
}
else
{
lean_object* v_a_1038_; lean_object* v___x_1040_; uint8_t v_isShared_1041_; uint8_t v_isSharedCheck_1045_; 
lean_dec(v_fuel_1011_);
lean_dec_ref(v_e_1010_);
v_a_1038_ = lean_ctor_get(v___y_1036_, 0);
v_isSharedCheck_1045_ = !lean_is_exclusive(v___y_1036_);
if (v_isSharedCheck_1045_ == 0)
{
v___x_1040_ = v___y_1036_;
v_isShared_1041_ = v_isSharedCheck_1045_;
goto v_resetjp_1039_;
}
else
{
lean_inc(v_a_1038_);
lean_dec(v___y_1036_);
v___x_1040_ = lean_box(0);
v_isShared_1041_ = v_isSharedCheck_1045_;
goto v_resetjp_1039_;
}
v_resetjp_1039_:
{
lean_object* v___x_1043_; 
if (v_isShared_1041_ == 0)
{
v___x_1043_ = v___x_1040_;
goto v_reusejp_1042_;
}
else
{
lean_object* v_reuseFailAlloc_1044_; 
v_reuseFailAlloc_1044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1044_, 0, v_a_1038_);
v___x_1043_ = v_reuseFailAlloc_1044_;
goto v_reusejp_1042_;
}
v_reusejp_1042_:
{
return v___x_1043_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp___boxed(lean_object* v_rewrites_1057_, lean_object* v_e_1058_, lean_object* v_fuel_1059_, lean_object* v_a_1060_, lean_object* v_a_1061_, lean_object* v_a_1062_, lean_object* v_a_1063_, lean_object* v_a_1064_, lean_object* v_a_1065_, lean_object* v_a_1066_){
_start:
{
lean_object* v_res_1067_; 
v_res_1067_ = l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp(v_rewrites_1057_, v_e_1058_, v_fuel_1059_, v_a_1060_, v_a_1061_, v_a_1062_, v_a_1063_, v_a_1064_, v_a_1065_);
lean_dec(v_a_1065_);
lean_dec_ref(v_a_1064_);
lean_dec(v_a_1063_);
lean_dec_ref(v_a_1062_);
lean_dec(v_a_1061_);
lean_dec_ref(v_a_1060_);
lean_dec_ref(v_rewrites_1057_);
return v_res_1067_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_spec__0(lean_object* v_as_1068_, size_t v_i_1069_, size_t v_stop_1070_, lean_object* v_b_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_){
_start:
{
lean_object* v___x_1079_; 
v___x_1079_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_spec__0___redArg(v_as_1068_, v_i_1069_, v_stop_1070_, v_b_1071_, v___y_1074_, v___y_1075_, v___y_1076_, v___y_1077_);
return v___x_1079_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_spec__0___boxed(lean_object* v_as_1080_, lean_object* v_i_1081_, lean_object* v_stop_1082_, lean_object* v_b_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_){
_start:
{
size_t v_i_boxed_1091_; size_t v_stop_boxed_1092_; lean_object* v_res_1093_; 
v_i_boxed_1091_ = lean_unbox_usize(v_i_1081_);
lean_dec(v_i_1081_);
v_stop_boxed_1092_ = lean_unbox_usize(v_stop_1082_);
lean_dec(v_stop_1082_);
v_res_1093_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_spec__0(v_as_1080_, v_i_boxed_1091_, v_stop_boxed_1092_, v_b_1083_, v___y_1084_, v___y_1085_, v___y_1086_, v___y_1087_, v___y_1088_, v___y_1089_);
lean_dec(v___y_1089_);
lean_dec_ref(v___y_1088_);
lean_dec(v___y_1087_);
lean_dec_ref(v___y_1086_);
lean_dec(v___y_1085_);
lean_dec_ref(v___y_1084_);
lean_dec_ref(v_as_1080_);
return v_res_1093_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply___lam__0(lean_object* v_s_1094_, lean_object* v_a_1095_, lean_object* v_pre_1096_, lean_object* v_u_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_){
_start:
{
lean_object* v___x_1103_; 
lean_inc_ref(v_u_1097_);
v___x_1103_ = l_Lean_Meta_mkEq(v_u_1097_, v_s_1094_, v___y_1098_, v___y_1099_, v___y_1100_, v___y_1101_);
if (lean_obj_tag(v___x_1103_) == 0)
{
lean_object* v_a_1104_; lean_object* v___x_1106_; uint8_t v_isShared_1107_; uint8_t v_isSharedCheck_1135_; 
v_a_1104_ = lean_ctor_get(v___x_1103_, 0);
v_isSharedCheck_1135_ = !lean_is_exclusive(v___x_1103_);
if (v_isSharedCheck_1135_ == 0)
{
v___x_1106_ = v___x_1103_;
v_isShared_1107_ = v_isSharedCheck_1135_;
goto v_resetjp_1105_;
}
else
{
lean_inc(v_a_1104_);
lean_dec(v___x_1103_);
v___x_1106_ = lean_box(0);
v_isShared_1107_ = v_isSharedCheck_1135_;
goto v_resetjp_1105_;
}
v_resetjp_1105_:
{
lean_object* v___x_1108_; lean_object* v___x_1110_; 
v___x_1108_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_LatticeOp_ofProp___closed__2));
if (v_isShared_1107_ == 0)
{
lean_ctor_set_tag(v___x_1106_, 1);
lean_ctor_set(v___x_1106_, 0, v_a_1095_);
v___x_1110_ = v___x_1106_;
goto v_reusejp_1109_;
}
else
{
lean_object* v_reuseFailAlloc_1134_; 
v_reuseFailAlloc_1134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1134_, 0, v_a_1095_);
v___x_1110_ = v_reuseFailAlloc_1134_;
goto v_reusejp_1109_;
}
v_reusejp_1109_:
{
lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; 
v___x_1111_ = lean_box(0);
v___x_1112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1112_, 0, v_a_1104_);
v___x_1113_ = lean_unsigned_to_nat(3u);
v___x_1114_ = lean_mk_empty_array_with_capacity(v___x_1113_);
v___x_1115_ = lean_array_push(v___x_1114_, v___x_1110_);
v___x_1116_ = lean_array_push(v___x_1115_, v___x_1111_);
v___x_1117_ = lean_array_push(v___x_1116_, v___x_1112_);
v___x_1118_ = l_Lean_Meta_mkAppOptM(v___x_1108_, v___x_1117_, v___y_1098_, v___y_1099_, v___y_1100_, v___y_1101_);
if (lean_obj_tag(v___x_1118_) == 0)
{
lean_object* v_a_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; 
v_a_1119_ = lean_ctor_get(v___x_1118_, 0);
lean_inc(v_a_1119_);
lean_dec_ref_known(v___x_1118_, 1);
v___x_1120_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__3));
v___x_1121_ = lean_unsigned_to_nat(2u);
v___x_1122_ = lean_mk_empty_array_with_capacity(v___x_1121_);
v___x_1123_ = lean_array_push(v___x_1122_, v_a_1119_);
v___x_1124_ = lean_array_push(v___x_1123_, v_pre_1096_);
v___x_1125_ = l_Lean_Meta_mkAppM(v___x_1120_, v___x_1124_, v___y_1098_, v___y_1099_, v___y_1100_, v___y_1101_);
if (lean_obj_tag(v___x_1125_) == 0)
{
lean_object* v_a_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; uint8_t v___x_1130_; uint8_t v___x_1131_; uint8_t v___x_1132_; lean_object* v___x_1133_; 
v_a_1126_ = lean_ctor_get(v___x_1125_, 0);
lean_inc(v_a_1126_);
lean_dec_ref_known(v___x_1125_, 1);
v___x_1127_ = lean_unsigned_to_nat(1u);
v___x_1128_ = lean_mk_empty_array_with_capacity(v___x_1127_);
v___x_1129_ = lean_array_push(v___x_1128_, v_u_1097_);
v___x_1130_ = 0;
v___x_1131_ = 1;
v___x_1132_ = 1;
v___x_1133_ = l_Lean_Meta_mkLambdaFVars(v___x_1129_, v_a_1126_, v___x_1130_, v___x_1131_, v___x_1130_, v___x_1131_, v___x_1132_, v___y_1098_, v___y_1099_, v___y_1100_, v___y_1101_);
lean_dec_ref(v___x_1129_);
return v___x_1133_;
}
else
{
lean_dec_ref(v_u_1097_);
return v___x_1125_;
}
}
else
{
lean_dec_ref(v_u_1097_);
lean_dec_ref(v_pre_1096_);
return v___x_1118_;
}
}
}
}
else
{
lean_dec_ref(v_u_1097_);
lean_dec_ref(v_pre_1096_);
lean_dec_ref(v_a_1095_);
return v___x_1103_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply___lam__0___boxed(lean_object* v_s_1136_, lean_object* v_a_1137_, lean_object* v_pre_1138_, lean_object* v_u_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_){
_start:
{
lean_object* v_res_1145_; 
v_res_1145_ = l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply___lam__0(v_s_1136_, v_a_1137_, v_pre_1138_, v_u_1139_, v___y_1140_, v___y_1141_, v___y_1142_, v___y_1143_);
lean_dec(v___y_1143_);
lean_dec_ref(v___y_1142_);
lean_dec(v___y_1141_);
lean_dec_ref(v___y_1140_);
return v_res_1145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply_spec__0_spec__0___redArg___lam__0(lean_object* v_k_1146_, lean_object* v_b_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_){
_start:
{
lean_object* v___x_1153_; 
lean_inc(v___y_1151_);
lean_inc_ref(v___y_1150_);
lean_inc(v___y_1149_);
lean_inc_ref(v___y_1148_);
v___x_1153_ = lean_apply_6(v_k_1146_, v_b_1147_, v___y_1148_, v___y_1149_, v___y_1150_, v___y_1151_, lean_box(0));
return v___x_1153_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply_spec__0_spec__0___redArg___lam__0___boxed(lean_object* v_k_1154_, lean_object* v_b_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_){
_start:
{
lean_object* v_res_1161_; 
v_res_1161_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply_spec__0_spec__0___redArg___lam__0(v_k_1154_, v_b_1155_, v___y_1156_, v___y_1157_, v___y_1158_, v___y_1159_);
lean_dec(v___y_1159_);
lean_dec_ref(v___y_1158_);
lean_dec(v___y_1157_);
lean_dec_ref(v___y_1156_);
return v_res_1161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply_spec__0_spec__0___redArg(lean_object* v_name_1162_, uint8_t v_bi_1163_, lean_object* v_type_1164_, lean_object* v_k_1165_, uint8_t v_kind_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_){
_start:
{
lean_object* v___f_1172_; lean_object* v___x_1173_; 
v___f_1172_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply_spec__0_spec__0___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1172_, 0, v_k_1165_);
v___x_1173_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1162_, v_bi_1163_, v_type_1164_, v___f_1172_, v_kind_1166_, v___y_1167_, v___y_1168_, v___y_1169_, v___y_1170_);
if (lean_obj_tag(v___x_1173_) == 0)
{
lean_object* v_a_1174_; lean_object* v___x_1176_; uint8_t v_isShared_1177_; uint8_t v_isSharedCheck_1181_; 
v_a_1174_ = lean_ctor_get(v___x_1173_, 0);
v_isSharedCheck_1181_ = !lean_is_exclusive(v___x_1173_);
if (v_isSharedCheck_1181_ == 0)
{
v___x_1176_ = v___x_1173_;
v_isShared_1177_ = v_isSharedCheck_1181_;
goto v_resetjp_1175_;
}
else
{
lean_inc(v_a_1174_);
lean_dec(v___x_1173_);
v___x_1176_ = lean_box(0);
v_isShared_1177_ = v_isSharedCheck_1181_;
goto v_resetjp_1175_;
}
v_resetjp_1175_:
{
lean_object* v___x_1179_; 
if (v_isShared_1177_ == 0)
{
v___x_1179_ = v___x_1176_;
goto v_reusejp_1178_;
}
else
{
lean_object* v_reuseFailAlloc_1180_; 
v_reuseFailAlloc_1180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1180_, 0, v_a_1174_);
v___x_1179_ = v_reuseFailAlloc_1180_;
goto v_reusejp_1178_;
}
v_reusejp_1178_:
{
return v___x_1179_;
}
}
}
else
{
lean_object* v_a_1182_; lean_object* v___x_1184_; uint8_t v_isShared_1185_; uint8_t v_isSharedCheck_1189_; 
v_a_1182_ = lean_ctor_get(v___x_1173_, 0);
v_isSharedCheck_1189_ = !lean_is_exclusive(v___x_1173_);
if (v_isSharedCheck_1189_ == 0)
{
v___x_1184_ = v___x_1173_;
v_isShared_1185_ = v_isSharedCheck_1189_;
goto v_resetjp_1183_;
}
else
{
lean_inc(v_a_1182_);
lean_dec(v___x_1173_);
v___x_1184_ = lean_box(0);
v_isShared_1185_ = v_isSharedCheck_1189_;
goto v_resetjp_1183_;
}
v_resetjp_1183_:
{
lean_object* v___x_1187_; 
if (v_isShared_1185_ == 0)
{
v___x_1187_ = v___x_1184_;
goto v_reusejp_1186_;
}
else
{
lean_object* v_reuseFailAlloc_1188_; 
v_reuseFailAlloc_1188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1188_, 0, v_a_1182_);
v___x_1187_ = v_reuseFailAlloc_1188_;
goto v_reusejp_1186_;
}
v_reusejp_1186_:
{
return v___x_1187_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply_spec__0_spec__0___redArg___boxed(lean_object* v_name_1190_, lean_object* v_bi_1191_, lean_object* v_type_1192_, lean_object* v_k_1193_, lean_object* v_kind_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_){
_start:
{
uint8_t v_bi_boxed_1200_; uint8_t v_kind_boxed_1201_; lean_object* v_res_1202_; 
v_bi_boxed_1200_ = lean_unbox(v_bi_1191_);
v_kind_boxed_1201_ = lean_unbox(v_kind_1194_);
v_res_1202_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply_spec__0_spec__0___redArg(v_name_1190_, v_bi_boxed_1200_, v_type_1192_, v_k_1193_, v_kind_boxed_1201_, v___y_1195_, v___y_1196_, v___y_1197_, v___y_1198_);
lean_dec(v___y_1198_);
lean_dec_ref(v___y_1197_);
lean_dec(v___y_1196_);
lean_dec_ref(v___y_1195_);
return v_res_1202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply_spec__0___redArg(lean_object* v_name_1203_, lean_object* v_type_1204_, lean_object* v_k_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_){
_start:
{
uint8_t v___x_1211_; uint8_t v___x_1212_; lean_object* v___x_1213_; 
v___x_1211_ = 0;
v___x_1212_ = 0;
v___x_1213_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply_spec__0_spec__0___redArg(v_name_1203_, v___x_1211_, v_type_1204_, v_k_1205_, v___x_1212_, v___y_1206_, v___y_1207_, v___y_1208_, v___y_1209_);
return v___x_1213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply_spec__0___redArg___boxed(lean_object* v_name_1214_, lean_object* v_type_1215_, lean_object* v_k_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_){
_start:
{
lean_object* v_res_1222_; 
v_res_1222_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply_spec__0___redArg(v_name_1214_, v_type_1215_, v_k_1216_, v___y_1217_, v___y_1218_, v___y_1219_, v___y_1220_);
lean_dec(v___y_1220_);
lean_dec_ref(v___y_1219_);
lean_dec(v___y_1218_);
lean_dec_ref(v___y_1217_);
return v_res_1222_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply___closed__1(void){
_start:
{
lean_object* v___x_1224_; lean_object* v___x_1225_; 
v___x_1224_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply___closed__0));
v___x_1225_ = l_Lean_stringToMessageData(v___x_1224_);
return v___x_1225_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply(lean_object* v_introThm_1234_, lean_object* v_opAs_1235_, lean_object* v_pre_1236_, lean_object* v_ss_1237_, lean_object* v_a_1238_, lean_object* v_a_1239_, lean_object* v_a_1240_, lean_object* v_a_1241_){
_start:
{
if (lean_obj_tag(v_ss_1237_) == 0)
{
lean_object* v___x_1243_; 
lean_inc(v_introThm_1234_);
v___x_1243_ = l_Lean_Meta_mkConstWithFreshMVarLevels(v_introThm_1234_, v_a_1238_, v_a_1239_, v_a_1240_, v_a_1241_);
if (lean_obj_tag(v___x_1243_) == 0)
{
lean_object* v_a_1244_; lean_object* v___x_1245_; 
v_a_1244_ = lean_ctor_get(v___x_1243_, 0);
lean_inc_n(v_a_1244_, 2);
lean_dec_ref_known(v___x_1243_, 1);
lean_inc(v_a_1241_);
lean_inc_ref(v_a_1240_);
lean_inc(v_a_1239_);
lean_inc_ref(v_a_1238_);
v___x_1245_ = lean_infer_type(v_a_1244_, v_a_1238_, v_a_1239_, v_a_1240_, v_a_1241_);
if (lean_obj_tag(v___x_1245_) == 0)
{
lean_object* v_a_1246_; uint8_t v___x_1247_; lean_object* v___x_1248_; 
v_a_1246_ = lean_ctor_get(v___x_1245_, 0);
lean_inc(v_a_1246_);
lean_dec_ref_known(v___x_1245_, 1);
v___x_1247_ = 0;
v___x_1248_ = l_Lean_Meta_forallMetaTelescope(v_a_1246_, v___x_1247_, v_a_1238_, v_a_1239_, v_a_1240_, v_a_1241_);
if (lean_obj_tag(v___x_1248_) == 0)
{
lean_object* v_a_1249_; lean_object* v___x_1251_; uint8_t v_isShared_1252_; uint8_t v_isSharedCheck_1308_; 
v_a_1249_ = lean_ctor_get(v___x_1248_, 0);
v_isSharedCheck_1308_ = !lean_is_exclusive(v___x_1248_);
if (v_isSharedCheck_1308_ == 0)
{
v___x_1251_ = v___x_1248_;
v_isShared_1252_ = v_isSharedCheck_1308_;
goto v_resetjp_1250_;
}
else
{
lean_inc(v_a_1249_);
lean_dec(v___x_1248_);
v___x_1251_ = lean_box(0);
v_isShared_1252_ = v_isSharedCheck_1308_;
goto v_resetjp_1250_;
}
v_resetjp_1250_:
{
lean_object* v_fst_1253_; lean_object* v_snd_1254_; lean_object* v___x_1256_; uint8_t v_isShared_1257_; uint8_t v_isSharedCheck_1307_; 
v_fst_1253_ = lean_ctor_get(v_a_1249_, 0);
v_snd_1254_ = lean_ctor_get(v_a_1249_, 1);
v_isSharedCheck_1307_ = !lean_is_exclusive(v_a_1249_);
if (v_isSharedCheck_1307_ == 0)
{
v___x_1256_ = v_a_1249_;
v_isShared_1257_ = v_isSharedCheck_1307_;
goto v_resetjp_1255_;
}
else
{
lean_inc(v_snd_1254_);
lean_inc(v_fst_1253_);
lean_dec(v_a_1249_);
v___x_1256_ = lean_box(0);
v_isShared_1257_ = v_isSharedCheck_1307_;
goto v_resetjp_1255_;
}
v_resetjp_1255_:
{
lean_object* v_snd_1263_; lean_object* v___x_1265_; uint8_t v_isShared_1266_; uint8_t v_isSharedCheck_1305_; 
v_snd_1263_ = lean_ctor_get(v_snd_1254_, 1);
v_isSharedCheck_1305_ = !lean_is_exclusive(v_snd_1254_);
if (v_isSharedCheck_1305_ == 0)
{
lean_object* v_unused_1306_; 
v_unused_1306_ = lean_ctor_get(v_snd_1254_, 0);
lean_dec(v_unused_1306_);
v___x_1265_ = v_snd_1254_;
v_isShared_1266_ = v_isSharedCheck_1305_;
goto v_resetjp_1264_;
}
else
{
lean_inc(v_snd_1263_);
lean_dec(v_snd_1254_);
v___x_1265_ = lean_box(0);
v_isShared_1266_ = v_isSharedCheck_1305_;
goto v_resetjp_1264_;
}
v___jp_1258_:
{
lean_object* v___x_1259_; lean_object* v___x_1261_; 
v___x_1259_ = l_Lean_mkAppN(v_a_1244_, v_fst_1253_);
lean_dec(v_fst_1253_);
if (v_isShared_1252_ == 0)
{
lean_ctor_set(v___x_1251_, 0, v___x_1259_);
v___x_1261_ = v___x_1251_;
goto v_reusejp_1260_;
}
else
{
lean_object* v_reuseFailAlloc_1262_; 
v_reuseFailAlloc_1262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1262_, 0, v___x_1259_);
v___x_1261_ = v_reuseFailAlloc_1262_;
goto v_reusejp_1260_;
}
v_reusejp_1260_:
{
return v___x_1261_;
}
}
v_resetjp_1264_:
{
lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; 
v___x_1267_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__2));
v___x_1268_ = lean_unsigned_to_nat(2u);
v___x_1269_ = lean_mk_empty_array_with_capacity(v___x_1268_);
v___x_1270_ = lean_array_push(v___x_1269_, v_pre_1236_);
v___x_1271_ = lean_array_push(v___x_1270_, v_opAs_1235_);
v___x_1272_ = l_Lean_Meta_mkAppM(v___x_1267_, v___x_1271_, v_a_1238_, v_a_1239_, v_a_1240_, v_a_1241_);
if (lean_obj_tag(v___x_1272_) == 0)
{
lean_object* v_a_1273_; lean_object* v___x_1274_; 
v_a_1273_ = lean_ctor_get(v___x_1272_, 0);
lean_inc_n(v_a_1273_, 2);
lean_dec_ref_known(v___x_1272_, 1);
v___x_1274_ = l_Lean_Meta_isExprDefEq(v_snd_1263_, v_a_1273_, v_a_1238_, v_a_1239_, v_a_1240_, v_a_1241_);
if (lean_obj_tag(v___x_1274_) == 0)
{
lean_object* v_a_1275_; uint8_t v___x_1276_; 
v_a_1275_ = lean_ctor_get(v___x_1274_, 0);
lean_inc(v_a_1275_);
lean_dec_ref_known(v___x_1274_, 1);
v___x_1276_ = lean_unbox(v_a_1275_);
lean_dec(v_a_1275_);
if (v___x_1276_ == 0)
{
lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1280_; 
v___x_1277_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__4);
v___x_1278_ = l_Lean_MessageData_ofName(v_introThm_1234_);
if (v_isShared_1266_ == 0)
{
lean_ctor_set_tag(v___x_1265_, 7);
lean_ctor_set(v___x_1265_, 1, v___x_1278_);
lean_ctor_set(v___x_1265_, 0, v___x_1277_);
v___x_1280_ = v___x_1265_;
goto v_reusejp_1279_;
}
else
{
lean_object* v_reuseFailAlloc_1296_; 
v_reuseFailAlloc_1296_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1296_, 0, v___x_1277_);
lean_ctor_set(v_reuseFailAlloc_1296_, 1, v___x_1278_);
v___x_1280_ = v_reuseFailAlloc_1296_;
goto v_reusejp_1279_;
}
v_reusejp_1279_:
{
lean_object* v___x_1281_; lean_object* v___x_1283_; 
v___x_1281_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply___closed__1, &l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply___closed__1_once, _init_l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply___closed__1);
if (v_isShared_1257_ == 0)
{
lean_ctor_set_tag(v___x_1256_, 7);
lean_ctor_set(v___x_1256_, 1, v___x_1281_);
lean_ctor_set(v___x_1256_, 0, v___x_1280_);
v___x_1283_ = v___x_1256_;
goto v_reusejp_1282_;
}
else
{
lean_object* v_reuseFailAlloc_1295_; 
v_reuseFailAlloc_1295_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1295_, 0, v___x_1280_);
lean_ctor_set(v_reuseFailAlloc_1295_, 1, v___x_1281_);
v___x_1283_ = v_reuseFailAlloc_1295_;
goto v_reusejp_1282_;
}
v_reusejp_1282_:
{
lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; 
v___x_1284_ = l_Lean_MessageData_ofExpr(v_a_1273_);
v___x_1285_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1285_, 0, v___x_1283_);
lean_ctor_set(v___x_1285_, 1, v___x_1284_);
v___x_1286_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__1___redArg(v___x_1285_, v_a_1238_, v_a_1239_, v_a_1240_, v_a_1241_);
if (lean_obj_tag(v___x_1286_) == 0)
{
lean_dec_ref_known(v___x_1286_, 1);
goto v___jp_1258_;
}
else
{
lean_object* v_a_1287_; lean_object* v___x_1289_; uint8_t v_isShared_1290_; uint8_t v_isSharedCheck_1294_; 
lean_dec(v_fst_1253_);
lean_del_object(v___x_1251_);
lean_dec(v_a_1244_);
v_a_1287_ = lean_ctor_get(v___x_1286_, 0);
v_isSharedCheck_1294_ = !lean_is_exclusive(v___x_1286_);
if (v_isSharedCheck_1294_ == 0)
{
v___x_1289_ = v___x_1286_;
v_isShared_1290_ = v_isSharedCheck_1294_;
goto v_resetjp_1288_;
}
else
{
lean_inc(v_a_1287_);
lean_dec(v___x_1286_);
v___x_1289_ = lean_box(0);
v_isShared_1290_ = v_isSharedCheck_1294_;
goto v_resetjp_1288_;
}
v_resetjp_1288_:
{
lean_object* v___x_1292_; 
if (v_isShared_1290_ == 0)
{
v___x_1292_ = v___x_1289_;
goto v_reusejp_1291_;
}
else
{
lean_object* v_reuseFailAlloc_1293_; 
v_reuseFailAlloc_1293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1293_, 0, v_a_1287_);
v___x_1292_ = v_reuseFailAlloc_1293_;
goto v_reusejp_1291_;
}
v_reusejp_1291_:
{
return v___x_1292_;
}
}
}
}
}
}
else
{
lean_dec(v_a_1273_);
lean_del_object(v___x_1265_);
lean_del_object(v___x_1256_);
lean_dec(v_introThm_1234_);
goto v___jp_1258_;
}
}
else
{
lean_object* v_a_1297_; lean_object* v___x_1299_; uint8_t v_isShared_1300_; uint8_t v_isSharedCheck_1304_; 
lean_dec(v_a_1273_);
lean_del_object(v___x_1265_);
lean_del_object(v___x_1256_);
lean_dec(v_fst_1253_);
lean_del_object(v___x_1251_);
lean_dec(v_a_1244_);
lean_dec(v_introThm_1234_);
v_a_1297_ = lean_ctor_get(v___x_1274_, 0);
v_isSharedCheck_1304_ = !lean_is_exclusive(v___x_1274_);
if (v_isSharedCheck_1304_ == 0)
{
v___x_1299_ = v___x_1274_;
v_isShared_1300_ = v_isSharedCheck_1304_;
goto v_resetjp_1298_;
}
else
{
lean_inc(v_a_1297_);
lean_dec(v___x_1274_);
v___x_1299_ = lean_box(0);
v_isShared_1300_ = v_isSharedCheck_1304_;
goto v_resetjp_1298_;
}
v_resetjp_1298_:
{
lean_object* v___x_1302_; 
if (v_isShared_1300_ == 0)
{
v___x_1302_ = v___x_1299_;
goto v_reusejp_1301_;
}
else
{
lean_object* v_reuseFailAlloc_1303_; 
v_reuseFailAlloc_1303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1303_, 0, v_a_1297_);
v___x_1302_ = v_reuseFailAlloc_1303_;
goto v_reusejp_1301_;
}
v_reusejp_1301_:
{
return v___x_1302_;
}
}
}
}
else
{
lean_del_object(v___x_1265_);
lean_dec(v_snd_1263_);
lean_del_object(v___x_1256_);
lean_dec(v_fst_1253_);
lean_del_object(v___x_1251_);
lean_dec(v_a_1244_);
lean_dec(v_introThm_1234_);
return v___x_1272_;
}
}
}
}
}
else
{
lean_object* v_a_1309_; lean_object* v___x_1311_; uint8_t v_isShared_1312_; uint8_t v_isSharedCheck_1316_; 
lean_dec(v_a_1244_);
lean_dec_ref(v_pre_1236_);
lean_dec_ref(v_opAs_1235_);
lean_dec(v_introThm_1234_);
v_a_1309_ = lean_ctor_get(v___x_1248_, 0);
v_isSharedCheck_1316_ = !lean_is_exclusive(v___x_1248_);
if (v_isSharedCheck_1316_ == 0)
{
v___x_1311_ = v___x_1248_;
v_isShared_1312_ = v_isSharedCheck_1316_;
goto v_resetjp_1310_;
}
else
{
lean_inc(v_a_1309_);
lean_dec(v___x_1248_);
v___x_1311_ = lean_box(0);
v_isShared_1312_ = v_isSharedCheck_1316_;
goto v_resetjp_1310_;
}
v_resetjp_1310_:
{
lean_object* v___x_1314_; 
if (v_isShared_1312_ == 0)
{
v___x_1314_ = v___x_1311_;
goto v_reusejp_1313_;
}
else
{
lean_object* v_reuseFailAlloc_1315_; 
v_reuseFailAlloc_1315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1315_, 0, v_a_1309_);
v___x_1314_ = v_reuseFailAlloc_1315_;
goto v_reusejp_1313_;
}
v_reusejp_1313_:
{
return v___x_1314_;
}
}
}
}
else
{
lean_dec(v_a_1244_);
lean_dec_ref(v_pre_1236_);
lean_dec_ref(v_opAs_1235_);
lean_dec(v_introThm_1234_);
return v___x_1245_;
}
}
else
{
lean_dec_ref(v_pre_1236_);
lean_dec_ref(v_opAs_1235_);
lean_dec(v_introThm_1234_);
return v___x_1243_;
}
}
else
{
lean_object* v___x_1317_; 
lean_inc(v_a_1241_);
lean_inc_ref(v_a_1240_);
lean_inc(v_a_1239_);
lean_inc_ref(v_a_1238_);
lean_inc_ref(v_pre_1236_);
v___x_1317_ = lean_infer_type(v_pre_1236_, v_a_1238_, v_a_1239_, v_a_1240_, v_a_1241_);
if (lean_obj_tag(v___x_1317_) == 0)
{
lean_object* v_a_1318_; lean_object* v___x_1319_; lean_object* v_s_1320_; lean_object* v___x_1321_; 
v_a_1318_ = lean_ctor_get(v___x_1317_, 0);
lean_inc(v_a_1318_);
lean_dec_ref_known(v___x_1317_, 1);
v___x_1319_ = l_Lean_instInhabitedExpr;
v_s_1320_ = l_List_getLast_x21___redArg(v___x_1319_, v_ss_1237_);
lean_inc(v_a_1241_);
lean_inc_ref(v_a_1240_);
lean_inc(v_a_1239_);
lean_inc_ref(v_a_1238_);
lean_inc(v_s_1320_);
v___x_1321_ = lean_infer_type(v_s_1320_, v_a_1238_, v_a_1239_, v_a_1240_, v_a_1241_);
if (lean_obj_tag(v___x_1321_) == 0)
{
lean_object* v_a_1322_; lean_object* v___f_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; 
v_a_1322_ = lean_ctor_get(v___x_1321_, 0);
lean_inc(v_a_1322_);
lean_dec_ref_known(v___x_1321_, 1);
lean_inc_ref(v_pre_1236_);
lean_inc(v_s_1320_);
v___f_1323_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply___lam__0___boxed), 9, 3);
lean_closure_set(v___f_1323_, 0, v_s_1320_);
lean_closure_set(v___f_1323_, 1, v_a_1318_);
lean_closure_set(v___f_1323_, 2, v_pre_1236_);
v___x_1324_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply___closed__3));
v___x_1325_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply_spec__0___redArg(v___x_1324_, v_a_1322_, v___f_1323_, v_a_1238_, v_a_1239_, v_a_1240_, v_a_1241_);
if (lean_obj_tag(v___x_1325_) == 0)
{
lean_object* v_a_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v_init_1329_; lean_object* v___x_1330_; lean_object* v_Q_1331_; lean_object* v___x_1332_; 
v_a_1326_ = lean_ctor_get(v___x_1325_, 0);
lean_inc(v_a_1326_);
lean_dec_ref_known(v___x_1325_, 1);
v___x_1327_ = lean_array_mk(v_ss_1237_);
v___x_1328_ = lean_array_pop(v___x_1327_);
v_init_1329_ = lean_array_to_list(v___x_1328_);
lean_inc(v_init_1329_);
v___x_1330_ = lean_array_mk(v_init_1329_);
lean_inc_ref(v_opAs_1235_);
v_Q_1331_ = l_Lean_mkAppN(v_opAs_1235_, v___x_1330_);
lean_dec_ref(v___x_1330_);
v___x_1332_ = l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply(v_introThm_1234_, v_opAs_1235_, v_a_1326_, v_init_1329_, v_a_1238_, v_a_1239_, v_a_1240_, v_a_1241_);
if (lean_obj_tag(v___x_1332_) == 0)
{
lean_object* v_a_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; 
v_a_1333_ = lean_ctor_get(v___x_1332_, 0);
lean_inc(v_a_1333_);
lean_dec_ref_known(v___x_1332_, 1);
v___x_1334_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply___closed__5));
v___x_1335_ = lean_unsigned_to_nat(4u);
v___x_1336_ = lean_mk_empty_array_with_capacity(v___x_1335_);
v___x_1337_ = lean_array_push(v___x_1336_, v_s_1320_);
v___x_1338_ = lean_array_push(v___x_1337_, v_pre_1236_);
v___x_1339_ = lean_array_push(v___x_1338_, v_Q_1331_);
v___x_1340_ = lean_array_push(v___x_1339_, v_a_1333_);
v___x_1341_ = l_Lean_Meta_mkAppM(v___x_1334_, v___x_1340_, v_a_1238_, v_a_1239_, v_a_1240_, v_a_1241_);
return v___x_1341_;
}
else
{
lean_dec_ref(v_Q_1331_);
lean_dec(v_s_1320_);
lean_dec_ref(v_pre_1236_);
return v___x_1332_;
}
}
else
{
lean_dec(v_s_1320_);
lean_dec(v_ss_1237_);
lean_dec_ref(v_pre_1236_);
lean_dec_ref(v_opAs_1235_);
lean_dec(v_introThm_1234_);
return v___x_1325_;
}
}
else
{
lean_dec(v_s_1320_);
lean_dec(v_a_1318_);
lean_dec(v_ss_1237_);
lean_dec_ref(v_pre_1236_);
lean_dec_ref(v_opAs_1235_);
lean_dec(v_introThm_1234_);
return v___x_1321_;
}
}
else
{
lean_dec(v_ss_1237_);
lean_dec_ref(v_pre_1236_);
lean_dec_ref(v_opAs_1235_);
lean_dec(v_introThm_1234_);
return v___x_1317_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply___boxed(lean_object* v_introThm_1342_, lean_object* v_opAs_1343_, lean_object* v_pre_1344_, lean_object* v_ss_1345_, lean_object* v_a_1346_, lean_object* v_a_1347_, lean_object* v_a_1348_, lean_object* v_a_1349_, lean_object* v_a_1350_){
_start:
{
lean_object* v_res_1351_; 
v_res_1351_ = l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply(v_introThm_1342_, v_opAs_1343_, v_pre_1344_, v_ss_1345_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
lean_dec(v_a_1349_);
lean_dec_ref(v_a_1348_);
lean_dec(v_a_1347_);
lean_dec_ref(v_a_1346_);
return v_res_1351_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply_spec__0_spec__0(lean_object* v_00_u03b1_1352_, lean_object* v_name_1353_, uint8_t v_bi_1354_, lean_object* v_type_1355_, lean_object* v_k_1356_, uint8_t v_kind_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_){
_start:
{
lean_object* v___x_1363_; 
v___x_1363_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply_spec__0_spec__0___redArg(v_name_1353_, v_bi_1354_, v_type_1355_, v_k_1356_, v_kind_1357_, v___y_1358_, v___y_1359_, v___y_1360_, v___y_1361_);
return v___x_1363_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1364_, lean_object* v_name_1365_, lean_object* v_bi_1366_, lean_object* v_type_1367_, lean_object* v_k_1368_, lean_object* v_kind_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_){
_start:
{
uint8_t v_bi_boxed_1375_; uint8_t v_kind_boxed_1376_; lean_object* v_res_1377_; 
v_bi_boxed_1375_ = lean_unbox(v_bi_1366_);
v_kind_boxed_1376_ = lean_unbox(v_kind_1369_);
v_res_1377_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply_spec__0_spec__0(v_00_u03b1_1364_, v_name_1365_, v_bi_boxed_1375_, v_type_1367_, v_k_1368_, v_kind_boxed_1376_, v___y_1370_, v___y_1371_, v___y_1372_, v___y_1373_);
lean_dec(v___y_1373_);
lean_dec_ref(v___y_1372_);
lean_dec(v___y_1371_);
lean_dec_ref(v___y_1370_);
return v_res_1377_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply_spec__0(lean_object* v_00_u03b1_1378_, lean_object* v_name_1379_, lean_object* v_type_1380_, lean_object* v_k_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_){
_start:
{
lean_object* v___x_1387_; 
v___x_1387_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply_spec__0___redArg(v_name_1379_, v_type_1380_, v_k_1381_, v___y_1382_, v___y_1383_, v___y_1384_, v___y_1385_);
return v___x_1387_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply_spec__0___boxed(lean_object* v_00_u03b1_1388_, lean_object* v_name_1389_, lean_object* v_type_1390_, lean_object* v_k_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_){
_start:
{
lean_object* v_res_1397_; 
v_res_1397_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply_spec__0(v_00_u03b1_1388_, v_name_1389_, v_type_1390_, v_k_1391_, v___y_1392_, v___y_1393_, v___y_1394_, v___y_1395_);
lean_dec(v___y_1395_);
lean_dec_ref(v___y_1394_);
lean_dec(v___y_1393_);
lean_dec_ref(v___y_1392_);
return v_res_1397_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__0___redArg(size_t v_sz_1398_, size_t v_i_1399_, lean_object* v_bs_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_){
_start:
{
uint8_t v___x_1406_; 
v___x_1406_ = lean_usize_dec_lt(v_i_1399_, v_sz_1398_);
if (v___x_1406_ == 0)
{
lean_object* v___x_1407_; 
v___x_1407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1407_, 0, v_bs_1400_);
return v___x_1407_;
}
else
{
lean_object* v_v_1408_; lean_object* v___x_1409_; lean_object* v_bs_x27_1410_; lean_object* v___y_1412_; lean_object* v___x_1426_; 
v_v_1408_ = lean_array_uget(v_bs_1400_, v_i_1399_);
v___x_1409_ = lean_unsigned_to_nat(0u);
v_bs_x27_1410_ = lean_array_uset(v_bs_1400_, v_i_1399_, v___x_1409_);
lean_inc(v___y_1404_);
lean_inc_ref(v___y_1403_);
lean_inc(v___y_1402_);
lean_inc_ref(v___y_1401_);
v___x_1426_ = lean_infer_type(v_v_1408_, v___y_1401_, v___y_1402_, v___y_1403_, v___y_1404_);
if (lean_obj_tag(v___x_1426_) == 0)
{
lean_object* v_a_1427_; lean_object* v___x_1429_; uint8_t v_isShared_1430_; uint8_t v_isSharedCheck_1437_; 
v_a_1427_ = lean_ctor_get(v___x_1426_, 0);
v_isSharedCheck_1437_ = !lean_is_exclusive(v___x_1426_);
if (v_isSharedCheck_1437_ == 0)
{
v___x_1429_ = v___x_1426_;
v_isShared_1430_ = v_isSharedCheck_1437_;
goto v_resetjp_1428_;
}
else
{
lean_inc(v_a_1427_);
lean_dec(v___x_1426_);
v___x_1429_ = lean_box(0);
v_isShared_1430_ = v_isSharedCheck_1437_;
goto v_resetjp_1428_;
}
v_resetjp_1428_:
{
lean_object* v___x_1432_; 
if (v_isShared_1430_ == 0)
{
lean_ctor_set_tag(v___x_1429_, 1);
v___x_1432_ = v___x_1429_;
goto v_reusejp_1431_;
}
else
{
lean_object* v_reuseFailAlloc_1436_; 
v_reuseFailAlloc_1436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1436_, 0, v_a_1427_);
v___x_1432_ = v_reuseFailAlloc_1436_;
goto v_reusejp_1431_;
}
v_reusejp_1431_:
{
uint8_t v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; 
v___x_1433_ = 0;
v___x_1434_ = lean_box(0);
v___x_1435_ = l_Lean_Meta_mkFreshExprMVar(v___x_1432_, v___x_1433_, v___x_1434_, v___y_1401_, v___y_1402_, v___y_1403_, v___y_1404_);
v___y_1412_ = v___x_1435_;
goto v___jp_1411_;
}
}
}
else
{
v___y_1412_ = v___x_1426_;
goto v___jp_1411_;
}
v___jp_1411_:
{
if (lean_obj_tag(v___y_1412_) == 0)
{
lean_object* v_a_1413_; size_t v___x_1414_; size_t v___x_1415_; lean_object* v___x_1416_; 
v_a_1413_ = lean_ctor_get(v___y_1412_, 0);
lean_inc(v_a_1413_);
lean_dec_ref_known(v___y_1412_, 1);
v___x_1414_ = ((size_t)1ULL);
v___x_1415_ = lean_usize_add(v_i_1399_, v___x_1414_);
v___x_1416_ = lean_array_uset(v_bs_x27_1410_, v_i_1399_, v_a_1413_);
v_i_1399_ = v___x_1415_;
v_bs_1400_ = v___x_1416_;
goto _start;
}
else
{
lean_object* v_a_1418_; lean_object* v___x_1420_; uint8_t v_isShared_1421_; uint8_t v_isSharedCheck_1425_; 
lean_dec_ref(v_bs_x27_1410_);
v_a_1418_ = lean_ctor_get(v___y_1412_, 0);
v_isSharedCheck_1425_ = !lean_is_exclusive(v___y_1412_);
if (v_isSharedCheck_1425_ == 0)
{
v___x_1420_ = v___y_1412_;
v_isShared_1421_ = v_isSharedCheck_1425_;
goto v_resetjp_1419_;
}
else
{
lean_inc(v_a_1418_);
lean_dec(v___y_1412_);
v___x_1420_ = lean_box(0);
v_isShared_1421_ = v_isSharedCheck_1425_;
goto v_resetjp_1419_;
}
v_resetjp_1419_:
{
lean_object* v___x_1423_; 
if (v_isShared_1421_ == 0)
{
v___x_1423_ = v___x_1420_;
goto v_reusejp_1422_;
}
else
{
lean_object* v_reuseFailAlloc_1424_; 
v_reuseFailAlloc_1424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1424_, 0, v_a_1418_);
v___x_1423_ = v_reuseFailAlloc_1424_;
goto v_reusejp_1422_;
}
v_reusejp_1422_:
{
return v___x_1423_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__0___redArg___boxed(lean_object* v_sz_1438_, lean_object* v_i_1439_, lean_object* v_bs_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_){
_start:
{
size_t v_sz_boxed_1446_; size_t v_i_boxed_1447_; lean_object* v_res_1448_; 
v_sz_boxed_1446_ = lean_unbox_usize(v_sz_1438_);
lean_dec(v_sz_1438_);
v_i_boxed_1447_ = lean_unbox_usize(v_i_1439_);
lean_dec(v_i_1439_);
v_res_1448_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__0___redArg(v_sz_boxed_1446_, v_i_boxed_1447_, v_bs_1440_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_);
lean_dec(v___y_1444_);
lean_dec_ref(v___y_1443_);
lean_dec(v___y_1442_);
lean_dec_ref(v___y_1441_);
return v_res_1448_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__1_spec__1___redArg(lean_object* v_m_1449_, lean_object* v_query_1450_){
_start:
{
lean_object* v___x_1451_; 
v___x_1451_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0___redArg(v_m_1449_, v_query_1450_);
if (lean_obj_tag(v___x_1451_) == 0)
{
lean_object* v_index_1452_; lean_object* v_key_1453_; lean_object* v_value_1454_; lean_object* v___x_1456_; uint8_t v_isShared_1457_; uint8_t v_isSharedCheck_1461_; 
v_index_1452_ = lean_ctor_get(v___x_1451_, 0);
v_key_1453_ = lean_ctor_get(v___x_1451_, 1);
v_value_1454_ = lean_ctor_get(v___x_1451_, 2);
v_isSharedCheck_1461_ = !lean_is_exclusive(v___x_1451_);
if (v_isSharedCheck_1461_ == 0)
{
v___x_1456_ = v___x_1451_;
v_isShared_1457_ = v_isSharedCheck_1461_;
goto v_resetjp_1455_;
}
else
{
lean_inc(v_value_1454_);
lean_inc(v_key_1453_);
lean_inc(v_index_1452_);
lean_dec(v___x_1451_);
v___x_1456_ = lean_box(0);
v_isShared_1457_ = v_isSharedCheck_1461_;
goto v_resetjp_1455_;
}
v_resetjp_1455_:
{
lean_object* v___x_1459_; 
if (v_isShared_1457_ == 0)
{
v___x_1459_ = v___x_1456_;
goto v_reusejp_1458_;
}
else
{
lean_object* v_reuseFailAlloc_1460_; 
v_reuseFailAlloc_1460_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1460_, 0, v_index_1452_);
lean_ctor_set(v_reuseFailAlloc_1460_, 1, v_key_1453_);
lean_ctor_set(v_reuseFailAlloc_1460_, 2, v_value_1454_);
v___x_1459_ = v_reuseFailAlloc_1460_;
goto v_reusejp_1458_;
}
v_reusejp_1458_:
{
return v___x_1459_;
}
}
}
else
{
lean_object* v___x_1462_; 
lean_dec(v___x_1451_);
v___x_1462_ = lean_box(1);
return v___x_1462_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__1_spec__1___redArg___boxed(lean_object* v_m_1463_, lean_object* v_query_1464_){
_start:
{
lean_object* v_res_1465_; 
v_res_1465_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__1_spec__1___redArg(v_m_1463_, v_query_1464_);
lean_dec(v_query_1464_);
lean_dec_ref(v_m_1463_);
return v_res_1465_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__1___redArg(lean_object* v_m_1466_, lean_object* v_a_1467_){
_start:
{
lean_object* v___x_1468_; 
v___x_1468_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__1_spec__1___redArg(v_m_1466_, v_a_1467_);
if (lean_obj_tag(v___x_1468_) == 0)
{
lean_object* v_value_1469_; lean_object* v___x_1470_; 
v_value_1469_ = lean_ctor_get(v___x_1468_, 2);
lean_inc(v_value_1469_);
lean_dec_ref_known(v___x_1468_, 3);
v___x_1470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1470_, 0, v_value_1469_);
return v___x_1470_;
}
else
{
lean_object* v___x_1471_; 
v___x_1471_ = lean_box(0);
return v___x_1471_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__1___redArg___boxed(lean_object* v_m_1472_, lean_object* v_a_1473_){
_start:
{
lean_object* v_res_1474_; 
v_res_1474_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__1___redArg(v_m_1472_, v_a_1473_);
lean_dec(v_a_1473_);
lean_dec_ref(v_m_1472_);
return v_res_1474_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__2___closed__4(void){
_start:
{
lean_object* v___x_1481_; lean_object* v___x_1482_; 
v___x_1481_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__2___closed__3));
v___x_1482_ = l_Lean_stringToMessageData(v___x_1481_);
return v___x_1482_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__2___closed__6(void){
_start:
{
lean_object* v___x_1484_; lean_object* v___x_1485_; 
v___x_1484_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__2___closed__5));
v___x_1485_ = l_Lean_stringToMessageData(v___x_1484_);
return v___x_1485_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__2___closed__7(void){
_start:
{
lean_object* v___x_1486_; lean_object* v_dummy_1487_; 
v___x_1486_ = lean_box(0);
v_dummy_1487_ = l_Lean_Expr_sort___override(v___x_1486_);
return v_dummy_1487_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__2(lean_object* v_op_1488_, lean_object* v___y_1489_, lean_object* v_a_1490_, lean_object* v_x_1491_, lean_object* v_x_1492_, lean_object* v_x_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_){
_start:
{
lean_object* v_prf_1502_; lean_object* v___y_1503_; lean_object* v___y_1504_; lean_object* v___y_1505_; lean_object* v___y_1506_; 
if (lean_obj_tag(v_x_1491_) == 5)
{
lean_object* v_fn_1523_; lean_object* v_arg_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; 
v_fn_1523_ = lean_ctor_get(v_x_1491_, 0);
lean_inc_ref(v_fn_1523_);
v_arg_1524_ = lean_ctor_get(v_x_1491_, 1);
lean_inc_ref(v_arg_1524_);
lean_dec_ref_known(v_x_1491_, 2);
v___x_1525_ = lean_array_set(v_x_1492_, v_x_1493_, v_arg_1524_);
v___x_1526_ = lean_unsigned_to_nat(1u);
v___x_1527_ = lean_nat_sub(v_x_1493_, v___x_1526_);
lean_dec(v_x_1493_);
v_x_1491_ = v_fn_1523_;
v_x_1492_ = v___x_1525_;
v_x_1493_ = v___x_1527_;
goto _start;
}
else
{
lean_object* v_head_1529_; lean_object* v_numConst_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; size_t v_sz_1533_; size_t v___x_1534_; lean_object* v___x_1535_; 
lean_dec(v_x_1493_);
v_head_1529_ = lean_ctor_get(v_op_1488_, 0);
lean_inc(v_head_1529_);
v_numConst_1530_ = lean_ctor_get(v_op_1488_, 1);
lean_inc_n(v_numConst_1530_, 2);
lean_dec_ref(v_op_1488_);
v___x_1531_ = lean_array_get_size(v_x_1492_);
v___x_1532_ = l_Array_extract___redArg(v_x_1492_, v_numConst_1530_, v___x_1531_);
v_sz_1533_ = lean_array_size(v___x_1532_);
v___x_1534_ = ((size_t)0ULL);
v___x_1535_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__0___redArg(v_sz_1533_, v___x_1534_, v___x_1532_, v___y_1496_, v___y_1497_, v___y_1498_, v___y_1499_);
if (lean_obj_tag(v___x_1535_) == 0)
{
lean_object* v_a_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; 
v_a_1536_ = lean_ctor_get(v___x_1535_, 0);
lean_inc(v_a_1536_);
lean_dec_ref_known(v___x_1535_, 1);
v___x_1537_ = lean_unsigned_to_nat(0u);
v___x_1538_ = l_Array_extract___redArg(v_x_1492_, v___x_1537_, v_numConst_1530_);
lean_dec_ref(v_x_1492_);
v___x_1539_ = l_Array_append___redArg(v___x_1538_, v_a_1536_);
lean_dec(v_a_1536_);
v___x_1540_ = l_Lean_mkAppN(v_x_1491_, v___x_1539_);
lean_dec_ref(v___x_1539_);
v___x_1541_ = lean_unsigned_to_nat(256u);
lean_inc_ref(v___x_1540_);
v___x_1542_ = l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp(v___y_1489_, v___x_1540_, v___x_1541_, v___y_1494_, v___y_1495_, v___y_1496_, v___y_1497_, v___y_1498_, v___y_1499_);
if (lean_obj_tag(v___x_1542_) == 0)
{
lean_object* v_a_1543_; lean_object* v_fst_1544_; lean_object* v_snd_1545_; lean_object* v___x_1547_; uint8_t v_isShared_1548_; uint8_t v_isSharedCheck_1717_; 
v_a_1543_ = lean_ctor_get(v___x_1542_, 0);
lean_inc(v_a_1543_);
lean_dec_ref_known(v___x_1542_, 1);
v_fst_1544_ = lean_ctor_get(v_a_1543_, 0);
v_snd_1545_ = lean_ctor_get(v_a_1543_, 1);
v_isSharedCheck_1717_ = !lean_is_exclusive(v_a_1543_);
if (v_isSharedCheck_1717_ == 0)
{
v___x_1547_ = v_a_1543_;
v_isShared_1548_ = v_isSharedCheck_1717_;
goto v_resetjp_1546_;
}
else
{
lean_inc(v_snd_1545_);
lean_inc(v_fst_1544_);
lean_dec(v_a_1543_);
v___x_1547_ = lean_box(0);
v_isShared_1548_ = v_isSharedCheck_1717_;
goto v_resetjp_1546_;
}
v_resetjp_1546_:
{
lean_object* v___x_1549_; 
lean_inc(v___y_1499_);
lean_inc_ref(v___y_1498_);
lean_inc(v___y_1497_);
lean_inc_ref(v___y_1496_);
v___x_1549_ = lean_infer_type(v___x_1540_, v___y_1496_, v___y_1497_, v___y_1498_, v___y_1499_);
if (lean_obj_tag(v___x_1549_) == 0)
{
lean_object* v_a_1550_; lean_object* v___x_1551_; uint8_t v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; 
v_a_1550_ = lean_ctor_get(v___x_1549_, 0);
lean_inc(v_a_1550_);
lean_dec_ref_known(v___x_1549_, 1);
v___x_1551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1551_, 0, v_a_1550_);
v___x_1552_ = 0;
v___x_1553_ = lean_box(0);
v___x_1554_ = l_Lean_Meta_mkFreshExprMVar(v___x_1551_, v___x_1552_, v___x_1553_, v___y_1496_, v___y_1497_, v___y_1498_, v___y_1499_);
if (lean_obj_tag(v___x_1554_) == 0)
{
lean_object* v_a_1555_; lean_object* v___y_1557_; lean_object* v___y_1558_; lean_object* v___y_1559_; lean_object* v___y_1560_; lean_object* v___y_1561_; lean_object* v___y_1562_; lean_object* v_a_1563_; lean_object* v___y_1611_; lean_object* v_eqProof_1612_; lean_object* v___y_1613_; lean_object* v___y_1614_; lean_object* v___y_1615_; lean_object* v___y_1616_; lean_object* v___x_1644_; lean_object* v___y_1646_; lean_object* v___x_1699_; 
v_a_1555_ = lean_ctor_get(v___x_1554_, 0);
lean_inc(v_a_1555_);
lean_dec_ref_known(v___x_1554_, 1);
v___x_1644_ = l_Lean_Expr_getAppFn(v_fst_1544_);
v___x_1699_ = l_Lean_Expr_constName_x3f(v___x_1644_);
if (lean_obj_tag(v___x_1699_) == 0)
{
v___y_1646_ = v___x_1553_;
goto v___jp_1645_;
}
else
{
lean_object* v_val_1700_; 
v_val_1700_ = lean_ctor_get(v___x_1699_, 0);
lean_inc(v_val_1700_);
lean_dec_ref_known(v___x_1699_, 1);
v___y_1646_ = v_val_1700_;
goto v___jp_1645_;
}
v___jp_1556_:
{
lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; 
v___x_1564_ = lean_unsigned_to_nat(1u);
v___x_1565_ = lean_mk_empty_array_with_capacity(v___x_1564_);
lean_inc_ref(v___x_1565_);
v___x_1566_ = lean_array_push(v___x_1565_, v_a_1555_);
v___x_1567_ = l_Lean_Meta_mkAppM(v___y_1557_, v___x_1566_, v___y_1559_, v___y_1561_, v___y_1558_, v___y_1560_);
if (lean_obj_tag(v___x_1567_) == 0)
{
lean_object* v_a_1568_; lean_object* v___x_1569_; 
v_a_1568_ = lean_ctor_get(v___x_1567_, 0);
lean_inc(v_a_1568_);
lean_dec_ref_known(v___x_1567_, 1);
v___x_1569_ = l_Lean_Meta_mkCongrArg(v_a_1568_, v___y_1562_, v___y_1559_, v___y_1561_, v___y_1558_, v___y_1560_);
if (lean_obj_tag(v___x_1569_) == 0)
{
lean_object* v_a_1570_; lean_object* v___x_1571_; 
v_a_1570_ = lean_ctor_get(v___x_1569_, 0);
lean_inc(v_a_1570_);
lean_dec_ref_known(v___x_1569_, 1);
v___x_1571_ = l_Lean_Meta_mkEqSymm(v_a_1570_, v___y_1559_, v___y_1561_, v___y_1558_, v___y_1560_);
if (lean_obj_tag(v___x_1571_) == 0)
{
lean_object* v_a_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; 
v_a_1572_ = lean_ctor_get(v___x_1571_, 0);
lean_inc(v_a_1572_);
lean_dec_ref_known(v___x_1571_, 1);
v___x_1573_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__2___closed__2));
v___x_1574_ = lean_array_push(v___x_1565_, v_a_1572_);
v___x_1575_ = l_Lean_Meta_mkAppM(v___x_1573_, v___x_1574_, v___y_1559_, v___y_1561_, v___y_1558_, v___y_1560_);
if (lean_obj_tag(v___x_1575_) == 0)
{
lean_object* v_a_1576_; lean_object* v___x_1577_; 
v_a_1576_ = lean_ctor_get(v___x_1575_, 0);
lean_inc(v_a_1576_);
lean_dec_ref_known(v___x_1575_, 1);
v___x_1577_ = l_Lean_Expr_app___override(v_a_1576_, v_a_1563_);
v_prf_1502_ = v___x_1577_;
v___y_1503_ = v___y_1559_;
v___y_1504_ = v___y_1561_;
v___y_1505_ = v___y_1558_;
v___y_1506_ = v___y_1560_;
goto v___jp_1501_;
}
else
{
lean_object* v_a_1578_; lean_object* v___x_1580_; uint8_t v_isShared_1581_; uint8_t v_isSharedCheck_1585_; 
lean_dec_ref(v_a_1563_);
v_a_1578_ = lean_ctor_get(v___x_1575_, 0);
v_isSharedCheck_1585_ = !lean_is_exclusive(v___x_1575_);
if (v_isSharedCheck_1585_ == 0)
{
v___x_1580_ = v___x_1575_;
v_isShared_1581_ = v_isSharedCheck_1585_;
goto v_resetjp_1579_;
}
else
{
lean_inc(v_a_1578_);
lean_dec(v___x_1575_);
v___x_1580_ = lean_box(0);
v_isShared_1581_ = v_isSharedCheck_1585_;
goto v_resetjp_1579_;
}
v_resetjp_1579_:
{
lean_object* v___x_1583_; 
if (v_isShared_1581_ == 0)
{
v___x_1583_ = v___x_1580_;
goto v_reusejp_1582_;
}
else
{
lean_object* v_reuseFailAlloc_1584_; 
v_reuseFailAlloc_1584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1584_, 0, v_a_1578_);
v___x_1583_ = v_reuseFailAlloc_1584_;
goto v_reusejp_1582_;
}
v_reusejp_1582_:
{
return v___x_1583_;
}
}
}
}
else
{
lean_object* v_a_1586_; lean_object* v___x_1588_; uint8_t v_isShared_1589_; uint8_t v_isSharedCheck_1593_; 
lean_dec_ref(v___x_1565_);
lean_dec_ref(v_a_1563_);
v_a_1586_ = lean_ctor_get(v___x_1571_, 0);
v_isSharedCheck_1593_ = !lean_is_exclusive(v___x_1571_);
if (v_isSharedCheck_1593_ == 0)
{
v___x_1588_ = v___x_1571_;
v_isShared_1589_ = v_isSharedCheck_1593_;
goto v_resetjp_1587_;
}
else
{
lean_inc(v_a_1586_);
lean_dec(v___x_1571_);
v___x_1588_ = lean_box(0);
v_isShared_1589_ = v_isSharedCheck_1593_;
goto v_resetjp_1587_;
}
v_resetjp_1587_:
{
lean_object* v___x_1591_; 
if (v_isShared_1589_ == 0)
{
v___x_1591_ = v___x_1588_;
goto v_reusejp_1590_;
}
else
{
lean_object* v_reuseFailAlloc_1592_; 
v_reuseFailAlloc_1592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1592_, 0, v_a_1586_);
v___x_1591_ = v_reuseFailAlloc_1592_;
goto v_reusejp_1590_;
}
v_reusejp_1590_:
{
return v___x_1591_;
}
}
}
}
else
{
lean_object* v_a_1594_; lean_object* v___x_1596_; uint8_t v_isShared_1597_; uint8_t v_isSharedCheck_1601_; 
lean_dec_ref(v___x_1565_);
lean_dec_ref(v_a_1563_);
v_a_1594_ = lean_ctor_get(v___x_1569_, 0);
v_isSharedCheck_1601_ = !lean_is_exclusive(v___x_1569_);
if (v_isSharedCheck_1601_ == 0)
{
v___x_1596_ = v___x_1569_;
v_isShared_1597_ = v_isSharedCheck_1601_;
goto v_resetjp_1595_;
}
else
{
lean_inc(v_a_1594_);
lean_dec(v___x_1569_);
v___x_1596_ = lean_box(0);
v_isShared_1597_ = v_isSharedCheck_1601_;
goto v_resetjp_1595_;
}
v_resetjp_1595_:
{
lean_object* v___x_1599_; 
if (v_isShared_1597_ == 0)
{
v___x_1599_ = v___x_1596_;
goto v_reusejp_1598_;
}
else
{
lean_object* v_reuseFailAlloc_1600_; 
v_reuseFailAlloc_1600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1600_, 0, v_a_1594_);
v___x_1599_ = v_reuseFailAlloc_1600_;
goto v_reusejp_1598_;
}
v_reusejp_1598_:
{
return v___x_1599_;
}
}
}
}
else
{
lean_object* v_a_1602_; lean_object* v___x_1604_; uint8_t v_isShared_1605_; uint8_t v_isSharedCheck_1609_; 
lean_dec_ref(v___x_1565_);
lean_dec_ref(v_a_1563_);
lean_dec_ref(v___y_1562_);
v_a_1602_ = lean_ctor_get(v___x_1567_, 0);
v_isSharedCheck_1609_ = !lean_is_exclusive(v___x_1567_);
if (v_isSharedCheck_1609_ == 0)
{
v___x_1604_ = v___x_1567_;
v_isShared_1605_ = v_isSharedCheck_1609_;
goto v_resetjp_1603_;
}
else
{
lean_inc(v_a_1602_);
lean_dec(v___x_1567_);
v___x_1604_ = lean_box(0);
v_isShared_1605_ = v_isSharedCheck_1609_;
goto v_resetjp_1603_;
}
v_resetjp_1603_:
{
lean_object* v___x_1607_; 
if (v_isShared_1605_ == 0)
{
v___x_1607_ = v___x_1604_;
goto v_reusejp_1606_;
}
else
{
lean_object* v_reuseFailAlloc_1608_; 
v_reuseFailAlloc_1608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1608_, 0, v_a_1602_);
v___x_1607_ = v_reuseFailAlloc_1608_;
goto v_reusejp_1606_;
}
v_reusejp_1606_:
{
return v___x_1607_;
}
}
}
}
v___jp_1610_:
{
lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; 
v___x_1617_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__2));
v___x_1618_ = lean_unsigned_to_nat(2u);
v___x_1619_ = lean_mk_empty_array_with_capacity(v___x_1618_);
lean_inc(v_a_1555_);
v___x_1620_ = lean_array_push(v___x_1619_, v_a_1555_);
v___x_1621_ = lean_array_push(v___x_1620_, v_fst_1544_);
v___x_1622_ = l_Lean_Meta_mkAppM(v___x_1617_, v___x_1621_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_);
if (lean_obj_tag(v___x_1622_) == 0)
{
if (lean_obj_tag(v___y_1611_) == 0)
{
lean_object* v_a_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; 
v_a_1623_ = lean_ctor_get(v___x_1622_, 0);
lean_inc(v_a_1623_);
lean_dec_ref_known(v___x_1622_, 1);
v___x_1624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1624_, 0, v_a_1623_);
v___x_1625_ = l_Lean_Meta_mkFreshExprMVar(v___x_1624_, v___x_1552_, v___x_1553_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_);
if (lean_obj_tag(v___x_1625_) == 0)
{
lean_object* v_a_1626_; 
v_a_1626_ = lean_ctor_get(v___x_1625_, 0);
lean_inc(v_a_1626_);
lean_dec_ref_known(v___x_1625_, 1);
v___y_1557_ = v___x_1617_;
v___y_1558_ = v___y_1615_;
v___y_1559_ = v___y_1613_;
v___y_1560_ = v___y_1616_;
v___y_1561_ = v___y_1614_;
v___y_1562_ = v_eqProof_1612_;
v_a_1563_ = v_a_1626_;
goto v___jp_1556_;
}
else
{
lean_object* v_a_1627_; lean_object* v___x_1629_; uint8_t v_isShared_1630_; uint8_t v_isSharedCheck_1634_; 
lean_dec_ref(v_eqProof_1612_);
lean_dec(v_a_1555_);
v_a_1627_ = lean_ctor_get(v___x_1625_, 0);
v_isSharedCheck_1634_ = !lean_is_exclusive(v___x_1625_);
if (v_isSharedCheck_1634_ == 0)
{
v___x_1629_ = v___x_1625_;
v_isShared_1630_ = v_isSharedCheck_1634_;
goto v_resetjp_1628_;
}
else
{
lean_inc(v_a_1627_);
lean_dec(v___x_1625_);
v___x_1629_ = lean_box(0);
v_isShared_1630_ = v_isSharedCheck_1634_;
goto v_resetjp_1628_;
}
v_resetjp_1628_:
{
lean_object* v___x_1632_; 
if (v_isShared_1630_ == 0)
{
v___x_1632_ = v___x_1629_;
goto v_reusejp_1631_;
}
else
{
lean_object* v_reuseFailAlloc_1633_; 
v_reuseFailAlloc_1633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1633_, 0, v_a_1627_);
v___x_1632_ = v_reuseFailAlloc_1633_;
goto v_reusejp_1631_;
}
v_reusejp_1631_:
{
return v___x_1632_;
}
}
}
}
else
{
lean_object* v_val_1635_; 
lean_dec_ref_known(v___x_1622_, 1);
v_val_1635_ = lean_ctor_get(v___y_1611_, 0);
lean_inc(v_val_1635_);
lean_dec_ref_known(v___y_1611_, 1);
v___y_1557_ = v___x_1617_;
v___y_1558_ = v___y_1615_;
v___y_1559_ = v___y_1613_;
v___y_1560_ = v___y_1616_;
v___y_1561_ = v___y_1614_;
v___y_1562_ = v_eqProof_1612_;
v_a_1563_ = v_val_1635_;
goto v___jp_1556_;
}
}
else
{
lean_object* v_a_1636_; lean_object* v___x_1638_; uint8_t v_isShared_1639_; uint8_t v_isSharedCheck_1643_; 
lean_dec_ref(v_eqProof_1612_);
lean_dec(v___y_1611_);
lean_dec(v_a_1555_);
v_a_1636_ = lean_ctor_get(v___x_1622_, 0);
v_isSharedCheck_1643_ = !lean_is_exclusive(v___x_1622_);
if (v_isSharedCheck_1643_ == 0)
{
v___x_1638_ = v___x_1622_;
v_isShared_1639_ = v_isSharedCheck_1643_;
goto v_resetjp_1637_;
}
else
{
lean_inc(v_a_1636_);
lean_dec(v___x_1622_);
v___x_1638_ = lean_box(0);
v_isShared_1639_ = v_isSharedCheck_1643_;
goto v_resetjp_1637_;
}
v_resetjp_1637_:
{
lean_object* v___x_1641_; 
if (v_isShared_1639_ == 0)
{
v___x_1641_ = v___x_1638_;
goto v_reusejp_1640_;
}
else
{
lean_object* v_reuseFailAlloc_1642_; 
v_reuseFailAlloc_1642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1642_, 0, v_a_1636_);
v___x_1641_ = v_reuseFailAlloc_1642_;
goto v_reusejp_1640_;
}
v_reusejp_1640_:
{
return v___x_1641_;
}
}
}
}
v___jp_1645_:
{
lean_object* v___x_1647_; 
v___x_1647_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__1___redArg(v_a_1490_, v___y_1646_);
lean_dec(v___y_1646_);
if (lean_obj_tag(v___x_1647_) == 0)
{
lean_dec_ref(v___x_1644_);
if (lean_obj_tag(v_snd_1545_) == 0)
{
lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1651_; 
lean_dec(v_a_1555_);
lean_dec(v_fst_1544_);
v___x_1648_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__2___closed__4, &l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__2___closed__4_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__2___closed__4);
v___x_1649_ = l_Lean_MessageData_ofName(v_head_1529_);
if (v_isShared_1548_ == 0)
{
lean_ctor_set_tag(v___x_1547_, 7);
lean_ctor_set(v___x_1547_, 1, v___x_1649_);
lean_ctor_set(v___x_1547_, 0, v___x_1648_);
v___x_1651_ = v___x_1547_;
goto v_reusejp_1650_;
}
else
{
lean_object* v_reuseFailAlloc_1663_; 
v_reuseFailAlloc_1663_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1663_, 0, v___x_1648_);
lean_ctor_set(v_reuseFailAlloc_1663_, 1, v___x_1649_);
v___x_1651_ = v_reuseFailAlloc_1663_;
goto v_reusejp_1650_;
}
v_reusejp_1650_:
{
lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v_a_1655_; lean_object* v___x_1657_; uint8_t v_isShared_1658_; uint8_t v_isSharedCheck_1662_; 
v___x_1652_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__2___closed__6, &l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__2___closed__6_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__2___closed__6);
v___x_1653_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1653_, 0, v___x_1651_);
lean_ctor_set(v___x_1653_, 1, v___x_1652_);
v___x_1654_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_go_spec__0___redArg(v___x_1653_, v___y_1496_, v___y_1497_, v___y_1498_, v___y_1499_);
v_a_1655_ = lean_ctor_get(v___x_1654_, 0);
v_isSharedCheck_1662_ = !lean_is_exclusive(v___x_1654_);
if (v_isSharedCheck_1662_ == 0)
{
v___x_1657_ = v___x_1654_;
v_isShared_1658_ = v_isSharedCheck_1662_;
goto v_resetjp_1656_;
}
else
{
lean_inc(v_a_1655_);
lean_dec(v___x_1654_);
v___x_1657_ = lean_box(0);
v_isShared_1658_ = v_isSharedCheck_1662_;
goto v_resetjp_1656_;
}
v_resetjp_1656_:
{
lean_object* v___x_1660_; 
if (v_isShared_1658_ == 0)
{
v___x_1660_ = v___x_1657_;
goto v_reusejp_1659_;
}
else
{
lean_object* v_reuseFailAlloc_1661_; 
v_reuseFailAlloc_1661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1661_, 0, v_a_1655_);
v___x_1660_ = v_reuseFailAlloc_1661_;
goto v_reusejp_1659_;
}
v_reusejp_1659_:
{
return v___x_1660_;
}
}
}
}
else
{
lean_object* v_val_1664_; lean_object* v___x_1665_; 
lean_del_object(v___x_1547_);
lean_dec(v_head_1529_);
v_val_1664_ = lean_ctor_get(v_snd_1545_, 0);
lean_inc(v_val_1664_);
lean_dec_ref_known(v_snd_1545_, 1);
v___x_1665_ = lean_box(0);
v___y_1611_ = v___x_1665_;
v_eqProof_1612_ = v_val_1664_;
v___y_1613_ = v___y_1496_;
v___y_1614_ = v___y_1497_;
v___y_1615_ = v___y_1498_;
v___y_1616_ = v___y_1499_;
goto v___jp_1610_;
}
}
else
{
lean_object* v_val_1666_; lean_object* v_fst_1667_; lean_object* v_snd_1668_; lean_object* v_dummy_1669_; lean_object* v_nargs_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; 
lean_del_object(v___x_1547_);
lean_dec(v_head_1529_);
v_val_1666_ = lean_ctor_get(v___x_1647_, 0);
lean_inc(v_val_1666_);
lean_dec_ref_known(v___x_1647_, 1);
v_fst_1667_ = lean_ctor_get(v_val_1666_, 0);
lean_inc(v_fst_1667_);
v_snd_1668_ = lean_ctor_get(v_val_1666_, 1);
lean_inc_n(v_snd_1668_, 2);
lean_dec(v_val_1666_);
v_dummy_1669_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__2___closed__7, &l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__2___closed__7_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__2___closed__7);
v_nargs_1670_ = l_Lean_Expr_getAppNumArgs(v_fst_1544_);
lean_inc(v_nargs_1670_);
v___x_1671_ = lean_mk_array(v_nargs_1670_, v_dummy_1669_);
v___x_1672_ = lean_unsigned_to_nat(1u);
v___x_1673_ = lean_nat_sub(v_nargs_1670_, v___x_1672_);
lean_dec(v_nargs_1670_);
lean_inc(v_fst_1544_);
v___x_1674_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_fst_1544_, v___x_1671_, v___x_1673_);
v___x_1675_ = l_Array_extract___redArg(v___x_1674_, v___x_1537_, v_snd_1668_);
v___x_1676_ = l_Lean_mkAppN(v___x_1644_, v___x_1675_);
lean_dec_ref(v___x_1675_);
v___x_1677_ = lean_array_get_size(v___x_1674_);
v___x_1678_ = l_Array_extract___redArg(v___x_1674_, v_snd_1668_, v___x_1677_);
lean_dec_ref(v___x_1674_);
v___x_1679_ = lean_array_to_list(v___x_1678_);
lean_inc(v_a_1555_);
v___x_1680_ = l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply(v_fst_1667_, v___x_1676_, v_a_1555_, v___x_1679_, v___y_1496_, v___y_1497_, v___y_1498_, v___y_1499_);
if (lean_obj_tag(v___x_1680_) == 0)
{
if (lean_obj_tag(v_snd_1545_) == 0)
{
lean_object* v_a_1681_; 
lean_dec(v_a_1555_);
lean_dec(v_fst_1544_);
v_a_1681_ = lean_ctor_get(v___x_1680_, 0);
lean_inc(v_a_1681_);
lean_dec_ref_known(v___x_1680_, 1);
v_prf_1502_ = v_a_1681_;
v___y_1503_ = v___y_1496_;
v___y_1504_ = v___y_1497_;
v___y_1505_ = v___y_1498_;
v___y_1506_ = v___y_1499_;
goto v___jp_1501_;
}
else
{
lean_object* v_a_1682_; lean_object* v_val_1683_; lean_object* v___x_1685_; uint8_t v_isShared_1686_; uint8_t v_isSharedCheck_1690_; 
v_a_1682_ = lean_ctor_get(v___x_1680_, 0);
lean_inc(v_a_1682_);
lean_dec_ref_known(v___x_1680_, 1);
v_val_1683_ = lean_ctor_get(v_snd_1545_, 0);
v_isSharedCheck_1690_ = !lean_is_exclusive(v_snd_1545_);
if (v_isSharedCheck_1690_ == 0)
{
v___x_1685_ = v_snd_1545_;
v_isShared_1686_ = v_isSharedCheck_1690_;
goto v_resetjp_1684_;
}
else
{
lean_inc(v_val_1683_);
lean_dec(v_snd_1545_);
v___x_1685_ = lean_box(0);
v_isShared_1686_ = v_isSharedCheck_1690_;
goto v_resetjp_1684_;
}
v_resetjp_1684_:
{
lean_object* v___x_1688_; 
if (v_isShared_1686_ == 0)
{
lean_ctor_set(v___x_1685_, 0, v_a_1682_);
v___x_1688_ = v___x_1685_;
goto v_reusejp_1687_;
}
else
{
lean_object* v_reuseFailAlloc_1689_; 
v_reuseFailAlloc_1689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1689_, 0, v_a_1682_);
v___x_1688_ = v_reuseFailAlloc_1689_;
goto v_reusejp_1687_;
}
v_reusejp_1687_:
{
v___y_1611_ = v___x_1688_;
v_eqProof_1612_ = v_val_1683_;
v___y_1613_ = v___y_1496_;
v___y_1614_ = v___y_1497_;
v___y_1615_ = v___y_1498_;
v___y_1616_ = v___y_1499_;
goto v___jp_1610_;
}
}
}
}
else
{
lean_object* v_a_1691_; lean_object* v___x_1693_; uint8_t v_isShared_1694_; uint8_t v_isSharedCheck_1698_; 
lean_dec(v_a_1555_);
lean_dec(v_snd_1545_);
lean_dec(v_fst_1544_);
v_a_1691_ = lean_ctor_get(v___x_1680_, 0);
v_isSharedCheck_1698_ = !lean_is_exclusive(v___x_1680_);
if (v_isSharedCheck_1698_ == 0)
{
v___x_1693_ = v___x_1680_;
v_isShared_1694_ = v_isSharedCheck_1698_;
goto v_resetjp_1692_;
}
else
{
lean_inc(v_a_1691_);
lean_dec(v___x_1680_);
v___x_1693_ = lean_box(0);
v_isShared_1694_ = v_isSharedCheck_1698_;
goto v_resetjp_1692_;
}
v_resetjp_1692_:
{
lean_object* v___x_1696_; 
if (v_isShared_1694_ == 0)
{
v___x_1696_ = v___x_1693_;
goto v_reusejp_1695_;
}
else
{
lean_object* v_reuseFailAlloc_1697_; 
v_reuseFailAlloc_1697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1697_, 0, v_a_1691_);
v___x_1696_ = v_reuseFailAlloc_1697_;
goto v_reusejp_1695_;
}
v_reusejp_1695_:
{
return v___x_1696_;
}
}
}
}
}
}
else
{
lean_object* v_a_1701_; lean_object* v___x_1703_; uint8_t v_isShared_1704_; uint8_t v_isSharedCheck_1708_; 
lean_del_object(v___x_1547_);
lean_dec(v_snd_1545_);
lean_dec(v_fst_1544_);
lean_dec(v_head_1529_);
v_a_1701_ = lean_ctor_get(v___x_1554_, 0);
v_isSharedCheck_1708_ = !lean_is_exclusive(v___x_1554_);
if (v_isSharedCheck_1708_ == 0)
{
v___x_1703_ = v___x_1554_;
v_isShared_1704_ = v_isSharedCheck_1708_;
goto v_resetjp_1702_;
}
else
{
lean_inc(v_a_1701_);
lean_dec(v___x_1554_);
v___x_1703_ = lean_box(0);
v_isShared_1704_ = v_isSharedCheck_1708_;
goto v_resetjp_1702_;
}
v_resetjp_1702_:
{
lean_object* v___x_1706_; 
if (v_isShared_1704_ == 0)
{
v___x_1706_ = v___x_1703_;
goto v_reusejp_1705_;
}
else
{
lean_object* v_reuseFailAlloc_1707_; 
v_reuseFailAlloc_1707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1707_, 0, v_a_1701_);
v___x_1706_ = v_reuseFailAlloc_1707_;
goto v_reusejp_1705_;
}
v_reusejp_1705_:
{
return v___x_1706_;
}
}
}
}
else
{
lean_object* v_a_1709_; lean_object* v___x_1711_; uint8_t v_isShared_1712_; uint8_t v_isSharedCheck_1716_; 
lean_del_object(v___x_1547_);
lean_dec(v_snd_1545_);
lean_dec(v_fst_1544_);
lean_dec(v_head_1529_);
v_a_1709_ = lean_ctor_get(v___x_1549_, 0);
v_isSharedCheck_1716_ = !lean_is_exclusive(v___x_1549_);
if (v_isSharedCheck_1716_ == 0)
{
v___x_1711_ = v___x_1549_;
v_isShared_1712_ = v_isSharedCheck_1716_;
goto v_resetjp_1710_;
}
else
{
lean_inc(v_a_1709_);
lean_dec(v___x_1549_);
v___x_1711_ = lean_box(0);
v_isShared_1712_ = v_isSharedCheck_1716_;
goto v_resetjp_1710_;
}
v_resetjp_1710_:
{
lean_object* v___x_1714_; 
if (v_isShared_1712_ == 0)
{
v___x_1714_ = v___x_1711_;
goto v_reusejp_1713_;
}
else
{
lean_object* v_reuseFailAlloc_1715_; 
v_reuseFailAlloc_1715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1715_, 0, v_a_1709_);
v___x_1714_ = v_reuseFailAlloc_1715_;
goto v_reusejp_1713_;
}
v_reusejp_1713_:
{
return v___x_1714_;
}
}
}
}
}
else
{
lean_object* v_a_1718_; lean_object* v___x_1720_; uint8_t v_isShared_1721_; uint8_t v_isSharedCheck_1725_; 
lean_dec_ref(v___x_1540_);
lean_dec(v_head_1529_);
v_a_1718_ = lean_ctor_get(v___x_1542_, 0);
v_isSharedCheck_1725_ = !lean_is_exclusive(v___x_1542_);
if (v_isSharedCheck_1725_ == 0)
{
v___x_1720_ = v___x_1542_;
v_isShared_1721_ = v_isSharedCheck_1725_;
goto v_resetjp_1719_;
}
else
{
lean_inc(v_a_1718_);
lean_dec(v___x_1542_);
v___x_1720_ = lean_box(0);
v_isShared_1721_ = v_isSharedCheck_1725_;
goto v_resetjp_1719_;
}
v_resetjp_1719_:
{
lean_object* v___x_1723_; 
if (v_isShared_1721_ == 0)
{
v___x_1723_ = v___x_1720_;
goto v_reusejp_1722_;
}
else
{
lean_object* v_reuseFailAlloc_1724_; 
v_reuseFailAlloc_1724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1724_, 0, v_a_1718_);
v___x_1723_ = v_reuseFailAlloc_1724_;
goto v_reusejp_1722_;
}
v_reusejp_1722_:
{
return v___x_1723_;
}
}
}
}
else
{
lean_object* v_a_1726_; lean_object* v___x_1728_; uint8_t v_isShared_1729_; uint8_t v_isSharedCheck_1733_; 
lean_dec(v_numConst_1530_);
lean_dec(v_head_1529_);
lean_dec_ref(v_x_1492_);
lean_dec_ref(v_x_1491_);
v_a_1726_ = lean_ctor_get(v___x_1535_, 0);
v_isSharedCheck_1733_ = !lean_is_exclusive(v___x_1535_);
if (v_isSharedCheck_1733_ == 0)
{
v___x_1728_ = v___x_1535_;
v_isShared_1729_ = v_isSharedCheck_1733_;
goto v_resetjp_1727_;
}
else
{
lean_inc(v_a_1726_);
lean_dec(v___x_1535_);
v___x_1728_ = lean_box(0);
v_isShared_1729_ = v_isSharedCheck_1733_;
goto v_resetjp_1727_;
}
v_resetjp_1727_:
{
lean_object* v___x_1731_; 
if (v_isShared_1729_ == 0)
{
v___x_1731_ = v___x_1728_;
goto v_reusejp_1730_;
}
else
{
lean_object* v_reuseFailAlloc_1732_; 
v_reuseFailAlloc_1732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1732_, 0, v_a_1726_);
v___x_1731_ = v_reuseFailAlloc_1732_;
goto v_reusejp_1730_;
}
v_reusejp_1730_:
{
return v___x_1731_;
}
}
}
}
v___jp_1501_:
{
uint8_t v___x_1507_; lean_object* v___x_1508_; 
v___x_1507_ = 1;
v___x_1508_ = l_Lean_Meta_abstractMVars(v_prf_1502_, v___x_1507_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_);
if (lean_obj_tag(v___x_1508_) == 0)
{
lean_object* v_a_1509_; lean_object* v_paramNames_1510_; lean_object* v_expr_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; 
v_a_1509_ = lean_ctor_get(v___x_1508_, 0);
lean_inc(v_a_1509_);
lean_dec_ref_known(v___x_1508_, 1);
v_paramNames_1510_ = lean_ctor_get(v_a_1509_, 0);
lean_inc_ref(v_paramNames_1510_);
v_expr_1511_ = lean_ctor_get(v_a_1509_, 2);
lean_inc_ref(v_expr_1511_);
lean_dec(v_a_1509_);
v___x_1512_ = lean_array_to_list(v_paramNames_1510_);
v___x_1513_ = lean_box(0);
v___x_1514_ = l_Lean_Meta_Sym_mkBackwardRuleFromExpr(v_expr_1511_, v___x_1512_, v___x_1513_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_);
return v___x_1514_;
}
else
{
lean_object* v_a_1515_; lean_object* v___x_1517_; uint8_t v_isShared_1518_; uint8_t v_isSharedCheck_1522_; 
v_a_1515_ = lean_ctor_get(v___x_1508_, 0);
v_isSharedCheck_1522_ = !lean_is_exclusive(v___x_1508_);
if (v_isSharedCheck_1522_ == 0)
{
v___x_1517_ = v___x_1508_;
v_isShared_1518_ = v_isSharedCheck_1522_;
goto v_resetjp_1516_;
}
else
{
lean_inc(v_a_1515_);
lean_dec(v___x_1508_);
v___x_1517_ = lean_box(0);
v_isShared_1518_ = v_isSharedCheck_1522_;
goto v_resetjp_1516_;
}
v_resetjp_1516_:
{
lean_object* v___x_1520_; 
if (v_isShared_1518_ == 0)
{
v___x_1520_ = v___x_1517_;
goto v_reusejp_1519_;
}
else
{
lean_object* v_reuseFailAlloc_1521_; 
v_reuseFailAlloc_1521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1521_, 0, v_a_1515_);
v___x_1520_ = v_reuseFailAlloc_1521_;
goto v_reusejp_1519_;
}
v_reusejp_1519_:
{
return v___x_1520_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__2___boxed(lean_object* v_op_1734_, lean_object* v___y_1735_, lean_object* v_a_1736_, lean_object* v_x_1737_, lean_object* v_x_1738_, lean_object* v_x_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_){
_start:
{
lean_object* v_res_1747_; 
v_res_1747_ = l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__2(v_op_1734_, v___y_1735_, v_a_1736_, v_x_1737_, v_x_1738_, v_x_1739_, v___y_1740_, v___y_1741_, v___y_1742_, v___y_1743_, v___y_1744_, v___y_1745_);
lean_dec(v___y_1745_);
lean_dec_ref(v___y_1744_);
lean_dec(v___y_1743_);
lean_dec_ref(v___y_1742_);
lean_dec(v___y_1741_);
lean_dec_ref(v___y_1740_);
lean_dec_ref(v_a_1736_);
lean_dec_ref(v___y_1735_);
return v_res_1747_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__4(lean_object* v_as_1748_, size_t v_i_1749_, size_t v_stop_1750_, lean_object* v_b_1751_){
_start:
{
uint8_t v___x_1752_; 
v___x_1752_ = lean_usize_dec_eq(v_i_1749_, v_stop_1750_);
if (v___x_1752_ == 0)
{
lean_object* v___x_1753_; lean_object* v_rewrites_1754_; lean_object* v___x_1755_; size_t v___x_1756_; size_t v___x_1757_; 
v___x_1753_ = lean_array_uget_borrowed(v_as_1748_, v_i_1749_);
v_rewrites_1754_ = lean_ctor_get(v___x_1753_, 2);
v___x_1755_ = l_Array_append___redArg(v_b_1751_, v_rewrites_1754_);
v___x_1756_ = ((size_t)1ULL);
v___x_1757_ = lean_usize_add(v_i_1749_, v___x_1756_);
v_i_1749_ = v___x_1757_;
v_b_1751_ = v___x_1755_;
goto _start;
}
else
{
return v_b_1751_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__4___boxed(lean_object* v_as_1759_, lean_object* v_i_1760_, lean_object* v_stop_1761_, lean_object* v_b_1762_){
_start:
{
size_t v_i_boxed_1763_; size_t v_stop_boxed_1764_; lean_object* v_res_1765_; 
v_i_boxed_1763_ = lean_unbox_usize(v_i_1760_);
lean_dec(v_i_1760_);
v_stop_boxed_1764_ = lean_unbox_usize(v_stop_1761_);
lean_dec(v_stop_1761_);
v_res_1765_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__4(v_as_1759_, v_i_boxed_1763_, v_stop_boxed_1764_, v_b_1762_);
lean_dec_ref(v_as_1759_);
return v_res_1765_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__3(lean_object* v_as_1766_, size_t v_i_1767_, size_t v_stop_1768_, lean_object* v_b_1769_){
_start:
{
lean_object* v___y_1771_; uint8_t v___x_1775_; 
v___x_1775_ = lean_usize_dec_eq(v_i_1767_, v_stop_1768_);
if (v___x_1775_ == 0)
{
lean_object* v___x_1776_; lean_object* v_terminal_x3f_1777_; 
v___x_1776_ = lean_array_uget_borrowed(v_as_1766_, v_i_1767_);
v_terminal_x3f_1777_ = lean_ctor_get(v___x_1776_, 3);
if (lean_obj_tag(v_terminal_x3f_1777_) == 0)
{
lean_object* v___x_1778_; lean_object* v___x_1779_; 
v___x_1778_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__3));
v___x_1779_ = l_Array_append___redArg(v_b_1769_, v___x_1778_);
v___y_1771_ = v___x_1779_;
goto v___jp_1770_;
}
else
{
lean_object* v_val_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; 
v_val_1780_ = lean_ctor_get(v_terminal_x3f_1777_, 0);
v___x_1781_ = lean_unsigned_to_nat(1u);
v___x_1782_ = lean_mk_empty_array_with_capacity(v___x_1781_);
lean_inc(v_val_1780_);
v___x_1783_ = lean_array_push(v___x_1782_, v_val_1780_);
v___x_1784_ = l_Array_append___redArg(v_b_1769_, v___x_1783_);
lean_dec_ref(v___x_1783_);
v___y_1771_ = v___x_1784_;
goto v___jp_1770_;
}
}
else
{
return v_b_1769_;
}
v___jp_1770_:
{
size_t v___x_1772_; size_t v___x_1773_; 
v___x_1772_ = ((size_t)1ULL);
v___x_1773_ = lean_usize_add(v_i_1767_, v___x_1772_);
v_i_1767_ = v___x_1773_;
v_b_1769_ = v___y_1771_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__3___boxed(lean_object* v_as_1785_, lean_object* v_i_1786_, lean_object* v_stop_1787_, lean_object* v_b_1788_){
_start:
{
size_t v_i_boxed_1789_; size_t v_stop_boxed_1790_; lean_object* v_res_1791_; 
v_i_boxed_1789_ = lean_unbox_usize(v_i_1786_);
lean_dec(v_i_1786_);
v_stop_boxed_1790_ = lean_unbox_usize(v_stop_1787_);
lean_dec(v_stop_1787_);
v_res_1791_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__3(v_as_1785_, v_i_boxed_1789_, v_stop_boxed_1790_, v_b_1788_);
lean_dec_ref(v_as_1785_);
return v_res_1791_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_mkLatticeOpRule___closed__0(void){
_start:
{
lean_object* v___x_1792_; size_t v___x_1793_; size_t v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; 
v___x_1792_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__3));
v___x_1793_ = lean_usize_once(&l_Lean_Elab_Tactic_VCGen_latticeOps___closed__6, &l_Lean_Elab_Tactic_VCGen_latticeOps___closed__6_once, _init_l_Lean_Elab_Tactic_VCGen_latticeOps___closed__6);
v___x_1794_ = ((size_t)0ULL);
v___x_1795_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_builtinLatticeOps));
v___x_1796_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__3(v___x_1795_, v___x_1794_, v___x_1793_, v___x_1792_);
return v___x_1796_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_mkLatticeOpRule(lean_object* v_rhs_1797_, lean_object* v_op_1798_, lean_object* v_a_1799_, lean_object* v_a_1800_, lean_object* v_a_1801_, lean_object* v_a_1802_, lean_object* v_a_1803_, lean_object* v_a_1804_){
_start:
{
lean_object* v___y_1807_; lean_object* v___y_1808_; lean_object* v___y_1809_; lean_object* v_rewrites_1827_; lean_object* v_terminal_x3f_1828_; lean_object* v___x_1829_; lean_object* v___y_1831_; lean_object* v___y_1832_; lean_object* v___y_1839_; uint8_t v___x_1845_; 
v_rewrites_1827_ = lean_ctor_get(v_op_1798_, 2);
v_terminal_x3f_1828_ = lean_ctor_get(v_op_1798_, 3);
v___x_1829_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_builtinLatticeOps));
v___x_1845_ = lean_uint8_once(&l_Lean_Elab_Tactic_VCGen_latticeOps___closed__4, &l_Lean_Elab_Tactic_VCGen_latticeOps___closed__4_once, _init_l_Lean_Elab_Tactic_VCGen_latticeOps___closed__4);
if (v___x_1845_ == 0)
{
lean_inc_ref(v_rewrites_1827_);
v___y_1839_ = v_rewrites_1827_;
goto v___jp_1838_;
}
else
{
uint8_t v___x_1846_; 
v___x_1846_ = lean_uint8_once(&l_Lean_Elab_Tactic_VCGen_latticeOps___closed__5, &l_Lean_Elab_Tactic_VCGen_latticeOps___closed__5_once, _init_l_Lean_Elab_Tactic_VCGen_latticeOps___closed__5);
if (v___x_1846_ == 0)
{
if (v___x_1845_ == 0)
{
lean_inc_ref(v_rewrites_1827_);
v___y_1839_ = v_rewrites_1827_;
goto v___jp_1838_;
}
else
{
size_t v___x_1847_; size_t v___x_1848_; lean_object* v___x_1849_; 
v___x_1847_ = ((size_t)0ULL);
v___x_1848_ = lean_usize_once(&l_Lean_Elab_Tactic_VCGen_latticeOps___closed__6, &l_Lean_Elab_Tactic_VCGen_latticeOps___closed__6_once, _init_l_Lean_Elab_Tactic_VCGen_latticeOps___closed__6);
lean_inc_ref(v_rewrites_1827_);
v___x_1849_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__4(v___x_1829_, v___x_1847_, v___x_1848_, v_rewrites_1827_);
v___y_1839_ = v___x_1849_;
goto v___jp_1838_;
}
}
else
{
size_t v___x_1850_; size_t v___x_1851_; lean_object* v___x_1852_; 
v___x_1850_ = ((size_t)0ULL);
v___x_1851_ = lean_usize_once(&l_Lean_Elab_Tactic_VCGen_latticeOps___closed__6, &l_Lean_Elab_Tactic_VCGen_latticeOps___closed__6_once, _init_l_Lean_Elab_Tactic_VCGen_latticeOps___closed__6);
lean_inc_ref(v_rewrites_1827_);
v___x_1852_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__4(v___x_1829_, v___x_1850_, v___x_1851_, v_rewrites_1827_);
v___y_1839_ = v___x_1852_;
goto v___jp_1838_;
}
}
v___jp_1806_:
{
lean_object* v___x_1810_; lean_object* v___x_1811_; 
lean_inc_ref(v___y_1807_);
v___x_1810_ = l_Array_append___redArg(v___y_1807_, v___y_1809_);
lean_dec_ref(v___y_1809_);
v___x_1811_ = l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals(v___x_1810_, v_a_1801_, v_a_1802_, v_a_1803_, v_a_1804_);
lean_dec_ref(v___x_1810_);
if (lean_obj_tag(v___x_1811_) == 0)
{
lean_object* v_a_1812_; lean_object* v_dummy_1813_; lean_object* v_nargs_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; 
v_a_1812_ = lean_ctor_get(v___x_1811_, 0);
lean_inc(v_a_1812_);
lean_dec_ref_known(v___x_1811_, 1);
v_dummy_1813_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__2___closed__7, &l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__2___closed__7_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__2___closed__7);
v_nargs_1814_ = l_Lean_Expr_getAppNumArgs(v_rhs_1797_);
lean_inc(v_nargs_1814_);
v___x_1815_ = lean_mk_array(v_nargs_1814_, v_dummy_1813_);
v___x_1816_ = lean_unsigned_to_nat(1u);
v___x_1817_ = lean_nat_sub(v_nargs_1814_, v___x_1816_);
lean_dec(v_nargs_1814_);
v___x_1818_ = l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__2(v_op_1798_, v___y_1808_, v_a_1812_, v_rhs_1797_, v___x_1815_, v___x_1817_, v_a_1799_, v_a_1800_, v_a_1801_, v_a_1802_, v_a_1803_, v_a_1804_);
lean_dec(v_a_1812_);
lean_dec_ref(v___y_1808_);
return v___x_1818_;
}
else
{
lean_object* v_a_1819_; lean_object* v___x_1821_; uint8_t v_isShared_1822_; uint8_t v_isSharedCheck_1826_; 
lean_dec_ref(v___y_1808_);
lean_dec_ref(v_op_1798_);
lean_dec_ref(v_rhs_1797_);
v_a_1819_ = lean_ctor_get(v___x_1811_, 0);
v_isSharedCheck_1826_ = !lean_is_exclusive(v___x_1811_);
if (v_isSharedCheck_1826_ == 0)
{
v___x_1821_ = v___x_1811_;
v_isShared_1822_ = v_isSharedCheck_1826_;
goto v_resetjp_1820_;
}
else
{
lean_inc(v_a_1819_);
lean_dec(v___x_1811_);
v___x_1821_ = lean_box(0);
v_isShared_1822_ = v_isSharedCheck_1826_;
goto v_resetjp_1820_;
}
v_resetjp_1820_:
{
lean_object* v___x_1824_; 
if (v_isShared_1822_ == 0)
{
v___x_1824_ = v___x_1821_;
goto v_reusejp_1823_;
}
else
{
lean_object* v_reuseFailAlloc_1825_; 
v_reuseFailAlloc_1825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1825_, 0, v_a_1819_);
v___x_1824_ = v_reuseFailAlloc_1825_;
goto v_reusejp_1823_;
}
v_reusejp_1823_:
{
return v___x_1824_;
}
}
}
}
v___jp_1830_:
{
if (lean_obj_tag(v_terminal_x3f_1828_) == 0)
{
lean_object* v___x_1833_; 
v___x_1833_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__3));
v___y_1807_ = v___y_1832_;
v___y_1808_ = v___y_1831_;
v___y_1809_ = v___x_1833_;
goto v___jp_1806_;
}
else
{
lean_object* v_val_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; 
v_val_1834_ = lean_ctor_get(v_terminal_x3f_1828_, 0);
v___x_1835_ = lean_unsigned_to_nat(1u);
v___x_1836_ = lean_mk_empty_array_with_capacity(v___x_1835_);
lean_inc(v_val_1834_);
v___x_1837_ = lean_array_push(v___x_1836_, v_val_1834_);
v___y_1807_ = v___y_1832_;
v___y_1808_ = v___y_1831_;
v___y_1809_ = v___x_1837_;
goto v___jp_1806_;
}
}
v___jp_1838_:
{
lean_object* v___x_1840_; uint8_t v___x_1841_; 
v___x_1840_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__3));
v___x_1841_ = lean_uint8_once(&l_Lean_Elab_Tactic_VCGen_latticeOps___closed__4, &l_Lean_Elab_Tactic_VCGen_latticeOps___closed__4_once, _init_l_Lean_Elab_Tactic_VCGen_latticeOps___closed__4);
if (v___x_1841_ == 0)
{
v___y_1831_ = v___y_1839_;
v___y_1832_ = v___x_1840_;
goto v___jp_1830_;
}
else
{
uint8_t v___x_1842_; 
v___x_1842_ = lean_uint8_once(&l_Lean_Elab_Tactic_VCGen_latticeOps___closed__5, &l_Lean_Elab_Tactic_VCGen_latticeOps___closed__5_once, _init_l_Lean_Elab_Tactic_VCGen_latticeOps___closed__5);
if (v___x_1842_ == 0)
{
if (v___x_1841_ == 0)
{
v___y_1831_ = v___y_1839_;
v___y_1832_ = v___x_1840_;
goto v___jp_1830_;
}
else
{
lean_object* v___x_1843_; 
v___x_1843_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_mkLatticeOpRule___closed__0, &l_Lean_Elab_Tactic_VCGen_mkLatticeOpRule___closed__0_once, _init_l_Lean_Elab_Tactic_VCGen_mkLatticeOpRule___closed__0);
v___y_1831_ = v___y_1839_;
v___y_1832_ = v___x_1843_;
goto v___jp_1830_;
}
}
else
{
lean_object* v___x_1844_; 
v___x_1844_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_mkLatticeOpRule___closed__0, &l_Lean_Elab_Tactic_VCGen_mkLatticeOpRule___closed__0_once, _init_l_Lean_Elab_Tactic_VCGen_mkLatticeOpRule___closed__0);
v___y_1831_ = v___y_1839_;
v___y_1832_ = v___x_1844_;
goto v___jp_1830_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_mkLatticeOpRule___boxed(lean_object* v_rhs_1853_, lean_object* v_op_1854_, lean_object* v_a_1855_, lean_object* v_a_1856_, lean_object* v_a_1857_, lean_object* v_a_1858_, lean_object* v_a_1859_, lean_object* v_a_1860_, lean_object* v_a_1861_){
_start:
{
lean_object* v_res_1862_; 
v_res_1862_ = l_Lean_Elab_Tactic_VCGen_mkLatticeOpRule(v_rhs_1853_, v_op_1854_, v_a_1855_, v_a_1856_, v_a_1857_, v_a_1858_, v_a_1859_, v_a_1860_);
lean_dec(v_a_1860_);
lean_dec_ref(v_a_1859_);
lean_dec(v_a_1858_);
lean_dec_ref(v_a_1857_);
lean_dec(v_a_1856_);
lean_dec_ref(v_a_1855_);
return v_res_1862_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__0(size_t v_sz_1863_, size_t v_i_1864_, lean_object* v_bs_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_){
_start:
{
lean_object* v___x_1873_; 
v___x_1873_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__0___redArg(v_sz_1863_, v_i_1864_, v_bs_1865_, v___y_1868_, v___y_1869_, v___y_1870_, v___y_1871_);
return v___x_1873_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__0___boxed(lean_object* v_sz_1874_, lean_object* v_i_1875_, lean_object* v_bs_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_){
_start:
{
size_t v_sz_boxed_1884_; size_t v_i_boxed_1885_; lean_object* v_res_1886_; 
v_sz_boxed_1884_ = lean_unbox_usize(v_sz_1874_);
lean_dec(v_sz_1874_);
v_i_boxed_1885_ = lean_unbox_usize(v_i_1875_);
lean_dec(v_i_1875_);
v_res_1886_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__0(v_sz_boxed_1884_, v_i_boxed_1885_, v_bs_1876_, v___y_1877_, v___y_1878_, v___y_1879_, v___y_1880_, v___y_1881_, v___y_1882_);
lean_dec(v___y_1882_);
lean_dec_ref(v___y_1881_);
lean_dec(v___y_1880_);
lean_dec_ref(v___y_1879_);
lean_dec(v___y_1878_);
lean_dec_ref(v___y_1877_);
return v_res_1886_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__1(lean_object* v_00_u03b2_1887_, lean_object* v_m_1888_, lean_object* v_a_1889_){
_start:
{
lean_object* v___x_1890_; 
v___x_1890_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__1___redArg(v_m_1888_, v_a_1889_);
return v___x_1890_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__1___boxed(lean_object* v_00_u03b2_1891_, lean_object* v_m_1892_, lean_object* v_a_1893_){
_start:
{
lean_object* v_res_1894_; 
v_res_1894_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__1(v_00_u03b2_1891_, v_m_1892_, v_a_1893_);
lean_dec(v_a_1893_);
lean_dec_ref(v_m_1892_);
return v_res_1894_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__1_spec__1(lean_object* v_00_u03b2_1895_, lean_object* v_m_1896_, lean_object* v_query_1897_){
_start:
{
lean_object* v___x_1898_; 
v___x_1898_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__1_spec__1___redArg(v_m_1896_, v_query_1897_);
return v___x_1898_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__1_spec__1___boxed(lean_object* v_00_u03b2_1899_, lean_object* v_m_1900_, lean_object* v_query_1901_){
_start:
{
lean_object* v_res_1902_; 
v_res_1902_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__1_spec__1(v_00_u03b2_1899_, v_m_1900_, v_query_1901_);
lean_dec(v_query_1901_);
lean_dec_ref(v_m_1900_);
return v_res_1902_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_Apply(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_Order_Heyting(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_VCGen_FrameProc(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_Order_FrameClosure(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_Rewrite(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_AppBuilder(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_AbstractMVars(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_VCGen_LatticeOp(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Sym_Apply(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_Order_Heyting(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_VCGen_FrameProc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_Order_FrameClosure(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Simp_Rewrite(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_AppBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_AbstractMVars(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Tactic_VCGen_latticeOps = _init_l_Lean_Elab_Tactic_VCGen_latticeOps();
lean_mark_persistent(l_Lean_Elab_Tactic_VCGen_latticeOps);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_VCGen_LatticeOp(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Sym_Apply(uint8_t builtin);
lean_object* initialize_Std_Internal_Order_Heyting(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_VCGen_FrameProc(uint8_t builtin);
lean_object* initialize_Std_Internal_Order_FrameClosure(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_Rewrite(uint8_t builtin);
lean_object* initialize_Lean_Meta_AppBuilder(uint8_t builtin);
lean_object* initialize_Lean_Meta_AbstractMVars(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_VCGen_LatticeOp(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Sym_Apply(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal_Order_Heyting(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_VCGen_FrameProc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal_Order_FrameClosure(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Simp_Rewrite(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_AppBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_AbstractMVars(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_VCGen_LatticeOp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_VCGen_LatticeOp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_VCGen_LatticeOp(builtin);
}
#ifdef __cplusplus
}
#endif
