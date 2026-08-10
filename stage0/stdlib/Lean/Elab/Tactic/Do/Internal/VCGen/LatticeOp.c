// Lean compiler output
// Module: Lean.Elab.Tactic.Do.Internal.VCGen.LatticeOp
// Imports: public import Lean.Meta.Sym.Apply public import Std.Internal.Do.Order.Heyting public import Lean.Elab.Tactic.Do.Internal.VCGen.FrameProc import Lean.Meta.Sym.Simp.Rewrite import Lean.Meta.AppBuilder import Lean.Meta.AbstractMVars
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
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVar(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Meta_mkConstWithFreshMVarLevels(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallMetaTelescope(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAppM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_List_getLast_x21___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAppOptM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* lean_array_pop(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_mkTheoremFromDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_Theorems_insert(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_dischargeNone___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_SimpM_run_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_mkEqTrans(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Meta_abstractMVars(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_mkBackwardRuleFromExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_extract___redArg(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_Theorems_rewrite___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkCongrArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqSymm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_constName_x3f(lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallMetaTelescopeReducing(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_meet___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_meet___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_meet___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_meet___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Order"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_meet___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_meet___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_meet___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meet"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_meet___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_meet___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_meet___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_meet___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_meet___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_meet___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_meet___closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_meet___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_meet___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_meet___closed__2_value),LEAN_SCALAR_PTR_LITERAL(194, 193, 63, 6, 53, 61, 199, 176)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_meet___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_meet___closed__3_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_meet___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "meet_apply"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_meet___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_meet___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_meet___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_meet___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_meet___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_meet___closed__5_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_meet___closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_meet___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_meet___closed__5_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_meet___closed__4_value),LEAN_SCALAR_PTR_LITERAL(99, 197, 244, 134, 174, 130, 207, 233)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_meet___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_meet___closed__5_value;
static const lean_array_object l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_meet___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_meet___closed__5_value)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_meet___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_meet___closed__6_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_meet___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "le_meet"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_meet___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_meet___closed__7_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_meet___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_meet___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_meet___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_meet___closed__8_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_meet___closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_meet___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_meet___closed__8_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_meet___closed__7_value),LEAN_SCALAR_PTR_LITERAL(190, 114, 168, 215, 244, 74, 160, 2)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_meet___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_meet___closed__8_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_meet___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_meet___closed__8_value)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_meet___closed__9 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_meet___closed__9_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_meet___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_meet___closed__3_value),((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_meet___closed__6_value),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_meet___closed__9_value)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_meet___closed__10 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_meet___closed__10_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_meet = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_meet___closed__10_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_himp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "himp"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_himp___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_himp___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_himp___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_meet___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_himp___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_himp___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_meet___closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_himp___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_himp___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_himp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(173, 29, 48, 122, 5, 158, 45, 140)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_himp___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_himp___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_himp___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "himp_apply"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_himp___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_himp___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_himp___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_meet___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_himp___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_himp___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_meet___closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_himp___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_himp___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_himp___closed__2_value),LEAN_SCALAR_PTR_LITERAL(185, 113, 71, 38, 245, 240, 32, 111)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_himp___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_himp___closed__3_value;
static const lean_array_object l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_himp___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_himp___closed__3_value)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_himp___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_himp___closed__4_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_himp___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "le_himp"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_himp___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_himp___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_himp___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_meet___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_himp___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_himp___closed__6_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_meet___closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_himp___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_himp___closed__6_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_himp___closed__5_value),LEAN_SCALAR_PTR_LITERAL(34, 1, 31, 114, 210, 147, 30, 159)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_himp___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_himp___closed__6_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_himp___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_himp___closed__6_value)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_himp___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_himp___closed__7_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_himp___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_himp___closed__1_value),((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_himp___closed__4_value),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_himp___closed__7_value)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_himp___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_himp___closed__8_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_himp = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_himp___closed__8_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_ofProp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "CompleteLattice"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_ofProp___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_ofProp___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_ofProp___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "ofProp"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_ofProp___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_ofProp___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_ofProp___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_meet___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_ofProp___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_ofProp___closed__2_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_meet___closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_ofProp___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_ofProp___closed__2_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_ofProp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(239, 140, 127, 117, 148, 144, 166, 107)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_ofProp___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_ofProp___closed__2_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_ofProp___closed__1_value),LEAN_SCALAR_PTR_LITERAL(51, 160, 150, 32, 134, 96, 114, 42)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_ofProp___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_ofProp___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_ofProp___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "ofProp_apply"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_ofProp___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_ofProp___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_ofProp___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_meet___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_ofProp___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_ofProp___closed__4_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_meet___closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_ofProp___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_ofProp___closed__4_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_ofProp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(239, 140, 127, 117, 148, 144, 166, 107)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_ofProp___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_ofProp___closed__4_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_ofProp___closed__3_value),LEAN_SCALAR_PTR_LITERAL(43, 0, 38, 134, 51, 116, 27, 243)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_ofProp___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_ofProp___closed__4_value;
static const lean_array_object l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_ofProp___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_ofProp___closed__4_value)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_ofProp___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_ofProp___closed__5_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_ofProp___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "top_le_ofProp"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_ofProp___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_ofProp___closed__6_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_ofProp___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_meet___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_ofProp___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_ofProp___closed__7_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_meet___closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_ofProp___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_ofProp___closed__7_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_ofProp___closed__6_value),LEAN_SCALAR_PTR_LITERAL(240, 115, 147, 236, 50, 105, 134, 105)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_ofProp___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_ofProp___closed__7_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_ofProp___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_ofProp___closed__7_value)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_ofProp___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_ofProp___closed__8_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_ofProp___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_ofProp___closed__2_value),((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_ofProp___closed__5_value),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_ofProp___closed__8_value)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_ofProp___closed__9 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_ofProp___closed__9_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_ofProp = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_ofProp___closed__9_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_top___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "top"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_top___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_top___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_top___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_meet___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_top___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_top___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_meet___closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_top___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_top___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_top___closed__0_value),LEAN_SCALAR_PTR_LITERAL(219, 33, 148, 124, 218, 91, 248, 169)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_top___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_top___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_top___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "top_apply"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_top___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_top___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_top___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_meet___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_top___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_top___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_meet___closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_top___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_top___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_top___closed__2_value),LEAN_SCALAR_PTR_LITERAL(230, 219, 32, 190, 96, 78, 240, 61)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_top___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_top___closed__3_value;
static const lean_array_object l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_top___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_top___closed__3_value)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_top___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_top___closed__4_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_top___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "le_top"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_top___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_top___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_top___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_meet___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_top___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_top___closed__6_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_meet___closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_top___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_top___closed__6_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_top___closed__5_value),LEAN_SCALAR_PTR_LITERAL(236, 200, 120, 191, 69, 224, 183, 155)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_top___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_top___closed__6_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_top___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_top___closed__6_value)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_top___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_top___closed__7_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_top___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_top___closed__1_value),((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_top___closed__4_value),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_top___closed__7_value)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_top___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_top___closed__8_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_top = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_top___closed__8_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_upperAdjoint___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "PreservesSup"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_upperAdjoint___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_upperAdjoint___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_upperAdjoint___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "upperAdjoint"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_upperAdjoint___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_upperAdjoint___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_upperAdjoint___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_meet___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_upperAdjoint___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_upperAdjoint___closed__2_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_meet___closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_upperAdjoint___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_upperAdjoint___closed__2_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_upperAdjoint___closed__0_value),LEAN_SCALAR_PTR_LITERAL(184, 207, 242, 99, 37, 43, 114, 21)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_upperAdjoint___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_upperAdjoint___closed__2_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_upperAdjoint___closed__1_value),LEAN_SCALAR_PTR_LITERAL(196, 52, 128, 160, 100, 147, 237, 166)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_upperAdjoint___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_upperAdjoint___closed__2_value;
static const lean_array_object l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_upperAdjoint___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_upperAdjoint___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_upperAdjoint___closed__3_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_upperAdjoint___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "le_upperAdjoint"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_upperAdjoint___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_upperAdjoint___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_upperAdjoint___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_meet___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_upperAdjoint___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_upperAdjoint___closed__5_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_meet___closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_upperAdjoint___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_upperAdjoint___closed__5_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_upperAdjoint___closed__0_value),LEAN_SCALAR_PTR_LITERAL(184, 207, 242, 99, 37, 43, 114, 21)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_upperAdjoint___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_upperAdjoint___closed__5_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_upperAdjoint___closed__4_value),LEAN_SCALAR_PTR_LITERAL(28, 162, 178, 118, 193, 187, 169, 14)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_upperAdjoint___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_upperAdjoint___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_upperAdjoint___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_upperAdjoint___closed__5_value)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_upperAdjoint___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_upperAdjoint___closed__6_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_upperAdjoint___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_upperAdjoint___closed__2_value),((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_upperAdjoint___closed__3_value),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_upperAdjoint___closed__6_value)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_upperAdjoint___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_upperAdjoint___closed__7_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_upperAdjoint = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_upperAdjoint___closed__7_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_iInf___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "iInf"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_iInf___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_iInf___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_iInf___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_meet___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_iInf___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_iInf___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_meet___closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_iInf___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_iInf___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_iInf___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 96, 105, 10, 16, 194, 128, 157)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_iInf___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_iInf___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_iInf___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "iInf_apply"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_iInf___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_iInf___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_iInf___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_meet___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_iInf___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_iInf___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_meet___closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_iInf___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_iInf___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_iInf___closed__2_value),LEAN_SCALAR_PTR_LITERAL(13, 69, 58, 252, 126, 189, 121, 48)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_iInf___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_iInf___closed__3_value;
static const lean_array_object l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_iInf___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_iInf___closed__3_value)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_iInf___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_iInf___closed__4_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_iInf___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "le_iInf"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_iInf___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_iInf___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_iInf___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_meet___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_iInf___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_iInf___closed__6_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_meet___closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_iInf___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_iInf___closed__6_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_iInf___closed__5_value),LEAN_SCALAR_PTR_LITERAL(137, 155, 79, 233, 132, 15, 131, 19)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_iInf___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_iInf___closed__6_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_iInf___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_iInf___closed__6_value)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_iInf___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_iInf___closed__7_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_iInf___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_iInf___closed__1_value),((lean_object*)(((size_t)(3) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_iInf___closed__4_value),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_iInf___closed__7_value)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_iInf___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_iInf___closed__8_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_iInf = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_iInf___closed__8_value;
static const lean_array_object l_Lean_Elab_Tactic_Do_Internal_VCGen_builtinLatticeOps___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*6, .m_other = 0, .m_tag = 246}, .m_size = 6, .m_capacity = 6, .m_data = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_meet___closed__10_value),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_himp___closed__8_value),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_ofProp___closed__9_value),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_top___closed__8_value),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_upperAdjoint___closed__7_value),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_iInf___closed__8_value)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_builtinLatticeOps___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_builtinLatticeOps___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_builtinLatticeOps = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_builtinLatticeOps___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_latticeOps_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_latticeOps_spec__0_spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_latticeOps_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_latticeOps_spec__0_spec__1___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_latticeOps_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_latticeOps_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_latticeOps_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_Internal_VCGen_latticeOps_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_Internal_VCGen_latticeOps_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_VCGen_latticeOps___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_latticeOps___closed__0;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_VCGen_latticeOps___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_latticeOps___closed__1;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_VCGen_latticeOps___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_latticeOps___closed__2;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_VCGen_latticeOps___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Lean_Elab_Tactic_Do_Internal_VCGen_latticeOps___closed__3;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_VCGen_latticeOps___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Lean_Elab_Tactic_Do_Internal_VCGen_latticeOps___closed__4;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_VCGen_latticeOps___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_Elab_Tactic_Do_Internal_VCGen_latticeOps___closed__5;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_VCGen_latticeOps___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_latticeOps___closed__6;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_latticeOps;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_latticeOps_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_latticeOps_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_latticeOps_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_latticeOps_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_latticeOps_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_latticeOps_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_latticeOps_spec__0_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "PartialOrder"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__2___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__2___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "rel"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__2___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__2___closed__1_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__2___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_meet___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__2___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__2___closed__2_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_meet___closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__2___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__2___closed__2_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(179, 3, 218, 237, 219, 72, 94, 177)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__2___closed__2_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__2___closed__1_value),LEAN_SCALAR_PTR_LITERAL(41, 174, 7, 105, 99, 77, 97, 125)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__2___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__2___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "lattice terminal "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__2___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__2___closed__3_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__2___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__2___closed__4;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__2___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 33, .m_data = " does not conclude a `⊑` relation"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__2___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__2___closed__5_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__2___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__2___closed__6;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__2___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 56, .m_capacity = 56, .m_length = 55, .m_data = " has no head constant on its conclusion right-hand side"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__2___closed__7 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__2___closed__7_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__2___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__2___closed__8;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_go___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_go___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_go_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_go_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 83, .m_capacity = 83, .m_length = 82, .m_data = "lattice saturation did not terminate; the rewrite set is likely non-terminating on"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_go___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_go___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_go___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_go___closed__1;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_go___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(100000) << 1) | 1)),((lean_object*)(((size_t)(2) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_go___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_go___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_Simp_dischargeNone___boxed, .m_arity = 11, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp___closed__1;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply_spec__0_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply_spec__0_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply_spec__0_spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = " does not conclude "};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply___closed__1;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "u"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply___closed__2_value),LEAN_SCALAR_PTR_LITERAL(232, 178, 247, 241, 102, 42, 87, 174)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply___closed__3_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "le_apply_of_point_meet_le"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_meet___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply___closed__5_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_meet___closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply___closed__5_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply___closed__4_value),LEAN_SCALAR_PTR_LITERAL(147, 15, 136, 52, 94, 223, 161, 163)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply___closed__5_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply_spec__0_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__1_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__0___redArg(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__2___closed__0 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__2___closed__0_value;
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "mp"};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__2___closed__1 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__2___closed__1_value;
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__2___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__2___closed__2_value_aux_0),((lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__2___closed__1_value),LEAN_SCALAR_PTR_LITERAL(183, 66, 254, 161, 210, 133, 94, 78)}};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__2___closed__2 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__2___closed__2_value;
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "lattice operator `"};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__2___closed__3 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__2___closed__3_value;
static lean_once_cell_t l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__2___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__2___closed__4;
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__2___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 86, .m_capacity = 86, .m_length = 85, .m_data = "` neither reduces nor has a registered terminal; its split rule would be the identity"};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__2___closed__5 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__2___closed__5_value;
static lean_once_cell_t l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__2___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__2___closed__6;
static lean_once_cell_t l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__2___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__2___closed__7;
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__4(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__3(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_latticeOps_spec__0_spec__2___redArg(lean_object* v_a_179_, lean_object* v_b_180_, lean_object* v_x_181_){
_start:
{
if (lean_obj_tag(v_x_181_) == 0)
{
lean_dec(v_b_180_);
lean_dec(v_a_179_);
return v_x_181_;
}
else
{
lean_object* v_key_182_; lean_object* v_value_183_; lean_object* v_tail_184_; lean_object* v___x_186_; uint8_t v_isShared_187_; uint8_t v_isSharedCheck_196_; 
v_key_182_ = lean_ctor_get(v_x_181_, 0);
v_value_183_ = lean_ctor_get(v_x_181_, 1);
v_tail_184_ = lean_ctor_get(v_x_181_, 2);
v_isSharedCheck_196_ = !lean_is_exclusive(v_x_181_);
if (v_isSharedCheck_196_ == 0)
{
v___x_186_ = v_x_181_;
v_isShared_187_ = v_isSharedCheck_196_;
goto v_resetjp_185_;
}
else
{
lean_inc(v_tail_184_);
lean_inc(v_value_183_);
lean_inc(v_key_182_);
lean_dec(v_x_181_);
v___x_186_ = lean_box(0);
v_isShared_187_ = v_isSharedCheck_196_;
goto v_resetjp_185_;
}
v_resetjp_185_:
{
uint8_t v___x_188_; 
v___x_188_ = lean_name_eq(v_key_182_, v_a_179_);
if (v___x_188_ == 0)
{
lean_object* v___x_189_; lean_object* v___x_191_; 
v___x_189_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_latticeOps_spec__0_spec__2___redArg(v_a_179_, v_b_180_, v_tail_184_);
if (v_isShared_187_ == 0)
{
lean_ctor_set(v___x_186_, 2, v___x_189_);
v___x_191_ = v___x_186_;
goto v_reusejp_190_;
}
else
{
lean_object* v_reuseFailAlloc_192_; 
v_reuseFailAlloc_192_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_192_, 0, v_key_182_);
lean_ctor_set(v_reuseFailAlloc_192_, 1, v_value_183_);
lean_ctor_set(v_reuseFailAlloc_192_, 2, v___x_189_);
v___x_191_ = v_reuseFailAlloc_192_;
goto v_reusejp_190_;
}
v_reusejp_190_:
{
return v___x_191_;
}
}
else
{
lean_object* v___x_194_; 
lean_dec(v_value_183_);
lean_dec(v_key_182_);
if (v_isShared_187_ == 0)
{
lean_ctor_set(v___x_186_, 1, v_b_180_);
lean_ctor_set(v___x_186_, 0, v_a_179_);
v___x_194_ = v___x_186_;
goto v_reusejp_193_;
}
else
{
lean_object* v_reuseFailAlloc_195_; 
v_reuseFailAlloc_195_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_195_, 0, v_a_179_);
lean_ctor_set(v_reuseFailAlloc_195_, 1, v_b_180_);
lean_ctor_set(v_reuseFailAlloc_195_, 2, v_tail_184_);
v___x_194_ = v_reuseFailAlloc_195_;
goto v_reusejp_193_;
}
v_reusejp_193_:
{
return v___x_194_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_latticeOps_spec__0_spec__1_spec__2_spec__4___redArg(lean_object* v_x_197_, lean_object* v_x_198_){
_start:
{
if (lean_obj_tag(v_x_198_) == 0)
{
return v_x_197_;
}
else
{
lean_object* v_key_199_; lean_object* v_value_200_; lean_object* v_tail_201_; lean_object* v___x_203_; uint8_t v_isShared_204_; uint8_t v_isSharedCheck_227_; 
v_key_199_ = lean_ctor_get(v_x_198_, 0);
v_value_200_ = lean_ctor_get(v_x_198_, 1);
v_tail_201_ = lean_ctor_get(v_x_198_, 2);
v_isSharedCheck_227_ = !lean_is_exclusive(v_x_198_);
if (v_isSharedCheck_227_ == 0)
{
v___x_203_ = v_x_198_;
v_isShared_204_ = v_isSharedCheck_227_;
goto v_resetjp_202_;
}
else
{
lean_inc(v_tail_201_);
lean_inc(v_value_200_);
lean_inc(v_key_199_);
lean_dec(v_x_198_);
v___x_203_ = lean_box(0);
v_isShared_204_ = v_isSharedCheck_227_;
goto v_resetjp_202_;
}
v_resetjp_202_:
{
lean_object* v___x_205_; uint64_t v___y_207_; 
v___x_205_ = lean_array_get_size(v_x_197_);
if (lean_obj_tag(v_key_199_) == 0)
{
uint64_t v___x_225_; 
v___x_225_ = 1723ULL;
v___y_207_ = v___x_225_;
goto v___jp_206_;
}
else
{
uint64_t v_hash_226_; 
v_hash_226_ = lean_ctor_get_uint64(v_key_199_, sizeof(void*)*2);
v___y_207_ = v_hash_226_;
goto v___jp_206_;
}
v___jp_206_:
{
uint64_t v___x_208_; uint64_t v___x_209_; uint64_t v_fold_210_; uint64_t v___x_211_; uint64_t v___x_212_; uint64_t v___x_213_; size_t v___x_214_; size_t v___x_215_; size_t v___x_216_; size_t v___x_217_; size_t v___x_218_; lean_object* v___x_219_; lean_object* v___x_221_; 
v___x_208_ = 32ULL;
v___x_209_ = lean_uint64_shift_right(v___y_207_, v___x_208_);
v_fold_210_ = lean_uint64_xor(v___y_207_, v___x_209_);
v___x_211_ = 16ULL;
v___x_212_ = lean_uint64_shift_right(v_fold_210_, v___x_211_);
v___x_213_ = lean_uint64_xor(v_fold_210_, v___x_212_);
v___x_214_ = lean_uint64_to_usize(v___x_213_);
v___x_215_ = lean_usize_of_nat(v___x_205_);
v___x_216_ = ((size_t)1ULL);
v___x_217_ = lean_usize_sub(v___x_215_, v___x_216_);
v___x_218_ = lean_usize_land(v___x_214_, v___x_217_);
v___x_219_ = lean_array_uget_borrowed(v_x_197_, v___x_218_);
lean_inc(v___x_219_);
if (v_isShared_204_ == 0)
{
lean_ctor_set(v___x_203_, 2, v___x_219_);
v___x_221_ = v___x_203_;
goto v_reusejp_220_;
}
else
{
lean_object* v_reuseFailAlloc_224_; 
v_reuseFailAlloc_224_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_224_, 0, v_key_199_);
lean_ctor_set(v_reuseFailAlloc_224_, 1, v_value_200_);
lean_ctor_set(v_reuseFailAlloc_224_, 2, v___x_219_);
v___x_221_ = v_reuseFailAlloc_224_;
goto v_reusejp_220_;
}
v_reusejp_220_:
{
lean_object* v___x_222_; 
v___x_222_ = lean_array_uset(v_x_197_, v___x_218_, v___x_221_);
v_x_197_ = v___x_222_;
v_x_198_ = v_tail_201_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_latticeOps_spec__0_spec__1_spec__2___redArg(lean_object* v_i_228_, lean_object* v_source_229_, lean_object* v_target_230_){
_start:
{
lean_object* v___x_231_; uint8_t v___x_232_; 
v___x_231_ = lean_array_get_size(v_source_229_);
v___x_232_ = lean_nat_dec_lt(v_i_228_, v___x_231_);
if (v___x_232_ == 0)
{
lean_dec_ref(v_source_229_);
lean_dec(v_i_228_);
return v_target_230_;
}
else
{
lean_object* v_es_233_; lean_object* v___x_234_; lean_object* v_source_235_; lean_object* v_target_236_; lean_object* v___x_237_; lean_object* v___x_238_; 
v_es_233_ = lean_array_fget(v_source_229_, v_i_228_);
v___x_234_ = lean_box(0);
v_source_235_ = lean_array_fset(v_source_229_, v_i_228_, v___x_234_);
v_target_236_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_latticeOps_spec__0_spec__1_spec__2_spec__4___redArg(v_target_230_, v_es_233_);
v___x_237_ = lean_unsigned_to_nat(1u);
v___x_238_ = lean_nat_add(v_i_228_, v___x_237_);
lean_dec(v_i_228_);
v_i_228_ = v___x_238_;
v_source_229_ = v_source_235_;
v_target_230_ = v_target_236_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_latticeOps_spec__0_spec__1___redArg(lean_object* v_data_240_){
_start:
{
lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v_nbuckets_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; 
v___x_241_ = lean_array_get_size(v_data_240_);
v___x_242_ = lean_unsigned_to_nat(2u);
v_nbuckets_243_ = lean_nat_mul(v___x_241_, v___x_242_);
v___x_244_ = lean_unsigned_to_nat(0u);
v___x_245_ = lean_box(0);
v___x_246_ = lean_mk_array(v_nbuckets_243_, v___x_245_);
v___x_247_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_latticeOps_spec__0_spec__1_spec__2___redArg(v___x_244_, v_data_240_, v___x_246_);
return v___x_247_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_latticeOps_spec__0_spec__0___redArg(lean_object* v_a_248_, lean_object* v_x_249_){
_start:
{
if (lean_obj_tag(v_x_249_) == 0)
{
uint8_t v___x_250_; 
v___x_250_ = 0;
return v___x_250_;
}
else
{
lean_object* v_key_251_; lean_object* v_tail_252_; uint8_t v___x_253_; 
v_key_251_ = lean_ctor_get(v_x_249_, 0);
v_tail_252_ = lean_ctor_get(v_x_249_, 2);
v___x_253_ = lean_name_eq(v_key_251_, v_a_248_);
if (v___x_253_ == 0)
{
v_x_249_ = v_tail_252_;
goto _start;
}
else
{
return v___x_253_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_latticeOps_spec__0_spec__0___redArg___boxed(lean_object* v_a_255_, lean_object* v_x_256_){
_start:
{
uint8_t v_res_257_; lean_object* v_r_258_; 
v_res_257_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_latticeOps_spec__0_spec__0___redArg(v_a_255_, v_x_256_);
lean_dec(v_x_256_);
lean_dec(v_a_255_);
v_r_258_ = lean_box(v_res_257_);
return v_r_258_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_latticeOps_spec__0___redArg(lean_object* v_m_259_, lean_object* v_a_260_, lean_object* v_b_261_){
_start:
{
lean_object* v_size_262_; lean_object* v_buckets_263_; lean_object* v___x_265_; uint8_t v_isShared_266_; uint8_t v_isSharedCheck_309_; 
v_size_262_ = lean_ctor_get(v_m_259_, 0);
v_buckets_263_ = lean_ctor_get(v_m_259_, 1);
v_isSharedCheck_309_ = !lean_is_exclusive(v_m_259_);
if (v_isSharedCheck_309_ == 0)
{
v___x_265_ = v_m_259_;
v_isShared_266_ = v_isSharedCheck_309_;
goto v_resetjp_264_;
}
else
{
lean_inc(v_buckets_263_);
lean_inc(v_size_262_);
lean_dec(v_m_259_);
v___x_265_ = lean_box(0);
v_isShared_266_ = v_isSharedCheck_309_;
goto v_resetjp_264_;
}
v_resetjp_264_:
{
lean_object* v___x_267_; uint64_t v___y_269_; 
v___x_267_ = lean_array_get_size(v_buckets_263_);
if (lean_obj_tag(v_a_260_) == 0)
{
uint64_t v___x_307_; 
v___x_307_ = 1723ULL;
v___y_269_ = v___x_307_;
goto v___jp_268_;
}
else
{
uint64_t v_hash_308_; 
v_hash_308_ = lean_ctor_get_uint64(v_a_260_, sizeof(void*)*2);
v___y_269_ = v_hash_308_;
goto v___jp_268_;
}
v___jp_268_:
{
uint64_t v___x_270_; uint64_t v___x_271_; uint64_t v_fold_272_; uint64_t v___x_273_; uint64_t v___x_274_; uint64_t v___x_275_; size_t v___x_276_; size_t v___x_277_; size_t v___x_278_; size_t v___x_279_; size_t v___x_280_; lean_object* v_bkt_281_; uint8_t v___x_282_; 
v___x_270_ = 32ULL;
v___x_271_ = lean_uint64_shift_right(v___y_269_, v___x_270_);
v_fold_272_ = lean_uint64_xor(v___y_269_, v___x_271_);
v___x_273_ = 16ULL;
v___x_274_ = lean_uint64_shift_right(v_fold_272_, v___x_273_);
v___x_275_ = lean_uint64_xor(v_fold_272_, v___x_274_);
v___x_276_ = lean_uint64_to_usize(v___x_275_);
v___x_277_ = lean_usize_of_nat(v___x_267_);
v___x_278_ = ((size_t)1ULL);
v___x_279_ = lean_usize_sub(v___x_277_, v___x_278_);
v___x_280_ = lean_usize_land(v___x_276_, v___x_279_);
v_bkt_281_ = lean_array_uget_borrowed(v_buckets_263_, v___x_280_);
v___x_282_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_latticeOps_spec__0_spec__0___redArg(v_a_260_, v_bkt_281_);
if (v___x_282_ == 0)
{
lean_object* v___x_283_; lean_object* v_size_x27_284_; lean_object* v___x_285_; lean_object* v_buckets_x27_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; uint8_t v___x_292_; 
v___x_283_ = lean_unsigned_to_nat(1u);
v_size_x27_284_ = lean_nat_add(v_size_262_, v___x_283_);
lean_dec(v_size_262_);
lean_inc(v_bkt_281_);
v___x_285_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_285_, 0, v_a_260_);
lean_ctor_set(v___x_285_, 1, v_b_261_);
lean_ctor_set(v___x_285_, 2, v_bkt_281_);
v_buckets_x27_286_ = lean_array_uset(v_buckets_263_, v___x_280_, v___x_285_);
v___x_287_ = lean_unsigned_to_nat(4u);
v___x_288_ = lean_nat_mul(v_size_x27_284_, v___x_287_);
v___x_289_ = lean_unsigned_to_nat(3u);
v___x_290_ = lean_nat_div(v___x_288_, v___x_289_);
lean_dec(v___x_288_);
v___x_291_ = lean_array_get_size(v_buckets_x27_286_);
v___x_292_ = lean_nat_dec_le(v___x_290_, v___x_291_);
lean_dec(v___x_290_);
if (v___x_292_ == 0)
{
lean_object* v_val_293_; lean_object* v___x_295_; 
v_val_293_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_latticeOps_spec__0_spec__1___redArg(v_buckets_x27_286_);
if (v_isShared_266_ == 0)
{
lean_ctor_set(v___x_265_, 1, v_val_293_);
lean_ctor_set(v___x_265_, 0, v_size_x27_284_);
v___x_295_ = v___x_265_;
goto v_reusejp_294_;
}
else
{
lean_object* v_reuseFailAlloc_296_; 
v_reuseFailAlloc_296_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_296_, 0, v_size_x27_284_);
lean_ctor_set(v_reuseFailAlloc_296_, 1, v_val_293_);
v___x_295_ = v_reuseFailAlloc_296_;
goto v_reusejp_294_;
}
v_reusejp_294_:
{
return v___x_295_;
}
}
else
{
lean_object* v___x_298_; 
if (v_isShared_266_ == 0)
{
lean_ctor_set(v___x_265_, 1, v_buckets_x27_286_);
lean_ctor_set(v___x_265_, 0, v_size_x27_284_);
v___x_298_ = v___x_265_;
goto v_reusejp_297_;
}
else
{
lean_object* v_reuseFailAlloc_299_; 
v_reuseFailAlloc_299_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_299_, 0, v_size_x27_284_);
lean_ctor_set(v_reuseFailAlloc_299_, 1, v_buckets_x27_286_);
v___x_298_ = v_reuseFailAlloc_299_;
goto v_reusejp_297_;
}
v_reusejp_297_:
{
return v___x_298_;
}
}
}
else
{
lean_object* v___x_300_; lean_object* v_buckets_x27_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_305_; 
lean_inc(v_bkt_281_);
v___x_300_ = lean_box(0);
v_buckets_x27_301_ = lean_array_uset(v_buckets_263_, v___x_280_, v___x_300_);
v___x_302_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_latticeOps_spec__0_spec__2___redArg(v_a_260_, v_b_261_, v_bkt_281_);
v___x_303_ = lean_array_uset(v_buckets_x27_301_, v___x_280_, v___x_302_);
if (v_isShared_266_ == 0)
{
lean_ctor_set(v___x_265_, 1, v___x_303_);
v___x_305_ = v___x_265_;
goto v_reusejp_304_;
}
else
{
lean_object* v_reuseFailAlloc_306_; 
v_reuseFailAlloc_306_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_306_, 0, v_size_262_);
lean_ctor_set(v_reuseFailAlloc_306_, 1, v___x_303_);
v___x_305_ = v_reuseFailAlloc_306_;
goto v_reusejp_304_;
}
v_reusejp_304_:
{
return v___x_305_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_Internal_VCGen_latticeOps_spec__1(lean_object* v_as_310_, size_t v_i_311_, size_t v_stop_312_, lean_object* v_b_313_){
_start:
{
uint8_t v___x_314_; 
v___x_314_ = lean_usize_dec_eq(v_i_311_, v_stop_312_);
if (v___x_314_ == 0)
{
lean_object* v___x_315_; lean_object* v_head_316_; lean_object* v___x_317_; size_t v___x_318_; size_t v___x_319_; 
v___x_315_ = lean_array_uget_borrowed(v_as_310_, v_i_311_);
v_head_316_ = lean_ctor_get(v___x_315_, 0);
lean_inc(v___x_315_);
lean_inc(v_head_316_);
v___x_317_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_latticeOps_spec__0___redArg(v_b_313_, v_head_316_, v___x_315_);
v___x_318_ = ((size_t)1ULL);
v___x_319_ = lean_usize_add(v_i_311_, v___x_318_);
v_i_311_ = v___x_319_;
v_b_313_ = v___x_317_;
goto _start;
}
else
{
return v_b_313_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_Internal_VCGen_latticeOps_spec__1___boxed(lean_object* v_as_321_, lean_object* v_i_322_, lean_object* v_stop_323_, lean_object* v_b_324_){
_start:
{
size_t v_i_boxed_325_; size_t v_stop_boxed_326_; lean_object* v_res_327_; 
v_i_boxed_325_ = lean_unbox_usize(v_i_322_);
lean_dec(v_i_322_);
v_stop_boxed_326_ = lean_unbox_usize(v_stop_323_);
lean_dec(v_stop_323_);
v_res_327_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_Internal_VCGen_latticeOps_spec__1(v_as_321_, v_i_boxed_325_, v_stop_boxed_326_, v_b_324_);
lean_dec_ref(v_as_321_);
return v_res_327_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_latticeOps___closed__0(void){
_start:
{
lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; 
v___x_328_ = lean_box(0);
v___x_329_ = lean_unsigned_to_nat(16u);
v___x_330_ = lean_mk_array(v___x_329_, v___x_328_);
return v___x_330_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_latticeOps___closed__1(void){
_start:
{
lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; 
v___x_331_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_latticeOps___closed__0, &l_Lean_Elab_Tactic_Do_Internal_VCGen_latticeOps___closed__0_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_latticeOps___closed__0);
v___x_332_ = lean_unsigned_to_nat(0u);
v___x_333_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_333_, 0, v___x_332_);
lean_ctor_set(v___x_333_, 1, v___x_331_);
return v___x_333_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_latticeOps___closed__2(void){
_start:
{
lean_object* v___x_334_; lean_object* v___x_335_; 
v___x_334_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_builtinLatticeOps));
v___x_335_ = lean_array_get_size(v___x_334_);
return v___x_335_;
}
}
static uint8_t _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_latticeOps___closed__3(void){
_start:
{
lean_object* v___x_336_; lean_object* v___x_337_; uint8_t v___x_338_; 
v___x_336_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_latticeOps___closed__2, &l_Lean_Elab_Tactic_Do_Internal_VCGen_latticeOps___closed__2_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_latticeOps___closed__2);
v___x_337_ = lean_unsigned_to_nat(0u);
v___x_338_ = lean_nat_dec_lt(v___x_337_, v___x_336_);
return v___x_338_;
}
}
static uint8_t _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_latticeOps___closed__4(void){
_start:
{
lean_object* v___x_339_; uint8_t v___x_340_; 
v___x_339_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_latticeOps___closed__2, &l_Lean_Elab_Tactic_Do_Internal_VCGen_latticeOps___closed__2_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_latticeOps___closed__2);
v___x_340_ = lean_nat_dec_le(v___x_339_, v___x_339_);
return v___x_340_;
}
}
static size_t _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_latticeOps___closed__5(void){
_start:
{
lean_object* v___x_341_; size_t v___x_342_; 
v___x_341_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_latticeOps___closed__2, &l_Lean_Elab_Tactic_Do_Internal_VCGen_latticeOps___closed__2_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_latticeOps___closed__2);
v___x_342_ = lean_usize_of_nat(v___x_341_);
return v___x_342_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_latticeOps___closed__6(void){
_start:
{
lean_object* v___x_343_; size_t v___x_344_; size_t v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; 
v___x_343_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_latticeOps___closed__1, &l_Lean_Elab_Tactic_Do_Internal_VCGen_latticeOps___closed__1_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_latticeOps___closed__1);
v___x_344_ = lean_usize_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_latticeOps___closed__5, &l_Lean_Elab_Tactic_Do_Internal_VCGen_latticeOps___closed__5_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_latticeOps___closed__5);
v___x_345_ = ((size_t)0ULL);
v___x_346_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_builtinLatticeOps));
v___x_347_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_Internal_VCGen_latticeOps_spec__1(v___x_346_, v___x_345_, v___x_344_, v___x_343_);
return v___x_347_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_latticeOps(void){
_start:
{
lean_object* v___x_348_; uint8_t v___x_349_; 
v___x_348_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_latticeOps___closed__1, &l_Lean_Elab_Tactic_Do_Internal_VCGen_latticeOps___closed__1_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_latticeOps___closed__1);
v___x_349_ = lean_uint8_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_latticeOps___closed__3, &l_Lean_Elab_Tactic_Do_Internal_VCGen_latticeOps___closed__3_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_latticeOps___closed__3);
if (v___x_349_ == 0)
{
return v___x_348_;
}
else
{
uint8_t v___x_350_; 
v___x_350_ = lean_uint8_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_latticeOps___closed__4, &l_Lean_Elab_Tactic_Do_Internal_VCGen_latticeOps___closed__4_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_latticeOps___closed__4);
if (v___x_350_ == 0)
{
if (v___x_349_ == 0)
{
return v___x_348_;
}
else
{
lean_object* v___x_351_; 
v___x_351_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_latticeOps___closed__6, &l_Lean_Elab_Tactic_Do_Internal_VCGen_latticeOps___closed__6_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_latticeOps___closed__6);
return v___x_351_;
}
}
else
{
lean_object* v___x_352_; 
v___x_352_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_latticeOps___closed__6, &l_Lean_Elab_Tactic_Do_Internal_VCGen_latticeOps___closed__6_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_latticeOps___closed__6);
return v___x_352_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_latticeOps_spec__0(lean_object* v_00_u03b2_353_, lean_object* v_m_354_, lean_object* v_a_355_, lean_object* v_b_356_){
_start:
{
lean_object* v___x_357_; 
v___x_357_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_latticeOps_spec__0___redArg(v_m_354_, v_a_355_, v_b_356_);
return v___x_357_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_latticeOps_spec__0_spec__0(lean_object* v_00_u03b2_358_, lean_object* v_a_359_, lean_object* v_x_360_){
_start:
{
uint8_t v___x_361_; 
v___x_361_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_latticeOps_spec__0_spec__0___redArg(v_a_359_, v_x_360_);
return v___x_361_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_latticeOps_spec__0_spec__0___boxed(lean_object* v_00_u03b2_362_, lean_object* v_a_363_, lean_object* v_x_364_){
_start:
{
uint8_t v_res_365_; lean_object* v_r_366_; 
v_res_365_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_latticeOps_spec__0_spec__0(v_00_u03b2_362_, v_a_363_, v_x_364_);
lean_dec(v_x_364_);
lean_dec(v_a_363_);
v_r_366_ = lean_box(v_res_365_);
return v_r_366_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_latticeOps_spec__0_spec__1(lean_object* v_00_u03b2_367_, lean_object* v_data_368_){
_start:
{
lean_object* v___x_369_; 
v___x_369_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_latticeOps_spec__0_spec__1___redArg(v_data_368_);
return v___x_369_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_latticeOps_spec__0_spec__2(lean_object* v_00_u03b2_370_, lean_object* v_a_371_, lean_object* v_b_372_, lean_object* v_x_373_){
_start:
{
lean_object* v___x_374_; 
v___x_374_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_latticeOps_spec__0_spec__2___redArg(v_a_371_, v_b_372_, v_x_373_);
return v___x_374_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_latticeOps_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_375_, lean_object* v_i_376_, lean_object* v_source_377_, lean_object* v_target_378_){
_start:
{
lean_object* v___x_379_; 
v___x_379_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_latticeOps_spec__0_spec__1_spec__2___redArg(v_i_376_, v_source_377_, v_target_378_);
return v___x_379_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_latticeOps_spec__0_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_380_, lean_object* v_x_381_, lean_object* v_x_382_){
_start:
{
lean_object* v___x_383_; 
v___x_383_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_latticeOps_spec__0_spec__1_spec__2_spec__4___redArg(v_x_381_, v_x_382_);
return v___x_383_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__0___redArg(lean_object* v_e_384_, lean_object* v___y_385_){
_start:
{
uint8_t v___x_387_; 
v___x_387_ = l_Lean_Expr_hasMVar(v_e_384_);
if (v___x_387_ == 0)
{
lean_object* v___x_388_; 
v___x_388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_388_, 0, v_e_384_);
return v___x_388_;
}
else
{
lean_object* v___x_389_; lean_object* v_mctx_390_; lean_object* v___x_391_; lean_object* v_fst_392_; lean_object* v_snd_393_; lean_object* v___x_394_; lean_object* v_cache_395_; lean_object* v_zetaDeltaFVarIds_396_; lean_object* v_postponed_397_; lean_object* v_diag_398_; lean_object* v___x_400_; uint8_t v_isShared_401_; uint8_t v_isSharedCheck_407_; 
v___x_389_ = lean_st_ref_get(v___y_385_);
v_mctx_390_ = lean_ctor_get(v___x_389_, 0);
lean_inc_ref(v_mctx_390_);
lean_dec(v___x_389_);
v___x_391_ = l_Lean_instantiateMVarsCore(v_mctx_390_, v_e_384_);
v_fst_392_ = lean_ctor_get(v___x_391_, 0);
lean_inc(v_fst_392_);
v_snd_393_ = lean_ctor_get(v___x_391_, 1);
lean_inc(v_snd_393_);
lean_dec_ref(v___x_391_);
v___x_394_ = lean_st_ref_take(v___y_385_);
v_cache_395_ = lean_ctor_get(v___x_394_, 1);
v_zetaDeltaFVarIds_396_ = lean_ctor_get(v___x_394_, 2);
v_postponed_397_ = lean_ctor_get(v___x_394_, 3);
v_diag_398_ = lean_ctor_get(v___x_394_, 4);
v_isSharedCheck_407_ = !lean_is_exclusive(v___x_394_);
if (v_isSharedCheck_407_ == 0)
{
lean_object* v_unused_408_; 
v_unused_408_ = lean_ctor_get(v___x_394_, 0);
lean_dec(v_unused_408_);
v___x_400_ = v___x_394_;
v_isShared_401_ = v_isSharedCheck_407_;
goto v_resetjp_399_;
}
else
{
lean_inc(v_diag_398_);
lean_inc(v_postponed_397_);
lean_inc(v_zetaDeltaFVarIds_396_);
lean_inc(v_cache_395_);
lean_dec(v___x_394_);
v___x_400_ = lean_box(0);
v_isShared_401_ = v_isSharedCheck_407_;
goto v_resetjp_399_;
}
v_resetjp_399_:
{
lean_object* v___x_403_; 
if (v_isShared_401_ == 0)
{
lean_ctor_set(v___x_400_, 0, v_snd_393_);
v___x_403_ = v___x_400_;
goto v_reusejp_402_;
}
else
{
lean_object* v_reuseFailAlloc_406_; 
v_reuseFailAlloc_406_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_406_, 0, v_snd_393_);
lean_ctor_set(v_reuseFailAlloc_406_, 1, v_cache_395_);
lean_ctor_set(v_reuseFailAlloc_406_, 2, v_zetaDeltaFVarIds_396_);
lean_ctor_set(v_reuseFailAlloc_406_, 3, v_postponed_397_);
lean_ctor_set(v_reuseFailAlloc_406_, 4, v_diag_398_);
v___x_403_ = v_reuseFailAlloc_406_;
goto v_reusejp_402_;
}
v_reusejp_402_:
{
lean_object* v___x_404_; lean_object* v___x_405_; 
v___x_404_ = lean_st_ref_set(v___y_385_, v___x_403_);
v___x_405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_405_, 0, v_fst_392_);
return v___x_405_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__0___redArg___boxed(lean_object* v_e_409_, lean_object* v___y_410_, lean_object* v___y_411_){
_start:
{
lean_object* v_res_412_; 
v_res_412_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__0___redArg(v_e_409_, v___y_410_);
lean_dec(v___y_410_);
return v_res_412_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__0(lean_object* v_e_413_, lean_object* v___y_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_){
_start:
{
lean_object* v___x_419_; 
v___x_419_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__0___redArg(v_e_413_, v___y_415_);
return v___x_419_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__0___boxed(lean_object* v_e_420_, lean_object* v___y_421_, lean_object* v___y_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_){
_start:
{
lean_object* v_res_426_; 
v_res_426_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__0(v_e_420_, v___y_421_, v___y_422_, v___y_423_, v___y_424_);
lean_dec(v___y_424_);
lean_dec_ref(v___y_423_);
lean_dec(v___y_422_);
lean_dec_ref(v___y_421_);
return v_res_426_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__1_spec__1(lean_object* v_msgData_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v___y_430_, lean_object* v___y_431_){
_start:
{
lean_object* v___x_433_; lean_object* v_env_434_; lean_object* v___x_435_; lean_object* v_mctx_436_; lean_object* v_lctx_437_; lean_object* v_options_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; 
v___x_433_ = lean_st_ref_get(v___y_431_);
v_env_434_ = lean_ctor_get(v___x_433_, 0);
lean_inc_ref(v_env_434_);
lean_dec(v___x_433_);
v___x_435_ = lean_st_ref_get(v___y_429_);
v_mctx_436_ = lean_ctor_get(v___x_435_, 0);
lean_inc_ref(v_mctx_436_);
lean_dec(v___x_435_);
v_lctx_437_ = lean_ctor_get(v___y_428_, 2);
v_options_438_ = lean_ctor_get(v___y_430_, 2);
lean_inc_ref(v_options_438_);
lean_inc_ref(v_lctx_437_);
v___x_439_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_439_, 0, v_env_434_);
lean_ctor_set(v___x_439_, 1, v_mctx_436_);
lean_ctor_set(v___x_439_, 2, v_lctx_437_);
lean_ctor_set(v___x_439_, 3, v_options_438_);
v___x_440_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_440_, 0, v___x_439_);
lean_ctor_set(v___x_440_, 1, v_msgData_427_);
v___x_441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_441_, 0, v___x_440_);
return v___x_441_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__1_spec__1___boxed(lean_object* v_msgData_442_, lean_object* v___y_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_){
_start:
{
lean_object* v_res_448_; 
v_res_448_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__1_spec__1(v_msgData_442_, v___y_443_, v___y_444_, v___y_445_, v___y_446_);
lean_dec(v___y_446_);
lean_dec_ref(v___y_445_);
lean_dec(v___y_444_);
lean_dec_ref(v___y_443_);
return v_res_448_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__1___redArg(lean_object* v_msg_449_, lean_object* v___y_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_){
_start:
{
lean_object* v_ref_455_; lean_object* v___x_456_; lean_object* v_a_457_; lean_object* v___x_459_; uint8_t v_isShared_460_; uint8_t v_isSharedCheck_465_; 
v_ref_455_ = lean_ctor_get(v___y_452_, 5);
v___x_456_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__1_spec__1(v_msg_449_, v___y_450_, v___y_451_, v___y_452_, v___y_453_);
v_a_457_ = lean_ctor_get(v___x_456_, 0);
v_isSharedCheck_465_ = !lean_is_exclusive(v___x_456_);
if (v_isSharedCheck_465_ == 0)
{
v___x_459_ = v___x_456_;
v_isShared_460_ = v_isSharedCheck_465_;
goto v_resetjp_458_;
}
else
{
lean_inc(v_a_457_);
lean_dec(v___x_456_);
v___x_459_ = lean_box(0);
v_isShared_460_ = v_isSharedCheck_465_;
goto v_resetjp_458_;
}
v_resetjp_458_:
{
lean_object* v___x_461_; lean_object* v___x_463_; 
lean_inc(v_ref_455_);
v___x_461_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_461_, 0, v_ref_455_);
lean_ctor_set(v___x_461_, 1, v_a_457_);
if (v_isShared_460_ == 0)
{
lean_ctor_set_tag(v___x_459_, 1);
lean_ctor_set(v___x_459_, 0, v___x_461_);
v___x_463_ = v___x_459_;
goto v_reusejp_462_;
}
else
{
lean_object* v_reuseFailAlloc_464_; 
v_reuseFailAlloc_464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_464_, 0, v___x_461_);
v___x_463_ = v_reuseFailAlloc_464_;
goto v_reusejp_462_;
}
v_reusejp_462_:
{
return v___x_463_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__1___redArg___boxed(lean_object* v_msg_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_){
_start:
{
lean_object* v_res_472_; 
v_res_472_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__1___redArg(v_msg_466_, v___y_467_, v___y_468_, v___y_469_, v___y_470_);
lean_dec(v___y_470_);
lean_dec_ref(v___y_469_);
lean_dec(v___y_468_);
lean_dec_ref(v___y_467_);
return v_res_472_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__2___closed__4(void){
_start:
{
lean_object* v___x_481_; lean_object* v___x_482_; 
v___x_481_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__2___closed__3));
v___x_482_ = l_Lean_stringToMessageData(v___x_481_);
return v___x_482_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__2___closed__6(void){
_start:
{
lean_object* v___x_484_; lean_object* v___x_485_; 
v___x_484_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__2___closed__5));
v___x_485_ = l_Lean_stringToMessageData(v___x_484_);
return v___x_485_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__2___closed__8(void){
_start:
{
lean_object* v___x_487_; lean_object* v___x_488_; 
v___x_487_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__2___closed__7));
v___x_488_ = l_Lean_stringToMessageData(v___x_487_);
return v___x_488_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__2(lean_object* v_as_489_, size_t v_sz_490_, size_t v_i_491_, lean_object* v_b_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_, lean_object* v___y_496_){
_start:
{
lean_object* v_a_499_; uint8_t v___x_503_; 
v___x_503_ = lean_usize_dec_lt(v_i_491_, v_sz_490_);
if (v___x_503_ == 0)
{
lean_object* v___x_504_; 
v___x_504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_504_, 0, v_b_492_);
return v___x_504_;
}
else
{
lean_object* v_a_505_; lean_object* v___x_506_; 
v_a_505_ = lean_array_uget_borrowed(v_as_489_, v_i_491_);
lean_inc(v_a_505_);
v___x_506_ = l_Lean_Meta_mkConstWithFreshMVarLevels(v_a_505_, v___y_493_, v___y_494_, v___y_495_, v___y_496_);
if (lean_obj_tag(v___x_506_) == 0)
{
lean_object* v_a_507_; lean_object* v___x_508_; 
v_a_507_ = lean_ctor_get(v___x_506_, 0);
lean_inc(v_a_507_);
lean_dec_ref_known(v___x_506_, 1);
lean_inc(v___y_496_);
lean_inc_ref(v___y_495_);
lean_inc(v___y_494_);
lean_inc_ref(v___y_493_);
v___x_508_ = lean_infer_type(v_a_507_, v___y_493_, v___y_494_, v___y_495_, v___y_496_);
if (lean_obj_tag(v___x_508_) == 0)
{
lean_object* v_a_509_; lean_object* v___x_510_; uint8_t v___x_511_; lean_object* v___x_512_; 
v_a_509_ = lean_ctor_get(v___x_508_, 0);
lean_inc(v_a_509_);
lean_dec_ref_known(v___x_508_, 1);
v___x_510_ = lean_box(0);
v___x_511_ = 0;
v___x_512_ = l_Lean_Meta_forallMetaTelescopeReducing(v_a_509_, v___x_510_, v___x_511_, v___y_493_, v___y_494_, v___y_495_, v___y_496_);
if (lean_obj_tag(v___x_512_) == 0)
{
lean_object* v_a_513_; lean_object* v_snd_514_; lean_object* v___x_516_; uint8_t v_isShared_517_; uint8_t v_isSharedCheck_578_; 
v_a_513_ = lean_ctor_get(v___x_512_, 0);
lean_inc(v_a_513_);
lean_dec_ref_known(v___x_512_, 1);
v_snd_514_ = lean_ctor_get(v_a_513_, 1);
v_isSharedCheck_578_ = !lean_is_exclusive(v_a_513_);
if (v_isSharedCheck_578_ == 0)
{
lean_object* v_unused_579_; 
v_unused_579_ = lean_ctor_get(v_a_513_, 0);
lean_dec(v_unused_579_);
v___x_516_ = v_a_513_;
v_isShared_517_ = v_isSharedCheck_578_;
goto v_resetjp_515_;
}
else
{
lean_inc(v_snd_514_);
lean_dec(v_a_513_);
v___x_516_ = lean_box(0);
v_isShared_517_ = v_isSharedCheck_578_;
goto v_resetjp_515_;
}
v_resetjp_515_:
{
lean_object* v_snd_518_; lean_object* v___x_520_; uint8_t v_isShared_521_; uint8_t v_isSharedCheck_576_; 
v_snd_518_ = lean_ctor_get(v_snd_514_, 1);
v_isSharedCheck_576_ = !lean_is_exclusive(v_snd_514_);
if (v_isSharedCheck_576_ == 0)
{
lean_object* v_unused_577_; 
v_unused_577_ = lean_ctor_get(v_snd_514_, 0);
lean_dec(v_unused_577_);
v___x_520_ = v_snd_514_;
v_isShared_521_ = v_isSharedCheck_576_;
goto v_resetjp_519_;
}
else
{
lean_inc(v_snd_518_);
lean_dec(v_snd_514_);
v___x_520_ = lean_box(0);
v_isShared_521_ = v_isSharedCheck_576_;
goto v_resetjp_519_;
}
v_resetjp_519_:
{
lean_object* v___x_522_; 
v___x_522_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__0___redArg(v_snd_518_, v___y_494_);
if (lean_obj_tag(v___x_522_) == 0)
{
lean_object* v_a_523_; lean_object* v___x_524_; lean_object* v___x_525_; uint8_t v___x_526_; 
v_a_523_ = lean_ctor_get(v___x_522_, 0);
lean_inc(v_a_523_);
lean_dec_ref_known(v___x_522_, 1);
v___x_524_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__2___closed__2));
v___x_525_ = lean_unsigned_to_nat(4u);
v___x_526_ = l_Lean_Expr_isAppOfArity(v_a_523_, v___x_524_, v___x_525_);
if (v___x_526_ == 0)
{
lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_530_; 
lean_dec(v_a_523_);
lean_del_object(v___x_520_);
v___x_527_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__2___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__2___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__2___closed__4);
lean_inc(v_a_505_);
v___x_528_ = l_Lean_MessageData_ofName(v_a_505_);
if (v_isShared_517_ == 0)
{
lean_ctor_set_tag(v___x_516_, 7);
lean_ctor_set(v___x_516_, 1, v___x_528_);
lean_ctor_set(v___x_516_, 0, v___x_527_);
v___x_530_ = v___x_516_;
goto v_reusejp_529_;
}
else
{
lean_object* v_reuseFailAlloc_542_; 
v_reuseFailAlloc_542_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_542_, 0, v___x_527_);
lean_ctor_set(v_reuseFailAlloc_542_, 1, v___x_528_);
v___x_530_ = v_reuseFailAlloc_542_;
goto v_reusejp_529_;
}
v_reusejp_529_:
{
lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; 
v___x_531_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__2___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__2___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__2___closed__6);
v___x_532_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_532_, 0, v___x_530_);
lean_ctor_set(v___x_532_, 1, v___x_531_);
v___x_533_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__1___redArg(v___x_532_, v___y_493_, v___y_494_, v___y_495_, v___y_496_);
if (lean_obj_tag(v___x_533_) == 0)
{
lean_dec_ref_known(v___x_533_, 1);
v_a_499_ = v_b_492_;
goto v___jp_498_;
}
else
{
lean_object* v_a_534_; lean_object* v___x_536_; uint8_t v_isShared_537_; uint8_t v_isSharedCheck_541_; 
lean_dec_ref(v_b_492_);
v_a_534_ = lean_ctor_get(v___x_533_, 0);
v_isSharedCheck_541_ = !lean_is_exclusive(v___x_533_);
if (v_isSharedCheck_541_ == 0)
{
v___x_536_ = v___x_533_;
v_isShared_537_ = v_isSharedCheck_541_;
goto v_resetjp_535_;
}
else
{
lean_inc(v_a_534_);
lean_dec(v___x_533_);
v___x_536_ = lean_box(0);
v_isShared_537_ = v_isSharedCheck_541_;
goto v_resetjp_535_;
}
v_resetjp_535_:
{
lean_object* v___x_539_; 
if (v_isShared_537_ == 0)
{
v___x_539_ = v___x_536_;
goto v_reusejp_538_;
}
else
{
lean_object* v_reuseFailAlloc_540_; 
v_reuseFailAlloc_540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_540_, 0, v_a_534_);
v___x_539_ = v_reuseFailAlloc_540_;
goto v_reusejp_538_;
}
v_reusejp_538_:
{
return v___x_539_;
}
}
}
}
}
else
{
lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; 
v___x_543_ = l_Lean_Expr_appArg_x21(v_a_523_);
lean_dec(v_a_523_);
v___x_544_ = l_Lean_Expr_getAppFn(v___x_543_);
v___x_545_ = l_Lean_Expr_constName_x3f(v___x_544_);
lean_dec_ref(v___x_544_);
if (lean_obj_tag(v___x_545_) == 1)
{
lean_object* v_val_546_; lean_object* v___x_547_; lean_object* v___x_549_; 
lean_del_object(v___x_516_);
v_val_546_ = lean_ctor_get(v___x_545_, 0);
lean_inc(v_val_546_);
lean_dec_ref_known(v___x_545_, 1);
v___x_547_ = l_Lean_Expr_getAppNumArgs(v___x_543_);
lean_dec_ref(v___x_543_);
lean_inc(v_a_505_);
if (v_isShared_521_ == 0)
{
lean_ctor_set(v___x_520_, 1, v___x_547_);
lean_ctor_set(v___x_520_, 0, v_a_505_);
v___x_549_ = v___x_520_;
goto v_reusejp_548_;
}
else
{
lean_object* v_reuseFailAlloc_551_; 
v_reuseFailAlloc_551_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_551_, 0, v_a_505_);
lean_ctor_set(v_reuseFailAlloc_551_, 1, v___x_547_);
v___x_549_ = v_reuseFailAlloc_551_;
goto v_reusejp_548_;
}
v_reusejp_548_:
{
lean_object* v___x_550_; 
v___x_550_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_latticeOps_spec__0___redArg(v_b_492_, v_val_546_, v___x_549_);
v_a_499_ = v___x_550_;
goto v___jp_498_;
}
}
else
{
lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_555_; 
lean_dec(v___x_545_);
lean_dec_ref(v___x_543_);
lean_del_object(v___x_520_);
v___x_552_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__2___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__2___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__2___closed__4);
lean_inc(v_a_505_);
v___x_553_ = l_Lean_MessageData_ofName(v_a_505_);
if (v_isShared_517_ == 0)
{
lean_ctor_set_tag(v___x_516_, 7);
lean_ctor_set(v___x_516_, 1, v___x_553_);
lean_ctor_set(v___x_516_, 0, v___x_552_);
v___x_555_ = v___x_516_;
goto v_reusejp_554_;
}
else
{
lean_object* v_reuseFailAlloc_567_; 
v_reuseFailAlloc_567_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_567_, 0, v___x_552_);
lean_ctor_set(v_reuseFailAlloc_567_, 1, v___x_553_);
v___x_555_ = v_reuseFailAlloc_567_;
goto v_reusejp_554_;
}
v_reusejp_554_:
{
lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; 
v___x_556_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__2___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__2___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__2___closed__8);
v___x_557_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_557_, 0, v___x_555_);
lean_ctor_set(v___x_557_, 1, v___x_556_);
v___x_558_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__1___redArg(v___x_557_, v___y_493_, v___y_494_, v___y_495_, v___y_496_);
if (lean_obj_tag(v___x_558_) == 0)
{
lean_dec_ref_known(v___x_558_, 1);
v_a_499_ = v_b_492_;
goto v___jp_498_;
}
else
{
lean_object* v_a_559_; lean_object* v___x_561_; uint8_t v_isShared_562_; uint8_t v_isSharedCheck_566_; 
lean_dec_ref(v_b_492_);
v_a_559_ = lean_ctor_get(v___x_558_, 0);
v_isSharedCheck_566_ = !lean_is_exclusive(v___x_558_);
if (v_isSharedCheck_566_ == 0)
{
v___x_561_ = v___x_558_;
v_isShared_562_ = v_isSharedCheck_566_;
goto v_resetjp_560_;
}
else
{
lean_inc(v_a_559_);
lean_dec(v___x_558_);
v___x_561_ = lean_box(0);
v_isShared_562_ = v_isSharedCheck_566_;
goto v_resetjp_560_;
}
v_resetjp_560_:
{
lean_object* v___x_564_; 
if (v_isShared_562_ == 0)
{
v___x_564_ = v___x_561_;
goto v_reusejp_563_;
}
else
{
lean_object* v_reuseFailAlloc_565_; 
v_reuseFailAlloc_565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_565_, 0, v_a_559_);
v___x_564_ = v_reuseFailAlloc_565_;
goto v_reusejp_563_;
}
v_reusejp_563_:
{
return v___x_564_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_568_; lean_object* v___x_570_; uint8_t v_isShared_571_; uint8_t v_isSharedCheck_575_; 
lean_del_object(v___x_520_);
lean_del_object(v___x_516_);
lean_dec_ref(v_b_492_);
v_a_568_ = lean_ctor_get(v___x_522_, 0);
v_isSharedCheck_575_ = !lean_is_exclusive(v___x_522_);
if (v_isSharedCheck_575_ == 0)
{
v___x_570_ = v___x_522_;
v_isShared_571_ = v_isSharedCheck_575_;
goto v_resetjp_569_;
}
else
{
lean_inc(v_a_568_);
lean_dec(v___x_522_);
v___x_570_ = lean_box(0);
v_isShared_571_ = v_isSharedCheck_575_;
goto v_resetjp_569_;
}
v_resetjp_569_:
{
lean_object* v___x_573_; 
if (v_isShared_571_ == 0)
{
v___x_573_ = v___x_570_;
goto v_reusejp_572_;
}
else
{
lean_object* v_reuseFailAlloc_574_; 
v_reuseFailAlloc_574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_574_, 0, v_a_568_);
v___x_573_ = v_reuseFailAlloc_574_;
goto v_reusejp_572_;
}
v_reusejp_572_:
{
return v___x_573_;
}
}
}
}
}
}
else
{
lean_object* v_a_580_; lean_object* v___x_582_; uint8_t v_isShared_583_; uint8_t v_isSharedCheck_587_; 
lean_dec_ref(v_b_492_);
v_a_580_ = lean_ctor_get(v___x_512_, 0);
v_isSharedCheck_587_ = !lean_is_exclusive(v___x_512_);
if (v_isSharedCheck_587_ == 0)
{
v___x_582_ = v___x_512_;
v_isShared_583_ = v_isSharedCheck_587_;
goto v_resetjp_581_;
}
else
{
lean_inc(v_a_580_);
lean_dec(v___x_512_);
v___x_582_ = lean_box(0);
v_isShared_583_ = v_isSharedCheck_587_;
goto v_resetjp_581_;
}
v_resetjp_581_:
{
lean_object* v___x_585_; 
if (v_isShared_583_ == 0)
{
v___x_585_ = v___x_582_;
goto v_reusejp_584_;
}
else
{
lean_object* v_reuseFailAlloc_586_; 
v_reuseFailAlloc_586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_586_, 0, v_a_580_);
v___x_585_ = v_reuseFailAlloc_586_;
goto v_reusejp_584_;
}
v_reusejp_584_:
{
return v___x_585_;
}
}
}
}
else
{
lean_object* v_a_588_; lean_object* v___x_590_; uint8_t v_isShared_591_; uint8_t v_isSharedCheck_595_; 
lean_dec_ref(v_b_492_);
v_a_588_ = lean_ctor_get(v___x_508_, 0);
v_isSharedCheck_595_ = !lean_is_exclusive(v___x_508_);
if (v_isSharedCheck_595_ == 0)
{
v___x_590_ = v___x_508_;
v_isShared_591_ = v_isSharedCheck_595_;
goto v_resetjp_589_;
}
else
{
lean_inc(v_a_588_);
lean_dec(v___x_508_);
v___x_590_ = lean_box(0);
v_isShared_591_ = v_isSharedCheck_595_;
goto v_resetjp_589_;
}
v_resetjp_589_:
{
lean_object* v___x_593_; 
if (v_isShared_591_ == 0)
{
v___x_593_ = v___x_590_;
goto v_reusejp_592_;
}
else
{
lean_object* v_reuseFailAlloc_594_; 
v_reuseFailAlloc_594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_594_, 0, v_a_588_);
v___x_593_ = v_reuseFailAlloc_594_;
goto v_reusejp_592_;
}
v_reusejp_592_:
{
return v___x_593_;
}
}
}
}
else
{
lean_object* v_a_596_; lean_object* v___x_598_; uint8_t v_isShared_599_; uint8_t v_isSharedCheck_603_; 
lean_dec_ref(v_b_492_);
v_a_596_ = lean_ctor_get(v___x_506_, 0);
v_isSharedCheck_603_ = !lean_is_exclusive(v___x_506_);
if (v_isSharedCheck_603_ == 0)
{
v___x_598_ = v___x_506_;
v_isShared_599_ = v_isSharedCheck_603_;
goto v_resetjp_597_;
}
else
{
lean_inc(v_a_596_);
lean_dec(v___x_506_);
v___x_598_ = lean_box(0);
v_isShared_599_ = v_isSharedCheck_603_;
goto v_resetjp_597_;
}
v_resetjp_597_:
{
lean_object* v___x_601_; 
if (v_isShared_599_ == 0)
{
v___x_601_ = v___x_598_;
goto v_reusejp_600_;
}
else
{
lean_object* v_reuseFailAlloc_602_; 
v_reuseFailAlloc_602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_602_, 0, v_a_596_);
v___x_601_ = v_reuseFailAlloc_602_;
goto v_reusejp_600_;
}
v_reusejp_600_:
{
return v___x_601_;
}
}
}
}
v___jp_498_:
{
size_t v___x_500_; size_t v___x_501_; 
v___x_500_ = ((size_t)1ULL);
v___x_501_ = lean_usize_add(v_i_491_, v___x_500_);
v_i_491_ = v___x_501_;
v_b_492_ = v_a_499_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__2___boxed(lean_object* v_as_604_, lean_object* v_sz_605_, lean_object* v_i_606_, lean_object* v_b_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_){
_start:
{
size_t v_sz_boxed_613_; size_t v_i_boxed_614_; lean_object* v_res_615_; 
v_sz_boxed_613_ = lean_unbox_usize(v_sz_605_);
lean_dec(v_sz_605_);
v_i_boxed_614_ = lean_unbox_usize(v_i_606_);
lean_dec(v_i_606_);
v_res_615_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__2(v_as_604_, v_sz_boxed_613_, v_i_boxed_614_, v_b_607_, v___y_608_, v___y_609_, v___y_610_, v___y_611_);
lean_dec(v___y_611_);
lean_dec_ref(v___y_610_);
lean_dec(v___y_609_);
lean_dec_ref(v___y_608_);
lean_dec_ref(v_as_604_);
return v_res_615_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals(lean_object* v_names_616_, lean_object* v_a_617_, lean_object* v_a_618_, lean_object* v_a_619_, lean_object* v_a_620_){
_start:
{
lean_object* v_m_622_; size_t v_sz_623_; size_t v___x_624_; lean_object* v___x_625_; 
v_m_622_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_latticeOps___closed__1, &l_Lean_Elab_Tactic_Do_Internal_VCGen_latticeOps___closed__1_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_latticeOps___closed__1);
v_sz_623_ = lean_array_size(v_names_616_);
v___x_624_ = ((size_t)0ULL);
v___x_625_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__2(v_names_616_, v_sz_623_, v___x_624_, v_m_622_, v_a_617_, v_a_618_, v_a_619_, v_a_620_);
return v___x_625_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals___boxed(lean_object* v_names_626_, lean_object* v_a_627_, lean_object* v_a_628_, lean_object* v_a_629_, lean_object* v_a_630_, lean_object* v_a_631_){
_start:
{
lean_object* v_res_632_; 
v_res_632_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals(v_names_626_, v_a_627_, v_a_628_, v_a_629_, v_a_630_);
lean_dec(v_a_630_);
lean_dec_ref(v_a_629_);
lean_dec(v_a_628_);
lean_dec_ref(v_a_627_);
lean_dec_ref(v_names_626_);
return v_res_632_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__1(lean_object* v_00_u03b1_633_, lean_object* v_msg_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_){
_start:
{
lean_object* v___x_640_; 
v___x_640_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__1___redArg(v_msg_634_, v___y_635_, v___y_636_, v___y_637_, v___y_638_);
return v___x_640_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__1___boxed(lean_object* v_00_u03b1_641_, lean_object* v_msg_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_, lean_object* v___y_646_, lean_object* v___y_647_){
_start:
{
lean_object* v_res_648_; 
v_res_648_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__1(v_00_u03b1_641_, v_msg_642_, v___y_643_, v___y_644_, v___y_645_, v___y_646_);
lean_dec(v___y_646_);
lean_dec_ref(v___y_645_);
lean_dec(v___y_644_);
lean_dec_ref(v___y_643_);
return v_res_648_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_go___lam__0(uint8_t v_isZero_649_, lean_object* v_x_650_, lean_object* v___y_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_){
_start:
{
lean_object* v___x_661_; lean_object* v___x_662_; 
v___x_661_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_661_, 0, v_isZero_649_);
lean_ctor_set_uint8(v___x_661_, 1, v_isZero_649_);
v___x_662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_662_, 0, v___x_661_);
return v___x_662_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_go___lam__0___boxed(lean_object* v_isZero_663_, lean_object* v_x_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_){
_start:
{
uint8_t v_isZero_boxed_675_; lean_object* v_res_676_; 
v_isZero_boxed_675_ = lean_unbox(v_isZero_663_);
v_res_676_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_go___lam__0(v_isZero_boxed_675_, v_x_664_, v___y_665_, v___y_666_, v___y_667_, v___y_668_, v___y_669_, v___y_670_, v___y_671_, v___y_672_, v___y_673_);
lean_dec(v___y_673_);
lean_dec_ref(v___y_672_);
lean_dec(v___y_671_);
lean_dec_ref(v___y_670_);
lean_dec(v___y_669_);
lean_dec_ref(v___y_668_);
lean_dec(v___y_667_);
lean_dec_ref(v___y_666_);
lean_dec(v___y_665_);
lean_dec_ref(v_x_664_);
return v_res_676_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_go_spec__0___redArg(lean_object* v_msg_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_){
_start:
{
lean_object* v_ref_683_; lean_object* v___x_684_; lean_object* v_a_685_; lean_object* v___x_687_; uint8_t v_isShared_688_; uint8_t v_isSharedCheck_693_; 
v_ref_683_ = lean_ctor_get(v___y_680_, 5);
v___x_684_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__1_spec__1(v_msg_677_, v___y_678_, v___y_679_, v___y_680_, v___y_681_);
v_a_685_ = lean_ctor_get(v___x_684_, 0);
v_isSharedCheck_693_ = !lean_is_exclusive(v___x_684_);
if (v_isSharedCheck_693_ == 0)
{
v___x_687_ = v___x_684_;
v_isShared_688_ = v_isSharedCheck_693_;
goto v_resetjp_686_;
}
else
{
lean_inc(v_a_685_);
lean_dec(v___x_684_);
v___x_687_ = lean_box(0);
v_isShared_688_ = v_isSharedCheck_693_;
goto v_resetjp_686_;
}
v_resetjp_686_:
{
lean_object* v___x_689_; lean_object* v___x_691_; 
lean_inc(v_ref_683_);
v___x_689_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_689_, 0, v_ref_683_);
lean_ctor_set(v___x_689_, 1, v_a_685_);
if (v_isShared_688_ == 0)
{
lean_ctor_set_tag(v___x_687_, 1);
lean_ctor_set(v___x_687_, 0, v___x_689_);
v___x_691_ = v___x_687_;
goto v_reusejp_690_;
}
else
{
lean_object* v_reuseFailAlloc_692_; 
v_reuseFailAlloc_692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_692_, 0, v___x_689_);
v___x_691_ = v_reuseFailAlloc_692_;
goto v_reusejp_690_;
}
v_reusejp_690_:
{
return v___x_691_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_go_spec__0___redArg___boxed(lean_object* v_msg_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_){
_start:
{
lean_object* v_res_700_; 
v_res_700_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_go_spec__0___redArg(v_msg_694_, v___y_695_, v___y_696_, v___y_697_, v___y_698_);
lean_dec(v___y_698_);
lean_dec_ref(v___y_697_);
lean_dec(v___y_696_);
lean_dec_ref(v___y_695_);
return v_res_700_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_go___closed__1(void){
_start:
{
lean_object* v___x_702_; lean_object* v___x_703_; 
v___x_702_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_go___closed__0));
v___x_703_ = l_Lean_stringToMessageData(v___x_702_);
return v___x_703_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_go(lean_object* v_step_707_, lean_object* v_e_u2080_708_, lean_object* v_cur_709_, lean_object* v_proof_x3f_710_, lean_object* v_a_711_, lean_object* v_a_712_, lean_object* v_a_713_, lean_object* v_a_714_, lean_object* v_a_715_, lean_object* v_a_716_, lean_object* v_a_717_){
_start:
{
lean_object* v_zero_719_; uint8_t v_isZero_720_; 
v_zero_719_ = lean_unsigned_to_nat(0u);
v_isZero_720_ = lean_nat_dec_eq(v_a_711_, v_zero_719_);
if (v_isZero_720_ == 1)
{
lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; 
lean_dec(v_a_711_);
lean_dec(v_proof_x3f_710_);
lean_dec_ref(v_e_u2080_708_);
lean_dec_ref(v_step_707_);
v___x_721_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_go___closed__1, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_go___closed__1_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_go___closed__1);
v___x_722_ = l_Lean_indentExpr(v_cur_709_);
v___x_723_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_723_, 0, v___x_721_);
lean_ctor_set(v___x_723_, 1, v___x_722_);
v___x_724_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_go_spec__0___redArg(v___x_723_, v_a_714_, v_a_715_, v_a_716_, v_a_717_);
return v___x_724_;
}
else
{
lean_object* v___x_725_; lean_object* v___f_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; 
v___x_725_ = lean_box(v_isZero_720_);
v___f_726_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_go___lam__0___boxed), 12, 1);
lean_closure_set(v___f_726_, 0, v___x_725_);
lean_inc_ref(v_step_707_);
lean_inc_ref(v_cur_709_);
v___x_727_ = lean_apply_1(v_step_707_, v_cur_709_);
lean_inc_ref(v___f_726_);
v___x_728_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_728_, 0, v___f_726_);
lean_ctor_set(v___x_728_, 1, v___f_726_);
v___x_729_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_go___closed__2));
v___x_730_ = l_Lean_Meta_Sym_Simp_SimpM_run_x27___redArg(v___x_727_, v___x_728_, v___x_729_, v_a_712_, v_a_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_);
if (lean_obj_tag(v___x_730_) == 0)
{
lean_object* v_a_731_; lean_object* v___x_733_; uint8_t v_isShared_734_; uint8_t v_isSharedCheck_764_; 
v_a_731_ = lean_ctor_get(v___x_730_, 0);
v_isSharedCheck_764_ = !lean_is_exclusive(v___x_730_);
if (v_isSharedCheck_764_ == 0)
{
v___x_733_ = v___x_730_;
v_isShared_734_ = v_isSharedCheck_764_;
goto v_resetjp_732_;
}
else
{
lean_inc(v_a_731_);
lean_dec(v___x_730_);
v___x_733_ = lean_box(0);
v_isShared_734_ = v_isSharedCheck_764_;
goto v_resetjp_732_;
}
v_resetjp_732_:
{
if (lean_obj_tag(v_a_731_) == 0)
{
lean_object* v___x_735_; lean_object* v___x_737_; 
lean_dec_ref_known(v_a_731_, 0);
lean_dec(v_a_711_);
lean_dec_ref(v_e_u2080_708_);
lean_dec_ref(v_step_707_);
v___x_735_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_735_, 0, v_cur_709_);
lean_ctor_set(v___x_735_, 1, v_proof_x3f_710_);
if (v_isShared_734_ == 0)
{
lean_ctor_set(v___x_733_, 0, v___x_735_);
v___x_737_ = v___x_733_;
goto v_reusejp_736_;
}
else
{
lean_object* v_reuseFailAlloc_738_; 
v_reuseFailAlloc_738_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_738_, 0, v___x_735_);
v___x_737_ = v_reuseFailAlloc_738_;
goto v_reusejp_736_;
}
v_reusejp_736_:
{
return v___x_737_;
}
}
else
{
lean_object* v_e_x27_739_; lean_object* v_proof_740_; lean_object* v_one_741_; lean_object* v_n_742_; lean_object* v_proof_744_; lean_object* v___y_745_; lean_object* v___y_746_; lean_object* v___y_747_; lean_object* v___y_748_; lean_object* v___y_749_; lean_object* v___y_750_; 
lean_del_object(v___x_733_);
v_e_x27_739_ = lean_ctor_get(v_a_731_, 0);
lean_inc_ref(v_e_x27_739_);
v_proof_740_ = lean_ctor_get(v_a_731_, 1);
lean_inc_ref(v_proof_740_);
lean_dec_ref_known(v_a_731_, 2);
v_one_741_ = lean_unsigned_to_nat(1u);
v_n_742_ = lean_nat_sub(v_a_711_, v_one_741_);
lean_dec(v_a_711_);
if (lean_obj_tag(v_proof_x3f_710_) == 0)
{
lean_dec_ref(v_cur_709_);
v_proof_744_ = v_proof_740_;
v___y_745_ = v_a_712_;
v___y_746_ = v_a_713_;
v___y_747_ = v_a_714_;
v___y_748_ = v_a_715_;
v___y_749_ = v_a_716_;
v___y_750_ = v_a_717_;
goto v___jp_743_;
}
else
{
lean_object* v_val_753_; lean_object* v___x_754_; 
v_val_753_ = lean_ctor_get(v_proof_x3f_710_, 0);
lean_inc(v_val_753_);
lean_dec_ref_known(v_proof_x3f_710_, 1);
lean_inc_ref(v_e_x27_739_);
lean_inc_ref(v_e_u2080_708_);
v___x_754_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v_e_u2080_708_, v_cur_709_, v_val_753_, v_e_x27_739_, v_proof_740_, v_a_712_, v_a_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_);
if (lean_obj_tag(v___x_754_) == 0)
{
lean_object* v_a_755_; 
v_a_755_ = lean_ctor_get(v___x_754_, 0);
lean_inc(v_a_755_);
lean_dec_ref_known(v___x_754_, 1);
v_proof_744_ = v_a_755_;
v___y_745_ = v_a_712_;
v___y_746_ = v_a_713_;
v___y_747_ = v_a_714_;
v___y_748_ = v_a_715_;
v___y_749_ = v_a_716_;
v___y_750_ = v_a_717_;
goto v___jp_743_;
}
else
{
lean_object* v_a_756_; lean_object* v___x_758_; uint8_t v_isShared_759_; uint8_t v_isSharedCheck_763_; 
lean_dec(v_n_742_);
lean_dec_ref(v_e_x27_739_);
lean_dec_ref(v_e_u2080_708_);
lean_dec_ref(v_step_707_);
v_a_756_ = lean_ctor_get(v___x_754_, 0);
v_isSharedCheck_763_ = !lean_is_exclusive(v___x_754_);
if (v_isSharedCheck_763_ == 0)
{
v___x_758_ = v___x_754_;
v_isShared_759_ = v_isSharedCheck_763_;
goto v_resetjp_757_;
}
else
{
lean_inc(v_a_756_);
lean_dec(v___x_754_);
v___x_758_ = lean_box(0);
v_isShared_759_ = v_isSharedCheck_763_;
goto v_resetjp_757_;
}
v_resetjp_757_:
{
lean_object* v___x_761_; 
if (v_isShared_759_ == 0)
{
v___x_761_ = v___x_758_;
goto v_reusejp_760_;
}
else
{
lean_object* v_reuseFailAlloc_762_; 
v_reuseFailAlloc_762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_762_, 0, v_a_756_);
v___x_761_ = v_reuseFailAlloc_762_;
goto v_reusejp_760_;
}
v_reusejp_760_:
{
return v___x_761_;
}
}
}
}
v___jp_743_:
{
lean_object* v___x_751_; 
v___x_751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_751_, 0, v_proof_744_);
v_cur_709_ = v_e_x27_739_;
v_proof_x3f_710_ = v___x_751_;
v_a_711_ = v_n_742_;
v_a_712_ = v___y_745_;
v_a_713_ = v___y_746_;
v_a_714_ = v___y_747_;
v_a_715_ = v___y_748_;
v_a_716_ = v___y_749_;
v_a_717_ = v___y_750_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_765_; lean_object* v___x_767_; uint8_t v_isShared_768_; uint8_t v_isSharedCheck_772_; 
lean_dec(v_a_711_);
lean_dec(v_proof_x3f_710_);
lean_dec_ref(v_cur_709_);
lean_dec_ref(v_e_u2080_708_);
lean_dec_ref(v_step_707_);
v_a_765_ = lean_ctor_get(v___x_730_, 0);
v_isSharedCheck_772_ = !lean_is_exclusive(v___x_730_);
if (v_isSharedCheck_772_ == 0)
{
v___x_767_ = v___x_730_;
v_isShared_768_ = v_isSharedCheck_772_;
goto v_resetjp_766_;
}
else
{
lean_inc(v_a_765_);
lean_dec(v___x_730_);
v___x_767_ = lean_box(0);
v_isShared_768_ = v_isSharedCheck_772_;
goto v_resetjp_766_;
}
v_resetjp_766_:
{
lean_object* v___x_770_; 
if (v_isShared_768_ == 0)
{
v___x_770_ = v___x_767_;
goto v_reusejp_769_;
}
else
{
lean_object* v_reuseFailAlloc_771_; 
v_reuseFailAlloc_771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_771_, 0, v_a_765_);
v___x_770_ = v_reuseFailAlloc_771_;
goto v_reusejp_769_;
}
v_reusejp_769_:
{
return v___x_770_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_go___boxed(lean_object* v_step_773_, lean_object* v_e_u2080_774_, lean_object* v_cur_775_, lean_object* v_proof_x3f_776_, lean_object* v_a_777_, lean_object* v_a_778_, lean_object* v_a_779_, lean_object* v_a_780_, lean_object* v_a_781_, lean_object* v_a_782_, lean_object* v_a_783_, lean_object* v_a_784_){
_start:
{
lean_object* v_res_785_; 
v_res_785_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_go(v_step_773_, v_e_u2080_774_, v_cur_775_, v_proof_x3f_776_, v_a_777_, v_a_778_, v_a_779_, v_a_780_, v_a_781_, v_a_782_, v_a_783_);
lean_dec(v_a_783_);
lean_dec_ref(v_a_782_);
lean_dec(v_a_781_);
lean_dec_ref(v_a_780_);
lean_dec(v_a_779_);
lean_dec_ref(v_a_778_);
return v_res_785_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_go_spec__0(lean_object* v_00_u03b1_786_, lean_object* v_msg_787_, lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v___y_793_){
_start:
{
lean_object* v___x_795_; 
v___x_795_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_go_spec__0___redArg(v_msg_787_, v___y_790_, v___y_791_, v___y_792_, v___y_793_);
return v___x_795_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_go_spec__0___boxed(lean_object* v_00_u03b1_796_, lean_object* v_msg_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_){
_start:
{
lean_object* v_res_805_; 
v_res_805_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_go_spec__0(v_00_u03b1_796_, v_msg_797_, v___y_798_, v___y_799_, v___y_800_, v___y_801_, v___y_802_, v___y_803_);
lean_dec(v___y_803_);
lean_dec_ref(v___y_802_);
lean_dec(v___y_801_);
lean_dec_ref(v___y_800_);
lean_dec(v___y_799_);
lean_dec_ref(v___y_798_);
return v_res_805_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_spec__0___redArg(lean_object* v_as_806_, size_t v_i_807_, size_t v_stop_808_, lean_object* v_b_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_){
_start:
{
uint8_t v___x_815_; 
v___x_815_ = lean_usize_dec_eq(v_i_807_, v_stop_808_);
if (v___x_815_ == 0)
{
lean_object* v___x_816_; lean_object* v___x_817_; 
v___x_816_ = lean_array_uget_borrowed(v_as_806_, v_i_807_);
lean_inc(v___x_816_);
v___x_817_ = l_Lean_Meta_Sym_Simp_mkTheoremFromDecl(v___x_816_, v___y_810_, v___y_811_, v___y_812_, v___y_813_);
if (lean_obj_tag(v___x_817_) == 0)
{
lean_object* v_a_818_; lean_object* v___x_819_; size_t v___x_820_; size_t v___x_821_; 
v_a_818_ = lean_ctor_get(v___x_817_, 0);
lean_inc(v_a_818_);
lean_dec_ref_known(v___x_817_, 1);
v___x_819_ = l_Lean_Meta_Sym_Simp_Theorems_insert(v_b_809_, v_a_818_);
v___x_820_ = ((size_t)1ULL);
v___x_821_ = lean_usize_add(v_i_807_, v___x_820_);
v_i_807_ = v___x_821_;
v_b_809_ = v___x_819_;
goto _start;
}
else
{
lean_object* v_a_823_; lean_object* v___x_825_; uint8_t v_isShared_826_; uint8_t v_isSharedCheck_830_; 
lean_dec_ref(v_b_809_);
v_a_823_ = lean_ctor_get(v___x_817_, 0);
v_isSharedCheck_830_ = !lean_is_exclusive(v___x_817_);
if (v_isSharedCheck_830_ == 0)
{
v___x_825_ = v___x_817_;
v_isShared_826_ = v_isSharedCheck_830_;
goto v_resetjp_824_;
}
else
{
lean_inc(v_a_823_);
lean_dec(v___x_817_);
v___x_825_ = lean_box(0);
v_isShared_826_ = v_isSharedCheck_830_;
goto v_resetjp_824_;
}
v_resetjp_824_:
{
lean_object* v___x_828_; 
if (v_isShared_826_ == 0)
{
v___x_828_ = v___x_825_;
goto v_reusejp_827_;
}
else
{
lean_object* v_reuseFailAlloc_829_; 
v_reuseFailAlloc_829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_829_, 0, v_a_823_);
v___x_828_ = v_reuseFailAlloc_829_;
goto v_reusejp_827_;
}
v_reusejp_827_:
{
return v___x_828_;
}
}
}
}
else
{
lean_object* v___x_831_; 
v___x_831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_831_, 0, v_b_809_);
return v___x_831_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_spec__0___redArg___boxed(lean_object* v_as_832_, lean_object* v_i_833_, lean_object* v_stop_834_, lean_object* v_b_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_, lean_object* v___y_840_){
_start:
{
size_t v_i_boxed_841_; size_t v_stop_boxed_842_; lean_object* v_res_843_; 
v_i_boxed_841_ = lean_unbox_usize(v_i_833_);
lean_dec(v_i_833_);
v_stop_boxed_842_ = lean_unbox_usize(v_stop_834_);
lean_dec(v_stop_834_);
v_res_843_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_spec__0___redArg(v_as_832_, v_i_boxed_841_, v_stop_boxed_842_, v_b_835_, v___y_836_, v___y_837_, v___y_838_, v___y_839_);
lean_dec(v___y_839_);
lean_dec_ref(v___y_838_);
lean_dec(v___y_837_);
lean_dec_ref(v___y_836_);
lean_dec_ref(v_as_832_);
return v_res_843_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp___closed__1(void){
_start:
{
lean_object* v___x_845_; 
v___x_845_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_845_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp___closed__2(void){
_start:
{
lean_object* v___x_846_; lean_object* v___x_847_; 
v___x_846_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp___closed__1, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp___closed__1_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp___closed__1);
v___x_847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_847_, 0, v___x_846_);
return v___x_847_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp(lean_object* v_rewrites_848_, lean_object* v_e_849_, lean_object* v_fuel_850_, lean_object* v_a_851_, lean_object* v_a_852_, lean_object* v_a_853_, lean_object* v_a_854_, lean_object* v_a_855_, lean_object* v_a_856_){
_start:
{
lean_object* v_a_859_; lean_object* v___y_875_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; uint8_t v___x_888_; 
v___x_885_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp___closed__2, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp___closed__2_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp___closed__2);
v___x_886_ = lean_unsigned_to_nat(0u);
v___x_887_ = lean_array_get_size(v_rewrites_848_);
v___x_888_ = lean_nat_dec_lt(v___x_886_, v___x_887_);
if (v___x_888_ == 0)
{
v_a_859_ = v___x_885_;
goto v___jp_858_;
}
else
{
uint8_t v___x_889_; 
v___x_889_ = lean_nat_dec_le(v___x_887_, v___x_887_);
if (v___x_889_ == 0)
{
if (v___x_888_ == 0)
{
v_a_859_ = v___x_885_;
goto v___jp_858_;
}
else
{
size_t v___x_890_; size_t v___x_891_; lean_object* v___x_892_; 
v___x_890_ = ((size_t)0ULL);
v___x_891_ = lean_usize_of_nat(v___x_887_);
v___x_892_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_spec__0___redArg(v_rewrites_848_, v___x_890_, v___x_891_, v___x_885_, v_a_853_, v_a_854_, v_a_855_, v_a_856_);
v___y_875_ = v___x_892_;
goto v___jp_874_;
}
}
else
{
size_t v___x_893_; size_t v___x_894_; lean_object* v___x_895_; 
v___x_893_ = ((size_t)0ULL);
v___x_894_ = lean_usize_of_nat(v___x_887_);
v___x_895_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_spec__0___redArg(v_rewrites_848_, v___x_893_, v___x_894_, v___x_885_, v_a_853_, v_a_854_, v_a_855_, v_a_856_);
v___y_875_ = v___x_895_;
goto v___jp_874_;
}
}
v___jp_858_:
{
lean_object* v___x_860_; 
v___x_860_ = l_Lean_Meta_Sym_shareCommon(v_e_849_, v_a_851_, v_a_852_, v_a_853_, v_a_854_, v_a_855_, v_a_856_);
if (lean_obj_tag(v___x_860_) == 0)
{
lean_object* v_a_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; 
v_a_861_ = lean_ctor_get(v___x_860_, 0);
lean_inc_n(v_a_861_, 2);
lean_dec_ref_known(v___x_860_, 1);
v___x_862_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp___closed__0));
v___x_863_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Simp_Theorems_rewrite___boxed), 13, 2);
lean_closure_set(v___x_863_, 0, v_a_859_);
lean_closure_set(v___x_863_, 1, v___x_862_);
v___x_864_ = lean_box(0);
v___x_865_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_go(v___x_863_, v_a_861_, v_a_861_, v___x_864_, v_fuel_850_, v_a_851_, v_a_852_, v_a_853_, v_a_854_, v_a_855_, v_a_856_);
return v___x_865_;
}
else
{
lean_object* v_a_866_; lean_object* v___x_868_; uint8_t v_isShared_869_; uint8_t v_isSharedCheck_873_; 
lean_dec_ref(v_a_859_);
lean_dec(v_fuel_850_);
v_a_866_ = lean_ctor_get(v___x_860_, 0);
v_isSharedCheck_873_ = !lean_is_exclusive(v___x_860_);
if (v_isSharedCheck_873_ == 0)
{
v___x_868_ = v___x_860_;
v_isShared_869_ = v_isSharedCheck_873_;
goto v_resetjp_867_;
}
else
{
lean_inc(v_a_866_);
lean_dec(v___x_860_);
v___x_868_ = lean_box(0);
v_isShared_869_ = v_isSharedCheck_873_;
goto v_resetjp_867_;
}
v_resetjp_867_:
{
lean_object* v___x_871_; 
if (v_isShared_869_ == 0)
{
v___x_871_ = v___x_868_;
goto v_reusejp_870_;
}
else
{
lean_object* v_reuseFailAlloc_872_; 
v_reuseFailAlloc_872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_872_, 0, v_a_866_);
v___x_871_ = v_reuseFailAlloc_872_;
goto v_reusejp_870_;
}
v_reusejp_870_:
{
return v___x_871_;
}
}
}
}
v___jp_874_:
{
if (lean_obj_tag(v___y_875_) == 0)
{
lean_object* v_a_876_; 
v_a_876_ = lean_ctor_get(v___y_875_, 0);
lean_inc(v_a_876_);
lean_dec_ref_known(v___y_875_, 1);
v_a_859_ = v_a_876_;
goto v___jp_858_;
}
else
{
lean_object* v_a_877_; lean_object* v___x_879_; uint8_t v_isShared_880_; uint8_t v_isSharedCheck_884_; 
lean_dec(v_fuel_850_);
lean_dec_ref(v_e_849_);
v_a_877_ = lean_ctor_get(v___y_875_, 0);
v_isSharedCheck_884_ = !lean_is_exclusive(v___y_875_);
if (v_isSharedCheck_884_ == 0)
{
v___x_879_ = v___y_875_;
v_isShared_880_ = v_isSharedCheck_884_;
goto v_resetjp_878_;
}
else
{
lean_inc(v_a_877_);
lean_dec(v___y_875_);
v___x_879_ = lean_box(0);
v_isShared_880_ = v_isSharedCheck_884_;
goto v_resetjp_878_;
}
v_resetjp_878_:
{
lean_object* v___x_882_; 
if (v_isShared_880_ == 0)
{
v___x_882_ = v___x_879_;
goto v_reusejp_881_;
}
else
{
lean_object* v_reuseFailAlloc_883_; 
v_reuseFailAlloc_883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_883_, 0, v_a_877_);
v___x_882_ = v_reuseFailAlloc_883_;
goto v_reusejp_881_;
}
v_reusejp_881_:
{
return v___x_882_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp___boxed(lean_object* v_rewrites_896_, lean_object* v_e_897_, lean_object* v_fuel_898_, lean_object* v_a_899_, lean_object* v_a_900_, lean_object* v_a_901_, lean_object* v_a_902_, lean_object* v_a_903_, lean_object* v_a_904_, lean_object* v_a_905_){
_start:
{
lean_object* v_res_906_; 
v_res_906_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp(v_rewrites_896_, v_e_897_, v_fuel_898_, v_a_899_, v_a_900_, v_a_901_, v_a_902_, v_a_903_, v_a_904_);
lean_dec(v_a_904_);
lean_dec_ref(v_a_903_);
lean_dec(v_a_902_);
lean_dec_ref(v_a_901_);
lean_dec(v_a_900_);
lean_dec_ref(v_a_899_);
lean_dec_ref(v_rewrites_896_);
return v_res_906_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_spec__0(lean_object* v_as_907_, size_t v_i_908_, size_t v_stop_909_, lean_object* v_b_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_){
_start:
{
lean_object* v___x_918_; 
v___x_918_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_spec__0___redArg(v_as_907_, v_i_908_, v_stop_909_, v_b_910_, v___y_913_, v___y_914_, v___y_915_, v___y_916_);
return v___x_918_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_spec__0___boxed(lean_object* v_as_919_, lean_object* v_i_920_, lean_object* v_stop_921_, lean_object* v_b_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_){
_start:
{
size_t v_i_boxed_930_; size_t v_stop_boxed_931_; lean_object* v_res_932_; 
v_i_boxed_930_ = lean_unbox_usize(v_i_920_);
lean_dec(v_i_920_);
v_stop_boxed_931_ = lean_unbox_usize(v_stop_921_);
lean_dec(v_stop_921_);
v_res_932_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_spec__0(v_as_919_, v_i_boxed_930_, v_stop_boxed_931_, v_b_922_, v___y_923_, v___y_924_, v___y_925_, v___y_926_, v___y_927_, v___y_928_);
lean_dec(v___y_928_);
lean_dec_ref(v___y_927_);
lean_dec(v___y_926_);
lean_dec_ref(v___y_925_);
lean_dec(v___y_924_);
lean_dec_ref(v___y_923_);
lean_dec_ref(v_as_919_);
return v_res_932_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply___lam__0(lean_object* v_s_933_, lean_object* v_a_934_, lean_object* v_pre_935_, lean_object* v_u_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_){
_start:
{
lean_object* v___x_942_; 
lean_inc_ref(v_u_936_);
v___x_942_ = l_Lean_Meta_mkEq(v_u_936_, v_s_933_, v___y_937_, v___y_938_, v___y_939_, v___y_940_);
if (lean_obj_tag(v___x_942_) == 0)
{
lean_object* v_a_943_; lean_object* v___x_945_; uint8_t v_isShared_946_; uint8_t v_isSharedCheck_974_; 
v_a_943_ = lean_ctor_get(v___x_942_, 0);
v_isSharedCheck_974_ = !lean_is_exclusive(v___x_942_);
if (v_isSharedCheck_974_ == 0)
{
v___x_945_ = v___x_942_;
v_isShared_946_ = v_isSharedCheck_974_;
goto v_resetjp_944_;
}
else
{
lean_inc(v_a_943_);
lean_dec(v___x_942_);
v___x_945_ = lean_box(0);
v_isShared_946_ = v_isSharedCheck_974_;
goto v_resetjp_944_;
}
v_resetjp_944_:
{
lean_object* v___x_947_; lean_object* v___x_949_; 
v___x_947_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_ofProp___closed__2));
if (v_isShared_946_ == 0)
{
lean_ctor_set_tag(v___x_945_, 1);
lean_ctor_set(v___x_945_, 0, v_a_934_);
v___x_949_ = v___x_945_;
goto v_reusejp_948_;
}
else
{
lean_object* v_reuseFailAlloc_973_; 
v_reuseFailAlloc_973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_973_, 0, v_a_934_);
v___x_949_ = v_reuseFailAlloc_973_;
goto v_reusejp_948_;
}
v_reusejp_948_:
{
lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; 
v___x_950_ = lean_box(0);
v___x_951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_951_, 0, v_a_943_);
v___x_952_ = lean_unsigned_to_nat(3u);
v___x_953_ = lean_mk_empty_array_with_capacity(v___x_952_);
v___x_954_ = lean_array_push(v___x_953_, v___x_949_);
v___x_955_ = lean_array_push(v___x_954_, v___x_950_);
v___x_956_ = lean_array_push(v___x_955_, v___x_951_);
v___x_957_ = l_Lean_Meta_mkAppOptM(v___x_947_, v___x_956_, v___y_937_, v___y_938_, v___y_939_, v___y_940_);
if (lean_obj_tag(v___x_957_) == 0)
{
lean_object* v_a_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; 
v_a_958_ = lean_ctor_get(v___x_957_, 0);
lean_inc(v_a_958_);
lean_dec_ref_known(v___x_957_, 1);
v___x_959_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_meet___closed__3));
v___x_960_ = lean_unsigned_to_nat(2u);
v___x_961_ = lean_mk_empty_array_with_capacity(v___x_960_);
v___x_962_ = lean_array_push(v___x_961_, v_a_958_);
v___x_963_ = lean_array_push(v___x_962_, v_pre_935_);
v___x_964_ = l_Lean_Meta_mkAppM(v___x_959_, v___x_963_, v___y_937_, v___y_938_, v___y_939_, v___y_940_);
if (lean_obj_tag(v___x_964_) == 0)
{
lean_object* v_a_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; uint8_t v___x_969_; uint8_t v___x_970_; uint8_t v___x_971_; lean_object* v___x_972_; 
v_a_965_ = lean_ctor_get(v___x_964_, 0);
lean_inc(v_a_965_);
lean_dec_ref_known(v___x_964_, 1);
v___x_966_ = lean_unsigned_to_nat(1u);
v___x_967_ = lean_mk_empty_array_with_capacity(v___x_966_);
v___x_968_ = lean_array_push(v___x_967_, v_u_936_);
v___x_969_ = 0;
v___x_970_ = 1;
v___x_971_ = 1;
v___x_972_ = l_Lean_Meta_mkLambdaFVars(v___x_968_, v_a_965_, v___x_969_, v___x_970_, v___x_969_, v___x_970_, v___x_971_, v___y_937_, v___y_938_, v___y_939_, v___y_940_);
lean_dec_ref(v___x_968_);
return v___x_972_;
}
else
{
lean_dec_ref(v_u_936_);
return v___x_964_;
}
}
else
{
lean_dec_ref(v_u_936_);
lean_dec_ref(v_pre_935_);
return v___x_957_;
}
}
}
}
else
{
lean_dec_ref(v_u_936_);
lean_dec_ref(v_pre_935_);
lean_dec_ref(v_a_934_);
return v___x_942_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply___lam__0___boxed(lean_object* v_s_975_, lean_object* v_a_976_, lean_object* v_pre_977_, lean_object* v_u_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_){
_start:
{
lean_object* v_res_984_; 
v_res_984_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply___lam__0(v_s_975_, v_a_976_, v_pre_977_, v_u_978_, v___y_979_, v___y_980_, v___y_981_, v___y_982_);
lean_dec(v___y_982_);
lean_dec_ref(v___y_981_);
lean_dec(v___y_980_);
lean_dec_ref(v___y_979_);
return v_res_984_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply_spec__0_spec__0___redArg___lam__0(lean_object* v_k_985_, lean_object* v_b_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_){
_start:
{
lean_object* v___x_992_; 
lean_inc(v___y_990_);
lean_inc_ref(v___y_989_);
lean_inc(v___y_988_);
lean_inc_ref(v___y_987_);
v___x_992_ = lean_apply_6(v_k_985_, v_b_986_, v___y_987_, v___y_988_, v___y_989_, v___y_990_, lean_box(0));
return v___x_992_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply_spec__0_spec__0___redArg___lam__0___boxed(lean_object* v_k_993_, lean_object* v_b_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_){
_start:
{
lean_object* v_res_1000_; 
v_res_1000_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply_spec__0_spec__0___redArg___lam__0(v_k_993_, v_b_994_, v___y_995_, v___y_996_, v___y_997_, v___y_998_);
lean_dec(v___y_998_);
lean_dec_ref(v___y_997_);
lean_dec(v___y_996_);
lean_dec_ref(v___y_995_);
return v_res_1000_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply_spec__0_spec__0___redArg(lean_object* v_name_1001_, uint8_t v_bi_1002_, lean_object* v_type_1003_, lean_object* v_k_1004_, uint8_t v_kind_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_){
_start:
{
lean_object* v___f_1011_; lean_object* v___x_1012_; 
v___f_1011_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply_spec__0_spec__0___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1011_, 0, v_k_1004_);
v___x_1012_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1001_, v_bi_1002_, v_type_1003_, v___f_1011_, v_kind_1005_, v___y_1006_, v___y_1007_, v___y_1008_, v___y_1009_);
if (lean_obj_tag(v___x_1012_) == 0)
{
lean_object* v_a_1013_; lean_object* v___x_1015_; uint8_t v_isShared_1016_; uint8_t v_isSharedCheck_1020_; 
v_a_1013_ = lean_ctor_get(v___x_1012_, 0);
v_isSharedCheck_1020_ = !lean_is_exclusive(v___x_1012_);
if (v_isSharedCheck_1020_ == 0)
{
v___x_1015_ = v___x_1012_;
v_isShared_1016_ = v_isSharedCheck_1020_;
goto v_resetjp_1014_;
}
else
{
lean_inc(v_a_1013_);
lean_dec(v___x_1012_);
v___x_1015_ = lean_box(0);
v_isShared_1016_ = v_isSharedCheck_1020_;
goto v_resetjp_1014_;
}
v_resetjp_1014_:
{
lean_object* v___x_1018_; 
if (v_isShared_1016_ == 0)
{
v___x_1018_ = v___x_1015_;
goto v_reusejp_1017_;
}
else
{
lean_object* v_reuseFailAlloc_1019_; 
v_reuseFailAlloc_1019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1019_, 0, v_a_1013_);
v___x_1018_ = v_reuseFailAlloc_1019_;
goto v_reusejp_1017_;
}
v_reusejp_1017_:
{
return v___x_1018_;
}
}
}
else
{
lean_object* v_a_1021_; lean_object* v___x_1023_; uint8_t v_isShared_1024_; uint8_t v_isSharedCheck_1028_; 
v_a_1021_ = lean_ctor_get(v___x_1012_, 0);
v_isSharedCheck_1028_ = !lean_is_exclusive(v___x_1012_);
if (v_isSharedCheck_1028_ == 0)
{
v___x_1023_ = v___x_1012_;
v_isShared_1024_ = v_isSharedCheck_1028_;
goto v_resetjp_1022_;
}
else
{
lean_inc(v_a_1021_);
lean_dec(v___x_1012_);
v___x_1023_ = lean_box(0);
v_isShared_1024_ = v_isSharedCheck_1028_;
goto v_resetjp_1022_;
}
v_resetjp_1022_:
{
lean_object* v___x_1026_; 
if (v_isShared_1024_ == 0)
{
v___x_1026_ = v___x_1023_;
goto v_reusejp_1025_;
}
else
{
lean_object* v_reuseFailAlloc_1027_; 
v_reuseFailAlloc_1027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1027_, 0, v_a_1021_);
v___x_1026_ = v_reuseFailAlloc_1027_;
goto v_reusejp_1025_;
}
v_reusejp_1025_:
{
return v___x_1026_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply_spec__0_spec__0___redArg___boxed(lean_object* v_name_1029_, lean_object* v_bi_1030_, lean_object* v_type_1031_, lean_object* v_k_1032_, lean_object* v_kind_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_){
_start:
{
uint8_t v_bi_boxed_1039_; uint8_t v_kind_boxed_1040_; lean_object* v_res_1041_; 
v_bi_boxed_1039_ = lean_unbox(v_bi_1030_);
v_kind_boxed_1040_ = lean_unbox(v_kind_1033_);
v_res_1041_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply_spec__0_spec__0___redArg(v_name_1029_, v_bi_boxed_1039_, v_type_1031_, v_k_1032_, v_kind_boxed_1040_, v___y_1034_, v___y_1035_, v___y_1036_, v___y_1037_);
lean_dec(v___y_1037_);
lean_dec_ref(v___y_1036_);
lean_dec(v___y_1035_);
lean_dec_ref(v___y_1034_);
return v_res_1041_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply_spec__0___redArg(lean_object* v_name_1042_, lean_object* v_type_1043_, lean_object* v_k_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_){
_start:
{
uint8_t v___x_1050_; uint8_t v___x_1051_; lean_object* v___x_1052_; 
v___x_1050_ = 0;
v___x_1051_ = 0;
v___x_1052_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply_spec__0_spec__0___redArg(v_name_1042_, v___x_1050_, v_type_1043_, v_k_1044_, v___x_1051_, v___y_1045_, v___y_1046_, v___y_1047_, v___y_1048_);
return v___x_1052_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply_spec__0___redArg___boxed(lean_object* v_name_1053_, lean_object* v_type_1054_, lean_object* v_k_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_){
_start:
{
lean_object* v_res_1061_; 
v_res_1061_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply_spec__0___redArg(v_name_1053_, v_type_1054_, v_k_1055_, v___y_1056_, v___y_1057_, v___y_1058_, v___y_1059_);
lean_dec(v___y_1059_);
lean_dec_ref(v___y_1058_);
lean_dec(v___y_1057_);
lean_dec_ref(v___y_1056_);
return v_res_1061_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply___closed__1(void){
_start:
{
lean_object* v___x_1063_; lean_object* v___x_1064_; 
v___x_1063_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply___closed__0));
v___x_1064_ = l_Lean_stringToMessageData(v___x_1063_);
return v___x_1064_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply(lean_object* v_introThm_1073_, lean_object* v_opAs_1074_, lean_object* v_pre_1075_, lean_object* v_ss_1076_, lean_object* v_a_1077_, lean_object* v_a_1078_, lean_object* v_a_1079_, lean_object* v_a_1080_){
_start:
{
if (lean_obj_tag(v_ss_1076_) == 0)
{
lean_object* v___x_1082_; 
lean_inc(v_introThm_1073_);
v___x_1082_ = l_Lean_Meta_mkConstWithFreshMVarLevels(v_introThm_1073_, v_a_1077_, v_a_1078_, v_a_1079_, v_a_1080_);
if (lean_obj_tag(v___x_1082_) == 0)
{
lean_object* v_a_1083_; lean_object* v___x_1084_; 
v_a_1083_ = lean_ctor_get(v___x_1082_, 0);
lean_inc_n(v_a_1083_, 2);
lean_dec_ref_known(v___x_1082_, 1);
lean_inc(v_a_1080_);
lean_inc_ref(v_a_1079_);
lean_inc(v_a_1078_);
lean_inc_ref(v_a_1077_);
v___x_1084_ = lean_infer_type(v_a_1083_, v_a_1077_, v_a_1078_, v_a_1079_, v_a_1080_);
if (lean_obj_tag(v___x_1084_) == 0)
{
lean_object* v_a_1085_; uint8_t v___x_1086_; lean_object* v___x_1087_; 
v_a_1085_ = lean_ctor_get(v___x_1084_, 0);
lean_inc(v_a_1085_);
lean_dec_ref_known(v___x_1084_, 1);
v___x_1086_ = 0;
v___x_1087_ = l_Lean_Meta_forallMetaTelescope(v_a_1085_, v___x_1086_, v_a_1077_, v_a_1078_, v_a_1079_, v_a_1080_);
if (lean_obj_tag(v___x_1087_) == 0)
{
lean_object* v_a_1088_; lean_object* v___x_1090_; uint8_t v_isShared_1091_; uint8_t v_isSharedCheck_1147_; 
v_a_1088_ = lean_ctor_get(v___x_1087_, 0);
v_isSharedCheck_1147_ = !lean_is_exclusive(v___x_1087_);
if (v_isSharedCheck_1147_ == 0)
{
v___x_1090_ = v___x_1087_;
v_isShared_1091_ = v_isSharedCheck_1147_;
goto v_resetjp_1089_;
}
else
{
lean_inc(v_a_1088_);
lean_dec(v___x_1087_);
v___x_1090_ = lean_box(0);
v_isShared_1091_ = v_isSharedCheck_1147_;
goto v_resetjp_1089_;
}
v_resetjp_1089_:
{
lean_object* v_fst_1092_; lean_object* v_snd_1093_; lean_object* v___x_1095_; uint8_t v_isShared_1096_; uint8_t v_isSharedCheck_1146_; 
v_fst_1092_ = lean_ctor_get(v_a_1088_, 0);
v_snd_1093_ = lean_ctor_get(v_a_1088_, 1);
v_isSharedCheck_1146_ = !lean_is_exclusive(v_a_1088_);
if (v_isSharedCheck_1146_ == 0)
{
v___x_1095_ = v_a_1088_;
v_isShared_1096_ = v_isSharedCheck_1146_;
goto v_resetjp_1094_;
}
else
{
lean_inc(v_snd_1093_);
lean_inc(v_fst_1092_);
lean_dec(v_a_1088_);
v___x_1095_ = lean_box(0);
v_isShared_1096_ = v_isSharedCheck_1146_;
goto v_resetjp_1094_;
}
v_resetjp_1094_:
{
lean_object* v_snd_1102_; lean_object* v___x_1104_; uint8_t v_isShared_1105_; uint8_t v_isSharedCheck_1144_; 
v_snd_1102_ = lean_ctor_get(v_snd_1093_, 1);
v_isSharedCheck_1144_ = !lean_is_exclusive(v_snd_1093_);
if (v_isSharedCheck_1144_ == 0)
{
lean_object* v_unused_1145_; 
v_unused_1145_ = lean_ctor_get(v_snd_1093_, 0);
lean_dec(v_unused_1145_);
v___x_1104_ = v_snd_1093_;
v_isShared_1105_ = v_isSharedCheck_1144_;
goto v_resetjp_1103_;
}
else
{
lean_inc(v_snd_1102_);
lean_dec(v_snd_1093_);
v___x_1104_ = lean_box(0);
v_isShared_1105_ = v_isSharedCheck_1144_;
goto v_resetjp_1103_;
}
v___jp_1097_:
{
lean_object* v___x_1098_; lean_object* v___x_1100_; 
v___x_1098_ = l_Lean_mkAppN(v_a_1083_, v_fst_1092_);
lean_dec(v_fst_1092_);
if (v_isShared_1091_ == 0)
{
lean_ctor_set(v___x_1090_, 0, v___x_1098_);
v___x_1100_ = v___x_1090_;
goto v_reusejp_1099_;
}
else
{
lean_object* v_reuseFailAlloc_1101_; 
v_reuseFailAlloc_1101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1101_, 0, v___x_1098_);
v___x_1100_ = v_reuseFailAlloc_1101_;
goto v_reusejp_1099_;
}
v_reusejp_1099_:
{
return v___x_1100_;
}
}
v_resetjp_1103_:
{
lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; 
v___x_1106_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__2___closed__2));
v___x_1107_ = lean_unsigned_to_nat(2u);
v___x_1108_ = lean_mk_empty_array_with_capacity(v___x_1107_);
v___x_1109_ = lean_array_push(v___x_1108_, v_pre_1075_);
v___x_1110_ = lean_array_push(v___x_1109_, v_opAs_1074_);
v___x_1111_ = l_Lean_Meta_mkAppM(v___x_1106_, v___x_1110_, v_a_1077_, v_a_1078_, v_a_1079_, v_a_1080_);
if (lean_obj_tag(v___x_1111_) == 0)
{
lean_object* v_a_1112_; lean_object* v___x_1113_; 
v_a_1112_ = lean_ctor_get(v___x_1111_, 0);
lean_inc_n(v_a_1112_, 2);
lean_dec_ref_known(v___x_1111_, 1);
v___x_1113_ = l_Lean_Meta_isExprDefEq(v_snd_1102_, v_a_1112_, v_a_1077_, v_a_1078_, v_a_1079_, v_a_1080_);
if (lean_obj_tag(v___x_1113_) == 0)
{
lean_object* v_a_1114_; uint8_t v___x_1115_; 
v_a_1114_ = lean_ctor_get(v___x_1113_, 0);
lean_inc(v_a_1114_);
lean_dec_ref_known(v___x_1113_, 1);
v___x_1115_ = lean_unbox(v_a_1114_);
lean_dec(v_a_1114_);
if (v___x_1115_ == 0)
{
lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1119_; 
v___x_1116_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__2___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__2___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__2___closed__4);
v___x_1117_ = l_Lean_MessageData_ofName(v_introThm_1073_);
if (v_isShared_1105_ == 0)
{
lean_ctor_set_tag(v___x_1104_, 7);
lean_ctor_set(v___x_1104_, 1, v___x_1117_);
lean_ctor_set(v___x_1104_, 0, v___x_1116_);
v___x_1119_ = v___x_1104_;
goto v_reusejp_1118_;
}
else
{
lean_object* v_reuseFailAlloc_1135_; 
v_reuseFailAlloc_1135_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1135_, 0, v___x_1116_);
lean_ctor_set(v_reuseFailAlloc_1135_, 1, v___x_1117_);
v___x_1119_ = v_reuseFailAlloc_1135_;
goto v_reusejp_1118_;
}
v_reusejp_1118_:
{
lean_object* v___x_1120_; lean_object* v___x_1122_; 
v___x_1120_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply___closed__1, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply___closed__1_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply___closed__1);
if (v_isShared_1096_ == 0)
{
lean_ctor_set_tag(v___x_1095_, 7);
lean_ctor_set(v___x_1095_, 1, v___x_1120_);
lean_ctor_set(v___x_1095_, 0, v___x_1119_);
v___x_1122_ = v___x_1095_;
goto v_reusejp_1121_;
}
else
{
lean_object* v_reuseFailAlloc_1134_; 
v_reuseFailAlloc_1134_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1134_, 0, v___x_1119_);
lean_ctor_set(v_reuseFailAlloc_1134_, 1, v___x_1120_);
v___x_1122_ = v_reuseFailAlloc_1134_;
goto v_reusejp_1121_;
}
v_reusejp_1121_:
{
lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; 
v___x_1123_ = l_Lean_MessageData_ofExpr(v_a_1112_);
v___x_1124_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1124_, 0, v___x_1122_);
lean_ctor_set(v___x_1124_, 1, v___x_1123_);
v___x_1125_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__1___redArg(v___x_1124_, v_a_1077_, v_a_1078_, v_a_1079_, v_a_1080_);
if (lean_obj_tag(v___x_1125_) == 0)
{
lean_dec_ref_known(v___x_1125_, 1);
goto v___jp_1097_;
}
else
{
lean_object* v_a_1126_; lean_object* v___x_1128_; uint8_t v_isShared_1129_; uint8_t v_isSharedCheck_1133_; 
lean_dec(v_fst_1092_);
lean_del_object(v___x_1090_);
lean_dec(v_a_1083_);
v_a_1126_ = lean_ctor_get(v___x_1125_, 0);
v_isSharedCheck_1133_ = !lean_is_exclusive(v___x_1125_);
if (v_isSharedCheck_1133_ == 0)
{
v___x_1128_ = v___x_1125_;
v_isShared_1129_ = v_isSharedCheck_1133_;
goto v_resetjp_1127_;
}
else
{
lean_inc(v_a_1126_);
lean_dec(v___x_1125_);
v___x_1128_ = lean_box(0);
v_isShared_1129_ = v_isSharedCheck_1133_;
goto v_resetjp_1127_;
}
v_resetjp_1127_:
{
lean_object* v___x_1131_; 
if (v_isShared_1129_ == 0)
{
v___x_1131_ = v___x_1128_;
goto v_reusejp_1130_;
}
else
{
lean_object* v_reuseFailAlloc_1132_; 
v_reuseFailAlloc_1132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1132_, 0, v_a_1126_);
v___x_1131_ = v_reuseFailAlloc_1132_;
goto v_reusejp_1130_;
}
v_reusejp_1130_:
{
return v___x_1131_;
}
}
}
}
}
}
else
{
lean_dec(v_a_1112_);
lean_del_object(v___x_1104_);
lean_del_object(v___x_1095_);
lean_dec(v_introThm_1073_);
goto v___jp_1097_;
}
}
else
{
lean_object* v_a_1136_; lean_object* v___x_1138_; uint8_t v_isShared_1139_; uint8_t v_isSharedCheck_1143_; 
lean_dec(v_a_1112_);
lean_del_object(v___x_1104_);
lean_del_object(v___x_1095_);
lean_dec(v_fst_1092_);
lean_del_object(v___x_1090_);
lean_dec(v_a_1083_);
lean_dec(v_introThm_1073_);
v_a_1136_ = lean_ctor_get(v___x_1113_, 0);
v_isSharedCheck_1143_ = !lean_is_exclusive(v___x_1113_);
if (v_isSharedCheck_1143_ == 0)
{
v___x_1138_ = v___x_1113_;
v_isShared_1139_ = v_isSharedCheck_1143_;
goto v_resetjp_1137_;
}
else
{
lean_inc(v_a_1136_);
lean_dec(v___x_1113_);
v___x_1138_ = lean_box(0);
v_isShared_1139_ = v_isSharedCheck_1143_;
goto v_resetjp_1137_;
}
v_resetjp_1137_:
{
lean_object* v___x_1141_; 
if (v_isShared_1139_ == 0)
{
v___x_1141_ = v___x_1138_;
goto v_reusejp_1140_;
}
else
{
lean_object* v_reuseFailAlloc_1142_; 
v_reuseFailAlloc_1142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1142_, 0, v_a_1136_);
v___x_1141_ = v_reuseFailAlloc_1142_;
goto v_reusejp_1140_;
}
v_reusejp_1140_:
{
return v___x_1141_;
}
}
}
}
else
{
lean_del_object(v___x_1104_);
lean_dec(v_snd_1102_);
lean_del_object(v___x_1095_);
lean_dec(v_fst_1092_);
lean_del_object(v___x_1090_);
lean_dec(v_a_1083_);
lean_dec(v_introThm_1073_);
return v___x_1111_;
}
}
}
}
}
else
{
lean_object* v_a_1148_; lean_object* v___x_1150_; uint8_t v_isShared_1151_; uint8_t v_isSharedCheck_1155_; 
lean_dec(v_a_1083_);
lean_dec_ref(v_pre_1075_);
lean_dec_ref(v_opAs_1074_);
lean_dec(v_introThm_1073_);
v_a_1148_ = lean_ctor_get(v___x_1087_, 0);
v_isSharedCheck_1155_ = !lean_is_exclusive(v___x_1087_);
if (v_isSharedCheck_1155_ == 0)
{
v___x_1150_ = v___x_1087_;
v_isShared_1151_ = v_isSharedCheck_1155_;
goto v_resetjp_1149_;
}
else
{
lean_inc(v_a_1148_);
lean_dec(v___x_1087_);
v___x_1150_ = lean_box(0);
v_isShared_1151_ = v_isSharedCheck_1155_;
goto v_resetjp_1149_;
}
v_resetjp_1149_:
{
lean_object* v___x_1153_; 
if (v_isShared_1151_ == 0)
{
v___x_1153_ = v___x_1150_;
goto v_reusejp_1152_;
}
else
{
lean_object* v_reuseFailAlloc_1154_; 
v_reuseFailAlloc_1154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1154_, 0, v_a_1148_);
v___x_1153_ = v_reuseFailAlloc_1154_;
goto v_reusejp_1152_;
}
v_reusejp_1152_:
{
return v___x_1153_;
}
}
}
}
else
{
lean_dec(v_a_1083_);
lean_dec_ref(v_pre_1075_);
lean_dec_ref(v_opAs_1074_);
lean_dec(v_introThm_1073_);
return v___x_1084_;
}
}
else
{
lean_dec_ref(v_pre_1075_);
lean_dec_ref(v_opAs_1074_);
lean_dec(v_introThm_1073_);
return v___x_1082_;
}
}
else
{
lean_object* v___x_1156_; 
lean_inc(v_a_1080_);
lean_inc_ref(v_a_1079_);
lean_inc(v_a_1078_);
lean_inc_ref(v_a_1077_);
lean_inc_ref(v_pre_1075_);
v___x_1156_ = lean_infer_type(v_pre_1075_, v_a_1077_, v_a_1078_, v_a_1079_, v_a_1080_);
if (lean_obj_tag(v___x_1156_) == 0)
{
lean_object* v_a_1157_; lean_object* v___x_1158_; lean_object* v_s_1159_; lean_object* v___x_1160_; 
v_a_1157_ = lean_ctor_get(v___x_1156_, 0);
lean_inc(v_a_1157_);
lean_dec_ref_known(v___x_1156_, 1);
v___x_1158_ = l_Lean_instInhabitedExpr;
v_s_1159_ = l_List_getLast_x21___redArg(v___x_1158_, v_ss_1076_);
lean_inc(v_a_1080_);
lean_inc_ref(v_a_1079_);
lean_inc(v_a_1078_);
lean_inc_ref(v_a_1077_);
lean_inc(v_s_1159_);
v___x_1160_ = lean_infer_type(v_s_1159_, v_a_1077_, v_a_1078_, v_a_1079_, v_a_1080_);
if (lean_obj_tag(v___x_1160_) == 0)
{
lean_object* v_a_1161_; lean_object* v___f_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; 
v_a_1161_ = lean_ctor_get(v___x_1160_, 0);
lean_inc(v_a_1161_);
lean_dec_ref_known(v___x_1160_, 1);
lean_inc_ref(v_pre_1075_);
lean_inc(v_s_1159_);
v___f_1162_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply___lam__0___boxed), 9, 3);
lean_closure_set(v___f_1162_, 0, v_s_1159_);
lean_closure_set(v___f_1162_, 1, v_a_1157_);
lean_closure_set(v___f_1162_, 2, v_pre_1075_);
v___x_1163_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply___closed__3));
v___x_1164_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply_spec__0___redArg(v___x_1163_, v_a_1161_, v___f_1162_, v_a_1077_, v_a_1078_, v_a_1079_, v_a_1080_);
if (lean_obj_tag(v___x_1164_) == 0)
{
lean_object* v_a_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v_init_1168_; lean_object* v___x_1169_; lean_object* v_Q_1170_; lean_object* v___x_1171_; 
v_a_1165_ = lean_ctor_get(v___x_1164_, 0);
lean_inc(v_a_1165_);
lean_dec_ref_known(v___x_1164_, 1);
v___x_1166_ = lean_array_mk(v_ss_1076_);
v___x_1167_ = lean_array_pop(v___x_1166_);
v_init_1168_ = lean_array_to_list(v___x_1167_);
lean_inc(v_init_1168_);
v___x_1169_ = lean_array_mk(v_init_1168_);
lean_inc_ref(v_opAs_1074_);
v_Q_1170_ = l_Lean_mkAppN(v_opAs_1074_, v___x_1169_);
lean_dec_ref(v___x_1169_);
v___x_1171_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply(v_introThm_1073_, v_opAs_1074_, v_a_1165_, v_init_1168_, v_a_1077_, v_a_1078_, v_a_1079_, v_a_1080_);
if (lean_obj_tag(v___x_1171_) == 0)
{
lean_object* v_a_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; 
v_a_1172_ = lean_ctor_get(v___x_1171_, 0);
lean_inc(v_a_1172_);
lean_dec_ref_known(v___x_1171_, 1);
v___x_1173_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply___closed__5));
v___x_1174_ = lean_unsigned_to_nat(4u);
v___x_1175_ = lean_mk_empty_array_with_capacity(v___x_1174_);
v___x_1176_ = lean_array_push(v___x_1175_, v_s_1159_);
v___x_1177_ = lean_array_push(v___x_1176_, v_pre_1075_);
v___x_1178_ = lean_array_push(v___x_1177_, v_Q_1170_);
v___x_1179_ = lean_array_push(v___x_1178_, v_a_1172_);
v___x_1180_ = l_Lean_Meta_mkAppM(v___x_1173_, v___x_1179_, v_a_1077_, v_a_1078_, v_a_1079_, v_a_1080_);
return v___x_1180_;
}
else
{
lean_dec_ref(v_Q_1170_);
lean_dec(v_s_1159_);
lean_dec_ref(v_pre_1075_);
return v___x_1171_;
}
}
else
{
lean_dec(v_s_1159_);
lean_dec(v_ss_1076_);
lean_dec_ref(v_pre_1075_);
lean_dec_ref(v_opAs_1074_);
lean_dec(v_introThm_1073_);
return v___x_1164_;
}
}
else
{
lean_dec(v_s_1159_);
lean_dec(v_a_1157_);
lean_dec(v_ss_1076_);
lean_dec_ref(v_pre_1075_);
lean_dec_ref(v_opAs_1074_);
lean_dec(v_introThm_1073_);
return v___x_1160_;
}
}
else
{
lean_dec(v_ss_1076_);
lean_dec_ref(v_pre_1075_);
lean_dec_ref(v_opAs_1074_);
lean_dec(v_introThm_1073_);
return v___x_1156_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply___boxed(lean_object* v_introThm_1181_, lean_object* v_opAs_1182_, lean_object* v_pre_1183_, lean_object* v_ss_1184_, lean_object* v_a_1185_, lean_object* v_a_1186_, lean_object* v_a_1187_, lean_object* v_a_1188_, lean_object* v_a_1189_){
_start:
{
lean_object* v_res_1190_; 
v_res_1190_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply(v_introThm_1181_, v_opAs_1182_, v_pre_1183_, v_ss_1184_, v_a_1185_, v_a_1186_, v_a_1187_, v_a_1188_);
lean_dec(v_a_1188_);
lean_dec_ref(v_a_1187_);
lean_dec(v_a_1186_);
lean_dec_ref(v_a_1185_);
return v_res_1190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply_spec__0_spec__0(lean_object* v_00_u03b1_1191_, lean_object* v_name_1192_, uint8_t v_bi_1193_, lean_object* v_type_1194_, lean_object* v_k_1195_, uint8_t v_kind_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_){
_start:
{
lean_object* v___x_1202_; 
v___x_1202_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply_spec__0_spec__0___redArg(v_name_1192_, v_bi_1193_, v_type_1194_, v_k_1195_, v_kind_1196_, v___y_1197_, v___y_1198_, v___y_1199_, v___y_1200_);
return v___x_1202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1203_, lean_object* v_name_1204_, lean_object* v_bi_1205_, lean_object* v_type_1206_, lean_object* v_k_1207_, lean_object* v_kind_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_){
_start:
{
uint8_t v_bi_boxed_1214_; uint8_t v_kind_boxed_1215_; lean_object* v_res_1216_; 
v_bi_boxed_1214_ = lean_unbox(v_bi_1205_);
v_kind_boxed_1215_ = lean_unbox(v_kind_1208_);
v_res_1216_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply_spec__0_spec__0(v_00_u03b1_1203_, v_name_1204_, v_bi_boxed_1214_, v_type_1206_, v_k_1207_, v_kind_boxed_1215_, v___y_1209_, v___y_1210_, v___y_1211_, v___y_1212_);
lean_dec(v___y_1212_);
lean_dec_ref(v___y_1211_);
lean_dec(v___y_1210_);
lean_dec_ref(v___y_1209_);
return v_res_1216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply_spec__0(lean_object* v_00_u03b1_1217_, lean_object* v_name_1218_, lean_object* v_type_1219_, lean_object* v_k_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_){
_start:
{
lean_object* v___x_1226_; 
v___x_1226_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply_spec__0___redArg(v_name_1218_, v_type_1219_, v_k_1220_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_);
return v___x_1226_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply_spec__0___boxed(lean_object* v_00_u03b1_1227_, lean_object* v_name_1228_, lean_object* v_type_1229_, lean_object* v_k_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_){
_start:
{
lean_object* v_res_1236_; 
v_res_1236_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply_spec__0(v_00_u03b1_1227_, v_name_1228_, v_type_1229_, v_k_1230_, v___y_1231_, v___y_1232_, v___y_1233_, v___y_1234_);
lean_dec(v___y_1234_);
lean_dec_ref(v___y_1233_);
lean_dec(v___y_1232_);
lean_dec_ref(v___y_1231_);
return v_res_1236_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__1_spec__1___redArg(lean_object* v_a_1237_, lean_object* v_x_1238_){
_start:
{
if (lean_obj_tag(v_x_1238_) == 0)
{
lean_object* v___x_1239_; 
v___x_1239_ = lean_box(0);
return v___x_1239_;
}
else
{
lean_object* v_key_1240_; lean_object* v_value_1241_; lean_object* v_tail_1242_; uint8_t v___x_1243_; 
v_key_1240_ = lean_ctor_get(v_x_1238_, 0);
v_value_1241_ = lean_ctor_get(v_x_1238_, 1);
v_tail_1242_ = lean_ctor_get(v_x_1238_, 2);
v___x_1243_ = lean_name_eq(v_key_1240_, v_a_1237_);
if (v___x_1243_ == 0)
{
v_x_1238_ = v_tail_1242_;
goto _start;
}
else
{
lean_object* v___x_1245_; 
lean_inc(v_value_1241_);
v___x_1245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1245_, 0, v_value_1241_);
return v___x_1245_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__1_spec__1___redArg___boxed(lean_object* v_a_1246_, lean_object* v_x_1247_){
_start:
{
lean_object* v_res_1248_; 
v_res_1248_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__1_spec__1___redArg(v_a_1246_, v_x_1247_);
lean_dec(v_x_1247_);
lean_dec(v_a_1246_);
return v_res_1248_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__1___redArg(lean_object* v_m_1249_, lean_object* v_a_1250_){
_start:
{
lean_object* v_buckets_1251_; lean_object* v___x_1252_; uint64_t v___y_1254_; 
v_buckets_1251_ = lean_ctor_get(v_m_1249_, 1);
v___x_1252_ = lean_array_get_size(v_buckets_1251_);
if (lean_obj_tag(v_a_1250_) == 0)
{
uint64_t v___x_1268_; 
v___x_1268_ = 1723ULL;
v___y_1254_ = v___x_1268_;
goto v___jp_1253_;
}
else
{
uint64_t v_hash_1269_; 
v_hash_1269_ = lean_ctor_get_uint64(v_a_1250_, sizeof(void*)*2);
v___y_1254_ = v_hash_1269_;
goto v___jp_1253_;
}
v___jp_1253_:
{
uint64_t v___x_1255_; uint64_t v___x_1256_; uint64_t v_fold_1257_; uint64_t v___x_1258_; uint64_t v___x_1259_; uint64_t v___x_1260_; size_t v___x_1261_; size_t v___x_1262_; size_t v___x_1263_; size_t v___x_1264_; size_t v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; 
v___x_1255_ = 32ULL;
v___x_1256_ = lean_uint64_shift_right(v___y_1254_, v___x_1255_);
v_fold_1257_ = lean_uint64_xor(v___y_1254_, v___x_1256_);
v___x_1258_ = 16ULL;
v___x_1259_ = lean_uint64_shift_right(v_fold_1257_, v___x_1258_);
v___x_1260_ = lean_uint64_xor(v_fold_1257_, v___x_1259_);
v___x_1261_ = lean_uint64_to_usize(v___x_1260_);
v___x_1262_ = lean_usize_of_nat(v___x_1252_);
v___x_1263_ = ((size_t)1ULL);
v___x_1264_ = lean_usize_sub(v___x_1262_, v___x_1263_);
v___x_1265_ = lean_usize_land(v___x_1261_, v___x_1264_);
v___x_1266_ = lean_array_uget_borrowed(v_buckets_1251_, v___x_1265_);
v___x_1267_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__1_spec__1___redArg(v_a_1250_, v___x_1266_);
return v___x_1267_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__1___redArg___boxed(lean_object* v_m_1270_, lean_object* v_a_1271_){
_start:
{
lean_object* v_res_1272_; 
v_res_1272_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__1___redArg(v_m_1270_, v_a_1271_);
lean_dec(v_a_1271_);
lean_dec_ref(v_m_1270_);
return v_res_1272_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__0___redArg(size_t v_sz_1273_, size_t v_i_1274_, lean_object* v_bs_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_){
_start:
{
uint8_t v___x_1281_; 
v___x_1281_ = lean_usize_dec_lt(v_i_1274_, v_sz_1273_);
if (v___x_1281_ == 0)
{
lean_object* v___x_1282_; 
v___x_1282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1282_, 0, v_bs_1275_);
return v___x_1282_;
}
else
{
lean_object* v_v_1283_; lean_object* v___x_1284_; lean_object* v_bs_x27_1285_; lean_object* v___y_1287_; lean_object* v___x_1301_; 
v_v_1283_ = lean_array_uget(v_bs_1275_, v_i_1274_);
v___x_1284_ = lean_unsigned_to_nat(0u);
v_bs_x27_1285_ = lean_array_uset(v_bs_1275_, v_i_1274_, v___x_1284_);
lean_inc(v___y_1279_);
lean_inc_ref(v___y_1278_);
lean_inc(v___y_1277_);
lean_inc_ref(v___y_1276_);
v___x_1301_ = lean_infer_type(v_v_1283_, v___y_1276_, v___y_1277_, v___y_1278_, v___y_1279_);
if (lean_obj_tag(v___x_1301_) == 0)
{
lean_object* v_a_1302_; lean_object* v___x_1304_; uint8_t v_isShared_1305_; uint8_t v_isSharedCheck_1312_; 
v_a_1302_ = lean_ctor_get(v___x_1301_, 0);
v_isSharedCheck_1312_ = !lean_is_exclusive(v___x_1301_);
if (v_isSharedCheck_1312_ == 0)
{
v___x_1304_ = v___x_1301_;
v_isShared_1305_ = v_isSharedCheck_1312_;
goto v_resetjp_1303_;
}
else
{
lean_inc(v_a_1302_);
lean_dec(v___x_1301_);
v___x_1304_ = lean_box(0);
v_isShared_1305_ = v_isSharedCheck_1312_;
goto v_resetjp_1303_;
}
v_resetjp_1303_:
{
lean_object* v___x_1307_; 
if (v_isShared_1305_ == 0)
{
lean_ctor_set_tag(v___x_1304_, 1);
v___x_1307_ = v___x_1304_;
goto v_reusejp_1306_;
}
else
{
lean_object* v_reuseFailAlloc_1311_; 
v_reuseFailAlloc_1311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1311_, 0, v_a_1302_);
v___x_1307_ = v_reuseFailAlloc_1311_;
goto v_reusejp_1306_;
}
v_reusejp_1306_:
{
uint8_t v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; 
v___x_1308_ = 0;
v___x_1309_ = lean_box(0);
v___x_1310_ = l_Lean_Meta_mkFreshExprMVar(v___x_1307_, v___x_1308_, v___x_1309_, v___y_1276_, v___y_1277_, v___y_1278_, v___y_1279_);
v___y_1287_ = v___x_1310_;
goto v___jp_1286_;
}
}
}
else
{
v___y_1287_ = v___x_1301_;
goto v___jp_1286_;
}
v___jp_1286_:
{
if (lean_obj_tag(v___y_1287_) == 0)
{
lean_object* v_a_1288_; size_t v___x_1289_; size_t v___x_1290_; lean_object* v___x_1291_; 
v_a_1288_ = lean_ctor_get(v___y_1287_, 0);
lean_inc(v_a_1288_);
lean_dec_ref_known(v___y_1287_, 1);
v___x_1289_ = ((size_t)1ULL);
v___x_1290_ = lean_usize_add(v_i_1274_, v___x_1289_);
v___x_1291_ = lean_array_uset(v_bs_x27_1285_, v_i_1274_, v_a_1288_);
v_i_1274_ = v___x_1290_;
v_bs_1275_ = v___x_1291_;
goto _start;
}
else
{
lean_object* v_a_1293_; lean_object* v___x_1295_; uint8_t v_isShared_1296_; uint8_t v_isSharedCheck_1300_; 
lean_dec_ref(v_bs_x27_1285_);
v_a_1293_ = lean_ctor_get(v___y_1287_, 0);
v_isSharedCheck_1300_ = !lean_is_exclusive(v___y_1287_);
if (v_isSharedCheck_1300_ == 0)
{
v___x_1295_ = v___y_1287_;
v_isShared_1296_ = v_isSharedCheck_1300_;
goto v_resetjp_1294_;
}
else
{
lean_inc(v_a_1293_);
lean_dec(v___y_1287_);
v___x_1295_ = lean_box(0);
v_isShared_1296_ = v_isSharedCheck_1300_;
goto v_resetjp_1294_;
}
v_resetjp_1294_:
{
lean_object* v___x_1298_; 
if (v_isShared_1296_ == 0)
{
v___x_1298_ = v___x_1295_;
goto v_reusejp_1297_;
}
else
{
lean_object* v_reuseFailAlloc_1299_; 
v_reuseFailAlloc_1299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1299_, 0, v_a_1293_);
v___x_1298_ = v_reuseFailAlloc_1299_;
goto v_reusejp_1297_;
}
v_reusejp_1297_:
{
return v___x_1298_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__0___redArg___boxed(lean_object* v_sz_1313_, lean_object* v_i_1314_, lean_object* v_bs_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_){
_start:
{
size_t v_sz_boxed_1321_; size_t v_i_boxed_1322_; lean_object* v_res_1323_; 
v_sz_boxed_1321_ = lean_unbox_usize(v_sz_1313_);
lean_dec(v_sz_1313_);
v_i_boxed_1322_ = lean_unbox_usize(v_i_1314_);
lean_dec(v_i_1314_);
v_res_1323_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__0___redArg(v_sz_boxed_1321_, v_i_boxed_1322_, v_bs_1315_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_);
lean_dec(v___y_1319_);
lean_dec_ref(v___y_1318_);
lean_dec(v___y_1317_);
lean_dec_ref(v___y_1316_);
return v_res_1323_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__2___closed__4(void){
_start:
{
lean_object* v___x_1330_; lean_object* v___x_1331_; 
v___x_1330_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__2___closed__3));
v___x_1331_ = l_Lean_stringToMessageData(v___x_1330_);
return v___x_1331_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__2___closed__6(void){
_start:
{
lean_object* v___x_1333_; lean_object* v___x_1334_; 
v___x_1333_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__2___closed__5));
v___x_1334_ = l_Lean_stringToMessageData(v___x_1333_);
return v___x_1334_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__2___closed__7(void){
_start:
{
lean_object* v___x_1335_; lean_object* v_dummy_1336_; 
v___x_1335_ = lean_box(0);
v_dummy_1336_ = l_Lean_Expr_sort___override(v___x_1335_);
return v_dummy_1336_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__2(lean_object* v_op_1337_, lean_object* v___y_1338_, lean_object* v_a_1339_, lean_object* v_x_1340_, lean_object* v_x_1341_, lean_object* v_x_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_){
_start:
{
lean_object* v_prf_1351_; lean_object* v___y_1352_; lean_object* v___y_1353_; lean_object* v___y_1354_; lean_object* v___y_1355_; 
if (lean_obj_tag(v_x_1340_) == 5)
{
lean_object* v_fn_1372_; lean_object* v_arg_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; 
v_fn_1372_ = lean_ctor_get(v_x_1340_, 0);
lean_inc_ref(v_fn_1372_);
v_arg_1373_ = lean_ctor_get(v_x_1340_, 1);
lean_inc_ref(v_arg_1373_);
lean_dec_ref_known(v_x_1340_, 2);
v___x_1374_ = lean_array_set(v_x_1341_, v_x_1342_, v_arg_1373_);
v___x_1375_ = lean_unsigned_to_nat(1u);
v___x_1376_ = lean_nat_sub(v_x_1342_, v___x_1375_);
lean_dec(v_x_1342_);
v_x_1340_ = v_fn_1372_;
v_x_1341_ = v___x_1374_;
v_x_1342_ = v___x_1376_;
goto _start;
}
else
{
lean_object* v_head_1378_; lean_object* v_numConst_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; size_t v_sz_1382_; size_t v___x_1383_; lean_object* v___x_1384_; 
lean_dec(v_x_1342_);
v_head_1378_ = lean_ctor_get(v_op_1337_, 0);
lean_inc(v_head_1378_);
v_numConst_1379_ = lean_ctor_get(v_op_1337_, 1);
lean_inc_n(v_numConst_1379_, 2);
lean_dec_ref(v_op_1337_);
v___x_1380_ = lean_array_get_size(v_x_1341_);
v___x_1381_ = l_Array_extract___redArg(v_x_1341_, v_numConst_1379_, v___x_1380_);
v_sz_1382_ = lean_array_size(v___x_1381_);
v___x_1383_ = ((size_t)0ULL);
v___x_1384_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__0___redArg(v_sz_1382_, v___x_1383_, v___x_1381_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_);
if (lean_obj_tag(v___x_1384_) == 0)
{
lean_object* v_a_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; 
v_a_1385_ = lean_ctor_get(v___x_1384_, 0);
lean_inc(v_a_1385_);
lean_dec_ref_known(v___x_1384_, 1);
v___x_1386_ = lean_unsigned_to_nat(0u);
v___x_1387_ = l_Array_extract___redArg(v_x_1341_, v___x_1386_, v_numConst_1379_);
lean_dec_ref(v_x_1341_);
v___x_1388_ = l_Array_append___redArg(v___x_1387_, v_a_1385_);
lean_dec(v_a_1385_);
v___x_1389_ = l_Lean_mkAppN(v_x_1340_, v___x_1388_);
lean_dec_ref(v___x_1388_);
v___x_1390_ = lean_unsigned_to_nat(256u);
lean_inc_ref(v___x_1389_);
v___x_1391_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp(v___y_1338_, v___x_1389_, v___x_1390_, v___y_1343_, v___y_1344_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_);
if (lean_obj_tag(v___x_1391_) == 0)
{
lean_object* v_a_1392_; lean_object* v_fst_1393_; lean_object* v_snd_1394_; lean_object* v___x_1396_; uint8_t v_isShared_1397_; uint8_t v_isSharedCheck_1566_; 
v_a_1392_ = lean_ctor_get(v___x_1391_, 0);
lean_inc(v_a_1392_);
lean_dec_ref_known(v___x_1391_, 1);
v_fst_1393_ = lean_ctor_get(v_a_1392_, 0);
v_snd_1394_ = lean_ctor_get(v_a_1392_, 1);
v_isSharedCheck_1566_ = !lean_is_exclusive(v_a_1392_);
if (v_isSharedCheck_1566_ == 0)
{
v___x_1396_ = v_a_1392_;
v_isShared_1397_ = v_isSharedCheck_1566_;
goto v_resetjp_1395_;
}
else
{
lean_inc(v_snd_1394_);
lean_inc(v_fst_1393_);
lean_dec(v_a_1392_);
v___x_1396_ = lean_box(0);
v_isShared_1397_ = v_isSharedCheck_1566_;
goto v_resetjp_1395_;
}
v_resetjp_1395_:
{
lean_object* v___x_1398_; 
lean_inc(v___y_1348_);
lean_inc_ref(v___y_1347_);
lean_inc(v___y_1346_);
lean_inc_ref(v___y_1345_);
v___x_1398_ = lean_infer_type(v___x_1389_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_);
if (lean_obj_tag(v___x_1398_) == 0)
{
lean_object* v_a_1399_; lean_object* v___x_1400_; uint8_t v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; 
v_a_1399_ = lean_ctor_get(v___x_1398_, 0);
lean_inc(v_a_1399_);
lean_dec_ref_known(v___x_1398_, 1);
v___x_1400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1400_, 0, v_a_1399_);
v___x_1401_ = 0;
v___x_1402_ = lean_box(0);
v___x_1403_ = l_Lean_Meta_mkFreshExprMVar(v___x_1400_, v___x_1401_, v___x_1402_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_);
if (lean_obj_tag(v___x_1403_) == 0)
{
lean_object* v_a_1404_; lean_object* v___y_1406_; lean_object* v___y_1407_; lean_object* v___y_1408_; lean_object* v___y_1409_; lean_object* v___y_1410_; lean_object* v___y_1411_; lean_object* v_a_1412_; lean_object* v___y_1460_; lean_object* v_eqProof_1461_; lean_object* v___y_1462_; lean_object* v___y_1463_; lean_object* v___y_1464_; lean_object* v___y_1465_; lean_object* v___x_1493_; lean_object* v___y_1495_; lean_object* v___x_1548_; 
v_a_1404_ = lean_ctor_get(v___x_1403_, 0);
lean_inc(v_a_1404_);
lean_dec_ref_known(v___x_1403_, 1);
v___x_1493_ = l_Lean_Expr_getAppFn(v_fst_1393_);
v___x_1548_ = l_Lean_Expr_constName_x3f(v___x_1493_);
if (lean_obj_tag(v___x_1548_) == 0)
{
v___y_1495_ = v___x_1402_;
goto v___jp_1494_;
}
else
{
lean_object* v_val_1549_; 
v_val_1549_ = lean_ctor_get(v___x_1548_, 0);
lean_inc(v_val_1549_);
lean_dec_ref_known(v___x_1548_, 1);
v___y_1495_ = v_val_1549_;
goto v___jp_1494_;
}
v___jp_1405_:
{
lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; 
v___x_1413_ = lean_unsigned_to_nat(1u);
v___x_1414_ = lean_mk_empty_array_with_capacity(v___x_1413_);
lean_inc_ref(v___x_1414_);
v___x_1415_ = lean_array_push(v___x_1414_, v_a_1404_);
v___x_1416_ = l_Lean_Meta_mkAppM(v___y_1410_, v___x_1415_, v___y_1411_, v___y_1409_, v___y_1406_, v___y_1408_);
if (lean_obj_tag(v___x_1416_) == 0)
{
lean_object* v_a_1417_; lean_object* v___x_1418_; 
v_a_1417_ = lean_ctor_get(v___x_1416_, 0);
lean_inc(v_a_1417_);
lean_dec_ref_known(v___x_1416_, 1);
v___x_1418_ = l_Lean_Meta_mkCongrArg(v_a_1417_, v___y_1407_, v___y_1411_, v___y_1409_, v___y_1406_, v___y_1408_);
if (lean_obj_tag(v___x_1418_) == 0)
{
lean_object* v_a_1419_; lean_object* v___x_1420_; 
v_a_1419_ = lean_ctor_get(v___x_1418_, 0);
lean_inc(v_a_1419_);
lean_dec_ref_known(v___x_1418_, 1);
v___x_1420_ = l_Lean_Meta_mkEqSymm(v_a_1419_, v___y_1411_, v___y_1409_, v___y_1406_, v___y_1408_);
if (lean_obj_tag(v___x_1420_) == 0)
{
lean_object* v_a_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; 
v_a_1421_ = lean_ctor_get(v___x_1420_, 0);
lean_inc(v_a_1421_);
lean_dec_ref_known(v___x_1420_, 1);
v___x_1422_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__2___closed__2));
v___x_1423_ = lean_array_push(v___x_1414_, v_a_1421_);
v___x_1424_ = l_Lean_Meta_mkAppM(v___x_1422_, v___x_1423_, v___y_1411_, v___y_1409_, v___y_1406_, v___y_1408_);
if (lean_obj_tag(v___x_1424_) == 0)
{
lean_object* v_a_1425_; lean_object* v___x_1426_; 
v_a_1425_ = lean_ctor_get(v___x_1424_, 0);
lean_inc(v_a_1425_);
lean_dec_ref_known(v___x_1424_, 1);
v___x_1426_ = l_Lean_Expr_app___override(v_a_1425_, v_a_1412_);
v_prf_1351_ = v___x_1426_;
v___y_1352_ = v___y_1411_;
v___y_1353_ = v___y_1409_;
v___y_1354_ = v___y_1406_;
v___y_1355_ = v___y_1408_;
goto v___jp_1350_;
}
else
{
lean_object* v_a_1427_; lean_object* v___x_1429_; uint8_t v_isShared_1430_; uint8_t v_isSharedCheck_1434_; 
lean_dec_ref(v_a_1412_);
v_a_1427_ = lean_ctor_get(v___x_1424_, 0);
v_isSharedCheck_1434_ = !lean_is_exclusive(v___x_1424_);
if (v_isSharedCheck_1434_ == 0)
{
v___x_1429_ = v___x_1424_;
v_isShared_1430_ = v_isSharedCheck_1434_;
goto v_resetjp_1428_;
}
else
{
lean_inc(v_a_1427_);
lean_dec(v___x_1424_);
v___x_1429_ = lean_box(0);
v_isShared_1430_ = v_isSharedCheck_1434_;
goto v_resetjp_1428_;
}
v_resetjp_1428_:
{
lean_object* v___x_1432_; 
if (v_isShared_1430_ == 0)
{
v___x_1432_ = v___x_1429_;
goto v_reusejp_1431_;
}
else
{
lean_object* v_reuseFailAlloc_1433_; 
v_reuseFailAlloc_1433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1433_, 0, v_a_1427_);
v___x_1432_ = v_reuseFailAlloc_1433_;
goto v_reusejp_1431_;
}
v_reusejp_1431_:
{
return v___x_1432_;
}
}
}
}
else
{
lean_object* v_a_1435_; lean_object* v___x_1437_; uint8_t v_isShared_1438_; uint8_t v_isSharedCheck_1442_; 
lean_dec_ref(v___x_1414_);
lean_dec_ref(v_a_1412_);
v_a_1435_ = lean_ctor_get(v___x_1420_, 0);
v_isSharedCheck_1442_ = !lean_is_exclusive(v___x_1420_);
if (v_isSharedCheck_1442_ == 0)
{
v___x_1437_ = v___x_1420_;
v_isShared_1438_ = v_isSharedCheck_1442_;
goto v_resetjp_1436_;
}
else
{
lean_inc(v_a_1435_);
lean_dec(v___x_1420_);
v___x_1437_ = lean_box(0);
v_isShared_1438_ = v_isSharedCheck_1442_;
goto v_resetjp_1436_;
}
v_resetjp_1436_:
{
lean_object* v___x_1440_; 
if (v_isShared_1438_ == 0)
{
v___x_1440_ = v___x_1437_;
goto v_reusejp_1439_;
}
else
{
lean_object* v_reuseFailAlloc_1441_; 
v_reuseFailAlloc_1441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1441_, 0, v_a_1435_);
v___x_1440_ = v_reuseFailAlloc_1441_;
goto v_reusejp_1439_;
}
v_reusejp_1439_:
{
return v___x_1440_;
}
}
}
}
else
{
lean_object* v_a_1443_; lean_object* v___x_1445_; uint8_t v_isShared_1446_; uint8_t v_isSharedCheck_1450_; 
lean_dec_ref(v___x_1414_);
lean_dec_ref(v_a_1412_);
v_a_1443_ = lean_ctor_get(v___x_1418_, 0);
v_isSharedCheck_1450_ = !lean_is_exclusive(v___x_1418_);
if (v_isSharedCheck_1450_ == 0)
{
v___x_1445_ = v___x_1418_;
v_isShared_1446_ = v_isSharedCheck_1450_;
goto v_resetjp_1444_;
}
else
{
lean_inc(v_a_1443_);
lean_dec(v___x_1418_);
v___x_1445_ = lean_box(0);
v_isShared_1446_ = v_isSharedCheck_1450_;
goto v_resetjp_1444_;
}
v_resetjp_1444_:
{
lean_object* v___x_1448_; 
if (v_isShared_1446_ == 0)
{
v___x_1448_ = v___x_1445_;
goto v_reusejp_1447_;
}
else
{
lean_object* v_reuseFailAlloc_1449_; 
v_reuseFailAlloc_1449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1449_, 0, v_a_1443_);
v___x_1448_ = v_reuseFailAlloc_1449_;
goto v_reusejp_1447_;
}
v_reusejp_1447_:
{
return v___x_1448_;
}
}
}
}
else
{
lean_object* v_a_1451_; lean_object* v___x_1453_; uint8_t v_isShared_1454_; uint8_t v_isSharedCheck_1458_; 
lean_dec_ref(v___x_1414_);
lean_dec_ref(v_a_1412_);
lean_dec_ref(v___y_1407_);
v_a_1451_ = lean_ctor_get(v___x_1416_, 0);
v_isSharedCheck_1458_ = !lean_is_exclusive(v___x_1416_);
if (v_isSharedCheck_1458_ == 0)
{
v___x_1453_ = v___x_1416_;
v_isShared_1454_ = v_isSharedCheck_1458_;
goto v_resetjp_1452_;
}
else
{
lean_inc(v_a_1451_);
lean_dec(v___x_1416_);
v___x_1453_ = lean_box(0);
v_isShared_1454_ = v_isSharedCheck_1458_;
goto v_resetjp_1452_;
}
v_resetjp_1452_:
{
lean_object* v___x_1456_; 
if (v_isShared_1454_ == 0)
{
v___x_1456_ = v___x_1453_;
goto v_reusejp_1455_;
}
else
{
lean_object* v_reuseFailAlloc_1457_; 
v_reuseFailAlloc_1457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1457_, 0, v_a_1451_);
v___x_1456_ = v_reuseFailAlloc_1457_;
goto v_reusejp_1455_;
}
v_reusejp_1455_:
{
return v___x_1456_;
}
}
}
}
v___jp_1459_:
{
lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; 
v___x_1466_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__2___closed__2));
v___x_1467_ = lean_unsigned_to_nat(2u);
v___x_1468_ = lean_mk_empty_array_with_capacity(v___x_1467_);
lean_inc(v_a_1404_);
v___x_1469_ = lean_array_push(v___x_1468_, v_a_1404_);
v___x_1470_ = lean_array_push(v___x_1469_, v_fst_1393_);
v___x_1471_ = l_Lean_Meta_mkAppM(v___x_1466_, v___x_1470_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_);
if (lean_obj_tag(v___x_1471_) == 0)
{
if (lean_obj_tag(v___y_1460_) == 0)
{
lean_object* v_a_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; 
v_a_1472_ = lean_ctor_get(v___x_1471_, 0);
lean_inc(v_a_1472_);
lean_dec_ref_known(v___x_1471_, 1);
v___x_1473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1473_, 0, v_a_1472_);
v___x_1474_ = l_Lean_Meta_mkFreshExprMVar(v___x_1473_, v___x_1401_, v___x_1402_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_);
if (lean_obj_tag(v___x_1474_) == 0)
{
lean_object* v_a_1475_; 
v_a_1475_ = lean_ctor_get(v___x_1474_, 0);
lean_inc(v_a_1475_);
lean_dec_ref_known(v___x_1474_, 1);
v___y_1406_ = v___y_1464_;
v___y_1407_ = v_eqProof_1461_;
v___y_1408_ = v___y_1465_;
v___y_1409_ = v___y_1463_;
v___y_1410_ = v___x_1466_;
v___y_1411_ = v___y_1462_;
v_a_1412_ = v_a_1475_;
goto v___jp_1405_;
}
else
{
lean_object* v_a_1476_; lean_object* v___x_1478_; uint8_t v_isShared_1479_; uint8_t v_isSharedCheck_1483_; 
lean_dec_ref(v_eqProof_1461_);
lean_dec(v_a_1404_);
v_a_1476_ = lean_ctor_get(v___x_1474_, 0);
v_isSharedCheck_1483_ = !lean_is_exclusive(v___x_1474_);
if (v_isSharedCheck_1483_ == 0)
{
v___x_1478_ = v___x_1474_;
v_isShared_1479_ = v_isSharedCheck_1483_;
goto v_resetjp_1477_;
}
else
{
lean_inc(v_a_1476_);
lean_dec(v___x_1474_);
v___x_1478_ = lean_box(0);
v_isShared_1479_ = v_isSharedCheck_1483_;
goto v_resetjp_1477_;
}
v_resetjp_1477_:
{
lean_object* v___x_1481_; 
if (v_isShared_1479_ == 0)
{
v___x_1481_ = v___x_1478_;
goto v_reusejp_1480_;
}
else
{
lean_object* v_reuseFailAlloc_1482_; 
v_reuseFailAlloc_1482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1482_, 0, v_a_1476_);
v___x_1481_ = v_reuseFailAlloc_1482_;
goto v_reusejp_1480_;
}
v_reusejp_1480_:
{
return v___x_1481_;
}
}
}
}
else
{
lean_object* v_val_1484_; 
lean_dec_ref_known(v___x_1471_, 1);
v_val_1484_ = lean_ctor_get(v___y_1460_, 0);
lean_inc(v_val_1484_);
lean_dec_ref_known(v___y_1460_, 1);
v___y_1406_ = v___y_1464_;
v___y_1407_ = v_eqProof_1461_;
v___y_1408_ = v___y_1465_;
v___y_1409_ = v___y_1463_;
v___y_1410_ = v___x_1466_;
v___y_1411_ = v___y_1462_;
v_a_1412_ = v_val_1484_;
goto v___jp_1405_;
}
}
else
{
lean_object* v_a_1485_; lean_object* v___x_1487_; uint8_t v_isShared_1488_; uint8_t v_isSharedCheck_1492_; 
lean_dec_ref(v_eqProof_1461_);
lean_dec(v___y_1460_);
lean_dec(v_a_1404_);
v_a_1485_ = lean_ctor_get(v___x_1471_, 0);
v_isSharedCheck_1492_ = !lean_is_exclusive(v___x_1471_);
if (v_isSharedCheck_1492_ == 0)
{
v___x_1487_ = v___x_1471_;
v_isShared_1488_ = v_isSharedCheck_1492_;
goto v_resetjp_1486_;
}
else
{
lean_inc(v_a_1485_);
lean_dec(v___x_1471_);
v___x_1487_ = lean_box(0);
v_isShared_1488_ = v_isSharedCheck_1492_;
goto v_resetjp_1486_;
}
v_resetjp_1486_:
{
lean_object* v___x_1490_; 
if (v_isShared_1488_ == 0)
{
v___x_1490_ = v___x_1487_;
goto v_reusejp_1489_;
}
else
{
lean_object* v_reuseFailAlloc_1491_; 
v_reuseFailAlloc_1491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1491_, 0, v_a_1485_);
v___x_1490_ = v_reuseFailAlloc_1491_;
goto v_reusejp_1489_;
}
v_reusejp_1489_:
{
return v___x_1490_;
}
}
}
}
v___jp_1494_:
{
lean_object* v___x_1496_; 
v___x_1496_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__1___redArg(v_a_1339_, v___y_1495_);
lean_dec(v___y_1495_);
if (lean_obj_tag(v___x_1496_) == 0)
{
lean_dec_ref(v___x_1493_);
if (lean_obj_tag(v_snd_1394_) == 0)
{
lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1500_; 
lean_dec(v_a_1404_);
lean_dec(v_fst_1393_);
v___x_1497_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__2___closed__4, &l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__2___closed__4_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__2___closed__4);
v___x_1498_ = l_Lean_MessageData_ofName(v_head_1378_);
if (v_isShared_1397_ == 0)
{
lean_ctor_set_tag(v___x_1396_, 7);
lean_ctor_set(v___x_1396_, 1, v___x_1498_);
lean_ctor_set(v___x_1396_, 0, v___x_1497_);
v___x_1500_ = v___x_1396_;
goto v_reusejp_1499_;
}
else
{
lean_object* v_reuseFailAlloc_1512_; 
v_reuseFailAlloc_1512_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1512_, 0, v___x_1497_);
lean_ctor_set(v_reuseFailAlloc_1512_, 1, v___x_1498_);
v___x_1500_ = v_reuseFailAlloc_1512_;
goto v_reusejp_1499_;
}
v_reusejp_1499_:
{
lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v_a_1504_; lean_object* v___x_1506_; uint8_t v_isShared_1507_; uint8_t v_isSharedCheck_1511_; 
v___x_1501_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__2___closed__6, &l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__2___closed__6_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__2___closed__6);
v___x_1502_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1502_, 0, v___x_1500_);
lean_ctor_set(v___x_1502_, 1, v___x_1501_);
v___x_1503_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_go_spec__0___redArg(v___x_1502_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_);
v_a_1504_ = lean_ctor_get(v___x_1503_, 0);
v_isSharedCheck_1511_ = !lean_is_exclusive(v___x_1503_);
if (v_isSharedCheck_1511_ == 0)
{
v___x_1506_ = v___x_1503_;
v_isShared_1507_ = v_isSharedCheck_1511_;
goto v_resetjp_1505_;
}
else
{
lean_inc(v_a_1504_);
lean_dec(v___x_1503_);
v___x_1506_ = lean_box(0);
v_isShared_1507_ = v_isSharedCheck_1511_;
goto v_resetjp_1505_;
}
v_resetjp_1505_:
{
lean_object* v___x_1509_; 
if (v_isShared_1507_ == 0)
{
v___x_1509_ = v___x_1506_;
goto v_reusejp_1508_;
}
else
{
lean_object* v_reuseFailAlloc_1510_; 
v_reuseFailAlloc_1510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1510_, 0, v_a_1504_);
v___x_1509_ = v_reuseFailAlloc_1510_;
goto v_reusejp_1508_;
}
v_reusejp_1508_:
{
return v___x_1509_;
}
}
}
}
else
{
lean_object* v_val_1513_; lean_object* v___x_1514_; 
lean_del_object(v___x_1396_);
lean_dec(v_head_1378_);
v_val_1513_ = lean_ctor_get(v_snd_1394_, 0);
lean_inc(v_val_1513_);
lean_dec_ref_known(v_snd_1394_, 1);
v___x_1514_ = lean_box(0);
v___y_1460_ = v___x_1514_;
v_eqProof_1461_ = v_val_1513_;
v___y_1462_ = v___y_1345_;
v___y_1463_ = v___y_1346_;
v___y_1464_ = v___y_1347_;
v___y_1465_ = v___y_1348_;
goto v___jp_1459_;
}
}
else
{
lean_object* v_val_1515_; lean_object* v_fst_1516_; lean_object* v_snd_1517_; lean_object* v_dummy_1518_; lean_object* v_nargs_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; 
lean_del_object(v___x_1396_);
lean_dec(v_head_1378_);
v_val_1515_ = lean_ctor_get(v___x_1496_, 0);
lean_inc(v_val_1515_);
lean_dec_ref_known(v___x_1496_, 1);
v_fst_1516_ = lean_ctor_get(v_val_1515_, 0);
lean_inc(v_fst_1516_);
v_snd_1517_ = lean_ctor_get(v_val_1515_, 1);
lean_inc_n(v_snd_1517_, 2);
lean_dec(v_val_1515_);
v_dummy_1518_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__2___closed__7, &l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__2___closed__7_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__2___closed__7);
v_nargs_1519_ = l_Lean_Expr_getAppNumArgs(v_fst_1393_);
lean_inc(v_nargs_1519_);
v___x_1520_ = lean_mk_array(v_nargs_1519_, v_dummy_1518_);
v___x_1521_ = lean_unsigned_to_nat(1u);
v___x_1522_ = lean_nat_sub(v_nargs_1519_, v___x_1521_);
lean_dec(v_nargs_1519_);
lean_inc(v_fst_1393_);
v___x_1523_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_fst_1393_, v___x_1520_, v___x_1522_);
v___x_1524_ = l_Array_extract___redArg(v___x_1523_, v___x_1386_, v_snd_1517_);
v___x_1525_ = l_Lean_mkAppN(v___x_1493_, v___x_1524_);
lean_dec_ref(v___x_1524_);
v___x_1526_ = lean_array_get_size(v___x_1523_);
v___x_1527_ = l_Array_extract___redArg(v___x_1523_, v_snd_1517_, v___x_1526_);
lean_dec_ref(v___x_1523_);
v___x_1528_ = lean_array_to_list(v___x_1527_);
lean_inc(v_a_1404_);
v___x_1529_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply(v_fst_1516_, v___x_1525_, v_a_1404_, v___x_1528_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_);
if (lean_obj_tag(v___x_1529_) == 0)
{
if (lean_obj_tag(v_snd_1394_) == 0)
{
lean_object* v_a_1530_; 
lean_dec(v_a_1404_);
lean_dec(v_fst_1393_);
v_a_1530_ = lean_ctor_get(v___x_1529_, 0);
lean_inc(v_a_1530_);
lean_dec_ref_known(v___x_1529_, 1);
v_prf_1351_ = v_a_1530_;
v___y_1352_ = v___y_1345_;
v___y_1353_ = v___y_1346_;
v___y_1354_ = v___y_1347_;
v___y_1355_ = v___y_1348_;
goto v___jp_1350_;
}
else
{
lean_object* v_a_1531_; lean_object* v_val_1532_; lean_object* v___x_1534_; uint8_t v_isShared_1535_; uint8_t v_isSharedCheck_1539_; 
v_a_1531_ = lean_ctor_get(v___x_1529_, 0);
lean_inc(v_a_1531_);
lean_dec_ref_known(v___x_1529_, 1);
v_val_1532_ = lean_ctor_get(v_snd_1394_, 0);
v_isSharedCheck_1539_ = !lean_is_exclusive(v_snd_1394_);
if (v_isSharedCheck_1539_ == 0)
{
v___x_1534_ = v_snd_1394_;
v_isShared_1535_ = v_isSharedCheck_1539_;
goto v_resetjp_1533_;
}
else
{
lean_inc(v_val_1532_);
lean_dec(v_snd_1394_);
v___x_1534_ = lean_box(0);
v_isShared_1535_ = v_isSharedCheck_1539_;
goto v_resetjp_1533_;
}
v_resetjp_1533_:
{
lean_object* v___x_1537_; 
if (v_isShared_1535_ == 0)
{
lean_ctor_set(v___x_1534_, 0, v_a_1531_);
v___x_1537_ = v___x_1534_;
goto v_reusejp_1536_;
}
else
{
lean_object* v_reuseFailAlloc_1538_; 
v_reuseFailAlloc_1538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1538_, 0, v_a_1531_);
v___x_1537_ = v_reuseFailAlloc_1538_;
goto v_reusejp_1536_;
}
v_reusejp_1536_:
{
v___y_1460_ = v___x_1537_;
v_eqProof_1461_ = v_val_1532_;
v___y_1462_ = v___y_1345_;
v___y_1463_ = v___y_1346_;
v___y_1464_ = v___y_1347_;
v___y_1465_ = v___y_1348_;
goto v___jp_1459_;
}
}
}
}
else
{
lean_object* v_a_1540_; lean_object* v___x_1542_; uint8_t v_isShared_1543_; uint8_t v_isSharedCheck_1547_; 
lean_dec(v_a_1404_);
lean_dec(v_snd_1394_);
lean_dec(v_fst_1393_);
v_a_1540_ = lean_ctor_get(v___x_1529_, 0);
v_isSharedCheck_1547_ = !lean_is_exclusive(v___x_1529_);
if (v_isSharedCheck_1547_ == 0)
{
v___x_1542_ = v___x_1529_;
v_isShared_1543_ = v_isSharedCheck_1547_;
goto v_resetjp_1541_;
}
else
{
lean_inc(v_a_1540_);
lean_dec(v___x_1529_);
v___x_1542_ = lean_box(0);
v_isShared_1543_ = v_isSharedCheck_1547_;
goto v_resetjp_1541_;
}
v_resetjp_1541_:
{
lean_object* v___x_1545_; 
if (v_isShared_1543_ == 0)
{
v___x_1545_ = v___x_1542_;
goto v_reusejp_1544_;
}
else
{
lean_object* v_reuseFailAlloc_1546_; 
v_reuseFailAlloc_1546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1546_, 0, v_a_1540_);
v___x_1545_ = v_reuseFailAlloc_1546_;
goto v_reusejp_1544_;
}
v_reusejp_1544_:
{
return v___x_1545_;
}
}
}
}
}
}
else
{
lean_object* v_a_1550_; lean_object* v___x_1552_; uint8_t v_isShared_1553_; uint8_t v_isSharedCheck_1557_; 
lean_del_object(v___x_1396_);
lean_dec(v_snd_1394_);
lean_dec(v_fst_1393_);
lean_dec(v_head_1378_);
v_a_1550_ = lean_ctor_get(v___x_1403_, 0);
v_isSharedCheck_1557_ = !lean_is_exclusive(v___x_1403_);
if (v_isSharedCheck_1557_ == 0)
{
v___x_1552_ = v___x_1403_;
v_isShared_1553_ = v_isSharedCheck_1557_;
goto v_resetjp_1551_;
}
else
{
lean_inc(v_a_1550_);
lean_dec(v___x_1403_);
v___x_1552_ = lean_box(0);
v_isShared_1553_ = v_isSharedCheck_1557_;
goto v_resetjp_1551_;
}
v_resetjp_1551_:
{
lean_object* v___x_1555_; 
if (v_isShared_1553_ == 0)
{
v___x_1555_ = v___x_1552_;
goto v_reusejp_1554_;
}
else
{
lean_object* v_reuseFailAlloc_1556_; 
v_reuseFailAlloc_1556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1556_, 0, v_a_1550_);
v___x_1555_ = v_reuseFailAlloc_1556_;
goto v_reusejp_1554_;
}
v_reusejp_1554_:
{
return v___x_1555_;
}
}
}
}
else
{
lean_object* v_a_1558_; lean_object* v___x_1560_; uint8_t v_isShared_1561_; uint8_t v_isSharedCheck_1565_; 
lean_del_object(v___x_1396_);
lean_dec(v_snd_1394_);
lean_dec(v_fst_1393_);
lean_dec(v_head_1378_);
v_a_1558_ = lean_ctor_get(v___x_1398_, 0);
v_isSharedCheck_1565_ = !lean_is_exclusive(v___x_1398_);
if (v_isSharedCheck_1565_ == 0)
{
v___x_1560_ = v___x_1398_;
v_isShared_1561_ = v_isSharedCheck_1565_;
goto v_resetjp_1559_;
}
else
{
lean_inc(v_a_1558_);
lean_dec(v___x_1398_);
v___x_1560_ = lean_box(0);
v_isShared_1561_ = v_isSharedCheck_1565_;
goto v_resetjp_1559_;
}
v_resetjp_1559_:
{
lean_object* v___x_1563_; 
if (v_isShared_1561_ == 0)
{
v___x_1563_ = v___x_1560_;
goto v_reusejp_1562_;
}
else
{
lean_object* v_reuseFailAlloc_1564_; 
v_reuseFailAlloc_1564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1564_, 0, v_a_1558_);
v___x_1563_ = v_reuseFailAlloc_1564_;
goto v_reusejp_1562_;
}
v_reusejp_1562_:
{
return v___x_1563_;
}
}
}
}
}
else
{
lean_object* v_a_1567_; lean_object* v___x_1569_; uint8_t v_isShared_1570_; uint8_t v_isSharedCheck_1574_; 
lean_dec_ref(v___x_1389_);
lean_dec(v_head_1378_);
v_a_1567_ = lean_ctor_get(v___x_1391_, 0);
v_isSharedCheck_1574_ = !lean_is_exclusive(v___x_1391_);
if (v_isSharedCheck_1574_ == 0)
{
v___x_1569_ = v___x_1391_;
v_isShared_1570_ = v_isSharedCheck_1574_;
goto v_resetjp_1568_;
}
else
{
lean_inc(v_a_1567_);
lean_dec(v___x_1391_);
v___x_1569_ = lean_box(0);
v_isShared_1570_ = v_isSharedCheck_1574_;
goto v_resetjp_1568_;
}
v_resetjp_1568_:
{
lean_object* v___x_1572_; 
if (v_isShared_1570_ == 0)
{
v___x_1572_ = v___x_1569_;
goto v_reusejp_1571_;
}
else
{
lean_object* v_reuseFailAlloc_1573_; 
v_reuseFailAlloc_1573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1573_, 0, v_a_1567_);
v___x_1572_ = v_reuseFailAlloc_1573_;
goto v_reusejp_1571_;
}
v_reusejp_1571_:
{
return v___x_1572_;
}
}
}
}
else
{
lean_object* v_a_1575_; lean_object* v___x_1577_; uint8_t v_isShared_1578_; uint8_t v_isSharedCheck_1582_; 
lean_dec(v_numConst_1379_);
lean_dec(v_head_1378_);
lean_dec_ref(v_x_1341_);
lean_dec_ref(v_x_1340_);
v_a_1575_ = lean_ctor_get(v___x_1384_, 0);
v_isSharedCheck_1582_ = !lean_is_exclusive(v___x_1384_);
if (v_isSharedCheck_1582_ == 0)
{
v___x_1577_ = v___x_1384_;
v_isShared_1578_ = v_isSharedCheck_1582_;
goto v_resetjp_1576_;
}
else
{
lean_inc(v_a_1575_);
lean_dec(v___x_1384_);
v___x_1577_ = lean_box(0);
v_isShared_1578_ = v_isSharedCheck_1582_;
goto v_resetjp_1576_;
}
v_resetjp_1576_:
{
lean_object* v___x_1580_; 
if (v_isShared_1578_ == 0)
{
v___x_1580_ = v___x_1577_;
goto v_reusejp_1579_;
}
else
{
lean_object* v_reuseFailAlloc_1581_; 
v_reuseFailAlloc_1581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1581_, 0, v_a_1575_);
v___x_1580_ = v_reuseFailAlloc_1581_;
goto v_reusejp_1579_;
}
v_reusejp_1579_:
{
return v___x_1580_;
}
}
}
}
v___jp_1350_:
{
uint8_t v___x_1356_; lean_object* v___x_1357_; 
v___x_1356_ = 1;
v___x_1357_ = l_Lean_Meta_abstractMVars(v_prf_1351_, v___x_1356_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_);
if (lean_obj_tag(v___x_1357_) == 0)
{
lean_object* v_a_1358_; lean_object* v_paramNames_1359_; lean_object* v_expr_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; 
v_a_1358_ = lean_ctor_get(v___x_1357_, 0);
lean_inc(v_a_1358_);
lean_dec_ref_known(v___x_1357_, 1);
v_paramNames_1359_ = lean_ctor_get(v_a_1358_, 0);
lean_inc_ref(v_paramNames_1359_);
v_expr_1360_ = lean_ctor_get(v_a_1358_, 2);
lean_inc_ref(v_expr_1360_);
lean_dec(v_a_1358_);
v___x_1361_ = lean_array_to_list(v_paramNames_1359_);
v___x_1362_ = lean_box(0);
v___x_1363_ = l_Lean_Meta_Sym_mkBackwardRuleFromExpr(v_expr_1360_, v___x_1361_, v___x_1362_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_);
return v___x_1363_;
}
else
{
lean_object* v_a_1364_; lean_object* v___x_1366_; uint8_t v_isShared_1367_; uint8_t v_isSharedCheck_1371_; 
v_a_1364_ = lean_ctor_get(v___x_1357_, 0);
v_isSharedCheck_1371_ = !lean_is_exclusive(v___x_1357_);
if (v_isSharedCheck_1371_ == 0)
{
v___x_1366_ = v___x_1357_;
v_isShared_1367_ = v_isSharedCheck_1371_;
goto v_resetjp_1365_;
}
else
{
lean_inc(v_a_1364_);
lean_dec(v___x_1357_);
v___x_1366_ = lean_box(0);
v_isShared_1367_ = v_isSharedCheck_1371_;
goto v_resetjp_1365_;
}
v_resetjp_1365_:
{
lean_object* v___x_1369_; 
if (v_isShared_1367_ == 0)
{
v___x_1369_ = v___x_1366_;
goto v_reusejp_1368_;
}
else
{
lean_object* v_reuseFailAlloc_1370_; 
v_reuseFailAlloc_1370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1370_, 0, v_a_1364_);
v___x_1369_ = v_reuseFailAlloc_1370_;
goto v_reusejp_1368_;
}
v_reusejp_1368_:
{
return v___x_1369_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__2___boxed(lean_object* v_op_1583_, lean_object* v___y_1584_, lean_object* v_a_1585_, lean_object* v_x_1586_, lean_object* v_x_1587_, lean_object* v_x_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_){
_start:
{
lean_object* v_res_1596_; 
v_res_1596_ = l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__2(v_op_1583_, v___y_1584_, v_a_1585_, v_x_1586_, v_x_1587_, v_x_1588_, v___y_1589_, v___y_1590_, v___y_1591_, v___y_1592_, v___y_1593_, v___y_1594_);
lean_dec(v___y_1594_);
lean_dec_ref(v___y_1593_);
lean_dec(v___y_1592_);
lean_dec_ref(v___y_1591_);
lean_dec(v___y_1590_);
lean_dec_ref(v___y_1589_);
lean_dec_ref(v_a_1585_);
lean_dec_ref(v___y_1584_);
return v_res_1596_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__4(lean_object* v_as_1597_, size_t v_i_1598_, size_t v_stop_1599_, lean_object* v_b_1600_){
_start:
{
uint8_t v___x_1601_; 
v___x_1601_ = lean_usize_dec_eq(v_i_1598_, v_stop_1599_);
if (v___x_1601_ == 0)
{
lean_object* v___x_1602_; lean_object* v_rewrites_1603_; lean_object* v___x_1604_; size_t v___x_1605_; size_t v___x_1606_; 
v___x_1602_ = lean_array_uget_borrowed(v_as_1597_, v_i_1598_);
v_rewrites_1603_ = lean_ctor_get(v___x_1602_, 2);
v___x_1604_ = l_Array_append___redArg(v_b_1600_, v_rewrites_1603_);
v___x_1605_ = ((size_t)1ULL);
v___x_1606_ = lean_usize_add(v_i_1598_, v___x_1605_);
v_i_1598_ = v___x_1606_;
v_b_1600_ = v___x_1604_;
goto _start;
}
else
{
return v_b_1600_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__4___boxed(lean_object* v_as_1608_, lean_object* v_i_1609_, lean_object* v_stop_1610_, lean_object* v_b_1611_){
_start:
{
size_t v_i_boxed_1612_; size_t v_stop_boxed_1613_; lean_object* v_res_1614_; 
v_i_boxed_1612_ = lean_unbox_usize(v_i_1609_);
lean_dec(v_i_1609_);
v_stop_boxed_1613_ = lean_unbox_usize(v_stop_1610_);
lean_dec(v_stop_1610_);
v_res_1614_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__4(v_as_1608_, v_i_boxed_1612_, v_stop_boxed_1613_, v_b_1611_);
lean_dec_ref(v_as_1608_);
return v_res_1614_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__3(lean_object* v_as_1615_, size_t v_i_1616_, size_t v_stop_1617_, lean_object* v_b_1618_){
_start:
{
lean_object* v___y_1620_; uint8_t v___x_1624_; 
v___x_1624_ = lean_usize_dec_eq(v_i_1616_, v_stop_1617_);
if (v___x_1624_ == 0)
{
lean_object* v___x_1625_; lean_object* v_terminal_x3f_1626_; 
v___x_1625_ = lean_array_uget_borrowed(v_as_1615_, v_i_1616_);
v_terminal_x3f_1626_ = lean_ctor_get(v___x_1625_, 3);
if (lean_obj_tag(v_terminal_x3f_1626_) == 0)
{
lean_object* v___x_1627_; lean_object* v___x_1628_; 
v___x_1627_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_upperAdjoint___closed__3));
v___x_1628_ = l_Array_append___redArg(v_b_1618_, v___x_1627_);
v___y_1620_ = v___x_1628_;
goto v___jp_1619_;
}
else
{
lean_object* v_val_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; 
v_val_1629_ = lean_ctor_get(v_terminal_x3f_1626_, 0);
v___x_1630_ = lean_unsigned_to_nat(1u);
v___x_1631_ = lean_mk_empty_array_with_capacity(v___x_1630_);
lean_inc(v_val_1629_);
v___x_1632_ = lean_array_push(v___x_1631_, v_val_1629_);
v___x_1633_ = l_Array_append___redArg(v_b_1618_, v___x_1632_);
lean_dec_ref(v___x_1632_);
v___y_1620_ = v___x_1633_;
goto v___jp_1619_;
}
}
else
{
return v_b_1618_;
}
v___jp_1619_:
{
size_t v___x_1621_; size_t v___x_1622_; 
v___x_1621_ = ((size_t)1ULL);
v___x_1622_ = lean_usize_add(v_i_1616_, v___x_1621_);
v_i_1616_ = v___x_1622_;
v_b_1618_ = v___y_1620_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__3___boxed(lean_object* v_as_1634_, lean_object* v_i_1635_, lean_object* v_stop_1636_, lean_object* v_b_1637_){
_start:
{
size_t v_i_boxed_1638_; size_t v_stop_boxed_1639_; lean_object* v_res_1640_; 
v_i_boxed_1638_ = lean_unbox_usize(v_i_1635_);
lean_dec(v_i_1635_);
v_stop_boxed_1639_ = lean_unbox_usize(v_stop_1636_);
lean_dec(v_stop_1636_);
v_res_1640_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__3(v_as_1634_, v_i_boxed_1638_, v_stop_boxed_1639_, v_b_1637_);
lean_dec_ref(v_as_1634_);
return v_res_1640_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule___closed__0(void){
_start:
{
lean_object* v___x_1641_; size_t v___x_1642_; size_t v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; 
v___x_1641_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_upperAdjoint___closed__3));
v___x_1642_ = lean_usize_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_latticeOps___closed__5, &l_Lean_Elab_Tactic_Do_Internal_VCGen_latticeOps___closed__5_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_latticeOps___closed__5);
v___x_1643_ = ((size_t)0ULL);
v___x_1644_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_builtinLatticeOps));
v___x_1645_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__3(v___x_1644_, v___x_1643_, v___x_1642_, v___x_1641_);
return v___x_1645_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule(lean_object* v_rhs_1646_, lean_object* v_op_1647_, lean_object* v_a_1648_, lean_object* v_a_1649_, lean_object* v_a_1650_, lean_object* v_a_1651_, lean_object* v_a_1652_, lean_object* v_a_1653_){
_start:
{
lean_object* v___y_1656_; lean_object* v___y_1657_; lean_object* v___y_1658_; lean_object* v_rewrites_1676_; lean_object* v_terminal_x3f_1677_; lean_object* v___x_1678_; lean_object* v___y_1680_; lean_object* v___y_1681_; lean_object* v___y_1688_; uint8_t v___x_1694_; 
v_rewrites_1676_ = lean_ctor_get(v_op_1647_, 2);
v_terminal_x3f_1677_ = lean_ctor_get(v_op_1647_, 3);
v___x_1678_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_builtinLatticeOps));
v___x_1694_ = lean_uint8_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_latticeOps___closed__3, &l_Lean_Elab_Tactic_Do_Internal_VCGen_latticeOps___closed__3_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_latticeOps___closed__3);
if (v___x_1694_ == 0)
{
lean_inc_ref(v_rewrites_1676_);
v___y_1688_ = v_rewrites_1676_;
goto v___jp_1687_;
}
else
{
uint8_t v___x_1695_; 
v___x_1695_ = lean_uint8_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_latticeOps___closed__4, &l_Lean_Elab_Tactic_Do_Internal_VCGen_latticeOps___closed__4_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_latticeOps___closed__4);
if (v___x_1695_ == 0)
{
if (v___x_1694_ == 0)
{
lean_inc_ref(v_rewrites_1676_);
v___y_1688_ = v_rewrites_1676_;
goto v___jp_1687_;
}
else
{
size_t v___x_1696_; size_t v___x_1697_; lean_object* v___x_1698_; 
v___x_1696_ = ((size_t)0ULL);
v___x_1697_ = lean_usize_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_latticeOps___closed__5, &l_Lean_Elab_Tactic_Do_Internal_VCGen_latticeOps___closed__5_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_latticeOps___closed__5);
lean_inc_ref(v_rewrites_1676_);
v___x_1698_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__4(v___x_1678_, v___x_1696_, v___x_1697_, v_rewrites_1676_);
v___y_1688_ = v___x_1698_;
goto v___jp_1687_;
}
}
else
{
size_t v___x_1699_; size_t v___x_1700_; lean_object* v___x_1701_; 
v___x_1699_ = ((size_t)0ULL);
v___x_1700_ = lean_usize_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_latticeOps___closed__5, &l_Lean_Elab_Tactic_Do_Internal_VCGen_latticeOps___closed__5_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_latticeOps___closed__5);
lean_inc_ref(v_rewrites_1676_);
v___x_1701_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__4(v___x_1678_, v___x_1699_, v___x_1700_, v_rewrites_1676_);
v___y_1688_ = v___x_1701_;
goto v___jp_1687_;
}
}
v___jp_1655_:
{
lean_object* v___x_1659_; lean_object* v___x_1660_; 
lean_inc_ref(v___y_1657_);
v___x_1659_ = l_Array_append___redArg(v___y_1657_, v___y_1658_);
lean_dec_ref(v___y_1658_);
v___x_1660_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals(v___x_1659_, v_a_1650_, v_a_1651_, v_a_1652_, v_a_1653_);
lean_dec_ref(v___x_1659_);
if (lean_obj_tag(v___x_1660_) == 0)
{
lean_object* v_a_1661_; lean_object* v_dummy_1662_; lean_object* v_nargs_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; 
v_a_1661_ = lean_ctor_get(v___x_1660_, 0);
lean_inc(v_a_1661_);
lean_dec_ref_known(v___x_1660_, 1);
v_dummy_1662_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__2___closed__7, &l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__2___closed__7_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__2___closed__7);
v_nargs_1663_ = l_Lean_Expr_getAppNumArgs(v_rhs_1646_);
lean_inc(v_nargs_1663_);
v___x_1664_ = lean_mk_array(v_nargs_1663_, v_dummy_1662_);
v___x_1665_ = lean_unsigned_to_nat(1u);
v___x_1666_ = lean_nat_sub(v_nargs_1663_, v___x_1665_);
lean_dec(v_nargs_1663_);
v___x_1667_ = l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__2(v_op_1647_, v___y_1656_, v_a_1661_, v_rhs_1646_, v___x_1664_, v___x_1666_, v_a_1648_, v_a_1649_, v_a_1650_, v_a_1651_, v_a_1652_, v_a_1653_);
lean_dec(v_a_1661_);
lean_dec_ref(v___y_1656_);
return v___x_1667_;
}
else
{
lean_object* v_a_1668_; lean_object* v___x_1670_; uint8_t v_isShared_1671_; uint8_t v_isSharedCheck_1675_; 
lean_dec_ref(v___y_1656_);
lean_dec_ref(v_op_1647_);
lean_dec_ref(v_rhs_1646_);
v_a_1668_ = lean_ctor_get(v___x_1660_, 0);
v_isSharedCheck_1675_ = !lean_is_exclusive(v___x_1660_);
if (v_isSharedCheck_1675_ == 0)
{
v___x_1670_ = v___x_1660_;
v_isShared_1671_ = v_isSharedCheck_1675_;
goto v_resetjp_1669_;
}
else
{
lean_inc(v_a_1668_);
lean_dec(v___x_1660_);
v___x_1670_ = lean_box(0);
v_isShared_1671_ = v_isSharedCheck_1675_;
goto v_resetjp_1669_;
}
v_resetjp_1669_:
{
lean_object* v___x_1673_; 
if (v_isShared_1671_ == 0)
{
v___x_1673_ = v___x_1670_;
goto v_reusejp_1672_;
}
else
{
lean_object* v_reuseFailAlloc_1674_; 
v_reuseFailAlloc_1674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1674_, 0, v_a_1668_);
v___x_1673_ = v_reuseFailAlloc_1674_;
goto v_reusejp_1672_;
}
v_reusejp_1672_:
{
return v___x_1673_;
}
}
}
}
v___jp_1679_:
{
if (lean_obj_tag(v_terminal_x3f_1677_) == 0)
{
lean_object* v___x_1682_; 
v___x_1682_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_upperAdjoint___closed__3));
v___y_1656_ = v___y_1680_;
v___y_1657_ = v___y_1681_;
v___y_1658_ = v___x_1682_;
goto v___jp_1655_;
}
else
{
lean_object* v_val_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; 
v_val_1683_ = lean_ctor_get(v_terminal_x3f_1677_, 0);
v___x_1684_ = lean_unsigned_to_nat(1u);
v___x_1685_ = lean_mk_empty_array_with_capacity(v___x_1684_);
lean_inc(v_val_1683_);
v___x_1686_ = lean_array_push(v___x_1685_, v_val_1683_);
v___y_1656_ = v___y_1680_;
v___y_1657_ = v___y_1681_;
v___y_1658_ = v___x_1686_;
goto v___jp_1655_;
}
}
v___jp_1687_:
{
lean_object* v___x_1689_; uint8_t v___x_1690_; 
v___x_1689_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_upperAdjoint___closed__3));
v___x_1690_ = lean_uint8_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_latticeOps___closed__3, &l_Lean_Elab_Tactic_Do_Internal_VCGen_latticeOps___closed__3_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_latticeOps___closed__3);
if (v___x_1690_ == 0)
{
v___y_1680_ = v___y_1688_;
v___y_1681_ = v___x_1689_;
goto v___jp_1679_;
}
else
{
uint8_t v___x_1691_; 
v___x_1691_ = lean_uint8_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_latticeOps___closed__4, &l_Lean_Elab_Tactic_Do_Internal_VCGen_latticeOps___closed__4_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_latticeOps___closed__4);
if (v___x_1691_ == 0)
{
if (v___x_1690_ == 0)
{
v___y_1680_ = v___y_1688_;
v___y_1681_ = v___x_1689_;
goto v___jp_1679_;
}
else
{
lean_object* v___x_1692_; 
v___x_1692_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule___closed__0, &l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule___closed__0_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule___closed__0);
v___y_1680_ = v___y_1688_;
v___y_1681_ = v___x_1692_;
goto v___jp_1679_;
}
}
else
{
lean_object* v___x_1693_; 
v___x_1693_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule___closed__0, &l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule___closed__0_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule___closed__0);
v___y_1680_ = v___y_1688_;
v___y_1681_ = v___x_1693_;
goto v___jp_1679_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule___boxed(lean_object* v_rhs_1702_, lean_object* v_op_1703_, lean_object* v_a_1704_, lean_object* v_a_1705_, lean_object* v_a_1706_, lean_object* v_a_1707_, lean_object* v_a_1708_, lean_object* v_a_1709_, lean_object* v_a_1710_){
_start:
{
lean_object* v_res_1711_; 
v_res_1711_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule(v_rhs_1702_, v_op_1703_, v_a_1704_, v_a_1705_, v_a_1706_, v_a_1707_, v_a_1708_, v_a_1709_);
lean_dec(v_a_1709_);
lean_dec_ref(v_a_1708_);
lean_dec(v_a_1707_);
lean_dec_ref(v_a_1706_);
lean_dec(v_a_1705_);
lean_dec_ref(v_a_1704_);
return v_res_1711_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__0(size_t v_sz_1712_, size_t v_i_1713_, lean_object* v_bs_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_){
_start:
{
lean_object* v___x_1722_; 
v___x_1722_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__0___redArg(v_sz_1712_, v_i_1713_, v_bs_1714_, v___y_1717_, v___y_1718_, v___y_1719_, v___y_1720_);
return v___x_1722_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__0___boxed(lean_object* v_sz_1723_, lean_object* v_i_1724_, lean_object* v_bs_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_){
_start:
{
size_t v_sz_boxed_1733_; size_t v_i_boxed_1734_; lean_object* v_res_1735_; 
v_sz_boxed_1733_ = lean_unbox_usize(v_sz_1723_);
lean_dec(v_sz_1723_);
v_i_boxed_1734_ = lean_unbox_usize(v_i_1724_);
lean_dec(v_i_1724_);
v_res_1735_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__0(v_sz_boxed_1733_, v_i_boxed_1734_, v_bs_1725_, v___y_1726_, v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_);
lean_dec(v___y_1731_);
lean_dec_ref(v___y_1730_);
lean_dec(v___y_1729_);
lean_dec_ref(v___y_1728_);
lean_dec(v___y_1727_);
lean_dec_ref(v___y_1726_);
return v_res_1735_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__1(lean_object* v_00_u03b2_1736_, lean_object* v_m_1737_, lean_object* v_a_1738_){
_start:
{
lean_object* v___x_1739_; 
v___x_1739_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__1___redArg(v_m_1737_, v_a_1738_);
return v___x_1739_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__1___boxed(lean_object* v_00_u03b2_1740_, lean_object* v_m_1741_, lean_object* v_a_1742_){
_start:
{
lean_object* v_res_1743_; 
v_res_1743_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__1(v_00_u03b2_1740_, v_m_1741_, v_a_1742_);
lean_dec(v_a_1742_);
lean_dec_ref(v_m_1741_);
return v_res_1743_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__1_spec__1(lean_object* v_00_u03b2_1744_, lean_object* v_a_1745_, lean_object* v_x_1746_){
_start:
{
lean_object* v___x_1747_; 
v___x_1747_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__1_spec__1___redArg(v_a_1745_, v_x_1746_);
return v___x_1747_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__1_spec__1___boxed(lean_object* v_00_u03b2_1748_, lean_object* v_a_1749_, lean_object* v_x_1750_){
_start:
{
lean_object* v_res_1751_; 
v_res_1751_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__1_spec__1(v_00_u03b2_1748_, v_a_1749_, v_x_1750_);
lean_dec(v_x_1750_);
lean_dec(v_a_1749_);
return v_res_1751_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_Apply(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_Do_Order_Heyting(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProc(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_Rewrite(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_AppBuilder(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_AbstractMVars(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Sym_Apply(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_Do_Order_Heyting(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProc(builtin);
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
l_Lean_Elab_Tactic_Do_Internal_VCGen_latticeOps = _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_latticeOps();
lean_mark_persistent(l_Lean_Elab_Tactic_Do_Internal_VCGen_latticeOps);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Sym_Apply(uint8_t builtin);
lean_object* initialize_Std_Internal_Do_Order_Heyting(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProc(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_Rewrite(uint8_t builtin);
lean_object* initialize_Lean_Meta_AppBuilder(uint8_t builtin);
lean_object* initialize_Lean_Meta_AbstractMVars(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Sym_Apply(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal_Do_Order_Heyting(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProc(builtin);
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
res = runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp(builtin);
}
#ifdef __cplusplus
}
#endif
