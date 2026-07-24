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
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_mkTheoremFromDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_Theorems_insert(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_dischargeNone___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_SimpM_run_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_mkEqTrans(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable_spec__0_spec__1_spec__2_spec__4___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable_spec__0_spec__1_spec__2_spec__4___redArg___closed__0;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable_spec__0_spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable_spec__0_spec__1___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable___closed__0;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable___closed__1;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable___closed__2;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable_spec__0_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals___closed__0;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_go___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_go___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_go_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_go_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 107, .m_capacity = 107, .m_length = 106, .m_data = "lattice saturation did not terminate; a registered `@[frameproc]` rewrite set is likely non-terminating on"};
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
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "frame operator `"};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__2___closed__3 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__2___closed__3_value;
static lean_once_cell_t l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__2___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__2___closed__4;
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__2___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 94, .m_capacity = 94, .m_length = 93, .m_data = "` neither reduces nor has a registered terminal; its lattice split rule would be the identity"};
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable_spec__0_spec__2___redArg(lean_object* v_a_179_, lean_object* v_b_180_, lean_object* v_x_181_){
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
v___x_189_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable_spec__0_spec__2___redArg(v_a_179_, v_b_180_, v_tail_184_);
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
static uint64_t _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable_spec__0_spec__1_spec__2_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_197_; uint64_t v___x_198_; 
v___x_197_ = lean_unsigned_to_nat(1723u);
v___x_198_ = lean_uint64_of_nat(v___x_197_);
return v___x_198_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable_spec__0_spec__1_spec__2_spec__4___redArg(lean_object* v_x_199_, lean_object* v_x_200_){
_start:
{
if (lean_obj_tag(v_x_200_) == 0)
{
return v_x_199_;
}
else
{
lean_object* v_key_201_; lean_object* v_value_202_; lean_object* v_tail_203_; lean_object* v___x_205_; uint8_t v_isShared_206_; uint8_t v_isSharedCheck_229_; 
v_key_201_ = lean_ctor_get(v_x_200_, 0);
v_value_202_ = lean_ctor_get(v_x_200_, 1);
v_tail_203_ = lean_ctor_get(v_x_200_, 2);
v_isSharedCheck_229_ = !lean_is_exclusive(v_x_200_);
if (v_isSharedCheck_229_ == 0)
{
v___x_205_ = v_x_200_;
v_isShared_206_ = v_isSharedCheck_229_;
goto v_resetjp_204_;
}
else
{
lean_inc(v_tail_203_);
lean_inc(v_value_202_);
lean_inc(v_key_201_);
lean_dec(v_x_200_);
v___x_205_ = lean_box(0);
v_isShared_206_ = v_isSharedCheck_229_;
goto v_resetjp_204_;
}
v_resetjp_204_:
{
lean_object* v___x_207_; uint64_t v___y_209_; 
v___x_207_ = lean_array_get_size(v_x_199_);
if (lean_obj_tag(v_key_201_) == 0)
{
uint64_t v___x_227_; 
v___x_227_ = lean_uint64_once(&l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable_spec__0_spec__1_spec__2_spec__4___redArg___closed__0, &l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable_spec__0_spec__1_spec__2_spec__4___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable_spec__0_spec__1_spec__2_spec__4___redArg___closed__0);
v___y_209_ = v___x_227_;
goto v___jp_208_;
}
else
{
uint64_t v_hash_228_; 
v_hash_228_ = lean_ctor_get_uint64(v_key_201_, sizeof(void*)*2);
v___y_209_ = v_hash_228_;
goto v___jp_208_;
}
v___jp_208_:
{
uint64_t v___x_210_; uint64_t v___x_211_; uint64_t v_fold_212_; uint64_t v___x_213_; uint64_t v___x_214_; uint64_t v___x_215_; size_t v___x_216_; size_t v___x_217_; size_t v___x_218_; size_t v___x_219_; size_t v___x_220_; lean_object* v___x_221_; lean_object* v___x_223_; 
v___x_210_ = 32ULL;
v___x_211_ = lean_uint64_shift_right(v___y_209_, v___x_210_);
v_fold_212_ = lean_uint64_xor(v___y_209_, v___x_211_);
v___x_213_ = 16ULL;
v___x_214_ = lean_uint64_shift_right(v_fold_212_, v___x_213_);
v___x_215_ = lean_uint64_xor(v_fold_212_, v___x_214_);
v___x_216_ = lean_uint64_to_usize(v___x_215_);
v___x_217_ = lean_usize_of_nat(v___x_207_);
v___x_218_ = ((size_t)1ULL);
v___x_219_ = lean_usize_sub(v___x_217_, v___x_218_);
v___x_220_ = lean_usize_land(v___x_216_, v___x_219_);
v___x_221_ = lean_array_uget_borrowed(v_x_199_, v___x_220_);
lean_inc(v___x_221_);
if (v_isShared_206_ == 0)
{
lean_ctor_set(v___x_205_, 2, v___x_221_);
v___x_223_ = v___x_205_;
goto v_reusejp_222_;
}
else
{
lean_object* v_reuseFailAlloc_226_; 
v_reuseFailAlloc_226_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_226_, 0, v_key_201_);
lean_ctor_set(v_reuseFailAlloc_226_, 1, v_value_202_);
lean_ctor_set(v_reuseFailAlloc_226_, 2, v___x_221_);
v___x_223_ = v_reuseFailAlloc_226_;
goto v_reusejp_222_;
}
v_reusejp_222_:
{
lean_object* v___x_224_; 
v___x_224_ = lean_array_uset(v_x_199_, v___x_220_, v___x_223_);
v_x_199_ = v___x_224_;
v_x_200_ = v_tail_203_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable_spec__0_spec__1_spec__2___redArg(lean_object* v_i_230_, lean_object* v_source_231_, lean_object* v_target_232_){
_start:
{
lean_object* v___x_233_; uint8_t v___x_234_; 
v___x_233_ = lean_array_get_size(v_source_231_);
v___x_234_ = lean_nat_dec_lt(v_i_230_, v___x_233_);
if (v___x_234_ == 0)
{
lean_dec_ref(v_source_231_);
lean_dec(v_i_230_);
return v_target_232_;
}
else
{
lean_object* v_es_235_; lean_object* v___x_236_; lean_object* v_source_237_; lean_object* v_target_238_; lean_object* v___x_239_; lean_object* v___x_240_; 
v_es_235_ = lean_array_fget(v_source_231_, v_i_230_);
v___x_236_ = lean_box(0);
v_source_237_ = lean_array_fset(v_source_231_, v_i_230_, v___x_236_);
v_target_238_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable_spec__0_spec__1_spec__2_spec__4___redArg(v_target_232_, v_es_235_);
v___x_239_ = lean_unsigned_to_nat(1u);
v___x_240_ = lean_nat_add(v_i_230_, v___x_239_);
lean_dec(v_i_230_);
v_i_230_ = v___x_240_;
v_source_231_ = v_source_237_;
v_target_232_ = v_target_238_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable_spec__0_spec__1___redArg(lean_object* v_data_242_){
_start:
{
lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v_nbuckets_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; 
v___x_243_ = lean_array_get_size(v_data_242_);
v___x_244_ = lean_unsigned_to_nat(2u);
v_nbuckets_245_ = lean_nat_mul(v___x_243_, v___x_244_);
v___x_246_ = lean_unsigned_to_nat(0u);
v___x_247_ = lean_box(0);
v___x_248_ = lean_mk_array(v_nbuckets_245_, v___x_247_);
v___x_249_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable_spec__0_spec__1_spec__2___redArg(v___x_246_, v_data_242_, v___x_248_);
return v___x_249_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable_spec__0_spec__0___redArg(lean_object* v_a_250_, lean_object* v_x_251_){
_start:
{
if (lean_obj_tag(v_x_251_) == 0)
{
uint8_t v___x_252_; 
v___x_252_ = 0;
return v___x_252_;
}
else
{
lean_object* v_key_253_; lean_object* v_tail_254_; uint8_t v___x_255_; 
v_key_253_ = lean_ctor_get(v_x_251_, 0);
v_tail_254_ = lean_ctor_get(v_x_251_, 2);
v___x_255_ = lean_name_eq(v_key_253_, v_a_250_);
if (v___x_255_ == 0)
{
v_x_251_ = v_tail_254_;
goto _start;
}
else
{
return v___x_255_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable_spec__0_spec__0___redArg___boxed(lean_object* v_a_257_, lean_object* v_x_258_){
_start:
{
uint8_t v_res_259_; lean_object* v_r_260_; 
v_res_259_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable_spec__0_spec__0___redArg(v_a_257_, v_x_258_);
lean_dec(v_x_258_);
lean_dec(v_a_257_);
v_r_260_ = lean_box(v_res_259_);
return v_r_260_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable_spec__0___redArg(lean_object* v_m_261_, lean_object* v_a_262_, lean_object* v_b_263_){
_start:
{
lean_object* v_size_264_; lean_object* v_buckets_265_; lean_object* v___x_267_; uint8_t v_isShared_268_; uint8_t v_isSharedCheck_311_; 
v_size_264_ = lean_ctor_get(v_m_261_, 0);
v_buckets_265_ = lean_ctor_get(v_m_261_, 1);
v_isSharedCheck_311_ = !lean_is_exclusive(v_m_261_);
if (v_isSharedCheck_311_ == 0)
{
v___x_267_ = v_m_261_;
v_isShared_268_ = v_isSharedCheck_311_;
goto v_resetjp_266_;
}
else
{
lean_inc(v_buckets_265_);
lean_inc(v_size_264_);
lean_dec(v_m_261_);
v___x_267_ = lean_box(0);
v_isShared_268_ = v_isSharedCheck_311_;
goto v_resetjp_266_;
}
v_resetjp_266_:
{
lean_object* v___x_269_; uint64_t v___y_271_; 
v___x_269_ = lean_array_get_size(v_buckets_265_);
if (lean_obj_tag(v_a_262_) == 0)
{
uint64_t v___x_309_; 
v___x_309_ = lean_uint64_once(&l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable_spec__0_spec__1_spec__2_spec__4___redArg___closed__0, &l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable_spec__0_spec__1_spec__2_spec__4___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable_spec__0_spec__1_spec__2_spec__4___redArg___closed__0);
v___y_271_ = v___x_309_;
goto v___jp_270_;
}
else
{
uint64_t v_hash_310_; 
v_hash_310_ = lean_ctor_get_uint64(v_a_262_, sizeof(void*)*2);
v___y_271_ = v_hash_310_;
goto v___jp_270_;
}
v___jp_270_:
{
uint64_t v___x_272_; uint64_t v___x_273_; uint64_t v_fold_274_; uint64_t v___x_275_; uint64_t v___x_276_; uint64_t v___x_277_; size_t v___x_278_; size_t v___x_279_; size_t v___x_280_; size_t v___x_281_; size_t v___x_282_; lean_object* v_bkt_283_; uint8_t v___x_284_; 
v___x_272_ = 32ULL;
v___x_273_ = lean_uint64_shift_right(v___y_271_, v___x_272_);
v_fold_274_ = lean_uint64_xor(v___y_271_, v___x_273_);
v___x_275_ = 16ULL;
v___x_276_ = lean_uint64_shift_right(v_fold_274_, v___x_275_);
v___x_277_ = lean_uint64_xor(v_fold_274_, v___x_276_);
v___x_278_ = lean_uint64_to_usize(v___x_277_);
v___x_279_ = lean_usize_of_nat(v___x_269_);
v___x_280_ = ((size_t)1ULL);
v___x_281_ = lean_usize_sub(v___x_279_, v___x_280_);
v___x_282_ = lean_usize_land(v___x_278_, v___x_281_);
v_bkt_283_ = lean_array_uget_borrowed(v_buckets_265_, v___x_282_);
v___x_284_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable_spec__0_spec__0___redArg(v_a_262_, v_bkt_283_);
if (v___x_284_ == 0)
{
lean_object* v___x_285_; lean_object* v_size_x27_286_; lean_object* v___x_287_; lean_object* v_buckets_x27_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; uint8_t v___x_294_; 
v___x_285_ = lean_unsigned_to_nat(1u);
v_size_x27_286_ = lean_nat_add(v_size_264_, v___x_285_);
lean_dec(v_size_264_);
lean_inc(v_bkt_283_);
v___x_287_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_287_, 0, v_a_262_);
lean_ctor_set(v___x_287_, 1, v_b_263_);
lean_ctor_set(v___x_287_, 2, v_bkt_283_);
v_buckets_x27_288_ = lean_array_uset(v_buckets_265_, v___x_282_, v___x_287_);
v___x_289_ = lean_unsigned_to_nat(4u);
v___x_290_ = lean_nat_mul(v_size_x27_286_, v___x_289_);
v___x_291_ = lean_unsigned_to_nat(3u);
v___x_292_ = lean_nat_div(v___x_290_, v___x_291_);
lean_dec(v___x_290_);
v___x_293_ = lean_array_get_size(v_buckets_x27_288_);
v___x_294_ = lean_nat_dec_le(v___x_292_, v___x_293_);
lean_dec(v___x_292_);
if (v___x_294_ == 0)
{
lean_object* v_val_295_; lean_object* v___x_297_; 
v_val_295_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable_spec__0_spec__1___redArg(v_buckets_x27_288_);
if (v_isShared_268_ == 0)
{
lean_ctor_set(v___x_267_, 1, v_val_295_);
lean_ctor_set(v___x_267_, 0, v_size_x27_286_);
v___x_297_ = v___x_267_;
goto v_reusejp_296_;
}
else
{
lean_object* v_reuseFailAlloc_298_; 
v_reuseFailAlloc_298_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_298_, 0, v_size_x27_286_);
lean_ctor_set(v_reuseFailAlloc_298_, 1, v_val_295_);
v___x_297_ = v_reuseFailAlloc_298_;
goto v_reusejp_296_;
}
v_reusejp_296_:
{
return v___x_297_;
}
}
else
{
lean_object* v___x_300_; 
if (v_isShared_268_ == 0)
{
lean_ctor_set(v___x_267_, 1, v_buckets_x27_288_);
lean_ctor_set(v___x_267_, 0, v_size_x27_286_);
v___x_300_ = v___x_267_;
goto v_reusejp_299_;
}
else
{
lean_object* v_reuseFailAlloc_301_; 
v_reuseFailAlloc_301_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_301_, 0, v_size_x27_286_);
lean_ctor_set(v_reuseFailAlloc_301_, 1, v_buckets_x27_288_);
v___x_300_ = v_reuseFailAlloc_301_;
goto v_reusejp_299_;
}
v_reusejp_299_:
{
return v___x_300_;
}
}
}
else
{
lean_object* v___x_302_; lean_object* v_buckets_x27_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_307_; 
lean_inc(v_bkt_283_);
v___x_302_ = lean_box(0);
v_buckets_x27_303_ = lean_array_uset(v_buckets_265_, v___x_282_, v___x_302_);
v___x_304_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable_spec__0_spec__2___redArg(v_a_262_, v_b_263_, v_bkt_283_);
v___x_305_ = lean_array_uset(v_buckets_x27_303_, v___x_282_, v___x_304_);
if (v_isShared_268_ == 0)
{
lean_ctor_set(v___x_267_, 1, v___x_305_);
v___x_307_ = v___x_267_;
goto v_reusejp_306_;
}
else
{
lean_object* v_reuseFailAlloc_308_; 
v_reuseFailAlloc_308_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_308_, 0, v_size_264_);
lean_ctor_set(v_reuseFailAlloc_308_, 1, v___x_305_);
v___x_307_ = v_reuseFailAlloc_308_;
goto v_reusejp_306_;
}
v_reusejp_306_:
{
return v___x_307_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable_spec__1(lean_object* v_as_312_, size_t v_i_313_, size_t v_stop_314_, lean_object* v_b_315_){
_start:
{
uint8_t v___x_316_; 
v___x_316_ = lean_usize_dec_eq(v_i_313_, v_stop_314_);
if (v___x_316_ == 0)
{
lean_object* v___x_317_; lean_object* v_head_318_; lean_object* v___x_319_; size_t v___x_320_; size_t v___x_321_; 
v___x_317_ = lean_array_uget_borrowed(v_as_312_, v_i_313_);
v_head_318_ = lean_ctor_get(v___x_317_, 0);
lean_inc(v___x_317_);
lean_inc(v_head_318_);
v___x_319_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable_spec__0___redArg(v_b_315_, v_head_318_, v___x_317_);
v___x_320_ = ((size_t)1ULL);
v___x_321_ = lean_usize_add(v_i_313_, v___x_320_);
v_i_313_ = v___x_321_;
v_b_315_ = v___x_319_;
goto _start;
}
else
{
return v_b_315_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable_spec__1___boxed(lean_object* v_as_323_, lean_object* v_i_324_, lean_object* v_stop_325_, lean_object* v_b_326_){
_start:
{
size_t v_i_boxed_327_; size_t v_stop_boxed_328_; lean_object* v_res_329_; 
v_i_boxed_327_ = lean_unbox_usize(v_i_324_);
lean_dec(v_i_324_);
v_stop_boxed_328_ = lean_unbox_usize(v_stop_325_);
lean_dec(v_stop_325_);
v_res_329_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable_spec__1(v_as_323_, v_i_boxed_327_, v_stop_boxed_328_, v_b_326_);
lean_dec_ref(v_as_323_);
return v_res_329_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable___closed__0(void){
_start:
{
lean_object* v___x_330_; lean_object* v___x_331_; 
v___x_330_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_builtinLatticeOps));
v___x_331_ = lean_array_get_size(v___x_330_);
return v___x_331_;
}
}
static uint8_t _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable___closed__1(void){
_start:
{
lean_object* v___x_332_; lean_object* v___x_333_; uint8_t v___x_334_; 
v___x_332_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable___closed__0, &l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable___closed__0_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable___closed__0);
v___x_333_ = lean_unsigned_to_nat(0u);
v___x_334_ = lean_nat_dec_lt(v___x_333_, v___x_332_);
return v___x_334_;
}
}
static uint8_t _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable___closed__2(void){
_start:
{
lean_object* v___x_335_; uint8_t v___x_336_; 
v___x_335_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable___closed__0, &l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable___closed__0_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable___closed__0);
v___x_336_ = lean_nat_dec_le(v___x_335_, v___x_335_);
return v___x_336_;
}
}
static size_t _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable___closed__3(void){
_start:
{
lean_object* v___x_337_; size_t v___x_338_; 
v___x_337_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable___closed__0, &l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable___closed__0_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable___closed__0);
v___x_338_ = lean_usize_of_nat(v___x_337_);
return v___x_338_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable(lean_object* v_frameSplits_339_){
_start:
{
lean_object* v___x_340_; uint8_t v___x_341_; 
v___x_340_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_builtinLatticeOps));
v___x_341_ = lean_uint8_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable___closed__1, &l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable___closed__1_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable___closed__1);
if (v___x_341_ == 0)
{
return v_frameSplits_339_;
}
else
{
uint8_t v___x_342_; 
v___x_342_ = lean_uint8_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable___closed__2, &l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable___closed__2_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable___closed__2);
if (v___x_342_ == 0)
{
if (v___x_341_ == 0)
{
return v_frameSplits_339_;
}
else
{
size_t v___x_343_; size_t v___x_344_; lean_object* v___x_345_; 
v___x_343_ = ((size_t)0ULL);
v___x_344_ = lean_usize_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable___closed__3, &l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable___closed__3_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable___closed__3);
v___x_345_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable_spec__1(v___x_340_, v___x_343_, v___x_344_, v_frameSplits_339_);
return v___x_345_;
}
}
else
{
size_t v___x_346_; size_t v___x_347_; lean_object* v___x_348_; 
v___x_346_ = ((size_t)0ULL);
v___x_347_ = lean_usize_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable___closed__3, &l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable___closed__3_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable___closed__3);
v___x_348_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable_spec__1(v___x_340_, v___x_346_, v___x_347_, v_frameSplits_339_);
return v___x_348_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable_spec__0(lean_object* v_00_u03b2_349_, lean_object* v_m_350_, lean_object* v_a_351_, lean_object* v_b_352_){
_start:
{
lean_object* v___x_353_; 
v___x_353_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable_spec__0___redArg(v_m_350_, v_a_351_, v_b_352_);
return v___x_353_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable_spec__0_spec__0(lean_object* v_00_u03b2_354_, lean_object* v_a_355_, lean_object* v_x_356_){
_start:
{
uint8_t v___x_357_; 
v___x_357_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable_spec__0_spec__0___redArg(v_a_355_, v_x_356_);
return v___x_357_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable_spec__0_spec__0___boxed(lean_object* v_00_u03b2_358_, lean_object* v_a_359_, lean_object* v_x_360_){
_start:
{
uint8_t v_res_361_; lean_object* v_r_362_; 
v_res_361_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable_spec__0_spec__0(v_00_u03b2_358_, v_a_359_, v_x_360_);
lean_dec(v_x_360_);
lean_dec(v_a_359_);
v_r_362_ = lean_box(v_res_361_);
return v_r_362_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable_spec__0_spec__1(lean_object* v_00_u03b2_363_, lean_object* v_data_364_){
_start:
{
lean_object* v___x_365_; 
v___x_365_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable_spec__0_spec__1___redArg(v_data_364_);
return v___x_365_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable_spec__0_spec__2(lean_object* v_00_u03b2_366_, lean_object* v_a_367_, lean_object* v_b_368_, lean_object* v_x_369_){
_start:
{
lean_object* v___x_370_; 
v___x_370_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable_spec__0_spec__2___redArg(v_a_367_, v_b_368_, v_x_369_);
return v___x_370_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_371_, lean_object* v_i_372_, lean_object* v_source_373_, lean_object* v_target_374_){
_start:
{
lean_object* v___x_375_; 
v___x_375_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable_spec__0_spec__1_spec__2___redArg(v_i_372_, v_source_373_, v_target_374_);
return v___x_375_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable_spec__0_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_376_, lean_object* v_x_377_, lean_object* v_x_378_){
_start:
{
lean_object* v___x_379_; 
v___x_379_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable_spec__0_spec__1_spec__2_spec__4___redArg(v_x_377_, v_x_378_);
return v___x_379_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__0___redArg(lean_object* v_e_380_, lean_object* v___y_381_){
_start:
{
uint8_t v___x_383_; 
v___x_383_ = l_Lean_Expr_hasMVar(v_e_380_);
if (v___x_383_ == 0)
{
lean_object* v___x_384_; 
v___x_384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_384_, 0, v_e_380_);
return v___x_384_;
}
else
{
lean_object* v___x_385_; lean_object* v_mctx_386_; lean_object* v___x_387_; lean_object* v_fst_388_; lean_object* v_snd_389_; lean_object* v___x_390_; lean_object* v_cache_391_; lean_object* v_zetaDeltaFVarIds_392_; lean_object* v_postponed_393_; lean_object* v_diag_394_; lean_object* v___x_396_; uint8_t v_isShared_397_; uint8_t v_isSharedCheck_403_; 
v___x_385_ = lean_st_ref_get(v___y_381_);
v_mctx_386_ = lean_ctor_get(v___x_385_, 0);
lean_inc_ref(v_mctx_386_);
lean_dec(v___x_385_);
v___x_387_ = l_Lean_instantiateMVarsCore(v_mctx_386_, v_e_380_);
v_fst_388_ = lean_ctor_get(v___x_387_, 0);
lean_inc(v_fst_388_);
v_snd_389_ = lean_ctor_get(v___x_387_, 1);
lean_inc(v_snd_389_);
lean_dec_ref(v___x_387_);
v___x_390_ = lean_st_ref_take(v___y_381_);
v_cache_391_ = lean_ctor_get(v___x_390_, 1);
v_zetaDeltaFVarIds_392_ = lean_ctor_get(v___x_390_, 2);
v_postponed_393_ = lean_ctor_get(v___x_390_, 3);
v_diag_394_ = lean_ctor_get(v___x_390_, 4);
v_isSharedCheck_403_ = !lean_is_exclusive(v___x_390_);
if (v_isSharedCheck_403_ == 0)
{
lean_object* v_unused_404_; 
v_unused_404_ = lean_ctor_get(v___x_390_, 0);
lean_dec(v_unused_404_);
v___x_396_ = v___x_390_;
v_isShared_397_ = v_isSharedCheck_403_;
goto v_resetjp_395_;
}
else
{
lean_inc(v_diag_394_);
lean_inc(v_postponed_393_);
lean_inc(v_zetaDeltaFVarIds_392_);
lean_inc(v_cache_391_);
lean_dec(v___x_390_);
v___x_396_ = lean_box(0);
v_isShared_397_ = v_isSharedCheck_403_;
goto v_resetjp_395_;
}
v_resetjp_395_:
{
lean_object* v___x_399_; 
if (v_isShared_397_ == 0)
{
lean_ctor_set(v___x_396_, 0, v_snd_389_);
v___x_399_ = v___x_396_;
goto v_reusejp_398_;
}
else
{
lean_object* v_reuseFailAlloc_402_; 
v_reuseFailAlloc_402_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_402_, 0, v_snd_389_);
lean_ctor_set(v_reuseFailAlloc_402_, 1, v_cache_391_);
lean_ctor_set(v_reuseFailAlloc_402_, 2, v_zetaDeltaFVarIds_392_);
lean_ctor_set(v_reuseFailAlloc_402_, 3, v_postponed_393_);
lean_ctor_set(v_reuseFailAlloc_402_, 4, v_diag_394_);
v___x_399_ = v_reuseFailAlloc_402_;
goto v_reusejp_398_;
}
v_reusejp_398_:
{
lean_object* v___x_400_; lean_object* v___x_401_; 
v___x_400_ = lean_st_ref_set(v___y_381_, v___x_399_);
v___x_401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_401_, 0, v_fst_388_);
return v___x_401_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__0___redArg___boxed(lean_object* v_e_405_, lean_object* v___y_406_, lean_object* v___y_407_){
_start:
{
lean_object* v_res_408_; 
v_res_408_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__0___redArg(v_e_405_, v___y_406_);
lean_dec(v___y_406_);
return v_res_408_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__0(lean_object* v_e_409_, lean_object* v___y_410_, lean_object* v___y_411_, lean_object* v___y_412_, lean_object* v___y_413_){
_start:
{
lean_object* v___x_415_; 
v___x_415_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__0___redArg(v_e_409_, v___y_411_);
return v___x_415_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__0___boxed(lean_object* v_e_416_, lean_object* v___y_417_, lean_object* v___y_418_, lean_object* v___y_419_, lean_object* v___y_420_, lean_object* v___y_421_){
_start:
{
lean_object* v_res_422_; 
v_res_422_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__0(v_e_416_, v___y_417_, v___y_418_, v___y_419_, v___y_420_);
lean_dec(v___y_420_);
lean_dec_ref(v___y_419_);
lean_dec(v___y_418_);
lean_dec_ref(v___y_417_);
return v_res_422_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__1_spec__1(lean_object* v_msgData_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_){
_start:
{
lean_object* v___x_429_; lean_object* v_env_430_; lean_object* v___x_431_; lean_object* v_mctx_432_; lean_object* v_lctx_433_; lean_object* v_options_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; 
v___x_429_ = lean_st_ref_get(v___y_427_);
v_env_430_ = lean_ctor_get(v___x_429_, 0);
lean_inc_ref(v_env_430_);
lean_dec(v___x_429_);
v___x_431_ = lean_st_ref_get(v___y_425_);
v_mctx_432_ = lean_ctor_get(v___x_431_, 0);
lean_inc_ref(v_mctx_432_);
lean_dec(v___x_431_);
v_lctx_433_ = lean_ctor_get(v___y_424_, 2);
v_options_434_ = lean_ctor_get(v___y_426_, 2);
lean_inc_ref(v_options_434_);
lean_inc_ref(v_lctx_433_);
v___x_435_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_435_, 0, v_env_430_);
lean_ctor_set(v___x_435_, 1, v_mctx_432_);
lean_ctor_set(v___x_435_, 2, v_lctx_433_);
lean_ctor_set(v___x_435_, 3, v_options_434_);
v___x_436_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_436_, 0, v___x_435_);
lean_ctor_set(v___x_436_, 1, v_msgData_423_);
v___x_437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_437_, 0, v___x_436_);
return v___x_437_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__1_spec__1___boxed(lean_object* v_msgData_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_){
_start:
{
lean_object* v_res_444_; 
v_res_444_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__1_spec__1(v_msgData_438_, v___y_439_, v___y_440_, v___y_441_, v___y_442_);
lean_dec(v___y_442_);
lean_dec_ref(v___y_441_);
lean_dec(v___y_440_);
lean_dec_ref(v___y_439_);
return v_res_444_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__1___redArg(lean_object* v_msg_445_, lean_object* v___y_446_, lean_object* v___y_447_, lean_object* v___y_448_, lean_object* v___y_449_){
_start:
{
lean_object* v_ref_451_; lean_object* v___x_452_; lean_object* v_a_453_; lean_object* v___x_455_; uint8_t v_isShared_456_; uint8_t v_isSharedCheck_461_; 
v_ref_451_ = lean_ctor_get(v___y_448_, 5);
v___x_452_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__1_spec__1(v_msg_445_, v___y_446_, v___y_447_, v___y_448_, v___y_449_);
v_a_453_ = lean_ctor_get(v___x_452_, 0);
v_isSharedCheck_461_ = !lean_is_exclusive(v___x_452_);
if (v_isSharedCheck_461_ == 0)
{
v___x_455_ = v___x_452_;
v_isShared_456_ = v_isSharedCheck_461_;
goto v_resetjp_454_;
}
else
{
lean_inc(v_a_453_);
lean_dec(v___x_452_);
v___x_455_ = lean_box(0);
v_isShared_456_ = v_isSharedCheck_461_;
goto v_resetjp_454_;
}
v_resetjp_454_:
{
lean_object* v___x_457_; lean_object* v___x_459_; 
lean_inc(v_ref_451_);
v___x_457_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_457_, 0, v_ref_451_);
lean_ctor_set(v___x_457_, 1, v_a_453_);
if (v_isShared_456_ == 0)
{
lean_ctor_set_tag(v___x_455_, 1);
lean_ctor_set(v___x_455_, 0, v___x_457_);
v___x_459_ = v___x_455_;
goto v_reusejp_458_;
}
else
{
lean_object* v_reuseFailAlloc_460_; 
v_reuseFailAlloc_460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_460_, 0, v___x_457_);
v___x_459_ = v_reuseFailAlloc_460_;
goto v_reusejp_458_;
}
v_reusejp_458_:
{
return v___x_459_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__1___redArg___boxed(lean_object* v_msg_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_){
_start:
{
lean_object* v_res_468_; 
v_res_468_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__1___redArg(v_msg_462_, v___y_463_, v___y_464_, v___y_465_, v___y_466_);
lean_dec(v___y_466_);
lean_dec_ref(v___y_465_);
lean_dec(v___y_464_);
lean_dec_ref(v___y_463_);
return v_res_468_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__2___closed__4(void){
_start:
{
lean_object* v___x_477_; lean_object* v___x_478_; 
v___x_477_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__2___closed__3));
v___x_478_ = l_Lean_stringToMessageData(v___x_477_);
return v___x_478_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__2___closed__6(void){
_start:
{
lean_object* v___x_480_; lean_object* v___x_481_; 
v___x_480_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__2___closed__5));
v___x_481_ = l_Lean_stringToMessageData(v___x_480_);
return v___x_481_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__2___closed__8(void){
_start:
{
lean_object* v___x_483_; lean_object* v___x_484_; 
v___x_483_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__2___closed__7));
v___x_484_ = l_Lean_stringToMessageData(v___x_483_);
return v___x_484_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__2(lean_object* v_as_485_, size_t v_sz_486_, size_t v_i_487_, lean_object* v_b_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_){
_start:
{
lean_object* v_a_495_; uint8_t v___x_499_; 
v___x_499_ = lean_usize_dec_lt(v_i_487_, v_sz_486_);
if (v___x_499_ == 0)
{
lean_object* v___x_500_; 
v___x_500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_500_, 0, v_b_488_);
return v___x_500_;
}
else
{
lean_object* v_a_501_; lean_object* v___x_502_; 
v_a_501_ = lean_array_uget_borrowed(v_as_485_, v_i_487_);
lean_inc(v_a_501_);
v___x_502_ = l_Lean_Meta_mkConstWithFreshMVarLevels(v_a_501_, v___y_489_, v___y_490_, v___y_491_, v___y_492_);
if (lean_obj_tag(v___x_502_) == 0)
{
lean_object* v_a_503_; lean_object* v___x_504_; 
v_a_503_ = lean_ctor_get(v___x_502_, 0);
lean_inc(v_a_503_);
lean_dec_ref_known(v___x_502_, 1);
lean_inc(v___y_492_);
lean_inc_ref(v___y_491_);
lean_inc(v___y_490_);
lean_inc_ref(v___y_489_);
v___x_504_ = lean_infer_type(v_a_503_, v___y_489_, v___y_490_, v___y_491_, v___y_492_);
if (lean_obj_tag(v___x_504_) == 0)
{
lean_object* v_a_505_; lean_object* v___x_506_; uint8_t v___x_507_; lean_object* v___x_508_; 
v_a_505_ = lean_ctor_get(v___x_504_, 0);
lean_inc(v_a_505_);
lean_dec_ref_known(v___x_504_, 1);
v___x_506_ = lean_box(0);
v___x_507_ = 0;
v___x_508_ = l_Lean_Meta_forallMetaTelescopeReducing(v_a_505_, v___x_506_, v___x_507_, v___y_489_, v___y_490_, v___y_491_, v___y_492_);
if (lean_obj_tag(v___x_508_) == 0)
{
lean_object* v_a_509_; lean_object* v_snd_510_; lean_object* v___x_512_; uint8_t v_isShared_513_; uint8_t v_isSharedCheck_574_; 
v_a_509_ = lean_ctor_get(v___x_508_, 0);
lean_inc(v_a_509_);
lean_dec_ref_known(v___x_508_, 1);
v_snd_510_ = lean_ctor_get(v_a_509_, 1);
v_isSharedCheck_574_ = !lean_is_exclusive(v_a_509_);
if (v_isSharedCheck_574_ == 0)
{
lean_object* v_unused_575_; 
v_unused_575_ = lean_ctor_get(v_a_509_, 0);
lean_dec(v_unused_575_);
v___x_512_ = v_a_509_;
v_isShared_513_ = v_isSharedCheck_574_;
goto v_resetjp_511_;
}
else
{
lean_inc(v_snd_510_);
lean_dec(v_a_509_);
v___x_512_ = lean_box(0);
v_isShared_513_ = v_isSharedCheck_574_;
goto v_resetjp_511_;
}
v_resetjp_511_:
{
lean_object* v_snd_514_; lean_object* v___x_516_; uint8_t v_isShared_517_; uint8_t v_isSharedCheck_572_; 
v_snd_514_ = lean_ctor_get(v_snd_510_, 1);
v_isSharedCheck_572_ = !lean_is_exclusive(v_snd_510_);
if (v_isSharedCheck_572_ == 0)
{
lean_object* v_unused_573_; 
v_unused_573_ = lean_ctor_get(v_snd_510_, 0);
lean_dec(v_unused_573_);
v___x_516_ = v_snd_510_;
v_isShared_517_ = v_isSharedCheck_572_;
goto v_resetjp_515_;
}
else
{
lean_inc(v_snd_514_);
lean_dec(v_snd_510_);
v___x_516_ = lean_box(0);
v_isShared_517_ = v_isSharedCheck_572_;
goto v_resetjp_515_;
}
v_resetjp_515_:
{
lean_object* v___x_518_; 
v___x_518_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__0___redArg(v_snd_514_, v___y_490_);
if (lean_obj_tag(v___x_518_) == 0)
{
lean_object* v_a_519_; lean_object* v___x_520_; lean_object* v___x_521_; uint8_t v___x_522_; 
v_a_519_ = lean_ctor_get(v___x_518_, 0);
lean_inc(v_a_519_);
lean_dec_ref_known(v___x_518_, 1);
v___x_520_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__2___closed__2));
v___x_521_ = lean_unsigned_to_nat(4u);
v___x_522_ = l_Lean_Expr_isAppOfArity(v_a_519_, v___x_520_, v___x_521_);
if (v___x_522_ == 0)
{
lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_526_; 
lean_dec(v_a_519_);
lean_del_object(v___x_516_);
v___x_523_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__2___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__2___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__2___closed__4);
lean_inc(v_a_501_);
v___x_524_ = l_Lean_MessageData_ofName(v_a_501_);
if (v_isShared_513_ == 0)
{
lean_ctor_set_tag(v___x_512_, 7);
lean_ctor_set(v___x_512_, 1, v___x_524_);
lean_ctor_set(v___x_512_, 0, v___x_523_);
v___x_526_ = v___x_512_;
goto v_reusejp_525_;
}
else
{
lean_object* v_reuseFailAlloc_538_; 
v_reuseFailAlloc_538_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_538_, 0, v___x_523_);
lean_ctor_set(v_reuseFailAlloc_538_, 1, v___x_524_);
v___x_526_ = v_reuseFailAlloc_538_;
goto v_reusejp_525_;
}
v_reusejp_525_:
{
lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; 
v___x_527_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__2___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__2___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__2___closed__6);
v___x_528_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_528_, 0, v___x_526_);
lean_ctor_set(v___x_528_, 1, v___x_527_);
v___x_529_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__1___redArg(v___x_528_, v___y_489_, v___y_490_, v___y_491_, v___y_492_);
if (lean_obj_tag(v___x_529_) == 0)
{
lean_dec_ref_known(v___x_529_, 1);
v_a_495_ = v_b_488_;
goto v___jp_494_;
}
else
{
lean_object* v_a_530_; lean_object* v___x_532_; uint8_t v_isShared_533_; uint8_t v_isSharedCheck_537_; 
lean_dec_ref(v_b_488_);
v_a_530_ = lean_ctor_get(v___x_529_, 0);
v_isSharedCheck_537_ = !lean_is_exclusive(v___x_529_);
if (v_isSharedCheck_537_ == 0)
{
v___x_532_ = v___x_529_;
v_isShared_533_ = v_isSharedCheck_537_;
goto v_resetjp_531_;
}
else
{
lean_inc(v_a_530_);
lean_dec(v___x_529_);
v___x_532_ = lean_box(0);
v_isShared_533_ = v_isSharedCheck_537_;
goto v_resetjp_531_;
}
v_resetjp_531_:
{
lean_object* v___x_535_; 
if (v_isShared_533_ == 0)
{
v___x_535_ = v___x_532_;
goto v_reusejp_534_;
}
else
{
lean_object* v_reuseFailAlloc_536_; 
v_reuseFailAlloc_536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_536_, 0, v_a_530_);
v___x_535_ = v_reuseFailAlloc_536_;
goto v_reusejp_534_;
}
v_reusejp_534_:
{
return v___x_535_;
}
}
}
}
}
else
{
lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; 
v___x_539_ = l_Lean_Expr_appArg_x21(v_a_519_);
lean_dec(v_a_519_);
v___x_540_ = l_Lean_Expr_getAppFn(v___x_539_);
v___x_541_ = l_Lean_Expr_constName_x3f(v___x_540_);
lean_dec_ref(v___x_540_);
if (lean_obj_tag(v___x_541_) == 1)
{
lean_object* v_val_542_; lean_object* v___x_543_; lean_object* v___x_545_; 
lean_del_object(v___x_512_);
v_val_542_ = lean_ctor_get(v___x_541_, 0);
lean_inc(v_val_542_);
lean_dec_ref_known(v___x_541_, 1);
v___x_543_ = l_Lean_Expr_getAppNumArgs(v___x_539_);
lean_dec_ref(v___x_539_);
lean_inc(v_a_501_);
if (v_isShared_517_ == 0)
{
lean_ctor_set(v___x_516_, 1, v___x_543_);
lean_ctor_set(v___x_516_, 0, v_a_501_);
v___x_545_ = v___x_516_;
goto v_reusejp_544_;
}
else
{
lean_object* v_reuseFailAlloc_547_; 
v_reuseFailAlloc_547_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_547_, 0, v_a_501_);
lean_ctor_set(v_reuseFailAlloc_547_, 1, v___x_543_);
v___x_545_ = v_reuseFailAlloc_547_;
goto v_reusejp_544_;
}
v_reusejp_544_:
{
lean_object* v___x_546_; 
v___x_546_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable_spec__0___redArg(v_b_488_, v_val_542_, v___x_545_);
v_a_495_ = v___x_546_;
goto v___jp_494_;
}
}
else
{
lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_551_; 
lean_dec(v___x_541_);
lean_dec_ref(v___x_539_);
lean_del_object(v___x_516_);
v___x_548_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__2___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__2___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__2___closed__4);
lean_inc(v_a_501_);
v___x_549_ = l_Lean_MessageData_ofName(v_a_501_);
if (v_isShared_513_ == 0)
{
lean_ctor_set_tag(v___x_512_, 7);
lean_ctor_set(v___x_512_, 1, v___x_549_);
lean_ctor_set(v___x_512_, 0, v___x_548_);
v___x_551_ = v___x_512_;
goto v_reusejp_550_;
}
else
{
lean_object* v_reuseFailAlloc_563_; 
v_reuseFailAlloc_563_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_563_, 0, v___x_548_);
lean_ctor_set(v_reuseFailAlloc_563_, 1, v___x_549_);
v___x_551_ = v_reuseFailAlloc_563_;
goto v_reusejp_550_;
}
v_reusejp_550_:
{
lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; 
v___x_552_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__2___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__2___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__2___closed__8);
v___x_553_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_553_, 0, v___x_551_);
lean_ctor_set(v___x_553_, 1, v___x_552_);
v___x_554_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__1___redArg(v___x_553_, v___y_489_, v___y_490_, v___y_491_, v___y_492_);
if (lean_obj_tag(v___x_554_) == 0)
{
lean_dec_ref_known(v___x_554_, 1);
v_a_495_ = v_b_488_;
goto v___jp_494_;
}
else
{
lean_object* v_a_555_; lean_object* v___x_557_; uint8_t v_isShared_558_; uint8_t v_isSharedCheck_562_; 
lean_dec_ref(v_b_488_);
v_a_555_ = lean_ctor_get(v___x_554_, 0);
v_isSharedCheck_562_ = !lean_is_exclusive(v___x_554_);
if (v_isSharedCheck_562_ == 0)
{
v___x_557_ = v___x_554_;
v_isShared_558_ = v_isSharedCheck_562_;
goto v_resetjp_556_;
}
else
{
lean_inc(v_a_555_);
lean_dec(v___x_554_);
v___x_557_ = lean_box(0);
v_isShared_558_ = v_isSharedCheck_562_;
goto v_resetjp_556_;
}
v_resetjp_556_:
{
lean_object* v___x_560_; 
if (v_isShared_558_ == 0)
{
v___x_560_ = v___x_557_;
goto v_reusejp_559_;
}
else
{
lean_object* v_reuseFailAlloc_561_; 
v_reuseFailAlloc_561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_561_, 0, v_a_555_);
v___x_560_ = v_reuseFailAlloc_561_;
goto v_reusejp_559_;
}
v_reusejp_559_:
{
return v___x_560_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_564_; lean_object* v___x_566_; uint8_t v_isShared_567_; uint8_t v_isSharedCheck_571_; 
lean_del_object(v___x_516_);
lean_del_object(v___x_512_);
lean_dec_ref(v_b_488_);
v_a_564_ = lean_ctor_get(v___x_518_, 0);
v_isSharedCheck_571_ = !lean_is_exclusive(v___x_518_);
if (v_isSharedCheck_571_ == 0)
{
v___x_566_ = v___x_518_;
v_isShared_567_ = v_isSharedCheck_571_;
goto v_resetjp_565_;
}
else
{
lean_inc(v_a_564_);
lean_dec(v___x_518_);
v___x_566_ = lean_box(0);
v_isShared_567_ = v_isSharedCheck_571_;
goto v_resetjp_565_;
}
v_resetjp_565_:
{
lean_object* v___x_569_; 
if (v_isShared_567_ == 0)
{
v___x_569_ = v___x_566_;
goto v_reusejp_568_;
}
else
{
lean_object* v_reuseFailAlloc_570_; 
v_reuseFailAlloc_570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_570_, 0, v_a_564_);
v___x_569_ = v_reuseFailAlloc_570_;
goto v_reusejp_568_;
}
v_reusejp_568_:
{
return v___x_569_;
}
}
}
}
}
}
else
{
lean_object* v_a_576_; lean_object* v___x_578_; uint8_t v_isShared_579_; uint8_t v_isSharedCheck_583_; 
lean_dec_ref(v_b_488_);
v_a_576_ = lean_ctor_get(v___x_508_, 0);
v_isSharedCheck_583_ = !lean_is_exclusive(v___x_508_);
if (v_isSharedCheck_583_ == 0)
{
v___x_578_ = v___x_508_;
v_isShared_579_ = v_isSharedCheck_583_;
goto v_resetjp_577_;
}
else
{
lean_inc(v_a_576_);
lean_dec(v___x_508_);
v___x_578_ = lean_box(0);
v_isShared_579_ = v_isSharedCheck_583_;
goto v_resetjp_577_;
}
v_resetjp_577_:
{
lean_object* v___x_581_; 
if (v_isShared_579_ == 0)
{
v___x_581_ = v___x_578_;
goto v_reusejp_580_;
}
else
{
lean_object* v_reuseFailAlloc_582_; 
v_reuseFailAlloc_582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_582_, 0, v_a_576_);
v___x_581_ = v_reuseFailAlloc_582_;
goto v_reusejp_580_;
}
v_reusejp_580_:
{
return v___x_581_;
}
}
}
}
else
{
lean_object* v_a_584_; lean_object* v___x_586_; uint8_t v_isShared_587_; uint8_t v_isSharedCheck_591_; 
lean_dec_ref(v_b_488_);
v_a_584_ = lean_ctor_get(v___x_504_, 0);
v_isSharedCheck_591_ = !lean_is_exclusive(v___x_504_);
if (v_isSharedCheck_591_ == 0)
{
v___x_586_ = v___x_504_;
v_isShared_587_ = v_isSharedCheck_591_;
goto v_resetjp_585_;
}
else
{
lean_inc(v_a_584_);
lean_dec(v___x_504_);
v___x_586_ = lean_box(0);
v_isShared_587_ = v_isSharedCheck_591_;
goto v_resetjp_585_;
}
v_resetjp_585_:
{
lean_object* v___x_589_; 
if (v_isShared_587_ == 0)
{
v___x_589_ = v___x_586_;
goto v_reusejp_588_;
}
else
{
lean_object* v_reuseFailAlloc_590_; 
v_reuseFailAlloc_590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_590_, 0, v_a_584_);
v___x_589_ = v_reuseFailAlloc_590_;
goto v_reusejp_588_;
}
v_reusejp_588_:
{
return v___x_589_;
}
}
}
}
else
{
lean_object* v_a_592_; lean_object* v___x_594_; uint8_t v_isShared_595_; uint8_t v_isSharedCheck_599_; 
lean_dec_ref(v_b_488_);
v_a_592_ = lean_ctor_get(v___x_502_, 0);
v_isSharedCheck_599_ = !lean_is_exclusive(v___x_502_);
if (v_isSharedCheck_599_ == 0)
{
v___x_594_ = v___x_502_;
v_isShared_595_ = v_isSharedCheck_599_;
goto v_resetjp_593_;
}
else
{
lean_inc(v_a_592_);
lean_dec(v___x_502_);
v___x_594_ = lean_box(0);
v_isShared_595_ = v_isSharedCheck_599_;
goto v_resetjp_593_;
}
v_resetjp_593_:
{
lean_object* v___x_597_; 
if (v_isShared_595_ == 0)
{
v___x_597_ = v___x_594_;
goto v_reusejp_596_;
}
else
{
lean_object* v_reuseFailAlloc_598_; 
v_reuseFailAlloc_598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_598_, 0, v_a_592_);
v___x_597_ = v_reuseFailAlloc_598_;
goto v_reusejp_596_;
}
v_reusejp_596_:
{
return v___x_597_;
}
}
}
}
v___jp_494_:
{
size_t v___x_496_; size_t v___x_497_; 
v___x_496_ = ((size_t)1ULL);
v___x_497_ = lean_usize_add(v_i_487_, v___x_496_);
v_i_487_ = v___x_497_;
v_b_488_ = v_a_495_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__2___boxed(lean_object* v_as_600_, lean_object* v_sz_601_, lean_object* v_i_602_, lean_object* v_b_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_){
_start:
{
size_t v_sz_boxed_609_; size_t v_i_boxed_610_; lean_object* v_res_611_; 
v_sz_boxed_609_ = lean_unbox_usize(v_sz_601_);
lean_dec(v_sz_601_);
v_i_boxed_610_ = lean_unbox_usize(v_i_602_);
lean_dec(v_i_602_);
v_res_611_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__2(v_as_600_, v_sz_boxed_609_, v_i_boxed_610_, v_b_603_, v___y_604_, v___y_605_, v___y_606_, v___y_607_);
lean_dec(v___y_607_);
lean_dec_ref(v___y_606_);
lean_dec(v___y_605_);
lean_dec_ref(v___y_604_);
lean_dec_ref(v_as_600_);
return v_res_611_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals___closed__0(void){
_start:
{
lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; 
v___x_612_ = lean_box(0);
v___x_613_ = lean_unsigned_to_nat(16u);
v___x_614_ = lean_mk_array(v___x_613_, v___x_612_);
return v___x_614_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals___closed__1(void){
_start:
{
lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v_m_617_; 
v___x_615_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals___closed__0, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals___closed__0_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals___closed__0);
v___x_616_ = lean_unsigned_to_nat(0u);
v_m_617_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_m_617_, 0, v___x_616_);
lean_ctor_set(v_m_617_, 1, v___x_615_);
return v_m_617_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals(lean_object* v_names_618_, lean_object* v_a_619_, lean_object* v_a_620_, lean_object* v_a_621_, lean_object* v_a_622_){
_start:
{
lean_object* v_m_624_; size_t v_sz_625_; size_t v___x_626_; lean_object* v___x_627_; 
v_m_624_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals___closed__1, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals___closed__1_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals___closed__1);
v_sz_625_ = lean_array_size(v_names_618_);
v___x_626_ = ((size_t)0ULL);
v___x_627_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__2(v_names_618_, v_sz_625_, v___x_626_, v_m_624_, v_a_619_, v_a_620_, v_a_621_, v_a_622_);
return v___x_627_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals___boxed(lean_object* v_names_628_, lean_object* v_a_629_, lean_object* v_a_630_, lean_object* v_a_631_, lean_object* v_a_632_, lean_object* v_a_633_){
_start:
{
lean_object* v_res_634_; 
v_res_634_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals(v_names_628_, v_a_629_, v_a_630_, v_a_631_, v_a_632_);
lean_dec(v_a_632_);
lean_dec_ref(v_a_631_);
lean_dec(v_a_630_);
lean_dec_ref(v_a_629_);
lean_dec_ref(v_names_628_);
return v_res_634_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__1(lean_object* v_00_u03b1_635_, lean_object* v_msg_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_){
_start:
{
lean_object* v___x_642_; 
v___x_642_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__1___redArg(v_msg_636_, v___y_637_, v___y_638_, v___y_639_, v___y_640_);
return v___x_642_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__1___boxed(lean_object* v_00_u03b1_643_, lean_object* v_msg_644_, lean_object* v___y_645_, lean_object* v___y_646_, lean_object* v___y_647_, lean_object* v___y_648_, lean_object* v___y_649_){
_start:
{
lean_object* v_res_650_; 
v_res_650_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__1(v_00_u03b1_643_, v_msg_644_, v___y_645_, v___y_646_, v___y_647_, v___y_648_);
lean_dec(v___y_648_);
lean_dec_ref(v___y_647_);
lean_dec(v___y_646_);
lean_dec_ref(v___y_645_);
return v_res_650_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_go___lam__0(uint8_t v_isZero_651_, lean_object* v_x_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_){
_start:
{
lean_object* v___x_663_; lean_object* v___x_664_; 
v___x_663_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_663_, 0, v_isZero_651_);
lean_ctor_set_uint8(v___x_663_, 1, v_isZero_651_);
v___x_664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_664_, 0, v___x_663_);
return v___x_664_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_go___lam__0___boxed(lean_object* v_isZero_665_, lean_object* v_x_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_){
_start:
{
uint8_t v_isZero_boxed_677_; lean_object* v_res_678_; 
v_isZero_boxed_677_ = lean_unbox(v_isZero_665_);
v_res_678_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_go___lam__0(v_isZero_boxed_677_, v_x_666_, v___y_667_, v___y_668_, v___y_669_, v___y_670_, v___y_671_, v___y_672_, v___y_673_, v___y_674_, v___y_675_);
lean_dec(v___y_675_);
lean_dec_ref(v___y_674_);
lean_dec(v___y_673_);
lean_dec_ref(v___y_672_);
lean_dec(v___y_671_);
lean_dec_ref(v___y_670_);
lean_dec(v___y_669_);
lean_dec_ref(v___y_668_);
lean_dec(v___y_667_);
lean_dec_ref(v_x_666_);
return v_res_678_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_go_spec__0___redArg(lean_object* v_msg_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_){
_start:
{
lean_object* v_ref_685_; lean_object* v___x_686_; lean_object* v_a_687_; lean_object* v___x_689_; uint8_t v_isShared_690_; uint8_t v_isSharedCheck_695_; 
v_ref_685_ = lean_ctor_get(v___y_682_, 5);
v___x_686_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__1_spec__1(v_msg_679_, v___y_680_, v___y_681_, v___y_682_, v___y_683_);
v_a_687_ = lean_ctor_get(v___x_686_, 0);
v_isSharedCheck_695_ = !lean_is_exclusive(v___x_686_);
if (v_isSharedCheck_695_ == 0)
{
v___x_689_ = v___x_686_;
v_isShared_690_ = v_isSharedCheck_695_;
goto v_resetjp_688_;
}
else
{
lean_inc(v_a_687_);
lean_dec(v___x_686_);
v___x_689_ = lean_box(0);
v_isShared_690_ = v_isSharedCheck_695_;
goto v_resetjp_688_;
}
v_resetjp_688_:
{
lean_object* v___x_691_; lean_object* v___x_693_; 
lean_inc(v_ref_685_);
v___x_691_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_691_, 0, v_ref_685_);
lean_ctor_set(v___x_691_, 1, v_a_687_);
if (v_isShared_690_ == 0)
{
lean_ctor_set_tag(v___x_689_, 1);
lean_ctor_set(v___x_689_, 0, v___x_691_);
v___x_693_ = v___x_689_;
goto v_reusejp_692_;
}
else
{
lean_object* v_reuseFailAlloc_694_; 
v_reuseFailAlloc_694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_694_, 0, v___x_691_);
v___x_693_ = v_reuseFailAlloc_694_;
goto v_reusejp_692_;
}
v_reusejp_692_:
{
return v___x_693_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_go_spec__0___redArg___boxed(lean_object* v_msg_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_){
_start:
{
lean_object* v_res_702_; 
v_res_702_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_go_spec__0___redArg(v_msg_696_, v___y_697_, v___y_698_, v___y_699_, v___y_700_);
lean_dec(v___y_700_);
lean_dec_ref(v___y_699_);
lean_dec(v___y_698_);
lean_dec_ref(v___y_697_);
return v_res_702_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_go___closed__1(void){
_start:
{
lean_object* v___x_704_; lean_object* v___x_705_; 
v___x_704_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_go___closed__0));
v___x_705_ = l_Lean_stringToMessageData(v___x_704_);
return v___x_705_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_go(lean_object* v_step_709_, lean_object* v_e_u2080_710_, lean_object* v_cur_711_, lean_object* v_proof_x3f_712_, lean_object* v_a_713_, lean_object* v_a_714_, lean_object* v_a_715_, lean_object* v_a_716_, lean_object* v_a_717_, lean_object* v_a_718_, lean_object* v_a_719_){
_start:
{
lean_object* v_zero_721_; uint8_t v_isZero_722_; 
v_zero_721_ = lean_unsigned_to_nat(0u);
v_isZero_722_ = lean_nat_dec_eq(v_a_713_, v_zero_721_);
if (v_isZero_722_ == 1)
{
lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; 
lean_dec(v_a_713_);
lean_dec(v_proof_x3f_712_);
lean_dec_ref(v_e_u2080_710_);
lean_dec_ref(v_step_709_);
v___x_723_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_go___closed__1, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_go___closed__1_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_go___closed__1);
v___x_724_ = l_Lean_indentExpr(v_cur_711_);
v___x_725_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_725_, 0, v___x_723_);
lean_ctor_set(v___x_725_, 1, v___x_724_);
v___x_726_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_go_spec__0___redArg(v___x_725_, v_a_716_, v_a_717_, v_a_718_, v_a_719_);
return v___x_726_;
}
else
{
lean_object* v___x_727_; lean_object* v___f_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; 
v___x_727_ = lean_box(v_isZero_722_);
v___f_728_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_go___lam__0___boxed), 12, 1);
lean_closure_set(v___f_728_, 0, v___x_727_);
lean_inc_ref(v_step_709_);
lean_inc_ref(v_cur_711_);
v___x_729_ = lean_apply_1(v_step_709_, v_cur_711_);
lean_inc_ref(v___f_728_);
v___x_730_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_730_, 0, v___f_728_);
lean_ctor_set(v___x_730_, 1, v___f_728_);
v___x_731_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_go___closed__2));
v___x_732_ = l_Lean_Meta_Sym_Simp_SimpM_run_x27___redArg(v___x_729_, v___x_730_, v___x_731_, v_a_714_, v_a_715_, v_a_716_, v_a_717_, v_a_718_, v_a_719_);
if (lean_obj_tag(v___x_732_) == 0)
{
lean_object* v_a_733_; lean_object* v___x_735_; uint8_t v_isShared_736_; uint8_t v_isSharedCheck_766_; 
v_a_733_ = lean_ctor_get(v___x_732_, 0);
v_isSharedCheck_766_ = !lean_is_exclusive(v___x_732_);
if (v_isSharedCheck_766_ == 0)
{
v___x_735_ = v___x_732_;
v_isShared_736_ = v_isSharedCheck_766_;
goto v_resetjp_734_;
}
else
{
lean_inc(v_a_733_);
lean_dec(v___x_732_);
v___x_735_ = lean_box(0);
v_isShared_736_ = v_isSharedCheck_766_;
goto v_resetjp_734_;
}
v_resetjp_734_:
{
if (lean_obj_tag(v_a_733_) == 0)
{
lean_object* v___x_737_; lean_object* v___x_739_; 
lean_dec_ref_known(v_a_733_, 0);
lean_dec(v_a_713_);
lean_dec_ref(v_e_u2080_710_);
lean_dec_ref(v_step_709_);
v___x_737_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_737_, 0, v_cur_711_);
lean_ctor_set(v___x_737_, 1, v_proof_x3f_712_);
if (v_isShared_736_ == 0)
{
lean_ctor_set(v___x_735_, 0, v___x_737_);
v___x_739_ = v___x_735_;
goto v_reusejp_738_;
}
else
{
lean_object* v_reuseFailAlloc_740_; 
v_reuseFailAlloc_740_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_740_, 0, v___x_737_);
v___x_739_ = v_reuseFailAlloc_740_;
goto v_reusejp_738_;
}
v_reusejp_738_:
{
return v___x_739_;
}
}
else
{
lean_object* v_e_x27_741_; lean_object* v_proof_742_; lean_object* v_one_743_; lean_object* v_n_744_; lean_object* v_proof_746_; lean_object* v___y_747_; lean_object* v___y_748_; lean_object* v___y_749_; lean_object* v___y_750_; lean_object* v___y_751_; lean_object* v___y_752_; 
lean_del_object(v___x_735_);
v_e_x27_741_ = lean_ctor_get(v_a_733_, 0);
lean_inc_ref(v_e_x27_741_);
v_proof_742_ = lean_ctor_get(v_a_733_, 1);
lean_inc_ref(v_proof_742_);
lean_dec_ref_known(v_a_733_, 2);
v_one_743_ = lean_unsigned_to_nat(1u);
v_n_744_ = lean_nat_sub(v_a_713_, v_one_743_);
lean_dec(v_a_713_);
if (lean_obj_tag(v_proof_x3f_712_) == 0)
{
lean_dec_ref(v_cur_711_);
v_proof_746_ = v_proof_742_;
v___y_747_ = v_a_714_;
v___y_748_ = v_a_715_;
v___y_749_ = v_a_716_;
v___y_750_ = v_a_717_;
v___y_751_ = v_a_718_;
v___y_752_ = v_a_719_;
goto v___jp_745_;
}
else
{
lean_object* v_val_755_; lean_object* v___x_756_; 
v_val_755_ = lean_ctor_get(v_proof_x3f_712_, 0);
lean_inc(v_val_755_);
lean_dec_ref_known(v_proof_x3f_712_, 1);
lean_inc_ref(v_e_x27_741_);
lean_inc_ref(v_e_u2080_710_);
v___x_756_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v_e_u2080_710_, v_cur_711_, v_val_755_, v_e_x27_741_, v_proof_742_, v_a_714_, v_a_715_, v_a_716_, v_a_717_, v_a_718_, v_a_719_);
if (lean_obj_tag(v___x_756_) == 0)
{
lean_object* v_a_757_; 
v_a_757_ = lean_ctor_get(v___x_756_, 0);
lean_inc(v_a_757_);
lean_dec_ref_known(v___x_756_, 1);
v_proof_746_ = v_a_757_;
v___y_747_ = v_a_714_;
v___y_748_ = v_a_715_;
v___y_749_ = v_a_716_;
v___y_750_ = v_a_717_;
v___y_751_ = v_a_718_;
v___y_752_ = v_a_719_;
goto v___jp_745_;
}
else
{
lean_object* v_a_758_; lean_object* v___x_760_; uint8_t v_isShared_761_; uint8_t v_isSharedCheck_765_; 
lean_dec(v_n_744_);
lean_dec_ref(v_e_x27_741_);
lean_dec_ref(v_e_u2080_710_);
lean_dec_ref(v_step_709_);
v_a_758_ = lean_ctor_get(v___x_756_, 0);
v_isSharedCheck_765_ = !lean_is_exclusive(v___x_756_);
if (v_isSharedCheck_765_ == 0)
{
v___x_760_ = v___x_756_;
v_isShared_761_ = v_isSharedCheck_765_;
goto v_resetjp_759_;
}
else
{
lean_inc(v_a_758_);
lean_dec(v___x_756_);
v___x_760_ = lean_box(0);
v_isShared_761_ = v_isSharedCheck_765_;
goto v_resetjp_759_;
}
v_resetjp_759_:
{
lean_object* v___x_763_; 
if (v_isShared_761_ == 0)
{
v___x_763_ = v___x_760_;
goto v_reusejp_762_;
}
else
{
lean_object* v_reuseFailAlloc_764_; 
v_reuseFailAlloc_764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_764_, 0, v_a_758_);
v___x_763_ = v_reuseFailAlloc_764_;
goto v_reusejp_762_;
}
v_reusejp_762_:
{
return v___x_763_;
}
}
}
}
v___jp_745_:
{
lean_object* v___x_753_; 
v___x_753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_753_, 0, v_proof_746_);
v_cur_711_ = v_e_x27_741_;
v_proof_x3f_712_ = v___x_753_;
v_a_713_ = v_n_744_;
v_a_714_ = v___y_747_;
v_a_715_ = v___y_748_;
v_a_716_ = v___y_749_;
v_a_717_ = v___y_750_;
v_a_718_ = v___y_751_;
v_a_719_ = v___y_752_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_767_; lean_object* v___x_769_; uint8_t v_isShared_770_; uint8_t v_isSharedCheck_774_; 
lean_dec(v_a_713_);
lean_dec(v_proof_x3f_712_);
lean_dec_ref(v_cur_711_);
lean_dec_ref(v_e_u2080_710_);
lean_dec_ref(v_step_709_);
v_a_767_ = lean_ctor_get(v___x_732_, 0);
v_isSharedCheck_774_ = !lean_is_exclusive(v___x_732_);
if (v_isSharedCheck_774_ == 0)
{
v___x_769_ = v___x_732_;
v_isShared_770_ = v_isSharedCheck_774_;
goto v_resetjp_768_;
}
else
{
lean_inc(v_a_767_);
lean_dec(v___x_732_);
v___x_769_ = lean_box(0);
v_isShared_770_ = v_isSharedCheck_774_;
goto v_resetjp_768_;
}
v_resetjp_768_:
{
lean_object* v___x_772_; 
if (v_isShared_770_ == 0)
{
v___x_772_ = v___x_769_;
goto v_reusejp_771_;
}
else
{
lean_object* v_reuseFailAlloc_773_; 
v_reuseFailAlloc_773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_773_, 0, v_a_767_);
v___x_772_ = v_reuseFailAlloc_773_;
goto v_reusejp_771_;
}
v_reusejp_771_:
{
return v___x_772_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_go___boxed(lean_object* v_step_775_, lean_object* v_e_u2080_776_, lean_object* v_cur_777_, lean_object* v_proof_x3f_778_, lean_object* v_a_779_, lean_object* v_a_780_, lean_object* v_a_781_, lean_object* v_a_782_, lean_object* v_a_783_, lean_object* v_a_784_, lean_object* v_a_785_, lean_object* v_a_786_){
_start:
{
lean_object* v_res_787_; 
v_res_787_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_go(v_step_775_, v_e_u2080_776_, v_cur_777_, v_proof_x3f_778_, v_a_779_, v_a_780_, v_a_781_, v_a_782_, v_a_783_, v_a_784_, v_a_785_);
lean_dec(v_a_785_);
lean_dec_ref(v_a_784_);
lean_dec(v_a_783_);
lean_dec_ref(v_a_782_);
lean_dec(v_a_781_);
lean_dec_ref(v_a_780_);
return v_res_787_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_go_spec__0(lean_object* v_00_u03b1_788_, lean_object* v_msg_789_, lean_object* v___y_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v___y_793_, lean_object* v___y_794_, lean_object* v___y_795_){
_start:
{
lean_object* v___x_797_; 
v___x_797_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_go_spec__0___redArg(v_msg_789_, v___y_792_, v___y_793_, v___y_794_, v___y_795_);
return v___x_797_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_go_spec__0___boxed(lean_object* v_00_u03b1_798_, lean_object* v_msg_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_){
_start:
{
lean_object* v_res_807_; 
v_res_807_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_go_spec__0(v_00_u03b1_798_, v_msg_799_, v___y_800_, v___y_801_, v___y_802_, v___y_803_, v___y_804_, v___y_805_);
lean_dec(v___y_805_);
lean_dec_ref(v___y_804_);
lean_dec(v___y_803_);
lean_dec_ref(v___y_802_);
lean_dec(v___y_801_);
lean_dec_ref(v___y_800_);
return v_res_807_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_spec__0___redArg(lean_object* v_as_808_, size_t v_i_809_, size_t v_stop_810_, lean_object* v_b_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_){
_start:
{
uint8_t v___x_817_; 
v___x_817_ = lean_usize_dec_eq(v_i_809_, v_stop_810_);
if (v___x_817_ == 0)
{
lean_object* v___x_818_; lean_object* v___x_819_; 
v___x_818_ = lean_array_uget_borrowed(v_as_808_, v_i_809_);
lean_inc(v___x_818_);
v___x_819_ = l_Lean_Meta_Sym_Simp_mkTheoremFromDecl(v___x_818_, v___y_812_, v___y_813_, v___y_814_, v___y_815_);
if (lean_obj_tag(v___x_819_) == 0)
{
lean_object* v_a_820_; lean_object* v___x_821_; size_t v___x_822_; size_t v___x_823_; 
v_a_820_ = lean_ctor_get(v___x_819_, 0);
lean_inc(v_a_820_);
lean_dec_ref_known(v___x_819_, 1);
v___x_821_ = l_Lean_Meta_Sym_Simp_Theorems_insert(v_b_811_, v_a_820_);
v___x_822_ = ((size_t)1ULL);
v___x_823_ = lean_usize_add(v_i_809_, v___x_822_);
v_i_809_ = v___x_823_;
v_b_811_ = v___x_821_;
goto _start;
}
else
{
lean_object* v_a_825_; lean_object* v___x_827_; uint8_t v_isShared_828_; uint8_t v_isSharedCheck_832_; 
lean_dec_ref(v_b_811_);
v_a_825_ = lean_ctor_get(v___x_819_, 0);
v_isSharedCheck_832_ = !lean_is_exclusive(v___x_819_);
if (v_isSharedCheck_832_ == 0)
{
v___x_827_ = v___x_819_;
v_isShared_828_ = v_isSharedCheck_832_;
goto v_resetjp_826_;
}
else
{
lean_inc(v_a_825_);
lean_dec(v___x_819_);
v___x_827_ = lean_box(0);
v_isShared_828_ = v_isSharedCheck_832_;
goto v_resetjp_826_;
}
v_resetjp_826_:
{
lean_object* v___x_830_; 
if (v_isShared_828_ == 0)
{
v___x_830_ = v___x_827_;
goto v_reusejp_829_;
}
else
{
lean_object* v_reuseFailAlloc_831_; 
v_reuseFailAlloc_831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_831_, 0, v_a_825_);
v___x_830_ = v_reuseFailAlloc_831_;
goto v_reusejp_829_;
}
v_reusejp_829_:
{
return v___x_830_;
}
}
}
}
else
{
lean_object* v___x_833_; 
v___x_833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_833_, 0, v_b_811_);
return v___x_833_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_spec__0___redArg___boxed(lean_object* v_as_834_, lean_object* v_i_835_, lean_object* v_stop_836_, lean_object* v_b_837_, lean_object* v___y_838_, lean_object* v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_){
_start:
{
size_t v_i_boxed_843_; size_t v_stop_boxed_844_; lean_object* v_res_845_; 
v_i_boxed_843_ = lean_unbox_usize(v_i_835_);
lean_dec(v_i_835_);
v_stop_boxed_844_ = lean_unbox_usize(v_stop_836_);
lean_dec(v_stop_836_);
v_res_845_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_spec__0___redArg(v_as_834_, v_i_boxed_843_, v_stop_boxed_844_, v_b_837_, v___y_838_, v___y_839_, v___y_840_, v___y_841_);
lean_dec(v___y_841_);
lean_dec_ref(v___y_840_);
lean_dec(v___y_839_);
lean_dec_ref(v___y_838_);
lean_dec_ref(v_as_834_);
return v_res_845_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp___closed__1(void){
_start:
{
lean_object* v___x_847_; 
v___x_847_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_847_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp___closed__2(void){
_start:
{
lean_object* v___x_848_; lean_object* v___x_849_; 
v___x_848_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp___closed__1, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp___closed__1_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp___closed__1);
v___x_849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_849_, 0, v___x_848_);
return v___x_849_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp(lean_object* v_rewrites_850_, lean_object* v_e_851_, lean_object* v_fuel_852_, lean_object* v_a_853_, lean_object* v_a_854_, lean_object* v_a_855_, lean_object* v_a_856_, lean_object* v_a_857_, lean_object* v_a_858_){
_start:
{
lean_object* v_a_861_; lean_object* v___y_877_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; uint8_t v___x_890_; 
v___x_887_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp___closed__2, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp___closed__2_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp___closed__2);
v___x_888_ = lean_unsigned_to_nat(0u);
v___x_889_ = lean_array_get_size(v_rewrites_850_);
v___x_890_ = lean_nat_dec_lt(v___x_888_, v___x_889_);
if (v___x_890_ == 0)
{
v_a_861_ = v___x_887_;
goto v___jp_860_;
}
else
{
uint8_t v___x_891_; 
v___x_891_ = lean_nat_dec_le(v___x_889_, v___x_889_);
if (v___x_891_ == 0)
{
if (v___x_890_ == 0)
{
v_a_861_ = v___x_887_;
goto v___jp_860_;
}
else
{
size_t v___x_892_; size_t v___x_893_; lean_object* v___x_894_; 
v___x_892_ = ((size_t)0ULL);
v___x_893_ = lean_usize_of_nat(v___x_889_);
v___x_894_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_spec__0___redArg(v_rewrites_850_, v___x_892_, v___x_893_, v___x_887_, v_a_855_, v_a_856_, v_a_857_, v_a_858_);
v___y_877_ = v___x_894_;
goto v___jp_876_;
}
}
else
{
size_t v___x_895_; size_t v___x_896_; lean_object* v___x_897_; 
v___x_895_ = ((size_t)0ULL);
v___x_896_ = lean_usize_of_nat(v___x_889_);
v___x_897_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_spec__0___redArg(v_rewrites_850_, v___x_895_, v___x_896_, v___x_887_, v_a_855_, v_a_856_, v_a_857_, v_a_858_);
v___y_877_ = v___x_897_;
goto v___jp_876_;
}
}
v___jp_860_:
{
lean_object* v___x_862_; 
v___x_862_ = l_Lean_Meta_Sym_shareCommon(v_e_851_, v_a_853_, v_a_854_, v_a_855_, v_a_856_, v_a_857_, v_a_858_);
if (lean_obj_tag(v___x_862_) == 0)
{
lean_object* v_a_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; 
v_a_863_ = lean_ctor_get(v___x_862_, 0);
lean_inc_n(v_a_863_, 2);
lean_dec_ref_known(v___x_862_, 1);
v___x_864_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp___closed__0));
v___x_865_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Simp_Theorems_rewrite___boxed), 13, 2);
lean_closure_set(v___x_865_, 0, v_a_861_);
lean_closure_set(v___x_865_, 1, v___x_864_);
v___x_866_ = lean_box(0);
v___x_867_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_go(v___x_865_, v_a_863_, v_a_863_, v___x_866_, v_fuel_852_, v_a_853_, v_a_854_, v_a_855_, v_a_856_, v_a_857_, v_a_858_);
return v___x_867_;
}
else
{
lean_object* v_a_868_; lean_object* v___x_870_; uint8_t v_isShared_871_; uint8_t v_isSharedCheck_875_; 
lean_dec_ref(v_a_861_);
lean_dec(v_fuel_852_);
v_a_868_ = lean_ctor_get(v___x_862_, 0);
v_isSharedCheck_875_ = !lean_is_exclusive(v___x_862_);
if (v_isSharedCheck_875_ == 0)
{
v___x_870_ = v___x_862_;
v_isShared_871_ = v_isSharedCheck_875_;
goto v_resetjp_869_;
}
else
{
lean_inc(v_a_868_);
lean_dec(v___x_862_);
v___x_870_ = lean_box(0);
v_isShared_871_ = v_isSharedCheck_875_;
goto v_resetjp_869_;
}
v_resetjp_869_:
{
lean_object* v___x_873_; 
if (v_isShared_871_ == 0)
{
v___x_873_ = v___x_870_;
goto v_reusejp_872_;
}
else
{
lean_object* v_reuseFailAlloc_874_; 
v_reuseFailAlloc_874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_874_, 0, v_a_868_);
v___x_873_ = v_reuseFailAlloc_874_;
goto v_reusejp_872_;
}
v_reusejp_872_:
{
return v___x_873_;
}
}
}
}
v___jp_876_:
{
if (lean_obj_tag(v___y_877_) == 0)
{
lean_object* v_a_878_; 
v_a_878_ = lean_ctor_get(v___y_877_, 0);
lean_inc(v_a_878_);
lean_dec_ref_known(v___y_877_, 1);
v_a_861_ = v_a_878_;
goto v___jp_860_;
}
else
{
lean_object* v_a_879_; lean_object* v___x_881_; uint8_t v_isShared_882_; uint8_t v_isSharedCheck_886_; 
lean_dec(v_fuel_852_);
lean_dec_ref(v_e_851_);
v_a_879_ = lean_ctor_get(v___y_877_, 0);
v_isSharedCheck_886_ = !lean_is_exclusive(v___y_877_);
if (v_isSharedCheck_886_ == 0)
{
v___x_881_ = v___y_877_;
v_isShared_882_ = v_isSharedCheck_886_;
goto v_resetjp_880_;
}
else
{
lean_inc(v_a_879_);
lean_dec(v___y_877_);
v___x_881_ = lean_box(0);
v_isShared_882_ = v_isSharedCheck_886_;
goto v_resetjp_880_;
}
v_resetjp_880_:
{
lean_object* v___x_884_; 
if (v_isShared_882_ == 0)
{
v___x_884_ = v___x_881_;
goto v_reusejp_883_;
}
else
{
lean_object* v_reuseFailAlloc_885_; 
v_reuseFailAlloc_885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_885_, 0, v_a_879_);
v___x_884_ = v_reuseFailAlloc_885_;
goto v_reusejp_883_;
}
v_reusejp_883_:
{
return v___x_884_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp___boxed(lean_object* v_rewrites_898_, lean_object* v_e_899_, lean_object* v_fuel_900_, lean_object* v_a_901_, lean_object* v_a_902_, lean_object* v_a_903_, lean_object* v_a_904_, lean_object* v_a_905_, lean_object* v_a_906_, lean_object* v_a_907_){
_start:
{
lean_object* v_res_908_; 
v_res_908_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp(v_rewrites_898_, v_e_899_, v_fuel_900_, v_a_901_, v_a_902_, v_a_903_, v_a_904_, v_a_905_, v_a_906_);
lean_dec(v_a_906_);
lean_dec_ref(v_a_905_);
lean_dec(v_a_904_);
lean_dec_ref(v_a_903_);
lean_dec(v_a_902_);
lean_dec_ref(v_a_901_);
lean_dec_ref(v_rewrites_898_);
return v_res_908_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_spec__0(lean_object* v_as_909_, size_t v_i_910_, size_t v_stop_911_, lean_object* v_b_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_){
_start:
{
lean_object* v___x_920_; 
v___x_920_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_spec__0___redArg(v_as_909_, v_i_910_, v_stop_911_, v_b_912_, v___y_915_, v___y_916_, v___y_917_, v___y_918_);
return v___x_920_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_spec__0___boxed(lean_object* v_as_921_, lean_object* v_i_922_, lean_object* v_stop_923_, lean_object* v_b_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_){
_start:
{
size_t v_i_boxed_932_; size_t v_stop_boxed_933_; lean_object* v_res_934_; 
v_i_boxed_932_ = lean_unbox_usize(v_i_922_);
lean_dec(v_i_922_);
v_stop_boxed_933_ = lean_unbox_usize(v_stop_923_);
lean_dec(v_stop_923_);
v_res_934_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_spec__0(v_as_921_, v_i_boxed_932_, v_stop_boxed_933_, v_b_924_, v___y_925_, v___y_926_, v___y_927_, v___y_928_, v___y_929_, v___y_930_);
lean_dec(v___y_930_);
lean_dec_ref(v___y_929_);
lean_dec(v___y_928_);
lean_dec_ref(v___y_927_);
lean_dec(v___y_926_);
lean_dec_ref(v___y_925_);
lean_dec_ref(v_as_921_);
return v_res_934_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply___lam__0(lean_object* v_s_935_, lean_object* v_a_936_, lean_object* v_pre_937_, lean_object* v_u_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_){
_start:
{
lean_object* v___x_944_; 
lean_inc_ref(v_u_938_);
v___x_944_ = l_Lean_Meta_mkEq(v_u_938_, v_s_935_, v___y_939_, v___y_940_, v___y_941_, v___y_942_);
if (lean_obj_tag(v___x_944_) == 0)
{
lean_object* v_a_945_; lean_object* v___x_947_; uint8_t v_isShared_948_; uint8_t v_isSharedCheck_976_; 
v_a_945_ = lean_ctor_get(v___x_944_, 0);
v_isSharedCheck_976_ = !lean_is_exclusive(v___x_944_);
if (v_isSharedCheck_976_ == 0)
{
v___x_947_ = v___x_944_;
v_isShared_948_ = v_isSharedCheck_976_;
goto v_resetjp_946_;
}
else
{
lean_inc(v_a_945_);
lean_dec(v___x_944_);
v___x_947_ = lean_box(0);
v_isShared_948_ = v_isSharedCheck_976_;
goto v_resetjp_946_;
}
v_resetjp_946_:
{
lean_object* v___x_949_; lean_object* v___x_951_; 
v___x_949_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_ofProp___closed__2));
if (v_isShared_948_ == 0)
{
lean_ctor_set_tag(v___x_947_, 1);
lean_ctor_set(v___x_947_, 0, v_a_936_);
v___x_951_ = v___x_947_;
goto v_reusejp_950_;
}
else
{
lean_object* v_reuseFailAlloc_975_; 
v_reuseFailAlloc_975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_975_, 0, v_a_936_);
v___x_951_ = v_reuseFailAlloc_975_;
goto v_reusejp_950_;
}
v_reusejp_950_:
{
lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; 
v___x_952_ = lean_box(0);
v___x_953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_953_, 0, v_a_945_);
v___x_954_ = lean_unsigned_to_nat(3u);
v___x_955_ = lean_mk_empty_array_with_capacity(v___x_954_);
v___x_956_ = lean_array_push(v___x_955_, v___x_951_);
v___x_957_ = lean_array_push(v___x_956_, v___x_952_);
v___x_958_ = lean_array_push(v___x_957_, v___x_953_);
v___x_959_ = l_Lean_Meta_mkAppOptM(v___x_949_, v___x_958_, v___y_939_, v___y_940_, v___y_941_, v___y_942_);
if (lean_obj_tag(v___x_959_) == 0)
{
lean_object* v_a_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; 
v_a_960_ = lean_ctor_get(v___x_959_, 0);
lean_inc(v_a_960_);
lean_dec_ref_known(v___x_959_, 1);
v___x_961_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_meet___closed__3));
v___x_962_ = lean_unsigned_to_nat(2u);
v___x_963_ = lean_mk_empty_array_with_capacity(v___x_962_);
v___x_964_ = lean_array_push(v___x_963_, v_a_960_);
v___x_965_ = lean_array_push(v___x_964_, v_pre_937_);
v___x_966_ = l_Lean_Meta_mkAppM(v___x_961_, v___x_965_, v___y_939_, v___y_940_, v___y_941_, v___y_942_);
if (lean_obj_tag(v___x_966_) == 0)
{
lean_object* v_a_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; uint8_t v___x_971_; uint8_t v___x_972_; uint8_t v___x_973_; lean_object* v___x_974_; 
v_a_967_ = lean_ctor_get(v___x_966_, 0);
lean_inc(v_a_967_);
lean_dec_ref_known(v___x_966_, 1);
v___x_968_ = lean_unsigned_to_nat(1u);
v___x_969_ = lean_mk_empty_array_with_capacity(v___x_968_);
v___x_970_ = lean_array_push(v___x_969_, v_u_938_);
v___x_971_ = 0;
v___x_972_ = 1;
v___x_973_ = 1;
v___x_974_ = l_Lean_Meta_mkLambdaFVars(v___x_970_, v_a_967_, v___x_971_, v___x_972_, v___x_971_, v___x_972_, v___x_973_, v___y_939_, v___y_940_, v___y_941_, v___y_942_);
lean_dec_ref(v___x_970_);
return v___x_974_;
}
else
{
lean_dec_ref(v_u_938_);
return v___x_966_;
}
}
else
{
lean_dec_ref(v_u_938_);
lean_dec_ref(v_pre_937_);
return v___x_959_;
}
}
}
}
else
{
lean_dec_ref(v_u_938_);
lean_dec_ref(v_pre_937_);
lean_dec_ref(v_a_936_);
return v___x_944_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply___lam__0___boxed(lean_object* v_s_977_, lean_object* v_a_978_, lean_object* v_pre_979_, lean_object* v_u_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_){
_start:
{
lean_object* v_res_986_; 
v_res_986_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply___lam__0(v_s_977_, v_a_978_, v_pre_979_, v_u_980_, v___y_981_, v___y_982_, v___y_983_, v___y_984_);
lean_dec(v___y_984_);
lean_dec_ref(v___y_983_);
lean_dec(v___y_982_);
lean_dec_ref(v___y_981_);
return v_res_986_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply_spec__0_spec__0___redArg___lam__0(lean_object* v_k_987_, lean_object* v_b_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_){
_start:
{
lean_object* v___x_994_; 
lean_inc(v___y_992_);
lean_inc_ref(v___y_991_);
lean_inc(v___y_990_);
lean_inc_ref(v___y_989_);
v___x_994_ = lean_apply_6(v_k_987_, v_b_988_, v___y_989_, v___y_990_, v___y_991_, v___y_992_, lean_box(0));
return v___x_994_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply_spec__0_spec__0___redArg___lam__0___boxed(lean_object* v_k_995_, lean_object* v_b_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_){
_start:
{
lean_object* v_res_1002_; 
v_res_1002_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply_spec__0_spec__0___redArg___lam__0(v_k_995_, v_b_996_, v___y_997_, v___y_998_, v___y_999_, v___y_1000_);
lean_dec(v___y_1000_);
lean_dec_ref(v___y_999_);
lean_dec(v___y_998_);
lean_dec_ref(v___y_997_);
return v_res_1002_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply_spec__0_spec__0___redArg(lean_object* v_name_1003_, uint8_t v_bi_1004_, lean_object* v_type_1005_, lean_object* v_k_1006_, uint8_t v_kind_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_){
_start:
{
lean_object* v___f_1013_; lean_object* v___x_1014_; 
v___f_1013_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply_spec__0_spec__0___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1013_, 0, v_k_1006_);
v___x_1014_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1003_, v_bi_1004_, v_type_1005_, v___f_1013_, v_kind_1007_, v___y_1008_, v___y_1009_, v___y_1010_, v___y_1011_);
if (lean_obj_tag(v___x_1014_) == 0)
{
lean_object* v_a_1015_; lean_object* v___x_1017_; uint8_t v_isShared_1018_; uint8_t v_isSharedCheck_1022_; 
v_a_1015_ = lean_ctor_get(v___x_1014_, 0);
v_isSharedCheck_1022_ = !lean_is_exclusive(v___x_1014_);
if (v_isSharedCheck_1022_ == 0)
{
v___x_1017_ = v___x_1014_;
v_isShared_1018_ = v_isSharedCheck_1022_;
goto v_resetjp_1016_;
}
else
{
lean_inc(v_a_1015_);
lean_dec(v___x_1014_);
v___x_1017_ = lean_box(0);
v_isShared_1018_ = v_isSharedCheck_1022_;
goto v_resetjp_1016_;
}
v_resetjp_1016_:
{
lean_object* v___x_1020_; 
if (v_isShared_1018_ == 0)
{
v___x_1020_ = v___x_1017_;
goto v_reusejp_1019_;
}
else
{
lean_object* v_reuseFailAlloc_1021_; 
v_reuseFailAlloc_1021_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1021_, 0, v_a_1015_);
v___x_1020_ = v_reuseFailAlloc_1021_;
goto v_reusejp_1019_;
}
v_reusejp_1019_:
{
return v___x_1020_;
}
}
}
else
{
lean_object* v_a_1023_; lean_object* v___x_1025_; uint8_t v_isShared_1026_; uint8_t v_isSharedCheck_1030_; 
v_a_1023_ = lean_ctor_get(v___x_1014_, 0);
v_isSharedCheck_1030_ = !lean_is_exclusive(v___x_1014_);
if (v_isSharedCheck_1030_ == 0)
{
v___x_1025_ = v___x_1014_;
v_isShared_1026_ = v_isSharedCheck_1030_;
goto v_resetjp_1024_;
}
else
{
lean_inc(v_a_1023_);
lean_dec(v___x_1014_);
v___x_1025_ = lean_box(0);
v_isShared_1026_ = v_isSharedCheck_1030_;
goto v_resetjp_1024_;
}
v_resetjp_1024_:
{
lean_object* v___x_1028_; 
if (v_isShared_1026_ == 0)
{
v___x_1028_ = v___x_1025_;
goto v_reusejp_1027_;
}
else
{
lean_object* v_reuseFailAlloc_1029_; 
v_reuseFailAlloc_1029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1029_, 0, v_a_1023_);
v___x_1028_ = v_reuseFailAlloc_1029_;
goto v_reusejp_1027_;
}
v_reusejp_1027_:
{
return v___x_1028_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply_spec__0_spec__0___redArg___boxed(lean_object* v_name_1031_, lean_object* v_bi_1032_, lean_object* v_type_1033_, lean_object* v_k_1034_, lean_object* v_kind_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_){
_start:
{
uint8_t v_bi_boxed_1041_; uint8_t v_kind_boxed_1042_; lean_object* v_res_1043_; 
v_bi_boxed_1041_ = lean_unbox(v_bi_1032_);
v_kind_boxed_1042_ = lean_unbox(v_kind_1035_);
v_res_1043_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply_spec__0_spec__0___redArg(v_name_1031_, v_bi_boxed_1041_, v_type_1033_, v_k_1034_, v_kind_boxed_1042_, v___y_1036_, v___y_1037_, v___y_1038_, v___y_1039_);
lean_dec(v___y_1039_);
lean_dec_ref(v___y_1038_);
lean_dec(v___y_1037_);
lean_dec_ref(v___y_1036_);
return v_res_1043_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply_spec__0___redArg(lean_object* v_name_1044_, lean_object* v_type_1045_, lean_object* v_k_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_){
_start:
{
uint8_t v___x_1052_; uint8_t v___x_1053_; lean_object* v___x_1054_; 
v___x_1052_ = 0;
v___x_1053_ = 0;
v___x_1054_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply_spec__0_spec__0___redArg(v_name_1044_, v___x_1052_, v_type_1045_, v_k_1046_, v___x_1053_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_);
return v___x_1054_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply_spec__0___redArg___boxed(lean_object* v_name_1055_, lean_object* v_type_1056_, lean_object* v_k_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_){
_start:
{
lean_object* v_res_1063_; 
v_res_1063_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply_spec__0___redArg(v_name_1055_, v_type_1056_, v_k_1057_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_);
lean_dec(v___y_1061_);
lean_dec_ref(v___y_1060_);
lean_dec(v___y_1059_);
lean_dec_ref(v___y_1058_);
return v_res_1063_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply___closed__1(void){
_start:
{
lean_object* v___x_1065_; lean_object* v___x_1066_; 
v___x_1065_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply___closed__0));
v___x_1066_ = l_Lean_stringToMessageData(v___x_1065_);
return v___x_1066_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply(lean_object* v_introThm_1075_, lean_object* v_opAs_1076_, lean_object* v_pre_1077_, lean_object* v_ss_1078_, lean_object* v_a_1079_, lean_object* v_a_1080_, lean_object* v_a_1081_, lean_object* v_a_1082_){
_start:
{
if (lean_obj_tag(v_ss_1078_) == 0)
{
lean_object* v___x_1084_; 
lean_inc(v_introThm_1075_);
v___x_1084_ = l_Lean_Meta_mkConstWithFreshMVarLevels(v_introThm_1075_, v_a_1079_, v_a_1080_, v_a_1081_, v_a_1082_);
if (lean_obj_tag(v___x_1084_) == 0)
{
lean_object* v_a_1085_; lean_object* v___x_1086_; 
v_a_1085_ = lean_ctor_get(v___x_1084_, 0);
lean_inc_n(v_a_1085_, 2);
lean_dec_ref_known(v___x_1084_, 1);
lean_inc(v_a_1082_);
lean_inc_ref(v_a_1081_);
lean_inc(v_a_1080_);
lean_inc_ref(v_a_1079_);
v___x_1086_ = lean_infer_type(v_a_1085_, v_a_1079_, v_a_1080_, v_a_1081_, v_a_1082_);
if (lean_obj_tag(v___x_1086_) == 0)
{
lean_object* v_a_1087_; uint8_t v___x_1088_; lean_object* v___x_1089_; 
v_a_1087_ = lean_ctor_get(v___x_1086_, 0);
lean_inc(v_a_1087_);
lean_dec_ref_known(v___x_1086_, 1);
v___x_1088_ = 0;
v___x_1089_ = l_Lean_Meta_forallMetaTelescope(v_a_1087_, v___x_1088_, v_a_1079_, v_a_1080_, v_a_1081_, v_a_1082_);
if (lean_obj_tag(v___x_1089_) == 0)
{
lean_object* v_a_1090_; lean_object* v___x_1092_; uint8_t v_isShared_1093_; uint8_t v_isSharedCheck_1149_; 
v_a_1090_ = lean_ctor_get(v___x_1089_, 0);
v_isSharedCheck_1149_ = !lean_is_exclusive(v___x_1089_);
if (v_isSharedCheck_1149_ == 0)
{
v___x_1092_ = v___x_1089_;
v_isShared_1093_ = v_isSharedCheck_1149_;
goto v_resetjp_1091_;
}
else
{
lean_inc(v_a_1090_);
lean_dec(v___x_1089_);
v___x_1092_ = lean_box(0);
v_isShared_1093_ = v_isSharedCheck_1149_;
goto v_resetjp_1091_;
}
v_resetjp_1091_:
{
lean_object* v_fst_1094_; lean_object* v_snd_1095_; lean_object* v___x_1097_; uint8_t v_isShared_1098_; uint8_t v_isSharedCheck_1148_; 
v_fst_1094_ = lean_ctor_get(v_a_1090_, 0);
v_snd_1095_ = lean_ctor_get(v_a_1090_, 1);
v_isSharedCheck_1148_ = !lean_is_exclusive(v_a_1090_);
if (v_isSharedCheck_1148_ == 0)
{
v___x_1097_ = v_a_1090_;
v_isShared_1098_ = v_isSharedCheck_1148_;
goto v_resetjp_1096_;
}
else
{
lean_inc(v_snd_1095_);
lean_inc(v_fst_1094_);
lean_dec(v_a_1090_);
v___x_1097_ = lean_box(0);
v_isShared_1098_ = v_isSharedCheck_1148_;
goto v_resetjp_1096_;
}
v_resetjp_1096_:
{
lean_object* v_snd_1104_; lean_object* v___x_1106_; uint8_t v_isShared_1107_; uint8_t v_isSharedCheck_1146_; 
v_snd_1104_ = lean_ctor_get(v_snd_1095_, 1);
v_isSharedCheck_1146_ = !lean_is_exclusive(v_snd_1095_);
if (v_isSharedCheck_1146_ == 0)
{
lean_object* v_unused_1147_; 
v_unused_1147_ = lean_ctor_get(v_snd_1095_, 0);
lean_dec(v_unused_1147_);
v___x_1106_ = v_snd_1095_;
v_isShared_1107_ = v_isSharedCheck_1146_;
goto v_resetjp_1105_;
}
else
{
lean_inc(v_snd_1104_);
lean_dec(v_snd_1095_);
v___x_1106_ = lean_box(0);
v_isShared_1107_ = v_isSharedCheck_1146_;
goto v_resetjp_1105_;
}
v___jp_1099_:
{
lean_object* v___x_1100_; lean_object* v___x_1102_; 
v___x_1100_ = l_Lean_mkAppN(v_a_1085_, v_fst_1094_);
lean_dec(v_fst_1094_);
if (v_isShared_1093_ == 0)
{
lean_ctor_set(v___x_1092_, 0, v___x_1100_);
v___x_1102_ = v___x_1092_;
goto v_reusejp_1101_;
}
else
{
lean_object* v_reuseFailAlloc_1103_; 
v_reuseFailAlloc_1103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1103_, 0, v___x_1100_);
v___x_1102_ = v_reuseFailAlloc_1103_;
goto v_reusejp_1101_;
}
v_reusejp_1101_:
{
return v___x_1102_;
}
}
v_resetjp_1105_:
{
lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; 
v___x_1108_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__2___closed__2));
v___x_1109_ = lean_unsigned_to_nat(2u);
v___x_1110_ = lean_mk_empty_array_with_capacity(v___x_1109_);
v___x_1111_ = lean_array_push(v___x_1110_, v_pre_1077_);
v___x_1112_ = lean_array_push(v___x_1111_, v_opAs_1076_);
v___x_1113_ = l_Lean_Meta_mkAppM(v___x_1108_, v___x_1112_, v_a_1079_, v_a_1080_, v_a_1081_, v_a_1082_);
if (lean_obj_tag(v___x_1113_) == 0)
{
lean_object* v_a_1114_; lean_object* v___x_1115_; 
v_a_1114_ = lean_ctor_get(v___x_1113_, 0);
lean_inc_n(v_a_1114_, 2);
lean_dec_ref_known(v___x_1113_, 1);
v___x_1115_ = l_Lean_Meta_isExprDefEq(v_snd_1104_, v_a_1114_, v_a_1079_, v_a_1080_, v_a_1081_, v_a_1082_);
if (lean_obj_tag(v___x_1115_) == 0)
{
lean_object* v_a_1116_; uint8_t v___x_1117_; 
v_a_1116_ = lean_ctor_get(v___x_1115_, 0);
lean_inc(v_a_1116_);
lean_dec_ref_known(v___x_1115_, 1);
v___x_1117_ = lean_unbox(v_a_1116_);
lean_dec(v_a_1116_);
if (v___x_1117_ == 0)
{
lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1121_; 
v___x_1118_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__2___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__2___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__2___closed__4);
v___x_1119_ = l_Lean_MessageData_ofName(v_introThm_1075_);
if (v_isShared_1107_ == 0)
{
lean_ctor_set_tag(v___x_1106_, 7);
lean_ctor_set(v___x_1106_, 1, v___x_1119_);
lean_ctor_set(v___x_1106_, 0, v___x_1118_);
v___x_1121_ = v___x_1106_;
goto v_reusejp_1120_;
}
else
{
lean_object* v_reuseFailAlloc_1137_; 
v_reuseFailAlloc_1137_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1137_, 0, v___x_1118_);
lean_ctor_set(v_reuseFailAlloc_1137_, 1, v___x_1119_);
v___x_1121_ = v_reuseFailAlloc_1137_;
goto v_reusejp_1120_;
}
v_reusejp_1120_:
{
lean_object* v___x_1122_; lean_object* v___x_1124_; 
v___x_1122_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply___closed__1, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply___closed__1_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply___closed__1);
if (v_isShared_1098_ == 0)
{
lean_ctor_set_tag(v___x_1097_, 7);
lean_ctor_set(v___x_1097_, 1, v___x_1122_);
lean_ctor_set(v___x_1097_, 0, v___x_1121_);
v___x_1124_ = v___x_1097_;
goto v_reusejp_1123_;
}
else
{
lean_object* v_reuseFailAlloc_1136_; 
v_reuseFailAlloc_1136_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1136_, 0, v___x_1121_);
lean_ctor_set(v_reuseFailAlloc_1136_, 1, v___x_1122_);
v___x_1124_ = v_reuseFailAlloc_1136_;
goto v_reusejp_1123_;
}
v_reusejp_1123_:
{
lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; 
v___x_1125_ = l_Lean_MessageData_ofExpr(v_a_1114_);
v___x_1126_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1126_, 0, v___x_1124_);
lean_ctor_set(v___x_1126_, 1, v___x_1125_);
v___x_1127_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__1___redArg(v___x_1126_, v_a_1079_, v_a_1080_, v_a_1081_, v_a_1082_);
if (lean_obj_tag(v___x_1127_) == 0)
{
lean_dec_ref_known(v___x_1127_, 1);
goto v___jp_1099_;
}
else
{
lean_object* v_a_1128_; lean_object* v___x_1130_; uint8_t v_isShared_1131_; uint8_t v_isSharedCheck_1135_; 
lean_dec(v_fst_1094_);
lean_del_object(v___x_1092_);
lean_dec(v_a_1085_);
v_a_1128_ = lean_ctor_get(v___x_1127_, 0);
v_isSharedCheck_1135_ = !lean_is_exclusive(v___x_1127_);
if (v_isSharedCheck_1135_ == 0)
{
v___x_1130_ = v___x_1127_;
v_isShared_1131_ = v_isSharedCheck_1135_;
goto v_resetjp_1129_;
}
else
{
lean_inc(v_a_1128_);
lean_dec(v___x_1127_);
v___x_1130_ = lean_box(0);
v_isShared_1131_ = v_isSharedCheck_1135_;
goto v_resetjp_1129_;
}
v_resetjp_1129_:
{
lean_object* v___x_1133_; 
if (v_isShared_1131_ == 0)
{
v___x_1133_ = v___x_1130_;
goto v_reusejp_1132_;
}
else
{
lean_object* v_reuseFailAlloc_1134_; 
v_reuseFailAlloc_1134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1134_, 0, v_a_1128_);
v___x_1133_ = v_reuseFailAlloc_1134_;
goto v_reusejp_1132_;
}
v_reusejp_1132_:
{
return v___x_1133_;
}
}
}
}
}
}
else
{
lean_dec(v_a_1114_);
lean_del_object(v___x_1106_);
lean_del_object(v___x_1097_);
lean_dec(v_introThm_1075_);
goto v___jp_1099_;
}
}
else
{
lean_object* v_a_1138_; lean_object* v___x_1140_; uint8_t v_isShared_1141_; uint8_t v_isSharedCheck_1145_; 
lean_dec(v_a_1114_);
lean_del_object(v___x_1106_);
lean_del_object(v___x_1097_);
lean_dec(v_fst_1094_);
lean_del_object(v___x_1092_);
lean_dec(v_a_1085_);
lean_dec(v_introThm_1075_);
v_a_1138_ = lean_ctor_get(v___x_1115_, 0);
v_isSharedCheck_1145_ = !lean_is_exclusive(v___x_1115_);
if (v_isSharedCheck_1145_ == 0)
{
v___x_1140_ = v___x_1115_;
v_isShared_1141_ = v_isSharedCheck_1145_;
goto v_resetjp_1139_;
}
else
{
lean_inc(v_a_1138_);
lean_dec(v___x_1115_);
v___x_1140_ = lean_box(0);
v_isShared_1141_ = v_isSharedCheck_1145_;
goto v_resetjp_1139_;
}
v_resetjp_1139_:
{
lean_object* v___x_1143_; 
if (v_isShared_1141_ == 0)
{
v___x_1143_ = v___x_1140_;
goto v_reusejp_1142_;
}
else
{
lean_object* v_reuseFailAlloc_1144_; 
v_reuseFailAlloc_1144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1144_, 0, v_a_1138_);
v___x_1143_ = v_reuseFailAlloc_1144_;
goto v_reusejp_1142_;
}
v_reusejp_1142_:
{
return v___x_1143_;
}
}
}
}
else
{
lean_del_object(v___x_1106_);
lean_dec(v_snd_1104_);
lean_del_object(v___x_1097_);
lean_dec(v_fst_1094_);
lean_del_object(v___x_1092_);
lean_dec(v_a_1085_);
lean_dec(v_introThm_1075_);
return v___x_1113_;
}
}
}
}
}
else
{
lean_object* v_a_1150_; lean_object* v___x_1152_; uint8_t v_isShared_1153_; uint8_t v_isSharedCheck_1157_; 
lean_dec(v_a_1085_);
lean_dec_ref(v_pre_1077_);
lean_dec_ref(v_opAs_1076_);
lean_dec(v_introThm_1075_);
v_a_1150_ = lean_ctor_get(v___x_1089_, 0);
v_isSharedCheck_1157_ = !lean_is_exclusive(v___x_1089_);
if (v_isSharedCheck_1157_ == 0)
{
v___x_1152_ = v___x_1089_;
v_isShared_1153_ = v_isSharedCheck_1157_;
goto v_resetjp_1151_;
}
else
{
lean_inc(v_a_1150_);
lean_dec(v___x_1089_);
v___x_1152_ = lean_box(0);
v_isShared_1153_ = v_isSharedCheck_1157_;
goto v_resetjp_1151_;
}
v_resetjp_1151_:
{
lean_object* v___x_1155_; 
if (v_isShared_1153_ == 0)
{
v___x_1155_ = v___x_1152_;
goto v_reusejp_1154_;
}
else
{
lean_object* v_reuseFailAlloc_1156_; 
v_reuseFailAlloc_1156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1156_, 0, v_a_1150_);
v___x_1155_ = v_reuseFailAlloc_1156_;
goto v_reusejp_1154_;
}
v_reusejp_1154_:
{
return v___x_1155_;
}
}
}
}
else
{
lean_dec(v_a_1085_);
lean_dec_ref(v_pre_1077_);
lean_dec_ref(v_opAs_1076_);
lean_dec(v_introThm_1075_);
return v___x_1086_;
}
}
else
{
lean_dec_ref(v_pre_1077_);
lean_dec_ref(v_opAs_1076_);
lean_dec(v_introThm_1075_);
return v___x_1084_;
}
}
else
{
lean_object* v___x_1158_; 
lean_inc(v_a_1082_);
lean_inc_ref(v_a_1081_);
lean_inc(v_a_1080_);
lean_inc_ref(v_a_1079_);
lean_inc_ref(v_pre_1077_);
v___x_1158_ = lean_infer_type(v_pre_1077_, v_a_1079_, v_a_1080_, v_a_1081_, v_a_1082_);
if (lean_obj_tag(v___x_1158_) == 0)
{
lean_object* v_a_1159_; lean_object* v___x_1160_; lean_object* v_s_1161_; lean_object* v___x_1162_; 
v_a_1159_ = lean_ctor_get(v___x_1158_, 0);
lean_inc(v_a_1159_);
lean_dec_ref_known(v___x_1158_, 1);
v___x_1160_ = l_Lean_instInhabitedExpr;
v_s_1161_ = l_List_getLast_x21___redArg(v___x_1160_, v_ss_1078_);
lean_inc(v_a_1082_);
lean_inc_ref(v_a_1081_);
lean_inc(v_a_1080_);
lean_inc_ref(v_a_1079_);
lean_inc(v_s_1161_);
v___x_1162_ = lean_infer_type(v_s_1161_, v_a_1079_, v_a_1080_, v_a_1081_, v_a_1082_);
if (lean_obj_tag(v___x_1162_) == 0)
{
lean_object* v_a_1163_; lean_object* v___f_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; 
v_a_1163_ = lean_ctor_get(v___x_1162_, 0);
lean_inc(v_a_1163_);
lean_dec_ref_known(v___x_1162_, 1);
lean_inc_ref(v_pre_1077_);
lean_inc(v_s_1161_);
v___f_1164_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply___lam__0___boxed), 9, 3);
lean_closure_set(v___f_1164_, 0, v_s_1161_);
lean_closure_set(v___f_1164_, 1, v_a_1159_);
lean_closure_set(v___f_1164_, 2, v_pre_1077_);
v___x_1165_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply___closed__3));
v___x_1166_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply_spec__0___redArg(v___x_1165_, v_a_1163_, v___f_1164_, v_a_1079_, v_a_1080_, v_a_1081_, v_a_1082_);
if (lean_obj_tag(v___x_1166_) == 0)
{
lean_object* v_a_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v_init_1170_; lean_object* v___x_1171_; lean_object* v_Q_1172_; lean_object* v___x_1173_; 
v_a_1167_ = lean_ctor_get(v___x_1166_, 0);
lean_inc(v_a_1167_);
lean_dec_ref_known(v___x_1166_, 1);
v___x_1168_ = lean_array_mk(v_ss_1078_);
v___x_1169_ = lean_array_pop(v___x_1168_);
v_init_1170_ = lean_array_to_list(v___x_1169_);
lean_inc(v_init_1170_);
v___x_1171_ = lean_array_mk(v_init_1170_);
lean_inc_ref(v_opAs_1076_);
v_Q_1172_ = l_Lean_mkAppN(v_opAs_1076_, v___x_1171_);
lean_dec_ref(v___x_1171_);
v___x_1173_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply(v_introThm_1075_, v_opAs_1076_, v_a_1167_, v_init_1170_, v_a_1079_, v_a_1080_, v_a_1081_, v_a_1082_);
if (lean_obj_tag(v___x_1173_) == 0)
{
lean_object* v_a_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; 
v_a_1174_ = lean_ctor_get(v___x_1173_, 0);
lean_inc(v_a_1174_);
lean_dec_ref_known(v___x_1173_, 1);
v___x_1175_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply___closed__5));
v___x_1176_ = lean_unsigned_to_nat(4u);
v___x_1177_ = lean_mk_empty_array_with_capacity(v___x_1176_);
v___x_1178_ = lean_array_push(v___x_1177_, v_s_1161_);
v___x_1179_ = lean_array_push(v___x_1178_, v_pre_1077_);
v___x_1180_ = lean_array_push(v___x_1179_, v_Q_1172_);
v___x_1181_ = lean_array_push(v___x_1180_, v_a_1174_);
v___x_1182_ = l_Lean_Meta_mkAppM(v___x_1175_, v___x_1181_, v_a_1079_, v_a_1080_, v_a_1081_, v_a_1082_);
return v___x_1182_;
}
else
{
lean_dec_ref(v_Q_1172_);
lean_dec(v_s_1161_);
lean_dec_ref(v_pre_1077_);
return v___x_1173_;
}
}
else
{
lean_dec(v_s_1161_);
lean_dec(v_ss_1078_);
lean_dec_ref(v_pre_1077_);
lean_dec_ref(v_opAs_1076_);
lean_dec(v_introThm_1075_);
return v___x_1166_;
}
}
else
{
lean_dec(v_s_1161_);
lean_dec(v_a_1159_);
lean_dec(v_ss_1078_);
lean_dec_ref(v_pre_1077_);
lean_dec_ref(v_opAs_1076_);
lean_dec(v_introThm_1075_);
return v___x_1162_;
}
}
else
{
lean_dec(v_ss_1078_);
lean_dec_ref(v_pre_1077_);
lean_dec_ref(v_opAs_1076_);
lean_dec(v_introThm_1075_);
return v___x_1158_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply___boxed(lean_object* v_introThm_1183_, lean_object* v_opAs_1184_, lean_object* v_pre_1185_, lean_object* v_ss_1186_, lean_object* v_a_1187_, lean_object* v_a_1188_, lean_object* v_a_1189_, lean_object* v_a_1190_, lean_object* v_a_1191_){
_start:
{
lean_object* v_res_1192_; 
v_res_1192_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply(v_introThm_1183_, v_opAs_1184_, v_pre_1185_, v_ss_1186_, v_a_1187_, v_a_1188_, v_a_1189_, v_a_1190_);
lean_dec(v_a_1190_);
lean_dec_ref(v_a_1189_);
lean_dec(v_a_1188_);
lean_dec_ref(v_a_1187_);
return v_res_1192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply_spec__0_spec__0(lean_object* v_00_u03b1_1193_, lean_object* v_name_1194_, uint8_t v_bi_1195_, lean_object* v_type_1196_, lean_object* v_k_1197_, uint8_t v_kind_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_){
_start:
{
lean_object* v___x_1204_; 
v___x_1204_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply_spec__0_spec__0___redArg(v_name_1194_, v_bi_1195_, v_type_1196_, v_k_1197_, v_kind_1198_, v___y_1199_, v___y_1200_, v___y_1201_, v___y_1202_);
return v___x_1204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1205_, lean_object* v_name_1206_, lean_object* v_bi_1207_, lean_object* v_type_1208_, lean_object* v_k_1209_, lean_object* v_kind_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_){
_start:
{
uint8_t v_bi_boxed_1216_; uint8_t v_kind_boxed_1217_; lean_object* v_res_1218_; 
v_bi_boxed_1216_ = lean_unbox(v_bi_1207_);
v_kind_boxed_1217_ = lean_unbox(v_kind_1210_);
v_res_1218_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply_spec__0_spec__0(v_00_u03b1_1205_, v_name_1206_, v_bi_boxed_1216_, v_type_1208_, v_k_1209_, v_kind_boxed_1217_, v___y_1211_, v___y_1212_, v___y_1213_, v___y_1214_);
lean_dec(v___y_1214_);
lean_dec_ref(v___y_1213_);
lean_dec(v___y_1212_);
lean_dec_ref(v___y_1211_);
return v_res_1218_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply_spec__0(lean_object* v_00_u03b1_1219_, lean_object* v_name_1220_, lean_object* v_type_1221_, lean_object* v_k_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_){
_start:
{
lean_object* v___x_1228_; 
v___x_1228_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply_spec__0___redArg(v_name_1220_, v_type_1221_, v_k_1222_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_);
return v___x_1228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply_spec__0___boxed(lean_object* v_00_u03b1_1229_, lean_object* v_name_1230_, lean_object* v_type_1231_, lean_object* v_k_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_){
_start:
{
lean_object* v_res_1238_; 
v_res_1238_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply_spec__0(v_00_u03b1_1229_, v_name_1230_, v_type_1231_, v_k_1232_, v___y_1233_, v___y_1234_, v___y_1235_, v___y_1236_);
lean_dec(v___y_1236_);
lean_dec_ref(v___y_1235_);
lean_dec(v___y_1234_);
lean_dec_ref(v___y_1233_);
return v_res_1238_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__1_spec__1___redArg(lean_object* v_a_1239_, lean_object* v_x_1240_){
_start:
{
if (lean_obj_tag(v_x_1240_) == 0)
{
lean_object* v___x_1241_; 
v___x_1241_ = lean_box(0);
return v___x_1241_;
}
else
{
lean_object* v_key_1242_; lean_object* v_value_1243_; lean_object* v_tail_1244_; uint8_t v___x_1245_; 
v_key_1242_ = lean_ctor_get(v_x_1240_, 0);
v_value_1243_ = lean_ctor_get(v_x_1240_, 1);
v_tail_1244_ = lean_ctor_get(v_x_1240_, 2);
v___x_1245_ = lean_name_eq(v_key_1242_, v_a_1239_);
if (v___x_1245_ == 0)
{
v_x_1240_ = v_tail_1244_;
goto _start;
}
else
{
lean_object* v___x_1247_; 
lean_inc(v_value_1243_);
v___x_1247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1247_, 0, v_value_1243_);
return v___x_1247_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__1_spec__1___redArg___boxed(lean_object* v_a_1248_, lean_object* v_x_1249_){
_start:
{
lean_object* v_res_1250_; 
v_res_1250_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__1_spec__1___redArg(v_a_1248_, v_x_1249_);
lean_dec(v_x_1249_);
lean_dec(v_a_1248_);
return v_res_1250_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__1___redArg(lean_object* v_m_1251_, lean_object* v_a_1252_){
_start:
{
lean_object* v_buckets_1253_; lean_object* v___x_1254_; uint64_t v___y_1256_; 
v_buckets_1253_ = lean_ctor_get(v_m_1251_, 1);
v___x_1254_ = lean_array_get_size(v_buckets_1253_);
if (lean_obj_tag(v_a_1252_) == 0)
{
uint64_t v___x_1270_; 
v___x_1270_ = lean_uint64_once(&l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable_spec__0_spec__1_spec__2_spec__4___redArg___closed__0, &l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable_spec__0_spec__1_spec__2_spec__4___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable_spec__0_spec__1_spec__2_spec__4___redArg___closed__0);
v___y_1256_ = v___x_1270_;
goto v___jp_1255_;
}
else
{
uint64_t v_hash_1271_; 
v_hash_1271_ = lean_ctor_get_uint64(v_a_1252_, sizeof(void*)*2);
v___y_1256_ = v_hash_1271_;
goto v___jp_1255_;
}
v___jp_1255_:
{
uint64_t v___x_1257_; uint64_t v___x_1258_; uint64_t v_fold_1259_; uint64_t v___x_1260_; uint64_t v___x_1261_; uint64_t v___x_1262_; size_t v___x_1263_; size_t v___x_1264_; size_t v___x_1265_; size_t v___x_1266_; size_t v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; 
v___x_1257_ = 32ULL;
v___x_1258_ = lean_uint64_shift_right(v___y_1256_, v___x_1257_);
v_fold_1259_ = lean_uint64_xor(v___y_1256_, v___x_1258_);
v___x_1260_ = 16ULL;
v___x_1261_ = lean_uint64_shift_right(v_fold_1259_, v___x_1260_);
v___x_1262_ = lean_uint64_xor(v_fold_1259_, v___x_1261_);
v___x_1263_ = lean_uint64_to_usize(v___x_1262_);
v___x_1264_ = lean_usize_of_nat(v___x_1254_);
v___x_1265_ = ((size_t)1ULL);
v___x_1266_ = lean_usize_sub(v___x_1264_, v___x_1265_);
v___x_1267_ = lean_usize_land(v___x_1263_, v___x_1266_);
v___x_1268_ = lean_array_uget_borrowed(v_buckets_1253_, v___x_1267_);
v___x_1269_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__1_spec__1___redArg(v_a_1252_, v___x_1268_);
return v___x_1269_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__1___redArg___boxed(lean_object* v_m_1272_, lean_object* v_a_1273_){
_start:
{
lean_object* v_res_1274_; 
v_res_1274_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__1___redArg(v_m_1272_, v_a_1273_);
lean_dec(v_a_1273_);
lean_dec_ref(v_m_1272_);
return v_res_1274_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__0___redArg(size_t v_sz_1275_, size_t v_i_1276_, lean_object* v_bs_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_){
_start:
{
uint8_t v___x_1283_; 
v___x_1283_ = lean_usize_dec_lt(v_i_1276_, v_sz_1275_);
if (v___x_1283_ == 0)
{
lean_object* v___x_1284_; 
v___x_1284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1284_, 0, v_bs_1277_);
return v___x_1284_;
}
else
{
lean_object* v_v_1285_; lean_object* v___x_1286_; lean_object* v_bs_x27_1287_; lean_object* v___y_1289_; lean_object* v___x_1303_; 
v_v_1285_ = lean_array_uget(v_bs_1277_, v_i_1276_);
v___x_1286_ = lean_unsigned_to_nat(0u);
v_bs_x27_1287_ = lean_array_uset(v_bs_1277_, v_i_1276_, v___x_1286_);
lean_inc(v___y_1281_);
lean_inc_ref(v___y_1280_);
lean_inc(v___y_1279_);
lean_inc_ref(v___y_1278_);
v___x_1303_ = lean_infer_type(v_v_1285_, v___y_1278_, v___y_1279_, v___y_1280_, v___y_1281_);
if (lean_obj_tag(v___x_1303_) == 0)
{
lean_object* v_a_1304_; lean_object* v___x_1306_; uint8_t v_isShared_1307_; uint8_t v_isSharedCheck_1314_; 
v_a_1304_ = lean_ctor_get(v___x_1303_, 0);
v_isSharedCheck_1314_ = !lean_is_exclusive(v___x_1303_);
if (v_isSharedCheck_1314_ == 0)
{
v___x_1306_ = v___x_1303_;
v_isShared_1307_ = v_isSharedCheck_1314_;
goto v_resetjp_1305_;
}
else
{
lean_inc(v_a_1304_);
lean_dec(v___x_1303_);
v___x_1306_ = lean_box(0);
v_isShared_1307_ = v_isSharedCheck_1314_;
goto v_resetjp_1305_;
}
v_resetjp_1305_:
{
lean_object* v___x_1309_; 
if (v_isShared_1307_ == 0)
{
lean_ctor_set_tag(v___x_1306_, 1);
v___x_1309_ = v___x_1306_;
goto v_reusejp_1308_;
}
else
{
lean_object* v_reuseFailAlloc_1313_; 
v_reuseFailAlloc_1313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1313_, 0, v_a_1304_);
v___x_1309_ = v_reuseFailAlloc_1313_;
goto v_reusejp_1308_;
}
v_reusejp_1308_:
{
uint8_t v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; 
v___x_1310_ = 0;
v___x_1311_ = lean_box(0);
v___x_1312_ = l_Lean_Meta_mkFreshExprMVar(v___x_1309_, v___x_1310_, v___x_1311_, v___y_1278_, v___y_1279_, v___y_1280_, v___y_1281_);
v___y_1289_ = v___x_1312_;
goto v___jp_1288_;
}
}
}
else
{
v___y_1289_ = v___x_1303_;
goto v___jp_1288_;
}
v___jp_1288_:
{
if (lean_obj_tag(v___y_1289_) == 0)
{
lean_object* v_a_1290_; size_t v___x_1291_; size_t v___x_1292_; lean_object* v___x_1293_; 
v_a_1290_ = lean_ctor_get(v___y_1289_, 0);
lean_inc(v_a_1290_);
lean_dec_ref_known(v___y_1289_, 1);
v___x_1291_ = ((size_t)1ULL);
v___x_1292_ = lean_usize_add(v_i_1276_, v___x_1291_);
v___x_1293_ = lean_array_uset(v_bs_x27_1287_, v_i_1276_, v_a_1290_);
v_i_1276_ = v___x_1292_;
v_bs_1277_ = v___x_1293_;
goto _start;
}
else
{
lean_object* v_a_1295_; lean_object* v___x_1297_; uint8_t v_isShared_1298_; uint8_t v_isSharedCheck_1302_; 
lean_dec_ref(v_bs_x27_1287_);
v_a_1295_ = lean_ctor_get(v___y_1289_, 0);
v_isSharedCheck_1302_ = !lean_is_exclusive(v___y_1289_);
if (v_isSharedCheck_1302_ == 0)
{
v___x_1297_ = v___y_1289_;
v_isShared_1298_ = v_isSharedCheck_1302_;
goto v_resetjp_1296_;
}
else
{
lean_inc(v_a_1295_);
lean_dec(v___y_1289_);
v___x_1297_ = lean_box(0);
v_isShared_1298_ = v_isSharedCheck_1302_;
goto v_resetjp_1296_;
}
v_resetjp_1296_:
{
lean_object* v___x_1300_; 
if (v_isShared_1298_ == 0)
{
v___x_1300_ = v___x_1297_;
goto v_reusejp_1299_;
}
else
{
lean_object* v_reuseFailAlloc_1301_; 
v_reuseFailAlloc_1301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1301_, 0, v_a_1295_);
v___x_1300_ = v_reuseFailAlloc_1301_;
goto v_reusejp_1299_;
}
v_reusejp_1299_:
{
return v___x_1300_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__0___redArg___boxed(lean_object* v_sz_1315_, lean_object* v_i_1316_, lean_object* v_bs_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_){
_start:
{
size_t v_sz_boxed_1323_; size_t v_i_boxed_1324_; lean_object* v_res_1325_; 
v_sz_boxed_1323_ = lean_unbox_usize(v_sz_1315_);
lean_dec(v_sz_1315_);
v_i_boxed_1324_ = lean_unbox_usize(v_i_1316_);
lean_dec(v_i_1316_);
v_res_1325_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__0___redArg(v_sz_boxed_1323_, v_i_boxed_1324_, v_bs_1317_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_);
lean_dec(v___y_1321_);
lean_dec_ref(v___y_1320_);
lean_dec(v___y_1319_);
lean_dec_ref(v___y_1318_);
return v_res_1325_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__2___closed__4(void){
_start:
{
lean_object* v___x_1332_; lean_object* v___x_1333_; 
v___x_1332_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__2___closed__3));
v___x_1333_ = l_Lean_stringToMessageData(v___x_1332_);
return v___x_1333_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__2___closed__6(void){
_start:
{
lean_object* v___x_1335_; lean_object* v___x_1336_; 
v___x_1335_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__2___closed__5));
v___x_1336_ = l_Lean_stringToMessageData(v___x_1335_);
return v___x_1336_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__2___closed__7(void){
_start:
{
lean_object* v___x_1337_; lean_object* v_dummy_1338_; 
v___x_1337_ = lean_box(0);
v_dummy_1338_ = l_Lean_Expr_sort___override(v___x_1337_);
return v_dummy_1338_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__2(lean_object* v_op_1339_, lean_object* v___y_1340_, lean_object* v_a_1341_, lean_object* v_x_1342_, lean_object* v_x_1343_, lean_object* v_x_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_){
_start:
{
lean_object* v_prf_1353_; lean_object* v___y_1354_; lean_object* v___y_1355_; lean_object* v___y_1356_; lean_object* v___y_1357_; 
if (lean_obj_tag(v_x_1342_) == 5)
{
lean_object* v_fn_1374_; lean_object* v_arg_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; 
v_fn_1374_ = lean_ctor_get(v_x_1342_, 0);
lean_inc_ref(v_fn_1374_);
v_arg_1375_ = lean_ctor_get(v_x_1342_, 1);
lean_inc_ref(v_arg_1375_);
lean_dec_ref_known(v_x_1342_, 2);
v___x_1376_ = lean_array_set(v_x_1343_, v_x_1344_, v_arg_1375_);
v___x_1377_ = lean_unsigned_to_nat(1u);
v___x_1378_ = lean_nat_sub(v_x_1344_, v___x_1377_);
lean_dec(v_x_1344_);
v_x_1342_ = v_fn_1374_;
v_x_1343_ = v___x_1376_;
v_x_1344_ = v___x_1378_;
goto _start;
}
else
{
lean_object* v_head_1380_; lean_object* v_numConst_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; size_t v_sz_1384_; size_t v___x_1385_; lean_object* v___x_1386_; 
lean_dec(v_x_1344_);
v_head_1380_ = lean_ctor_get(v_op_1339_, 0);
lean_inc(v_head_1380_);
v_numConst_1381_ = lean_ctor_get(v_op_1339_, 1);
lean_inc_n(v_numConst_1381_, 2);
lean_dec_ref(v_op_1339_);
v___x_1382_ = lean_array_get_size(v_x_1343_);
v___x_1383_ = l_Array_extract___redArg(v_x_1343_, v_numConst_1381_, v___x_1382_);
v_sz_1384_ = lean_array_size(v___x_1383_);
v___x_1385_ = ((size_t)0ULL);
v___x_1386_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__0___redArg(v_sz_1384_, v___x_1385_, v___x_1383_, v___y_1347_, v___y_1348_, v___y_1349_, v___y_1350_);
if (lean_obj_tag(v___x_1386_) == 0)
{
lean_object* v_a_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; 
v_a_1387_ = lean_ctor_get(v___x_1386_, 0);
lean_inc(v_a_1387_);
lean_dec_ref_known(v___x_1386_, 1);
v___x_1388_ = lean_unsigned_to_nat(0u);
v___x_1389_ = l_Array_extract___redArg(v_x_1343_, v___x_1388_, v_numConst_1381_);
lean_dec_ref(v_x_1343_);
v___x_1390_ = l_Array_append___redArg(v___x_1389_, v_a_1387_);
lean_dec(v_a_1387_);
v___x_1391_ = l_Lean_mkAppN(v_x_1342_, v___x_1390_);
lean_dec_ref(v___x_1390_);
v___x_1392_ = lean_unsigned_to_nat(256u);
lean_inc_ref(v___x_1391_);
v___x_1393_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp(v___y_1340_, v___x_1391_, v___x_1392_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_, v___y_1349_, v___y_1350_);
if (lean_obj_tag(v___x_1393_) == 0)
{
lean_object* v_a_1394_; lean_object* v_fst_1395_; lean_object* v_snd_1396_; lean_object* v___x_1398_; uint8_t v_isShared_1399_; uint8_t v_isSharedCheck_1568_; 
v_a_1394_ = lean_ctor_get(v___x_1393_, 0);
lean_inc(v_a_1394_);
lean_dec_ref_known(v___x_1393_, 1);
v_fst_1395_ = lean_ctor_get(v_a_1394_, 0);
v_snd_1396_ = lean_ctor_get(v_a_1394_, 1);
v_isSharedCheck_1568_ = !lean_is_exclusive(v_a_1394_);
if (v_isSharedCheck_1568_ == 0)
{
v___x_1398_ = v_a_1394_;
v_isShared_1399_ = v_isSharedCheck_1568_;
goto v_resetjp_1397_;
}
else
{
lean_inc(v_snd_1396_);
lean_inc(v_fst_1395_);
lean_dec(v_a_1394_);
v___x_1398_ = lean_box(0);
v_isShared_1399_ = v_isSharedCheck_1568_;
goto v_resetjp_1397_;
}
v_resetjp_1397_:
{
lean_object* v___x_1400_; 
lean_inc(v___y_1350_);
lean_inc_ref(v___y_1349_);
lean_inc(v___y_1348_);
lean_inc_ref(v___y_1347_);
v___x_1400_ = lean_infer_type(v___x_1391_, v___y_1347_, v___y_1348_, v___y_1349_, v___y_1350_);
if (lean_obj_tag(v___x_1400_) == 0)
{
lean_object* v_a_1401_; lean_object* v___x_1402_; uint8_t v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; 
v_a_1401_ = lean_ctor_get(v___x_1400_, 0);
lean_inc(v_a_1401_);
lean_dec_ref_known(v___x_1400_, 1);
v___x_1402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1402_, 0, v_a_1401_);
v___x_1403_ = 0;
v___x_1404_ = lean_box(0);
v___x_1405_ = l_Lean_Meta_mkFreshExprMVar(v___x_1402_, v___x_1403_, v___x_1404_, v___y_1347_, v___y_1348_, v___y_1349_, v___y_1350_);
if (lean_obj_tag(v___x_1405_) == 0)
{
lean_object* v_a_1406_; lean_object* v___y_1408_; lean_object* v___y_1409_; lean_object* v___y_1410_; lean_object* v___y_1411_; lean_object* v___y_1412_; lean_object* v___y_1413_; lean_object* v_a_1414_; lean_object* v___y_1462_; lean_object* v_eqProof_1463_; lean_object* v___y_1464_; lean_object* v___y_1465_; lean_object* v___y_1466_; lean_object* v___y_1467_; lean_object* v___x_1495_; lean_object* v___y_1497_; lean_object* v___x_1550_; 
v_a_1406_ = lean_ctor_get(v___x_1405_, 0);
lean_inc(v_a_1406_);
lean_dec_ref_known(v___x_1405_, 1);
v___x_1495_ = l_Lean_Expr_getAppFn(v_fst_1395_);
v___x_1550_ = l_Lean_Expr_constName_x3f(v___x_1495_);
if (lean_obj_tag(v___x_1550_) == 0)
{
v___y_1497_ = v___x_1404_;
goto v___jp_1496_;
}
else
{
lean_object* v_val_1551_; 
v_val_1551_ = lean_ctor_get(v___x_1550_, 0);
lean_inc(v_val_1551_);
lean_dec_ref_known(v___x_1550_, 1);
v___y_1497_ = v_val_1551_;
goto v___jp_1496_;
}
v___jp_1407_:
{
lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; 
v___x_1415_ = lean_unsigned_to_nat(1u);
v___x_1416_ = lean_mk_empty_array_with_capacity(v___x_1415_);
lean_inc_ref(v___x_1416_);
v___x_1417_ = lean_array_push(v___x_1416_, v_a_1406_);
v___x_1418_ = l_Lean_Meta_mkAppM(v___y_1411_, v___x_1417_, v___y_1413_, v___y_1409_, v___y_1408_, v___y_1410_);
if (lean_obj_tag(v___x_1418_) == 0)
{
lean_object* v_a_1419_; lean_object* v___x_1420_; 
v_a_1419_ = lean_ctor_get(v___x_1418_, 0);
lean_inc(v_a_1419_);
lean_dec_ref_known(v___x_1418_, 1);
v___x_1420_ = l_Lean_Meta_mkCongrArg(v_a_1419_, v___y_1412_, v___y_1413_, v___y_1409_, v___y_1408_, v___y_1410_);
if (lean_obj_tag(v___x_1420_) == 0)
{
lean_object* v_a_1421_; lean_object* v___x_1422_; 
v_a_1421_ = lean_ctor_get(v___x_1420_, 0);
lean_inc(v_a_1421_);
lean_dec_ref_known(v___x_1420_, 1);
v___x_1422_ = l_Lean_Meta_mkEqSymm(v_a_1421_, v___y_1413_, v___y_1409_, v___y_1408_, v___y_1410_);
if (lean_obj_tag(v___x_1422_) == 0)
{
lean_object* v_a_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; 
v_a_1423_ = lean_ctor_get(v___x_1422_, 0);
lean_inc(v_a_1423_);
lean_dec_ref_known(v___x_1422_, 1);
v___x_1424_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__2___closed__2));
v___x_1425_ = lean_array_push(v___x_1416_, v_a_1423_);
v___x_1426_ = l_Lean_Meta_mkAppM(v___x_1424_, v___x_1425_, v___y_1413_, v___y_1409_, v___y_1408_, v___y_1410_);
if (lean_obj_tag(v___x_1426_) == 0)
{
lean_object* v_a_1427_; lean_object* v___x_1428_; 
v_a_1427_ = lean_ctor_get(v___x_1426_, 0);
lean_inc(v_a_1427_);
lean_dec_ref_known(v___x_1426_, 1);
v___x_1428_ = l_Lean_Expr_app___override(v_a_1427_, v_a_1414_);
v_prf_1353_ = v___x_1428_;
v___y_1354_ = v___y_1413_;
v___y_1355_ = v___y_1409_;
v___y_1356_ = v___y_1408_;
v___y_1357_ = v___y_1410_;
goto v___jp_1352_;
}
else
{
lean_object* v_a_1429_; lean_object* v___x_1431_; uint8_t v_isShared_1432_; uint8_t v_isSharedCheck_1436_; 
lean_dec_ref(v_a_1414_);
v_a_1429_ = lean_ctor_get(v___x_1426_, 0);
v_isSharedCheck_1436_ = !lean_is_exclusive(v___x_1426_);
if (v_isSharedCheck_1436_ == 0)
{
v___x_1431_ = v___x_1426_;
v_isShared_1432_ = v_isSharedCheck_1436_;
goto v_resetjp_1430_;
}
else
{
lean_inc(v_a_1429_);
lean_dec(v___x_1426_);
v___x_1431_ = lean_box(0);
v_isShared_1432_ = v_isSharedCheck_1436_;
goto v_resetjp_1430_;
}
v_resetjp_1430_:
{
lean_object* v___x_1434_; 
if (v_isShared_1432_ == 0)
{
v___x_1434_ = v___x_1431_;
goto v_reusejp_1433_;
}
else
{
lean_object* v_reuseFailAlloc_1435_; 
v_reuseFailAlloc_1435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1435_, 0, v_a_1429_);
v___x_1434_ = v_reuseFailAlloc_1435_;
goto v_reusejp_1433_;
}
v_reusejp_1433_:
{
return v___x_1434_;
}
}
}
}
else
{
lean_object* v_a_1437_; lean_object* v___x_1439_; uint8_t v_isShared_1440_; uint8_t v_isSharedCheck_1444_; 
lean_dec_ref(v___x_1416_);
lean_dec_ref(v_a_1414_);
v_a_1437_ = lean_ctor_get(v___x_1422_, 0);
v_isSharedCheck_1444_ = !lean_is_exclusive(v___x_1422_);
if (v_isSharedCheck_1444_ == 0)
{
v___x_1439_ = v___x_1422_;
v_isShared_1440_ = v_isSharedCheck_1444_;
goto v_resetjp_1438_;
}
else
{
lean_inc(v_a_1437_);
lean_dec(v___x_1422_);
v___x_1439_ = lean_box(0);
v_isShared_1440_ = v_isSharedCheck_1444_;
goto v_resetjp_1438_;
}
v_resetjp_1438_:
{
lean_object* v___x_1442_; 
if (v_isShared_1440_ == 0)
{
v___x_1442_ = v___x_1439_;
goto v_reusejp_1441_;
}
else
{
lean_object* v_reuseFailAlloc_1443_; 
v_reuseFailAlloc_1443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1443_, 0, v_a_1437_);
v___x_1442_ = v_reuseFailAlloc_1443_;
goto v_reusejp_1441_;
}
v_reusejp_1441_:
{
return v___x_1442_;
}
}
}
}
else
{
lean_object* v_a_1445_; lean_object* v___x_1447_; uint8_t v_isShared_1448_; uint8_t v_isSharedCheck_1452_; 
lean_dec_ref(v___x_1416_);
lean_dec_ref(v_a_1414_);
v_a_1445_ = lean_ctor_get(v___x_1420_, 0);
v_isSharedCheck_1452_ = !lean_is_exclusive(v___x_1420_);
if (v_isSharedCheck_1452_ == 0)
{
v___x_1447_ = v___x_1420_;
v_isShared_1448_ = v_isSharedCheck_1452_;
goto v_resetjp_1446_;
}
else
{
lean_inc(v_a_1445_);
lean_dec(v___x_1420_);
v___x_1447_ = lean_box(0);
v_isShared_1448_ = v_isSharedCheck_1452_;
goto v_resetjp_1446_;
}
v_resetjp_1446_:
{
lean_object* v___x_1450_; 
if (v_isShared_1448_ == 0)
{
v___x_1450_ = v___x_1447_;
goto v_reusejp_1449_;
}
else
{
lean_object* v_reuseFailAlloc_1451_; 
v_reuseFailAlloc_1451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1451_, 0, v_a_1445_);
v___x_1450_ = v_reuseFailAlloc_1451_;
goto v_reusejp_1449_;
}
v_reusejp_1449_:
{
return v___x_1450_;
}
}
}
}
else
{
lean_object* v_a_1453_; lean_object* v___x_1455_; uint8_t v_isShared_1456_; uint8_t v_isSharedCheck_1460_; 
lean_dec_ref(v___x_1416_);
lean_dec_ref(v_a_1414_);
lean_dec_ref(v___y_1412_);
v_a_1453_ = lean_ctor_get(v___x_1418_, 0);
v_isSharedCheck_1460_ = !lean_is_exclusive(v___x_1418_);
if (v_isSharedCheck_1460_ == 0)
{
v___x_1455_ = v___x_1418_;
v_isShared_1456_ = v_isSharedCheck_1460_;
goto v_resetjp_1454_;
}
else
{
lean_inc(v_a_1453_);
lean_dec(v___x_1418_);
v___x_1455_ = lean_box(0);
v_isShared_1456_ = v_isSharedCheck_1460_;
goto v_resetjp_1454_;
}
v_resetjp_1454_:
{
lean_object* v___x_1458_; 
if (v_isShared_1456_ == 0)
{
v___x_1458_ = v___x_1455_;
goto v_reusejp_1457_;
}
else
{
lean_object* v_reuseFailAlloc_1459_; 
v_reuseFailAlloc_1459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1459_, 0, v_a_1453_);
v___x_1458_ = v_reuseFailAlloc_1459_;
goto v_reusejp_1457_;
}
v_reusejp_1457_:
{
return v___x_1458_;
}
}
}
}
v___jp_1461_:
{
lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; 
v___x_1468_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__2___closed__2));
v___x_1469_ = lean_unsigned_to_nat(2u);
v___x_1470_ = lean_mk_empty_array_with_capacity(v___x_1469_);
lean_inc(v_a_1406_);
v___x_1471_ = lean_array_push(v___x_1470_, v_a_1406_);
v___x_1472_ = lean_array_push(v___x_1471_, v_fst_1395_);
v___x_1473_ = l_Lean_Meta_mkAppM(v___x_1468_, v___x_1472_, v___y_1464_, v___y_1465_, v___y_1466_, v___y_1467_);
if (lean_obj_tag(v___x_1473_) == 0)
{
if (lean_obj_tag(v___y_1462_) == 0)
{
lean_object* v_a_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; 
v_a_1474_ = lean_ctor_get(v___x_1473_, 0);
lean_inc(v_a_1474_);
lean_dec_ref_known(v___x_1473_, 1);
v___x_1475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1475_, 0, v_a_1474_);
v___x_1476_ = l_Lean_Meta_mkFreshExprMVar(v___x_1475_, v___x_1403_, v___x_1404_, v___y_1464_, v___y_1465_, v___y_1466_, v___y_1467_);
if (lean_obj_tag(v___x_1476_) == 0)
{
lean_object* v_a_1477_; 
v_a_1477_ = lean_ctor_get(v___x_1476_, 0);
lean_inc(v_a_1477_);
lean_dec_ref_known(v___x_1476_, 1);
v___y_1408_ = v___y_1466_;
v___y_1409_ = v___y_1465_;
v___y_1410_ = v___y_1467_;
v___y_1411_ = v___x_1468_;
v___y_1412_ = v_eqProof_1463_;
v___y_1413_ = v___y_1464_;
v_a_1414_ = v_a_1477_;
goto v___jp_1407_;
}
else
{
lean_object* v_a_1478_; lean_object* v___x_1480_; uint8_t v_isShared_1481_; uint8_t v_isSharedCheck_1485_; 
lean_dec_ref(v_eqProof_1463_);
lean_dec(v_a_1406_);
v_a_1478_ = lean_ctor_get(v___x_1476_, 0);
v_isSharedCheck_1485_ = !lean_is_exclusive(v___x_1476_);
if (v_isSharedCheck_1485_ == 0)
{
v___x_1480_ = v___x_1476_;
v_isShared_1481_ = v_isSharedCheck_1485_;
goto v_resetjp_1479_;
}
else
{
lean_inc(v_a_1478_);
lean_dec(v___x_1476_);
v___x_1480_ = lean_box(0);
v_isShared_1481_ = v_isSharedCheck_1485_;
goto v_resetjp_1479_;
}
v_resetjp_1479_:
{
lean_object* v___x_1483_; 
if (v_isShared_1481_ == 0)
{
v___x_1483_ = v___x_1480_;
goto v_reusejp_1482_;
}
else
{
lean_object* v_reuseFailAlloc_1484_; 
v_reuseFailAlloc_1484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1484_, 0, v_a_1478_);
v___x_1483_ = v_reuseFailAlloc_1484_;
goto v_reusejp_1482_;
}
v_reusejp_1482_:
{
return v___x_1483_;
}
}
}
}
else
{
lean_object* v_val_1486_; 
lean_dec_ref_known(v___x_1473_, 1);
v_val_1486_ = lean_ctor_get(v___y_1462_, 0);
lean_inc(v_val_1486_);
lean_dec_ref_known(v___y_1462_, 1);
v___y_1408_ = v___y_1466_;
v___y_1409_ = v___y_1465_;
v___y_1410_ = v___y_1467_;
v___y_1411_ = v___x_1468_;
v___y_1412_ = v_eqProof_1463_;
v___y_1413_ = v___y_1464_;
v_a_1414_ = v_val_1486_;
goto v___jp_1407_;
}
}
else
{
lean_object* v_a_1487_; lean_object* v___x_1489_; uint8_t v_isShared_1490_; uint8_t v_isSharedCheck_1494_; 
lean_dec_ref(v_eqProof_1463_);
lean_dec(v___y_1462_);
lean_dec(v_a_1406_);
v_a_1487_ = lean_ctor_get(v___x_1473_, 0);
v_isSharedCheck_1494_ = !lean_is_exclusive(v___x_1473_);
if (v_isSharedCheck_1494_ == 0)
{
v___x_1489_ = v___x_1473_;
v_isShared_1490_ = v_isSharedCheck_1494_;
goto v_resetjp_1488_;
}
else
{
lean_inc(v_a_1487_);
lean_dec(v___x_1473_);
v___x_1489_ = lean_box(0);
v_isShared_1490_ = v_isSharedCheck_1494_;
goto v_resetjp_1488_;
}
v_resetjp_1488_:
{
lean_object* v___x_1492_; 
if (v_isShared_1490_ == 0)
{
v___x_1492_ = v___x_1489_;
goto v_reusejp_1491_;
}
else
{
lean_object* v_reuseFailAlloc_1493_; 
v_reuseFailAlloc_1493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1493_, 0, v_a_1487_);
v___x_1492_ = v_reuseFailAlloc_1493_;
goto v_reusejp_1491_;
}
v_reusejp_1491_:
{
return v___x_1492_;
}
}
}
}
v___jp_1496_:
{
lean_object* v___x_1498_; 
v___x_1498_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__1___redArg(v_a_1341_, v___y_1497_);
lean_dec(v___y_1497_);
if (lean_obj_tag(v___x_1498_) == 0)
{
lean_dec_ref(v___x_1495_);
if (lean_obj_tag(v_snd_1396_) == 0)
{
lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1502_; 
lean_dec(v_a_1406_);
lean_dec(v_fst_1395_);
v___x_1499_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__2___closed__4, &l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__2___closed__4_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__2___closed__4);
v___x_1500_ = l_Lean_MessageData_ofName(v_head_1380_);
if (v_isShared_1399_ == 0)
{
lean_ctor_set_tag(v___x_1398_, 7);
lean_ctor_set(v___x_1398_, 1, v___x_1500_);
lean_ctor_set(v___x_1398_, 0, v___x_1499_);
v___x_1502_ = v___x_1398_;
goto v_reusejp_1501_;
}
else
{
lean_object* v_reuseFailAlloc_1514_; 
v_reuseFailAlloc_1514_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1514_, 0, v___x_1499_);
lean_ctor_set(v_reuseFailAlloc_1514_, 1, v___x_1500_);
v___x_1502_ = v_reuseFailAlloc_1514_;
goto v_reusejp_1501_;
}
v_reusejp_1501_:
{
lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v_a_1506_; lean_object* v___x_1508_; uint8_t v_isShared_1509_; uint8_t v_isSharedCheck_1513_; 
v___x_1503_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__2___closed__6, &l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__2___closed__6_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__2___closed__6);
v___x_1504_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1504_, 0, v___x_1502_);
lean_ctor_set(v___x_1504_, 1, v___x_1503_);
v___x_1505_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_go_spec__0___redArg(v___x_1504_, v___y_1347_, v___y_1348_, v___y_1349_, v___y_1350_);
v_a_1506_ = lean_ctor_get(v___x_1505_, 0);
v_isSharedCheck_1513_ = !lean_is_exclusive(v___x_1505_);
if (v_isSharedCheck_1513_ == 0)
{
v___x_1508_ = v___x_1505_;
v_isShared_1509_ = v_isSharedCheck_1513_;
goto v_resetjp_1507_;
}
else
{
lean_inc(v_a_1506_);
lean_dec(v___x_1505_);
v___x_1508_ = lean_box(0);
v_isShared_1509_ = v_isSharedCheck_1513_;
goto v_resetjp_1507_;
}
v_resetjp_1507_:
{
lean_object* v___x_1511_; 
if (v_isShared_1509_ == 0)
{
v___x_1511_ = v___x_1508_;
goto v_reusejp_1510_;
}
else
{
lean_object* v_reuseFailAlloc_1512_; 
v_reuseFailAlloc_1512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1512_, 0, v_a_1506_);
v___x_1511_ = v_reuseFailAlloc_1512_;
goto v_reusejp_1510_;
}
v_reusejp_1510_:
{
return v___x_1511_;
}
}
}
}
else
{
lean_object* v_val_1515_; lean_object* v___x_1516_; 
lean_del_object(v___x_1398_);
lean_dec(v_head_1380_);
v_val_1515_ = lean_ctor_get(v_snd_1396_, 0);
lean_inc(v_val_1515_);
lean_dec_ref_known(v_snd_1396_, 1);
v___x_1516_ = lean_box(0);
v___y_1462_ = v___x_1516_;
v_eqProof_1463_ = v_val_1515_;
v___y_1464_ = v___y_1347_;
v___y_1465_ = v___y_1348_;
v___y_1466_ = v___y_1349_;
v___y_1467_ = v___y_1350_;
goto v___jp_1461_;
}
}
else
{
lean_object* v_val_1517_; lean_object* v_fst_1518_; lean_object* v_snd_1519_; lean_object* v_dummy_1520_; lean_object* v_nargs_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; 
lean_del_object(v___x_1398_);
lean_dec(v_head_1380_);
v_val_1517_ = lean_ctor_get(v___x_1498_, 0);
lean_inc(v_val_1517_);
lean_dec_ref_known(v___x_1498_, 1);
v_fst_1518_ = lean_ctor_get(v_val_1517_, 0);
lean_inc(v_fst_1518_);
v_snd_1519_ = lean_ctor_get(v_val_1517_, 1);
lean_inc_n(v_snd_1519_, 2);
lean_dec(v_val_1517_);
v_dummy_1520_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__2___closed__7, &l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__2___closed__7_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__2___closed__7);
v_nargs_1521_ = l_Lean_Expr_getAppNumArgs(v_fst_1395_);
lean_inc(v_nargs_1521_);
v___x_1522_ = lean_mk_array(v_nargs_1521_, v_dummy_1520_);
v___x_1523_ = lean_unsigned_to_nat(1u);
v___x_1524_ = lean_nat_sub(v_nargs_1521_, v___x_1523_);
lean_dec(v_nargs_1521_);
lean_inc(v_fst_1395_);
v___x_1525_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_fst_1395_, v___x_1522_, v___x_1524_);
v___x_1526_ = l_Array_extract___redArg(v___x_1525_, v___x_1388_, v_snd_1519_);
v___x_1527_ = l_Lean_mkAppN(v___x_1495_, v___x_1526_);
lean_dec_ref(v___x_1526_);
v___x_1528_ = lean_array_get_size(v___x_1525_);
v___x_1529_ = l_Array_extract___redArg(v___x_1525_, v_snd_1519_, v___x_1528_);
lean_dec_ref(v___x_1525_);
v___x_1530_ = lean_array_to_list(v___x_1529_);
lean_inc(v_a_1406_);
v___x_1531_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply(v_fst_1518_, v___x_1527_, v_a_1406_, v___x_1530_, v___y_1347_, v___y_1348_, v___y_1349_, v___y_1350_);
if (lean_obj_tag(v___x_1531_) == 0)
{
if (lean_obj_tag(v_snd_1396_) == 0)
{
lean_object* v_a_1532_; 
lean_dec(v_a_1406_);
lean_dec(v_fst_1395_);
v_a_1532_ = lean_ctor_get(v___x_1531_, 0);
lean_inc(v_a_1532_);
lean_dec_ref_known(v___x_1531_, 1);
v_prf_1353_ = v_a_1532_;
v___y_1354_ = v___y_1347_;
v___y_1355_ = v___y_1348_;
v___y_1356_ = v___y_1349_;
v___y_1357_ = v___y_1350_;
goto v___jp_1352_;
}
else
{
lean_object* v_a_1533_; lean_object* v_val_1534_; lean_object* v___x_1536_; uint8_t v_isShared_1537_; uint8_t v_isSharedCheck_1541_; 
v_a_1533_ = lean_ctor_get(v___x_1531_, 0);
lean_inc(v_a_1533_);
lean_dec_ref_known(v___x_1531_, 1);
v_val_1534_ = lean_ctor_get(v_snd_1396_, 0);
v_isSharedCheck_1541_ = !lean_is_exclusive(v_snd_1396_);
if (v_isSharedCheck_1541_ == 0)
{
v___x_1536_ = v_snd_1396_;
v_isShared_1537_ = v_isSharedCheck_1541_;
goto v_resetjp_1535_;
}
else
{
lean_inc(v_val_1534_);
lean_dec(v_snd_1396_);
v___x_1536_ = lean_box(0);
v_isShared_1537_ = v_isSharedCheck_1541_;
goto v_resetjp_1535_;
}
v_resetjp_1535_:
{
lean_object* v___x_1539_; 
if (v_isShared_1537_ == 0)
{
lean_ctor_set(v___x_1536_, 0, v_a_1533_);
v___x_1539_ = v___x_1536_;
goto v_reusejp_1538_;
}
else
{
lean_object* v_reuseFailAlloc_1540_; 
v_reuseFailAlloc_1540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1540_, 0, v_a_1533_);
v___x_1539_ = v_reuseFailAlloc_1540_;
goto v_reusejp_1538_;
}
v_reusejp_1538_:
{
v___y_1462_ = v___x_1539_;
v_eqProof_1463_ = v_val_1534_;
v___y_1464_ = v___y_1347_;
v___y_1465_ = v___y_1348_;
v___y_1466_ = v___y_1349_;
v___y_1467_ = v___y_1350_;
goto v___jp_1461_;
}
}
}
}
else
{
lean_object* v_a_1542_; lean_object* v___x_1544_; uint8_t v_isShared_1545_; uint8_t v_isSharedCheck_1549_; 
lean_dec(v_a_1406_);
lean_dec(v_snd_1396_);
lean_dec(v_fst_1395_);
v_a_1542_ = lean_ctor_get(v___x_1531_, 0);
v_isSharedCheck_1549_ = !lean_is_exclusive(v___x_1531_);
if (v_isSharedCheck_1549_ == 0)
{
v___x_1544_ = v___x_1531_;
v_isShared_1545_ = v_isSharedCheck_1549_;
goto v_resetjp_1543_;
}
else
{
lean_inc(v_a_1542_);
lean_dec(v___x_1531_);
v___x_1544_ = lean_box(0);
v_isShared_1545_ = v_isSharedCheck_1549_;
goto v_resetjp_1543_;
}
v_resetjp_1543_:
{
lean_object* v___x_1547_; 
if (v_isShared_1545_ == 0)
{
v___x_1547_ = v___x_1544_;
goto v_reusejp_1546_;
}
else
{
lean_object* v_reuseFailAlloc_1548_; 
v_reuseFailAlloc_1548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1548_, 0, v_a_1542_);
v___x_1547_ = v_reuseFailAlloc_1548_;
goto v_reusejp_1546_;
}
v_reusejp_1546_:
{
return v___x_1547_;
}
}
}
}
}
}
else
{
lean_object* v_a_1552_; lean_object* v___x_1554_; uint8_t v_isShared_1555_; uint8_t v_isSharedCheck_1559_; 
lean_del_object(v___x_1398_);
lean_dec(v_snd_1396_);
lean_dec(v_fst_1395_);
lean_dec(v_head_1380_);
v_a_1552_ = lean_ctor_get(v___x_1405_, 0);
v_isSharedCheck_1559_ = !lean_is_exclusive(v___x_1405_);
if (v_isSharedCheck_1559_ == 0)
{
v___x_1554_ = v___x_1405_;
v_isShared_1555_ = v_isSharedCheck_1559_;
goto v_resetjp_1553_;
}
else
{
lean_inc(v_a_1552_);
lean_dec(v___x_1405_);
v___x_1554_ = lean_box(0);
v_isShared_1555_ = v_isSharedCheck_1559_;
goto v_resetjp_1553_;
}
v_resetjp_1553_:
{
lean_object* v___x_1557_; 
if (v_isShared_1555_ == 0)
{
v___x_1557_ = v___x_1554_;
goto v_reusejp_1556_;
}
else
{
lean_object* v_reuseFailAlloc_1558_; 
v_reuseFailAlloc_1558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1558_, 0, v_a_1552_);
v___x_1557_ = v_reuseFailAlloc_1558_;
goto v_reusejp_1556_;
}
v_reusejp_1556_:
{
return v___x_1557_;
}
}
}
}
else
{
lean_object* v_a_1560_; lean_object* v___x_1562_; uint8_t v_isShared_1563_; uint8_t v_isSharedCheck_1567_; 
lean_del_object(v___x_1398_);
lean_dec(v_snd_1396_);
lean_dec(v_fst_1395_);
lean_dec(v_head_1380_);
v_a_1560_ = lean_ctor_get(v___x_1400_, 0);
v_isSharedCheck_1567_ = !lean_is_exclusive(v___x_1400_);
if (v_isSharedCheck_1567_ == 0)
{
v___x_1562_ = v___x_1400_;
v_isShared_1563_ = v_isSharedCheck_1567_;
goto v_resetjp_1561_;
}
else
{
lean_inc(v_a_1560_);
lean_dec(v___x_1400_);
v___x_1562_ = lean_box(0);
v_isShared_1563_ = v_isSharedCheck_1567_;
goto v_resetjp_1561_;
}
v_resetjp_1561_:
{
lean_object* v___x_1565_; 
if (v_isShared_1563_ == 0)
{
v___x_1565_ = v___x_1562_;
goto v_reusejp_1564_;
}
else
{
lean_object* v_reuseFailAlloc_1566_; 
v_reuseFailAlloc_1566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1566_, 0, v_a_1560_);
v___x_1565_ = v_reuseFailAlloc_1566_;
goto v_reusejp_1564_;
}
v_reusejp_1564_:
{
return v___x_1565_;
}
}
}
}
}
else
{
lean_object* v_a_1569_; lean_object* v___x_1571_; uint8_t v_isShared_1572_; uint8_t v_isSharedCheck_1576_; 
lean_dec_ref(v___x_1391_);
lean_dec(v_head_1380_);
v_a_1569_ = lean_ctor_get(v___x_1393_, 0);
v_isSharedCheck_1576_ = !lean_is_exclusive(v___x_1393_);
if (v_isSharedCheck_1576_ == 0)
{
v___x_1571_ = v___x_1393_;
v_isShared_1572_ = v_isSharedCheck_1576_;
goto v_resetjp_1570_;
}
else
{
lean_inc(v_a_1569_);
lean_dec(v___x_1393_);
v___x_1571_ = lean_box(0);
v_isShared_1572_ = v_isSharedCheck_1576_;
goto v_resetjp_1570_;
}
v_resetjp_1570_:
{
lean_object* v___x_1574_; 
if (v_isShared_1572_ == 0)
{
v___x_1574_ = v___x_1571_;
goto v_reusejp_1573_;
}
else
{
lean_object* v_reuseFailAlloc_1575_; 
v_reuseFailAlloc_1575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1575_, 0, v_a_1569_);
v___x_1574_ = v_reuseFailAlloc_1575_;
goto v_reusejp_1573_;
}
v_reusejp_1573_:
{
return v___x_1574_;
}
}
}
}
else
{
lean_object* v_a_1577_; lean_object* v___x_1579_; uint8_t v_isShared_1580_; uint8_t v_isSharedCheck_1584_; 
lean_dec(v_numConst_1381_);
lean_dec(v_head_1380_);
lean_dec_ref(v_x_1343_);
lean_dec_ref(v_x_1342_);
v_a_1577_ = lean_ctor_get(v___x_1386_, 0);
v_isSharedCheck_1584_ = !lean_is_exclusive(v___x_1386_);
if (v_isSharedCheck_1584_ == 0)
{
v___x_1579_ = v___x_1386_;
v_isShared_1580_ = v_isSharedCheck_1584_;
goto v_resetjp_1578_;
}
else
{
lean_inc(v_a_1577_);
lean_dec(v___x_1386_);
v___x_1579_ = lean_box(0);
v_isShared_1580_ = v_isSharedCheck_1584_;
goto v_resetjp_1578_;
}
v_resetjp_1578_:
{
lean_object* v___x_1582_; 
if (v_isShared_1580_ == 0)
{
v___x_1582_ = v___x_1579_;
goto v_reusejp_1581_;
}
else
{
lean_object* v_reuseFailAlloc_1583_; 
v_reuseFailAlloc_1583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1583_, 0, v_a_1577_);
v___x_1582_ = v_reuseFailAlloc_1583_;
goto v_reusejp_1581_;
}
v_reusejp_1581_:
{
return v___x_1582_;
}
}
}
}
v___jp_1352_:
{
uint8_t v___x_1358_; lean_object* v___x_1359_; 
v___x_1358_ = 1;
v___x_1359_ = l_Lean_Meta_abstractMVars(v_prf_1353_, v___x_1358_, v___y_1354_, v___y_1355_, v___y_1356_, v___y_1357_);
if (lean_obj_tag(v___x_1359_) == 0)
{
lean_object* v_a_1360_; lean_object* v_paramNames_1361_; lean_object* v_expr_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; 
v_a_1360_ = lean_ctor_get(v___x_1359_, 0);
lean_inc(v_a_1360_);
lean_dec_ref_known(v___x_1359_, 1);
v_paramNames_1361_ = lean_ctor_get(v_a_1360_, 0);
lean_inc_ref(v_paramNames_1361_);
v_expr_1362_ = lean_ctor_get(v_a_1360_, 2);
lean_inc_ref(v_expr_1362_);
lean_dec(v_a_1360_);
v___x_1363_ = lean_array_to_list(v_paramNames_1361_);
v___x_1364_ = lean_box(0);
v___x_1365_ = l_Lean_Meta_Sym_mkBackwardRuleFromExpr(v_expr_1362_, v___x_1363_, v___x_1364_, v___y_1354_, v___y_1355_, v___y_1356_, v___y_1357_);
return v___x_1365_;
}
else
{
lean_object* v_a_1366_; lean_object* v___x_1368_; uint8_t v_isShared_1369_; uint8_t v_isSharedCheck_1373_; 
v_a_1366_ = lean_ctor_get(v___x_1359_, 0);
v_isSharedCheck_1373_ = !lean_is_exclusive(v___x_1359_);
if (v_isSharedCheck_1373_ == 0)
{
v___x_1368_ = v___x_1359_;
v_isShared_1369_ = v_isSharedCheck_1373_;
goto v_resetjp_1367_;
}
else
{
lean_inc(v_a_1366_);
lean_dec(v___x_1359_);
v___x_1368_ = lean_box(0);
v_isShared_1369_ = v_isSharedCheck_1373_;
goto v_resetjp_1367_;
}
v_resetjp_1367_:
{
lean_object* v___x_1371_; 
if (v_isShared_1369_ == 0)
{
v___x_1371_ = v___x_1368_;
goto v_reusejp_1370_;
}
else
{
lean_object* v_reuseFailAlloc_1372_; 
v_reuseFailAlloc_1372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1372_, 0, v_a_1366_);
v___x_1371_ = v_reuseFailAlloc_1372_;
goto v_reusejp_1370_;
}
v_reusejp_1370_:
{
return v___x_1371_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__2___boxed(lean_object* v_op_1585_, lean_object* v___y_1586_, lean_object* v_a_1587_, lean_object* v_x_1588_, lean_object* v_x_1589_, lean_object* v_x_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_){
_start:
{
lean_object* v_res_1598_; 
v_res_1598_ = l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__2(v_op_1585_, v___y_1586_, v_a_1587_, v_x_1588_, v_x_1589_, v_x_1590_, v___y_1591_, v___y_1592_, v___y_1593_, v___y_1594_, v___y_1595_, v___y_1596_);
lean_dec(v___y_1596_);
lean_dec_ref(v___y_1595_);
lean_dec(v___y_1594_);
lean_dec_ref(v___y_1593_);
lean_dec(v___y_1592_);
lean_dec_ref(v___y_1591_);
lean_dec_ref(v_a_1587_);
lean_dec_ref(v___y_1586_);
return v_res_1598_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__4(lean_object* v_as_1599_, size_t v_i_1600_, size_t v_stop_1601_, lean_object* v_b_1602_){
_start:
{
uint8_t v___x_1603_; 
v___x_1603_ = lean_usize_dec_eq(v_i_1600_, v_stop_1601_);
if (v___x_1603_ == 0)
{
lean_object* v___x_1604_; lean_object* v_rewrites_1605_; lean_object* v___x_1606_; size_t v___x_1607_; size_t v___x_1608_; 
v___x_1604_ = lean_array_uget_borrowed(v_as_1599_, v_i_1600_);
v_rewrites_1605_ = lean_ctor_get(v___x_1604_, 2);
v___x_1606_ = l_Array_append___redArg(v_b_1602_, v_rewrites_1605_);
v___x_1607_ = ((size_t)1ULL);
v___x_1608_ = lean_usize_add(v_i_1600_, v___x_1607_);
v_i_1600_ = v___x_1608_;
v_b_1602_ = v___x_1606_;
goto _start;
}
else
{
return v_b_1602_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__4___boxed(lean_object* v_as_1610_, lean_object* v_i_1611_, lean_object* v_stop_1612_, lean_object* v_b_1613_){
_start:
{
size_t v_i_boxed_1614_; size_t v_stop_boxed_1615_; lean_object* v_res_1616_; 
v_i_boxed_1614_ = lean_unbox_usize(v_i_1611_);
lean_dec(v_i_1611_);
v_stop_boxed_1615_ = lean_unbox_usize(v_stop_1612_);
lean_dec(v_stop_1612_);
v_res_1616_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__4(v_as_1610_, v_i_boxed_1614_, v_stop_boxed_1615_, v_b_1613_);
lean_dec_ref(v_as_1610_);
return v_res_1616_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__3(lean_object* v_as_1617_, size_t v_i_1618_, size_t v_stop_1619_, lean_object* v_b_1620_){
_start:
{
lean_object* v___y_1622_; uint8_t v___x_1626_; 
v___x_1626_ = lean_usize_dec_eq(v_i_1618_, v_stop_1619_);
if (v___x_1626_ == 0)
{
lean_object* v___x_1627_; lean_object* v_terminal_x3f_1628_; 
v___x_1627_ = lean_array_uget_borrowed(v_as_1617_, v_i_1618_);
v_terminal_x3f_1628_ = lean_ctor_get(v___x_1627_, 3);
if (lean_obj_tag(v_terminal_x3f_1628_) == 0)
{
lean_object* v___x_1629_; lean_object* v___x_1630_; 
v___x_1629_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_upperAdjoint___closed__3));
v___x_1630_ = l_Array_append___redArg(v_b_1620_, v___x_1629_);
v___y_1622_ = v___x_1630_;
goto v___jp_1621_;
}
else
{
lean_object* v_val_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; 
v_val_1631_ = lean_ctor_get(v_terminal_x3f_1628_, 0);
v___x_1632_ = lean_unsigned_to_nat(1u);
v___x_1633_ = lean_mk_empty_array_with_capacity(v___x_1632_);
lean_inc(v_val_1631_);
v___x_1634_ = lean_array_push(v___x_1633_, v_val_1631_);
v___x_1635_ = l_Array_append___redArg(v_b_1620_, v___x_1634_);
lean_dec_ref(v___x_1634_);
v___y_1622_ = v___x_1635_;
goto v___jp_1621_;
}
}
else
{
return v_b_1620_;
}
v___jp_1621_:
{
size_t v___x_1623_; size_t v___x_1624_; 
v___x_1623_ = ((size_t)1ULL);
v___x_1624_ = lean_usize_add(v_i_1618_, v___x_1623_);
v_i_1618_ = v___x_1624_;
v_b_1620_ = v___y_1622_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__3___boxed(lean_object* v_as_1636_, lean_object* v_i_1637_, lean_object* v_stop_1638_, lean_object* v_b_1639_){
_start:
{
size_t v_i_boxed_1640_; size_t v_stop_boxed_1641_; lean_object* v_res_1642_; 
v_i_boxed_1640_ = lean_unbox_usize(v_i_1637_);
lean_dec(v_i_1637_);
v_stop_boxed_1641_ = lean_unbox_usize(v_stop_1638_);
lean_dec(v_stop_1638_);
v_res_1642_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__3(v_as_1636_, v_i_boxed_1640_, v_stop_boxed_1641_, v_b_1639_);
lean_dec_ref(v_as_1636_);
return v_res_1642_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule___closed__0(void){
_start:
{
lean_object* v___x_1643_; size_t v___x_1644_; size_t v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; 
v___x_1643_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_upperAdjoint___closed__3));
v___x_1644_ = lean_usize_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable___closed__3, &l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable___closed__3_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable___closed__3);
v___x_1645_ = ((size_t)0ULL);
v___x_1646_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_builtinLatticeOps));
v___x_1647_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__3(v___x_1646_, v___x_1645_, v___x_1644_, v___x_1643_);
return v___x_1647_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule(lean_object* v_rhs_1648_, lean_object* v_op_1649_, lean_object* v_a_1650_, lean_object* v_a_1651_, lean_object* v_a_1652_, lean_object* v_a_1653_, lean_object* v_a_1654_, lean_object* v_a_1655_){
_start:
{
lean_object* v___y_1658_; lean_object* v___y_1659_; lean_object* v___y_1660_; lean_object* v_rewrites_1678_; lean_object* v_terminal_x3f_1679_; lean_object* v___x_1680_; lean_object* v___y_1682_; lean_object* v___y_1683_; lean_object* v___y_1690_; uint8_t v___x_1696_; 
v_rewrites_1678_ = lean_ctor_get(v_op_1649_, 2);
v_terminal_x3f_1679_ = lean_ctor_get(v_op_1649_, 3);
v___x_1680_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_builtinLatticeOps));
v___x_1696_ = lean_uint8_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable___closed__1, &l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable___closed__1_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable___closed__1);
if (v___x_1696_ == 0)
{
lean_inc_ref(v_rewrites_1678_);
v___y_1690_ = v_rewrites_1678_;
goto v___jp_1689_;
}
else
{
uint8_t v___x_1697_; 
v___x_1697_ = lean_uint8_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable___closed__2, &l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable___closed__2_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable___closed__2);
if (v___x_1697_ == 0)
{
if (v___x_1696_ == 0)
{
lean_inc_ref(v_rewrites_1678_);
v___y_1690_ = v_rewrites_1678_;
goto v___jp_1689_;
}
else
{
size_t v___x_1698_; size_t v___x_1699_; lean_object* v___x_1700_; 
v___x_1698_ = ((size_t)0ULL);
v___x_1699_ = lean_usize_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable___closed__3, &l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable___closed__3_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable___closed__3);
lean_inc_ref(v_rewrites_1678_);
v___x_1700_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__4(v___x_1680_, v___x_1698_, v___x_1699_, v_rewrites_1678_);
v___y_1690_ = v___x_1700_;
goto v___jp_1689_;
}
}
else
{
size_t v___x_1701_; size_t v___x_1702_; lean_object* v___x_1703_; 
v___x_1701_ = ((size_t)0ULL);
v___x_1702_ = lean_usize_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable___closed__3, &l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable___closed__3_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable___closed__3);
lean_inc_ref(v_rewrites_1678_);
v___x_1703_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__4(v___x_1680_, v___x_1701_, v___x_1702_, v_rewrites_1678_);
v___y_1690_ = v___x_1703_;
goto v___jp_1689_;
}
}
v___jp_1657_:
{
lean_object* v___x_1661_; lean_object* v___x_1662_; 
lean_inc_ref(v___y_1658_);
v___x_1661_ = l_Array_append___redArg(v___y_1658_, v___y_1660_);
lean_dec_ref(v___y_1660_);
v___x_1662_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals(v___x_1661_, v_a_1652_, v_a_1653_, v_a_1654_, v_a_1655_);
lean_dec_ref(v___x_1661_);
if (lean_obj_tag(v___x_1662_) == 0)
{
lean_object* v_a_1663_; lean_object* v_dummy_1664_; lean_object* v_nargs_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; 
v_a_1663_ = lean_ctor_get(v___x_1662_, 0);
lean_inc(v_a_1663_);
lean_dec_ref_known(v___x_1662_, 1);
v_dummy_1664_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__2___closed__7, &l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__2___closed__7_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__2___closed__7);
v_nargs_1665_ = l_Lean_Expr_getAppNumArgs(v_rhs_1648_);
lean_inc(v_nargs_1665_);
v___x_1666_ = lean_mk_array(v_nargs_1665_, v_dummy_1664_);
v___x_1667_ = lean_unsigned_to_nat(1u);
v___x_1668_ = lean_nat_sub(v_nargs_1665_, v___x_1667_);
lean_dec(v_nargs_1665_);
v___x_1669_ = l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__2(v_op_1649_, v___y_1659_, v_a_1663_, v_rhs_1648_, v___x_1666_, v___x_1668_, v_a_1650_, v_a_1651_, v_a_1652_, v_a_1653_, v_a_1654_, v_a_1655_);
lean_dec(v_a_1663_);
lean_dec_ref(v___y_1659_);
return v___x_1669_;
}
else
{
lean_object* v_a_1670_; lean_object* v___x_1672_; uint8_t v_isShared_1673_; uint8_t v_isSharedCheck_1677_; 
lean_dec_ref(v___y_1659_);
lean_dec_ref(v_op_1649_);
lean_dec_ref(v_rhs_1648_);
v_a_1670_ = lean_ctor_get(v___x_1662_, 0);
v_isSharedCheck_1677_ = !lean_is_exclusive(v___x_1662_);
if (v_isSharedCheck_1677_ == 0)
{
v___x_1672_ = v___x_1662_;
v_isShared_1673_ = v_isSharedCheck_1677_;
goto v_resetjp_1671_;
}
else
{
lean_inc(v_a_1670_);
lean_dec(v___x_1662_);
v___x_1672_ = lean_box(0);
v_isShared_1673_ = v_isSharedCheck_1677_;
goto v_resetjp_1671_;
}
v_resetjp_1671_:
{
lean_object* v___x_1675_; 
if (v_isShared_1673_ == 0)
{
v___x_1675_ = v___x_1672_;
goto v_reusejp_1674_;
}
else
{
lean_object* v_reuseFailAlloc_1676_; 
v_reuseFailAlloc_1676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1676_, 0, v_a_1670_);
v___x_1675_ = v_reuseFailAlloc_1676_;
goto v_reusejp_1674_;
}
v_reusejp_1674_:
{
return v___x_1675_;
}
}
}
}
v___jp_1681_:
{
if (lean_obj_tag(v_terminal_x3f_1679_) == 0)
{
lean_object* v___x_1684_; 
v___x_1684_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_upperAdjoint___closed__3));
v___y_1658_ = v___y_1683_;
v___y_1659_ = v___y_1682_;
v___y_1660_ = v___x_1684_;
goto v___jp_1657_;
}
else
{
lean_object* v_val_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; 
v_val_1685_ = lean_ctor_get(v_terminal_x3f_1679_, 0);
v___x_1686_ = lean_unsigned_to_nat(1u);
v___x_1687_ = lean_mk_empty_array_with_capacity(v___x_1686_);
lean_inc(v_val_1685_);
v___x_1688_ = lean_array_push(v___x_1687_, v_val_1685_);
v___y_1658_ = v___y_1683_;
v___y_1659_ = v___y_1682_;
v___y_1660_ = v___x_1688_;
goto v___jp_1657_;
}
}
v___jp_1689_:
{
lean_object* v___x_1691_; uint8_t v___x_1692_; 
v___x_1691_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_upperAdjoint___closed__3));
v___x_1692_ = lean_uint8_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable___closed__1, &l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable___closed__1_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable___closed__1);
if (v___x_1692_ == 0)
{
v___y_1682_ = v___y_1690_;
v___y_1683_ = v___x_1691_;
goto v___jp_1681_;
}
else
{
uint8_t v___x_1693_; 
v___x_1693_ = lean_uint8_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable___closed__2, &l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable___closed__2_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable___closed__2);
if (v___x_1693_ == 0)
{
if (v___x_1692_ == 0)
{
v___y_1682_ = v___y_1690_;
v___y_1683_ = v___x_1691_;
goto v___jp_1681_;
}
else
{
lean_object* v___x_1694_; 
v___x_1694_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule___closed__0, &l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule___closed__0_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule___closed__0);
v___y_1682_ = v___y_1690_;
v___y_1683_ = v___x_1694_;
goto v___jp_1681_;
}
}
else
{
lean_object* v___x_1695_; 
v___x_1695_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule___closed__0, &l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule___closed__0_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule___closed__0);
v___y_1682_ = v___y_1690_;
v___y_1683_ = v___x_1695_;
goto v___jp_1681_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule___boxed(lean_object* v_rhs_1704_, lean_object* v_op_1705_, lean_object* v_a_1706_, lean_object* v_a_1707_, lean_object* v_a_1708_, lean_object* v_a_1709_, lean_object* v_a_1710_, lean_object* v_a_1711_, lean_object* v_a_1712_){
_start:
{
lean_object* v_res_1713_; 
v_res_1713_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule(v_rhs_1704_, v_op_1705_, v_a_1706_, v_a_1707_, v_a_1708_, v_a_1709_, v_a_1710_, v_a_1711_);
lean_dec(v_a_1711_);
lean_dec_ref(v_a_1710_);
lean_dec(v_a_1709_);
lean_dec_ref(v_a_1708_);
lean_dec(v_a_1707_);
lean_dec_ref(v_a_1706_);
return v_res_1713_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__0(size_t v_sz_1714_, size_t v_i_1715_, lean_object* v_bs_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_){
_start:
{
lean_object* v___x_1724_; 
v___x_1724_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__0___redArg(v_sz_1714_, v_i_1715_, v_bs_1716_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_);
return v___x_1724_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__0___boxed(lean_object* v_sz_1725_, lean_object* v_i_1726_, lean_object* v_bs_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_){
_start:
{
size_t v_sz_boxed_1735_; size_t v_i_boxed_1736_; lean_object* v_res_1737_; 
v_sz_boxed_1735_ = lean_unbox_usize(v_sz_1725_);
lean_dec(v_sz_1725_);
v_i_boxed_1736_ = lean_unbox_usize(v_i_1726_);
lean_dec(v_i_1726_);
v_res_1737_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__0(v_sz_boxed_1735_, v_i_boxed_1736_, v_bs_1727_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_);
lean_dec(v___y_1733_);
lean_dec_ref(v___y_1732_);
lean_dec(v___y_1731_);
lean_dec_ref(v___y_1730_);
lean_dec(v___y_1729_);
lean_dec_ref(v___y_1728_);
return v_res_1737_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__1(lean_object* v_00_u03b2_1738_, lean_object* v_m_1739_, lean_object* v_a_1740_){
_start:
{
lean_object* v___x_1741_; 
v___x_1741_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__1___redArg(v_m_1739_, v_a_1740_);
return v___x_1741_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__1___boxed(lean_object* v_00_u03b2_1742_, lean_object* v_m_1743_, lean_object* v_a_1744_){
_start:
{
lean_object* v_res_1745_; 
v_res_1745_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__1(v_00_u03b2_1742_, v_m_1743_, v_a_1744_);
lean_dec(v_a_1744_);
lean_dec_ref(v_m_1743_);
return v_res_1745_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__1_spec__1(lean_object* v_00_u03b2_1746_, lean_object* v_a_1747_, lean_object* v_x_1748_){
_start:
{
lean_object* v___x_1749_; 
v___x_1749_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__1_spec__1___redArg(v_a_1747_, v_x_1748_);
return v___x_1749_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__1_spec__1___boxed(lean_object* v_00_u03b2_1750_, lean_object* v_a_1751_, lean_object* v_x_1752_){
_start:
{
lean_object* v_res_1753_; 
v_res_1753_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__1_spec__1(v_00_u03b2_1750_, v_a_1751_, v_x_1752_);
lean_dec(v_x_1752_);
lean_dec(v_a_1751_);
return v_res_1753_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_Apply(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_Do_Order_Heyting(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProc(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_Rewrite(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_AppBuilder(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_AbstractMVars(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
