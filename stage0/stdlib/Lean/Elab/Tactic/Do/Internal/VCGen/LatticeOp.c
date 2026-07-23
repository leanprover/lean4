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
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
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
static const lean_array_object l_Lean_Elab_Tactic_Do_Internal_VCGen_builtinLatticeOps___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*5, .m_other = 0, .m_tag = 246}, .m_size = 5, .m_capacity = 5, .m_data = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_meet___closed__10_value),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_himp___closed__8_value),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_ofProp___closed__9_value),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_top___closed__8_value),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_upperAdjoint___closed__7_value)}};
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable_spec__0_spec__2___redArg(lean_object* v_a_150_, lean_object* v_b_151_, lean_object* v_x_152_){
_start:
{
if (lean_obj_tag(v_x_152_) == 0)
{
lean_dec(v_b_151_);
lean_dec(v_a_150_);
return v_x_152_;
}
else
{
lean_object* v_key_153_; lean_object* v_value_154_; lean_object* v_tail_155_; lean_object* v___x_157_; uint8_t v_isShared_158_; uint8_t v_isSharedCheck_167_; 
v_key_153_ = lean_ctor_get(v_x_152_, 0);
v_value_154_ = lean_ctor_get(v_x_152_, 1);
v_tail_155_ = lean_ctor_get(v_x_152_, 2);
v_isSharedCheck_167_ = !lean_is_exclusive(v_x_152_);
if (v_isSharedCheck_167_ == 0)
{
v___x_157_ = v_x_152_;
v_isShared_158_ = v_isSharedCheck_167_;
goto v_resetjp_156_;
}
else
{
lean_inc(v_tail_155_);
lean_inc(v_value_154_);
lean_inc(v_key_153_);
lean_dec(v_x_152_);
v___x_157_ = lean_box(0);
v_isShared_158_ = v_isSharedCheck_167_;
goto v_resetjp_156_;
}
v_resetjp_156_:
{
uint8_t v___x_159_; 
v___x_159_ = lean_name_eq(v_key_153_, v_a_150_);
if (v___x_159_ == 0)
{
lean_object* v___x_160_; lean_object* v___x_162_; 
v___x_160_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable_spec__0_spec__2___redArg(v_a_150_, v_b_151_, v_tail_155_);
if (v_isShared_158_ == 0)
{
lean_ctor_set(v___x_157_, 2, v___x_160_);
v___x_162_ = v___x_157_;
goto v_reusejp_161_;
}
else
{
lean_object* v_reuseFailAlloc_163_; 
v_reuseFailAlloc_163_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_163_, 0, v_key_153_);
lean_ctor_set(v_reuseFailAlloc_163_, 1, v_value_154_);
lean_ctor_set(v_reuseFailAlloc_163_, 2, v___x_160_);
v___x_162_ = v_reuseFailAlloc_163_;
goto v_reusejp_161_;
}
v_reusejp_161_:
{
return v___x_162_;
}
}
else
{
lean_object* v___x_165_; 
lean_dec(v_value_154_);
lean_dec(v_key_153_);
if (v_isShared_158_ == 0)
{
lean_ctor_set(v___x_157_, 1, v_b_151_);
lean_ctor_set(v___x_157_, 0, v_a_150_);
v___x_165_ = v___x_157_;
goto v_reusejp_164_;
}
else
{
lean_object* v_reuseFailAlloc_166_; 
v_reuseFailAlloc_166_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_166_, 0, v_a_150_);
lean_ctor_set(v_reuseFailAlloc_166_, 1, v_b_151_);
lean_ctor_set(v_reuseFailAlloc_166_, 2, v_tail_155_);
v___x_165_ = v_reuseFailAlloc_166_;
goto v_reusejp_164_;
}
v_reusejp_164_:
{
return v___x_165_;
}
}
}
}
}
}
static uint64_t _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable_spec__0_spec__1_spec__2_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_168_; uint64_t v___x_169_; 
v___x_168_ = lean_unsigned_to_nat(1723u);
v___x_169_ = lean_uint64_of_nat(v___x_168_);
return v___x_169_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable_spec__0_spec__1_spec__2_spec__4___redArg(lean_object* v_x_170_, lean_object* v_x_171_){
_start:
{
if (lean_obj_tag(v_x_171_) == 0)
{
return v_x_170_;
}
else
{
lean_object* v_key_172_; lean_object* v_value_173_; lean_object* v_tail_174_; lean_object* v___x_176_; uint8_t v_isShared_177_; uint8_t v_isSharedCheck_200_; 
v_key_172_ = lean_ctor_get(v_x_171_, 0);
v_value_173_ = lean_ctor_get(v_x_171_, 1);
v_tail_174_ = lean_ctor_get(v_x_171_, 2);
v_isSharedCheck_200_ = !lean_is_exclusive(v_x_171_);
if (v_isSharedCheck_200_ == 0)
{
v___x_176_ = v_x_171_;
v_isShared_177_ = v_isSharedCheck_200_;
goto v_resetjp_175_;
}
else
{
lean_inc(v_tail_174_);
lean_inc(v_value_173_);
lean_inc(v_key_172_);
lean_dec(v_x_171_);
v___x_176_ = lean_box(0);
v_isShared_177_ = v_isSharedCheck_200_;
goto v_resetjp_175_;
}
v_resetjp_175_:
{
lean_object* v___x_178_; uint64_t v___y_180_; 
v___x_178_ = lean_array_get_size(v_x_170_);
if (lean_obj_tag(v_key_172_) == 0)
{
uint64_t v___x_198_; 
v___x_198_ = lean_uint64_once(&l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable_spec__0_spec__1_spec__2_spec__4___redArg___closed__0, &l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable_spec__0_spec__1_spec__2_spec__4___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable_spec__0_spec__1_spec__2_spec__4___redArg___closed__0);
v___y_180_ = v___x_198_;
goto v___jp_179_;
}
else
{
uint64_t v_hash_199_; 
v_hash_199_ = lean_ctor_get_uint64(v_key_172_, sizeof(void*)*2);
v___y_180_ = v_hash_199_;
goto v___jp_179_;
}
v___jp_179_:
{
uint64_t v___x_181_; uint64_t v___x_182_; uint64_t v_fold_183_; uint64_t v___x_184_; uint64_t v___x_185_; uint64_t v___x_186_; size_t v___x_187_; size_t v___x_188_; size_t v___x_189_; size_t v___x_190_; size_t v___x_191_; lean_object* v___x_192_; lean_object* v___x_194_; 
v___x_181_ = 32ULL;
v___x_182_ = lean_uint64_shift_right(v___y_180_, v___x_181_);
v_fold_183_ = lean_uint64_xor(v___y_180_, v___x_182_);
v___x_184_ = 16ULL;
v___x_185_ = lean_uint64_shift_right(v_fold_183_, v___x_184_);
v___x_186_ = lean_uint64_xor(v_fold_183_, v___x_185_);
v___x_187_ = lean_uint64_to_usize(v___x_186_);
v___x_188_ = lean_usize_of_nat(v___x_178_);
v___x_189_ = ((size_t)1ULL);
v___x_190_ = lean_usize_sub(v___x_188_, v___x_189_);
v___x_191_ = lean_usize_land(v___x_187_, v___x_190_);
v___x_192_ = lean_array_uget_borrowed(v_x_170_, v___x_191_);
lean_inc(v___x_192_);
if (v_isShared_177_ == 0)
{
lean_ctor_set(v___x_176_, 2, v___x_192_);
v___x_194_ = v___x_176_;
goto v_reusejp_193_;
}
else
{
lean_object* v_reuseFailAlloc_197_; 
v_reuseFailAlloc_197_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_197_, 0, v_key_172_);
lean_ctor_set(v_reuseFailAlloc_197_, 1, v_value_173_);
lean_ctor_set(v_reuseFailAlloc_197_, 2, v___x_192_);
v___x_194_ = v_reuseFailAlloc_197_;
goto v_reusejp_193_;
}
v_reusejp_193_:
{
lean_object* v___x_195_; 
v___x_195_ = lean_array_uset(v_x_170_, v___x_191_, v___x_194_);
v_x_170_ = v___x_195_;
v_x_171_ = v_tail_174_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable_spec__0_spec__1_spec__2___redArg(lean_object* v_i_201_, lean_object* v_source_202_, lean_object* v_target_203_){
_start:
{
lean_object* v___x_204_; uint8_t v___x_205_; 
v___x_204_ = lean_array_get_size(v_source_202_);
v___x_205_ = lean_nat_dec_lt(v_i_201_, v___x_204_);
if (v___x_205_ == 0)
{
lean_dec_ref(v_source_202_);
lean_dec(v_i_201_);
return v_target_203_;
}
else
{
lean_object* v_es_206_; lean_object* v___x_207_; lean_object* v_source_208_; lean_object* v_target_209_; lean_object* v___x_210_; lean_object* v___x_211_; 
v_es_206_ = lean_array_fget(v_source_202_, v_i_201_);
v___x_207_ = lean_box(0);
v_source_208_ = lean_array_fset(v_source_202_, v_i_201_, v___x_207_);
v_target_209_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable_spec__0_spec__1_spec__2_spec__4___redArg(v_target_203_, v_es_206_);
v___x_210_ = lean_unsigned_to_nat(1u);
v___x_211_ = lean_nat_add(v_i_201_, v___x_210_);
lean_dec(v_i_201_);
v_i_201_ = v___x_211_;
v_source_202_ = v_source_208_;
v_target_203_ = v_target_209_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable_spec__0_spec__1___redArg(lean_object* v_data_213_){
_start:
{
lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v_nbuckets_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; 
v___x_214_ = lean_array_get_size(v_data_213_);
v___x_215_ = lean_unsigned_to_nat(2u);
v_nbuckets_216_ = lean_nat_mul(v___x_214_, v___x_215_);
v___x_217_ = lean_unsigned_to_nat(0u);
v___x_218_ = lean_box(0);
v___x_219_ = lean_mk_array(v_nbuckets_216_, v___x_218_);
v___x_220_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable_spec__0_spec__1_spec__2___redArg(v___x_217_, v_data_213_, v___x_219_);
return v___x_220_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable_spec__0_spec__0___redArg(lean_object* v_a_221_, lean_object* v_x_222_){
_start:
{
if (lean_obj_tag(v_x_222_) == 0)
{
uint8_t v___x_223_; 
v___x_223_ = 0;
return v___x_223_;
}
else
{
lean_object* v_key_224_; lean_object* v_tail_225_; uint8_t v___x_226_; 
v_key_224_ = lean_ctor_get(v_x_222_, 0);
v_tail_225_ = lean_ctor_get(v_x_222_, 2);
v___x_226_ = lean_name_eq(v_key_224_, v_a_221_);
if (v___x_226_ == 0)
{
v_x_222_ = v_tail_225_;
goto _start;
}
else
{
return v___x_226_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable_spec__0_spec__0___redArg___boxed(lean_object* v_a_228_, lean_object* v_x_229_){
_start:
{
uint8_t v_res_230_; lean_object* v_r_231_; 
v_res_230_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable_spec__0_spec__0___redArg(v_a_228_, v_x_229_);
lean_dec(v_x_229_);
lean_dec(v_a_228_);
v_r_231_ = lean_box(v_res_230_);
return v_r_231_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable_spec__0___redArg(lean_object* v_m_232_, lean_object* v_a_233_, lean_object* v_b_234_){
_start:
{
lean_object* v_size_235_; lean_object* v_buckets_236_; lean_object* v___x_238_; uint8_t v_isShared_239_; uint8_t v_isSharedCheck_282_; 
v_size_235_ = lean_ctor_get(v_m_232_, 0);
v_buckets_236_ = lean_ctor_get(v_m_232_, 1);
v_isSharedCheck_282_ = !lean_is_exclusive(v_m_232_);
if (v_isSharedCheck_282_ == 0)
{
v___x_238_ = v_m_232_;
v_isShared_239_ = v_isSharedCheck_282_;
goto v_resetjp_237_;
}
else
{
lean_inc(v_buckets_236_);
lean_inc(v_size_235_);
lean_dec(v_m_232_);
v___x_238_ = lean_box(0);
v_isShared_239_ = v_isSharedCheck_282_;
goto v_resetjp_237_;
}
v_resetjp_237_:
{
lean_object* v___x_240_; uint64_t v___y_242_; 
v___x_240_ = lean_array_get_size(v_buckets_236_);
if (lean_obj_tag(v_a_233_) == 0)
{
uint64_t v___x_280_; 
v___x_280_ = lean_uint64_once(&l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable_spec__0_spec__1_spec__2_spec__4___redArg___closed__0, &l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable_spec__0_spec__1_spec__2_spec__4___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable_spec__0_spec__1_spec__2_spec__4___redArg___closed__0);
v___y_242_ = v___x_280_;
goto v___jp_241_;
}
else
{
uint64_t v_hash_281_; 
v_hash_281_ = lean_ctor_get_uint64(v_a_233_, sizeof(void*)*2);
v___y_242_ = v_hash_281_;
goto v___jp_241_;
}
v___jp_241_:
{
uint64_t v___x_243_; uint64_t v___x_244_; uint64_t v_fold_245_; uint64_t v___x_246_; uint64_t v___x_247_; uint64_t v___x_248_; size_t v___x_249_; size_t v___x_250_; size_t v___x_251_; size_t v___x_252_; size_t v___x_253_; lean_object* v_bkt_254_; uint8_t v___x_255_; 
v___x_243_ = 32ULL;
v___x_244_ = lean_uint64_shift_right(v___y_242_, v___x_243_);
v_fold_245_ = lean_uint64_xor(v___y_242_, v___x_244_);
v___x_246_ = 16ULL;
v___x_247_ = lean_uint64_shift_right(v_fold_245_, v___x_246_);
v___x_248_ = lean_uint64_xor(v_fold_245_, v___x_247_);
v___x_249_ = lean_uint64_to_usize(v___x_248_);
v___x_250_ = lean_usize_of_nat(v___x_240_);
v___x_251_ = ((size_t)1ULL);
v___x_252_ = lean_usize_sub(v___x_250_, v___x_251_);
v___x_253_ = lean_usize_land(v___x_249_, v___x_252_);
v_bkt_254_ = lean_array_uget_borrowed(v_buckets_236_, v___x_253_);
v___x_255_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable_spec__0_spec__0___redArg(v_a_233_, v_bkt_254_);
if (v___x_255_ == 0)
{
lean_object* v___x_256_; lean_object* v_size_x27_257_; lean_object* v___x_258_; lean_object* v_buckets_x27_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; uint8_t v___x_265_; 
v___x_256_ = lean_unsigned_to_nat(1u);
v_size_x27_257_ = lean_nat_add(v_size_235_, v___x_256_);
lean_dec(v_size_235_);
lean_inc(v_bkt_254_);
v___x_258_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_258_, 0, v_a_233_);
lean_ctor_set(v___x_258_, 1, v_b_234_);
lean_ctor_set(v___x_258_, 2, v_bkt_254_);
v_buckets_x27_259_ = lean_array_uset(v_buckets_236_, v___x_253_, v___x_258_);
v___x_260_ = lean_unsigned_to_nat(4u);
v___x_261_ = lean_nat_mul(v_size_x27_257_, v___x_260_);
v___x_262_ = lean_unsigned_to_nat(3u);
v___x_263_ = lean_nat_div(v___x_261_, v___x_262_);
lean_dec(v___x_261_);
v___x_264_ = lean_array_get_size(v_buckets_x27_259_);
v___x_265_ = lean_nat_dec_le(v___x_263_, v___x_264_);
lean_dec(v___x_263_);
if (v___x_265_ == 0)
{
lean_object* v_val_266_; lean_object* v___x_268_; 
v_val_266_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable_spec__0_spec__1___redArg(v_buckets_x27_259_);
if (v_isShared_239_ == 0)
{
lean_ctor_set(v___x_238_, 1, v_val_266_);
lean_ctor_set(v___x_238_, 0, v_size_x27_257_);
v___x_268_ = v___x_238_;
goto v_reusejp_267_;
}
else
{
lean_object* v_reuseFailAlloc_269_; 
v_reuseFailAlloc_269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_269_, 0, v_size_x27_257_);
lean_ctor_set(v_reuseFailAlloc_269_, 1, v_val_266_);
v___x_268_ = v_reuseFailAlloc_269_;
goto v_reusejp_267_;
}
v_reusejp_267_:
{
return v___x_268_;
}
}
else
{
lean_object* v___x_271_; 
if (v_isShared_239_ == 0)
{
lean_ctor_set(v___x_238_, 1, v_buckets_x27_259_);
lean_ctor_set(v___x_238_, 0, v_size_x27_257_);
v___x_271_ = v___x_238_;
goto v_reusejp_270_;
}
else
{
lean_object* v_reuseFailAlloc_272_; 
v_reuseFailAlloc_272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_272_, 0, v_size_x27_257_);
lean_ctor_set(v_reuseFailAlloc_272_, 1, v_buckets_x27_259_);
v___x_271_ = v_reuseFailAlloc_272_;
goto v_reusejp_270_;
}
v_reusejp_270_:
{
return v___x_271_;
}
}
}
else
{
lean_object* v___x_273_; lean_object* v_buckets_x27_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_278_; 
lean_inc(v_bkt_254_);
v___x_273_ = lean_box(0);
v_buckets_x27_274_ = lean_array_uset(v_buckets_236_, v___x_253_, v___x_273_);
v___x_275_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable_spec__0_spec__2___redArg(v_a_233_, v_b_234_, v_bkt_254_);
v___x_276_ = lean_array_uset(v_buckets_x27_274_, v___x_253_, v___x_275_);
if (v_isShared_239_ == 0)
{
lean_ctor_set(v___x_238_, 1, v___x_276_);
v___x_278_ = v___x_238_;
goto v_reusejp_277_;
}
else
{
lean_object* v_reuseFailAlloc_279_; 
v_reuseFailAlloc_279_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_279_, 0, v_size_235_);
lean_ctor_set(v_reuseFailAlloc_279_, 1, v___x_276_);
v___x_278_ = v_reuseFailAlloc_279_;
goto v_reusejp_277_;
}
v_reusejp_277_:
{
return v___x_278_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable_spec__1(lean_object* v_as_283_, size_t v_i_284_, size_t v_stop_285_, lean_object* v_b_286_){
_start:
{
uint8_t v___x_287_; 
v___x_287_ = lean_usize_dec_eq(v_i_284_, v_stop_285_);
if (v___x_287_ == 0)
{
lean_object* v___x_288_; lean_object* v_head_289_; lean_object* v___x_290_; size_t v___x_291_; size_t v___x_292_; 
v___x_288_ = lean_array_uget_borrowed(v_as_283_, v_i_284_);
v_head_289_ = lean_ctor_get(v___x_288_, 0);
lean_inc(v___x_288_);
lean_inc(v_head_289_);
v___x_290_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable_spec__0___redArg(v_b_286_, v_head_289_, v___x_288_);
v___x_291_ = ((size_t)1ULL);
v___x_292_ = lean_usize_add(v_i_284_, v___x_291_);
v_i_284_ = v___x_292_;
v_b_286_ = v___x_290_;
goto _start;
}
else
{
return v_b_286_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable_spec__1___boxed(lean_object* v_as_294_, lean_object* v_i_295_, lean_object* v_stop_296_, lean_object* v_b_297_){
_start:
{
size_t v_i_boxed_298_; size_t v_stop_boxed_299_; lean_object* v_res_300_; 
v_i_boxed_298_ = lean_unbox_usize(v_i_295_);
lean_dec(v_i_295_);
v_stop_boxed_299_ = lean_unbox_usize(v_stop_296_);
lean_dec(v_stop_296_);
v_res_300_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable_spec__1(v_as_294_, v_i_boxed_298_, v_stop_boxed_299_, v_b_297_);
lean_dec_ref(v_as_294_);
return v_res_300_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable___closed__0(void){
_start:
{
lean_object* v___x_301_; lean_object* v___x_302_; 
v___x_301_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_builtinLatticeOps));
v___x_302_ = lean_array_get_size(v___x_301_);
return v___x_302_;
}
}
static uint8_t _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable___closed__1(void){
_start:
{
lean_object* v___x_303_; lean_object* v___x_304_; uint8_t v___x_305_; 
v___x_303_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable___closed__0, &l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable___closed__0_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable___closed__0);
v___x_304_ = lean_unsigned_to_nat(0u);
v___x_305_ = lean_nat_dec_lt(v___x_304_, v___x_303_);
return v___x_305_;
}
}
static uint8_t _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable___closed__2(void){
_start:
{
lean_object* v___x_306_; uint8_t v___x_307_; 
v___x_306_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable___closed__0, &l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable___closed__0_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable___closed__0);
v___x_307_ = lean_nat_dec_le(v___x_306_, v___x_306_);
return v___x_307_;
}
}
static size_t _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable___closed__3(void){
_start:
{
lean_object* v___x_308_; size_t v___x_309_; 
v___x_308_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable___closed__0, &l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable___closed__0_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable___closed__0);
v___x_309_ = lean_usize_of_nat(v___x_308_);
return v___x_309_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable(lean_object* v_frameSplits_310_){
_start:
{
lean_object* v___x_311_; uint8_t v___x_312_; 
v___x_311_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_builtinLatticeOps));
v___x_312_ = lean_uint8_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable___closed__1, &l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable___closed__1_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable___closed__1);
if (v___x_312_ == 0)
{
return v_frameSplits_310_;
}
else
{
uint8_t v___x_313_; 
v___x_313_ = lean_uint8_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable___closed__2, &l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable___closed__2_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable___closed__2);
if (v___x_313_ == 0)
{
if (v___x_312_ == 0)
{
return v_frameSplits_310_;
}
else
{
size_t v___x_314_; size_t v___x_315_; lean_object* v___x_316_; 
v___x_314_ = ((size_t)0ULL);
v___x_315_ = lean_usize_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable___closed__3, &l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable___closed__3_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable___closed__3);
v___x_316_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable_spec__1(v___x_311_, v___x_314_, v___x_315_, v_frameSplits_310_);
return v___x_316_;
}
}
else
{
size_t v___x_317_; size_t v___x_318_; lean_object* v___x_319_; 
v___x_317_ = ((size_t)0ULL);
v___x_318_ = lean_usize_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable___closed__3, &l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable___closed__3_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable___closed__3);
v___x_319_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable_spec__1(v___x_311_, v___x_317_, v___x_318_, v_frameSplits_310_);
return v___x_319_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable_spec__0(lean_object* v_00_u03b2_320_, lean_object* v_m_321_, lean_object* v_a_322_, lean_object* v_b_323_){
_start:
{
lean_object* v___x_324_; 
v___x_324_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable_spec__0___redArg(v_m_321_, v_a_322_, v_b_323_);
return v___x_324_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable_spec__0_spec__0(lean_object* v_00_u03b2_325_, lean_object* v_a_326_, lean_object* v_x_327_){
_start:
{
uint8_t v___x_328_; 
v___x_328_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable_spec__0_spec__0___redArg(v_a_326_, v_x_327_);
return v___x_328_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable_spec__0_spec__0___boxed(lean_object* v_00_u03b2_329_, lean_object* v_a_330_, lean_object* v_x_331_){
_start:
{
uint8_t v_res_332_; lean_object* v_r_333_; 
v_res_332_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable_spec__0_spec__0(v_00_u03b2_329_, v_a_330_, v_x_331_);
lean_dec(v_x_331_);
lean_dec(v_a_330_);
v_r_333_ = lean_box(v_res_332_);
return v_r_333_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable_spec__0_spec__1(lean_object* v_00_u03b2_334_, lean_object* v_data_335_){
_start:
{
lean_object* v___x_336_; 
v___x_336_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable_spec__0_spec__1___redArg(v_data_335_);
return v___x_336_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable_spec__0_spec__2(lean_object* v_00_u03b2_337_, lean_object* v_a_338_, lean_object* v_b_339_, lean_object* v_x_340_){
_start:
{
lean_object* v___x_341_; 
v___x_341_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable_spec__0_spec__2___redArg(v_a_338_, v_b_339_, v_x_340_);
return v___x_341_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_342_, lean_object* v_i_343_, lean_object* v_source_344_, lean_object* v_target_345_){
_start:
{
lean_object* v___x_346_; 
v___x_346_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable_spec__0_spec__1_spec__2___redArg(v_i_343_, v_source_344_, v_target_345_);
return v___x_346_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable_spec__0_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_347_, lean_object* v_x_348_, lean_object* v_x_349_){
_start:
{
lean_object* v___x_350_; 
v___x_350_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable_spec__0_spec__1_spec__2_spec__4___redArg(v_x_348_, v_x_349_);
return v___x_350_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__0___redArg(lean_object* v_e_351_, lean_object* v___y_352_){
_start:
{
uint8_t v___x_354_; 
v___x_354_ = l_Lean_Expr_hasMVar(v_e_351_);
if (v___x_354_ == 0)
{
lean_object* v___x_355_; 
v___x_355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_355_, 0, v_e_351_);
return v___x_355_;
}
else
{
lean_object* v___x_356_; lean_object* v_mctx_357_; lean_object* v___x_358_; lean_object* v_fst_359_; lean_object* v_snd_360_; lean_object* v___x_361_; lean_object* v_cache_362_; lean_object* v_zetaDeltaFVarIds_363_; lean_object* v_postponed_364_; lean_object* v_diag_365_; lean_object* v___x_367_; uint8_t v_isShared_368_; uint8_t v_isSharedCheck_374_; 
v___x_356_ = lean_st_ref_get(v___y_352_);
v_mctx_357_ = lean_ctor_get(v___x_356_, 0);
lean_inc_ref(v_mctx_357_);
lean_dec(v___x_356_);
v___x_358_ = l_Lean_instantiateMVarsCore(v_mctx_357_, v_e_351_);
v_fst_359_ = lean_ctor_get(v___x_358_, 0);
lean_inc(v_fst_359_);
v_snd_360_ = lean_ctor_get(v___x_358_, 1);
lean_inc(v_snd_360_);
lean_dec_ref(v___x_358_);
v___x_361_ = lean_st_ref_take(v___y_352_);
v_cache_362_ = lean_ctor_get(v___x_361_, 1);
v_zetaDeltaFVarIds_363_ = lean_ctor_get(v___x_361_, 2);
v_postponed_364_ = lean_ctor_get(v___x_361_, 3);
v_diag_365_ = lean_ctor_get(v___x_361_, 4);
v_isSharedCheck_374_ = !lean_is_exclusive(v___x_361_);
if (v_isSharedCheck_374_ == 0)
{
lean_object* v_unused_375_; 
v_unused_375_ = lean_ctor_get(v___x_361_, 0);
lean_dec(v_unused_375_);
v___x_367_ = v___x_361_;
v_isShared_368_ = v_isSharedCheck_374_;
goto v_resetjp_366_;
}
else
{
lean_inc(v_diag_365_);
lean_inc(v_postponed_364_);
lean_inc(v_zetaDeltaFVarIds_363_);
lean_inc(v_cache_362_);
lean_dec(v___x_361_);
v___x_367_ = lean_box(0);
v_isShared_368_ = v_isSharedCheck_374_;
goto v_resetjp_366_;
}
v_resetjp_366_:
{
lean_object* v___x_370_; 
if (v_isShared_368_ == 0)
{
lean_ctor_set(v___x_367_, 0, v_snd_360_);
v___x_370_ = v___x_367_;
goto v_reusejp_369_;
}
else
{
lean_object* v_reuseFailAlloc_373_; 
v_reuseFailAlloc_373_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_373_, 0, v_snd_360_);
lean_ctor_set(v_reuseFailAlloc_373_, 1, v_cache_362_);
lean_ctor_set(v_reuseFailAlloc_373_, 2, v_zetaDeltaFVarIds_363_);
lean_ctor_set(v_reuseFailAlloc_373_, 3, v_postponed_364_);
lean_ctor_set(v_reuseFailAlloc_373_, 4, v_diag_365_);
v___x_370_ = v_reuseFailAlloc_373_;
goto v_reusejp_369_;
}
v_reusejp_369_:
{
lean_object* v___x_371_; lean_object* v___x_372_; 
v___x_371_ = lean_st_ref_set(v___y_352_, v___x_370_);
v___x_372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_372_, 0, v_fst_359_);
return v___x_372_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__0___redArg___boxed(lean_object* v_e_376_, lean_object* v___y_377_, lean_object* v___y_378_){
_start:
{
lean_object* v_res_379_; 
v_res_379_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__0___redArg(v_e_376_, v___y_377_);
lean_dec(v___y_377_);
return v_res_379_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__0(lean_object* v_e_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_){
_start:
{
lean_object* v___x_386_; 
v___x_386_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__0___redArg(v_e_380_, v___y_382_);
return v___x_386_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__0___boxed(lean_object* v_e_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_){
_start:
{
lean_object* v_res_393_; 
v_res_393_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__0(v_e_387_, v___y_388_, v___y_389_, v___y_390_, v___y_391_);
lean_dec(v___y_391_);
lean_dec_ref(v___y_390_);
lean_dec(v___y_389_);
lean_dec_ref(v___y_388_);
return v_res_393_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__1_spec__1(lean_object* v_msgData_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_){
_start:
{
lean_object* v___x_400_; lean_object* v_env_401_; lean_object* v___x_402_; lean_object* v_mctx_403_; lean_object* v_lctx_404_; lean_object* v_options_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; 
v___x_400_ = lean_st_ref_get(v___y_398_);
v_env_401_ = lean_ctor_get(v___x_400_, 0);
lean_inc_ref(v_env_401_);
lean_dec(v___x_400_);
v___x_402_ = lean_st_ref_get(v___y_396_);
v_mctx_403_ = lean_ctor_get(v___x_402_, 0);
lean_inc_ref(v_mctx_403_);
lean_dec(v___x_402_);
v_lctx_404_ = lean_ctor_get(v___y_395_, 2);
v_options_405_ = lean_ctor_get(v___y_397_, 2);
lean_inc_ref(v_options_405_);
lean_inc_ref(v_lctx_404_);
v___x_406_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_406_, 0, v_env_401_);
lean_ctor_set(v___x_406_, 1, v_mctx_403_);
lean_ctor_set(v___x_406_, 2, v_lctx_404_);
lean_ctor_set(v___x_406_, 3, v_options_405_);
v___x_407_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_407_, 0, v___x_406_);
lean_ctor_set(v___x_407_, 1, v_msgData_394_);
v___x_408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_408_, 0, v___x_407_);
return v___x_408_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__1_spec__1___boxed(lean_object* v_msgData_409_, lean_object* v___y_410_, lean_object* v___y_411_, lean_object* v___y_412_, lean_object* v___y_413_, lean_object* v___y_414_){
_start:
{
lean_object* v_res_415_; 
v_res_415_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__1_spec__1(v_msgData_409_, v___y_410_, v___y_411_, v___y_412_, v___y_413_);
lean_dec(v___y_413_);
lean_dec_ref(v___y_412_);
lean_dec(v___y_411_);
lean_dec_ref(v___y_410_);
return v_res_415_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__1___redArg(lean_object* v_msg_416_, lean_object* v___y_417_, lean_object* v___y_418_, lean_object* v___y_419_, lean_object* v___y_420_){
_start:
{
lean_object* v_ref_422_; lean_object* v___x_423_; lean_object* v_a_424_; lean_object* v___x_426_; uint8_t v_isShared_427_; uint8_t v_isSharedCheck_432_; 
v_ref_422_ = lean_ctor_get(v___y_419_, 5);
v___x_423_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__1_spec__1(v_msg_416_, v___y_417_, v___y_418_, v___y_419_, v___y_420_);
v_a_424_ = lean_ctor_get(v___x_423_, 0);
v_isSharedCheck_432_ = !lean_is_exclusive(v___x_423_);
if (v_isSharedCheck_432_ == 0)
{
v___x_426_ = v___x_423_;
v_isShared_427_ = v_isSharedCheck_432_;
goto v_resetjp_425_;
}
else
{
lean_inc(v_a_424_);
lean_dec(v___x_423_);
v___x_426_ = lean_box(0);
v_isShared_427_ = v_isSharedCheck_432_;
goto v_resetjp_425_;
}
v_resetjp_425_:
{
lean_object* v___x_428_; lean_object* v___x_430_; 
lean_inc(v_ref_422_);
v___x_428_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_428_, 0, v_ref_422_);
lean_ctor_set(v___x_428_, 1, v_a_424_);
if (v_isShared_427_ == 0)
{
lean_ctor_set_tag(v___x_426_, 1);
lean_ctor_set(v___x_426_, 0, v___x_428_);
v___x_430_ = v___x_426_;
goto v_reusejp_429_;
}
else
{
lean_object* v_reuseFailAlloc_431_; 
v_reuseFailAlloc_431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_431_, 0, v___x_428_);
v___x_430_ = v_reuseFailAlloc_431_;
goto v_reusejp_429_;
}
v_reusejp_429_:
{
return v___x_430_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__1___redArg___boxed(lean_object* v_msg_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_){
_start:
{
lean_object* v_res_439_; 
v_res_439_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__1___redArg(v_msg_433_, v___y_434_, v___y_435_, v___y_436_, v___y_437_);
lean_dec(v___y_437_);
lean_dec_ref(v___y_436_);
lean_dec(v___y_435_);
lean_dec_ref(v___y_434_);
return v_res_439_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__2___closed__4(void){
_start:
{
lean_object* v___x_448_; lean_object* v___x_449_; 
v___x_448_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__2___closed__3));
v___x_449_ = l_Lean_stringToMessageData(v___x_448_);
return v___x_449_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__2___closed__6(void){
_start:
{
lean_object* v___x_451_; lean_object* v___x_452_; 
v___x_451_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__2___closed__5));
v___x_452_ = l_Lean_stringToMessageData(v___x_451_);
return v___x_452_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__2___closed__8(void){
_start:
{
lean_object* v___x_454_; lean_object* v___x_455_; 
v___x_454_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__2___closed__7));
v___x_455_ = l_Lean_stringToMessageData(v___x_454_);
return v___x_455_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__2(lean_object* v_as_456_, size_t v_sz_457_, size_t v_i_458_, lean_object* v_b_459_, lean_object* v___y_460_, lean_object* v___y_461_, lean_object* v___y_462_, lean_object* v___y_463_){
_start:
{
lean_object* v_a_466_; uint8_t v___x_470_; 
v___x_470_ = lean_usize_dec_lt(v_i_458_, v_sz_457_);
if (v___x_470_ == 0)
{
lean_object* v___x_471_; 
v___x_471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_471_, 0, v_b_459_);
return v___x_471_;
}
else
{
lean_object* v_a_472_; lean_object* v___x_473_; 
v_a_472_ = lean_array_uget_borrowed(v_as_456_, v_i_458_);
lean_inc(v_a_472_);
v___x_473_ = l_Lean_Meta_mkConstWithFreshMVarLevels(v_a_472_, v___y_460_, v___y_461_, v___y_462_, v___y_463_);
if (lean_obj_tag(v___x_473_) == 0)
{
lean_object* v_a_474_; lean_object* v___x_475_; 
v_a_474_ = lean_ctor_get(v___x_473_, 0);
lean_inc(v_a_474_);
lean_dec_ref_known(v___x_473_, 1);
lean_inc(v___y_463_);
lean_inc_ref(v___y_462_);
lean_inc(v___y_461_);
lean_inc_ref(v___y_460_);
v___x_475_ = lean_infer_type(v_a_474_, v___y_460_, v___y_461_, v___y_462_, v___y_463_);
if (lean_obj_tag(v___x_475_) == 0)
{
lean_object* v_a_476_; lean_object* v___x_477_; uint8_t v___x_478_; lean_object* v___x_479_; 
v_a_476_ = lean_ctor_get(v___x_475_, 0);
lean_inc(v_a_476_);
lean_dec_ref_known(v___x_475_, 1);
v___x_477_ = lean_box(0);
v___x_478_ = 0;
v___x_479_ = l_Lean_Meta_forallMetaTelescopeReducing(v_a_476_, v___x_477_, v___x_478_, v___y_460_, v___y_461_, v___y_462_, v___y_463_);
if (lean_obj_tag(v___x_479_) == 0)
{
lean_object* v_a_480_; lean_object* v_snd_481_; lean_object* v___x_483_; uint8_t v_isShared_484_; uint8_t v_isSharedCheck_545_; 
v_a_480_ = lean_ctor_get(v___x_479_, 0);
lean_inc(v_a_480_);
lean_dec_ref_known(v___x_479_, 1);
v_snd_481_ = lean_ctor_get(v_a_480_, 1);
v_isSharedCheck_545_ = !lean_is_exclusive(v_a_480_);
if (v_isSharedCheck_545_ == 0)
{
lean_object* v_unused_546_; 
v_unused_546_ = lean_ctor_get(v_a_480_, 0);
lean_dec(v_unused_546_);
v___x_483_ = v_a_480_;
v_isShared_484_ = v_isSharedCheck_545_;
goto v_resetjp_482_;
}
else
{
lean_inc(v_snd_481_);
lean_dec(v_a_480_);
v___x_483_ = lean_box(0);
v_isShared_484_ = v_isSharedCheck_545_;
goto v_resetjp_482_;
}
v_resetjp_482_:
{
lean_object* v_snd_485_; lean_object* v___x_487_; uint8_t v_isShared_488_; uint8_t v_isSharedCheck_543_; 
v_snd_485_ = lean_ctor_get(v_snd_481_, 1);
v_isSharedCheck_543_ = !lean_is_exclusive(v_snd_481_);
if (v_isSharedCheck_543_ == 0)
{
lean_object* v_unused_544_; 
v_unused_544_ = lean_ctor_get(v_snd_481_, 0);
lean_dec(v_unused_544_);
v___x_487_ = v_snd_481_;
v_isShared_488_ = v_isSharedCheck_543_;
goto v_resetjp_486_;
}
else
{
lean_inc(v_snd_485_);
lean_dec(v_snd_481_);
v___x_487_ = lean_box(0);
v_isShared_488_ = v_isSharedCheck_543_;
goto v_resetjp_486_;
}
v_resetjp_486_:
{
lean_object* v___x_489_; 
v___x_489_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__0___redArg(v_snd_485_, v___y_461_);
if (lean_obj_tag(v___x_489_) == 0)
{
lean_object* v_a_490_; lean_object* v___x_491_; lean_object* v___x_492_; uint8_t v___x_493_; 
v_a_490_ = lean_ctor_get(v___x_489_, 0);
lean_inc(v_a_490_);
lean_dec_ref_known(v___x_489_, 1);
v___x_491_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__2___closed__2));
v___x_492_ = lean_unsigned_to_nat(4u);
v___x_493_ = l_Lean_Expr_isAppOfArity(v_a_490_, v___x_491_, v___x_492_);
if (v___x_493_ == 0)
{
lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_497_; 
lean_dec(v_a_490_);
lean_del_object(v___x_487_);
v___x_494_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__2___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__2___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__2___closed__4);
lean_inc(v_a_472_);
v___x_495_ = l_Lean_MessageData_ofName(v_a_472_);
if (v_isShared_484_ == 0)
{
lean_ctor_set_tag(v___x_483_, 7);
lean_ctor_set(v___x_483_, 1, v___x_495_);
lean_ctor_set(v___x_483_, 0, v___x_494_);
v___x_497_ = v___x_483_;
goto v_reusejp_496_;
}
else
{
lean_object* v_reuseFailAlloc_509_; 
v_reuseFailAlloc_509_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_509_, 0, v___x_494_);
lean_ctor_set(v_reuseFailAlloc_509_, 1, v___x_495_);
v___x_497_ = v_reuseFailAlloc_509_;
goto v_reusejp_496_;
}
v_reusejp_496_:
{
lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; 
v___x_498_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__2___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__2___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__2___closed__6);
v___x_499_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_499_, 0, v___x_497_);
lean_ctor_set(v___x_499_, 1, v___x_498_);
v___x_500_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__1___redArg(v___x_499_, v___y_460_, v___y_461_, v___y_462_, v___y_463_);
if (lean_obj_tag(v___x_500_) == 0)
{
lean_dec_ref_known(v___x_500_, 1);
v_a_466_ = v_b_459_;
goto v___jp_465_;
}
else
{
lean_object* v_a_501_; lean_object* v___x_503_; uint8_t v_isShared_504_; uint8_t v_isSharedCheck_508_; 
lean_dec_ref(v_b_459_);
v_a_501_ = lean_ctor_get(v___x_500_, 0);
v_isSharedCheck_508_ = !lean_is_exclusive(v___x_500_);
if (v_isSharedCheck_508_ == 0)
{
v___x_503_ = v___x_500_;
v_isShared_504_ = v_isSharedCheck_508_;
goto v_resetjp_502_;
}
else
{
lean_inc(v_a_501_);
lean_dec(v___x_500_);
v___x_503_ = lean_box(0);
v_isShared_504_ = v_isSharedCheck_508_;
goto v_resetjp_502_;
}
v_resetjp_502_:
{
lean_object* v___x_506_; 
if (v_isShared_504_ == 0)
{
v___x_506_ = v___x_503_;
goto v_reusejp_505_;
}
else
{
lean_object* v_reuseFailAlloc_507_; 
v_reuseFailAlloc_507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_507_, 0, v_a_501_);
v___x_506_ = v_reuseFailAlloc_507_;
goto v_reusejp_505_;
}
v_reusejp_505_:
{
return v___x_506_;
}
}
}
}
}
else
{
lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; 
v___x_510_ = l_Lean_Expr_appArg_x21(v_a_490_);
lean_dec(v_a_490_);
v___x_511_ = l_Lean_Expr_getAppFn(v___x_510_);
v___x_512_ = l_Lean_Expr_constName_x3f(v___x_511_);
lean_dec_ref(v___x_511_);
if (lean_obj_tag(v___x_512_) == 1)
{
lean_object* v_val_513_; lean_object* v___x_514_; lean_object* v___x_516_; 
lean_del_object(v___x_483_);
v_val_513_ = lean_ctor_get(v___x_512_, 0);
lean_inc(v_val_513_);
lean_dec_ref_known(v___x_512_, 1);
v___x_514_ = l_Lean_Expr_getAppNumArgs(v___x_510_);
lean_dec_ref(v___x_510_);
lean_inc(v_a_472_);
if (v_isShared_488_ == 0)
{
lean_ctor_set(v___x_487_, 1, v___x_514_);
lean_ctor_set(v___x_487_, 0, v_a_472_);
v___x_516_ = v___x_487_;
goto v_reusejp_515_;
}
else
{
lean_object* v_reuseFailAlloc_518_; 
v_reuseFailAlloc_518_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_518_, 0, v_a_472_);
lean_ctor_set(v_reuseFailAlloc_518_, 1, v___x_514_);
v___x_516_ = v_reuseFailAlloc_518_;
goto v_reusejp_515_;
}
v_reusejp_515_:
{
lean_object* v___x_517_; 
v___x_517_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable_spec__0___redArg(v_b_459_, v_val_513_, v___x_516_);
v_a_466_ = v___x_517_;
goto v___jp_465_;
}
}
else
{
lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_522_; 
lean_dec(v___x_512_);
lean_dec_ref(v___x_510_);
lean_del_object(v___x_487_);
v___x_519_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__2___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__2___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__2___closed__4);
lean_inc(v_a_472_);
v___x_520_ = l_Lean_MessageData_ofName(v_a_472_);
if (v_isShared_484_ == 0)
{
lean_ctor_set_tag(v___x_483_, 7);
lean_ctor_set(v___x_483_, 1, v___x_520_);
lean_ctor_set(v___x_483_, 0, v___x_519_);
v___x_522_ = v___x_483_;
goto v_reusejp_521_;
}
else
{
lean_object* v_reuseFailAlloc_534_; 
v_reuseFailAlloc_534_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_534_, 0, v___x_519_);
lean_ctor_set(v_reuseFailAlloc_534_, 1, v___x_520_);
v___x_522_ = v_reuseFailAlloc_534_;
goto v_reusejp_521_;
}
v_reusejp_521_:
{
lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; 
v___x_523_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__2___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__2___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__2___closed__8);
v___x_524_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_524_, 0, v___x_522_);
lean_ctor_set(v___x_524_, 1, v___x_523_);
v___x_525_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__1___redArg(v___x_524_, v___y_460_, v___y_461_, v___y_462_, v___y_463_);
if (lean_obj_tag(v___x_525_) == 0)
{
lean_dec_ref_known(v___x_525_, 1);
v_a_466_ = v_b_459_;
goto v___jp_465_;
}
else
{
lean_object* v_a_526_; lean_object* v___x_528_; uint8_t v_isShared_529_; uint8_t v_isSharedCheck_533_; 
lean_dec_ref(v_b_459_);
v_a_526_ = lean_ctor_get(v___x_525_, 0);
v_isSharedCheck_533_ = !lean_is_exclusive(v___x_525_);
if (v_isSharedCheck_533_ == 0)
{
v___x_528_ = v___x_525_;
v_isShared_529_ = v_isSharedCheck_533_;
goto v_resetjp_527_;
}
else
{
lean_inc(v_a_526_);
lean_dec(v___x_525_);
v___x_528_ = lean_box(0);
v_isShared_529_ = v_isSharedCheck_533_;
goto v_resetjp_527_;
}
v_resetjp_527_:
{
lean_object* v___x_531_; 
if (v_isShared_529_ == 0)
{
v___x_531_ = v___x_528_;
goto v_reusejp_530_;
}
else
{
lean_object* v_reuseFailAlloc_532_; 
v_reuseFailAlloc_532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_532_, 0, v_a_526_);
v___x_531_ = v_reuseFailAlloc_532_;
goto v_reusejp_530_;
}
v_reusejp_530_:
{
return v___x_531_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_535_; lean_object* v___x_537_; uint8_t v_isShared_538_; uint8_t v_isSharedCheck_542_; 
lean_del_object(v___x_487_);
lean_del_object(v___x_483_);
lean_dec_ref(v_b_459_);
v_a_535_ = lean_ctor_get(v___x_489_, 0);
v_isSharedCheck_542_ = !lean_is_exclusive(v___x_489_);
if (v_isSharedCheck_542_ == 0)
{
v___x_537_ = v___x_489_;
v_isShared_538_ = v_isSharedCheck_542_;
goto v_resetjp_536_;
}
else
{
lean_inc(v_a_535_);
lean_dec(v___x_489_);
v___x_537_ = lean_box(0);
v_isShared_538_ = v_isSharedCheck_542_;
goto v_resetjp_536_;
}
v_resetjp_536_:
{
lean_object* v___x_540_; 
if (v_isShared_538_ == 0)
{
v___x_540_ = v___x_537_;
goto v_reusejp_539_;
}
else
{
lean_object* v_reuseFailAlloc_541_; 
v_reuseFailAlloc_541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_541_, 0, v_a_535_);
v___x_540_ = v_reuseFailAlloc_541_;
goto v_reusejp_539_;
}
v_reusejp_539_:
{
return v___x_540_;
}
}
}
}
}
}
else
{
lean_object* v_a_547_; lean_object* v___x_549_; uint8_t v_isShared_550_; uint8_t v_isSharedCheck_554_; 
lean_dec_ref(v_b_459_);
v_a_547_ = lean_ctor_get(v___x_479_, 0);
v_isSharedCheck_554_ = !lean_is_exclusive(v___x_479_);
if (v_isSharedCheck_554_ == 0)
{
v___x_549_ = v___x_479_;
v_isShared_550_ = v_isSharedCheck_554_;
goto v_resetjp_548_;
}
else
{
lean_inc(v_a_547_);
lean_dec(v___x_479_);
v___x_549_ = lean_box(0);
v_isShared_550_ = v_isSharedCheck_554_;
goto v_resetjp_548_;
}
v_resetjp_548_:
{
lean_object* v___x_552_; 
if (v_isShared_550_ == 0)
{
v___x_552_ = v___x_549_;
goto v_reusejp_551_;
}
else
{
lean_object* v_reuseFailAlloc_553_; 
v_reuseFailAlloc_553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_553_, 0, v_a_547_);
v___x_552_ = v_reuseFailAlloc_553_;
goto v_reusejp_551_;
}
v_reusejp_551_:
{
return v___x_552_;
}
}
}
}
else
{
lean_object* v_a_555_; lean_object* v___x_557_; uint8_t v_isShared_558_; uint8_t v_isSharedCheck_562_; 
lean_dec_ref(v_b_459_);
v_a_555_ = lean_ctor_get(v___x_475_, 0);
v_isSharedCheck_562_ = !lean_is_exclusive(v___x_475_);
if (v_isSharedCheck_562_ == 0)
{
v___x_557_ = v___x_475_;
v_isShared_558_ = v_isSharedCheck_562_;
goto v_resetjp_556_;
}
else
{
lean_inc(v_a_555_);
lean_dec(v___x_475_);
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
else
{
lean_object* v_a_563_; lean_object* v___x_565_; uint8_t v_isShared_566_; uint8_t v_isSharedCheck_570_; 
lean_dec_ref(v_b_459_);
v_a_563_ = lean_ctor_get(v___x_473_, 0);
v_isSharedCheck_570_ = !lean_is_exclusive(v___x_473_);
if (v_isSharedCheck_570_ == 0)
{
v___x_565_ = v___x_473_;
v_isShared_566_ = v_isSharedCheck_570_;
goto v_resetjp_564_;
}
else
{
lean_inc(v_a_563_);
lean_dec(v___x_473_);
v___x_565_ = lean_box(0);
v_isShared_566_ = v_isSharedCheck_570_;
goto v_resetjp_564_;
}
v_resetjp_564_:
{
lean_object* v___x_568_; 
if (v_isShared_566_ == 0)
{
v___x_568_ = v___x_565_;
goto v_reusejp_567_;
}
else
{
lean_object* v_reuseFailAlloc_569_; 
v_reuseFailAlloc_569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_569_, 0, v_a_563_);
v___x_568_ = v_reuseFailAlloc_569_;
goto v_reusejp_567_;
}
v_reusejp_567_:
{
return v___x_568_;
}
}
}
}
v___jp_465_:
{
size_t v___x_467_; size_t v___x_468_; 
v___x_467_ = ((size_t)1ULL);
v___x_468_ = lean_usize_add(v_i_458_, v___x_467_);
v_i_458_ = v___x_468_;
v_b_459_ = v_a_466_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__2___boxed(lean_object* v_as_571_, lean_object* v_sz_572_, lean_object* v_i_573_, lean_object* v_b_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_){
_start:
{
size_t v_sz_boxed_580_; size_t v_i_boxed_581_; lean_object* v_res_582_; 
v_sz_boxed_580_ = lean_unbox_usize(v_sz_572_);
lean_dec(v_sz_572_);
v_i_boxed_581_ = lean_unbox_usize(v_i_573_);
lean_dec(v_i_573_);
v_res_582_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__2(v_as_571_, v_sz_boxed_580_, v_i_boxed_581_, v_b_574_, v___y_575_, v___y_576_, v___y_577_, v___y_578_);
lean_dec(v___y_578_);
lean_dec_ref(v___y_577_);
lean_dec(v___y_576_);
lean_dec_ref(v___y_575_);
lean_dec_ref(v_as_571_);
return v_res_582_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals___closed__0(void){
_start:
{
lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; 
v___x_583_ = lean_box(0);
v___x_584_ = lean_unsigned_to_nat(16u);
v___x_585_ = lean_mk_array(v___x_584_, v___x_583_);
return v___x_585_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals___closed__1(void){
_start:
{
lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v_m_588_; 
v___x_586_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals___closed__0, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals___closed__0_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals___closed__0);
v___x_587_ = lean_unsigned_to_nat(0u);
v_m_588_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_m_588_, 0, v___x_587_);
lean_ctor_set(v_m_588_, 1, v___x_586_);
return v_m_588_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals(lean_object* v_names_589_, lean_object* v_a_590_, lean_object* v_a_591_, lean_object* v_a_592_, lean_object* v_a_593_){
_start:
{
lean_object* v_m_595_; size_t v_sz_596_; size_t v___x_597_; lean_object* v___x_598_; 
v_m_595_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals___closed__1, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals___closed__1_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals___closed__1);
v_sz_596_ = lean_array_size(v_names_589_);
v___x_597_ = ((size_t)0ULL);
v___x_598_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__2(v_names_589_, v_sz_596_, v___x_597_, v_m_595_, v_a_590_, v_a_591_, v_a_592_, v_a_593_);
return v___x_598_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals___boxed(lean_object* v_names_599_, lean_object* v_a_600_, lean_object* v_a_601_, lean_object* v_a_602_, lean_object* v_a_603_, lean_object* v_a_604_){
_start:
{
lean_object* v_res_605_; 
v_res_605_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals(v_names_599_, v_a_600_, v_a_601_, v_a_602_, v_a_603_);
lean_dec(v_a_603_);
lean_dec_ref(v_a_602_);
lean_dec(v_a_601_);
lean_dec_ref(v_a_600_);
lean_dec_ref(v_names_599_);
return v_res_605_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__1(lean_object* v_00_u03b1_606_, lean_object* v_msg_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_){
_start:
{
lean_object* v___x_613_; 
v___x_613_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__1___redArg(v_msg_607_, v___y_608_, v___y_609_, v___y_610_, v___y_611_);
return v___x_613_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__1___boxed(lean_object* v_00_u03b1_614_, lean_object* v_msg_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_){
_start:
{
lean_object* v_res_621_; 
v_res_621_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__1(v_00_u03b1_614_, v_msg_615_, v___y_616_, v___y_617_, v___y_618_, v___y_619_);
lean_dec(v___y_619_);
lean_dec_ref(v___y_618_);
lean_dec(v___y_617_);
lean_dec_ref(v___y_616_);
return v_res_621_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_go___lam__0(uint8_t v_isZero_622_, lean_object* v_x_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_, lean_object* v___y_629_, lean_object* v___y_630_, lean_object* v___y_631_, lean_object* v___y_632_){
_start:
{
lean_object* v___x_634_; lean_object* v___x_635_; 
v___x_634_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_634_, 0, v_isZero_622_);
lean_ctor_set_uint8(v___x_634_, 1, v_isZero_622_);
v___x_635_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_635_, 0, v___x_634_);
return v___x_635_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_go___lam__0___boxed(lean_object* v_isZero_636_, lean_object* v_x_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_, lean_object* v___y_646_, lean_object* v___y_647_){
_start:
{
uint8_t v_isZero_boxed_648_; lean_object* v_res_649_; 
v_isZero_boxed_648_ = lean_unbox(v_isZero_636_);
v_res_649_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_go___lam__0(v_isZero_boxed_648_, v_x_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_, v___y_642_, v___y_643_, v___y_644_, v___y_645_, v___y_646_);
lean_dec(v___y_646_);
lean_dec_ref(v___y_645_);
lean_dec(v___y_644_);
lean_dec_ref(v___y_643_);
lean_dec(v___y_642_);
lean_dec_ref(v___y_641_);
lean_dec(v___y_640_);
lean_dec_ref(v___y_639_);
lean_dec(v___y_638_);
lean_dec_ref(v_x_637_);
return v_res_649_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_go_spec__0___redArg(lean_object* v_msg_650_, lean_object* v___y_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_){
_start:
{
lean_object* v_ref_656_; lean_object* v___x_657_; lean_object* v_a_658_; lean_object* v___x_660_; uint8_t v_isShared_661_; uint8_t v_isSharedCheck_666_; 
v_ref_656_ = lean_ctor_get(v___y_653_, 5);
v___x_657_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__1_spec__1(v_msg_650_, v___y_651_, v___y_652_, v___y_653_, v___y_654_);
v_a_658_ = lean_ctor_get(v___x_657_, 0);
v_isSharedCheck_666_ = !lean_is_exclusive(v___x_657_);
if (v_isSharedCheck_666_ == 0)
{
v___x_660_ = v___x_657_;
v_isShared_661_ = v_isSharedCheck_666_;
goto v_resetjp_659_;
}
else
{
lean_inc(v_a_658_);
lean_dec(v___x_657_);
v___x_660_ = lean_box(0);
v_isShared_661_ = v_isSharedCheck_666_;
goto v_resetjp_659_;
}
v_resetjp_659_:
{
lean_object* v___x_662_; lean_object* v___x_664_; 
lean_inc(v_ref_656_);
v___x_662_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_662_, 0, v_ref_656_);
lean_ctor_set(v___x_662_, 1, v_a_658_);
if (v_isShared_661_ == 0)
{
lean_ctor_set_tag(v___x_660_, 1);
lean_ctor_set(v___x_660_, 0, v___x_662_);
v___x_664_ = v___x_660_;
goto v_reusejp_663_;
}
else
{
lean_object* v_reuseFailAlloc_665_; 
v_reuseFailAlloc_665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_665_, 0, v___x_662_);
v___x_664_ = v_reuseFailAlloc_665_;
goto v_reusejp_663_;
}
v_reusejp_663_:
{
return v___x_664_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_go_spec__0___redArg___boxed(lean_object* v_msg_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_){
_start:
{
lean_object* v_res_673_; 
v_res_673_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_go_spec__0___redArg(v_msg_667_, v___y_668_, v___y_669_, v___y_670_, v___y_671_);
lean_dec(v___y_671_);
lean_dec_ref(v___y_670_);
lean_dec(v___y_669_);
lean_dec_ref(v___y_668_);
return v_res_673_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_go___closed__1(void){
_start:
{
lean_object* v___x_675_; lean_object* v___x_676_; 
v___x_675_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_go___closed__0));
v___x_676_ = l_Lean_stringToMessageData(v___x_675_);
return v___x_676_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_go(lean_object* v_step_680_, lean_object* v_e_u2080_681_, lean_object* v_cur_682_, lean_object* v_proof_x3f_683_, lean_object* v_a_684_, lean_object* v_a_685_, lean_object* v_a_686_, lean_object* v_a_687_, lean_object* v_a_688_, lean_object* v_a_689_, lean_object* v_a_690_){
_start:
{
lean_object* v_zero_692_; uint8_t v_isZero_693_; 
v_zero_692_ = lean_unsigned_to_nat(0u);
v_isZero_693_ = lean_nat_dec_eq(v_a_684_, v_zero_692_);
if (v_isZero_693_ == 1)
{
lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; 
lean_dec(v_a_684_);
lean_dec(v_proof_x3f_683_);
lean_dec_ref(v_e_u2080_681_);
lean_dec_ref(v_step_680_);
v___x_694_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_go___closed__1, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_go___closed__1_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_go___closed__1);
v___x_695_ = l_Lean_indentExpr(v_cur_682_);
v___x_696_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_696_, 0, v___x_694_);
lean_ctor_set(v___x_696_, 1, v___x_695_);
v___x_697_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_go_spec__0___redArg(v___x_696_, v_a_687_, v_a_688_, v_a_689_, v_a_690_);
return v___x_697_;
}
else
{
lean_object* v___x_698_; lean_object* v___f_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; 
v___x_698_ = lean_box(v_isZero_693_);
v___f_699_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_go___lam__0___boxed), 12, 1);
lean_closure_set(v___f_699_, 0, v___x_698_);
lean_inc_ref(v_step_680_);
lean_inc_ref(v_cur_682_);
v___x_700_ = lean_apply_1(v_step_680_, v_cur_682_);
lean_inc_ref(v___f_699_);
v___x_701_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_701_, 0, v___f_699_);
lean_ctor_set(v___x_701_, 1, v___f_699_);
v___x_702_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_go___closed__2));
v___x_703_ = l_Lean_Meta_Sym_Simp_SimpM_run_x27___redArg(v___x_700_, v___x_701_, v___x_702_, v_a_685_, v_a_686_, v_a_687_, v_a_688_, v_a_689_, v_a_690_);
if (lean_obj_tag(v___x_703_) == 0)
{
lean_object* v_a_704_; lean_object* v___x_706_; uint8_t v_isShared_707_; uint8_t v_isSharedCheck_737_; 
v_a_704_ = lean_ctor_get(v___x_703_, 0);
v_isSharedCheck_737_ = !lean_is_exclusive(v___x_703_);
if (v_isSharedCheck_737_ == 0)
{
v___x_706_ = v___x_703_;
v_isShared_707_ = v_isSharedCheck_737_;
goto v_resetjp_705_;
}
else
{
lean_inc(v_a_704_);
lean_dec(v___x_703_);
v___x_706_ = lean_box(0);
v_isShared_707_ = v_isSharedCheck_737_;
goto v_resetjp_705_;
}
v_resetjp_705_:
{
if (lean_obj_tag(v_a_704_) == 0)
{
lean_object* v___x_708_; lean_object* v___x_710_; 
lean_dec_ref_known(v_a_704_, 0);
lean_dec(v_a_684_);
lean_dec_ref(v_e_u2080_681_);
lean_dec_ref(v_step_680_);
v___x_708_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_708_, 0, v_cur_682_);
lean_ctor_set(v___x_708_, 1, v_proof_x3f_683_);
if (v_isShared_707_ == 0)
{
lean_ctor_set(v___x_706_, 0, v___x_708_);
v___x_710_ = v___x_706_;
goto v_reusejp_709_;
}
else
{
lean_object* v_reuseFailAlloc_711_; 
v_reuseFailAlloc_711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_711_, 0, v___x_708_);
v___x_710_ = v_reuseFailAlloc_711_;
goto v_reusejp_709_;
}
v_reusejp_709_:
{
return v___x_710_;
}
}
else
{
lean_object* v_e_x27_712_; lean_object* v_proof_713_; lean_object* v_one_714_; lean_object* v_n_715_; lean_object* v_proof_717_; lean_object* v___y_718_; lean_object* v___y_719_; lean_object* v___y_720_; lean_object* v___y_721_; lean_object* v___y_722_; lean_object* v___y_723_; 
lean_del_object(v___x_706_);
v_e_x27_712_ = lean_ctor_get(v_a_704_, 0);
lean_inc_ref(v_e_x27_712_);
v_proof_713_ = lean_ctor_get(v_a_704_, 1);
lean_inc_ref(v_proof_713_);
lean_dec_ref_known(v_a_704_, 2);
v_one_714_ = lean_unsigned_to_nat(1u);
v_n_715_ = lean_nat_sub(v_a_684_, v_one_714_);
lean_dec(v_a_684_);
if (lean_obj_tag(v_proof_x3f_683_) == 0)
{
lean_dec_ref(v_cur_682_);
v_proof_717_ = v_proof_713_;
v___y_718_ = v_a_685_;
v___y_719_ = v_a_686_;
v___y_720_ = v_a_687_;
v___y_721_ = v_a_688_;
v___y_722_ = v_a_689_;
v___y_723_ = v_a_690_;
goto v___jp_716_;
}
else
{
lean_object* v_val_726_; lean_object* v___x_727_; 
v_val_726_ = lean_ctor_get(v_proof_x3f_683_, 0);
lean_inc(v_val_726_);
lean_dec_ref_known(v_proof_x3f_683_, 1);
lean_inc_ref(v_e_x27_712_);
lean_inc_ref(v_e_u2080_681_);
v___x_727_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v_e_u2080_681_, v_cur_682_, v_val_726_, v_e_x27_712_, v_proof_713_, v_a_685_, v_a_686_, v_a_687_, v_a_688_, v_a_689_, v_a_690_);
if (lean_obj_tag(v___x_727_) == 0)
{
lean_object* v_a_728_; 
v_a_728_ = lean_ctor_get(v___x_727_, 0);
lean_inc(v_a_728_);
lean_dec_ref_known(v___x_727_, 1);
v_proof_717_ = v_a_728_;
v___y_718_ = v_a_685_;
v___y_719_ = v_a_686_;
v___y_720_ = v_a_687_;
v___y_721_ = v_a_688_;
v___y_722_ = v_a_689_;
v___y_723_ = v_a_690_;
goto v___jp_716_;
}
else
{
lean_object* v_a_729_; lean_object* v___x_731_; uint8_t v_isShared_732_; uint8_t v_isSharedCheck_736_; 
lean_dec(v_n_715_);
lean_dec_ref(v_e_x27_712_);
lean_dec_ref(v_e_u2080_681_);
lean_dec_ref(v_step_680_);
v_a_729_ = lean_ctor_get(v___x_727_, 0);
v_isSharedCheck_736_ = !lean_is_exclusive(v___x_727_);
if (v_isSharedCheck_736_ == 0)
{
v___x_731_ = v___x_727_;
v_isShared_732_ = v_isSharedCheck_736_;
goto v_resetjp_730_;
}
else
{
lean_inc(v_a_729_);
lean_dec(v___x_727_);
v___x_731_ = lean_box(0);
v_isShared_732_ = v_isSharedCheck_736_;
goto v_resetjp_730_;
}
v_resetjp_730_:
{
lean_object* v___x_734_; 
if (v_isShared_732_ == 0)
{
v___x_734_ = v___x_731_;
goto v_reusejp_733_;
}
else
{
lean_object* v_reuseFailAlloc_735_; 
v_reuseFailAlloc_735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_735_, 0, v_a_729_);
v___x_734_ = v_reuseFailAlloc_735_;
goto v_reusejp_733_;
}
v_reusejp_733_:
{
return v___x_734_;
}
}
}
}
v___jp_716_:
{
lean_object* v___x_724_; 
v___x_724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_724_, 0, v_proof_717_);
v_cur_682_ = v_e_x27_712_;
v_proof_x3f_683_ = v___x_724_;
v_a_684_ = v_n_715_;
v_a_685_ = v___y_718_;
v_a_686_ = v___y_719_;
v_a_687_ = v___y_720_;
v_a_688_ = v___y_721_;
v_a_689_ = v___y_722_;
v_a_690_ = v___y_723_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_738_; lean_object* v___x_740_; uint8_t v_isShared_741_; uint8_t v_isSharedCheck_745_; 
lean_dec(v_a_684_);
lean_dec(v_proof_x3f_683_);
lean_dec_ref(v_cur_682_);
lean_dec_ref(v_e_u2080_681_);
lean_dec_ref(v_step_680_);
v_a_738_ = lean_ctor_get(v___x_703_, 0);
v_isSharedCheck_745_ = !lean_is_exclusive(v___x_703_);
if (v_isSharedCheck_745_ == 0)
{
v___x_740_ = v___x_703_;
v_isShared_741_ = v_isSharedCheck_745_;
goto v_resetjp_739_;
}
else
{
lean_inc(v_a_738_);
lean_dec(v___x_703_);
v___x_740_ = lean_box(0);
v_isShared_741_ = v_isSharedCheck_745_;
goto v_resetjp_739_;
}
v_resetjp_739_:
{
lean_object* v___x_743_; 
if (v_isShared_741_ == 0)
{
v___x_743_ = v___x_740_;
goto v_reusejp_742_;
}
else
{
lean_object* v_reuseFailAlloc_744_; 
v_reuseFailAlloc_744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_744_, 0, v_a_738_);
v___x_743_ = v_reuseFailAlloc_744_;
goto v_reusejp_742_;
}
v_reusejp_742_:
{
return v___x_743_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_go___boxed(lean_object* v_step_746_, lean_object* v_e_u2080_747_, lean_object* v_cur_748_, lean_object* v_proof_x3f_749_, lean_object* v_a_750_, lean_object* v_a_751_, lean_object* v_a_752_, lean_object* v_a_753_, lean_object* v_a_754_, lean_object* v_a_755_, lean_object* v_a_756_, lean_object* v_a_757_){
_start:
{
lean_object* v_res_758_; 
v_res_758_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_go(v_step_746_, v_e_u2080_747_, v_cur_748_, v_proof_x3f_749_, v_a_750_, v_a_751_, v_a_752_, v_a_753_, v_a_754_, v_a_755_, v_a_756_);
lean_dec(v_a_756_);
lean_dec_ref(v_a_755_);
lean_dec(v_a_754_);
lean_dec_ref(v_a_753_);
lean_dec(v_a_752_);
lean_dec_ref(v_a_751_);
return v_res_758_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_go_spec__0(lean_object* v_00_u03b1_759_, lean_object* v_msg_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_){
_start:
{
lean_object* v___x_768_; 
v___x_768_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_go_spec__0___redArg(v_msg_760_, v___y_763_, v___y_764_, v___y_765_, v___y_766_);
return v___x_768_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_go_spec__0___boxed(lean_object* v_00_u03b1_769_, lean_object* v_msg_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_){
_start:
{
lean_object* v_res_778_; 
v_res_778_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_go_spec__0(v_00_u03b1_769_, v_msg_770_, v___y_771_, v___y_772_, v___y_773_, v___y_774_, v___y_775_, v___y_776_);
lean_dec(v___y_776_);
lean_dec_ref(v___y_775_);
lean_dec(v___y_774_);
lean_dec_ref(v___y_773_);
lean_dec(v___y_772_);
lean_dec_ref(v___y_771_);
return v_res_778_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_spec__0___redArg(lean_object* v_as_779_, size_t v_i_780_, size_t v_stop_781_, lean_object* v_b_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_){
_start:
{
uint8_t v___x_788_; 
v___x_788_ = lean_usize_dec_eq(v_i_780_, v_stop_781_);
if (v___x_788_ == 0)
{
lean_object* v___x_789_; lean_object* v___x_790_; 
v___x_789_ = lean_array_uget_borrowed(v_as_779_, v_i_780_);
lean_inc(v___x_789_);
v___x_790_ = l_Lean_Meta_Sym_Simp_mkTheoremFromDecl(v___x_789_, v___y_783_, v___y_784_, v___y_785_, v___y_786_);
if (lean_obj_tag(v___x_790_) == 0)
{
lean_object* v_a_791_; lean_object* v___x_792_; size_t v___x_793_; size_t v___x_794_; 
v_a_791_ = lean_ctor_get(v___x_790_, 0);
lean_inc(v_a_791_);
lean_dec_ref_known(v___x_790_, 1);
v___x_792_ = l_Lean_Meta_Sym_Simp_Theorems_insert(v_b_782_, v_a_791_);
v___x_793_ = ((size_t)1ULL);
v___x_794_ = lean_usize_add(v_i_780_, v___x_793_);
v_i_780_ = v___x_794_;
v_b_782_ = v___x_792_;
goto _start;
}
else
{
lean_object* v_a_796_; lean_object* v___x_798_; uint8_t v_isShared_799_; uint8_t v_isSharedCheck_803_; 
lean_dec_ref(v_b_782_);
v_a_796_ = lean_ctor_get(v___x_790_, 0);
v_isSharedCheck_803_ = !lean_is_exclusive(v___x_790_);
if (v_isSharedCheck_803_ == 0)
{
v___x_798_ = v___x_790_;
v_isShared_799_ = v_isSharedCheck_803_;
goto v_resetjp_797_;
}
else
{
lean_inc(v_a_796_);
lean_dec(v___x_790_);
v___x_798_ = lean_box(0);
v_isShared_799_ = v_isSharedCheck_803_;
goto v_resetjp_797_;
}
v_resetjp_797_:
{
lean_object* v___x_801_; 
if (v_isShared_799_ == 0)
{
v___x_801_ = v___x_798_;
goto v_reusejp_800_;
}
else
{
lean_object* v_reuseFailAlloc_802_; 
v_reuseFailAlloc_802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_802_, 0, v_a_796_);
v___x_801_ = v_reuseFailAlloc_802_;
goto v_reusejp_800_;
}
v_reusejp_800_:
{
return v___x_801_;
}
}
}
}
else
{
lean_object* v___x_804_; 
v___x_804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_804_, 0, v_b_782_);
return v___x_804_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_spec__0___redArg___boxed(lean_object* v_as_805_, lean_object* v_i_806_, lean_object* v_stop_807_, lean_object* v_b_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_){
_start:
{
size_t v_i_boxed_814_; size_t v_stop_boxed_815_; lean_object* v_res_816_; 
v_i_boxed_814_ = lean_unbox_usize(v_i_806_);
lean_dec(v_i_806_);
v_stop_boxed_815_ = lean_unbox_usize(v_stop_807_);
lean_dec(v_stop_807_);
v_res_816_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_spec__0___redArg(v_as_805_, v_i_boxed_814_, v_stop_boxed_815_, v_b_808_, v___y_809_, v___y_810_, v___y_811_, v___y_812_);
lean_dec(v___y_812_);
lean_dec_ref(v___y_811_);
lean_dec(v___y_810_);
lean_dec_ref(v___y_809_);
lean_dec_ref(v_as_805_);
return v_res_816_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp___closed__1(void){
_start:
{
lean_object* v___x_818_; 
v___x_818_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_818_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp___closed__2(void){
_start:
{
lean_object* v___x_819_; lean_object* v___x_820_; 
v___x_819_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp___closed__1, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp___closed__1_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp___closed__1);
v___x_820_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_820_, 0, v___x_819_);
return v___x_820_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp(lean_object* v_rewrites_821_, lean_object* v_e_822_, lean_object* v_fuel_823_, lean_object* v_a_824_, lean_object* v_a_825_, lean_object* v_a_826_, lean_object* v_a_827_, lean_object* v_a_828_, lean_object* v_a_829_){
_start:
{
lean_object* v_a_832_; lean_object* v___y_848_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; uint8_t v___x_861_; 
v___x_858_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp___closed__2, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp___closed__2_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp___closed__2);
v___x_859_ = lean_unsigned_to_nat(0u);
v___x_860_ = lean_array_get_size(v_rewrites_821_);
v___x_861_ = lean_nat_dec_lt(v___x_859_, v___x_860_);
if (v___x_861_ == 0)
{
v_a_832_ = v___x_858_;
goto v___jp_831_;
}
else
{
uint8_t v___x_862_; 
v___x_862_ = lean_nat_dec_le(v___x_860_, v___x_860_);
if (v___x_862_ == 0)
{
if (v___x_861_ == 0)
{
v_a_832_ = v___x_858_;
goto v___jp_831_;
}
else
{
size_t v___x_863_; size_t v___x_864_; lean_object* v___x_865_; 
v___x_863_ = ((size_t)0ULL);
v___x_864_ = lean_usize_of_nat(v___x_860_);
v___x_865_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_spec__0___redArg(v_rewrites_821_, v___x_863_, v___x_864_, v___x_858_, v_a_826_, v_a_827_, v_a_828_, v_a_829_);
v___y_848_ = v___x_865_;
goto v___jp_847_;
}
}
else
{
size_t v___x_866_; size_t v___x_867_; lean_object* v___x_868_; 
v___x_866_ = ((size_t)0ULL);
v___x_867_ = lean_usize_of_nat(v___x_860_);
v___x_868_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_spec__0___redArg(v_rewrites_821_, v___x_866_, v___x_867_, v___x_858_, v_a_826_, v_a_827_, v_a_828_, v_a_829_);
v___y_848_ = v___x_868_;
goto v___jp_847_;
}
}
v___jp_831_:
{
lean_object* v___x_833_; 
v___x_833_ = l_Lean_Meta_Sym_shareCommon(v_e_822_, v_a_824_, v_a_825_, v_a_826_, v_a_827_, v_a_828_, v_a_829_);
if (lean_obj_tag(v___x_833_) == 0)
{
lean_object* v_a_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; 
v_a_834_ = lean_ctor_get(v___x_833_, 0);
lean_inc_n(v_a_834_, 2);
lean_dec_ref_known(v___x_833_, 1);
v___x_835_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp___closed__0));
v___x_836_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Simp_Theorems_rewrite___boxed), 13, 2);
lean_closure_set(v___x_836_, 0, v_a_832_);
lean_closure_set(v___x_836_, 1, v___x_835_);
v___x_837_ = lean_box(0);
v___x_838_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_go(v___x_836_, v_a_834_, v_a_834_, v___x_837_, v_fuel_823_, v_a_824_, v_a_825_, v_a_826_, v_a_827_, v_a_828_, v_a_829_);
return v___x_838_;
}
else
{
lean_object* v_a_839_; lean_object* v___x_841_; uint8_t v_isShared_842_; uint8_t v_isSharedCheck_846_; 
lean_dec_ref(v_a_832_);
lean_dec(v_fuel_823_);
v_a_839_ = lean_ctor_get(v___x_833_, 0);
v_isSharedCheck_846_ = !lean_is_exclusive(v___x_833_);
if (v_isSharedCheck_846_ == 0)
{
v___x_841_ = v___x_833_;
v_isShared_842_ = v_isSharedCheck_846_;
goto v_resetjp_840_;
}
else
{
lean_inc(v_a_839_);
lean_dec(v___x_833_);
v___x_841_ = lean_box(0);
v_isShared_842_ = v_isSharedCheck_846_;
goto v_resetjp_840_;
}
v_resetjp_840_:
{
lean_object* v___x_844_; 
if (v_isShared_842_ == 0)
{
v___x_844_ = v___x_841_;
goto v_reusejp_843_;
}
else
{
lean_object* v_reuseFailAlloc_845_; 
v_reuseFailAlloc_845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_845_, 0, v_a_839_);
v___x_844_ = v_reuseFailAlloc_845_;
goto v_reusejp_843_;
}
v_reusejp_843_:
{
return v___x_844_;
}
}
}
}
v___jp_847_:
{
if (lean_obj_tag(v___y_848_) == 0)
{
lean_object* v_a_849_; 
v_a_849_ = lean_ctor_get(v___y_848_, 0);
lean_inc(v_a_849_);
lean_dec_ref_known(v___y_848_, 1);
v_a_832_ = v_a_849_;
goto v___jp_831_;
}
else
{
lean_object* v_a_850_; lean_object* v___x_852_; uint8_t v_isShared_853_; uint8_t v_isSharedCheck_857_; 
lean_dec(v_fuel_823_);
lean_dec_ref(v_e_822_);
v_a_850_ = lean_ctor_get(v___y_848_, 0);
v_isSharedCheck_857_ = !lean_is_exclusive(v___y_848_);
if (v_isSharedCheck_857_ == 0)
{
v___x_852_ = v___y_848_;
v_isShared_853_ = v_isSharedCheck_857_;
goto v_resetjp_851_;
}
else
{
lean_inc(v_a_850_);
lean_dec(v___y_848_);
v___x_852_ = lean_box(0);
v_isShared_853_ = v_isSharedCheck_857_;
goto v_resetjp_851_;
}
v_resetjp_851_:
{
lean_object* v___x_855_; 
if (v_isShared_853_ == 0)
{
v___x_855_ = v___x_852_;
goto v_reusejp_854_;
}
else
{
lean_object* v_reuseFailAlloc_856_; 
v_reuseFailAlloc_856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_856_, 0, v_a_850_);
v___x_855_ = v_reuseFailAlloc_856_;
goto v_reusejp_854_;
}
v_reusejp_854_:
{
return v___x_855_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp___boxed(lean_object* v_rewrites_869_, lean_object* v_e_870_, lean_object* v_fuel_871_, lean_object* v_a_872_, lean_object* v_a_873_, lean_object* v_a_874_, lean_object* v_a_875_, lean_object* v_a_876_, lean_object* v_a_877_, lean_object* v_a_878_){
_start:
{
lean_object* v_res_879_; 
v_res_879_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp(v_rewrites_869_, v_e_870_, v_fuel_871_, v_a_872_, v_a_873_, v_a_874_, v_a_875_, v_a_876_, v_a_877_);
lean_dec(v_a_877_);
lean_dec_ref(v_a_876_);
lean_dec(v_a_875_);
lean_dec_ref(v_a_874_);
lean_dec(v_a_873_);
lean_dec_ref(v_a_872_);
lean_dec_ref(v_rewrites_869_);
return v_res_879_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_spec__0(lean_object* v_as_880_, size_t v_i_881_, size_t v_stop_882_, lean_object* v_b_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_){
_start:
{
lean_object* v___x_891_; 
v___x_891_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_spec__0___redArg(v_as_880_, v_i_881_, v_stop_882_, v_b_883_, v___y_886_, v___y_887_, v___y_888_, v___y_889_);
return v___x_891_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_spec__0___boxed(lean_object* v_as_892_, lean_object* v_i_893_, lean_object* v_stop_894_, lean_object* v_b_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_){
_start:
{
size_t v_i_boxed_903_; size_t v_stop_boxed_904_; lean_object* v_res_905_; 
v_i_boxed_903_ = lean_unbox_usize(v_i_893_);
lean_dec(v_i_893_);
v_stop_boxed_904_ = lean_unbox_usize(v_stop_894_);
lean_dec(v_stop_894_);
v_res_905_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_spec__0(v_as_892_, v_i_boxed_903_, v_stop_boxed_904_, v_b_895_, v___y_896_, v___y_897_, v___y_898_, v___y_899_, v___y_900_, v___y_901_);
lean_dec(v___y_901_);
lean_dec_ref(v___y_900_);
lean_dec(v___y_899_);
lean_dec_ref(v___y_898_);
lean_dec(v___y_897_);
lean_dec_ref(v___y_896_);
lean_dec_ref(v_as_892_);
return v_res_905_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply___lam__0(lean_object* v_s_906_, lean_object* v_a_907_, lean_object* v_pre_908_, lean_object* v_u_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_){
_start:
{
lean_object* v___x_915_; 
lean_inc_ref(v_u_909_);
v___x_915_ = l_Lean_Meta_mkEq(v_u_909_, v_s_906_, v___y_910_, v___y_911_, v___y_912_, v___y_913_);
if (lean_obj_tag(v___x_915_) == 0)
{
lean_object* v_a_916_; lean_object* v___x_918_; uint8_t v_isShared_919_; uint8_t v_isSharedCheck_947_; 
v_a_916_ = lean_ctor_get(v___x_915_, 0);
v_isSharedCheck_947_ = !lean_is_exclusive(v___x_915_);
if (v_isSharedCheck_947_ == 0)
{
v___x_918_ = v___x_915_;
v_isShared_919_ = v_isSharedCheck_947_;
goto v_resetjp_917_;
}
else
{
lean_inc(v_a_916_);
lean_dec(v___x_915_);
v___x_918_ = lean_box(0);
v_isShared_919_ = v_isSharedCheck_947_;
goto v_resetjp_917_;
}
v_resetjp_917_:
{
lean_object* v___x_920_; lean_object* v___x_922_; 
v___x_920_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_ofProp___closed__2));
if (v_isShared_919_ == 0)
{
lean_ctor_set_tag(v___x_918_, 1);
lean_ctor_set(v___x_918_, 0, v_a_907_);
v___x_922_ = v___x_918_;
goto v_reusejp_921_;
}
else
{
lean_object* v_reuseFailAlloc_946_; 
v_reuseFailAlloc_946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_946_, 0, v_a_907_);
v___x_922_ = v_reuseFailAlloc_946_;
goto v_reusejp_921_;
}
v_reusejp_921_:
{
lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; 
v___x_923_ = lean_box(0);
v___x_924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_924_, 0, v_a_916_);
v___x_925_ = lean_unsigned_to_nat(3u);
v___x_926_ = lean_mk_empty_array_with_capacity(v___x_925_);
v___x_927_ = lean_array_push(v___x_926_, v___x_922_);
v___x_928_ = lean_array_push(v___x_927_, v___x_923_);
v___x_929_ = lean_array_push(v___x_928_, v___x_924_);
v___x_930_ = l_Lean_Meta_mkAppOptM(v___x_920_, v___x_929_, v___y_910_, v___y_911_, v___y_912_, v___y_913_);
if (lean_obj_tag(v___x_930_) == 0)
{
lean_object* v_a_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; 
v_a_931_ = lean_ctor_get(v___x_930_, 0);
lean_inc(v_a_931_);
lean_dec_ref_known(v___x_930_, 1);
v___x_932_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_meet___closed__3));
v___x_933_ = lean_unsigned_to_nat(2u);
v___x_934_ = lean_mk_empty_array_with_capacity(v___x_933_);
v___x_935_ = lean_array_push(v___x_934_, v_a_931_);
v___x_936_ = lean_array_push(v___x_935_, v_pre_908_);
v___x_937_ = l_Lean_Meta_mkAppM(v___x_932_, v___x_936_, v___y_910_, v___y_911_, v___y_912_, v___y_913_);
if (lean_obj_tag(v___x_937_) == 0)
{
lean_object* v_a_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; uint8_t v___x_942_; uint8_t v___x_943_; uint8_t v___x_944_; lean_object* v___x_945_; 
v_a_938_ = lean_ctor_get(v___x_937_, 0);
lean_inc(v_a_938_);
lean_dec_ref_known(v___x_937_, 1);
v___x_939_ = lean_unsigned_to_nat(1u);
v___x_940_ = lean_mk_empty_array_with_capacity(v___x_939_);
v___x_941_ = lean_array_push(v___x_940_, v_u_909_);
v___x_942_ = 0;
v___x_943_ = 1;
v___x_944_ = 1;
v___x_945_ = l_Lean_Meta_mkLambdaFVars(v___x_941_, v_a_938_, v___x_942_, v___x_943_, v___x_942_, v___x_943_, v___x_944_, v___y_910_, v___y_911_, v___y_912_, v___y_913_);
lean_dec_ref(v___x_941_);
return v___x_945_;
}
else
{
lean_dec_ref(v_u_909_);
return v___x_937_;
}
}
else
{
lean_dec_ref(v_u_909_);
lean_dec_ref(v_pre_908_);
return v___x_930_;
}
}
}
}
else
{
lean_dec_ref(v_u_909_);
lean_dec_ref(v_pre_908_);
lean_dec_ref(v_a_907_);
return v___x_915_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply___lam__0___boxed(lean_object* v_s_948_, lean_object* v_a_949_, lean_object* v_pre_950_, lean_object* v_u_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_){
_start:
{
lean_object* v_res_957_; 
v_res_957_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply___lam__0(v_s_948_, v_a_949_, v_pre_950_, v_u_951_, v___y_952_, v___y_953_, v___y_954_, v___y_955_);
lean_dec(v___y_955_);
lean_dec_ref(v___y_954_);
lean_dec(v___y_953_);
lean_dec_ref(v___y_952_);
return v_res_957_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply_spec__0_spec__0___redArg___lam__0(lean_object* v_k_958_, lean_object* v_b_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_){
_start:
{
lean_object* v___x_965_; 
lean_inc(v___y_963_);
lean_inc_ref(v___y_962_);
lean_inc(v___y_961_);
lean_inc_ref(v___y_960_);
v___x_965_ = lean_apply_6(v_k_958_, v_b_959_, v___y_960_, v___y_961_, v___y_962_, v___y_963_, lean_box(0));
return v___x_965_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply_spec__0_spec__0___redArg___lam__0___boxed(lean_object* v_k_966_, lean_object* v_b_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_){
_start:
{
lean_object* v_res_973_; 
v_res_973_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply_spec__0_spec__0___redArg___lam__0(v_k_966_, v_b_967_, v___y_968_, v___y_969_, v___y_970_, v___y_971_);
lean_dec(v___y_971_);
lean_dec_ref(v___y_970_);
lean_dec(v___y_969_);
lean_dec_ref(v___y_968_);
return v_res_973_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply_spec__0_spec__0___redArg(lean_object* v_name_974_, uint8_t v_bi_975_, lean_object* v_type_976_, lean_object* v_k_977_, uint8_t v_kind_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_){
_start:
{
lean_object* v___f_984_; lean_object* v___x_985_; 
v___f_984_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply_spec__0_spec__0___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_984_, 0, v_k_977_);
v___x_985_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_974_, v_bi_975_, v_type_976_, v___f_984_, v_kind_978_, v___y_979_, v___y_980_, v___y_981_, v___y_982_);
if (lean_obj_tag(v___x_985_) == 0)
{
lean_object* v_a_986_; lean_object* v___x_988_; uint8_t v_isShared_989_; uint8_t v_isSharedCheck_993_; 
v_a_986_ = lean_ctor_get(v___x_985_, 0);
v_isSharedCheck_993_ = !lean_is_exclusive(v___x_985_);
if (v_isSharedCheck_993_ == 0)
{
v___x_988_ = v___x_985_;
v_isShared_989_ = v_isSharedCheck_993_;
goto v_resetjp_987_;
}
else
{
lean_inc(v_a_986_);
lean_dec(v___x_985_);
v___x_988_ = lean_box(0);
v_isShared_989_ = v_isSharedCheck_993_;
goto v_resetjp_987_;
}
v_resetjp_987_:
{
lean_object* v___x_991_; 
if (v_isShared_989_ == 0)
{
v___x_991_ = v___x_988_;
goto v_reusejp_990_;
}
else
{
lean_object* v_reuseFailAlloc_992_; 
v_reuseFailAlloc_992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_992_, 0, v_a_986_);
v___x_991_ = v_reuseFailAlloc_992_;
goto v_reusejp_990_;
}
v_reusejp_990_:
{
return v___x_991_;
}
}
}
else
{
lean_object* v_a_994_; lean_object* v___x_996_; uint8_t v_isShared_997_; uint8_t v_isSharedCheck_1001_; 
v_a_994_ = lean_ctor_get(v___x_985_, 0);
v_isSharedCheck_1001_ = !lean_is_exclusive(v___x_985_);
if (v_isSharedCheck_1001_ == 0)
{
v___x_996_ = v___x_985_;
v_isShared_997_ = v_isSharedCheck_1001_;
goto v_resetjp_995_;
}
else
{
lean_inc(v_a_994_);
lean_dec(v___x_985_);
v___x_996_ = lean_box(0);
v_isShared_997_ = v_isSharedCheck_1001_;
goto v_resetjp_995_;
}
v_resetjp_995_:
{
lean_object* v___x_999_; 
if (v_isShared_997_ == 0)
{
v___x_999_ = v___x_996_;
goto v_reusejp_998_;
}
else
{
lean_object* v_reuseFailAlloc_1000_; 
v_reuseFailAlloc_1000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1000_, 0, v_a_994_);
v___x_999_ = v_reuseFailAlloc_1000_;
goto v_reusejp_998_;
}
v_reusejp_998_:
{
return v___x_999_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply_spec__0_spec__0___redArg___boxed(lean_object* v_name_1002_, lean_object* v_bi_1003_, lean_object* v_type_1004_, lean_object* v_k_1005_, lean_object* v_kind_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_){
_start:
{
uint8_t v_bi_boxed_1012_; uint8_t v_kind_boxed_1013_; lean_object* v_res_1014_; 
v_bi_boxed_1012_ = lean_unbox(v_bi_1003_);
v_kind_boxed_1013_ = lean_unbox(v_kind_1006_);
v_res_1014_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply_spec__0_spec__0___redArg(v_name_1002_, v_bi_boxed_1012_, v_type_1004_, v_k_1005_, v_kind_boxed_1013_, v___y_1007_, v___y_1008_, v___y_1009_, v___y_1010_);
lean_dec(v___y_1010_);
lean_dec_ref(v___y_1009_);
lean_dec(v___y_1008_);
lean_dec_ref(v___y_1007_);
return v_res_1014_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply_spec__0___redArg(lean_object* v_name_1015_, lean_object* v_type_1016_, lean_object* v_k_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_){
_start:
{
uint8_t v___x_1023_; uint8_t v___x_1024_; lean_object* v___x_1025_; 
v___x_1023_ = 0;
v___x_1024_ = 0;
v___x_1025_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply_spec__0_spec__0___redArg(v_name_1015_, v___x_1023_, v_type_1016_, v_k_1017_, v___x_1024_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_);
return v___x_1025_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply_spec__0___redArg___boxed(lean_object* v_name_1026_, lean_object* v_type_1027_, lean_object* v_k_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_){
_start:
{
lean_object* v_res_1034_; 
v_res_1034_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply_spec__0___redArg(v_name_1026_, v_type_1027_, v_k_1028_, v___y_1029_, v___y_1030_, v___y_1031_, v___y_1032_);
lean_dec(v___y_1032_);
lean_dec_ref(v___y_1031_);
lean_dec(v___y_1030_);
lean_dec_ref(v___y_1029_);
return v_res_1034_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply___closed__1(void){
_start:
{
lean_object* v___x_1036_; lean_object* v___x_1037_; 
v___x_1036_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply___closed__0));
v___x_1037_ = l_Lean_stringToMessageData(v___x_1036_);
return v___x_1037_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply(lean_object* v_introThm_1046_, lean_object* v_opAs_1047_, lean_object* v_pre_1048_, lean_object* v_ss_1049_, lean_object* v_a_1050_, lean_object* v_a_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_){
_start:
{
if (lean_obj_tag(v_ss_1049_) == 0)
{
lean_object* v___x_1055_; 
lean_inc(v_introThm_1046_);
v___x_1055_ = l_Lean_Meta_mkConstWithFreshMVarLevels(v_introThm_1046_, v_a_1050_, v_a_1051_, v_a_1052_, v_a_1053_);
if (lean_obj_tag(v___x_1055_) == 0)
{
lean_object* v_a_1056_; lean_object* v___x_1057_; 
v_a_1056_ = lean_ctor_get(v___x_1055_, 0);
lean_inc_n(v_a_1056_, 2);
lean_dec_ref_known(v___x_1055_, 1);
lean_inc(v_a_1053_);
lean_inc_ref(v_a_1052_);
lean_inc(v_a_1051_);
lean_inc_ref(v_a_1050_);
v___x_1057_ = lean_infer_type(v_a_1056_, v_a_1050_, v_a_1051_, v_a_1052_, v_a_1053_);
if (lean_obj_tag(v___x_1057_) == 0)
{
lean_object* v_a_1058_; uint8_t v___x_1059_; lean_object* v___x_1060_; 
v_a_1058_ = lean_ctor_get(v___x_1057_, 0);
lean_inc(v_a_1058_);
lean_dec_ref_known(v___x_1057_, 1);
v___x_1059_ = 0;
v___x_1060_ = l_Lean_Meta_forallMetaTelescope(v_a_1058_, v___x_1059_, v_a_1050_, v_a_1051_, v_a_1052_, v_a_1053_);
if (lean_obj_tag(v___x_1060_) == 0)
{
lean_object* v_a_1061_; lean_object* v___x_1063_; uint8_t v_isShared_1064_; uint8_t v_isSharedCheck_1120_; 
v_a_1061_ = lean_ctor_get(v___x_1060_, 0);
v_isSharedCheck_1120_ = !lean_is_exclusive(v___x_1060_);
if (v_isSharedCheck_1120_ == 0)
{
v___x_1063_ = v___x_1060_;
v_isShared_1064_ = v_isSharedCheck_1120_;
goto v_resetjp_1062_;
}
else
{
lean_inc(v_a_1061_);
lean_dec(v___x_1060_);
v___x_1063_ = lean_box(0);
v_isShared_1064_ = v_isSharedCheck_1120_;
goto v_resetjp_1062_;
}
v_resetjp_1062_:
{
lean_object* v_fst_1065_; lean_object* v_snd_1066_; lean_object* v___x_1068_; uint8_t v_isShared_1069_; uint8_t v_isSharedCheck_1119_; 
v_fst_1065_ = lean_ctor_get(v_a_1061_, 0);
v_snd_1066_ = lean_ctor_get(v_a_1061_, 1);
v_isSharedCheck_1119_ = !lean_is_exclusive(v_a_1061_);
if (v_isSharedCheck_1119_ == 0)
{
v___x_1068_ = v_a_1061_;
v_isShared_1069_ = v_isSharedCheck_1119_;
goto v_resetjp_1067_;
}
else
{
lean_inc(v_snd_1066_);
lean_inc(v_fst_1065_);
lean_dec(v_a_1061_);
v___x_1068_ = lean_box(0);
v_isShared_1069_ = v_isSharedCheck_1119_;
goto v_resetjp_1067_;
}
v_resetjp_1067_:
{
lean_object* v_snd_1075_; lean_object* v___x_1077_; uint8_t v_isShared_1078_; uint8_t v_isSharedCheck_1117_; 
v_snd_1075_ = lean_ctor_get(v_snd_1066_, 1);
v_isSharedCheck_1117_ = !lean_is_exclusive(v_snd_1066_);
if (v_isSharedCheck_1117_ == 0)
{
lean_object* v_unused_1118_; 
v_unused_1118_ = lean_ctor_get(v_snd_1066_, 0);
lean_dec(v_unused_1118_);
v___x_1077_ = v_snd_1066_;
v_isShared_1078_ = v_isSharedCheck_1117_;
goto v_resetjp_1076_;
}
else
{
lean_inc(v_snd_1075_);
lean_dec(v_snd_1066_);
v___x_1077_ = lean_box(0);
v_isShared_1078_ = v_isSharedCheck_1117_;
goto v_resetjp_1076_;
}
v___jp_1070_:
{
lean_object* v___x_1071_; lean_object* v___x_1073_; 
v___x_1071_ = l_Lean_mkAppN(v_a_1056_, v_fst_1065_);
lean_dec(v_fst_1065_);
if (v_isShared_1064_ == 0)
{
lean_ctor_set(v___x_1063_, 0, v___x_1071_);
v___x_1073_ = v___x_1063_;
goto v_reusejp_1072_;
}
else
{
lean_object* v_reuseFailAlloc_1074_; 
v_reuseFailAlloc_1074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1074_, 0, v___x_1071_);
v___x_1073_ = v_reuseFailAlloc_1074_;
goto v_reusejp_1072_;
}
v_reusejp_1072_:
{
return v___x_1073_;
}
}
v_resetjp_1076_:
{
lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; 
v___x_1079_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__2___closed__2));
v___x_1080_ = lean_unsigned_to_nat(2u);
v___x_1081_ = lean_mk_empty_array_with_capacity(v___x_1080_);
v___x_1082_ = lean_array_push(v___x_1081_, v_pre_1048_);
v___x_1083_ = lean_array_push(v___x_1082_, v_opAs_1047_);
v___x_1084_ = l_Lean_Meta_mkAppM(v___x_1079_, v___x_1083_, v_a_1050_, v_a_1051_, v_a_1052_, v_a_1053_);
if (lean_obj_tag(v___x_1084_) == 0)
{
lean_object* v_a_1085_; lean_object* v___x_1086_; 
v_a_1085_ = lean_ctor_get(v___x_1084_, 0);
lean_inc_n(v_a_1085_, 2);
lean_dec_ref_known(v___x_1084_, 1);
v___x_1086_ = l_Lean_Meta_isExprDefEq(v_snd_1075_, v_a_1085_, v_a_1050_, v_a_1051_, v_a_1052_, v_a_1053_);
if (lean_obj_tag(v___x_1086_) == 0)
{
lean_object* v_a_1087_; uint8_t v___x_1088_; 
v_a_1087_ = lean_ctor_get(v___x_1086_, 0);
lean_inc(v_a_1087_);
lean_dec_ref_known(v___x_1086_, 1);
v___x_1088_ = lean_unbox(v_a_1087_);
lean_dec(v_a_1087_);
if (v___x_1088_ == 0)
{
lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1092_; 
v___x_1089_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__2___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__2___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__2___closed__4);
v___x_1090_ = l_Lean_MessageData_ofName(v_introThm_1046_);
if (v_isShared_1078_ == 0)
{
lean_ctor_set_tag(v___x_1077_, 7);
lean_ctor_set(v___x_1077_, 1, v___x_1090_);
lean_ctor_set(v___x_1077_, 0, v___x_1089_);
v___x_1092_ = v___x_1077_;
goto v_reusejp_1091_;
}
else
{
lean_object* v_reuseFailAlloc_1108_; 
v_reuseFailAlloc_1108_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1108_, 0, v___x_1089_);
lean_ctor_set(v_reuseFailAlloc_1108_, 1, v___x_1090_);
v___x_1092_ = v_reuseFailAlloc_1108_;
goto v_reusejp_1091_;
}
v_reusejp_1091_:
{
lean_object* v___x_1093_; lean_object* v___x_1095_; 
v___x_1093_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply___closed__1, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply___closed__1_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply___closed__1);
if (v_isShared_1069_ == 0)
{
lean_ctor_set_tag(v___x_1068_, 7);
lean_ctor_set(v___x_1068_, 1, v___x_1093_);
lean_ctor_set(v___x_1068_, 0, v___x_1092_);
v___x_1095_ = v___x_1068_;
goto v_reusejp_1094_;
}
else
{
lean_object* v_reuseFailAlloc_1107_; 
v_reuseFailAlloc_1107_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1107_, 0, v___x_1092_);
lean_ctor_set(v_reuseFailAlloc_1107_, 1, v___x_1093_);
v___x_1095_ = v_reuseFailAlloc_1107_;
goto v_reusejp_1094_;
}
v_reusejp_1094_:
{
lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; 
v___x_1096_ = l_Lean_MessageData_ofExpr(v_a_1085_);
v___x_1097_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1097_, 0, v___x_1095_);
lean_ctor_set(v___x_1097_, 1, v___x_1096_);
v___x_1098_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__1___redArg(v___x_1097_, v_a_1050_, v_a_1051_, v_a_1052_, v_a_1053_);
if (lean_obj_tag(v___x_1098_) == 0)
{
lean_dec_ref_known(v___x_1098_, 1);
goto v___jp_1070_;
}
else
{
lean_object* v_a_1099_; lean_object* v___x_1101_; uint8_t v_isShared_1102_; uint8_t v_isSharedCheck_1106_; 
lean_dec(v_fst_1065_);
lean_del_object(v___x_1063_);
lean_dec(v_a_1056_);
v_a_1099_ = lean_ctor_get(v___x_1098_, 0);
v_isSharedCheck_1106_ = !lean_is_exclusive(v___x_1098_);
if (v_isSharedCheck_1106_ == 0)
{
v___x_1101_ = v___x_1098_;
v_isShared_1102_ = v_isSharedCheck_1106_;
goto v_resetjp_1100_;
}
else
{
lean_inc(v_a_1099_);
lean_dec(v___x_1098_);
v___x_1101_ = lean_box(0);
v_isShared_1102_ = v_isSharedCheck_1106_;
goto v_resetjp_1100_;
}
v_resetjp_1100_:
{
lean_object* v___x_1104_; 
if (v_isShared_1102_ == 0)
{
v___x_1104_ = v___x_1101_;
goto v_reusejp_1103_;
}
else
{
lean_object* v_reuseFailAlloc_1105_; 
v_reuseFailAlloc_1105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1105_, 0, v_a_1099_);
v___x_1104_ = v_reuseFailAlloc_1105_;
goto v_reusejp_1103_;
}
v_reusejp_1103_:
{
return v___x_1104_;
}
}
}
}
}
}
else
{
lean_dec(v_a_1085_);
lean_del_object(v___x_1077_);
lean_del_object(v___x_1068_);
lean_dec(v_introThm_1046_);
goto v___jp_1070_;
}
}
else
{
lean_object* v_a_1109_; lean_object* v___x_1111_; uint8_t v_isShared_1112_; uint8_t v_isSharedCheck_1116_; 
lean_dec(v_a_1085_);
lean_del_object(v___x_1077_);
lean_del_object(v___x_1068_);
lean_dec(v_fst_1065_);
lean_del_object(v___x_1063_);
lean_dec(v_a_1056_);
lean_dec(v_introThm_1046_);
v_a_1109_ = lean_ctor_get(v___x_1086_, 0);
v_isSharedCheck_1116_ = !lean_is_exclusive(v___x_1086_);
if (v_isSharedCheck_1116_ == 0)
{
v___x_1111_ = v___x_1086_;
v_isShared_1112_ = v_isSharedCheck_1116_;
goto v_resetjp_1110_;
}
else
{
lean_inc(v_a_1109_);
lean_dec(v___x_1086_);
v___x_1111_ = lean_box(0);
v_isShared_1112_ = v_isSharedCheck_1116_;
goto v_resetjp_1110_;
}
v_resetjp_1110_:
{
lean_object* v___x_1114_; 
if (v_isShared_1112_ == 0)
{
v___x_1114_ = v___x_1111_;
goto v_reusejp_1113_;
}
else
{
lean_object* v_reuseFailAlloc_1115_; 
v_reuseFailAlloc_1115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1115_, 0, v_a_1109_);
v___x_1114_ = v_reuseFailAlloc_1115_;
goto v_reusejp_1113_;
}
v_reusejp_1113_:
{
return v___x_1114_;
}
}
}
}
else
{
lean_del_object(v___x_1077_);
lean_dec(v_snd_1075_);
lean_del_object(v___x_1068_);
lean_dec(v_fst_1065_);
lean_del_object(v___x_1063_);
lean_dec(v_a_1056_);
lean_dec(v_introThm_1046_);
return v___x_1084_;
}
}
}
}
}
else
{
lean_object* v_a_1121_; lean_object* v___x_1123_; uint8_t v_isShared_1124_; uint8_t v_isSharedCheck_1128_; 
lean_dec(v_a_1056_);
lean_dec_ref(v_pre_1048_);
lean_dec_ref(v_opAs_1047_);
lean_dec(v_introThm_1046_);
v_a_1121_ = lean_ctor_get(v___x_1060_, 0);
v_isSharedCheck_1128_ = !lean_is_exclusive(v___x_1060_);
if (v_isSharedCheck_1128_ == 0)
{
v___x_1123_ = v___x_1060_;
v_isShared_1124_ = v_isSharedCheck_1128_;
goto v_resetjp_1122_;
}
else
{
lean_inc(v_a_1121_);
lean_dec(v___x_1060_);
v___x_1123_ = lean_box(0);
v_isShared_1124_ = v_isSharedCheck_1128_;
goto v_resetjp_1122_;
}
v_resetjp_1122_:
{
lean_object* v___x_1126_; 
if (v_isShared_1124_ == 0)
{
v___x_1126_ = v___x_1123_;
goto v_reusejp_1125_;
}
else
{
lean_object* v_reuseFailAlloc_1127_; 
v_reuseFailAlloc_1127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1127_, 0, v_a_1121_);
v___x_1126_ = v_reuseFailAlloc_1127_;
goto v_reusejp_1125_;
}
v_reusejp_1125_:
{
return v___x_1126_;
}
}
}
}
else
{
lean_dec(v_a_1056_);
lean_dec_ref(v_pre_1048_);
lean_dec_ref(v_opAs_1047_);
lean_dec(v_introThm_1046_);
return v___x_1057_;
}
}
else
{
lean_dec_ref(v_pre_1048_);
lean_dec_ref(v_opAs_1047_);
lean_dec(v_introThm_1046_);
return v___x_1055_;
}
}
else
{
lean_object* v___x_1129_; 
lean_inc(v_a_1053_);
lean_inc_ref(v_a_1052_);
lean_inc(v_a_1051_);
lean_inc_ref(v_a_1050_);
lean_inc_ref(v_pre_1048_);
v___x_1129_ = lean_infer_type(v_pre_1048_, v_a_1050_, v_a_1051_, v_a_1052_, v_a_1053_);
if (lean_obj_tag(v___x_1129_) == 0)
{
lean_object* v_a_1130_; lean_object* v___x_1131_; lean_object* v_s_1132_; lean_object* v___x_1133_; 
v_a_1130_ = lean_ctor_get(v___x_1129_, 0);
lean_inc(v_a_1130_);
lean_dec_ref_known(v___x_1129_, 1);
v___x_1131_ = l_Lean_instInhabitedExpr;
v_s_1132_ = l_List_getLast_x21___redArg(v___x_1131_, v_ss_1049_);
lean_inc(v_a_1053_);
lean_inc_ref(v_a_1052_);
lean_inc(v_a_1051_);
lean_inc_ref(v_a_1050_);
lean_inc(v_s_1132_);
v___x_1133_ = lean_infer_type(v_s_1132_, v_a_1050_, v_a_1051_, v_a_1052_, v_a_1053_);
if (lean_obj_tag(v___x_1133_) == 0)
{
lean_object* v_a_1134_; lean_object* v___f_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; 
v_a_1134_ = lean_ctor_get(v___x_1133_, 0);
lean_inc(v_a_1134_);
lean_dec_ref_known(v___x_1133_, 1);
lean_inc_ref(v_pre_1048_);
lean_inc(v_s_1132_);
v___f_1135_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply___lam__0___boxed), 9, 3);
lean_closure_set(v___f_1135_, 0, v_s_1132_);
lean_closure_set(v___f_1135_, 1, v_a_1130_);
lean_closure_set(v___f_1135_, 2, v_pre_1048_);
v___x_1136_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply___closed__3));
v___x_1137_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply_spec__0___redArg(v___x_1136_, v_a_1134_, v___f_1135_, v_a_1050_, v_a_1051_, v_a_1052_, v_a_1053_);
if (lean_obj_tag(v___x_1137_) == 0)
{
lean_object* v_a_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v_init_1141_; lean_object* v___x_1142_; lean_object* v_Q_1143_; lean_object* v___x_1144_; 
v_a_1138_ = lean_ctor_get(v___x_1137_, 0);
lean_inc(v_a_1138_);
lean_dec_ref_known(v___x_1137_, 1);
v___x_1139_ = lean_array_mk(v_ss_1049_);
v___x_1140_ = lean_array_pop(v___x_1139_);
v_init_1141_ = lean_array_to_list(v___x_1140_);
lean_inc(v_init_1141_);
v___x_1142_ = lean_array_mk(v_init_1141_);
lean_inc_ref(v_opAs_1047_);
v_Q_1143_ = l_Lean_mkAppN(v_opAs_1047_, v___x_1142_);
lean_dec_ref(v___x_1142_);
v___x_1144_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply(v_introThm_1046_, v_opAs_1047_, v_a_1138_, v_init_1141_, v_a_1050_, v_a_1051_, v_a_1052_, v_a_1053_);
if (lean_obj_tag(v___x_1144_) == 0)
{
lean_object* v_a_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; 
v_a_1145_ = lean_ctor_get(v___x_1144_, 0);
lean_inc(v_a_1145_);
lean_dec_ref_known(v___x_1144_, 1);
v___x_1146_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply___closed__5));
v___x_1147_ = lean_unsigned_to_nat(4u);
v___x_1148_ = lean_mk_empty_array_with_capacity(v___x_1147_);
v___x_1149_ = lean_array_push(v___x_1148_, v_s_1132_);
v___x_1150_ = lean_array_push(v___x_1149_, v_pre_1048_);
v___x_1151_ = lean_array_push(v___x_1150_, v_Q_1143_);
v___x_1152_ = lean_array_push(v___x_1151_, v_a_1145_);
v___x_1153_ = l_Lean_Meta_mkAppM(v___x_1146_, v___x_1152_, v_a_1050_, v_a_1051_, v_a_1052_, v_a_1053_);
return v___x_1153_;
}
else
{
lean_dec_ref(v_Q_1143_);
lean_dec(v_s_1132_);
lean_dec_ref(v_pre_1048_);
return v___x_1144_;
}
}
else
{
lean_dec(v_s_1132_);
lean_dec(v_ss_1049_);
lean_dec_ref(v_pre_1048_);
lean_dec_ref(v_opAs_1047_);
lean_dec(v_introThm_1046_);
return v___x_1137_;
}
}
else
{
lean_dec(v_s_1132_);
lean_dec(v_a_1130_);
lean_dec(v_ss_1049_);
lean_dec_ref(v_pre_1048_);
lean_dec_ref(v_opAs_1047_);
lean_dec(v_introThm_1046_);
return v___x_1133_;
}
}
else
{
lean_dec(v_ss_1049_);
lean_dec_ref(v_pre_1048_);
lean_dec_ref(v_opAs_1047_);
lean_dec(v_introThm_1046_);
return v___x_1129_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply___boxed(lean_object* v_introThm_1154_, lean_object* v_opAs_1155_, lean_object* v_pre_1156_, lean_object* v_ss_1157_, lean_object* v_a_1158_, lean_object* v_a_1159_, lean_object* v_a_1160_, lean_object* v_a_1161_, lean_object* v_a_1162_){
_start:
{
lean_object* v_res_1163_; 
v_res_1163_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply(v_introThm_1154_, v_opAs_1155_, v_pre_1156_, v_ss_1157_, v_a_1158_, v_a_1159_, v_a_1160_, v_a_1161_);
lean_dec(v_a_1161_);
lean_dec_ref(v_a_1160_);
lean_dec(v_a_1159_);
lean_dec_ref(v_a_1158_);
return v_res_1163_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply_spec__0_spec__0(lean_object* v_00_u03b1_1164_, lean_object* v_name_1165_, uint8_t v_bi_1166_, lean_object* v_type_1167_, lean_object* v_k_1168_, uint8_t v_kind_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_){
_start:
{
lean_object* v___x_1175_; 
v___x_1175_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply_spec__0_spec__0___redArg(v_name_1165_, v_bi_1166_, v_type_1167_, v_k_1168_, v_kind_1169_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_);
return v___x_1175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1176_, lean_object* v_name_1177_, lean_object* v_bi_1178_, lean_object* v_type_1179_, lean_object* v_k_1180_, lean_object* v_kind_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_){
_start:
{
uint8_t v_bi_boxed_1187_; uint8_t v_kind_boxed_1188_; lean_object* v_res_1189_; 
v_bi_boxed_1187_ = lean_unbox(v_bi_1178_);
v_kind_boxed_1188_ = lean_unbox(v_kind_1181_);
v_res_1189_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply_spec__0_spec__0(v_00_u03b1_1176_, v_name_1177_, v_bi_boxed_1187_, v_type_1179_, v_k_1180_, v_kind_boxed_1188_, v___y_1182_, v___y_1183_, v___y_1184_, v___y_1185_);
lean_dec(v___y_1185_);
lean_dec_ref(v___y_1184_);
lean_dec(v___y_1183_);
lean_dec_ref(v___y_1182_);
return v_res_1189_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply_spec__0(lean_object* v_00_u03b1_1190_, lean_object* v_name_1191_, lean_object* v_type_1192_, lean_object* v_k_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_){
_start:
{
lean_object* v___x_1199_; 
v___x_1199_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply_spec__0___redArg(v_name_1191_, v_type_1192_, v_k_1193_, v___y_1194_, v___y_1195_, v___y_1196_, v___y_1197_);
return v___x_1199_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply_spec__0___boxed(lean_object* v_00_u03b1_1200_, lean_object* v_name_1201_, lean_object* v_type_1202_, lean_object* v_k_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_){
_start:
{
lean_object* v_res_1209_; 
v_res_1209_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply_spec__0(v_00_u03b1_1200_, v_name_1201_, v_type_1202_, v_k_1203_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_);
lean_dec(v___y_1207_);
lean_dec_ref(v___y_1206_);
lean_dec(v___y_1205_);
lean_dec_ref(v___y_1204_);
return v_res_1209_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__1_spec__1___redArg(lean_object* v_a_1210_, lean_object* v_x_1211_){
_start:
{
if (lean_obj_tag(v_x_1211_) == 0)
{
lean_object* v___x_1212_; 
v___x_1212_ = lean_box(0);
return v___x_1212_;
}
else
{
lean_object* v_key_1213_; lean_object* v_value_1214_; lean_object* v_tail_1215_; uint8_t v___x_1216_; 
v_key_1213_ = lean_ctor_get(v_x_1211_, 0);
v_value_1214_ = lean_ctor_get(v_x_1211_, 1);
v_tail_1215_ = lean_ctor_get(v_x_1211_, 2);
v___x_1216_ = lean_name_eq(v_key_1213_, v_a_1210_);
if (v___x_1216_ == 0)
{
v_x_1211_ = v_tail_1215_;
goto _start;
}
else
{
lean_object* v___x_1218_; 
lean_inc(v_value_1214_);
v___x_1218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1218_, 0, v_value_1214_);
return v___x_1218_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__1_spec__1___redArg___boxed(lean_object* v_a_1219_, lean_object* v_x_1220_){
_start:
{
lean_object* v_res_1221_; 
v_res_1221_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__1_spec__1___redArg(v_a_1219_, v_x_1220_);
lean_dec(v_x_1220_);
lean_dec(v_a_1219_);
return v_res_1221_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__1___redArg(lean_object* v_m_1222_, lean_object* v_a_1223_){
_start:
{
lean_object* v_buckets_1224_; lean_object* v___x_1225_; uint64_t v___y_1227_; 
v_buckets_1224_ = lean_ctor_get(v_m_1222_, 1);
v___x_1225_ = lean_array_get_size(v_buckets_1224_);
if (lean_obj_tag(v_a_1223_) == 0)
{
uint64_t v___x_1241_; 
v___x_1241_ = lean_uint64_once(&l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable_spec__0_spec__1_spec__2_spec__4___redArg___closed__0, &l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable_spec__0_spec__1_spec__2_spec__4___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable_spec__0_spec__1_spec__2_spec__4___redArg___closed__0);
v___y_1227_ = v___x_1241_;
goto v___jp_1226_;
}
else
{
uint64_t v_hash_1242_; 
v_hash_1242_ = lean_ctor_get_uint64(v_a_1223_, sizeof(void*)*2);
v___y_1227_ = v_hash_1242_;
goto v___jp_1226_;
}
v___jp_1226_:
{
uint64_t v___x_1228_; uint64_t v___x_1229_; uint64_t v_fold_1230_; uint64_t v___x_1231_; uint64_t v___x_1232_; uint64_t v___x_1233_; size_t v___x_1234_; size_t v___x_1235_; size_t v___x_1236_; size_t v___x_1237_; size_t v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; 
v___x_1228_ = 32ULL;
v___x_1229_ = lean_uint64_shift_right(v___y_1227_, v___x_1228_);
v_fold_1230_ = lean_uint64_xor(v___y_1227_, v___x_1229_);
v___x_1231_ = 16ULL;
v___x_1232_ = lean_uint64_shift_right(v_fold_1230_, v___x_1231_);
v___x_1233_ = lean_uint64_xor(v_fold_1230_, v___x_1232_);
v___x_1234_ = lean_uint64_to_usize(v___x_1233_);
v___x_1235_ = lean_usize_of_nat(v___x_1225_);
v___x_1236_ = ((size_t)1ULL);
v___x_1237_ = lean_usize_sub(v___x_1235_, v___x_1236_);
v___x_1238_ = lean_usize_land(v___x_1234_, v___x_1237_);
v___x_1239_ = lean_array_uget_borrowed(v_buckets_1224_, v___x_1238_);
v___x_1240_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__1_spec__1___redArg(v_a_1223_, v___x_1239_);
return v___x_1240_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__1___redArg___boxed(lean_object* v_m_1243_, lean_object* v_a_1244_){
_start:
{
lean_object* v_res_1245_; 
v_res_1245_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__1___redArg(v_m_1243_, v_a_1244_);
lean_dec(v_a_1244_);
lean_dec_ref(v_m_1243_);
return v_res_1245_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__0___redArg(size_t v_sz_1246_, size_t v_i_1247_, lean_object* v_bs_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_){
_start:
{
uint8_t v___x_1254_; 
v___x_1254_ = lean_usize_dec_lt(v_i_1247_, v_sz_1246_);
if (v___x_1254_ == 0)
{
lean_object* v___x_1255_; 
v___x_1255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1255_, 0, v_bs_1248_);
return v___x_1255_;
}
else
{
lean_object* v_v_1256_; lean_object* v___x_1257_; lean_object* v_bs_x27_1258_; lean_object* v___y_1260_; lean_object* v___x_1274_; 
v_v_1256_ = lean_array_uget(v_bs_1248_, v_i_1247_);
v___x_1257_ = lean_unsigned_to_nat(0u);
v_bs_x27_1258_ = lean_array_uset(v_bs_1248_, v_i_1247_, v___x_1257_);
lean_inc(v___y_1252_);
lean_inc_ref(v___y_1251_);
lean_inc(v___y_1250_);
lean_inc_ref(v___y_1249_);
v___x_1274_ = lean_infer_type(v_v_1256_, v___y_1249_, v___y_1250_, v___y_1251_, v___y_1252_);
if (lean_obj_tag(v___x_1274_) == 0)
{
lean_object* v_a_1275_; lean_object* v___x_1277_; uint8_t v_isShared_1278_; uint8_t v_isSharedCheck_1285_; 
v_a_1275_ = lean_ctor_get(v___x_1274_, 0);
v_isSharedCheck_1285_ = !lean_is_exclusive(v___x_1274_);
if (v_isSharedCheck_1285_ == 0)
{
v___x_1277_ = v___x_1274_;
v_isShared_1278_ = v_isSharedCheck_1285_;
goto v_resetjp_1276_;
}
else
{
lean_inc(v_a_1275_);
lean_dec(v___x_1274_);
v___x_1277_ = lean_box(0);
v_isShared_1278_ = v_isSharedCheck_1285_;
goto v_resetjp_1276_;
}
v_resetjp_1276_:
{
lean_object* v___x_1280_; 
if (v_isShared_1278_ == 0)
{
lean_ctor_set_tag(v___x_1277_, 1);
v___x_1280_ = v___x_1277_;
goto v_reusejp_1279_;
}
else
{
lean_object* v_reuseFailAlloc_1284_; 
v_reuseFailAlloc_1284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1284_, 0, v_a_1275_);
v___x_1280_ = v_reuseFailAlloc_1284_;
goto v_reusejp_1279_;
}
v_reusejp_1279_:
{
uint8_t v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; 
v___x_1281_ = 0;
v___x_1282_ = lean_box(0);
v___x_1283_ = l_Lean_Meta_mkFreshExprMVar(v___x_1280_, v___x_1281_, v___x_1282_, v___y_1249_, v___y_1250_, v___y_1251_, v___y_1252_);
v___y_1260_ = v___x_1283_;
goto v___jp_1259_;
}
}
}
else
{
v___y_1260_ = v___x_1274_;
goto v___jp_1259_;
}
v___jp_1259_:
{
if (lean_obj_tag(v___y_1260_) == 0)
{
lean_object* v_a_1261_; size_t v___x_1262_; size_t v___x_1263_; lean_object* v___x_1264_; 
v_a_1261_ = lean_ctor_get(v___y_1260_, 0);
lean_inc(v_a_1261_);
lean_dec_ref_known(v___y_1260_, 1);
v___x_1262_ = ((size_t)1ULL);
v___x_1263_ = lean_usize_add(v_i_1247_, v___x_1262_);
v___x_1264_ = lean_array_uset(v_bs_x27_1258_, v_i_1247_, v_a_1261_);
v_i_1247_ = v___x_1263_;
v_bs_1248_ = v___x_1264_;
goto _start;
}
else
{
lean_object* v_a_1266_; lean_object* v___x_1268_; uint8_t v_isShared_1269_; uint8_t v_isSharedCheck_1273_; 
lean_dec_ref(v_bs_x27_1258_);
v_a_1266_ = lean_ctor_get(v___y_1260_, 0);
v_isSharedCheck_1273_ = !lean_is_exclusive(v___y_1260_);
if (v_isSharedCheck_1273_ == 0)
{
v___x_1268_ = v___y_1260_;
v_isShared_1269_ = v_isSharedCheck_1273_;
goto v_resetjp_1267_;
}
else
{
lean_inc(v_a_1266_);
lean_dec(v___y_1260_);
v___x_1268_ = lean_box(0);
v_isShared_1269_ = v_isSharedCheck_1273_;
goto v_resetjp_1267_;
}
v_resetjp_1267_:
{
lean_object* v___x_1271_; 
if (v_isShared_1269_ == 0)
{
v___x_1271_ = v___x_1268_;
goto v_reusejp_1270_;
}
else
{
lean_object* v_reuseFailAlloc_1272_; 
v_reuseFailAlloc_1272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1272_, 0, v_a_1266_);
v___x_1271_ = v_reuseFailAlloc_1272_;
goto v_reusejp_1270_;
}
v_reusejp_1270_:
{
return v___x_1271_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__0___redArg___boxed(lean_object* v_sz_1286_, lean_object* v_i_1287_, lean_object* v_bs_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_){
_start:
{
size_t v_sz_boxed_1294_; size_t v_i_boxed_1295_; lean_object* v_res_1296_; 
v_sz_boxed_1294_ = lean_unbox_usize(v_sz_1286_);
lean_dec(v_sz_1286_);
v_i_boxed_1295_ = lean_unbox_usize(v_i_1287_);
lean_dec(v_i_1287_);
v_res_1296_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__0___redArg(v_sz_boxed_1294_, v_i_boxed_1295_, v_bs_1288_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_);
lean_dec(v___y_1292_);
lean_dec_ref(v___y_1291_);
lean_dec(v___y_1290_);
lean_dec_ref(v___y_1289_);
return v_res_1296_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__2___closed__4(void){
_start:
{
lean_object* v___x_1303_; lean_object* v___x_1304_; 
v___x_1303_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__2___closed__3));
v___x_1304_ = l_Lean_stringToMessageData(v___x_1303_);
return v___x_1304_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__2___closed__6(void){
_start:
{
lean_object* v___x_1306_; lean_object* v___x_1307_; 
v___x_1306_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__2___closed__5));
v___x_1307_ = l_Lean_stringToMessageData(v___x_1306_);
return v___x_1307_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__2___closed__7(void){
_start:
{
lean_object* v___x_1308_; lean_object* v_dummy_1309_; 
v___x_1308_ = lean_box(0);
v_dummy_1309_ = l_Lean_Expr_sort___override(v___x_1308_);
return v_dummy_1309_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__2(lean_object* v_op_1310_, lean_object* v___y_1311_, lean_object* v_a_1312_, lean_object* v_x_1313_, lean_object* v_x_1314_, lean_object* v_x_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_){
_start:
{
lean_object* v_prf_1324_; lean_object* v___y_1325_; lean_object* v___y_1326_; lean_object* v___y_1327_; lean_object* v___y_1328_; 
if (lean_obj_tag(v_x_1313_) == 5)
{
lean_object* v_fn_1345_; lean_object* v_arg_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; 
v_fn_1345_ = lean_ctor_get(v_x_1313_, 0);
lean_inc_ref(v_fn_1345_);
v_arg_1346_ = lean_ctor_get(v_x_1313_, 1);
lean_inc_ref(v_arg_1346_);
lean_dec_ref_known(v_x_1313_, 2);
v___x_1347_ = lean_array_set(v_x_1314_, v_x_1315_, v_arg_1346_);
v___x_1348_ = lean_unsigned_to_nat(1u);
v___x_1349_ = lean_nat_sub(v_x_1315_, v___x_1348_);
lean_dec(v_x_1315_);
v_x_1313_ = v_fn_1345_;
v_x_1314_ = v___x_1347_;
v_x_1315_ = v___x_1349_;
goto _start;
}
else
{
lean_object* v_head_1351_; lean_object* v_numConst_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; size_t v_sz_1355_; size_t v___x_1356_; lean_object* v___x_1357_; 
lean_dec(v_x_1315_);
v_head_1351_ = lean_ctor_get(v_op_1310_, 0);
lean_inc(v_head_1351_);
v_numConst_1352_ = lean_ctor_get(v_op_1310_, 1);
lean_inc_n(v_numConst_1352_, 2);
lean_dec_ref(v_op_1310_);
v___x_1353_ = lean_array_get_size(v_x_1314_);
v___x_1354_ = l_Array_extract___redArg(v_x_1314_, v_numConst_1352_, v___x_1353_);
v_sz_1355_ = lean_array_size(v___x_1354_);
v___x_1356_ = ((size_t)0ULL);
v___x_1357_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__0___redArg(v_sz_1355_, v___x_1356_, v___x_1354_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_);
if (lean_obj_tag(v___x_1357_) == 0)
{
lean_object* v_a_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; 
v_a_1358_ = lean_ctor_get(v___x_1357_, 0);
lean_inc(v_a_1358_);
lean_dec_ref_known(v___x_1357_, 1);
v___x_1359_ = lean_unsigned_to_nat(0u);
v___x_1360_ = l_Array_extract___redArg(v_x_1314_, v___x_1359_, v_numConst_1352_);
lean_dec_ref(v_x_1314_);
v___x_1361_ = l_Array_append___redArg(v___x_1360_, v_a_1358_);
lean_dec(v_a_1358_);
v___x_1362_ = l_Lean_mkAppN(v_x_1313_, v___x_1361_);
lean_dec_ref(v___x_1361_);
v___x_1363_ = lean_unsigned_to_nat(256u);
lean_inc_ref(v___x_1362_);
v___x_1364_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp(v___y_1311_, v___x_1362_, v___x_1363_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_);
if (lean_obj_tag(v___x_1364_) == 0)
{
lean_object* v_a_1365_; lean_object* v_fst_1366_; lean_object* v_snd_1367_; lean_object* v___x_1369_; uint8_t v_isShared_1370_; uint8_t v_isSharedCheck_1539_; 
v_a_1365_ = lean_ctor_get(v___x_1364_, 0);
lean_inc(v_a_1365_);
lean_dec_ref_known(v___x_1364_, 1);
v_fst_1366_ = lean_ctor_get(v_a_1365_, 0);
v_snd_1367_ = lean_ctor_get(v_a_1365_, 1);
v_isSharedCheck_1539_ = !lean_is_exclusive(v_a_1365_);
if (v_isSharedCheck_1539_ == 0)
{
v___x_1369_ = v_a_1365_;
v_isShared_1370_ = v_isSharedCheck_1539_;
goto v_resetjp_1368_;
}
else
{
lean_inc(v_snd_1367_);
lean_inc(v_fst_1366_);
lean_dec(v_a_1365_);
v___x_1369_ = lean_box(0);
v_isShared_1370_ = v_isSharedCheck_1539_;
goto v_resetjp_1368_;
}
v_resetjp_1368_:
{
lean_object* v___x_1371_; 
lean_inc(v___y_1321_);
lean_inc_ref(v___y_1320_);
lean_inc(v___y_1319_);
lean_inc_ref(v___y_1318_);
v___x_1371_ = lean_infer_type(v___x_1362_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_);
if (lean_obj_tag(v___x_1371_) == 0)
{
lean_object* v_a_1372_; lean_object* v___x_1373_; uint8_t v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; 
v_a_1372_ = lean_ctor_get(v___x_1371_, 0);
lean_inc(v_a_1372_);
lean_dec_ref_known(v___x_1371_, 1);
v___x_1373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1373_, 0, v_a_1372_);
v___x_1374_ = 0;
v___x_1375_ = lean_box(0);
v___x_1376_ = l_Lean_Meta_mkFreshExprMVar(v___x_1373_, v___x_1374_, v___x_1375_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_);
if (lean_obj_tag(v___x_1376_) == 0)
{
lean_object* v_a_1377_; lean_object* v___y_1379_; lean_object* v___y_1380_; lean_object* v___y_1381_; lean_object* v___y_1382_; lean_object* v___y_1383_; lean_object* v___y_1384_; lean_object* v_a_1385_; lean_object* v___y_1433_; lean_object* v_eqProof_1434_; lean_object* v___y_1435_; lean_object* v___y_1436_; lean_object* v___y_1437_; lean_object* v___y_1438_; lean_object* v___x_1466_; lean_object* v___y_1468_; lean_object* v___x_1521_; 
v_a_1377_ = lean_ctor_get(v___x_1376_, 0);
lean_inc(v_a_1377_);
lean_dec_ref_known(v___x_1376_, 1);
v___x_1466_ = l_Lean_Expr_getAppFn(v_fst_1366_);
v___x_1521_ = l_Lean_Expr_constName_x3f(v___x_1466_);
if (lean_obj_tag(v___x_1521_) == 0)
{
v___y_1468_ = v___x_1375_;
goto v___jp_1467_;
}
else
{
lean_object* v_val_1522_; 
v_val_1522_ = lean_ctor_get(v___x_1521_, 0);
lean_inc(v_val_1522_);
lean_dec_ref_known(v___x_1521_, 1);
v___y_1468_ = v_val_1522_;
goto v___jp_1467_;
}
v___jp_1378_:
{
lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; 
v___x_1386_ = lean_unsigned_to_nat(1u);
v___x_1387_ = lean_mk_empty_array_with_capacity(v___x_1386_);
lean_inc_ref(v___x_1387_);
v___x_1388_ = lean_array_push(v___x_1387_, v_a_1377_);
v___x_1389_ = l_Lean_Meta_mkAppM(v___y_1383_, v___x_1388_, v___y_1382_, v___y_1381_, v___y_1380_, v___y_1379_);
if (lean_obj_tag(v___x_1389_) == 0)
{
lean_object* v_a_1390_; lean_object* v___x_1391_; 
v_a_1390_ = lean_ctor_get(v___x_1389_, 0);
lean_inc(v_a_1390_);
lean_dec_ref_known(v___x_1389_, 1);
v___x_1391_ = l_Lean_Meta_mkCongrArg(v_a_1390_, v___y_1384_, v___y_1382_, v___y_1381_, v___y_1380_, v___y_1379_);
if (lean_obj_tag(v___x_1391_) == 0)
{
lean_object* v_a_1392_; lean_object* v___x_1393_; 
v_a_1392_ = lean_ctor_get(v___x_1391_, 0);
lean_inc(v_a_1392_);
lean_dec_ref_known(v___x_1391_, 1);
v___x_1393_ = l_Lean_Meta_mkEqSymm(v_a_1392_, v___y_1382_, v___y_1381_, v___y_1380_, v___y_1379_);
if (lean_obj_tag(v___x_1393_) == 0)
{
lean_object* v_a_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; 
v_a_1394_ = lean_ctor_get(v___x_1393_, 0);
lean_inc(v_a_1394_);
lean_dec_ref_known(v___x_1393_, 1);
v___x_1395_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__2___closed__2));
v___x_1396_ = lean_array_push(v___x_1387_, v_a_1394_);
v___x_1397_ = l_Lean_Meta_mkAppM(v___x_1395_, v___x_1396_, v___y_1382_, v___y_1381_, v___y_1380_, v___y_1379_);
if (lean_obj_tag(v___x_1397_) == 0)
{
lean_object* v_a_1398_; lean_object* v___x_1399_; 
v_a_1398_ = lean_ctor_get(v___x_1397_, 0);
lean_inc(v_a_1398_);
lean_dec_ref_known(v___x_1397_, 1);
v___x_1399_ = l_Lean_Expr_app___override(v_a_1398_, v_a_1385_);
v_prf_1324_ = v___x_1399_;
v___y_1325_ = v___y_1382_;
v___y_1326_ = v___y_1381_;
v___y_1327_ = v___y_1380_;
v___y_1328_ = v___y_1379_;
goto v___jp_1323_;
}
else
{
lean_object* v_a_1400_; lean_object* v___x_1402_; uint8_t v_isShared_1403_; uint8_t v_isSharedCheck_1407_; 
lean_dec_ref(v_a_1385_);
v_a_1400_ = lean_ctor_get(v___x_1397_, 0);
v_isSharedCheck_1407_ = !lean_is_exclusive(v___x_1397_);
if (v_isSharedCheck_1407_ == 0)
{
v___x_1402_ = v___x_1397_;
v_isShared_1403_ = v_isSharedCheck_1407_;
goto v_resetjp_1401_;
}
else
{
lean_inc(v_a_1400_);
lean_dec(v___x_1397_);
v___x_1402_ = lean_box(0);
v_isShared_1403_ = v_isSharedCheck_1407_;
goto v_resetjp_1401_;
}
v_resetjp_1401_:
{
lean_object* v___x_1405_; 
if (v_isShared_1403_ == 0)
{
v___x_1405_ = v___x_1402_;
goto v_reusejp_1404_;
}
else
{
lean_object* v_reuseFailAlloc_1406_; 
v_reuseFailAlloc_1406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1406_, 0, v_a_1400_);
v___x_1405_ = v_reuseFailAlloc_1406_;
goto v_reusejp_1404_;
}
v_reusejp_1404_:
{
return v___x_1405_;
}
}
}
}
else
{
lean_object* v_a_1408_; lean_object* v___x_1410_; uint8_t v_isShared_1411_; uint8_t v_isSharedCheck_1415_; 
lean_dec_ref(v___x_1387_);
lean_dec_ref(v_a_1385_);
v_a_1408_ = lean_ctor_get(v___x_1393_, 0);
v_isSharedCheck_1415_ = !lean_is_exclusive(v___x_1393_);
if (v_isSharedCheck_1415_ == 0)
{
v___x_1410_ = v___x_1393_;
v_isShared_1411_ = v_isSharedCheck_1415_;
goto v_resetjp_1409_;
}
else
{
lean_inc(v_a_1408_);
lean_dec(v___x_1393_);
v___x_1410_ = lean_box(0);
v_isShared_1411_ = v_isSharedCheck_1415_;
goto v_resetjp_1409_;
}
v_resetjp_1409_:
{
lean_object* v___x_1413_; 
if (v_isShared_1411_ == 0)
{
v___x_1413_ = v___x_1410_;
goto v_reusejp_1412_;
}
else
{
lean_object* v_reuseFailAlloc_1414_; 
v_reuseFailAlloc_1414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1414_, 0, v_a_1408_);
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
else
{
lean_object* v_a_1416_; lean_object* v___x_1418_; uint8_t v_isShared_1419_; uint8_t v_isSharedCheck_1423_; 
lean_dec_ref(v___x_1387_);
lean_dec_ref(v_a_1385_);
v_a_1416_ = lean_ctor_get(v___x_1391_, 0);
v_isSharedCheck_1423_ = !lean_is_exclusive(v___x_1391_);
if (v_isSharedCheck_1423_ == 0)
{
v___x_1418_ = v___x_1391_;
v_isShared_1419_ = v_isSharedCheck_1423_;
goto v_resetjp_1417_;
}
else
{
lean_inc(v_a_1416_);
lean_dec(v___x_1391_);
v___x_1418_ = lean_box(0);
v_isShared_1419_ = v_isSharedCheck_1423_;
goto v_resetjp_1417_;
}
v_resetjp_1417_:
{
lean_object* v___x_1421_; 
if (v_isShared_1419_ == 0)
{
v___x_1421_ = v___x_1418_;
goto v_reusejp_1420_;
}
else
{
lean_object* v_reuseFailAlloc_1422_; 
v_reuseFailAlloc_1422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1422_, 0, v_a_1416_);
v___x_1421_ = v_reuseFailAlloc_1422_;
goto v_reusejp_1420_;
}
v_reusejp_1420_:
{
return v___x_1421_;
}
}
}
}
else
{
lean_object* v_a_1424_; lean_object* v___x_1426_; uint8_t v_isShared_1427_; uint8_t v_isSharedCheck_1431_; 
lean_dec_ref(v___x_1387_);
lean_dec_ref(v_a_1385_);
lean_dec_ref(v___y_1384_);
v_a_1424_ = lean_ctor_get(v___x_1389_, 0);
v_isSharedCheck_1431_ = !lean_is_exclusive(v___x_1389_);
if (v_isSharedCheck_1431_ == 0)
{
v___x_1426_ = v___x_1389_;
v_isShared_1427_ = v_isSharedCheck_1431_;
goto v_resetjp_1425_;
}
else
{
lean_inc(v_a_1424_);
lean_dec(v___x_1389_);
v___x_1426_ = lean_box(0);
v_isShared_1427_ = v_isSharedCheck_1431_;
goto v_resetjp_1425_;
}
v_resetjp_1425_:
{
lean_object* v___x_1429_; 
if (v_isShared_1427_ == 0)
{
v___x_1429_ = v___x_1426_;
goto v_reusejp_1428_;
}
else
{
lean_object* v_reuseFailAlloc_1430_; 
v_reuseFailAlloc_1430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1430_, 0, v_a_1424_);
v___x_1429_ = v_reuseFailAlloc_1430_;
goto v_reusejp_1428_;
}
v_reusejp_1428_:
{
return v___x_1429_;
}
}
}
}
v___jp_1432_:
{
lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; 
v___x_1439_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__2___closed__2));
v___x_1440_ = lean_unsigned_to_nat(2u);
v___x_1441_ = lean_mk_empty_array_with_capacity(v___x_1440_);
lean_inc(v_a_1377_);
v___x_1442_ = lean_array_push(v___x_1441_, v_a_1377_);
v___x_1443_ = lean_array_push(v___x_1442_, v_fst_1366_);
v___x_1444_ = l_Lean_Meta_mkAppM(v___x_1439_, v___x_1443_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_);
if (lean_obj_tag(v___x_1444_) == 0)
{
if (lean_obj_tag(v___y_1433_) == 0)
{
lean_object* v_a_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; 
v_a_1445_ = lean_ctor_get(v___x_1444_, 0);
lean_inc(v_a_1445_);
lean_dec_ref_known(v___x_1444_, 1);
v___x_1446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1446_, 0, v_a_1445_);
v___x_1447_ = l_Lean_Meta_mkFreshExprMVar(v___x_1446_, v___x_1374_, v___x_1375_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_);
if (lean_obj_tag(v___x_1447_) == 0)
{
lean_object* v_a_1448_; 
v_a_1448_ = lean_ctor_get(v___x_1447_, 0);
lean_inc(v_a_1448_);
lean_dec_ref_known(v___x_1447_, 1);
v___y_1379_ = v___y_1438_;
v___y_1380_ = v___y_1437_;
v___y_1381_ = v___y_1436_;
v___y_1382_ = v___y_1435_;
v___y_1383_ = v___x_1439_;
v___y_1384_ = v_eqProof_1434_;
v_a_1385_ = v_a_1448_;
goto v___jp_1378_;
}
else
{
lean_object* v_a_1449_; lean_object* v___x_1451_; uint8_t v_isShared_1452_; uint8_t v_isSharedCheck_1456_; 
lean_dec_ref(v_eqProof_1434_);
lean_dec(v_a_1377_);
v_a_1449_ = lean_ctor_get(v___x_1447_, 0);
v_isSharedCheck_1456_ = !lean_is_exclusive(v___x_1447_);
if (v_isSharedCheck_1456_ == 0)
{
v___x_1451_ = v___x_1447_;
v_isShared_1452_ = v_isSharedCheck_1456_;
goto v_resetjp_1450_;
}
else
{
lean_inc(v_a_1449_);
lean_dec(v___x_1447_);
v___x_1451_ = lean_box(0);
v_isShared_1452_ = v_isSharedCheck_1456_;
goto v_resetjp_1450_;
}
v_resetjp_1450_:
{
lean_object* v___x_1454_; 
if (v_isShared_1452_ == 0)
{
v___x_1454_ = v___x_1451_;
goto v_reusejp_1453_;
}
else
{
lean_object* v_reuseFailAlloc_1455_; 
v_reuseFailAlloc_1455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1455_, 0, v_a_1449_);
v___x_1454_ = v_reuseFailAlloc_1455_;
goto v_reusejp_1453_;
}
v_reusejp_1453_:
{
return v___x_1454_;
}
}
}
}
else
{
lean_object* v_val_1457_; 
lean_dec_ref_known(v___x_1444_, 1);
v_val_1457_ = lean_ctor_get(v___y_1433_, 0);
lean_inc(v_val_1457_);
lean_dec_ref_known(v___y_1433_, 1);
v___y_1379_ = v___y_1438_;
v___y_1380_ = v___y_1437_;
v___y_1381_ = v___y_1436_;
v___y_1382_ = v___y_1435_;
v___y_1383_ = v___x_1439_;
v___y_1384_ = v_eqProof_1434_;
v_a_1385_ = v_val_1457_;
goto v___jp_1378_;
}
}
else
{
lean_object* v_a_1458_; lean_object* v___x_1460_; uint8_t v_isShared_1461_; uint8_t v_isSharedCheck_1465_; 
lean_dec_ref(v_eqProof_1434_);
lean_dec(v___y_1433_);
lean_dec(v_a_1377_);
v_a_1458_ = lean_ctor_get(v___x_1444_, 0);
v_isSharedCheck_1465_ = !lean_is_exclusive(v___x_1444_);
if (v_isSharedCheck_1465_ == 0)
{
v___x_1460_ = v___x_1444_;
v_isShared_1461_ = v_isSharedCheck_1465_;
goto v_resetjp_1459_;
}
else
{
lean_inc(v_a_1458_);
lean_dec(v___x_1444_);
v___x_1460_ = lean_box(0);
v_isShared_1461_ = v_isSharedCheck_1465_;
goto v_resetjp_1459_;
}
v_resetjp_1459_:
{
lean_object* v___x_1463_; 
if (v_isShared_1461_ == 0)
{
v___x_1463_ = v___x_1460_;
goto v_reusejp_1462_;
}
else
{
lean_object* v_reuseFailAlloc_1464_; 
v_reuseFailAlloc_1464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1464_, 0, v_a_1458_);
v___x_1463_ = v_reuseFailAlloc_1464_;
goto v_reusejp_1462_;
}
v_reusejp_1462_:
{
return v___x_1463_;
}
}
}
}
v___jp_1467_:
{
lean_object* v___x_1469_; 
v___x_1469_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__1___redArg(v_a_1312_, v___y_1468_);
lean_dec(v___y_1468_);
if (lean_obj_tag(v___x_1469_) == 0)
{
lean_dec_ref(v___x_1466_);
if (lean_obj_tag(v_snd_1367_) == 0)
{
lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1473_; 
lean_dec(v_a_1377_);
lean_dec(v_fst_1366_);
v___x_1470_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__2___closed__4, &l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__2___closed__4_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__2___closed__4);
v___x_1471_ = l_Lean_MessageData_ofName(v_head_1351_);
if (v_isShared_1370_ == 0)
{
lean_ctor_set_tag(v___x_1369_, 7);
lean_ctor_set(v___x_1369_, 1, v___x_1471_);
lean_ctor_set(v___x_1369_, 0, v___x_1470_);
v___x_1473_ = v___x_1369_;
goto v_reusejp_1472_;
}
else
{
lean_object* v_reuseFailAlloc_1485_; 
v_reuseFailAlloc_1485_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1485_, 0, v___x_1470_);
lean_ctor_set(v_reuseFailAlloc_1485_, 1, v___x_1471_);
v___x_1473_ = v_reuseFailAlloc_1485_;
goto v_reusejp_1472_;
}
v_reusejp_1472_:
{
lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v_a_1477_; lean_object* v___x_1479_; uint8_t v_isShared_1480_; uint8_t v_isSharedCheck_1484_; 
v___x_1474_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__2___closed__6, &l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__2___closed__6_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__2___closed__6);
v___x_1475_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1475_, 0, v___x_1473_);
lean_ctor_set(v___x_1475_, 1, v___x_1474_);
v___x_1476_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_go_spec__0___redArg(v___x_1475_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_);
v_a_1477_ = lean_ctor_get(v___x_1476_, 0);
v_isSharedCheck_1484_ = !lean_is_exclusive(v___x_1476_);
if (v_isSharedCheck_1484_ == 0)
{
v___x_1479_ = v___x_1476_;
v_isShared_1480_ = v_isSharedCheck_1484_;
goto v_resetjp_1478_;
}
else
{
lean_inc(v_a_1477_);
lean_dec(v___x_1476_);
v___x_1479_ = lean_box(0);
v_isShared_1480_ = v_isSharedCheck_1484_;
goto v_resetjp_1478_;
}
v_resetjp_1478_:
{
lean_object* v___x_1482_; 
if (v_isShared_1480_ == 0)
{
v___x_1482_ = v___x_1479_;
goto v_reusejp_1481_;
}
else
{
lean_object* v_reuseFailAlloc_1483_; 
v_reuseFailAlloc_1483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1483_, 0, v_a_1477_);
v___x_1482_ = v_reuseFailAlloc_1483_;
goto v_reusejp_1481_;
}
v_reusejp_1481_:
{
return v___x_1482_;
}
}
}
}
else
{
lean_object* v_val_1486_; lean_object* v___x_1487_; 
lean_del_object(v___x_1369_);
lean_dec(v_head_1351_);
v_val_1486_ = lean_ctor_get(v_snd_1367_, 0);
lean_inc(v_val_1486_);
lean_dec_ref_known(v_snd_1367_, 1);
v___x_1487_ = lean_box(0);
v___y_1433_ = v___x_1487_;
v_eqProof_1434_ = v_val_1486_;
v___y_1435_ = v___y_1318_;
v___y_1436_ = v___y_1319_;
v___y_1437_ = v___y_1320_;
v___y_1438_ = v___y_1321_;
goto v___jp_1432_;
}
}
else
{
lean_object* v_val_1488_; lean_object* v_fst_1489_; lean_object* v_snd_1490_; lean_object* v_dummy_1491_; lean_object* v_nargs_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; 
lean_del_object(v___x_1369_);
lean_dec(v_head_1351_);
v_val_1488_ = lean_ctor_get(v___x_1469_, 0);
lean_inc(v_val_1488_);
lean_dec_ref_known(v___x_1469_, 1);
v_fst_1489_ = lean_ctor_get(v_val_1488_, 0);
lean_inc(v_fst_1489_);
v_snd_1490_ = lean_ctor_get(v_val_1488_, 1);
lean_inc_n(v_snd_1490_, 2);
lean_dec(v_val_1488_);
v_dummy_1491_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__2___closed__7, &l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__2___closed__7_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__2___closed__7);
v_nargs_1492_ = l_Lean_Expr_getAppNumArgs(v_fst_1366_);
lean_inc(v_nargs_1492_);
v___x_1493_ = lean_mk_array(v_nargs_1492_, v_dummy_1491_);
v___x_1494_ = lean_unsigned_to_nat(1u);
v___x_1495_ = lean_nat_sub(v_nargs_1492_, v___x_1494_);
lean_dec(v_nargs_1492_);
lean_inc(v_fst_1366_);
v___x_1496_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_fst_1366_, v___x_1493_, v___x_1495_);
v___x_1497_ = l_Array_extract___redArg(v___x_1496_, v___x_1359_, v_snd_1490_);
v___x_1498_ = l_Lean_mkAppN(v___x_1466_, v___x_1497_);
lean_dec_ref(v___x_1497_);
v___x_1499_ = lean_array_get_size(v___x_1496_);
v___x_1500_ = l_Array_extract___redArg(v___x_1496_, v_snd_1490_, v___x_1499_);
lean_dec_ref(v___x_1496_);
v___x_1501_ = lean_array_to_list(v___x_1500_);
lean_inc(v_a_1377_);
v___x_1502_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply(v_fst_1489_, v___x_1498_, v_a_1377_, v___x_1501_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_);
if (lean_obj_tag(v___x_1502_) == 0)
{
if (lean_obj_tag(v_snd_1367_) == 0)
{
lean_object* v_a_1503_; 
lean_dec(v_a_1377_);
lean_dec(v_fst_1366_);
v_a_1503_ = lean_ctor_get(v___x_1502_, 0);
lean_inc(v_a_1503_);
lean_dec_ref_known(v___x_1502_, 1);
v_prf_1324_ = v_a_1503_;
v___y_1325_ = v___y_1318_;
v___y_1326_ = v___y_1319_;
v___y_1327_ = v___y_1320_;
v___y_1328_ = v___y_1321_;
goto v___jp_1323_;
}
else
{
lean_object* v_a_1504_; lean_object* v_val_1505_; lean_object* v___x_1507_; uint8_t v_isShared_1508_; uint8_t v_isSharedCheck_1512_; 
v_a_1504_ = lean_ctor_get(v___x_1502_, 0);
lean_inc(v_a_1504_);
lean_dec_ref_known(v___x_1502_, 1);
v_val_1505_ = lean_ctor_get(v_snd_1367_, 0);
v_isSharedCheck_1512_ = !lean_is_exclusive(v_snd_1367_);
if (v_isSharedCheck_1512_ == 0)
{
v___x_1507_ = v_snd_1367_;
v_isShared_1508_ = v_isSharedCheck_1512_;
goto v_resetjp_1506_;
}
else
{
lean_inc(v_val_1505_);
lean_dec(v_snd_1367_);
v___x_1507_ = lean_box(0);
v_isShared_1508_ = v_isSharedCheck_1512_;
goto v_resetjp_1506_;
}
v_resetjp_1506_:
{
lean_object* v___x_1510_; 
if (v_isShared_1508_ == 0)
{
lean_ctor_set(v___x_1507_, 0, v_a_1504_);
v___x_1510_ = v___x_1507_;
goto v_reusejp_1509_;
}
else
{
lean_object* v_reuseFailAlloc_1511_; 
v_reuseFailAlloc_1511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1511_, 0, v_a_1504_);
v___x_1510_ = v_reuseFailAlloc_1511_;
goto v_reusejp_1509_;
}
v_reusejp_1509_:
{
v___y_1433_ = v___x_1510_;
v_eqProof_1434_ = v_val_1505_;
v___y_1435_ = v___y_1318_;
v___y_1436_ = v___y_1319_;
v___y_1437_ = v___y_1320_;
v___y_1438_ = v___y_1321_;
goto v___jp_1432_;
}
}
}
}
else
{
lean_object* v_a_1513_; lean_object* v___x_1515_; uint8_t v_isShared_1516_; uint8_t v_isSharedCheck_1520_; 
lean_dec(v_a_1377_);
lean_dec(v_snd_1367_);
lean_dec(v_fst_1366_);
v_a_1513_ = lean_ctor_get(v___x_1502_, 0);
v_isSharedCheck_1520_ = !lean_is_exclusive(v___x_1502_);
if (v_isSharedCheck_1520_ == 0)
{
v___x_1515_ = v___x_1502_;
v_isShared_1516_ = v_isSharedCheck_1520_;
goto v_resetjp_1514_;
}
else
{
lean_inc(v_a_1513_);
lean_dec(v___x_1502_);
v___x_1515_ = lean_box(0);
v_isShared_1516_ = v_isSharedCheck_1520_;
goto v_resetjp_1514_;
}
v_resetjp_1514_:
{
lean_object* v___x_1518_; 
if (v_isShared_1516_ == 0)
{
v___x_1518_ = v___x_1515_;
goto v_reusejp_1517_;
}
else
{
lean_object* v_reuseFailAlloc_1519_; 
v_reuseFailAlloc_1519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1519_, 0, v_a_1513_);
v___x_1518_ = v_reuseFailAlloc_1519_;
goto v_reusejp_1517_;
}
v_reusejp_1517_:
{
return v___x_1518_;
}
}
}
}
}
}
else
{
lean_object* v_a_1523_; lean_object* v___x_1525_; uint8_t v_isShared_1526_; uint8_t v_isSharedCheck_1530_; 
lean_del_object(v___x_1369_);
lean_dec(v_snd_1367_);
lean_dec(v_fst_1366_);
lean_dec(v_head_1351_);
v_a_1523_ = lean_ctor_get(v___x_1376_, 0);
v_isSharedCheck_1530_ = !lean_is_exclusive(v___x_1376_);
if (v_isSharedCheck_1530_ == 0)
{
v___x_1525_ = v___x_1376_;
v_isShared_1526_ = v_isSharedCheck_1530_;
goto v_resetjp_1524_;
}
else
{
lean_inc(v_a_1523_);
lean_dec(v___x_1376_);
v___x_1525_ = lean_box(0);
v_isShared_1526_ = v_isSharedCheck_1530_;
goto v_resetjp_1524_;
}
v_resetjp_1524_:
{
lean_object* v___x_1528_; 
if (v_isShared_1526_ == 0)
{
v___x_1528_ = v___x_1525_;
goto v_reusejp_1527_;
}
else
{
lean_object* v_reuseFailAlloc_1529_; 
v_reuseFailAlloc_1529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1529_, 0, v_a_1523_);
v___x_1528_ = v_reuseFailAlloc_1529_;
goto v_reusejp_1527_;
}
v_reusejp_1527_:
{
return v___x_1528_;
}
}
}
}
else
{
lean_object* v_a_1531_; lean_object* v___x_1533_; uint8_t v_isShared_1534_; uint8_t v_isSharedCheck_1538_; 
lean_del_object(v___x_1369_);
lean_dec(v_snd_1367_);
lean_dec(v_fst_1366_);
lean_dec(v_head_1351_);
v_a_1531_ = lean_ctor_get(v___x_1371_, 0);
v_isSharedCheck_1538_ = !lean_is_exclusive(v___x_1371_);
if (v_isSharedCheck_1538_ == 0)
{
v___x_1533_ = v___x_1371_;
v_isShared_1534_ = v_isSharedCheck_1538_;
goto v_resetjp_1532_;
}
else
{
lean_inc(v_a_1531_);
lean_dec(v___x_1371_);
v___x_1533_ = lean_box(0);
v_isShared_1534_ = v_isSharedCheck_1538_;
goto v_resetjp_1532_;
}
v_resetjp_1532_:
{
lean_object* v___x_1536_; 
if (v_isShared_1534_ == 0)
{
v___x_1536_ = v___x_1533_;
goto v_reusejp_1535_;
}
else
{
lean_object* v_reuseFailAlloc_1537_; 
v_reuseFailAlloc_1537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1537_, 0, v_a_1531_);
v___x_1536_ = v_reuseFailAlloc_1537_;
goto v_reusejp_1535_;
}
v_reusejp_1535_:
{
return v___x_1536_;
}
}
}
}
}
else
{
lean_object* v_a_1540_; lean_object* v___x_1542_; uint8_t v_isShared_1543_; uint8_t v_isSharedCheck_1547_; 
lean_dec_ref(v___x_1362_);
lean_dec(v_head_1351_);
v_a_1540_ = lean_ctor_get(v___x_1364_, 0);
v_isSharedCheck_1547_ = !lean_is_exclusive(v___x_1364_);
if (v_isSharedCheck_1547_ == 0)
{
v___x_1542_ = v___x_1364_;
v_isShared_1543_ = v_isSharedCheck_1547_;
goto v_resetjp_1541_;
}
else
{
lean_inc(v_a_1540_);
lean_dec(v___x_1364_);
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
else
{
lean_object* v_a_1548_; lean_object* v___x_1550_; uint8_t v_isShared_1551_; uint8_t v_isSharedCheck_1555_; 
lean_dec(v_numConst_1352_);
lean_dec(v_head_1351_);
lean_dec_ref(v_x_1314_);
lean_dec_ref(v_x_1313_);
v_a_1548_ = lean_ctor_get(v___x_1357_, 0);
v_isSharedCheck_1555_ = !lean_is_exclusive(v___x_1357_);
if (v_isSharedCheck_1555_ == 0)
{
v___x_1550_ = v___x_1357_;
v_isShared_1551_ = v_isSharedCheck_1555_;
goto v_resetjp_1549_;
}
else
{
lean_inc(v_a_1548_);
lean_dec(v___x_1357_);
v___x_1550_ = lean_box(0);
v_isShared_1551_ = v_isSharedCheck_1555_;
goto v_resetjp_1549_;
}
v_resetjp_1549_:
{
lean_object* v___x_1553_; 
if (v_isShared_1551_ == 0)
{
v___x_1553_ = v___x_1550_;
goto v_reusejp_1552_;
}
else
{
lean_object* v_reuseFailAlloc_1554_; 
v_reuseFailAlloc_1554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1554_, 0, v_a_1548_);
v___x_1553_ = v_reuseFailAlloc_1554_;
goto v_reusejp_1552_;
}
v_reusejp_1552_:
{
return v___x_1553_;
}
}
}
}
v___jp_1323_:
{
uint8_t v___x_1329_; lean_object* v___x_1330_; 
v___x_1329_ = 1;
v___x_1330_ = l_Lean_Meta_abstractMVars(v_prf_1324_, v___x_1329_, v___y_1325_, v___y_1326_, v___y_1327_, v___y_1328_);
if (lean_obj_tag(v___x_1330_) == 0)
{
lean_object* v_a_1331_; lean_object* v_paramNames_1332_; lean_object* v_expr_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; 
v_a_1331_ = lean_ctor_get(v___x_1330_, 0);
lean_inc(v_a_1331_);
lean_dec_ref_known(v___x_1330_, 1);
v_paramNames_1332_ = lean_ctor_get(v_a_1331_, 0);
lean_inc_ref(v_paramNames_1332_);
v_expr_1333_ = lean_ctor_get(v_a_1331_, 2);
lean_inc_ref(v_expr_1333_);
lean_dec(v_a_1331_);
v___x_1334_ = lean_array_to_list(v_paramNames_1332_);
v___x_1335_ = lean_box(0);
v___x_1336_ = l_Lean_Meta_Sym_mkBackwardRuleFromExpr(v_expr_1333_, v___x_1334_, v___x_1335_, v___y_1325_, v___y_1326_, v___y_1327_, v___y_1328_);
return v___x_1336_;
}
else
{
lean_object* v_a_1337_; lean_object* v___x_1339_; uint8_t v_isShared_1340_; uint8_t v_isSharedCheck_1344_; 
v_a_1337_ = lean_ctor_get(v___x_1330_, 0);
v_isSharedCheck_1344_ = !lean_is_exclusive(v___x_1330_);
if (v_isSharedCheck_1344_ == 0)
{
v___x_1339_ = v___x_1330_;
v_isShared_1340_ = v_isSharedCheck_1344_;
goto v_resetjp_1338_;
}
else
{
lean_inc(v_a_1337_);
lean_dec(v___x_1330_);
v___x_1339_ = lean_box(0);
v_isShared_1340_ = v_isSharedCheck_1344_;
goto v_resetjp_1338_;
}
v_resetjp_1338_:
{
lean_object* v___x_1342_; 
if (v_isShared_1340_ == 0)
{
v___x_1342_ = v___x_1339_;
goto v_reusejp_1341_;
}
else
{
lean_object* v_reuseFailAlloc_1343_; 
v_reuseFailAlloc_1343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1343_, 0, v_a_1337_);
v___x_1342_ = v_reuseFailAlloc_1343_;
goto v_reusejp_1341_;
}
v_reusejp_1341_:
{
return v___x_1342_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__2___boxed(lean_object* v_op_1556_, lean_object* v___y_1557_, lean_object* v_a_1558_, lean_object* v_x_1559_, lean_object* v_x_1560_, lean_object* v_x_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_){
_start:
{
lean_object* v_res_1569_; 
v_res_1569_ = l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__2(v_op_1556_, v___y_1557_, v_a_1558_, v_x_1559_, v_x_1560_, v_x_1561_, v___y_1562_, v___y_1563_, v___y_1564_, v___y_1565_, v___y_1566_, v___y_1567_);
lean_dec(v___y_1567_);
lean_dec_ref(v___y_1566_);
lean_dec(v___y_1565_);
lean_dec_ref(v___y_1564_);
lean_dec(v___y_1563_);
lean_dec_ref(v___y_1562_);
lean_dec_ref(v_a_1558_);
lean_dec_ref(v___y_1557_);
return v_res_1569_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__4(lean_object* v_as_1570_, size_t v_i_1571_, size_t v_stop_1572_, lean_object* v_b_1573_){
_start:
{
uint8_t v___x_1574_; 
v___x_1574_ = lean_usize_dec_eq(v_i_1571_, v_stop_1572_);
if (v___x_1574_ == 0)
{
lean_object* v___x_1575_; lean_object* v_rewrites_1576_; lean_object* v___x_1577_; size_t v___x_1578_; size_t v___x_1579_; 
v___x_1575_ = lean_array_uget_borrowed(v_as_1570_, v_i_1571_);
v_rewrites_1576_ = lean_ctor_get(v___x_1575_, 2);
v___x_1577_ = l_Array_append___redArg(v_b_1573_, v_rewrites_1576_);
v___x_1578_ = ((size_t)1ULL);
v___x_1579_ = lean_usize_add(v_i_1571_, v___x_1578_);
v_i_1571_ = v___x_1579_;
v_b_1573_ = v___x_1577_;
goto _start;
}
else
{
return v_b_1573_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__4___boxed(lean_object* v_as_1581_, lean_object* v_i_1582_, lean_object* v_stop_1583_, lean_object* v_b_1584_){
_start:
{
size_t v_i_boxed_1585_; size_t v_stop_boxed_1586_; lean_object* v_res_1587_; 
v_i_boxed_1585_ = lean_unbox_usize(v_i_1582_);
lean_dec(v_i_1582_);
v_stop_boxed_1586_ = lean_unbox_usize(v_stop_1583_);
lean_dec(v_stop_1583_);
v_res_1587_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__4(v_as_1581_, v_i_boxed_1585_, v_stop_boxed_1586_, v_b_1584_);
lean_dec_ref(v_as_1581_);
return v_res_1587_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__3(lean_object* v_as_1588_, size_t v_i_1589_, size_t v_stop_1590_, lean_object* v_b_1591_){
_start:
{
lean_object* v___y_1593_; uint8_t v___x_1597_; 
v___x_1597_ = lean_usize_dec_eq(v_i_1589_, v_stop_1590_);
if (v___x_1597_ == 0)
{
lean_object* v___x_1598_; lean_object* v_terminal_x3f_1599_; 
v___x_1598_ = lean_array_uget_borrowed(v_as_1588_, v_i_1589_);
v_terminal_x3f_1599_ = lean_ctor_get(v___x_1598_, 3);
if (lean_obj_tag(v_terminal_x3f_1599_) == 0)
{
lean_object* v___x_1600_; lean_object* v___x_1601_; 
v___x_1600_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_upperAdjoint___closed__3));
v___x_1601_ = l_Array_append___redArg(v_b_1591_, v___x_1600_);
v___y_1593_ = v___x_1601_;
goto v___jp_1592_;
}
else
{
lean_object* v_val_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; 
v_val_1602_ = lean_ctor_get(v_terminal_x3f_1599_, 0);
v___x_1603_ = lean_unsigned_to_nat(1u);
v___x_1604_ = lean_mk_empty_array_with_capacity(v___x_1603_);
lean_inc(v_val_1602_);
v___x_1605_ = lean_array_push(v___x_1604_, v_val_1602_);
v___x_1606_ = l_Array_append___redArg(v_b_1591_, v___x_1605_);
lean_dec_ref(v___x_1605_);
v___y_1593_ = v___x_1606_;
goto v___jp_1592_;
}
}
else
{
return v_b_1591_;
}
v___jp_1592_:
{
size_t v___x_1594_; size_t v___x_1595_; 
v___x_1594_ = ((size_t)1ULL);
v___x_1595_ = lean_usize_add(v_i_1589_, v___x_1594_);
v_i_1589_ = v___x_1595_;
v_b_1591_ = v___y_1593_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__3___boxed(lean_object* v_as_1607_, lean_object* v_i_1608_, lean_object* v_stop_1609_, lean_object* v_b_1610_){
_start:
{
size_t v_i_boxed_1611_; size_t v_stop_boxed_1612_; lean_object* v_res_1613_; 
v_i_boxed_1611_ = lean_unbox_usize(v_i_1608_);
lean_dec(v_i_1608_);
v_stop_boxed_1612_ = lean_unbox_usize(v_stop_1609_);
lean_dec(v_stop_1609_);
v_res_1613_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__3(v_as_1607_, v_i_boxed_1611_, v_stop_boxed_1612_, v_b_1610_);
lean_dec_ref(v_as_1607_);
return v_res_1613_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule___closed__0(void){
_start:
{
lean_object* v___x_1614_; size_t v___x_1615_; size_t v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; 
v___x_1614_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_upperAdjoint___closed__3));
v___x_1615_ = lean_usize_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable___closed__3, &l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable___closed__3_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable___closed__3);
v___x_1616_ = ((size_t)0ULL);
v___x_1617_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_builtinLatticeOps));
v___x_1618_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__3(v___x_1617_, v___x_1616_, v___x_1615_, v___x_1614_);
return v___x_1618_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule(lean_object* v_rhs_1619_, lean_object* v_op_1620_, lean_object* v_a_1621_, lean_object* v_a_1622_, lean_object* v_a_1623_, lean_object* v_a_1624_, lean_object* v_a_1625_, lean_object* v_a_1626_){
_start:
{
lean_object* v___y_1629_; lean_object* v___y_1630_; lean_object* v___y_1631_; lean_object* v_rewrites_1649_; lean_object* v_terminal_x3f_1650_; lean_object* v___x_1651_; lean_object* v___y_1653_; lean_object* v___y_1654_; lean_object* v___y_1661_; uint8_t v___x_1667_; 
v_rewrites_1649_ = lean_ctor_get(v_op_1620_, 2);
v_terminal_x3f_1650_ = lean_ctor_get(v_op_1620_, 3);
v___x_1651_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_builtinLatticeOps));
v___x_1667_ = lean_uint8_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable___closed__1, &l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable___closed__1_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable___closed__1);
if (v___x_1667_ == 0)
{
lean_inc_ref(v_rewrites_1649_);
v___y_1661_ = v_rewrites_1649_;
goto v___jp_1660_;
}
else
{
uint8_t v___x_1668_; 
v___x_1668_ = lean_uint8_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable___closed__2, &l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable___closed__2_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable___closed__2);
if (v___x_1668_ == 0)
{
if (v___x_1667_ == 0)
{
lean_inc_ref(v_rewrites_1649_);
v___y_1661_ = v_rewrites_1649_;
goto v___jp_1660_;
}
else
{
size_t v___x_1669_; size_t v___x_1670_; lean_object* v___x_1671_; 
v___x_1669_ = ((size_t)0ULL);
v___x_1670_ = lean_usize_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable___closed__3, &l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable___closed__3_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable___closed__3);
lean_inc_ref(v_rewrites_1649_);
v___x_1671_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__4(v___x_1651_, v___x_1669_, v___x_1670_, v_rewrites_1649_);
v___y_1661_ = v___x_1671_;
goto v___jp_1660_;
}
}
else
{
size_t v___x_1672_; size_t v___x_1673_; lean_object* v___x_1674_; 
v___x_1672_ = ((size_t)0ULL);
v___x_1673_ = lean_usize_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable___closed__3, &l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable___closed__3_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable___closed__3);
lean_inc_ref(v_rewrites_1649_);
v___x_1674_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__4(v___x_1651_, v___x_1672_, v___x_1673_, v_rewrites_1649_);
v___y_1661_ = v___x_1674_;
goto v___jp_1660_;
}
}
v___jp_1628_:
{
lean_object* v___x_1632_; lean_object* v___x_1633_; 
lean_inc_ref(v___y_1629_);
v___x_1632_ = l_Array_append___redArg(v___y_1629_, v___y_1631_);
lean_dec_ref(v___y_1631_);
v___x_1633_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals(v___x_1632_, v_a_1623_, v_a_1624_, v_a_1625_, v_a_1626_);
lean_dec_ref(v___x_1632_);
if (lean_obj_tag(v___x_1633_) == 0)
{
lean_object* v_a_1634_; lean_object* v_dummy_1635_; lean_object* v_nargs_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; 
v_a_1634_ = lean_ctor_get(v___x_1633_, 0);
lean_inc(v_a_1634_);
lean_dec_ref_known(v___x_1633_, 1);
v_dummy_1635_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__2___closed__7, &l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__2___closed__7_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__2___closed__7);
v_nargs_1636_ = l_Lean_Expr_getAppNumArgs(v_rhs_1619_);
lean_inc(v_nargs_1636_);
v___x_1637_ = lean_mk_array(v_nargs_1636_, v_dummy_1635_);
v___x_1638_ = lean_unsigned_to_nat(1u);
v___x_1639_ = lean_nat_sub(v_nargs_1636_, v___x_1638_);
lean_dec(v_nargs_1636_);
v___x_1640_ = l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__2(v_op_1620_, v___y_1630_, v_a_1634_, v_rhs_1619_, v___x_1637_, v___x_1639_, v_a_1621_, v_a_1622_, v_a_1623_, v_a_1624_, v_a_1625_, v_a_1626_);
lean_dec(v_a_1634_);
lean_dec_ref(v___y_1630_);
return v___x_1640_;
}
else
{
lean_object* v_a_1641_; lean_object* v___x_1643_; uint8_t v_isShared_1644_; uint8_t v_isSharedCheck_1648_; 
lean_dec_ref(v___y_1630_);
lean_dec_ref(v_op_1620_);
lean_dec_ref(v_rhs_1619_);
v_a_1641_ = lean_ctor_get(v___x_1633_, 0);
v_isSharedCheck_1648_ = !lean_is_exclusive(v___x_1633_);
if (v_isSharedCheck_1648_ == 0)
{
v___x_1643_ = v___x_1633_;
v_isShared_1644_ = v_isSharedCheck_1648_;
goto v_resetjp_1642_;
}
else
{
lean_inc(v_a_1641_);
lean_dec(v___x_1633_);
v___x_1643_ = lean_box(0);
v_isShared_1644_ = v_isSharedCheck_1648_;
goto v_resetjp_1642_;
}
v_resetjp_1642_:
{
lean_object* v___x_1646_; 
if (v_isShared_1644_ == 0)
{
v___x_1646_ = v___x_1643_;
goto v_reusejp_1645_;
}
else
{
lean_object* v_reuseFailAlloc_1647_; 
v_reuseFailAlloc_1647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1647_, 0, v_a_1641_);
v___x_1646_ = v_reuseFailAlloc_1647_;
goto v_reusejp_1645_;
}
v_reusejp_1645_:
{
return v___x_1646_;
}
}
}
}
v___jp_1652_:
{
if (lean_obj_tag(v_terminal_x3f_1650_) == 0)
{
lean_object* v___x_1655_; 
v___x_1655_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_upperAdjoint___closed__3));
v___y_1629_ = v___y_1654_;
v___y_1630_ = v___y_1653_;
v___y_1631_ = v___x_1655_;
goto v___jp_1628_;
}
else
{
lean_object* v_val_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; 
v_val_1656_ = lean_ctor_get(v_terminal_x3f_1650_, 0);
v___x_1657_ = lean_unsigned_to_nat(1u);
v___x_1658_ = lean_mk_empty_array_with_capacity(v___x_1657_);
lean_inc(v_val_1656_);
v___x_1659_ = lean_array_push(v___x_1658_, v_val_1656_);
v___y_1629_ = v___y_1654_;
v___y_1630_ = v___y_1653_;
v___y_1631_ = v___x_1659_;
goto v___jp_1628_;
}
}
v___jp_1660_:
{
lean_object* v___x_1662_; uint8_t v___x_1663_; 
v___x_1662_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_upperAdjoint___closed__3));
v___x_1663_ = lean_uint8_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable___closed__1, &l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable___closed__1_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable___closed__1);
if (v___x_1663_ == 0)
{
v___y_1653_ = v___y_1661_;
v___y_1654_ = v___x_1662_;
goto v___jp_1652_;
}
else
{
uint8_t v___x_1664_; 
v___x_1664_ = lean_uint8_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable___closed__2, &l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable___closed__2_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable___closed__2);
if (v___x_1664_ == 0)
{
if (v___x_1663_ == 0)
{
v___y_1653_ = v___y_1661_;
v___y_1654_ = v___x_1662_;
goto v___jp_1652_;
}
else
{
lean_object* v___x_1665_; 
v___x_1665_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule___closed__0, &l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule___closed__0_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule___closed__0);
v___y_1653_ = v___y_1661_;
v___y_1654_ = v___x_1665_;
goto v___jp_1652_;
}
}
else
{
lean_object* v___x_1666_; 
v___x_1666_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule___closed__0, &l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule___closed__0_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule___closed__0);
v___y_1653_ = v___y_1661_;
v___y_1654_ = v___x_1666_;
goto v___jp_1652_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule___boxed(lean_object* v_rhs_1675_, lean_object* v_op_1676_, lean_object* v_a_1677_, lean_object* v_a_1678_, lean_object* v_a_1679_, lean_object* v_a_1680_, lean_object* v_a_1681_, lean_object* v_a_1682_, lean_object* v_a_1683_){
_start:
{
lean_object* v_res_1684_; 
v_res_1684_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule(v_rhs_1675_, v_op_1676_, v_a_1677_, v_a_1678_, v_a_1679_, v_a_1680_, v_a_1681_, v_a_1682_);
lean_dec(v_a_1682_);
lean_dec_ref(v_a_1681_);
lean_dec(v_a_1680_);
lean_dec_ref(v_a_1679_);
lean_dec(v_a_1678_);
lean_dec_ref(v_a_1677_);
return v_res_1684_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__0(size_t v_sz_1685_, size_t v_i_1686_, lean_object* v_bs_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_){
_start:
{
lean_object* v___x_1695_; 
v___x_1695_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__0___redArg(v_sz_1685_, v_i_1686_, v_bs_1687_, v___y_1690_, v___y_1691_, v___y_1692_, v___y_1693_);
return v___x_1695_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__0___boxed(lean_object* v_sz_1696_, lean_object* v_i_1697_, lean_object* v_bs_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_){
_start:
{
size_t v_sz_boxed_1706_; size_t v_i_boxed_1707_; lean_object* v_res_1708_; 
v_sz_boxed_1706_ = lean_unbox_usize(v_sz_1696_);
lean_dec(v_sz_1696_);
v_i_boxed_1707_ = lean_unbox_usize(v_i_1697_);
lean_dec(v_i_1697_);
v_res_1708_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__0(v_sz_boxed_1706_, v_i_boxed_1707_, v_bs_1698_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_);
lean_dec(v___y_1704_);
lean_dec_ref(v___y_1703_);
lean_dec(v___y_1702_);
lean_dec_ref(v___y_1701_);
lean_dec(v___y_1700_);
lean_dec_ref(v___y_1699_);
return v_res_1708_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__1(lean_object* v_00_u03b2_1709_, lean_object* v_m_1710_, lean_object* v_a_1711_){
_start:
{
lean_object* v___x_1712_; 
v___x_1712_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__1___redArg(v_m_1710_, v_a_1711_);
return v___x_1712_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__1___boxed(lean_object* v_00_u03b2_1713_, lean_object* v_m_1714_, lean_object* v_a_1715_){
_start:
{
lean_object* v_res_1716_; 
v_res_1716_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__1(v_00_u03b2_1713_, v_m_1714_, v_a_1715_);
lean_dec(v_a_1715_);
lean_dec_ref(v_m_1714_);
return v_res_1716_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__1_spec__1(lean_object* v_00_u03b2_1717_, lean_object* v_a_1718_, lean_object* v_x_1719_){
_start:
{
lean_object* v___x_1720_; 
v___x_1720_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__1_spec__1___redArg(v_a_1718_, v_x_1719_);
return v___x_1720_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__1_spec__1___boxed(lean_object* v_00_u03b2_1721_, lean_object* v_a_1722_, lean_object* v_x_1723_){
_start:
{
lean_object* v_res_1724_; 
v_res_1724_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__1_spec__1(v_00_u03b2_1721_, v_a_1722_, v_x_1723_);
lean_dec(v_x_1723_);
lean_dec(v_a_1722_);
return v_res_1724_;
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
