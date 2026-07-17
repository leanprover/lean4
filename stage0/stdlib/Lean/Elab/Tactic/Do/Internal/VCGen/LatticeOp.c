// Lean compiler output
// Module: Lean.Elab.Tactic.Do.Internal.VCGen.LatticeOp
// Imports: public import Lean.Meta.Sym.Apply public import Std.Internal.Do.Order.Heyting public import Lean.Elab.Tactic.Do.Internal.VCGen.FrameProc import Lean.Meta.AppBuilder import Lean.Meta.AbstractMVars
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
lean_object* l_Lean_Expr_sort___override(lean_object*);
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
lean_object* l_Lean_Meta_mkCongrFun(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Lean_Meta_saveState___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallMetaTelescopeReducing(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SavedState_restore___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Array_extract___redArg(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Meta_mkEqTrans(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_abstractMVars(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_mkBackwardRuleFromExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkCongrArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqSymm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_constName_x3f(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 107, .m_capacity = 107, .m_length = 106, .m_data = "lattice saturation did not terminate; a registered `@[frameproc]` rewrite set is likely non-terminating on"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp___closed__1_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp___closed__2;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_spec__1___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_spec__1___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_spec__1___closed__1_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_spec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_spec__1___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_spec__1___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_spec__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_spec__1___closed__3;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "mp"};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__2___closed__0 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__2___closed__0_value;
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__2___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_spec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__2___closed__1_value_aux_0),((lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(183, 66, 254, 161, 210, 133, 94, 78)}};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__2___closed__1 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__2___closed__1_value;
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "frame operator `"};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__2___closed__2 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__2___closed__2_value;
static lean_once_cell_t l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__2___closed__3;
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 94, .m_capacity = 94, .m_length = 93, .m_data = "` neither reduces nor has a registered terminal; its lattice split rule would be the identity"};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__2___closed__4 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__2___closed__4_value;
static lean_once_cell_t l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__2___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__2___closed__5;
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__4(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__3(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_spec__0(lean_object* v_as_622_, size_t v_i_623_, size_t v_stop_624_, lean_object* v_b_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_, lean_object* v___y_629_){
_start:
{
uint8_t v___x_631_; 
v___x_631_ = lean_usize_dec_eq(v_i_623_, v_stop_624_);
if (v___x_631_ == 0)
{
lean_object* v___x_632_; lean_object* v___x_633_; 
v___x_632_ = lean_array_uget_borrowed(v_as_622_, v_i_623_);
lean_inc(v___x_632_);
v___x_633_ = l_Lean_Meta_mkCongrFun(v_b_625_, v___x_632_, v___y_626_, v___y_627_, v___y_628_, v___y_629_);
if (lean_obj_tag(v___x_633_) == 0)
{
lean_object* v_a_634_; size_t v___x_635_; size_t v___x_636_; 
v_a_634_ = lean_ctor_get(v___x_633_, 0);
lean_inc(v_a_634_);
lean_dec_ref_known(v___x_633_, 1);
v___x_635_ = ((size_t)1ULL);
v___x_636_ = lean_usize_add(v_i_623_, v___x_635_);
v_i_623_ = v___x_636_;
v_b_625_ = v_a_634_;
goto _start;
}
else
{
return v___x_633_;
}
}
else
{
lean_object* v___x_638_; 
v___x_638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_638_, 0, v_b_625_);
return v___x_638_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_spec__0___boxed(lean_object* v_as_639_, lean_object* v_i_640_, lean_object* v_stop_641_, lean_object* v_b_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_, lean_object* v___y_646_, lean_object* v___y_647_){
_start:
{
size_t v_i_boxed_648_; size_t v_stop_boxed_649_; lean_object* v_res_650_; 
v_i_boxed_648_ = lean_unbox_usize(v_i_640_);
lean_dec(v_i_640_);
v_stop_boxed_649_ = lean_unbox_usize(v_stop_641_);
lean_dec(v_stop_641_);
v_res_650_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_spec__0(v_as_639_, v_i_boxed_648_, v_stop_boxed_649_, v_b_642_, v___y_643_, v___y_644_, v___y_645_, v___y_646_);
lean_dec(v___y_646_);
lean_dec_ref(v___y_645_);
lean_dec(v___y_644_);
lean_dec_ref(v___y_643_);
lean_dec_ref(v_as_639_);
return v_res_650_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp___closed__2(void){
_start:
{
lean_object* v___x_655_; lean_object* v___x_656_; 
v___x_655_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp___closed__1));
v___x_656_ = l_Lean_stringToMessageData(v___x_655_);
return v___x_656_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_spec__1___closed__3(void){
_start:
{
lean_object* v___x_663_; lean_object* v_dummy_664_; 
v___x_663_ = lean_box(0);
v_dummy_664_ = l_Lean_Expr_sort___override(v___x_663_);
return v_dummy_664_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_spec__1(lean_object* v_e_665_, lean_object* v_fuel_666_, lean_object* v_rewrites_667_, lean_object* v_as_668_, size_t v_sz_669_, size_t v_i_670_, lean_object* v_b_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_){
_start:
{
uint8_t v___x_677_; 
v___x_677_ = lean_usize_dec_lt(v_i_670_, v_sz_669_);
if (v___x_677_ == 0)
{
lean_object* v___x_678_; 
lean_dec_ref(v_e_665_);
v___x_678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_678_, 0, v_b_671_);
return v___x_678_;
}
else
{
lean_object* v___x_679_; 
lean_dec_ref(v_b_671_);
v___x_679_ = l_Lean_Meta_saveState___redArg(v___y_673_, v___y_675_);
if (lean_obj_tag(v___x_679_) == 0)
{
lean_object* v_a_680_; lean_object* v_a_681_; lean_object* v___x_682_; 
v_a_680_ = lean_ctor_get(v___x_679_, 0);
lean_inc(v_a_680_);
lean_dec_ref_known(v___x_679_, 1);
v_a_681_ = lean_array_uget_borrowed(v_as_668_, v_i_670_);
lean_inc(v_a_681_);
v___x_682_ = l_Lean_Meta_mkConstWithFreshMVarLevels(v_a_681_, v___y_672_, v___y_673_, v___y_674_, v___y_675_);
if (lean_obj_tag(v___x_682_) == 0)
{
lean_object* v_a_683_; lean_object* v___x_684_; 
v_a_683_ = lean_ctor_get(v___x_682_, 0);
lean_inc_n(v_a_683_, 2);
lean_dec_ref_known(v___x_682_, 1);
lean_inc(v___y_675_);
lean_inc_ref(v___y_674_);
lean_inc(v___y_673_);
lean_inc_ref(v___y_672_);
v___x_684_ = lean_infer_type(v_a_683_, v___y_672_, v___y_673_, v___y_674_, v___y_675_);
if (lean_obj_tag(v___x_684_) == 0)
{
lean_object* v_a_685_; lean_object* v___x_686_; uint8_t v___x_687_; lean_object* v___x_688_; 
v_a_685_ = lean_ctor_get(v___x_684_, 0);
lean_inc(v_a_685_);
lean_dec_ref_known(v___x_684_, 1);
v___x_686_ = lean_box(0);
v___x_687_ = 0;
v___x_688_ = l_Lean_Meta_forallMetaTelescopeReducing(v_a_685_, v___x_686_, v___x_687_, v___y_672_, v___y_673_, v___y_674_, v___y_675_);
if (lean_obj_tag(v___x_688_) == 0)
{
lean_object* v_a_689_; lean_object* v_snd_690_; lean_object* v_fst_691_; lean_object* v___x_693_; uint8_t v_isShared_694_; uint8_t v_isSharedCheck_826_; 
v_a_689_ = lean_ctor_get(v___x_688_, 0);
lean_inc(v_a_689_);
lean_dec_ref_known(v___x_688_, 1);
v_snd_690_ = lean_ctor_get(v_a_689_, 1);
v_fst_691_ = lean_ctor_get(v_a_689_, 0);
v_isSharedCheck_826_ = !lean_is_exclusive(v_a_689_);
if (v_isSharedCheck_826_ == 0)
{
v___x_693_ = v_a_689_;
v_isShared_694_ = v_isSharedCheck_826_;
goto v_resetjp_692_;
}
else
{
lean_inc(v_snd_690_);
lean_inc(v_fst_691_);
lean_dec(v_a_689_);
v___x_693_ = lean_box(0);
v_isShared_694_ = v_isSharedCheck_826_;
goto v_resetjp_692_;
}
v_resetjp_692_:
{
lean_object* v_snd_695_; lean_object* v___x_697_; uint8_t v_isShared_698_; uint8_t v_isSharedCheck_824_; 
v_snd_695_ = lean_ctor_get(v_snd_690_, 1);
v_isSharedCheck_824_ = !lean_is_exclusive(v_snd_690_);
if (v_isSharedCheck_824_ == 0)
{
lean_object* v_unused_825_; 
v_unused_825_ = lean_ctor_get(v_snd_690_, 0);
lean_dec(v_unused_825_);
v___x_697_ = v_snd_690_;
v_isShared_698_ = v_isSharedCheck_824_;
goto v_resetjp_696_;
}
else
{
lean_inc(v_snd_695_);
lean_dec(v_snd_690_);
v___x_697_ = lean_box(0);
v_isShared_698_ = v_isSharedCheck_824_;
goto v_resetjp_696_;
}
v_resetjp_696_:
{
lean_object* v___x_699_; 
v___x_699_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__0___redArg(v_snd_695_, v___y_673_);
if (lean_obj_tag(v___x_699_) == 0)
{
lean_object* v_a_700_; lean_object* v___x_702_; uint8_t v_isShared_703_; uint8_t v_isSharedCheck_815_; 
v_a_700_ = lean_ctor_get(v___x_699_, 0);
v_isSharedCheck_815_ = !lean_is_exclusive(v___x_699_);
if (v_isSharedCheck_815_ == 0)
{
v___x_702_ = v___x_699_;
v_isShared_703_ = v_isSharedCheck_815_;
goto v_resetjp_701_;
}
else
{
lean_inc(v_a_700_);
lean_dec(v___x_699_);
v___x_702_ = lean_box(0);
v_isShared_703_ = v_isSharedCheck_815_;
goto v_resetjp_701_;
}
v_resetjp_701_:
{
lean_object* v___x_704_; lean_object* v___y_706_; lean_object* v_proof_707_; lean_object* v___x_719_; lean_object* v___y_721_; lean_object* v___y_722_; lean_object* v___x_735_; lean_object* v___x_736_; uint8_t v___x_737_; 
v___x_704_ = lean_box(0);
v___x_719_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_spec__1___closed__0));
v___x_735_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_spec__1___closed__2));
v___x_736_ = lean_unsigned_to_nat(3u);
v___x_737_ = l_Lean_Expr_isAppOfArity(v_a_700_, v___x_735_, v___x_736_);
if (v___x_737_ == 0)
{
lean_del_object(v___x_702_);
lean_dec(v_a_700_);
lean_del_object(v___x_697_);
lean_del_object(v___x_693_);
lean_dec(v_fst_691_);
lean_dec(v_a_683_);
v___y_721_ = v___y_673_;
v___y_722_ = v___y_675_;
goto v___jp_720_;
}
else
{
lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; uint8_t v___x_742_; 
v___x_738_ = l_Lean_Expr_appFn_x21(v_a_700_);
v___x_739_ = l_Lean_Expr_appArg_x21(v___x_738_);
lean_dec_ref(v___x_738_);
v___x_740_ = l_Lean_Expr_getAppNumArgs(v___x_739_);
v___x_741_ = l_Lean_Expr_getAppNumArgs(v_e_665_);
v___x_742_ = lean_nat_dec_le(v___x_740_, v___x_741_);
if (v___x_742_ == 0)
{
lean_dec(v___x_741_);
lean_dec(v___x_740_);
lean_dec_ref(v___x_739_);
lean_del_object(v___x_702_);
lean_dec(v_a_700_);
lean_del_object(v___x_697_);
lean_del_object(v___x_693_);
lean_dec(v_fst_691_);
lean_dec(v_a_683_);
v___y_721_ = v___y_673_;
v___y_722_ = v___y_675_;
goto v___jp_720_;
}
else
{
lean_object* v_dummy_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; 
v_dummy_743_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_spec__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_spec__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_spec__1___closed__3);
lean_inc(v___x_741_);
v___x_744_ = lean_mk_array(v___x_741_, v_dummy_743_);
v___x_745_ = lean_unsigned_to_nat(1u);
v___x_746_ = lean_nat_sub(v___x_741_, v___x_745_);
lean_dec(v___x_741_);
lean_inc_ref(v_e_665_);
v___x_747_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_665_, v___x_744_, v___x_746_);
v___x_748_ = l_Lean_Expr_getAppFn(v_e_665_);
v___x_749_ = lean_unsigned_to_nat(0u);
lean_inc(v___x_740_);
v___x_750_ = l_Array_extract___redArg(v___x_747_, v___x_749_, v___x_740_);
v___x_751_ = l_Lean_mkAppN(v___x_748_, v___x_750_);
lean_dec_ref(v___x_750_);
v___x_752_ = l_Lean_Meta_isExprDefEq(v___x_739_, v___x_751_, v___y_672_, v___y_673_, v___y_674_, v___y_675_);
if (lean_obj_tag(v___x_752_) == 0)
{
lean_object* v_a_753_; uint8_t v___x_754_; 
v_a_753_ = lean_ctor_get(v___x_752_, 0);
lean_inc(v_a_753_);
lean_dec_ref_known(v___x_752_, 1);
v___x_754_ = lean_unbox(v_a_753_);
lean_dec(v_a_753_);
if (v___x_754_ == 0)
{
lean_dec_ref(v___x_747_);
lean_dec(v___x_740_);
lean_del_object(v___x_702_);
lean_dec(v_a_700_);
lean_del_object(v___x_697_);
lean_del_object(v___x_693_);
lean_dec(v_fst_691_);
lean_dec(v_a_683_);
v___y_721_ = v___y_673_;
v___y_722_ = v___y_675_;
goto v___jp_720_;
}
else
{
lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v_a_758_; lean_object* v___y_787_; lean_object* v___x_797_; lean_object* v___x_798_; uint8_t v___x_799_; 
lean_dec(v_a_680_);
lean_dec_ref(v_e_665_);
v___x_755_ = lean_array_get_size(v___x_747_);
v___x_756_ = l_Array_extract___redArg(v___x_747_, v___x_740_, v___x_755_);
lean_dec_ref(v___x_747_);
v___x_797_ = l_Lean_mkAppN(v_a_683_, v_fst_691_);
lean_dec(v_fst_691_);
v___x_798_ = lean_array_get_size(v___x_756_);
v___x_799_ = lean_nat_dec_lt(v___x_749_, v___x_798_);
if (v___x_799_ == 0)
{
v_a_758_ = v___x_797_;
goto v___jp_757_;
}
else
{
uint8_t v___x_800_; 
v___x_800_ = lean_nat_dec_le(v___x_798_, v___x_798_);
if (v___x_800_ == 0)
{
if (v___x_799_ == 0)
{
v_a_758_ = v___x_797_;
goto v___jp_757_;
}
else
{
size_t v___x_801_; size_t v___x_802_; lean_object* v___x_803_; 
v___x_801_ = ((size_t)0ULL);
v___x_802_ = lean_usize_of_nat(v___x_798_);
v___x_803_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_spec__0(v___x_756_, v___x_801_, v___x_802_, v___x_797_, v___y_672_, v___y_673_, v___y_674_, v___y_675_);
v___y_787_ = v___x_803_;
goto v___jp_786_;
}
}
else
{
size_t v___x_804_; size_t v___x_805_; lean_object* v___x_806_; 
v___x_804_ = ((size_t)0ULL);
v___x_805_ = lean_usize_of_nat(v___x_798_);
v___x_806_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_spec__0(v___x_756_, v___x_804_, v___x_805_, v___x_797_, v___y_672_, v___y_673_, v___y_674_, v___y_675_);
v___y_787_ = v___x_806_;
goto v___jp_786_;
}
}
v___jp_757_:
{
lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; 
v___x_759_ = l_Lean_Expr_appArg_x21(v_a_700_);
lean_dec(v_a_700_);
v___x_760_ = l_Lean_mkAppN(v___x_759_, v___x_756_);
lean_dec_ref(v___x_756_);
v___x_761_ = lean_nat_sub(v_fuel_666_, v___x_745_);
v___x_762_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp(v_rewrites_667_, v___x_760_, v___x_761_, v___y_672_, v___y_673_, v___y_674_, v___y_675_);
lean_dec(v___x_761_);
if (lean_obj_tag(v___x_762_) == 0)
{
lean_object* v_a_763_; lean_object* v_snd_764_; 
v_a_763_ = lean_ctor_get(v___x_762_, 0);
lean_inc(v_a_763_);
lean_dec_ref_known(v___x_762_, 1);
v_snd_764_ = lean_ctor_get(v_a_763_, 1);
if (lean_obj_tag(v_snd_764_) == 0)
{
lean_object* v_fst_765_; 
v_fst_765_ = lean_ctor_get(v_a_763_, 0);
lean_inc(v_fst_765_);
lean_dec(v_a_763_);
v___y_706_ = v_fst_765_;
v_proof_707_ = v_a_758_;
goto v___jp_705_;
}
else
{
lean_object* v_fst_766_; lean_object* v_val_767_; lean_object* v___x_768_; 
lean_inc_ref(v_snd_764_);
v_fst_766_ = lean_ctor_get(v_a_763_, 0);
lean_inc(v_fst_766_);
lean_dec(v_a_763_);
v_val_767_ = lean_ctor_get(v_snd_764_, 0);
lean_inc(v_val_767_);
lean_dec_ref_known(v_snd_764_, 1);
v___x_768_ = l_Lean_Meta_mkEqTrans(v_a_758_, v_val_767_, v___y_672_, v___y_673_, v___y_674_, v___y_675_);
if (lean_obj_tag(v___x_768_) == 0)
{
lean_object* v_a_769_; 
v_a_769_ = lean_ctor_get(v___x_768_, 0);
lean_inc(v_a_769_);
lean_dec_ref_known(v___x_768_, 1);
v___y_706_ = v_fst_766_;
v_proof_707_ = v_a_769_;
goto v___jp_705_;
}
else
{
lean_object* v_a_770_; lean_object* v___x_772_; uint8_t v_isShared_773_; uint8_t v_isSharedCheck_777_; 
lean_dec(v_fst_766_);
lean_del_object(v___x_702_);
lean_del_object(v___x_697_);
lean_del_object(v___x_693_);
v_a_770_ = lean_ctor_get(v___x_768_, 0);
v_isSharedCheck_777_ = !lean_is_exclusive(v___x_768_);
if (v_isSharedCheck_777_ == 0)
{
v___x_772_ = v___x_768_;
v_isShared_773_ = v_isSharedCheck_777_;
goto v_resetjp_771_;
}
else
{
lean_inc(v_a_770_);
lean_dec(v___x_768_);
v___x_772_ = lean_box(0);
v_isShared_773_ = v_isSharedCheck_777_;
goto v_resetjp_771_;
}
v_resetjp_771_:
{
lean_object* v___x_775_; 
if (v_isShared_773_ == 0)
{
v___x_775_ = v___x_772_;
goto v_reusejp_774_;
}
else
{
lean_object* v_reuseFailAlloc_776_; 
v_reuseFailAlloc_776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_776_, 0, v_a_770_);
v___x_775_ = v_reuseFailAlloc_776_;
goto v_reusejp_774_;
}
v_reusejp_774_:
{
return v___x_775_;
}
}
}
}
}
else
{
lean_object* v_a_778_; lean_object* v___x_780_; uint8_t v_isShared_781_; uint8_t v_isSharedCheck_785_; 
lean_dec_ref(v_a_758_);
lean_del_object(v___x_702_);
lean_del_object(v___x_697_);
lean_del_object(v___x_693_);
v_a_778_ = lean_ctor_get(v___x_762_, 0);
v_isSharedCheck_785_ = !lean_is_exclusive(v___x_762_);
if (v_isSharedCheck_785_ == 0)
{
v___x_780_ = v___x_762_;
v_isShared_781_ = v_isSharedCheck_785_;
goto v_resetjp_779_;
}
else
{
lean_inc(v_a_778_);
lean_dec(v___x_762_);
v___x_780_ = lean_box(0);
v_isShared_781_ = v_isSharedCheck_785_;
goto v_resetjp_779_;
}
v_resetjp_779_:
{
lean_object* v___x_783_; 
if (v_isShared_781_ == 0)
{
v___x_783_ = v___x_780_;
goto v_reusejp_782_;
}
else
{
lean_object* v_reuseFailAlloc_784_; 
v_reuseFailAlloc_784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_784_, 0, v_a_778_);
v___x_783_ = v_reuseFailAlloc_784_;
goto v_reusejp_782_;
}
v_reusejp_782_:
{
return v___x_783_;
}
}
}
}
v___jp_786_:
{
if (lean_obj_tag(v___y_787_) == 0)
{
lean_object* v_a_788_; 
v_a_788_ = lean_ctor_get(v___y_787_, 0);
lean_inc(v_a_788_);
lean_dec_ref_known(v___y_787_, 1);
v_a_758_ = v_a_788_;
goto v___jp_757_;
}
else
{
lean_object* v_a_789_; lean_object* v___x_791_; uint8_t v_isShared_792_; uint8_t v_isSharedCheck_796_; 
lean_dec_ref(v___x_756_);
lean_del_object(v___x_702_);
lean_dec(v_a_700_);
lean_del_object(v___x_697_);
lean_del_object(v___x_693_);
v_a_789_ = lean_ctor_get(v___y_787_, 0);
v_isSharedCheck_796_ = !lean_is_exclusive(v___y_787_);
if (v_isSharedCheck_796_ == 0)
{
v___x_791_ = v___y_787_;
v_isShared_792_ = v_isSharedCheck_796_;
goto v_resetjp_790_;
}
else
{
lean_inc(v_a_789_);
lean_dec(v___y_787_);
v___x_791_ = lean_box(0);
v_isShared_792_ = v_isSharedCheck_796_;
goto v_resetjp_790_;
}
v_resetjp_790_:
{
lean_object* v___x_794_; 
if (v_isShared_792_ == 0)
{
v___x_794_ = v___x_791_;
goto v_reusejp_793_;
}
else
{
lean_object* v_reuseFailAlloc_795_; 
v_reuseFailAlloc_795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_795_, 0, v_a_789_);
v___x_794_ = v_reuseFailAlloc_795_;
goto v_reusejp_793_;
}
v_reusejp_793_:
{
return v___x_794_;
}
}
}
}
}
}
else
{
lean_object* v_a_807_; lean_object* v___x_809_; uint8_t v_isShared_810_; uint8_t v_isSharedCheck_814_; 
lean_dec_ref(v___x_747_);
lean_dec(v___x_740_);
lean_del_object(v___x_702_);
lean_dec(v_a_700_);
lean_del_object(v___x_697_);
lean_del_object(v___x_693_);
lean_dec(v_fst_691_);
lean_dec(v_a_683_);
lean_dec(v_a_680_);
lean_dec_ref(v_e_665_);
v_a_807_ = lean_ctor_get(v___x_752_, 0);
v_isSharedCheck_814_ = !lean_is_exclusive(v___x_752_);
if (v_isSharedCheck_814_ == 0)
{
v___x_809_ = v___x_752_;
v_isShared_810_ = v_isSharedCheck_814_;
goto v_resetjp_808_;
}
else
{
lean_inc(v_a_807_);
lean_dec(v___x_752_);
v___x_809_ = lean_box(0);
v_isShared_810_ = v_isSharedCheck_814_;
goto v_resetjp_808_;
}
v_resetjp_808_:
{
lean_object* v___x_812_; 
if (v_isShared_810_ == 0)
{
v___x_812_ = v___x_809_;
goto v_reusejp_811_;
}
else
{
lean_object* v_reuseFailAlloc_813_; 
v_reuseFailAlloc_813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_813_, 0, v_a_807_);
v___x_812_ = v_reuseFailAlloc_813_;
goto v_reusejp_811_;
}
v_reusejp_811_:
{
return v___x_812_;
}
}
}
}
}
v___jp_705_:
{
lean_object* v___x_708_; lean_object* v___x_710_; 
v___x_708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_708_, 0, v_proof_707_);
if (v_isShared_698_ == 0)
{
lean_ctor_set(v___x_697_, 1, v___x_708_);
lean_ctor_set(v___x_697_, 0, v___y_706_);
v___x_710_ = v___x_697_;
goto v_reusejp_709_;
}
else
{
lean_object* v_reuseFailAlloc_718_; 
v_reuseFailAlloc_718_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_718_, 0, v___y_706_);
lean_ctor_set(v_reuseFailAlloc_718_, 1, v___x_708_);
v___x_710_ = v_reuseFailAlloc_718_;
goto v_reusejp_709_;
}
v_reusejp_709_:
{
lean_object* v___x_711_; lean_object* v___x_713_; 
v___x_711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_711_, 0, v___x_710_);
if (v_isShared_694_ == 0)
{
lean_ctor_set(v___x_693_, 1, v___x_704_);
lean_ctor_set(v___x_693_, 0, v___x_711_);
v___x_713_ = v___x_693_;
goto v_reusejp_712_;
}
else
{
lean_object* v_reuseFailAlloc_717_; 
v_reuseFailAlloc_717_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_717_, 0, v___x_711_);
lean_ctor_set(v_reuseFailAlloc_717_, 1, v___x_704_);
v___x_713_ = v_reuseFailAlloc_717_;
goto v_reusejp_712_;
}
v_reusejp_712_:
{
lean_object* v___x_715_; 
if (v_isShared_703_ == 0)
{
lean_ctor_set(v___x_702_, 0, v___x_713_);
v___x_715_ = v___x_702_;
goto v_reusejp_714_;
}
else
{
lean_object* v_reuseFailAlloc_716_; 
v_reuseFailAlloc_716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_716_, 0, v___x_713_);
v___x_715_ = v_reuseFailAlloc_716_;
goto v_reusejp_714_;
}
v_reusejp_714_:
{
return v___x_715_;
}
}
}
}
v___jp_720_:
{
lean_object* v___x_723_; 
v___x_723_ = l_Lean_Meta_SavedState_restore___redArg(v_a_680_, v___y_721_, v___y_722_);
lean_dec(v_a_680_);
if (lean_obj_tag(v___x_723_) == 0)
{
size_t v___x_724_; size_t v___x_725_; 
lean_dec_ref_known(v___x_723_, 1);
v___x_724_ = ((size_t)1ULL);
v___x_725_ = lean_usize_add(v_i_670_, v___x_724_);
v_i_670_ = v___x_725_;
v_b_671_ = v___x_719_;
goto _start;
}
else
{
lean_object* v_a_727_; lean_object* v___x_729_; uint8_t v_isShared_730_; uint8_t v_isSharedCheck_734_; 
lean_dec_ref(v_e_665_);
v_a_727_ = lean_ctor_get(v___x_723_, 0);
v_isSharedCheck_734_ = !lean_is_exclusive(v___x_723_);
if (v_isSharedCheck_734_ == 0)
{
v___x_729_ = v___x_723_;
v_isShared_730_ = v_isSharedCheck_734_;
goto v_resetjp_728_;
}
else
{
lean_inc(v_a_727_);
lean_dec(v___x_723_);
v___x_729_ = lean_box(0);
v_isShared_730_ = v_isSharedCheck_734_;
goto v_resetjp_728_;
}
v_resetjp_728_:
{
lean_object* v___x_732_; 
if (v_isShared_730_ == 0)
{
v___x_732_ = v___x_729_;
goto v_reusejp_731_;
}
else
{
lean_object* v_reuseFailAlloc_733_; 
v_reuseFailAlloc_733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_733_, 0, v_a_727_);
v___x_732_ = v_reuseFailAlloc_733_;
goto v_reusejp_731_;
}
v_reusejp_731_:
{
return v___x_732_;
}
}
}
}
}
}
else
{
lean_object* v_a_816_; lean_object* v___x_818_; uint8_t v_isShared_819_; uint8_t v_isSharedCheck_823_; 
lean_del_object(v___x_697_);
lean_del_object(v___x_693_);
lean_dec(v_fst_691_);
lean_dec(v_a_683_);
lean_dec(v_a_680_);
lean_dec_ref(v_e_665_);
v_a_816_ = lean_ctor_get(v___x_699_, 0);
v_isSharedCheck_823_ = !lean_is_exclusive(v___x_699_);
if (v_isSharedCheck_823_ == 0)
{
v___x_818_ = v___x_699_;
v_isShared_819_ = v_isSharedCheck_823_;
goto v_resetjp_817_;
}
else
{
lean_inc(v_a_816_);
lean_dec(v___x_699_);
v___x_818_ = lean_box(0);
v_isShared_819_ = v_isSharedCheck_823_;
goto v_resetjp_817_;
}
v_resetjp_817_:
{
lean_object* v___x_821_; 
if (v_isShared_819_ == 0)
{
v___x_821_ = v___x_818_;
goto v_reusejp_820_;
}
else
{
lean_object* v_reuseFailAlloc_822_; 
v_reuseFailAlloc_822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_822_, 0, v_a_816_);
v___x_821_ = v_reuseFailAlloc_822_;
goto v_reusejp_820_;
}
v_reusejp_820_:
{
return v___x_821_;
}
}
}
}
}
}
else
{
lean_object* v_a_827_; lean_object* v___x_829_; uint8_t v_isShared_830_; uint8_t v_isSharedCheck_834_; 
lean_dec(v_a_683_);
lean_dec(v_a_680_);
lean_dec_ref(v_e_665_);
v_a_827_ = lean_ctor_get(v___x_688_, 0);
v_isSharedCheck_834_ = !lean_is_exclusive(v___x_688_);
if (v_isSharedCheck_834_ == 0)
{
v___x_829_ = v___x_688_;
v_isShared_830_ = v_isSharedCheck_834_;
goto v_resetjp_828_;
}
else
{
lean_inc(v_a_827_);
lean_dec(v___x_688_);
v___x_829_ = lean_box(0);
v_isShared_830_ = v_isSharedCheck_834_;
goto v_resetjp_828_;
}
v_resetjp_828_:
{
lean_object* v___x_832_; 
if (v_isShared_830_ == 0)
{
v___x_832_ = v___x_829_;
goto v_reusejp_831_;
}
else
{
lean_object* v_reuseFailAlloc_833_; 
v_reuseFailAlloc_833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_833_, 0, v_a_827_);
v___x_832_ = v_reuseFailAlloc_833_;
goto v_reusejp_831_;
}
v_reusejp_831_:
{
return v___x_832_;
}
}
}
}
else
{
lean_object* v_a_835_; lean_object* v___x_837_; uint8_t v_isShared_838_; uint8_t v_isSharedCheck_842_; 
lean_dec(v_a_683_);
lean_dec(v_a_680_);
lean_dec_ref(v_e_665_);
v_a_835_ = lean_ctor_get(v___x_684_, 0);
v_isSharedCheck_842_ = !lean_is_exclusive(v___x_684_);
if (v_isSharedCheck_842_ == 0)
{
v___x_837_ = v___x_684_;
v_isShared_838_ = v_isSharedCheck_842_;
goto v_resetjp_836_;
}
else
{
lean_inc(v_a_835_);
lean_dec(v___x_684_);
v___x_837_ = lean_box(0);
v_isShared_838_ = v_isSharedCheck_842_;
goto v_resetjp_836_;
}
v_resetjp_836_:
{
lean_object* v___x_840_; 
if (v_isShared_838_ == 0)
{
v___x_840_ = v___x_837_;
goto v_reusejp_839_;
}
else
{
lean_object* v_reuseFailAlloc_841_; 
v_reuseFailAlloc_841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_841_, 0, v_a_835_);
v___x_840_ = v_reuseFailAlloc_841_;
goto v_reusejp_839_;
}
v_reusejp_839_:
{
return v___x_840_;
}
}
}
}
else
{
lean_object* v_a_843_; lean_object* v___x_845_; uint8_t v_isShared_846_; uint8_t v_isSharedCheck_850_; 
lean_dec(v_a_680_);
lean_dec_ref(v_e_665_);
v_a_843_ = lean_ctor_get(v___x_682_, 0);
v_isSharedCheck_850_ = !lean_is_exclusive(v___x_682_);
if (v_isSharedCheck_850_ == 0)
{
v___x_845_ = v___x_682_;
v_isShared_846_ = v_isSharedCheck_850_;
goto v_resetjp_844_;
}
else
{
lean_inc(v_a_843_);
lean_dec(v___x_682_);
v___x_845_ = lean_box(0);
v_isShared_846_ = v_isSharedCheck_850_;
goto v_resetjp_844_;
}
v_resetjp_844_:
{
lean_object* v___x_848_; 
if (v_isShared_846_ == 0)
{
v___x_848_ = v___x_845_;
goto v_reusejp_847_;
}
else
{
lean_object* v_reuseFailAlloc_849_; 
v_reuseFailAlloc_849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_849_, 0, v_a_843_);
v___x_848_ = v_reuseFailAlloc_849_;
goto v_reusejp_847_;
}
v_reusejp_847_:
{
return v___x_848_;
}
}
}
}
else
{
lean_object* v_a_851_; lean_object* v___x_853_; uint8_t v_isShared_854_; uint8_t v_isSharedCheck_858_; 
lean_dec_ref(v_e_665_);
v_a_851_ = lean_ctor_get(v___x_679_, 0);
v_isSharedCheck_858_ = !lean_is_exclusive(v___x_679_);
if (v_isSharedCheck_858_ == 0)
{
v___x_853_ = v___x_679_;
v_isShared_854_ = v_isSharedCheck_858_;
goto v_resetjp_852_;
}
else
{
lean_inc(v_a_851_);
lean_dec(v___x_679_);
v___x_853_ = lean_box(0);
v_isShared_854_ = v_isSharedCheck_858_;
goto v_resetjp_852_;
}
v_resetjp_852_:
{
lean_object* v___x_856_; 
if (v_isShared_854_ == 0)
{
v___x_856_ = v___x_853_;
goto v_reusejp_855_;
}
else
{
lean_object* v_reuseFailAlloc_857_; 
v_reuseFailAlloc_857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_857_, 0, v_a_851_);
v___x_856_ = v_reuseFailAlloc_857_;
goto v_reusejp_855_;
}
v_reusejp_855_:
{
return v___x_856_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp(lean_object* v_rewrites_859_, lean_object* v_e_860_, lean_object* v_fuel_861_, lean_object* v_a_862_, lean_object* v_a_863_, lean_object* v_a_864_, lean_object* v_a_865_){
_start:
{
lean_object* v___y_868_; lean_object* v___y_869_; lean_object* v___y_870_; lean_object* v___y_871_; lean_object* v___x_906_; uint8_t v___x_907_; 
v___x_906_ = lean_unsigned_to_nat(0u);
v___x_907_ = lean_nat_dec_eq(v_fuel_861_, v___x_906_);
if (v___x_907_ == 0)
{
v___y_868_ = v_a_862_;
v___y_869_ = v_a_863_;
v___y_870_ = v_a_864_;
v___y_871_ = v_a_865_;
goto v___jp_867_;
}
else
{
lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; 
v___x_908_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp___closed__2, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp___closed__2_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp___closed__2);
lean_inc_ref(v_e_860_);
v___x_909_ = l_Lean_indentExpr(v_e_860_);
v___x_910_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_910_, 0, v___x_908_);
lean_ctor_set(v___x_910_, 1, v___x_909_);
v___x_911_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__1___redArg(v___x_910_, v_a_862_, v_a_863_, v_a_864_, v_a_865_);
if (lean_obj_tag(v___x_911_) == 0)
{
lean_dec_ref_known(v___x_911_, 1);
v___y_868_ = v_a_862_;
v___y_869_ = v_a_863_;
v___y_870_ = v_a_864_;
v___y_871_ = v_a_865_;
goto v___jp_867_;
}
else
{
lean_object* v_a_912_; lean_object* v___x_914_; uint8_t v_isShared_915_; uint8_t v_isSharedCheck_919_; 
lean_dec_ref(v_e_860_);
v_a_912_ = lean_ctor_get(v___x_911_, 0);
v_isSharedCheck_919_ = !lean_is_exclusive(v___x_911_);
if (v_isSharedCheck_919_ == 0)
{
v___x_914_ = v___x_911_;
v_isShared_915_ = v_isSharedCheck_919_;
goto v_resetjp_913_;
}
else
{
lean_inc(v_a_912_);
lean_dec(v___x_911_);
v___x_914_ = lean_box(0);
v_isShared_915_ = v_isSharedCheck_919_;
goto v_resetjp_913_;
}
v_resetjp_913_:
{
lean_object* v___x_917_; 
if (v_isShared_915_ == 0)
{
v___x_917_ = v___x_914_;
goto v_reusejp_916_;
}
else
{
lean_object* v_reuseFailAlloc_918_; 
v_reuseFailAlloc_918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_918_, 0, v_a_912_);
v___x_917_ = v_reuseFailAlloc_918_;
goto v_reusejp_916_;
}
v_reusejp_916_:
{
return v___x_917_;
}
}
}
}
v___jp_867_:
{
lean_object* v___x_872_; lean_object* v___x_873_; size_t v_sz_874_; size_t v___x_875_; lean_object* v___x_876_; 
v___x_872_ = lean_box(0);
v___x_873_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp___closed__0));
v_sz_874_ = lean_array_size(v_rewrites_859_);
v___x_875_ = ((size_t)0ULL);
lean_inc_ref(v_e_860_);
v___x_876_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_spec__1(v_e_860_, v_fuel_861_, v_rewrites_859_, v_rewrites_859_, v_sz_874_, v___x_875_, v___x_873_, v___y_868_, v___y_869_, v___y_870_, v___y_871_);
if (lean_obj_tag(v___x_876_) == 0)
{
lean_object* v_a_877_; lean_object* v___x_879_; uint8_t v_isShared_880_; uint8_t v_isSharedCheck_897_; 
v_a_877_ = lean_ctor_get(v___x_876_, 0);
v_isSharedCheck_897_ = !lean_is_exclusive(v___x_876_);
if (v_isSharedCheck_897_ == 0)
{
v___x_879_ = v___x_876_;
v_isShared_880_ = v_isSharedCheck_897_;
goto v_resetjp_878_;
}
else
{
lean_inc(v_a_877_);
lean_dec(v___x_876_);
v___x_879_ = lean_box(0);
v_isShared_880_ = v_isSharedCheck_897_;
goto v_resetjp_878_;
}
v_resetjp_878_:
{
lean_object* v_fst_881_; lean_object* v___x_883_; uint8_t v_isShared_884_; uint8_t v_isSharedCheck_895_; 
v_fst_881_ = lean_ctor_get(v_a_877_, 0);
v_isSharedCheck_895_ = !lean_is_exclusive(v_a_877_);
if (v_isSharedCheck_895_ == 0)
{
lean_object* v_unused_896_; 
v_unused_896_ = lean_ctor_get(v_a_877_, 1);
lean_dec(v_unused_896_);
v___x_883_ = v_a_877_;
v_isShared_884_ = v_isSharedCheck_895_;
goto v_resetjp_882_;
}
else
{
lean_inc(v_fst_881_);
lean_dec(v_a_877_);
v___x_883_ = lean_box(0);
v_isShared_884_ = v_isSharedCheck_895_;
goto v_resetjp_882_;
}
v_resetjp_882_:
{
if (lean_obj_tag(v_fst_881_) == 0)
{
lean_object* v___x_886_; 
if (v_isShared_884_ == 0)
{
lean_ctor_set(v___x_883_, 1, v___x_872_);
lean_ctor_set(v___x_883_, 0, v_e_860_);
v___x_886_ = v___x_883_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_890_; 
v_reuseFailAlloc_890_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_890_, 0, v_e_860_);
lean_ctor_set(v_reuseFailAlloc_890_, 1, v___x_872_);
v___x_886_ = v_reuseFailAlloc_890_;
goto v_reusejp_885_;
}
v_reusejp_885_:
{
lean_object* v___x_888_; 
if (v_isShared_880_ == 0)
{
lean_ctor_set(v___x_879_, 0, v___x_886_);
v___x_888_ = v___x_879_;
goto v_reusejp_887_;
}
else
{
lean_object* v_reuseFailAlloc_889_; 
v_reuseFailAlloc_889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_889_, 0, v___x_886_);
v___x_888_ = v_reuseFailAlloc_889_;
goto v_reusejp_887_;
}
v_reusejp_887_:
{
return v___x_888_;
}
}
}
else
{
lean_object* v_val_891_; lean_object* v___x_893_; 
lean_del_object(v___x_883_);
lean_dec_ref(v_e_860_);
v_val_891_ = lean_ctor_get(v_fst_881_, 0);
lean_inc(v_val_891_);
lean_dec_ref_known(v_fst_881_, 1);
if (v_isShared_880_ == 0)
{
lean_ctor_set(v___x_879_, 0, v_val_891_);
v___x_893_ = v___x_879_;
goto v_reusejp_892_;
}
else
{
lean_object* v_reuseFailAlloc_894_; 
v_reuseFailAlloc_894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_894_, 0, v_val_891_);
v___x_893_ = v_reuseFailAlloc_894_;
goto v_reusejp_892_;
}
v_reusejp_892_:
{
return v___x_893_;
}
}
}
}
}
else
{
lean_object* v_a_898_; lean_object* v___x_900_; uint8_t v_isShared_901_; uint8_t v_isSharedCheck_905_; 
lean_dec_ref(v_e_860_);
v_a_898_ = lean_ctor_get(v___x_876_, 0);
v_isSharedCheck_905_ = !lean_is_exclusive(v___x_876_);
if (v_isSharedCheck_905_ == 0)
{
v___x_900_ = v___x_876_;
v_isShared_901_ = v_isSharedCheck_905_;
goto v_resetjp_899_;
}
else
{
lean_inc(v_a_898_);
lean_dec(v___x_876_);
v___x_900_ = lean_box(0);
v_isShared_901_ = v_isSharedCheck_905_;
goto v_resetjp_899_;
}
v_resetjp_899_:
{
lean_object* v___x_903_; 
if (v_isShared_901_ == 0)
{
v___x_903_ = v___x_900_;
goto v_reusejp_902_;
}
else
{
lean_object* v_reuseFailAlloc_904_; 
v_reuseFailAlloc_904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_904_, 0, v_a_898_);
v___x_903_ = v_reuseFailAlloc_904_;
goto v_reusejp_902_;
}
v_reusejp_902_:
{
return v___x_903_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp___boxed(lean_object* v_rewrites_920_, lean_object* v_e_921_, lean_object* v_fuel_922_, lean_object* v_a_923_, lean_object* v_a_924_, lean_object* v_a_925_, lean_object* v_a_926_, lean_object* v_a_927_){
_start:
{
lean_object* v_res_928_; 
v_res_928_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp(v_rewrites_920_, v_e_921_, v_fuel_922_, v_a_923_, v_a_924_, v_a_925_, v_a_926_);
lean_dec(v_a_926_);
lean_dec_ref(v_a_925_);
lean_dec(v_a_924_);
lean_dec_ref(v_a_923_);
lean_dec(v_fuel_922_);
lean_dec_ref(v_rewrites_920_);
return v_res_928_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_spec__1___boxed(lean_object* v_e_929_, lean_object* v_fuel_930_, lean_object* v_rewrites_931_, lean_object* v_as_932_, lean_object* v_sz_933_, lean_object* v_i_934_, lean_object* v_b_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_){
_start:
{
size_t v_sz_boxed_941_; size_t v_i_boxed_942_; lean_object* v_res_943_; 
v_sz_boxed_941_ = lean_unbox_usize(v_sz_933_);
lean_dec(v_sz_933_);
v_i_boxed_942_ = lean_unbox_usize(v_i_934_);
lean_dec(v_i_934_);
v_res_943_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_spec__1(v_e_929_, v_fuel_930_, v_rewrites_931_, v_as_932_, v_sz_boxed_941_, v_i_boxed_942_, v_b_935_, v___y_936_, v___y_937_, v___y_938_, v___y_939_);
lean_dec(v___y_939_);
lean_dec_ref(v___y_938_);
lean_dec(v___y_937_);
lean_dec_ref(v___y_936_);
lean_dec_ref(v_as_932_);
lean_dec_ref(v_rewrites_931_);
lean_dec(v_fuel_930_);
return v_res_943_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply___lam__0(lean_object* v_s_944_, lean_object* v_a_945_, lean_object* v_pre_946_, lean_object* v_u_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_){
_start:
{
lean_object* v___x_953_; 
lean_inc_ref(v_u_947_);
v___x_953_ = l_Lean_Meta_mkEq(v_u_947_, v_s_944_, v___y_948_, v___y_949_, v___y_950_, v___y_951_);
if (lean_obj_tag(v___x_953_) == 0)
{
lean_object* v_a_954_; lean_object* v___x_956_; uint8_t v_isShared_957_; uint8_t v_isSharedCheck_985_; 
v_a_954_ = lean_ctor_get(v___x_953_, 0);
v_isSharedCheck_985_ = !lean_is_exclusive(v___x_953_);
if (v_isSharedCheck_985_ == 0)
{
v___x_956_ = v___x_953_;
v_isShared_957_ = v_isSharedCheck_985_;
goto v_resetjp_955_;
}
else
{
lean_inc(v_a_954_);
lean_dec(v___x_953_);
v___x_956_ = lean_box(0);
v_isShared_957_ = v_isSharedCheck_985_;
goto v_resetjp_955_;
}
v_resetjp_955_:
{
lean_object* v___x_958_; lean_object* v___x_960_; 
v___x_958_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_ofProp___closed__2));
if (v_isShared_957_ == 0)
{
lean_ctor_set_tag(v___x_956_, 1);
lean_ctor_set(v___x_956_, 0, v_a_945_);
v___x_960_ = v___x_956_;
goto v_reusejp_959_;
}
else
{
lean_object* v_reuseFailAlloc_984_; 
v_reuseFailAlloc_984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_984_, 0, v_a_945_);
v___x_960_ = v_reuseFailAlloc_984_;
goto v_reusejp_959_;
}
v_reusejp_959_:
{
lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; 
v___x_961_ = lean_box(0);
v___x_962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_962_, 0, v_a_954_);
v___x_963_ = lean_unsigned_to_nat(3u);
v___x_964_ = lean_mk_empty_array_with_capacity(v___x_963_);
v___x_965_ = lean_array_push(v___x_964_, v___x_960_);
v___x_966_ = lean_array_push(v___x_965_, v___x_961_);
v___x_967_ = lean_array_push(v___x_966_, v___x_962_);
v___x_968_ = l_Lean_Meta_mkAppOptM(v___x_958_, v___x_967_, v___y_948_, v___y_949_, v___y_950_, v___y_951_);
if (lean_obj_tag(v___x_968_) == 0)
{
lean_object* v_a_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; 
v_a_969_ = lean_ctor_get(v___x_968_, 0);
lean_inc(v_a_969_);
lean_dec_ref_known(v___x_968_, 1);
v___x_970_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_meet___closed__3));
v___x_971_ = lean_unsigned_to_nat(2u);
v___x_972_ = lean_mk_empty_array_with_capacity(v___x_971_);
v___x_973_ = lean_array_push(v___x_972_, v_a_969_);
v___x_974_ = lean_array_push(v___x_973_, v_pre_946_);
v___x_975_ = l_Lean_Meta_mkAppM(v___x_970_, v___x_974_, v___y_948_, v___y_949_, v___y_950_, v___y_951_);
if (lean_obj_tag(v___x_975_) == 0)
{
lean_object* v_a_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; uint8_t v___x_980_; uint8_t v___x_981_; uint8_t v___x_982_; lean_object* v___x_983_; 
v_a_976_ = lean_ctor_get(v___x_975_, 0);
lean_inc(v_a_976_);
lean_dec_ref_known(v___x_975_, 1);
v___x_977_ = lean_unsigned_to_nat(1u);
v___x_978_ = lean_mk_empty_array_with_capacity(v___x_977_);
v___x_979_ = lean_array_push(v___x_978_, v_u_947_);
v___x_980_ = 0;
v___x_981_ = 1;
v___x_982_ = 1;
v___x_983_ = l_Lean_Meta_mkLambdaFVars(v___x_979_, v_a_976_, v___x_980_, v___x_981_, v___x_980_, v___x_981_, v___x_982_, v___y_948_, v___y_949_, v___y_950_, v___y_951_);
lean_dec_ref(v___x_979_);
return v___x_983_;
}
else
{
lean_dec_ref(v_u_947_);
return v___x_975_;
}
}
else
{
lean_dec_ref(v_u_947_);
lean_dec_ref(v_pre_946_);
return v___x_968_;
}
}
}
}
else
{
lean_dec_ref(v_u_947_);
lean_dec_ref(v_pre_946_);
lean_dec_ref(v_a_945_);
return v___x_953_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply___lam__0___boxed(lean_object* v_s_986_, lean_object* v_a_987_, lean_object* v_pre_988_, lean_object* v_u_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_){
_start:
{
lean_object* v_res_995_; 
v_res_995_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply___lam__0(v_s_986_, v_a_987_, v_pre_988_, v_u_989_, v___y_990_, v___y_991_, v___y_992_, v___y_993_);
lean_dec(v___y_993_);
lean_dec_ref(v___y_992_);
lean_dec(v___y_991_);
lean_dec_ref(v___y_990_);
return v_res_995_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply_spec__0_spec__0___redArg___lam__0(lean_object* v_k_996_, lean_object* v_b_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_){
_start:
{
lean_object* v___x_1003_; 
lean_inc(v___y_1001_);
lean_inc_ref(v___y_1000_);
lean_inc(v___y_999_);
lean_inc_ref(v___y_998_);
v___x_1003_ = lean_apply_6(v_k_996_, v_b_997_, v___y_998_, v___y_999_, v___y_1000_, v___y_1001_, lean_box(0));
return v___x_1003_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply_spec__0_spec__0___redArg___lam__0___boxed(lean_object* v_k_1004_, lean_object* v_b_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_){
_start:
{
lean_object* v_res_1011_; 
v_res_1011_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply_spec__0_spec__0___redArg___lam__0(v_k_1004_, v_b_1005_, v___y_1006_, v___y_1007_, v___y_1008_, v___y_1009_);
lean_dec(v___y_1009_);
lean_dec_ref(v___y_1008_);
lean_dec(v___y_1007_);
lean_dec_ref(v___y_1006_);
return v_res_1011_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply_spec__0_spec__0___redArg(lean_object* v_name_1012_, uint8_t v_bi_1013_, lean_object* v_type_1014_, lean_object* v_k_1015_, uint8_t v_kind_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_){
_start:
{
lean_object* v___f_1022_; lean_object* v___x_1023_; 
v___f_1022_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply_spec__0_spec__0___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1022_, 0, v_k_1015_);
v___x_1023_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1012_, v_bi_1013_, v_type_1014_, v___f_1022_, v_kind_1016_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_);
if (lean_obj_tag(v___x_1023_) == 0)
{
lean_object* v_a_1024_; lean_object* v___x_1026_; uint8_t v_isShared_1027_; uint8_t v_isSharedCheck_1031_; 
v_a_1024_ = lean_ctor_get(v___x_1023_, 0);
v_isSharedCheck_1031_ = !lean_is_exclusive(v___x_1023_);
if (v_isSharedCheck_1031_ == 0)
{
v___x_1026_ = v___x_1023_;
v_isShared_1027_ = v_isSharedCheck_1031_;
goto v_resetjp_1025_;
}
else
{
lean_inc(v_a_1024_);
lean_dec(v___x_1023_);
v___x_1026_ = lean_box(0);
v_isShared_1027_ = v_isSharedCheck_1031_;
goto v_resetjp_1025_;
}
v_resetjp_1025_:
{
lean_object* v___x_1029_; 
if (v_isShared_1027_ == 0)
{
v___x_1029_ = v___x_1026_;
goto v_reusejp_1028_;
}
else
{
lean_object* v_reuseFailAlloc_1030_; 
v_reuseFailAlloc_1030_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1030_, 0, v_a_1024_);
v___x_1029_ = v_reuseFailAlloc_1030_;
goto v_reusejp_1028_;
}
v_reusejp_1028_:
{
return v___x_1029_;
}
}
}
else
{
lean_object* v_a_1032_; lean_object* v___x_1034_; uint8_t v_isShared_1035_; uint8_t v_isSharedCheck_1039_; 
v_a_1032_ = lean_ctor_get(v___x_1023_, 0);
v_isSharedCheck_1039_ = !lean_is_exclusive(v___x_1023_);
if (v_isSharedCheck_1039_ == 0)
{
v___x_1034_ = v___x_1023_;
v_isShared_1035_ = v_isSharedCheck_1039_;
goto v_resetjp_1033_;
}
else
{
lean_inc(v_a_1032_);
lean_dec(v___x_1023_);
v___x_1034_ = lean_box(0);
v_isShared_1035_ = v_isSharedCheck_1039_;
goto v_resetjp_1033_;
}
v_resetjp_1033_:
{
lean_object* v___x_1037_; 
if (v_isShared_1035_ == 0)
{
v___x_1037_ = v___x_1034_;
goto v_reusejp_1036_;
}
else
{
lean_object* v_reuseFailAlloc_1038_; 
v_reuseFailAlloc_1038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1038_, 0, v_a_1032_);
v___x_1037_ = v_reuseFailAlloc_1038_;
goto v_reusejp_1036_;
}
v_reusejp_1036_:
{
return v___x_1037_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply_spec__0_spec__0___redArg___boxed(lean_object* v_name_1040_, lean_object* v_bi_1041_, lean_object* v_type_1042_, lean_object* v_k_1043_, lean_object* v_kind_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_){
_start:
{
uint8_t v_bi_boxed_1050_; uint8_t v_kind_boxed_1051_; lean_object* v_res_1052_; 
v_bi_boxed_1050_ = lean_unbox(v_bi_1041_);
v_kind_boxed_1051_ = lean_unbox(v_kind_1044_);
v_res_1052_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply_spec__0_spec__0___redArg(v_name_1040_, v_bi_boxed_1050_, v_type_1042_, v_k_1043_, v_kind_boxed_1051_, v___y_1045_, v___y_1046_, v___y_1047_, v___y_1048_);
lean_dec(v___y_1048_);
lean_dec_ref(v___y_1047_);
lean_dec(v___y_1046_);
lean_dec_ref(v___y_1045_);
return v_res_1052_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply_spec__0___redArg(lean_object* v_name_1053_, lean_object* v_type_1054_, lean_object* v_k_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_){
_start:
{
uint8_t v___x_1061_; uint8_t v___x_1062_; lean_object* v___x_1063_; 
v___x_1061_ = 0;
v___x_1062_ = 0;
v___x_1063_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply_spec__0_spec__0___redArg(v_name_1053_, v___x_1061_, v_type_1054_, v_k_1055_, v___x_1062_, v___y_1056_, v___y_1057_, v___y_1058_, v___y_1059_);
return v___x_1063_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply_spec__0___redArg___boxed(lean_object* v_name_1064_, lean_object* v_type_1065_, lean_object* v_k_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_){
_start:
{
lean_object* v_res_1072_; 
v_res_1072_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply_spec__0___redArg(v_name_1064_, v_type_1065_, v_k_1066_, v___y_1067_, v___y_1068_, v___y_1069_, v___y_1070_);
lean_dec(v___y_1070_);
lean_dec_ref(v___y_1069_);
lean_dec(v___y_1068_);
lean_dec_ref(v___y_1067_);
return v_res_1072_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply___closed__1(void){
_start:
{
lean_object* v___x_1074_; lean_object* v___x_1075_; 
v___x_1074_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply___closed__0));
v___x_1075_ = l_Lean_stringToMessageData(v___x_1074_);
return v___x_1075_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply(lean_object* v_introThm_1084_, lean_object* v_opAs_1085_, lean_object* v_pre_1086_, lean_object* v_ss_1087_, lean_object* v_a_1088_, lean_object* v_a_1089_, lean_object* v_a_1090_, lean_object* v_a_1091_){
_start:
{
if (lean_obj_tag(v_ss_1087_) == 0)
{
lean_object* v___x_1093_; 
lean_inc(v_introThm_1084_);
v___x_1093_ = l_Lean_Meta_mkConstWithFreshMVarLevels(v_introThm_1084_, v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_);
if (lean_obj_tag(v___x_1093_) == 0)
{
lean_object* v_a_1094_; lean_object* v___x_1095_; 
v_a_1094_ = lean_ctor_get(v___x_1093_, 0);
lean_inc_n(v_a_1094_, 2);
lean_dec_ref_known(v___x_1093_, 1);
lean_inc(v_a_1091_);
lean_inc_ref(v_a_1090_);
lean_inc(v_a_1089_);
lean_inc_ref(v_a_1088_);
v___x_1095_ = lean_infer_type(v_a_1094_, v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_);
if (lean_obj_tag(v___x_1095_) == 0)
{
lean_object* v_a_1096_; uint8_t v___x_1097_; lean_object* v___x_1098_; 
v_a_1096_ = lean_ctor_get(v___x_1095_, 0);
lean_inc(v_a_1096_);
lean_dec_ref_known(v___x_1095_, 1);
v___x_1097_ = 0;
v___x_1098_ = l_Lean_Meta_forallMetaTelescope(v_a_1096_, v___x_1097_, v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_);
if (lean_obj_tag(v___x_1098_) == 0)
{
lean_object* v_a_1099_; lean_object* v___x_1101_; uint8_t v_isShared_1102_; uint8_t v_isSharedCheck_1158_; 
v_a_1099_ = lean_ctor_get(v___x_1098_, 0);
v_isSharedCheck_1158_ = !lean_is_exclusive(v___x_1098_);
if (v_isSharedCheck_1158_ == 0)
{
v___x_1101_ = v___x_1098_;
v_isShared_1102_ = v_isSharedCheck_1158_;
goto v_resetjp_1100_;
}
else
{
lean_inc(v_a_1099_);
lean_dec(v___x_1098_);
v___x_1101_ = lean_box(0);
v_isShared_1102_ = v_isSharedCheck_1158_;
goto v_resetjp_1100_;
}
v_resetjp_1100_:
{
lean_object* v_fst_1103_; lean_object* v_snd_1104_; lean_object* v___x_1106_; uint8_t v_isShared_1107_; uint8_t v_isSharedCheck_1157_; 
v_fst_1103_ = lean_ctor_get(v_a_1099_, 0);
v_snd_1104_ = lean_ctor_get(v_a_1099_, 1);
v_isSharedCheck_1157_ = !lean_is_exclusive(v_a_1099_);
if (v_isSharedCheck_1157_ == 0)
{
v___x_1106_ = v_a_1099_;
v_isShared_1107_ = v_isSharedCheck_1157_;
goto v_resetjp_1105_;
}
else
{
lean_inc(v_snd_1104_);
lean_inc(v_fst_1103_);
lean_dec(v_a_1099_);
v___x_1106_ = lean_box(0);
v_isShared_1107_ = v_isSharedCheck_1157_;
goto v_resetjp_1105_;
}
v_resetjp_1105_:
{
lean_object* v_snd_1113_; lean_object* v___x_1115_; uint8_t v_isShared_1116_; uint8_t v_isSharedCheck_1155_; 
v_snd_1113_ = lean_ctor_get(v_snd_1104_, 1);
v_isSharedCheck_1155_ = !lean_is_exclusive(v_snd_1104_);
if (v_isSharedCheck_1155_ == 0)
{
lean_object* v_unused_1156_; 
v_unused_1156_ = lean_ctor_get(v_snd_1104_, 0);
lean_dec(v_unused_1156_);
v___x_1115_ = v_snd_1104_;
v_isShared_1116_ = v_isSharedCheck_1155_;
goto v_resetjp_1114_;
}
else
{
lean_inc(v_snd_1113_);
lean_dec(v_snd_1104_);
v___x_1115_ = lean_box(0);
v_isShared_1116_ = v_isSharedCheck_1155_;
goto v_resetjp_1114_;
}
v___jp_1108_:
{
lean_object* v___x_1109_; lean_object* v___x_1111_; 
v___x_1109_ = l_Lean_mkAppN(v_a_1094_, v_fst_1103_);
lean_dec(v_fst_1103_);
if (v_isShared_1102_ == 0)
{
lean_ctor_set(v___x_1101_, 0, v___x_1109_);
v___x_1111_ = v___x_1101_;
goto v_reusejp_1110_;
}
else
{
lean_object* v_reuseFailAlloc_1112_; 
v_reuseFailAlloc_1112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1112_, 0, v___x_1109_);
v___x_1111_ = v_reuseFailAlloc_1112_;
goto v_reusejp_1110_;
}
v_reusejp_1110_:
{
return v___x_1111_;
}
}
v_resetjp_1114_:
{
lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; 
v___x_1117_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__2___closed__2));
v___x_1118_ = lean_unsigned_to_nat(2u);
v___x_1119_ = lean_mk_empty_array_with_capacity(v___x_1118_);
v___x_1120_ = lean_array_push(v___x_1119_, v_pre_1086_);
v___x_1121_ = lean_array_push(v___x_1120_, v_opAs_1085_);
v___x_1122_ = l_Lean_Meta_mkAppM(v___x_1117_, v___x_1121_, v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_);
if (lean_obj_tag(v___x_1122_) == 0)
{
lean_object* v_a_1123_; lean_object* v___x_1124_; 
v_a_1123_ = lean_ctor_get(v___x_1122_, 0);
lean_inc_n(v_a_1123_, 2);
lean_dec_ref_known(v___x_1122_, 1);
v___x_1124_ = l_Lean_Meta_isExprDefEq(v_snd_1113_, v_a_1123_, v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_);
if (lean_obj_tag(v___x_1124_) == 0)
{
lean_object* v_a_1125_; uint8_t v___x_1126_; 
v_a_1125_ = lean_ctor_get(v___x_1124_, 0);
lean_inc(v_a_1125_);
lean_dec_ref_known(v___x_1124_, 1);
v___x_1126_ = lean_unbox(v_a_1125_);
lean_dec(v_a_1125_);
if (v___x_1126_ == 0)
{
lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1130_; 
v___x_1127_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__2___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__2___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__2___closed__4);
v___x_1128_ = l_Lean_MessageData_ofName(v_introThm_1084_);
if (v_isShared_1116_ == 0)
{
lean_ctor_set_tag(v___x_1115_, 7);
lean_ctor_set(v___x_1115_, 1, v___x_1128_);
lean_ctor_set(v___x_1115_, 0, v___x_1127_);
v___x_1130_ = v___x_1115_;
goto v_reusejp_1129_;
}
else
{
lean_object* v_reuseFailAlloc_1146_; 
v_reuseFailAlloc_1146_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1146_, 0, v___x_1127_);
lean_ctor_set(v_reuseFailAlloc_1146_, 1, v___x_1128_);
v___x_1130_ = v_reuseFailAlloc_1146_;
goto v_reusejp_1129_;
}
v_reusejp_1129_:
{
lean_object* v___x_1131_; lean_object* v___x_1133_; 
v___x_1131_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply___closed__1, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply___closed__1_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply___closed__1);
if (v_isShared_1107_ == 0)
{
lean_ctor_set_tag(v___x_1106_, 7);
lean_ctor_set(v___x_1106_, 1, v___x_1131_);
lean_ctor_set(v___x_1106_, 0, v___x_1130_);
v___x_1133_ = v___x_1106_;
goto v_reusejp_1132_;
}
else
{
lean_object* v_reuseFailAlloc_1145_; 
v_reuseFailAlloc_1145_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1145_, 0, v___x_1130_);
lean_ctor_set(v_reuseFailAlloc_1145_, 1, v___x_1131_);
v___x_1133_ = v_reuseFailAlloc_1145_;
goto v_reusejp_1132_;
}
v_reusejp_1132_:
{
lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; 
v___x_1134_ = l_Lean_MessageData_ofExpr(v_a_1123_);
v___x_1135_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1135_, 0, v___x_1133_);
lean_ctor_set(v___x_1135_, 1, v___x_1134_);
v___x_1136_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__1___redArg(v___x_1135_, v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_);
if (lean_obj_tag(v___x_1136_) == 0)
{
lean_dec_ref_known(v___x_1136_, 1);
goto v___jp_1108_;
}
else
{
lean_object* v_a_1137_; lean_object* v___x_1139_; uint8_t v_isShared_1140_; uint8_t v_isSharedCheck_1144_; 
lean_dec(v_fst_1103_);
lean_del_object(v___x_1101_);
lean_dec(v_a_1094_);
v_a_1137_ = lean_ctor_get(v___x_1136_, 0);
v_isSharedCheck_1144_ = !lean_is_exclusive(v___x_1136_);
if (v_isSharedCheck_1144_ == 0)
{
v___x_1139_ = v___x_1136_;
v_isShared_1140_ = v_isSharedCheck_1144_;
goto v_resetjp_1138_;
}
else
{
lean_inc(v_a_1137_);
lean_dec(v___x_1136_);
v___x_1139_ = lean_box(0);
v_isShared_1140_ = v_isSharedCheck_1144_;
goto v_resetjp_1138_;
}
v_resetjp_1138_:
{
lean_object* v___x_1142_; 
if (v_isShared_1140_ == 0)
{
v___x_1142_ = v___x_1139_;
goto v_reusejp_1141_;
}
else
{
lean_object* v_reuseFailAlloc_1143_; 
v_reuseFailAlloc_1143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1143_, 0, v_a_1137_);
v___x_1142_ = v_reuseFailAlloc_1143_;
goto v_reusejp_1141_;
}
v_reusejp_1141_:
{
return v___x_1142_;
}
}
}
}
}
}
else
{
lean_dec(v_a_1123_);
lean_del_object(v___x_1115_);
lean_del_object(v___x_1106_);
lean_dec(v_introThm_1084_);
goto v___jp_1108_;
}
}
else
{
lean_object* v_a_1147_; lean_object* v___x_1149_; uint8_t v_isShared_1150_; uint8_t v_isSharedCheck_1154_; 
lean_dec(v_a_1123_);
lean_del_object(v___x_1115_);
lean_del_object(v___x_1106_);
lean_dec(v_fst_1103_);
lean_del_object(v___x_1101_);
lean_dec(v_a_1094_);
lean_dec(v_introThm_1084_);
v_a_1147_ = lean_ctor_get(v___x_1124_, 0);
v_isSharedCheck_1154_ = !lean_is_exclusive(v___x_1124_);
if (v_isSharedCheck_1154_ == 0)
{
v___x_1149_ = v___x_1124_;
v_isShared_1150_ = v_isSharedCheck_1154_;
goto v_resetjp_1148_;
}
else
{
lean_inc(v_a_1147_);
lean_dec(v___x_1124_);
v___x_1149_ = lean_box(0);
v_isShared_1150_ = v_isSharedCheck_1154_;
goto v_resetjp_1148_;
}
v_resetjp_1148_:
{
lean_object* v___x_1152_; 
if (v_isShared_1150_ == 0)
{
v___x_1152_ = v___x_1149_;
goto v_reusejp_1151_;
}
else
{
lean_object* v_reuseFailAlloc_1153_; 
v_reuseFailAlloc_1153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1153_, 0, v_a_1147_);
v___x_1152_ = v_reuseFailAlloc_1153_;
goto v_reusejp_1151_;
}
v_reusejp_1151_:
{
return v___x_1152_;
}
}
}
}
else
{
lean_del_object(v___x_1115_);
lean_dec(v_snd_1113_);
lean_del_object(v___x_1106_);
lean_dec(v_fst_1103_);
lean_del_object(v___x_1101_);
lean_dec(v_a_1094_);
lean_dec(v_introThm_1084_);
return v___x_1122_;
}
}
}
}
}
else
{
lean_object* v_a_1159_; lean_object* v___x_1161_; uint8_t v_isShared_1162_; uint8_t v_isSharedCheck_1166_; 
lean_dec(v_a_1094_);
lean_dec_ref(v_pre_1086_);
lean_dec_ref(v_opAs_1085_);
lean_dec(v_introThm_1084_);
v_a_1159_ = lean_ctor_get(v___x_1098_, 0);
v_isSharedCheck_1166_ = !lean_is_exclusive(v___x_1098_);
if (v_isSharedCheck_1166_ == 0)
{
v___x_1161_ = v___x_1098_;
v_isShared_1162_ = v_isSharedCheck_1166_;
goto v_resetjp_1160_;
}
else
{
lean_inc(v_a_1159_);
lean_dec(v___x_1098_);
v___x_1161_ = lean_box(0);
v_isShared_1162_ = v_isSharedCheck_1166_;
goto v_resetjp_1160_;
}
v_resetjp_1160_:
{
lean_object* v___x_1164_; 
if (v_isShared_1162_ == 0)
{
v___x_1164_ = v___x_1161_;
goto v_reusejp_1163_;
}
else
{
lean_object* v_reuseFailAlloc_1165_; 
v_reuseFailAlloc_1165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1165_, 0, v_a_1159_);
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
else
{
lean_dec(v_a_1094_);
lean_dec_ref(v_pre_1086_);
lean_dec_ref(v_opAs_1085_);
lean_dec(v_introThm_1084_);
return v___x_1095_;
}
}
else
{
lean_dec_ref(v_pre_1086_);
lean_dec_ref(v_opAs_1085_);
lean_dec(v_introThm_1084_);
return v___x_1093_;
}
}
else
{
lean_object* v___x_1167_; 
lean_inc(v_a_1091_);
lean_inc_ref(v_a_1090_);
lean_inc(v_a_1089_);
lean_inc_ref(v_a_1088_);
lean_inc_ref(v_pre_1086_);
v___x_1167_ = lean_infer_type(v_pre_1086_, v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_);
if (lean_obj_tag(v___x_1167_) == 0)
{
lean_object* v_a_1168_; lean_object* v___x_1169_; lean_object* v_s_1170_; lean_object* v___x_1171_; 
v_a_1168_ = lean_ctor_get(v___x_1167_, 0);
lean_inc(v_a_1168_);
lean_dec_ref_known(v___x_1167_, 1);
v___x_1169_ = l_Lean_instInhabitedExpr;
v_s_1170_ = l_List_getLast_x21___redArg(v___x_1169_, v_ss_1087_);
lean_inc(v_a_1091_);
lean_inc_ref(v_a_1090_);
lean_inc(v_a_1089_);
lean_inc_ref(v_a_1088_);
lean_inc(v_s_1170_);
v___x_1171_ = lean_infer_type(v_s_1170_, v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_);
if (lean_obj_tag(v___x_1171_) == 0)
{
lean_object* v_a_1172_; lean_object* v___f_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; 
v_a_1172_ = lean_ctor_get(v___x_1171_, 0);
lean_inc(v_a_1172_);
lean_dec_ref_known(v___x_1171_, 1);
lean_inc_ref(v_pre_1086_);
lean_inc(v_s_1170_);
v___f_1173_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply___lam__0___boxed), 9, 3);
lean_closure_set(v___f_1173_, 0, v_s_1170_);
lean_closure_set(v___f_1173_, 1, v_a_1168_);
lean_closure_set(v___f_1173_, 2, v_pre_1086_);
v___x_1174_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply___closed__3));
v___x_1175_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply_spec__0___redArg(v___x_1174_, v_a_1172_, v___f_1173_, v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_);
if (lean_obj_tag(v___x_1175_) == 0)
{
lean_object* v_a_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v_init_1179_; lean_object* v___x_1180_; lean_object* v_Q_1181_; lean_object* v___x_1182_; 
v_a_1176_ = lean_ctor_get(v___x_1175_, 0);
lean_inc(v_a_1176_);
lean_dec_ref_known(v___x_1175_, 1);
v___x_1177_ = lean_array_mk(v_ss_1087_);
v___x_1178_ = lean_array_pop(v___x_1177_);
v_init_1179_ = lean_array_to_list(v___x_1178_);
lean_inc(v_init_1179_);
v___x_1180_ = lean_array_mk(v_init_1179_);
lean_inc_ref(v_opAs_1085_);
v_Q_1181_ = l_Lean_mkAppN(v_opAs_1085_, v___x_1180_);
lean_dec_ref(v___x_1180_);
v___x_1182_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply(v_introThm_1084_, v_opAs_1085_, v_a_1176_, v_init_1179_, v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_);
if (lean_obj_tag(v___x_1182_) == 0)
{
lean_object* v_a_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; 
v_a_1183_ = lean_ctor_get(v___x_1182_, 0);
lean_inc(v_a_1183_);
lean_dec_ref_known(v___x_1182_, 1);
v___x_1184_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply___closed__5));
v___x_1185_ = lean_unsigned_to_nat(4u);
v___x_1186_ = lean_mk_empty_array_with_capacity(v___x_1185_);
v___x_1187_ = lean_array_push(v___x_1186_, v_s_1170_);
v___x_1188_ = lean_array_push(v___x_1187_, v_pre_1086_);
v___x_1189_ = lean_array_push(v___x_1188_, v_Q_1181_);
v___x_1190_ = lean_array_push(v___x_1189_, v_a_1183_);
v___x_1191_ = l_Lean_Meta_mkAppM(v___x_1184_, v___x_1190_, v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_);
return v___x_1191_;
}
else
{
lean_dec_ref(v_Q_1181_);
lean_dec(v_s_1170_);
lean_dec_ref(v_pre_1086_);
return v___x_1182_;
}
}
else
{
lean_dec(v_s_1170_);
lean_dec(v_ss_1087_);
lean_dec_ref(v_pre_1086_);
lean_dec_ref(v_opAs_1085_);
lean_dec(v_introThm_1084_);
return v___x_1175_;
}
}
else
{
lean_dec(v_s_1170_);
lean_dec(v_a_1168_);
lean_dec(v_ss_1087_);
lean_dec_ref(v_pre_1086_);
lean_dec_ref(v_opAs_1085_);
lean_dec(v_introThm_1084_);
return v___x_1171_;
}
}
else
{
lean_dec(v_ss_1087_);
lean_dec_ref(v_pre_1086_);
lean_dec_ref(v_opAs_1085_);
lean_dec(v_introThm_1084_);
return v___x_1167_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply___boxed(lean_object* v_introThm_1192_, lean_object* v_opAs_1193_, lean_object* v_pre_1194_, lean_object* v_ss_1195_, lean_object* v_a_1196_, lean_object* v_a_1197_, lean_object* v_a_1198_, lean_object* v_a_1199_, lean_object* v_a_1200_){
_start:
{
lean_object* v_res_1201_; 
v_res_1201_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply(v_introThm_1192_, v_opAs_1193_, v_pre_1194_, v_ss_1195_, v_a_1196_, v_a_1197_, v_a_1198_, v_a_1199_);
lean_dec(v_a_1199_);
lean_dec_ref(v_a_1198_);
lean_dec(v_a_1197_);
lean_dec_ref(v_a_1196_);
return v_res_1201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply_spec__0_spec__0(lean_object* v_00_u03b1_1202_, lean_object* v_name_1203_, uint8_t v_bi_1204_, lean_object* v_type_1205_, lean_object* v_k_1206_, uint8_t v_kind_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_){
_start:
{
lean_object* v___x_1213_; 
v___x_1213_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply_spec__0_spec__0___redArg(v_name_1203_, v_bi_1204_, v_type_1205_, v_k_1206_, v_kind_1207_, v___y_1208_, v___y_1209_, v___y_1210_, v___y_1211_);
return v___x_1213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1214_, lean_object* v_name_1215_, lean_object* v_bi_1216_, lean_object* v_type_1217_, lean_object* v_k_1218_, lean_object* v_kind_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_){
_start:
{
uint8_t v_bi_boxed_1225_; uint8_t v_kind_boxed_1226_; lean_object* v_res_1227_; 
v_bi_boxed_1225_ = lean_unbox(v_bi_1216_);
v_kind_boxed_1226_ = lean_unbox(v_kind_1219_);
v_res_1227_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply_spec__0_spec__0(v_00_u03b1_1214_, v_name_1215_, v_bi_boxed_1225_, v_type_1217_, v_k_1218_, v_kind_boxed_1226_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_);
lean_dec(v___y_1223_);
lean_dec_ref(v___y_1222_);
lean_dec(v___y_1221_);
lean_dec_ref(v___y_1220_);
return v_res_1227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply_spec__0(lean_object* v_00_u03b1_1228_, lean_object* v_name_1229_, lean_object* v_type_1230_, lean_object* v_k_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_){
_start:
{
lean_object* v___x_1237_; 
v___x_1237_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply_spec__0___redArg(v_name_1229_, v_type_1230_, v_k_1231_, v___y_1232_, v___y_1233_, v___y_1234_, v___y_1235_);
return v___x_1237_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply_spec__0___boxed(lean_object* v_00_u03b1_1238_, lean_object* v_name_1239_, lean_object* v_type_1240_, lean_object* v_k_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_){
_start:
{
lean_object* v_res_1247_; 
v_res_1247_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply_spec__0(v_00_u03b1_1238_, v_name_1239_, v_type_1240_, v_k_1241_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_);
lean_dec(v___y_1245_);
lean_dec_ref(v___y_1244_);
lean_dec(v___y_1243_);
lean_dec_ref(v___y_1242_);
return v_res_1247_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__1_spec__1___redArg(lean_object* v_a_1248_, lean_object* v_x_1249_){
_start:
{
if (lean_obj_tag(v_x_1249_) == 0)
{
lean_object* v___x_1250_; 
v___x_1250_ = lean_box(0);
return v___x_1250_;
}
else
{
lean_object* v_key_1251_; lean_object* v_value_1252_; lean_object* v_tail_1253_; uint8_t v___x_1254_; 
v_key_1251_ = lean_ctor_get(v_x_1249_, 0);
v_value_1252_ = lean_ctor_get(v_x_1249_, 1);
v_tail_1253_ = lean_ctor_get(v_x_1249_, 2);
v___x_1254_ = lean_name_eq(v_key_1251_, v_a_1248_);
if (v___x_1254_ == 0)
{
v_x_1249_ = v_tail_1253_;
goto _start;
}
else
{
lean_object* v___x_1256_; 
lean_inc(v_value_1252_);
v___x_1256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1256_, 0, v_value_1252_);
return v___x_1256_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__1_spec__1___redArg___boxed(lean_object* v_a_1257_, lean_object* v_x_1258_){
_start:
{
lean_object* v_res_1259_; 
v_res_1259_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__1_spec__1___redArg(v_a_1257_, v_x_1258_);
lean_dec(v_x_1258_);
lean_dec(v_a_1257_);
return v_res_1259_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__1___redArg(lean_object* v_m_1260_, lean_object* v_a_1261_){
_start:
{
lean_object* v_buckets_1262_; lean_object* v___x_1263_; uint64_t v___y_1265_; 
v_buckets_1262_ = lean_ctor_get(v_m_1260_, 1);
v___x_1263_ = lean_array_get_size(v_buckets_1262_);
if (lean_obj_tag(v_a_1261_) == 0)
{
uint64_t v___x_1279_; 
v___x_1279_ = lean_uint64_once(&l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable_spec__0_spec__1_spec__2_spec__4___redArg___closed__0, &l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable_spec__0_spec__1_spec__2_spec__4___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable_spec__0_spec__1_spec__2_spec__4___redArg___closed__0);
v___y_1265_ = v___x_1279_;
goto v___jp_1264_;
}
else
{
uint64_t v_hash_1280_; 
v_hash_1280_ = lean_ctor_get_uint64(v_a_1261_, sizeof(void*)*2);
v___y_1265_ = v_hash_1280_;
goto v___jp_1264_;
}
v___jp_1264_:
{
uint64_t v___x_1266_; uint64_t v___x_1267_; uint64_t v_fold_1268_; uint64_t v___x_1269_; uint64_t v___x_1270_; uint64_t v___x_1271_; size_t v___x_1272_; size_t v___x_1273_; size_t v___x_1274_; size_t v___x_1275_; size_t v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; 
v___x_1266_ = 32ULL;
v___x_1267_ = lean_uint64_shift_right(v___y_1265_, v___x_1266_);
v_fold_1268_ = lean_uint64_xor(v___y_1265_, v___x_1267_);
v___x_1269_ = 16ULL;
v___x_1270_ = lean_uint64_shift_right(v_fold_1268_, v___x_1269_);
v___x_1271_ = lean_uint64_xor(v_fold_1268_, v___x_1270_);
v___x_1272_ = lean_uint64_to_usize(v___x_1271_);
v___x_1273_ = lean_usize_of_nat(v___x_1263_);
v___x_1274_ = ((size_t)1ULL);
v___x_1275_ = lean_usize_sub(v___x_1273_, v___x_1274_);
v___x_1276_ = lean_usize_land(v___x_1272_, v___x_1275_);
v___x_1277_ = lean_array_uget_borrowed(v_buckets_1262_, v___x_1276_);
v___x_1278_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__1_spec__1___redArg(v_a_1261_, v___x_1277_);
return v___x_1278_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__1___redArg___boxed(lean_object* v_m_1281_, lean_object* v_a_1282_){
_start:
{
lean_object* v_res_1283_; 
v_res_1283_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__1___redArg(v_m_1281_, v_a_1282_);
lean_dec(v_a_1282_);
lean_dec_ref(v_m_1281_);
return v_res_1283_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__0(size_t v_sz_1284_, size_t v_i_1285_, lean_object* v_bs_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_){
_start:
{
uint8_t v___x_1292_; 
v___x_1292_ = lean_usize_dec_lt(v_i_1285_, v_sz_1284_);
if (v___x_1292_ == 0)
{
lean_object* v___x_1293_; 
v___x_1293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1293_, 0, v_bs_1286_);
return v___x_1293_;
}
else
{
lean_object* v_v_1294_; lean_object* v___x_1295_; lean_object* v_bs_x27_1296_; lean_object* v___y_1298_; lean_object* v___x_1312_; 
v_v_1294_ = lean_array_uget(v_bs_1286_, v_i_1285_);
v___x_1295_ = lean_unsigned_to_nat(0u);
v_bs_x27_1296_ = lean_array_uset(v_bs_1286_, v_i_1285_, v___x_1295_);
lean_inc(v___y_1290_);
lean_inc_ref(v___y_1289_);
lean_inc(v___y_1288_);
lean_inc_ref(v___y_1287_);
v___x_1312_ = lean_infer_type(v_v_1294_, v___y_1287_, v___y_1288_, v___y_1289_, v___y_1290_);
if (lean_obj_tag(v___x_1312_) == 0)
{
lean_object* v_a_1313_; lean_object* v___x_1315_; uint8_t v_isShared_1316_; uint8_t v_isSharedCheck_1323_; 
v_a_1313_ = lean_ctor_get(v___x_1312_, 0);
v_isSharedCheck_1323_ = !lean_is_exclusive(v___x_1312_);
if (v_isSharedCheck_1323_ == 0)
{
v___x_1315_ = v___x_1312_;
v_isShared_1316_ = v_isSharedCheck_1323_;
goto v_resetjp_1314_;
}
else
{
lean_inc(v_a_1313_);
lean_dec(v___x_1312_);
v___x_1315_ = lean_box(0);
v_isShared_1316_ = v_isSharedCheck_1323_;
goto v_resetjp_1314_;
}
v_resetjp_1314_:
{
lean_object* v___x_1318_; 
if (v_isShared_1316_ == 0)
{
lean_ctor_set_tag(v___x_1315_, 1);
v___x_1318_ = v___x_1315_;
goto v_reusejp_1317_;
}
else
{
lean_object* v_reuseFailAlloc_1322_; 
v_reuseFailAlloc_1322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1322_, 0, v_a_1313_);
v___x_1318_ = v_reuseFailAlloc_1322_;
goto v_reusejp_1317_;
}
v_reusejp_1317_:
{
uint8_t v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; 
v___x_1319_ = 0;
v___x_1320_ = lean_box(0);
v___x_1321_ = l_Lean_Meta_mkFreshExprMVar(v___x_1318_, v___x_1319_, v___x_1320_, v___y_1287_, v___y_1288_, v___y_1289_, v___y_1290_);
v___y_1298_ = v___x_1321_;
goto v___jp_1297_;
}
}
}
else
{
v___y_1298_ = v___x_1312_;
goto v___jp_1297_;
}
v___jp_1297_:
{
if (lean_obj_tag(v___y_1298_) == 0)
{
lean_object* v_a_1299_; size_t v___x_1300_; size_t v___x_1301_; lean_object* v___x_1302_; 
v_a_1299_ = lean_ctor_get(v___y_1298_, 0);
lean_inc(v_a_1299_);
lean_dec_ref_known(v___y_1298_, 1);
v___x_1300_ = ((size_t)1ULL);
v___x_1301_ = lean_usize_add(v_i_1285_, v___x_1300_);
v___x_1302_ = lean_array_uset(v_bs_x27_1296_, v_i_1285_, v_a_1299_);
v_i_1285_ = v___x_1301_;
v_bs_1286_ = v___x_1302_;
goto _start;
}
else
{
lean_object* v_a_1304_; lean_object* v___x_1306_; uint8_t v_isShared_1307_; uint8_t v_isSharedCheck_1311_; 
lean_dec_ref(v_bs_x27_1296_);
v_a_1304_ = lean_ctor_get(v___y_1298_, 0);
v_isSharedCheck_1311_ = !lean_is_exclusive(v___y_1298_);
if (v_isSharedCheck_1311_ == 0)
{
v___x_1306_ = v___y_1298_;
v_isShared_1307_ = v_isSharedCheck_1311_;
goto v_resetjp_1305_;
}
else
{
lean_inc(v_a_1304_);
lean_dec(v___y_1298_);
v___x_1306_ = lean_box(0);
v_isShared_1307_ = v_isSharedCheck_1311_;
goto v_resetjp_1305_;
}
v_resetjp_1305_:
{
lean_object* v___x_1309_; 
if (v_isShared_1307_ == 0)
{
v___x_1309_ = v___x_1306_;
goto v_reusejp_1308_;
}
else
{
lean_object* v_reuseFailAlloc_1310_; 
v_reuseFailAlloc_1310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1310_, 0, v_a_1304_);
v___x_1309_ = v_reuseFailAlloc_1310_;
goto v_reusejp_1308_;
}
v_reusejp_1308_:
{
return v___x_1309_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__0___boxed(lean_object* v_sz_1324_, lean_object* v_i_1325_, lean_object* v_bs_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_){
_start:
{
size_t v_sz_boxed_1332_; size_t v_i_boxed_1333_; lean_object* v_res_1334_; 
v_sz_boxed_1332_ = lean_unbox_usize(v_sz_1324_);
lean_dec(v_sz_1324_);
v_i_boxed_1333_ = lean_unbox_usize(v_i_1325_);
lean_dec(v_i_1325_);
v_res_1334_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__0(v_sz_boxed_1332_, v_i_boxed_1333_, v_bs_1326_, v___y_1327_, v___y_1328_, v___y_1329_, v___y_1330_);
lean_dec(v___y_1330_);
lean_dec_ref(v___y_1329_);
lean_dec(v___y_1328_);
lean_dec_ref(v___y_1327_);
return v_res_1334_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__2___closed__3(void){
_start:
{
lean_object* v___x_1340_; lean_object* v___x_1341_; 
v___x_1340_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__2___closed__2));
v___x_1341_ = l_Lean_stringToMessageData(v___x_1340_);
return v___x_1341_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__2___closed__5(void){
_start:
{
lean_object* v___x_1343_; lean_object* v___x_1344_; 
v___x_1343_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__2___closed__4));
v___x_1344_ = l_Lean_stringToMessageData(v___x_1343_);
return v___x_1344_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__2(lean_object* v_op_1345_, lean_object* v___y_1346_, lean_object* v_a_1347_, lean_object* v_x_1348_, lean_object* v_x_1349_, lean_object* v_x_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_){
_start:
{
lean_object* v_prf_1357_; lean_object* v___y_1358_; lean_object* v___y_1359_; lean_object* v___y_1360_; lean_object* v___y_1361_; 
if (lean_obj_tag(v_x_1348_) == 5)
{
lean_object* v_fn_1378_; lean_object* v_arg_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; 
v_fn_1378_ = lean_ctor_get(v_x_1348_, 0);
lean_inc_ref(v_fn_1378_);
v_arg_1379_ = lean_ctor_get(v_x_1348_, 1);
lean_inc_ref(v_arg_1379_);
lean_dec_ref_known(v_x_1348_, 2);
v___x_1380_ = lean_array_set(v_x_1349_, v_x_1350_, v_arg_1379_);
v___x_1381_ = lean_unsigned_to_nat(1u);
v___x_1382_ = lean_nat_sub(v_x_1350_, v___x_1381_);
lean_dec(v_x_1350_);
v_x_1348_ = v_fn_1378_;
v_x_1349_ = v___x_1380_;
v_x_1350_ = v___x_1382_;
goto _start;
}
else
{
lean_object* v_head_1384_; lean_object* v_numConst_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; size_t v_sz_1388_; size_t v___x_1389_; lean_object* v___x_1390_; 
lean_dec(v_x_1350_);
v_head_1384_ = lean_ctor_get(v_op_1345_, 0);
lean_inc(v_head_1384_);
v_numConst_1385_ = lean_ctor_get(v_op_1345_, 1);
lean_inc_n(v_numConst_1385_, 2);
lean_dec_ref(v_op_1345_);
v___x_1386_ = lean_array_get_size(v_x_1349_);
v___x_1387_ = l_Array_extract___redArg(v_x_1349_, v_numConst_1385_, v___x_1386_);
v_sz_1388_ = lean_array_size(v___x_1387_);
v___x_1389_ = ((size_t)0ULL);
v___x_1390_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__0(v_sz_1388_, v___x_1389_, v___x_1387_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_);
if (lean_obj_tag(v___x_1390_) == 0)
{
lean_object* v_a_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; 
v_a_1391_ = lean_ctor_get(v___x_1390_, 0);
lean_inc(v_a_1391_);
lean_dec_ref_known(v___x_1390_, 1);
v___x_1392_ = lean_unsigned_to_nat(0u);
v___x_1393_ = l_Array_extract___redArg(v_x_1349_, v___x_1392_, v_numConst_1385_);
lean_dec_ref(v_x_1349_);
v___x_1394_ = l_Array_append___redArg(v___x_1393_, v_a_1391_);
lean_dec(v_a_1391_);
v___x_1395_ = l_Lean_mkAppN(v_x_1348_, v___x_1394_);
lean_dec_ref(v___x_1394_);
v___x_1396_ = lean_unsigned_to_nat(256u);
lean_inc_ref(v___x_1395_);
v___x_1397_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp(v___y_1346_, v___x_1395_, v___x_1396_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_);
if (lean_obj_tag(v___x_1397_) == 0)
{
lean_object* v_a_1398_; lean_object* v_fst_1399_; lean_object* v_snd_1400_; lean_object* v___x_1402_; uint8_t v_isShared_1403_; uint8_t v_isSharedCheck_1572_; 
v_a_1398_ = lean_ctor_get(v___x_1397_, 0);
lean_inc(v_a_1398_);
lean_dec_ref_known(v___x_1397_, 1);
v_fst_1399_ = lean_ctor_get(v_a_1398_, 0);
v_snd_1400_ = lean_ctor_get(v_a_1398_, 1);
v_isSharedCheck_1572_ = !lean_is_exclusive(v_a_1398_);
if (v_isSharedCheck_1572_ == 0)
{
v___x_1402_ = v_a_1398_;
v_isShared_1403_ = v_isSharedCheck_1572_;
goto v_resetjp_1401_;
}
else
{
lean_inc(v_snd_1400_);
lean_inc(v_fst_1399_);
lean_dec(v_a_1398_);
v___x_1402_ = lean_box(0);
v_isShared_1403_ = v_isSharedCheck_1572_;
goto v_resetjp_1401_;
}
v_resetjp_1401_:
{
lean_object* v___x_1404_; 
lean_inc(v___y_1354_);
lean_inc_ref(v___y_1353_);
lean_inc(v___y_1352_);
lean_inc_ref(v___y_1351_);
v___x_1404_ = lean_infer_type(v___x_1395_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_);
if (lean_obj_tag(v___x_1404_) == 0)
{
lean_object* v_a_1405_; lean_object* v___x_1406_; uint8_t v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; 
v_a_1405_ = lean_ctor_get(v___x_1404_, 0);
lean_inc(v_a_1405_);
lean_dec_ref_known(v___x_1404_, 1);
v___x_1406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1406_, 0, v_a_1405_);
v___x_1407_ = 0;
v___x_1408_ = lean_box(0);
v___x_1409_ = l_Lean_Meta_mkFreshExprMVar(v___x_1406_, v___x_1407_, v___x_1408_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_);
if (lean_obj_tag(v___x_1409_) == 0)
{
lean_object* v_a_1410_; lean_object* v___y_1412_; lean_object* v___y_1413_; lean_object* v___y_1414_; lean_object* v___y_1415_; lean_object* v___y_1416_; lean_object* v___y_1417_; lean_object* v_a_1418_; lean_object* v___y_1466_; lean_object* v_eqProof_1467_; lean_object* v___y_1468_; lean_object* v___y_1469_; lean_object* v___y_1470_; lean_object* v___y_1471_; lean_object* v___x_1499_; lean_object* v___y_1501_; lean_object* v___x_1554_; 
v_a_1410_ = lean_ctor_get(v___x_1409_, 0);
lean_inc(v_a_1410_);
lean_dec_ref_known(v___x_1409_, 1);
v___x_1499_ = l_Lean_Expr_getAppFn(v_fst_1399_);
v___x_1554_ = l_Lean_Expr_constName_x3f(v___x_1499_);
if (lean_obj_tag(v___x_1554_) == 0)
{
v___y_1501_ = v___x_1408_;
goto v___jp_1500_;
}
else
{
lean_object* v_val_1555_; 
v_val_1555_ = lean_ctor_get(v___x_1554_, 0);
lean_inc(v_val_1555_);
lean_dec_ref_known(v___x_1554_, 1);
v___y_1501_ = v_val_1555_;
goto v___jp_1500_;
}
v___jp_1411_:
{
lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; 
v___x_1419_ = lean_unsigned_to_nat(1u);
v___x_1420_ = lean_mk_empty_array_with_capacity(v___x_1419_);
lean_inc_ref(v___x_1420_);
v___x_1421_ = lean_array_push(v___x_1420_, v_a_1410_);
v___x_1422_ = l_Lean_Meta_mkAppM(v___y_1415_, v___x_1421_, v___y_1414_, v___y_1412_, v___y_1413_, v___y_1417_);
if (lean_obj_tag(v___x_1422_) == 0)
{
lean_object* v_a_1423_; lean_object* v___x_1424_; 
v_a_1423_ = lean_ctor_get(v___x_1422_, 0);
lean_inc(v_a_1423_);
lean_dec_ref_known(v___x_1422_, 1);
v___x_1424_ = l_Lean_Meta_mkCongrArg(v_a_1423_, v___y_1416_, v___y_1414_, v___y_1412_, v___y_1413_, v___y_1417_);
if (lean_obj_tag(v___x_1424_) == 0)
{
lean_object* v_a_1425_; lean_object* v___x_1426_; 
v_a_1425_ = lean_ctor_get(v___x_1424_, 0);
lean_inc(v_a_1425_);
lean_dec_ref_known(v___x_1424_, 1);
v___x_1426_ = l_Lean_Meta_mkEqSymm(v_a_1425_, v___y_1414_, v___y_1412_, v___y_1413_, v___y_1417_);
if (lean_obj_tag(v___x_1426_) == 0)
{
lean_object* v_a_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; 
v_a_1427_ = lean_ctor_get(v___x_1426_, 0);
lean_inc(v_a_1427_);
lean_dec_ref_known(v___x_1426_, 1);
v___x_1428_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__2___closed__1));
v___x_1429_ = lean_array_push(v___x_1420_, v_a_1427_);
v___x_1430_ = l_Lean_Meta_mkAppM(v___x_1428_, v___x_1429_, v___y_1414_, v___y_1412_, v___y_1413_, v___y_1417_);
if (lean_obj_tag(v___x_1430_) == 0)
{
lean_object* v_a_1431_; lean_object* v___x_1432_; 
v_a_1431_ = lean_ctor_get(v___x_1430_, 0);
lean_inc(v_a_1431_);
lean_dec_ref_known(v___x_1430_, 1);
v___x_1432_ = l_Lean_Expr_app___override(v_a_1431_, v_a_1418_);
v_prf_1357_ = v___x_1432_;
v___y_1358_ = v___y_1414_;
v___y_1359_ = v___y_1412_;
v___y_1360_ = v___y_1413_;
v___y_1361_ = v___y_1417_;
goto v___jp_1356_;
}
else
{
lean_object* v_a_1433_; lean_object* v___x_1435_; uint8_t v_isShared_1436_; uint8_t v_isSharedCheck_1440_; 
lean_dec_ref(v_a_1418_);
v_a_1433_ = lean_ctor_get(v___x_1430_, 0);
v_isSharedCheck_1440_ = !lean_is_exclusive(v___x_1430_);
if (v_isSharedCheck_1440_ == 0)
{
v___x_1435_ = v___x_1430_;
v_isShared_1436_ = v_isSharedCheck_1440_;
goto v_resetjp_1434_;
}
else
{
lean_inc(v_a_1433_);
lean_dec(v___x_1430_);
v___x_1435_ = lean_box(0);
v_isShared_1436_ = v_isSharedCheck_1440_;
goto v_resetjp_1434_;
}
v_resetjp_1434_:
{
lean_object* v___x_1438_; 
if (v_isShared_1436_ == 0)
{
v___x_1438_ = v___x_1435_;
goto v_reusejp_1437_;
}
else
{
lean_object* v_reuseFailAlloc_1439_; 
v_reuseFailAlloc_1439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1439_, 0, v_a_1433_);
v___x_1438_ = v_reuseFailAlloc_1439_;
goto v_reusejp_1437_;
}
v_reusejp_1437_:
{
return v___x_1438_;
}
}
}
}
else
{
lean_object* v_a_1441_; lean_object* v___x_1443_; uint8_t v_isShared_1444_; uint8_t v_isSharedCheck_1448_; 
lean_dec_ref(v___x_1420_);
lean_dec_ref(v_a_1418_);
v_a_1441_ = lean_ctor_get(v___x_1426_, 0);
v_isSharedCheck_1448_ = !lean_is_exclusive(v___x_1426_);
if (v_isSharedCheck_1448_ == 0)
{
v___x_1443_ = v___x_1426_;
v_isShared_1444_ = v_isSharedCheck_1448_;
goto v_resetjp_1442_;
}
else
{
lean_inc(v_a_1441_);
lean_dec(v___x_1426_);
v___x_1443_ = lean_box(0);
v_isShared_1444_ = v_isSharedCheck_1448_;
goto v_resetjp_1442_;
}
v_resetjp_1442_:
{
lean_object* v___x_1446_; 
if (v_isShared_1444_ == 0)
{
v___x_1446_ = v___x_1443_;
goto v_reusejp_1445_;
}
else
{
lean_object* v_reuseFailAlloc_1447_; 
v_reuseFailAlloc_1447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1447_, 0, v_a_1441_);
v___x_1446_ = v_reuseFailAlloc_1447_;
goto v_reusejp_1445_;
}
v_reusejp_1445_:
{
return v___x_1446_;
}
}
}
}
else
{
lean_object* v_a_1449_; lean_object* v___x_1451_; uint8_t v_isShared_1452_; uint8_t v_isSharedCheck_1456_; 
lean_dec_ref(v___x_1420_);
lean_dec_ref(v_a_1418_);
v_a_1449_ = lean_ctor_get(v___x_1424_, 0);
v_isSharedCheck_1456_ = !lean_is_exclusive(v___x_1424_);
if (v_isSharedCheck_1456_ == 0)
{
v___x_1451_ = v___x_1424_;
v_isShared_1452_ = v_isSharedCheck_1456_;
goto v_resetjp_1450_;
}
else
{
lean_inc(v_a_1449_);
lean_dec(v___x_1424_);
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
lean_object* v_a_1457_; lean_object* v___x_1459_; uint8_t v_isShared_1460_; uint8_t v_isSharedCheck_1464_; 
lean_dec_ref(v___x_1420_);
lean_dec_ref(v_a_1418_);
lean_dec_ref(v___y_1416_);
v_a_1457_ = lean_ctor_get(v___x_1422_, 0);
v_isSharedCheck_1464_ = !lean_is_exclusive(v___x_1422_);
if (v_isSharedCheck_1464_ == 0)
{
v___x_1459_ = v___x_1422_;
v_isShared_1460_ = v_isSharedCheck_1464_;
goto v_resetjp_1458_;
}
else
{
lean_inc(v_a_1457_);
lean_dec(v___x_1422_);
v___x_1459_ = lean_box(0);
v_isShared_1460_ = v_isSharedCheck_1464_;
goto v_resetjp_1458_;
}
v_resetjp_1458_:
{
lean_object* v___x_1462_; 
if (v_isShared_1460_ == 0)
{
v___x_1462_ = v___x_1459_;
goto v_reusejp_1461_;
}
else
{
lean_object* v_reuseFailAlloc_1463_; 
v_reuseFailAlloc_1463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1463_, 0, v_a_1457_);
v___x_1462_ = v_reuseFailAlloc_1463_;
goto v_reusejp_1461_;
}
v_reusejp_1461_:
{
return v___x_1462_;
}
}
}
}
v___jp_1465_:
{
lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; 
v___x_1472_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__2___closed__2));
v___x_1473_ = lean_unsigned_to_nat(2u);
v___x_1474_ = lean_mk_empty_array_with_capacity(v___x_1473_);
lean_inc(v_a_1410_);
v___x_1475_ = lean_array_push(v___x_1474_, v_a_1410_);
v___x_1476_ = lean_array_push(v___x_1475_, v_fst_1399_);
v___x_1477_ = l_Lean_Meta_mkAppM(v___x_1472_, v___x_1476_, v___y_1468_, v___y_1469_, v___y_1470_, v___y_1471_);
if (lean_obj_tag(v___x_1477_) == 0)
{
if (lean_obj_tag(v___y_1466_) == 0)
{
lean_object* v_a_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; 
v_a_1478_ = lean_ctor_get(v___x_1477_, 0);
lean_inc(v_a_1478_);
lean_dec_ref_known(v___x_1477_, 1);
v___x_1479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1479_, 0, v_a_1478_);
v___x_1480_ = l_Lean_Meta_mkFreshExprMVar(v___x_1479_, v___x_1407_, v___x_1408_, v___y_1468_, v___y_1469_, v___y_1470_, v___y_1471_);
if (lean_obj_tag(v___x_1480_) == 0)
{
lean_object* v_a_1481_; 
v_a_1481_ = lean_ctor_get(v___x_1480_, 0);
lean_inc(v_a_1481_);
lean_dec_ref_known(v___x_1480_, 1);
v___y_1412_ = v___y_1469_;
v___y_1413_ = v___y_1470_;
v___y_1414_ = v___y_1468_;
v___y_1415_ = v___x_1472_;
v___y_1416_ = v_eqProof_1467_;
v___y_1417_ = v___y_1471_;
v_a_1418_ = v_a_1481_;
goto v___jp_1411_;
}
else
{
lean_object* v_a_1482_; lean_object* v___x_1484_; uint8_t v_isShared_1485_; uint8_t v_isSharedCheck_1489_; 
lean_dec_ref(v_eqProof_1467_);
lean_dec(v_a_1410_);
v_a_1482_ = lean_ctor_get(v___x_1480_, 0);
v_isSharedCheck_1489_ = !lean_is_exclusive(v___x_1480_);
if (v_isSharedCheck_1489_ == 0)
{
v___x_1484_ = v___x_1480_;
v_isShared_1485_ = v_isSharedCheck_1489_;
goto v_resetjp_1483_;
}
else
{
lean_inc(v_a_1482_);
lean_dec(v___x_1480_);
v___x_1484_ = lean_box(0);
v_isShared_1485_ = v_isSharedCheck_1489_;
goto v_resetjp_1483_;
}
v_resetjp_1483_:
{
lean_object* v___x_1487_; 
if (v_isShared_1485_ == 0)
{
v___x_1487_ = v___x_1484_;
goto v_reusejp_1486_;
}
else
{
lean_object* v_reuseFailAlloc_1488_; 
v_reuseFailAlloc_1488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1488_, 0, v_a_1482_);
v___x_1487_ = v_reuseFailAlloc_1488_;
goto v_reusejp_1486_;
}
v_reusejp_1486_:
{
return v___x_1487_;
}
}
}
}
else
{
lean_object* v_val_1490_; 
lean_dec_ref_known(v___x_1477_, 1);
v_val_1490_ = lean_ctor_get(v___y_1466_, 0);
lean_inc(v_val_1490_);
lean_dec_ref_known(v___y_1466_, 1);
v___y_1412_ = v___y_1469_;
v___y_1413_ = v___y_1470_;
v___y_1414_ = v___y_1468_;
v___y_1415_ = v___x_1472_;
v___y_1416_ = v_eqProof_1467_;
v___y_1417_ = v___y_1471_;
v_a_1418_ = v_val_1490_;
goto v___jp_1411_;
}
}
else
{
lean_object* v_a_1491_; lean_object* v___x_1493_; uint8_t v_isShared_1494_; uint8_t v_isSharedCheck_1498_; 
lean_dec_ref(v_eqProof_1467_);
lean_dec(v___y_1466_);
lean_dec(v_a_1410_);
v_a_1491_ = lean_ctor_get(v___x_1477_, 0);
v_isSharedCheck_1498_ = !lean_is_exclusive(v___x_1477_);
if (v_isSharedCheck_1498_ == 0)
{
v___x_1493_ = v___x_1477_;
v_isShared_1494_ = v_isSharedCheck_1498_;
goto v_resetjp_1492_;
}
else
{
lean_inc(v_a_1491_);
lean_dec(v___x_1477_);
v___x_1493_ = lean_box(0);
v_isShared_1494_ = v_isSharedCheck_1498_;
goto v_resetjp_1492_;
}
v_resetjp_1492_:
{
lean_object* v___x_1496_; 
if (v_isShared_1494_ == 0)
{
v___x_1496_ = v___x_1493_;
goto v_reusejp_1495_;
}
else
{
lean_object* v_reuseFailAlloc_1497_; 
v_reuseFailAlloc_1497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1497_, 0, v_a_1491_);
v___x_1496_ = v_reuseFailAlloc_1497_;
goto v_reusejp_1495_;
}
v_reusejp_1495_:
{
return v___x_1496_;
}
}
}
}
v___jp_1500_:
{
lean_object* v___x_1502_; 
v___x_1502_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__1___redArg(v_a_1347_, v___y_1501_);
lean_dec(v___y_1501_);
if (lean_obj_tag(v___x_1502_) == 0)
{
lean_dec_ref(v___x_1499_);
if (lean_obj_tag(v_snd_1400_) == 0)
{
lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1506_; 
lean_dec(v_a_1410_);
lean_dec(v_fst_1399_);
v___x_1503_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__2___closed__3, &l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__2___closed__3_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__2___closed__3);
v___x_1504_ = l_Lean_MessageData_ofName(v_head_1384_);
if (v_isShared_1403_ == 0)
{
lean_ctor_set_tag(v___x_1402_, 7);
lean_ctor_set(v___x_1402_, 1, v___x_1504_);
lean_ctor_set(v___x_1402_, 0, v___x_1503_);
v___x_1506_ = v___x_1402_;
goto v_reusejp_1505_;
}
else
{
lean_object* v_reuseFailAlloc_1518_; 
v_reuseFailAlloc_1518_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1518_, 0, v___x_1503_);
lean_ctor_set(v_reuseFailAlloc_1518_, 1, v___x_1504_);
v___x_1506_ = v_reuseFailAlloc_1518_;
goto v_reusejp_1505_;
}
v_reusejp_1505_:
{
lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v_a_1510_; lean_object* v___x_1512_; uint8_t v_isShared_1513_; uint8_t v_isSharedCheck_1517_; 
v___x_1507_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__2___closed__5, &l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__2___closed__5_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__2___closed__5);
v___x_1508_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1508_, 0, v___x_1506_);
lean_ctor_set(v___x_1508_, 1, v___x_1507_);
v___x_1509_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals_spec__1___redArg(v___x_1508_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_);
v_a_1510_ = lean_ctor_get(v___x_1509_, 0);
v_isSharedCheck_1517_ = !lean_is_exclusive(v___x_1509_);
if (v_isSharedCheck_1517_ == 0)
{
v___x_1512_ = v___x_1509_;
v_isShared_1513_ = v_isSharedCheck_1517_;
goto v_resetjp_1511_;
}
else
{
lean_inc(v_a_1510_);
lean_dec(v___x_1509_);
v___x_1512_ = lean_box(0);
v_isShared_1513_ = v_isSharedCheck_1517_;
goto v_resetjp_1511_;
}
v_resetjp_1511_:
{
lean_object* v___x_1515_; 
if (v_isShared_1513_ == 0)
{
v___x_1515_ = v___x_1512_;
goto v_reusejp_1514_;
}
else
{
lean_object* v_reuseFailAlloc_1516_; 
v_reuseFailAlloc_1516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1516_, 0, v_a_1510_);
v___x_1515_ = v_reuseFailAlloc_1516_;
goto v_reusejp_1514_;
}
v_reusejp_1514_:
{
return v___x_1515_;
}
}
}
}
else
{
lean_object* v_val_1519_; lean_object* v___x_1520_; 
lean_del_object(v___x_1402_);
lean_dec(v_head_1384_);
v_val_1519_ = lean_ctor_get(v_snd_1400_, 0);
lean_inc(v_val_1519_);
lean_dec_ref_known(v_snd_1400_, 1);
v___x_1520_ = lean_box(0);
v___y_1466_ = v___x_1520_;
v_eqProof_1467_ = v_val_1519_;
v___y_1468_ = v___y_1351_;
v___y_1469_ = v___y_1352_;
v___y_1470_ = v___y_1353_;
v___y_1471_ = v___y_1354_;
goto v___jp_1465_;
}
}
else
{
lean_object* v_val_1521_; lean_object* v_fst_1522_; lean_object* v_snd_1523_; lean_object* v_dummy_1524_; lean_object* v_nargs_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; 
lean_del_object(v___x_1402_);
lean_dec(v_head_1384_);
v_val_1521_ = lean_ctor_get(v___x_1502_, 0);
lean_inc(v_val_1521_);
lean_dec_ref_known(v___x_1502_, 1);
v_fst_1522_ = lean_ctor_get(v_val_1521_, 0);
lean_inc(v_fst_1522_);
v_snd_1523_ = lean_ctor_get(v_val_1521_, 1);
lean_inc_n(v_snd_1523_, 2);
lean_dec(v_val_1521_);
v_dummy_1524_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_spec__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_spec__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_spec__1___closed__3);
v_nargs_1525_ = l_Lean_Expr_getAppNumArgs(v_fst_1399_);
lean_inc(v_nargs_1525_);
v___x_1526_ = lean_mk_array(v_nargs_1525_, v_dummy_1524_);
v___x_1527_ = lean_unsigned_to_nat(1u);
v___x_1528_ = lean_nat_sub(v_nargs_1525_, v___x_1527_);
lean_dec(v_nargs_1525_);
lean_inc(v_fst_1399_);
v___x_1529_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_fst_1399_, v___x_1526_, v___x_1528_);
v___x_1530_ = l_Array_extract___redArg(v___x_1529_, v___x_1392_, v_snd_1523_);
v___x_1531_ = l_Lean_mkAppN(v___x_1499_, v___x_1530_);
lean_dec_ref(v___x_1530_);
v___x_1532_ = lean_array_get_size(v___x_1529_);
v___x_1533_ = l_Array_extract___redArg(v___x_1529_, v_snd_1523_, v___x_1532_);
lean_dec_ref(v___x_1529_);
v___x_1534_ = lean_array_to_list(v___x_1533_);
lean_inc(v_a_1410_);
v___x_1535_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkPointFrameApply(v_fst_1522_, v___x_1531_, v_a_1410_, v___x_1534_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_);
if (lean_obj_tag(v___x_1535_) == 0)
{
if (lean_obj_tag(v_snd_1400_) == 0)
{
lean_object* v_a_1536_; 
lean_dec(v_a_1410_);
lean_dec(v_fst_1399_);
v_a_1536_ = lean_ctor_get(v___x_1535_, 0);
lean_inc(v_a_1536_);
lean_dec_ref_known(v___x_1535_, 1);
v_prf_1357_ = v_a_1536_;
v___y_1358_ = v___y_1351_;
v___y_1359_ = v___y_1352_;
v___y_1360_ = v___y_1353_;
v___y_1361_ = v___y_1354_;
goto v___jp_1356_;
}
else
{
lean_object* v_a_1537_; lean_object* v_val_1538_; lean_object* v___x_1540_; uint8_t v_isShared_1541_; uint8_t v_isSharedCheck_1545_; 
v_a_1537_ = lean_ctor_get(v___x_1535_, 0);
lean_inc(v_a_1537_);
lean_dec_ref_known(v___x_1535_, 1);
v_val_1538_ = lean_ctor_get(v_snd_1400_, 0);
v_isSharedCheck_1545_ = !lean_is_exclusive(v_snd_1400_);
if (v_isSharedCheck_1545_ == 0)
{
v___x_1540_ = v_snd_1400_;
v_isShared_1541_ = v_isSharedCheck_1545_;
goto v_resetjp_1539_;
}
else
{
lean_inc(v_val_1538_);
lean_dec(v_snd_1400_);
v___x_1540_ = lean_box(0);
v_isShared_1541_ = v_isSharedCheck_1545_;
goto v_resetjp_1539_;
}
v_resetjp_1539_:
{
lean_object* v___x_1543_; 
if (v_isShared_1541_ == 0)
{
lean_ctor_set(v___x_1540_, 0, v_a_1537_);
v___x_1543_ = v___x_1540_;
goto v_reusejp_1542_;
}
else
{
lean_object* v_reuseFailAlloc_1544_; 
v_reuseFailAlloc_1544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1544_, 0, v_a_1537_);
v___x_1543_ = v_reuseFailAlloc_1544_;
goto v_reusejp_1542_;
}
v_reusejp_1542_:
{
v___y_1466_ = v___x_1543_;
v_eqProof_1467_ = v_val_1538_;
v___y_1468_ = v___y_1351_;
v___y_1469_ = v___y_1352_;
v___y_1470_ = v___y_1353_;
v___y_1471_ = v___y_1354_;
goto v___jp_1465_;
}
}
}
}
else
{
lean_object* v_a_1546_; lean_object* v___x_1548_; uint8_t v_isShared_1549_; uint8_t v_isSharedCheck_1553_; 
lean_dec(v_a_1410_);
lean_dec(v_snd_1400_);
lean_dec(v_fst_1399_);
v_a_1546_ = lean_ctor_get(v___x_1535_, 0);
v_isSharedCheck_1553_ = !lean_is_exclusive(v___x_1535_);
if (v_isSharedCheck_1553_ == 0)
{
v___x_1548_ = v___x_1535_;
v_isShared_1549_ = v_isSharedCheck_1553_;
goto v_resetjp_1547_;
}
else
{
lean_inc(v_a_1546_);
lean_dec(v___x_1535_);
v___x_1548_ = lean_box(0);
v_isShared_1549_ = v_isSharedCheck_1553_;
goto v_resetjp_1547_;
}
v_resetjp_1547_:
{
lean_object* v___x_1551_; 
if (v_isShared_1549_ == 0)
{
v___x_1551_ = v___x_1548_;
goto v_reusejp_1550_;
}
else
{
lean_object* v_reuseFailAlloc_1552_; 
v_reuseFailAlloc_1552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1552_, 0, v_a_1546_);
v___x_1551_ = v_reuseFailAlloc_1552_;
goto v_reusejp_1550_;
}
v_reusejp_1550_:
{
return v___x_1551_;
}
}
}
}
}
}
else
{
lean_object* v_a_1556_; lean_object* v___x_1558_; uint8_t v_isShared_1559_; uint8_t v_isSharedCheck_1563_; 
lean_del_object(v___x_1402_);
lean_dec(v_snd_1400_);
lean_dec(v_fst_1399_);
lean_dec(v_head_1384_);
v_a_1556_ = lean_ctor_get(v___x_1409_, 0);
v_isSharedCheck_1563_ = !lean_is_exclusive(v___x_1409_);
if (v_isSharedCheck_1563_ == 0)
{
v___x_1558_ = v___x_1409_;
v_isShared_1559_ = v_isSharedCheck_1563_;
goto v_resetjp_1557_;
}
else
{
lean_inc(v_a_1556_);
lean_dec(v___x_1409_);
v___x_1558_ = lean_box(0);
v_isShared_1559_ = v_isSharedCheck_1563_;
goto v_resetjp_1557_;
}
v_resetjp_1557_:
{
lean_object* v___x_1561_; 
if (v_isShared_1559_ == 0)
{
v___x_1561_ = v___x_1558_;
goto v_reusejp_1560_;
}
else
{
lean_object* v_reuseFailAlloc_1562_; 
v_reuseFailAlloc_1562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1562_, 0, v_a_1556_);
v___x_1561_ = v_reuseFailAlloc_1562_;
goto v_reusejp_1560_;
}
v_reusejp_1560_:
{
return v___x_1561_;
}
}
}
}
else
{
lean_object* v_a_1564_; lean_object* v___x_1566_; uint8_t v_isShared_1567_; uint8_t v_isSharedCheck_1571_; 
lean_del_object(v___x_1402_);
lean_dec(v_snd_1400_);
lean_dec(v_fst_1399_);
lean_dec(v_head_1384_);
v_a_1564_ = lean_ctor_get(v___x_1404_, 0);
v_isSharedCheck_1571_ = !lean_is_exclusive(v___x_1404_);
if (v_isSharedCheck_1571_ == 0)
{
v___x_1566_ = v___x_1404_;
v_isShared_1567_ = v_isSharedCheck_1571_;
goto v_resetjp_1565_;
}
else
{
lean_inc(v_a_1564_);
lean_dec(v___x_1404_);
v___x_1566_ = lean_box(0);
v_isShared_1567_ = v_isSharedCheck_1571_;
goto v_resetjp_1565_;
}
v_resetjp_1565_:
{
lean_object* v___x_1569_; 
if (v_isShared_1567_ == 0)
{
v___x_1569_ = v___x_1566_;
goto v_reusejp_1568_;
}
else
{
lean_object* v_reuseFailAlloc_1570_; 
v_reuseFailAlloc_1570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1570_, 0, v_a_1564_);
v___x_1569_ = v_reuseFailAlloc_1570_;
goto v_reusejp_1568_;
}
v_reusejp_1568_:
{
return v___x_1569_;
}
}
}
}
}
else
{
lean_object* v_a_1573_; lean_object* v___x_1575_; uint8_t v_isShared_1576_; uint8_t v_isSharedCheck_1580_; 
lean_dec_ref(v___x_1395_);
lean_dec(v_head_1384_);
v_a_1573_ = lean_ctor_get(v___x_1397_, 0);
v_isSharedCheck_1580_ = !lean_is_exclusive(v___x_1397_);
if (v_isSharedCheck_1580_ == 0)
{
v___x_1575_ = v___x_1397_;
v_isShared_1576_ = v_isSharedCheck_1580_;
goto v_resetjp_1574_;
}
else
{
lean_inc(v_a_1573_);
lean_dec(v___x_1397_);
v___x_1575_ = lean_box(0);
v_isShared_1576_ = v_isSharedCheck_1580_;
goto v_resetjp_1574_;
}
v_resetjp_1574_:
{
lean_object* v___x_1578_; 
if (v_isShared_1576_ == 0)
{
v___x_1578_ = v___x_1575_;
goto v_reusejp_1577_;
}
else
{
lean_object* v_reuseFailAlloc_1579_; 
v_reuseFailAlloc_1579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1579_, 0, v_a_1573_);
v___x_1578_ = v_reuseFailAlloc_1579_;
goto v_reusejp_1577_;
}
v_reusejp_1577_:
{
return v___x_1578_;
}
}
}
}
else
{
lean_object* v_a_1581_; lean_object* v___x_1583_; uint8_t v_isShared_1584_; uint8_t v_isSharedCheck_1588_; 
lean_dec(v_numConst_1385_);
lean_dec(v_head_1384_);
lean_dec_ref(v_x_1349_);
lean_dec_ref(v_x_1348_);
v_a_1581_ = lean_ctor_get(v___x_1390_, 0);
v_isSharedCheck_1588_ = !lean_is_exclusive(v___x_1390_);
if (v_isSharedCheck_1588_ == 0)
{
v___x_1583_ = v___x_1390_;
v_isShared_1584_ = v_isSharedCheck_1588_;
goto v_resetjp_1582_;
}
else
{
lean_inc(v_a_1581_);
lean_dec(v___x_1390_);
v___x_1583_ = lean_box(0);
v_isShared_1584_ = v_isSharedCheck_1588_;
goto v_resetjp_1582_;
}
v_resetjp_1582_:
{
lean_object* v___x_1586_; 
if (v_isShared_1584_ == 0)
{
v___x_1586_ = v___x_1583_;
goto v_reusejp_1585_;
}
else
{
lean_object* v_reuseFailAlloc_1587_; 
v_reuseFailAlloc_1587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1587_, 0, v_a_1581_);
v___x_1586_ = v_reuseFailAlloc_1587_;
goto v_reusejp_1585_;
}
v_reusejp_1585_:
{
return v___x_1586_;
}
}
}
}
v___jp_1356_:
{
uint8_t v___x_1362_; lean_object* v___x_1363_; 
v___x_1362_ = 1;
v___x_1363_ = l_Lean_Meta_abstractMVars(v_prf_1357_, v___x_1362_, v___y_1358_, v___y_1359_, v___y_1360_, v___y_1361_);
if (lean_obj_tag(v___x_1363_) == 0)
{
lean_object* v_a_1364_; lean_object* v_paramNames_1365_; lean_object* v_expr_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; 
v_a_1364_ = lean_ctor_get(v___x_1363_, 0);
lean_inc(v_a_1364_);
lean_dec_ref_known(v___x_1363_, 1);
v_paramNames_1365_ = lean_ctor_get(v_a_1364_, 0);
lean_inc_ref(v_paramNames_1365_);
v_expr_1366_ = lean_ctor_get(v_a_1364_, 2);
lean_inc_ref(v_expr_1366_);
lean_dec(v_a_1364_);
v___x_1367_ = lean_array_to_list(v_paramNames_1365_);
v___x_1368_ = lean_box(0);
v___x_1369_ = l_Lean_Meta_Sym_mkBackwardRuleFromExpr(v_expr_1366_, v___x_1367_, v___x_1368_, v___y_1358_, v___y_1359_, v___y_1360_, v___y_1361_);
return v___x_1369_;
}
else
{
lean_object* v_a_1370_; lean_object* v___x_1372_; uint8_t v_isShared_1373_; uint8_t v_isSharedCheck_1377_; 
v_a_1370_ = lean_ctor_get(v___x_1363_, 0);
v_isSharedCheck_1377_ = !lean_is_exclusive(v___x_1363_);
if (v_isSharedCheck_1377_ == 0)
{
v___x_1372_ = v___x_1363_;
v_isShared_1373_ = v_isSharedCheck_1377_;
goto v_resetjp_1371_;
}
else
{
lean_inc(v_a_1370_);
lean_dec(v___x_1363_);
v___x_1372_ = lean_box(0);
v_isShared_1373_ = v_isSharedCheck_1377_;
goto v_resetjp_1371_;
}
v_resetjp_1371_:
{
lean_object* v___x_1375_; 
if (v_isShared_1373_ == 0)
{
v___x_1375_ = v___x_1372_;
goto v_reusejp_1374_;
}
else
{
lean_object* v_reuseFailAlloc_1376_; 
v_reuseFailAlloc_1376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1376_, 0, v_a_1370_);
v___x_1375_ = v_reuseFailAlloc_1376_;
goto v_reusejp_1374_;
}
v_reusejp_1374_:
{
return v___x_1375_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__2___boxed(lean_object* v_op_1589_, lean_object* v___y_1590_, lean_object* v_a_1591_, lean_object* v_x_1592_, lean_object* v_x_1593_, lean_object* v_x_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_){
_start:
{
lean_object* v_res_1600_; 
v_res_1600_ = l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__2(v_op_1589_, v___y_1590_, v_a_1591_, v_x_1592_, v_x_1593_, v_x_1594_, v___y_1595_, v___y_1596_, v___y_1597_, v___y_1598_);
lean_dec(v___y_1598_);
lean_dec_ref(v___y_1597_);
lean_dec(v___y_1596_);
lean_dec_ref(v___y_1595_);
lean_dec_ref(v_a_1591_);
lean_dec_ref(v___y_1590_);
return v_res_1600_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__4(lean_object* v_as_1601_, size_t v_i_1602_, size_t v_stop_1603_, lean_object* v_b_1604_){
_start:
{
uint8_t v___x_1605_; 
v___x_1605_ = lean_usize_dec_eq(v_i_1602_, v_stop_1603_);
if (v___x_1605_ == 0)
{
lean_object* v___x_1606_; lean_object* v_rewrites_1607_; lean_object* v___x_1608_; size_t v___x_1609_; size_t v___x_1610_; 
v___x_1606_ = lean_array_uget_borrowed(v_as_1601_, v_i_1602_);
v_rewrites_1607_ = lean_ctor_get(v___x_1606_, 2);
v___x_1608_ = l_Array_append___redArg(v_b_1604_, v_rewrites_1607_);
v___x_1609_ = ((size_t)1ULL);
v___x_1610_ = lean_usize_add(v_i_1602_, v___x_1609_);
v_i_1602_ = v___x_1610_;
v_b_1604_ = v___x_1608_;
goto _start;
}
else
{
return v_b_1604_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__4___boxed(lean_object* v_as_1612_, lean_object* v_i_1613_, lean_object* v_stop_1614_, lean_object* v_b_1615_){
_start:
{
size_t v_i_boxed_1616_; size_t v_stop_boxed_1617_; lean_object* v_res_1618_; 
v_i_boxed_1616_ = lean_unbox_usize(v_i_1613_);
lean_dec(v_i_1613_);
v_stop_boxed_1617_ = lean_unbox_usize(v_stop_1614_);
lean_dec(v_stop_1614_);
v_res_1618_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__4(v_as_1612_, v_i_boxed_1616_, v_stop_boxed_1617_, v_b_1615_);
lean_dec_ref(v_as_1612_);
return v_res_1618_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__3(lean_object* v_as_1619_, size_t v_i_1620_, size_t v_stop_1621_, lean_object* v_b_1622_){
_start:
{
lean_object* v___y_1624_; uint8_t v___x_1628_; 
v___x_1628_ = lean_usize_dec_eq(v_i_1620_, v_stop_1621_);
if (v___x_1628_ == 0)
{
lean_object* v___x_1629_; lean_object* v_terminal_x3f_1630_; 
v___x_1629_ = lean_array_uget_borrowed(v_as_1619_, v_i_1620_);
v_terminal_x3f_1630_ = lean_ctor_get(v___x_1629_, 3);
if (lean_obj_tag(v_terminal_x3f_1630_) == 0)
{
lean_object* v___x_1631_; lean_object* v___x_1632_; 
v___x_1631_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_upperAdjoint___closed__3));
v___x_1632_ = l_Array_append___redArg(v_b_1622_, v___x_1631_);
v___y_1624_ = v___x_1632_;
goto v___jp_1623_;
}
else
{
lean_object* v_val_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; 
v_val_1633_ = lean_ctor_get(v_terminal_x3f_1630_, 0);
v___x_1634_ = lean_unsigned_to_nat(1u);
v___x_1635_ = lean_mk_empty_array_with_capacity(v___x_1634_);
lean_inc(v_val_1633_);
v___x_1636_ = lean_array_push(v___x_1635_, v_val_1633_);
v___x_1637_ = l_Array_append___redArg(v_b_1622_, v___x_1636_);
lean_dec_ref(v___x_1636_);
v___y_1624_ = v___x_1637_;
goto v___jp_1623_;
}
}
else
{
return v_b_1622_;
}
v___jp_1623_:
{
size_t v___x_1625_; size_t v___x_1626_; 
v___x_1625_ = ((size_t)1ULL);
v___x_1626_ = lean_usize_add(v_i_1620_, v___x_1625_);
v_i_1620_ = v___x_1626_;
v_b_1622_ = v___y_1624_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__3___boxed(lean_object* v_as_1638_, lean_object* v_i_1639_, lean_object* v_stop_1640_, lean_object* v_b_1641_){
_start:
{
size_t v_i_boxed_1642_; size_t v_stop_boxed_1643_; lean_object* v_res_1644_; 
v_i_boxed_1642_ = lean_unbox_usize(v_i_1639_);
lean_dec(v_i_1639_);
v_stop_boxed_1643_ = lean_unbox_usize(v_stop_1640_);
lean_dec(v_stop_1640_);
v_res_1644_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__3(v_as_1638_, v_i_boxed_1642_, v_stop_boxed_1643_, v_b_1641_);
lean_dec_ref(v_as_1638_);
return v_res_1644_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule___closed__0(void){
_start:
{
lean_object* v___x_1645_; size_t v___x_1646_; size_t v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; 
v___x_1645_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_upperAdjoint___closed__3));
v___x_1646_ = lean_usize_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable___closed__3, &l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable___closed__3_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpTable___closed__3);
v___x_1647_ = ((size_t)0ULL);
v___x_1648_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_builtinLatticeOps));
v___x_1649_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__3(v___x_1648_, v___x_1647_, v___x_1646_, v___x_1645_);
return v___x_1649_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule(lean_object* v_rhs_1650_, lean_object* v_op_1651_, lean_object* v_a_1652_, lean_object* v_a_1653_, lean_object* v_a_1654_, lean_object* v_a_1655_){
_start:
{
lean_object* v___y_1658_; lean_object* v___y_1659_; lean_object* v___y_1660_; lean_object* v_rewrites_1678_; lean_object* v_terminal_x3f_1679_; lean_object* v___x_1680_; lean_object* v___y_1682_; lean_object* v___y_1683_; lean_object* v___y_1690_; uint8_t v___x_1696_; 
v_rewrites_1678_ = lean_ctor_get(v_op_1651_, 2);
v_terminal_x3f_1679_ = lean_ctor_get(v_op_1651_, 3);
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
lean_inc_ref(v___y_1659_);
v___x_1661_ = l_Array_append___redArg(v___y_1659_, v___y_1660_);
lean_dec_ref(v___y_1660_);
v___x_1662_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeTerminals(v___x_1661_, v_a_1652_, v_a_1653_, v_a_1654_, v_a_1655_);
lean_dec_ref(v___x_1661_);
if (lean_obj_tag(v___x_1662_) == 0)
{
lean_object* v_a_1663_; lean_object* v_dummy_1664_; lean_object* v_nargs_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; 
v_a_1663_ = lean_ctor_get(v___x_1662_, 0);
lean_inc(v_a_1663_);
lean_dec_ref_known(v___x_1662_, 1);
v_dummy_1664_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_spec__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_spec__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp_0__Lean_Elab_Tactic_Do_Internal_VCGen_saturateLatticeOp_spec__1___closed__3);
v_nargs_1665_ = l_Lean_Expr_getAppNumArgs(v_rhs_1650_);
lean_inc(v_nargs_1665_);
v___x_1666_ = lean_mk_array(v_nargs_1665_, v_dummy_1664_);
v___x_1667_ = lean_unsigned_to_nat(1u);
v___x_1668_ = lean_nat_sub(v_nargs_1665_, v___x_1667_);
lean_dec(v_nargs_1665_);
v___x_1669_ = l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__2(v_op_1651_, v___y_1658_, v_a_1663_, v_rhs_1650_, v___x_1666_, v___x_1668_, v_a_1652_, v_a_1653_, v_a_1654_, v_a_1655_);
lean_dec(v_a_1663_);
lean_dec_ref(v___y_1658_);
return v___x_1669_;
}
else
{
lean_object* v_a_1670_; lean_object* v___x_1672_; uint8_t v_isShared_1673_; uint8_t v_isSharedCheck_1677_; 
lean_dec_ref(v___y_1658_);
lean_dec_ref(v_op_1651_);
lean_dec_ref(v_rhs_1650_);
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
v___y_1658_ = v___y_1682_;
v___y_1659_ = v___y_1683_;
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
v___y_1658_ = v___y_1682_;
v___y_1659_ = v___y_1683_;
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule___boxed(lean_object* v_rhs_1704_, lean_object* v_op_1705_, lean_object* v_a_1706_, lean_object* v_a_1707_, lean_object* v_a_1708_, lean_object* v_a_1709_, lean_object* v_a_1710_){
_start:
{
lean_object* v_res_1711_; 
v_res_1711_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule(v_rhs_1704_, v_op_1705_, v_a_1706_, v_a_1707_, v_a_1708_, v_a_1709_);
lean_dec(v_a_1709_);
lean_dec_ref(v_a_1708_);
lean_dec(v_a_1707_);
lean_dec_ref(v_a_1706_);
return v_res_1711_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__1(lean_object* v_00_u03b2_1712_, lean_object* v_m_1713_, lean_object* v_a_1714_){
_start:
{
lean_object* v___x_1715_; 
v___x_1715_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__1___redArg(v_m_1713_, v_a_1714_);
return v___x_1715_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__1___boxed(lean_object* v_00_u03b2_1716_, lean_object* v_m_1717_, lean_object* v_a_1718_){
_start:
{
lean_object* v_res_1719_; 
v_res_1719_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__1(v_00_u03b2_1716_, v_m_1717_, v_a_1718_);
lean_dec(v_a_1718_);
lean_dec_ref(v_m_1717_);
return v_res_1719_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__1_spec__1(lean_object* v_00_u03b2_1720_, lean_object* v_a_1721_, lean_object* v_x_1722_){
_start:
{
lean_object* v___x_1723_; 
v___x_1723_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__1_spec__1___redArg(v_a_1721_, v_x_1722_);
return v___x_1723_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__1_spec__1___boxed(lean_object* v_00_u03b2_1724_, lean_object* v_a_1725_, lean_object* v_x_1726_){
_start:
{
lean_object* v_res_1727_; 
v_res_1727_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule_spec__1_spec__1(v_00_u03b2_1724_, v_a_1725_, v_x_1726_);
lean_dec(v_x_1726_);
lean_dec(v_a_1725_);
return v_res_1727_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_Apply(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_Do_Order_Heyting(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProc(uint8_t builtin);
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
