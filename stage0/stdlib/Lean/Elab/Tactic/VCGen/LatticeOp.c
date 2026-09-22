// Lean compiler output
// Module: Lean.Elab.Tactic.VCGen.LatticeOp
// Imports: public import Lean.Meta.Sym.Apply public import Std.Internal.Order.Heyting import Std.Internal.Order.FrameClosure import Lean.Meta.Sym.Simp.Rewrite import Lean.Meta.AppBuilder import Lean.Meta.AbstractMVars
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
lean_object* lean_array_mk(lean_object*);
lean_object* lean_array_pop(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAppOptM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_SimpM_run_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_mkEqTrans(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
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
lean_object* l_Lean_Expr_constName_x3f(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
lean_object* l_Lean_Meta_abstractMVars(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_mkBackwardRuleFromExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_extract___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_dischargeNone___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_Theorems_rewrite___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Meta_Sym_Simp_mkTheoremFromDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_Theorems_insert(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkCongrArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqSymm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Order"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meet"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__4_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__2_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__4_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__3_value),LEAN_SCALAR_PTR_LITERAL(194, 193, 63, 6, 53, 61, 199, 176)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__4_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "meet_apply"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__6_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__2_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__6_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__5_value),LEAN_SCALAR_PTR_LITERAL(99, 197, 244, 134, 174, 130, 207, 233)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__6_value;
static const lean_array_object l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__6_value)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__7_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "le_meet"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__8_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__9_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__2_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__9_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__8_value),LEAN_SCALAR_PTR_LITERAL(190, 114, 168, 215, 244, 74, 160, 2)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__9 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__9_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__9_value)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__10 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__10_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__4_value),((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__7_value),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__10_value),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__0_value)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__11 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__11_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_meet = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__11_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_LatticeOp_himp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "himp"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_himp___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_himp___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_himp___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_himp___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_himp___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__2_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_himp___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_himp___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_himp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(173, 29, 48, 122, 5, 158, 45, 140)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_himp___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_himp___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_LatticeOp_himp___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "himp_apply"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_himp___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_himp___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_himp___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_himp___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_himp___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__2_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_himp___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_himp___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_himp___closed__2_value),LEAN_SCALAR_PTR_LITERAL(185, 113, 71, 38, 245, 240, 32, 111)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_himp___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_himp___closed__3_value;
static const lean_array_object l_Lean_Elab_Tactic_VCGen_LatticeOp_himp___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_himp___closed__3_value)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_himp___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_himp___closed__4_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_LatticeOp_himp___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "le_himp"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_himp___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_himp___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_himp___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_himp___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_himp___closed__6_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__2_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_himp___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_himp___closed__6_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_himp___closed__5_value),LEAN_SCALAR_PTR_LITERAL(34, 1, 31, 114, 210, 147, 30, 159)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_himp___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_himp___closed__6_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_himp___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_himp___closed__6_value)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_himp___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_himp___closed__7_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_himp___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_himp___closed__1_value),((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_himp___closed__4_value),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_himp___closed__7_value),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__0_value)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_himp___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_himp___closed__8_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_himp = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_himp___closed__8_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_LatticeOp_ofProp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "CompleteLattice"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_ofProp___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_ofProp___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_LatticeOp_ofProp___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "ofProp"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_ofProp___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_ofProp___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_ofProp___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_ofProp___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_ofProp___closed__2_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__2_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_ofProp___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_ofProp___closed__2_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_ofProp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(239, 140, 127, 117, 148, 144, 166, 107)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_ofProp___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_ofProp___closed__2_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_ofProp___closed__1_value),LEAN_SCALAR_PTR_LITERAL(51, 160, 150, 32, 134, 96, 114, 42)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_ofProp___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_ofProp___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_LatticeOp_ofProp___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "ofProp_apply"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_ofProp___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_ofProp___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_ofProp___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_ofProp___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_ofProp___closed__4_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__2_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_ofProp___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_ofProp___closed__4_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_ofProp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(239, 140, 127, 117, 148, 144, 166, 107)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_ofProp___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_ofProp___closed__4_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_ofProp___closed__3_value),LEAN_SCALAR_PTR_LITERAL(43, 0, 38, 134, 51, 116, 27, 243)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_ofProp___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_ofProp___closed__4_value;
static const lean_array_object l_Lean_Elab_Tactic_VCGen_LatticeOp_ofProp___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_ofProp___closed__4_value)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_ofProp___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_ofProp___closed__5_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_LatticeOp_ofProp___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "top_le_ofProp"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_ofProp___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_ofProp___closed__6_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_ofProp___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_ofProp___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_ofProp___closed__7_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__2_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_ofProp___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_ofProp___closed__7_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_ofProp___closed__6_value),LEAN_SCALAR_PTR_LITERAL(240, 115, 147, 236, 50, 105, 134, 105)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_ofProp___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_ofProp___closed__7_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_ofProp___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_ofProp___closed__7_value)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_ofProp___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_ofProp___closed__8_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_ofProp___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_ofProp___closed__2_value),((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_ofProp___closed__5_value),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_ofProp___closed__8_value),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__0_value)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_ofProp___closed__9 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_ofProp___closed__9_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_ofProp = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_ofProp___closed__9_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_LatticeOp_top___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "top"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_top___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_top___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_top___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_top___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_top___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__2_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_top___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_top___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_top___closed__0_value),LEAN_SCALAR_PTR_LITERAL(219, 33, 148, 124, 218, 91, 248, 169)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_top___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_top___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_LatticeOp_top___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "top_apply"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_top___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_top___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_top___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_top___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_top___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__2_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_top___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_top___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_top___closed__2_value),LEAN_SCALAR_PTR_LITERAL(230, 219, 32, 190, 96, 78, 240, 61)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_top___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_top___closed__3_value;
static const lean_array_object l_Lean_Elab_Tactic_VCGen_LatticeOp_top___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_top___closed__3_value)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_top___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_top___closed__4_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_LatticeOp_top___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "le_top"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_top___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_top___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_top___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_top___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_top___closed__6_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__2_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_top___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_top___closed__6_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_top___closed__5_value),LEAN_SCALAR_PTR_LITERAL(236, 200, 120, 191, 69, 224, 183, 155)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_top___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_top___closed__6_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_top___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_top___closed__6_value)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_top___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_top___closed__7_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_top___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_top___closed__1_value),((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_top___closed__4_value),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_top___closed__7_value),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__0_value)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_top___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_top___closed__8_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_top = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_top___closed__8_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "PreservesSup"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "upperAdjoint"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__2_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__2_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__2_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__0_value),LEAN_SCALAR_PTR_LITERAL(184, 207, 242, 99, 37, 43, 114, 21)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__2_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__1_value),LEAN_SCALAR_PTR_LITERAL(196, 52, 128, 160, 100, 147, 237, 166)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "FrameOp"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__3_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "upperAdjoint_pointwise_apply"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__5_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__2_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__5_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__3_value),LEAN_SCALAR_PTR_LITERAL(229, 61, 90, 123, 91, 82, 164, 46)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__5_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__4_value),LEAN_SCALAR_PTR_LITERAL(228, 97, 152, 21, 240, 180, 215, 25)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__5_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "upperAdjoint_ignore"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__6_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__7_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__2_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__7_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__3_value),LEAN_SCALAR_PTR_LITERAL(229, 61, 90, 123, 91, 82, 164, 46)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__7_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__6_value),LEAN_SCALAR_PTR_LITERAL(74, 144, 233, 4, 80, 167, 167, 85)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__7_value;
static const lean_array_object l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__5_value),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__7_value)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__8_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "le_upperAdjoint"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__9 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__9_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__10_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__2_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__10_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__10_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__0_value),LEAN_SCALAR_PTR_LITERAL(184, 207, 242, 99, 37, 43, 114, 21)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__10_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__9_value),LEAN_SCALAR_PTR_LITERAL(28, 162, 178, 118, 193, 187, 169, 14)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__10 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__10_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__10_value)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__11 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__11_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__2_value),((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__8_value),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__11_value),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__0_value)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__12 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__12_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__12_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_LatticeOp_iInf___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "iInf"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_iInf___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_iInf___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_iInf___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_iInf___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_iInf___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__2_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_iInf___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_iInf___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_iInf___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 96, 105, 10, 16, 194, 128, 157)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_iInf___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_iInf___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_LatticeOp_iInf___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "iInf_apply"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_iInf___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_iInf___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_iInf___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_iInf___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_iInf___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__2_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_iInf___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_iInf___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_iInf___closed__2_value),LEAN_SCALAR_PTR_LITERAL(13, 69, 58, 252, 126, 189, 121, 48)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_iInf___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_iInf___closed__3_value;
static const lean_array_object l_Lean_Elab_Tactic_VCGen_LatticeOp_iInf___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_iInf___closed__3_value)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_iInf___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_iInf___closed__4_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_LatticeOp_iInf___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "le_iInf"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_iInf___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_iInf___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_iInf___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_iInf___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_iInf___closed__6_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__2_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_iInf___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_iInf___closed__6_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_iInf___closed__5_value),LEAN_SCALAR_PTR_LITERAL(137, 155, 79, 233, 132, 15, 131, 19)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_iInf___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_iInf___closed__6_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_iInf___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_iInf___closed__6_value)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_iInf___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_iInf___closed__7_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_iInf___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_iInf___closed__1_value),((lean_object*)(((size_t)(3) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_iInf___closed__4_value),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_iInf___closed__7_value),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__0_value)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_iInf___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_iInf___closed__8_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_iInf = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_iInf___closed__8_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_projectsRewritableOperand___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_projectsRewritableOperand___closed__0;
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_projectsRewritableOperand___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "bot"};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_projectsRewritableOperand___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_projectsRewritableOperand___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_projectsRewritableOperand___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "prod"};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_projectsRewritableOperand___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_projectsRewritableOperand___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_projectsRewritableOperand___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_projectsRewritableOperand___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_projectsRewritableOperand___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__2_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_projectsRewritableOperand___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_projectsRewritableOperand___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__3_value),LEAN_SCALAR_PTR_LITERAL(229, 61, 90, 123, 91, 82, 164, 46)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_projectsRewritableOperand___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_projectsRewritableOperand___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_projectsRewritableOperand___closed__2_value),LEAN_SCALAR_PTR_LITERAL(157, 133, 236, 145, 12, 77, 122, 73)}};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_projectsRewritableOperand___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_projectsRewritableOperand___closed__3_value;
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_projectsRewritableOperand(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_projectsRewritableOperand___boxed(lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Prod"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "fst"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__0_value),LEAN_SCALAR_PTR_LITERAL(121, 119, 164, 206, 221, 118, 48, 212)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__2_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__1_value),LEAN_SCALAR_PTR_LITERAL(170, 44, 236, 58, 247, 164, 254, 114)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "fst_bot"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__4_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__2_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__4_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__0_value),LEAN_SCALAR_PTR_LITERAL(85, 207, 85, 101, 141, 28, 12, 60)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__4_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__3_value),LEAN_SCALAR_PTR_LITERAL(186, 58, 243, 31, 167, 194, 180, 25)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__4_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "fst_top"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__6_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__2_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__6_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__0_value),LEAN_SCALAR_PTR_LITERAL(85, 207, 85, 101, 141, 28, 12, 60)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__6_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__5_value),LEAN_SCALAR_PTR_LITERAL(179, 128, 115, 193, 32, 36, 28, 147)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__6_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "bot_apply"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__7_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__8_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__2_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__8_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__7_value),LEAN_SCALAR_PTR_LITERAL(245, 109, 99, 66, 8, 241, 194, 60)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__8_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "prod_fst"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__9 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__9_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__10_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__2_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__10_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__10_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__3_value),LEAN_SCALAR_PTR_LITERAL(229, 61, 90, 123, 91, 82, 164, 46)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__10_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__9_value),LEAN_SCALAR_PTR_LITERAL(171, 75, 215, 94, 1, 119, 52, 128)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__10 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__10_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "pointwise_apply"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__11 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__11_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__12_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__12_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__2_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__12_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__12_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__3_value),LEAN_SCALAR_PTR_LITERAL(229, 61, 90, 123, 91, 82, 164, 46)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__12_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__11_value),LEAN_SCALAR_PTR_LITERAL(113, 17, 225, 29, 225, 237, 185, 146)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__12 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__12_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "ignore_apply"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__13 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__13_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__14_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__14_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__2_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__14_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__14_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__3_value),LEAN_SCALAR_PTR_LITERAL(229, 61, 90, 123, 91, 82, 164, 46)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__14_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__13_value),LEAN_SCALAR_PTR_LITERAL(7, 31, 13, 121, 203, 153, 52, 174)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__14 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__14_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "upperAdjoint_prod_fst"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__15 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__15_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__16_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__16_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__2_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__16_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__16_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__3_value),LEAN_SCALAR_PTR_LITERAL(229, 61, 90, 123, 91, 82, 164, 46)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__16_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__15_value),LEAN_SCALAR_PTR_LITERAL(105, 223, 108, 4, 135, 195, 200, 89)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__16 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__16_value;
static const lean_array_object l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*8, .m_other = 0, .m_tag = 246}, .m_size = 8, .m_capacity = 8, .m_data = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__4_value),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__6_value),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__8_value),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_top___closed__3_value),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__10_value),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__12_value),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__14_value),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__16_value)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__17 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__17_value;
static const lean_closure_object l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_projectsRewritableOperand___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__18 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__18_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__2_value),((lean_object*)(((size_t)(3) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__17_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__18_value)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__19 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__19_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_fst = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__19_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_LatticeOp_snd___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "snd"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_snd___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_snd___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_snd___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__0_value),LEAN_SCALAR_PTR_LITERAL(121, 119, 164, 206, 221, 118, 48, 212)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_snd___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_snd___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_snd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(35, 40, 163, 84, 60, 49, 151, 224)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_snd___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_snd___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_LatticeOp_snd___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "snd_bot"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_snd___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_snd___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_snd___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_snd___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_snd___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__2_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_snd___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_snd___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__0_value),LEAN_SCALAR_PTR_LITERAL(85, 207, 85, 101, 141, 28, 12, 60)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_snd___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_snd___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_snd___closed__2_value),LEAN_SCALAR_PTR_LITERAL(57, 77, 34, 250, 153, 237, 26, 225)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_snd___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_snd___closed__3_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_LatticeOp_snd___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "snd_top"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_snd___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_snd___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_snd___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_snd___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_snd___closed__5_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__2_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_snd___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_snd___closed__5_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__0_value),LEAN_SCALAR_PTR_LITERAL(85, 207, 85, 101, 141, 28, 12, 60)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_snd___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_snd___closed__5_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_snd___closed__4_value),LEAN_SCALAR_PTR_LITERAL(7, 83, 81, 15, 47, 49, 64, 196)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_snd___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_snd___closed__5_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_LatticeOp_snd___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "prod_snd"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_snd___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_snd___closed__6_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_snd___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_snd___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_snd___closed__7_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__2_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_snd___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_snd___closed__7_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__3_value),LEAN_SCALAR_PTR_LITERAL(229, 61, 90, 123, 91, 82, 164, 46)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_snd___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_snd___closed__7_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_snd___closed__6_value),LEAN_SCALAR_PTR_LITERAL(152, 14, 106, 162, 136, 42, 40, 84)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_snd___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_snd___closed__7_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_LatticeOp_snd___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "upperAdjoint_prod_snd"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_snd___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_snd___closed__8_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_snd___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_snd___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_snd___closed__9_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__2_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_snd___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_snd___closed__9_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__3_value),LEAN_SCALAR_PTR_LITERAL(229, 61, 90, 123, 91, 82, 164, 46)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_snd___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_snd___closed__9_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_snd___closed__8_value),LEAN_SCALAR_PTR_LITERAL(54, 211, 10, 73, 121, 22, 210, 55)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_snd___closed__9 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_snd___closed__9_value;
static const lean_array_object l_Lean_Elab_Tactic_VCGen_LatticeOp_snd___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*8, .m_other = 0, .m_tag = 246}, .m_size = 8, .m_capacity = 8, .m_data = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_snd___closed__3_value),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_snd___closed__5_value),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__8_value),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_top___closed__3_value),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_snd___closed__7_value),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__12_value),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__14_value),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_snd___closed__9_value)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_snd___closed__10 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_snd___closed__10_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_snd___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_snd___closed__1_value),((lean_object*)(((size_t)(3) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_snd___closed__10_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__18_value)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_snd___closed__11 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_snd___closed__11_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_snd = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_snd___closed__11_value;
static const lean_array_object l_Lean_Elab_Tactic_VCGen_builtinLatticeOps___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*8, .m_other = 0, .m_tag = 246}, .m_size = 8, .m_capacity = 8, .m_data = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__11_value),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_himp___closed__8_value),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_ofProp___closed__9_value),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_top___closed__8_value),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__12_value),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_iInf___closed__8_value),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__19_value),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_snd___closed__11_value)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_builtinLatticeOps___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_builtinLatticeOps___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_Tactic_VCGen_builtinLatticeOps = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_builtinLatticeOps___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0_spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0_spec__1___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_Tactic_VCGen_latticeOps___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_VCGen_latticeOps___closed__0;
static lean_once_cell_t l_Lean_Elab_Tactic_VCGen_latticeOps___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_VCGen_latticeOps___closed__1;
static lean_once_cell_t l_Lean_Elab_Tactic_VCGen_latticeOps___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_VCGen_latticeOps___closed__2;
static lean_once_cell_t l_Lean_Elab_Tactic_VCGen_latticeOps___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Lean_Elab_Tactic_VCGen_latticeOps___closed__3;
static lean_once_cell_t l_Lean_Elab_Tactic_VCGen_latticeOps___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Lean_Elab_Tactic_VCGen_latticeOps___closed__4;
static lean_once_cell_t l_Lean_Elab_Tactic_VCGen_latticeOps___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_Elab_Tactic_VCGen_latticeOps___closed__5;
static lean_once_cell_t l_Lean_Elab_Tactic_VCGen_latticeOps___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_VCGen_latticeOps___closed__6;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_latticeOps;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__2_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__2_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
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
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply___closed__5_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__2_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__1_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__4(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__3___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__3___closed__0_value;
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___lam__0(lean_object* v_x_1_){
_start:
{
uint8_t v___x_2_; 
v___x_2_ = 1;
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___lam__0___boxed(lean_object* v_x_3_){
_start:
{
uint8_t v_res_4_; lean_object* v_r_5_; 
v_res_4_ = l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___lam__0(v_x_3_);
lean_dec_ref(v_x_3_);
v_r_5_ = lean_box(v_res_4_);
return v_r_5_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_projectsRewritableOperand___closed__0(void){
_start:
{
lean_object* v___x_193_; lean_object* v_dummy_194_; 
v___x_193_ = lean_box(0);
v_dummy_194_ = l_Lean_Expr_sort___override(v___x_193_);
return v_dummy_194_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_projectsRewritableOperand(lean_object* v_rhs_202_){
_start:
{
lean_object* v_dummy_203_; lean_object* v_nargs_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; uint8_t v___x_211_; 
v_dummy_203_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_projectsRewritableOperand___closed__0, &l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_projectsRewritableOperand___closed__0_once, _init_l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_projectsRewritableOperand___closed__0);
v_nargs_204_ = l_Lean_Expr_getAppNumArgs(v_rhs_202_);
lean_inc(v_nargs_204_);
v___x_205_ = lean_mk_array(v_nargs_204_, v_dummy_203_);
v___x_206_ = lean_unsigned_to_nat(1u);
v___x_207_ = lean_nat_sub(v_nargs_204_, v___x_206_);
lean_dec(v_nargs_204_);
v___x_208_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_rhs_202_, v___x_205_, v___x_207_);
v___x_209_ = lean_unsigned_to_nat(2u);
v___x_210_ = lean_array_get_size(v___x_208_);
v___x_211_ = lean_nat_dec_lt(v___x_209_, v___x_210_);
if (v___x_211_ == 0)
{
lean_dec_ref(v___x_208_);
return v___x_211_;
}
else
{
lean_object* v___x_212_; lean_object* v___x_213_; 
v___x_212_ = lean_array_fget(v___x_208_, v___x_209_);
lean_dec_ref(v___x_208_);
v___x_213_ = l_Lean_Expr_getAppFn(v___x_212_);
if (lean_obj_tag(v___x_213_) == 4)
{
lean_object* v_declName_214_; 
v_declName_214_ = lean_ctor_get(v___x_213_, 0);
lean_inc(v_declName_214_);
lean_dec_ref_known(v___x_213_, 2);
if (lean_obj_tag(v_declName_214_) == 1)
{
lean_object* v_pre_215_; 
v_pre_215_ = lean_ctor_get(v_declName_214_, 0);
lean_inc(v_pre_215_);
if (lean_obj_tag(v_pre_215_) == 1)
{
lean_object* v_pre_216_; 
v_pre_216_ = lean_ctor_get(v_pre_215_, 0);
lean_inc(v_pre_216_);
if (lean_obj_tag(v_pre_216_) == 1)
{
lean_object* v_pre_217_; 
v_pre_217_ = lean_ctor_get(v_pre_216_, 0);
switch(lean_obj_tag(v_pre_217_))
{
case 0:
{
lean_object* v_str_218_; lean_object* v_str_219_; lean_object* v_str_220_; lean_object* v___x_221_; uint8_t v___x_222_; 
lean_dec(v___x_212_);
v_str_218_ = lean_ctor_get(v_declName_214_, 1);
lean_inc_ref(v_str_218_);
lean_dec_ref_known(v_declName_214_, 2);
v_str_219_ = lean_ctor_get(v_pre_215_, 1);
lean_inc_ref(v_str_219_);
lean_dec_ref_known(v_pre_215_, 2);
v_str_220_ = lean_ctor_get(v_pre_216_, 1);
lean_inc_ref(v_str_220_);
lean_dec_ref_known(v_pre_216_, 2);
v___x_221_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__1));
v___x_222_ = lean_string_dec_eq(v_str_220_, v___x_221_);
lean_dec_ref(v_str_220_);
if (v___x_222_ == 0)
{
lean_dec_ref(v_str_219_);
lean_dec_ref(v_str_218_);
return v___x_222_;
}
else
{
lean_object* v___x_223_; uint8_t v___x_224_; 
v___x_223_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__2));
v___x_224_ = lean_string_dec_eq(v_str_219_, v___x_223_);
lean_dec_ref(v_str_219_);
if (v___x_224_ == 0)
{
lean_dec_ref(v_str_218_);
return v___x_224_;
}
else
{
lean_object* v___x_225_; uint8_t v___x_226_; 
v___x_225_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_projectsRewritableOperand___closed__1));
v___x_226_ = lean_string_dec_eq(v_str_218_, v___x_225_);
if (v___x_226_ == 0)
{
lean_object* v___x_227_; uint8_t v___x_228_; 
v___x_227_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_LatticeOp_top___closed__0));
v___x_228_ = lean_string_dec_eq(v_str_218_, v___x_227_);
lean_dec_ref(v_str_218_);
return v___x_228_;
}
else
{
lean_dec_ref(v_str_218_);
return v___x_226_;
}
}
}
}
case 1:
{
lean_object* v_pre_229_; 
lean_inc_ref(v_pre_217_);
v_pre_229_ = lean_ctor_get(v_pre_217_, 0);
if (lean_obj_tag(v_pre_229_) == 0)
{
lean_object* v_str_230_; lean_object* v_str_231_; lean_object* v_str_232_; lean_object* v_str_233_; lean_object* v___x_234_; uint8_t v___x_235_; 
v_str_230_ = lean_ctor_get(v_declName_214_, 1);
lean_inc_ref(v_str_230_);
lean_dec_ref_known(v_declName_214_, 2);
v_str_231_ = lean_ctor_get(v_pre_215_, 1);
lean_inc_ref(v_str_231_);
lean_dec_ref_known(v_pre_215_, 2);
v_str_232_ = lean_ctor_get(v_pre_216_, 1);
lean_inc_ref(v_str_232_);
lean_dec_ref_known(v_pre_216_, 2);
v_str_233_ = lean_ctor_get(v_pre_217_, 1);
lean_inc_ref(v_str_233_);
lean_dec_ref_known(v_pre_217_, 2);
v___x_234_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__1));
v___x_235_ = lean_string_dec_eq(v_str_233_, v___x_234_);
lean_dec_ref(v_str_233_);
if (v___x_235_ == 0)
{
lean_dec_ref(v_str_232_);
lean_dec_ref(v_str_231_);
lean_dec_ref(v_str_230_);
lean_dec(v___x_212_);
return v___x_235_;
}
else
{
lean_object* v___x_236_; uint8_t v___x_237_; 
v___x_236_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__2));
v___x_237_ = lean_string_dec_eq(v_str_232_, v___x_236_);
lean_dec_ref(v_str_232_);
if (v___x_237_ == 0)
{
lean_dec_ref(v_str_231_);
lean_dec_ref(v_str_230_);
lean_dec(v___x_212_);
return v___x_237_;
}
else
{
lean_object* v___x_238_; uint8_t v___x_239_; 
v___x_238_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__3));
v___x_239_ = lean_string_dec_eq(v_str_231_, v___x_238_);
if (v___x_239_ == 0)
{
lean_object* v___x_240_; uint8_t v___x_241_; 
v___x_240_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__0));
v___x_241_ = lean_string_dec_eq(v_str_231_, v___x_240_);
lean_dec_ref(v_str_231_);
if (v___x_241_ == 0)
{
lean_dec_ref(v_str_230_);
lean_dec(v___x_212_);
return v___x_241_;
}
else
{
lean_object* v___x_242_; uint8_t v___x_243_; 
v___x_242_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__1));
v___x_243_ = lean_string_dec_eq(v_str_230_, v___x_242_);
lean_dec_ref(v_str_230_);
if (v___x_243_ == 0)
{
lean_dec(v___x_212_);
return v___x_243_;
}
else
{
lean_object* v_nargs_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; uint8_t v___x_249_; 
v_nargs_244_ = l_Lean_Expr_getAppNumArgs(v___x_212_);
lean_inc(v_nargs_244_);
v___x_245_ = lean_mk_array(v_nargs_244_, v_dummy_203_);
v___x_246_ = lean_nat_sub(v_nargs_244_, v___x_206_);
lean_dec(v_nargs_244_);
v___x_247_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v___x_212_, v___x_245_, v___x_246_);
v___x_248_ = lean_array_get_size(v___x_247_);
v___x_249_ = lean_nat_dec_lt(v___x_209_, v___x_248_);
if (v___x_249_ == 0)
{
lean_dec_ref(v___x_247_);
return v___x_239_;
}
else
{
lean_object* v___x_250_; lean_object* v___x_251_; uint8_t v___x_252_; 
v___x_250_ = lean_array_fget(v___x_247_, v___x_209_);
lean_dec_ref(v___x_247_);
v___x_251_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_projectsRewritableOperand___closed__3));
v___x_252_ = l_Lean_Expr_isAppOf(v___x_250_, v___x_251_);
lean_dec(v___x_250_);
return v___x_252_;
}
}
}
}
else
{
lean_object* v___x_253_; uint8_t v___x_254_; 
lean_dec_ref(v_str_231_);
lean_dec(v___x_212_);
v___x_253_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_projectsRewritableOperand___closed__2));
v___x_254_ = lean_string_dec_eq(v_str_230_, v___x_253_);
lean_dec_ref(v_str_230_);
return v___x_254_;
}
}
}
}
else
{
uint8_t v___x_255_; 
lean_dec_ref_known(v_pre_217_, 2);
lean_dec_ref_known(v_pre_216_, 2);
lean_dec_ref_known(v_pre_215_, 2);
lean_dec_ref_known(v_declName_214_, 2);
lean_dec(v___x_212_);
v___x_255_ = 0;
return v___x_255_;
}
}
default: 
{
uint8_t v___x_256_; 
lean_dec_ref_known(v_pre_216_, 2);
lean_dec_ref_known(v_pre_215_, 2);
lean_dec_ref_known(v_declName_214_, 2);
lean_dec(v___x_212_);
v___x_256_ = 0;
return v___x_256_;
}
}
}
else
{
uint8_t v___x_257_; 
lean_dec(v_pre_216_);
lean_dec_ref_known(v_pre_215_, 2);
lean_dec_ref_known(v_declName_214_, 2);
lean_dec(v___x_212_);
v___x_257_ = 0;
return v___x_257_;
}
}
else
{
uint8_t v___x_258_; 
lean_dec_ref_known(v_declName_214_, 2);
lean_dec(v_pre_215_);
lean_dec(v___x_212_);
v___x_258_ = 0;
return v___x_258_;
}
}
else
{
uint8_t v___x_259_; 
lean_dec(v_declName_214_);
lean_dec(v___x_212_);
v___x_259_ = 0;
return v___x_259_;
}
}
else
{
uint8_t v___x_260_; 
lean_dec_ref(v___x_213_);
lean_dec(v___x_212_);
v___x_260_ = 0;
return v___x_260_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_projectsRewritableOperand___boxed(lean_object* v_rhs_261_){
_start:
{
uint8_t v_res_262_; lean_object* v_r_263_; 
v_res_262_ = l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_projectsRewritableOperand(v_rhs_261_);
v_r_263_ = lean_box(v_res_262_);
return v_r_263_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0_spec__2___redArg(lean_object* v_a_408_, lean_object* v_b_409_, lean_object* v_x_410_){
_start:
{
if (lean_obj_tag(v_x_410_) == 0)
{
lean_dec(v_b_409_);
lean_dec(v_a_408_);
return v_x_410_;
}
else
{
lean_object* v_key_411_; lean_object* v_value_412_; lean_object* v_tail_413_; lean_object* v___x_415_; uint8_t v_isShared_416_; uint8_t v_isSharedCheck_425_; 
v_key_411_ = lean_ctor_get(v_x_410_, 0);
v_value_412_ = lean_ctor_get(v_x_410_, 1);
v_tail_413_ = lean_ctor_get(v_x_410_, 2);
v_isSharedCheck_425_ = !lean_is_exclusive(v_x_410_);
if (v_isSharedCheck_425_ == 0)
{
v___x_415_ = v_x_410_;
v_isShared_416_ = v_isSharedCheck_425_;
goto v_resetjp_414_;
}
else
{
lean_inc(v_tail_413_);
lean_inc(v_value_412_);
lean_inc(v_key_411_);
lean_dec(v_x_410_);
v___x_415_ = lean_box(0);
v_isShared_416_ = v_isSharedCheck_425_;
goto v_resetjp_414_;
}
v_resetjp_414_:
{
uint8_t v___x_417_; 
v___x_417_ = lean_name_eq(v_key_411_, v_a_408_);
if (v___x_417_ == 0)
{
lean_object* v___x_418_; lean_object* v___x_420_; 
v___x_418_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0_spec__2___redArg(v_a_408_, v_b_409_, v_tail_413_);
if (v_isShared_416_ == 0)
{
lean_ctor_set(v___x_415_, 2, v___x_418_);
v___x_420_ = v___x_415_;
goto v_reusejp_419_;
}
else
{
lean_object* v_reuseFailAlloc_421_; 
v_reuseFailAlloc_421_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_421_, 0, v_key_411_);
lean_ctor_set(v_reuseFailAlloc_421_, 1, v_value_412_);
lean_ctor_set(v_reuseFailAlloc_421_, 2, v___x_418_);
v___x_420_ = v_reuseFailAlloc_421_;
goto v_reusejp_419_;
}
v_reusejp_419_:
{
return v___x_420_;
}
}
else
{
lean_object* v___x_423_; 
lean_dec(v_value_412_);
lean_dec(v_key_411_);
if (v_isShared_416_ == 0)
{
lean_ctor_set(v___x_415_, 1, v_b_409_);
lean_ctor_set(v___x_415_, 0, v_a_408_);
v___x_423_ = v___x_415_;
goto v_reusejp_422_;
}
else
{
lean_object* v_reuseFailAlloc_424_; 
v_reuseFailAlloc_424_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_424_, 0, v_a_408_);
lean_ctor_set(v_reuseFailAlloc_424_, 1, v_b_409_);
lean_ctor_set(v_reuseFailAlloc_424_, 2, v_tail_413_);
v___x_423_ = v_reuseFailAlloc_424_;
goto v_reusejp_422_;
}
v_reusejp_422_:
{
return v___x_423_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0_spec__1_spec__2_spec__4___redArg(lean_object* v_x_426_, lean_object* v_x_427_){
_start:
{
if (lean_obj_tag(v_x_427_) == 0)
{
return v_x_426_;
}
else
{
lean_object* v_key_428_; lean_object* v_value_429_; lean_object* v_tail_430_; lean_object* v___x_432_; uint8_t v_isShared_433_; uint8_t v_isSharedCheck_456_; 
v_key_428_ = lean_ctor_get(v_x_427_, 0);
v_value_429_ = lean_ctor_get(v_x_427_, 1);
v_tail_430_ = lean_ctor_get(v_x_427_, 2);
v_isSharedCheck_456_ = !lean_is_exclusive(v_x_427_);
if (v_isSharedCheck_456_ == 0)
{
v___x_432_ = v_x_427_;
v_isShared_433_ = v_isSharedCheck_456_;
goto v_resetjp_431_;
}
else
{
lean_inc(v_tail_430_);
lean_inc(v_value_429_);
lean_inc(v_key_428_);
lean_dec(v_x_427_);
v___x_432_ = lean_box(0);
v_isShared_433_ = v_isSharedCheck_456_;
goto v_resetjp_431_;
}
v_resetjp_431_:
{
lean_object* v___x_434_; uint64_t v___y_436_; 
v___x_434_ = lean_array_get_size(v_x_426_);
if (lean_obj_tag(v_key_428_) == 0)
{
uint64_t v___x_454_; 
v___x_454_ = 1723ULL;
v___y_436_ = v___x_454_;
goto v___jp_435_;
}
else
{
uint64_t v_hash_455_; 
v_hash_455_ = lean_ctor_get_uint64(v_key_428_, sizeof(void*)*2);
v___y_436_ = v_hash_455_;
goto v___jp_435_;
}
v___jp_435_:
{
uint64_t v___x_437_; uint64_t v___x_438_; uint64_t v_fold_439_; uint64_t v___x_440_; uint64_t v___x_441_; uint64_t v___x_442_; size_t v___x_443_; size_t v___x_444_; size_t v___x_445_; size_t v___x_446_; size_t v___x_447_; lean_object* v___x_448_; lean_object* v___x_450_; 
v___x_437_ = 32ULL;
v___x_438_ = lean_uint64_shift_right(v___y_436_, v___x_437_);
v_fold_439_ = lean_uint64_xor(v___y_436_, v___x_438_);
v___x_440_ = 16ULL;
v___x_441_ = lean_uint64_shift_right(v_fold_439_, v___x_440_);
v___x_442_ = lean_uint64_xor(v_fold_439_, v___x_441_);
v___x_443_ = lean_uint64_to_usize(v___x_442_);
v___x_444_ = lean_usize_of_nat(v___x_434_);
v___x_445_ = ((size_t)1ULL);
v___x_446_ = lean_usize_sub(v___x_444_, v___x_445_);
v___x_447_ = lean_usize_land(v___x_443_, v___x_446_);
v___x_448_ = lean_array_uget_borrowed(v_x_426_, v___x_447_);
lean_inc(v___x_448_);
if (v_isShared_433_ == 0)
{
lean_ctor_set(v___x_432_, 2, v___x_448_);
v___x_450_ = v___x_432_;
goto v_reusejp_449_;
}
else
{
lean_object* v_reuseFailAlloc_453_; 
v_reuseFailAlloc_453_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_453_, 0, v_key_428_);
lean_ctor_set(v_reuseFailAlloc_453_, 1, v_value_429_);
lean_ctor_set(v_reuseFailAlloc_453_, 2, v___x_448_);
v___x_450_ = v_reuseFailAlloc_453_;
goto v_reusejp_449_;
}
v_reusejp_449_:
{
lean_object* v___x_451_; 
v___x_451_ = lean_array_uset(v_x_426_, v___x_447_, v___x_450_);
v_x_426_ = v___x_451_;
v_x_427_ = v_tail_430_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0_spec__1_spec__2___redArg(lean_object* v_i_457_, lean_object* v_source_458_, lean_object* v_target_459_){
_start:
{
lean_object* v___x_460_; uint8_t v___x_461_; 
v___x_460_ = lean_array_get_size(v_source_458_);
v___x_461_ = lean_nat_dec_lt(v_i_457_, v___x_460_);
if (v___x_461_ == 0)
{
lean_dec_ref(v_source_458_);
lean_dec(v_i_457_);
return v_target_459_;
}
else
{
lean_object* v_es_462_; lean_object* v___x_463_; lean_object* v_source_464_; lean_object* v_target_465_; lean_object* v___x_466_; lean_object* v___x_467_; 
v_es_462_ = lean_array_fget(v_source_458_, v_i_457_);
v___x_463_ = lean_box(0);
v_source_464_ = lean_array_fset(v_source_458_, v_i_457_, v___x_463_);
v_target_465_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0_spec__1_spec__2_spec__4___redArg(v_target_459_, v_es_462_);
v___x_466_ = lean_unsigned_to_nat(1u);
v___x_467_ = lean_nat_add(v_i_457_, v___x_466_);
lean_dec(v_i_457_);
v_i_457_ = v___x_467_;
v_source_458_ = v_source_464_;
v_target_459_ = v_target_465_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0_spec__1___redArg(lean_object* v_data_469_){
_start:
{
lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v_nbuckets_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; 
v___x_470_ = lean_array_get_size(v_data_469_);
v___x_471_ = lean_unsigned_to_nat(2u);
v_nbuckets_472_ = lean_nat_mul(v___x_470_, v___x_471_);
v___x_473_ = lean_unsigned_to_nat(0u);
v___x_474_ = lean_box(0);
v___x_475_ = lean_mk_array(v_nbuckets_472_, v___x_474_);
v___x_476_ = lean_array_propagate_mark(v_data_469_, v___x_475_);
v___x_477_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0_spec__1_spec__2___redArg(v___x_473_, v_data_469_, v___x_476_);
return v___x_477_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0_spec__0___redArg(lean_object* v_a_478_, lean_object* v_x_479_){
_start:
{
if (lean_obj_tag(v_x_479_) == 0)
{
uint8_t v___x_480_; 
v___x_480_ = 0;
return v___x_480_;
}
else
{
lean_object* v_key_481_; lean_object* v_tail_482_; uint8_t v___x_483_; 
v_key_481_ = lean_ctor_get(v_x_479_, 0);
v_tail_482_ = lean_ctor_get(v_x_479_, 2);
v___x_483_ = lean_name_eq(v_key_481_, v_a_478_);
if (v___x_483_ == 0)
{
v_x_479_ = v_tail_482_;
goto _start;
}
else
{
return v___x_483_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0_spec__0___redArg___boxed(lean_object* v_a_485_, lean_object* v_x_486_){
_start:
{
uint8_t v_res_487_; lean_object* v_r_488_; 
v_res_487_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0_spec__0___redArg(v_a_485_, v_x_486_);
lean_dec(v_x_486_);
lean_dec(v_a_485_);
v_r_488_ = lean_box(v_res_487_);
return v_r_488_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0___redArg(lean_object* v_m_489_, lean_object* v_a_490_, lean_object* v_b_491_){
_start:
{
lean_object* v_size_492_; lean_object* v_buckets_493_; lean_object* v___x_495_; uint8_t v_isShared_496_; uint8_t v_isSharedCheck_539_; 
v_size_492_ = lean_ctor_get(v_m_489_, 0);
v_buckets_493_ = lean_ctor_get(v_m_489_, 1);
v_isSharedCheck_539_ = !lean_is_exclusive(v_m_489_);
if (v_isSharedCheck_539_ == 0)
{
v___x_495_ = v_m_489_;
v_isShared_496_ = v_isSharedCheck_539_;
goto v_resetjp_494_;
}
else
{
lean_inc(v_buckets_493_);
lean_inc(v_size_492_);
lean_dec(v_m_489_);
v___x_495_ = lean_box(0);
v_isShared_496_ = v_isSharedCheck_539_;
goto v_resetjp_494_;
}
v_resetjp_494_:
{
lean_object* v___x_497_; uint64_t v___y_499_; 
v___x_497_ = lean_array_get_size(v_buckets_493_);
if (lean_obj_tag(v_a_490_) == 0)
{
uint64_t v___x_537_; 
v___x_537_ = 1723ULL;
v___y_499_ = v___x_537_;
goto v___jp_498_;
}
else
{
uint64_t v_hash_538_; 
v_hash_538_ = lean_ctor_get_uint64(v_a_490_, sizeof(void*)*2);
v___y_499_ = v_hash_538_;
goto v___jp_498_;
}
v___jp_498_:
{
uint64_t v___x_500_; uint64_t v___x_501_; uint64_t v_fold_502_; uint64_t v___x_503_; uint64_t v___x_504_; uint64_t v___x_505_; size_t v___x_506_; size_t v___x_507_; size_t v___x_508_; size_t v___x_509_; size_t v___x_510_; lean_object* v_bkt_511_; uint8_t v___x_512_; 
v___x_500_ = 32ULL;
v___x_501_ = lean_uint64_shift_right(v___y_499_, v___x_500_);
v_fold_502_ = lean_uint64_xor(v___y_499_, v___x_501_);
v___x_503_ = 16ULL;
v___x_504_ = lean_uint64_shift_right(v_fold_502_, v___x_503_);
v___x_505_ = lean_uint64_xor(v_fold_502_, v___x_504_);
v___x_506_ = lean_uint64_to_usize(v___x_505_);
v___x_507_ = lean_usize_of_nat(v___x_497_);
v___x_508_ = ((size_t)1ULL);
v___x_509_ = lean_usize_sub(v___x_507_, v___x_508_);
v___x_510_ = lean_usize_land(v___x_506_, v___x_509_);
v_bkt_511_ = lean_array_uget_borrowed(v_buckets_493_, v___x_510_);
v___x_512_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0_spec__0___redArg(v_a_490_, v_bkt_511_);
if (v___x_512_ == 0)
{
lean_object* v___x_513_; lean_object* v_size_x27_514_; lean_object* v___x_515_; lean_object* v_buckets_x27_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; uint8_t v___x_522_; 
v___x_513_ = lean_unsigned_to_nat(1u);
v_size_x27_514_ = lean_nat_add(v_size_492_, v___x_513_);
lean_dec(v_size_492_);
lean_inc(v_bkt_511_);
v___x_515_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_515_, 0, v_a_490_);
lean_ctor_set(v___x_515_, 1, v_b_491_);
lean_ctor_set(v___x_515_, 2, v_bkt_511_);
v_buckets_x27_516_ = lean_array_uset(v_buckets_493_, v___x_510_, v___x_515_);
v___x_517_ = lean_unsigned_to_nat(4u);
v___x_518_ = lean_nat_mul(v_size_x27_514_, v___x_517_);
v___x_519_ = lean_unsigned_to_nat(3u);
v___x_520_ = lean_nat_div(v___x_518_, v___x_519_);
lean_dec(v___x_518_);
v___x_521_ = lean_array_get_size(v_buckets_x27_516_);
v___x_522_ = lean_nat_dec_le(v___x_520_, v___x_521_);
lean_dec(v___x_520_);
if (v___x_522_ == 0)
{
lean_object* v_val_523_; lean_object* v___x_525_; 
v_val_523_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0_spec__1___redArg(v_buckets_x27_516_);
if (v_isShared_496_ == 0)
{
lean_ctor_set(v___x_495_, 1, v_val_523_);
lean_ctor_set(v___x_495_, 0, v_size_x27_514_);
v___x_525_ = v___x_495_;
goto v_reusejp_524_;
}
else
{
lean_object* v_reuseFailAlloc_526_; 
v_reuseFailAlloc_526_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_526_, 0, v_size_x27_514_);
lean_ctor_set(v_reuseFailAlloc_526_, 1, v_val_523_);
v___x_525_ = v_reuseFailAlloc_526_;
goto v_reusejp_524_;
}
v_reusejp_524_:
{
return v___x_525_;
}
}
else
{
lean_object* v___x_528_; 
if (v_isShared_496_ == 0)
{
lean_ctor_set(v___x_495_, 1, v_buckets_x27_516_);
lean_ctor_set(v___x_495_, 0, v_size_x27_514_);
v___x_528_ = v___x_495_;
goto v_reusejp_527_;
}
else
{
lean_object* v_reuseFailAlloc_529_; 
v_reuseFailAlloc_529_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_529_, 0, v_size_x27_514_);
lean_ctor_set(v_reuseFailAlloc_529_, 1, v_buckets_x27_516_);
v___x_528_ = v_reuseFailAlloc_529_;
goto v_reusejp_527_;
}
v_reusejp_527_:
{
return v___x_528_;
}
}
}
else
{
lean_object* v___x_530_; lean_object* v_buckets_x27_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_535_; 
lean_inc(v_bkt_511_);
v___x_530_ = lean_box(0);
v_buckets_x27_531_ = lean_array_uset(v_buckets_493_, v___x_510_, v___x_530_);
v___x_532_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0_spec__2___redArg(v_a_490_, v_b_491_, v_bkt_511_);
v___x_533_ = lean_array_uset(v_buckets_x27_531_, v___x_510_, v___x_532_);
if (v_isShared_496_ == 0)
{
lean_ctor_set(v___x_495_, 1, v___x_533_);
v___x_535_ = v___x_495_;
goto v_reusejp_534_;
}
else
{
lean_object* v_reuseFailAlloc_536_; 
v_reuseFailAlloc_536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_536_, 0, v_size_492_);
lean_ctor_set(v_reuseFailAlloc_536_, 1, v___x_533_);
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
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__1(lean_object* v_as_540_, size_t v_i_541_, size_t v_stop_542_, lean_object* v_b_543_){
_start:
{
uint8_t v___x_544_; 
v___x_544_ = lean_usize_dec_eq(v_i_541_, v_stop_542_);
if (v___x_544_ == 0)
{
lean_object* v___x_545_; lean_object* v_head_546_; lean_object* v___x_547_; size_t v___x_548_; size_t v___x_549_; 
v___x_545_ = lean_array_uget_borrowed(v_as_540_, v_i_541_);
v_head_546_ = lean_ctor_get(v___x_545_, 0);
lean_inc(v___x_545_);
lean_inc(v_head_546_);
v___x_547_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0___redArg(v_b_543_, v_head_546_, v___x_545_);
v___x_548_ = ((size_t)1ULL);
v___x_549_ = lean_usize_add(v_i_541_, v___x_548_);
v_i_541_ = v___x_549_;
v_b_543_ = v___x_547_;
goto _start;
}
else
{
return v_b_543_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__1___boxed(lean_object* v_as_551_, lean_object* v_i_552_, lean_object* v_stop_553_, lean_object* v_b_554_){
_start:
{
size_t v_i_boxed_555_; size_t v_stop_boxed_556_; lean_object* v_res_557_; 
v_i_boxed_555_ = lean_unbox_usize(v_i_552_);
lean_dec(v_i_552_);
v_stop_boxed_556_ = lean_unbox_usize(v_stop_553_);
lean_dec(v_stop_553_);
v_res_557_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__1(v_as_551_, v_i_boxed_555_, v_stop_boxed_556_, v_b_554_);
lean_dec_ref(v_as_551_);
return v_res_557_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_latticeOps___closed__0(void){
_start:
{
lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; 
v___x_558_ = lean_box(0);
v___x_559_ = lean_unsigned_to_nat(16u);
v___x_560_ = lean_mk_array(v___x_559_, v___x_558_);
return v___x_560_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_latticeOps___closed__1(void){
_start:
{
lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; 
v___x_561_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_latticeOps___closed__0, &l_Lean_Elab_Tactic_VCGen_latticeOps___closed__0_once, _init_l_Lean_Elab_Tactic_VCGen_latticeOps___closed__0);
v___x_562_ = lean_unsigned_to_nat(0u);
v___x_563_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_563_, 0, v___x_562_);
lean_ctor_set(v___x_563_, 1, v___x_561_);
return v___x_563_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_latticeOps___closed__2(void){
_start:
{
lean_object* v___x_564_; lean_object* v___x_565_; 
v___x_564_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_builtinLatticeOps));
v___x_565_ = lean_array_get_size(v___x_564_);
return v___x_565_;
}
}
static uint8_t _init_l_Lean_Elab_Tactic_VCGen_latticeOps___closed__3(void){
_start:
{
lean_object* v___x_566_; lean_object* v___x_567_; uint8_t v___x_568_; 
v___x_566_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_latticeOps___closed__2, &l_Lean_Elab_Tactic_VCGen_latticeOps___closed__2_once, _init_l_Lean_Elab_Tactic_VCGen_latticeOps___closed__2);
v___x_567_ = lean_unsigned_to_nat(0u);
v___x_568_ = lean_nat_dec_lt(v___x_567_, v___x_566_);
return v___x_568_;
}
}
static uint8_t _init_l_Lean_Elab_Tactic_VCGen_latticeOps___closed__4(void){
_start:
{
lean_object* v___x_569_; uint8_t v___x_570_; 
v___x_569_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_latticeOps___closed__2, &l_Lean_Elab_Tactic_VCGen_latticeOps___closed__2_once, _init_l_Lean_Elab_Tactic_VCGen_latticeOps___closed__2);
v___x_570_ = lean_nat_dec_le(v___x_569_, v___x_569_);
return v___x_570_;
}
}
static size_t _init_l_Lean_Elab_Tactic_VCGen_latticeOps___closed__5(void){
_start:
{
lean_object* v___x_571_; size_t v___x_572_; 
v___x_571_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_latticeOps___closed__2, &l_Lean_Elab_Tactic_VCGen_latticeOps___closed__2_once, _init_l_Lean_Elab_Tactic_VCGen_latticeOps___closed__2);
v___x_572_ = lean_usize_of_nat(v___x_571_);
return v___x_572_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_latticeOps___closed__6(void){
_start:
{
lean_object* v___x_573_; size_t v___x_574_; size_t v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; 
v___x_573_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_latticeOps___closed__1, &l_Lean_Elab_Tactic_VCGen_latticeOps___closed__1_once, _init_l_Lean_Elab_Tactic_VCGen_latticeOps___closed__1);
v___x_574_ = lean_usize_once(&l_Lean_Elab_Tactic_VCGen_latticeOps___closed__5, &l_Lean_Elab_Tactic_VCGen_latticeOps___closed__5_once, _init_l_Lean_Elab_Tactic_VCGen_latticeOps___closed__5);
v___x_575_ = ((size_t)0ULL);
v___x_576_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_builtinLatticeOps));
v___x_577_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__1(v___x_576_, v___x_575_, v___x_574_, v___x_573_);
return v___x_577_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_latticeOps(void){
_start:
{
lean_object* v___x_578_; uint8_t v___x_579_; 
v___x_578_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_latticeOps___closed__1, &l_Lean_Elab_Tactic_VCGen_latticeOps___closed__1_once, _init_l_Lean_Elab_Tactic_VCGen_latticeOps___closed__1);
v___x_579_ = lean_uint8_once(&l_Lean_Elab_Tactic_VCGen_latticeOps___closed__3, &l_Lean_Elab_Tactic_VCGen_latticeOps___closed__3_once, _init_l_Lean_Elab_Tactic_VCGen_latticeOps___closed__3);
if (v___x_579_ == 0)
{
return v___x_578_;
}
else
{
uint8_t v___x_580_; 
v___x_580_ = lean_uint8_once(&l_Lean_Elab_Tactic_VCGen_latticeOps___closed__4, &l_Lean_Elab_Tactic_VCGen_latticeOps___closed__4_once, _init_l_Lean_Elab_Tactic_VCGen_latticeOps___closed__4);
if (v___x_580_ == 0)
{
if (v___x_579_ == 0)
{
return v___x_578_;
}
else
{
lean_object* v___x_581_; 
v___x_581_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_latticeOps___closed__6, &l_Lean_Elab_Tactic_VCGen_latticeOps___closed__6_once, _init_l_Lean_Elab_Tactic_VCGen_latticeOps___closed__6);
return v___x_581_;
}
}
else
{
lean_object* v___x_582_; 
v___x_582_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_latticeOps___closed__6, &l_Lean_Elab_Tactic_VCGen_latticeOps___closed__6_once, _init_l_Lean_Elab_Tactic_VCGen_latticeOps___closed__6);
return v___x_582_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0(lean_object* v_00_u03b2_583_, lean_object* v_m_584_, lean_object* v_a_585_, lean_object* v_b_586_){
_start:
{
lean_object* v___x_587_; 
v___x_587_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0___redArg(v_m_584_, v_a_585_, v_b_586_);
return v___x_587_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0_spec__0(lean_object* v_00_u03b2_588_, lean_object* v_a_589_, lean_object* v_x_590_){
_start:
{
uint8_t v___x_591_; 
v___x_591_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0_spec__0___redArg(v_a_589_, v_x_590_);
return v___x_591_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0_spec__0___boxed(lean_object* v_00_u03b2_592_, lean_object* v_a_593_, lean_object* v_x_594_){
_start:
{
uint8_t v_res_595_; lean_object* v_r_596_; 
v_res_595_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0_spec__0(v_00_u03b2_592_, v_a_593_, v_x_594_);
lean_dec(v_x_594_);
lean_dec(v_a_593_);
v_r_596_ = lean_box(v_res_595_);
return v_r_596_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0_spec__1(lean_object* v_00_u03b2_597_, lean_object* v_data_598_){
_start:
{
lean_object* v___x_599_; 
v___x_599_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0_spec__1___redArg(v_data_598_);
return v___x_599_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0_spec__2(lean_object* v_00_u03b2_600_, lean_object* v_a_601_, lean_object* v_b_602_, lean_object* v_x_603_){
_start:
{
lean_object* v___x_604_; 
v___x_604_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0_spec__2___redArg(v_a_601_, v_b_602_, v_x_603_);
return v___x_604_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_605_, lean_object* v_i_606_, lean_object* v_source_607_, lean_object* v_target_608_){
_start:
{
lean_object* v___x_609_; 
v___x_609_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0_spec__1_spec__2___redArg(v_i_606_, v_source_607_, v_target_608_);
return v___x_609_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_610_, lean_object* v_x_611_, lean_object* v_x_612_){
_start:
{
lean_object* v___x_613_; 
v___x_613_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0_spec__1_spec__2_spec__4___redArg(v_x_611_, v_x_612_);
return v___x_613_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__0___redArg(lean_object* v_e_614_, lean_object* v___y_615_){
_start:
{
uint8_t v___x_617_; 
v___x_617_ = l_Lean_Expr_hasMVar(v_e_614_);
if (v___x_617_ == 0)
{
lean_object* v___x_618_; 
v___x_618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_618_, 0, v_e_614_);
return v___x_618_;
}
else
{
lean_object* v___x_619_; lean_object* v_mctx_620_; lean_object* v___x_621_; lean_object* v_fst_622_; lean_object* v_snd_623_; lean_object* v___x_624_; lean_object* v_cache_625_; lean_object* v_zetaDeltaFVarIds_626_; lean_object* v_postponed_627_; lean_object* v_diag_628_; lean_object* v___x_630_; uint8_t v_isShared_631_; uint8_t v_isSharedCheck_637_; 
v___x_619_ = lean_st_ref_get(v___y_615_);
v_mctx_620_ = lean_ctor_get(v___x_619_, 0);
lean_inc_ref(v_mctx_620_);
lean_dec(v___x_619_);
v___x_621_ = l_Lean_instantiateMVarsCore(v_mctx_620_, v_e_614_);
v_fst_622_ = lean_ctor_get(v___x_621_, 0);
lean_inc(v_fst_622_);
v_snd_623_ = lean_ctor_get(v___x_621_, 1);
lean_inc(v_snd_623_);
lean_dec_ref(v___x_621_);
v___x_624_ = lean_st_ref_take(v___y_615_);
v_cache_625_ = lean_ctor_get(v___x_624_, 1);
v_zetaDeltaFVarIds_626_ = lean_ctor_get(v___x_624_, 2);
v_postponed_627_ = lean_ctor_get(v___x_624_, 3);
v_diag_628_ = lean_ctor_get(v___x_624_, 4);
v_isSharedCheck_637_ = !lean_is_exclusive(v___x_624_);
if (v_isSharedCheck_637_ == 0)
{
lean_object* v_unused_638_; 
v_unused_638_ = lean_ctor_get(v___x_624_, 0);
lean_dec(v_unused_638_);
v___x_630_ = v___x_624_;
v_isShared_631_ = v_isSharedCheck_637_;
goto v_resetjp_629_;
}
else
{
lean_inc(v_diag_628_);
lean_inc(v_postponed_627_);
lean_inc(v_zetaDeltaFVarIds_626_);
lean_inc(v_cache_625_);
lean_dec(v___x_624_);
v___x_630_ = lean_box(0);
v_isShared_631_ = v_isSharedCheck_637_;
goto v_resetjp_629_;
}
v_resetjp_629_:
{
lean_object* v___x_633_; 
if (v_isShared_631_ == 0)
{
lean_ctor_set(v___x_630_, 0, v_snd_623_);
v___x_633_ = v___x_630_;
goto v_reusejp_632_;
}
else
{
lean_object* v_reuseFailAlloc_636_; 
v_reuseFailAlloc_636_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_636_, 0, v_snd_623_);
lean_ctor_set(v_reuseFailAlloc_636_, 1, v_cache_625_);
lean_ctor_set(v_reuseFailAlloc_636_, 2, v_zetaDeltaFVarIds_626_);
lean_ctor_set(v_reuseFailAlloc_636_, 3, v_postponed_627_);
lean_ctor_set(v_reuseFailAlloc_636_, 4, v_diag_628_);
v___x_633_ = v_reuseFailAlloc_636_;
goto v_reusejp_632_;
}
v_reusejp_632_:
{
lean_object* v___x_634_; lean_object* v___x_635_; 
v___x_634_ = lean_st_ref_put(v___y_615_, v___x_633_);
v___x_635_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_635_, 0, v_fst_622_);
return v___x_635_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__0___redArg___boxed(lean_object* v_e_639_, lean_object* v___y_640_, lean_object* v___y_641_){
_start:
{
lean_object* v_res_642_; 
v_res_642_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__0___redArg(v_e_639_, v___y_640_);
lean_dec(v___y_640_);
return v_res_642_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__0(lean_object* v_e_643_, lean_object* v___y_644_, lean_object* v___y_645_, lean_object* v___y_646_, lean_object* v___y_647_){
_start:
{
lean_object* v___x_649_; 
v___x_649_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__0___redArg(v_e_643_, v___y_645_);
return v___x_649_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__0___boxed(lean_object* v_e_650_, lean_object* v___y_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_){
_start:
{
lean_object* v_res_656_; 
v_res_656_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__0(v_e_650_, v___y_651_, v___y_652_, v___y_653_, v___y_654_);
lean_dec(v___y_654_);
lean_dec_ref(v___y_653_);
lean_dec(v___y_652_);
lean_dec_ref(v___y_651_);
return v_res_656_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__1_spec__1(lean_object* v_msgData_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_){
_start:
{
lean_object* v___x_663_; lean_object* v_env_664_; lean_object* v___x_665_; lean_object* v_toCold_666_; lean_object* v_mctx_667_; lean_object* v_lctx_668_; lean_object* v_options_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; 
v___x_663_ = lean_st_ref_get(v___y_661_);
v_env_664_ = lean_ctor_get(v___x_663_, 0);
lean_inc_ref(v_env_664_);
lean_dec(v___x_663_);
v___x_665_ = lean_st_ref_get(v___y_659_);
v_toCold_666_ = lean_ctor_get(v___y_660_, 0);
v_mctx_667_ = lean_ctor_get(v___x_665_, 0);
lean_inc_ref(v_mctx_667_);
lean_dec(v___x_665_);
v_lctx_668_ = lean_ctor_get(v___y_658_, 2);
v_options_669_ = lean_ctor_get(v_toCold_666_, 2);
lean_inc_ref(v_options_669_);
lean_inc_ref(v_lctx_668_);
v___x_670_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_670_, 0, v_env_664_);
lean_ctor_set(v___x_670_, 1, v_mctx_667_);
lean_ctor_set(v___x_670_, 2, v_lctx_668_);
lean_ctor_set(v___x_670_, 3, v_options_669_);
v___x_671_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_671_, 0, v___x_670_);
lean_ctor_set(v___x_671_, 1, v_msgData_657_);
v___x_672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_672_, 0, v___x_671_);
return v___x_672_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__1_spec__1___boxed(lean_object* v_msgData_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_){
_start:
{
lean_object* v_res_679_; 
v_res_679_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__1_spec__1(v_msgData_673_, v___y_674_, v___y_675_, v___y_676_, v___y_677_);
lean_dec(v___y_677_);
lean_dec_ref(v___y_676_);
lean_dec(v___y_675_);
lean_dec_ref(v___y_674_);
return v_res_679_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__1___redArg(lean_object* v_msg_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_){
_start:
{
lean_object* v_ref_686_; lean_object* v___x_687_; lean_object* v_a_688_; lean_object* v___x_690_; uint8_t v_isShared_691_; uint8_t v_isSharedCheck_696_; 
v_ref_686_ = lean_ctor_get(v___y_683_, 2);
v___x_687_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__1_spec__1(v_msg_680_, v___y_681_, v___y_682_, v___y_683_, v___y_684_);
v_a_688_ = lean_ctor_get(v___x_687_, 0);
v_isSharedCheck_696_ = !lean_is_exclusive(v___x_687_);
if (v_isSharedCheck_696_ == 0)
{
v___x_690_ = v___x_687_;
v_isShared_691_ = v_isSharedCheck_696_;
goto v_resetjp_689_;
}
else
{
lean_inc(v_a_688_);
lean_dec(v___x_687_);
v___x_690_ = lean_box(0);
v_isShared_691_ = v_isSharedCheck_696_;
goto v_resetjp_689_;
}
v_resetjp_689_:
{
lean_object* v___x_692_; lean_object* v___x_694_; 
lean_inc(v_ref_686_);
v___x_692_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_692_, 0, v_ref_686_);
lean_ctor_set(v___x_692_, 1, v_a_688_);
if (v_isShared_691_ == 0)
{
lean_ctor_set_tag(v___x_690_, 1);
lean_ctor_set(v___x_690_, 0, v___x_692_);
v___x_694_ = v___x_690_;
goto v_reusejp_693_;
}
else
{
lean_object* v_reuseFailAlloc_695_; 
v_reuseFailAlloc_695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_695_, 0, v___x_692_);
v___x_694_ = v_reuseFailAlloc_695_;
goto v_reusejp_693_;
}
v_reusejp_693_:
{
return v___x_694_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__1___redArg___boxed(lean_object* v_msg_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_){
_start:
{
lean_object* v_res_703_; 
v_res_703_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__1___redArg(v_msg_697_, v___y_698_, v___y_699_, v___y_700_, v___y_701_);
lean_dec(v___y_701_);
lean_dec_ref(v___y_700_);
lean_dec(v___y_699_);
lean_dec_ref(v___y_698_);
return v_res_703_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__4(void){
_start:
{
lean_object* v___x_712_; lean_object* v___x_713_; 
v___x_712_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__3));
v___x_713_ = l_Lean_stringToMessageData(v___x_712_);
return v___x_713_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__6(void){
_start:
{
lean_object* v___x_715_; lean_object* v___x_716_; 
v___x_715_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__5));
v___x_716_ = l_Lean_stringToMessageData(v___x_715_);
return v___x_716_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__8(void){
_start:
{
lean_object* v___x_718_; lean_object* v___x_719_; 
v___x_718_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__7));
v___x_719_ = l_Lean_stringToMessageData(v___x_718_);
return v___x_719_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2(lean_object* v_as_720_, size_t v_sz_721_, size_t v_i_722_, lean_object* v_b_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_){
_start:
{
lean_object* v_a_730_; uint8_t v___x_734_; 
v___x_734_ = lean_usize_dec_lt(v_i_722_, v_sz_721_);
if (v___x_734_ == 0)
{
lean_object* v___x_735_; 
v___x_735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_735_, 0, v_b_723_);
return v___x_735_;
}
else
{
lean_object* v_a_736_; lean_object* v___x_737_; 
v_a_736_ = lean_array_uget_borrowed(v_as_720_, v_i_722_);
lean_inc(v_a_736_);
v___x_737_ = l_Lean_Meta_mkConstWithFreshMVarLevels(v_a_736_, v___y_724_, v___y_725_, v___y_726_, v___y_727_);
if (lean_obj_tag(v___x_737_) == 0)
{
lean_object* v_a_738_; lean_object* v___x_739_; 
v_a_738_ = lean_ctor_get(v___x_737_, 0);
lean_inc(v_a_738_);
lean_dec_ref_known(v___x_737_, 1);
lean_inc(v___y_727_);
lean_inc_ref(v___y_726_);
lean_inc(v___y_725_);
lean_inc_ref(v___y_724_);
v___x_739_ = lean_infer_type(v_a_738_, v___y_724_, v___y_725_, v___y_726_, v___y_727_);
if (lean_obj_tag(v___x_739_) == 0)
{
lean_object* v_a_740_; lean_object* v___x_741_; uint8_t v___x_742_; lean_object* v___x_743_; 
v_a_740_ = lean_ctor_get(v___x_739_, 0);
lean_inc(v_a_740_);
lean_dec_ref_known(v___x_739_, 1);
v___x_741_ = lean_box(0);
v___x_742_ = 0;
v___x_743_ = l_Lean_Meta_forallMetaTelescopeReducing(v_a_740_, v___x_741_, v___x_742_, v___y_724_, v___y_725_, v___y_726_, v___y_727_);
if (lean_obj_tag(v___x_743_) == 0)
{
lean_object* v_a_744_; lean_object* v_snd_745_; lean_object* v___x_747_; uint8_t v_isShared_748_; uint8_t v_isSharedCheck_809_; 
v_a_744_ = lean_ctor_get(v___x_743_, 0);
lean_inc(v_a_744_);
lean_dec_ref_known(v___x_743_, 1);
v_snd_745_ = lean_ctor_get(v_a_744_, 1);
v_isSharedCheck_809_ = !lean_is_exclusive(v_a_744_);
if (v_isSharedCheck_809_ == 0)
{
lean_object* v_unused_810_; 
v_unused_810_ = lean_ctor_get(v_a_744_, 0);
lean_dec(v_unused_810_);
v___x_747_ = v_a_744_;
v_isShared_748_ = v_isSharedCheck_809_;
goto v_resetjp_746_;
}
else
{
lean_inc(v_snd_745_);
lean_dec(v_a_744_);
v___x_747_ = lean_box(0);
v_isShared_748_ = v_isSharedCheck_809_;
goto v_resetjp_746_;
}
v_resetjp_746_:
{
lean_object* v_snd_749_; lean_object* v___x_751_; uint8_t v_isShared_752_; uint8_t v_isSharedCheck_807_; 
v_snd_749_ = lean_ctor_get(v_snd_745_, 1);
v_isSharedCheck_807_ = !lean_is_exclusive(v_snd_745_);
if (v_isSharedCheck_807_ == 0)
{
lean_object* v_unused_808_; 
v_unused_808_ = lean_ctor_get(v_snd_745_, 0);
lean_dec(v_unused_808_);
v___x_751_ = v_snd_745_;
v_isShared_752_ = v_isSharedCheck_807_;
goto v_resetjp_750_;
}
else
{
lean_inc(v_snd_749_);
lean_dec(v_snd_745_);
v___x_751_ = lean_box(0);
v_isShared_752_ = v_isSharedCheck_807_;
goto v_resetjp_750_;
}
v_resetjp_750_:
{
lean_object* v___x_753_; 
v___x_753_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__0___redArg(v_snd_749_, v___y_725_);
if (lean_obj_tag(v___x_753_) == 0)
{
lean_object* v_a_754_; lean_object* v___x_755_; lean_object* v___x_756_; uint8_t v___x_757_; 
v_a_754_ = lean_ctor_get(v___x_753_, 0);
lean_inc(v_a_754_);
lean_dec_ref_known(v___x_753_, 1);
v___x_755_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__2));
v___x_756_ = lean_unsigned_to_nat(4u);
v___x_757_ = l_Lean_Expr_isAppOfArity(v_a_754_, v___x_755_, v___x_756_);
if (v___x_757_ == 0)
{
lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_761_; 
lean_dec(v_a_754_);
lean_del_object(v___x_751_);
v___x_758_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__4);
lean_inc(v_a_736_);
v___x_759_ = l_Lean_MessageData_ofName(v_a_736_);
if (v_isShared_748_ == 0)
{
lean_ctor_set_tag(v___x_747_, 7);
lean_ctor_set(v___x_747_, 1, v___x_759_);
lean_ctor_set(v___x_747_, 0, v___x_758_);
v___x_761_ = v___x_747_;
goto v_reusejp_760_;
}
else
{
lean_object* v_reuseFailAlloc_773_; 
v_reuseFailAlloc_773_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_773_, 0, v___x_758_);
lean_ctor_set(v_reuseFailAlloc_773_, 1, v___x_759_);
v___x_761_ = v_reuseFailAlloc_773_;
goto v_reusejp_760_;
}
v_reusejp_760_:
{
lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; 
v___x_762_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__6);
v___x_763_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_763_, 0, v___x_761_);
lean_ctor_set(v___x_763_, 1, v___x_762_);
v___x_764_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__1___redArg(v___x_763_, v___y_724_, v___y_725_, v___y_726_, v___y_727_);
if (lean_obj_tag(v___x_764_) == 0)
{
lean_dec_ref_known(v___x_764_, 1);
v_a_730_ = v_b_723_;
goto v___jp_729_;
}
else
{
lean_object* v_a_765_; lean_object* v___x_767_; uint8_t v_isShared_768_; uint8_t v_isSharedCheck_772_; 
lean_dec_ref(v_b_723_);
v_a_765_ = lean_ctor_get(v___x_764_, 0);
v_isSharedCheck_772_ = !lean_is_exclusive(v___x_764_);
if (v_isSharedCheck_772_ == 0)
{
v___x_767_ = v___x_764_;
v_isShared_768_ = v_isSharedCheck_772_;
goto v_resetjp_766_;
}
else
{
lean_inc(v_a_765_);
lean_dec(v___x_764_);
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
else
{
lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; 
v___x_774_ = l_Lean_Expr_appArg_x21(v_a_754_);
lean_dec(v_a_754_);
v___x_775_ = l_Lean_Expr_getAppFn(v___x_774_);
v___x_776_ = l_Lean_Expr_constName_x3f(v___x_775_);
lean_dec_ref(v___x_775_);
if (lean_obj_tag(v___x_776_) == 1)
{
lean_object* v_val_777_; lean_object* v___x_778_; lean_object* v___x_780_; 
lean_del_object(v___x_747_);
v_val_777_ = lean_ctor_get(v___x_776_, 0);
lean_inc(v_val_777_);
lean_dec_ref_known(v___x_776_, 1);
v___x_778_ = l_Lean_Expr_getAppNumArgs(v___x_774_);
lean_dec_ref(v___x_774_);
lean_inc(v_a_736_);
if (v_isShared_752_ == 0)
{
lean_ctor_set(v___x_751_, 1, v___x_778_);
lean_ctor_set(v___x_751_, 0, v_a_736_);
v___x_780_ = v___x_751_;
goto v_reusejp_779_;
}
else
{
lean_object* v_reuseFailAlloc_782_; 
v_reuseFailAlloc_782_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_782_, 0, v_a_736_);
lean_ctor_set(v_reuseFailAlloc_782_, 1, v___x_778_);
v___x_780_ = v_reuseFailAlloc_782_;
goto v_reusejp_779_;
}
v_reusejp_779_:
{
lean_object* v___x_781_; 
v___x_781_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0___redArg(v_b_723_, v_val_777_, v___x_780_);
v_a_730_ = v___x_781_;
goto v___jp_729_;
}
}
else
{
lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_786_; 
lean_dec(v___x_776_);
lean_dec_ref(v___x_774_);
lean_del_object(v___x_751_);
v___x_783_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__4);
lean_inc(v_a_736_);
v___x_784_ = l_Lean_MessageData_ofName(v_a_736_);
if (v_isShared_748_ == 0)
{
lean_ctor_set_tag(v___x_747_, 7);
lean_ctor_set(v___x_747_, 1, v___x_784_);
lean_ctor_set(v___x_747_, 0, v___x_783_);
v___x_786_ = v___x_747_;
goto v_reusejp_785_;
}
else
{
lean_object* v_reuseFailAlloc_798_; 
v_reuseFailAlloc_798_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_798_, 0, v___x_783_);
lean_ctor_set(v_reuseFailAlloc_798_, 1, v___x_784_);
v___x_786_ = v_reuseFailAlloc_798_;
goto v_reusejp_785_;
}
v_reusejp_785_:
{
lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; 
v___x_787_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__8);
v___x_788_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_788_, 0, v___x_786_);
lean_ctor_set(v___x_788_, 1, v___x_787_);
v___x_789_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__1___redArg(v___x_788_, v___y_724_, v___y_725_, v___y_726_, v___y_727_);
if (lean_obj_tag(v___x_789_) == 0)
{
lean_dec_ref_known(v___x_789_, 1);
v_a_730_ = v_b_723_;
goto v___jp_729_;
}
else
{
lean_object* v_a_790_; lean_object* v___x_792_; uint8_t v_isShared_793_; uint8_t v_isSharedCheck_797_; 
lean_dec_ref(v_b_723_);
v_a_790_ = lean_ctor_get(v___x_789_, 0);
v_isSharedCheck_797_ = !lean_is_exclusive(v___x_789_);
if (v_isSharedCheck_797_ == 0)
{
v___x_792_ = v___x_789_;
v_isShared_793_ = v_isSharedCheck_797_;
goto v_resetjp_791_;
}
else
{
lean_inc(v_a_790_);
lean_dec(v___x_789_);
v___x_792_ = lean_box(0);
v_isShared_793_ = v_isSharedCheck_797_;
goto v_resetjp_791_;
}
v_resetjp_791_:
{
lean_object* v___x_795_; 
if (v_isShared_793_ == 0)
{
v___x_795_ = v___x_792_;
goto v_reusejp_794_;
}
else
{
lean_object* v_reuseFailAlloc_796_; 
v_reuseFailAlloc_796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_796_, 0, v_a_790_);
v___x_795_ = v_reuseFailAlloc_796_;
goto v_reusejp_794_;
}
v_reusejp_794_:
{
return v___x_795_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_799_; lean_object* v___x_801_; uint8_t v_isShared_802_; uint8_t v_isSharedCheck_806_; 
lean_del_object(v___x_751_);
lean_del_object(v___x_747_);
lean_dec_ref(v_b_723_);
v_a_799_ = lean_ctor_get(v___x_753_, 0);
v_isSharedCheck_806_ = !lean_is_exclusive(v___x_753_);
if (v_isSharedCheck_806_ == 0)
{
v___x_801_ = v___x_753_;
v_isShared_802_ = v_isSharedCheck_806_;
goto v_resetjp_800_;
}
else
{
lean_inc(v_a_799_);
lean_dec(v___x_753_);
v___x_801_ = lean_box(0);
v_isShared_802_ = v_isSharedCheck_806_;
goto v_resetjp_800_;
}
v_resetjp_800_:
{
lean_object* v___x_804_; 
if (v_isShared_802_ == 0)
{
v___x_804_ = v___x_801_;
goto v_reusejp_803_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v_a_799_);
v___x_804_ = v_reuseFailAlloc_805_;
goto v_reusejp_803_;
}
v_reusejp_803_:
{
return v___x_804_;
}
}
}
}
}
}
else
{
lean_object* v_a_811_; lean_object* v___x_813_; uint8_t v_isShared_814_; uint8_t v_isSharedCheck_818_; 
lean_dec_ref(v_b_723_);
v_a_811_ = lean_ctor_get(v___x_743_, 0);
v_isSharedCheck_818_ = !lean_is_exclusive(v___x_743_);
if (v_isSharedCheck_818_ == 0)
{
v___x_813_ = v___x_743_;
v_isShared_814_ = v_isSharedCheck_818_;
goto v_resetjp_812_;
}
else
{
lean_inc(v_a_811_);
lean_dec(v___x_743_);
v___x_813_ = lean_box(0);
v_isShared_814_ = v_isSharedCheck_818_;
goto v_resetjp_812_;
}
v_resetjp_812_:
{
lean_object* v___x_816_; 
if (v_isShared_814_ == 0)
{
v___x_816_ = v___x_813_;
goto v_reusejp_815_;
}
else
{
lean_object* v_reuseFailAlloc_817_; 
v_reuseFailAlloc_817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_817_, 0, v_a_811_);
v___x_816_ = v_reuseFailAlloc_817_;
goto v_reusejp_815_;
}
v_reusejp_815_:
{
return v___x_816_;
}
}
}
}
else
{
lean_object* v_a_819_; lean_object* v___x_821_; uint8_t v_isShared_822_; uint8_t v_isSharedCheck_826_; 
lean_dec_ref(v_b_723_);
v_a_819_ = lean_ctor_get(v___x_739_, 0);
v_isSharedCheck_826_ = !lean_is_exclusive(v___x_739_);
if (v_isSharedCheck_826_ == 0)
{
v___x_821_ = v___x_739_;
v_isShared_822_ = v_isSharedCheck_826_;
goto v_resetjp_820_;
}
else
{
lean_inc(v_a_819_);
lean_dec(v___x_739_);
v___x_821_ = lean_box(0);
v_isShared_822_ = v_isSharedCheck_826_;
goto v_resetjp_820_;
}
v_resetjp_820_:
{
lean_object* v___x_824_; 
if (v_isShared_822_ == 0)
{
v___x_824_ = v___x_821_;
goto v_reusejp_823_;
}
else
{
lean_object* v_reuseFailAlloc_825_; 
v_reuseFailAlloc_825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_825_, 0, v_a_819_);
v___x_824_ = v_reuseFailAlloc_825_;
goto v_reusejp_823_;
}
v_reusejp_823_:
{
return v___x_824_;
}
}
}
}
else
{
lean_object* v_a_827_; lean_object* v___x_829_; uint8_t v_isShared_830_; uint8_t v_isSharedCheck_834_; 
lean_dec_ref(v_b_723_);
v_a_827_ = lean_ctor_get(v___x_737_, 0);
v_isSharedCheck_834_ = !lean_is_exclusive(v___x_737_);
if (v_isSharedCheck_834_ == 0)
{
v___x_829_ = v___x_737_;
v_isShared_830_ = v_isSharedCheck_834_;
goto v_resetjp_828_;
}
else
{
lean_inc(v_a_827_);
lean_dec(v___x_737_);
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
v___jp_729_:
{
size_t v___x_731_; size_t v___x_732_; 
v___x_731_ = ((size_t)1ULL);
v___x_732_ = lean_usize_add(v_i_722_, v___x_731_);
v_i_722_ = v___x_732_;
v_b_723_ = v_a_730_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___boxed(lean_object* v_as_835_, lean_object* v_sz_836_, lean_object* v_i_837_, lean_object* v_b_838_, lean_object* v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_){
_start:
{
size_t v_sz_boxed_844_; size_t v_i_boxed_845_; lean_object* v_res_846_; 
v_sz_boxed_844_ = lean_unbox_usize(v_sz_836_);
lean_dec(v_sz_836_);
v_i_boxed_845_ = lean_unbox_usize(v_i_837_);
lean_dec(v_i_837_);
v_res_846_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2(v_as_835_, v_sz_boxed_844_, v_i_boxed_845_, v_b_838_, v___y_839_, v___y_840_, v___y_841_, v___y_842_);
lean_dec(v___y_842_);
lean_dec_ref(v___y_841_);
lean_dec(v___y_840_);
lean_dec_ref(v___y_839_);
lean_dec_ref(v_as_835_);
return v_res_846_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals(lean_object* v_names_847_, lean_object* v_a_848_, lean_object* v_a_849_, lean_object* v_a_850_, lean_object* v_a_851_){
_start:
{
lean_object* v_m_853_; size_t v_sz_854_; size_t v___x_855_; lean_object* v___x_856_; 
v_m_853_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_latticeOps___closed__1, &l_Lean_Elab_Tactic_VCGen_latticeOps___closed__1_once, _init_l_Lean_Elab_Tactic_VCGen_latticeOps___closed__1);
v_sz_854_ = lean_array_size(v_names_847_);
v___x_855_ = ((size_t)0ULL);
v___x_856_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2(v_names_847_, v_sz_854_, v___x_855_, v_m_853_, v_a_848_, v_a_849_, v_a_850_, v_a_851_);
return v___x_856_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals___boxed(lean_object* v_names_857_, lean_object* v_a_858_, lean_object* v_a_859_, lean_object* v_a_860_, lean_object* v_a_861_, lean_object* v_a_862_){
_start:
{
lean_object* v_res_863_; 
v_res_863_ = l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals(v_names_857_, v_a_858_, v_a_859_, v_a_860_, v_a_861_);
lean_dec(v_a_861_);
lean_dec_ref(v_a_860_);
lean_dec(v_a_859_);
lean_dec_ref(v_a_858_);
lean_dec_ref(v_names_857_);
return v_res_863_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__1(lean_object* v_00_u03b1_864_, lean_object* v_msg_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_){
_start:
{
lean_object* v___x_871_; 
v___x_871_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__1___redArg(v_msg_865_, v___y_866_, v___y_867_, v___y_868_, v___y_869_);
return v___x_871_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__1___boxed(lean_object* v_00_u03b1_872_, lean_object* v_msg_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_){
_start:
{
lean_object* v_res_879_; 
v_res_879_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__1(v_00_u03b1_872_, v_msg_873_, v___y_874_, v___y_875_, v___y_876_, v___y_877_);
lean_dec(v___y_877_);
lean_dec_ref(v___y_876_);
lean_dec(v___y_875_);
lean_dec_ref(v___y_874_);
return v_res_879_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_go___lam__0(uint8_t v_isZero_880_, lean_object* v_x_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_){
_start:
{
lean_object* v___x_892_; lean_object* v___x_893_; 
v___x_892_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_892_, 0, v_isZero_880_);
lean_ctor_set_uint8(v___x_892_, 1, v_isZero_880_);
v___x_893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_893_, 0, v___x_892_);
return v___x_893_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_go___lam__0___boxed(lean_object* v_isZero_894_, lean_object* v_x_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_){
_start:
{
uint8_t v_isZero_boxed_906_; lean_object* v_res_907_; 
v_isZero_boxed_906_ = lean_unbox(v_isZero_894_);
v_res_907_ = l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_go___lam__0(v_isZero_boxed_906_, v_x_895_, v___y_896_, v___y_897_, v___y_898_, v___y_899_, v___y_900_, v___y_901_, v___y_902_, v___y_903_, v___y_904_);
lean_dec(v___y_904_);
lean_dec_ref(v___y_903_);
lean_dec(v___y_902_);
lean_dec_ref(v___y_901_);
lean_dec(v___y_900_);
lean_dec_ref(v___y_899_);
lean_dec(v___y_898_);
lean_dec_ref(v___y_897_);
lean_dec(v___y_896_);
lean_dec_ref(v_x_895_);
return v_res_907_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_go_spec__0___redArg(lean_object* v_msg_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_){
_start:
{
lean_object* v_ref_914_; lean_object* v___x_915_; lean_object* v_a_916_; lean_object* v___x_918_; uint8_t v_isShared_919_; uint8_t v_isSharedCheck_924_; 
v_ref_914_ = lean_ctor_get(v___y_911_, 2);
v___x_915_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__1_spec__1(v_msg_908_, v___y_909_, v___y_910_, v___y_911_, v___y_912_);
v_a_916_ = lean_ctor_get(v___x_915_, 0);
v_isSharedCheck_924_ = !lean_is_exclusive(v___x_915_);
if (v_isSharedCheck_924_ == 0)
{
v___x_918_ = v___x_915_;
v_isShared_919_ = v_isSharedCheck_924_;
goto v_resetjp_917_;
}
else
{
lean_inc(v_a_916_);
lean_dec(v___x_915_);
v___x_918_ = lean_box(0);
v_isShared_919_ = v_isSharedCheck_924_;
goto v_resetjp_917_;
}
v_resetjp_917_:
{
lean_object* v___x_920_; lean_object* v___x_922_; 
lean_inc(v_ref_914_);
v___x_920_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_920_, 0, v_ref_914_);
lean_ctor_set(v___x_920_, 1, v_a_916_);
if (v_isShared_919_ == 0)
{
lean_ctor_set_tag(v___x_918_, 1);
lean_ctor_set(v___x_918_, 0, v___x_920_);
v___x_922_ = v___x_918_;
goto v_reusejp_921_;
}
else
{
lean_object* v_reuseFailAlloc_923_; 
v_reuseFailAlloc_923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_923_, 0, v___x_920_);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_go_spec__0___redArg___boxed(lean_object* v_msg_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_){
_start:
{
lean_object* v_res_931_; 
v_res_931_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_go_spec__0___redArg(v_msg_925_, v___y_926_, v___y_927_, v___y_928_, v___y_929_);
lean_dec(v___y_929_);
lean_dec_ref(v___y_928_);
lean_dec(v___y_927_);
lean_dec_ref(v___y_926_);
return v_res_931_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_go___closed__1(void){
_start:
{
lean_object* v___x_933_; lean_object* v___x_934_; 
v___x_933_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_go___closed__0));
v___x_934_ = l_Lean_stringToMessageData(v___x_933_);
return v___x_934_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_go(lean_object* v_step_938_, lean_object* v_e_u2080_939_, lean_object* v_cur_940_, lean_object* v_proof_x3f_941_, lean_object* v_a_942_, lean_object* v_a_943_, lean_object* v_a_944_, lean_object* v_a_945_, lean_object* v_a_946_, lean_object* v_a_947_, lean_object* v_a_948_){
_start:
{
lean_object* v_zero_950_; uint8_t v_isZero_951_; 
v_zero_950_ = lean_unsigned_to_nat(0u);
v_isZero_951_ = lean_nat_dec_eq(v_a_942_, v_zero_950_);
if (v_isZero_951_ == 1)
{
lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; 
lean_dec(v_a_942_);
lean_dec(v_proof_x3f_941_);
lean_dec_ref(v_e_u2080_939_);
lean_dec_ref(v_step_938_);
v___x_952_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_go___closed__1, &l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_go___closed__1_once, _init_l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_go___closed__1);
v___x_953_ = l_Lean_indentExpr(v_cur_940_);
v___x_954_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_954_, 0, v___x_952_);
lean_ctor_set(v___x_954_, 1, v___x_953_);
v___x_955_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_go_spec__0___redArg(v___x_954_, v_a_945_, v_a_946_, v_a_947_, v_a_948_);
return v___x_955_;
}
else
{
lean_object* v___x_956_; lean_object* v___f_957_; lean_object* v_one_958_; lean_object* v_n_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; 
v___x_956_ = lean_box(v_isZero_951_);
v___f_957_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_go___lam__0___boxed), 12, 1);
lean_closure_set(v___f_957_, 0, v___x_956_);
v_one_958_ = lean_unsigned_to_nat(1u);
v_n_959_ = lean_nat_sub(v_a_942_, v_one_958_);
lean_dec(v_a_942_);
lean_inc_ref(v_step_938_);
lean_inc_ref(v_cur_940_);
v___x_960_ = lean_apply_1(v_step_938_, v_cur_940_);
lean_inc_ref(v___f_957_);
v___x_961_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_961_, 0, v___f_957_);
lean_ctor_set(v___x_961_, 1, v___f_957_);
v___x_962_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_go___closed__2));
v___x_963_ = l_Lean_Meta_Sym_Simp_SimpM_run_x27___redArg(v___x_960_, v___x_961_, v___x_962_, v_a_943_, v_a_944_, v_a_945_, v_a_946_, v_a_947_, v_a_948_);
if (lean_obj_tag(v___x_963_) == 0)
{
lean_object* v_a_964_; lean_object* v___x_966_; uint8_t v_isShared_967_; uint8_t v_isSharedCheck_995_; 
v_a_964_ = lean_ctor_get(v___x_963_, 0);
v_isSharedCheck_995_ = !lean_is_exclusive(v___x_963_);
if (v_isSharedCheck_995_ == 0)
{
v___x_966_ = v___x_963_;
v_isShared_967_ = v_isSharedCheck_995_;
goto v_resetjp_965_;
}
else
{
lean_inc(v_a_964_);
lean_dec(v___x_963_);
v___x_966_ = lean_box(0);
v_isShared_967_ = v_isSharedCheck_995_;
goto v_resetjp_965_;
}
v_resetjp_965_:
{
if (lean_obj_tag(v_a_964_) == 0)
{
lean_object* v___x_968_; lean_object* v___x_970_; 
lean_dec_ref_known(v_a_964_, 0);
lean_dec(v_n_959_);
lean_dec_ref(v_e_u2080_939_);
lean_dec_ref(v_step_938_);
v___x_968_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_968_, 0, v_cur_940_);
lean_ctor_set(v___x_968_, 1, v_proof_x3f_941_);
if (v_isShared_967_ == 0)
{
lean_ctor_set(v___x_966_, 0, v___x_968_);
v___x_970_ = v___x_966_;
goto v_reusejp_969_;
}
else
{
lean_object* v_reuseFailAlloc_971_; 
v_reuseFailAlloc_971_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_971_, 0, v___x_968_);
v___x_970_ = v_reuseFailAlloc_971_;
goto v_reusejp_969_;
}
v_reusejp_969_:
{
return v___x_970_;
}
}
else
{
lean_object* v_e_x27_972_; lean_object* v_proof_973_; lean_object* v_proof_975_; lean_object* v___y_976_; lean_object* v___y_977_; lean_object* v___y_978_; lean_object* v___y_979_; lean_object* v___y_980_; lean_object* v___y_981_; 
lean_del_object(v___x_966_);
v_e_x27_972_ = lean_ctor_get(v_a_964_, 0);
lean_inc_ref(v_e_x27_972_);
v_proof_973_ = lean_ctor_get(v_a_964_, 1);
lean_inc_ref(v_proof_973_);
lean_dec_ref_known(v_a_964_, 2);
if (lean_obj_tag(v_proof_x3f_941_) == 0)
{
lean_dec_ref(v_cur_940_);
v_proof_975_ = v_proof_973_;
v___y_976_ = v_a_943_;
v___y_977_ = v_a_944_;
v___y_978_ = v_a_945_;
v___y_979_ = v_a_946_;
v___y_980_ = v_a_947_;
v___y_981_ = v_a_948_;
goto v___jp_974_;
}
else
{
lean_object* v_val_984_; lean_object* v___x_985_; 
v_val_984_ = lean_ctor_get(v_proof_x3f_941_, 0);
lean_inc(v_val_984_);
lean_dec_ref_known(v_proof_x3f_941_, 1);
lean_inc_ref(v_e_x27_972_);
lean_inc_ref(v_e_u2080_939_);
v___x_985_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v_e_u2080_939_, v_cur_940_, v_val_984_, v_e_x27_972_, v_proof_973_, v_a_943_, v_a_944_, v_a_945_, v_a_946_, v_a_947_, v_a_948_);
if (lean_obj_tag(v___x_985_) == 0)
{
lean_object* v_a_986_; 
v_a_986_ = lean_ctor_get(v___x_985_, 0);
lean_inc(v_a_986_);
lean_dec_ref_known(v___x_985_, 1);
v_proof_975_ = v_a_986_;
v___y_976_ = v_a_943_;
v___y_977_ = v_a_944_;
v___y_978_ = v_a_945_;
v___y_979_ = v_a_946_;
v___y_980_ = v_a_947_;
v___y_981_ = v_a_948_;
goto v___jp_974_;
}
else
{
lean_object* v_a_987_; lean_object* v___x_989_; uint8_t v_isShared_990_; uint8_t v_isSharedCheck_994_; 
lean_dec_ref(v_e_x27_972_);
lean_dec(v_n_959_);
lean_dec_ref(v_e_u2080_939_);
lean_dec_ref(v_step_938_);
v_a_987_ = lean_ctor_get(v___x_985_, 0);
v_isSharedCheck_994_ = !lean_is_exclusive(v___x_985_);
if (v_isSharedCheck_994_ == 0)
{
v___x_989_ = v___x_985_;
v_isShared_990_ = v_isSharedCheck_994_;
goto v_resetjp_988_;
}
else
{
lean_inc(v_a_987_);
lean_dec(v___x_985_);
v___x_989_ = lean_box(0);
v_isShared_990_ = v_isSharedCheck_994_;
goto v_resetjp_988_;
}
v_resetjp_988_:
{
lean_object* v___x_992_; 
if (v_isShared_990_ == 0)
{
v___x_992_ = v___x_989_;
goto v_reusejp_991_;
}
else
{
lean_object* v_reuseFailAlloc_993_; 
v_reuseFailAlloc_993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_993_, 0, v_a_987_);
v___x_992_ = v_reuseFailAlloc_993_;
goto v_reusejp_991_;
}
v_reusejp_991_:
{
return v___x_992_;
}
}
}
}
v___jp_974_:
{
lean_object* v___x_982_; 
v___x_982_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_982_, 0, v_proof_975_);
v_cur_940_ = v_e_x27_972_;
v_proof_x3f_941_ = v___x_982_;
v_a_942_ = v_n_959_;
v_a_943_ = v___y_976_;
v_a_944_ = v___y_977_;
v_a_945_ = v___y_978_;
v_a_946_ = v___y_979_;
v_a_947_ = v___y_980_;
v_a_948_ = v___y_981_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_996_; lean_object* v___x_998_; uint8_t v_isShared_999_; uint8_t v_isSharedCheck_1003_; 
lean_dec(v_n_959_);
lean_dec(v_proof_x3f_941_);
lean_dec_ref(v_cur_940_);
lean_dec_ref(v_e_u2080_939_);
lean_dec_ref(v_step_938_);
v_a_996_ = lean_ctor_get(v___x_963_, 0);
v_isSharedCheck_1003_ = !lean_is_exclusive(v___x_963_);
if (v_isSharedCheck_1003_ == 0)
{
v___x_998_ = v___x_963_;
v_isShared_999_ = v_isSharedCheck_1003_;
goto v_resetjp_997_;
}
else
{
lean_inc(v_a_996_);
lean_dec(v___x_963_);
v___x_998_ = lean_box(0);
v_isShared_999_ = v_isSharedCheck_1003_;
goto v_resetjp_997_;
}
v_resetjp_997_:
{
lean_object* v___x_1001_; 
if (v_isShared_999_ == 0)
{
v___x_1001_ = v___x_998_;
goto v_reusejp_1000_;
}
else
{
lean_object* v_reuseFailAlloc_1002_; 
v_reuseFailAlloc_1002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1002_, 0, v_a_996_);
v___x_1001_ = v_reuseFailAlloc_1002_;
goto v_reusejp_1000_;
}
v_reusejp_1000_:
{
return v___x_1001_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_go___boxed(lean_object* v_step_1004_, lean_object* v_e_u2080_1005_, lean_object* v_cur_1006_, lean_object* v_proof_x3f_1007_, lean_object* v_a_1008_, lean_object* v_a_1009_, lean_object* v_a_1010_, lean_object* v_a_1011_, lean_object* v_a_1012_, lean_object* v_a_1013_, lean_object* v_a_1014_, lean_object* v_a_1015_){
_start:
{
lean_object* v_res_1016_; 
v_res_1016_ = l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_go(v_step_1004_, v_e_u2080_1005_, v_cur_1006_, v_proof_x3f_1007_, v_a_1008_, v_a_1009_, v_a_1010_, v_a_1011_, v_a_1012_, v_a_1013_, v_a_1014_);
lean_dec(v_a_1014_);
lean_dec_ref(v_a_1013_);
lean_dec(v_a_1012_);
lean_dec_ref(v_a_1011_);
lean_dec(v_a_1010_);
lean_dec_ref(v_a_1009_);
return v_res_1016_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_go_spec__0(lean_object* v_00_u03b1_1017_, lean_object* v_msg_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_){
_start:
{
lean_object* v___x_1026_; 
v___x_1026_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_go_spec__0___redArg(v_msg_1018_, v___y_1021_, v___y_1022_, v___y_1023_, v___y_1024_);
return v___x_1026_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_go_spec__0___boxed(lean_object* v_00_u03b1_1027_, lean_object* v_msg_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_){
_start:
{
lean_object* v_res_1036_; 
v_res_1036_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_go_spec__0(v_00_u03b1_1027_, v_msg_1028_, v___y_1029_, v___y_1030_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_);
lean_dec(v___y_1034_);
lean_dec_ref(v___y_1033_);
lean_dec(v___y_1032_);
lean_dec_ref(v___y_1031_);
lean_dec(v___y_1030_);
lean_dec_ref(v___y_1029_);
return v_res_1036_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_spec__0___redArg(lean_object* v_as_1037_, size_t v_i_1038_, size_t v_stop_1039_, lean_object* v_b_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_){
_start:
{
uint8_t v___x_1046_; 
v___x_1046_ = lean_usize_dec_eq(v_i_1038_, v_stop_1039_);
if (v___x_1046_ == 0)
{
lean_object* v___x_1047_; lean_object* v___x_1048_; 
v___x_1047_ = lean_array_uget_borrowed(v_as_1037_, v_i_1038_);
lean_inc(v___x_1047_);
v___x_1048_ = l_Lean_Meta_Sym_Simp_mkTheoremFromDecl(v___x_1047_, v___y_1041_, v___y_1042_, v___y_1043_, v___y_1044_);
if (lean_obj_tag(v___x_1048_) == 0)
{
lean_object* v_a_1049_; lean_object* v___x_1050_; size_t v___x_1051_; size_t v___x_1052_; 
v_a_1049_ = lean_ctor_get(v___x_1048_, 0);
lean_inc(v_a_1049_);
lean_dec_ref_known(v___x_1048_, 1);
v___x_1050_ = l_Lean_Meta_Sym_Simp_Theorems_insert(v_b_1040_, v_a_1049_);
v___x_1051_ = ((size_t)1ULL);
v___x_1052_ = lean_usize_add(v_i_1038_, v___x_1051_);
v_i_1038_ = v___x_1052_;
v_b_1040_ = v___x_1050_;
goto _start;
}
else
{
lean_object* v_a_1054_; lean_object* v___x_1056_; uint8_t v_isShared_1057_; uint8_t v_isSharedCheck_1061_; 
lean_dec_ref(v_b_1040_);
v_a_1054_ = lean_ctor_get(v___x_1048_, 0);
v_isSharedCheck_1061_ = !lean_is_exclusive(v___x_1048_);
if (v_isSharedCheck_1061_ == 0)
{
v___x_1056_ = v___x_1048_;
v_isShared_1057_ = v_isSharedCheck_1061_;
goto v_resetjp_1055_;
}
else
{
lean_inc(v_a_1054_);
lean_dec(v___x_1048_);
v___x_1056_ = lean_box(0);
v_isShared_1057_ = v_isSharedCheck_1061_;
goto v_resetjp_1055_;
}
v_resetjp_1055_:
{
lean_object* v___x_1059_; 
if (v_isShared_1057_ == 0)
{
v___x_1059_ = v___x_1056_;
goto v_reusejp_1058_;
}
else
{
lean_object* v_reuseFailAlloc_1060_; 
v_reuseFailAlloc_1060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1060_, 0, v_a_1054_);
v___x_1059_ = v_reuseFailAlloc_1060_;
goto v_reusejp_1058_;
}
v_reusejp_1058_:
{
return v___x_1059_;
}
}
}
}
else
{
lean_object* v___x_1062_; 
v___x_1062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1062_, 0, v_b_1040_);
return v___x_1062_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_spec__0___redArg___boxed(lean_object* v_as_1063_, lean_object* v_i_1064_, lean_object* v_stop_1065_, lean_object* v_b_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_){
_start:
{
size_t v_i_boxed_1072_; size_t v_stop_boxed_1073_; lean_object* v_res_1074_; 
v_i_boxed_1072_ = lean_unbox_usize(v_i_1064_);
lean_dec(v_i_1064_);
v_stop_boxed_1073_ = lean_unbox_usize(v_stop_1065_);
lean_dec(v_stop_1065_);
v_res_1074_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_spec__0___redArg(v_as_1063_, v_i_boxed_1072_, v_stop_boxed_1073_, v_b_1066_, v___y_1067_, v___y_1068_, v___y_1069_, v___y_1070_);
lean_dec(v___y_1070_);
lean_dec_ref(v___y_1069_);
lean_dec(v___y_1068_);
lean_dec_ref(v___y_1067_);
lean_dec_ref(v_as_1063_);
return v_res_1074_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp___closed__1(void){
_start:
{
lean_object* v___x_1076_; 
v___x_1076_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1076_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp___closed__2(void){
_start:
{
lean_object* v___x_1077_; lean_object* v___x_1078_; 
v___x_1077_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp___closed__1, &l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp___closed__1_once, _init_l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp___closed__1);
v___x_1078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1078_, 0, v___x_1077_);
return v___x_1078_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp(lean_object* v_rewrites_1079_, lean_object* v_e_1080_, lean_object* v_fuel_1081_, lean_object* v_a_1082_, lean_object* v_a_1083_, lean_object* v_a_1084_, lean_object* v_a_1085_, lean_object* v_a_1086_, lean_object* v_a_1087_){
_start:
{
lean_object* v_a_1090_; lean_object* v___y_1106_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; uint8_t v___x_1119_; 
v___x_1116_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp___closed__2, &l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp___closed__2_once, _init_l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp___closed__2);
v___x_1117_ = lean_unsigned_to_nat(0u);
v___x_1118_ = lean_array_get_size(v_rewrites_1079_);
v___x_1119_ = lean_nat_dec_lt(v___x_1117_, v___x_1118_);
if (v___x_1119_ == 0)
{
v_a_1090_ = v___x_1116_;
goto v___jp_1089_;
}
else
{
uint8_t v___x_1120_; 
v___x_1120_ = lean_nat_dec_le(v___x_1118_, v___x_1118_);
if (v___x_1120_ == 0)
{
if (v___x_1119_ == 0)
{
v_a_1090_ = v___x_1116_;
goto v___jp_1089_;
}
else
{
size_t v___x_1121_; size_t v___x_1122_; lean_object* v___x_1123_; 
v___x_1121_ = ((size_t)0ULL);
v___x_1122_ = lean_usize_of_nat(v___x_1118_);
v___x_1123_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_spec__0___redArg(v_rewrites_1079_, v___x_1121_, v___x_1122_, v___x_1116_, v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_);
v___y_1106_ = v___x_1123_;
goto v___jp_1105_;
}
}
else
{
size_t v___x_1124_; size_t v___x_1125_; lean_object* v___x_1126_; 
v___x_1124_ = ((size_t)0ULL);
v___x_1125_ = lean_usize_of_nat(v___x_1118_);
v___x_1126_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_spec__0___redArg(v_rewrites_1079_, v___x_1124_, v___x_1125_, v___x_1116_, v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_);
v___y_1106_ = v___x_1126_;
goto v___jp_1105_;
}
}
v___jp_1089_:
{
lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; 
v___x_1091_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp___closed__0));
v___x_1092_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Simp_Theorems_rewrite___boxed), 13, 2);
lean_closure_set(v___x_1092_, 0, v_a_1090_);
lean_closure_set(v___x_1092_, 1, v___x_1091_);
v___x_1093_ = l_Lean_Meta_Sym_shareCommon(v_e_1080_, v_a_1082_, v_a_1083_, v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_);
if (lean_obj_tag(v___x_1093_) == 0)
{
lean_object* v_a_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; 
v_a_1094_ = lean_ctor_get(v___x_1093_, 0);
lean_inc_n(v_a_1094_, 2);
lean_dec_ref_known(v___x_1093_, 1);
v___x_1095_ = lean_box(0);
v___x_1096_ = l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_go(v___x_1092_, v_a_1094_, v_a_1094_, v___x_1095_, v_fuel_1081_, v_a_1082_, v_a_1083_, v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_);
return v___x_1096_;
}
else
{
lean_object* v_a_1097_; lean_object* v___x_1099_; uint8_t v_isShared_1100_; uint8_t v_isSharedCheck_1104_; 
lean_dec_ref(v___x_1092_);
lean_dec(v_fuel_1081_);
v_a_1097_ = lean_ctor_get(v___x_1093_, 0);
v_isSharedCheck_1104_ = !lean_is_exclusive(v___x_1093_);
if (v_isSharedCheck_1104_ == 0)
{
v___x_1099_ = v___x_1093_;
v_isShared_1100_ = v_isSharedCheck_1104_;
goto v_resetjp_1098_;
}
else
{
lean_inc(v_a_1097_);
lean_dec(v___x_1093_);
v___x_1099_ = lean_box(0);
v_isShared_1100_ = v_isSharedCheck_1104_;
goto v_resetjp_1098_;
}
v_resetjp_1098_:
{
lean_object* v___x_1102_; 
if (v_isShared_1100_ == 0)
{
v___x_1102_ = v___x_1099_;
goto v_reusejp_1101_;
}
else
{
lean_object* v_reuseFailAlloc_1103_; 
v_reuseFailAlloc_1103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1103_, 0, v_a_1097_);
v___x_1102_ = v_reuseFailAlloc_1103_;
goto v_reusejp_1101_;
}
v_reusejp_1101_:
{
return v___x_1102_;
}
}
}
}
v___jp_1105_:
{
if (lean_obj_tag(v___y_1106_) == 0)
{
lean_object* v_a_1107_; 
v_a_1107_ = lean_ctor_get(v___y_1106_, 0);
lean_inc(v_a_1107_);
lean_dec_ref_known(v___y_1106_, 1);
v_a_1090_ = v_a_1107_;
goto v___jp_1089_;
}
else
{
lean_object* v_a_1108_; lean_object* v___x_1110_; uint8_t v_isShared_1111_; uint8_t v_isSharedCheck_1115_; 
lean_dec(v_fuel_1081_);
lean_dec_ref(v_e_1080_);
v_a_1108_ = lean_ctor_get(v___y_1106_, 0);
v_isSharedCheck_1115_ = !lean_is_exclusive(v___y_1106_);
if (v_isSharedCheck_1115_ == 0)
{
v___x_1110_ = v___y_1106_;
v_isShared_1111_ = v_isSharedCheck_1115_;
goto v_resetjp_1109_;
}
else
{
lean_inc(v_a_1108_);
lean_dec(v___y_1106_);
v___x_1110_ = lean_box(0);
v_isShared_1111_ = v_isSharedCheck_1115_;
goto v_resetjp_1109_;
}
v_resetjp_1109_:
{
lean_object* v___x_1113_; 
if (v_isShared_1111_ == 0)
{
v___x_1113_ = v___x_1110_;
goto v_reusejp_1112_;
}
else
{
lean_object* v_reuseFailAlloc_1114_; 
v_reuseFailAlloc_1114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1114_, 0, v_a_1108_);
v___x_1113_ = v_reuseFailAlloc_1114_;
goto v_reusejp_1112_;
}
v_reusejp_1112_:
{
return v___x_1113_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp___boxed(lean_object* v_rewrites_1127_, lean_object* v_e_1128_, lean_object* v_fuel_1129_, lean_object* v_a_1130_, lean_object* v_a_1131_, lean_object* v_a_1132_, lean_object* v_a_1133_, lean_object* v_a_1134_, lean_object* v_a_1135_, lean_object* v_a_1136_){
_start:
{
lean_object* v_res_1137_; 
v_res_1137_ = l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp(v_rewrites_1127_, v_e_1128_, v_fuel_1129_, v_a_1130_, v_a_1131_, v_a_1132_, v_a_1133_, v_a_1134_, v_a_1135_);
lean_dec(v_a_1135_);
lean_dec_ref(v_a_1134_);
lean_dec(v_a_1133_);
lean_dec_ref(v_a_1132_);
lean_dec(v_a_1131_);
lean_dec_ref(v_a_1130_);
lean_dec_ref(v_rewrites_1127_);
return v_res_1137_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_spec__0(lean_object* v_as_1138_, size_t v_i_1139_, size_t v_stop_1140_, lean_object* v_b_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_){
_start:
{
lean_object* v___x_1149_; 
v___x_1149_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_spec__0___redArg(v_as_1138_, v_i_1139_, v_stop_1140_, v_b_1141_, v___y_1144_, v___y_1145_, v___y_1146_, v___y_1147_);
return v___x_1149_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_spec__0___boxed(lean_object* v_as_1150_, lean_object* v_i_1151_, lean_object* v_stop_1152_, lean_object* v_b_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_){
_start:
{
size_t v_i_boxed_1161_; size_t v_stop_boxed_1162_; lean_object* v_res_1163_; 
v_i_boxed_1161_ = lean_unbox_usize(v_i_1151_);
lean_dec(v_i_1151_);
v_stop_boxed_1162_ = lean_unbox_usize(v_stop_1152_);
lean_dec(v_stop_1152_);
v_res_1163_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_spec__0(v_as_1150_, v_i_boxed_1161_, v_stop_boxed_1162_, v_b_1153_, v___y_1154_, v___y_1155_, v___y_1156_, v___y_1157_, v___y_1158_, v___y_1159_);
lean_dec(v___y_1159_);
lean_dec_ref(v___y_1158_);
lean_dec(v___y_1157_);
lean_dec_ref(v___y_1156_);
lean_dec(v___y_1155_);
lean_dec_ref(v___y_1154_);
lean_dec_ref(v_as_1150_);
return v_res_1163_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply___lam__0(lean_object* v_s_1164_, lean_object* v_a_1165_, lean_object* v_pre_1166_, lean_object* v_u_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_){
_start:
{
lean_object* v___x_1173_; 
lean_inc_ref(v_u_1167_);
v___x_1173_ = l_Lean_Meta_mkEq(v_u_1167_, v_s_1164_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_);
if (lean_obj_tag(v___x_1173_) == 0)
{
lean_object* v_a_1174_; lean_object* v___x_1176_; uint8_t v_isShared_1177_; uint8_t v_isSharedCheck_1205_; 
v_a_1174_ = lean_ctor_get(v___x_1173_, 0);
v_isSharedCheck_1205_ = !lean_is_exclusive(v___x_1173_);
if (v_isSharedCheck_1205_ == 0)
{
v___x_1176_ = v___x_1173_;
v_isShared_1177_ = v_isSharedCheck_1205_;
goto v_resetjp_1175_;
}
else
{
lean_inc(v_a_1174_);
lean_dec(v___x_1173_);
v___x_1176_ = lean_box(0);
v_isShared_1177_ = v_isSharedCheck_1205_;
goto v_resetjp_1175_;
}
v_resetjp_1175_:
{
lean_object* v___x_1178_; lean_object* v___x_1180_; 
v___x_1178_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_LatticeOp_ofProp___closed__2));
if (v_isShared_1177_ == 0)
{
lean_ctor_set_tag(v___x_1176_, 1);
lean_ctor_set(v___x_1176_, 0, v_a_1165_);
v___x_1180_ = v___x_1176_;
goto v_reusejp_1179_;
}
else
{
lean_object* v_reuseFailAlloc_1204_; 
v_reuseFailAlloc_1204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1204_, 0, v_a_1165_);
v___x_1180_ = v_reuseFailAlloc_1204_;
goto v_reusejp_1179_;
}
v_reusejp_1179_:
{
lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; 
v___x_1181_ = lean_box(0);
v___x_1182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1182_, 0, v_a_1174_);
v___x_1183_ = lean_unsigned_to_nat(3u);
v___x_1184_ = lean_mk_empty_array_with_capacity(v___x_1183_);
v___x_1185_ = lean_array_push(v___x_1184_, v___x_1180_);
v___x_1186_ = lean_array_push(v___x_1185_, v___x_1181_);
v___x_1187_ = lean_array_push(v___x_1186_, v___x_1182_);
v___x_1188_ = l_Lean_Meta_mkAppOptM(v___x_1178_, v___x_1187_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_);
if (lean_obj_tag(v___x_1188_) == 0)
{
lean_object* v_a_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; 
v_a_1189_ = lean_ctor_get(v___x_1188_, 0);
lean_inc(v_a_1189_);
lean_dec_ref_known(v___x_1188_, 1);
v___x_1190_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__4));
v___x_1191_ = lean_unsigned_to_nat(2u);
v___x_1192_ = lean_mk_empty_array_with_capacity(v___x_1191_);
v___x_1193_ = lean_array_push(v___x_1192_, v_a_1189_);
v___x_1194_ = lean_array_push(v___x_1193_, v_pre_1166_);
v___x_1195_ = l_Lean_Meta_mkAppM(v___x_1190_, v___x_1194_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_);
if (lean_obj_tag(v___x_1195_) == 0)
{
lean_object* v_a_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; uint8_t v___x_1200_; uint8_t v___x_1201_; uint8_t v___x_1202_; lean_object* v___x_1203_; 
v_a_1196_ = lean_ctor_get(v___x_1195_, 0);
lean_inc(v_a_1196_);
lean_dec_ref_known(v___x_1195_, 1);
v___x_1197_ = lean_unsigned_to_nat(1u);
v___x_1198_ = lean_mk_empty_array_with_capacity(v___x_1197_);
v___x_1199_ = lean_array_push(v___x_1198_, v_u_1167_);
v___x_1200_ = 0;
v___x_1201_ = 1;
v___x_1202_ = 1;
v___x_1203_ = l_Lean_Meta_mkLambdaFVars(v___x_1199_, v_a_1196_, v___x_1200_, v___x_1201_, v___x_1200_, v___x_1201_, v___x_1202_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_);
lean_dec_ref(v___x_1199_);
return v___x_1203_;
}
else
{
lean_dec_ref(v_u_1167_);
return v___x_1195_;
}
}
else
{
lean_dec_ref(v_u_1167_);
lean_dec_ref(v_pre_1166_);
return v___x_1188_;
}
}
}
}
else
{
lean_dec_ref(v_u_1167_);
lean_dec_ref(v_pre_1166_);
lean_dec_ref(v_a_1165_);
return v___x_1173_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply___lam__0___boxed(lean_object* v_s_1206_, lean_object* v_a_1207_, lean_object* v_pre_1208_, lean_object* v_u_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_){
_start:
{
lean_object* v_res_1215_; 
v_res_1215_ = l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply___lam__0(v_s_1206_, v_a_1207_, v_pre_1208_, v_u_1209_, v___y_1210_, v___y_1211_, v___y_1212_, v___y_1213_);
lean_dec(v___y_1213_);
lean_dec_ref(v___y_1212_);
lean_dec(v___y_1211_);
lean_dec_ref(v___y_1210_);
return v_res_1215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply_spec__0_spec__0___redArg___lam__0(lean_object* v_k_1216_, lean_object* v_b_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_){
_start:
{
lean_object* v___x_1223_; 
lean_inc(v___y_1221_);
lean_inc_ref(v___y_1220_);
lean_inc(v___y_1219_);
lean_inc_ref(v___y_1218_);
v___x_1223_ = lean_apply_6(v_k_1216_, v_b_1217_, v___y_1218_, v___y_1219_, v___y_1220_, v___y_1221_, lean_box(0));
return v___x_1223_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply_spec__0_spec__0___redArg___lam__0___boxed(lean_object* v_k_1224_, lean_object* v_b_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_){
_start:
{
lean_object* v_res_1231_; 
v_res_1231_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply_spec__0_spec__0___redArg___lam__0(v_k_1224_, v_b_1225_, v___y_1226_, v___y_1227_, v___y_1228_, v___y_1229_);
lean_dec(v___y_1229_);
lean_dec_ref(v___y_1228_);
lean_dec(v___y_1227_);
lean_dec_ref(v___y_1226_);
return v_res_1231_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply_spec__0_spec__0___redArg(lean_object* v_name_1232_, uint8_t v_bi_1233_, lean_object* v_type_1234_, lean_object* v_k_1235_, uint8_t v_kind_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_){
_start:
{
lean_object* v___f_1242_; lean_object* v___x_1243_; 
v___f_1242_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply_spec__0_spec__0___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1242_, 0, v_k_1235_);
v___x_1243_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1232_, v_bi_1233_, v_type_1234_, v___f_1242_, v_kind_1236_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_);
if (lean_obj_tag(v___x_1243_) == 0)
{
lean_object* v_a_1244_; lean_object* v___x_1246_; uint8_t v_isShared_1247_; uint8_t v_isSharedCheck_1251_; 
v_a_1244_ = lean_ctor_get(v___x_1243_, 0);
v_isSharedCheck_1251_ = !lean_is_exclusive(v___x_1243_);
if (v_isSharedCheck_1251_ == 0)
{
v___x_1246_ = v___x_1243_;
v_isShared_1247_ = v_isSharedCheck_1251_;
goto v_resetjp_1245_;
}
else
{
lean_inc(v_a_1244_);
lean_dec(v___x_1243_);
v___x_1246_ = lean_box(0);
v_isShared_1247_ = v_isSharedCheck_1251_;
goto v_resetjp_1245_;
}
v_resetjp_1245_:
{
lean_object* v___x_1249_; 
if (v_isShared_1247_ == 0)
{
v___x_1249_ = v___x_1246_;
goto v_reusejp_1248_;
}
else
{
lean_object* v_reuseFailAlloc_1250_; 
v_reuseFailAlloc_1250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1250_, 0, v_a_1244_);
v___x_1249_ = v_reuseFailAlloc_1250_;
goto v_reusejp_1248_;
}
v_reusejp_1248_:
{
return v___x_1249_;
}
}
}
else
{
lean_object* v_a_1252_; lean_object* v___x_1254_; uint8_t v_isShared_1255_; uint8_t v_isSharedCheck_1259_; 
v_a_1252_ = lean_ctor_get(v___x_1243_, 0);
v_isSharedCheck_1259_ = !lean_is_exclusive(v___x_1243_);
if (v_isSharedCheck_1259_ == 0)
{
v___x_1254_ = v___x_1243_;
v_isShared_1255_ = v_isSharedCheck_1259_;
goto v_resetjp_1253_;
}
else
{
lean_inc(v_a_1252_);
lean_dec(v___x_1243_);
v___x_1254_ = lean_box(0);
v_isShared_1255_ = v_isSharedCheck_1259_;
goto v_resetjp_1253_;
}
v_resetjp_1253_:
{
lean_object* v___x_1257_; 
if (v_isShared_1255_ == 0)
{
v___x_1257_ = v___x_1254_;
goto v_reusejp_1256_;
}
else
{
lean_object* v_reuseFailAlloc_1258_; 
v_reuseFailAlloc_1258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1258_, 0, v_a_1252_);
v___x_1257_ = v_reuseFailAlloc_1258_;
goto v_reusejp_1256_;
}
v_reusejp_1256_:
{
return v___x_1257_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply_spec__0_spec__0___redArg___boxed(lean_object* v_name_1260_, lean_object* v_bi_1261_, lean_object* v_type_1262_, lean_object* v_k_1263_, lean_object* v_kind_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_){
_start:
{
uint8_t v_bi_boxed_1270_; uint8_t v_kind_boxed_1271_; lean_object* v_res_1272_; 
v_bi_boxed_1270_ = lean_unbox(v_bi_1261_);
v_kind_boxed_1271_ = lean_unbox(v_kind_1264_);
v_res_1272_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply_spec__0_spec__0___redArg(v_name_1260_, v_bi_boxed_1270_, v_type_1262_, v_k_1263_, v_kind_boxed_1271_, v___y_1265_, v___y_1266_, v___y_1267_, v___y_1268_);
lean_dec(v___y_1268_);
lean_dec_ref(v___y_1267_);
lean_dec(v___y_1266_);
lean_dec_ref(v___y_1265_);
return v_res_1272_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply_spec__0___redArg(lean_object* v_name_1273_, lean_object* v_type_1274_, lean_object* v_k_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_){
_start:
{
uint8_t v___x_1281_; uint8_t v___x_1282_; lean_object* v___x_1283_; 
v___x_1281_ = 0;
v___x_1282_ = 0;
v___x_1283_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply_spec__0_spec__0___redArg(v_name_1273_, v___x_1281_, v_type_1274_, v_k_1275_, v___x_1282_, v___y_1276_, v___y_1277_, v___y_1278_, v___y_1279_);
return v___x_1283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply_spec__0___redArg___boxed(lean_object* v_name_1284_, lean_object* v_type_1285_, lean_object* v_k_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_){
_start:
{
lean_object* v_res_1292_; 
v_res_1292_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply_spec__0___redArg(v_name_1284_, v_type_1285_, v_k_1286_, v___y_1287_, v___y_1288_, v___y_1289_, v___y_1290_);
lean_dec(v___y_1290_);
lean_dec_ref(v___y_1289_);
lean_dec(v___y_1288_);
lean_dec_ref(v___y_1287_);
return v_res_1292_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply___closed__1(void){
_start:
{
lean_object* v___x_1294_; lean_object* v___x_1295_; 
v___x_1294_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply___closed__0));
v___x_1295_ = l_Lean_stringToMessageData(v___x_1294_);
return v___x_1295_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply(lean_object* v_introThm_1304_, lean_object* v_opAs_1305_, lean_object* v_pre_1306_, lean_object* v_ss_1307_, lean_object* v_a_1308_, lean_object* v_a_1309_, lean_object* v_a_1310_, lean_object* v_a_1311_){
_start:
{
if (lean_obj_tag(v_ss_1307_) == 0)
{
lean_object* v___x_1313_; 
lean_inc(v_introThm_1304_);
v___x_1313_ = l_Lean_Meta_mkConstWithFreshMVarLevels(v_introThm_1304_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_);
if (lean_obj_tag(v___x_1313_) == 0)
{
lean_object* v_a_1314_; lean_object* v___x_1315_; 
v_a_1314_ = lean_ctor_get(v___x_1313_, 0);
lean_inc_n(v_a_1314_, 2);
lean_dec_ref_known(v___x_1313_, 1);
lean_inc(v_a_1311_);
lean_inc_ref(v_a_1310_);
lean_inc(v_a_1309_);
lean_inc_ref(v_a_1308_);
v___x_1315_ = lean_infer_type(v_a_1314_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_);
if (lean_obj_tag(v___x_1315_) == 0)
{
lean_object* v_a_1316_; uint8_t v___x_1317_; lean_object* v___x_1318_; 
v_a_1316_ = lean_ctor_get(v___x_1315_, 0);
lean_inc(v_a_1316_);
lean_dec_ref_known(v___x_1315_, 1);
v___x_1317_ = 0;
v___x_1318_ = l_Lean_Meta_forallMetaTelescope(v_a_1316_, v___x_1317_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_);
if (lean_obj_tag(v___x_1318_) == 0)
{
lean_object* v_a_1319_; lean_object* v___x_1321_; uint8_t v_isShared_1322_; uint8_t v_isSharedCheck_1378_; 
v_a_1319_ = lean_ctor_get(v___x_1318_, 0);
v_isSharedCheck_1378_ = !lean_is_exclusive(v___x_1318_);
if (v_isSharedCheck_1378_ == 0)
{
v___x_1321_ = v___x_1318_;
v_isShared_1322_ = v_isSharedCheck_1378_;
goto v_resetjp_1320_;
}
else
{
lean_inc(v_a_1319_);
lean_dec(v___x_1318_);
v___x_1321_ = lean_box(0);
v_isShared_1322_ = v_isSharedCheck_1378_;
goto v_resetjp_1320_;
}
v_resetjp_1320_:
{
lean_object* v_fst_1323_; lean_object* v_snd_1324_; lean_object* v___x_1326_; uint8_t v_isShared_1327_; uint8_t v_isSharedCheck_1377_; 
v_fst_1323_ = lean_ctor_get(v_a_1319_, 0);
v_snd_1324_ = lean_ctor_get(v_a_1319_, 1);
v_isSharedCheck_1377_ = !lean_is_exclusive(v_a_1319_);
if (v_isSharedCheck_1377_ == 0)
{
v___x_1326_ = v_a_1319_;
v_isShared_1327_ = v_isSharedCheck_1377_;
goto v_resetjp_1325_;
}
else
{
lean_inc(v_snd_1324_);
lean_inc(v_fst_1323_);
lean_dec(v_a_1319_);
v___x_1326_ = lean_box(0);
v_isShared_1327_ = v_isSharedCheck_1377_;
goto v_resetjp_1325_;
}
v_resetjp_1325_:
{
lean_object* v_snd_1333_; lean_object* v___x_1335_; uint8_t v_isShared_1336_; uint8_t v_isSharedCheck_1375_; 
v_snd_1333_ = lean_ctor_get(v_snd_1324_, 1);
v_isSharedCheck_1375_ = !lean_is_exclusive(v_snd_1324_);
if (v_isSharedCheck_1375_ == 0)
{
lean_object* v_unused_1376_; 
v_unused_1376_ = lean_ctor_get(v_snd_1324_, 0);
lean_dec(v_unused_1376_);
v___x_1335_ = v_snd_1324_;
v_isShared_1336_ = v_isSharedCheck_1375_;
goto v_resetjp_1334_;
}
else
{
lean_inc(v_snd_1333_);
lean_dec(v_snd_1324_);
v___x_1335_ = lean_box(0);
v_isShared_1336_ = v_isSharedCheck_1375_;
goto v_resetjp_1334_;
}
v___jp_1328_:
{
lean_object* v___x_1329_; lean_object* v___x_1331_; 
v___x_1329_ = l_Lean_mkAppN(v_a_1314_, v_fst_1323_);
lean_dec(v_fst_1323_);
if (v_isShared_1322_ == 0)
{
lean_ctor_set(v___x_1321_, 0, v___x_1329_);
v___x_1331_ = v___x_1321_;
goto v_reusejp_1330_;
}
else
{
lean_object* v_reuseFailAlloc_1332_; 
v_reuseFailAlloc_1332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1332_, 0, v___x_1329_);
v___x_1331_ = v_reuseFailAlloc_1332_;
goto v_reusejp_1330_;
}
v_reusejp_1330_:
{
return v___x_1331_;
}
}
v_resetjp_1334_:
{
lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; 
v___x_1337_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__2));
v___x_1338_ = lean_unsigned_to_nat(2u);
v___x_1339_ = lean_mk_empty_array_with_capacity(v___x_1338_);
v___x_1340_ = lean_array_push(v___x_1339_, v_pre_1306_);
v___x_1341_ = lean_array_push(v___x_1340_, v_opAs_1305_);
v___x_1342_ = l_Lean_Meta_mkAppM(v___x_1337_, v___x_1341_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_);
if (lean_obj_tag(v___x_1342_) == 0)
{
lean_object* v_a_1343_; lean_object* v___x_1344_; 
v_a_1343_ = lean_ctor_get(v___x_1342_, 0);
lean_inc_n(v_a_1343_, 2);
lean_dec_ref_known(v___x_1342_, 1);
v___x_1344_ = l_Lean_Meta_isExprDefEq(v_snd_1333_, v_a_1343_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_);
if (lean_obj_tag(v___x_1344_) == 0)
{
lean_object* v_a_1345_; uint8_t v___x_1346_; 
v_a_1345_ = lean_ctor_get(v___x_1344_, 0);
lean_inc(v_a_1345_);
lean_dec_ref_known(v___x_1344_, 1);
v___x_1346_ = lean_unbox(v_a_1345_);
lean_dec(v_a_1345_);
if (v___x_1346_ == 0)
{
lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1350_; 
v___x_1347_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__4);
v___x_1348_ = l_Lean_MessageData_ofName(v_introThm_1304_);
if (v_isShared_1336_ == 0)
{
lean_ctor_set_tag(v___x_1335_, 7);
lean_ctor_set(v___x_1335_, 1, v___x_1348_);
lean_ctor_set(v___x_1335_, 0, v___x_1347_);
v___x_1350_ = v___x_1335_;
goto v_reusejp_1349_;
}
else
{
lean_object* v_reuseFailAlloc_1366_; 
v_reuseFailAlloc_1366_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1366_, 0, v___x_1347_);
lean_ctor_set(v_reuseFailAlloc_1366_, 1, v___x_1348_);
v___x_1350_ = v_reuseFailAlloc_1366_;
goto v_reusejp_1349_;
}
v_reusejp_1349_:
{
lean_object* v___x_1351_; lean_object* v___x_1353_; 
v___x_1351_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply___closed__1, &l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply___closed__1_once, _init_l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply___closed__1);
if (v_isShared_1327_ == 0)
{
lean_ctor_set_tag(v___x_1326_, 7);
lean_ctor_set(v___x_1326_, 1, v___x_1351_);
lean_ctor_set(v___x_1326_, 0, v___x_1350_);
v___x_1353_ = v___x_1326_;
goto v_reusejp_1352_;
}
else
{
lean_object* v_reuseFailAlloc_1365_; 
v_reuseFailAlloc_1365_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1365_, 0, v___x_1350_);
lean_ctor_set(v_reuseFailAlloc_1365_, 1, v___x_1351_);
v___x_1353_ = v_reuseFailAlloc_1365_;
goto v_reusejp_1352_;
}
v_reusejp_1352_:
{
lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; 
v___x_1354_ = l_Lean_MessageData_ofExpr(v_a_1343_);
v___x_1355_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1355_, 0, v___x_1353_);
lean_ctor_set(v___x_1355_, 1, v___x_1354_);
v___x_1356_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__1___redArg(v___x_1355_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_);
if (lean_obj_tag(v___x_1356_) == 0)
{
lean_dec_ref_known(v___x_1356_, 1);
goto v___jp_1328_;
}
else
{
lean_object* v_a_1357_; lean_object* v___x_1359_; uint8_t v_isShared_1360_; uint8_t v_isSharedCheck_1364_; 
lean_dec(v_fst_1323_);
lean_del_object(v___x_1321_);
lean_dec(v_a_1314_);
v_a_1357_ = lean_ctor_get(v___x_1356_, 0);
v_isSharedCheck_1364_ = !lean_is_exclusive(v___x_1356_);
if (v_isSharedCheck_1364_ == 0)
{
v___x_1359_ = v___x_1356_;
v_isShared_1360_ = v_isSharedCheck_1364_;
goto v_resetjp_1358_;
}
else
{
lean_inc(v_a_1357_);
lean_dec(v___x_1356_);
v___x_1359_ = lean_box(0);
v_isShared_1360_ = v_isSharedCheck_1364_;
goto v_resetjp_1358_;
}
v_resetjp_1358_:
{
lean_object* v___x_1362_; 
if (v_isShared_1360_ == 0)
{
v___x_1362_ = v___x_1359_;
goto v_reusejp_1361_;
}
else
{
lean_object* v_reuseFailAlloc_1363_; 
v_reuseFailAlloc_1363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1363_, 0, v_a_1357_);
v___x_1362_ = v_reuseFailAlloc_1363_;
goto v_reusejp_1361_;
}
v_reusejp_1361_:
{
return v___x_1362_;
}
}
}
}
}
}
else
{
lean_dec(v_a_1343_);
lean_del_object(v___x_1335_);
lean_del_object(v___x_1326_);
lean_dec(v_introThm_1304_);
goto v___jp_1328_;
}
}
else
{
lean_object* v_a_1367_; lean_object* v___x_1369_; uint8_t v_isShared_1370_; uint8_t v_isSharedCheck_1374_; 
lean_dec(v_a_1343_);
lean_del_object(v___x_1335_);
lean_del_object(v___x_1326_);
lean_dec(v_fst_1323_);
lean_del_object(v___x_1321_);
lean_dec(v_a_1314_);
lean_dec(v_introThm_1304_);
v_a_1367_ = lean_ctor_get(v___x_1344_, 0);
v_isSharedCheck_1374_ = !lean_is_exclusive(v___x_1344_);
if (v_isSharedCheck_1374_ == 0)
{
v___x_1369_ = v___x_1344_;
v_isShared_1370_ = v_isSharedCheck_1374_;
goto v_resetjp_1368_;
}
else
{
lean_inc(v_a_1367_);
lean_dec(v___x_1344_);
v___x_1369_ = lean_box(0);
v_isShared_1370_ = v_isSharedCheck_1374_;
goto v_resetjp_1368_;
}
v_resetjp_1368_:
{
lean_object* v___x_1372_; 
if (v_isShared_1370_ == 0)
{
v___x_1372_ = v___x_1369_;
goto v_reusejp_1371_;
}
else
{
lean_object* v_reuseFailAlloc_1373_; 
v_reuseFailAlloc_1373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1373_, 0, v_a_1367_);
v___x_1372_ = v_reuseFailAlloc_1373_;
goto v_reusejp_1371_;
}
v_reusejp_1371_:
{
return v___x_1372_;
}
}
}
}
else
{
lean_del_object(v___x_1335_);
lean_dec(v_snd_1333_);
lean_del_object(v___x_1326_);
lean_dec(v_fst_1323_);
lean_del_object(v___x_1321_);
lean_dec(v_a_1314_);
lean_dec(v_introThm_1304_);
return v___x_1342_;
}
}
}
}
}
else
{
lean_object* v_a_1379_; lean_object* v___x_1381_; uint8_t v_isShared_1382_; uint8_t v_isSharedCheck_1386_; 
lean_dec(v_a_1314_);
lean_dec_ref(v_pre_1306_);
lean_dec_ref(v_opAs_1305_);
lean_dec(v_introThm_1304_);
v_a_1379_ = lean_ctor_get(v___x_1318_, 0);
v_isSharedCheck_1386_ = !lean_is_exclusive(v___x_1318_);
if (v_isSharedCheck_1386_ == 0)
{
v___x_1381_ = v___x_1318_;
v_isShared_1382_ = v_isSharedCheck_1386_;
goto v_resetjp_1380_;
}
else
{
lean_inc(v_a_1379_);
lean_dec(v___x_1318_);
v___x_1381_ = lean_box(0);
v_isShared_1382_ = v_isSharedCheck_1386_;
goto v_resetjp_1380_;
}
v_resetjp_1380_:
{
lean_object* v___x_1384_; 
if (v_isShared_1382_ == 0)
{
v___x_1384_ = v___x_1381_;
goto v_reusejp_1383_;
}
else
{
lean_object* v_reuseFailAlloc_1385_; 
v_reuseFailAlloc_1385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1385_, 0, v_a_1379_);
v___x_1384_ = v_reuseFailAlloc_1385_;
goto v_reusejp_1383_;
}
v_reusejp_1383_:
{
return v___x_1384_;
}
}
}
}
else
{
lean_dec(v_a_1314_);
lean_dec_ref(v_pre_1306_);
lean_dec_ref(v_opAs_1305_);
lean_dec(v_introThm_1304_);
return v___x_1315_;
}
}
else
{
lean_dec_ref(v_pre_1306_);
lean_dec_ref(v_opAs_1305_);
lean_dec(v_introThm_1304_);
return v___x_1313_;
}
}
else
{
lean_object* v___x_1387_; lean_object* v_s_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v_init_1391_; lean_object* v___x_1392_; lean_object* v_Q_1393_; lean_object* v___x_1394_; 
v___x_1387_ = l_Lean_instInhabitedExpr;
v_s_1388_ = l_List_getLast_x21___redArg(v___x_1387_, v_ss_1307_);
v___x_1389_ = lean_array_mk(v_ss_1307_);
v___x_1390_ = lean_array_pop(v___x_1389_);
v_init_1391_ = lean_array_to_list(v___x_1390_);
lean_inc(v_init_1391_);
v___x_1392_ = lean_array_mk(v_init_1391_);
lean_inc_ref(v_opAs_1305_);
v_Q_1393_ = l_Lean_mkAppN(v_opAs_1305_, v___x_1392_);
lean_dec_ref(v___x_1392_);
lean_inc(v_a_1311_);
lean_inc_ref(v_a_1310_);
lean_inc(v_a_1309_);
lean_inc_ref(v_a_1308_);
lean_inc_ref(v_pre_1306_);
v___x_1394_ = lean_infer_type(v_pre_1306_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_);
if (lean_obj_tag(v___x_1394_) == 0)
{
lean_object* v_a_1395_; lean_object* v___f_1396_; lean_object* v___x_1397_; 
v_a_1395_ = lean_ctor_get(v___x_1394_, 0);
lean_inc(v_a_1395_);
lean_dec_ref_known(v___x_1394_, 1);
lean_inc_ref(v_pre_1306_);
lean_inc_n(v_s_1388_, 2);
v___f_1396_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply___lam__0___boxed), 9, 3);
lean_closure_set(v___f_1396_, 0, v_s_1388_);
lean_closure_set(v___f_1396_, 1, v_a_1395_);
lean_closure_set(v___f_1396_, 2, v_pre_1306_);
lean_inc(v_a_1311_);
lean_inc_ref(v_a_1310_);
lean_inc(v_a_1309_);
lean_inc_ref(v_a_1308_);
v___x_1397_ = lean_infer_type(v_s_1388_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_);
if (lean_obj_tag(v___x_1397_) == 0)
{
lean_object* v_a_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; 
v_a_1398_ = lean_ctor_get(v___x_1397_, 0);
lean_inc(v_a_1398_);
lean_dec_ref_known(v___x_1397_, 1);
v___x_1399_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply___closed__3));
v___x_1400_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply_spec__0___redArg(v___x_1399_, v_a_1398_, v___f_1396_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_);
if (lean_obj_tag(v___x_1400_) == 0)
{
lean_object* v_a_1401_; lean_object* v___x_1402_; 
v_a_1401_ = lean_ctor_get(v___x_1400_, 0);
lean_inc(v_a_1401_);
lean_dec_ref_known(v___x_1400_, 1);
v___x_1402_ = l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply(v_introThm_1304_, v_opAs_1305_, v_a_1401_, v_init_1391_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_);
if (lean_obj_tag(v___x_1402_) == 0)
{
lean_object* v_a_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; 
v_a_1403_ = lean_ctor_get(v___x_1402_, 0);
lean_inc(v_a_1403_);
lean_dec_ref_known(v___x_1402_, 1);
v___x_1404_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply___closed__5));
v___x_1405_ = lean_unsigned_to_nat(4u);
v___x_1406_ = lean_mk_empty_array_with_capacity(v___x_1405_);
v___x_1407_ = lean_array_push(v___x_1406_, v_s_1388_);
v___x_1408_ = lean_array_push(v___x_1407_, v_pre_1306_);
v___x_1409_ = lean_array_push(v___x_1408_, v_Q_1393_);
v___x_1410_ = lean_array_push(v___x_1409_, v_a_1403_);
v___x_1411_ = l_Lean_Meta_mkAppM(v___x_1404_, v___x_1410_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_);
return v___x_1411_;
}
else
{
lean_dec_ref(v_Q_1393_);
lean_dec(v_s_1388_);
lean_dec_ref(v_pre_1306_);
return v___x_1402_;
}
}
else
{
lean_dec_ref(v_Q_1393_);
lean_dec(v_init_1391_);
lean_dec(v_s_1388_);
lean_dec_ref(v_pre_1306_);
lean_dec_ref(v_opAs_1305_);
lean_dec(v_introThm_1304_);
return v___x_1400_;
}
}
else
{
lean_dec_ref(v___f_1396_);
lean_dec_ref(v_Q_1393_);
lean_dec(v_init_1391_);
lean_dec(v_s_1388_);
lean_dec_ref(v_pre_1306_);
lean_dec_ref(v_opAs_1305_);
lean_dec(v_introThm_1304_);
return v___x_1397_;
}
}
else
{
lean_dec_ref(v_Q_1393_);
lean_dec(v_init_1391_);
lean_dec(v_s_1388_);
lean_dec_ref(v_pre_1306_);
lean_dec_ref(v_opAs_1305_);
lean_dec(v_introThm_1304_);
return v___x_1394_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply___boxed(lean_object* v_introThm_1412_, lean_object* v_opAs_1413_, lean_object* v_pre_1414_, lean_object* v_ss_1415_, lean_object* v_a_1416_, lean_object* v_a_1417_, lean_object* v_a_1418_, lean_object* v_a_1419_, lean_object* v_a_1420_){
_start:
{
lean_object* v_res_1421_; 
v_res_1421_ = l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply(v_introThm_1412_, v_opAs_1413_, v_pre_1414_, v_ss_1415_, v_a_1416_, v_a_1417_, v_a_1418_, v_a_1419_);
lean_dec(v_a_1419_);
lean_dec_ref(v_a_1418_);
lean_dec(v_a_1417_);
lean_dec_ref(v_a_1416_);
return v_res_1421_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply_spec__0_spec__0(lean_object* v_00_u03b1_1422_, lean_object* v_name_1423_, uint8_t v_bi_1424_, lean_object* v_type_1425_, lean_object* v_k_1426_, uint8_t v_kind_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_){
_start:
{
lean_object* v___x_1433_; 
v___x_1433_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply_spec__0_spec__0___redArg(v_name_1423_, v_bi_1424_, v_type_1425_, v_k_1426_, v_kind_1427_, v___y_1428_, v___y_1429_, v___y_1430_, v___y_1431_);
return v___x_1433_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1434_, lean_object* v_name_1435_, lean_object* v_bi_1436_, lean_object* v_type_1437_, lean_object* v_k_1438_, lean_object* v_kind_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_){
_start:
{
uint8_t v_bi_boxed_1445_; uint8_t v_kind_boxed_1446_; lean_object* v_res_1447_; 
v_bi_boxed_1445_ = lean_unbox(v_bi_1436_);
v_kind_boxed_1446_ = lean_unbox(v_kind_1439_);
v_res_1447_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply_spec__0_spec__0(v_00_u03b1_1434_, v_name_1435_, v_bi_boxed_1445_, v_type_1437_, v_k_1438_, v_kind_boxed_1446_, v___y_1440_, v___y_1441_, v___y_1442_, v___y_1443_);
lean_dec(v___y_1443_);
lean_dec_ref(v___y_1442_);
lean_dec(v___y_1441_);
lean_dec_ref(v___y_1440_);
return v_res_1447_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply_spec__0(lean_object* v_00_u03b1_1448_, lean_object* v_name_1449_, lean_object* v_type_1450_, lean_object* v_k_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_){
_start:
{
lean_object* v___x_1457_; 
v___x_1457_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply_spec__0___redArg(v_name_1449_, v_type_1450_, v_k_1451_, v___y_1452_, v___y_1453_, v___y_1454_, v___y_1455_);
return v___x_1457_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply_spec__0___boxed(lean_object* v_00_u03b1_1458_, lean_object* v_name_1459_, lean_object* v_type_1460_, lean_object* v_k_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_){
_start:
{
lean_object* v_res_1467_; 
v_res_1467_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply_spec__0(v_00_u03b1_1458_, v_name_1459_, v_type_1460_, v_k_1461_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_);
lean_dec(v___y_1465_);
lean_dec_ref(v___y_1464_);
lean_dec(v___y_1463_);
lean_dec_ref(v___y_1462_);
return v_res_1467_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__0___redArg(size_t v_sz_1468_, size_t v_i_1469_, lean_object* v_bs_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_){
_start:
{
uint8_t v___x_1476_; 
v___x_1476_ = lean_usize_dec_lt(v_i_1469_, v_sz_1468_);
if (v___x_1476_ == 0)
{
lean_object* v___x_1477_; 
v___x_1477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1477_, 0, v_bs_1470_);
return v___x_1477_;
}
else
{
lean_object* v_v_1478_; lean_object* v___x_1479_; lean_object* v_bs_x27_1480_; lean_object* v___y_1482_; lean_object* v___x_1496_; 
v_v_1478_ = lean_array_uget(v_bs_1470_, v_i_1469_);
v___x_1479_ = lean_unsigned_to_nat(0u);
v_bs_x27_1480_ = lean_array_uset(v_bs_1470_, v_i_1469_, v___x_1479_);
lean_inc(v___y_1474_);
lean_inc_ref(v___y_1473_);
lean_inc(v___y_1472_);
lean_inc_ref(v___y_1471_);
v___x_1496_ = lean_infer_type(v_v_1478_, v___y_1471_, v___y_1472_, v___y_1473_, v___y_1474_);
if (lean_obj_tag(v___x_1496_) == 0)
{
lean_object* v_a_1497_; lean_object* v___x_1499_; uint8_t v_isShared_1500_; uint8_t v_isSharedCheck_1507_; 
v_a_1497_ = lean_ctor_get(v___x_1496_, 0);
v_isSharedCheck_1507_ = !lean_is_exclusive(v___x_1496_);
if (v_isSharedCheck_1507_ == 0)
{
v___x_1499_ = v___x_1496_;
v_isShared_1500_ = v_isSharedCheck_1507_;
goto v_resetjp_1498_;
}
else
{
lean_inc(v_a_1497_);
lean_dec(v___x_1496_);
v___x_1499_ = lean_box(0);
v_isShared_1500_ = v_isSharedCheck_1507_;
goto v_resetjp_1498_;
}
v_resetjp_1498_:
{
lean_object* v___x_1502_; 
if (v_isShared_1500_ == 0)
{
lean_ctor_set_tag(v___x_1499_, 1);
v___x_1502_ = v___x_1499_;
goto v_reusejp_1501_;
}
else
{
lean_object* v_reuseFailAlloc_1506_; 
v_reuseFailAlloc_1506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1506_, 0, v_a_1497_);
v___x_1502_ = v_reuseFailAlloc_1506_;
goto v_reusejp_1501_;
}
v_reusejp_1501_:
{
uint8_t v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; 
v___x_1503_ = 0;
v___x_1504_ = lean_box(0);
v___x_1505_ = l_Lean_Meta_mkFreshExprMVar(v___x_1502_, v___x_1503_, v___x_1504_, v___y_1471_, v___y_1472_, v___y_1473_, v___y_1474_);
v___y_1482_ = v___x_1505_;
goto v___jp_1481_;
}
}
}
else
{
v___y_1482_ = v___x_1496_;
goto v___jp_1481_;
}
v___jp_1481_:
{
if (lean_obj_tag(v___y_1482_) == 0)
{
lean_object* v_a_1483_; size_t v___x_1484_; size_t v___x_1485_; lean_object* v___x_1486_; 
v_a_1483_ = lean_ctor_get(v___y_1482_, 0);
lean_inc(v_a_1483_);
lean_dec_ref_known(v___y_1482_, 1);
v___x_1484_ = ((size_t)1ULL);
v___x_1485_ = lean_usize_add(v_i_1469_, v___x_1484_);
v___x_1486_ = lean_array_uset(v_bs_x27_1480_, v_i_1469_, v_a_1483_);
v_i_1469_ = v___x_1485_;
v_bs_1470_ = v___x_1486_;
goto _start;
}
else
{
lean_object* v_a_1488_; lean_object* v___x_1490_; uint8_t v_isShared_1491_; uint8_t v_isSharedCheck_1495_; 
lean_dec_ref(v_bs_x27_1480_);
v_a_1488_ = lean_ctor_get(v___y_1482_, 0);
v_isSharedCheck_1495_ = !lean_is_exclusive(v___y_1482_);
if (v_isSharedCheck_1495_ == 0)
{
v___x_1490_ = v___y_1482_;
v_isShared_1491_ = v_isSharedCheck_1495_;
goto v_resetjp_1489_;
}
else
{
lean_inc(v_a_1488_);
lean_dec(v___y_1482_);
v___x_1490_ = lean_box(0);
v_isShared_1491_ = v_isSharedCheck_1495_;
goto v_resetjp_1489_;
}
v_resetjp_1489_:
{
lean_object* v___x_1493_; 
if (v_isShared_1491_ == 0)
{
v___x_1493_ = v___x_1490_;
goto v_reusejp_1492_;
}
else
{
lean_object* v_reuseFailAlloc_1494_; 
v_reuseFailAlloc_1494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1494_, 0, v_a_1488_);
v___x_1493_ = v_reuseFailAlloc_1494_;
goto v_reusejp_1492_;
}
v_reusejp_1492_:
{
return v___x_1493_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__0___redArg___boxed(lean_object* v_sz_1508_, lean_object* v_i_1509_, lean_object* v_bs_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_){
_start:
{
size_t v_sz_boxed_1516_; size_t v_i_boxed_1517_; lean_object* v_res_1518_; 
v_sz_boxed_1516_ = lean_unbox_usize(v_sz_1508_);
lean_dec(v_sz_1508_);
v_i_boxed_1517_ = lean_unbox_usize(v_i_1509_);
lean_dec(v_i_1509_);
v_res_1518_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__0___redArg(v_sz_boxed_1516_, v_i_boxed_1517_, v_bs_1510_, v___y_1511_, v___y_1512_, v___y_1513_, v___y_1514_);
lean_dec(v___y_1514_);
lean_dec_ref(v___y_1513_);
lean_dec(v___y_1512_);
lean_dec_ref(v___y_1511_);
return v_res_1518_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__1_spec__1___redArg(lean_object* v_a_1519_, lean_object* v_x_1520_){
_start:
{
if (lean_obj_tag(v_x_1520_) == 0)
{
lean_object* v___x_1521_; 
v___x_1521_ = lean_box(0);
return v___x_1521_;
}
else
{
lean_object* v_key_1522_; lean_object* v_value_1523_; lean_object* v_tail_1524_; uint8_t v___x_1525_; 
v_key_1522_ = lean_ctor_get(v_x_1520_, 0);
v_value_1523_ = lean_ctor_get(v_x_1520_, 1);
v_tail_1524_ = lean_ctor_get(v_x_1520_, 2);
v___x_1525_ = lean_name_eq(v_key_1522_, v_a_1519_);
if (v___x_1525_ == 0)
{
v_x_1520_ = v_tail_1524_;
goto _start;
}
else
{
lean_object* v___x_1527_; 
lean_inc(v_value_1523_);
v___x_1527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1527_, 0, v_value_1523_);
return v___x_1527_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__1_spec__1___redArg___boxed(lean_object* v_a_1528_, lean_object* v_x_1529_){
_start:
{
lean_object* v_res_1530_; 
v_res_1530_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__1_spec__1___redArg(v_a_1528_, v_x_1529_);
lean_dec(v_x_1529_);
lean_dec(v_a_1528_);
return v_res_1530_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__1___redArg(lean_object* v_m_1531_, lean_object* v_a_1532_){
_start:
{
lean_object* v_buckets_1533_; lean_object* v___x_1534_; uint64_t v___y_1536_; 
v_buckets_1533_ = lean_ctor_get(v_m_1531_, 1);
v___x_1534_ = lean_array_get_size(v_buckets_1533_);
if (lean_obj_tag(v_a_1532_) == 0)
{
uint64_t v___x_1550_; 
v___x_1550_ = 1723ULL;
v___y_1536_ = v___x_1550_;
goto v___jp_1535_;
}
else
{
uint64_t v_hash_1551_; 
v_hash_1551_ = lean_ctor_get_uint64(v_a_1532_, sizeof(void*)*2);
v___y_1536_ = v_hash_1551_;
goto v___jp_1535_;
}
v___jp_1535_:
{
uint64_t v___x_1537_; uint64_t v___x_1538_; uint64_t v_fold_1539_; uint64_t v___x_1540_; uint64_t v___x_1541_; uint64_t v___x_1542_; size_t v___x_1543_; size_t v___x_1544_; size_t v___x_1545_; size_t v___x_1546_; size_t v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; 
v___x_1537_ = 32ULL;
v___x_1538_ = lean_uint64_shift_right(v___y_1536_, v___x_1537_);
v_fold_1539_ = lean_uint64_xor(v___y_1536_, v___x_1538_);
v___x_1540_ = 16ULL;
v___x_1541_ = lean_uint64_shift_right(v_fold_1539_, v___x_1540_);
v___x_1542_ = lean_uint64_xor(v_fold_1539_, v___x_1541_);
v___x_1543_ = lean_uint64_to_usize(v___x_1542_);
v___x_1544_ = lean_usize_of_nat(v___x_1534_);
v___x_1545_ = ((size_t)1ULL);
v___x_1546_ = lean_usize_sub(v___x_1544_, v___x_1545_);
v___x_1547_ = lean_usize_land(v___x_1543_, v___x_1546_);
v___x_1548_ = lean_array_uget_borrowed(v_buckets_1533_, v___x_1547_);
v___x_1549_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__1_spec__1___redArg(v_a_1532_, v___x_1548_);
return v___x_1549_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__1___redArg___boxed(lean_object* v_m_1552_, lean_object* v_a_1553_){
_start:
{
lean_object* v_res_1554_; 
v_res_1554_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__1___redArg(v_m_1552_, v_a_1553_);
lean_dec(v_a_1553_);
lean_dec_ref(v_m_1552_);
return v_res_1554_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__2___closed__4(void){
_start:
{
lean_object* v___x_1561_; lean_object* v___x_1562_; 
v___x_1561_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__2___closed__3));
v___x_1562_ = l_Lean_stringToMessageData(v___x_1561_);
return v___x_1562_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__2___closed__6(void){
_start:
{
lean_object* v___x_1564_; lean_object* v___x_1565_; 
v___x_1564_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__2___closed__5));
v___x_1565_ = l_Lean_stringToMessageData(v___x_1564_);
return v___x_1565_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__2(lean_object* v_op_1566_, lean_object* v___y_1567_, lean_object* v_a_1568_, lean_object* v_x_1569_, lean_object* v_x_1570_, lean_object* v_x_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_){
_start:
{
lean_object* v_prf_1580_; lean_object* v___y_1581_; lean_object* v___y_1582_; lean_object* v___y_1583_; lean_object* v___y_1584_; 
if (lean_obj_tag(v_x_1569_) == 5)
{
lean_object* v_fn_1601_; lean_object* v_arg_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; 
v_fn_1601_ = lean_ctor_get(v_x_1569_, 0);
lean_inc_ref(v_fn_1601_);
v_arg_1602_ = lean_ctor_get(v_x_1569_, 1);
lean_inc_ref(v_arg_1602_);
lean_dec_ref_known(v_x_1569_, 2);
v___x_1603_ = lean_array_set(v_x_1570_, v_x_1571_, v_arg_1602_);
v___x_1604_ = lean_unsigned_to_nat(1u);
v___x_1605_ = lean_nat_sub(v_x_1571_, v___x_1604_);
lean_dec(v_x_1571_);
v_x_1569_ = v_fn_1601_;
v_x_1570_ = v___x_1603_;
v_x_1571_ = v___x_1605_;
goto _start;
}
else
{
lean_object* v_head_1607_; lean_object* v_numConst_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; size_t v_sz_1612_; size_t v___x_1613_; lean_object* v___x_1614_; 
lean_dec(v_x_1571_);
v_head_1607_ = lean_ctor_get(v_op_1566_, 0);
lean_inc(v_head_1607_);
v_numConst_1608_ = lean_ctor_get(v_op_1566_, 1);
lean_inc_n(v_numConst_1608_, 2);
lean_dec_ref(v_op_1566_);
v___x_1609_ = lean_unsigned_to_nat(0u);
v___x_1610_ = lean_array_get_size(v_x_1570_);
v___x_1611_ = l_Array_extract___redArg(v_x_1570_, v_numConst_1608_, v___x_1610_);
v_sz_1612_ = lean_array_size(v___x_1611_);
v___x_1613_ = ((size_t)0ULL);
v___x_1614_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__0___redArg(v_sz_1612_, v___x_1613_, v___x_1611_, v___y_1574_, v___y_1575_, v___y_1576_, v___y_1577_);
if (lean_obj_tag(v___x_1614_) == 0)
{
lean_object* v_a_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; 
v_a_1615_ = lean_ctor_get(v___x_1614_, 0);
lean_inc(v_a_1615_);
lean_dec_ref_known(v___x_1614_, 1);
v___x_1616_ = l_Array_extract___redArg(v_x_1570_, v___x_1609_, v_numConst_1608_);
lean_dec_ref(v_x_1570_);
v___x_1617_ = l_Array_append___redArg(v___x_1616_, v_a_1615_);
lean_dec(v_a_1615_);
v___x_1618_ = l_Lean_mkAppN(v_x_1569_, v___x_1617_);
lean_dec_ref(v___x_1617_);
v___x_1619_ = lean_unsigned_to_nat(256u);
lean_inc_ref(v___x_1618_);
v___x_1620_ = l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp(v___y_1567_, v___x_1618_, v___x_1619_, v___y_1572_, v___y_1573_, v___y_1574_, v___y_1575_, v___y_1576_, v___y_1577_);
if (lean_obj_tag(v___x_1620_) == 0)
{
lean_object* v_a_1621_; lean_object* v_fst_1622_; lean_object* v_snd_1623_; lean_object* v___x_1625_; uint8_t v_isShared_1626_; uint8_t v_isSharedCheck_1795_; 
v_a_1621_ = lean_ctor_get(v___x_1620_, 0);
lean_inc(v_a_1621_);
lean_dec_ref_known(v___x_1620_, 1);
v_fst_1622_ = lean_ctor_get(v_a_1621_, 0);
v_snd_1623_ = lean_ctor_get(v_a_1621_, 1);
v_isSharedCheck_1795_ = !lean_is_exclusive(v_a_1621_);
if (v_isSharedCheck_1795_ == 0)
{
v___x_1625_ = v_a_1621_;
v_isShared_1626_ = v_isSharedCheck_1795_;
goto v_resetjp_1624_;
}
else
{
lean_inc(v_snd_1623_);
lean_inc(v_fst_1622_);
lean_dec(v_a_1621_);
v___x_1625_ = lean_box(0);
v_isShared_1626_ = v_isSharedCheck_1795_;
goto v_resetjp_1624_;
}
v_resetjp_1624_:
{
lean_object* v___x_1627_; 
lean_inc(v___y_1577_);
lean_inc_ref(v___y_1576_);
lean_inc(v___y_1575_);
lean_inc_ref(v___y_1574_);
v___x_1627_ = lean_infer_type(v___x_1618_, v___y_1574_, v___y_1575_, v___y_1576_, v___y_1577_);
if (lean_obj_tag(v___x_1627_) == 0)
{
lean_object* v_a_1628_; lean_object* v___x_1629_; uint8_t v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; 
v_a_1628_ = lean_ctor_get(v___x_1627_, 0);
lean_inc(v_a_1628_);
lean_dec_ref_known(v___x_1627_, 1);
v___x_1629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1629_, 0, v_a_1628_);
v___x_1630_ = 0;
v___x_1631_ = lean_box(0);
v___x_1632_ = l_Lean_Meta_mkFreshExprMVar(v___x_1629_, v___x_1630_, v___x_1631_, v___y_1574_, v___y_1575_, v___y_1576_, v___y_1577_);
if (lean_obj_tag(v___x_1632_) == 0)
{
lean_object* v_a_1633_; lean_object* v___y_1635_; lean_object* v___y_1636_; lean_object* v___y_1637_; lean_object* v___y_1638_; lean_object* v___y_1639_; lean_object* v___y_1640_; lean_object* v_a_1641_; lean_object* v___y_1689_; lean_object* v_eqProof_1690_; lean_object* v___y_1691_; lean_object* v___y_1692_; lean_object* v___y_1693_; lean_object* v___y_1694_; lean_object* v___x_1722_; lean_object* v___y_1724_; lean_object* v___x_1777_; 
v_a_1633_ = lean_ctor_get(v___x_1632_, 0);
lean_inc(v_a_1633_);
lean_dec_ref_known(v___x_1632_, 1);
v___x_1722_ = l_Lean_Expr_getAppFn(v_fst_1622_);
v___x_1777_ = l_Lean_Expr_constName_x3f(v___x_1722_);
if (lean_obj_tag(v___x_1777_) == 0)
{
v___y_1724_ = v___x_1631_;
goto v___jp_1723_;
}
else
{
lean_object* v_val_1778_; 
v_val_1778_ = lean_ctor_get(v___x_1777_, 0);
lean_inc(v_val_1778_);
lean_dec_ref_known(v___x_1777_, 1);
v___y_1724_ = v_val_1778_;
goto v___jp_1723_;
}
v___jp_1634_:
{
lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; 
v___x_1642_ = lean_unsigned_to_nat(1u);
v___x_1643_ = lean_mk_empty_array_with_capacity(v___x_1642_);
lean_inc_ref(v___x_1643_);
v___x_1644_ = lean_array_push(v___x_1643_, v_a_1633_);
v___x_1645_ = l_Lean_Meta_mkAppM(v___y_1635_, v___x_1644_, v___y_1639_, v___y_1640_, v___y_1636_, v___y_1637_);
if (lean_obj_tag(v___x_1645_) == 0)
{
lean_object* v_a_1646_; lean_object* v___x_1647_; 
v_a_1646_ = lean_ctor_get(v___x_1645_, 0);
lean_inc(v_a_1646_);
lean_dec_ref_known(v___x_1645_, 1);
v___x_1647_ = l_Lean_Meta_mkCongrArg(v_a_1646_, v___y_1638_, v___y_1639_, v___y_1640_, v___y_1636_, v___y_1637_);
if (lean_obj_tag(v___x_1647_) == 0)
{
lean_object* v_a_1648_; lean_object* v___x_1649_; 
v_a_1648_ = lean_ctor_get(v___x_1647_, 0);
lean_inc(v_a_1648_);
lean_dec_ref_known(v___x_1647_, 1);
v___x_1649_ = l_Lean_Meta_mkEqSymm(v_a_1648_, v___y_1639_, v___y_1640_, v___y_1636_, v___y_1637_);
if (lean_obj_tag(v___x_1649_) == 0)
{
lean_object* v_a_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; 
v_a_1650_ = lean_ctor_get(v___x_1649_, 0);
lean_inc(v_a_1650_);
lean_dec_ref_known(v___x_1649_, 1);
v___x_1651_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__2___closed__2));
v___x_1652_ = lean_array_push(v___x_1643_, v_a_1650_);
v___x_1653_ = l_Lean_Meta_mkAppM(v___x_1651_, v___x_1652_, v___y_1639_, v___y_1640_, v___y_1636_, v___y_1637_);
if (lean_obj_tag(v___x_1653_) == 0)
{
lean_object* v_a_1654_; lean_object* v___x_1655_; 
v_a_1654_ = lean_ctor_get(v___x_1653_, 0);
lean_inc(v_a_1654_);
lean_dec_ref_known(v___x_1653_, 1);
v___x_1655_ = l_Lean_Expr_app___override(v_a_1654_, v_a_1641_);
v_prf_1580_ = v___x_1655_;
v___y_1581_ = v___y_1639_;
v___y_1582_ = v___y_1640_;
v___y_1583_ = v___y_1636_;
v___y_1584_ = v___y_1637_;
goto v___jp_1579_;
}
else
{
lean_object* v_a_1656_; lean_object* v___x_1658_; uint8_t v_isShared_1659_; uint8_t v_isSharedCheck_1663_; 
lean_dec_ref(v_a_1641_);
v_a_1656_ = lean_ctor_get(v___x_1653_, 0);
v_isSharedCheck_1663_ = !lean_is_exclusive(v___x_1653_);
if (v_isSharedCheck_1663_ == 0)
{
v___x_1658_ = v___x_1653_;
v_isShared_1659_ = v_isSharedCheck_1663_;
goto v_resetjp_1657_;
}
else
{
lean_inc(v_a_1656_);
lean_dec(v___x_1653_);
v___x_1658_ = lean_box(0);
v_isShared_1659_ = v_isSharedCheck_1663_;
goto v_resetjp_1657_;
}
v_resetjp_1657_:
{
lean_object* v___x_1661_; 
if (v_isShared_1659_ == 0)
{
v___x_1661_ = v___x_1658_;
goto v_reusejp_1660_;
}
else
{
lean_object* v_reuseFailAlloc_1662_; 
v_reuseFailAlloc_1662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1662_, 0, v_a_1656_);
v___x_1661_ = v_reuseFailAlloc_1662_;
goto v_reusejp_1660_;
}
v_reusejp_1660_:
{
return v___x_1661_;
}
}
}
}
else
{
lean_object* v_a_1664_; lean_object* v___x_1666_; uint8_t v_isShared_1667_; uint8_t v_isSharedCheck_1671_; 
lean_dec_ref(v___x_1643_);
lean_dec_ref(v_a_1641_);
v_a_1664_ = lean_ctor_get(v___x_1649_, 0);
v_isSharedCheck_1671_ = !lean_is_exclusive(v___x_1649_);
if (v_isSharedCheck_1671_ == 0)
{
v___x_1666_ = v___x_1649_;
v_isShared_1667_ = v_isSharedCheck_1671_;
goto v_resetjp_1665_;
}
else
{
lean_inc(v_a_1664_);
lean_dec(v___x_1649_);
v___x_1666_ = lean_box(0);
v_isShared_1667_ = v_isSharedCheck_1671_;
goto v_resetjp_1665_;
}
v_resetjp_1665_:
{
lean_object* v___x_1669_; 
if (v_isShared_1667_ == 0)
{
v___x_1669_ = v___x_1666_;
goto v_reusejp_1668_;
}
else
{
lean_object* v_reuseFailAlloc_1670_; 
v_reuseFailAlloc_1670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1670_, 0, v_a_1664_);
v___x_1669_ = v_reuseFailAlloc_1670_;
goto v_reusejp_1668_;
}
v_reusejp_1668_:
{
return v___x_1669_;
}
}
}
}
else
{
lean_object* v_a_1672_; lean_object* v___x_1674_; uint8_t v_isShared_1675_; uint8_t v_isSharedCheck_1679_; 
lean_dec_ref(v___x_1643_);
lean_dec_ref(v_a_1641_);
v_a_1672_ = lean_ctor_get(v___x_1647_, 0);
v_isSharedCheck_1679_ = !lean_is_exclusive(v___x_1647_);
if (v_isSharedCheck_1679_ == 0)
{
v___x_1674_ = v___x_1647_;
v_isShared_1675_ = v_isSharedCheck_1679_;
goto v_resetjp_1673_;
}
else
{
lean_inc(v_a_1672_);
lean_dec(v___x_1647_);
v___x_1674_ = lean_box(0);
v_isShared_1675_ = v_isSharedCheck_1679_;
goto v_resetjp_1673_;
}
v_resetjp_1673_:
{
lean_object* v___x_1677_; 
if (v_isShared_1675_ == 0)
{
v___x_1677_ = v___x_1674_;
goto v_reusejp_1676_;
}
else
{
lean_object* v_reuseFailAlloc_1678_; 
v_reuseFailAlloc_1678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1678_, 0, v_a_1672_);
v___x_1677_ = v_reuseFailAlloc_1678_;
goto v_reusejp_1676_;
}
v_reusejp_1676_:
{
return v___x_1677_;
}
}
}
}
else
{
lean_object* v_a_1680_; lean_object* v___x_1682_; uint8_t v_isShared_1683_; uint8_t v_isSharedCheck_1687_; 
lean_dec_ref(v___x_1643_);
lean_dec_ref(v_a_1641_);
lean_dec_ref(v___y_1638_);
v_a_1680_ = lean_ctor_get(v___x_1645_, 0);
v_isSharedCheck_1687_ = !lean_is_exclusive(v___x_1645_);
if (v_isSharedCheck_1687_ == 0)
{
v___x_1682_ = v___x_1645_;
v_isShared_1683_ = v_isSharedCheck_1687_;
goto v_resetjp_1681_;
}
else
{
lean_inc(v_a_1680_);
lean_dec(v___x_1645_);
v___x_1682_ = lean_box(0);
v_isShared_1683_ = v_isSharedCheck_1687_;
goto v_resetjp_1681_;
}
v_resetjp_1681_:
{
lean_object* v___x_1685_; 
if (v_isShared_1683_ == 0)
{
v___x_1685_ = v___x_1682_;
goto v_reusejp_1684_;
}
else
{
lean_object* v_reuseFailAlloc_1686_; 
v_reuseFailAlloc_1686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1686_, 0, v_a_1680_);
v___x_1685_ = v_reuseFailAlloc_1686_;
goto v_reusejp_1684_;
}
v_reusejp_1684_:
{
return v___x_1685_;
}
}
}
}
v___jp_1688_:
{
lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; 
v___x_1695_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__2));
v___x_1696_ = lean_unsigned_to_nat(2u);
v___x_1697_ = lean_mk_empty_array_with_capacity(v___x_1696_);
lean_inc(v_a_1633_);
v___x_1698_ = lean_array_push(v___x_1697_, v_a_1633_);
v___x_1699_ = lean_array_push(v___x_1698_, v_fst_1622_);
v___x_1700_ = l_Lean_Meta_mkAppM(v___x_1695_, v___x_1699_, v___y_1691_, v___y_1692_, v___y_1693_, v___y_1694_);
if (lean_obj_tag(v___x_1700_) == 0)
{
if (lean_obj_tag(v___y_1689_) == 0)
{
lean_object* v_a_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; 
v_a_1701_ = lean_ctor_get(v___x_1700_, 0);
lean_inc(v_a_1701_);
lean_dec_ref_known(v___x_1700_, 1);
v___x_1702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1702_, 0, v_a_1701_);
v___x_1703_ = l_Lean_Meta_mkFreshExprMVar(v___x_1702_, v___x_1630_, v___x_1631_, v___y_1691_, v___y_1692_, v___y_1693_, v___y_1694_);
if (lean_obj_tag(v___x_1703_) == 0)
{
lean_object* v_a_1704_; 
v_a_1704_ = lean_ctor_get(v___x_1703_, 0);
lean_inc(v_a_1704_);
lean_dec_ref_known(v___x_1703_, 1);
v___y_1635_ = v___x_1695_;
v___y_1636_ = v___y_1693_;
v___y_1637_ = v___y_1694_;
v___y_1638_ = v_eqProof_1690_;
v___y_1639_ = v___y_1691_;
v___y_1640_ = v___y_1692_;
v_a_1641_ = v_a_1704_;
goto v___jp_1634_;
}
else
{
lean_object* v_a_1705_; lean_object* v___x_1707_; uint8_t v_isShared_1708_; uint8_t v_isSharedCheck_1712_; 
lean_dec_ref(v_eqProof_1690_);
lean_dec(v_a_1633_);
v_a_1705_ = lean_ctor_get(v___x_1703_, 0);
v_isSharedCheck_1712_ = !lean_is_exclusive(v___x_1703_);
if (v_isSharedCheck_1712_ == 0)
{
v___x_1707_ = v___x_1703_;
v_isShared_1708_ = v_isSharedCheck_1712_;
goto v_resetjp_1706_;
}
else
{
lean_inc(v_a_1705_);
lean_dec(v___x_1703_);
v___x_1707_ = lean_box(0);
v_isShared_1708_ = v_isSharedCheck_1712_;
goto v_resetjp_1706_;
}
v_resetjp_1706_:
{
lean_object* v___x_1710_; 
if (v_isShared_1708_ == 0)
{
v___x_1710_ = v___x_1707_;
goto v_reusejp_1709_;
}
else
{
lean_object* v_reuseFailAlloc_1711_; 
v_reuseFailAlloc_1711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1711_, 0, v_a_1705_);
v___x_1710_ = v_reuseFailAlloc_1711_;
goto v_reusejp_1709_;
}
v_reusejp_1709_:
{
return v___x_1710_;
}
}
}
}
else
{
lean_object* v_val_1713_; 
lean_dec_ref_known(v___x_1700_, 1);
v_val_1713_ = lean_ctor_get(v___y_1689_, 0);
lean_inc(v_val_1713_);
lean_dec_ref_known(v___y_1689_, 1);
v___y_1635_ = v___x_1695_;
v___y_1636_ = v___y_1693_;
v___y_1637_ = v___y_1694_;
v___y_1638_ = v_eqProof_1690_;
v___y_1639_ = v___y_1691_;
v___y_1640_ = v___y_1692_;
v_a_1641_ = v_val_1713_;
goto v___jp_1634_;
}
}
else
{
lean_object* v_a_1714_; lean_object* v___x_1716_; uint8_t v_isShared_1717_; uint8_t v_isSharedCheck_1721_; 
lean_dec_ref(v_eqProof_1690_);
lean_dec(v___y_1689_);
lean_dec(v_a_1633_);
v_a_1714_ = lean_ctor_get(v___x_1700_, 0);
v_isSharedCheck_1721_ = !lean_is_exclusive(v___x_1700_);
if (v_isSharedCheck_1721_ == 0)
{
v___x_1716_ = v___x_1700_;
v_isShared_1717_ = v_isSharedCheck_1721_;
goto v_resetjp_1715_;
}
else
{
lean_inc(v_a_1714_);
lean_dec(v___x_1700_);
v___x_1716_ = lean_box(0);
v_isShared_1717_ = v_isSharedCheck_1721_;
goto v_resetjp_1715_;
}
v_resetjp_1715_:
{
lean_object* v___x_1719_; 
if (v_isShared_1717_ == 0)
{
v___x_1719_ = v___x_1716_;
goto v_reusejp_1718_;
}
else
{
lean_object* v_reuseFailAlloc_1720_; 
v_reuseFailAlloc_1720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1720_, 0, v_a_1714_);
v___x_1719_ = v_reuseFailAlloc_1720_;
goto v_reusejp_1718_;
}
v_reusejp_1718_:
{
return v___x_1719_;
}
}
}
}
v___jp_1723_:
{
lean_object* v___x_1725_; 
v___x_1725_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__1___redArg(v_a_1568_, v___y_1724_);
lean_dec(v___y_1724_);
if (lean_obj_tag(v___x_1725_) == 0)
{
lean_dec_ref(v___x_1722_);
if (lean_obj_tag(v_snd_1623_) == 0)
{
lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1729_; 
lean_dec(v_a_1633_);
lean_dec(v_fst_1622_);
v___x_1726_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__2___closed__4, &l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__2___closed__4_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__2___closed__4);
v___x_1727_ = l_Lean_MessageData_ofName(v_head_1607_);
if (v_isShared_1626_ == 0)
{
lean_ctor_set_tag(v___x_1625_, 7);
lean_ctor_set(v___x_1625_, 1, v___x_1727_);
lean_ctor_set(v___x_1625_, 0, v___x_1726_);
v___x_1729_ = v___x_1625_;
goto v_reusejp_1728_;
}
else
{
lean_object* v_reuseFailAlloc_1741_; 
v_reuseFailAlloc_1741_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1741_, 0, v___x_1726_);
lean_ctor_set(v_reuseFailAlloc_1741_, 1, v___x_1727_);
v___x_1729_ = v_reuseFailAlloc_1741_;
goto v_reusejp_1728_;
}
v_reusejp_1728_:
{
lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v_a_1733_; lean_object* v___x_1735_; uint8_t v_isShared_1736_; uint8_t v_isSharedCheck_1740_; 
v___x_1730_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__2___closed__6, &l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__2___closed__6_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__2___closed__6);
v___x_1731_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1731_, 0, v___x_1729_);
lean_ctor_set(v___x_1731_, 1, v___x_1730_);
v___x_1732_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_go_spec__0___redArg(v___x_1731_, v___y_1574_, v___y_1575_, v___y_1576_, v___y_1577_);
v_a_1733_ = lean_ctor_get(v___x_1732_, 0);
v_isSharedCheck_1740_ = !lean_is_exclusive(v___x_1732_);
if (v_isSharedCheck_1740_ == 0)
{
v___x_1735_ = v___x_1732_;
v_isShared_1736_ = v_isSharedCheck_1740_;
goto v_resetjp_1734_;
}
else
{
lean_inc(v_a_1733_);
lean_dec(v___x_1732_);
v___x_1735_ = lean_box(0);
v_isShared_1736_ = v_isSharedCheck_1740_;
goto v_resetjp_1734_;
}
v_resetjp_1734_:
{
lean_object* v___x_1738_; 
if (v_isShared_1736_ == 0)
{
v___x_1738_ = v___x_1735_;
goto v_reusejp_1737_;
}
else
{
lean_object* v_reuseFailAlloc_1739_; 
v_reuseFailAlloc_1739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1739_, 0, v_a_1733_);
v___x_1738_ = v_reuseFailAlloc_1739_;
goto v_reusejp_1737_;
}
v_reusejp_1737_:
{
return v___x_1738_;
}
}
}
}
else
{
lean_object* v_val_1742_; lean_object* v___x_1743_; 
lean_del_object(v___x_1625_);
lean_dec(v_head_1607_);
v_val_1742_ = lean_ctor_get(v_snd_1623_, 0);
lean_inc(v_val_1742_);
lean_dec_ref_known(v_snd_1623_, 1);
v___x_1743_ = lean_box(0);
v___y_1689_ = v___x_1743_;
v_eqProof_1690_ = v_val_1742_;
v___y_1691_ = v___y_1574_;
v___y_1692_ = v___y_1575_;
v___y_1693_ = v___y_1576_;
v___y_1694_ = v___y_1577_;
goto v___jp_1688_;
}
}
else
{
lean_object* v_val_1744_; lean_object* v_fst_1745_; lean_object* v_snd_1746_; lean_object* v_dummy_1747_; lean_object* v_nargs_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; 
lean_del_object(v___x_1625_);
lean_dec(v_head_1607_);
v_val_1744_ = lean_ctor_get(v___x_1725_, 0);
lean_inc(v_val_1744_);
lean_dec_ref_known(v___x_1725_, 1);
v_fst_1745_ = lean_ctor_get(v_val_1744_, 0);
lean_inc(v_fst_1745_);
v_snd_1746_ = lean_ctor_get(v_val_1744_, 1);
lean_inc_n(v_snd_1746_, 2);
lean_dec(v_val_1744_);
v_dummy_1747_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_projectsRewritableOperand___closed__0, &l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_projectsRewritableOperand___closed__0_once, _init_l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_projectsRewritableOperand___closed__0);
v_nargs_1748_ = l_Lean_Expr_getAppNumArgs(v_fst_1622_);
lean_inc(v_nargs_1748_);
v___x_1749_ = lean_mk_array(v_nargs_1748_, v_dummy_1747_);
v___x_1750_ = lean_unsigned_to_nat(1u);
v___x_1751_ = lean_nat_sub(v_nargs_1748_, v___x_1750_);
lean_dec(v_nargs_1748_);
lean_inc(v_fst_1622_);
v___x_1752_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_fst_1622_, v___x_1749_, v___x_1751_);
v___x_1753_ = l_Array_extract___redArg(v___x_1752_, v___x_1609_, v_snd_1746_);
v___x_1754_ = l_Lean_mkAppN(v___x_1722_, v___x_1753_);
lean_dec_ref(v___x_1753_);
v___x_1755_ = lean_array_get_size(v___x_1752_);
v___x_1756_ = l_Array_extract___redArg(v___x_1752_, v_snd_1746_, v___x_1755_);
lean_dec_ref(v___x_1752_);
v___x_1757_ = lean_array_to_list(v___x_1756_);
lean_inc(v_a_1633_);
v___x_1758_ = l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply(v_fst_1745_, v___x_1754_, v_a_1633_, v___x_1757_, v___y_1574_, v___y_1575_, v___y_1576_, v___y_1577_);
if (lean_obj_tag(v___x_1758_) == 0)
{
if (lean_obj_tag(v_snd_1623_) == 0)
{
lean_object* v_a_1759_; 
lean_dec(v_a_1633_);
lean_dec(v_fst_1622_);
v_a_1759_ = lean_ctor_get(v___x_1758_, 0);
lean_inc(v_a_1759_);
lean_dec_ref_known(v___x_1758_, 1);
v_prf_1580_ = v_a_1759_;
v___y_1581_ = v___y_1574_;
v___y_1582_ = v___y_1575_;
v___y_1583_ = v___y_1576_;
v___y_1584_ = v___y_1577_;
goto v___jp_1579_;
}
else
{
lean_object* v_a_1760_; lean_object* v_val_1761_; lean_object* v___x_1763_; uint8_t v_isShared_1764_; uint8_t v_isSharedCheck_1768_; 
v_a_1760_ = lean_ctor_get(v___x_1758_, 0);
lean_inc(v_a_1760_);
lean_dec_ref_known(v___x_1758_, 1);
v_val_1761_ = lean_ctor_get(v_snd_1623_, 0);
v_isSharedCheck_1768_ = !lean_is_exclusive(v_snd_1623_);
if (v_isSharedCheck_1768_ == 0)
{
v___x_1763_ = v_snd_1623_;
v_isShared_1764_ = v_isSharedCheck_1768_;
goto v_resetjp_1762_;
}
else
{
lean_inc(v_val_1761_);
lean_dec(v_snd_1623_);
v___x_1763_ = lean_box(0);
v_isShared_1764_ = v_isSharedCheck_1768_;
goto v_resetjp_1762_;
}
v_resetjp_1762_:
{
lean_object* v___x_1766_; 
if (v_isShared_1764_ == 0)
{
lean_ctor_set(v___x_1763_, 0, v_a_1760_);
v___x_1766_ = v___x_1763_;
goto v_reusejp_1765_;
}
else
{
lean_object* v_reuseFailAlloc_1767_; 
v_reuseFailAlloc_1767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1767_, 0, v_a_1760_);
v___x_1766_ = v_reuseFailAlloc_1767_;
goto v_reusejp_1765_;
}
v_reusejp_1765_:
{
v___y_1689_ = v___x_1766_;
v_eqProof_1690_ = v_val_1761_;
v___y_1691_ = v___y_1574_;
v___y_1692_ = v___y_1575_;
v___y_1693_ = v___y_1576_;
v___y_1694_ = v___y_1577_;
goto v___jp_1688_;
}
}
}
}
else
{
lean_object* v_a_1769_; lean_object* v___x_1771_; uint8_t v_isShared_1772_; uint8_t v_isSharedCheck_1776_; 
lean_dec(v_a_1633_);
lean_dec(v_snd_1623_);
lean_dec(v_fst_1622_);
v_a_1769_ = lean_ctor_get(v___x_1758_, 0);
v_isSharedCheck_1776_ = !lean_is_exclusive(v___x_1758_);
if (v_isSharedCheck_1776_ == 0)
{
v___x_1771_ = v___x_1758_;
v_isShared_1772_ = v_isSharedCheck_1776_;
goto v_resetjp_1770_;
}
else
{
lean_inc(v_a_1769_);
lean_dec(v___x_1758_);
v___x_1771_ = lean_box(0);
v_isShared_1772_ = v_isSharedCheck_1776_;
goto v_resetjp_1770_;
}
v_resetjp_1770_:
{
lean_object* v___x_1774_; 
if (v_isShared_1772_ == 0)
{
v___x_1774_ = v___x_1771_;
goto v_reusejp_1773_;
}
else
{
lean_object* v_reuseFailAlloc_1775_; 
v_reuseFailAlloc_1775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1775_, 0, v_a_1769_);
v___x_1774_ = v_reuseFailAlloc_1775_;
goto v_reusejp_1773_;
}
v_reusejp_1773_:
{
return v___x_1774_;
}
}
}
}
}
}
else
{
lean_object* v_a_1779_; lean_object* v___x_1781_; uint8_t v_isShared_1782_; uint8_t v_isSharedCheck_1786_; 
lean_del_object(v___x_1625_);
lean_dec(v_snd_1623_);
lean_dec(v_fst_1622_);
lean_dec(v_head_1607_);
v_a_1779_ = lean_ctor_get(v___x_1632_, 0);
v_isSharedCheck_1786_ = !lean_is_exclusive(v___x_1632_);
if (v_isSharedCheck_1786_ == 0)
{
v___x_1781_ = v___x_1632_;
v_isShared_1782_ = v_isSharedCheck_1786_;
goto v_resetjp_1780_;
}
else
{
lean_inc(v_a_1779_);
lean_dec(v___x_1632_);
v___x_1781_ = lean_box(0);
v_isShared_1782_ = v_isSharedCheck_1786_;
goto v_resetjp_1780_;
}
v_resetjp_1780_:
{
lean_object* v___x_1784_; 
if (v_isShared_1782_ == 0)
{
v___x_1784_ = v___x_1781_;
goto v_reusejp_1783_;
}
else
{
lean_object* v_reuseFailAlloc_1785_; 
v_reuseFailAlloc_1785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1785_, 0, v_a_1779_);
v___x_1784_ = v_reuseFailAlloc_1785_;
goto v_reusejp_1783_;
}
v_reusejp_1783_:
{
return v___x_1784_;
}
}
}
}
else
{
lean_object* v_a_1787_; lean_object* v___x_1789_; uint8_t v_isShared_1790_; uint8_t v_isSharedCheck_1794_; 
lean_del_object(v___x_1625_);
lean_dec(v_snd_1623_);
lean_dec(v_fst_1622_);
lean_dec(v_head_1607_);
v_a_1787_ = lean_ctor_get(v___x_1627_, 0);
v_isSharedCheck_1794_ = !lean_is_exclusive(v___x_1627_);
if (v_isSharedCheck_1794_ == 0)
{
v___x_1789_ = v___x_1627_;
v_isShared_1790_ = v_isSharedCheck_1794_;
goto v_resetjp_1788_;
}
else
{
lean_inc(v_a_1787_);
lean_dec(v___x_1627_);
v___x_1789_ = lean_box(0);
v_isShared_1790_ = v_isSharedCheck_1794_;
goto v_resetjp_1788_;
}
v_resetjp_1788_:
{
lean_object* v___x_1792_; 
if (v_isShared_1790_ == 0)
{
v___x_1792_ = v___x_1789_;
goto v_reusejp_1791_;
}
else
{
lean_object* v_reuseFailAlloc_1793_; 
v_reuseFailAlloc_1793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1793_, 0, v_a_1787_);
v___x_1792_ = v_reuseFailAlloc_1793_;
goto v_reusejp_1791_;
}
v_reusejp_1791_:
{
return v___x_1792_;
}
}
}
}
}
else
{
lean_object* v_a_1796_; lean_object* v___x_1798_; uint8_t v_isShared_1799_; uint8_t v_isSharedCheck_1803_; 
lean_dec_ref(v___x_1618_);
lean_dec(v_head_1607_);
v_a_1796_ = lean_ctor_get(v___x_1620_, 0);
v_isSharedCheck_1803_ = !lean_is_exclusive(v___x_1620_);
if (v_isSharedCheck_1803_ == 0)
{
v___x_1798_ = v___x_1620_;
v_isShared_1799_ = v_isSharedCheck_1803_;
goto v_resetjp_1797_;
}
else
{
lean_inc(v_a_1796_);
lean_dec(v___x_1620_);
v___x_1798_ = lean_box(0);
v_isShared_1799_ = v_isSharedCheck_1803_;
goto v_resetjp_1797_;
}
v_resetjp_1797_:
{
lean_object* v___x_1801_; 
if (v_isShared_1799_ == 0)
{
v___x_1801_ = v___x_1798_;
goto v_reusejp_1800_;
}
else
{
lean_object* v_reuseFailAlloc_1802_; 
v_reuseFailAlloc_1802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1802_, 0, v_a_1796_);
v___x_1801_ = v_reuseFailAlloc_1802_;
goto v_reusejp_1800_;
}
v_reusejp_1800_:
{
return v___x_1801_;
}
}
}
}
else
{
lean_object* v_a_1804_; lean_object* v___x_1806_; uint8_t v_isShared_1807_; uint8_t v_isSharedCheck_1811_; 
lean_dec(v_numConst_1608_);
lean_dec(v_head_1607_);
lean_dec_ref(v_x_1570_);
lean_dec_ref(v_x_1569_);
v_a_1804_ = lean_ctor_get(v___x_1614_, 0);
v_isSharedCheck_1811_ = !lean_is_exclusive(v___x_1614_);
if (v_isSharedCheck_1811_ == 0)
{
v___x_1806_ = v___x_1614_;
v_isShared_1807_ = v_isSharedCheck_1811_;
goto v_resetjp_1805_;
}
else
{
lean_inc(v_a_1804_);
lean_dec(v___x_1614_);
v___x_1806_ = lean_box(0);
v_isShared_1807_ = v_isSharedCheck_1811_;
goto v_resetjp_1805_;
}
v_resetjp_1805_:
{
lean_object* v___x_1809_; 
if (v_isShared_1807_ == 0)
{
v___x_1809_ = v___x_1806_;
goto v_reusejp_1808_;
}
else
{
lean_object* v_reuseFailAlloc_1810_; 
v_reuseFailAlloc_1810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1810_, 0, v_a_1804_);
v___x_1809_ = v_reuseFailAlloc_1810_;
goto v_reusejp_1808_;
}
v_reusejp_1808_:
{
return v___x_1809_;
}
}
}
}
v___jp_1579_:
{
uint8_t v___x_1585_; lean_object* v___x_1586_; 
v___x_1585_ = 1;
v___x_1586_ = l_Lean_Meta_abstractMVars(v_prf_1580_, v___x_1585_, v___y_1581_, v___y_1582_, v___y_1583_, v___y_1584_);
if (lean_obj_tag(v___x_1586_) == 0)
{
lean_object* v_a_1587_; lean_object* v_paramNames_1588_; lean_object* v_expr_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; 
v_a_1587_ = lean_ctor_get(v___x_1586_, 0);
lean_inc(v_a_1587_);
lean_dec_ref_known(v___x_1586_, 1);
v_paramNames_1588_ = lean_ctor_get(v_a_1587_, 0);
lean_inc_ref(v_paramNames_1588_);
v_expr_1589_ = lean_ctor_get(v_a_1587_, 2);
lean_inc_ref(v_expr_1589_);
lean_dec(v_a_1587_);
v___x_1590_ = lean_array_to_list(v_paramNames_1588_);
v___x_1591_ = lean_box(0);
v___x_1592_ = l_Lean_Meta_Sym_mkBackwardRuleFromExpr(v_expr_1589_, v___x_1590_, v___x_1591_, v___y_1581_, v___y_1582_, v___y_1583_, v___y_1584_);
return v___x_1592_;
}
else
{
lean_object* v_a_1593_; lean_object* v___x_1595_; uint8_t v_isShared_1596_; uint8_t v_isSharedCheck_1600_; 
v_a_1593_ = lean_ctor_get(v___x_1586_, 0);
v_isSharedCheck_1600_ = !lean_is_exclusive(v___x_1586_);
if (v_isSharedCheck_1600_ == 0)
{
v___x_1595_ = v___x_1586_;
v_isShared_1596_ = v_isSharedCheck_1600_;
goto v_resetjp_1594_;
}
else
{
lean_inc(v_a_1593_);
lean_dec(v___x_1586_);
v___x_1595_ = lean_box(0);
v_isShared_1596_ = v_isSharedCheck_1600_;
goto v_resetjp_1594_;
}
v_resetjp_1594_:
{
lean_object* v___x_1598_; 
if (v_isShared_1596_ == 0)
{
v___x_1598_ = v___x_1595_;
goto v_reusejp_1597_;
}
else
{
lean_object* v_reuseFailAlloc_1599_; 
v_reuseFailAlloc_1599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1599_, 0, v_a_1593_);
v___x_1598_ = v_reuseFailAlloc_1599_;
goto v_reusejp_1597_;
}
v_reusejp_1597_:
{
return v___x_1598_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__2___boxed(lean_object* v_op_1812_, lean_object* v___y_1813_, lean_object* v_a_1814_, lean_object* v_x_1815_, lean_object* v_x_1816_, lean_object* v_x_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_){
_start:
{
lean_object* v_res_1825_; 
v_res_1825_ = l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__2(v_op_1812_, v___y_1813_, v_a_1814_, v_x_1815_, v_x_1816_, v_x_1817_, v___y_1818_, v___y_1819_, v___y_1820_, v___y_1821_, v___y_1822_, v___y_1823_);
lean_dec(v___y_1823_);
lean_dec_ref(v___y_1822_);
lean_dec(v___y_1821_);
lean_dec_ref(v___y_1820_);
lean_dec(v___y_1819_);
lean_dec_ref(v___y_1818_);
lean_dec_ref(v_a_1814_);
lean_dec_ref(v___y_1813_);
return v_res_1825_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__4(lean_object* v_as_1826_, size_t v_i_1827_, size_t v_stop_1828_, lean_object* v_b_1829_){
_start:
{
uint8_t v___x_1830_; 
v___x_1830_ = lean_usize_dec_eq(v_i_1827_, v_stop_1828_);
if (v___x_1830_ == 0)
{
lean_object* v___x_1831_; lean_object* v_rewrites_1832_; lean_object* v___x_1833_; size_t v___x_1834_; size_t v___x_1835_; 
v___x_1831_ = lean_array_uget_borrowed(v_as_1826_, v_i_1827_);
v_rewrites_1832_ = lean_ctor_get(v___x_1831_, 2);
v___x_1833_ = l_Array_append___redArg(v_b_1829_, v_rewrites_1832_);
v___x_1834_ = ((size_t)1ULL);
v___x_1835_ = lean_usize_add(v_i_1827_, v___x_1834_);
v_i_1827_ = v___x_1835_;
v_b_1829_ = v___x_1833_;
goto _start;
}
else
{
return v_b_1829_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__4___boxed(lean_object* v_as_1837_, lean_object* v_i_1838_, lean_object* v_stop_1839_, lean_object* v_b_1840_){
_start:
{
size_t v_i_boxed_1841_; size_t v_stop_boxed_1842_; lean_object* v_res_1843_; 
v_i_boxed_1841_ = lean_unbox_usize(v_i_1838_);
lean_dec(v_i_1838_);
v_stop_boxed_1842_ = lean_unbox_usize(v_stop_1839_);
lean_dec(v_stop_1839_);
v_res_1843_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__4(v_as_1837_, v_i_boxed_1841_, v_stop_boxed_1842_, v_b_1840_);
lean_dec_ref(v_as_1837_);
return v_res_1843_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__3(lean_object* v_as_1846_, size_t v_i_1847_, size_t v_stop_1848_, lean_object* v_b_1849_){
_start:
{
lean_object* v___y_1851_; uint8_t v___x_1855_; 
v___x_1855_ = lean_usize_dec_eq(v_i_1847_, v_stop_1848_);
if (v___x_1855_ == 0)
{
lean_object* v___x_1856_; lean_object* v_terminal_x3f_1857_; 
v___x_1856_ = lean_array_uget_borrowed(v_as_1846_, v_i_1847_);
v_terminal_x3f_1857_ = lean_ctor_get(v___x_1856_, 3);
if (lean_obj_tag(v_terminal_x3f_1857_) == 0)
{
lean_object* v___x_1858_; lean_object* v___x_1859_; 
v___x_1858_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__3___closed__0));
v___x_1859_ = l_Array_append___redArg(v_b_1849_, v___x_1858_);
v___y_1851_ = v___x_1859_;
goto v___jp_1850_;
}
else
{
lean_object* v_val_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; 
v_val_1860_ = lean_ctor_get(v_terminal_x3f_1857_, 0);
v___x_1861_ = lean_unsigned_to_nat(1u);
v___x_1862_ = lean_mk_empty_array_with_capacity(v___x_1861_);
lean_inc(v_val_1860_);
v___x_1863_ = lean_array_push(v___x_1862_, v_val_1860_);
v___x_1864_ = l_Array_append___redArg(v_b_1849_, v___x_1863_);
lean_dec_ref(v___x_1863_);
v___y_1851_ = v___x_1864_;
goto v___jp_1850_;
}
}
else
{
return v_b_1849_;
}
v___jp_1850_:
{
size_t v___x_1852_; size_t v___x_1853_; 
v___x_1852_ = ((size_t)1ULL);
v___x_1853_ = lean_usize_add(v_i_1847_, v___x_1852_);
v_i_1847_ = v___x_1853_;
v_b_1849_ = v___y_1851_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__3___boxed(lean_object* v_as_1865_, lean_object* v_i_1866_, lean_object* v_stop_1867_, lean_object* v_b_1868_){
_start:
{
size_t v_i_boxed_1869_; size_t v_stop_boxed_1870_; lean_object* v_res_1871_; 
v_i_boxed_1869_ = lean_unbox_usize(v_i_1866_);
lean_dec(v_i_1866_);
v_stop_boxed_1870_ = lean_unbox_usize(v_stop_1867_);
lean_dec(v_stop_1867_);
v_res_1871_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__3(v_as_1865_, v_i_boxed_1869_, v_stop_boxed_1870_, v_b_1868_);
lean_dec_ref(v_as_1865_);
return v_res_1871_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_mkLatticeOpRule___closed__0(void){
_start:
{
lean_object* v___x_1872_; size_t v___x_1873_; size_t v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; 
v___x_1872_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__3___closed__0));
v___x_1873_ = lean_usize_once(&l_Lean_Elab_Tactic_VCGen_latticeOps___closed__5, &l_Lean_Elab_Tactic_VCGen_latticeOps___closed__5_once, _init_l_Lean_Elab_Tactic_VCGen_latticeOps___closed__5);
v___x_1874_ = ((size_t)0ULL);
v___x_1875_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_builtinLatticeOps));
v___x_1876_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__3(v___x_1875_, v___x_1874_, v___x_1873_, v___x_1872_);
return v___x_1876_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_mkLatticeOpRule(lean_object* v_rhs_1877_, lean_object* v_op_1878_, lean_object* v_a_1879_, lean_object* v_a_1880_, lean_object* v_a_1881_, lean_object* v_a_1882_, lean_object* v_a_1883_, lean_object* v_a_1884_){
_start:
{
lean_object* v___y_1887_; lean_object* v___y_1888_; lean_object* v___y_1889_; lean_object* v_rewrites_1907_; lean_object* v_terminal_x3f_1908_; lean_object* v___x_1909_; lean_object* v___y_1911_; lean_object* v___y_1912_; lean_object* v___y_1919_; uint8_t v___x_1925_; 
v_rewrites_1907_ = lean_ctor_get(v_op_1878_, 2);
v_terminal_x3f_1908_ = lean_ctor_get(v_op_1878_, 3);
v___x_1909_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_builtinLatticeOps));
v___x_1925_ = lean_uint8_once(&l_Lean_Elab_Tactic_VCGen_latticeOps___closed__3, &l_Lean_Elab_Tactic_VCGen_latticeOps___closed__3_once, _init_l_Lean_Elab_Tactic_VCGen_latticeOps___closed__3);
if (v___x_1925_ == 0)
{
lean_inc_ref(v_rewrites_1907_);
v___y_1919_ = v_rewrites_1907_;
goto v___jp_1918_;
}
else
{
uint8_t v___x_1926_; 
v___x_1926_ = lean_uint8_once(&l_Lean_Elab_Tactic_VCGen_latticeOps___closed__4, &l_Lean_Elab_Tactic_VCGen_latticeOps___closed__4_once, _init_l_Lean_Elab_Tactic_VCGen_latticeOps___closed__4);
if (v___x_1926_ == 0)
{
if (v___x_1925_ == 0)
{
lean_inc_ref(v_rewrites_1907_);
v___y_1919_ = v_rewrites_1907_;
goto v___jp_1918_;
}
else
{
size_t v___x_1927_; size_t v___x_1928_; lean_object* v___x_1929_; 
v___x_1927_ = ((size_t)0ULL);
v___x_1928_ = lean_usize_once(&l_Lean_Elab_Tactic_VCGen_latticeOps___closed__5, &l_Lean_Elab_Tactic_VCGen_latticeOps___closed__5_once, _init_l_Lean_Elab_Tactic_VCGen_latticeOps___closed__5);
lean_inc_ref(v_rewrites_1907_);
v___x_1929_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__4(v___x_1909_, v___x_1927_, v___x_1928_, v_rewrites_1907_);
v___y_1919_ = v___x_1929_;
goto v___jp_1918_;
}
}
else
{
size_t v___x_1930_; size_t v___x_1931_; lean_object* v___x_1932_; 
v___x_1930_ = ((size_t)0ULL);
v___x_1931_ = lean_usize_once(&l_Lean_Elab_Tactic_VCGen_latticeOps___closed__5, &l_Lean_Elab_Tactic_VCGen_latticeOps___closed__5_once, _init_l_Lean_Elab_Tactic_VCGen_latticeOps___closed__5);
lean_inc_ref(v_rewrites_1907_);
v___x_1932_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__4(v___x_1909_, v___x_1930_, v___x_1931_, v_rewrites_1907_);
v___y_1919_ = v___x_1932_;
goto v___jp_1918_;
}
}
v___jp_1886_:
{
lean_object* v___x_1890_; lean_object* v___x_1891_; 
lean_inc_ref(v___y_1888_);
v___x_1890_ = l_Array_append___redArg(v___y_1888_, v___y_1889_);
lean_dec_ref(v___y_1889_);
v___x_1891_ = l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals(v___x_1890_, v_a_1881_, v_a_1882_, v_a_1883_, v_a_1884_);
lean_dec_ref(v___x_1890_);
if (lean_obj_tag(v___x_1891_) == 0)
{
lean_object* v_a_1892_; lean_object* v_dummy_1893_; lean_object* v_nargs_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; 
v_a_1892_ = lean_ctor_get(v___x_1891_, 0);
lean_inc(v_a_1892_);
lean_dec_ref_known(v___x_1891_, 1);
v_dummy_1893_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_projectsRewritableOperand___closed__0, &l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_projectsRewritableOperand___closed__0_once, _init_l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_projectsRewritableOperand___closed__0);
v_nargs_1894_ = l_Lean_Expr_getAppNumArgs(v_rhs_1877_);
lean_inc(v_nargs_1894_);
v___x_1895_ = lean_mk_array(v_nargs_1894_, v_dummy_1893_);
v___x_1896_ = lean_unsigned_to_nat(1u);
v___x_1897_ = lean_nat_sub(v_nargs_1894_, v___x_1896_);
lean_dec(v_nargs_1894_);
v___x_1898_ = l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__2(v_op_1878_, v___y_1887_, v_a_1892_, v_rhs_1877_, v___x_1895_, v___x_1897_, v_a_1879_, v_a_1880_, v_a_1881_, v_a_1882_, v_a_1883_, v_a_1884_);
lean_dec(v_a_1892_);
lean_dec_ref(v___y_1887_);
return v___x_1898_;
}
else
{
lean_object* v_a_1899_; lean_object* v___x_1901_; uint8_t v_isShared_1902_; uint8_t v_isSharedCheck_1906_; 
lean_dec_ref(v___y_1887_);
lean_dec_ref(v_op_1878_);
lean_dec_ref(v_rhs_1877_);
v_a_1899_ = lean_ctor_get(v___x_1891_, 0);
v_isSharedCheck_1906_ = !lean_is_exclusive(v___x_1891_);
if (v_isSharedCheck_1906_ == 0)
{
v___x_1901_ = v___x_1891_;
v_isShared_1902_ = v_isSharedCheck_1906_;
goto v_resetjp_1900_;
}
else
{
lean_inc(v_a_1899_);
lean_dec(v___x_1891_);
v___x_1901_ = lean_box(0);
v_isShared_1902_ = v_isSharedCheck_1906_;
goto v_resetjp_1900_;
}
v_resetjp_1900_:
{
lean_object* v___x_1904_; 
if (v_isShared_1902_ == 0)
{
v___x_1904_ = v___x_1901_;
goto v_reusejp_1903_;
}
else
{
lean_object* v_reuseFailAlloc_1905_; 
v_reuseFailAlloc_1905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1905_, 0, v_a_1899_);
v___x_1904_ = v_reuseFailAlloc_1905_;
goto v_reusejp_1903_;
}
v_reusejp_1903_:
{
return v___x_1904_;
}
}
}
}
v___jp_1910_:
{
if (lean_obj_tag(v_terminal_x3f_1908_) == 0)
{
lean_object* v___x_1913_; 
v___x_1913_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__3___closed__0));
v___y_1887_ = v___y_1911_;
v___y_1888_ = v___y_1912_;
v___y_1889_ = v___x_1913_;
goto v___jp_1886_;
}
else
{
lean_object* v_val_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; 
v_val_1914_ = lean_ctor_get(v_terminal_x3f_1908_, 0);
v___x_1915_ = lean_unsigned_to_nat(1u);
v___x_1916_ = lean_mk_empty_array_with_capacity(v___x_1915_);
lean_inc(v_val_1914_);
v___x_1917_ = lean_array_push(v___x_1916_, v_val_1914_);
v___y_1887_ = v___y_1911_;
v___y_1888_ = v___y_1912_;
v___y_1889_ = v___x_1917_;
goto v___jp_1886_;
}
}
v___jp_1918_:
{
lean_object* v___x_1920_; uint8_t v___x_1921_; 
v___x_1920_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__3___closed__0));
v___x_1921_ = lean_uint8_once(&l_Lean_Elab_Tactic_VCGen_latticeOps___closed__3, &l_Lean_Elab_Tactic_VCGen_latticeOps___closed__3_once, _init_l_Lean_Elab_Tactic_VCGen_latticeOps___closed__3);
if (v___x_1921_ == 0)
{
v___y_1911_ = v___y_1919_;
v___y_1912_ = v___x_1920_;
goto v___jp_1910_;
}
else
{
uint8_t v___x_1922_; 
v___x_1922_ = lean_uint8_once(&l_Lean_Elab_Tactic_VCGen_latticeOps___closed__4, &l_Lean_Elab_Tactic_VCGen_latticeOps___closed__4_once, _init_l_Lean_Elab_Tactic_VCGen_latticeOps___closed__4);
if (v___x_1922_ == 0)
{
if (v___x_1921_ == 0)
{
v___y_1911_ = v___y_1919_;
v___y_1912_ = v___x_1920_;
goto v___jp_1910_;
}
else
{
lean_object* v___x_1923_; 
v___x_1923_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_mkLatticeOpRule___closed__0, &l_Lean_Elab_Tactic_VCGen_mkLatticeOpRule___closed__0_once, _init_l_Lean_Elab_Tactic_VCGen_mkLatticeOpRule___closed__0);
v___y_1911_ = v___y_1919_;
v___y_1912_ = v___x_1923_;
goto v___jp_1910_;
}
}
else
{
lean_object* v___x_1924_; 
v___x_1924_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_mkLatticeOpRule___closed__0, &l_Lean_Elab_Tactic_VCGen_mkLatticeOpRule___closed__0_once, _init_l_Lean_Elab_Tactic_VCGen_mkLatticeOpRule___closed__0);
v___y_1911_ = v___y_1919_;
v___y_1912_ = v___x_1924_;
goto v___jp_1910_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_mkLatticeOpRule___boxed(lean_object* v_rhs_1933_, lean_object* v_op_1934_, lean_object* v_a_1935_, lean_object* v_a_1936_, lean_object* v_a_1937_, lean_object* v_a_1938_, lean_object* v_a_1939_, lean_object* v_a_1940_, lean_object* v_a_1941_){
_start:
{
lean_object* v_res_1942_; 
v_res_1942_ = l_Lean_Elab_Tactic_VCGen_mkLatticeOpRule(v_rhs_1933_, v_op_1934_, v_a_1935_, v_a_1936_, v_a_1937_, v_a_1938_, v_a_1939_, v_a_1940_);
lean_dec(v_a_1940_);
lean_dec_ref(v_a_1939_);
lean_dec(v_a_1938_);
lean_dec_ref(v_a_1937_);
lean_dec(v_a_1936_);
lean_dec_ref(v_a_1935_);
return v_res_1942_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__0(size_t v_sz_1943_, size_t v_i_1944_, lean_object* v_bs_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_){
_start:
{
lean_object* v___x_1953_; 
v___x_1953_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__0___redArg(v_sz_1943_, v_i_1944_, v_bs_1945_, v___y_1948_, v___y_1949_, v___y_1950_, v___y_1951_);
return v___x_1953_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__0___boxed(lean_object* v_sz_1954_, lean_object* v_i_1955_, lean_object* v_bs_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_){
_start:
{
size_t v_sz_boxed_1964_; size_t v_i_boxed_1965_; lean_object* v_res_1966_; 
v_sz_boxed_1964_ = lean_unbox_usize(v_sz_1954_);
lean_dec(v_sz_1954_);
v_i_boxed_1965_ = lean_unbox_usize(v_i_1955_);
lean_dec(v_i_1955_);
v_res_1966_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__0(v_sz_boxed_1964_, v_i_boxed_1965_, v_bs_1956_, v___y_1957_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_, v___y_1962_);
lean_dec(v___y_1962_);
lean_dec_ref(v___y_1961_);
lean_dec(v___y_1960_);
lean_dec_ref(v___y_1959_);
lean_dec(v___y_1958_);
lean_dec_ref(v___y_1957_);
return v_res_1966_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__1(lean_object* v_00_u03b2_1967_, lean_object* v_m_1968_, lean_object* v_a_1969_){
_start:
{
lean_object* v___x_1970_; 
v___x_1970_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__1___redArg(v_m_1968_, v_a_1969_);
return v___x_1970_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__1___boxed(lean_object* v_00_u03b2_1971_, lean_object* v_m_1972_, lean_object* v_a_1973_){
_start:
{
lean_object* v_res_1974_; 
v_res_1974_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__1(v_00_u03b2_1971_, v_m_1972_, v_a_1973_);
lean_dec(v_a_1973_);
lean_dec_ref(v_m_1972_);
return v_res_1974_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__1_spec__1(lean_object* v_00_u03b2_1975_, lean_object* v_a_1976_, lean_object* v_x_1977_){
_start:
{
lean_object* v___x_1978_; 
v___x_1978_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__1_spec__1___redArg(v_a_1976_, v_x_1977_);
return v___x_1978_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__1_spec__1___boxed(lean_object* v_00_u03b2_1979_, lean_object* v_a_1980_, lean_object* v_x_1981_){
_start:
{
lean_object* v_res_1982_; 
v_res_1982_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__1_spec__1(v_00_u03b2_1979_, v_a_1980_, v_x_1981_);
lean_dec(v_x_1981_);
lean_dec(v_a_1980_);
return v_res_1982_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_Apply(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_Order_Heyting(uint8_t builtin);
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
