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
static const lean_string_object l_Lean_Elab_Tactic_VCGen_LatticeOp_himp___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "le_himp_of_meet_le_left"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_himp___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_himp___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_himp___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_himp___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_himp___closed__6_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__2_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_himp___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_himp___closed__6_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_himp___closed__5_value),LEAN_SCALAR_PTR_LITERAL(175, 68, 87, 56, 106, 132, 75, 188)}};
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
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_ofProp___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_ofProp___closed__7_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_ofProp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(239, 140, 127, 117, 148, 144, 166, 107)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_ofProp___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_ofProp___closed__7_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_ofProp___closed__6_value),LEAN_SCALAR_PTR_LITERAL(176, 72, 220, 161, 159, 51, 212, 120)}};
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
static lean_once_cell_t l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp___closed__3;
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
lean_object* v___x_194_; lean_object* v_dummy_195_; 
v___x_194_ = lean_box(0);
v_dummy_195_ = l_Lean_Expr_sort___override(v___x_194_);
return v_dummy_195_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_projectsRewritableOperand(lean_object* v_rhs_203_){
_start:
{
lean_object* v_dummy_204_; lean_object* v_nargs_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; uint8_t v___x_212_; 
v_dummy_204_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_projectsRewritableOperand___closed__0, &l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_projectsRewritableOperand___closed__0_once, _init_l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_projectsRewritableOperand___closed__0);
v_nargs_205_ = l_Lean_Expr_getAppNumArgs(v_rhs_203_);
lean_inc(v_nargs_205_);
v___x_206_ = lean_mk_array(v_nargs_205_, v_dummy_204_);
v___x_207_ = lean_unsigned_to_nat(1u);
v___x_208_ = lean_nat_sub(v_nargs_205_, v___x_207_);
lean_dec(v_nargs_205_);
v___x_209_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_rhs_203_, v___x_206_, v___x_208_);
v___x_210_ = lean_unsigned_to_nat(2u);
v___x_211_ = lean_array_get_size(v___x_209_);
v___x_212_ = lean_nat_dec_lt(v___x_210_, v___x_211_);
if (v___x_212_ == 0)
{
lean_dec_ref(v___x_209_);
return v___x_212_;
}
else
{
lean_object* v___x_213_; lean_object* v___x_214_; 
v___x_213_ = lean_array_fget(v___x_209_, v___x_210_);
lean_dec_ref(v___x_209_);
v___x_214_ = l_Lean_Expr_getAppFn(v___x_213_);
if (lean_obj_tag(v___x_214_) == 4)
{
lean_object* v_declName_215_; 
v_declName_215_ = lean_ctor_get(v___x_214_, 0);
lean_inc(v_declName_215_);
lean_dec_ref_known(v___x_214_, 2);
if (lean_obj_tag(v_declName_215_) == 1)
{
lean_object* v_pre_216_; 
v_pre_216_ = lean_ctor_get(v_declName_215_, 0);
lean_inc(v_pre_216_);
if (lean_obj_tag(v_pre_216_) == 1)
{
lean_object* v_pre_217_; 
v_pre_217_ = lean_ctor_get(v_pre_216_, 0);
lean_inc(v_pre_217_);
if (lean_obj_tag(v_pre_217_) == 1)
{
lean_object* v_pre_218_; 
v_pre_218_ = lean_ctor_get(v_pre_217_, 0);
switch(lean_obj_tag(v_pre_218_))
{
case 0:
{
lean_object* v_str_219_; lean_object* v_str_220_; lean_object* v_str_221_; lean_object* v___x_222_; uint8_t v___x_223_; 
lean_dec(v___x_213_);
v_str_219_ = lean_ctor_get(v_declName_215_, 1);
lean_inc_ref(v_str_219_);
lean_dec_ref_known(v_declName_215_, 2);
v_str_220_ = lean_ctor_get(v_pre_216_, 1);
lean_inc_ref(v_str_220_);
lean_dec_ref_known(v_pre_216_, 2);
v_str_221_ = lean_ctor_get(v_pre_217_, 1);
lean_inc_ref(v_str_221_);
lean_dec_ref_known(v_pre_217_, 2);
v___x_222_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__1));
v___x_223_ = lean_string_dec_eq(v_str_221_, v___x_222_);
lean_dec_ref(v_str_221_);
if (v___x_223_ == 0)
{
lean_dec_ref(v_str_220_);
lean_dec_ref(v_str_219_);
return v___x_223_;
}
else
{
lean_object* v___x_224_; uint8_t v___x_225_; 
v___x_224_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__2));
v___x_225_ = lean_string_dec_eq(v_str_220_, v___x_224_);
lean_dec_ref(v_str_220_);
if (v___x_225_ == 0)
{
lean_dec_ref(v_str_219_);
return v___x_225_;
}
else
{
lean_object* v___x_226_; uint8_t v___x_227_; 
v___x_226_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_projectsRewritableOperand___closed__1));
v___x_227_ = lean_string_dec_eq(v_str_219_, v___x_226_);
if (v___x_227_ == 0)
{
lean_object* v___x_228_; uint8_t v___x_229_; 
v___x_228_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_LatticeOp_top___closed__0));
v___x_229_ = lean_string_dec_eq(v_str_219_, v___x_228_);
lean_dec_ref(v_str_219_);
return v___x_229_;
}
else
{
lean_dec_ref(v_str_219_);
return v___x_227_;
}
}
}
}
case 1:
{
lean_object* v_pre_230_; 
lean_inc_ref(v_pre_218_);
v_pre_230_ = lean_ctor_get(v_pre_218_, 0);
if (lean_obj_tag(v_pre_230_) == 0)
{
lean_object* v_str_231_; lean_object* v_str_232_; lean_object* v_str_233_; lean_object* v_str_234_; lean_object* v___x_235_; uint8_t v___x_236_; 
v_str_231_ = lean_ctor_get(v_declName_215_, 1);
lean_inc_ref(v_str_231_);
lean_dec_ref_known(v_declName_215_, 2);
v_str_232_ = lean_ctor_get(v_pre_216_, 1);
lean_inc_ref(v_str_232_);
lean_dec_ref_known(v_pre_216_, 2);
v_str_233_ = lean_ctor_get(v_pre_217_, 1);
lean_inc_ref(v_str_233_);
lean_dec_ref_known(v_pre_217_, 2);
v_str_234_ = lean_ctor_get(v_pre_218_, 1);
lean_inc_ref(v_str_234_);
lean_dec_ref_known(v_pre_218_, 2);
v___x_235_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__1));
v___x_236_ = lean_string_dec_eq(v_str_234_, v___x_235_);
lean_dec_ref(v_str_234_);
if (v___x_236_ == 0)
{
lean_dec_ref(v_str_233_);
lean_dec_ref(v_str_232_);
lean_dec_ref(v_str_231_);
lean_dec(v___x_213_);
return v___x_236_;
}
else
{
lean_object* v___x_237_; uint8_t v___x_238_; 
v___x_237_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__2));
v___x_238_ = lean_string_dec_eq(v_str_233_, v___x_237_);
lean_dec_ref(v_str_233_);
if (v___x_238_ == 0)
{
lean_dec_ref(v_str_232_);
lean_dec_ref(v_str_231_);
lean_dec(v___x_213_);
return v___x_238_;
}
else
{
lean_object* v___x_239_; uint8_t v___x_240_; 
v___x_239_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__3));
v___x_240_ = lean_string_dec_eq(v_str_232_, v___x_239_);
if (v___x_240_ == 0)
{
lean_object* v___x_241_; uint8_t v___x_242_; 
v___x_241_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__0));
v___x_242_ = lean_string_dec_eq(v_str_232_, v___x_241_);
lean_dec_ref(v_str_232_);
if (v___x_242_ == 0)
{
lean_dec_ref(v_str_231_);
lean_dec(v___x_213_);
return v___x_242_;
}
else
{
lean_object* v___x_243_; uint8_t v___x_244_; 
v___x_243_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__1));
v___x_244_ = lean_string_dec_eq(v_str_231_, v___x_243_);
lean_dec_ref(v_str_231_);
if (v___x_244_ == 0)
{
lean_dec(v___x_213_);
return v___x_244_;
}
else
{
lean_object* v_nargs_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; uint8_t v___x_250_; 
v_nargs_245_ = l_Lean_Expr_getAppNumArgs(v___x_213_);
lean_inc(v_nargs_245_);
v___x_246_ = lean_mk_array(v_nargs_245_, v_dummy_204_);
v___x_247_ = lean_nat_sub(v_nargs_245_, v___x_207_);
lean_dec(v_nargs_245_);
v___x_248_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v___x_213_, v___x_246_, v___x_247_);
v___x_249_ = lean_array_get_size(v___x_248_);
v___x_250_ = lean_nat_dec_lt(v___x_210_, v___x_249_);
if (v___x_250_ == 0)
{
lean_dec_ref(v___x_248_);
return v___x_240_;
}
else
{
lean_object* v___x_251_; lean_object* v___x_252_; uint8_t v___x_253_; 
v___x_251_ = lean_array_fget(v___x_248_, v___x_210_);
lean_dec_ref(v___x_248_);
v___x_252_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_projectsRewritableOperand___closed__3));
v___x_253_ = l_Lean_Expr_isAppOf(v___x_251_, v___x_252_);
lean_dec(v___x_251_);
return v___x_253_;
}
}
}
}
else
{
lean_object* v___x_254_; uint8_t v___x_255_; 
lean_dec_ref(v_str_232_);
lean_dec(v___x_213_);
v___x_254_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_projectsRewritableOperand___closed__2));
v___x_255_ = lean_string_dec_eq(v_str_231_, v___x_254_);
lean_dec_ref(v_str_231_);
return v___x_255_;
}
}
}
}
else
{
uint8_t v___x_256_; 
lean_dec_ref_known(v_pre_218_, 2);
lean_dec_ref_known(v_pre_217_, 2);
lean_dec_ref_known(v_pre_216_, 2);
lean_dec_ref_known(v_declName_215_, 2);
lean_dec(v___x_213_);
v___x_256_ = 0;
return v___x_256_;
}
}
default: 
{
uint8_t v___x_257_; 
lean_dec_ref_known(v_pre_217_, 2);
lean_dec_ref_known(v_pre_216_, 2);
lean_dec_ref_known(v_declName_215_, 2);
lean_dec(v___x_213_);
v___x_257_ = 0;
return v___x_257_;
}
}
}
else
{
uint8_t v___x_258_; 
lean_dec(v_pre_217_);
lean_dec_ref_known(v_pre_216_, 2);
lean_dec_ref_known(v_declName_215_, 2);
lean_dec(v___x_213_);
v___x_258_ = 0;
return v___x_258_;
}
}
else
{
uint8_t v___x_259_; 
lean_dec(v_pre_216_);
lean_dec_ref_known(v_declName_215_, 2);
lean_dec(v___x_213_);
v___x_259_ = 0;
return v___x_259_;
}
}
else
{
uint8_t v___x_260_; 
lean_dec(v_declName_215_);
lean_dec(v___x_213_);
v___x_260_ = 0;
return v___x_260_;
}
}
else
{
uint8_t v___x_261_; 
lean_dec_ref(v___x_214_);
lean_dec(v___x_213_);
v___x_261_ = 0;
return v___x_261_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_projectsRewritableOperand___boxed(lean_object* v_rhs_262_){
_start:
{
uint8_t v_res_263_; lean_object* v_r_264_; 
v_res_263_ = l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_projectsRewritableOperand(v_rhs_262_);
v_r_264_ = lean_box(v_res_263_);
return v_r_264_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0_spec__2___redArg(lean_object* v_a_409_, lean_object* v_b_410_, lean_object* v_x_411_){
_start:
{
if (lean_obj_tag(v_x_411_) == 0)
{
lean_dec(v_b_410_);
lean_dec(v_a_409_);
return v_x_411_;
}
else
{
lean_object* v_key_412_; lean_object* v_value_413_; lean_object* v_tail_414_; lean_object* v___x_416_; uint8_t v_isShared_417_; uint8_t v_isSharedCheck_426_; 
v_key_412_ = lean_ctor_get(v_x_411_, 0);
v_value_413_ = lean_ctor_get(v_x_411_, 1);
v_tail_414_ = lean_ctor_get(v_x_411_, 2);
v_isSharedCheck_426_ = !lean_is_exclusive(v_x_411_);
if (v_isSharedCheck_426_ == 0)
{
v___x_416_ = v_x_411_;
v_isShared_417_ = v_isSharedCheck_426_;
goto v_resetjp_415_;
}
else
{
lean_inc(v_tail_414_);
lean_inc(v_value_413_);
lean_inc(v_key_412_);
lean_dec(v_x_411_);
v___x_416_ = lean_box(0);
v_isShared_417_ = v_isSharedCheck_426_;
goto v_resetjp_415_;
}
v_resetjp_415_:
{
uint8_t v___x_418_; 
v___x_418_ = lean_name_eq(v_key_412_, v_a_409_);
if (v___x_418_ == 0)
{
lean_object* v___x_419_; lean_object* v___x_421_; 
v___x_419_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0_spec__2___redArg(v_a_409_, v_b_410_, v_tail_414_);
if (v_isShared_417_ == 0)
{
lean_ctor_set(v___x_416_, 2, v___x_419_);
v___x_421_ = v___x_416_;
goto v_reusejp_420_;
}
else
{
lean_object* v_reuseFailAlloc_422_; 
v_reuseFailAlloc_422_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_422_, 0, v_key_412_);
lean_ctor_set(v_reuseFailAlloc_422_, 1, v_value_413_);
lean_ctor_set(v_reuseFailAlloc_422_, 2, v___x_419_);
v___x_421_ = v_reuseFailAlloc_422_;
goto v_reusejp_420_;
}
v_reusejp_420_:
{
return v___x_421_;
}
}
else
{
lean_object* v___x_424_; 
lean_dec(v_value_413_);
lean_dec(v_key_412_);
if (v_isShared_417_ == 0)
{
lean_ctor_set(v___x_416_, 1, v_b_410_);
lean_ctor_set(v___x_416_, 0, v_a_409_);
v___x_424_ = v___x_416_;
goto v_reusejp_423_;
}
else
{
lean_object* v_reuseFailAlloc_425_; 
v_reuseFailAlloc_425_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_425_, 0, v_a_409_);
lean_ctor_set(v_reuseFailAlloc_425_, 1, v_b_410_);
lean_ctor_set(v_reuseFailAlloc_425_, 2, v_tail_414_);
v___x_424_ = v_reuseFailAlloc_425_;
goto v_reusejp_423_;
}
v_reusejp_423_:
{
return v___x_424_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0_spec__1_spec__2_spec__4___redArg(lean_object* v_x_427_, lean_object* v_x_428_){
_start:
{
if (lean_obj_tag(v_x_428_) == 0)
{
return v_x_427_;
}
else
{
lean_object* v_key_429_; lean_object* v_value_430_; lean_object* v_tail_431_; lean_object* v___x_433_; uint8_t v_isShared_434_; uint8_t v_isSharedCheck_457_; 
v_key_429_ = lean_ctor_get(v_x_428_, 0);
v_value_430_ = lean_ctor_get(v_x_428_, 1);
v_tail_431_ = lean_ctor_get(v_x_428_, 2);
v_isSharedCheck_457_ = !lean_is_exclusive(v_x_428_);
if (v_isSharedCheck_457_ == 0)
{
v___x_433_ = v_x_428_;
v_isShared_434_ = v_isSharedCheck_457_;
goto v_resetjp_432_;
}
else
{
lean_inc(v_tail_431_);
lean_inc(v_value_430_);
lean_inc(v_key_429_);
lean_dec(v_x_428_);
v___x_433_ = lean_box(0);
v_isShared_434_ = v_isSharedCheck_457_;
goto v_resetjp_432_;
}
v_resetjp_432_:
{
lean_object* v___x_435_; uint64_t v___y_437_; 
v___x_435_ = lean_array_get_size(v_x_427_);
if (lean_obj_tag(v_key_429_) == 0)
{
uint64_t v___x_455_; 
v___x_455_ = 1723ULL;
v___y_437_ = v___x_455_;
goto v___jp_436_;
}
else
{
uint64_t v_hash_456_; 
v_hash_456_ = lean_ctor_get_uint64(v_key_429_, sizeof(void*)*2);
v___y_437_ = v_hash_456_;
goto v___jp_436_;
}
v___jp_436_:
{
uint64_t v___x_438_; uint64_t v___x_439_; uint64_t v_fold_440_; uint64_t v___x_441_; uint64_t v___x_442_; uint64_t v___x_443_; size_t v___x_444_; size_t v___x_445_; size_t v___x_446_; size_t v___x_447_; size_t v___x_448_; lean_object* v___x_449_; lean_object* v___x_451_; 
v___x_438_ = 32ULL;
v___x_439_ = lean_uint64_shift_right(v___y_437_, v___x_438_);
v_fold_440_ = lean_uint64_xor(v___y_437_, v___x_439_);
v___x_441_ = 16ULL;
v___x_442_ = lean_uint64_shift_right(v_fold_440_, v___x_441_);
v___x_443_ = lean_uint64_xor(v_fold_440_, v___x_442_);
v___x_444_ = lean_uint64_to_usize(v___x_443_);
v___x_445_ = lean_usize_of_nat(v___x_435_);
v___x_446_ = ((size_t)1ULL);
v___x_447_ = lean_usize_sub(v___x_445_, v___x_446_);
v___x_448_ = lean_usize_land(v___x_444_, v___x_447_);
v___x_449_ = lean_array_uget_borrowed(v_x_427_, v___x_448_);
lean_inc(v___x_449_);
if (v_isShared_434_ == 0)
{
lean_ctor_set(v___x_433_, 2, v___x_449_);
v___x_451_ = v___x_433_;
goto v_reusejp_450_;
}
else
{
lean_object* v_reuseFailAlloc_454_; 
v_reuseFailAlloc_454_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_454_, 0, v_key_429_);
lean_ctor_set(v_reuseFailAlloc_454_, 1, v_value_430_);
lean_ctor_set(v_reuseFailAlloc_454_, 2, v___x_449_);
v___x_451_ = v_reuseFailAlloc_454_;
goto v_reusejp_450_;
}
v_reusejp_450_:
{
lean_object* v___x_452_; 
v___x_452_ = lean_array_uset(v_x_427_, v___x_448_, v___x_451_);
v_x_427_ = v___x_452_;
v_x_428_ = v_tail_431_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0_spec__1_spec__2___redArg(lean_object* v_i_458_, lean_object* v_source_459_, lean_object* v_target_460_){
_start:
{
lean_object* v___x_461_; uint8_t v___x_462_; 
v___x_461_ = lean_array_get_size(v_source_459_);
v___x_462_ = lean_nat_dec_lt(v_i_458_, v___x_461_);
if (v___x_462_ == 0)
{
lean_dec_ref(v_source_459_);
lean_dec(v_i_458_);
return v_target_460_;
}
else
{
lean_object* v_es_463_; lean_object* v___x_464_; lean_object* v_source_465_; lean_object* v_target_466_; lean_object* v___x_467_; lean_object* v___x_468_; 
v_es_463_ = lean_array_fget(v_source_459_, v_i_458_);
v___x_464_ = lean_box(0);
v_source_465_ = lean_array_fset(v_source_459_, v_i_458_, v___x_464_);
v_target_466_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0_spec__1_spec__2_spec__4___redArg(v_target_460_, v_es_463_);
v___x_467_ = lean_unsigned_to_nat(1u);
v___x_468_ = lean_nat_add(v_i_458_, v___x_467_);
lean_dec(v_i_458_);
v_i_458_ = v___x_468_;
v_source_459_ = v_source_465_;
v_target_460_ = v_target_466_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0_spec__1___redArg(lean_object* v_data_470_){
_start:
{
lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v_nbuckets_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; 
v___x_471_ = lean_array_get_size(v_data_470_);
v___x_472_ = lean_unsigned_to_nat(2u);
v_nbuckets_473_ = lean_nat_mul(v___x_471_, v___x_472_);
v___x_474_ = lean_unsigned_to_nat(0u);
v___x_475_ = lean_box(0);
v___x_476_ = lean_mk_array(v_nbuckets_473_, v___x_475_);
v___x_477_ = lean_array_propagate_mark(v_data_470_, v___x_476_);
v___x_478_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0_spec__1_spec__2___redArg(v___x_474_, v_data_470_, v___x_477_);
return v___x_478_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0_spec__0___redArg(lean_object* v_a_479_, lean_object* v_x_480_){
_start:
{
if (lean_obj_tag(v_x_480_) == 0)
{
uint8_t v___x_481_; 
v___x_481_ = 0;
return v___x_481_;
}
else
{
lean_object* v_key_482_; lean_object* v_tail_483_; uint8_t v___x_484_; 
v_key_482_ = lean_ctor_get(v_x_480_, 0);
v_tail_483_ = lean_ctor_get(v_x_480_, 2);
v___x_484_ = lean_name_eq(v_key_482_, v_a_479_);
if (v___x_484_ == 0)
{
v_x_480_ = v_tail_483_;
goto _start;
}
else
{
return v___x_484_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0_spec__0___redArg___boxed(lean_object* v_a_486_, lean_object* v_x_487_){
_start:
{
uint8_t v_res_488_; lean_object* v_r_489_; 
v_res_488_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0_spec__0___redArg(v_a_486_, v_x_487_);
lean_dec(v_x_487_);
lean_dec(v_a_486_);
v_r_489_ = lean_box(v_res_488_);
return v_r_489_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0___redArg(lean_object* v_m_490_, lean_object* v_a_491_, lean_object* v_b_492_){
_start:
{
lean_object* v_size_493_; lean_object* v_buckets_494_; lean_object* v___x_496_; uint8_t v_isShared_497_; uint8_t v_isSharedCheck_540_; 
v_size_493_ = lean_ctor_get(v_m_490_, 0);
v_buckets_494_ = lean_ctor_get(v_m_490_, 1);
v_isSharedCheck_540_ = !lean_is_exclusive(v_m_490_);
if (v_isSharedCheck_540_ == 0)
{
v___x_496_ = v_m_490_;
v_isShared_497_ = v_isSharedCheck_540_;
goto v_resetjp_495_;
}
else
{
lean_inc(v_buckets_494_);
lean_inc(v_size_493_);
lean_dec(v_m_490_);
v___x_496_ = lean_box(0);
v_isShared_497_ = v_isSharedCheck_540_;
goto v_resetjp_495_;
}
v_resetjp_495_:
{
lean_object* v___x_498_; uint64_t v___y_500_; 
v___x_498_ = lean_array_get_size(v_buckets_494_);
if (lean_obj_tag(v_a_491_) == 0)
{
uint64_t v___x_538_; 
v___x_538_ = 1723ULL;
v___y_500_ = v___x_538_;
goto v___jp_499_;
}
else
{
uint64_t v_hash_539_; 
v_hash_539_ = lean_ctor_get_uint64(v_a_491_, sizeof(void*)*2);
v___y_500_ = v_hash_539_;
goto v___jp_499_;
}
v___jp_499_:
{
uint64_t v___x_501_; uint64_t v___x_502_; uint64_t v_fold_503_; uint64_t v___x_504_; uint64_t v___x_505_; uint64_t v___x_506_; size_t v___x_507_; size_t v___x_508_; size_t v___x_509_; size_t v___x_510_; size_t v___x_511_; lean_object* v_bkt_512_; uint8_t v___x_513_; 
v___x_501_ = 32ULL;
v___x_502_ = lean_uint64_shift_right(v___y_500_, v___x_501_);
v_fold_503_ = lean_uint64_xor(v___y_500_, v___x_502_);
v___x_504_ = 16ULL;
v___x_505_ = lean_uint64_shift_right(v_fold_503_, v___x_504_);
v___x_506_ = lean_uint64_xor(v_fold_503_, v___x_505_);
v___x_507_ = lean_uint64_to_usize(v___x_506_);
v___x_508_ = lean_usize_of_nat(v___x_498_);
v___x_509_ = ((size_t)1ULL);
v___x_510_ = lean_usize_sub(v___x_508_, v___x_509_);
v___x_511_ = lean_usize_land(v___x_507_, v___x_510_);
v_bkt_512_ = lean_array_uget_borrowed(v_buckets_494_, v___x_511_);
v___x_513_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0_spec__0___redArg(v_a_491_, v_bkt_512_);
if (v___x_513_ == 0)
{
lean_object* v___x_514_; lean_object* v_size_x27_515_; lean_object* v___x_516_; lean_object* v_buckets_x27_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; uint8_t v___x_523_; 
v___x_514_ = lean_unsigned_to_nat(1u);
v_size_x27_515_ = lean_nat_add(v_size_493_, v___x_514_);
lean_dec(v_size_493_);
lean_inc(v_bkt_512_);
v___x_516_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_516_, 0, v_a_491_);
lean_ctor_set(v___x_516_, 1, v_b_492_);
lean_ctor_set(v___x_516_, 2, v_bkt_512_);
v_buckets_x27_517_ = lean_array_uset(v_buckets_494_, v___x_511_, v___x_516_);
v___x_518_ = lean_unsigned_to_nat(4u);
v___x_519_ = lean_nat_mul(v_size_x27_515_, v___x_518_);
v___x_520_ = lean_unsigned_to_nat(3u);
v___x_521_ = lean_nat_div(v___x_519_, v___x_520_);
lean_dec(v___x_519_);
v___x_522_ = lean_array_get_size(v_buckets_x27_517_);
v___x_523_ = lean_nat_dec_le(v___x_521_, v___x_522_);
lean_dec(v___x_521_);
if (v___x_523_ == 0)
{
lean_object* v_val_524_; lean_object* v___x_526_; 
v_val_524_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0_spec__1___redArg(v_buckets_x27_517_);
if (v_isShared_497_ == 0)
{
lean_ctor_set(v___x_496_, 1, v_val_524_);
lean_ctor_set(v___x_496_, 0, v_size_x27_515_);
v___x_526_ = v___x_496_;
goto v_reusejp_525_;
}
else
{
lean_object* v_reuseFailAlloc_527_; 
v_reuseFailAlloc_527_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_527_, 0, v_size_x27_515_);
lean_ctor_set(v_reuseFailAlloc_527_, 1, v_val_524_);
v___x_526_ = v_reuseFailAlloc_527_;
goto v_reusejp_525_;
}
v_reusejp_525_:
{
return v___x_526_;
}
}
else
{
lean_object* v___x_529_; 
if (v_isShared_497_ == 0)
{
lean_ctor_set(v___x_496_, 1, v_buckets_x27_517_);
lean_ctor_set(v___x_496_, 0, v_size_x27_515_);
v___x_529_ = v___x_496_;
goto v_reusejp_528_;
}
else
{
lean_object* v_reuseFailAlloc_530_; 
v_reuseFailAlloc_530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_530_, 0, v_size_x27_515_);
lean_ctor_set(v_reuseFailAlloc_530_, 1, v_buckets_x27_517_);
v___x_529_ = v_reuseFailAlloc_530_;
goto v_reusejp_528_;
}
v_reusejp_528_:
{
return v___x_529_;
}
}
}
else
{
lean_object* v___x_531_; lean_object* v_buckets_x27_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_536_; 
lean_inc(v_bkt_512_);
v___x_531_ = lean_box(0);
v_buckets_x27_532_ = lean_array_uset(v_buckets_494_, v___x_511_, v___x_531_);
v___x_533_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0_spec__2___redArg(v_a_491_, v_b_492_, v_bkt_512_);
v___x_534_ = lean_array_uset(v_buckets_x27_532_, v___x_511_, v___x_533_);
if (v_isShared_497_ == 0)
{
lean_ctor_set(v___x_496_, 1, v___x_534_);
v___x_536_ = v___x_496_;
goto v_reusejp_535_;
}
else
{
lean_object* v_reuseFailAlloc_537_; 
v_reuseFailAlloc_537_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_537_, 0, v_size_493_);
lean_ctor_set(v_reuseFailAlloc_537_, 1, v___x_534_);
v___x_536_ = v_reuseFailAlloc_537_;
goto v_reusejp_535_;
}
v_reusejp_535_:
{
return v___x_536_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__1(lean_object* v_as_541_, size_t v_i_542_, size_t v_stop_543_, lean_object* v_b_544_){
_start:
{
uint8_t v___x_545_; 
v___x_545_ = lean_usize_dec_eq(v_i_542_, v_stop_543_);
if (v___x_545_ == 0)
{
lean_object* v___x_546_; lean_object* v_head_547_; lean_object* v___x_548_; size_t v___x_549_; size_t v___x_550_; 
v___x_546_ = lean_array_uget_borrowed(v_as_541_, v_i_542_);
v_head_547_ = lean_ctor_get(v___x_546_, 0);
lean_inc(v___x_546_);
lean_inc(v_head_547_);
v___x_548_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0___redArg(v_b_544_, v_head_547_, v___x_546_);
v___x_549_ = ((size_t)1ULL);
v___x_550_ = lean_usize_add(v_i_542_, v___x_549_);
v_i_542_ = v___x_550_;
v_b_544_ = v___x_548_;
goto _start;
}
else
{
return v_b_544_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__1___boxed(lean_object* v_as_552_, lean_object* v_i_553_, lean_object* v_stop_554_, lean_object* v_b_555_){
_start:
{
size_t v_i_boxed_556_; size_t v_stop_boxed_557_; lean_object* v_res_558_; 
v_i_boxed_556_ = lean_unbox_usize(v_i_553_);
lean_dec(v_i_553_);
v_stop_boxed_557_ = lean_unbox_usize(v_stop_554_);
lean_dec(v_stop_554_);
v_res_558_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__1(v_as_552_, v_i_boxed_556_, v_stop_boxed_557_, v_b_555_);
lean_dec_ref(v_as_552_);
return v_res_558_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_latticeOps___closed__0(void){
_start:
{
lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; 
v___x_559_ = lean_box(0);
v___x_560_ = lean_unsigned_to_nat(16u);
v___x_561_ = lean_mk_array(v___x_560_, v___x_559_);
return v___x_561_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_latticeOps___closed__1(void){
_start:
{
lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; 
v___x_562_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_latticeOps___closed__0, &l_Lean_Elab_Tactic_VCGen_latticeOps___closed__0_once, _init_l_Lean_Elab_Tactic_VCGen_latticeOps___closed__0);
v___x_563_ = lean_unsigned_to_nat(0u);
v___x_564_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_564_, 0, v___x_563_);
lean_ctor_set(v___x_564_, 1, v___x_562_);
return v___x_564_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_latticeOps___closed__2(void){
_start:
{
lean_object* v___x_565_; lean_object* v___x_566_; 
v___x_565_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_builtinLatticeOps));
v___x_566_ = lean_array_get_size(v___x_565_);
return v___x_566_;
}
}
static uint8_t _init_l_Lean_Elab_Tactic_VCGen_latticeOps___closed__3(void){
_start:
{
lean_object* v___x_567_; lean_object* v___x_568_; uint8_t v___x_569_; 
v___x_567_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_latticeOps___closed__2, &l_Lean_Elab_Tactic_VCGen_latticeOps___closed__2_once, _init_l_Lean_Elab_Tactic_VCGen_latticeOps___closed__2);
v___x_568_ = lean_unsigned_to_nat(0u);
v___x_569_ = lean_nat_dec_lt(v___x_568_, v___x_567_);
return v___x_569_;
}
}
static uint8_t _init_l_Lean_Elab_Tactic_VCGen_latticeOps___closed__4(void){
_start:
{
lean_object* v___x_570_; uint8_t v___x_571_; 
v___x_570_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_latticeOps___closed__2, &l_Lean_Elab_Tactic_VCGen_latticeOps___closed__2_once, _init_l_Lean_Elab_Tactic_VCGen_latticeOps___closed__2);
v___x_571_ = lean_nat_dec_le(v___x_570_, v___x_570_);
return v___x_571_;
}
}
static size_t _init_l_Lean_Elab_Tactic_VCGen_latticeOps___closed__5(void){
_start:
{
lean_object* v___x_572_; size_t v___x_573_; 
v___x_572_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_latticeOps___closed__2, &l_Lean_Elab_Tactic_VCGen_latticeOps___closed__2_once, _init_l_Lean_Elab_Tactic_VCGen_latticeOps___closed__2);
v___x_573_ = lean_usize_of_nat(v___x_572_);
return v___x_573_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_latticeOps___closed__6(void){
_start:
{
lean_object* v___x_574_; size_t v___x_575_; size_t v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; 
v___x_574_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_latticeOps___closed__1, &l_Lean_Elab_Tactic_VCGen_latticeOps___closed__1_once, _init_l_Lean_Elab_Tactic_VCGen_latticeOps___closed__1);
v___x_575_ = lean_usize_once(&l_Lean_Elab_Tactic_VCGen_latticeOps___closed__5, &l_Lean_Elab_Tactic_VCGen_latticeOps___closed__5_once, _init_l_Lean_Elab_Tactic_VCGen_latticeOps___closed__5);
v___x_576_ = ((size_t)0ULL);
v___x_577_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_builtinLatticeOps));
v___x_578_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__1(v___x_577_, v___x_576_, v___x_575_, v___x_574_);
return v___x_578_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_latticeOps(void){
_start:
{
lean_object* v___x_579_; uint8_t v___x_580_; 
v___x_579_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_latticeOps___closed__1, &l_Lean_Elab_Tactic_VCGen_latticeOps___closed__1_once, _init_l_Lean_Elab_Tactic_VCGen_latticeOps___closed__1);
v___x_580_ = lean_uint8_once(&l_Lean_Elab_Tactic_VCGen_latticeOps___closed__3, &l_Lean_Elab_Tactic_VCGen_latticeOps___closed__3_once, _init_l_Lean_Elab_Tactic_VCGen_latticeOps___closed__3);
if (v___x_580_ == 0)
{
return v___x_579_;
}
else
{
uint8_t v___x_581_; 
v___x_581_ = lean_uint8_once(&l_Lean_Elab_Tactic_VCGen_latticeOps___closed__4, &l_Lean_Elab_Tactic_VCGen_latticeOps___closed__4_once, _init_l_Lean_Elab_Tactic_VCGen_latticeOps___closed__4);
if (v___x_581_ == 0)
{
if (v___x_580_ == 0)
{
return v___x_579_;
}
else
{
lean_object* v___x_582_; 
v___x_582_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_latticeOps___closed__6, &l_Lean_Elab_Tactic_VCGen_latticeOps___closed__6_once, _init_l_Lean_Elab_Tactic_VCGen_latticeOps___closed__6);
return v___x_582_;
}
}
else
{
lean_object* v___x_583_; 
v___x_583_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_latticeOps___closed__6, &l_Lean_Elab_Tactic_VCGen_latticeOps___closed__6_once, _init_l_Lean_Elab_Tactic_VCGen_latticeOps___closed__6);
return v___x_583_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0(lean_object* v_00_u03b2_584_, lean_object* v_m_585_, lean_object* v_a_586_, lean_object* v_b_587_){
_start:
{
lean_object* v___x_588_; 
v___x_588_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0___redArg(v_m_585_, v_a_586_, v_b_587_);
return v___x_588_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0_spec__0(lean_object* v_00_u03b2_589_, lean_object* v_a_590_, lean_object* v_x_591_){
_start:
{
uint8_t v___x_592_; 
v___x_592_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0_spec__0___redArg(v_a_590_, v_x_591_);
return v___x_592_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0_spec__0___boxed(lean_object* v_00_u03b2_593_, lean_object* v_a_594_, lean_object* v_x_595_){
_start:
{
uint8_t v_res_596_; lean_object* v_r_597_; 
v_res_596_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0_spec__0(v_00_u03b2_593_, v_a_594_, v_x_595_);
lean_dec(v_x_595_);
lean_dec(v_a_594_);
v_r_597_ = lean_box(v_res_596_);
return v_r_597_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0_spec__1(lean_object* v_00_u03b2_598_, lean_object* v_data_599_){
_start:
{
lean_object* v___x_600_; 
v___x_600_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0_spec__1___redArg(v_data_599_);
return v___x_600_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0_spec__2(lean_object* v_00_u03b2_601_, lean_object* v_a_602_, lean_object* v_b_603_, lean_object* v_x_604_){
_start:
{
lean_object* v___x_605_; 
v___x_605_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0_spec__2___redArg(v_a_602_, v_b_603_, v_x_604_);
return v___x_605_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_606_, lean_object* v_i_607_, lean_object* v_source_608_, lean_object* v_target_609_){
_start:
{
lean_object* v___x_610_; 
v___x_610_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0_spec__1_spec__2___redArg(v_i_607_, v_source_608_, v_target_609_);
return v___x_610_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_611_, lean_object* v_x_612_, lean_object* v_x_613_){
_start:
{
lean_object* v___x_614_; 
v___x_614_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0_spec__1_spec__2_spec__4___redArg(v_x_612_, v_x_613_);
return v___x_614_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__0___redArg(lean_object* v_e_615_, lean_object* v___y_616_){
_start:
{
uint8_t v___x_618_; 
v___x_618_ = l_Lean_Expr_hasMVar(v_e_615_);
if (v___x_618_ == 0)
{
lean_object* v___x_619_; 
v___x_619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_619_, 0, v_e_615_);
return v___x_619_;
}
else
{
lean_object* v___x_620_; lean_object* v_mctx_621_; lean_object* v___x_622_; lean_object* v_fst_623_; lean_object* v_snd_624_; lean_object* v___x_625_; lean_object* v_cache_626_; lean_object* v_zetaDeltaFVarIds_627_; lean_object* v_postponed_628_; lean_object* v_diag_629_; lean_object* v___x_631_; uint8_t v_isShared_632_; uint8_t v_isSharedCheck_638_; 
v___x_620_ = lean_st_ref_get(v___y_616_);
v_mctx_621_ = lean_ctor_get(v___x_620_, 0);
lean_inc_ref(v_mctx_621_);
lean_dec(v___x_620_);
v___x_622_ = l_Lean_instantiateMVarsCore(v_mctx_621_, v_e_615_);
v_fst_623_ = lean_ctor_get(v___x_622_, 0);
lean_inc(v_fst_623_);
v_snd_624_ = lean_ctor_get(v___x_622_, 1);
lean_inc(v_snd_624_);
lean_dec_ref(v___x_622_);
v___x_625_ = lean_st_ref_take(v___y_616_);
v_cache_626_ = lean_ctor_get(v___x_625_, 1);
v_zetaDeltaFVarIds_627_ = lean_ctor_get(v___x_625_, 2);
v_postponed_628_ = lean_ctor_get(v___x_625_, 3);
v_diag_629_ = lean_ctor_get(v___x_625_, 4);
v_isSharedCheck_638_ = !lean_is_exclusive(v___x_625_);
if (v_isSharedCheck_638_ == 0)
{
lean_object* v_unused_639_; 
v_unused_639_ = lean_ctor_get(v___x_625_, 0);
lean_dec(v_unused_639_);
v___x_631_ = v___x_625_;
v_isShared_632_ = v_isSharedCheck_638_;
goto v_resetjp_630_;
}
else
{
lean_inc(v_diag_629_);
lean_inc(v_postponed_628_);
lean_inc(v_zetaDeltaFVarIds_627_);
lean_inc(v_cache_626_);
lean_dec(v___x_625_);
v___x_631_ = lean_box(0);
v_isShared_632_ = v_isSharedCheck_638_;
goto v_resetjp_630_;
}
v_resetjp_630_:
{
lean_object* v___x_634_; 
if (v_isShared_632_ == 0)
{
lean_ctor_set(v___x_631_, 0, v_snd_624_);
v___x_634_ = v___x_631_;
goto v_reusejp_633_;
}
else
{
lean_object* v_reuseFailAlloc_637_; 
v_reuseFailAlloc_637_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_637_, 0, v_snd_624_);
lean_ctor_set(v_reuseFailAlloc_637_, 1, v_cache_626_);
lean_ctor_set(v_reuseFailAlloc_637_, 2, v_zetaDeltaFVarIds_627_);
lean_ctor_set(v_reuseFailAlloc_637_, 3, v_postponed_628_);
lean_ctor_set(v_reuseFailAlloc_637_, 4, v_diag_629_);
v___x_634_ = v_reuseFailAlloc_637_;
goto v_reusejp_633_;
}
v_reusejp_633_:
{
lean_object* v___x_635_; lean_object* v___x_636_; 
v___x_635_ = lean_st_ref_put(v___y_616_, v___x_634_);
v___x_636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_636_, 0, v_fst_623_);
return v___x_636_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__0___redArg___boxed(lean_object* v_e_640_, lean_object* v___y_641_, lean_object* v___y_642_){
_start:
{
lean_object* v_res_643_; 
v_res_643_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__0___redArg(v_e_640_, v___y_641_);
lean_dec(v___y_641_);
return v_res_643_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__0(lean_object* v_e_644_, lean_object* v___y_645_, lean_object* v___y_646_, lean_object* v___y_647_, lean_object* v___y_648_){
_start:
{
lean_object* v___x_650_; 
v___x_650_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__0___redArg(v_e_644_, v___y_646_);
return v___x_650_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__0___boxed(lean_object* v_e_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_){
_start:
{
lean_object* v_res_657_; 
v_res_657_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__0(v_e_651_, v___y_652_, v___y_653_, v___y_654_, v___y_655_);
lean_dec(v___y_655_);
lean_dec_ref(v___y_654_);
lean_dec(v___y_653_);
lean_dec_ref(v___y_652_);
return v_res_657_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__1_spec__1(lean_object* v_msgData_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_){
_start:
{
lean_object* v___x_664_; lean_object* v_env_665_; lean_object* v___x_666_; lean_object* v_toCold_667_; lean_object* v_mctx_668_; lean_object* v_lctx_669_; lean_object* v_options_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; 
v___x_664_ = lean_st_ref_get(v___y_662_);
v_env_665_ = lean_ctor_get(v___x_664_, 0);
lean_inc_ref(v_env_665_);
lean_dec(v___x_664_);
v___x_666_ = lean_st_ref_get(v___y_660_);
v_toCold_667_ = lean_ctor_get(v___y_661_, 0);
v_mctx_668_ = lean_ctor_get(v___x_666_, 0);
lean_inc_ref(v_mctx_668_);
lean_dec(v___x_666_);
v_lctx_669_ = lean_ctor_get(v___y_659_, 2);
v_options_670_ = lean_ctor_get(v_toCold_667_, 2);
lean_inc_ref(v_options_670_);
lean_inc_ref(v_lctx_669_);
v___x_671_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_671_, 0, v_env_665_);
lean_ctor_set(v___x_671_, 1, v_mctx_668_);
lean_ctor_set(v___x_671_, 2, v_lctx_669_);
lean_ctor_set(v___x_671_, 3, v_options_670_);
v___x_672_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_672_, 0, v___x_671_);
lean_ctor_set(v___x_672_, 1, v_msgData_658_);
v___x_673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_673_, 0, v___x_672_);
return v___x_673_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__1_spec__1___boxed(lean_object* v_msgData_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_){
_start:
{
lean_object* v_res_680_; 
v_res_680_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__1_spec__1(v_msgData_674_, v___y_675_, v___y_676_, v___y_677_, v___y_678_);
lean_dec(v___y_678_);
lean_dec_ref(v___y_677_);
lean_dec(v___y_676_);
lean_dec_ref(v___y_675_);
return v_res_680_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__1___redArg(lean_object* v_msg_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_){
_start:
{
lean_object* v_ref_687_; lean_object* v___x_688_; lean_object* v_a_689_; lean_object* v___x_691_; uint8_t v_isShared_692_; uint8_t v_isSharedCheck_697_; 
v_ref_687_ = lean_ctor_get(v___y_684_, 2);
v___x_688_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__1_spec__1(v_msg_681_, v___y_682_, v___y_683_, v___y_684_, v___y_685_);
v_a_689_ = lean_ctor_get(v___x_688_, 0);
v_isSharedCheck_697_ = !lean_is_exclusive(v___x_688_);
if (v_isSharedCheck_697_ == 0)
{
v___x_691_ = v___x_688_;
v_isShared_692_ = v_isSharedCheck_697_;
goto v_resetjp_690_;
}
else
{
lean_inc(v_a_689_);
lean_dec(v___x_688_);
v___x_691_ = lean_box(0);
v_isShared_692_ = v_isSharedCheck_697_;
goto v_resetjp_690_;
}
v_resetjp_690_:
{
lean_object* v___x_693_; lean_object* v___x_695_; 
lean_inc(v_ref_687_);
v___x_693_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_693_, 0, v_ref_687_);
lean_ctor_set(v___x_693_, 1, v_a_689_);
if (v_isShared_692_ == 0)
{
lean_ctor_set_tag(v___x_691_, 1);
lean_ctor_set(v___x_691_, 0, v___x_693_);
v___x_695_ = v___x_691_;
goto v_reusejp_694_;
}
else
{
lean_object* v_reuseFailAlloc_696_; 
v_reuseFailAlloc_696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_696_, 0, v___x_693_);
v___x_695_ = v_reuseFailAlloc_696_;
goto v_reusejp_694_;
}
v_reusejp_694_:
{
return v___x_695_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__1___redArg___boxed(lean_object* v_msg_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_){
_start:
{
lean_object* v_res_704_; 
v_res_704_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__1___redArg(v_msg_698_, v___y_699_, v___y_700_, v___y_701_, v___y_702_);
lean_dec(v___y_702_);
lean_dec_ref(v___y_701_);
lean_dec(v___y_700_);
lean_dec_ref(v___y_699_);
return v_res_704_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__4(void){
_start:
{
lean_object* v___x_713_; lean_object* v___x_714_; 
v___x_713_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__3));
v___x_714_ = l_Lean_stringToMessageData(v___x_713_);
return v___x_714_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__6(void){
_start:
{
lean_object* v___x_716_; lean_object* v___x_717_; 
v___x_716_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__5));
v___x_717_ = l_Lean_stringToMessageData(v___x_716_);
return v___x_717_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__8(void){
_start:
{
lean_object* v___x_719_; lean_object* v___x_720_; 
v___x_719_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__7));
v___x_720_ = l_Lean_stringToMessageData(v___x_719_);
return v___x_720_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2(lean_object* v_as_721_, size_t v_sz_722_, size_t v_i_723_, lean_object* v_b_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_){
_start:
{
lean_object* v_a_731_; uint8_t v___x_735_; 
v___x_735_ = lean_usize_dec_lt(v_i_723_, v_sz_722_);
if (v___x_735_ == 0)
{
lean_object* v___x_736_; 
v___x_736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_736_, 0, v_b_724_);
return v___x_736_;
}
else
{
lean_object* v_a_737_; lean_object* v___x_738_; 
v_a_737_ = lean_array_uget_borrowed(v_as_721_, v_i_723_);
lean_inc(v_a_737_);
v___x_738_ = l_Lean_Meta_mkConstWithFreshMVarLevels(v_a_737_, v___y_725_, v___y_726_, v___y_727_, v___y_728_);
if (lean_obj_tag(v___x_738_) == 0)
{
lean_object* v_a_739_; lean_object* v___x_740_; 
v_a_739_ = lean_ctor_get(v___x_738_, 0);
lean_inc(v_a_739_);
lean_dec_ref_known(v___x_738_, 1);
lean_inc(v___y_728_);
lean_inc_ref(v___y_727_);
lean_inc(v___y_726_);
lean_inc_ref(v___y_725_);
v___x_740_ = lean_infer_type(v_a_739_, v___y_725_, v___y_726_, v___y_727_, v___y_728_);
if (lean_obj_tag(v___x_740_) == 0)
{
lean_object* v_a_741_; lean_object* v___x_742_; uint8_t v___x_743_; lean_object* v___x_744_; 
v_a_741_ = lean_ctor_get(v___x_740_, 0);
lean_inc(v_a_741_);
lean_dec_ref_known(v___x_740_, 1);
v___x_742_ = lean_box(0);
v___x_743_ = 0;
v___x_744_ = l_Lean_Meta_forallMetaTelescopeReducing(v_a_741_, v___x_742_, v___x_743_, v___y_725_, v___y_726_, v___y_727_, v___y_728_);
if (lean_obj_tag(v___x_744_) == 0)
{
lean_object* v_a_745_; lean_object* v_snd_746_; lean_object* v___x_748_; uint8_t v_isShared_749_; uint8_t v_isSharedCheck_810_; 
v_a_745_ = lean_ctor_get(v___x_744_, 0);
lean_inc(v_a_745_);
lean_dec_ref_known(v___x_744_, 1);
v_snd_746_ = lean_ctor_get(v_a_745_, 1);
v_isSharedCheck_810_ = !lean_is_exclusive(v_a_745_);
if (v_isSharedCheck_810_ == 0)
{
lean_object* v_unused_811_; 
v_unused_811_ = lean_ctor_get(v_a_745_, 0);
lean_dec(v_unused_811_);
v___x_748_ = v_a_745_;
v_isShared_749_ = v_isSharedCheck_810_;
goto v_resetjp_747_;
}
else
{
lean_inc(v_snd_746_);
lean_dec(v_a_745_);
v___x_748_ = lean_box(0);
v_isShared_749_ = v_isSharedCheck_810_;
goto v_resetjp_747_;
}
v_resetjp_747_:
{
lean_object* v_snd_750_; lean_object* v___x_752_; uint8_t v_isShared_753_; uint8_t v_isSharedCheck_808_; 
v_snd_750_ = lean_ctor_get(v_snd_746_, 1);
v_isSharedCheck_808_ = !lean_is_exclusive(v_snd_746_);
if (v_isSharedCheck_808_ == 0)
{
lean_object* v_unused_809_; 
v_unused_809_ = lean_ctor_get(v_snd_746_, 0);
lean_dec(v_unused_809_);
v___x_752_ = v_snd_746_;
v_isShared_753_ = v_isSharedCheck_808_;
goto v_resetjp_751_;
}
else
{
lean_inc(v_snd_750_);
lean_dec(v_snd_746_);
v___x_752_ = lean_box(0);
v_isShared_753_ = v_isSharedCheck_808_;
goto v_resetjp_751_;
}
v_resetjp_751_:
{
lean_object* v___x_754_; 
v___x_754_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__0___redArg(v_snd_750_, v___y_726_);
if (lean_obj_tag(v___x_754_) == 0)
{
lean_object* v_a_755_; lean_object* v___x_756_; lean_object* v___x_757_; uint8_t v___x_758_; 
v_a_755_ = lean_ctor_get(v___x_754_, 0);
lean_inc(v_a_755_);
lean_dec_ref_known(v___x_754_, 1);
v___x_756_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__2));
v___x_757_ = lean_unsigned_to_nat(4u);
v___x_758_ = l_Lean_Expr_isAppOfArity(v_a_755_, v___x_756_, v___x_757_);
if (v___x_758_ == 0)
{
lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_762_; 
lean_dec(v_a_755_);
lean_del_object(v___x_752_);
v___x_759_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__4);
lean_inc(v_a_737_);
v___x_760_ = l_Lean_MessageData_ofName(v_a_737_);
if (v_isShared_749_ == 0)
{
lean_ctor_set_tag(v___x_748_, 7);
lean_ctor_set(v___x_748_, 1, v___x_760_);
lean_ctor_set(v___x_748_, 0, v___x_759_);
v___x_762_ = v___x_748_;
goto v_reusejp_761_;
}
else
{
lean_object* v_reuseFailAlloc_774_; 
v_reuseFailAlloc_774_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_774_, 0, v___x_759_);
lean_ctor_set(v_reuseFailAlloc_774_, 1, v___x_760_);
v___x_762_ = v_reuseFailAlloc_774_;
goto v_reusejp_761_;
}
v_reusejp_761_:
{
lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; 
v___x_763_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__6);
v___x_764_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_764_, 0, v___x_762_);
lean_ctor_set(v___x_764_, 1, v___x_763_);
v___x_765_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__1___redArg(v___x_764_, v___y_725_, v___y_726_, v___y_727_, v___y_728_);
if (lean_obj_tag(v___x_765_) == 0)
{
lean_dec_ref_known(v___x_765_, 1);
v_a_731_ = v_b_724_;
goto v___jp_730_;
}
else
{
lean_object* v_a_766_; lean_object* v___x_768_; uint8_t v_isShared_769_; uint8_t v_isSharedCheck_773_; 
lean_dec_ref(v_b_724_);
v_a_766_ = lean_ctor_get(v___x_765_, 0);
v_isSharedCheck_773_ = !lean_is_exclusive(v___x_765_);
if (v_isSharedCheck_773_ == 0)
{
v___x_768_ = v___x_765_;
v_isShared_769_ = v_isSharedCheck_773_;
goto v_resetjp_767_;
}
else
{
lean_inc(v_a_766_);
lean_dec(v___x_765_);
v___x_768_ = lean_box(0);
v_isShared_769_ = v_isSharedCheck_773_;
goto v_resetjp_767_;
}
v_resetjp_767_:
{
lean_object* v___x_771_; 
if (v_isShared_769_ == 0)
{
v___x_771_ = v___x_768_;
goto v_reusejp_770_;
}
else
{
lean_object* v_reuseFailAlloc_772_; 
v_reuseFailAlloc_772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_772_, 0, v_a_766_);
v___x_771_ = v_reuseFailAlloc_772_;
goto v_reusejp_770_;
}
v_reusejp_770_:
{
return v___x_771_;
}
}
}
}
}
else
{
lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; 
v___x_775_ = l_Lean_Expr_appArg_x21(v_a_755_);
lean_dec(v_a_755_);
v___x_776_ = l_Lean_Expr_getAppFn(v___x_775_);
v___x_777_ = l_Lean_Expr_constName_x3f(v___x_776_);
lean_dec_ref(v___x_776_);
if (lean_obj_tag(v___x_777_) == 1)
{
lean_object* v_val_778_; lean_object* v___x_779_; lean_object* v___x_781_; 
lean_del_object(v___x_748_);
v_val_778_ = lean_ctor_get(v___x_777_, 0);
lean_inc(v_val_778_);
lean_dec_ref_known(v___x_777_, 1);
v___x_779_ = l_Lean_Expr_getAppNumArgs(v___x_775_);
lean_dec_ref(v___x_775_);
lean_inc(v_a_737_);
if (v_isShared_753_ == 0)
{
lean_ctor_set(v___x_752_, 1, v___x_779_);
lean_ctor_set(v___x_752_, 0, v_a_737_);
v___x_781_ = v___x_752_;
goto v_reusejp_780_;
}
else
{
lean_object* v_reuseFailAlloc_783_; 
v_reuseFailAlloc_783_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_783_, 0, v_a_737_);
lean_ctor_set(v_reuseFailAlloc_783_, 1, v___x_779_);
v___x_781_ = v_reuseFailAlloc_783_;
goto v_reusejp_780_;
}
v_reusejp_780_:
{
lean_object* v___x_782_; 
v___x_782_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0___redArg(v_b_724_, v_val_778_, v___x_781_);
v_a_731_ = v___x_782_;
goto v___jp_730_;
}
}
else
{
lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_787_; 
lean_dec(v___x_777_);
lean_dec_ref(v___x_775_);
lean_del_object(v___x_752_);
v___x_784_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__4);
lean_inc(v_a_737_);
v___x_785_ = l_Lean_MessageData_ofName(v_a_737_);
if (v_isShared_749_ == 0)
{
lean_ctor_set_tag(v___x_748_, 7);
lean_ctor_set(v___x_748_, 1, v___x_785_);
lean_ctor_set(v___x_748_, 0, v___x_784_);
v___x_787_ = v___x_748_;
goto v_reusejp_786_;
}
else
{
lean_object* v_reuseFailAlloc_799_; 
v_reuseFailAlloc_799_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_799_, 0, v___x_784_);
lean_ctor_set(v_reuseFailAlloc_799_, 1, v___x_785_);
v___x_787_ = v_reuseFailAlloc_799_;
goto v_reusejp_786_;
}
v_reusejp_786_:
{
lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; 
v___x_788_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__8);
v___x_789_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_789_, 0, v___x_787_);
lean_ctor_set(v___x_789_, 1, v___x_788_);
v___x_790_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__1___redArg(v___x_789_, v___y_725_, v___y_726_, v___y_727_, v___y_728_);
if (lean_obj_tag(v___x_790_) == 0)
{
lean_dec_ref_known(v___x_790_, 1);
v_a_731_ = v_b_724_;
goto v___jp_730_;
}
else
{
lean_object* v_a_791_; lean_object* v___x_793_; uint8_t v_isShared_794_; uint8_t v_isSharedCheck_798_; 
lean_dec_ref(v_b_724_);
v_a_791_ = lean_ctor_get(v___x_790_, 0);
v_isSharedCheck_798_ = !lean_is_exclusive(v___x_790_);
if (v_isSharedCheck_798_ == 0)
{
v___x_793_ = v___x_790_;
v_isShared_794_ = v_isSharedCheck_798_;
goto v_resetjp_792_;
}
else
{
lean_inc(v_a_791_);
lean_dec(v___x_790_);
v___x_793_ = lean_box(0);
v_isShared_794_ = v_isSharedCheck_798_;
goto v_resetjp_792_;
}
v_resetjp_792_:
{
lean_object* v___x_796_; 
if (v_isShared_794_ == 0)
{
v___x_796_ = v___x_793_;
goto v_reusejp_795_;
}
else
{
lean_object* v_reuseFailAlloc_797_; 
v_reuseFailAlloc_797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_797_, 0, v_a_791_);
v___x_796_ = v_reuseFailAlloc_797_;
goto v_reusejp_795_;
}
v_reusejp_795_:
{
return v___x_796_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_800_; lean_object* v___x_802_; uint8_t v_isShared_803_; uint8_t v_isSharedCheck_807_; 
lean_del_object(v___x_752_);
lean_del_object(v___x_748_);
lean_dec_ref(v_b_724_);
v_a_800_ = lean_ctor_get(v___x_754_, 0);
v_isSharedCheck_807_ = !lean_is_exclusive(v___x_754_);
if (v_isSharedCheck_807_ == 0)
{
v___x_802_ = v___x_754_;
v_isShared_803_ = v_isSharedCheck_807_;
goto v_resetjp_801_;
}
else
{
lean_inc(v_a_800_);
lean_dec(v___x_754_);
v___x_802_ = lean_box(0);
v_isShared_803_ = v_isSharedCheck_807_;
goto v_resetjp_801_;
}
v_resetjp_801_:
{
lean_object* v___x_805_; 
if (v_isShared_803_ == 0)
{
v___x_805_ = v___x_802_;
goto v_reusejp_804_;
}
else
{
lean_object* v_reuseFailAlloc_806_; 
v_reuseFailAlloc_806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_806_, 0, v_a_800_);
v___x_805_ = v_reuseFailAlloc_806_;
goto v_reusejp_804_;
}
v_reusejp_804_:
{
return v___x_805_;
}
}
}
}
}
}
else
{
lean_object* v_a_812_; lean_object* v___x_814_; uint8_t v_isShared_815_; uint8_t v_isSharedCheck_819_; 
lean_dec_ref(v_b_724_);
v_a_812_ = lean_ctor_get(v___x_744_, 0);
v_isSharedCheck_819_ = !lean_is_exclusive(v___x_744_);
if (v_isSharedCheck_819_ == 0)
{
v___x_814_ = v___x_744_;
v_isShared_815_ = v_isSharedCheck_819_;
goto v_resetjp_813_;
}
else
{
lean_inc(v_a_812_);
lean_dec(v___x_744_);
v___x_814_ = lean_box(0);
v_isShared_815_ = v_isSharedCheck_819_;
goto v_resetjp_813_;
}
v_resetjp_813_:
{
lean_object* v___x_817_; 
if (v_isShared_815_ == 0)
{
v___x_817_ = v___x_814_;
goto v_reusejp_816_;
}
else
{
lean_object* v_reuseFailAlloc_818_; 
v_reuseFailAlloc_818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_818_, 0, v_a_812_);
v___x_817_ = v_reuseFailAlloc_818_;
goto v_reusejp_816_;
}
v_reusejp_816_:
{
return v___x_817_;
}
}
}
}
else
{
lean_object* v_a_820_; lean_object* v___x_822_; uint8_t v_isShared_823_; uint8_t v_isSharedCheck_827_; 
lean_dec_ref(v_b_724_);
v_a_820_ = lean_ctor_get(v___x_740_, 0);
v_isSharedCheck_827_ = !lean_is_exclusive(v___x_740_);
if (v_isSharedCheck_827_ == 0)
{
v___x_822_ = v___x_740_;
v_isShared_823_ = v_isSharedCheck_827_;
goto v_resetjp_821_;
}
else
{
lean_inc(v_a_820_);
lean_dec(v___x_740_);
v___x_822_ = lean_box(0);
v_isShared_823_ = v_isSharedCheck_827_;
goto v_resetjp_821_;
}
v_resetjp_821_:
{
lean_object* v___x_825_; 
if (v_isShared_823_ == 0)
{
v___x_825_ = v___x_822_;
goto v_reusejp_824_;
}
else
{
lean_object* v_reuseFailAlloc_826_; 
v_reuseFailAlloc_826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_826_, 0, v_a_820_);
v___x_825_ = v_reuseFailAlloc_826_;
goto v_reusejp_824_;
}
v_reusejp_824_:
{
return v___x_825_;
}
}
}
}
else
{
lean_object* v_a_828_; lean_object* v___x_830_; uint8_t v_isShared_831_; uint8_t v_isSharedCheck_835_; 
lean_dec_ref(v_b_724_);
v_a_828_ = lean_ctor_get(v___x_738_, 0);
v_isSharedCheck_835_ = !lean_is_exclusive(v___x_738_);
if (v_isSharedCheck_835_ == 0)
{
v___x_830_ = v___x_738_;
v_isShared_831_ = v_isSharedCheck_835_;
goto v_resetjp_829_;
}
else
{
lean_inc(v_a_828_);
lean_dec(v___x_738_);
v___x_830_ = lean_box(0);
v_isShared_831_ = v_isSharedCheck_835_;
goto v_resetjp_829_;
}
v_resetjp_829_:
{
lean_object* v___x_833_; 
if (v_isShared_831_ == 0)
{
v___x_833_ = v___x_830_;
goto v_reusejp_832_;
}
else
{
lean_object* v_reuseFailAlloc_834_; 
v_reuseFailAlloc_834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_834_, 0, v_a_828_);
v___x_833_ = v_reuseFailAlloc_834_;
goto v_reusejp_832_;
}
v_reusejp_832_:
{
return v___x_833_;
}
}
}
}
v___jp_730_:
{
size_t v___x_732_; size_t v___x_733_; 
v___x_732_ = ((size_t)1ULL);
v___x_733_ = lean_usize_add(v_i_723_, v___x_732_);
v_i_723_ = v___x_733_;
v_b_724_ = v_a_731_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___boxed(lean_object* v_as_836_, lean_object* v_sz_837_, lean_object* v_i_838_, lean_object* v_b_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_){
_start:
{
size_t v_sz_boxed_845_; size_t v_i_boxed_846_; lean_object* v_res_847_; 
v_sz_boxed_845_ = lean_unbox_usize(v_sz_837_);
lean_dec(v_sz_837_);
v_i_boxed_846_ = lean_unbox_usize(v_i_838_);
lean_dec(v_i_838_);
v_res_847_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2(v_as_836_, v_sz_boxed_845_, v_i_boxed_846_, v_b_839_, v___y_840_, v___y_841_, v___y_842_, v___y_843_);
lean_dec(v___y_843_);
lean_dec_ref(v___y_842_);
lean_dec(v___y_841_);
lean_dec_ref(v___y_840_);
lean_dec_ref(v_as_836_);
return v_res_847_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals(lean_object* v_names_848_, lean_object* v_a_849_, lean_object* v_a_850_, lean_object* v_a_851_, lean_object* v_a_852_){
_start:
{
lean_object* v_m_854_; size_t v_sz_855_; size_t v___x_856_; lean_object* v___x_857_; 
v_m_854_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_latticeOps___closed__1, &l_Lean_Elab_Tactic_VCGen_latticeOps___closed__1_once, _init_l_Lean_Elab_Tactic_VCGen_latticeOps___closed__1);
v_sz_855_ = lean_array_size(v_names_848_);
v___x_856_ = ((size_t)0ULL);
v___x_857_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2(v_names_848_, v_sz_855_, v___x_856_, v_m_854_, v_a_849_, v_a_850_, v_a_851_, v_a_852_);
return v___x_857_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals___boxed(lean_object* v_names_858_, lean_object* v_a_859_, lean_object* v_a_860_, lean_object* v_a_861_, lean_object* v_a_862_, lean_object* v_a_863_){
_start:
{
lean_object* v_res_864_; 
v_res_864_ = l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals(v_names_858_, v_a_859_, v_a_860_, v_a_861_, v_a_862_);
lean_dec(v_a_862_);
lean_dec_ref(v_a_861_);
lean_dec(v_a_860_);
lean_dec_ref(v_a_859_);
lean_dec_ref(v_names_858_);
return v_res_864_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__1(lean_object* v_00_u03b1_865_, lean_object* v_msg_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_){
_start:
{
lean_object* v___x_872_; 
v___x_872_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__1___redArg(v_msg_866_, v___y_867_, v___y_868_, v___y_869_, v___y_870_);
return v___x_872_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__1___boxed(lean_object* v_00_u03b1_873_, lean_object* v_msg_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_){
_start:
{
lean_object* v_res_880_; 
v_res_880_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__1(v_00_u03b1_873_, v_msg_874_, v___y_875_, v___y_876_, v___y_877_, v___y_878_);
lean_dec(v___y_878_);
lean_dec_ref(v___y_877_);
lean_dec(v___y_876_);
lean_dec_ref(v___y_875_);
return v_res_880_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_go___lam__0(uint8_t v_isZero_881_, lean_object* v_x_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_){
_start:
{
lean_object* v___x_893_; lean_object* v___x_894_; 
v___x_893_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_893_, 0, v_isZero_881_);
lean_ctor_set_uint8(v___x_893_, 1, v_isZero_881_);
v___x_894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_894_, 0, v___x_893_);
return v___x_894_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_go___lam__0___boxed(lean_object* v_isZero_895_, lean_object* v_x_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_){
_start:
{
uint8_t v_isZero_boxed_907_; lean_object* v_res_908_; 
v_isZero_boxed_907_ = lean_unbox(v_isZero_895_);
v_res_908_ = l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_go___lam__0(v_isZero_boxed_907_, v_x_896_, v___y_897_, v___y_898_, v___y_899_, v___y_900_, v___y_901_, v___y_902_, v___y_903_, v___y_904_, v___y_905_);
lean_dec(v___y_905_);
lean_dec_ref(v___y_904_);
lean_dec(v___y_903_);
lean_dec_ref(v___y_902_);
lean_dec(v___y_901_);
lean_dec_ref(v___y_900_);
lean_dec(v___y_899_);
lean_dec_ref(v___y_898_);
lean_dec(v___y_897_);
lean_dec_ref(v_x_896_);
return v_res_908_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_go_spec__0___redArg(lean_object* v_msg_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_){
_start:
{
lean_object* v_ref_915_; lean_object* v___x_916_; lean_object* v_a_917_; lean_object* v___x_919_; uint8_t v_isShared_920_; uint8_t v_isSharedCheck_925_; 
v_ref_915_ = lean_ctor_get(v___y_912_, 2);
v___x_916_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__1_spec__1(v_msg_909_, v___y_910_, v___y_911_, v___y_912_, v___y_913_);
v_a_917_ = lean_ctor_get(v___x_916_, 0);
v_isSharedCheck_925_ = !lean_is_exclusive(v___x_916_);
if (v_isSharedCheck_925_ == 0)
{
v___x_919_ = v___x_916_;
v_isShared_920_ = v_isSharedCheck_925_;
goto v_resetjp_918_;
}
else
{
lean_inc(v_a_917_);
lean_dec(v___x_916_);
v___x_919_ = lean_box(0);
v_isShared_920_ = v_isSharedCheck_925_;
goto v_resetjp_918_;
}
v_resetjp_918_:
{
lean_object* v___x_921_; lean_object* v___x_923_; 
lean_inc(v_ref_915_);
v___x_921_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_921_, 0, v_ref_915_);
lean_ctor_set(v___x_921_, 1, v_a_917_);
if (v_isShared_920_ == 0)
{
lean_ctor_set_tag(v___x_919_, 1);
lean_ctor_set(v___x_919_, 0, v___x_921_);
v___x_923_ = v___x_919_;
goto v_reusejp_922_;
}
else
{
lean_object* v_reuseFailAlloc_924_; 
v_reuseFailAlloc_924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_924_, 0, v___x_921_);
v___x_923_ = v_reuseFailAlloc_924_;
goto v_reusejp_922_;
}
v_reusejp_922_:
{
return v___x_923_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_go_spec__0___redArg___boxed(lean_object* v_msg_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_){
_start:
{
lean_object* v_res_932_; 
v_res_932_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_go_spec__0___redArg(v_msg_926_, v___y_927_, v___y_928_, v___y_929_, v___y_930_);
lean_dec(v___y_930_);
lean_dec_ref(v___y_929_);
lean_dec(v___y_928_);
lean_dec_ref(v___y_927_);
return v_res_932_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_go___closed__1(void){
_start:
{
lean_object* v___x_934_; lean_object* v___x_935_; 
v___x_934_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_go___closed__0));
v___x_935_ = l_Lean_stringToMessageData(v___x_934_);
return v___x_935_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_go(lean_object* v_step_939_, lean_object* v_e_u2080_940_, lean_object* v_cur_941_, lean_object* v_proof_x3f_942_, lean_object* v_a_943_, lean_object* v_a_944_, lean_object* v_a_945_, lean_object* v_a_946_, lean_object* v_a_947_, lean_object* v_a_948_, lean_object* v_a_949_){
_start:
{
lean_object* v_zero_951_; uint8_t v_isZero_952_; 
v_zero_951_ = lean_unsigned_to_nat(0u);
v_isZero_952_ = lean_nat_dec_eq(v_a_943_, v_zero_951_);
if (v_isZero_952_ == 1)
{
lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; 
lean_dec(v_a_943_);
lean_dec(v_proof_x3f_942_);
lean_dec_ref(v_e_u2080_940_);
lean_dec_ref(v_step_939_);
v___x_953_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_go___closed__1, &l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_go___closed__1_once, _init_l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_go___closed__1);
v___x_954_ = l_Lean_indentExpr(v_cur_941_);
v___x_955_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_955_, 0, v___x_953_);
lean_ctor_set(v___x_955_, 1, v___x_954_);
v___x_956_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_go_spec__0___redArg(v___x_955_, v_a_946_, v_a_947_, v_a_948_, v_a_949_);
return v___x_956_;
}
else
{
lean_object* v___x_957_; lean_object* v___f_958_; lean_object* v_one_959_; lean_object* v_n_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; 
v___x_957_ = lean_box(v_isZero_952_);
v___f_958_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_go___lam__0___boxed), 12, 1);
lean_closure_set(v___f_958_, 0, v___x_957_);
v_one_959_ = lean_unsigned_to_nat(1u);
v_n_960_ = lean_nat_sub(v_a_943_, v_one_959_);
lean_dec(v_a_943_);
lean_inc_ref(v_step_939_);
lean_inc_ref(v_cur_941_);
v___x_961_ = lean_apply_1(v_step_939_, v_cur_941_);
lean_inc_ref(v___f_958_);
v___x_962_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_962_, 0, v___f_958_);
lean_ctor_set(v___x_962_, 1, v___f_958_);
v___x_963_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_go___closed__2));
v___x_964_ = l_Lean_Meta_Sym_Simp_SimpM_run_x27___redArg(v___x_961_, v___x_962_, v___x_963_, v_a_944_, v_a_945_, v_a_946_, v_a_947_, v_a_948_, v_a_949_);
if (lean_obj_tag(v___x_964_) == 0)
{
lean_object* v_a_965_; lean_object* v___x_967_; uint8_t v_isShared_968_; uint8_t v_isSharedCheck_996_; 
v_a_965_ = lean_ctor_get(v___x_964_, 0);
v_isSharedCheck_996_ = !lean_is_exclusive(v___x_964_);
if (v_isSharedCheck_996_ == 0)
{
v___x_967_ = v___x_964_;
v_isShared_968_ = v_isSharedCheck_996_;
goto v_resetjp_966_;
}
else
{
lean_inc(v_a_965_);
lean_dec(v___x_964_);
v___x_967_ = lean_box(0);
v_isShared_968_ = v_isSharedCheck_996_;
goto v_resetjp_966_;
}
v_resetjp_966_:
{
if (lean_obj_tag(v_a_965_) == 0)
{
lean_object* v___x_969_; lean_object* v___x_971_; 
lean_dec_ref_known(v_a_965_, 0);
lean_dec(v_n_960_);
lean_dec_ref(v_e_u2080_940_);
lean_dec_ref(v_step_939_);
v___x_969_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_969_, 0, v_cur_941_);
lean_ctor_set(v___x_969_, 1, v_proof_x3f_942_);
if (v_isShared_968_ == 0)
{
lean_ctor_set(v___x_967_, 0, v___x_969_);
v___x_971_ = v___x_967_;
goto v_reusejp_970_;
}
else
{
lean_object* v_reuseFailAlloc_972_; 
v_reuseFailAlloc_972_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_972_, 0, v___x_969_);
v___x_971_ = v_reuseFailAlloc_972_;
goto v_reusejp_970_;
}
v_reusejp_970_:
{
return v___x_971_;
}
}
else
{
lean_object* v_e_x27_973_; lean_object* v_proof_974_; lean_object* v_proof_976_; lean_object* v___y_977_; lean_object* v___y_978_; lean_object* v___y_979_; lean_object* v___y_980_; lean_object* v___y_981_; lean_object* v___y_982_; 
lean_del_object(v___x_967_);
v_e_x27_973_ = lean_ctor_get(v_a_965_, 0);
lean_inc_ref(v_e_x27_973_);
v_proof_974_ = lean_ctor_get(v_a_965_, 1);
lean_inc_ref(v_proof_974_);
lean_dec_ref_known(v_a_965_, 2);
if (lean_obj_tag(v_proof_x3f_942_) == 0)
{
lean_dec_ref(v_cur_941_);
v_proof_976_ = v_proof_974_;
v___y_977_ = v_a_944_;
v___y_978_ = v_a_945_;
v___y_979_ = v_a_946_;
v___y_980_ = v_a_947_;
v___y_981_ = v_a_948_;
v___y_982_ = v_a_949_;
goto v___jp_975_;
}
else
{
lean_object* v_val_985_; lean_object* v___x_986_; 
v_val_985_ = lean_ctor_get(v_proof_x3f_942_, 0);
lean_inc(v_val_985_);
lean_dec_ref_known(v_proof_x3f_942_, 1);
lean_inc_ref(v_e_x27_973_);
lean_inc_ref(v_e_u2080_940_);
v___x_986_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v_e_u2080_940_, v_cur_941_, v_val_985_, v_e_x27_973_, v_proof_974_, v_a_944_, v_a_945_, v_a_946_, v_a_947_, v_a_948_, v_a_949_);
if (lean_obj_tag(v___x_986_) == 0)
{
lean_object* v_a_987_; 
v_a_987_ = lean_ctor_get(v___x_986_, 0);
lean_inc(v_a_987_);
lean_dec_ref_known(v___x_986_, 1);
v_proof_976_ = v_a_987_;
v___y_977_ = v_a_944_;
v___y_978_ = v_a_945_;
v___y_979_ = v_a_946_;
v___y_980_ = v_a_947_;
v___y_981_ = v_a_948_;
v___y_982_ = v_a_949_;
goto v___jp_975_;
}
else
{
lean_object* v_a_988_; lean_object* v___x_990_; uint8_t v_isShared_991_; uint8_t v_isSharedCheck_995_; 
lean_dec_ref(v_e_x27_973_);
lean_dec(v_n_960_);
lean_dec_ref(v_e_u2080_940_);
lean_dec_ref(v_step_939_);
v_a_988_ = lean_ctor_get(v___x_986_, 0);
v_isSharedCheck_995_ = !lean_is_exclusive(v___x_986_);
if (v_isSharedCheck_995_ == 0)
{
v___x_990_ = v___x_986_;
v_isShared_991_ = v_isSharedCheck_995_;
goto v_resetjp_989_;
}
else
{
lean_inc(v_a_988_);
lean_dec(v___x_986_);
v___x_990_ = lean_box(0);
v_isShared_991_ = v_isSharedCheck_995_;
goto v_resetjp_989_;
}
v_resetjp_989_:
{
lean_object* v___x_993_; 
if (v_isShared_991_ == 0)
{
v___x_993_ = v___x_990_;
goto v_reusejp_992_;
}
else
{
lean_object* v_reuseFailAlloc_994_; 
v_reuseFailAlloc_994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_994_, 0, v_a_988_);
v___x_993_ = v_reuseFailAlloc_994_;
goto v_reusejp_992_;
}
v_reusejp_992_:
{
return v___x_993_;
}
}
}
}
v___jp_975_:
{
lean_object* v___x_983_; 
v___x_983_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_983_, 0, v_proof_976_);
v_cur_941_ = v_e_x27_973_;
v_proof_x3f_942_ = v___x_983_;
v_a_943_ = v_n_960_;
v_a_944_ = v___y_977_;
v_a_945_ = v___y_978_;
v_a_946_ = v___y_979_;
v_a_947_ = v___y_980_;
v_a_948_ = v___y_981_;
v_a_949_ = v___y_982_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_997_; lean_object* v___x_999_; uint8_t v_isShared_1000_; uint8_t v_isSharedCheck_1004_; 
lean_dec(v_n_960_);
lean_dec(v_proof_x3f_942_);
lean_dec_ref(v_cur_941_);
lean_dec_ref(v_e_u2080_940_);
lean_dec_ref(v_step_939_);
v_a_997_ = lean_ctor_get(v___x_964_, 0);
v_isSharedCheck_1004_ = !lean_is_exclusive(v___x_964_);
if (v_isSharedCheck_1004_ == 0)
{
v___x_999_ = v___x_964_;
v_isShared_1000_ = v_isSharedCheck_1004_;
goto v_resetjp_998_;
}
else
{
lean_inc(v_a_997_);
lean_dec(v___x_964_);
v___x_999_ = lean_box(0);
v_isShared_1000_ = v_isSharedCheck_1004_;
goto v_resetjp_998_;
}
v_resetjp_998_:
{
lean_object* v___x_1002_; 
if (v_isShared_1000_ == 0)
{
v___x_1002_ = v___x_999_;
goto v_reusejp_1001_;
}
else
{
lean_object* v_reuseFailAlloc_1003_; 
v_reuseFailAlloc_1003_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1003_, 0, v_a_997_);
v___x_1002_ = v_reuseFailAlloc_1003_;
goto v_reusejp_1001_;
}
v_reusejp_1001_:
{
return v___x_1002_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_go___boxed(lean_object* v_step_1005_, lean_object* v_e_u2080_1006_, lean_object* v_cur_1007_, lean_object* v_proof_x3f_1008_, lean_object* v_a_1009_, lean_object* v_a_1010_, lean_object* v_a_1011_, lean_object* v_a_1012_, lean_object* v_a_1013_, lean_object* v_a_1014_, lean_object* v_a_1015_, lean_object* v_a_1016_){
_start:
{
lean_object* v_res_1017_; 
v_res_1017_ = l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_go(v_step_1005_, v_e_u2080_1006_, v_cur_1007_, v_proof_x3f_1008_, v_a_1009_, v_a_1010_, v_a_1011_, v_a_1012_, v_a_1013_, v_a_1014_, v_a_1015_);
lean_dec(v_a_1015_);
lean_dec_ref(v_a_1014_);
lean_dec(v_a_1013_);
lean_dec_ref(v_a_1012_);
lean_dec(v_a_1011_);
lean_dec_ref(v_a_1010_);
return v_res_1017_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_go_spec__0(lean_object* v_00_u03b1_1018_, lean_object* v_msg_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_){
_start:
{
lean_object* v___x_1027_; 
v___x_1027_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_go_spec__0___redArg(v_msg_1019_, v___y_1022_, v___y_1023_, v___y_1024_, v___y_1025_);
return v___x_1027_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_go_spec__0___boxed(lean_object* v_00_u03b1_1028_, lean_object* v_msg_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_){
_start:
{
lean_object* v_res_1037_; 
v_res_1037_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_go_spec__0(v_00_u03b1_1028_, v_msg_1029_, v___y_1030_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_, v___y_1035_);
lean_dec(v___y_1035_);
lean_dec_ref(v___y_1034_);
lean_dec(v___y_1033_);
lean_dec_ref(v___y_1032_);
lean_dec(v___y_1031_);
lean_dec_ref(v___y_1030_);
return v_res_1037_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_spec__0___redArg(lean_object* v_as_1038_, size_t v_i_1039_, size_t v_stop_1040_, lean_object* v_b_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_){
_start:
{
uint8_t v___x_1047_; 
v___x_1047_ = lean_usize_dec_eq(v_i_1039_, v_stop_1040_);
if (v___x_1047_ == 0)
{
lean_object* v___x_1048_; lean_object* v___x_1049_; 
v___x_1048_ = lean_array_uget_borrowed(v_as_1038_, v_i_1039_);
lean_inc(v___x_1048_);
v___x_1049_ = l_Lean_Meta_Sym_Simp_mkTheoremFromDecl(v___x_1048_, v___y_1042_, v___y_1043_, v___y_1044_, v___y_1045_);
if (lean_obj_tag(v___x_1049_) == 0)
{
lean_object* v_a_1050_; lean_object* v___x_1051_; size_t v___x_1052_; size_t v___x_1053_; 
v_a_1050_ = lean_ctor_get(v___x_1049_, 0);
lean_inc(v_a_1050_);
lean_dec_ref_known(v___x_1049_, 1);
v___x_1051_ = l_Lean_Meta_Sym_Simp_Theorems_insert(v_b_1041_, v_a_1050_);
v___x_1052_ = ((size_t)1ULL);
v___x_1053_ = lean_usize_add(v_i_1039_, v___x_1052_);
v_i_1039_ = v___x_1053_;
v_b_1041_ = v___x_1051_;
goto _start;
}
else
{
lean_object* v_a_1055_; lean_object* v___x_1057_; uint8_t v_isShared_1058_; uint8_t v_isSharedCheck_1062_; 
lean_dec_ref(v_b_1041_);
v_a_1055_ = lean_ctor_get(v___x_1049_, 0);
v_isSharedCheck_1062_ = !lean_is_exclusive(v___x_1049_);
if (v_isSharedCheck_1062_ == 0)
{
v___x_1057_ = v___x_1049_;
v_isShared_1058_ = v_isSharedCheck_1062_;
goto v_resetjp_1056_;
}
else
{
lean_inc(v_a_1055_);
lean_dec(v___x_1049_);
v___x_1057_ = lean_box(0);
v_isShared_1058_ = v_isSharedCheck_1062_;
goto v_resetjp_1056_;
}
v_resetjp_1056_:
{
lean_object* v___x_1060_; 
if (v_isShared_1058_ == 0)
{
v___x_1060_ = v___x_1057_;
goto v_reusejp_1059_;
}
else
{
lean_object* v_reuseFailAlloc_1061_; 
v_reuseFailAlloc_1061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1061_, 0, v_a_1055_);
v___x_1060_ = v_reuseFailAlloc_1061_;
goto v_reusejp_1059_;
}
v_reusejp_1059_:
{
return v___x_1060_;
}
}
}
}
else
{
lean_object* v___x_1063_; 
v___x_1063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1063_, 0, v_b_1041_);
return v___x_1063_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_spec__0___redArg___boxed(lean_object* v_as_1064_, lean_object* v_i_1065_, lean_object* v_stop_1066_, lean_object* v_b_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_){
_start:
{
size_t v_i_boxed_1073_; size_t v_stop_boxed_1074_; lean_object* v_res_1075_; 
v_i_boxed_1073_ = lean_unbox_usize(v_i_1065_);
lean_dec(v_i_1065_);
v_stop_boxed_1074_ = lean_unbox_usize(v_stop_1066_);
lean_dec(v_stop_1066_);
v_res_1075_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_spec__0___redArg(v_as_1064_, v_i_boxed_1073_, v_stop_boxed_1074_, v_b_1067_, v___y_1068_, v___y_1069_, v___y_1070_, v___y_1071_);
lean_dec(v___y_1071_);
lean_dec_ref(v___y_1070_);
lean_dec(v___y_1069_);
lean_dec_ref(v___y_1068_);
lean_dec_ref(v_as_1064_);
return v_res_1075_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp___closed__1(void){
_start:
{
lean_object* v___x_1077_; 
v___x_1077_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1077_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp___closed__2(void){
_start:
{
lean_object* v___x_1078_; lean_object* v___x_1079_; 
v___x_1078_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp___closed__1, &l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp___closed__1_once, _init_l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp___closed__1);
v___x_1079_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1079_, 0, v___x_1078_);
return v___x_1079_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp___closed__3(void){
_start:
{
lean_object* v___x_1080_; lean_object* v___x_1081_; 
v___x_1080_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp___closed__2, &l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp___closed__2_once, _init_l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp___closed__2);
v___x_1081_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1081_, 0, v___x_1080_);
lean_ctor_set(v___x_1081_, 1, v___x_1080_);
return v___x_1081_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp(lean_object* v_rewrites_1082_, lean_object* v_e_1083_, lean_object* v_fuel_1084_, lean_object* v_a_1085_, lean_object* v_a_1086_, lean_object* v_a_1087_, lean_object* v_a_1088_, lean_object* v_a_1089_, lean_object* v_a_1090_){
_start:
{
lean_object* v_a_1093_; lean_object* v___y_1109_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; uint8_t v___x_1122_; 
v___x_1119_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp___closed__3, &l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp___closed__3_once, _init_l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp___closed__3);
v___x_1120_ = lean_unsigned_to_nat(0u);
v___x_1121_ = lean_array_get_size(v_rewrites_1082_);
v___x_1122_ = lean_nat_dec_lt(v___x_1120_, v___x_1121_);
if (v___x_1122_ == 0)
{
v_a_1093_ = v___x_1119_;
goto v___jp_1092_;
}
else
{
uint8_t v___x_1123_; 
v___x_1123_ = lean_nat_dec_le(v___x_1121_, v___x_1121_);
if (v___x_1123_ == 0)
{
if (v___x_1122_ == 0)
{
v_a_1093_ = v___x_1119_;
goto v___jp_1092_;
}
else
{
size_t v___x_1124_; size_t v___x_1125_; lean_object* v___x_1126_; 
v___x_1124_ = ((size_t)0ULL);
v___x_1125_ = lean_usize_of_nat(v___x_1121_);
v___x_1126_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_spec__0___redArg(v_rewrites_1082_, v___x_1124_, v___x_1125_, v___x_1119_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_);
v___y_1109_ = v___x_1126_;
goto v___jp_1108_;
}
}
else
{
size_t v___x_1127_; size_t v___x_1128_; lean_object* v___x_1129_; 
v___x_1127_ = ((size_t)0ULL);
v___x_1128_ = lean_usize_of_nat(v___x_1121_);
v___x_1129_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_spec__0___redArg(v_rewrites_1082_, v___x_1127_, v___x_1128_, v___x_1119_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_);
v___y_1109_ = v___x_1129_;
goto v___jp_1108_;
}
}
v___jp_1092_:
{
lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; 
v___x_1094_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp___closed__0));
v___x_1095_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Simp_Theorems_rewrite___boxed), 13, 2);
lean_closure_set(v___x_1095_, 0, v_a_1093_);
lean_closure_set(v___x_1095_, 1, v___x_1094_);
v___x_1096_ = l_Lean_Meta_Sym_shareCommon(v_e_1083_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_);
if (lean_obj_tag(v___x_1096_) == 0)
{
lean_object* v_a_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; 
v_a_1097_ = lean_ctor_get(v___x_1096_, 0);
lean_inc_n(v_a_1097_, 2);
lean_dec_ref_known(v___x_1096_, 1);
v___x_1098_ = lean_box(0);
v___x_1099_ = l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_go(v___x_1095_, v_a_1097_, v_a_1097_, v___x_1098_, v_fuel_1084_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_);
return v___x_1099_;
}
else
{
lean_object* v_a_1100_; lean_object* v___x_1102_; uint8_t v_isShared_1103_; uint8_t v_isSharedCheck_1107_; 
lean_dec_ref(v___x_1095_);
lean_dec(v_fuel_1084_);
v_a_1100_ = lean_ctor_get(v___x_1096_, 0);
v_isSharedCheck_1107_ = !lean_is_exclusive(v___x_1096_);
if (v_isSharedCheck_1107_ == 0)
{
v___x_1102_ = v___x_1096_;
v_isShared_1103_ = v_isSharedCheck_1107_;
goto v_resetjp_1101_;
}
else
{
lean_inc(v_a_1100_);
lean_dec(v___x_1096_);
v___x_1102_ = lean_box(0);
v_isShared_1103_ = v_isSharedCheck_1107_;
goto v_resetjp_1101_;
}
v_resetjp_1101_:
{
lean_object* v___x_1105_; 
if (v_isShared_1103_ == 0)
{
v___x_1105_ = v___x_1102_;
goto v_reusejp_1104_;
}
else
{
lean_object* v_reuseFailAlloc_1106_; 
v_reuseFailAlloc_1106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1106_, 0, v_a_1100_);
v___x_1105_ = v_reuseFailAlloc_1106_;
goto v_reusejp_1104_;
}
v_reusejp_1104_:
{
return v___x_1105_;
}
}
}
}
v___jp_1108_:
{
if (lean_obj_tag(v___y_1109_) == 0)
{
lean_object* v_a_1110_; 
v_a_1110_ = lean_ctor_get(v___y_1109_, 0);
lean_inc(v_a_1110_);
lean_dec_ref_known(v___y_1109_, 1);
v_a_1093_ = v_a_1110_;
goto v___jp_1092_;
}
else
{
lean_object* v_a_1111_; lean_object* v___x_1113_; uint8_t v_isShared_1114_; uint8_t v_isSharedCheck_1118_; 
lean_dec(v_fuel_1084_);
lean_dec_ref(v_e_1083_);
v_a_1111_ = lean_ctor_get(v___y_1109_, 0);
v_isSharedCheck_1118_ = !lean_is_exclusive(v___y_1109_);
if (v_isSharedCheck_1118_ == 0)
{
v___x_1113_ = v___y_1109_;
v_isShared_1114_ = v_isSharedCheck_1118_;
goto v_resetjp_1112_;
}
else
{
lean_inc(v_a_1111_);
lean_dec(v___y_1109_);
v___x_1113_ = lean_box(0);
v_isShared_1114_ = v_isSharedCheck_1118_;
goto v_resetjp_1112_;
}
v_resetjp_1112_:
{
lean_object* v___x_1116_; 
if (v_isShared_1114_ == 0)
{
v___x_1116_ = v___x_1113_;
goto v_reusejp_1115_;
}
else
{
lean_object* v_reuseFailAlloc_1117_; 
v_reuseFailAlloc_1117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1117_, 0, v_a_1111_);
v___x_1116_ = v_reuseFailAlloc_1117_;
goto v_reusejp_1115_;
}
v_reusejp_1115_:
{
return v___x_1116_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp___boxed(lean_object* v_rewrites_1130_, lean_object* v_e_1131_, lean_object* v_fuel_1132_, lean_object* v_a_1133_, lean_object* v_a_1134_, lean_object* v_a_1135_, lean_object* v_a_1136_, lean_object* v_a_1137_, lean_object* v_a_1138_, lean_object* v_a_1139_){
_start:
{
lean_object* v_res_1140_; 
v_res_1140_ = l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp(v_rewrites_1130_, v_e_1131_, v_fuel_1132_, v_a_1133_, v_a_1134_, v_a_1135_, v_a_1136_, v_a_1137_, v_a_1138_);
lean_dec(v_a_1138_);
lean_dec_ref(v_a_1137_);
lean_dec(v_a_1136_);
lean_dec_ref(v_a_1135_);
lean_dec(v_a_1134_);
lean_dec_ref(v_a_1133_);
lean_dec_ref(v_rewrites_1130_);
return v_res_1140_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_spec__0(lean_object* v_as_1141_, size_t v_i_1142_, size_t v_stop_1143_, lean_object* v_b_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_){
_start:
{
lean_object* v___x_1152_; 
v___x_1152_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_spec__0___redArg(v_as_1141_, v_i_1142_, v_stop_1143_, v_b_1144_, v___y_1147_, v___y_1148_, v___y_1149_, v___y_1150_);
return v___x_1152_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_spec__0___boxed(lean_object* v_as_1153_, lean_object* v_i_1154_, lean_object* v_stop_1155_, lean_object* v_b_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_){
_start:
{
size_t v_i_boxed_1164_; size_t v_stop_boxed_1165_; lean_object* v_res_1166_; 
v_i_boxed_1164_ = lean_unbox_usize(v_i_1154_);
lean_dec(v_i_1154_);
v_stop_boxed_1165_ = lean_unbox_usize(v_stop_1155_);
lean_dec(v_stop_1155_);
v_res_1166_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_spec__0(v_as_1153_, v_i_boxed_1164_, v_stop_boxed_1165_, v_b_1156_, v___y_1157_, v___y_1158_, v___y_1159_, v___y_1160_, v___y_1161_, v___y_1162_);
lean_dec(v___y_1162_);
lean_dec_ref(v___y_1161_);
lean_dec(v___y_1160_);
lean_dec_ref(v___y_1159_);
lean_dec(v___y_1158_);
lean_dec_ref(v___y_1157_);
lean_dec_ref(v_as_1153_);
return v_res_1166_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply___lam__0(lean_object* v_s_1167_, lean_object* v_a_1168_, lean_object* v_pre_1169_, lean_object* v_u_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_){
_start:
{
lean_object* v___x_1176_; 
lean_inc_ref(v_u_1170_);
v___x_1176_ = l_Lean_Meta_mkEq(v_u_1170_, v_s_1167_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_);
if (lean_obj_tag(v___x_1176_) == 0)
{
lean_object* v_a_1177_; lean_object* v___x_1179_; uint8_t v_isShared_1180_; uint8_t v_isSharedCheck_1208_; 
v_a_1177_ = lean_ctor_get(v___x_1176_, 0);
v_isSharedCheck_1208_ = !lean_is_exclusive(v___x_1176_);
if (v_isSharedCheck_1208_ == 0)
{
v___x_1179_ = v___x_1176_;
v_isShared_1180_ = v_isSharedCheck_1208_;
goto v_resetjp_1178_;
}
else
{
lean_inc(v_a_1177_);
lean_dec(v___x_1176_);
v___x_1179_ = lean_box(0);
v_isShared_1180_ = v_isSharedCheck_1208_;
goto v_resetjp_1178_;
}
v_resetjp_1178_:
{
lean_object* v___x_1181_; lean_object* v___x_1183_; 
v___x_1181_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_LatticeOp_ofProp___closed__2));
if (v_isShared_1180_ == 0)
{
lean_ctor_set_tag(v___x_1179_, 1);
lean_ctor_set(v___x_1179_, 0, v_a_1168_);
v___x_1183_ = v___x_1179_;
goto v_reusejp_1182_;
}
else
{
lean_object* v_reuseFailAlloc_1207_; 
v_reuseFailAlloc_1207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1207_, 0, v_a_1168_);
v___x_1183_ = v_reuseFailAlloc_1207_;
goto v_reusejp_1182_;
}
v_reusejp_1182_:
{
lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; 
v___x_1184_ = lean_box(0);
v___x_1185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1185_, 0, v_a_1177_);
v___x_1186_ = lean_unsigned_to_nat(3u);
v___x_1187_ = lean_mk_empty_array_with_capacity(v___x_1186_);
v___x_1188_ = lean_array_push(v___x_1187_, v___x_1183_);
v___x_1189_ = lean_array_push(v___x_1188_, v___x_1184_);
v___x_1190_ = lean_array_push(v___x_1189_, v___x_1185_);
v___x_1191_ = l_Lean_Meta_mkAppOptM(v___x_1181_, v___x_1190_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_);
if (lean_obj_tag(v___x_1191_) == 0)
{
lean_object* v_a_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; 
v_a_1192_ = lean_ctor_get(v___x_1191_, 0);
lean_inc(v_a_1192_);
lean_dec_ref_known(v___x_1191_, 1);
v___x_1193_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__4));
v___x_1194_ = lean_unsigned_to_nat(2u);
v___x_1195_ = lean_mk_empty_array_with_capacity(v___x_1194_);
v___x_1196_ = lean_array_push(v___x_1195_, v_a_1192_);
v___x_1197_ = lean_array_push(v___x_1196_, v_pre_1169_);
v___x_1198_ = l_Lean_Meta_mkAppM(v___x_1193_, v___x_1197_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_);
if (lean_obj_tag(v___x_1198_) == 0)
{
lean_object* v_a_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; uint8_t v___x_1203_; uint8_t v___x_1204_; uint8_t v___x_1205_; lean_object* v___x_1206_; 
v_a_1199_ = lean_ctor_get(v___x_1198_, 0);
lean_inc(v_a_1199_);
lean_dec_ref_known(v___x_1198_, 1);
v___x_1200_ = lean_unsigned_to_nat(1u);
v___x_1201_ = lean_mk_empty_array_with_capacity(v___x_1200_);
v___x_1202_ = lean_array_push(v___x_1201_, v_u_1170_);
v___x_1203_ = 0;
v___x_1204_ = 1;
v___x_1205_ = 1;
v___x_1206_ = l_Lean_Meta_mkLambdaFVars(v___x_1202_, v_a_1199_, v___x_1203_, v___x_1204_, v___x_1203_, v___x_1204_, v___x_1205_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_);
lean_dec_ref(v___x_1202_);
return v___x_1206_;
}
else
{
lean_dec_ref(v_u_1170_);
return v___x_1198_;
}
}
else
{
lean_dec_ref(v_u_1170_);
lean_dec_ref(v_pre_1169_);
return v___x_1191_;
}
}
}
}
else
{
lean_dec_ref(v_u_1170_);
lean_dec_ref(v_pre_1169_);
lean_dec_ref(v_a_1168_);
return v___x_1176_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply___lam__0___boxed(lean_object* v_s_1209_, lean_object* v_a_1210_, lean_object* v_pre_1211_, lean_object* v_u_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_){
_start:
{
lean_object* v_res_1218_; 
v_res_1218_ = l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply___lam__0(v_s_1209_, v_a_1210_, v_pre_1211_, v_u_1212_, v___y_1213_, v___y_1214_, v___y_1215_, v___y_1216_);
lean_dec(v___y_1216_);
lean_dec_ref(v___y_1215_);
lean_dec(v___y_1214_);
lean_dec_ref(v___y_1213_);
return v_res_1218_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply_spec__0_spec__0___redArg___lam__0(lean_object* v_k_1219_, lean_object* v_b_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_){
_start:
{
lean_object* v___x_1226_; 
lean_inc(v___y_1224_);
lean_inc_ref(v___y_1223_);
lean_inc(v___y_1222_);
lean_inc_ref(v___y_1221_);
v___x_1226_ = lean_apply_6(v_k_1219_, v_b_1220_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_, lean_box(0));
return v___x_1226_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply_spec__0_spec__0___redArg___lam__0___boxed(lean_object* v_k_1227_, lean_object* v_b_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_){
_start:
{
lean_object* v_res_1234_; 
v_res_1234_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply_spec__0_spec__0___redArg___lam__0(v_k_1227_, v_b_1228_, v___y_1229_, v___y_1230_, v___y_1231_, v___y_1232_);
lean_dec(v___y_1232_);
lean_dec_ref(v___y_1231_);
lean_dec(v___y_1230_);
lean_dec_ref(v___y_1229_);
return v_res_1234_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply_spec__0_spec__0___redArg(lean_object* v_name_1235_, uint8_t v_bi_1236_, lean_object* v_type_1237_, lean_object* v_k_1238_, uint8_t v_kind_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_){
_start:
{
lean_object* v___f_1245_; lean_object* v___x_1246_; 
v___f_1245_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply_spec__0_spec__0___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1245_, 0, v_k_1238_);
v___x_1246_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1235_, v_bi_1236_, v_type_1237_, v___f_1245_, v_kind_1239_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_);
if (lean_obj_tag(v___x_1246_) == 0)
{
lean_object* v_a_1247_; lean_object* v___x_1249_; uint8_t v_isShared_1250_; uint8_t v_isSharedCheck_1254_; 
v_a_1247_ = lean_ctor_get(v___x_1246_, 0);
v_isSharedCheck_1254_ = !lean_is_exclusive(v___x_1246_);
if (v_isSharedCheck_1254_ == 0)
{
v___x_1249_ = v___x_1246_;
v_isShared_1250_ = v_isSharedCheck_1254_;
goto v_resetjp_1248_;
}
else
{
lean_inc(v_a_1247_);
lean_dec(v___x_1246_);
v___x_1249_ = lean_box(0);
v_isShared_1250_ = v_isSharedCheck_1254_;
goto v_resetjp_1248_;
}
v_resetjp_1248_:
{
lean_object* v___x_1252_; 
if (v_isShared_1250_ == 0)
{
v___x_1252_ = v___x_1249_;
goto v_reusejp_1251_;
}
else
{
lean_object* v_reuseFailAlloc_1253_; 
v_reuseFailAlloc_1253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1253_, 0, v_a_1247_);
v___x_1252_ = v_reuseFailAlloc_1253_;
goto v_reusejp_1251_;
}
v_reusejp_1251_:
{
return v___x_1252_;
}
}
}
else
{
lean_object* v_a_1255_; lean_object* v___x_1257_; uint8_t v_isShared_1258_; uint8_t v_isSharedCheck_1262_; 
v_a_1255_ = lean_ctor_get(v___x_1246_, 0);
v_isSharedCheck_1262_ = !lean_is_exclusive(v___x_1246_);
if (v_isSharedCheck_1262_ == 0)
{
v___x_1257_ = v___x_1246_;
v_isShared_1258_ = v_isSharedCheck_1262_;
goto v_resetjp_1256_;
}
else
{
lean_inc(v_a_1255_);
lean_dec(v___x_1246_);
v___x_1257_ = lean_box(0);
v_isShared_1258_ = v_isSharedCheck_1262_;
goto v_resetjp_1256_;
}
v_resetjp_1256_:
{
lean_object* v___x_1260_; 
if (v_isShared_1258_ == 0)
{
v___x_1260_ = v___x_1257_;
goto v_reusejp_1259_;
}
else
{
lean_object* v_reuseFailAlloc_1261_; 
v_reuseFailAlloc_1261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1261_, 0, v_a_1255_);
v___x_1260_ = v_reuseFailAlloc_1261_;
goto v_reusejp_1259_;
}
v_reusejp_1259_:
{
return v___x_1260_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply_spec__0_spec__0___redArg___boxed(lean_object* v_name_1263_, lean_object* v_bi_1264_, lean_object* v_type_1265_, lean_object* v_k_1266_, lean_object* v_kind_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_){
_start:
{
uint8_t v_bi_boxed_1273_; uint8_t v_kind_boxed_1274_; lean_object* v_res_1275_; 
v_bi_boxed_1273_ = lean_unbox(v_bi_1264_);
v_kind_boxed_1274_ = lean_unbox(v_kind_1267_);
v_res_1275_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply_spec__0_spec__0___redArg(v_name_1263_, v_bi_boxed_1273_, v_type_1265_, v_k_1266_, v_kind_boxed_1274_, v___y_1268_, v___y_1269_, v___y_1270_, v___y_1271_);
lean_dec(v___y_1271_);
lean_dec_ref(v___y_1270_);
lean_dec(v___y_1269_);
lean_dec_ref(v___y_1268_);
return v_res_1275_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply_spec__0___redArg(lean_object* v_name_1276_, lean_object* v_type_1277_, lean_object* v_k_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_){
_start:
{
uint8_t v___x_1284_; uint8_t v___x_1285_; lean_object* v___x_1286_; 
v___x_1284_ = 0;
v___x_1285_ = 0;
v___x_1286_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply_spec__0_spec__0___redArg(v_name_1276_, v___x_1284_, v_type_1277_, v_k_1278_, v___x_1285_, v___y_1279_, v___y_1280_, v___y_1281_, v___y_1282_);
return v___x_1286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply_spec__0___redArg___boxed(lean_object* v_name_1287_, lean_object* v_type_1288_, lean_object* v_k_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_){
_start:
{
lean_object* v_res_1295_; 
v_res_1295_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply_spec__0___redArg(v_name_1287_, v_type_1288_, v_k_1289_, v___y_1290_, v___y_1291_, v___y_1292_, v___y_1293_);
lean_dec(v___y_1293_);
lean_dec_ref(v___y_1292_);
lean_dec(v___y_1291_);
lean_dec_ref(v___y_1290_);
return v_res_1295_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply___closed__1(void){
_start:
{
lean_object* v___x_1297_; lean_object* v___x_1298_; 
v___x_1297_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply___closed__0));
v___x_1298_ = l_Lean_stringToMessageData(v___x_1297_);
return v___x_1298_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply(lean_object* v_introThm_1307_, lean_object* v_opAs_1308_, lean_object* v_pre_1309_, lean_object* v_ss_1310_, lean_object* v_a_1311_, lean_object* v_a_1312_, lean_object* v_a_1313_, lean_object* v_a_1314_){
_start:
{
if (lean_obj_tag(v_ss_1310_) == 0)
{
lean_object* v___x_1316_; 
lean_inc(v_introThm_1307_);
v___x_1316_ = l_Lean_Meta_mkConstWithFreshMVarLevels(v_introThm_1307_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
if (lean_obj_tag(v___x_1316_) == 0)
{
lean_object* v_a_1317_; lean_object* v___x_1318_; 
v_a_1317_ = lean_ctor_get(v___x_1316_, 0);
lean_inc_n(v_a_1317_, 2);
lean_dec_ref_known(v___x_1316_, 1);
lean_inc(v_a_1314_);
lean_inc_ref(v_a_1313_);
lean_inc(v_a_1312_);
lean_inc_ref(v_a_1311_);
v___x_1318_ = lean_infer_type(v_a_1317_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
if (lean_obj_tag(v___x_1318_) == 0)
{
lean_object* v_a_1319_; uint8_t v___x_1320_; lean_object* v___x_1321_; 
v_a_1319_ = lean_ctor_get(v___x_1318_, 0);
lean_inc(v_a_1319_);
lean_dec_ref_known(v___x_1318_, 1);
v___x_1320_ = 0;
v___x_1321_ = l_Lean_Meta_forallMetaTelescope(v_a_1319_, v___x_1320_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
if (lean_obj_tag(v___x_1321_) == 0)
{
lean_object* v_a_1322_; lean_object* v___x_1324_; uint8_t v_isShared_1325_; uint8_t v_isSharedCheck_1381_; 
v_a_1322_ = lean_ctor_get(v___x_1321_, 0);
v_isSharedCheck_1381_ = !lean_is_exclusive(v___x_1321_);
if (v_isSharedCheck_1381_ == 0)
{
v___x_1324_ = v___x_1321_;
v_isShared_1325_ = v_isSharedCheck_1381_;
goto v_resetjp_1323_;
}
else
{
lean_inc(v_a_1322_);
lean_dec(v___x_1321_);
v___x_1324_ = lean_box(0);
v_isShared_1325_ = v_isSharedCheck_1381_;
goto v_resetjp_1323_;
}
v_resetjp_1323_:
{
lean_object* v_fst_1326_; lean_object* v_snd_1327_; lean_object* v___x_1329_; uint8_t v_isShared_1330_; uint8_t v_isSharedCheck_1380_; 
v_fst_1326_ = lean_ctor_get(v_a_1322_, 0);
v_snd_1327_ = lean_ctor_get(v_a_1322_, 1);
v_isSharedCheck_1380_ = !lean_is_exclusive(v_a_1322_);
if (v_isSharedCheck_1380_ == 0)
{
v___x_1329_ = v_a_1322_;
v_isShared_1330_ = v_isSharedCheck_1380_;
goto v_resetjp_1328_;
}
else
{
lean_inc(v_snd_1327_);
lean_inc(v_fst_1326_);
lean_dec(v_a_1322_);
v___x_1329_ = lean_box(0);
v_isShared_1330_ = v_isSharedCheck_1380_;
goto v_resetjp_1328_;
}
v_resetjp_1328_:
{
lean_object* v_snd_1336_; lean_object* v___x_1338_; uint8_t v_isShared_1339_; uint8_t v_isSharedCheck_1378_; 
v_snd_1336_ = lean_ctor_get(v_snd_1327_, 1);
v_isSharedCheck_1378_ = !lean_is_exclusive(v_snd_1327_);
if (v_isSharedCheck_1378_ == 0)
{
lean_object* v_unused_1379_; 
v_unused_1379_ = lean_ctor_get(v_snd_1327_, 0);
lean_dec(v_unused_1379_);
v___x_1338_ = v_snd_1327_;
v_isShared_1339_ = v_isSharedCheck_1378_;
goto v_resetjp_1337_;
}
else
{
lean_inc(v_snd_1336_);
lean_dec(v_snd_1327_);
v___x_1338_ = lean_box(0);
v_isShared_1339_ = v_isSharedCheck_1378_;
goto v_resetjp_1337_;
}
v___jp_1331_:
{
lean_object* v___x_1332_; lean_object* v___x_1334_; 
v___x_1332_ = l_Lean_mkAppN(v_a_1317_, v_fst_1326_);
lean_dec(v_fst_1326_);
if (v_isShared_1325_ == 0)
{
lean_ctor_set(v___x_1324_, 0, v___x_1332_);
v___x_1334_ = v___x_1324_;
goto v_reusejp_1333_;
}
else
{
lean_object* v_reuseFailAlloc_1335_; 
v_reuseFailAlloc_1335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1335_, 0, v___x_1332_);
v___x_1334_ = v_reuseFailAlloc_1335_;
goto v_reusejp_1333_;
}
v_reusejp_1333_:
{
return v___x_1334_;
}
}
v_resetjp_1337_:
{
lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; 
v___x_1340_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__2));
v___x_1341_ = lean_unsigned_to_nat(2u);
v___x_1342_ = lean_mk_empty_array_with_capacity(v___x_1341_);
v___x_1343_ = lean_array_push(v___x_1342_, v_pre_1309_);
v___x_1344_ = lean_array_push(v___x_1343_, v_opAs_1308_);
v___x_1345_ = l_Lean_Meta_mkAppM(v___x_1340_, v___x_1344_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
if (lean_obj_tag(v___x_1345_) == 0)
{
lean_object* v_a_1346_; lean_object* v___x_1347_; 
v_a_1346_ = lean_ctor_get(v___x_1345_, 0);
lean_inc_n(v_a_1346_, 2);
lean_dec_ref_known(v___x_1345_, 1);
v___x_1347_ = l_Lean_Meta_isExprDefEq(v_snd_1336_, v_a_1346_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
if (lean_obj_tag(v___x_1347_) == 0)
{
lean_object* v_a_1348_; uint8_t v___x_1349_; 
v_a_1348_ = lean_ctor_get(v___x_1347_, 0);
lean_inc(v_a_1348_);
lean_dec_ref_known(v___x_1347_, 1);
v___x_1349_ = lean_unbox(v_a_1348_);
lean_dec(v_a_1348_);
if (v___x_1349_ == 0)
{
lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1353_; 
v___x_1350_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__4);
v___x_1351_ = l_Lean_MessageData_ofName(v_introThm_1307_);
if (v_isShared_1339_ == 0)
{
lean_ctor_set_tag(v___x_1338_, 7);
lean_ctor_set(v___x_1338_, 1, v___x_1351_);
lean_ctor_set(v___x_1338_, 0, v___x_1350_);
v___x_1353_ = v___x_1338_;
goto v_reusejp_1352_;
}
else
{
lean_object* v_reuseFailAlloc_1369_; 
v_reuseFailAlloc_1369_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1369_, 0, v___x_1350_);
lean_ctor_set(v_reuseFailAlloc_1369_, 1, v___x_1351_);
v___x_1353_ = v_reuseFailAlloc_1369_;
goto v_reusejp_1352_;
}
v_reusejp_1352_:
{
lean_object* v___x_1354_; lean_object* v___x_1356_; 
v___x_1354_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply___closed__1, &l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply___closed__1_once, _init_l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply___closed__1);
if (v_isShared_1330_ == 0)
{
lean_ctor_set_tag(v___x_1329_, 7);
lean_ctor_set(v___x_1329_, 1, v___x_1354_);
lean_ctor_set(v___x_1329_, 0, v___x_1353_);
v___x_1356_ = v___x_1329_;
goto v_reusejp_1355_;
}
else
{
lean_object* v_reuseFailAlloc_1368_; 
v_reuseFailAlloc_1368_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1368_, 0, v___x_1353_);
lean_ctor_set(v_reuseFailAlloc_1368_, 1, v___x_1354_);
v___x_1356_ = v_reuseFailAlloc_1368_;
goto v_reusejp_1355_;
}
v_reusejp_1355_:
{
lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; 
v___x_1357_ = l_Lean_MessageData_ofExpr(v_a_1346_);
v___x_1358_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1358_, 0, v___x_1356_);
lean_ctor_set(v___x_1358_, 1, v___x_1357_);
v___x_1359_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__1___redArg(v___x_1358_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
if (lean_obj_tag(v___x_1359_) == 0)
{
lean_dec_ref_known(v___x_1359_, 1);
goto v___jp_1331_;
}
else
{
lean_object* v_a_1360_; lean_object* v___x_1362_; uint8_t v_isShared_1363_; uint8_t v_isSharedCheck_1367_; 
lean_dec(v_fst_1326_);
lean_del_object(v___x_1324_);
lean_dec(v_a_1317_);
v_a_1360_ = lean_ctor_get(v___x_1359_, 0);
v_isSharedCheck_1367_ = !lean_is_exclusive(v___x_1359_);
if (v_isSharedCheck_1367_ == 0)
{
v___x_1362_ = v___x_1359_;
v_isShared_1363_ = v_isSharedCheck_1367_;
goto v_resetjp_1361_;
}
else
{
lean_inc(v_a_1360_);
lean_dec(v___x_1359_);
v___x_1362_ = lean_box(0);
v_isShared_1363_ = v_isSharedCheck_1367_;
goto v_resetjp_1361_;
}
v_resetjp_1361_:
{
lean_object* v___x_1365_; 
if (v_isShared_1363_ == 0)
{
v___x_1365_ = v___x_1362_;
goto v_reusejp_1364_;
}
else
{
lean_object* v_reuseFailAlloc_1366_; 
v_reuseFailAlloc_1366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1366_, 0, v_a_1360_);
v___x_1365_ = v_reuseFailAlloc_1366_;
goto v_reusejp_1364_;
}
v_reusejp_1364_:
{
return v___x_1365_;
}
}
}
}
}
}
else
{
lean_dec(v_a_1346_);
lean_del_object(v___x_1338_);
lean_del_object(v___x_1329_);
lean_dec(v_introThm_1307_);
goto v___jp_1331_;
}
}
else
{
lean_object* v_a_1370_; lean_object* v___x_1372_; uint8_t v_isShared_1373_; uint8_t v_isSharedCheck_1377_; 
lean_dec(v_a_1346_);
lean_del_object(v___x_1338_);
lean_del_object(v___x_1329_);
lean_dec(v_fst_1326_);
lean_del_object(v___x_1324_);
lean_dec(v_a_1317_);
lean_dec(v_introThm_1307_);
v_a_1370_ = lean_ctor_get(v___x_1347_, 0);
v_isSharedCheck_1377_ = !lean_is_exclusive(v___x_1347_);
if (v_isSharedCheck_1377_ == 0)
{
v___x_1372_ = v___x_1347_;
v_isShared_1373_ = v_isSharedCheck_1377_;
goto v_resetjp_1371_;
}
else
{
lean_inc(v_a_1370_);
lean_dec(v___x_1347_);
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
else
{
lean_del_object(v___x_1338_);
lean_dec(v_snd_1336_);
lean_del_object(v___x_1329_);
lean_dec(v_fst_1326_);
lean_del_object(v___x_1324_);
lean_dec(v_a_1317_);
lean_dec(v_introThm_1307_);
return v___x_1345_;
}
}
}
}
}
else
{
lean_object* v_a_1382_; lean_object* v___x_1384_; uint8_t v_isShared_1385_; uint8_t v_isSharedCheck_1389_; 
lean_dec(v_a_1317_);
lean_dec_ref(v_pre_1309_);
lean_dec_ref(v_opAs_1308_);
lean_dec(v_introThm_1307_);
v_a_1382_ = lean_ctor_get(v___x_1321_, 0);
v_isSharedCheck_1389_ = !lean_is_exclusive(v___x_1321_);
if (v_isSharedCheck_1389_ == 0)
{
v___x_1384_ = v___x_1321_;
v_isShared_1385_ = v_isSharedCheck_1389_;
goto v_resetjp_1383_;
}
else
{
lean_inc(v_a_1382_);
lean_dec(v___x_1321_);
v___x_1384_ = lean_box(0);
v_isShared_1385_ = v_isSharedCheck_1389_;
goto v_resetjp_1383_;
}
v_resetjp_1383_:
{
lean_object* v___x_1387_; 
if (v_isShared_1385_ == 0)
{
v___x_1387_ = v___x_1384_;
goto v_reusejp_1386_;
}
else
{
lean_object* v_reuseFailAlloc_1388_; 
v_reuseFailAlloc_1388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1388_, 0, v_a_1382_);
v___x_1387_ = v_reuseFailAlloc_1388_;
goto v_reusejp_1386_;
}
v_reusejp_1386_:
{
return v___x_1387_;
}
}
}
}
else
{
lean_dec(v_a_1317_);
lean_dec_ref(v_pre_1309_);
lean_dec_ref(v_opAs_1308_);
lean_dec(v_introThm_1307_);
return v___x_1318_;
}
}
else
{
lean_dec_ref(v_pre_1309_);
lean_dec_ref(v_opAs_1308_);
lean_dec(v_introThm_1307_);
return v___x_1316_;
}
}
else
{
lean_object* v___x_1390_; lean_object* v_s_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v_init_1394_; lean_object* v___x_1395_; lean_object* v_Q_1396_; lean_object* v___x_1397_; 
v___x_1390_ = l_Lean_instInhabitedExpr;
v_s_1391_ = l_List_getLast_x21___redArg(v___x_1390_, v_ss_1310_);
v___x_1392_ = lean_array_mk(v_ss_1310_);
v___x_1393_ = lean_array_pop(v___x_1392_);
v_init_1394_ = lean_array_to_list(v___x_1393_);
lean_inc(v_init_1394_);
v___x_1395_ = lean_array_mk(v_init_1394_);
lean_inc_ref(v_opAs_1308_);
v_Q_1396_ = l_Lean_mkAppN(v_opAs_1308_, v___x_1395_);
lean_dec_ref(v___x_1395_);
lean_inc(v_a_1314_);
lean_inc_ref(v_a_1313_);
lean_inc(v_a_1312_);
lean_inc_ref(v_a_1311_);
lean_inc_ref(v_pre_1309_);
v___x_1397_ = lean_infer_type(v_pre_1309_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
if (lean_obj_tag(v___x_1397_) == 0)
{
lean_object* v_a_1398_; lean_object* v___f_1399_; lean_object* v___x_1400_; 
v_a_1398_ = lean_ctor_get(v___x_1397_, 0);
lean_inc(v_a_1398_);
lean_dec_ref_known(v___x_1397_, 1);
lean_inc_ref(v_pre_1309_);
lean_inc_n(v_s_1391_, 2);
v___f_1399_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply___lam__0___boxed), 9, 3);
lean_closure_set(v___f_1399_, 0, v_s_1391_);
lean_closure_set(v___f_1399_, 1, v_a_1398_);
lean_closure_set(v___f_1399_, 2, v_pre_1309_);
lean_inc(v_a_1314_);
lean_inc_ref(v_a_1313_);
lean_inc(v_a_1312_);
lean_inc_ref(v_a_1311_);
v___x_1400_ = lean_infer_type(v_s_1391_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
if (lean_obj_tag(v___x_1400_) == 0)
{
lean_object* v_a_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; 
v_a_1401_ = lean_ctor_get(v___x_1400_, 0);
lean_inc(v_a_1401_);
lean_dec_ref_known(v___x_1400_, 1);
v___x_1402_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply___closed__3));
v___x_1403_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply_spec__0___redArg(v___x_1402_, v_a_1401_, v___f_1399_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
if (lean_obj_tag(v___x_1403_) == 0)
{
lean_object* v_a_1404_; lean_object* v___x_1405_; 
v_a_1404_ = lean_ctor_get(v___x_1403_, 0);
lean_inc(v_a_1404_);
lean_dec_ref_known(v___x_1403_, 1);
v___x_1405_ = l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply(v_introThm_1307_, v_opAs_1308_, v_a_1404_, v_init_1394_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
if (lean_obj_tag(v___x_1405_) == 0)
{
lean_object* v_a_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; 
v_a_1406_ = lean_ctor_get(v___x_1405_, 0);
lean_inc(v_a_1406_);
lean_dec_ref_known(v___x_1405_, 1);
v___x_1407_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply___closed__5));
v___x_1408_ = lean_unsigned_to_nat(4u);
v___x_1409_ = lean_mk_empty_array_with_capacity(v___x_1408_);
v___x_1410_ = lean_array_push(v___x_1409_, v_s_1391_);
v___x_1411_ = lean_array_push(v___x_1410_, v_pre_1309_);
v___x_1412_ = lean_array_push(v___x_1411_, v_Q_1396_);
v___x_1413_ = lean_array_push(v___x_1412_, v_a_1406_);
v___x_1414_ = l_Lean_Meta_mkAppM(v___x_1407_, v___x_1413_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
return v___x_1414_;
}
else
{
lean_dec_ref(v_Q_1396_);
lean_dec(v_s_1391_);
lean_dec_ref(v_pre_1309_);
return v___x_1405_;
}
}
else
{
lean_dec_ref(v_Q_1396_);
lean_dec(v_init_1394_);
lean_dec(v_s_1391_);
lean_dec_ref(v_pre_1309_);
lean_dec_ref(v_opAs_1308_);
lean_dec(v_introThm_1307_);
return v___x_1403_;
}
}
else
{
lean_dec_ref(v___f_1399_);
lean_dec_ref(v_Q_1396_);
lean_dec(v_init_1394_);
lean_dec(v_s_1391_);
lean_dec_ref(v_pre_1309_);
lean_dec_ref(v_opAs_1308_);
lean_dec(v_introThm_1307_);
return v___x_1400_;
}
}
else
{
lean_dec_ref(v_Q_1396_);
lean_dec(v_init_1394_);
lean_dec(v_s_1391_);
lean_dec_ref(v_pre_1309_);
lean_dec_ref(v_opAs_1308_);
lean_dec(v_introThm_1307_);
return v___x_1397_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply___boxed(lean_object* v_introThm_1415_, lean_object* v_opAs_1416_, lean_object* v_pre_1417_, lean_object* v_ss_1418_, lean_object* v_a_1419_, lean_object* v_a_1420_, lean_object* v_a_1421_, lean_object* v_a_1422_, lean_object* v_a_1423_){
_start:
{
lean_object* v_res_1424_; 
v_res_1424_ = l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply(v_introThm_1415_, v_opAs_1416_, v_pre_1417_, v_ss_1418_, v_a_1419_, v_a_1420_, v_a_1421_, v_a_1422_);
lean_dec(v_a_1422_);
lean_dec_ref(v_a_1421_);
lean_dec(v_a_1420_);
lean_dec_ref(v_a_1419_);
return v_res_1424_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply_spec__0_spec__0(lean_object* v_00_u03b1_1425_, lean_object* v_name_1426_, uint8_t v_bi_1427_, lean_object* v_type_1428_, lean_object* v_k_1429_, uint8_t v_kind_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_){
_start:
{
lean_object* v___x_1436_; 
v___x_1436_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply_spec__0_spec__0___redArg(v_name_1426_, v_bi_1427_, v_type_1428_, v_k_1429_, v_kind_1430_, v___y_1431_, v___y_1432_, v___y_1433_, v___y_1434_);
return v___x_1436_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1437_, lean_object* v_name_1438_, lean_object* v_bi_1439_, lean_object* v_type_1440_, lean_object* v_k_1441_, lean_object* v_kind_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_){
_start:
{
uint8_t v_bi_boxed_1448_; uint8_t v_kind_boxed_1449_; lean_object* v_res_1450_; 
v_bi_boxed_1448_ = lean_unbox(v_bi_1439_);
v_kind_boxed_1449_ = lean_unbox(v_kind_1442_);
v_res_1450_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply_spec__0_spec__0(v_00_u03b1_1437_, v_name_1438_, v_bi_boxed_1448_, v_type_1440_, v_k_1441_, v_kind_boxed_1449_, v___y_1443_, v___y_1444_, v___y_1445_, v___y_1446_);
lean_dec(v___y_1446_);
lean_dec_ref(v___y_1445_);
lean_dec(v___y_1444_);
lean_dec_ref(v___y_1443_);
return v_res_1450_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply_spec__0(lean_object* v_00_u03b1_1451_, lean_object* v_name_1452_, lean_object* v_type_1453_, lean_object* v_k_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_){
_start:
{
lean_object* v___x_1460_; 
v___x_1460_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply_spec__0___redArg(v_name_1452_, v_type_1453_, v_k_1454_, v___y_1455_, v___y_1456_, v___y_1457_, v___y_1458_);
return v___x_1460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply_spec__0___boxed(lean_object* v_00_u03b1_1461_, lean_object* v_name_1462_, lean_object* v_type_1463_, lean_object* v_k_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_){
_start:
{
lean_object* v_res_1470_; 
v_res_1470_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply_spec__0(v_00_u03b1_1461_, v_name_1462_, v_type_1463_, v_k_1464_, v___y_1465_, v___y_1466_, v___y_1467_, v___y_1468_);
lean_dec(v___y_1468_);
lean_dec_ref(v___y_1467_);
lean_dec(v___y_1466_);
lean_dec_ref(v___y_1465_);
return v_res_1470_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__0___redArg(size_t v_sz_1471_, size_t v_i_1472_, lean_object* v_bs_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_){
_start:
{
uint8_t v___x_1479_; 
v___x_1479_ = lean_usize_dec_lt(v_i_1472_, v_sz_1471_);
if (v___x_1479_ == 0)
{
lean_object* v___x_1480_; 
v___x_1480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1480_, 0, v_bs_1473_);
return v___x_1480_;
}
else
{
lean_object* v_v_1481_; lean_object* v___x_1482_; lean_object* v_bs_x27_1483_; lean_object* v___y_1485_; lean_object* v___x_1499_; 
v_v_1481_ = lean_array_uget(v_bs_1473_, v_i_1472_);
v___x_1482_ = lean_unsigned_to_nat(0u);
v_bs_x27_1483_ = lean_array_uset(v_bs_1473_, v_i_1472_, v___x_1482_);
lean_inc(v___y_1477_);
lean_inc_ref(v___y_1476_);
lean_inc(v___y_1475_);
lean_inc_ref(v___y_1474_);
v___x_1499_ = lean_infer_type(v_v_1481_, v___y_1474_, v___y_1475_, v___y_1476_, v___y_1477_);
if (lean_obj_tag(v___x_1499_) == 0)
{
lean_object* v_a_1500_; lean_object* v___x_1502_; uint8_t v_isShared_1503_; uint8_t v_isSharedCheck_1510_; 
v_a_1500_ = lean_ctor_get(v___x_1499_, 0);
v_isSharedCheck_1510_ = !lean_is_exclusive(v___x_1499_);
if (v_isSharedCheck_1510_ == 0)
{
v___x_1502_ = v___x_1499_;
v_isShared_1503_ = v_isSharedCheck_1510_;
goto v_resetjp_1501_;
}
else
{
lean_inc(v_a_1500_);
lean_dec(v___x_1499_);
v___x_1502_ = lean_box(0);
v_isShared_1503_ = v_isSharedCheck_1510_;
goto v_resetjp_1501_;
}
v_resetjp_1501_:
{
lean_object* v___x_1505_; 
if (v_isShared_1503_ == 0)
{
lean_ctor_set_tag(v___x_1502_, 1);
v___x_1505_ = v___x_1502_;
goto v_reusejp_1504_;
}
else
{
lean_object* v_reuseFailAlloc_1509_; 
v_reuseFailAlloc_1509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1509_, 0, v_a_1500_);
v___x_1505_ = v_reuseFailAlloc_1509_;
goto v_reusejp_1504_;
}
v_reusejp_1504_:
{
uint8_t v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; 
v___x_1506_ = 0;
v___x_1507_ = lean_box(0);
v___x_1508_ = l_Lean_Meta_mkFreshExprMVar(v___x_1505_, v___x_1506_, v___x_1507_, v___y_1474_, v___y_1475_, v___y_1476_, v___y_1477_);
v___y_1485_ = v___x_1508_;
goto v___jp_1484_;
}
}
}
else
{
v___y_1485_ = v___x_1499_;
goto v___jp_1484_;
}
v___jp_1484_:
{
if (lean_obj_tag(v___y_1485_) == 0)
{
lean_object* v_a_1486_; size_t v___x_1487_; size_t v___x_1488_; lean_object* v___x_1489_; 
v_a_1486_ = lean_ctor_get(v___y_1485_, 0);
lean_inc(v_a_1486_);
lean_dec_ref_known(v___y_1485_, 1);
v___x_1487_ = ((size_t)1ULL);
v___x_1488_ = lean_usize_add(v_i_1472_, v___x_1487_);
v___x_1489_ = lean_array_uset(v_bs_x27_1483_, v_i_1472_, v_a_1486_);
v_i_1472_ = v___x_1488_;
v_bs_1473_ = v___x_1489_;
goto _start;
}
else
{
lean_object* v_a_1491_; lean_object* v___x_1493_; uint8_t v_isShared_1494_; uint8_t v_isSharedCheck_1498_; 
lean_dec_ref(v_bs_x27_1483_);
v_a_1491_ = lean_ctor_get(v___y_1485_, 0);
v_isSharedCheck_1498_ = !lean_is_exclusive(v___y_1485_);
if (v_isSharedCheck_1498_ == 0)
{
v___x_1493_ = v___y_1485_;
v_isShared_1494_ = v_isSharedCheck_1498_;
goto v_resetjp_1492_;
}
else
{
lean_inc(v_a_1491_);
lean_dec(v___y_1485_);
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
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__0___redArg___boxed(lean_object* v_sz_1511_, lean_object* v_i_1512_, lean_object* v_bs_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_){
_start:
{
size_t v_sz_boxed_1519_; size_t v_i_boxed_1520_; lean_object* v_res_1521_; 
v_sz_boxed_1519_ = lean_unbox_usize(v_sz_1511_);
lean_dec(v_sz_1511_);
v_i_boxed_1520_ = lean_unbox_usize(v_i_1512_);
lean_dec(v_i_1512_);
v_res_1521_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__0___redArg(v_sz_boxed_1519_, v_i_boxed_1520_, v_bs_1513_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_);
lean_dec(v___y_1517_);
lean_dec_ref(v___y_1516_);
lean_dec(v___y_1515_);
lean_dec_ref(v___y_1514_);
return v_res_1521_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__1_spec__1___redArg(lean_object* v_a_1522_, lean_object* v_x_1523_){
_start:
{
if (lean_obj_tag(v_x_1523_) == 0)
{
lean_object* v___x_1524_; 
v___x_1524_ = lean_box(0);
return v___x_1524_;
}
else
{
lean_object* v_key_1525_; lean_object* v_value_1526_; lean_object* v_tail_1527_; uint8_t v___x_1528_; 
v_key_1525_ = lean_ctor_get(v_x_1523_, 0);
v_value_1526_ = lean_ctor_get(v_x_1523_, 1);
v_tail_1527_ = lean_ctor_get(v_x_1523_, 2);
v___x_1528_ = lean_name_eq(v_key_1525_, v_a_1522_);
if (v___x_1528_ == 0)
{
v_x_1523_ = v_tail_1527_;
goto _start;
}
else
{
lean_object* v___x_1530_; 
lean_inc(v_value_1526_);
v___x_1530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1530_, 0, v_value_1526_);
return v___x_1530_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__1_spec__1___redArg___boxed(lean_object* v_a_1531_, lean_object* v_x_1532_){
_start:
{
lean_object* v_res_1533_; 
v_res_1533_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__1_spec__1___redArg(v_a_1531_, v_x_1532_);
lean_dec(v_x_1532_);
lean_dec(v_a_1531_);
return v_res_1533_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__1___redArg(lean_object* v_m_1534_, lean_object* v_a_1535_){
_start:
{
lean_object* v_buckets_1536_; lean_object* v___x_1537_; uint64_t v___y_1539_; 
v_buckets_1536_ = lean_ctor_get(v_m_1534_, 1);
v___x_1537_ = lean_array_get_size(v_buckets_1536_);
if (lean_obj_tag(v_a_1535_) == 0)
{
uint64_t v___x_1553_; 
v___x_1553_ = 1723ULL;
v___y_1539_ = v___x_1553_;
goto v___jp_1538_;
}
else
{
uint64_t v_hash_1554_; 
v_hash_1554_ = lean_ctor_get_uint64(v_a_1535_, sizeof(void*)*2);
v___y_1539_ = v_hash_1554_;
goto v___jp_1538_;
}
v___jp_1538_:
{
uint64_t v___x_1540_; uint64_t v___x_1541_; uint64_t v_fold_1542_; uint64_t v___x_1543_; uint64_t v___x_1544_; uint64_t v___x_1545_; size_t v___x_1546_; size_t v___x_1547_; size_t v___x_1548_; size_t v___x_1549_; size_t v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; 
v___x_1540_ = 32ULL;
v___x_1541_ = lean_uint64_shift_right(v___y_1539_, v___x_1540_);
v_fold_1542_ = lean_uint64_xor(v___y_1539_, v___x_1541_);
v___x_1543_ = 16ULL;
v___x_1544_ = lean_uint64_shift_right(v_fold_1542_, v___x_1543_);
v___x_1545_ = lean_uint64_xor(v_fold_1542_, v___x_1544_);
v___x_1546_ = lean_uint64_to_usize(v___x_1545_);
v___x_1547_ = lean_usize_of_nat(v___x_1537_);
v___x_1548_ = ((size_t)1ULL);
v___x_1549_ = lean_usize_sub(v___x_1547_, v___x_1548_);
v___x_1550_ = lean_usize_land(v___x_1546_, v___x_1549_);
v___x_1551_ = lean_array_uget_borrowed(v_buckets_1536_, v___x_1550_);
v___x_1552_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__1_spec__1___redArg(v_a_1535_, v___x_1551_);
return v___x_1552_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__1___redArg___boxed(lean_object* v_m_1555_, lean_object* v_a_1556_){
_start:
{
lean_object* v_res_1557_; 
v_res_1557_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__1___redArg(v_m_1555_, v_a_1556_);
lean_dec(v_a_1556_);
lean_dec_ref(v_m_1555_);
return v_res_1557_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__2___closed__4(void){
_start:
{
lean_object* v___x_1564_; lean_object* v___x_1565_; 
v___x_1564_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__2___closed__3));
v___x_1565_ = l_Lean_stringToMessageData(v___x_1564_);
return v___x_1565_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__2___closed__6(void){
_start:
{
lean_object* v___x_1567_; lean_object* v___x_1568_; 
v___x_1567_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__2___closed__5));
v___x_1568_ = l_Lean_stringToMessageData(v___x_1567_);
return v___x_1568_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__2(lean_object* v_op_1569_, lean_object* v___y_1570_, lean_object* v_a_1571_, lean_object* v_x_1572_, lean_object* v_x_1573_, lean_object* v_x_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_){
_start:
{
lean_object* v_prf_1583_; lean_object* v___y_1584_; lean_object* v___y_1585_; lean_object* v___y_1586_; lean_object* v___y_1587_; 
if (lean_obj_tag(v_x_1572_) == 5)
{
lean_object* v_fn_1604_; lean_object* v_arg_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; 
v_fn_1604_ = lean_ctor_get(v_x_1572_, 0);
lean_inc_ref(v_fn_1604_);
v_arg_1605_ = lean_ctor_get(v_x_1572_, 1);
lean_inc_ref(v_arg_1605_);
lean_dec_ref_known(v_x_1572_, 2);
v___x_1606_ = lean_array_set(v_x_1573_, v_x_1574_, v_arg_1605_);
v___x_1607_ = lean_unsigned_to_nat(1u);
v___x_1608_ = lean_nat_sub(v_x_1574_, v___x_1607_);
lean_dec(v_x_1574_);
v_x_1572_ = v_fn_1604_;
v_x_1573_ = v___x_1606_;
v_x_1574_ = v___x_1608_;
goto _start;
}
else
{
lean_object* v_head_1610_; lean_object* v_numConst_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; size_t v_sz_1615_; size_t v___x_1616_; lean_object* v___x_1617_; 
lean_dec(v_x_1574_);
v_head_1610_ = lean_ctor_get(v_op_1569_, 0);
lean_inc(v_head_1610_);
v_numConst_1611_ = lean_ctor_get(v_op_1569_, 1);
lean_inc_n(v_numConst_1611_, 2);
lean_dec_ref(v_op_1569_);
v___x_1612_ = lean_unsigned_to_nat(0u);
v___x_1613_ = lean_array_get_size(v_x_1573_);
v___x_1614_ = l_Array_extract___redArg(v_x_1573_, v_numConst_1611_, v___x_1613_);
v_sz_1615_ = lean_array_size(v___x_1614_);
v___x_1616_ = ((size_t)0ULL);
v___x_1617_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__0___redArg(v_sz_1615_, v___x_1616_, v___x_1614_, v___y_1577_, v___y_1578_, v___y_1579_, v___y_1580_);
if (lean_obj_tag(v___x_1617_) == 0)
{
lean_object* v_a_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; 
v_a_1618_ = lean_ctor_get(v___x_1617_, 0);
lean_inc(v_a_1618_);
lean_dec_ref_known(v___x_1617_, 1);
v___x_1619_ = l_Array_extract___redArg(v_x_1573_, v___x_1612_, v_numConst_1611_);
lean_dec_ref(v_x_1573_);
v___x_1620_ = l_Array_append___redArg(v___x_1619_, v_a_1618_);
lean_dec(v_a_1618_);
v___x_1621_ = l_Lean_mkAppN(v_x_1572_, v___x_1620_);
lean_dec_ref(v___x_1620_);
v___x_1622_ = lean_unsigned_to_nat(256u);
lean_inc_ref(v___x_1621_);
v___x_1623_ = l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp(v___y_1570_, v___x_1621_, v___x_1622_, v___y_1575_, v___y_1576_, v___y_1577_, v___y_1578_, v___y_1579_, v___y_1580_);
if (lean_obj_tag(v___x_1623_) == 0)
{
lean_object* v_a_1624_; lean_object* v_fst_1625_; lean_object* v_snd_1626_; lean_object* v___x_1628_; uint8_t v_isShared_1629_; uint8_t v_isSharedCheck_1798_; 
v_a_1624_ = lean_ctor_get(v___x_1623_, 0);
lean_inc(v_a_1624_);
lean_dec_ref_known(v___x_1623_, 1);
v_fst_1625_ = lean_ctor_get(v_a_1624_, 0);
v_snd_1626_ = lean_ctor_get(v_a_1624_, 1);
v_isSharedCheck_1798_ = !lean_is_exclusive(v_a_1624_);
if (v_isSharedCheck_1798_ == 0)
{
v___x_1628_ = v_a_1624_;
v_isShared_1629_ = v_isSharedCheck_1798_;
goto v_resetjp_1627_;
}
else
{
lean_inc(v_snd_1626_);
lean_inc(v_fst_1625_);
lean_dec(v_a_1624_);
v___x_1628_ = lean_box(0);
v_isShared_1629_ = v_isSharedCheck_1798_;
goto v_resetjp_1627_;
}
v_resetjp_1627_:
{
lean_object* v___x_1630_; 
lean_inc(v___y_1580_);
lean_inc_ref(v___y_1579_);
lean_inc(v___y_1578_);
lean_inc_ref(v___y_1577_);
v___x_1630_ = lean_infer_type(v___x_1621_, v___y_1577_, v___y_1578_, v___y_1579_, v___y_1580_);
if (lean_obj_tag(v___x_1630_) == 0)
{
lean_object* v_a_1631_; lean_object* v___x_1632_; uint8_t v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; 
v_a_1631_ = lean_ctor_get(v___x_1630_, 0);
lean_inc(v_a_1631_);
lean_dec_ref_known(v___x_1630_, 1);
v___x_1632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1632_, 0, v_a_1631_);
v___x_1633_ = 0;
v___x_1634_ = lean_box(0);
v___x_1635_ = l_Lean_Meta_mkFreshExprMVar(v___x_1632_, v___x_1633_, v___x_1634_, v___y_1577_, v___y_1578_, v___y_1579_, v___y_1580_);
if (lean_obj_tag(v___x_1635_) == 0)
{
lean_object* v_a_1636_; lean_object* v___y_1638_; lean_object* v___y_1639_; lean_object* v___y_1640_; lean_object* v___y_1641_; lean_object* v___y_1642_; lean_object* v___y_1643_; lean_object* v_a_1644_; lean_object* v___y_1692_; lean_object* v_eqProof_1693_; lean_object* v___y_1694_; lean_object* v___y_1695_; lean_object* v___y_1696_; lean_object* v___y_1697_; lean_object* v___x_1725_; lean_object* v___y_1727_; lean_object* v___x_1780_; 
v_a_1636_ = lean_ctor_get(v___x_1635_, 0);
lean_inc(v_a_1636_);
lean_dec_ref_known(v___x_1635_, 1);
v___x_1725_ = l_Lean_Expr_getAppFn(v_fst_1625_);
v___x_1780_ = l_Lean_Expr_constName_x3f(v___x_1725_);
if (lean_obj_tag(v___x_1780_) == 0)
{
v___y_1727_ = v___x_1634_;
goto v___jp_1726_;
}
else
{
lean_object* v_val_1781_; 
v_val_1781_ = lean_ctor_get(v___x_1780_, 0);
lean_inc(v_val_1781_);
lean_dec_ref_known(v___x_1780_, 1);
v___y_1727_ = v_val_1781_;
goto v___jp_1726_;
}
v___jp_1637_:
{
lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; 
v___x_1645_ = lean_unsigned_to_nat(1u);
v___x_1646_ = lean_mk_empty_array_with_capacity(v___x_1645_);
lean_inc_ref(v___x_1646_);
v___x_1647_ = lean_array_push(v___x_1646_, v_a_1636_);
v___x_1648_ = l_Lean_Meta_mkAppM(v___y_1640_, v___x_1647_, v___y_1639_, v___y_1642_, v___y_1638_, v___y_1641_);
if (lean_obj_tag(v___x_1648_) == 0)
{
lean_object* v_a_1649_; lean_object* v___x_1650_; 
v_a_1649_ = lean_ctor_get(v___x_1648_, 0);
lean_inc(v_a_1649_);
lean_dec_ref_known(v___x_1648_, 1);
v___x_1650_ = l_Lean_Meta_mkCongrArg(v_a_1649_, v___y_1643_, v___y_1639_, v___y_1642_, v___y_1638_, v___y_1641_);
if (lean_obj_tag(v___x_1650_) == 0)
{
lean_object* v_a_1651_; lean_object* v___x_1652_; 
v_a_1651_ = lean_ctor_get(v___x_1650_, 0);
lean_inc(v_a_1651_);
lean_dec_ref_known(v___x_1650_, 1);
v___x_1652_ = l_Lean_Meta_mkEqSymm(v_a_1651_, v___y_1639_, v___y_1642_, v___y_1638_, v___y_1641_);
if (lean_obj_tag(v___x_1652_) == 0)
{
lean_object* v_a_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; 
v_a_1653_ = lean_ctor_get(v___x_1652_, 0);
lean_inc(v_a_1653_);
lean_dec_ref_known(v___x_1652_, 1);
v___x_1654_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__2___closed__2));
v___x_1655_ = lean_array_push(v___x_1646_, v_a_1653_);
v___x_1656_ = l_Lean_Meta_mkAppM(v___x_1654_, v___x_1655_, v___y_1639_, v___y_1642_, v___y_1638_, v___y_1641_);
if (lean_obj_tag(v___x_1656_) == 0)
{
lean_object* v_a_1657_; lean_object* v___x_1658_; 
v_a_1657_ = lean_ctor_get(v___x_1656_, 0);
lean_inc(v_a_1657_);
lean_dec_ref_known(v___x_1656_, 1);
v___x_1658_ = l_Lean_Expr_app___override(v_a_1657_, v_a_1644_);
v_prf_1583_ = v___x_1658_;
v___y_1584_ = v___y_1639_;
v___y_1585_ = v___y_1642_;
v___y_1586_ = v___y_1638_;
v___y_1587_ = v___y_1641_;
goto v___jp_1582_;
}
else
{
lean_object* v_a_1659_; lean_object* v___x_1661_; uint8_t v_isShared_1662_; uint8_t v_isSharedCheck_1666_; 
lean_dec_ref(v_a_1644_);
v_a_1659_ = lean_ctor_get(v___x_1656_, 0);
v_isSharedCheck_1666_ = !lean_is_exclusive(v___x_1656_);
if (v_isSharedCheck_1666_ == 0)
{
v___x_1661_ = v___x_1656_;
v_isShared_1662_ = v_isSharedCheck_1666_;
goto v_resetjp_1660_;
}
else
{
lean_inc(v_a_1659_);
lean_dec(v___x_1656_);
v___x_1661_ = lean_box(0);
v_isShared_1662_ = v_isSharedCheck_1666_;
goto v_resetjp_1660_;
}
v_resetjp_1660_:
{
lean_object* v___x_1664_; 
if (v_isShared_1662_ == 0)
{
v___x_1664_ = v___x_1661_;
goto v_reusejp_1663_;
}
else
{
lean_object* v_reuseFailAlloc_1665_; 
v_reuseFailAlloc_1665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1665_, 0, v_a_1659_);
v___x_1664_ = v_reuseFailAlloc_1665_;
goto v_reusejp_1663_;
}
v_reusejp_1663_:
{
return v___x_1664_;
}
}
}
}
else
{
lean_object* v_a_1667_; lean_object* v___x_1669_; uint8_t v_isShared_1670_; uint8_t v_isSharedCheck_1674_; 
lean_dec_ref(v___x_1646_);
lean_dec_ref(v_a_1644_);
v_a_1667_ = lean_ctor_get(v___x_1652_, 0);
v_isSharedCheck_1674_ = !lean_is_exclusive(v___x_1652_);
if (v_isSharedCheck_1674_ == 0)
{
v___x_1669_ = v___x_1652_;
v_isShared_1670_ = v_isSharedCheck_1674_;
goto v_resetjp_1668_;
}
else
{
lean_inc(v_a_1667_);
lean_dec(v___x_1652_);
v___x_1669_ = lean_box(0);
v_isShared_1670_ = v_isSharedCheck_1674_;
goto v_resetjp_1668_;
}
v_resetjp_1668_:
{
lean_object* v___x_1672_; 
if (v_isShared_1670_ == 0)
{
v___x_1672_ = v___x_1669_;
goto v_reusejp_1671_;
}
else
{
lean_object* v_reuseFailAlloc_1673_; 
v_reuseFailAlloc_1673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1673_, 0, v_a_1667_);
v___x_1672_ = v_reuseFailAlloc_1673_;
goto v_reusejp_1671_;
}
v_reusejp_1671_:
{
return v___x_1672_;
}
}
}
}
else
{
lean_object* v_a_1675_; lean_object* v___x_1677_; uint8_t v_isShared_1678_; uint8_t v_isSharedCheck_1682_; 
lean_dec_ref(v___x_1646_);
lean_dec_ref(v_a_1644_);
v_a_1675_ = lean_ctor_get(v___x_1650_, 0);
v_isSharedCheck_1682_ = !lean_is_exclusive(v___x_1650_);
if (v_isSharedCheck_1682_ == 0)
{
v___x_1677_ = v___x_1650_;
v_isShared_1678_ = v_isSharedCheck_1682_;
goto v_resetjp_1676_;
}
else
{
lean_inc(v_a_1675_);
lean_dec(v___x_1650_);
v___x_1677_ = lean_box(0);
v_isShared_1678_ = v_isSharedCheck_1682_;
goto v_resetjp_1676_;
}
v_resetjp_1676_:
{
lean_object* v___x_1680_; 
if (v_isShared_1678_ == 0)
{
v___x_1680_ = v___x_1677_;
goto v_reusejp_1679_;
}
else
{
lean_object* v_reuseFailAlloc_1681_; 
v_reuseFailAlloc_1681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1681_, 0, v_a_1675_);
v___x_1680_ = v_reuseFailAlloc_1681_;
goto v_reusejp_1679_;
}
v_reusejp_1679_:
{
return v___x_1680_;
}
}
}
}
else
{
lean_object* v_a_1683_; lean_object* v___x_1685_; uint8_t v_isShared_1686_; uint8_t v_isSharedCheck_1690_; 
lean_dec_ref(v___x_1646_);
lean_dec_ref(v_a_1644_);
lean_dec_ref(v___y_1643_);
v_a_1683_ = lean_ctor_get(v___x_1648_, 0);
v_isSharedCheck_1690_ = !lean_is_exclusive(v___x_1648_);
if (v_isSharedCheck_1690_ == 0)
{
v___x_1685_ = v___x_1648_;
v_isShared_1686_ = v_isSharedCheck_1690_;
goto v_resetjp_1684_;
}
else
{
lean_inc(v_a_1683_);
lean_dec(v___x_1648_);
v___x_1685_ = lean_box(0);
v_isShared_1686_ = v_isSharedCheck_1690_;
goto v_resetjp_1684_;
}
v_resetjp_1684_:
{
lean_object* v___x_1688_; 
if (v_isShared_1686_ == 0)
{
v___x_1688_ = v___x_1685_;
goto v_reusejp_1687_;
}
else
{
lean_object* v_reuseFailAlloc_1689_; 
v_reuseFailAlloc_1689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1689_, 0, v_a_1683_);
v___x_1688_ = v_reuseFailAlloc_1689_;
goto v_reusejp_1687_;
}
v_reusejp_1687_:
{
return v___x_1688_;
}
}
}
}
v___jp_1691_:
{
lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; 
v___x_1698_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__2));
v___x_1699_ = lean_unsigned_to_nat(2u);
v___x_1700_ = lean_mk_empty_array_with_capacity(v___x_1699_);
lean_inc(v_a_1636_);
v___x_1701_ = lean_array_push(v___x_1700_, v_a_1636_);
v___x_1702_ = lean_array_push(v___x_1701_, v_fst_1625_);
v___x_1703_ = l_Lean_Meta_mkAppM(v___x_1698_, v___x_1702_, v___y_1694_, v___y_1695_, v___y_1696_, v___y_1697_);
if (lean_obj_tag(v___x_1703_) == 0)
{
if (lean_obj_tag(v___y_1692_) == 0)
{
lean_object* v_a_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; 
v_a_1704_ = lean_ctor_get(v___x_1703_, 0);
lean_inc(v_a_1704_);
lean_dec_ref_known(v___x_1703_, 1);
v___x_1705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1705_, 0, v_a_1704_);
v___x_1706_ = l_Lean_Meta_mkFreshExprMVar(v___x_1705_, v___x_1633_, v___x_1634_, v___y_1694_, v___y_1695_, v___y_1696_, v___y_1697_);
if (lean_obj_tag(v___x_1706_) == 0)
{
lean_object* v_a_1707_; 
v_a_1707_ = lean_ctor_get(v___x_1706_, 0);
lean_inc(v_a_1707_);
lean_dec_ref_known(v___x_1706_, 1);
v___y_1638_ = v___y_1696_;
v___y_1639_ = v___y_1694_;
v___y_1640_ = v___x_1698_;
v___y_1641_ = v___y_1697_;
v___y_1642_ = v___y_1695_;
v___y_1643_ = v_eqProof_1693_;
v_a_1644_ = v_a_1707_;
goto v___jp_1637_;
}
else
{
lean_object* v_a_1708_; lean_object* v___x_1710_; uint8_t v_isShared_1711_; uint8_t v_isSharedCheck_1715_; 
lean_dec_ref(v_eqProof_1693_);
lean_dec(v_a_1636_);
v_a_1708_ = lean_ctor_get(v___x_1706_, 0);
v_isSharedCheck_1715_ = !lean_is_exclusive(v___x_1706_);
if (v_isSharedCheck_1715_ == 0)
{
v___x_1710_ = v___x_1706_;
v_isShared_1711_ = v_isSharedCheck_1715_;
goto v_resetjp_1709_;
}
else
{
lean_inc(v_a_1708_);
lean_dec(v___x_1706_);
v___x_1710_ = lean_box(0);
v_isShared_1711_ = v_isSharedCheck_1715_;
goto v_resetjp_1709_;
}
v_resetjp_1709_:
{
lean_object* v___x_1713_; 
if (v_isShared_1711_ == 0)
{
v___x_1713_ = v___x_1710_;
goto v_reusejp_1712_;
}
else
{
lean_object* v_reuseFailAlloc_1714_; 
v_reuseFailAlloc_1714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1714_, 0, v_a_1708_);
v___x_1713_ = v_reuseFailAlloc_1714_;
goto v_reusejp_1712_;
}
v_reusejp_1712_:
{
return v___x_1713_;
}
}
}
}
else
{
lean_object* v_val_1716_; 
lean_dec_ref_known(v___x_1703_, 1);
v_val_1716_ = lean_ctor_get(v___y_1692_, 0);
lean_inc(v_val_1716_);
lean_dec_ref_known(v___y_1692_, 1);
v___y_1638_ = v___y_1696_;
v___y_1639_ = v___y_1694_;
v___y_1640_ = v___x_1698_;
v___y_1641_ = v___y_1697_;
v___y_1642_ = v___y_1695_;
v___y_1643_ = v_eqProof_1693_;
v_a_1644_ = v_val_1716_;
goto v___jp_1637_;
}
}
else
{
lean_object* v_a_1717_; lean_object* v___x_1719_; uint8_t v_isShared_1720_; uint8_t v_isSharedCheck_1724_; 
lean_dec_ref(v_eqProof_1693_);
lean_dec(v___y_1692_);
lean_dec(v_a_1636_);
v_a_1717_ = lean_ctor_get(v___x_1703_, 0);
v_isSharedCheck_1724_ = !lean_is_exclusive(v___x_1703_);
if (v_isSharedCheck_1724_ == 0)
{
v___x_1719_ = v___x_1703_;
v_isShared_1720_ = v_isSharedCheck_1724_;
goto v_resetjp_1718_;
}
else
{
lean_inc(v_a_1717_);
lean_dec(v___x_1703_);
v___x_1719_ = lean_box(0);
v_isShared_1720_ = v_isSharedCheck_1724_;
goto v_resetjp_1718_;
}
v_resetjp_1718_:
{
lean_object* v___x_1722_; 
if (v_isShared_1720_ == 0)
{
v___x_1722_ = v___x_1719_;
goto v_reusejp_1721_;
}
else
{
lean_object* v_reuseFailAlloc_1723_; 
v_reuseFailAlloc_1723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1723_, 0, v_a_1717_);
v___x_1722_ = v_reuseFailAlloc_1723_;
goto v_reusejp_1721_;
}
v_reusejp_1721_:
{
return v___x_1722_;
}
}
}
}
v___jp_1726_:
{
lean_object* v___x_1728_; 
v___x_1728_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__1___redArg(v_a_1571_, v___y_1727_);
lean_dec(v___y_1727_);
if (lean_obj_tag(v___x_1728_) == 0)
{
lean_dec_ref(v___x_1725_);
if (lean_obj_tag(v_snd_1626_) == 0)
{
lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1732_; 
lean_dec(v_a_1636_);
lean_dec(v_fst_1625_);
v___x_1729_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__2___closed__4, &l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__2___closed__4_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__2___closed__4);
v___x_1730_ = l_Lean_MessageData_ofName(v_head_1610_);
if (v_isShared_1629_ == 0)
{
lean_ctor_set_tag(v___x_1628_, 7);
lean_ctor_set(v___x_1628_, 1, v___x_1730_);
lean_ctor_set(v___x_1628_, 0, v___x_1729_);
v___x_1732_ = v___x_1628_;
goto v_reusejp_1731_;
}
else
{
lean_object* v_reuseFailAlloc_1744_; 
v_reuseFailAlloc_1744_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1744_, 0, v___x_1729_);
lean_ctor_set(v_reuseFailAlloc_1744_, 1, v___x_1730_);
v___x_1732_ = v_reuseFailAlloc_1744_;
goto v_reusejp_1731_;
}
v_reusejp_1731_:
{
lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v_a_1736_; lean_object* v___x_1738_; uint8_t v_isShared_1739_; uint8_t v_isSharedCheck_1743_; 
v___x_1733_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__2___closed__6, &l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__2___closed__6_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__2___closed__6);
v___x_1734_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1734_, 0, v___x_1732_);
lean_ctor_set(v___x_1734_, 1, v___x_1733_);
v___x_1735_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_go_spec__0___redArg(v___x_1734_, v___y_1577_, v___y_1578_, v___y_1579_, v___y_1580_);
v_a_1736_ = lean_ctor_get(v___x_1735_, 0);
v_isSharedCheck_1743_ = !lean_is_exclusive(v___x_1735_);
if (v_isSharedCheck_1743_ == 0)
{
v___x_1738_ = v___x_1735_;
v_isShared_1739_ = v_isSharedCheck_1743_;
goto v_resetjp_1737_;
}
else
{
lean_inc(v_a_1736_);
lean_dec(v___x_1735_);
v___x_1738_ = lean_box(0);
v_isShared_1739_ = v_isSharedCheck_1743_;
goto v_resetjp_1737_;
}
v_resetjp_1737_:
{
lean_object* v___x_1741_; 
if (v_isShared_1739_ == 0)
{
v___x_1741_ = v___x_1738_;
goto v_reusejp_1740_;
}
else
{
lean_object* v_reuseFailAlloc_1742_; 
v_reuseFailAlloc_1742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1742_, 0, v_a_1736_);
v___x_1741_ = v_reuseFailAlloc_1742_;
goto v_reusejp_1740_;
}
v_reusejp_1740_:
{
return v___x_1741_;
}
}
}
}
else
{
lean_object* v_val_1745_; lean_object* v___x_1746_; 
lean_del_object(v___x_1628_);
lean_dec(v_head_1610_);
v_val_1745_ = lean_ctor_get(v_snd_1626_, 0);
lean_inc(v_val_1745_);
lean_dec_ref_known(v_snd_1626_, 1);
v___x_1746_ = lean_box(0);
v___y_1692_ = v___x_1746_;
v_eqProof_1693_ = v_val_1745_;
v___y_1694_ = v___y_1577_;
v___y_1695_ = v___y_1578_;
v___y_1696_ = v___y_1579_;
v___y_1697_ = v___y_1580_;
goto v___jp_1691_;
}
}
else
{
lean_object* v_val_1747_; lean_object* v_fst_1748_; lean_object* v_snd_1749_; lean_object* v_dummy_1750_; lean_object* v_nargs_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; 
lean_del_object(v___x_1628_);
lean_dec(v_head_1610_);
v_val_1747_ = lean_ctor_get(v___x_1728_, 0);
lean_inc(v_val_1747_);
lean_dec_ref_known(v___x_1728_, 1);
v_fst_1748_ = lean_ctor_get(v_val_1747_, 0);
lean_inc(v_fst_1748_);
v_snd_1749_ = lean_ctor_get(v_val_1747_, 1);
lean_inc_n(v_snd_1749_, 2);
lean_dec(v_val_1747_);
v_dummy_1750_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_projectsRewritableOperand___closed__0, &l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_projectsRewritableOperand___closed__0_once, _init_l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_projectsRewritableOperand___closed__0);
v_nargs_1751_ = l_Lean_Expr_getAppNumArgs(v_fst_1625_);
lean_inc(v_nargs_1751_);
v___x_1752_ = lean_mk_array(v_nargs_1751_, v_dummy_1750_);
v___x_1753_ = lean_unsigned_to_nat(1u);
v___x_1754_ = lean_nat_sub(v_nargs_1751_, v___x_1753_);
lean_dec(v_nargs_1751_);
lean_inc(v_fst_1625_);
v___x_1755_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_fst_1625_, v___x_1752_, v___x_1754_);
v___x_1756_ = l_Array_extract___redArg(v___x_1755_, v___x_1612_, v_snd_1749_);
v___x_1757_ = l_Lean_mkAppN(v___x_1725_, v___x_1756_);
lean_dec_ref(v___x_1756_);
v___x_1758_ = lean_array_get_size(v___x_1755_);
v___x_1759_ = l_Array_extract___redArg(v___x_1755_, v_snd_1749_, v___x_1758_);
lean_dec_ref(v___x_1755_);
v___x_1760_ = lean_array_to_list(v___x_1759_);
lean_inc(v_a_1636_);
v___x_1761_ = l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply(v_fst_1748_, v___x_1757_, v_a_1636_, v___x_1760_, v___y_1577_, v___y_1578_, v___y_1579_, v___y_1580_);
if (lean_obj_tag(v___x_1761_) == 0)
{
if (lean_obj_tag(v_snd_1626_) == 0)
{
lean_object* v_a_1762_; 
lean_dec(v_a_1636_);
lean_dec(v_fst_1625_);
v_a_1762_ = lean_ctor_get(v___x_1761_, 0);
lean_inc(v_a_1762_);
lean_dec_ref_known(v___x_1761_, 1);
v_prf_1583_ = v_a_1762_;
v___y_1584_ = v___y_1577_;
v___y_1585_ = v___y_1578_;
v___y_1586_ = v___y_1579_;
v___y_1587_ = v___y_1580_;
goto v___jp_1582_;
}
else
{
lean_object* v_a_1763_; lean_object* v_val_1764_; lean_object* v___x_1766_; uint8_t v_isShared_1767_; uint8_t v_isSharedCheck_1771_; 
v_a_1763_ = lean_ctor_get(v___x_1761_, 0);
lean_inc(v_a_1763_);
lean_dec_ref_known(v___x_1761_, 1);
v_val_1764_ = lean_ctor_get(v_snd_1626_, 0);
v_isSharedCheck_1771_ = !lean_is_exclusive(v_snd_1626_);
if (v_isSharedCheck_1771_ == 0)
{
v___x_1766_ = v_snd_1626_;
v_isShared_1767_ = v_isSharedCheck_1771_;
goto v_resetjp_1765_;
}
else
{
lean_inc(v_val_1764_);
lean_dec(v_snd_1626_);
v___x_1766_ = lean_box(0);
v_isShared_1767_ = v_isSharedCheck_1771_;
goto v_resetjp_1765_;
}
v_resetjp_1765_:
{
lean_object* v___x_1769_; 
if (v_isShared_1767_ == 0)
{
lean_ctor_set(v___x_1766_, 0, v_a_1763_);
v___x_1769_ = v___x_1766_;
goto v_reusejp_1768_;
}
else
{
lean_object* v_reuseFailAlloc_1770_; 
v_reuseFailAlloc_1770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1770_, 0, v_a_1763_);
v___x_1769_ = v_reuseFailAlloc_1770_;
goto v_reusejp_1768_;
}
v_reusejp_1768_:
{
v___y_1692_ = v___x_1769_;
v_eqProof_1693_ = v_val_1764_;
v___y_1694_ = v___y_1577_;
v___y_1695_ = v___y_1578_;
v___y_1696_ = v___y_1579_;
v___y_1697_ = v___y_1580_;
goto v___jp_1691_;
}
}
}
}
else
{
lean_object* v_a_1772_; lean_object* v___x_1774_; uint8_t v_isShared_1775_; uint8_t v_isSharedCheck_1779_; 
lean_dec(v_a_1636_);
lean_dec(v_snd_1626_);
lean_dec(v_fst_1625_);
v_a_1772_ = lean_ctor_get(v___x_1761_, 0);
v_isSharedCheck_1779_ = !lean_is_exclusive(v___x_1761_);
if (v_isSharedCheck_1779_ == 0)
{
v___x_1774_ = v___x_1761_;
v_isShared_1775_ = v_isSharedCheck_1779_;
goto v_resetjp_1773_;
}
else
{
lean_inc(v_a_1772_);
lean_dec(v___x_1761_);
v___x_1774_ = lean_box(0);
v_isShared_1775_ = v_isSharedCheck_1779_;
goto v_resetjp_1773_;
}
v_resetjp_1773_:
{
lean_object* v___x_1777_; 
if (v_isShared_1775_ == 0)
{
v___x_1777_ = v___x_1774_;
goto v_reusejp_1776_;
}
else
{
lean_object* v_reuseFailAlloc_1778_; 
v_reuseFailAlloc_1778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1778_, 0, v_a_1772_);
v___x_1777_ = v_reuseFailAlloc_1778_;
goto v_reusejp_1776_;
}
v_reusejp_1776_:
{
return v___x_1777_;
}
}
}
}
}
}
else
{
lean_object* v_a_1782_; lean_object* v___x_1784_; uint8_t v_isShared_1785_; uint8_t v_isSharedCheck_1789_; 
lean_del_object(v___x_1628_);
lean_dec(v_snd_1626_);
lean_dec(v_fst_1625_);
lean_dec(v_head_1610_);
v_a_1782_ = lean_ctor_get(v___x_1635_, 0);
v_isSharedCheck_1789_ = !lean_is_exclusive(v___x_1635_);
if (v_isSharedCheck_1789_ == 0)
{
v___x_1784_ = v___x_1635_;
v_isShared_1785_ = v_isSharedCheck_1789_;
goto v_resetjp_1783_;
}
else
{
lean_inc(v_a_1782_);
lean_dec(v___x_1635_);
v___x_1784_ = lean_box(0);
v_isShared_1785_ = v_isSharedCheck_1789_;
goto v_resetjp_1783_;
}
v_resetjp_1783_:
{
lean_object* v___x_1787_; 
if (v_isShared_1785_ == 0)
{
v___x_1787_ = v___x_1784_;
goto v_reusejp_1786_;
}
else
{
lean_object* v_reuseFailAlloc_1788_; 
v_reuseFailAlloc_1788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1788_, 0, v_a_1782_);
v___x_1787_ = v_reuseFailAlloc_1788_;
goto v_reusejp_1786_;
}
v_reusejp_1786_:
{
return v___x_1787_;
}
}
}
}
else
{
lean_object* v_a_1790_; lean_object* v___x_1792_; uint8_t v_isShared_1793_; uint8_t v_isSharedCheck_1797_; 
lean_del_object(v___x_1628_);
lean_dec(v_snd_1626_);
lean_dec(v_fst_1625_);
lean_dec(v_head_1610_);
v_a_1790_ = lean_ctor_get(v___x_1630_, 0);
v_isSharedCheck_1797_ = !lean_is_exclusive(v___x_1630_);
if (v_isSharedCheck_1797_ == 0)
{
v___x_1792_ = v___x_1630_;
v_isShared_1793_ = v_isSharedCheck_1797_;
goto v_resetjp_1791_;
}
else
{
lean_inc(v_a_1790_);
lean_dec(v___x_1630_);
v___x_1792_ = lean_box(0);
v_isShared_1793_ = v_isSharedCheck_1797_;
goto v_resetjp_1791_;
}
v_resetjp_1791_:
{
lean_object* v___x_1795_; 
if (v_isShared_1793_ == 0)
{
v___x_1795_ = v___x_1792_;
goto v_reusejp_1794_;
}
else
{
lean_object* v_reuseFailAlloc_1796_; 
v_reuseFailAlloc_1796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1796_, 0, v_a_1790_);
v___x_1795_ = v_reuseFailAlloc_1796_;
goto v_reusejp_1794_;
}
v_reusejp_1794_:
{
return v___x_1795_;
}
}
}
}
}
else
{
lean_object* v_a_1799_; lean_object* v___x_1801_; uint8_t v_isShared_1802_; uint8_t v_isSharedCheck_1806_; 
lean_dec_ref(v___x_1621_);
lean_dec(v_head_1610_);
v_a_1799_ = lean_ctor_get(v___x_1623_, 0);
v_isSharedCheck_1806_ = !lean_is_exclusive(v___x_1623_);
if (v_isSharedCheck_1806_ == 0)
{
v___x_1801_ = v___x_1623_;
v_isShared_1802_ = v_isSharedCheck_1806_;
goto v_resetjp_1800_;
}
else
{
lean_inc(v_a_1799_);
lean_dec(v___x_1623_);
v___x_1801_ = lean_box(0);
v_isShared_1802_ = v_isSharedCheck_1806_;
goto v_resetjp_1800_;
}
v_resetjp_1800_:
{
lean_object* v___x_1804_; 
if (v_isShared_1802_ == 0)
{
v___x_1804_ = v___x_1801_;
goto v_reusejp_1803_;
}
else
{
lean_object* v_reuseFailAlloc_1805_; 
v_reuseFailAlloc_1805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1805_, 0, v_a_1799_);
v___x_1804_ = v_reuseFailAlloc_1805_;
goto v_reusejp_1803_;
}
v_reusejp_1803_:
{
return v___x_1804_;
}
}
}
}
else
{
lean_object* v_a_1807_; lean_object* v___x_1809_; uint8_t v_isShared_1810_; uint8_t v_isSharedCheck_1814_; 
lean_dec(v_numConst_1611_);
lean_dec(v_head_1610_);
lean_dec_ref(v_x_1573_);
lean_dec_ref(v_x_1572_);
v_a_1807_ = lean_ctor_get(v___x_1617_, 0);
v_isSharedCheck_1814_ = !lean_is_exclusive(v___x_1617_);
if (v_isSharedCheck_1814_ == 0)
{
v___x_1809_ = v___x_1617_;
v_isShared_1810_ = v_isSharedCheck_1814_;
goto v_resetjp_1808_;
}
else
{
lean_inc(v_a_1807_);
lean_dec(v___x_1617_);
v___x_1809_ = lean_box(0);
v_isShared_1810_ = v_isSharedCheck_1814_;
goto v_resetjp_1808_;
}
v_resetjp_1808_:
{
lean_object* v___x_1812_; 
if (v_isShared_1810_ == 0)
{
v___x_1812_ = v___x_1809_;
goto v_reusejp_1811_;
}
else
{
lean_object* v_reuseFailAlloc_1813_; 
v_reuseFailAlloc_1813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1813_, 0, v_a_1807_);
v___x_1812_ = v_reuseFailAlloc_1813_;
goto v_reusejp_1811_;
}
v_reusejp_1811_:
{
return v___x_1812_;
}
}
}
}
v___jp_1582_:
{
uint8_t v___x_1588_; lean_object* v___x_1589_; 
v___x_1588_ = 1;
v___x_1589_ = l_Lean_Meta_abstractMVars(v_prf_1583_, v___x_1588_, v___y_1584_, v___y_1585_, v___y_1586_, v___y_1587_);
if (lean_obj_tag(v___x_1589_) == 0)
{
lean_object* v_a_1590_; lean_object* v_paramNames_1591_; lean_object* v_expr_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; 
v_a_1590_ = lean_ctor_get(v___x_1589_, 0);
lean_inc(v_a_1590_);
lean_dec_ref_known(v___x_1589_, 1);
v_paramNames_1591_ = lean_ctor_get(v_a_1590_, 0);
lean_inc_ref(v_paramNames_1591_);
v_expr_1592_ = lean_ctor_get(v_a_1590_, 2);
lean_inc_ref(v_expr_1592_);
lean_dec(v_a_1590_);
v___x_1593_ = lean_array_to_list(v_paramNames_1591_);
v___x_1594_ = lean_box(0);
v___x_1595_ = l_Lean_Meta_Sym_mkBackwardRuleFromExpr(v_expr_1592_, v___x_1593_, v___x_1594_, v___y_1584_, v___y_1585_, v___y_1586_, v___y_1587_);
return v___x_1595_;
}
else
{
lean_object* v_a_1596_; lean_object* v___x_1598_; uint8_t v_isShared_1599_; uint8_t v_isSharedCheck_1603_; 
v_a_1596_ = lean_ctor_get(v___x_1589_, 0);
v_isSharedCheck_1603_ = !lean_is_exclusive(v___x_1589_);
if (v_isSharedCheck_1603_ == 0)
{
v___x_1598_ = v___x_1589_;
v_isShared_1599_ = v_isSharedCheck_1603_;
goto v_resetjp_1597_;
}
else
{
lean_inc(v_a_1596_);
lean_dec(v___x_1589_);
v___x_1598_ = lean_box(0);
v_isShared_1599_ = v_isSharedCheck_1603_;
goto v_resetjp_1597_;
}
v_resetjp_1597_:
{
lean_object* v___x_1601_; 
if (v_isShared_1599_ == 0)
{
v___x_1601_ = v___x_1598_;
goto v_reusejp_1600_;
}
else
{
lean_object* v_reuseFailAlloc_1602_; 
v_reuseFailAlloc_1602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1602_, 0, v_a_1596_);
v___x_1601_ = v_reuseFailAlloc_1602_;
goto v_reusejp_1600_;
}
v_reusejp_1600_:
{
return v___x_1601_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__2___boxed(lean_object* v_op_1815_, lean_object* v___y_1816_, lean_object* v_a_1817_, lean_object* v_x_1818_, lean_object* v_x_1819_, lean_object* v_x_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_){
_start:
{
lean_object* v_res_1828_; 
v_res_1828_ = l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__2(v_op_1815_, v___y_1816_, v_a_1817_, v_x_1818_, v_x_1819_, v_x_1820_, v___y_1821_, v___y_1822_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_);
lean_dec(v___y_1826_);
lean_dec_ref(v___y_1825_);
lean_dec(v___y_1824_);
lean_dec_ref(v___y_1823_);
lean_dec(v___y_1822_);
lean_dec_ref(v___y_1821_);
lean_dec_ref(v_a_1817_);
lean_dec_ref(v___y_1816_);
return v_res_1828_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__4(lean_object* v_as_1829_, size_t v_i_1830_, size_t v_stop_1831_, lean_object* v_b_1832_){
_start:
{
uint8_t v___x_1833_; 
v___x_1833_ = lean_usize_dec_eq(v_i_1830_, v_stop_1831_);
if (v___x_1833_ == 0)
{
lean_object* v___x_1834_; lean_object* v_rewrites_1835_; lean_object* v___x_1836_; size_t v___x_1837_; size_t v___x_1838_; 
v___x_1834_ = lean_array_uget_borrowed(v_as_1829_, v_i_1830_);
v_rewrites_1835_ = lean_ctor_get(v___x_1834_, 2);
v___x_1836_ = l_Array_append___redArg(v_b_1832_, v_rewrites_1835_);
v___x_1837_ = ((size_t)1ULL);
v___x_1838_ = lean_usize_add(v_i_1830_, v___x_1837_);
v_i_1830_ = v___x_1838_;
v_b_1832_ = v___x_1836_;
goto _start;
}
else
{
return v_b_1832_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__4___boxed(lean_object* v_as_1840_, lean_object* v_i_1841_, lean_object* v_stop_1842_, lean_object* v_b_1843_){
_start:
{
size_t v_i_boxed_1844_; size_t v_stop_boxed_1845_; lean_object* v_res_1846_; 
v_i_boxed_1844_ = lean_unbox_usize(v_i_1841_);
lean_dec(v_i_1841_);
v_stop_boxed_1845_ = lean_unbox_usize(v_stop_1842_);
lean_dec(v_stop_1842_);
v_res_1846_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__4(v_as_1840_, v_i_boxed_1844_, v_stop_boxed_1845_, v_b_1843_);
lean_dec_ref(v_as_1840_);
return v_res_1846_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__3(lean_object* v_as_1849_, size_t v_i_1850_, size_t v_stop_1851_, lean_object* v_b_1852_){
_start:
{
lean_object* v___y_1854_; uint8_t v___x_1858_; 
v___x_1858_ = lean_usize_dec_eq(v_i_1850_, v_stop_1851_);
if (v___x_1858_ == 0)
{
lean_object* v___x_1859_; lean_object* v_terminal_x3f_1860_; 
v___x_1859_ = lean_array_uget_borrowed(v_as_1849_, v_i_1850_);
v_terminal_x3f_1860_ = lean_ctor_get(v___x_1859_, 3);
if (lean_obj_tag(v_terminal_x3f_1860_) == 0)
{
lean_object* v___x_1861_; lean_object* v___x_1862_; 
v___x_1861_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__3___closed__0));
v___x_1862_ = l_Array_append___redArg(v_b_1852_, v___x_1861_);
v___y_1854_ = v___x_1862_;
goto v___jp_1853_;
}
else
{
lean_object* v_val_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; 
v_val_1863_ = lean_ctor_get(v_terminal_x3f_1860_, 0);
v___x_1864_ = lean_unsigned_to_nat(1u);
v___x_1865_ = lean_mk_empty_array_with_capacity(v___x_1864_);
lean_inc(v_val_1863_);
v___x_1866_ = lean_array_push(v___x_1865_, v_val_1863_);
v___x_1867_ = l_Array_append___redArg(v_b_1852_, v___x_1866_);
lean_dec_ref(v___x_1866_);
v___y_1854_ = v___x_1867_;
goto v___jp_1853_;
}
}
else
{
return v_b_1852_;
}
v___jp_1853_:
{
size_t v___x_1855_; size_t v___x_1856_; 
v___x_1855_ = ((size_t)1ULL);
v___x_1856_ = lean_usize_add(v_i_1850_, v___x_1855_);
v_i_1850_ = v___x_1856_;
v_b_1852_ = v___y_1854_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__3___boxed(lean_object* v_as_1868_, lean_object* v_i_1869_, lean_object* v_stop_1870_, lean_object* v_b_1871_){
_start:
{
size_t v_i_boxed_1872_; size_t v_stop_boxed_1873_; lean_object* v_res_1874_; 
v_i_boxed_1872_ = lean_unbox_usize(v_i_1869_);
lean_dec(v_i_1869_);
v_stop_boxed_1873_ = lean_unbox_usize(v_stop_1870_);
lean_dec(v_stop_1870_);
v_res_1874_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__3(v_as_1868_, v_i_boxed_1872_, v_stop_boxed_1873_, v_b_1871_);
lean_dec_ref(v_as_1868_);
return v_res_1874_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_mkLatticeOpRule___closed__0(void){
_start:
{
lean_object* v___x_1875_; size_t v___x_1876_; size_t v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; 
v___x_1875_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__3___closed__0));
v___x_1876_ = lean_usize_once(&l_Lean_Elab_Tactic_VCGen_latticeOps___closed__5, &l_Lean_Elab_Tactic_VCGen_latticeOps___closed__5_once, _init_l_Lean_Elab_Tactic_VCGen_latticeOps___closed__5);
v___x_1877_ = ((size_t)0ULL);
v___x_1878_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_builtinLatticeOps));
v___x_1879_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__3(v___x_1878_, v___x_1877_, v___x_1876_, v___x_1875_);
return v___x_1879_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_mkLatticeOpRule(lean_object* v_rhs_1880_, lean_object* v_op_1881_, lean_object* v_a_1882_, lean_object* v_a_1883_, lean_object* v_a_1884_, lean_object* v_a_1885_, lean_object* v_a_1886_, lean_object* v_a_1887_){
_start:
{
lean_object* v___y_1890_; lean_object* v___y_1891_; lean_object* v___y_1892_; lean_object* v_rewrites_1910_; lean_object* v_terminal_x3f_1911_; lean_object* v___x_1912_; lean_object* v___y_1914_; lean_object* v___y_1915_; lean_object* v___y_1922_; uint8_t v___x_1928_; 
v_rewrites_1910_ = lean_ctor_get(v_op_1881_, 2);
v_terminal_x3f_1911_ = lean_ctor_get(v_op_1881_, 3);
v___x_1912_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_builtinLatticeOps));
v___x_1928_ = lean_uint8_once(&l_Lean_Elab_Tactic_VCGen_latticeOps___closed__3, &l_Lean_Elab_Tactic_VCGen_latticeOps___closed__3_once, _init_l_Lean_Elab_Tactic_VCGen_latticeOps___closed__3);
if (v___x_1928_ == 0)
{
lean_inc_ref(v_rewrites_1910_);
v___y_1922_ = v_rewrites_1910_;
goto v___jp_1921_;
}
else
{
uint8_t v___x_1929_; 
v___x_1929_ = lean_uint8_once(&l_Lean_Elab_Tactic_VCGen_latticeOps___closed__4, &l_Lean_Elab_Tactic_VCGen_latticeOps___closed__4_once, _init_l_Lean_Elab_Tactic_VCGen_latticeOps___closed__4);
if (v___x_1929_ == 0)
{
if (v___x_1928_ == 0)
{
lean_inc_ref(v_rewrites_1910_);
v___y_1922_ = v_rewrites_1910_;
goto v___jp_1921_;
}
else
{
size_t v___x_1930_; size_t v___x_1931_; lean_object* v___x_1932_; 
v___x_1930_ = ((size_t)0ULL);
v___x_1931_ = lean_usize_once(&l_Lean_Elab_Tactic_VCGen_latticeOps___closed__5, &l_Lean_Elab_Tactic_VCGen_latticeOps___closed__5_once, _init_l_Lean_Elab_Tactic_VCGen_latticeOps___closed__5);
lean_inc_ref(v_rewrites_1910_);
v___x_1932_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__4(v___x_1912_, v___x_1930_, v___x_1931_, v_rewrites_1910_);
v___y_1922_ = v___x_1932_;
goto v___jp_1921_;
}
}
else
{
size_t v___x_1933_; size_t v___x_1934_; lean_object* v___x_1935_; 
v___x_1933_ = ((size_t)0ULL);
v___x_1934_ = lean_usize_once(&l_Lean_Elab_Tactic_VCGen_latticeOps___closed__5, &l_Lean_Elab_Tactic_VCGen_latticeOps___closed__5_once, _init_l_Lean_Elab_Tactic_VCGen_latticeOps___closed__5);
lean_inc_ref(v_rewrites_1910_);
v___x_1935_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__4(v___x_1912_, v___x_1933_, v___x_1934_, v_rewrites_1910_);
v___y_1922_ = v___x_1935_;
goto v___jp_1921_;
}
}
v___jp_1889_:
{
lean_object* v___x_1893_; lean_object* v___x_1894_; 
lean_inc_ref(v___y_1890_);
v___x_1893_ = l_Array_append___redArg(v___y_1890_, v___y_1892_);
lean_dec_ref(v___y_1892_);
v___x_1894_ = l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals(v___x_1893_, v_a_1884_, v_a_1885_, v_a_1886_, v_a_1887_);
lean_dec_ref(v___x_1893_);
if (lean_obj_tag(v___x_1894_) == 0)
{
lean_object* v_a_1895_; lean_object* v_dummy_1896_; lean_object* v_nargs_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; 
v_a_1895_ = lean_ctor_get(v___x_1894_, 0);
lean_inc(v_a_1895_);
lean_dec_ref_known(v___x_1894_, 1);
v_dummy_1896_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_projectsRewritableOperand___closed__0, &l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_projectsRewritableOperand___closed__0_once, _init_l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_projectsRewritableOperand___closed__0);
v_nargs_1897_ = l_Lean_Expr_getAppNumArgs(v_rhs_1880_);
lean_inc(v_nargs_1897_);
v___x_1898_ = lean_mk_array(v_nargs_1897_, v_dummy_1896_);
v___x_1899_ = lean_unsigned_to_nat(1u);
v___x_1900_ = lean_nat_sub(v_nargs_1897_, v___x_1899_);
lean_dec(v_nargs_1897_);
v___x_1901_ = l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__2(v_op_1881_, v___y_1891_, v_a_1895_, v_rhs_1880_, v___x_1898_, v___x_1900_, v_a_1882_, v_a_1883_, v_a_1884_, v_a_1885_, v_a_1886_, v_a_1887_);
lean_dec(v_a_1895_);
lean_dec_ref(v___y_1891_);
return v___x_1901_;
}
else
{
lean_object* v_a_1902_; lean_object* v___x_1904_; uint8_t v_isShared_1905_; uint8_t v_isSharedCheck_1909_; 
lean_dec_ref(v___y_1891_);
lean_dec_ref(v_op_1881_);
lean_dec_ref(v_rhs_1880_);
v_a_1902_ = lean_ctor_get(v___x_1894_, 0);
v_isSharedCheck_1909_ = !lean_is_exclusive(v___x_1894_);
if (v_isSharedCheck_1909_ == 0)
{
v___x_1904_ = v___x_1894_;
v_isShared_1905_ = v_isSharedCheck_1909_;
goto v_resetjp_1903_;
}
else
{
lean_inc(v_a_1902_);
lean_dec(v___x_1894_);
v___x_1904_ = lean_box(0);
v_isShared_1905_ = v_isSharedCheck_1909_;
goto v_resetjp_1903_;
}
v_resetjp_1903_:
{
lean_object* v___x_1907_; 
if (v_isShared_1905_ == 0)
{
v___x_1907_ = v___x_1904_;
goto v_reusejp_1906_;
}
else
{
lean_object* v_reuseFailAlloc_1908_; 
v_reuseFailAlloc_1908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1908_, 0, v_a_1902_);
v___x_1907_ = v_reuseFailAlloc_1908_;
goto v_reusejp_1906_;
}
v_reusejp_1906_:
{
return v___x_1907_;
}
}
}
}
v___jp_1913_:
{
if (lean_obj_tag(v_terminal_x3f_1911_) == 0)
{
lean_object* v___x_1916_; 
v___x_1916_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__3___closed__0));
v___y_1890_ = v___y_1915_;
v___y_1891_ = v___y_1914_;
v___y_1892_ = v___x_1916_;
goto v___jp_1889_;
}
else
{
lean_object* v_val_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; 
v_val_1917_ = lean_ctor_get(v_terminal_x3f_1911_, 0);
v___x_1918_ = lean_unsigned_to_nat(1u);
v___x_1919_ = lean_mk_empty_array_with_capacity(v___x_1918_);
lean_inc(v_val_1917_);
v___x_1920_ = lean_array_push(v___x_1919_, v_val_1917_);
v___y_1890_ = v___y_1915_;
v___y_1891_ = v___y_1914_;
v___y_1892_ = v___x_1920_;
goto v___jp_1889_;
}
}
v___jp_1921_:
{
lean_object* v___x_1923_; uint8_t v___x_1924_; 
v___x_1923_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__3___closed__0));
v___x_1924_ = lean_uint8_once(&l_Lean_Elab_Tactic_VCGen_latticeOps___closed__3, &l_Lean_Elab_Tactic_VCGen_latticeOps___closed__3_once, _init_l_Lean_Elab_Tactic_VCGen_latticeOps___closed__3);
if (v___x_1924_ == 0)
{
v___y_1914_ = v___y_1922_;
v___y_1915_ = v___x_1923_;
goto v___jp_1913_;
}
else
{
uint8_t v___x_1925_; 
v___x_1925_ = lean_uint8_once(&l_Lean_Elab_Tactic_VCGen_latticeOps___closed__4, &l_Lean_Elab_Tactic_VCGen_latticeOps___closed__4_once, _init_l_Lean_Elab_Tactic_VCGen_latticeOps___closed__4);
if (v___x_1925_ == 0)
{
if (v___x_1924_ == 0)
{
v___y_1914_ = v___y_1922_;
v___y_1915_ = v___x_1923_;
goto v___jp_1913_;
}
else
{
lean_object* v___x_1926_; 
v___x_1926_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_mkLatticeOpRule___closed__0, &l_Lean_Elab_Tactic_VCGen_mkLatticeOpRule___closed__0_once, _init_l_Lean_Elab_Tactic_VCGen_mkLatticeOpRule___closed__0);
v___y_1914_ = v___y_1922_;
v___y_1915_ = v___x_1926_;
goto v___jp_1913_;
}
}
else
{
lean_object* v___x_1927_; 
v___x_1927_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_mkLatticeOpRule___closed__0, &l_Lean_Elab_Tactic_VCGen_mkLatticeOpRule___closed__0_once, _init_l_Lean_Elab_Tactic_VCGen_mkLatticeOpRule___closed__0);
v___y_1914_ = v___y_1922_;
v___y_1915_ = v___x_1927_;
goto v___jp_1913_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_mkLatticeOpRule___boxed(lean_object* v_rhs_1936_, lean_object* v_op_1937_, lean_object* v_a_1938_, lean_object* v_a_1939_, lean_object* v_a_1940_, lean_object* v_a_1941_, lean_object* v_a_1942_, lean_object* v_a_1943_, lean_object* v_a_1944_){
_start:
{
lean_object* v_res_1945_; 
v_res_1945_ = l_Lean_Elab_Tactic_VCGen_mkLatticeOpRule(v_rhs_1936_, v_op_1937_, v_a_1938_, v_a_1939_, v_a_1940_, v_a_1941_, v_a_1942_, v_a_1943_);
lean_dec(v_a_1943_);
lean_dec_ref(v_a_1942_);
lean_dec(v_a_1941_);
lean_dec_ref(v_a_1940_);
lean_dec(v_a_1939_);
lean_dec_ref(v_a_1938_);
return v_res_1945_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__0(size_t v_sz_1946_, size_t v_i_1947_, lean_object* v_bs_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_){
_start:
{
lean_object* v___x_1956_; 
v___x_1956_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__0___redArg(v_sz_1946_, v_i_1947_, v_bs_1948_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_);
return v___x_1956_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__0___boxed(lean_object* v_sz_1957_, lean_object* v_i_1958_, lean_object* v_bs_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_){
_start:
{
size_t v_sz_boxed_1967_; size_t v_i_boxed_1968_; lean_object* v_res_1969_; 
v_sz_boxed_1967_ = lean_unbox_usize(v_sz_1957_);
lean_dec(v_sz_1957_);
v_i_boxed_1968_ = lean_unbox_usize(v_i_1958_);
lean_dec(v_i_1958_);
v_res_1969_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__0(v_sz_boxed_1967_, v_i_boxed_1968_, v_bs_1959_, v___y_1960_, v___y_1961_, v___y_1962_, v___y_1963_, v___y_1964_, v___y_1965_);
lean_dec(v___y_1965_);
lean_dec_ref(v___y_1964_);
lean_dec(v___y_1963_);
lean_dec_ref(v___y_1962_);
lean_dec(v___y_1961_);
lean_dec_ref(v___y_1960_);
return v_res_1969_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__1(lean_object* v_00_u03b2_1970_, lean_object* v_m_1971_, lean_object* v_a_1972_){
_start:
{
lean_object* v___x_1973_; 
v___x_1973_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__1___redArg(v_m_1971_, v_a_1972_);
return v___x_1973_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__1___boxed(lean_object* v_00_u03b2_1974_, lean_object* v_m_1975_, lean_object* v_a_1976_){
_start:
{
lean_object* v_res_1977_; 
v_res_1977_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__1(v_00_u03b2_1974_, v_m_1975_, v_a_1976_);
lean_dec(v_a_1976_);
lean_dec_ref(v_m_1975_);
return v_res_1977_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__1_spec__1(lean_object* v_00_u03b2_1978_, lean_object* v_a_1979_, lean_object* v_x_1980_){
_start:
{
lean_object* v___x_1981_; 
v___x_1981_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__1_spec__1___redArg(v_a_1979_, v_x_1980_);
return v___x_1981_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__1_spec__1___boxed(lean_object* v_00_u03b2_1982_, lean_object* v_a_1983_, lean_object* v_x_1984_){
_start:
{
lean_object* v_res_1985_; 
v_res_1985_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__1_spec__1(v_00_u03b2_1982_, v_a_1983_, v_x_1984_);
lean_dec(v_x_1984_);
lean_dec(v_a_1983_);
return v_res_1985_;
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
