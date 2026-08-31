// Lean compiler output
// Module: Lean.Elab.Tactic.VCGen.LatticeOp
// Imports: public import Lean.Meta.Sym.Apply public import Std.Internal.Order.Heyting import Lean.Meta.Sym.Simp.Rewrite import Lean.Meta.AppBuilder import Lean.Meta.AbstractMVars
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
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_SimpM_run_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_mkEqTrans(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
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
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Expr_constName_x3f(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Meta_abstractMVars(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_mkBackwardRuleFromExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_extract___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_dischargeNone___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_Theorems_rewrite___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
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
static const lean_array_object l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__3_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "le_upperAdjoint"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__5_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__2_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__5_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__0_value),LEAN_SCALAR_PTR_LITERAL(184, 207, 242, 99, 37, 43, 114, 21)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__5_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__4_value),LEAN_SCALAR_PTR_LITERAL(28, 162, 178, 118, 193, 187, 169, 14)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__5_value)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__6_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__2_value),((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__3_value),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__6_value),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__0_value)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__7_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__7_value;
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
static lean_once_cell_t l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_projectsBotOrTop___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_projectsBotOrTop___closed__0;
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_projectsBotOrTop___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "bot"};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_projectsBotOrTop___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_projectsBotOrTop___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_projectsBotOrTop___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_projectsBotOrTop___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_projectsBotOrTop___closed__2_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__2_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_projectsBotOrTop___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_projectsBotOrTop___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_projectsBotOrTop___closed__1_value),LEAN_SCALAR_PTR_LITERAL(89, 51, 159, 172, 220, 225, 54, 137)}};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_projectsBotOrTop___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_projectsBotOrTop___closed__2_value;
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_projectsBotOrTop(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_projectsBotOrTop___boxed(lean_object*);
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
static const lean_array_object l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__4_value),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__6_value),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__8_value),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_top___closed__3_value)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__9 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__9_value;
static const lean_closure_object l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_projectsBotOrTop___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__10 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__10_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__2_value),((lean_object*)(((size_t)(3) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__9_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__10_value)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__11 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__11_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_fst = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__11_value;
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
static const lean_array_object l_Lean_Elab_Tactic_VCGen_LatticeOp_snd___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_snd___closed__3_value),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_snd___closed__5_value),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__8_value),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_top___closed__3_value)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_snd___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_snd___closed__6_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_snd___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_snd___closed__1_value),((lean_object*)(((size_t)(3) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_snd___closed__6_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__10_value)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_snd___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_snd___closed__7_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_snd = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_snd___closed__7_value;
static const lean_array_object l_Lean_Elab_Tactic_VCGen_builtinLatticeOps___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*8, .m_other = 0, .m_tag = 246}, .m_size = 8, .m_capacity = 8, .m_data = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__11_value),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_himp___closed__8_value),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_ofProp___closed__9_value),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_top___closed__8_value),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__7_value),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_iInf___closed__8_value),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__11_value),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_snd___closed__7_value)}};
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
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_projectsBotOrTop___closed__0(void){
_start:
{
lean_object* v___x_176_; lean_object* v_dummy_177_; 
v___x_176_ = lean_box(0);
v_dummy_177_ = l_Lean_Expr_sort___override(v___x_176_);
return v_dummy_177_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_projectsBotOrTop(lean_object* v_rhs_183_){
_start:
{
lean_object* v_dummy_184_; lean_object* v_nargs_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; uint8_t v___x_192_; 
v_dummy_184_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_projectsBotOrTop___closed__0, &l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_projectsBotOrTop___closed__0_once, _init_l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_projectsBotOrTop___closed__0);
v_nargs_185_ = l_Lean_Expr_getAppNumArgs(v_rhs_183_);
lean_inc(v_nargs_185_);
v___x_186_ = lean_mk_array(v_nargs_185_, v_dummy_184_);
v___x_187_ = lean_unsigned_to_nat(1u);
v___x_188_ = lean_nat_sub(v_nargs_185_, v___x_187_);
lean_dec(v_nargs_185_);
v___x_189_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_rhs_183_, v___x_186_, v___x_188_);
v___x_190_ = lean_unsigned_to_nat(2u);
v___x_191_ = lean_array_get_size(v___x_189_);
v___x_192_ = lean_nat_dec_lt(v___x_190_, v___x_191_);
if (v___x_192_ == 0)
{
lean_dec_ref(v___x_189_);
return v___x_192_;
}
else
{
lean_object* v___x_193_; lean_object* v___x_194_; uint8_t v___x_195_; 
v___x_193_ = lean_array_fget(v___x_189_, v___x_190_);
lean_dec_ref(v___x_189_);
v___x_194_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_projectsBotOrTop___closed__2));
v___x_195_ = l_Lean_Expr_isAppOf(v___x_193_, v___x_194_);
if (v___x_195_ == 0)
{
lean_object* v___x_196_; uint8_t v___x_197_; 
v___x_196_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_LatticeOp_top___closed__1));
v___x_197_ = l_Lean_Expr_isAppOf(v___x_193_, v___x_196_);
lean_dec(v___x_193_);
return v___x_197_;
}
else
{
lean_dec(v___x_193_);
return v___x_195_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_projectsBotOrTop___boxed(lean_object* v_rhs_198_){
_start:
{
uint8_t v_res_199_; lean_object* v_r_200_; 
v_res_199_ = l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_projectsBotOrTop(v_rhs_198_);
v_r_200_ = lean_box(v_res_199_);
return v_r_200_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0_spec__2___redArg(lean_object* v_a_293_, lean_object* v_b_294_, lean_object* v_x_295_){
_start:
{
if (lean_obj_tag(v_x_295_) == 0)
{
lean_dec(v_b_294_);
lean_dec(v_a_293_);
return v_x_295_;
}
else
{
lean_object* v_key_296_; lean_object* v_value_297_; lean_object* v_tail_298_; lean_object* v___x_300_; uint8_t v_isShared_301_; uint8_t v_isSharedCheck_310_; 
v_key_296_ = lean_ctor_get(v_x_295_, 0);
v_value_297_ = lean_ctor_get(v_x_295_, 1);
v_tail_298_ = lean_ctor_get(v_x_295_, 2);
v_isSharedCheck_310_ = !lean_is_exclusive(v_x_295_);
if (v_isSharedCheck_310_ == 0)
{
v___x_300_ = v_x_295_;
v_isShared_301_ = v_isSharedCheck_310_;
goto v_resetjp_299_;
}
else
{
lean_inc(v_tail_298_);
lean_inc(v_value_297_);
lean_inc(v_key_296_);
lean_dec(v_x_295_);
v___x_300_ = lean_box(0);
v_isShared_301_ = v_isSharedCheck_310_;
goto v_resetjp_299_;
}
v_resetjp_299_:
{
uint8_t v___x_302_; 
v___x_302_ = lean_name_eq(v_key_296_, v_a_293_);
if (v___x_302_ == 0)
{
lean_object* v___x_303_; lean_object* v___x_305_; 
v___x_303_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0_spec__2___redArg(v_a_293_, v_b_294_, v_tail_298_);
if (v_isShared_301_ == 0)
{
lean_ctor_set(v___x_300_, 2, v___x_303_);
v___x_305_ = v___x_300_;
goto v_reusejp_304_;
}
else
{
lean_object* v_reuseFailAlloc_306_; 
v_reuseFailAlloc_306_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_306_, 0, v_key_296_);
lean_ctor_set(v_reuseFailAlloc_306_, 1, v_value_297_);
lean_ctor_set(v_reuseFailAlloc_306_, 2, v___x_303_);
v___x_305_ = v_reuseFailAlloc_306_;
goto v_reusejp_304_;
}
v_reusejp_304_:
{
return v___x_305_;
}
}
else
{
lean_object* v___x_308_; 
lean_dec(v_value_297_);
lean_dec(v_key_296_);
if (v_isShared_301_ == 0)
{
lean_ctor_set(v___x_300_, 1, v_b_294_);
lean_ctor_set(v___x_300_, 0, v_a_293_);
v___x_308_ = v___x_300_;
goto v_reusejp_307_;
}
else
{
lean_object* v_reuseFailAlloc_309_; 
v_reuseFailAlloc_309_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_309_, 0, v_a_293_);
lean_ctor_set(v_reuseFailAlloc_309_, 1, v_b_294_);
lean_ctor_set(v_reuseFailAlloc_309_, 2, v_tail_298_);
v___x_308_ = v_reuseFailAlloc_309_;
goto v_reusejp_307_;
}
v_reusejp_307_:
{
return v___x_308_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0_spec__1_spec__2_spec__4___redArg(lean_object* v_x_311_, lean_object* v_x_312_){
_start:
{
if (lean_obj_tag(v_x_312_) == 0)
{
return v_x_311_;
}
else
{
lean_object* v_key_313_; lean_object* v_value_314_; lean_object* v_tail_315_; lean_object* v___x_317_; uint8_t v_isShared_318_; uint8_t v_isSharedCheck_341_; 
v_key_313_ = lean_ctor_get(v_x_312_, 0);
v_value_314_ = lean_ctor_get(v_x_312_, 1);
v_tail_315_ = lean_ctor_get(v_x_312_, 2);
v_isSharedCheck_341_ = !lean_is_exclusive(v_x_312_);
if (v_isSharedCheck_341_ == 0)
{
v___x_317_ = v_x_312_;
v_isShared_318_ = v_isSharedCheck_341_;
goto v_resetjp_316_;
}
else
{
lean_inc(v_tail_315_);
lean_inc(v_value_314_);
lean_inc(v_key_313_);
lean_dec(v_x_312_);
v___x_317_ = lean_box(0);
v_isShared_318_ = v_isSharedCheck_341_;
goto v_resetjp_316_;
}
v_resetjp_316_:
{
lean_object* v___x_319_; uint64_t v___y_321_; 
v___x_319_ = lean_array_get_size(v_x_311_);
if (lean_obj_tag(v_key_313_) == 0)
{
uint64_t v___x_339_; 
v___x_339_ = 1723ULL;
v___y_321_ = v___x_339_;
goto v___jp_320_;
}
else
{
uint64_t v_hash_340_; 
v_hash_340_ = lean_ctor_get_uint64(v_key_313_, sizeof(void*)*2);
v___y_321_ = v_hash_340_;
goto v___jp_320_;
}
v___jp_320_:
{
uint64_t v___x_322_; uint64_t v___x_323_; uint64_t v_fold_324_; uint64_t v___x_325_; uint64_t v___x_326_; uint64_t v___x_327_; size_t v___x_328_; size_t v___x_329_; size_t v___x_330_; size_t v___x_331_; size_t v___x_332_; lean_object* v___x_333_; lean_object* v___x_335_; 
v___x_322_ = 32ULL;
v___x_323_ = lean_uint64_shift_right(v___y_321_, v___x_322_);
v_fold_324_ = lean_uint64_xor(v___y_321_, v___x_323_);
v___x_325_ = 16ULL;
v___x_326_ = lean_uint64_shift_right(v_fold_324_, v___x_325_);
v___x_327_ = lean_uint64_xor(v_fold_324_, v___x_326_);
v___x_328_ = lean_uint64_to_usize(v___x_327_);
v___x_329_ = lean_usize_of_nat(v___x_319_);
v___x_330_ = ((size_t)1ULL);
v___x_331_ = lean_usize_sub(v___x_329_, v___x_330_);
v___x_332_ = lean_usize_land(v___x_328_, v___x_331_);
v___x_333_ = lean_array_uget_borrowed(v_x_311_, v___x_332_);
lean_inc(v___x_333_);
if (v_isShared_318_ == 0)
{
lean_ctor_set(v___x_317_, 2, v___x_333_);
v___x_335_ = v___x_317_;
goto v_reusejp_334_;
}
else
{
lean_object* v_reuseFailAlloc_338_; 
v_reuseFailAlloc_338_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_338_, 0, v_key_313_);
lean_ctor_set(v_reuseFailAlloc_338_, 1, v_value_314_);
lean_ctor_set(v_reuseFailAlloc_338_, 2, v___x_333_);
v___x_335_ = v_reuseFailAlloc_338_;
goto v_reusejp_334_;
}
v_reusejp_334_:
{
lean_object* v___x_336_; 
v___x_336_ = lean_array_uset(v_x_311_, v___x_332_, v___x_335_);
v_x_311_ = v___x_336_;
v_x_312_ = v_tail_315_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0_spec__1_spec__2___redArg(lean_object* v_i_342_, lean_object* v_source_343_, lean_object* v_target_344_){
_start:
{
lean_object* v___x_345_; uint8_t v___x_346_; 
v___x_345_ = lean_array_get_size(v_source_343_);
v___x_346_ = lean_nat_dec_lt(v_i_342_, v___x_345_);
if (v___x_346_ == 0)
{
lean_dec_ref(v_source_343_);
lean_dec(v_i_342_);
return v_target_344_;
}
else
{
lean_object* v_es_347_; lean_object* v___x_348_; lean_object* v_source_349_; lean_object* v_target_350_; lean_object* v___x_351_; lean_object* v___x_352_; 
v_es_347_ = lean_array_fget(v_source_343_, v_i_342_);
v___x_348_ = lean_box(0);
v_source_349_ = lean_array_fset(v_source_343_, v_i_342_, v___x_348_);
v_target_350_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0_spec__1_spec__2_spec__4___redArg(v_target_344_, v_es_347_);
v___x_351_ = lean_unsigned_to_nat(1u);
v___x_352_ = lean_nat_add(v_i_342_, v___x_351_);
lean_dec(v_i_342_);
v_i_342_ = v___x_352_;
v_source_343_ = v_source_349_;
v_target_344_ = v_target_350_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0_spec__1___redArg(lean_object* v_data_354_){
_start:
{
lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v_nbuckets_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; 
v___x_355_ = lean_array_get_size(v_data_354_);
v___x_356_ = lean_unsigned_to_nat(2u);
v_nbuckets_357_ = lean_nat_mul(v___x_355_, v___x_356_);
v___x_358_ = lean_unsigned_to_nat(0u);
v___x_359_ = lean_box(0);
v___x_360_ = lean_mk_array(v_nbuckets_357_, v___x_359_);
v___x_361_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0_spec__1_spec__2___redArg(v___x_358_, v_data_354_, v___x_360_);
return v___x_361_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0_spec__0___redArg(lean_object* v_a_362_, lean_object* v_x_363_){
_start:
{
if (lean_obj_tag(v_x_363_) == 0)
{
uint8_t v___x_364_; 
v___x_364_ = 0;
return v___x_364_;
}
else
{
lean_object* v_key_365_; lean_object* v_tail_366_; uint8_t v___x_367_; 
v_key_365_ = lean_ctor_get(v_x_363_, 0);
v_tail_366_ = lean_ctor_get(v_x_363_, 2);
v___x_367_ = lean_name_eq(v_key_365_, v_a_362_);
if (v___x_367_ == 0)
{
v_x_363_ = v_tail_366_;
goto _start;
}
else
{
return v___x_367_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0_spec__0___redArg___boxed(lean_object* v_a_369_, lean_object* v_x_370_){
_start:
{
uint8_t v_res_371_; lean_object* v_r_372_; 
v_res_371_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0_spec__0___redArg(v_a_369_, v_x_370_);
lean_dec(v_x_370_);
lean_dec(v_a_369_);
v_r_372_ = lean_box(v_res_371_);
return v_r_372_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0___redArg(lean_object* v_m_373_, lean_object* v_a_374_, lean_object* v_b_375_){
_start:
{
lean_object* v_size_376_; lean_object* v_buckets_377_; lean_object* v___x_379_; uint8_t v_isShared_380_; uint8_t v_isSharedCheck_423_; 
v_size_376_ = lean_ctor_get(v_m_373_, 0);
v_buckets_377_ = lean_ctor_get(v_m_373_, 1);
v_isSharedCheck_423_ = !lean_is_exclusive(v_m_373_);
if (v_isSharedCheck_423_ == 0)
{
v___x_379_ = v_m_373_;
v_isShared_380_ = v_isSharedCheck_423_;
goto v_resetjp_378_;
}
else
{
lean_inc(v_buckets_377_);
lean_inc(v_size_376_);
lean_dec(v_m_373_);
v___x_379_ = lean_box(0);
v_isShared_380_ = v_isSharedCheck_423_;
goto v_resetjp_378_;
}
v_resetjp_378_:
{
lean_object* v___x_381_; uint64_t v___y_383_; 
v___x_381_ = lean_array_get_size(v_buckets_377_);
if (lean_obj_tag(v_a_374_) == 0)
{
uint64_t v___x_421_; 
v___x_421_ = 1723ULL;
v___y_383_ = v___x_421_;
goto v___jp_382_;
}
else
{
uint64_t v_hash_422_; 
v_hash_422_ = lean_ctor_get_uint64(v_a_374_, sizeof(void*)*2);
v___y_383_ = v_hash_422_;
goto v___jp_382_;
}
v___jp_382_:
{
uint64_t v___x_384_; uint64_t v___x_385_; uint64_t v_fold_386_; uint64_t v___x_387_; uint64_t v___x_388_; uint64_t v___x_389_; size_t v___x_390_; size_t v___x_391_; size_t v___x_392_; size_t v___x_393_; size_t v___x_394_; lean_object* v_bkt_395_; uint8_t v___x_396_; 
v___x_384_ = 32ULL;
v___x_385_ = lean_uint64_shift_right(v___y_383_, v___x_384_);
v_fold_386_ = lean_uint64_xor(v___y_383_, v___x_385_);
v___x_387_ = 16ULL;
v___x_388_ = lean_uint64_shift_right(v_fold_386_, v___x_387_);
v___x_389_ = lean_uint64_xor(v_fold_386_, v___x_388_);
v___x_390_ = lean_uint64_to_usize(v___x_389_);
v___x_391_ = lean_usize_of_nat(v___x_381_);
v___x_392_ = ((size_t)1ULL);
v___x_393_ = lean_usize_sub(v___x_391_, v___x_392_);
v___x_394_ = lean_usize_land(v___x_390_, v___x_393_);
v_bkt_395_ = lean_array_uget_borrowed(v_buckets_377_, v___x_394_);
v___x_396_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0_spec__0___redArg(v_a_374_, v_bkt_395_);
if (v___x_396_ == 0)
{
lean_object* v___x_397_; lean_object* v_size_x27_398_; lean_object* v___x_399_; lean_object* v_buckets_x27_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; uint8_t v___x_406_; 
v___x_397_ = lean_unsigned_to_nat(1u);
v_size_x27_398_ = lean_nat_add(v_size_376_, v___x_397_);
lean_dec(v_size_376_);
lean_inc(v_bkt_395_);
v___x_399_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_399_, 0, v_a_374_);
lean_ctor_set(v___x_399_, 1, v_b_375_);
lean_ctor_set(v___x_399_, 2, v_bkt_395_);
v_buckets_x27_400_ = lean_array_uset(v_buckets_377_, v___x_394_, v___x_399_);
v___x_401_ = lean_unsigned_to_nat(4u);
v___x_402_ = lean_nat_mul(v_size_x27_398_, v___x_401_);
v___x_403_ = lean_unsigned_to_nat(3u);
v___x_404_ = lean_nat_div(v___x_402_, v___x_403_);
lean_dec(v___x_402_);
v___x_405_ = lean_array_get_size(v_buckets_x27_400_);
v___x_406_ = lean_nat_dec_le(v___x_404_, v___x_405_);
lean_dec(v___x_404_);
if (v___x_406_ == 0)
{
lean_object* v_val_407_; lean_object* v___x_409_; 
v_val_407_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0_spec__1___redArg(v_buckets_x27_400_);
if (v_isShared_380_ == 0)
{
lean_ctor_set(v___x_379_, 1, v_val_407_);
lean_ctor_set(v___x_379_, 0, v_size_x27_398_);
v___x_409_ = v___x_379_;
goto v_reusejp_408_;
}
else
{
lean_object* v_reuseFailAlloc_410_; 
v_reuseFailAlloc_410_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_410_, 0, v_size_x27_398_);
lean_ctor_set(v_reuseFailAlloc_410_, 1, v_val_407_);
v___x_409_ = v_reuseFailAlloc_410_;
goto v_reusejp_408_;
}
v_reusejp_408_:
{
return v___x_409_;
}
}
else
{
lean_object* v___x_412_; 
if (v_isShared_380_ == 0)
{
lean_ctor_set(v___x_379_, 1, v_buckets_x27_400_);
lean_ctor_set(v___x_379_, 0, v_size_x27_398_);
v___x_412_ = v___x_379_;
goto v_reusejp_411_;
}
else
{
lean_object* v_reuseFailAlloc_413_; 
v_reuseFailAlloc_413_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_413_, 0, v_size_x27_398_);
lean_ctor_set(v_reuseFailAlloc_413_, 1, v_buckets_x27_400_);
v___x_412_ = v_reuseFailAlloc_413_;
goto v_reusejp_411_;
}
v_reusejp_411_:
{
return v___x_412_;
}
}
}
else
{
lean_object* v___x_414_; lean_object* v_buckets_x27_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_419_; 
lean_inc(v_bkt_395_);
v___x_414_ = lean_box(0);
v_buckets_x27_415_ = lean_array_uset(v_buckets_377_, v___x_394_, v___x_414_);
v___x_416_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0_spec__2___redArg(v_a_374_, v_b_375_, v_bkt_395_);
v___x_417_ = lean_array_uset(v_buckets_x27_415_, v___x_394_, v___x_416_);
if (v_isShared_380_ == 0)
{
lean_ctor_set(v___x_379_, 1, v___x_417_);
v___x_419_ = v___x_379_;
goto v_reusejp_418_;
}
else
{
lean_object* v_reuseFailAlloc_420_; 
v_reuseFailAlloc_420_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_420_, 0, v_size_376_);
lean_ctor_set(v_reuseFailAlloc_420_, 1, v___x_417_);
v___x_419_ = v_reuseFailAlloc_420_;
goto v_reusejp_418_;
}
v_reusejp_418_:
{
return v___x_419_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__1(lean_object* v_as_424_, size_t v_i_425_, size_t v_stop_426_, lean_object* v_b_427_){
_start:
{
uint8_t v___x_428_; 
v___x_428_ = lean_usize_dec_eq(v_i_425_, v_stop_426_);
if (v___x_428_ == 0)
{
lean_object* v___x_429_; lean_object* v_head_430_; lean_object* v___x_431_; size_t v___x_432_; size_t v___x_433_; 
v___x_429_ = lean_array_uget_borrowed(v_as_424_, v_i_425_);
v_head_430_ = lean_ctor_get(v___x_429_, 0);
lean_inc(v___x_429_);
lean_inc(v_head_430_);
v___x_431_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0___redArg(v_b_427_, v_head_430_, v___x_429_);
v___x_432_ = ((size_t)1ULL);
v___x_433_ = lean_usize_add(v_i_425_, v___x_432_);
v_i_425_ = v___x_433_;
v_b_427_ = v___x_431_;
goto _start;
}
else
{
return v_b_427_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__1___boxed(lean_object* v_as_435_, lean_object* v_i_436_, lean_object* v_stop_437_, lean_object* v_b_438_){
_start:
{
size_t v_i_boxed_439_; size_t v_stop_boxed_440_; lean_object* v_res_441_; 
v_i_boxed_439_ = lean_unbox_usize(v_i_436_);
lean_dec(v_i_436_);
v_stop_boxed_440_ = lean_unbox_usize(v_stop_437_);
lean_dec(v_stop_437_);
v_res_441_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__1(v_as_435_, v_i_boxed_439_, v_stop_boxed_440_, v_b_438_);
lean_dec_ref(v_as_435_);
return v_res_441_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_latticeOps___closed__0(void){
_start:
{
lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; 
v___x_442_ = lean_box(0);
v___x_443_ = lean_unsigned_to_nat(16u);
v___x_444_ = lean_mk_array(v___x_443_, v___x_442_);
return v___x_444_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_latticeOps___closed__1(void){
_start:
{
lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; 
v___x_445_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_latticeOps___closed__0, &l_Lean_Elab_Tactic_VCGen_latticeOps___closed__0_once, _init_l_Lean_Elab_Tactic_VCGen_latticeOps___closed__0);
v___x_446_ = lean_unsigned_to_nat(0u);
v___x_447_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_447_, 0, v___x_446_);
lean_ctor_set(v___x_447_, 1, v___x_445_);
return v___x_447_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_latticeOps___closed__2(void){
_start:
{
lean_object* v___x_448_; lean_object* v___x_449_; 
v___x_448_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_builtinLatticeOps));
v___x_449_ = lean_array_get_size(v___x_448_);
return v___x_449_;
}
}
static uint8_t _init_l_Lean_Elab_Tactic_VCGen_latticeOps___closed__3(void){
_start:
{
lean_object* v___x_450_; lean_object* v___x_451_; uint8_t v___x_452_; 
v___x_450_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_latticeOps___closed__2, &l_Lean_Elab_Tactic_VCGen_latticeOps___closed__2_once, _init_l_Lean_Elab_Tactic_VCGen_latticeOps___closed__2);
v___x_451_ = lean_unsigned_to_nat(0u);
v___x_452_ = lean_nat_dec_lt(v___x_451_, v___x_450_);
return v___x_452_;
}
}
static uint8_t _init_l_Lean_Elab_Tactic_VCGen_latticeOps___closed__4(void){
_start:
{
lean_object* v___x_453_; uint8_t v___x_454_; 
v___x_453_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_latticeOps___closed__2, &l_Lean_Elab_Tactic_VCGen_latticeOps___closed__2_once, _init_l_Lean_Elab_Tactic_VCGen_latticeOps___closed__2);
v___x_454_ = lean_nat_dec_le(v___x_453_, v___x_453_);
return v___x_454_;
}
}
static size_t _init_l_Lean_Elab_Tactic_VCGen_latticeOps___closed__5(void){
_start:
{
lean_object* v___x_455_; size_t v___x_456_; 
v___x_455_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_latticeOps___closed__2, &l_Lean_Elab_Tactic_VCGen_latticeOps___closed__2_once, _init_l_Lean_Elab_Tactic_VCGen_latticeOps___closed__2);
v___x_456_ = lean_usize_of_nat(v___x_455_);
return v___x_456_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_latticeOps___closed__6(void){
_start:
{
lean_object* v___x_457_; size_t v___x_458_; size_t v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; 
v___x_457_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_latticeOps___closed__1, &l_Lean_Elab_Tactic_VCGen_latticeOps___closed__1_once, _init_l_Lean_Elab_Tactic_VCGen_latticeOps___closed__1);
v___x_458_ = lean_usize_once(&l_Lean_Elab_Tactic_VCGen_latticeOps___closed__5, &l_Lean_Elab_Tactic_VCGen_latticeOps___closed__5_once, _init_l_Lean_Elab_Tactic_VCGen_latticeOps___closed__5);
v___x_459_ = ((size_t)0ULL);
v___x_460_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_builtinLatticeOps));
v___x_461_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__1(v___x_460_, v___x_459_, v___x_458_, v___x_457_);
return v___x_461_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_latticeOps(void){
_start:
{
lean_object* v___x_462_; uint8_t v___x_463_; 
v___x_462_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_latticeOps___closed__1, &l_Lean_Elab_Tactic_VCGen_latticeOps___closed__1_once, _init_l_Lean_Elab_Tactic_VCGen_latticeOps___closed__1);
v___x_463_ = lean_uint8_once(&l_Lean_Elab_Tactic_VCGen_latticeOps___closed__3, &l_Lean_Elab_Tactic_VCGen_latticeOps___closed__3_once, _init_l_Lean_Elab_Tactic_VCGen_latticeOps___closed__3);
if (v___x_463_ == 0)
{
return v___x_462_;
}
else
{
uint8_t v___x_464_; 
v___x_464_ = lean_uint8_once(&l_Lean_Elab_Tactic_VCGen_latticeOps___closed__4, &l_Lean_Elab_Tactic_VCGen_latticeOps___closed__4_once, _init_l_Lean_Elab_Tactic_VCGen_latticeOps___closed__4);
if (v___x_464_ == 0)
{
if (v___x_463_ == 0)
{
return v___x_462_;
}
else
{
lean_object* v___x_465_; 
v___x_465_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_latticeOps___closed__6, &l_Lean_Elab_Tactic_VCGen_latticeOps___closed__6_once, _init_l_Lean_Elab_Tactic_VCGen_latticeOps___closed__6);
return v___x_465_;
}
}
else
{
lean_object* v___x_466_; 
v___x_466_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_latticeOps___closed__6, &l_Lean_Elab_Tactic_VCGen_latticeOps___closed__6_once, _init_l_Lean_Elab_Tactic_VCGen_latticeOps___closed__6);
return v___x_466_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0(lean_object* v_00_u03b2_467_, lean_object* v_m_468_, lean_object* v_a_469_, lean_object* v_b_470_){
_start:
{
lean_object* v___x_471_; 
v___x_471_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0___redArg(v_m_468_, v_a_469_, v_b_470_);
return v___x_471_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0_spec__0(lean_object* v_00_u03b2_472_, lean_object* v_a_473_, lean_object* v_x_474_){
_start:
{
uint8_t v___x_475_; 
v___x_475_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0_spec__0___redArg(v_a_473_, v_x_474_);
return v___x_475_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0_spec__0___boxed(lean_object* v_00_u03b2_476_, lean_object* v_a_477_, lean_object* v_x_478_){
_start:
{
uint8_t v_res_479_; lean_object* v_r_480_; 
v_res_479_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0_spec__0(v_00_u03b2_476_, v_a_477_, v_x_478_);
lean_dec(v_x_478_);
lean_dec(v_a_477_);
v_r_480_ = lean_box(v_res_479_);
return v_r_480_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0_spec__1(lean_object* v_00_u03b2_481_, lean_object* v_data_482_){
_start:
{
lean_object* v___x_483_; 
v___x_483_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0_spec__1___redArg(v_data_482_);
return v___x_483_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0_spec__2(lean_object* v_00_u03b2_484_, lean_object* v_a_485_, lean_object* v_b_486_, lean_object* v_x_487_){
_start:
{
lean_object* v___x_488_; 
v___x_488_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0_spec__2___redArg(v_a_485_, v_b_486_, v_x_487_);
return v___x_488_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_489_, lean_object* v_i_490_, lean_object* v_source_491_, lean_object* v_target_492_){
_start:
{
lean_object* v___x_493_; 
v___x_493_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0_spec__1_spec__2___redArg(v_i_490_, v_source_491_, v_target_492_);
return v___x_493_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_494_, lean_object* v_x_495_, lean_object* v_x_496_){
_start:
{
lean_object* v___x_497_; 
v___x_497_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0_spec__1_spec__2_spec__4___redArg(v_x_495_, v_x_496_);
return v___x_497_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__0___redArg(lean_object* v_e_498_, lean_object* v___y_499_){
_start:
{
uint8_t v___x_501_; 
v___x_501_ = l_Lean_Expr_hasMVar(v_e_498_);
if (v___x_501_ == 0)
{
lean_object* v___x_502_; 
v___x_502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_502_, 0, v_e_498_);
return v___x_502_;
}
else
{
lean_object* v___x_503_; lean_object* v_mctx_504_; lean_object* v___x_505_; lean_object* v_fst_506_; lean_object* v_snd_507_; lean_object* v___x_508_; lean_object* v_cache_509_; lean_object* v_zetaDeltaFVarIds_510_; lean_object* v_postponed_511_; lean_object* v_diag_512_; lean_object* v___x_514_; uint8_t v_isShared_515_; uint8_t v_isSharedCheck_521_; 
v___x_503_ = lean_st_ref_get(v___y_499_);
v_mctx_504_ = lean_ctor_get(v___x_503_, 0);
lean_inc_ref(v_mctx_504_);
lean_dec(v___x_503_);
v___x_505_ = l_Lean_instantiateMVarsCore(v_mctx_504_, v_e_498_);
v_fst_506_ = lean_ctor_get(v___x_505_, 0);
lean_inc(v_fst_506_);
v_snd_507_ = lean_ctor_get(v___x_505_, 1);
lean_inc(v_snd_507_);
lean_dec_ref(v___x_505_);
v___x_508_ = lean_st_ref_take(v___y_499_);
v_cache_509_ = lean_ctor_get(v___x_508_, 1);
v_zetaDeltaFVarIds_510_ = lean_ctor_get(v___x_508_, 2);
v_postponed_511_ = lean_ctor_get(v___x_508_, 3);
v_diag_512_ = lean_ctor_get(v___x_508_, 4);
v_isSharedCheck_521_ = !lean_is_exclusive(v___x_508_);
if (v_isSharedCheck_521_ == 0)
{
lean_object* v_unused_522_; 
v_unused_522_ = lean_ctor_get(v___x_508_, 0);
lean_dec(v_unused_522_);
v___x_514_ = v___x_508_;
v_isShared_515_ = v_isSharedCheck_521_;
goto v_resetjp_513_;
}
else
{
lean_inc(v_diag_512_);
lean_inc(v_postponed_511_);
lean_inc(v_zetaDeltaFVarIds_510_);
lean_inc(v_cache_509_);
lean_dec(v___x_508_);
v___x_514_ = lean_box(0);
v_isShared_515_ = v_isSharedCheck_521_;
goto v_resetjp_513_;
}
v_resetjp_513_:
{
lean_object* v___x_517_; 
if (v_isShared_515_ == 0)
{
lean_ctor_set(v___x_514_, 0, v_snd_507_);
v___x_517_ = v___x_514_;
goto v_reusejp_516_;
}
else
{
lean_object* v_reuseFailAlloc_520_; 
v_reuseFailAlloc_520_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_520_, 0, v_snd_507_);
lean_ctor_set(v_reuseFailAlloc_520_, 1, v_cache_509_);
lean_ctor_set(v_reuseFailAlloc_520_, 2, v_zetaDeltaFVarIds_510_);
lean_ctor_set(v_reuseFailAlloc_520_, 3, v_postponed_511_);
lean_ctor_set(v_reuseFailAlloc_520_, 4, v_diag_512_);
v___x_517_ = v_reuseFailAlloc_520_;
goto v_reusejp_516_;
}
v_reusejp_516_:
{
lean_object* v___x_518_; lean_object* v___x_519_; 
v___x_518_ = lean_st_ref_put(v___y_499_, v___x_517_);
v___x_519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_519_, 0, v_fst_506_);
return v___x_519_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__0___redArg___boxed(lean_object* v_e_523_, lean_object* v___y_524_, lean_object* v___y_525_){
_start:
{
lean_object* v_res_526_; 
v_res_526_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__0___redArg(v_e_523_, v___y_524_);
lean_dec(v___y_524_);
return v_res_526_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__0(lean_object* v_e_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_){
_start:
{
lean_object* v___x_533_; 
v___x_533_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__0___redArg(v_e_527_, v___y_529_);
return v___x_533_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__0___boxed(lean_object* v_e_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_){
_start:
{
lean_object* v_res_540_; 
v_res_540_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__0(v_e_534_, v___y_535_, v___y_536_, v___y_537_, v___y_538_);
lean_dec(v___y_538_);
lean_dec_ref(v___y_537_);
lean_dec(v___y_536_);
lean_dec_ref(v___y_535_);
return v_res_540_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__1_spec__1(lean_object* v_msgData_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_){
_start:
{
lean_object* v___x_547_; lean_object* v_env_548_; lean_object* v___x_549_; lean_object* v_mctx_550_; lean_object* v_lctx_551_; lean_object* v_options_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; 
v___x_547_ = lean_st_ref_get(v___y_545_);
v_env_548_ = lean_ctor_get(v___x_547_, 0);
lean_inc_ref(v_env_548_);
lean_dec(v___x_547_);
v___x_549_ = lean_st_ref_get(v___y_543_);
v_mctx_550_ = lean_ctor_get(v___x_549_, 0);
lean_inc_ref(v_mctx_550_);
lean_dec(v___x_549_);
v_lctx_551_ = lean_ctor_get(v___y_542_, 2);
v_options_552_ = lean_ctor_get(v___y_544_, 1);
lean_inc_ref(v_options_552_);
lean_inc_ref(v_lctx_551_);
v___x_553_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_553_, 0, v_env_548_);
lean_ctor_set(v___x_553_, 1, v_mctx_550_);
lean_ctor_set(v___x_553_, 2, v_lctx_551_);
lean_ctor_set(v___x_553_, 3, v_options_552_);
v___x_554_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_554_, 0, v___x_553_);
lean_ctor_set(v___x_554_, 1, v_msgData_541_);
v___x_555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_555_, 0, v___x_554_);
return v___x_555_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__1_spec__1___boxed(lean_object* v_msgData_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_){
_start:
{
lean_object* v_res_562_; 
v_res_562_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__1_spec__1(v_msgData_556_, v___y_557_, v___y_558_, v___y_559_, v___y_560_);
lean_dec(v___y_560_);
lean_dec_ref(v___y_559_);
lean_dec(v___y_558_);
lean_dec_ref(v___y_557_);
return v_res_562_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__1___redArg(lean_object* v_msg_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_){
_start:
{
lean_object* v_ref_569_; lean_object* v___x_570_; lean_object* v_a_571_; lean_object* v___x_573_; uint8_t v_isShared_574_; uint8_t v_isSharedCheck_579_; 
v_ref_569_ = lean_ctor_get(v___y_566_, 4);
v___x_570_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__1_spec__1(v_msg_563_, v___y_564_, v___y_565_, v___y_566_, v___y_567_);
v_a_571_ = lean_ctor_get(v___x_570_, 0);
v_isSharedCheck_579_ = !lean_is_exclusive(v___x_570_);
if (v_isSharedCheck_579_ == 0)
{
v___x_573_ = v___x_570_;
v_isShared_574_ = v_isSharedCheck_579_;
goto v_resetjp_572_;
}
else
{
lean_inc(v_a_571_);
lean_dec(v___x_570_);
v___x_573_ = lean_box(0);
v_isShared_574_ = v_isSharedCheck_579_;
goto v_resetjp_572_;
}
v_resetjp_572_:
{
lean_object* v___x_575_; lean_object* v___x_577_; 
lean_inc(v_ref_569_);
v___x_575_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_575_, 0, v_ref_569_);
lean_ctor_set(v___x_575_, 1, v_a_571_);
if (v_isShared_574_ == 0)
{
lean_ctor_set_tag(v___x_573_, 1);
lean_ctor_set(v___x_573_, 0, v___x_575_);
v___x_577_ = v___x_573_;
goto v_reusejp_576_;
}
else
{
lean_object* v_reuseFailAlloc_578_; 
v_reuseFailAlloc_578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_578_, 0, v___x_575_);
v___x_577_ = v_reuseFailAlloc_578_;
goto v_reusejp_576_;
}
v_reusejp_576_:
{
return v___x_577_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__1___redArg___boxed(lean_object* v_msg_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_){
_start:
{
lean_object* v_res_586_; 
v_res_586_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__1___redArg(v_msg_580_, v___y_581_, v___y_582_, v___y_583_, v___y_584_);
lean_dec(v___y_584_);
lean_dec_ref(v___y_583_);
lean_dec(v___y_582_);
lean_dec_ref(v___y_581_);
return v_res_586_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__4(void){
_start:
{
lean_object* v___x_595_; lean_object* v___x_596_; 
v___x_595_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__3));
v___x_596_ = l_Lean_stringToMessageData(v___x_595_);
return v___x_596_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__6(void){
_start:
{
lean_object* v___x_598_; lean_object* v___x_599_; 
v___x_598_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__5));
v___x_599_ = l_Lean_stringToMessageData(v___x_598_);
return v___x_599_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__8(void){
_start:
{
lean_object* v___x_601_; lean_object* v___x_602_; 
v___x_601_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__7));
v___x_602_ = l_Lean_stringToMessageData(v___x_601_);
return v___x_602_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2(lean_object* v_as_603_, size_t v_sz_604_, size_t v_i_605_, lean_object* v_b_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_){
_start:
{
lean_object* v_a_613_; uint8_t v___x_617_; 
v___x_617_ = lean_usize_dec_lt(v_i_605_, v_sz_604_);
if (v___x_617_ == 0)
{
lean_object* v___x_618_; 
v___x_618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_618_, 0, v_b_606_);
return v___x_618_;
}
else
{
lean_object* v_a_619_; lean_object* v___x_620_; 
v_a_619_ = lean_array_uget_borrowed(v_as_603_, v_i_605_);
lean_inc(v_a_619_);
v___x_620_ = l_Lean_Meta_mkConstWithFreshMVarLevels(v_a_619_, v___y_607_, v___y_608_, v___y_609_, v___y_610_);
if (lean_obj_tag(v___x_620_) == 0)
{
lean_object* v_a_621_; lean_object* v___x_622_; 
v_a_621_ = lean_ctor_get(v___x_620_, 0);
lean_inc(v_a_621_);
lean_dec_ref_known(v___x_620_, 1);
lean_inc(v___y_610_);
lean_inc_ref(v___y_609_);
lean_inc(v___y_608_);
lean_inc_ref(v___y_607_);
v___x_622_ = lean_infer_type(v_a_621_, v___y_607_, v___y_608_, v___y_609_, v___y_610_);
if (lean_obj_tag(v___x_622_) == 0)
{
lean_object* v_a_623_; lean_object* v___x_624_; uint8_t v___x_625_; lean_object* v___x_626_; 
v_a_623_ = lean_ctor_get(v___x_622_, 0);
lean_inc(v_a_623_);
lean_dec_ref_known(v___x_622_, 1);
v___x_624_ = lean_box(0);
v___x_625_ = 0;
v___x_626_ = l_Lean_Meta_forallMetaTelescopeReducing(v_a_623_, v___x_624_, v___x_625_, v___y_607_, v___y_608_, v___y_609_, v___y_610_);
if (lean_obj_tag(v___x_626_) == 0)
{
lean_object* v_a_627_; lean_object* v_snd_628_; lean_object* v___x_630_; uint8_t v_isShared_631_; uint8_t v_isSharedCheck_692_; 
v_a_627_ = lean_ctor_get(v___x_626_, 0);
lean_inc(v_a_627_);
lean_dec_ref_known(v___x_626_, 1);
v_snd_628_ = lean_ctor_get(v_a_627_, 1);
v_isSharedCheck_692_ = !lean_is_exclusive(v_a_627_);
if (v_isSharedCheck_692_ == 0)
{
lean_object* v_unused_693_; 
v_unused_693_ = lean_ctor_get(v_a_627_, 0);
lean_dec(v_unused_693_);
v___x_630_ = v_a_627_;
v_isShared_631_ = v_isSharedCheck_692_;
goto v_resetjp_629_;
}
else
{
lean_inc(v_snd_628_);
lean_dec(v_a_627_);
v___x_630_ = lean_box(0);
v_isShared_631_ = v_isSharedCheck_692_;
goto v_resetjp_629_;
}
v_resetjp_629_:
{
lean_object* v_snd_632_; lean_object* v___x_634_; uint8_t v_isShared_635_; uint8_t v_isSharedCheck_690_; 
v_snd_632_ = lean_ctor_get(v_snd_628_, 1);
v_isSharedCheck_690_ = !lean_is_exclusive(v_snd_628_);
if (v_isSharedCheck_690_ == 0)
{
lean_object* v_unused_691_; 
v_unused_691_ = lean_ctor_get(v_snd_628_, 0);
lean_dec(v_unused_691_);
v___x_634_ = v_snd_628_;
v_isShared_635_ = v_isSharedCheck_690_;
goto v_resetjp_633_;
}
else
{
lean_inc(v_snd_632_);
lean_dec(v_snd_628_);
v___x_634_ = lean_box(0);
v_isShared_635_ = v_isSharedCheck_690_;
goto v_resetjp_633_;
}
v_resetjp_633_:
{
lean_object* v___x_636_; 
v___x_636_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__0___redArg(v_snd_632_, v___y_608_);
if (lean_obj_tag(v___x_636_) == 0)
{
lean_object* v_a_637_; lean_object* v___x_638_; lean_object* v___x_639_; uint8_t v___x_640_; 
v_a_637_ = lean_ctor_get(v___x_636_, 0);
lean_inc(v_a_637_);
lean_dec_ref_known(v___x_636_, 1);
v___x_638_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__2));
v___x_639_ = lean_unsigned_to_nat(4u);
v___x_640_ = l_Lean_Expr_isAppOfArity(v_a_637_, v___x_638_, v___x_639_);
if (v___x_640_ == 0)
{
lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_644_; 
lean_dec(v_a_637_);
lean_del_object(v___x_634_);
v___x_641_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__4);
lean_inc(v_a_619_);
v___x_642_ = l_Lean_MessageData_ofName(v_a_619_);
if (v_isShared_631_ == 0)
{
lean_ctor_set_tag(v___x_630_, 7);
lean_ctor_set(v___x_630_, 1, v___x_642_);
lean_ctor_set(v___x_630_, 0, v___x_641_);
v___x_644_ = v___x_630_;
goto v_reusejp_643_;
}
else
{
lean_object* v_reuseFailAlloc_656_; 
v_reuseFailAlloc_656_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_656_, 0, v___x_641_);
lean_ctor_set(v_reuseFailAlloc_656_, 1, v___x_642_);
v___x_644_ = v_reuseFailAlloc_656_;
goto v_reusejp_643_;
}
v_reusejp_643_:
{
lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; 
v___x_645_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__6);
v___x_646_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_646_, 0, v___x_644_);
lean_ctor_set(v___x_646_, 1, v___x_645_);
v___x_647_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__1___redArg(v___x_646_, v___y_607_, v___y_608_, v___y_609_, v___y_610_);
if (lean_obj_tag(v___x_647_) == 0)
{
lean_dec_ref_known(v___x_647_, 1);
v_a_613_ = v_b_606_;
goto v___jp_612_;
}
else
{
lean_object* v_a_648_; lean_object* v___x_650_; uint8_t v_isShared_651_; uint8_t v_isSharedCheck_655_; 
lean_dec_ref(v_b_606_);
v_a_648_ = lean_ctor_get(v___x_647_, 0);
v_isSharedCheck_655_ = !lean_is_exclusive(v___x_647_);
if (v_isSharedCheck_655_ == 0)
{
v___x_650_ = v___x_647_;
v_isShared_651_ = v_isSharedCheck_655_;
goto v_resetjp_649_;
}
else
{
lean_inc(v_a_648_);
lean_dec(v___x_647_);
v___x_650_ = lean_box(0);
v_isShared_651_ = v_isSharedCheck_655_;
goto v_resetjp_649_;
}
v_resetjp_649_:
{
lean_object* v___x_653_; 
if (v_isShared_651_ == 0)
{
v___x_653_ = v___x_650_;
goto v_reusejp_652_;
}
else
{
lean_object* v_reuseFailAlloc_654_; 
v_reuseFailAlloc_654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_654_, 0, v_a_648_);
v___x_653_ = v_reuseFailAlloc_654_;
goto v_reusejp_652_;
}
v_reusejp_652_:
{
return v___x_653_;
}
}
}
}
}
else
{
lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; 
v___x_657_ = l_Lean_Expr_appArg_x21(v_a_637_);
lean_dec(v_a_637_);
v___x_658_ = l_Lean_Expr_getAppFn(v___x_657_);
v___x_659_ = l_Lean_Expr_constName_x3f(v___x_658_);
lean_dec_ref(v___x_658_);
if (lean_obj_tag(v___x_659_) == 1)
{
lean_object* v_val_660_; lean_object* v___x_661_; lean_object* v___x_663_; 
lean_del_object(v___x_630_);
v_val_660_ = lean_ctor_get(v___x_659_, 0);
lean_inc(v_val_660_);
lean_dec_ref_known(v___x_659_, 1);
v___x_661_ = l_Lean_Expr_getAppNumArgs(v___x_657_);
lean_dec_ref(v___x_657_);
lean_inc(v_a_619_);
if (v_isShared_635_ == 0)
{
lean_ctor_set(v___x_634_, 1, v___x_661_);
lean_ctor_set(v___x_634_, 0, v_a_619_);
v___x_663_ = v___x_634_;
goto v_reusejp_662_;
}
else
{
lean_object* v_reuseFailAlloc_665_; 
v_reuseFailAlloc_665_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_665_, 0, v_a_619_);
lean_ctor_set(v_reuseFailAlloc_665_, 1, v___x_661_);
v___x_663_ = v_reuseFailAlloc_665_;
goto v_reusejp_662_;
}
v_reusejp_662_:
{
lean_object* v___x_664_; 
v___x_664_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0___redArg(v_b_606_, v_val_660_, v___x_663_);
v_a_613_ = v___x_664_;
goto v___jp_612_;
}
}
else
{
lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_669_; 
lean_dec(v___x_659_);
lean_dec_ref(v___x_657_);
lean_del_object(v___x_634_);
v___x_666_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__4);
lean_inc(v_a_619_);
v___x_667_ = l_Lean_MessageData_ofName(v_a_619_);
if (v_isShared_631_ == 0)
{
lean_ctor_set_tag(v___x_630_, 7);
lean_ctor_set(v___x_630_, 1, v___x_667_);
lean_ctor_set(v___x_630_, 0, v___x_666_);
v___x_669_ = v___x_630_;
goto v_reusejp_668_;
}
else
{
lean_object* v_reuseFailAlloc_681_; 
v_reuseFailAlloc_681_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_681_, 0, v___x_666_);
lean_ctor_set(v_reuseFailAlloc_681_, 1, v___x_667_);
v___x_669_ = v_reuseFailAlloc_681_;
goto v_reusejp_668_;
}
v_reusejp_668_:
{
lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; 
v___x_670_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__8);
v___x_671_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_671_, 0, v___x_669_);
lean_ctor_set(v___x_671_, 1, v___x_670_);
v___x_672_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__1___redArg(v___x_671_, v___y_607_, v___y_608_, v___y_609_, v___y_610_);
if (lean_obj_tag(v___x_672_) == 0)
{
lean_dec_ref_known(v___x_672_, 1);
v_a_613_ = v_b_606_;
goto v___jp_612_;
}
else
{
lean_object* v_a_673_; lean_object* v___x_675_; uint8_t v_isShared_676_; uint8_t v_isSharedCheck_680_; 
lean_dec_ref(v_b_606_);
v_a_673_ = lean_ctor_get(v___x_672_, 0);
v_isSharedCheck_680_ = !lean_is_exclusive(v___x_672_);
if (v_isSharedCheck_680_ == 0)
{
v___x_675_ = v___x_672_;
v_isShared_676_ = v_isSharedCheck_680_;
goto v_resetjp_674_;
}
else
{
lean_inc(v_a_673_);
lean_dec(v___x_672_);
v___x_675_ = lean_box(0);
v_isShared_676_ = v_isSharedCheck_680_;
goto v_resetjp_674_;
}
v_resetjp_674_:
{
lean_object* v___x_678_; 
if (v_isShared_676_ == 0)
{
v___x_678_ = v___x_675_;
goto v_reusejp_677_;
}
else
{
lean_object* v_reuseFailAlloc_679_; 
v_reuseFailAlloc_679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_679_, 0, v_a_673_);
v___x_678_ = v_reuseFailAlloc_679_;
goto v_reusejp_677_;
}
v_reusejp_677_:
{
return v___x_678_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_682_; lean_object* v___x_684_; uint8_t v_isShared_685_; uint8_t v_isSharedCheck_689_; 
lean_del_object(v___x_634_);
lean_del_object(v___x_630_);
lean_dec_ref(v_b_606_);
v_a_682_ = lean_ctor_get(v___x_636_, 0);
v_isSharedCheck_689_ = !lean_is_exclusive(v___x_636_);
if (v_isSharedCheck_689_ == 0)
{
v___x_684_ = v___x_636_;
v_isShared_685_ = v_isSharedCheck_689_;
goto v_resetjp_683_;
}
else
{
lean_inc(v_a_682_);
lean_dec(v___x_636_);
v___x_684_ = lean_box(0);
v_isShared_685_ = v_isSharedCheck_689_;
goto v_resetjp_683_;
}
v_resetjp_683_:
{
lean_object* v___x_687_; 
if (v_isShared_685_ == 0)
{
v___x_687_ = v___x_684_;
goto v_reusejp_686_;
}
else
{
lean_object* v_reuseFailAlloc_688_; 
v_reuseFailAlloc_688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_688_, 0, v_a_682_);
v___x_687_ = v_reuseFailAlloc_688_;
goto v_reusejp_686_;
}
v_reusejp_686_:
{
return v___x_687_;
}
}
}
}
}
}
else
{
lean_object* v_a_694_; lean_object* v___x_696_; uint8_t v_isShared_697_; uint8_t v_isSharedCheck_701_; 
lean_dec_ref(v_b_606_);
v_a_694_ = lean_ctor_get(v___x_626_, 0);
v_isSharedCheck_701_ = !lean_is_exclusive(v___x_626_);
if (v_isSharedCheck_701_ == 0)
{
v___x_696_ = v___x_626_;
v_isShared_697_ = v_isSharedCheck_701_;
goto v_resetjp_695_;
}
else
{
lean_inc(v_a_694_);
lean_dec(v___x_626_);
v___x_696_ = lean_box(0);
v_isShared_697_ = v_isSharedCheck_701_;
goto v_resetjp_695_;
}
v_resetjp_695_:
{
lean_object* v___x_699_; 
if (v_isShared_697_ == 0)
{
v___x_699_ = v___x_696_;
goto v_reusejp_698_;
}
else
{
lean_object* v_reuseFailAlloc_700_; 
v_reuseFailAlloc_700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_700_, 0, v_a_694_);
v___x_699_ = v_reuseFailAlloc_700_;
goto v_reusejp_698_;
}
v_reusejp_698_:
{
return v___x_699_;
}
}
}
}
else
{
lean_object* v_a_702_; lean_object* v___x_704_; uint8_t v_isShared_705_; uint8_t v_isSharedCheck_709_; 
lean_dec_ref(v_b_606_);
v_a_702_ = lean_ctor_get(v___x_622_, 0);
v_isSharedCheck_709_ = !lean_is_exclusive(v___x_622_);
if (v_isSharedCheck_709_ == 0)
{
v___x_704_ = v___x_622_;
v_isShared_705_ = v_isSharedCheck_709_;
goto v_resetjp_703_;
}
else
{
lean_inc(v_a_702_);
lean_dec(v___x_622_);
v___x_704_ = lean_box(0);
v_isShared_705_ = v_isSharedCheck_709_;
goto v_resetjp_703_;
}
v_resetjp_703_:
{
lean_object* v___x_707_; 
if (v_isShared_705_ == 0)
{
v___x_707_ = v___x_704_;
goto v_reusejp_706_;
}
else
{
lean_object* v_reuseFailAlloc_708_; 
v_reuseFailAlloc_708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_708_, 0, v_a_702_);
v___x_707_ = v_reuseFailAlloc_708_;
goto v_reusejp_706_;
}
v_reusejp_706_:
{
return v___x_707_;
}
}
}
}
else
{
lean_object* v_a_710_; lean_object* v___x_712_; uint8_t v_isShared_713_; uint8_t v_isSharedCheck_717_; 
lean_dec_ref(v_b_606_);
v_a_710_ = lean_ctor_get(v___x_620_, 0);
v_isSharedCheck_717_ = !lean_is_exclusive(v___x_620_);
if (v_isSharedCheck_717_ == 0)
{
v___x_712_ = v___x_620_;
v_isShared_713_ = v_isSharedCheck_717_;
goto v_resetjp_711_;
}
else
{
lean_inc(v_a_710_);
lean_dec(v___x_620_);
v___x_712_ = lean_box(0);
v_isShared_713_ = v_isSharedCheck_717_;
goto v_resetjp_711_;
}
v_resetjp_711_:
{
lean_object* v___x_715_; 
if (v_isShared_713_ == 0)
{
v___x_715_ = v___x_712_;
goto v_reusejp_714_;
}
else
{
lean_object* v_reuseFailAlloc_716_; 
v_reuseFailAlloc_716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_716_, 0, v_a_710_);
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
v___jp_612_:
{
size_t v___x_614_; size_t v___x_615_; 
v___x_614_ = ((size_t)1ULL);
v___x_615_ = lean_usize_add(v_i_605_, v___x_614_);
v_i_605_ = v___x_615_;
v_b_606_ = v_a_613_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___boxed(lean_object* v_as_718_, lean_object* v_sz_719_, lean_object* v_i_720_, lean_object* v_b_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_){
_start:
{
size_t v_sz_boxed_727_; size_t v_i_boxed_728_; lean_object* v_res_729_; 
v_sz_boxed_727_ = lean_unbox_usize(v_sz_719_);
lean_dec(v_sz_719_);
v_i_boxed_728_ = lean_unbox_usize(v_i_720_);
lean_dec(v_i_720_);
v_res_729_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2(v_as_718_, v_sz_boxed_727_, v_i_boxed_728_, v_b_721_, v___y_722_, v___y_723_, v___y_724_, v___y_725_);
lean_dec(v___y_725_);
lean_dec_ref(v___y_724_);
lean_dec(v___y_723_);
lean_dec_ref(v___y_722_);
lean_dec_ref(v_as_718_);
return v_res_729_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals(lean_object* v_names_730_, lean_object* v_a_731_, lean_object* v_a_732_, lean_object* v_a_733_, lean_object* v_a_734_){
_start:
{
lean_object* v_m_736_; size_t v_sz_737_; size_t v___x_738_; lean_object* v___x_739_; 
v_m_736_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_latticeOps___closed__1, &l_Lean_Elab_Tactic_VCGen_latticeOps___closed__1_once, _init_l_Lean_Elab_Tactic_VCGen_latticeOps___closed__1);
v_sz_737_ = lean_array_size(v_names_730_);
v___x_738_ = ((size_t)0ULL);
v___x_739_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2(v_names_730_, v_sz_737_, v___x_738_, v_m_736_, v_a_731_, v_a_732_, v_a_733_, v_a_734_);
return v___x_739_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals___boxed(lean_object* v_names_740_, lean_object* v_a_741_, lean_object* v_a_742_, lean_object* v_a_743_, lean_object* v_a_744_, lean_object* v_a_745_){
_start:
{
lean_object* v_res_746_; 
v_res_746_ = l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals(v_names_740_, v_a_741_, v_a_742_, v_a_743_, v_a_744_);
lean_dec(v_a_744_);
lean_dec_ref(v_a_743_);
lean_dec(v_a_742_);
lean_dec_ref(v_a_741_);
lean_dec_ref(v_names_740_);
return v_res_746_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__1(lean_object* v_00_u03b1_747_, lean_object* v_msg_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_){
_start:
{
lean_object* v___x_754_; 
v___x_754_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__1___redArg(v_msg_748_, v___y_749_, v___y_750_, v___y_751_, v___y_752_);
return v___x_754_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__1___boxed(lean_object* v_00_u03b1_755_, lean_object* v_msg_756_, lean_object* v___y_757_, lean_object* v___y_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_){
_start:
{
lean_object* v_res_762_; 
v_res_762_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__1(v_00_u03b1_755_, v_msg_756_, v___y_757_, v___y_758_, v___y_759_, v___y_760_);
lean_dec(v___y_760_);
lean_dec_ref(v___y_759_);
lean_dec(v___y_758_);
lean_dec_ref(v___y_757_);
return v_res_762_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_go___lam__0(uint8_t v_isZero_763_, lean_object* v_x_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v___y_773_){
_start:
{
lean_object* v___x_775_; lean_object* v___x_776_; 
v___x_775_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_775_, 0, v_isZero_763_);
lean_ctor_set_uint8(v___x_775_, 1, v_isZero_763_);
v___x_776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_776_, 0, v___x_775_);
return v___x_776_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_go___lam__0___boxed(lean_object* v_isZero_777_, lean_object* v_x_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_){
_start:
{
uint8_t v_isZero_boxed_789_; lean_object* v_res_790_; 
v_isZero_boxed_789_ = lean_unbox(v_isZero_777_);
v_res_790_ = l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_go___lam__0(v_isZero_boxed_789_, v_x_778_, v___y_779_, v___y_780_, v___y_781_, v___y_782_, v___y_783_, v___y_784_, v___y_785_, v___y_786_, v___y_787_);
lean_dec(v___y_787_);
lean_dec_ref(v___y_786_);
lean_dec(v___y_785_);
lean_dec_ref(v___y_784_);
lean_dec(v___y_783_);
lean_dec_ref(v___y_782_);
lean_dec(v___y_781_);
lean_dec_ref(v___y_780_);
lean_dec(v___y_779_);
lean_dec_ref(v_x_778_);
return v_res_790_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_go_spec__0___redArg(lean_object* v_msg_791_, lean_object* v___y_792_, lean_object* v___y_793_, lean_object* v___y_794_, lean_object* v___y_795_){
_start:
{
lean_object* v_ref_797_; lean_object* v___x_798_; lean_object* v_a_799_; lean_object* v___x_801_; uint8_t v_isShared_802_; uint8_t v_isSharedCheck_807_; 
v_ref_797_ = lean_ctor_get(v___y_794_, 4);
v___x_798_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__1_spec__1(v_msg_791_, v___y_792_, v___y_793_, v___y_794_, v___y_795_);
v_a_799_ = lean_ctor_get(v___x_798_, 0);
v_isSharedCheck_807_ = !lean_is_exclusive(v___x_798_);
if (v_isSharedCheck_807_ == 0)
{
v___x_801_ = v___x_798_;
v_isShared_802_ = v_isSharedCheck_807_;
goto v_resetjp_800_;
}
else
{
lean_inc(v_a_799_);
lean_dec(v___x_798_);
v___x_801_ = lean_box(0);
v_isShared_802_ = v_isSharedCheck_807_;
goto v_resetjp_800_;
}
v_resetjp_800_:
{
lean_object* v___x_803_; lean_object* v___x_805_; 
lean_inc(v_ref_797_);
v___x_803_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_803_, 0, v_ref_797_);
lean_ctor_set(v___x_803_, 1, v_a_799_);
if (v_isShared_802_ == 0)
{
lean_ctor_set_tag(v___x_801_, 1);
lean_ctor_set(v___x_801_, 0, v___x_803_);
v___x_805_ = v___x_801_;
goto v_reusejp_804_;
}
else
{
lean_object* v_reuseFailAlloc_806_; 
v_reuseFailAlloc_806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_806_, 0, v___x_803_);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_go_spec__0___redArg___boxed(lean_object* v_msg_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_){
_start:
{
lean_object* v_res_814_; 
v_res_814_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_go_spec__0___redArg(v_msg_808_, v___y_809_, v___y_810_, v___y_811_, v___y_812_);
lean_dec(v___y_812_);
lean_dec_ref(v___y_811_);
lean_dec(v___y_810_);
lean_dec_ref(v___y_809_);
return v_res_814_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_go___closed__1(void){
_start:
{
lean_object* v___x_816_; lean_object* v___x_817_; 
v___x_816_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_go___closed__0));
v___x_817_ = l_Lean_stringToMessageData(v___x_816_);
return v___x_817_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_go(lean_object* v_step_821_, lean_object* v_e_u2080_822_, lean_object* v_cur_823_, lean_object* v_proof_x3f_824_, lean_object* v_a_825_, lean_object* v_a_826_, lean_object* v_a_827_, lean_object* v_a_828_, lean_object* v_a_829_, lean_object* v_a_830_, lean_object* v_a_831_){
_start:
{
lean_object* v_zero_833_; uint8_t v_isZero_834_; 
v_zero_833_ = lean_unsigned_to_nat(0u);
v_isZero_834_ = lean_nat_dec_eq(v_a_825_, v_zero_833_);
if (v_isZero_834_ == 1)
{
lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; 
lean_dec(v_a_825_);
lean_dec(v_proof_x3f_824_);
lean_dec_ref(v_e_u2080_822_);
lean_dec_ref(v_step_821_);
v___x_835_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_go___closed__1, &l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_go___closed__1_once, _init_l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_go___closed__1);
v___x_836_ = l_Lean_indentExpr(v_cur_823_);
v___x_837_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_837_, 0, v___x_835_);
lean_ctor_set(v___x_837_, 1, v___x_836_);
v___x_838_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_go_spec__0___redArg(v___x_837_, v_a_828_, v_a_829_, v_a_830_, v_a_831_);
return v___x_838_;
}
else
{
lean_object* v___x_839_; lean_object* v___f_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; 
v___x_839_ = lean_box(v_isZero_834_);
v___f_840_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_go___lam__0___boxed), 12, 1);
lean_closure_set(v___f_840_, 0, v___x_839_);
lean_inc_ref(v_step_821_);
lean_inc_ref(v_cur_823_);
v___x_841_ = lean_apply_1(v_step_821_, v_cur_823_);
lean_inc_ref(v___f_840_);
v___x_842_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_842_, 0, v___f_840_);
lean_ctor_set(v___x_842_, 1, v___f_840_);
v___x_843_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_go___closed__2));
v___x_844_ = l_Lean_Meta_Sym_Simp_SimpM_run_x27___redArg(v___x_841_, v___x_842_, v___x_843_, v_a_826_, v_a_827_, v_a_828_, v_a_829_, v_a_830_, v_a_831_);
if (lean_obj_tag(v___x_844_) == 0)
{
lean_object* v_a_845_; lean_object* v___x_847_; uint8_t v_isShared_848_; uint8_t v_isSharedCheck_878_; 
v_a_845_ = lean_ctor_get(v___x_844_, 0);
v_isSharedCheck_878_ = !lean_is_exclusive(v___x_844_);
if (v_isSharedCheck_878_ == 0)
{
v___x_847_ = v___x_844_;
v_isShared_848_ = v_isSharedCheck_878_;
goto v_resetjp_846_;
}
else
{
lean_inc(v_a_845_);
lean_dec(v___x_844_);
v___x_847_ = lean_box(0);
v_isShared_848_ = v_isSharedCheck_878_;
goto v_resetjp_846_;
}
v_resetjp_846_:
{
if (lean_obj_tag(v_a_845_) == 0)
{
lean_object* v___x_849_; lean_object* v___x_851_; 
lean_dec_ref_known(v_a_845_, 0);
lean_dec(v_a_825_);
lean_dec_ref(v_e_u2080_822_);
lean_dec_ref(v_step_821_);
v___x_849_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_849_, 0, v_cur_823_);
lean_ctor_set(v___x_849_, 1, v_proof_x3f_824_);
if (v_isShared_848_ == 0)
{
lean_ctor_set(v___x_847_, 0, v___x_849_);
v___x_851_ = v___x_847_;
goto v_reusejp_850_;
}
else
{
lean_object* v_reuseFailAlloc_852_; 
v_reuseFailAlloc_852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_852_, 0, v___x_849_);
v___x_851_ = v_reuseFailAlloc_852_;
goto v_reusejp_850_;
}
v_reusejp_850_:
{
return v___x_851_;
}
}
else
{
lean_object* v_e_x27_853_; lean_object* v_proof_854_; lean_object* v_one_855_; lean_object* v_n_856_; lean_object* v_proof_858_; lean_object* v___y_859_; lean_object* v___y_860_; lean_object* v___y_861_; lean_object* v___y_862_; lean_object* v___y_863_; lean_object* v___y_864_; 
lean_del_object(v___x_847_);
v_e_x27_853_ = lean_ctor_get(v_a_845_, 0);
lean_inc_ref(v_e_x27_853_);
v_proof_854_ = lean_ctor_get(v_a_845_, 1);
lean_inc_ref(v_proof_854_);
lean_dec_ref_known(v_a_845_, 2);
v_one_855_ = lean_unsigned_to_nat(1u);
v_n_856_ = lean_nat_sub(v_a_825_, v_one_855_);
lean_dec(v_a_825_);
if (lean_obj_tag(v_proof_x3f_824_) == 0)
{
lean_dec_ref(v_cur_823_);
v_proof_858_ = v_proof_854_;
v___y_859_ = v_a_826_;
v___y_860_ = v_a_827_;
v___y_861_ = v_a_828_;
v___y_862_ = v_a_829_;
v___y_863_ = v_a_830_;
v___y_864_ = v_a_831_;
goto v___jp_857_;
}
else
{
lean_object* v_val_867_; lean_object* v___x_868_; 
v_val_867_ = lean_ctor_get(v_proof_x3f_824_, 0);
lean_inc(v_val_867_);
lean_dec_ref_known(v_proof_x3f_824_, 1);
lean_inc_ref(v_e_x27_853_);
lean_inc_ref(v_e_u2080_822_);
v___x_868_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v_e_u2080_822_, v_cur_823_, v_val_867_, v_e_x27_853_, v_proof_854_, v_a_826_, v_a_827_, v_a_828_, v_a_829_, v_a_830_, v_a_831_);
if (lean_obj_tag(v___x_868_) == 0)
{
lean_object* v_a_869_; 
v_a_869_ = lean_ctor_get(v___x_868_, 0);
lean_inc(v_a_869_);
lean_dec_ref_known(v___x_868_, 1);
v_proof_858_ = v_a_869_;
v___y_859_ = v_a_826_;
v___y_860_ = v_a_827_;
v___y_861_ = v_a_828_;
v___y_862_ = v_a_829_;
v___y_863_ = v_a_830_;
v___y_864_ = v_a_831_;
goto v___jp_857_;
}
else
{
lean_object* v_a_870_; lean_object* v___x_872_; uint8_t v_isShared_873_; uint8_t v_isSharedCheck_877_; 
lean_dec(v_n_856_);
lean_dec_ref(v_e_x27_853_);
lean_dec_ref(v_e_u2080_822_);
lean_dec_ref(v_step_821_);
v_a_870_ = lean_ctor_get(v___x_868_, 0);
v_isSharedCheck_877_ = !lean_is_exclusive(v___x_868_);
if (v_isSharedCheck_877_ == 0)
{
v___x_872_ = v___x_868_;
v_isShared_873_ = v_isSharedCheck_877_;
goto v_resetjp_871_;
}
else
{
lean_inc(v_a_870_);
lean_dec(v___x_868_);
v___x_872_ = lean_box(0);
v_isShared_873_ = v_isSharedCheck_877_;
goto v_resetjp_871_;
}
v_resetjp_871_:
{
lean_object* v___x_875_; 
if (v_isShared_873_ == 0)
{
v___x_875_ = v___x_872_;
goto v_reusejp_874_;
}
else
{
lean_object* v_reuseFailAlloc_876_; 
v_reuseFailAlloc_876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_876_, 0, v_a_870_);
v___x_875_ = v_reuseFailAlloc_876_;
goto v_reusejp_874_;
}
v_reusejp_874_:
{
return v___x_875_;
}
}
}
}
v___jp_857_:
{
lean_object* v___x_865_; 
v___x_865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_865_, 0, v_proof_858_);
v_cur_823_ = v_e_x27_853_;
v_proof_x3f_824_ = v___x_865_;
v_a_825_ = v_n_856_;
v_a_826_ = v___y_859_;
v_a_827_ = v___y_860_;
v_a_828_ = v___y_861_;
v_a_829_ = v___y_862_;
v_a_830_ = v___y_863_;
v_a_831_ = v___y_864_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_879_; lean_object* v___x_881_; uint8_t v_isShared_882_; uint8_t v_isSharedCheck_886_; 
lean_dec(v_a_825_);
lean_dec(v_proof_x3f_824_);
lean_dec_ref(v_cur_823_);
lean_dec_ref(v_e_u2080_822_);
lean_dec_ref(v_step_821_);
v_a_879_ = lean_ctor_get(v___x_844_, 0);
v_isSharedCheck_886_ = !lean_is_exclusive(v___x_844_);
if (v_isSharedCheck_886_ == 0)
{
v___x_881_ = v___x_844_;
v_isShared_882_ = v_isSharedCheck_886_;
goto v_resetjp_880_;
}
else
{
lean_inc(v_a_879_);
lean_dec(v___x_844_);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_go___boxed(lean_object* v_step_887_, lean_object* v_e_u2080_888_, lean_object* v_cur_889_, lean_object* v_proof_x3f_890_, lean_object* v_a_891_, lean_object* v_a_892_, lean_object* v_a_893_, lean_object* v_a_894_, lean_object* v_a_895_, lean_object* v_a_896_, lean_object* v_a_897_, lean_object* v_a_898_){
_start:
{
lean_object* v_res_899_; 
v_res_899_ = l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_go(v_step_887_, v_e_u2080_888_, v_cur_889_, v_proof_x3f_890_, v_a_891_, v_a_892_, v_a_893_, v_a_894_, v_a_895_, v_a_896_, v_a_897_);
lean_dec(v_a_897_);
lean_dec_ref(v_a_896_);
lean_dec(v_a_895_);
lean_dec_ref(v_a_894_);
lean_dec(v_a_893_);
lean_dec_ref(v_a_892_);
return v_res_899_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_go_spec__0(lean_object* v_00_u03b1_900_, lean_object* v_msg_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_){
_start:
{
lean_object* v___x_909_; 
v___x_909_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_go_spec__0___redArg(v_msg_901_, v___y_904_, v___y_905_, v___y_906_, v___y_907_);
return v___x_909_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_go_spec__0___boxed(lean_object* v_00_u03b1_910_, lean_object* v_msg_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_){
_start:
{
lean_object* v_res_919_; 
v_res_919_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_go_spec__0(v_00_u03b1_910_, v_msg_911_, v___y_912_, v___y_913_, v___y_914_, v___y_915_, v___y_916_, v___y_917_);
lean_dec(v___y_917_);
lean_dec_ref(v___y_916_);
lean_dec(v___y_915_);
lean_dec_ref(v___y_914_);
lean_dec(v___y_913_);
lean_dec_ref(v___y_912_);
return v_res_919_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_spec__0___redArg(lean_object* v_as_920_, size_t v_i_921_, size_t v_stop_922_, lean_object* v_b_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_){
_start:
{
uint8_t v___x_929_; 
v___x_929_ = lean_usize_dec_eq(v_i_921_, v_stop_922_);
if (v___x_929_ == 0)
{
lean_object* v___x_930_; lean_object* v___x_931_; 
v___x_930_ = lean_array_uget_borrowed(v_as_920_, v_i_921_);
lean_inc(v___x_930_);
v___x_931_ = l_Lean_Meta_Sym_Simp_mkTheoremFromDecl(v___x_930_, v___y_924_, v___y_925_, v___y_926_, v___y_927_);
if (lean_obj_tag(v___x_931_) == 0)
{
lean_object* v_a_932_; lean_object* v___x_933_; size_t v___x_934_; size_t v___x_935_; 
v_a_932_ = lean_ctor_get(v___x_931_, 0);
lean_inc(v_a_932_);
lean_dec_ref_known(v___x_931_, 1);
v___x_933_ = l_Lean_Meta_Sym_Simp_Theorems_insert(v_b_923_, v_a_932_);
v___x_934_ = ((size_t)1ULL);
v___x_935_ = lean_usize_add(v_i_921_, v___x_934_);
v_i_921_ = v___x_935_;
v_b_923_ = v___x_933_;
goto _start;
}
else
{
lean_object* v_a_937_; lean_object* v___x_939_; uint8_t v_isShared_940_; uint8_t v_isSharedCheck_944_; 
lean_dec_ref(v_b_923_);
v_a_937_ = lean_ctor_get(v___x_931_, 0);
v_isSharedCheck_944_ = !lean_is_exclusive(v___x_931_);
if (v_isSharedCheck_944_ == 0)
{
v___x_939_ = v___x_931_;
v_isShared_940_ = v_isSharedCheck_944_;
goto v_resetjp_938_;
}
else
{
lean_inc(v_a_937_);
lean_dec(v___x_931_);
v___x_939_ = lean_box(0);
v_isShared_940_ = v_isSharedCheck_944_;
goto v_resetjp_938_;
}
v_resetjp_938_:
{
lean_object* v___x_942_; 
if (v_isShared_940_ == 0)
{
v___x_942_ = v___x_939_;
goto v_reusejp_941_;
}
else
{
lean_object* v_reuseFailAlloc_943_; 
v_reuseFailAlloc_943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_943_, 0, v_a_937_);
v___x_942_ = v_reuseFailAlloc_943_;
goto v_reusejp_941_;
}
v_reusejp_941_:
{
return v___x_942_;
}
}
}
}
else
{
lean_object* v___x_945_; 
v___x_945_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_945_, 0, v_b_923_);
return v___x_945_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_spec__0___redArg___boxed(lean_object* v_as_946_, lean_object* v_i_947_, lean_object* v_stop_948_, lean_object* v_b_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_){
_start:
{
size_t v_i_boxed_955_; size_t v_stop_boxed_956_; lean_object* v_res_957_; 
v_i_boxed_955_ = lean_unbox_usize(v_i_947_);
lean_dec(v_i_947_);
v_stop_boxed_956_ = lean_unbox_usize(v_stop_948_);
lean_dec(v_stop_948_);
v_res_957_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_spec__0___redArg(v_as_946_, v_i_boxed_955_, v_stop_boxed_956_, v_b_949_, v___y_950_, v___y_951_, v___y_952_, v___y_953_);
lean_dec(v___y_953_);
lean_dec_ref(v___y_952_);
lean_dec(v___y_951_);
lean_dec_ref(v___y_950_);
lean_dec_ref(v_as_946_);
return v_res_957_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp___closed__1(void){
_start:
{
lean_object* v___x_959_; 
v___x_959_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_959_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp___closed__2(void){
_start:
{
lean_object* v___x_960_; lean_object* v___x_961_; 
v___x_960_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp___closed__1, &l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp___closed__1_once, _init_l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp___closed__1);
v___x_961_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_961_, 0, v___x_960_);
return v___x_961_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp(lean_object* v_rewrites_962_, lean_object* v_e_963_, lean_object* v_fuel_964_, lean_object* v_a_965_, lean_object* v_a_966_, lean_object* v_a_967_, lean_object* v_a_968_, lean_object* v_a_969_, lean_object* v_a_970_){
_start:
{
lean_object* v_a_973_; lean_object* v___y_989_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; uint8_t v___x_1002_; 
v___x_999_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp___closed__2, &l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp___closed__2_once, _init_l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp___closed__2);
v___x_1000_ = lean_unsigned_to_nat(0u);
v___x_1001_ = lean_array_get_size(v_rewrites_962_);
v___x_1002_ = lean_nat_dec_lt(v___x_1000_, v___x_1001_);
if (v___x_1002_ == 0)
{
v_a_973_ = v___x_999_;
goto v___jp_972_;
}
else
{
uint8_t v___x_1003_; 
v___x_1003_ = lean_nat_dec_le(v___x_1001_, v___x_1001_);
if (v___x_1003_ == 0)
{
if (v___x_1002_ == 0)
{
v_a_973_ = v___x_999_;
goto v___jp_972_;
}
else
{
size_t v___x_1004_; size_t v___x_1005_; lean_object* v___x_1006_; 
v___x_1004_ = ((size_t)0ULL);
v___x_1005_ = lean_usize_of_nat(v___x_1001_);
v___x_1006_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_spec__0___redArg(v_rewrites_962_, v___x_1004_, v___x_1005_, v___x_999_, v_a_967_, v_a_968_, v_a_969_, v_a_970_);
v___y_989_ = v___x_1006_;
goto v___jp_988_;
}
}
else
{
size_t v___x_1007_; size_t v___x_1008_; lean_object* v___x_1009_; 
v___x_1007_ = ((size_t)0ULL);
v___x_1008_ = lean_usize_of_nat(v___x_1001_);
v___x_1009_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_spec__0___redArg(v_rewrites_962_, v___x_1007_, v___x_1008_, v___x_999_, v_a_967_, v_a_968_, v_a_969_, v_a_970_);
v___y_989_ = v___x_1009_;
goto v___jp_988_;
}
}
v___jp_972_:
{
lean_object* v___x_974_; 
v___x_974_ = l_Lean_Meta_Sym_shareCommon(v_e_963_, v_a_965_, v_a_966_, v_a_967_, v_a_968_, v_a_969_, v_a_970_);
if (lean_obj_tag(v___x_974_) == 0)
{
lean_object* v_a_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; 
v_a_975_ = lean_ctor_get(v___x_974_, 0);
lean_inc_n(v_a_975_, 2);
lean_dec_ref_known(v___x_974_, 1);
v___x_976_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp___closed__0));
v___x_977_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Simp_Theorems_rewrite___boxed), 13, 2);
lean_closure_set(v___x_977_, 0, v_a_973_);
lean_closure_set(v___x_977_, 1, v___x_976_);
v___x_978_ = lean_box(0);
v___x_979_ = l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_go(v___x_977_, v_a_975_, v_a_975_, v___x_978_, v_fuel_964_, v_a_965_, v_a_966_, v_a_967_, v_a_968_, v_a_969_, v_a_970_);
return v___x_979_;
}
else
{
lean_object* v_a_980_; lean_object* v___x_982_; uint8_t v_isShared_983_; uint8_t v_isSharedCheck_987_; 
lean_dec_ref(v_a_973_);
lean_dec(v_fuel_964_);
v_a_980_ = lean_ctor_get(v___x_974_, 0);
v_isSharedCheck_987_ = !lean_is_exclusive(v___x_974_);
if (v_isSharedCheck_987_ == 0)
{
v___x_982_ = v___x_974_;
v_isShared_983_ = v_isSharedCheck_987_;
goto v_resetjp_981_;
}
else
{
lean_inc(v_a_980_);
lean_dec(v___x_974_);
v___x_982_ = lean_box(0);
v_isShared_983_ = v_isSharedCheck_987_;
goto v_resetjp_981_;
}
v_resetjp_981_:
{
lean_object* v___x_985_; 
if (v_isShared_983_ == 0)
{
v___x_985_ = v___x_982_;
goto v_reusejp_984_;
}
else
{
lean_object* v_reuseFailAlloc_986_; 
v_reuseFailAlloc_986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_986_, 0, v_a_980_);
v___x_985_ = v_reuseFailAlloc_986_;
goto v_reusejp_984_;
}
v_reusejp_984_:
{
return v___x_985_;
}
}
}
}
v___jp_988_:
{
if (lean_obj_tag(v___y_989_) == 0)
{
lean_object* v_a_990_; 
v_a_990_ = lean_ctor_get(v___y_989_, 0);
lean_inc(v_a_990_);
lean_dec_ref_known(v___y_989_, 1);
v_a_973_ = v_a_990_;
goto v___jp_972_;
}
else
{
lean_object* v_a_991_; lean_object* v___x_993_; uint8_t v_isShared_994_; uint8_t v_isSharedCheck_998_; 
lean_dec(v_fuel_964_);
lean_dec_ref(v_e_963_);
v_a_991_ = lean_ctor_get(v___y_989_, 0);
v_isSharedCheck_998_ = !lean_is_exclusive(v___y_989_);
if (v_isSharedCheck_998_ == 0)
{
v___x_993_ = v___y_989_;
v_isShared_994_ = v_isSharedCheck_998_;
goto v_resetjp_992_;
}
else
{
lean_inc(v_a_991_);
lean_dec(v___y_989_);
v___x_993_ = lean_box(0);
v_isShared_994_ = v_isSharedCheck_998_;
goto v_resetjp_992_;
}
v_resetjp_992_:
{
lean_object* v___x_996_; 
if (v_isShared_994_ == 0)
{
v___x_996_ = v___x_993_;
goto v_reusejp_995_;
}
else
{
lean_object* v_reuseFailAlloc_997_; 
v_reuseFailAlloc_997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_997_, 0, v_a_991_);
v___x_996_ = v_reuseFailAlloc_997_;
goto v_reusejp_995_;
}
v_reusejp_995_:
{
return v___x_996_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp___boxed(lean_object* v_rewrites_1010_, lean_object* v_e_1011_, lean_object* v_fuel_1012_, lean_object* v_a_1013_, lean_object* v_a_1014_, lean_object* v_a_1015_, lean_object* v_a_1016_, lean_object* v_a_1017_, lean_object* v_a_1018_, lean_object* v_a_1019_){
_start:
{
lean_object* v_res_1020_; 
v_res_1020_ = l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp(v_rewrites_1010_, v_e_1011_, v_fuel_1012_, v_a_1013_, v_a_1014_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_);
lean_dec(v_a_1018_);
lean_dec_ref(v_a_1017_);
lean_dec(v_a_1016_);
lean_dec_ref(v_a_1015_);
lean_dec(v_a_1014_);
lean_dec_ref(v_a_1013_);
lean_dec_ref(v_rewrites_1010_);
return v_res_1020_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_spec__0(lean_object* v_as_1021_, size_t v_i_1022_, size_t v_stop_1023_, lean_object* v_b_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_){
_start:
{
lean_object* v___x_1032_; 
v___x_1032_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_spec__0___redArg(v_as_1021_, v_i_1022_, v_stop_1023_, v_b_1024_, v___y_1027_, v___y_1028_, v___y_1029_, v___y_1030_);
return v___x_1032_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_spec__0___boxed(lean_object* v_as_1033_, lean_object* v_i_1034_, lean_object* v_stop_1035_, lean_object* v_b_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_){
_start:
{
size_t v_i_boxed_1044_; size_t v_stop_boxed_1045_; lean_object* v_res_1046_; 
v_i_boxed_1044_ = lean_unbox_usize(v_i_1034_);
lean_dec(v_i_1034_);
v_stop_boxed_1045_ = lean_unbox_usize(v_stop_1035_);
lean_dec(v_stop_1035_);
v_res_1046_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_spec__0(v_as_1033_, v_i_boxed_1044_, v_stop_boxed_1045_, v_b_1036_, v___y_1037_, v___y_1038_, v___y_1039_, v___y_1040_, v___y_1041_, v___y_1042_);
lean_dec(v___y_1042_);
lean_dec_ref(v___y_1041_);
lean_dec(v___y_1040_);
lean_dec_ref(v___y_1039_);
lean_dec(v___y_1038_);
lean_dec_ref(v___y_1037_);
lean_dec_ref(v_as_1033_);
return v_res_1046_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply___lam__0(lean_object* v_s_1047_, lean_object* v_a_1048_, lean_object* v_pre_1049_, lean_object* v_u_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_){
_start:
{
lean_object* v___x_1056_; 
lean_inc_ref(v_u_1050_);
v___x_1056_ = l_Lean_Meta_mkEq(v_u_1050_, v_s_1047_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_);
if (lean_obj_tag(v___x_1056_) == 0)
{
lean_object* v_a_1057_; lean_object* v___x_1059_; uint8_t v_isShared_1060_; uint8_t v_isSharedCheck_1088_; 
v_a_1057_ = lean_ctor_get(v___x_1056_, 0);
v_isSharedCheck_1088_ = !lean_is_exclusive(v___x_1056_);
if (v_isSharedCheck_1088_ == 0)
{
v___x_1059_ = v___x_1056_;
v_isShared_1060_ = v_isSharedCheck_1088_;
goto v_resetjp_1058_;
}
else
{
lean_inc(v_a_1057_);
lean_dec(v___x_1056_);
v___x_1059_ = lean_box(0);
v_isShared_1060_ = v_isSharedCheck_1088_;
goto v_resetjp_1058_;
}
v_resetjp_1058_:
{
lean_object* v___x_1061_; lean_object* v___x_1063_; 
v___x_1061_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_LatticeOp_ofProp___closed__2));
if (v_isShared_1060_ == 0)
{
lean_ctor_set_tag(v___x_1059_, 1);
lean_ctor_set(v___x_1059_, 0, v_a_1048_);
v___x_1063_ = v___x_1059_;
goto v_reusejp_1062_;
}
else
{
lean_object* v_reuseFailAlloc_1087_; 
v_reuseFailAlloc_1087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1087_, 0, v_a_1048_);
v___x_1063_ = v_reuseFailAlloc_1087_;
goto v_reusejp_1062_;
}
v_reusejp_1062_:
{
lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; 
v___x_1064_ = lean_box(0);
v___x_1065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1065_, 0, v_a_1057_);
v___x_1066_ = lean_unsigned_to_nat(3u);
v___x_1067_ = lean_mk_empty_array_with_capacity(v___x_1066_);
v___x_1068_ = lean_array_push(v___x_1067_, v___x_1063_);
v___x_1069_ = lean_array_push(v___x_1068_, v___x_1064_);
v___x_1070_ = lean_array_push(v___x_1069_, v___x_1065_);
v___x_1071_ = l_Lean_Meta_mkAppOptM(v___x_1061_, v___x_1070_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_);
if (lean_obj_tag(v___x_1071_) == 0)
{
lean_object* v_a_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; 
v_a_1072_ = lean_ctor_get(v___x_1071_, 0);
lean_inc(v_a_1072_);
lean_dec_ref_known(v___x_1071_, 1);
v___x_1073_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__4));
v___x_1074_ = lean_unsigned_to_nat(2u);
v___x_1075_ = lean_mk_empty_array_with_capacity(v___x_1074_);
v___x_1076_ = lean_array_push(v___x_1075_, v_a_1072_);
v___x_1077_ = lean_array_push(v___x_1076_, v_pre_1049_);
v___x_1078_ = l_Lean_Meta_mkAppM(v___x_1073_, v___x_1077_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_);
if (lean_obj_tag(v___x_1078_) == 0)
{
lean_object* v_a_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; uint8_t v___x_1083_; uint8_t v___x_1084_; uint8_t v___x_1085_; lean_object* v___x_1086_; 
v_a_1079_ = lean_ctor_get(v___x_1078_, 0);
lean_inc(v_a_1079_);
lean_dec_ref_known(v___x_1078_, 1);
v___x_1080_ = lean_unsigned_to_nat(1u);
v___x_1081_ = lean_mk_empty_array_with_capacity(v___x_1080_);
v___x_1082_ = lean_array_push(v___x_1081_, v_u_1050_);
v___x_1083_ = 0;
v___x_1084_ = 1;
v___x_1085_ = 1;
v___x_1086_ = l_Lean_Meta_mkLambdaFVars(v___x_1082_, v_a_1079_, v___x_1083_, v___x_1084_, v___x_1083_, v___x_1084_, v___x_1085_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_);
lean_dec_ref(v___x_1082_);
return v___x_1086_;
}
else
{
lean_dec_ref(v_u_1050_);
return v___x_1078_;
}
}
else
{
lean_dec_ref(v_u_1050_);
lean_dec_ref(v_pre_1049_);
return v___x_1071_;
}
}
}
}
else
{
lean_dec_ref(v_u_1050_);
lean_dec_ref(v_pre_1049_);
lean_dec_ref(v_a_1048_);
return v___x_1056_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply___lam__0___boxed(lean_object* v_s_1089_, lean_object* v_a_1090_, lean_object* v_pre_1091_, lean_object* v_u_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_){
_start:
{
lean_object* v_res_1098_; 
v_res_1098_ = l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply___lam__0(v_s_1089_, v_a_1090_, v_pre_1091_, v_u_1092_, v___y_1093_, v___y_1094_, v___y_1095_, v___y_1096_);
lean_dec(v___y_1096_);
lean_dec_ref(v___y_1095_);
lean_dec(v___y_1094_);
lean_dec_ref(v___y_1093_);
return v_res_1098_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply_spec__0_spec__0___redArg___lam__0(lean_object* v_k_1099_, lean_object* v_b_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_){
_start:
{
lean_object* v___x_1106_; 
lean_inc(v___y_1104_);
lean_inc_ref(v___y_1103_);
lean_inc(v___y_1102_);
lean_inc_ref(v___y_1101_);
v___x_1106_ = lean_apply_6(v_k_1099_, v_b_1100_, v___y_1101_, v___y_1102_, v___y_1103_, v___y_1104_, lean_box(0));
return v___x_1106_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply_spec__0_spec__0___redArg___lam__0___boxed(lean_object* v_k_1107_, lean_object* v_b_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_){
_start:
{
lean_object* v_res_1114_; 
v_res_1114_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply_spec__0_spec__0___redArg___lam__0(v_k_1107_, v_b_1108_, v___y_1109_, v___y_1110_, v___y_1111_, v___y_1112_);
lean_dec(v___y_1112_);
lean_dec_ref(v___y_1111_);
lean_dec(v___y_1110_);
lean_dec_ref(v___y_1109_);
return v_res_1114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply_spec__0_spec__0___redArg(lean_object* v_name_1115_, uint8_t v_bi_1116_, lean_object* v_type_1117_, lean_object* v_k_1118_, uint8_t v_kind_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_){
_start:
{
lean_object* v___f_1125_; lean_object* v___x_1126_; 
v___f_1125_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply_spec__0_spec__0___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1125_, 0, v_k_1118_);
v___x_1126_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1115_, v_bi_1116_, v_type_1117_, v___f_1125_, v_kind_1119_, v___y_1120_, v___y_1121_, v___y_1122_, v___y_1123_);
if (lean_obj_tag(v___x_1126_) == 0)
{
lean_object* v_a_1127_; lean_object* v___x_1129_; uint8_t v_isShared_1130_; uint8_t v_isSharedCheck_1134_; 
v_a_1127_ = lean_ctor_get(v___x_1126_, 0);
v_isSharedCheck_1134_ = !lean_is_exclusive(v___x_1126_);
if (v_isSharedCheck_1134_ == 0)
{
v___x_1129_ = v___x_1126_;
v_isShared_1130_ = v_isSharedCheck_1134_;
goto v_resetjp_1128_;
}
else
{
lean_inc(v_a_1127_);
lean_dec(v___x_1126_);
v___x_1129_ = lean_box(0);
v_isShared_1130_ = v_isSharedCheck_1134_;
goto v_resetjp_1128_;
}
v_resetjp_1128_:
{
lean_object* v___x_1132_; 
if (v_isShared_1130_ == 0)
{
v___x_1132_ = v___x_1129_;
goto v_reusejp_1131_;
}
else
{
lean_object* v_reuseFailAlloc_1133_; 
v_reuseFailAlloc_1133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1133_, 0, v_a_1127_);
v___x_1132_ = v_reuseFailAlloc_1133_;
goto v_reusejp_1131_;
}
v_reusejp_1131_:
{
return v___x_1132_;
}
}
}
else
{
lean_object* v_a_1135_; lean_object* v___x_1137_; uint8_t v_isShared_1138_; uint8_t v_isSharedCheck_1142_; 
v_a_1135_ = lean_ctor_get(v___x_1126_, 0);
v_isSharedCheck_1142_ = !lean_is_exclusive(v___x_1126_);
if (v_isSharedCheck_1142_ == 0)
{
v___x_1137_ = v___x_1126_;
v_isShared_1138_ = v_isSharedCheck_1142_;
goto v_resetjp_1136_;
}
else
{
lean_inc(v_a_1135_);
lean_dec(v___x_1126_);
v___x_1137_ = lean_box(0);
v_isShared_1138_ = v_isSharedCheck_1142_;
goto v_resetjp_1136_;
}
v_resetjp_1136_:
{
lean_object* v___x_1140_; 
if (v_isShared_1138_ == 0)
{
v___x_1140_ = v___x_1137_;
goto v_reusejp_1139_;
}
else
{
lean_object* v_reuseFailAlloc_1141_; 
v_reuseFailAlloc_1141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1141_, 0, v_a_1135_);
v___x_1140_ = v_reuseFailAlloc_1141_;
goto v_reusejp_1139_;
}
v_reusejp_1139_:
{
return v___x_1140_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply_spec__0_spec__0___redArg___boxed(lean_object* v_name_1143_, lean_object* v_bi_1144_, lean_object* v_type_1145_, lean_object* v_k_1146_, lean_object* v_kind_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_){
_start:
{
uint8_t v_bi_boxed_1153_; uint8_t v_kind_boxed_1154_; lean_object* v_res_1155_; 
v_bi_boxed_1153_ = lean_unbox(v_bi_1144_);
v_kind_boxed_1154_ = lean_unbox(v_kind_1147_);
v_res_1155_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply_spec__0_spec__0___redArg(v_name_1143_, v_bi_boxed_1153_, v_type_1145_, v_k_1146_, v_kind_boxed_1154_, v___y_1148_, v___y_1149_, v___y_1150_, v___y_1151_);
lean_dec(v___y_1151_);
lean_dec_ref(v___y_1150_);
lean_dec(v___y_1149_);
lean_dec_ref(v___y_1148_);
return v_res_1155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply_spec__0___redArg(lean_object* v_name_1156_, lean_object* v_type_1157_, lean_object* v_k_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_){
_start:
{
uint8_t v___x_1164_; uint8_t v___x_1165_; lean_object* v___x_1166_; 
v___x_1164_ = 0;
v___x_1165_ = 0;
v___x_1166_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply_spec__0_spec__0___redArg(v_name_1156_, v___x_1164_, v_type_1157_, v_k_1158_, v___x_1165_, v___y_1159_, v___y_1160_, v___y_1161_, v___y_1162_);
return v___x_1166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply_spec__0___redArg___boxed(lean_object* v_name_1167_, lean_object* v_type_1168_, lean_object* v_k_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_){
_start:
{
lean_object* v_res_1175_; 
v_res_1175_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply_spec__0___redArg(v_name_1167_, v_type_1168_, v_k_1169_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_);
lean_dec(v___y_1173_);
lean_dec_ref(v___y_1172_);
lean_dec(v___y_1171_);
lean_dec_ref(v___y_1170_);
return v_res_1175_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply___closed__1(void){
_start:
{
lean_object* v___x_1177_; lean_object* v___x_1178_; 
v___x_1177_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply___closed__0));
v___x_1178_ = l_Lean_stringToMessageData(v___x_1177_);
return v___x_1178_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply(lean_object* v_introThm_1187_, lean_object* v_opAs_1188_, lean_object* v_pre_1189_, lean_object* v_ss_1190_, lean_object* v_a_1191_, lean_object* v_a_1192_, lean_object* v_a_1193_, lean_object* v_a_1194_){
_start:
{
if (lean_obj_tag(v_ss_1190_) == 0)
{
lean_object* v___x_1196_; 
lean_inc(v_introThm_1187_);
v___x_1196_ = l_Lean_Meta_mkConstWithFreshMVarLevels(v_introThm_1187_, v_a_1191_, v_a_1192_, v_a_1193_, v_a_1194_);
if (lean_obj_tag(v___x_1196_) == 0)
{
lean_object* v_a_1197_; lean_object* v___x_1198_; 
v_a_1197_ = lean_ctor_get(v___x_1196_, 0);
lean_inc_n(v_a_1197_, 2);
lean_dec_ref_known(v___x_1196_, 1);
lean_inc(v_a_1194_);
lean_inc_ref(v_a_1193_);
lean_inc(v_a_1192_);
lean_inc_ref(v_a_1191_);
v___x_1198_ = lean_infer_type(v_a_1197_, v_a_1191_, v_a_1192_, v_a_1193_, v_a_1194_);
if (lean_obj_tag(v___x_1198_) == 0)
{
lean_object* v_a_1199_; uint8_t v___x_1200_; lean_object* v___x_1201_; 
v_a_1199_ = lean_ctor_get(v___x_1198_, 0);
lean_inc(v_a_1199_);
lean_dec_ref_known(v___x_1198_, 1);
v___x_1200_ = 0;
v___x_1201_ = l_Lean_Meta_forallMetaTelescope(v_a_1199_, v___x_1200_, v_a_1191_, v_a_1192_, v_a_1193_, v_a_1194_);
if (lean_obj_tag(v___x_1201_) == 0)
{
lean_object* v_a_1202_; lean_object* v___x_1204_; uint8_t v_isShared_1205_; uint8_t v_isSharedCheck_1261_; 
v_a_1202_ = lean_ctor_get(v___x_1201_, 0);
v_isSharedCheck_1261_ = !lean_is_exclusive(v___x_1201_);
if (v_isSharedCheck_1261_ == 0)
{
v___x_1204_ = v___x_1201_;
v_isShared_1205_ = v_isSharedCheck_1261_;
goto v_resetjp_1203_;
}
else
{
lean_inc(v_a_1202_);
lean_dec(v___x_1201_);
v___x_1204_ = lean_box(0);
v_isShared_1205_ = v_isSharedCheck_1261_;
goto v_resetjp_1203_;
}
v_resetjp_1203_:
{
lean_object* v_fst_1206_; lean_object* v_snd_1207_; lean_object* v___x_1209_; uint8_t v_isShared_1210_; uint8_t v_isSharedCheck_1260_; 
v_fst_1206_ = lean_ctor_get(v_a_1202_, 0);
v_snd_1207_ = lean_ctor_get(v_a_1202_, 1);
v_isSharedCheck_1260_ = !lean_is_exclusive(v_a_1202_);
if (v_isSharedCheck_1260_ == 0)
{
v___x_1209_ = v_a_1202_;
v_isShared_1210_ = v_isSharedCheck_1260_;
goto v_resetjp_1208_;
}
else
{
lean_inc(v_snd_1207_);
lean_inc(v_fst_1206_);
lean_dec(v_a_1202_);
v___x_1209_ = lean_box(0);
v_isShared_1210_ = v_isSharedCheck_1260_;
goto v_resetjp_1208_;
}
v_resetjp_1208_:
{
lean_object* v_snd_1216_; lean_object* v___x_1218_; uint8_t v_isShared_1219_; uint8_t v_isSharedCheck_1258_; 
v_snd_1216_ = lean_ctor_get(v_snd_1207_, 1);
v_isSharedCheck_1258_ = !lean_is_exclusive(v_snd_1207_);
if (v_isSharedCheck_1258_ == 0)
{
lean_object* v_unused_1259_; 
v_unused_1259_ = lean_ctor_get(v_snd_1207_, 0);
lean_dec(v_unused_1259_);
v___x_1218_ = v_snd_1207_;
v_isShared_1219_ = v_isSharedCheck_1258_;
goto v_resetjp_1217_;
}
else
{
lean_inc(v_snd_1216_);
lean_dec(v_snd_1207_);
v___x_1218_ = lean_box(0);
v_isShared_1219_ = v_isSharedCheck_1258_;
goto v_resetjp_1217_;
}
v___jp_1211_:
{
lean_object* v___x_1212_; lean_object* v___x_1214_; 
v___x_1212_ = l_Lean_mkAppN(v_a_1197_, v_fst_1206_);
lean_dec(v_fst_1206_);
if (v_isShared_1205_ == 0)
{
lean_ctor_set(v___x_1204_, 0, v___x_1212_);
v___x_1214_ = v___x_1204_;
goto v_reusejp_1213_;
}
else
{
lean_object* v_reuseFailAlloc_1215_; 
v_reuseFailAlloc_1215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1215_, 0, v___x_1212_);
v___x_1214_ = v_reuseFailAlloc_1215_;
goto v_reusejp_1213_;
}
v_reusejp_1213_:
{
return v___x_1214_;
}
}
v_resetjp_1217_:
{
lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; 
v___x_1220_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__2));
v___x_1221_ = lean_unsigned_to_nat(2u);
v___x_1222_ = lean_mk_empty_array_with_capacity(v___x_1221_);
v___x_1223_ = lean_array_push(v___x_1222_, v_pre_1189_);
v___x_1224_ = lean_array_push(v___x_1223_, v_opAs_1188_);
v___x_1225_ = l_Lean_Meta_mkAppM(v___x_1220_, v___x_1224_, v_a_1191_, v_a_1192_, v_a_1193_, v_a_1194_);
if (lean_obj_tag(v___x_1225_) == 0)
{
lean_object* v_a_1226_; lean_object* v___x_1227_; 
v_a_1226_ = lean_ctor_get(v___x_1225_, 0);
lean_inc_n(v_a_1226_, 2);
lean_dec_ref_known(v___x_1225_, 1);
v___x_1227_ = l_Lean_Meta_isExprDefEq(v_snd_1216_, v_a_1226_, v_a_1191_, v_a_1192_, v_a_1193_, v_a_1194_);
if (lean_obj_tag(v___x_1227_) == 0)
{
lean_object* v_a_1228_; uint8_t v___x_1229_; 
v_a_1228_ = lean_ctor_get(v___x_1227_, 0);
lean_inc(v_a_1228_);
lean_dec_ref_known(v___x_1227_, 1);
v___x_1229_ = lean_unbox(v_a_1228_);
lean_dec(v_a_1228_);
if (v___x_1229_ == 0)
{
lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1233_; 
v___x_1230_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__4);
v___x_1231_ = l_Lean_MessageData_ofName(v_introThm_1187_);
if (v_isShared_1219_ == 0)
{
lean_ctor_set_tag(v___x_1218_, 7);
lean_ctor_set(v___x_1218_, 1, v___x_1231_);
lean_ctor_set(v___x_1218_, 0, v___x_1230_);
v___x_1233_ = v___x_1218_;
goto v_reusejp_1232_;
}
else
{
lean_object* v_reuseFailAlloc_1249_; 
v_reuseFailAlloc_1249_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1249_, 0, v___x_1230_);
lean_ctor_set(v_reuseFailAlloc_1249_, 1, v___x_1231_);
v___x_1233_ = v_reuseFailAlloc_1249_;
goto v_reusejp_1232_;
}
v_reusejp_1232_:
{
lean_object* v___x_1234_; lean_object* v___x_1236_; 
v___x_1234_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply___closed__1, &l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply___closed__1_once, _init_l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply___closed__1);
if (v_isShared_1210_ == 0)
{
lean_ctor_set_tag(v___x_1209_, 7);
lean_ctor_set(v___x_1209_, 1, v___x_1234_);
lean_ctor_set(v___x_1209_, 0, v___x_1233_);
v___x_1236_ = v___x_1209_;
goto v_reusejp_1235_;
}
else
{
lean_object* v_reuseFailAlloc_1248_; 
v_reuseFailAlloc_1248_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1248_, 0, v___x_1233_);
lean_ctor_set(v_reuseFailAlloc_1248_, 1, v___x_1234_);
v___x_1236_ = v_reuseFailAlloc_1248_;
goto v_reusejp_1235_;
}
v_reusejp_1235_:
{
lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; 
v___x_1237_ = l_Lean_MessageData_ofExpr(v_a_1226_);
v___x_1238_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1238_, 0, v___x_1236_);
lean_ctor_set(v___x_1238_, 1, v___x_1237_);
v___x_1239_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__1___redArg(v___x_1238_, v_a_1191_, v_a_1192_, v_a_1193_, v_a_1194_);
if (lean_obj_tag(v___x_1239_) == 0)
{
lean_dec_ref_known(v___x_1239_, 1);
goto v___jp_1211_;
}
else
{
lean_object* v_a_1240_; lean_object* v___x_1242_; uint8_t v_isShared_1243_; uint8_t v_isSharedCheck_1247_; 
lean_dec(v_fst_1206_);
lean_del_object(v___x_1204_);
lean_dec(v_a_1197_);
v_a_1240_ = lean_ctor_get(v___x_1239_, 0);
v_isSharedCheck_1247_ = !lean_is_exclusive(v___x_1239_);
if (v_isSharedCheck_1247_ == 0)
{
v___x_1242_ = v___x_1239_;
v_isShared_1243_ = v_isSharedCheck_1247_;
goto v_resetjp_1241_;
}
else
{
lean_inc(v_a_1240_);
lean_dec(v___x_1239_);
v___x_1242_ = lean_box(0);
v_isShared_1243_ = v_isSharedCheck_1247_;
goto v_resetjp_1241_;
}
v_resetjp_1241_:
{
lean_object* v___x_1245_; 
if (v_isShared_1243_ == 0)
{
v___x_1245_ = v___x_1242_;
goto v_reusejp_1244_;
}
else
{
lean_object* v_reuseFailAlloc_1246_; 
v_reuseFailAlloc_1246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1246_, 0, v_a_1240_);
v___x_1245_ = v_reuseFailAlloc_1246_;
goto v_reusejp_1244_;
}
v_reusejp_1244_:
{
return v___x_1245_;
}
}
}
}
}
}
else
{
lean_dec(v_a_1226_);
lean_del_object(v___x_1218_);
lean_del_object(v___x_1209_);
lean_dec(v_introThm_1187_);
goto v___jp_1211_;
}
}
else
{
lean_object* v_a_1250_; lean_object* v___x_1252_; uint8_t v_isShared_1253_; uint8_t v_isSharedCheck_1257_; 
lean_dec(v_a_1226_);
lean_del_object(v___x_1218_);
lean_del_object(v___x_1209_);
lean_dec(v_fst_1206_);
lean_del_object(v___x_1204_);
lean_dec(v_a_1197_);
lean_dec(v_introThm_1187_);
v_a_1250_ = lean_ctor_get(v___x_1227_, 0);
v_isSharedCheck_1257_ = !lean_is_exclusive(v___x_1227_);
if (v_isSharedCheck_1257_ == 0)
{
v___x_1252_ = v___x_1227_;
v_isShared_1253_ = v_isSharedCheck_1257_;
goto v_resetjp_1251_;
}
else
{
lean_inc(v_a_1250_);
lean_dec(v___x_1227_);
v___x_1252_ = lean_box(0);
v_isShared_1253_ = v_isSharedCheck_1257_;
goto v_resetjp_1251_;
}
v_resetjp_1251_:
{
lean_object* v___x_1255_; 
if (v_isShared_1253_ == 0)
{
v___x_1255_ = v___x_1252_;
goto v_reusejp_1254_;
}
else
{
lean_object* v_reuseFailAlloc_1256_; 
v_reuseFailAlloc_1256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1256_, 0, v_a_1250_);
v___x_1255_ = v_reuseFailAlloc_1256_;
goto v_reusejp_1254_;
}
v_reusejp_1254_:
{
return v___x_1255_;
}
}
}
}
else
{
lean_del_object(v___x_1218_);
lean_dec(v_snd_1216_);
lean_del_object(v___x_1209_);
lean_dec(v_fst_1206_);
lean_del_object(v___x_1204_);
lean_dec(v_a_1197_);
lean_dec(v_introThm_1187_);
return v___x_1225_;
}
}
}
}
}
else
{
lean_object* v_a_1262_; lean_object* v___x_1264_; uint8_t v_isShared_1265_; uint8_t v_isSharedCheck_1269_; 
lean_dec(v_a_1197_);
lean_dec_ref(v_pre_1189_);
lean_dec_ref(v_opAs_1188_);
lean_dec(v_introThm_1187_);
v_a_1262_ = lean_ctor_get(v___x_1201_, 0);
v_isSharedCheck_1269_ = !lean_is_exclusive(v___x_1201_);
if (v_isSharedCheck_1269_ == 0)
{
v___x_1264_ = v___x_1201_;
v_isShared_1265_ = v_isSharedCheck_1269_;
goto v_resetjp_1263_;
}
else
{
lean_inc(v_a_1262_);
lean_dec(v___x_1201_);
v___x_1264_ = lean_box(0);
v_isShared_1265_ = v_isSharedCheck_1269_;
goto v_resetjp_1263_;
}
v_resetjp_1263_:
{
lean_object* v___x_1267_; 
if (v_isShared_1265_ == 0)
{
v___x_1267_ = v___x_1264_;
goto v_reusejp_1266_;
}
else
{
lean_object* v_reuseFailAlloc_1268_; 
v_reuseFailAlloc_1268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1268_, 0, v_a_1262_);
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
else
{
lean_dec(v_a_1197_);
lean_dec_ref(v_pre_1189_);
lean_dec_ref(v_opAs_1188_);
lean_dec(v_introThm_1187_);
return v___x_1198_;
}
}
else
{
lean_dec_ref(v_pre_1189_);
lean_dec_ref(v_opAs_1188_);
lean_dec(v_introThm_1187_);
return v___x_1196_;
}
}
else
{
lean_object* v___x_1270_; 
lean_inc(v_a_1194_);
lean_inc_ref(v_a_1193_);
lean_inc(v_a_1192_);
lean_inc_ref(v_a_1191_);
lean_inc_ref(v_pre_1189_);
v___x_1270_ = lean_infer_type(v_pre_1189_, v_a_1191_, v_a_1192_, v_a_1193_, v_a_1194_);
if (lean_obj_tag(v___x_1270_) == 0)
{
lean_object* v_a_1271_; lean_object* v___x_1272_; lean_object* v_s_1273_; lean_object* v___x_1274_; 
v_a_1271_ = lean_ctor_get(v___x_1270_, 0);
lean_inc(v_a_1271_);
lean_dec_ref_known(v___x_1270_, 1);
v___x_1272_ = l_Lean_instInhabitedExpr;
v_s_1273_ = l_List_getLast_x21___redArg(v___x_1272_, v_ss_1190_);
lean_inc(v_a_1194_);
lean_inc_ref(v_a_1193_);
lean_inc(v_a_1192_);
lean_inc_ref(v_a_1191_);
lean_inc(v_s_1273_);
v___x_1274_ = lean_infer_type(v_s_1273_, v_a_1191_, v_a_1192_, v_a_1193_, v_a_1194_);
if (lean_obj_tag(v___x_1274_) == 0)
{
lean_object* v_a_1275_; lean_object* v___f_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; 
v_a_1275_ = lean_ctor_get(v___x_1274_, 0);
lean_inc(v_a_1275_);
lean_dec_ref_known(v___x_1274_, 1);
lean_inc_ref(v_pre_1189_);
lean_inc(v_s_1273_);
v___f_1276_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply___lam__0___boxed), 9, 3);
lean_closure_set(v___f_1276_, 0, v_s_1273_);
lean_closure_set(v___f_1276_, 1, v_a_1271_);
lean_closure_set(v___f_1276_, 2, v_pre_1189_);
v___x_1277_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply___closed__3));
v___x_1278_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply_spec__0___redArg(v___x_1277_, v_a_1275_, v___f_1276_, v_a_1191_, v_a_1192_, v_a_1193_, v_a_1194_);
if (lean_obj_tag(v___x_1278_) == 0)
{
lean_object* v_a_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v_init_1282_; lean_object* v___x_1283_; lean_object* v_Q_1284_; lean_object* v___x_1285_; 
v_a_1279_ = lean_ctor_get(v___x_1278_, 0);
lean_inc(v_a_1279_);
lean_dec_ref_known(v___x_1278_, 1);
v___x_1280_ = lean_array_mk(v_ss_1190_);
v___x_1281_ = lean_array_pop(v___x_1280_);
v_init_1282_ = lean_array_to_list(v___x_1281_);
lean_inc(v_init_1282_);
v___x_1283_ = lean_array_mk(v_init_1282_);
lean_inc_ref(v_opAs_1188_);
v_Q_1284_ = l_Lean_mkAppN(v_opAs_1188_, v___x_1283_);
lean_dec_ref(v___x_1283_);
v___x_1285_ = l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply(v_introThm_1187_, v_opAs_1188_, v_a_1279_, v_init_1282_, v_a_1191_, v_a_1192_, v_a_1193_, v_a_1194_);
if (lean_obj_tag(v___x_1285_) == 0)
{
lean_object* v_a_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; 
v_a_1286_ = lean_ctor_get(v___x_1285_, 0);
lean_inc(v_a_1286_);
lean_dec_ref_known(v___x_1285_, 1);
v___x_1287_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply___closed__5));
v___x_1288_ = lean_unsigned_to_nat(4u);
v___x_1289_ = lean_mk_empty_array_with_capacity(v___x_1288_);
v___x_1290_ = lean_array_push(v___x_1289_, v_s_1273_);
v___x_1291_ = lean_array_push(v___x_1290_, v_pre_1189_);
v___x_1292_ = lean_array_push(v___x_1291_, v_Q_1284_);
v___x_1293_ = lean_array_push(v___x_1292_, v_a_1286_);
v___x_1294_ = l_Lean_Meta_mkAppM(v___x_1287_, v___x_1293_, v_a_1191_, v_a_1192_, v_a_1193_, v_a_1194_);
return v___x_1294_;
}
else
{
lean_dec_ref(v_Q_1284_);
lean_dec(v_s_1273_);
lean_dec_ref(v_pre_1189_);
return v___x_1285_;
}
}
else
{
lean_dec(v_s_1273_);
lean_dec(v_ss_1190_);
lean_dec_ref(v_pre_1189_);
lean_dec_ref(v_opAs_1188_);
lean_dec(v_introThm_1187_);
return v___x_1278_;
}
}
else
{
lean_dec(v_s_1273_);
lean_dec(v_a_1271_);
lean_dec(v_ss_1190_);
lean_dec_ref(v_pre_1189_);
lean_dec_ref(v_opAs_1188_);
lean_dec(v_introThm_1187_);
return v___x_1274_;
}
}
else
{
lean_dec(v_ss_1190_);
lean_dec_ref(v_pre_1189_);
lean_dec_ref(v_opAs_1188_);
lean_dec(v_introThm_1187_);
return v___x_1270_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply___boxed(lean_object* v_introThm_1295_, lean_object* v_opAs_1296_, lean_object* v_pre_1297_, lean_object* v_ss_1298_, lean_object* v_a_1299_, lean_object* v_a_1300_, lean_object* v_a_1301_, lean_object* v_a_1302_, lean_object* v_a_1303_){
_start:
{
lean_object* v_res_1304_; 
v_res_1304_ = l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply(v_introThm_1295_, v_opAs_1296_, v_pre_1297_, v_ss_1298_, v_a_1299_, v_a_1300_, v_a_1301_, v_a_1302_);
lean_dec(v_a_1302_);
lean_dec_ref(v_a_1301_);
lean_dec(v_a_1300_);
lean_dec_ref(v_a_1299_);
return v_res_1304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply_spec__0_spec__0(lean_object* v_00_u03b1_1305_, lean_object* v_name_1306_, uint8_t v_bi_1307_, lean_object* v_type_1308_, lean_object* v_k_1309_, uint8_t v_kind_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_){
_start:
{
lean_object* v___x_1316_; 
v___x_1316_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply_spec__0_spec__0___redArg(v_name_1306_, v_bi_1307_, v_type_1308_, v_k_1309_, v_kind_1310_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_);
return v___x_1316_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1317_, lean_object* v_name_1318_, lean_object* v_bi_1319_, lean_object* v_type_1320_, lean_object* v_k_1321_, lean_object* v_kind_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_){
_start:
{
uint8_t v_bi_boxed_1328_; uint8_t v_kind_boxed_1329_; lean_object* v_res_1330_; 
v_bi_boxed_1328_ = lean_unbox(v_bi_1319_);
v_kind_boxed_1329_ = lean_unbox(v_kind_1322_);
v_res_1330_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply_spec__0_spec__0(v_00_u03b1_1317_, v_name_1318_, v_bi_boxed_1328_, v_type_1320_, v_k_1321_, v_kind_boxed_1329_, v___y_1323_, v___y_1324_, v___y_1325_, v___y_1326_);
lean_dec(v___y_1326_);
lean_dec_ref(v___y_1325_);
lean_dec(v___y_1324_);
lean_dec_ref(v___y_1323_);
return v_res_1330_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply_spec__0(lean_object* v_00_u03b1_1331_, lean_object* v_name_1332_, lean_object* v_type_1333_, lean_object* v_k_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_){
_start:
{
lean_object* v___x_1340_; 
v___x_1340_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply_spec__0___redArg(v_name_1332_, v_type_1333_, v_k_1334_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_);
return v___x_1340_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply_spec__0___boxed(lean_object* v_00_u03b1_1341_, lean_object* v_name_1342_, lean_object* v_type_1343_, lean_object* v_k_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_){
_start:
{
lean_object* v_res_1350_; 
v_res_1350_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply_spec__0(v_00_u03b1_1341_, v_name_1342_, v_type_1343_, v_k_1344_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_);
lean_dec(v___y_1348_);
lean_dec_ref(v___y_1347_);
lean_dec(v___y_1346_);
lean_dec_ref(v___y_1345_);
return v_res_1350_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__0___redArg(size_t v_sz_1351_, size_t v_i_1352_, lean_object* v_bs_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_){
_start:
{
uint8_t v___x_1359_; 
v___x_1359_ = lean_usize_dec_lt(v_i_1352_, v_sz_1351_);
if (v___x_1359_ == 0)
{
lean_object* v___x_1360_; 
v___x_1360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1360_, 0, v_bs_1353_);
return v___x_1360_;
}
else
{
lean_object* v_v_1361_; lean_object* v___x_1362_; lean_object* v_bs_x27_1363_; lean_object* v___y_1365_; lean_object* v___x_1379_; 
v_v_1361_ = lean_array_uget(v_bs_1353_, v_i_1352_);
v___x_1362_ = lean_unsigned_to_nat(0u);
v_bs_x27_1363_ = lean_array_uset(v_bs_1353_, v_i_1352_, v___x_1362_);
lean_inc(v___y_1357_);
lean_inc_ref(v___y_1356_);
lean_inc(v___y_1355_);
lean_inc_ref(v___y_1354_);
v___x_1379_ = lean_infer_type(v_v_1361_, v___y_1354_, v___y_1355_, v___y_1356_, v___y_1357_);
if (lean_obj_tag(v___x_1379_) == 0)
{
lean_object* v_a_1380_; lean_object* v___x_1382_; uint8_t v_isShared_1383_; uint8_t v_isSharedCheck_1390_; 
v_a_1380_ = lean_ctor_get(v___x_1379_, 0);
v_isSharedCheck_1390_ = !lean_is_exclusive(v___x_1379_);
if (v_isSharedCheck_1390_ == 0)
{
v___x_1382_ = v___x_1379_;
v_isShared_1383_ = v_isSharedCheck_1390_;
goto v_resetjp_1381_;
}
else
{
lean_inc(v_a_1380_);
lean_dec(v___x_1379_);
v___x_1382_ = lean_box(0);
v_isShared_1383_ = v_isSharedCheck_1390_;
goto v_resetjp_1381_;
}
v_resetjp_1381_:
{
lean_object* v___x_1385_; 
if (v_isShared_1383_ == 0)
{
lean_ctor_set_tag(v___x_1382_, 1);
v___x_1385_ = v___x_1382_;
goto v_reusejp_1384_;
}
else
{
lean_object* v_reuseFailAlloc_1389_; 
v_reuseFailAlloc_1389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1389_, 0, v_a_1380_);
v___x_1385_ = v_reuseFailAlloc_1389_;
goto v_reusejp_1384_;
}
v_reusejp_1384_:
{
uint8_t v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; 
v___x_1386_ = 0;
v___x_1387_ = lean_box(0);
v___x_1388_ = l_Lean_Meta_mkFreshExprMVar(v___x_1385_, v___x_1386_, v___x_1387_, v___y_1354_, v___y_1355_, v___y_1356_, v___y_1357_);
v___y_1365_ = v___x_1388_;
goto v___jp_1364_;
}
}
}
else
{
v___y_1365_ = v___x_1379_;
goto v___jp_1364_;
}
v___jp_1364_:
{
if (lean_obj_tag(v___y_1365_) == 0)
{
lean_object* v_a_1366_; size_t v___x_1367_; size_t v___x_1368_; lean_object* v___x_1369_; 
v_a_1366_ = lean_ctor_get(v___y_1365_, 0);
lean_inc(v_a_1366_);
lean_dec_ref_known(v___y_1365_, 1);
v___x_1367_ = ((size_t)1ULL);
v___x_1368_ = lean_usize_add(v_i_1352_, v___x_1367_);
v___x_1369_ = lean_array_uset(v_bs_x27_1363_, v_i_1352_, v_a_1366_);
v_i_1352_ = v___x_1368_;
v_bs_1353_ = v___x_1369_;
goto _start;
}
else
{
lean_object* v_a_1371_; lean_object* v___x_1373_; uint8_t v_isShared_1374_; uint8_t v_isSharedCheck_1378_; 
lean_dec_ref(v_bs_x27_1363_);
v_a_1371_ = lean_ctor_get(v___y_1365_, 0);
v_isSharedCheck_1378_ = !lean_is_exclusive(v___y_1365_);
if (v_isSharedCheck_1378_ == 0)
{
v___x_1373_ = v___y_1365_;
v_isShared_1374_ = v_isSharedCheck_1378_;
goto v_resetjp_1372_;
}
else
{
lean_inc(v_a_1371_);
lean_dec(v___y_1365_);
v___x_1373_ = lean_box(0);
v_isShared_1374_ = v_isSharedCheck_1378_;
goto v_resetjp_1372_;
}
v_resetjp_1372_:
{
lean_object* v___x_1376_; 
if (v_isShared_1374_ == 0)
{
v___x_1376_ = v___x_1373_;
goto v_reusejp_1375_;
}
else
{
lean_object* v_reuseFailAlloc_1377_; 
v_reuseFailAlloc_1377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1377_, 0, v_a_1371_);
v___x_1376_ = v_reuseFailAlloc_1377_;
goto v_reusejp_1375_;
}
v_reusejp_1375_:
{
return v___x_1376_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__0___redArg___boxed(lean_object* v_sz_1391_, lean_object* v_i_1392_, lean_object* v_bs_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_){
_start:
{
size_t v_sz_boxed_1399_; size_t v_i_boxed_1400_; lean_object* v_res_1401_; 
v_sz_boxed_1399_ = lean_unbox_usize(v_sz_1391_);
lean_dec(v_sz_1391_);
v_i_boxed_1400_ = lean_unbox_usize(v_i_1392_);
lean_dec(v_i_1392_);
v_res_1401_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__0___redArg(v_sz_boxed_1399_, v_i_boxed_1400_, v_bs_1393_, v___y_1394_, v___y_1395_, v___y_1396_, v___y_1397_);
lean_dec(v___y_1397_);
lean_dec_ref(v___y_1396_);
lean_dec(v___y_1395_);
lean_dec_ref(v___y_1394_);
return v_res_1401_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__1_spec__1___redArg(lean_object* v_a_1402_, lean_object* v_x_1403_){
_start:
{
if (lean_obj_tag(v_x_1403_) == 0)
{
lean_object* v___x_1404_; 
v___x_1404_ = lean_box(0);
return v___x_1404_;
}
else
{
lean_object* v_key_1405_; lean_object* v_value_1406_; lean_object* v_tail_1407_; uint8_t v___x_1408_; 
v_key_1405_ = lean_ctor_get(v_x_1403_, 0);
v_value_1406_ = lean_ctor_get(v_x_1403_, 1);
v_tail_1407_ = lean_ctor_get(v_x_1403_, 2);
v___x_1408_ = lean_name_eq(v_key_1405_, v_a_1402_);
if (v___x_1408_ == 0)
{
v_x_1403_ = v_tail_1407_;
goto _start;
}
else
{
lean_object* v___x_1410_; 
lean_inc(v_value_1406_);
v___x_1410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1410_, 0, v_value_1406_);
return v___x_1410_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__1_spec__1___redArg___boxed(lean_object* v_a_1411_, lean_object* v_x_1412_){
_start:
{
lean_object* v_res_1413_; 
v_res_1413_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__1_spec__1___redArg(v_a_1411_, v_x_1412_);
lean_dec(v_x_1412_);
lean_dec(v_a_1411_);
return v_res_1413_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__1___redArg(lean_object* v_m_1414_, lean_object* v_a_1415_){
_start:
{
lean_object* v_buckets_1416_; lean_object* v___x_1417_; uint64_t v___y_1419_; 
v_buckets_1416_ = lean_ctor_get(v_m_1414_, 1);
v___x_1417_ = lean_array_get_size(v_buckets_1416_);
if (lean_obj_tag(v_a_1415_) == 0)
{
uint64_t v___x_1433_; 
v___x_1433_ = 1723ULL;
v___y_1419_ = v___x_1433_;
goto v___jp_1418_;
}
else
{
uint64_t v_hash_1434_; 
v_hash_1434_ = lean_ctor_get_uint64(v_a_1415_, sizeof(void*)*2);
v___y_1419_ = v_hash_1434_;
goto v___jp_1418_;
}
v___jp_1418_:
{
uint64_t v___x_1420_; uint64_t v___x_1421_; uint64_t v_fold_1422_; uint64_t v___x_1423_; uint64_t v___x_1424_; uint64_t v___x_1425_; size_t v___x_1426_; size_t v___x_1427_; size_t v___x_1428_; size_t v___x_1429_; size_t v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; 
v___x_1420_ = 32ULL;
v___x_1421_ = lean_uint64_shift_right(v___y_1419_, v___x_1420_);
v_fold_1422_ = lean_uint64_xor(v___y_1419_, v___x_1421_);
v___x_1423_ = 16ULL;
v___x_1424_ = lean_uint64_shift_right(v_fold_1422_, v___x_1423_);
v___x_1425_ = lean_uint64_xor(v_fold_1422_, v___x_1424_);
v___x_1426_ = lean_uint64_to_usize(v___x_1425_);
v___x_1427_ = lean_usize_of_nat(v___x_1417_);
v___x_1428_ = ((size_t)1ULL);
v___x_1429_ = lean_usize_sub(v___x_1427_, v___x_1428_);
v___x_1430_ = lean_usize_land(v___x_1426_, v___x_1429_);
v___x_1431_ = lean_array_uget_borrowed(v_buckets_1416_, v___x_1430_);
v___x_1432_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__1_spec__1___redArg(v_a_1415_, v___x_1431_);
return v___x_1432_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__1___redArg___boxed(lean_object* v_m_1435_, lean_object* v_a_1436_){
_start:
{
lean_object* v_res_1437_; 
v_res_1437_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__1___redArg(v_m_1435_, v_a_1436_);
lean_dec(v_a_1436_);
lean_dec_ref(v_m_1435_);
return v_res_1437_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__2___closed__4(void){
_start:
{
lean_object* v___x_1444_; lean_object* v___x_1445_; 
v___x_1444_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__2___closed__3));
v___x_1445_ = l_Lean_stringToMessageData(v___x_1444_);
return v___x_1445_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__2___closed__6(void){
_start:
{
lean_object* v___x_1447_; lean_object* v___x_1448_; 
v___x_1447_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__2___closed__5));
v___x_1448_ = l_Lean_stringToMessageData(v___x_1447_);
return v___x_1448_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__2(lean_object* v_op_1449_, lean_object* v___y_1450_, lean_object* v_a_1451_, lean_object* v_x_1452_, lean_object* v_x_1453_, lean_object* v_x_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_){
_start:
{
lean_object* v_prf_1463_; lean_object* v___y_1464_; lean_object* v___y_1465_; lean_object* v___y_1466_; lean_object* v___y_1467_; 
if (lean_obj_tag(v_x_1452_) == 5)
{
lean_object* v_fn_1484_; lean_object* v_arg_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; 
v_fn_1484_ = lean_ctor_get(v_x_1452_, 0);
lean_inc_ref(v_fn_1484_);
v_arg_1485_ = lean_ctor_get(v_x_1452_, 1);
lean_inc_ref(v_arg_1485_);
lean_dec_ref_known(v_x_1452_, 2);
v___x_1486_ = lean_array_set(v_x_1453_, v_x_1454_, v_arg_1485_);
v___x_1487_ = lean_unsigned_to_nat(1u);
v___x_1488_ = lean_nat_sub(v_x_1454_, v___x_1487_);
lean_dec(v_x_1454_);
v_x_1452_ = v_fn_1484_;
v_x_1453_ = v___x_1486_;
v_x_1454_ = v___x_1488_;
goto _start;
}
else
{
lean_object* v_head_1490_; lean_object* v_numConst_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; size_t v_sz_1494_; size_t v___x_1495_; lean_object* v___x_1496_; 
lean_dec(v_x_1454_);
v_head_1490_ = lean_ctor_get(v_op_1449_, 0);
lean_inc(v_head_1490_);
v_numConst_1491_ = lean_ctor_get(v_op_1449_, 1);
lean_inc_n(v_numConst_1491_, 2);
lean_dec_ref(v_op_1449_);
v___x_1492_ = lean_array_get_size(v_x_1453_);
v___x_1493_ = l_Array_extract___redArg(v_x_1453_, v_numConst_1491_, v___x_1492_);
v_sz_1494_ = lean_array_size(v___x_1493_);
v___x_1495_ = ((size_t)0ULL);
v___x_1496_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__0___redArg(v_sz_1494_, v___x_1495_, v___x_1493_, v___y_1457_, v___y_1458_, v___y_1459_, v___y_1460_);
if (lean_obj_tag(v___x_1496_) == 0)
{
lean_object* v_a_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; 
v_a_1497_ = lean_ctor_get(v___x_1496_, 0);
lean_inc(v_a_1497_);
lean_dec_ref_known(v___x_1496_, 1);
v___x_1498_ = lean_unsigned_to_nat(0u);
v___x_1499_ = l_Array_extract___redArg(v_x_1453_, v___x_1498_, v_numConst_1491_);
lean_dec_ref(v_x_1453_);
v___x_1500_ = l_Array_append___redArg(v___x_1499_, v_a_1497_);
lean_dec(v_a_1497_);
v___x_1501_ = l_Lean_mkAppN(v_x_1452_, v___x_1500_);
lean_dec_ref(v___x_1500_);
v___x_1502_ = lean_unsigned_to_nat(256u);
lean_inc_ref(v___x_1501_);
v___x_1503_ = l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp(v___y_1450_, v___x_1501_, v___x_1502_, v___y_1455_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_, v___y_1460_);
if (lean_obj_tag(v___x_1503_) == 0)
{
lean_object* v_a_1504_; lean_object* v_fst_1505_; lean_object* v_snd_1506_; lean_object* v___x_1508_; uint8_t v_isShared_1509_; uint8_t v_isSharedCheck_1678_; 
v_a_1504_ = lean_ctor_get(v___x_1503_, 0);
lean_inc(v_a_1504_);
lean_dec_ref_known(v___x_1503_, 1);
v_fst_1505_ = lean_ctor_get(v_a_1504_, 0);
v_snd_1506_ = lean_ctor_get(v_a_1504_, 1);
v_isSharedCheck_1678_ = !lean_is_exclusive(v_a_1504_);
if (v_isSharedCheck_1678_ == 0)
{
v___x_1508_ = v_a_1504_;
v_isShared_1509_ = v_isSharedCheck_1678_;
goto v_resetjp_1507_;
}
else
{
lean_inc(v_snd_1506_);
lean_inc(v_fst_1505_);
lean_dec(v_a_1504_);
v___x_1508_ = lean_box(0);
v_isShared_1509_ = v_isSharedCheck_1678_;
goto v_resetjp_1507_;
}
v_resetjp_1507_:
{
lean_object* v___x_1510_; 
lean_inc(v___y_1460_);
lean_inc_ref(v___y_1459_);
lean_inc(v___y_1458_);
lean_inc_ref(v___y_1457_);
v___x_1510_ = lean_infer_type(v___x_1501_, v___y_1457_, v___y_1458_, v___y_1459_, v___y_1460_);
if (lean_obj_tag(v___x_1510_) == 0)
{
lean_object* v_a_1511_; lean_object* v___x_1512_; uint8_t v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; 
v_a_1511_ = lean_ctor_get(v___x_1510_, 0);
lean_inc(v_a_1511_);
lean_dec_ref_known(v___x_1510_, 1);
v___x_1512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1512_, 0, v_a_1511_);
v___x_1513_ = 0;
v___x_1514_ = lean_box(0);
v___x_1515_ = l_Lean_Meta_mkFreshExprMVar(v___x_1512_, v___x_1513_, v___x_1514_, v___y_1457_, v___y_1458_, v___y_1459_, v___y_1460_);
if (lean_obj_tag(v___x_1515_) == 0)
{
lean_object* v_a_1516_; lean_object* v___y_1518_; lean_object* v___y_1519_; lean_object* v___y_1520_; lean_object* v___y_1521_; lean_object* v___y_1522_; lean_object* v___y_1523_; lean_object* v_a_1524_; lean_object* v___y_1572_; lean_object* v_eqProof_1573_; lean_object* v___y_1574_; lean_object* v___y_1575_; lean_object* v___y_1576_; lean_object* v___y_1577_; lean_object* v___x_1605_; lean_object* v___y_1607_; lean_object* v___x_1660_; 
v_a_1516_ = lean_ctor_get(v___x_1515_, 0);
lean_inc(v_a_1516_);
lean_dec_ref_known(v___x_1515_, 1);
v___x_1605_ = l_Lean_Expr_getAppFn(v_fst_1505_);
v___x_1660_ = l_Lean_Expr_constName_x3f(v___x_1605_);
if (lean_obj_tag(v___x_1660_) == 0)
{
v___y_1607_ = v___x_1514_;
goto v___jp_1606_;
}
else
{
lean_object* v_val_1661_; 
v_val_1661_ = lean_ctor_get(v___x_1660_, 0);
lean_inc(v_val_1661_);
lean_dec_ref_known(v___x_1660_, 1);
v___y_1607_ = v_val_1661_;
goto v___jp_1606_;
}
v___jp_1517_:
{
lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; 
v___x_1525_ = lean_unsigned_to_nat(1u);
v___x_1526_ = lean_mk_empty_array_with_capacity(v___x_1525_);
lean_inc_ref(v___x_1526_);
v___x_1527_ = lean_array_push(v___x_1526_, v_a_1516_);
v___x_1528_ = l_Lean_Meta_mkAppM(v___y_1518_, v___x_1527_, v___y_1521_, v___y_1522_, v___y_1523_, v___y_1520_);
if (lean_obj_tag(v___x_1528_) == 0)
{
lean_object* v_a_1529_; lean_object* v___x_1530_; 
v_a_1529_ = lean_ctor_get(v___x_1528_, 0);
lean_inc(v_a_1529_);
lean_dec_ref_known(v___x_1528_, 1);
v___x_1530_ = l_Lean_Meta_mkCongrArg(v_a_1529_, v___y_1519_, v___y_1521_, v___y_1522_, v___y_1523_, v___y_1520_);
if (lean_obj_tag(v___x_1530_) == 0)
{
lean_object* v_a_1531_; lean_object* v___x_1532_; 
v_a_1531_ = lean_ctor_get(v___x_1530_, 0);
lean_inc(v_a_1531_);
lean_dec_ref_known(v___x_1530_, 1);
v___x_1532_ = l_Lean_Meta_mkEqSymm(v_a_1531_, v___y_1521_, v___y_1522_, v___y_1523_, v___y_1520_);
if (lean_obj_tag(v___x_1532_) == 0)
{
lean_object* v_a_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; 
v_a_1533_ = lean_ctor_get(v___x_1532_, 0);
lean_inc(v_a_1533_);
lean_dec_ref_known(v___x_1532_, 1);
v___x_1534_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__2___closed__2));
v___x_1535_ = lean_array_push(v___x_1526_, v_a_1533_);
v___x_1536_ = l_Lean_Meta_mkAppM(v___x_1534_, v___x_1535_, v___y_1521_, v___y_1522_, v___y_1523_, v___y_1520_);
if (lean_obj_tag(v___x_1536_) == 0)
{
lean_object* v_a_1537_; lean_object* v___x_1538_; 
v_a_1537_ = lean_ctor_get(v___x_1536_, 0);
lean_inc(v_a_1537_);
lean_dec_ref_known(v___x_1536_, 1);
v___x_1538_ = l_Lean_Expr_app___override(v_a_1537_, v_a_1524_);
v_prf_1463_ = v___x_1538_;
v___y_1464_ = v___y_1521_;
v___y_1465_ = v___y_1522_;
v___y_1466_ = v___y_1523_;
v___y_1467_ = v___y_1520_;
goto v___jp_1462_;
}
else
{
lean_object* v_a_1539_; lean_object* v___x_1541_; uint8_t v_isShared_1542_; uint8_t v_isSharedCheck_1546_; 
lean_dec_ref(v_a_1524_);
v_a_1539_ = lean_ctor_get(v___x_1536_, 0);
v_isSharedCheck_1546_ = !lean_is_exclusive(v___x_1536_);
if (v_isSharedCheck_1546_ == 0)
{
v___x_1541_ = v___x_1536_;
v_isShared_1542_ = v_isSharedCheck_1546_;
goto v_resetjp_1540_;
}
else
{
lean_inc(v_a_1539_);
lean_dec(v___x_1536_);
v___x_1541_ = lean_box(0);
v_isShared_1542_ = v_isSharedCheck_1546_;
goto v_resetjp_1540_;
}
v_resetjp_1540_:
{
lean_object* v___x_1544_; 
if (v_isShared_1542_ == 0)
{
v___x_1544_ = v___x_1541_;
goto v_reusejp_1543_;
}
else
{
lean_object* v_reuseFailAlloc_1545_; 
v_reuseFailAlloc_1545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1545_, 0, v_a_1539_);
v___x_1544_ = v_reuseFailAlloc_1545_;
goto v_reusejp_1543_;
}
v_reusejp_1543_:
{
return v___x_1544_;
}
}
}
}
else
{
lean_object* v_a_1547_; lean_object* v___x_1549_; uint8_t v_isShared_1550_; uint8_t v_isSharedCheck_1554_; 
lean_dec_ref(v___x_1526_);
lean_dec_ref(v_a_1524_);
v_a_1547_ = lean_ctor_get(v___x_1532_, 0);
v_isSharedCheck_1554_ = !lean_is_exclusive(v___x_1532_);
if (v_isSharedCheck_1554_ == 0)
{
v___x_1549_ = v___x_1532_;
v_isShared_1550_ = v_isSharedCheck_1554_;
goto v_resetjp_1548_;
}
else
{
lean_inc(v_a_1547_);
lean_dec(v___x_1532_);
v___x_1549_ = lean_box(0);
v_isShared_1550_ = v_isSharedCheck_1554_;
goto v_resetjp_1548_;
}
v_resetjp_1548_:
{
lean_object* v___x_1552_; 
if (v_isShared_1550_ == 0)
{
v___x_1552_ = v___x_1549_;
goto v_reusejp_1551_;
}
else
{
lean_object* v_reuseFailAlloc_1553_; 
v_reuseFailAlloc_1553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1553_, 0, v_a_1547_);
v___x_1552_ = v_reuseFailAlloc_1553_;
goto v_reusejp_1551_;
}
v_reusejp_1551_:
{
return v___x_1552_;
}
}
}
}
else
{
lean_object* v_a_1555_; lean_object* v___x_1557_; uint8_t v_isShared_1558_; uint8_t v_isSharedCheck_1562_; 
lean_dec_ref(v___x_1526_);
lean_dec_ref(v_a_1524_);
v_a_1555_ = lean_ctor_get(v___x_1530_, 0);
v_isSharedCheck_1562_ = !lean_is_exclusive(v___x_1530_);
if (v_isSharedCheck_1562_ == 0)
{
v___x_1557_ = v___x_1530_;
v_isShared_1558_ = v_isSharedCheck_1562_;
goto v_resetjp_1556_;
}
else
{
lean_inc(v_a_1555_);
lean_dec(v___x_1530_);
v___x_1557_ = lean_box(0);
v_isShared_1558_ = v_isSharedCheck_1562_;
goto v_resetjp_1556_;
}
v_resetjp_1556_:
{
lean_object* v___x_1560_; 
if (v_isShared_1558_ == 0)
{
v___x_1560_ = v___x_1557_;
goto v_reusejp_1559_;
}
else
{
lean_object* v_reuseFailAlloc_1561_; 
v_reuseFailAlloc_1561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1561_, 0, v_a_1555_);
v___x_1560_ = v_reuseFailAlloc_1561_;
goto v_reusejp_1559_;
}
v_reusejp_1559_:
{
return v___x_1560_;
}
}
}
}
else
{
lean_object* v_a_1563_; lean_object* v___x_1565_; uint8_t v_isShared_1566_; uint8_t v_isSharedCheck_1570_; 
lean_dec_ref(v___x_1526_);
lean_dec_ref(v_a_1524_);
lean_dec_ref(v___y_1519_);
v_a_1563_ = lean_ctor_get(v___x_1528_, 0);
v_isSharedCheck_1570_ = !lean_is_exclusive(v___x_1528_);
if (v_isSharedCheck_1570_ == 0)
{
v___x_1565_ = v___x_1528_;
v_isShared_1566_ = v_isSharedCheck_1570_;
goto v_resetjp_1564_;
}
else
{
lean_inc(v_a_1563_);
lean_dec(v___x_1528_);
v___x_1565_ = lean_box(0);
v_isShared_1566_ = v_isSharedCheck_1570_;
goto v_resetjp_1564_;
}
v_resetjp_1564_:
{
lean_object* v___x_1568_; 
if (v_isShared_1566_ == 0)
{
v___x_1568_ = v___x_1565_;
goto v_reusejp_1567_;
}
else
{
lean_object* v_reuseFailAlloc_1569_; 
v_reuseFailAlloc_1569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1569_, 0, v_a_1563_);
v___x_1568_ = v_reuseFailAlloc_1569_;
goto v_reusejp_1567_;
}
v_reusejp_1567_:
{
return v___x_1568_;
}
}
}
}
v___jp_1571_:
{
lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; 
v___x_1578_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__2));
v___x_1579_ = lean_unsigned_to_nat(2u);
v___x_1580_ = lean_mk_empty_array_with_capacity(v___x_1579_);
lean_inc(v_a_1516_);
v___x_1581_ = lean_array_push(v___x_1580_, v_a_1516_);
v___x_1582_ = lean_array_push(v___x_1581_, v_fst_1505_);
v___x_1583_ = l_Lean_Meta_mkAppM(v___x_1578_, v___x_1582_, v___y_1574_, v___y_1575_, v___y_1576_, v___y_1577_);
if (lean_obj_tag(v___x_1583_) == 0)
{
if (lean_obj_tag(v___y_1572_) == 0)
{
lean_object* v_a_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; 
v_a_1584_ = lean_ctor_get(v___x_1583_, 0);
lean_inc(v_a_1584_);
lean_dec_ref_known(v___x_1583_, 1);
v___x_1585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1585_, 0, v_a_1584_);
v___x_1586_ = l_Lean_Meta_mkFreshExprMVar(v___x_1585_, v___x_1513_, v___x_1514_, v___y_1574_, v___y_1575_, v___y_1576_, v___y_1577_);
if (lean_obj_tag(v___x_1586_) == 0)
{
lean_object* v_a_1587_; 
v_a_1587_ = lean_ctor_get(v___x_1586_, 0);
lean_inc(v_a_1587_);
lean_dec_ref_known(v___x_1586_, 1);
v___y_1518_ = v___x_1578_;
v___y_1519_ = v_eqProof_1573_;
v___y_1520_ = v___y_1577_;
v___y_1521_ = v___y_1574_;
v___y_1522_ = v___y_1575_;
v___y_1523_ = v___y_1576_;
v_a_1524_ = v_a_1587_;
goto v___jp_1517_;
}
else
{
lean_object* v_a_1588_; lean_object* v___x_1590_; uint8_t v_isShared_1591_; uint8_t v_isSharedCheck_1595_; 
lean_dec_ref(v_eqProof_1573_);
lean_dec(v_a_1516_);
v_a_1588_ = lean_ctor_get(v___x_1586_, 0);
v_isSharedCheck_1595_ = !lean_is_exclusive(v___x_1586_);
if (v_isSharedCheck_1595_ == 0)
{
v___x_1590_ = v___x_1586_;
v_isShared_1591_ = v_isSharedCheck_1595_;
goto v_resetjp_1589_;
}
else
{
lean_inc(v_a_1588_);
lean_dec(v___x_1586_);
v___x_1590_ = lean_box(0);
v_isShared_1591_ = v_isSharedCheck_1595_;
goto v_resetjp_1589_;
}
v_resetjp_1589_:
{
lean_object* v___x_1593_; 
if (v_isShared_1591_ == 0)
{
v___x_1593_ = v___x_1590_;
goto v_reusejp_1592_;
}
else
{
lean_object* v_reuseFailAlloc_1594_; 
v_reuseFailAlloc_1594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1594_, 0, v_a_1588_);
v___x_1593_ = v_reuseFailAlloc_1594_;
goto v_reusejp_1592_;
}
v_reusejp_1592_:
{
return v___x_1593_;
}
}
}
}
else
{
lean_object* v_val_1596_; 
lean_dec_ref_known(v___x_1583_, 1);
v_val_1596_ = lean_ctor_get(v___y_1572_, 0);
lean_inc(v_val_1596_);
lean_dec_ref_known(v___y_1572_, 1);
v___y_1518_ = v___x_1578_;
v___y_1519_ = v_eqProof_1573_;
v___y_1520_ = v___y_1577_;
v___y_1521_ = v___y_1574_;
v___y_1522_ = v___y_1575_;
v___y_1523_ = v___y_1576_;
v_a_1524_ = v_val_1596_;
goto v___jp_1517_;
}
}
else
{
lean_object* v_a_1597_; lean_object* v___x_1599_; uint8_t v_isShared_1600_; uint8_t v_isSharedCheck_1604_; 
lean_dec_ref(v_eqProof_1573_);
lean_dec(v___y_1572_);
lean_dec(v_a_1516_);
v_a_1597_ = lean_ctor_get(v___x_1583_, 0);
v_isSharedCheck_1604_ = !lean_is_exclusive(v___x_1583_);
if (v_isSharedCheck_1604_ == 0)
{
v___x_1599_ = v___x_1583_;
v_isShared_1600_ = v_isSharedCheck_1604_;
goto v_resetjp_1598_;
}
else
{
lean_inc(v_a_1597_);
lean_dec(v___x_1583_);
v___x_1599_ = lean_box(0);
v_isShared_1600_ = v_isSharedCheck_1604_;
goto v_resetjp_1598_;
}
v_resetjp_1598_:
{
lean_object* v___x_1602_; 
if (v_isShared_1600_ == 0)
{
v___x_1602_ = v___x_1599_;
goto v_reusejp_1601_;
}
else
{
lean_object* v_reuseFailAlloc_1603_; 
v_reuseFailAlloc_1603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1603_, 0, v_a_1597_);
v___x_1602_ = v_reuseFailAlloc_1603_;
goto v_reusejp_1601_;
}
v_reusejp_1601_:
{
return v___x_1602_;
}
}
}
}
v___jp_1606_:
{
lean_object* v___x_1608_; 
v___x_1608_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__1___redArg(v_a_1451_, v___y_1607_);
lean_dec(v___y_1607_);
if (lean_obj_tag(v___x_1608_) == 0)
{
lean_dec_ref(v___x_1605_);
if (lean_obj_tag(v_snd_1506_) == 0)
{
lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1612_; 
lean_dec(v_a_1516_);
lean_dec(v_fst_1505_);
v___x_1609_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__2___closed__4, &l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__2___closed__4_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__2___closed__4);
v___x_1610_ = l_Lean_MessageData_ofName(v_head_1490_);
if (v_isShared_1509_ == 0)
{
lean_ctor_set_tag(v___x_1508_, 7);
lean_ctor_set(v___x_1508_, 1, v___x_1610_);
lean_ctor_set(v___x_1508_, 0, v___x_1609_);
v___x_1612_ = v___x_1508_;
goto v_reusejp_1611_;
}
else
{
lean_object* v_reuseFailAlloc_1624_; 
v_reuseFailAlloc_1624_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1624_, 0, v___x_1609_);
lean_ctor_set(v_reuseFailAlloc_1624_, 1, v___x_1610_);
v___x_1612_ = v_reuseFailAlloc_1624_;
goto v_reusejp_1611_;
}
v_reusejp_1611_:
{
lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v_a_1616_; lean_object* v___x_1618_; uint8_t v_isShared_1619_; uint8_t v_isSharedCheck_1623_; 
v___x_1613_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__2___closed__6, &l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__2___closed__6_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__2___closed__6);
v___x_1614_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1614_, 0, v___x_1612_);
lean_ctor_set(v___x_1614_, 1, v___x_1613_);
v___x_1615_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_go_spec__0___redArg(v___x_1614_, v___y_1457_, v___y_1458_, v___y_1459_, v___y_1460_);
v_a_1616_ = lean_ctor_get(v___x_1615_, 0);
v_isSharedCheck_1623_ = !lean_is_exclusive(v___x_1615_);
if (v_isSharedCheck_1623_ == 0)
{
v___x_1618_ = v___x_1615_;
v_isShared_1619_ = v_isSharedCheck_1623_;
goto v_resetjp_1617_;
}
else
{
lean_inc(v_a_1616_);
lean_dec(v___x_1615_);
v___x_1618_ = lean_box(0);
v_isShared_1619_ = v_isSharedCheck_1623_;
goto v_resetjp_1617_;
}
v_resetjp_1617_:
{
lean_object* v___x_1621_; 
if (v_isShared_1619_ == 0)
{
v___x_1621_ = v___x_1618_;
goto v_reusejp_1620_;
}
else
{
lean_object* v_reuseFailAlloc_1622_; 
v_reuseFailAlloc_1622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1622_, 0, v_a_1616_);
v___x_1621_ = v_reuseFailAlloc_1622_;
goto v_reusejp_1620_;
}
v_reusejp_1620_:
{
return v___x_1621_;
}
}
}
}
else
{
lean_object* v_val_1625_; lean_object* v___x_1626_; 
lean_del_object(v___x_1508_);
lean_dec(v_head_1490_);
v_val_1625_ = lean_ctor_get(v_snd_1506_, 0);
lean_inc(v_val_1625_);
lean_dec_ref_known(v_snd_1506_, 1);
v___x_1626_ = lean_box(0);
v___y_1572_ = v___x_1626_;
v_eqProof_1573_ = v_val_1625_;
v___y_1574_ = v___y_1457_;
v___y_1575_ = v___y_1458_;
v___y_1576_ = v___y_1459_;
v___y_1577_ = v___y_1460_;
goto v___jp_1571_;
}
}
else
{
lean_object* v_val_1627_; lean_object* v_fst_1628_; lean_object* v_snd_1629_; lean_object* v_dummy_1630_; lean_object* v_nargs_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; 
lean_del_object(v___x_1508_);
lean_dec(v_head_1490_);
v_val_1627_ = lean_ctor_get(v___x_1608_, 0);
lean_inc(v_val_1627_);
lean_dec_ref_known(v___x_1608_, 1);
v_fst_1628_ = lean_ctor_get(v_val_1627_, 0);
lean_inc(v_fst_1628_);
v_snd_1629_ = lean_ctor_get(v_val_1627_, 1);
lean_inc_n(v_snd_1629_, 2);
lean_dec(v_val_1627_);
v_dummy_1630_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_projectsBotOrTop___closed__0, &l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_projectsBotOrTop___closed__0_once, _init_l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_projectsBotOrTop___closed__0);
v_nargs_1631_ = l_Lean_Expr_getAppNumArgs(v_fst_1505_);
lean_inc(v_nargs_1631_);
v___x_1632_ = lean_mk_array(v_nargs_1631_, v_dummy_1630_);
v___x_1633_ = lean_unsigned_to_nat(1u);
v___x_1634_ = lean_nat_sub(v_nargs_1631_, v___x_1633_);
lean_dec(v_nargs_1631_);
lean_inc(v_fst_1505_);
v___x_1635_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_fst_1505_, v___x_1632_, v___x_1634_);
v___x_1636_ = l_Array_extract___redArg(v___x_1635_, v___x_1498_, v_snd_1629_);
v___x_1637_ = l_Lean_mkAppN(v___x_1605_, v___x_1636_);
lean_dec_ref(v___x_1636_);
v___x_1638_ = lean_array_get_size(v___x_1635_);
v___x_1639_ = l_Array_extract___redArg(v___x_1635_, v_snd_1629_, v___x_1638_);
lean_dec_ref(v___x_1635_);
v___x_1640_ = lean_array_to_list(v___x_1639_);
lean_inc(v_a_1516_);
v___x_1641_ = l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkPointFrameApply(v_fst_1628_, v___x_1637_, v_a_1516_, v___x_1640_, v___y_1457_, v___y_1458_, v___y_1459_, v___y_1460_);
if (lean_obj_tag(v___x_1641_) == 0)
{
if (lean_obj_tag(v_snd_1506_) == 0)
{
lean_object* v_a_1642_; 
lean_dec(v_a_1516_);
lean_dec(v_fst_1505_);
v_a_1642_ = lean_ctor_get(v___x_1641_, 0);
lean_inc(v_a_1642_);
lean_dec_ref_known(v___x_1641_, 1);
v_prf_1463_ = v_a_1642_;
v___y_1464_ = v___y_1457_;
v___y_1465_ = v___y_1458_;
v___y_1466_ = v___y_1459_;
v___y_1467_ = v___y_1460_;
goto v___jp_1462_;
}
else
{
lean_object* v_a_1643_; lean_object* v_val_1644_; lean_object* v___x_1646_; uint8_t v_isShared_1647_; uint8_t v_isSharedCheck_1651_; 
v_a_1643_ = lean_ctor_get(v___x_1641_, 0);
lean_inc(v_a_1643_);
lean_dec_ref_known(v___x_1641_, 1);
v_val_1644_ = lean_ctor_get(v_snd_1506_, 0);
v_isSharedCheck_1651_ = !lean_is_exclusive(v_snd_1506_);
if (v_isSharedCheck_1651_ == 0)
{
v___x_1646_ = v_snd_1506_;
v_isShared_1647_ = v_isSharedCheck_1651_;
goto v_resetjp_1645_;
}
else
{
lean_inc(v_val_1644_);
lean_dec(v_snd_1506_);
v___x_1646_ = lean_box(0);
v_isShared_1647_ = v_isSharedCheck_1651_;
goto v_resetjp_1645_;
}
v_resetjp_1645_:
{
lean_object* v___x_1649_; 
if (v_isShared_1647_ == 0)
{
lean_ctor_set(v___x_1646_, 0, v_a_1643_);
v___x_1649_ = v___x_1646_;
goto v_reusejp_1648_;
}
else
{
lean_object* v_reuseFailAlloc_1650_; 
v_reuseFailAlloc_1650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1650_, 0, v_a_1643_);
v___x_1649_ = v_reuseFailAlloc_1650_;
goto v_reusejp_1648_;
}
v_reusejp_1648_:
{
v___y_1572_ = v___x_1649_;
v_eqProof_1573_ = v_val_1644_;
v___y_1574_ = v___y_1457_;
v___y_1575_ = v___y_1458_;
v___y_1576_ = v___y_1459_;
v___y_1577_ = v___y_1460_;
goto v___jp_1571_;
}
}
}
}
else
{
lean_object* v_a_1652_; lean_object* v___x_1654_; uint8_t v_isShared_1655_; uint8_t v_isSharedCheck_1659_; 
lean_dec(v_a_1516_);
lean_dec(v_snd_1506_);
lean_dec(v_fst_1505_);
v_a_1652_ = lean_ctor_get(v___x_1641_, 0);
v_isSharedCheck_1659_ = !lean_is_exclusive(v___x_1641_);
if (v_isSharedCheck_1659_ == 0)
{
v___x_1654_ = v___x_1641_;
v_isShared_1655_ = v_isSharedCheck_1659_;
goto v_resetjp_1653_;
}
else
{
lean_inc(v_a_1652_);
lean_dec(v___x_1641_);
v___x_1654_ = lean_box(0);
v_isShared_1655_ = v_isSharedCheck_1659_;
goto v_resetjp_1653_;
}
v_resetjp_1653_:
{
lean_object* v___x_1657_; 
if (v_isShared_1655_ == 0)
{
v___x_1657_ = v___x_1654_;
goto v_reusejp_1656_;
}
else
{
lean_object* v_reuseFailAlloc_1658_; 
v_reuseFailAlloc_1658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1658_, 0, v_a_1652_);
v___x_1657_ = v_reuseFailAlloc_1658_;
goto v_reusejp_1656_;
}
v_reusejp_1656_:
{
return v___x_1657_;
}
}
}
}
}
}
else
{
lean_object* v_a_1662_; lean_object* v___x_1664_; uint8_t v_isShared_1665_; uint8_t v_isSharedCheck_1669_; 
lean_del_object(v___x_1508_);
lean_dec(v_snd_1506_);
lean_dec(v_fst_1505_);
lean_dec(v_head_1490_);
v_a_1662_ = lean_ctor_get(v___x_1515_, 0);
v_isSharedCheck_1669_ = !lean_is_exclusive(v___x_1515_);
if (v_isSharedCheck_1669_ == 0)
{
v___x_1664_ = v___x_1515_;
v_isShared_1665_ = v_isSharedCheck_1669_;
goto v_resetjp_1663_;
}
else
{
lean_inc(v_a_1662_);
lean_dec(v___x_1515_);
v___x_1664_ = lean_box(0);
v_isShared_1665_ = v_isSharedCheck_1669_;
goto v_resetjp_1663_;
}
v_resetjp_1663_:
{
lean_object* v___x_1667_; 
if (v_isShared_1665_ == 0)
{
v___x_1667_ = v___x_1664_;
goto v_reusejp_1666_;
}
else
{
lean_object* v_reuseFailAlloc_1668_; 
v_reuseFailAlloc_1668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1668_, 0, v_a_1662_);
v___x_1667_ = v_reuseFailAlloc_1668_;
goto v_reusejp_1666_;
}
v_reusejp_1666_:
{
return v___x_1667_;
}
}
}
}
else
{
lean_object* v_a_1670_; lean_object* v___x_1672_; uint8_t v_isShared_1673_; uint8_t v_isSharedCheck_1677_; 
lean_del_object(v___x_1508_);
lean_dec(v_snd_1506_);
lean_dec(v_fst_1505_);
lean_dec(v_head_1490_);
v_a_1670_ = lean_ctor_get(v___x_1510_, 0);
v_isSharedCheck_1677_ = !lean_is_exclusive(v___x_1510_);
if (v_isSharedCheck_1677_ == 0)
{
v___x_1672_ = v___x_1510_;
v_isShared_1673_ = v_isSharedCheck_1677_;
goto v_resetjp_1671_;
}
else
{
lean_inc(v_a_1670_);
lean_dec(v___x_1510_);
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
}
else
{
lean_object* v_a_1679_; lean_object* v___x_1681_; uint8_t v_isShared_1682_; uint8_t v_isSharedCheck_1686_; 
lean_dec_ref(v___x_1501_);
lean_dec(v_head_1490_);
v_a_1679_ = lean_ctor_get(v___x_1503_, 0);
v_isSharedCheck_1686_ = !lean_is_exclusive(v___x_1503_);
if (v_isSharedCheck_1686_ == 0)
{
v___x_1681_ = v___x_1503_;
v_isShared_1682_ = v_isSharedCheck_1686_;
goto v_resetjp_1680_;
}
else
{
lean_inc(v_a_1679_);
lean_dec(v___x_1503_);
v___x_1681_ = lean_box(0);
v_isShared_1682_ = v_isSharedCheck_1686_;
goto v_resetjp_1680_;
}
v_resetjp_1680_:
{
lean_object* v___x_1684_; 
if (v_isShared_1682_ == 0)
{
v___x_1684_ = v___x_1681_;
goto v_reusejp_1683_;
}
else
{
lean_object* v_reuseFailAlloc_1685_; 
v_reuseFailAlloc_1685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1685_, 0, v_a_1679_);
v___x_1684_ = v_reuseFailAlloc_1685_;
goto v_reusejp_1683_;
}
v_reusejp_1683_:
{
return v___x_1684_;
}
}
}
}
else
{
lean_object* v_a_1687_; lean_object* v___x_1689_; uint8_t v_isShared_1690_; uint8_t v_isSharedCheck_1694_; 
lean_dec(v_numConst_1491_);
lean_dec(v_head_1490_);
lean_dec_ref(v_x_1453_);
lean_dec_ref(v_x_1452_);
v_a_1687_ = lean_ctor_get(v___x_1496_, 0);
v_isSharedCheck_1694_ = !lean_is_exclusive(v___x_1496_);
if (v_isSharedCheck_1694_ == 0)
{
v___x_1689_ = v___x_1496_;
v_isShared_1690_ = v_isSharedCheck_1694_;
goto v_resetjp_1688_;
}
else
{
lean_inc(v_a_1687_);
lean_dec(v___x_1496_);
v___x_1689_ = lean_box(0);
v_isShared_1690_ = v_isSharedCheck_1694_;
goto v_resetjp_1688_;
}
v_resetjp_1688_:
{
lean_object* v___x_1692_; 
if (v_isShared_1690_ == 0)
{
v___x_1692_ = v___x_1689_;
goto v_reusejp_1691_;
}
else
{
lean_object* v_reuseFailAlloc_1693_; 
v_reuseFailAlloc_1693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1693_, 0, v_a_1687_);
v___x_1692_ = v_reuseFailAlloc_1693_;
goto v_reusejp_1691_;
}
v_reusejp_1691_:
{
return v___x_1692_;
}
}
}
}
v___jp_1462_:
{
uint8_t v___x_1468_; lean_object* v___x_1469_; 
v___x_1468_ = 1;
v___x_1469_ = l_Lean_Meta_abstractMVars(v_prf_1463_, v___x_1468_, v___y_1464_, v___y_1465_, v___y_1466_, v___y_1467_);
if (lean_obj_tag(v___x_1469_) == 0)
{
lean_object* v_a_1470_; lean_object* v_paramNames_1471_; lean_object* v_expr_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; 
v_a_1470_ = lean_ctor_get(v___x_1469_, 0);
lean_inc(v_a_1470_);
lean_dec_ref_known(v___x_1469_, 1);
v_paramNames_1471_ = lean_ctor_get(v_a_1470_, 0);
lean_inc_ref(v_paramNames_1471_);
v_expr_1472_ = lean_ctor_get(v_a_1470_, 2);
lean_inc_ref(v_expr_1472_);
lean_dec(v_a_1470_);
v___x_1473_ = lean_array_to_list(v_paramNames_1471_);
v___x_1474_ = lean_box(0);
v___x_1475_ = l_Lean_Meta_Sym_mkBackwardRuleFromExpr(v_expr_1472_, v___x_1473_, v___x_1474_, v___y_1464_, v___y_1465_, v___y_1466_, v___y_1467_);
return v___x_1475_;
}
else
{
lean_object* v_a_1476_; lean_object* v___x_1478_; uint8_t v_isShared_1479_; uint8_t v_isSharedCheck_1483_; 
v_a_1476_ = lean_ctor_get(v___x_1469_, 0);
v_isSharedCheck_1483_ = !lean_is_exclusive(v___x_1469_);
if (v_isSharedCheck_1483_ == 0)
{
v___x_1478_ = v___x_1469_;
v_isShared_1479_ = v_isSharedCheck_1483_;
goto v_resetjp_1477_;
}
else
{
lean_inc(v_a_1476_);
lean_dec(v___x_1469_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__2___boxed(lean_object* v_op_1695_, lean_object* v___y_1696_, lean_object* v_a_1697_, lean_object* v_x_1698_, lean_object* v_x_1699_, lean_object* v_x_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_){
_start:
{
lean_object* v_res_1708_; 
v_res_1708_ = l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__2(v_op_1695_, v___y_1696_, v_a_1697_, v_x_1698_, v_x_1699_, v_x_1700_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_, v___y_1706_);
lean_dec(v___y_1706_);
lean_dec_ref(v___y_1705_);
lean_dec(v___y_1704_);
lean_dec_ref(v___y_1703_);
lean_dec(v___y_1702_);
lean_dec_ref(v___y_1701_);
lean_dec_ref(v_a_1697_);
lean_dec_ref(v___y_1696_);
return v_res_1708_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__4(lean_object* v_as_1709_, size_t v_i_1710_, size_t v_stop_1711_, lean_object* v_b_1712_){
_start:
{
uint8_t v___x_1713_; 
v___x_1713_ = lean_usize_dec_eq(v_i_1710_, v_stop_1711_);
if (v___x_1713_ == 0)
{
lean_object* v___x_1714_; lean_object* v_rewrites_1715_; lean_object* v___x_1716_; size_t v___x_1717_; size_t v___x_1718_; 
v___x_1714_ = lean_array_uget_borrowed(v_as_1709_, v_i_1710_);
v_rewrites_1715_ = lean_ctor_get(v___x_1714_, 2);
v___x_1716_ = l_Array_append___redArg(v_b_1712_, v_rewrites_1715_);
v___x_1717_ = ((size_t)1ULL);
v___x_1718_ = lean_usize_add(v_i_1710_, v___x_1717_);
v_i_1710_ = v___x_1718_;
v_b_1712_ = v___x_1716_;
goto _start;
}
else
{
return v_b_1712_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__4___boxed(lean_object* v_as_1720_, lean_object* v_i_1721_, lean_object* v_stop_1722_, lean_object* v_b_1723_){
_start:
{
size_t v_i_boxed_1724_; size_t v_stop_boxed_1725_; lean_object* v_res_1726_; 
v_i_boxed_1724_ = lean_unbox_usize(v_i_1721_);
lean_dec(v_i_1721_);
v_stop_boxed_1725_ = lean_unbox_usize(v_stop_1722_);
lean_dec(v_stop_1722_);
v_res_1726_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__4(v_as_1720_, v_i_boxed_1724_, v_stop_boxed_1725_, v_b_1723_);
lean_dec_ref(v_as_1720_);
return v_res_1726_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__3(lean_object* v_as_1727_, size_t v_i_1728_, size_t v_stop_1729_, lean_object* v_b_1730_){
_start:
{
lean_object* v___y_1732_; uint8_t v___x_1736_; 
v___x_1736_ = lean_usize_dec_eq(v_i_1728_, v_stop_1729_);
if (v___x_1736_ == 0)
{
lean_object* v___x_1737_; lean_object* v_terminal_x3f_1738_; 
v___x_1737_ = lean_array_uget_borrowed(v_as_1727_, v_i_1728_);
v_terminal_x3f_1738_ = lean_ctor_get(v___x_1737_, 3);
if (lean_obj_tag(v_terminal_x3f_1738_) == 0)
{
lean_object* v___x_1739_; lean_object* v___x_1740_; 
v___x_1739_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__3));
v___x_1740_ = l_Array_append___redArg(v_b_1730_, v___x_1739_);
v___y_1732_ = v___x_1740_;
goto v___jp_1731_;
}
else
{
lean_object* v_val_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; 
v_val_1741_ = lean_ctor_get(v_terminal_x3f_1738_, 0);
v___x_1742_ = lean_unsigned_to_nat(1u);
v___x_1743_ = lean_mk_empty_array_with_capacity(v___x_1742_);
lean_inc(v_val_1741_);
v___x_1744_ = lean_array_push(v___x_1743_, v_val_1741_);
v___x_1745_ = l_Array_append___redArg(v_b_1730_, v___x_1744_);
lean_dec_ref(v___x_1744_);
v___y_1732_ = v___x_1745_;
goto v___jp_1731_;
}
}
else
{
return v_b_1730_;
}
v___jp_1731_:
{
size_t v___x_1733_; size_t v___x_1734_; 
v___x_1733_ = ((size_t)1ULL);
v___x_1734_ = lean_usize_add(v_i_1728_, v___x_1733_);
v_i_1728_ = v___x_1734_;
v_b_1730_ = v___y_1732_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__3___boxed(lean_object* v_as_1746_, lean_object* v_i_1747_, lean_object* v_stop_1748_, lean_object* v_b_1749_){
_start:
{
size_t v_i_boxed_1750_; size_t v_stop_boxed_1751_; lean_object* v_res_1752_; 
v_i_boxed_1750_ = lean_unbox_usize(v_i_1747_);
lean_dec(v_i_1747_);
v_stop_boxed_1751_ = lean_unbox_usize(v_stop_1748_);
lean_dec(v_stop_1748_);
v_res_1752_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__3(v_as_1746_, v_i_boxed_1750_, v_stop_boxed_1751_, v_b_1749_);
lean_dec_ref(v_as_1746_);
return v_res_1752_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_mkLatticeOpRule___closed__0(void){
_start:
{
lean_object* v___x_1753_; size_t v___x_1754_; size_t v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; 
v___x_1753_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__3));
v___x_1754_ = lean_usize_once(&l_Lean_Elab_Tactic_VCGen_latticeOps___closed__5, &l_Lean_Elab_Tactic_VCGen_latticeOps___closed__5_once, _init_l_Lean_Elab_Tactic_VCGen_latticeOps___closed__5);
v___x_1755_ = ((size_t)0ULL);
v___x_1756_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_builtinLatticeOps));
v___x_1757_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__3(v___x_1756_, v___x_1755_, v___x_1754_, v___x_1753_);
return v___x_1757_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_mkLatticeOpRule(lean_object* v_rhs_1758_, lean_object* v_op_1759_, lean_object* v_a_1760_, lean_object* v_a_1761_, lean_object* v_a_1762_, lean_object* v_a_1763_, lean_object* v_a_1764_, lean_object* v_a_1765_){
_start:
{
lean_object* v___y_1768_; lean_object* v___y_1769_; lean_object* v___y_1770_; lean_object* v_rewrites_1788_; lean_object* v_terminal_x3f_1789_; lean_object* v___x_1790_; lean_object* v___y_1792_; lean_object* v___y_1793_; lean_object* v___y_1800_; uint8_t v___x_1806_; 
v_rewrites_1788_ = lean_ctor_get(v_op_1759_, 2);
v_terminal_x3f_1789_ = lean_ctor_get(v_op_1759_, 3);
v___x_1790_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_builtinLatticeOps));
v___x_1806_ = lean_uint8_once(&l_Lean_Elab_Tactic_VCGen_latticeOps___closed__3, &l_Lean_Elab_Tactic_VCGen_latticeOps___closed__3_once, _init_l_Lean_Elab_Tactic_VCGen_latticeOps___closed__3);
if (v___x_1806_ == 0)
{
lean_inc_ref(v_rewrites_1788_);
v___y_1800_ = v_rewrites_1788_;
goto v___jp_1799_;
}
else
{
uint8_t v___x_1807_; 
v___x_1807_ = lean_uint8_once(&l_Lean_Elab_Tactic_VCGen_latticeOps___closed__4, &l_Lean_Elab_Tactic_VCGen_latticeOps___closed__4_once, _init_l_Lean_Elab_Tactic_VCGen_latticeOps___closed__4);
if (v___x_1807_ == 0)
{
if (v___x_1806_ == 0)
{
lean_inc_ref(v_rewrites_1788_);
v___y_1800_ = v_rewrites_1788_;
goto v___jp_1799_;
}
else
{
size_t v___x_1808_; size_t v___x_1809_; lean_object* v___x_1810_; 
v___x_1808_ = ((size_t)0ULL);
v___x_1809_ = lean_usize_once(&l_Lean_Elab_Tactic_VCGen_latticeOps___closed__5, &l_Lean_Elab_Tactic_VCGen_latticeOps___closed__5_once, _init_l_Lean_Elab_Tactic_VCGen_latticeOps___closed__5);
lean_inc_ref(v_rewrites_1788_);
v___x_1810_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__4(v___x_1790_, v___x_1808_, v___x_1809_, v_rewrites_1788_);
v___y_1800_ = v___x_1810_;
goto v___jp_1799_;
}
}
else
{
size_t v___x_1811_; size_t v___x_1812_; lean_object* v___x_1813_; 
v___x_1811_ = ((size_t)0ULL);
v___x_1812_ = lean_usize_once(&l_Lean_Elab_Tactic_VCGen_latticeOps___closed__5, &l_Lean_Elab_Tactic_VCGen_latticeOps___closed__5_once, _init_l_Lean_Elab_Tactic_VCGen_latticeOps___closed__5);
lean_inc_ref(v_rewrites_1788_);
v___x_1813_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__4(v___x_1790_, v___x_1811_, v___x_1812_, v_rewrites_1788_);
v___y_1800_ = v___x_1813_;
goto v___jp_1799_;
}
}
v___jp_1767_:
{
lean_object* v___x_1771_; lean_object* v___x_1772_; 
lean_inc_ref(v___y_1769_);
v___x_1771_ = l_Array_append___redArg(v___y_1769_, v___y_1770_);
lean_dec_ref(v___y_1770_);
v___x_1772_ = l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals(v___x_1771_, v_a_1762_, v_a_1763_, v_a_1764_, v_a_1765_);
lean_dec_ref(v___x_1771_);
if (lean_obj_tag(v___x_1772_) == 0)
{
lean_object* v_a_1773_; lean_object* v_dummy_1774_; lean_object* v_nargs_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; 
v_a_1773_ = lean_ctor_get(v___x_1772_, 0);
lean_inc(v_a_1773_);
lean_dec_ref_known(v___x_1772_, 1);
v_dummy_1774_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_projectsBotOrTop___closed__0, &l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_projectsBotOrTop___closed__0_once, _init_l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_projectsBotOrTop___closed__0);
v_nargs_1775_ = l_Lean_Expr_getAppNumArgs(v_rhs_1758_);
lean_inc(v_nargs_1775_);
v___x_1776_ = lean_mk_array(v_nargs_1775_, v_dummy_1774_);
v___x_1777_ = lean_unsigned_to_nat(1u);
v___x_1778_ = lean_nat_sub(v_nargs_1775_, v___x_1777_);
lean_dec(v_nargs_1775_);
v___x_1779_ = l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__2(v_op_1759_, v___y_1768_, v_a_1773_, v_rhs_1758_, v___x_1776_, v___x_1778_, v_a_1760_, v_a_1761_, v_a_1762_, v_a_1763_, v_a_1764_, v_a_1765_);
lean_dec(v_a_1773_);
lean_dec_ref(v___y_1768_);
return v___x_1779_;
}
else
{
lean_object* v_a_1780_; lean_object* v___x_1782_; uint8_t v_isShared_1783_; uint8_t v_isSharedCheck_1787_; 
lean_dec_ref(v___y_1768_);
lean_dec_ref(v_op_1759_);
lean_dec_ref(v_rhs_1758_);
v_a_1780_ = lean_ctor_get(v___x_1772_, 0);
v_isSharedCheck_1787_ = !lean_is_exclusive(v___x_1772_);
if (v_isSharedCheck_1787_ == 0)
{
v___x_1782_ = v___x_1772_;
v_isShared_1783_ = v_isSharedCheck_1787_;
goto v_resetjp_1781_;
}
else
{
lean_inc(v_a_1780_);
lean_dec(v___x_1772_);
v___x_1782_ = lean_box(0);
v_isShared_1783_ = v_isSharedCheck_1787_;
goto v_resetjp_1781_;
}
v_resetjp_1781_:
{
lean_object* v___x_1785_; 
if (v_isShared_1783_ == 0)
{
v___x_1785_ = v___x_1782_;
goto v_reusejp_1784_;
}
else
{
lean_object* v_reuseFailAlloc_1786_; 
v_reuseFailAlloc_1786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1786_, 0, v_a_1780_);
v___x_1785_ = v_reuseFailAlloc_1786_;
goto v_reusejp_1784_;
}
v_reusejp_1784_:
{
return v___x_1785_;
}
}
}
}
v___jp_1791_:
{
if (lean_obj_tag(v_terminal_x3f_1789_) == 0)
{
lean_object* v___x_1794_; 
v___x_1794_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__3));
v___y_1768_ = v___y_1792_;
v___y_1769_ = v___y_1793_;
v___y_1770_ = v___x_1794_;
goto v___jp_1767_;
}
else
{
lean_object* v_val_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; 
v_val_1795_ = lean_ctor_get(v_terminal_x3f_1789_, 0);
v___x_1796_ = lean_unsigned_to_nat(1u);
v___x_1797_ = lean_mk_empty_array_with_capacity(v___x_1796_);
lean_inc(v_val_1795_);
v___x_1798_ = lean_array_push(v___x_1797_, v_val_1795_);
v___y_1768_ = v___y_1792_;
v___y_1769_ = v___y_1793_;
v___y_1770_ = v___x_1798_;
goto v___jp_1767_;
}
}
v___jp_1799_:
{
lean_object* v___x_1801_; uint8_t v___x_1802_; 
v___x_1801_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__3));
v___x_1802_ = lean_uint8_once(&l_Lean_Elab_Tactic_VCGen_latticeOps___closed__3, &l_Lean_Elab_Tactic_VCGen_latticeOps___closed__3_once, _init_l_Lean_Elab_Tactic_VCGen_latticeOps___closed__3);
if (v___x_1802_ == 0)
{
v___y_1792_ = v___y_1800_;
v___y_1793_ = v___x_1801_;
goto v___jp_1791_;
}
else
{
uint8_t v___x_1803_; 
v___x_1803_ = lean_uint8_once(&l_Lean_Elab_Tactic_VCGen_latticeOps___closed__4, &l_Lean_Elab_Tactic_VCGen_latticeOps___closed__4_once, _init_l_Lean_Elab_Tactic_VCGen_latticeOps___closed__4);
if (v___x_1803_ == 0)
{
if (v___x_1802_ == 0)
{
v___y_1792_ = v___y_1800_;
v___y_1793_ = v___x_1801_;
goto v___jp_1791_;
}
else
{
lean_object* v___x_1804_; 
v___x_1804_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_mkLatticeOpRule___closed__0, &l_Lean_Elab_Tactic_VCGen_mkLatticeOpRule___closed__0_once, _init_l_Lean_Elab_Tactic_VCGen_mkLatticeOpRule___closed__0);
v___y_1792_ = v___y_1800_;
v___y_1793_ = v___x_1804_;
goto v___jp_1791_;
}
}
else
{
lean_object* v___x_1805_; 
v___x_1805_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_mkLatticeOpRule___closed__0, &l_Lean_Elab_Tactic_VCGen_mkLatticeOpRule___closed__0_once, _init_l_Lean_Elab_Tactic_VCGen_mkLatticeOpRule___closed__0);
v___y_1792_ = v___y_1800_;
v___y_1793_ = v___x_1805_;
goto v___jp_1791_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_mkLatticeOpRule___boxed(lean_object* v_rhs_1814_, lean_object* v_op_1815_, lean_object* v_a_1816_, lean_object* v_a_1817_, lean_object* v_a_1818_, lean_object* v_a_1819_, lean_object* v_a_1820_, lean_object* v_a_1821_, lean_object* v_a_1822_){
_start:
{
lean_object* v_res_1823_; 
v_res_1823_ = l_Lean_Elab_Tactic_VCGen_mkLatticeOpRule(v_rhs_1814_, v_op_1815_, v_a_1816_, v_a_1817_, v_a_1818_, v_a_1819_, v_a_1820_, v_a_1821_);
lean_dec(v_a_1821_);
lean_dec_ref(v_a_1820_);
lean_dec(v_a_1819_);
lean_dec_ref(v_a_1818_);
lean_dec(v_a_1817_);
lean_dec_ref(v_a_1816_);
return v_res_1823_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__0(size_t v_sz_1824_, size_t v_i_1825_, lean_object* v_bs_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_){
_start:
{
lean_object* v___x_1834_; 
v___x_1834_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__0___redArg(v_sz_1824_, v_i_1825_, v_bs_1826_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_);
return v___x_1834_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__0___boxed(lean_object* v_sz_1835_, lean_object* v_i_1836_, lean_object* v_bs_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_){
_start:
{
size_t v_sz_boxed_1845_; size_t v_i_boxed_1846_; lean_object* v_res_1847_; 
v_sz_boxed_1845_ = lean_unbox_usize(v_sz_1835_);
lean_dec(v_sz_1835_);
v_i_boxed_1846_ = lean_unbox_usize(v_i_1836_);
lean_dec(v_i_1836_);
v_res_1847_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__0(v_sz_boxed_1845_, v_i_boxed_1846_, v_bs_1837_, v___y_1838_, v___y_1839_, v___y_1840_, v___y_1841_, v___y_1842_, v___y_1843_);
lean_dec(v___y_1843_);
lean_dec_ref(v___y_1842_);
lean_dec(v___y_1841_);
lean_dec_ref(v___y_1840_);
lean_dec(v___y_1839_);
lean_dec_ref(v___y_1838_);
return v_res_1847_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__1(lean_object* v_00_u03b2_1848_, lean_object* v_m_1849_, lean_object* v_a_1850_){
_start:
{
lean_object* v___x_1851_; 
v___x_1851_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__1___redArg(v_m_1849_, v_a_1850_);
return v___x_1851_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__1___boxed(lean_object* v_00_u03b2_1852_, lean_object* v_m_1853_, lean_object* v_a_1854_){
_start:
{
lean_object* v_res_1855_; 
v_res_1855_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__1(v_00_u03b2_1852_, v_m_1853_, v_a_1854_);
lean_dec(v_a_1854_);
lean_dec_ref(v_m_1853_);
return v_res_1855_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__1_spec__1(lean_object* v_00_u03b2_1856_, lean_object* v_a_1857_, lean_object* v_x_1858_){
_start:
{
lean_object* v___x_1859_; 
v___x_1859_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__1_spec__1___redArg(v_a_1857_, v_x_1858_);
return v___x_1859_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__1_spec__1___boxed(lean_object* v_00_u03b2_1860_, lean_object* v_a_1861_, lean_object* v_x_1862_){
_start:
{
lean_object* v_res_1863_; 
v_res_1863_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__1_spec__1(v_00_u03b2_1860_, v_a_1861_, v_x_1862_);
lean_dec(v_x_1862_);
lean_dec(v_a_1861_);
return v_res_1863_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_Apply(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_Order_Heyting(uint8_t builtin);
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
