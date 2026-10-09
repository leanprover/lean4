// Lean compiler output
// Module: Lean.Elab.Tactic.VCGen.LatticeOp
// Imports: public import Lean.Meta.Sym.Apply public import Std.Internal.Order.Heyting import Std.Internal.Order.FrameClosure import Lean.Meta.Sym.Simp.Rewrite import Lean.Meta.AppBuilder import Lean.Meta.AbstractMVars public import Lean.Elab.Tactic.VCGen.ExcessArgsFrame
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
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_Lean_Meta_Sym_Simp_SimpM_run_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_mkEqTrans(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Level_isZero(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVar(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Meta_mkConstWithFreshMVarLevels(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallMetaTelescope(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Expr_constName_x3f(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
lean_object* l_Lean_Meta_abstractMVars(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_Meta_Sym_mkBackwardRuleFromExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_extract___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_dischargeNone___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_Theorems_rewrite___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Meta_Sym_Simp_mkTheoremFromDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_Theorems_insert(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAppM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkCongrArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqSymm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* l_Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_new(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_instantiate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_frame(lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
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
static const lean_string_object l_Lean_Elab_Tactic_VCGen_LatticeOp_and___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "And"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_and___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_and___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_and___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_and___closed__0_value),LEAN_SCALAR_PTR_LITERAL(49, 220, 212, 156, 122, 214, 55, 135)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_and___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_and___closed__1_value;
static const lean_array_object l_Lean_Elab_Tactic_VCGen_LatticeOp_and___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_and___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_and___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_LatticeOp_and___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "le_and"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_and___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_and___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_and___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_and___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_and___closed__4_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__2_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_and___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_and___closed__4_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_and___closed__3_value),LEAN_SCALAR_PTR_LITERAL(104, 173, 111, 35, 242, 166, 21, 147)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_and___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_and___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_and___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_and___closed__4_value)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_and___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_and___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_and___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_and___closed__1_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_and___closed__2_value),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_and___closed__5_value),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__0_value)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_and___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_and___closed__6_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_and = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_and___closed__6_value;
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_VCGen_LatticeOp_exists___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_exists___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_VCGen_LatticeOp_exists___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_VCGen_LatticeOp_exists___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_exists___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_exists___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_LatticeOp_exists___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Exists"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_exists___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_exists___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_exists___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_exists___closed__1_value),LEAN_SCALAR_PTR_LITERAL(65, 29, 48, 135, 199, 176, 149, 70)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_exists___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_exists___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_LatticeOp_exists___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "le_exists_prop"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_exists___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_exists___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_exists___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_exists___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_exists___closed__4_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__2_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_exists___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_exists___closed__4_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_exists___closed__3_value),LEAN_SCALAR_PTR_LITERAL(48, 3, 35, 173, 32, 61, 165, 185)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_exists___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_exists___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_exists___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_exists___closed__4_value)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_exists___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_exists___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_exists___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_exists___closed__2_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_and___closed__2_value),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_exists___closed__5_value),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_exists___closed__0_value)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_exists___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_exists___closed__6_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_exists = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_exists___closed__6_value;
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
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_VCGen_LatticeOp_iSup___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_iSup___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_VCGen_LatticeOp_iSup___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_VCGen_LatticeOp_iSup___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_iSup___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_iSup___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_LatticeOp_iSup___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "iSup"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_iSup___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_iSup___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_iSup___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_iSup___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_iSup___closed__2_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__2_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_iSup___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_iSup___closed__2_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_iSup___closed__1_value),LEAN_SCALAR_PTR_LITERAL(46, 241, 153, 184, 251, 59, 2, 100)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_iSup___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_iSup___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_LatticeOp_iSup___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "iSup_apply"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_iSup___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_iSup___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_iSup___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_iSup___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_iSup___closed__4_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__2_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_iSup___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_iSup___closed__4_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_iSup___closed__3_value),LEAN_SCALAR_PTR_LITERAL(49, 98, 179, 55, 4, 208, 18, 213)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_iSup___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_iSup___closed__4_value;
static const lean_array_object l_Lean_Elab_Tactic_VCGen_LatticeOp_iSup___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_iSup___closed__4_value)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_iSup___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_iSup___closed__5_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_LatticeOp_iSup___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "le_iSup_prop"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_iSup___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_iSup___closed__6_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_iSup___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_iSup___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_iSup___closed__7_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__2_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_iSup___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_iSup___closed__7_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_iSup___closed__6_value),LEAN_SCALAR_PTR_LITERAL(131, 21, 231, 15, 10, 24, 171, 200)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_iSup___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_iSup___closed__7_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_iSup___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_iSup___closed__7_value)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_iSup___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_iSup___closed__8_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_LatticeOp_iSup___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_iSup___closed__2_value),((lean_object*)(((size_t)(3) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_iSup___closed__5_value),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_iSup___closed__8_value),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_iSup___closed__0_value)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_iSup___closed__9 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_iSup___closed__9_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_iSup = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_iSup___closed__9_value;
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
static const lean_array_object l_Lean_Elab_Tactic_VCGen_builtinLatticeOps___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*11, .m_other = 0, .m_tag = 246}, .m_size = 11, .m_capacity = 11, .m_data = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__11_value),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_himp___closed__8_value),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_ofProp___closed__9_value),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_top___closed__8_value),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_and___closed__6_value),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_exists___closed__6_value),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__12_value),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_iInf___closed__8_value),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_iSup___closed__9_value),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_fst___closed__19_value),((lean_object*)&l_Lean_Elab_Tactic_VCGen_LatticeOp_snd___closed__11_value)}};
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
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkExcessArgsFrameApply___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = " does not conclude "};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkExcessArgsFrameApply___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkExcessArgsFrameApply___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkExcessArgsFrameApply___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkExcessArgsFrameApply___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkExcessArgsFrameApply(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkExcessArgsFrameApply___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_VCGen_LatticeOp_exists___lam__0(lean_object* v_rhs_144_){
_start:
{
lean_object* v___x_145_; 
v___x_145_ = l_Lean_Expr_getAppFn(v_rhs_144_);
if (lean_obj_tag(v___x_145_) == 4)
{
lean_object* v_us_146_; 
v_us_146_ = lean_ctor_get(v___x_145_, 1);
lean_inc(v_us_146_);
lean_dec_ref_known(v___x_145_, 2);
if (lean_obj_tag(v_us_146_) == 1)
{
lean_object* v_tail_147_; 
v_tail_147_ = lean_ctor_get(v_us_146_, 1);
if (lean_obj_tag(v_tail_147_) == 0)
{
lean_object* v_head_148_; uint8_t v___x_149_; 
v_head_148_ = lean_ctor_get(v_us_146_, 0);
lean_inc(v_head_148_);
lean_dec_ref_known(v_us_146_, 2);
v___x_149_ = l_Lean_Level_isZero(v_head_148_);
lean_dec(v_head_148_);
return v___x_149_;
}
else
{
uint8_t v___x_150_; 
lean_dec_ref_known(v_us_146_, 2);
v___x_150_ = 0;
return v___x_150_;
}
}
else
{
uint8_t v___x_151_; 
lean_dec(v_us_146_);
v___x_151_ = 0;
return v___x_151_;
}
}
else
{
uint8_t v___x_152_; 
lean_dec_ref(v___x_145_);
v___x_152_ = 0;
return v___x_152_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_exists___lam__0___boxed(lean_object* v_rhs_153_){
_start:
{
uint8_t v_res_154_; lean_object* v_r_155_; 
v_res_154_ = l_Lean_Elab_Tactic_VCGen_LatticeOp_exists___lam__0(v_rhs_153_);
lean_dec_ref(v_rhs_153_);
v_r_155_ = lean_box(v_res_154_);
return v_r_155_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_VCGen_LatticeOp_iSup___lam__0(lean_object* v_rhs_243_){
_start:
{
lean_object* v___x_244_; 
v___x_244_ = l_Lean_Expr_getAppFn(v_rhs_243_);
if (lean_obj_tag(v___x_244_) == 4)
{
lean_object* v_us_245_; 
v_us_245_ = lean_ctor_get(v___x_244_, 1);
lean_inc(v_us_245_);
lean_dec_ref_known(v___x_244_, 2);
if (lean_obj_tag(v_us_245_) == 1)
{
lean_object* v_tail_246_; 
v_tail_246_ = lean_ctor_get(v_us_245_, 1);
lean_inc(v_tail_246_);
lean_dec_ref_known(v_us_245_, 2);
if (lean_obj_tag(v_tail_246_) == 1)
{
lean_object* v_tail_247_; 
v_tail_247_ = lean_ctor_get(v_tail_246_, 1);
if (lean_obj_tag(v_tail_247_) == 0)
{
lean_object* v_head_248_; uint8_t v___x_249_; 
v_head_248_ = lean_ctor_get(v_tail_246_, 0);
lean_inc(v_head_248_);
lean_dec_ref_known(v_tail_246_, 2);
v___x_249_ = l_Lean_Level_isZero(v_head_248_);
lean_dec(v_head_248_);
return v___x_249_;
}
else
{
uint8_t v___x_250_; 
lean_dec_ref_known(v_tail_246_, 2);
v___x_250_ = 0;
return v___x_250_;
}
}
else
{
uint8_t v___x_251_; 
lean_dec(v_tail_246_);
v___x_251_ = 0;
return v___x_251_;
}
}
else
{
uint8_t v___x_252_; 
lean_dec(v_us_245_);
v___x_252_ = 0;
return v___x_252_;
}
}
else
{
uint8_t v___x_253_; 
lean_dec_ref(v___x_244_);
v___x_253_ = 0;
return v___x_253_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_LatticeOp_iSup___lam__0___boxed(lean_object* v_rhs_254_){
_start:
{
uint8_t v_res_255_; lean_object* v_r_256_; 
v_res_255_ = l_Lean_Elab_Tactic_VCGen_LatticeOp_iSup___lam__0(v_rhs_254_);
lean_dec_ref(v_rhs_254_);
v_r_256_ = lean_box(v_res_255_);
return v_r_256_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_projectsRewritableOperand___closed__0(void){
_start:
{
lean_object* v___x_286_; lean_object* v_dummy_287_; 
v___x_286_ = lean_box(0);
v_dummy_287_ = l_Lean_Expr_sort___override(v___x_286_);
return v_dummy_287_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_projectsRewritableOperand(lean_object* v_rhs_295_){
_start:
{
lean_object* v_dummy_296_; lean_object* v_nargs_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; uint8_t v___x_304_; 
v_dummy_296_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_projectsRewritableOperand___closed__0, &l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_projectsRewritableOperand___closed__0_once, _init_l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_projectsRewritableOperand___closed__0);
v_nargs_297_ = l_Lean_Expr_getAppNumArgs(v_rhs_295_);
lean_inc(v_nargs_297_);
v___x_298_ = lean_mk_array(v_nargs_297_, v_dummy_296_);
v___x_299_ = lean_unsigned_to_nat(1u);
v___x_300_ = lean_nat_sub(v_nargs_297_, v___x_299_);
lean_dec(v_nargs_297_);
v___x_301_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_rhs_295_, v___x_298_, v___x_300_);
v___x_302_ = lean_unsigned_to_nat(2u);
v___x_303_ = lean_array_get_size(v___x_301_);
v___x_304_ = lean_nat_dec_lt(v___x_302_, v___x_303_);
if (v___x_304_ == 0)
{
lean_dec_ref(v___x_301_);
return v___x_304_;
}
else
{
lean_object* v___x_305_; lean_object* v___x_306_; 
v___x_305_ = lean_array_fget(v___x_301_, v___x_302_);
lean_dec_ref(v___x_301_);
v___x_306_ = l_Lean_Expr_getAppFn(v___x_305_);
if (lean_obj_tag(v___x_306_) == 4)
{
lean_object* v_declName_307_; 
v_declName_307_ = lean_ctor_get(v___x_306_, 0);
lean_inc(v_declName_307_);
lean_dec_ref_known(v___x_306_, 2);
if (lean_obj_tag(v_declName_307_) == 1)
{
lean_object* v_pre_308_; 
v_pre_308_ = lean_ctor_get(v_declName_307_, 0);
lean_inc(v_pre_308_);
if (lean_obj_tag(v_pre_308_) == 1)
{
lean_object* v_pre_309_; 
v_pre_309_ = lean_ctor_get(v_pre_308_, 0);
lean_inc(v_pre_309_);
if (lean_obj_tag(v_pre_309_) == 1)
{
lean_object* v_pre_310_; 
v_pre_310_ = lean_ctor_get(v_pre_309_, 0);
switch(lean_obj_tag(v_pre_310_))
{
case 0:
{
lean_object* v_str_311_; lean_object* v_str_312_; lean_object* v_str_313_; lean_object* v___x_314_; uint8_t v___x_315_; 
lean_dec(v___x_305_);
v_str_311_ = lean_ctor_get(v_declName_307_, 1);
lean_inc_ref(v_str_311_);
lean_dec_ref_known(v_declName_307_, 2);
v_str_312_ = lean_ctor_get(v_pre_308_, 1);
lean_inc_ref(v_str_312_);
lean_dec_ref_known(v_pre_308_, 2);
v_str_313_ = lean_ctor_get(v_pre_309_, 1);
lean_inc_ref(v_str_313_);
lean_dec_ref_known(v_pre_309_, 2);
v___x_314_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__1));
v___x_315_ = lean_string_dec_eq(v_str_313_, v___x_314_);
lean_dec_ref(v_str_313_);
if (v___x_315_ == 0)
{
lean_dec_ref(v_str_312_);
lean_dec_ref(v_str_311_);
return v___x_315_;
}
else
{
lean_object* v___x_316_; uint8_t v___x_317_; 
v___x_316_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__2));
v___x_317_ = lean_string_dec_eq(v_str_312_, v___x_316_);
lean_dec_ref(v_str_312_);
if (v___x_317_ == 0)
{
lean_dec_ref(v_str_311_);
return v___x_317_;
}
else
{
lean_object* v___x_318_; uint8_t v___x_319_; 
v___x_318_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_projectsRewritableOperand___closed__1));
v___x_319_ = lean_string_dec_eq(v_str_311_, v___x_318_);
if (v___x_319_ == 0)
{
lean_object* v___x_320_; uint8_t v___x_321_; 
v___x_320_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_LatticeOp_top___closed__0));
v___x_321_ = lean_string_dec_eq(v_str_311_, v___x_320_);
lean_dec_ref(v_str_311_);
return v___x_321_;
}
else
{
lean_dec_ref(v_str_311_);
return v___x_319_;
}
}
}
}
case 1:
{
lean_object* v_pre_322_; 
lean_inc_ref(v_pre_310_);
v_pre_322_ = lean_ctor_get(v_pre_310_, 0);
if (lean_obj_tag(v_pre_322_) == 0)
{
lean_object* v_str_323_; lean_object* v_str_324_; lean_object* v_str_325_; lean_object* v_str_326_; lean_object* v___x_327_; uint8_t v___x_328_; 
v_str_323_ = lean_ctor_get(v_declName_307_, 1);
lean_inc_ref(v_str_323_);
lean_dec_ref_known(v_declName_307_, 2);
v_str_324_ = lean_ctor_get(v_pre_308_, 1);
lean_inc_ref(v_str_324_);
lean_dec_ref_known(v_pre_308_, 2);
v_str_325_ = lean_ctor_get(v_pre_309_, 1);
lean_inc_ref(v_str_325_);
lean_dec_ref_known(v_pre_309_, 2);
v_str_326_ = lean_ctor_get(v_pre_310_, 1);
lean_inc_ref(v_str_326_);
lean_dec_ref_known(v_pre_310_, 2);
v___x_327_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__1));
v___x_328_ = lean_string_dec_eq(v_str_326_, v___x_327_);
lean_dec_ref(v_str_326_);
if (v___x_328_ == 0)
{
lean_dec_ref(v_str_325_);
lean_dec_ref(v_str_324_);
lean_dec_ref(v_str_323_);
lean_dec(v___x_305_);
return v___x_328_;
}
else
{
lean_object* v___x_329_; uint8_t v___x_330_; 
v___x_329_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_LatticeOp_meet___closed__2));
v___x_330_ = lean_string_dec_eq(v_str_325_, v___x_329_);
lean_dec_ref(v_str_325_);
if (v___x_330_ == 0)
{
lean_dec_ref(v_str_324_);
lean_dec_ref(v_str_323_);
lean_dec(v___x_305_);
return v___x_330_;
}
else
{
lean_object* v___x_331_; uint8_t v___x_332_; 
v___x_331_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__3));
v___x_332_ = lean_string_dec_eq(v_str_324_, v___x_331_);
if (v___x_332_ == 0)
{
lean_object* v___x_333_; uint8_t v___x_334_; 
v___x_333_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__0));
v___x_334_ = lean_string_dec_eq(v_str_324_, v___x_333_);
lean_dec_ref(v_str_324_);
if (v___x_334_ == 0)
{
lean_dec_ref(v_str_323_);
lean_dec(v___x_305_);
return v___x_334_;
}
else
{
lean_object* v___x_335_; uint8_t v___x_336_; 
v___x_335_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_LatticeOp_upperAdjoint___closed__1));
v___x_336_ = lean_string_dec_eq(v_str_323_, v___x_335_);
lean_dec_ref(v_str_323_);
if (v___x_336_ == 0)
{
lean_dec(v___x_305_);
return v___x_336_;
}
else
{
lean_object* v_nargs_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; uint8_t v___x_342_; 
v_nargs_337_ = l_Lean_Expr_getAppNumArgs(v___x_305_);
lean_inc(v_nargs_337_);
v___x_338_ = lean_mk_array(v_nargs_337_, v_dummy_296_);
v___x_339_ = lean_nat_sub(v_nargs_337_, v___x_299_);
lean_dec(v_nargs_337_);
v___x_340_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v___x_305_, v___x_338_, v___x_339_);
v___x_341_ = lean_array_get_size(v___x_340_);
v___x_342_ = lean_nat_dec_lt(v___x_302_, v___x_341_);
if (v___x_342_ == 0)
{
lean_dec_ref(v___x_340_);
return v___x_332_;
}
else
{
lean_object* v___x_343_; lean_object* v___x_344_; uint8_t v___x_345_; 
v___x_343_ = lean_array_fget(v___x_340_, v___x_302_);
lean_dec_ref(v___x_340_);
v___x_344_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_projectsRewritableOperand___closed__3));
v___x_345_ = l_Lean_Expr_isAppOf(v___x_343_, v___x_344_);
lean_dec(v___x_343_);
return v___x_345_;
}
}
}
}
else
{
lean_object* v___x_346_; uint8_t v___x_347_; 
lean_dec_ref(v_str_324_);
lean_dec(v___x_305_);
v___x_346_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_projectsRewritableOperand___closed__2));
v___x_347_ = lean_string_dec_eq(v_str_323_, v___x_346_);
lean_dec_ref(v_str_323_);
return v___x_347_;
}
}
}
}
else
{
uint8_t v___x_348_; 
lean_dec_ref_known(v_pre_310_, 2);
lean_dec_ref_known(v_pre_309_, 2);
lean_dec_ref_known(v_pre_308_, 2);
lean_dec_ref_known(v_declName_307_, 2);
lean_dec(v___x_305_);
v___x_348_ = 0;
return v___x_348_;
}
}
default: 
{
uint8_t v___x_349_; 
lean_dec_ref_known(v_pre_309_, 2);
lean_dec_ref_known(v_pre_308_, 2);
lean_dec_ref_known(v_declName_307_, 2);
lean_dec(v___x_305_);
v___x_349_ = 0;
return v___x_349_;
}
}
}
else
{
uint8_t v___x_350_; 
lean_dec_ref_known(v_pre_308_, 2);
lean_dec(v_pre_309_);
lean_dec_ref_known(v_declName_307_, 2);
lean_dec(v___x_305_);
v___x_350_ = 0;
return v___x_350_;
}
}
else
{
uint8_t v___x_351_; 
lean_dec(v_pre_308_);
lean_dec_ref_known(v_declName_307_, 2);
lean_dec(v___x_305_);
v___x_351_ = 0;
return v___x_351_;
}
}
else
{
uint8_t v___x_352_; 
lean_dec(v_declName_307_);
lean_dec(v___x_305_);
v___x_352_ = 0;
return v___x_352_;
}
}
else
{
uint8_t v___x_353_; 
lean_dec_ref(v___x_306_);
lean_dec(v___x_305_);
v___x_353_ = 0;
return v___x_353_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_projectsRewritableOperand___boxed(lean_object* v_rhs_354_){
_start:
{
uint8_t v_res_355_; lean_object* v_r_356_; 
v_res_355_ = l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_projectsRewritableOperand(v_rhs_354_);
v_r_356_ = lean_box(v_res_355_);
return v_r_356_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0_spec__2___redArg(lean_object* v_a_507_, lean_object* v_b_508_, lean_object* v_x_509_){
_start:
{
if (lean_obj_tag(v_x_509_) == 0)
{
lean_dec(v_b_508_);
lean_dec(v_a_507_);
return v_x_509_;
}
else
{
lean_object* v_key_510_; lean_object* v_value_511_; lean_object* v_tail_512_; lean_object* v___x_514_; uint8_t v_isShared_515_; uint8_t v_isSharedCheck_524_; 
v_key_510_ = lean_ctor_get(v_x_509_, 0);
v_value_511_ = lean_ctor_get(v_x_509_, 1);
v_tail_512_ = lean_ctor_get(v_x_509_, 2);
v_isSharedCheck_524_ = !lean_is_exclusive(v_x_509_);
if (v_isSharedCheck_524_ == 0)
{
v___x_514_ = v_x_509_;
v_isShared_515_ = v_isSharedCheck_524_;
goto v_resetjp_513_;
}
else
{
lean_inc(v_tail_512_);
lean_inc(v_value_511_);
lean_inc(v_key_510_);
lean_dec(v_x_509_);
v___x_514_ = lean_box(0);
v_isShared_515_ = v_isSharedCheck_524_;
goto v_resetjp_513_;
}
v_resetjp_513_:
{
uint8_t v___x_516_; 
v___x_516_ = lean_name_eq(v_key_510_, v_a_507_);
if (v___x_516_ == 0)
{
lean_object* v___x_517_; lean_object* v___x_519_; 
v___x_517_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0_spec__2___redArg(v_a_507_, v_b_508_, v_tail_512_);
if (v_isShared_515_ == 0)
{
lean_ctor_set(v___x_514_, 2, v___x_517_);
v___x_519_ = v___x_514_;
goto v_reusejp_518_;
}
else
{
lean_object* v_reuseFailAlloc_520_; 
v_reuseFailAlloc_520_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_520_, 0, v_key_510_);
lean_ctor_set(v_reuseFailAlloc_520_, 1, v_value_511_);
lean_ctor_set(v_reuseFailAlloc_520_, 2, v___x_517_);
v___x_519_ = v_reuseFailAlloc_520_;
goto v_reusejp_518_;
}
v_reusejp_518_:
{
return v___x_519_;
}
}
else
{
lean_object* v___x_522_; 
lean_dec(v_value_511_);
lean_dec(v_key_510_);
if (v_isShared_515_ == 0)
{
lean_ctor_set(v___x_514_, 1, v_b_508_);
lean_ctor_set(v___x_514_, 0, v_a_507_);
v___x_522_ = v___x_514_;
goto v_reusejp_521_;
}
else
{
lean_object* v_reuseFailAlloc_523_; 
v_reuseFailAlloc_523_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_523_, 0, v_a_507_);
lean_ctor_set(v_reuseFailAlloc_523_, 1, v_b_508_);
lean_ctor_set(v_reuseFailAlloc_523_, 2, v_tail_512_);
v___x_522_ = v_reuseFailAlloc_523_;
goto v_reusejp_521_;
}
v_reusejp_521_:
{
return v___x_522_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0_spec__1_spec__2_spec__4___redArg(lean_object* v_x_525_, lean_object* v_x_526_){
_start:
{
if (lean_obj_tag(v_x_526_) == 0)
{
return v_x_525_;
}
else
{
lean_object* v_key_527_; lean_object* v_value_528_; lean_object* v_tail_529_; lean_object* v___x_531_; uint8_t v_isShared_532_; uint8_t v_isSharedCheck_555_; 
v_key_527_ = lean_ctor_get(v_x_526_, 0);
v_value_528_ = lean_ctor_get(v_x_526_, 1);
v_tail_529_ = lean_ctor_get(v_x_526_, 2);
v_isSharedCheck_555_ = !lean_is_exclusive(v_x_526_);
if (v_isSharedCheck_555_ == 0)
{
v___x_531_ = v_x_526_;
v_isShared_532_ = v_isSharedCheck_555_;
goto v_resetjp_530_;
}
else
{
lean_inc(v_tail_529_);
lean_inc(v_value_528_);
lean_inc(v_key_527_);
lean_dec(v_x_526_);
v___x_531_ = lean_box(0);
v_isShared_532_ = v_isSharedCheck_555_;
goto v_resetjp_530_;
}
v_resetjp_530_:
{
lean_object* v___x_533_; uint64_t v___y_535_; 
v___x_533_ = lean_array_get_size(v_x_525_);
if (lean_obj_tag(v_key_527_) == 0)
{
uint64_t v___x_553_; 
v___x_553_ = 1723ULL;
v___y_535_ = v___x_553_;
goto v___jp_534_;
}
else
{
uint64_t v_hash_554_; 
v_hash_554_ = lean_ctor_get_uint64(v_key_527_, sizeof(void*)*2);
v___y_535_ = v_hash_554_;
goto v___jp_534_;
}
v___jp_534_:
{
uint64_t v___x_536_; uint64_t v___x_537_; uint64_t v_fold_538_; uint64_t v___x_539_; uint64_t v___x_540_; uint64_t v___x_541_; size_t v___x_542_; size_t v___x_543_; size_t v___x_544_; size_t v___x_545_; size_t v___x_546_; lean_object* v___x_547_; lean_object* v___x_549_; 
v___x_536_ = 32ULL;
v___x_537_ = lean_uint64_shift_right(v___y_535_, v___x_536_);
v_fold_538_ = lean_uint64_xor(v___y_535_, v___x_537_);
v___x_539_ = 16ULL;
v___x_540_ = lean_uint64_shift_right(v_fold_538_, v___x_539_);
v___x_541_ = lean_uint64_xor(v_fold_538_, v___x_540_);
v___x_542_ = lean_uint64_to_usize(v___x_541_);
v___x_543_ = lean_usize_of_nat(v___x_533_);
v___x_544_ = ((size_t)1ULL);
v___x_545_ = lean_usize_sub(v___x_543_, v___x_544_);
v___x_546_ = lean_usize_land(v___x_542_, v___x_545_);
v___x_547_ = lean_array_uget_borrowed(v_x_525_, v___x_546_);
lean_inc(v___x_547_);
if (v_isShared_532_ == 0)
{
lean_ctor_set(v___x_531_, 2, v___x_547_);
v___x_549_ = v___x_531_;
goto v_reusejp_548_;
}
else
{
lean_object* v_reuseFailAlloc_552_; 
v_reuseFailAlloc_552_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_552_, 0, v_key_527_);
lean_ctor_set(v_reuseFailAlloc_552_, 1, v_value_528_);
lean_ctor_set(v_reuseFailAlloc_552_, 2, v___x_547_);
v___x_549_ = v_reuseFailAlloc_552_;
goto v_reusejp_548_;
}
v_reusejp_548_:
{
lean_object* v___x_550_; 
v___x_550_ = lean_array_uset(v_x_525_, v___x_546_, v___x_549_);
v_x_525_ = v___x_550_;
v_x_526_ = v_tail_529_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0_spec__1_spec__2___redArg(lean_object* v_i_556_, lean_object* v_source_557_, lean_object* v_target_558_){
_start:
{
lean_object* v___x_559_; uint8_t v___x_560_; 
v___x_559_ = lean_array_get_size(v_source_557_);
v___x_560_ = lean_nat_dec_lt(v_i_556_, v___x_559_);
if (v___x_560_ == 0)
{
lean_dec_ref(v_source_557_);
lean_dec(v_i_556_);
return v_target_558_;
}
else
{
lean_object* v_es_561_; lean_object* v___x_562_; lean_object* v_source_563_; lean_object* v_target_564_; lean_object* v___x_565_; lean_object* v___x_566_; 
v_es_561_ = lean_array_fget(v_source_557_, v_i_556_);
v___x_562_ = lean_box(0);
v_source_563_ = lean_array_fset(v_source_557_, v_i_556_, v___x_562_);
v_target_564_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0_spec__1_spec__2_spec__4___redArg(v_target_558_, v_es_561_);
v___x_565_ = lean_unsigned_to_nat(1u);
v___x_566_ = lean_nat_add(v_i_556_, v___x_565_);
lean_dec(v_i_556_);
v_i_556_ = v___x_566_;
v_source_557_ = v_source_563_;
v_target_558_ = v_target_564_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0_spec__1___redArg(lean_object* v_data_568_){
_start:
{
lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v_nbuckets_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; 
v___x_569_ = lean_array_get_size(v_data_568_);
v___x_570_ = lean_unsigned_to_nat(2u);
v_nbuckets_571_ = lean_nat_mul(v___x_569_, v___x_570_);
v___x_572_ = lean_unsigned_to_nat(0u);
v___x_573_ = lean_box(0);
v___x_574_ = lean_mk_array(v_nbuckets_571_, v___x_573_);
v___x_575_ = lean_array_propagate_mark(v_data_568_, v___x_574_);
v___x_576_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0_spec__1_spec__2___redArg(v___x_572_, v_data_568_, v___x_575_);
return v___x_576_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0_spec__0___redArg(lean_object* v_a_577_, lean_object* v_x_578_){
_start:
{
if (lean_obj_tag(v_x_578_) == 0)
{
uint8_t v___x_579_; 
v___x_579_ = 0;
return v___x_579_;
}
else
{
lean_object* v_key_580_; lean_object* v_tail_581_; uint8_t v___x_582_; 
v_key_580_ = lean_ctor_get(v_x_578_, 0);
v_tail_581_ = lean_ctor_get(v_x_578_, 2);
v___x_582_ = lean_name_eq(v_key_580_, v_a_577_);
if (v___x_582_ == 0)
{
v_x_578_ = v_tail_581_;
goto _start;
}
else
{
return v___x_582_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0_spec__0___redArg___boxed(lean_object* v_a_584_, lean_object* v_x_585_){
_start:
{
uint8_t v_res_586_; lean_object* v_r_587_; 
v_res_586_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0_spec__0___redArg(v_a_584_, v_x_585_);
lean_dec(v_x_585_);
lean_dec(v_a_584_);
v_r_587_ = lean_box(v_res_586_);
return v_r_587_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0___redArg(lean_object* v_m_588_, lean_object* v_a_589_, lean_object* v_b_590_){
_start:
{
lean_object* v_size_591_; lean_object* v_buckets_592_; lean_object* v___x_594_; uint8_t v_isShared_595_; uint8_t v_isSharedCheck_638_; 
v_size_591_ = lean_ctor_get(v_m_588_, 0);
v_buckets_592_ = lean_ctor_get(v_m_588_, 1);
v_isSharedCheck_638_ = !lean_is_exclusive(v_m_588_);
if (v_isSharedCheck_638_ == 0)
{
v___x_594_ = v_m_588_;
v_isShared_595_ = v_isSharedCheck_638_;
goto v_resetjp_593_;
}
else
{
lean_inc(v_buckets_592_);
lean_inc(v_size_591_);
lean_dec(v_m_588_);
v___x_594_ = lean_box(0);
v_isShared_595_ = v_isSharedCheck_638_;
goto v_resetjp_593_;
}
v_resetjp_593_:
{
lean_object* v___x_596_; uint64_t v___y_598_; 
v___x_596_ = lean_array_get_size(v_buckets_592_);
if (lean_obj_tag(v_a_589_) == 0)
{
uint64_t v___x_636_; 
v___x_636_ = 1723ULL;
v___y_598_ = v___x_636_;
goto v___jp_597_;
}
else
{
uint64_t v_hash_637_; 
v_hash_637_ = lean_ctor_get_uint64(v_a_589_, sizeof(void*)*2);
v___y_598_ = v_hash_637_;
goto v___jp_597_;
}
v___jp_597_:
{
uint64_t v___x_599_; uint64_t v___x_600_; uint64_t v_fold_601_; uint64_t v___x_602_; uint64_t v___x_603_; uint64_t v___x_604_; size_t v___x_605_; size_t v___x_606_; size_t v___x_607_; size_t v___x_608_; size_t v___x_609_; lean_object* v_bkt_610_; uint8_t v___x_611_; 
v___x_599_ = 32ULL;
v___x_600_ = lean_uint64_shift_right(v___y_598_, v___x_599_);
v_fold_601_ = lean_uint64_xor(v___y_598_, v___x_600_);
v___x_602_ = 16ULL;
v___x_603_ = lean_uint64_shift_right(v_fold_601_, v___x_602_);
v___x_604_ = lean_uint64_xor(v_fold_601_, v___x_603_);
v___x_605_ = lean_uint64_to_usize(v___x_604_);
v___x_606_ = lean_usize_of_nat(v___x_596_);
v___x_607_ = ((size_t)1ULL);
v___x_608_ = lean_usize_sub(v___x_606_, v___x_607_);
v___x_609_ = lean_usize_land(v___x_605_, v___x_608_);
v_bkt_610_ = lean_array_uget_borrowed(v_buckets_592_, v___x_609_);
v___x_611_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0_spec__0___redArg(v_a_589_, v_bkt_610_);
if (v___x_611_ == 0)
{
lean_object* v___x_612_; lean_object* v_size_x27_613_; lean_object* v___x_614_; lean_object* v_buckets_x27_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; uint8_t v___x_621_; 
v___x_612_ = lean_unsigned_to_nat(1u);
v_size_x27_613_ = lean_nat_add(v_size_591_, v___x_612_);
lean_dec(v_size_591_);
lean_inc(v_bkt_610_);
v___x_614_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_614_, 0, v_a_589_);
lean_ctor_set(v___x_614_, 1, v_b_590_);
lean_ctor_set(v___x_614_, 2, v_bkt_610_);
v_buckets_x27_615_ = lean_array_uset(v_buckets_592_, v___x_609_, v___x_614_);
v___x_616_ = lean_unsigned_to_nat(4u);
v___x_617_ = lean_nat_mul(v_size_x27_613_, v___x_616_);
v___x_618_ = lean_unsigned_to_nat(3u);
v___x_619_ = lean_nat_div(v___x_617_, v___x_618_);
lean_dec(v___x_617_);
v___x_620_ = lean_array_get_size(v_buckets_x27_615_);
v___x_621_ = lean_nat_dec_le(v___x_619_, v___x_620_);
lean_dec(v___x_619_);
if (v___x_621_ == 0)
{
lean_object* v_val_622_; lean_object* v___x_624_; 
v_val_622_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0_spec__1___redArg(v_buckets_x27_615_);
if (v_isShared_595_ == 0)
{
lean_ctor_set(v___x_594_, 1, v_val_622_);
lean_ctor_set(v___x_594_, 0, v_size_x27_613_);
v___x_624_ = v___x_594_;
goto v_reusejp_623_;
}
else
{
lean_object* v_reuseFailAlloc_625_; 
v_reuseFailAlloc_625_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_625_, 0, v_size_x27_613_);
lean_ctor_set(v_reuseFailAlloc_625_, 1, v_val_622_);
v___x_624_ = v_reuseFailAlloc_625_;
goto v_reusejp_623_;
}
v_reusejp_623_:
{
return v___x_624_;
}
}
else
{
lean_object* v___x_627_; 
if (v_isShared_595_ == 0)
{
lean_ctor_set(v___x_594_, 1, v_buckets_x27_615_);
lean_ctor_set(v___x_594_, 0, v_size_x27_613_);
v___x_627_ = v___x_594_;
goto v_reusejp_626_;
}
else
{
lean_object* v_reuseFailAlloc_628_; 
v_reuseFailAlloc_628_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_628_, 0, v_size_x27_613_);
lean_ctor_set(v_reuseFailAlloc_628_, 1, v_buckets_x27_615_);
v___x_627_ = v_reuseFailAlloc_628_;
goto v_reusejp_626_;
}
v_reusejp_626_:
{
return v___x_627_;
}
}
}
else
{
lean_object* v___x_629_; lean_object* v_buckets_x27_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_634_; 
lean_inc(v_bkt_610_);
v___x_629_ = lean_box(0);
v_buckets_x27_630_ = lean_array_uset(v_buckets_592_, v___x_609_, v___x_629_);
v___x_631_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0_spec__2___redArg(v_a_589_, v_b_590_, v_bkt_610_);
v___x_632_ = lean_array_uset(v_buckets_x27_630_, v___x_609_, v___x_631_);
if (v_isShared_595_ == 0)
{
lean_ctor_set(v___x_594_, 1, v___x_632_);
v___x_634_ = v___x_594_;
goto v_reusejp_633_;
}
else
{
lean_object* v_reuseFailAlloc_635_; 
v_reuseFailAlloc_635_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_635_, 0, v_size_591_);
lean_ctor_set(v_reuseFailAlloc_635_, 1, v___x_632_);
v___x_634_ = v_reuseFailAlloc_635_;
goto v_reusejp_633_;
}
v_reusejp_633_:
{
return v___x_634_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__1(lean_object* v_as_639_, size_t v_i_640_, size_t v_stop_641_, lean_object* v_b_642_){
_start:
{
uint8_t v___x_643_; 
v___x_643_ = lean_usize_dec_eq(v_i_640_, v_stop_641_);
if (v___x_643_ == 0)
{
lean_object* v___x_644_; lean_object* v_head_645_; lean_object* v___x_646_; size_t v___x_647_; size_t v___x_648_; 
v___x_644_ = lean_array_uget_borrowed(v_as_639_, v_i_640_);
v_head_645_ = lean_ctor_get(v___x_644_, 0);
lean_inc(v___x_644_);
lean_inc(v_head_645_);
v___x_646_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0___redArg(v_b_642_, v_head_645_, v___x_644_);
v___x_647_ = ((size_t)1ULL);
v___x_648_ = lean_usize_add(v_i_640_, v___x_647_);
v_i_640_ = v___x_648_;
v_b_642_ = v___x_646_;
goto _start;
}
else
{
return v_b_642_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__1___boxed(lean_object* v_as_650_, lean_object* v_i_651_, lean_object* v_stop_652_, lean_object* v_b_653_){
_start:
{
size_t v_i_boxed_654_; size_t v_stop_boxed_655_; lean_object* v_res_656_; 
v_i_boxed_654_ = lean_unbox_usize(v_i_651_);
lean_dec(v_i_651_);
v_stop_boxed_655_ = lean_unbox_usize(v_stop_652_);
lean_dec(v_stop_652_);
v_res_656_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__1(v_as_650_, v_i_boxed_654_, v_stop_boxed_655_, v_b_653_);
lean_dec_ref(v_as_650_);
return v_res_656_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_latticeOps___closed__0(void){
_start:
{
lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; 
v___x_657_ = lean_box(0);
v___x_658_ = lean_unsigned_to_nat(16u);
v___x_659_ = lean_mk_array(v___x_658_, v___x_657_);
return v___x_659_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_latticeOps___closed__1(void){
_start:
{
lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; 
v___x_660_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_latticeOps___closed__0, &l_Lean_Elab_Tactic_VCGen_latticeOps___closed__0_once, _init_l_Lean_Elab_Tactic_VCGen_latticeOps___closed__0);
v___x_661_ = lean_unsigned_to_nat(0u);
v___x_662_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_662_, 0, v___x_661_);
lean_ctor_set(v___x_662_, 1, v___x_660_);
return v___x_662_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_latticeOps___closed__2(void){
_start:
{
lean_object* v___x_663_; lean_object* v___x_664_; 
v___x_663_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_builtinLatticeOps));
v___x_664_ = lean_array_get_size(v___x_663_);
return v___x_664_;
}
}
static uint8_t _init_l_Lean_Elab_Tactic_VCGen_latticeOps___closed__3(void){
_start:
{
lean_object* v___x_665_; lean_object* v___x_666_; uint8_t v___x_667_; 
v___x_665_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_latticeOps___closed__2, &l_Lean_Elab_Tactic_VCGen_latticeOps___closed__2_once, _init_l_Lean_Elab_Tactic_VCGen_latticeOps___closed__2);
v___x_666_ = lean_unsigned_to_nat(0u);
v___x_667_ = lean_nat_dec_lt(v___x_666_, v___x_665_);
return v___x_667_;
}
}
static uint8_t _init_l_Lean_Elab_Tactic_VCGen_latticeOps___closed__4(void){
_start:
{
lean_object* v___x_668_; uint8_t v___x_669_; 
v___x_668_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_latticeOps___closed__2, &l_Lean_Elab_Tactic_VCGen_latticeOps___closed__2_once, _init_l_Lean_Elab_Tactic_VCGen_latticeOps___closed__2);
v___x_669_ = lean_nat_dec_le(v___x_668_, v___x_668_);
return v___x_669_;
}
}
static size_t _init_l_Lean_Elab_Tactic_VCGen_latticeOps___closed__5(void){
_start:
{
lean_object* v___x_670_; size_t v___x_671_; 
v___x_670_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_latticeOps___closed__2, &l_Lean_Elab_Tactic_VCGen_latticeOps___closed__2_once, _init_l_Lean_Elab_Tactic_VCGen_latticeOps___closed__2);
v___x_671_ = lean_usize_of_nat(v___x_670_);
return v___x_671_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_latticeOps___closed__6(void){
_start:
{
lean_object* v___x_672_; size_t v___x_673_; size_t v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; 
v___x_672_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_latticeOps___closed__1, &l_Lean_Elab_Tactic_VCGen_latticeOps___closed__1_once, _init_l_Lean_Elab_Tactic_VCGen_latticeOps___closed__1);
v___x_673_ = lean_usize_once(&l_Lean_Elab_Tactic_VCGen_latticeOps___closed__5, &l_Lean_Elab_Tactic_VCGen_latticeOps___closed__5_once, _init_l_Lean_Elab_Tactic_VCGen_latticeOps___closed__5);
v___x_674_ = ((size_t)0ULL);
v___x_675_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_builtinLatticeOps));
v___x_676_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__1(v___x_675_, v___x_674_, v___x_673_, v___x_672_);
return v___x_676_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_latticeOps(void){
_start:
{
lean_object* v___x_677_; uint8_t v___x_678_; 
v___x_677_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_latticeOps___closed__1, &l_Lean_Elab_Tactic_VCGen_latticeOps___closed__1_once, _init_l_Lean_Elab_Tactic_VCGen_latticeOps___closed__1);
v___x_678_ = lean_uint8_once(&l_Lean_Elab_Tactic_VCGen_latticeOps___closed__3, &l_Lean_Elab_Tactic_VCGen_latticeOps___closed__3_once, _init_l_Lean_Elab_Tactic_VCGen_latticeOps___closed__3);
if (v___x_678_ == 0)
{
return v___x_677_;
}
else
{
uint8_t v___x_679_; 
v___x_679_ = lean_uint8_once(&l_Lean_Elab_Tactic_VCGen_latticeOps___closed__4, &l_Lean_Elab_Tactic_VCGen_latticeOps___closed__4_once, _init_l_Lean_Elab_Tactic_VCGen_latticeOps___closed__4);
if (v___x_679_ == 0)
{
if (v___x_678_ == 0)
{
return v___x_677_;
}
else
{
lean_object* v___x_680_; 
v___x_680_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_latticeOps___closed__6, &l_Lean_Elab_Tactic_VCGen_latticeOps___closed__6_once, _init_l_Lean_Elab_Tactic_VCGen_latticeOps___closed__6);
return v___x_680_;
}
}
else
{
lean_object* v___x_681_; 
v___x_681_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_latticeOps___closed__6, &l_Lean_Elab_Tactic_VCGen_latticeOps___closed__6_once, _init_l_Lean_Elab_Tactic_VCGen_latticeOps___closed__6);
return v___x_681_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0(lean_object* v_00_u03b2_682_, lean_object* v_m_683_, lean_object* v_a_684_, lean_object* v_b_685_){
_start:
{
lean_object* v___x_686_; 
v___x_686_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0___redArg(v_m_683_, v_a_684_, v_b_685_);
return v___x_686_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0_spec__0(lean_object* v_00_u03b2_687_, lean_object* v_a_688_, lean_object* v_x_689_){
_start:
{
uint8_t v___x_690_; 
v___x_690_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0_spec__0___redArg(v_a_688_, v_x_689_);
return v___x_690_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0_spec__0___boxed(lean_object* v_00_u03b2_691_, lean_object* v_a_692_, lean_object* v_x_693_){
_start:
{
uint8_t v_res_694_; lean_object* v_r_695_; 
v_res_694_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0_spec__0(v_00_u03b2_691_, v_a_692_, v_x_693_);
lean_dec(v_x_693_);
lean_dec(v_a_692_);
v_r_695_ = lean_box(v_res_694_);
return v_r_695_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0_spec__1(lean_object* v_00_u03b2_696_, lean_object* v_data_697_){
_start:
{
lean_object* v___x_698_; 
v___x_698_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0_spec__1___redArg(v_data_697_);
return v___x_698_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0_spec__2(lean_object* v_00_u03b2_699_, lean_object* v_a_700_, lean_object* v_b_701_, lean_object* v_x_702_){
_start:
{
lean_object* v___x_703_; 
v___x_703_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0_spec__2___redArg(v_a_700_, v_b_701_, v_x_702_);
return v___x_703_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_704_, lean_object* v_i_705_, lean_object* v_source_706_, lean_object* v_target_707_){
_start:
{
lean_object* v___x_708_; 
v___x_708_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0_spec__1_spec__2___redArg(v_i_705_, v_source_706_, v_target_707_);
return v___x_708_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_709_, lean_object* v_x_710_, lean_object* v_x_711_){
_start:
{
lean_object* v___x_712_; 
v___x_712_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0_spec__1_spec__2_spec__4___redArg(v_x_710_, v_x_711_);
return v___x_712_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__0___redArg(lean_object* v_e_713_, lean_object* v___y_714_){
_start:
{
uint8_t v___x_716_; 
v___x_716_ = l_Lean_Expr_hasMVar(v_e_713_);
if (v___x_716_ == 0)
{
lean_object* v___x_717_; 
v___x_717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_717_, 0, v_e_713_);
return v___x_717_;
}
else
{
lean_object* v___x_718_; lean_object* v_mctx_719_; lean_object* v___x_720_; lean_object* v_fst_721_; lean_object* v_snd_722_; lean_object* v___x_723_; lean_object* v_cache_724_; lean_object* v_zetaDeltaFVarIds_725_; lean_object* v_postponed_726_; lean_object* v_diag_727_; lean_object* v___x_729_; uint8_t v_isShared_730_; uint8_t v_isSharedCheck_736_; 
v___x_718_ = lean_st_ref_get(v___y_714_);
v_mctx_719_ = lean_ctor_get(v___x_718_, 0);
lean_inc_ref(v_mctx_719_);
lean_dec(v___x_718_);
v___x_720_ = l_Lean_instantiateMVarsCore(v_mctx_719_, v_e_713_);
v_fst_721_ = lean_ctor_get(v___x_720_, 0);
lean_inc(v_fst_721_);
v_snd_722_ = lean_ctor_get(v___x_720_, 1);
lean_inc(v_snd_722_);
lean_dec_ref(v___x_720_);
v___x_723_ = lean_st_ref_take(v___y_714_);
v_cache_724_ = lean_ctor_get(v___x_723_, 1);
v_zetaDeltaFVarIds_725_ = lean_ctor_get(v___x_723_, 2);
v_postponed_726_ = lean_ctor_get(v___x_723_, 3);
v_diag_727_ = lean_ctor_get(v___x_723_, 4);
v_isSharedCheck_736_ = !lean_is_exclusive(v___x_723_);
if (v_isSharedCheck_736_ == 0)
{
lean_object* v_unused_737_; 
v_unused_737_ = lean_ctor_get(v___x_723_, 0);
lean_dec(v_unused_737_);
v___x_729_ = v___x_723_;
v_isShared_730_ = v_isSharedCheck_736_;
goto v_resetjp_728_;
}
else
{
lean_inc(v_diag_727_);
lean_inc(v_postponed_726_);
lean_inc(v_zetaDeltaFVarIds_725_);
lean_inc(v_cache_724_);
lean_dec(v___x_723_);
v___x_729_ = lean_box(0);
v_isShared_730_ = v_isSharedCheck_736_;
goto v_resetjp_728_;
}
v_resetjp_728_:
{
lean_object* v___x_732_; 
if (v_isShared_730_ == 0)
{
lean_ctor_set(v___x_729_, 0, v_snd_722_);
v___x_732_ = v___x_729_;
goto v_reusejp_731_;
}
else
{
lean_object* v_reuseFailAlloc_735_; 
v_reuseFailAlloc_735_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_735_, 0, v_snd_722_);
lean_ctor_set(v_reuseFailAlloc_735_, 1, v_cache_724_);
lean_ctor_set(v_reuseFailAlloc_735_, 2, v_zetaDeltaFVarIds_725_);
lean_ctor_set(v_reuseFailAlloc_735_, 3, v_postponed_726_);
lean_ctor_set(v_reuseFailAlloc_735_, 4, v_diag_727_);
v___x_732_ = v_reuseFailAlloc_735_;
goto v_reusejp_731_;
}
v_reusejp_731_:
{
lean_object* v___x_733_; lean_object* v___x_734_; 
v___x_733_ = lean_st_ref_put(v___y_714_, v___x_732_);
v___x_734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_734_, 0, v_fst_721_);
return v___x_734_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__0___redArg___boxed(lean_object* v_e_738_, lean_object* v___y_739_, lean_object* v___y_740_){
_start:
{
lean_object* v_res_741_; 
v_res_741_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__0___redArg(v_e_738_, v___y_739_);
lean_dec(v___y_739_);
return v_res_741_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__0(lean_object* v_e_742_, lean_object* v___y_743_, lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_){
_start:
{
lean_object* v___x_748_; 
v___x_748_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__0___redArg(v_e_742_, v___y_744_);
return v___x_748_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__0___boxed(lean_object* v_e_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_){
_start:
{
lean_object* v_res_755_; 
v_res_755_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__0(v_e_749_, v___y_750_, v___y_751_, v___y_752_, v___y_753_);
lean_dec(v___y_753_);
lean_dec_ref(v___y_752_);
lean_dec(v___y_751_);
lean_dec_ref(v___y_750_);
return v_res_755_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__1_spec__1(lean_object* v_msgData_756_, lean_object* v___y_757_, lean_object* v___y_758_, lean_object* v___y_759_, lean_object* v___y_760_){
_start:
{
lean_object* v___x_762_; lean_object* v_env_763_; uint8_t v___x_764_; lean_object* v_env_765_; lean_object* v___x_766_; lean_object* v_toCold_767_; lean_object* v_mctx_768_; lean_object* v_lctx_769_; lean_object* v_options_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; 
v___x_762_ = lean_st_ref_get(v___y_760_);
v_env_763_ = lean_ctor_get(v___x_762_, 0);
lean_inc_ref(v_env_763_);
lean_dec(v___x_762_);
v___x_764_ = 0;
v_env_765_ = l_Lean_Environment_setRecordingDeps(v_env_763_, v___x_764_);
v___x_766_ = lean_st_ref_get(v___y_758_);
v_toCold_767_ = lean_ctor_get(v___y_759_, 0);
v_mctx_768_ = lean_ctor_get(v___x_766_, 0);
lean_inc_ref(v_mctx_768_);
lean_dec(v___x_766_);
v_lctx_769_ = lean_ctor_get(v___y_757_, 2);
v_options_770_ = lean_ctor_get(v_toCold_767_, 2);
lean_inc_ref(v_options_770_);
lean_inc_ref(v_lctx_769_);
v___x_771_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_771_, 0, v_env_765_);
lean_ctor_set(v___x_771_, 1, v_mctx_768_);
lean_ctor_set(v___x_771_, 2, v_lctx_769_);
lean_ctor_set(v___x_771_, 3, v_options_770_);
v___x_772_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_772_, 0, v___x_771_);
lean_ctor_set(v___x_772_, 1, v_msgData_756_);
v___x_773_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_773_, 0, v___x_772_);
return v___x_773_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__1_spec__1___boxed(lean_object* v_msgData_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_){
_start:
{
lean_object* v_res_780_; 
v_res_780_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__1_spec__1(v_msgData_774_, v___y_775_, v___y_776_, v___y_777_, v___y_778_);
lean_dec(v___y_778_);
lean_dec_ref(v___y_777_);
lean_dec(v___y_776_);
lean_dec_ref(v___y_775_);
return v_res_780_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__1___redArg(lean_object* v_msg_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_){
_start:
{
lean_object* v_ref_787_; lean_object* v___x_788_; lean_object* v_a_789_; lean_object* v___x_791_; uint8_t v_isShared_792_; uint8_t v_isSharedCheck_797_; 
v_ref_787_ = lean_ctor_get(v___y_784_, 2);
v___x_788_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__1_spec__1(v_msg_781_, v___y_782_, v___y_783_, v___y_784_, v___y_785_);
v_a_789_ = lean_ctor_get(v___x_788_, 0);
v_isSharedCheck_797_ = !lean_is_exclusive(v___x_788_);
if (v_isSharedCheck_797_ == 0)
{
v___x_791_ = v___x_788_;
v_isShared_792_ = v_isSharedCheck_797_;
goto v_resetjp_790_;
}
else
{
lean_inc(v_a_789_);
lean_dec(v___x_788_);
v___x_791_ = lean_box(0);
v_isShared_792_ = v_isSharedCheck_797_;
goto v_resetjp_790_;
}
v_resetjp_790_:
{
lean_object* v___x_793_; lean_object* v___x_795_; 
lean_inc(v_ref_787_);
v___x_793_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_793_, 0, v_ref_787_);
lean_ctor_set(v___x_793_, 1, v_a_789_);
if (v_isShared_792_ == 0)
{
lean_ctor_set_tag(v___x_791_, 1);
lean_ctor_set(v___x_791_, 0, v___x_793_);
v___x_795_ = v___x_791_;
goto v_reusejp_794_;
}
else
{
lean_object* v_reuseFailAlloc_796_; 
v_reuseFailAlloc_796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_796_, 0, v___x_793_);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__1___redArg___boxed(lean_object* v_msg_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_){
_start:
{
lean_object* v_res_804_; 
v_res_804_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__1___redArg(v_msg_798_, v___y_799_, v___y_800_, v___y_801_, v___y_802_);
lean_dec(v___y_802_);
lean_dec_ref(v___y_801_);
lean_dec(v___y_800_);
lean_dec_ref(v___y_799_);
return v_res_804_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__4(void){
_start:
{
lean_object* v___x_813_; lean_object* v___x_814_; 
v___x_813_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__3));
v___x_814_ = l_Lean_stringToMessageData(v___x_813_);
return v___x_814_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__6(void){
_start:
{
lean_object* v___x_816_; lean_object* v___x_817_; 
v___x_816_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__5));
v___x_817_ = l_Lean_stringToMessageData(v___x_816_);
return v___x_817_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__8(void){
_start:
{
lean_object* v___x_819_; lean_object* v___x_820_; 
v___x_819_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__7));
v___x_820_ = l_Lean_stringToMessageData(v___x_819_);
return v___x_820_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2(lean_object* v_as_821_, size_t v_sz_822_, size_t v_i_823_, lean_object* v_b_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_){
_start:
{
lean_object* v_a_831_; uint8_t v___x_835_; 
v___x_835_ = lean_usize_dec_lt(v_i_823_, v_sz_822_);
if (v___x_835_ == 0)
{
lean_object* v___x_836_; 
v___x_836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_836_, 0, v_b_824_);
return v___x_836_;
}
else
{
lean_object* v_a_837_; lean_object* v___x_838_; 
v_a_837_ = lean_array_uget_borrowed(v_as_821_, v_i_823_);
lean_inc(v_a_837_);
v___x_838_ = l_Lean_Meta_mkConstWithFreshMVarLevels(v_a_837_, v___y_825_, v___y_826_, v___y_827_, v___y_828_);
if (lean_obj_tag(v___x_838_) == 0)
{
lean_object* v_a_839_; lean_object* v___x_840_; 
v_a_839_ = lean_ctor_get(v___x_838_, 0);
lean_inc(v_a_839_);
lean_dec_ref_known(v___x_838_, 1);
lean_inc(v___y_828_);
lean_inc_ref(v___y_827_);
lean_inc(v___y_826_);
lean_inc_ref(v___y_825_);
v___x_840_ = lean_infer_type(v_a_839_, v___y_825_, v___y_826_, v___y_827_, v___y_828_);
if (lean_obj_tag(v___x_840_) == 0)
{
lean_object* v_a_841_; uint8_t v___x_842_; lean_object* v___x_843_; 
v_a_841_ = lean_ctor_get(v___x_840_, 0);
lean_inc(v_a_841_);
lean_dec_ref_known(v___x_840_, 1);
v___x_842_ = 0;
v___x_843_ = l_Lean_Meta_forallMetaTelescope(v_a_841_, v___x_842_, v___y_825_, v___y_826_, v___y_827_, v___y_828_);
if (lean_obj_tag(v___x_843_) == 0)
{
lean_object* v_a_844_; lean_object* v_snd_845_; lean_object* v___x_847_; uint8_t v_isShared_848_; uint8_t v_isSharedCheck_909_; 
v_a_844_ = lean_ctor_get(v___x_843_, 0);
lean_inc(v_a_844_);
lean_dec_ref_known(v___x_843_, 1);
v_snd_845_ = lean_ctor_get(v_a_844_, 1);
v_isSharedCheck_909_ = !lean_is_exclusive(v_a_844_);
if (v_isSharedCheck_909_ == 0)
{
lean_object* v_unused_910_; 
v_unused_910_ = lean_ctor_get(v_a_844_, 0);
lean_dec(v_unused_910_);
v___x_847_ = v_a_844_;
v_isShared_848_ = v_isSharedCheck_909_;
goto v_resetjp_846_;
}
else
{
lean_inc(v_snd_845_);
lean_dec(v_a_844_);
v___x_847_ = lean_box(0);
v_isShared_848_ = v_isSharedCheck_909_;
goto v_resetjp_846_;
}
v_resetjp_846_:
{
lean_object* v_snd_849_; lean_object* v___x_851_; uint8_t v_isShared_852_; uint8_t v_isSharedCheck_907_; 
v_snd_849_ = lean_ctor_get(v_snd_845_, 1);
v_isSharedCheck_907_ = !lean_is_exclusive(v_snd_845_);
if (v_isSharedCheck_907_ == 0)
{
lean_object* v_unused_908_; 
v_unused_908_ = lean_ctor_get(v_snd_845_, 0);
lean_dec(v_unused_908_);
v___x_851_ = v_snd_845_;
v_isShared_852_ = v_isSharedCheck_907_;
goto v_resetjp_850_;
}
else
{
lean_inc(v_snd_849_);
lean_dec(v_snd_845_);
v___x_851_ = lean_box(0);
v_isShared_852_ = v_isSharedCheck_907_;
goto v_resetjp_850_;
}
v_resetjp_850_:
{
lean_object* v___x_853_; 
v___x_853_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__0___redArg(v_snd_849_, v___y_826_);
if (lean_obj_tag(v___x_853_) == 0)
{
lean_object* v_a_854_; lean_object* v___x_855_; lean_object* v___x_856_; uint8_t v___x_857_; 
v_a_854_ = lean_ctor_get(v___x_853_, 0);
lean_inc(v_a_854_);
lean_dec_ref_known(v___x_853_, 1);
v___x_855_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__2));
v___x_856_ = lean_unsigned_to_nat(4u);
v___x_857_ = l_Lean_Expr_isAppOfArity(v_a_854_, v___x_855_, v___x_856_);
if (v___x_857_ == 0)
{
lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_861_; 
lean_dec(v_a_854_);
lean_del_object(v___x_851_);
v___x_858_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__4);
lean_inc(v_a_837_);
v___x_859_ = l_Lean_MessageData_ofName(v_a_837_);
if (v_isShared_848_ == 0)
{
lean_ctor_set_tag(v___x_847_, 7);
lean_ctor_set(v___x_847_, 1, v___x_859_);
lean_ctor_set(v___x_847_, 0, v___x_858_);
v___x_861_ = v___x_847_;
goto v_reusejp_860_;
}
else
{
lean_object* v_reuseFailAlloc_873_; 
v_reuseFailAlloc_873_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_873_, 0, v___x_858_);
lean_ctor_set(v_reuseFailAlloc_873_, 1, v___x_859_);
v___x_861_ = v_reuseFailAlloc_873_;
goto v_reusejp_860_;
}
v_reusejp_860_:
{
lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; 
v___x_862_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__6);
v___x_863_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_863_, 0, v___x_861_);
lean_ctor_set(v___x_863_, 1, v___x_862_);
v___x_864_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__1___redArg(v___x_863_, v___y_825_, v___y_826_, v___y_827_, v___y_828_);
if (lean_obj_tag(v___x_864_) == 0)
{
lean_dec_ref_known(v___x_864_, 1);
v_a_831_ = v_b_824_;
goto v___jp_830_;
}
else
{
lean_object* v_a_865_; lean_object* v___x_867_; uint8_t v_isShared_868_; uint8_t v_isSharedCheck_872_; 
lean_dec_ref(v_b_824_);
v_a_865_ = lean_ctor_get(v___x_864_, 0);
v_isSharedCheck_872_ = !lean_is_exclusive(v___x_864_);
if (v_isSharedCheck_872_ == 0)
{
v___x_867_ = v___x_864_;
v_isShared_868_ = v_isSharedCheck_872_;
goto v_resetjp_866_;
}
else
{
lean_inc(v_a_865_);
lean_dec(v___x_864_);
v___x_867_ = lean_box(0);
v_isShared_868_ = v_isSharedCheck_872_;
goto v_resetjp_866_;
}
v_resetjp_866_:
{
lean_object* v___x_870_; 
if (v_isShared_868_ == 0)
{
v___x_870_ = v___x_867_;
goto v_reusejp_869_;
}
else
{
lean_object* v_reuseFailAlloc_871_; 
v_reuseFailAlloc_871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_871_, 0, v_a_865_);
v___x_870_ = v_reuseFailAlloc_871_;
goto v_reusejp_869_;
}
v_reusejp_869_:
{
return v___x_870_;
}
}
}
}
}
else
{
lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; 
v___x_874_ = l_Lean_Expr_appArg_x21(v_a_854_);
lean_dec(v_a_854_);
v___x_875_ = l_Lean_Expr_getAppFn(v___x_874_);
v___x_876_ = l_Lean_Expr_constName_x3f(v___x_875_);
lean_dec_ref(v___x_875_);
if (lean_obj_tag(v___x_876_) == 1)
{
lean_object* v_val_877_; lean_object* v___x_878_; lean_object* v___x_880_; 
lean_del_object(v___x_847_);
v_val_877_ = lean_ctor_get(v___x_876_, 0);
lean_inc(v_val_877_);
lean_dec_ref_known(v___x_876_, 1);
v___x_878_ = l_Lean_Expr_getAppNumArgs(v___x_874_);
lean_dec_ref(v___x_874_);
lean_inc(v_a_837_);
if (v_isShared_852_ == 0)
{
lean_ctor_set(v___x_851_, 1, v___x_878_);
lean_ctor_set(v___x_851_, 0, v_a_837_);
v___x_880_ = v___x_851_;
goto v_reusejp_879_;
}
else
{
lean_object* v_reuseFailAlloc_882_; 
v_reuseFailAlloc_882_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_882_, 0, v_a_837_);
lean_ctor_set(v_reuseFailAlloc_882_, 1, v___x_878_);
v___x_880_ = v_reuseFailAlloc_882_;
goto v_reusejp_879_;
}
v_reusejp_879_:
{
lean_object* v___x_881_; 
v___x_881_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_latticeOps_spec__0___redArg(v_b_824_, v_val_877_, v___x_880_);
v_a_831_ = v___x_881_;
goto v___jp_830_;
}
}
else
{
lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_886_; 
lean_dec(v___x_876_);
lean_dec_ref(v___x_874_);
lean_del_object(v___x_851_);
v___x_883_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__4);
lean_inc(v_a_837_);
v___x_884_ = l_Lean_MessageData_ofName(v_a_837_);
if (v_isShared_848_ == 0)
{
lean_ctor_set_tag(v___x_847_, 7);
lean_ctor_set(v___x_847_, 1, v___x_884_);
lean_ctor_set(v___x_847_, 0, v___x_883_);
v___x_886_ = v___x_847_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_898_; 
v_reuseFailAlloc_898_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_898_, 0, v___x_883_);
lean_ctor_set(v_reuseFailAlloc_898_, 1, v___x_884_);
v___x_886_ = v_reuseFailAlloc_898_;
goto v_reusejp_885_;
}
v_reusejp_885_:
{
lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; 
v___x_887_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__8);
v___x_888_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_888_, 0, v___x_886_);
lean_ctor_set(v___x_888_, 1, v___x_887_);
v___x_889_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__1___redArg(v___x_888_, v___y_825_, v___y_826_, v___y_827_, v___y_828_);
if (lean_obj_tag(v___x_889_) == 0)
{
lean_dec_ref_known(v___x_889_, 1);
v_a_831_ = v_b_824_;
goto v___jp_830_;
}
else
{
lean_object* v_a_890_; lean_object* v___x_892_; uint8_t v_isShared_893_; uint8_t v_isSharedCheck_897_; 
lean_dec_ref(v_b_824_);
v_a_890_ = lean_ctor_get(v___x_889_, 0);
v_isSharedCheck_897_ = !lean_is_exclusive(v___x_889_);
if (v_isSharedCheck_897_ == 0)
{
v___x_892_ = v___x_889_;
v_isShared_893_ = v_isSharedCheck_897_;
goto v_resetjp_891_;
}
else
{
lean_inc(v_a_890_);
lean_dec(v___x_889_);
v___x_892_ = lean_box(0);
v_isShared_893_ = v_isSharedCheck_897_;
goto v_resetjp_891_;
}
v_resetjp_891_:
{
lean_object* v___x_895_; 
if (v_isShared_893_ == 0)
{
v___x_895_ = v___x_892_;
goto v_reusejp_894_;
}
else
{
lean_object* v_reuseFailAlloc_896_; 
v_reuseFailAlloc_896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_896_, 0, v_a_890_);
v___x_895_ = v_reuseFailAlloc_896_;
goto v_reusejp_894_;
}
v_reusejp_894_:
{
return v___x_895_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_899_; lean_object* v___x_901_; uint8_t v_isShared_902_; uint8_t v_isSharedCheck_906_; 
lean_del_object(v___x_851_);
lean_del_object(v___x_847_);
lean_dec_ref(v_b_824_);
v_a_899_ = lean_ctor_get(v___x_853_, 0);
v_isSharedCheck_906_ = !lean_is_exclusive(v___x_853_);
if (v_isSharedCheck_906_ == 0)
{
v___x_901_ = v___x_853_;
v_isShared_902_ = v_isSharedCheck_906_;
goto v_resetjp_900_;
}
else
{
lean_inc(v_a_899_);
lean_dec(v___x_853_);
v___x_901_ = lean_box(0);
v_isShared_902_ = v_isSharedCheck_906_;
goto v_resetjp_900_;
}
v_resetjp_900_:
{
lean_object* v___x_904_; 
if (v_isShared_902_ == 0)
{
v___x_904_ = v___x_901_;
goto v_reusejp_903_;
}
else
{
lean_object* v_reuseFailAlloc_905_; 
v_reuseFailAlloc_905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_905_, 0, v_a_899_);
v___x_904_ = v_reuseFailAlloc_905_;
goto v_reusejp_903_;
}
v_reusejp_903_:
{
return v___x_904_;
}
}
}
}
}
}
else
{
lean_object* v_a_911_; lean_object* v___x_913_; uint8_t v_isShared_914_; uint8_t v_isSharedCheck_918_; 
lean_dec_ref(v_b_824_);
v_a_911_ = lean_ctor_get(v___x_843_, 0);
v_isSharedCheck_918_ = !lean_is_exclusive(v___x_843_);
if (v_isSharedCheck_918_ == 0)
{
v___x_913_ = v___x_843_;
v_isShared_914_ = v_isSharedCheck_918_;
goto v_resetjp_912_;
}
else
{
lean_inc(v_a_911_);
lean_dec(v___x_843_);
v___x_913_ = lean_box(0);
v_isShared_914_ = v_isSharedCheck_918_;
goto v_resetjp_912_;
}
v_resetjp_912_:
{
lean_object* v___x_916_; 
if (v_isShared_914_ == 0)
{
v___x_916_ = v___x_913_;
goto v_reusejp_915_;
}
else
{
lean_object* v_reuseFailAlloc_917_; 
v_reuseFailAlloc_917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_917_, 0, v_a_911_);
v___x_916_ = v_reuseFailAlloc_917_;
goto v_reusejp_915_;
}
v_reusejp_915_:
{
return v___x_916_;
}
}
}
}
else
{
lean_object* v_a_919_; lean_object* v___x_921_; uint8_t v_isShared_922_; uint8_t v_isSharedCheck_926_; 
lean_dec_ref(v_b_824_);
v_a_919_ = lean_ctor_get(v___x_840_, 0);
v_isSharedCheck_926_ = !lean_is_exclusive(v___x_840_);
if (v_isSharedCheck_926_ == 0)
{
v___x_921_ = v___x_840_;
v_isShared_922_ = v_isSharedCheck_926_;
goto v_resetjp_920_;
}
else
{
lean_inc(v_a_919_);
lean_dec(v___x_840_);
v___x_921_ = lean_box(0);
v_isShared_922_ = v_isSharedCheck_926_;
goto v_resetjp_920_;
}
v_resetjp_920_:
{
lean_object* v___x_924_; 
if (v_isShared_922_ == 0)
{
v___x_924_ = v___x_921_;
goto v_reusejp_923_;
}
else
{
lean_object* v_reuseFailAlloc_925_; 
v_reuseFailAlloc_925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_925_, 0, v_a_919_);
v___x_924_ = v_reuseFailAlloc_925_;
goto v_reusejp_923_;
}
v_reusejp_923_:
{
return v___x_924_;
}
}
}
}
else
{
lean_object* v_a_927_; lean_object* v___x_929_; uint8_t v_isShared_930_; uint8_t v_isSharedCheck_934_; 
lean_dec_ref(v_b_824_);
v_a_927_ = lean_ctor_get(v___x_838_, 0);
v_isSharedCheck_934_ = !lean_is_exclusive(v___x_838_);
if (v_isSharedCheck_934_ == 0)
{
v___x_929_ = v___x_838_;
v_isShared_930_ = v_isSharedCheck_934_;
goto v_resetjp_928_;
}
else
{
lean_inc(v_a_927_);
lean_dec(v___x_838_);
v___x_929_ = lean_box(0);
v_isShared_930_ = v_isSharedCheck_934_;
goto v_resetjp_928_;
}
v_resetjp_928_:
{
lean_object* v___x_932_; 
if (v_isShared_930_ == 0)
{
v___x_932_ = v___x_929_;
goto v_reusejp_931_;
}
else
{
lean_object* v_reuseFailAlloc_933_; 
v_reuseFailAlloc_933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_933_, 0, v_a_927_);
v___x_932_ = v_reuseFailAlloc_933_;
goto v_reusejp_931_;
}
v_reusejp_931_:
{
return v___x_932_;
}
}
}
}
v___jp_830_:
{
size_t v___x_832_; size_t v___x_833_; 
v___x_832_ = ((size_t)1ULL);
v___x_833_ = lean_usize_add(v_i_823_, v___x_832_);
v_i_823_ = v___x_833_;
v_b_824_ = v_a_831_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___boxed(lean_object* v_as_935_, lean_object* v_sz_936_, lean_object* v_i_937_, lean_object* v_b_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_){
_start:
{
size_t v_sz_boxed_944_; size_t v_i_boxed_945_; lean_object* v_res_946_; 
v_sz_boxed_944_ = lean_unbox_usize(v_sz_936_);
lean_dec(v_sz_936_);
v_i_boxed_945_ = lean_unbox_usize(v_i_937_);
lean_dec(v_i_937_);
v_res_946_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2(v_as_935_, v_sz_boxed_944_, v_i_boxed_945_, v_b_938_, v___y_939_, v___y_940_, v___y_941_, v___y_942_);
lean_dec(v___y_942_);
lean_dec_ref(v___y_941_);
lean_dec(v___y_940_);
lean_dec_ref(v___y_939_);
lean_dec_ref(v_as_935_);
return v_res_946_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals(lean_object* v_names_947_, lean_object* v_a_948_, lean_object* v_a_949_, lean_object* v_a_950_, lean_object* v_a_951_){
_start:
{
lean_object* v_m_953_; size_t v_sz_954_; size_t v___x_955_; lean_object* v___x_956_; 
v_m_953_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_latticeOps___closed__1, &l_Lean_Elab_Tactic_VCGen_latticeOps___closed__1_once, _init_l_Lean_Elab_Tactic_VCGen_latticeOps___closed__1);
v_sz_954_ = lean_array_size(v_names_947_);
v___x_955_ = ((size_t)0ULL);
v___x_956_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2(v_names_947_, v_sz_954_, v___x_955_, v_m_953_, v_a_948_, v_a_949_, v_a_950_, v_a_951_);
return v___x_956_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals___boxed(lean_object* v_names_957_, lean_object* v_a_958_, lean_object* v_a_959_, lean_object* v_a_960_, lean_object* v_a_961_, lean_object* v_a_962_){
_start:
{
lean_object* v_res_963_; 
v_res_963_ = l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals(v_names_957_, v_a_958_, v_a_959_, v_a_960_, v_a_961_);
lean_dec(v_a_961_);
lean_dec_ref(v_a_960_);
lean_dec(v_a_959_);
lean_dec_ref(v_a_958_);
lean_dec_ref(v_names_957_);
return v_res_963_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__1(lean_object* v_00_u03b1_964_, lean_object* v_msg_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_){
_start:
{
lean_object* v___x_971_; 
v___x_971_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__1___redArg(v_msg_965_, v___y_966_, v___y_967_, v___y_968_, v___y_969_);
return v___x_971_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__1___boxed(lean_object* v_00_u03b1_972_, lean_object* v_msg_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_){
_start:
{
lean_object* v_res_979_; 
v_res_979_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__1(v_00_u03b1_972_, v_msg_973_, v___y_974_, v___y_975_, v___y_976_, v___y_977_);
lean_dec(v___y_977_);
lean_dec_ref(v___y_976_);
lean_dec(v___y_975_);
lean_dec_ref(v___y_974_);
return v_res_979_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_go___lam__0(uint8_t v_isZero_980_, lean_object* v_x_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_){
_start:
{
lean_object* v___x_992_; lean_object* v___x_993_; 
v___x_992_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_992_, 0, v_isZero_980_);
lean_ctor_set_uint8(v___x_992_, 1, v_isZero_980_);
v___x_993_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_993_, 0, v___x_992_);
return v___x_993_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_go___lam__0___boxed(lean_object* v_isZero_994_, lean_object* v_x_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_){
_start:
{
uint8_t v_isZero_boxed_1006_; lean_object* v_res_1007_; 
v_isZero_boxed_1006_ = lean_unbox(v_isZero_994_);
v_res_1007_ = l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_go___lam__0(v_isZero_boxed_1006_, v_x_995_, v___y_996_, v___y_997_, v___y_998_, v___y_999_, v___y_1000_, v___y_1001_, v___y_1002_, v___y_1003_, v___y_1004_);
lean_dec(v___y_1004_);
lean_dec_ref(v___y_1003_);
lean_dec(v___y_1002_);
lean_dec_ref(v___y_1001_);
lean_dec(v___y_1000_);
lean_dec_ref(v___y_999_);
lean_dec(v___y_998_);
lean_dec_ref(v___y_997_);
lean_dec(v___y_996_);
lean_dec_ref(v_x_995_);
return v_res_1007_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_go_spec__0___redArg(lean_object* v_msg_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_){
_start:
{
lean_object* v_ref_1014_; lean_object* v___x_1015_; lean_object* v_a_1016_; lean_object* v___x_1018_; uint8_t v_isShared_1019_; uint8_t v_isSharedCheck_1024_; 
v_ref_1014_ = lean_ctor_get(v___y_1011_, 2);
v___x_1015_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__1_spec__1(v_msg_1008_, v___y_1009_, v___y_1010_, v___y_1011_, v___y_1012_);
v_a_1016_ = lean_ctor_get(v___x_1015_, 0);
v_isSharedCheck_1024_ = !lean_is_exclusive(v___x_1015_);
if (v_isSharedCheck_1024_ == 0)
{
v___x_1018_ = v___x_1015_;
v_isShared_1019_ = v_isSharedCheck_1024_;
goto v_resetjp_1017_;
}
else
{
lean_inc(v_a_1016_);
lean_dec(v___x_1015_);
v___x_1018_ = lean_box(0);
v_isShared_1019_ = v_isSharedCheck_1024_;
goto v_resetjp_1017_;
}
v_resetjp_1017_:
{
lean_object* v___x_1020_; lean_object* v___x_1022_; 
lean_inc(v_ref_1014_);
v___x_1020_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1020_, 0, v_ref_1014_);
lean_ctor_set(v___x_1020_, 1, v_a_1016_);
if (v_isShared_1019_ == 0)
{
lean_ctor_set_tag(v___x_1018_, 1);
lean_ctor_set(v___x_1018_, 0, v___x_1020_);
v___x_1022_ = v___x_1018_;
goto v_reusejp_1021_;
}
else
{
lean_object* v_reuseFailAlloc_1023_; 
v_reuseFailAlloc_1023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1023_, 0, v___x_1020_);
v___x_1022_ = v_reuseFailAlloc_1023_;
goto v_reusejp_1021_;
}
v_reusejp_1021_:
{
return v___x_1022_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_go_spec__0___redArg___boxed(lean_object* v_msg_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_){
_start:
{
lean_object* v_res_1031_; 
v_res_1031_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_go_spec__0___redArg(v_msg_1025_, v___y_1026_, v___y_1027_, v___y_1028_, v___y_1029_);
lean_dec(v___y_1029_);
lean_dec_ref(v___y_1028_);
lean_dec(v___y_1027_);
lean_dec_ref(v___y_1026_);
return v_res_1031_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_go___closed__1(void){
_start:
{
lean_object* v___x_1033_; lean_object* v___x_1034_; 
v___x_1033_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_go___closed__0));
v___x_1034_ = l_Lean_stringToMessageData(v___x_1033_);
return v___x_1034_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_go(lean_object* v_step_1038_, lean_object* v_e_u2080_1039_, lean_object* v_cur_1040_, lean_object* v_proof_x3f_1041_, lean_object* v_a_1042_, lean_object* v_a_1043_, lean_object* v_a_1044_, lean_object* v_a_1045_, lean_object* v_a_1046_, lean_object* v_a_1047_, lean_object* v_a_1048_){
_start:
{
lean_object* v_zero_1050_; uint8_t v_isZero_1051_; 
v_zero_1050_ = lean_unsigned_to_nat(0u);
v_isZero_1051_ = lean_nat_dec_eq(v_a_1042_, v_zero_1050_);
if (v_isZero_1051_ == 1)
{
lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; 
lean_dec(v_a_1042_);
lean_dec(v_proof_x3f_1041_);
lean_dec_ref(v_e_u2080_1039_);
lean_dec_ref(v_step_1038_);
v___x_1052_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_go___closed__1, &l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_go___closed__1_once, _init_l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_go___closed__1);
v___x_1053_ = l_Lean_indentExpr(v_cur_1040_);
v___x_1054_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1054_, 0, v___x_1052_);
lean_ctor_set(v___x_1054_, 1, v___x_1053_);
v___x_1055_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_go_spec__0___redArg(v___x_1054_, v_a_1045_, v_a_1046_, v_a_1047_, v_a_1048_);
return v___x_1055_;
}
else
{
lean_object* v___x_1056_; lean_object* v___f_1057_; lean_object* v_one_1058_; lean_object* v_n_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; 
v___x_1056_ = lean_box(v_isZero_1051_);
v___f_1057_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_go___lam__0___boxed), 12, 1);
lean_closure_set(v___f_1057_, 0, v___x_1056_);
v_one_1058_ = lean_unsigned_to_nat(1u);
v_n_1059_ = lean_nat_sub(v_a_1042_, v_one_1058_);
lean_dec(v_a_1042_);
lean_inc_ref(v_step_1038_);
lean_inc_ref(v_cur_1040_);
v___x_1060_ = lean_apply_1(v_step_1038_, v_cur_1040_);
lean_inc_ref(v___f_1057_);
v___x_1061_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1061_, 0, v___f_1057_);
lean_ctor_set(v___x_1061_, 1, v___f_1057_);
v___x_1062_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_go___closed__2));
v___x_1063_ = l_Lean_Meta_Sym_Simp_SimpM_run_x27___redArg(v___x_1060_, v___x_1061_, v___x_1062_, v_a_1043_, v_a_1044_, v_a_1045_, v_a_1046_, v_a_1047_, v_a_1048_);
if (lean_obj_tag(v___x_1063_) == 0)
{
lean_object* v_a_1064_; lean_object* v___x_1066_; uint8_t v_isShared_1067_; uint8_t v_isSharedCheck_1095_; 
v_a_1064_ = lean_ctor_get(v___x_1063_, 0);
v_isSharedCheck_1095_ = !lean_is_exclusive(v___x_1063_);
if (v_isSharedCheck_1095_ == 0)
{
v___x_1066_ = v___x_1063_;
v_isShared_1067_ = v_isSharedCheck_1095_;
goto v_resetjp_1065_;
}
else
{
lean_inc(v_a_1064_);
lean_dec(v___x_1063_);
v___x_1066_ = lean_box(0);
v_isShared_1067_ = v_isSharedCheck_1095_;
goto v_resetjp_1065_;
}
v_resetjp_1065_:
{
if (lean_obj_tag(v_a_1064_) == 0)
{
lean_object* v___x_1068_; lean_object* v___x_1070_; 
lean_dec_ref_known(v_a_1064_, 0);
lean_dec(v_n_1059_);
lean_dec_ref(v_e_u2080_1039_);
lean_dec_ref(v_step_1038_);
v___x_1068_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1068_, 0, v_cur_1040_);
lean_ctor_set(v___x_1068_, 1, v_proof_x3f_1041_);
if (v_isShared_1067_ == 0)
{
lean_ctor_set(v___x_1066_, 0, v___x_1068_);
v___x_1070_ = v___x_1066_;
goto v_reusejp_1069_;
}
else
{
lean_object* v_reuseFailAlloc_1071_; 
v_reuseFailAlloc_1071_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1071_, 0, v___x_1068_);
v___x_1070_ = v_reuseFailAlloc_1071_;
goto v_reusejp_1069_;
}
v_reusejp_1069_:
{
return v___x_1070_;
}
}
else
{
lean_object* v_e_x27_1072_; lean_object* v_proof_1073_; lean_object* v_proof_1075_; lean_object* v___y_1076_; lean_object* v___y_1077_; lean_object* v___y_1078_; lean_object* v___y_1079_; lean_object* v___y_1080_; lean_object* v___y_1081_; 
lean_del_object(v___x_1066_);
v_e_x27_1072_ = lean_ctor_get(v_a_1064_, 0);
lean_inc_ref(v_e_x27_1072_);
v_proof_1073_ = lean_ctor_get(v_a_1064_, 1);
lean_inc_ref(v_proof_1073_);
lean_dec_ref_known(v_a_1064_, 2);
if (lean_obj_tag(v_proof_x3f_1041_) == 0)
{
lean_dec_ref(v_cur_1040_);
v_proof_1075_ = v_proof_1073_;
v___y_1076_ = v_a_1043_;
v___y_1077_ = v_a_1044_;
v___y_1078_ = v_a_1045_;
v___y_1079_ = v_a_1046_;
v___y_1080_ = v_a_1047_;
v___y_1081_ = v_a_1048_;
goto v___jp_1074_;
}
else
{
lean_object* v_val_1084_; lean_object* v___x_1085_; 
v_val_1084_ = lean_ctor_get(v_proof_x3f_1041_, 0);
lean_inc(v_val_1084_);
lean_dec_ref_known(v_proof_x3f_1041_, 1);
lean_inc_ref(v_e_x27_1072_);
lean_inc_ref(v_e_u2080_1039_);
v___x_1085_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v_e_u2080_1039_, v_cur_1040_, v_val_1084_, v_e_x27_1072_, v_proof_1073_, v_a_1043_, v_a_1044_, v_a_1045_, v_a_1046_, v_a_1047_, v_a_1048_);
if (lean_obj_tag(v___x_1085_) == 0)
{
lean_object* v_a_1086_; 
v_a_1086_ = lean_ctor_get(v___x_1085_, 0);
lean_inc(v_a_1086_);
lean_dec_ref_known(v___x_1085_, 1);
v_proof_1075_ = v_a_1086_;
v___y_1076_ = v_a_1043_;
v___y_1077_ = v_a_1044_;
v___y_1078_ = v_a_1045_;
v___y_1079_ = v_a_1046_;
v___y_1080_ = v_a_1047_;
v___y_1081_ = v_a_1048_;
goto v___jp_1074_;
}
else
{
lean_object* v_a_1087_; lean_object* v___x_1089_; uint8_t v_isShared_1090_; uint8_t v_isSharedCheck_1094_; 
lean_dec_ref(v_e_x27_1072_);
lean_dec(v_n_1059_);
lean_dec_ref(v_e_u2080_1039_);
lean_dec_ref(v_step_1038_);
v_a_1087_ = lean_ctor_get(v___x_1085_, 0);
v_isSharedCheck_1094_ = !lean_is_exclusive(v___x_1085_);
if (v_isSharedCheck_1094_ == 0)
{
v___x_1089_ = v___x_1085_;
v_isShared_1090_ = v_isSharedCheck_1094_;
goto v_resetjp_1088_;
}
else
{
lean_inc(v_a_1087_);
lean_dec(v___x_1085_);
v___x_1089_ = lean_box(0);
v_isShared_1090_ = v_isSharedCheck_1094_;
goto v_resetjp_1088_;
}
v_resetjp_1088_:
{
lean_object* v___x_1092_; 
if (v_isShared_1090_ == 0)
{
v___x_1092_ = v___x_1089_;
goto v_reusejp_1091_;
}
else
{
lean_object* v_reuseFailAlloc_1093_; 
v_reuseFailAlloc_1093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1093_, 0, v_a_1087_);
v___x_1092_ = v_reuseFailAlloc_1093_;
goto v_reusejp_1091_;
}
v_reusejp_1091_:
{
return v___x_1092_;
}
}
}
}
v___jp_1074_:
{
lean_object* v___x_1082_; 
v___x_1082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1082_, 0, v_proof_1075_);
v_cur_1040_ = v_e_x27_1072_;
v_proof_x3f_1041_ = v___x_1082_;
v_a_1042_ = v_n_1059_;
v_a_1043_ = v___y_1076_;
v_a_1044_ = v___y_1077_;
v_a_1045_ = v___y_1078_;
v_a_1046_ = v___y_1079_;
v_a_1047_ = v___y_1080_;
v_a_1048_ = v___y_1081_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1096_; lean_object* v___x_1098_; uint8_t v_isShared_1099_; uint8_t v_isSharedCheck_1103_; 
lean_dec(v_n_1059_);
lean_dec(v_proof_x3f_1041_);
lean_dec_ref(v_cur_1040_);
lean_dec_ref(v_e_u2080_1039_);
lean_dec_ref(v_step_1038_);
v_a_1096_ = lean_ctor_get(v___x_1063_, 0);
v_isSharedCheck_1103_ = !lean_is_exclusive(v___x_1063_);
if (v_isSharedCheck_1103_ == 0)
{
v___x_1098_ = v___x_1063_;
v_isShared_1099_ = v_isSharedCheck_1103_;
goto v_resetjp_1097_;
}
else
{
lean_inc(v_a_1096_);
lean_dec(v___x_1063_);
v___x_1098_ = lean_box(0);
v_isShared_1099_ = v_isSharedCheck_1103_;
goto v_resetjp_1097_;
}
v_resetjp_1097_:
{
lean_object* v___x_1101_; 
if (v_isShared_1099_ == 0)
{
v___x_1101_ = v___x_1098_;
goto v_reusejp_1100_;
}
else
{
lean_object* v_reuseFailAlloc_1102_; 
v_reuseFailAlloc_1102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1102_, 0, v_a_1096_);
v___x_1101_ = v_reuseFailAlloc_1102_;
goto v_reusejp_1100_;
}
v_reusejp_1100_:
{
return v___x_1101_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_go___boxed(lean_object* v_step_1104_, lean_object* v_e_u2080_1105_, lean_object* v_cur_1106_, lean_object* v_proof_x3f_1107_, lean_object* v_a_1108_, lean_object* v_a_1109_, lean_object* v_a_1110_, lean_object* v_a_1111_, lean_object* v_a_1112_, lean_object* v_a_1113_, lean_object* v_a_1114_, lean_object* v_a_1115_){
_start:
{
lean_object* v_res_1116_; 
v_res_1116_ = l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_go(v_step_1104_, v_e_u2080_1105_, v_cur_1106_, v_proof_x3f_1107_, v_a_1108_, v_a_1109_, v_a_1110_, v_a_1111_, v_a_1112_, v_a_1113_, v_a_1114_);
lean_dec(v_a_1114_);
lean_dec_ref(v_a_1113_);
lean_dec(v_a_1112_);
lean_dec_ref(v_a_1111_);
lean_dec(v_a_1110_);
lean_dec_ref(v_a_1109_);
return v_res_1116_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_go_spec__0(lean_object* v_00_u03b1_1117_, lean_object* v_msg_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_){
_start:
{
lean_object* v___x_1126_; 
v___x_1126_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_go_spec__0___redArg(v_msg_1118_, v___y_1121_, v___y_1122_, v___y_1123_, v___y_1124_);
return v___x_1126_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_go_spec__0___boxed(lean_object* v_00_u03b1_1127_, lean_object* v_msg_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_){
_start:
{
lean_object* v_res_1136_; 
v_res_1136_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_go_spec__0(v_00_u03b1_1127_, v_msg_1128_, v___y_1129_, v___y_1130_, v___y_1131_, v___y_1132_, v___y_1133_, v___y_1134_);
lean_dec(v___y_1134_);
lean_dec_ref(v___y_1133_);
lean_dec(v___y_1132_);
lean_dec_ref(v___y_1131_);
lean_dec(v___y_1130_);
lean_dec_ref(v___y_1129_);
return v_res_1136_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_spec__0___redArg(lean_object* v_as_1137_, size_t v_i_1138_, size_t v_stop_1139_, lean_object* v_b_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_){
_start:
{
uint8_t v___x_1146_; 
v___x_1146_ = lean_usize_dec_eq(v_i_1138_, v_stop_1139_);
if (v___x_1146_ == 0)
{
lean_object* v___x_1147_; lean_object* v___x_1148_; 
v___x_1147_ = lean_array_uget_borrowed(v_as_1137_, v_i_1138_);
lean_inc(v___x_1147_);
v___x_1148_ = l_Lean_Meta_Sym_Simp_mkTheoremFromDecl(v___x_1147_, v___y_1141_, v___y_1142_, v___y_1143_, v___y_1144_);
if (lean_obj_tag(v___x_1148_) == 0)
{
lean_object* v_a_1149_; lean_object* v___x_1150_; size_t v___x_1151_; size_t v___x_1152_; 
v_a_1149_ = lean_ctor_get(v___x_1148_, 0);
lean_inc(v_a_1149_);
lean_dec_ref_known(v___x_1148_, 1);
v___x_1150_ = l_Lean_Meta_Sym_Simp_Theorems_insert(v_b_1140_, v_a_1149_);
v___x_1151_ = ((size_t)1ULL);
v___x_1152_ = lean_usize_add(v_i_1138_, v___x_1151_);
v_i_1138_ = v___x_1152_;
v_b_1140_ = v___x_1150_;
goto _start;
}
else
{
lean_object* v_a_1154_; lean_object* v___x_1156_; uint8_t v_isShared_1157_; uint8_t v_isSharedCheck_1161_; 
lean_dec_ref(v_b_1140_);
v_a_1154_ = lean_ctor_get(v___x_1148_, 0);
v_isSharedCheck_1161_ = !lean_is_exclusive(v___x_1148_);
if (v_isSharedCheck_1161_ == 0)
{
v___x_1156_ = v___x_1148_;
v_isShared_1157_ = v_isSharedCheck_1161_;
goto v_resetjp_1155_;
}
else
{
lean_inc(v_a_1154_);
lean_dec(v___x_1148_);
v___x_1156_ = lean_box(0);
v_isShared_1157_ = v_isSharedCheck_1161_;
goto v_resetjp_1155_;
}
v_resetjp_1155_:
{
lean_object* v___x_1159_; 
if (v_isShared_1157_ == 0)
{
v___x_1159_ = v___x_1156_;
goto v_reusejp_1158_;
}
else
{
lean_object* v_reuseFailAlloc_1160_; 
v_reuseFailAlloc_1160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1160_, 0, v_a_1154_);
v___x_1159_ = v_reuseFailAlloc_1160_;
goto v_reusejp_1158_;
}
v_reusejp_1158_:
{
return v___x_1159_;
}
}
}
}
else
{
lean_object* v___x_1162_; 
v___x_1162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1162_, 0, v_b_1140_);
return v___x_1162_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_spec__0___redArg___boxed(lean_object* v_as_1163_, lean_object* v_i_1164_, lean_object* v_stop_1165_, lean_object* v_b_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_){
_start:
{
size_t v_i_boxed_1172_; size_t v_stop_boxed_1173_; lean_object* v_res_1174_; 
v_i_boxed_1172_ = lean_unbox_usize(v_i_1164_);
lean_dec(v_i_1164_);
v_stop_boxed_1173_ = lean_unbox_usize(v_stop_1165_);
lean_dec(v_stop_1165_);
v_res_1174_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_spec__0___redArg(v_as_1163_, v_i_boxed_1172_, v_stop_boxed_1173_, v_b_1166_, v___y_1167_, v___y_1168_, v___y_1169_, v___y_1170_);
lean_dec(v___y_1170_);
lean_dec_ref(v___y_1169_);
lean_dec(v___y_1168_);
lean_dec_ref(v___y_1167_);
lean_dec_ref(v_as_1163_);
return v_res_1174_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp___closed__1(void){
_start:
{
lean_object* v___x_1176_; 
v___x_1176_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1176_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp___closed__2(void){
_start:
{
lean_object* v___x_1177_; lean_object* v___x_1178_; 
v___x_1177_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp___closed__1, &l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp___closed__1_once, _init_l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp___closed__1);
v___x_1178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1178_, 0, v___x_1177_);
return v___x_1178_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp___closed__3(void){
_start:
{
lean_object* v___x_1179_; lean_object* v___x_1180_; 
v___x_1179_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp___closed__2, &l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp___closed__2_once, _init_l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp___closed__2);
v___x_1180_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1180_, 0, v___x_1179_);
lean_ctor_set(v___x_1180_, 1, v___x_1179_);
return v___x_1180_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp(lean_object* v_rewrites_1181_, lean_object* v_e_1182_, lean_object* v_fuel_1183_, lean_object* v_a_1184_, lean_object* v_a_1185_, lean_object* v_a_1186_, lean_object* v_a_1187_, lean_object* v_a_1188_, lean_object* v_a_1189_){
_start:
{
lean_object* v_a_1192_; lean_object* v___y_1208_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; uint8_t v___x_1221_; 
v___x_1218_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp___closed__3, &l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp___closed__3_once, _init_l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp___closed__3);
v___x_1219_ = lean_unsigned_to_nat(0u);
v___x_1220_ = lean_array_get_size(v_rewrites_1181_);
v___x_1221_ = lean_nat_dec_lt(v___x_1219_, v___x_1220_);
if (v___x_1221_ == 0)
{
v_a_1192_ = v___x_1218_;
goto v___jp_1191_;
}
else
{
uint8_t v___x_1222_; 
v___x_1222_ = lean_nat_dec_le(v___x_1220_, v___x_1220_);
if (v___x_1222_ == 0)
{
if (v___x_1221_ == 0)
{
v_a_1192_ = v___x_1218_;
goto v___jp_1191_;
}
else
{
size_t v___x_1223_; size_t v___x_1224_; lean_object* v___x_1225_; 
v___x_1223_ = ((size_t)0ULL);
v___x_1224_ = lean_usize_of_nat(v___x_1220_);
v___x_1225_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_spec__0___redArg(v_rewrites_1181_, v___x_1223_, v___x_1224_, v___x_1218_, v_a_1186_, v_a_1187_, v_a_1188_, v_a_1189_);
v___y_1208_ = v___x_1225_;
goto v___jp_1207_;
}
}
else
{
size_t v___x_1226_; size_t v___x_1227_; lean_object* v___x_1228_; 
v___x_1226_ = ((size_t)0ULL);
v___x_1227_ = lean_usize_of_nat(v___x_1220_);
v___x_1228_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_spec__0___redArg(v_rewrites_1181_, v___x_1226_, v___x_1227_, v___x_1218_, v_a_1186_, v_a_1187_, v_a_1188_, v_a_1189_);
v___y_1208_ = v___x_1228_;
goto v___jp_1207_;
}
}
v___jp_1191_:
{
lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; 
v___x_1193_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp___closed__0));
v___x_1194_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Simp_Theorems_rewrite___boxed), 13, 2);
lean_closure_set(v___x_1194_, 0, v_a_1192_);
lean_closure_set(v___x_1194_, 1, v___x_1193_);
v___x_1195_ = l_Lean_Meta_Sym_shareCommon(v_e_1182_, v_a_1184_, v_a_1185_, v_a_1186_, v_a_1187_, v_a_1188_, v_a_1189_);
if (lean_obj_tag(v___x_1195_) == 0)
{
lean_object* v_a_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; 
v_a_1196_ = lean_ctor_get(v___x_1195_, 0);
lean_inc_n(v_a_1196_, 2);
lean_dec_ref_known(v___x_1195_, 1);
v___x_1197_ = lean_box(0);
v___x_1198_ = l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_go(v___x_1194_, v_a_1196_, v_a_1196_, v___x_1197_, v_fuel_1183_, v_a_1184_, v_a_1185_, v_a_1186_, v_a_1187_, v_a_1188_, v_a_1189_);
return v___x_1198_;
}
else
{
lean_object* v_a_1199_; lean_object* v___x_1201_; uint8_t v_isShared_1202_; uint8_t v_isSharedCheck_1206_; 
lean_dec_ref(v___x_1194_);
lean_dec(v_fuel_1183_);
v_a_1199_ = lean_ctor_get(v___x_1195_, 0);
v_isSharedCheck_1206_ = !lean_is_exclusive(v___x_1195_);
if (v_isSharedCheck_1206_ == 0)
{
v___x_1201_ = v___x_1195_;
v_isShared_1202_ = v_isSharedCheck_1206_;
goto v_resetjp_1200_;
}
else
{
lean_inc(v_a_1199_);
lean_dec(v___x_1195_);
v___x_1201_ = lean_box(0);
v_isShared_1202_ = v_isSharedCheck_1206_;
goto v_resetjp_1200_;
}
v_resetjp_1200_:
{
lean_object* v___x_1204_; 
if (v_isShared_1202_ == 0)
{
v___x_1204_ = v___x_1201_;
goto v_reusejp_1203_;
}
else
{
lean_object* v_reuseFailAlloc_1205_; 
v_reuseFailAlloc_1205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1205_, 0, v_a_1199_);
v___x_1204_ = v_reuseFailAlloc_1205_;
goto v_reusejp_1203_;
}
v_reusejp_1203_:
{
return v___x_1204_;
}
}
}
}
v___jp_1207_:
{
if (lean_obj_tag(v___y_1208_) == 0)
{
lean_object* v_a_1209_; 
v_a_1209_ = lean_ctor_get(v___y_1208_, 0);
lean_inc(v_a_1209_);
lean_dec_ref_known(v___y_1208_, 1);
v_a_1192_ = v_a_1209_;
goto v___jp_1191_;
}
else
{
lean_object* v_a_1210_; lean_object* v___x_1212_; uint8_t v_isShared_1213_; uint8_t v_isSharedCheck_1217_; 
lean_dec(v_fuel_1183_);
lean_dec_ref(v_e_1182_);
v_a_1210_ = lean_ctor_get(v___y_1208_, 0);
v_isSharedCheck_1217_ = !lean_is_exclusive(v___y_1208_);
if (v_isSharedCheck_1217_ == 0)
{
v___x_1212_ = v___y_1208_;
v_isShared_1213_ = v_isSharedCheck_1217_;
goto v_resetjp_1211_;
}
else
{
lean_inc(v_a_1210_);
lean_dec(v___y_1208_);
v___x_1212_ = lean_box(0);
v_isShared_1213_ = v_isSharedCheck_1217_;
goto v_resetjp_1211_;
}
v_resetjp_1211_:
{
lean_object* v___x_1215_; 
if (v_isShared_1213_ == 0)
{
v___x_1215_ = v___x_1212_;
goto v_reusejp_1214_;
}
else
{
lean_object* v_reuseFailAlloc_1216_; 
v_reuseFailAlloc_1216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1216_, 0, v_a_1210_);
v___x_1215_ = v_reuseFailAlloc_1216_;
goto v_reusejp_1214_;
}
v_reusejp_1214_:
{
return v___x_1215_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp___boxed(lean_object* v_rewrites_1229_, lean_object* v_e_1230_, lean_object* v_fuel_1231_, lean_object* v_a_1232_, lean_object* v_a_1233_, lean_object* v_a_1234_, lean_object* v_a_1235_, lean_object* v_a_1236_, lean_object* v_a_1237_, lean_object* v_a_1238_){
_start:
{
lean_object* v_res_1239_; 
v_res_1239_ = l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp(v_rewrites_1229_, v_e_1230_, v_fuel_1231_, v_a_1232_, v_a_1233_, v_a_1234_, v_a_1235_, v_a_1236_, v_a_1237_);
lean_dec(v_a_1237_);
lean_dec_ref(v_a_1236_);
lean_dec(v_a_1235_);
lean_dec_ref(v_a_1234_);
lean_dec(v_a_1233_);
lean_dec_ref(v_a_1232_);
lean_dec_ref(v_rewrites_1229_);
return v_res_1239_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_spec__0(lean_object* v_as_1240_, size_t v_i_1241_, size_t v_stop_1242_, lean_object* v_b_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_){
_start:
{
lean_object* v___x_1251_; 
v___x_1251_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_spec__0___redArg(v_as_1240_, v_i_1241_, v_stop_1242_, v_b_1243_, v___y_1246_, v___y_1247_, v___y_1248_, v___y_1249_);
return v___x_1251_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_spec__0___boxed(lean_object* v_as_1252_, lean_object* v_i_1253_, lean_object* v_stop_1254_, lean_object* v_b_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_){
_start:
{
size_t v_i_boxed_1263_; size_t v_stop_boxed_1264_; lean_object* v_res_1265_; 
v_i_boxed_1263_ = lean_unbox_usize(v_i_1253_);
lean_dec(v_i_1253_);
v_stop_boxed_1264_ = lean_unbox_usize(v_stop_1254_);
lean_dec(v_stop_1254_);
v_res_1265_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_spec__0(v_as_1252_, v_i_boxed_1263_, v_stop_boxed_1264_, v_b_1255_, v___y_1256_, v___y_1257_, v___y_1258_, v___y_1259_, v___y_1260_, v___y_1261_);
lean_dec(v___y_1261_);
lean_dec_ref(v___y_1260_);
lean_dec(v___y_1259_);
lean_dec_ref(v___y_1258_);
lean_dec(v___y_1257_);
lean_dec_ref(v___y_1256_);
lean_dec_ref(v_as_1252_);
return v_res_1265_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkExcessArgsFrameApply___closed__1(void){
_start:
{
lean_object* v___x_1267_; lean_object* v___x_1268_; 
v___x_1267_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkExcessArgsFrameApply___closed__0));
v___x_1268_ = l_Lean_stringToMessageData(v___x_1267_);
return v___x_1268_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkExcessArgsFrameApply(lean_object* v_introThm_1269_, lean_object* v_opAs_1270_, lean_object* v_pre_1271_, lean_object* v_ss_1272_, lean_object* v_a_1273_, lean_object* v_a_1274_, lean_object* v_a_1275_, lean_object* v_a_1276_){
_start:
{
lean_object* v_ss_1278_; lean_object* v___x_1279_; 
v_ss_1278_ = lean_array_mk(v_ss_1272_);
lean_inc_ref(v_ss_1278_);
v___x_1279_ = l_Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_new(v_pre_1271_, v_ss_1278_, v_a_1273_, v_a_1274_, v_a_1275_, v_a_1276_);
if (lean_obj_tag(v___x_1279_) == 0)
{
lean_object* v_a_1280_; lean_object* v___x_1281_; 
v_a_1280_ = lean_ctor_get(v___x_1279_, 0);
lean_inc(v_a_1280_);
lean_dec_ref_known(v___x_1279_, 1);
lean_inc(v_introThm_1269_);
v___x_1281_ = l_Lean_Meta_mkConstWithFreshMVarLevels(v_introThm_1269_, v_a_1273_, v_a_1274_, v_a_1275_, v_a_1276_);
if (lean_obj_tag(v___x_1281_) == 0)
{
lean_object* v_a_1282_; lean_object* v___x_1283_; 
v_a_1282_ = lean_ctor_get(v___x_1281_, 0);
lean_inc_n(v_a_1282_, 2);
lean_dec_ref_known(v___x_1281_, 1);
lean_inc(v_a_1276_);
lean_inc_ref(v_a_1275_);
lean_inc(v_a_1274_);
lean_inc_ref(v_a_1273_);
v___x_1283_ = lean_infer_type(v_a_1282_, v_a_1273_, v_a_1274_, v_a_1275_, v_a_1276_);
if (lean_obj_tag(v___x_1283_) == 0)
{
lean_object* v_a_1284_; uint8_t v___x_1285_; lean_object* v___x_1286_; 
v_a_1284_ = lean_ctor_get(v___x_1283_, 0);
lean_inc(v_a_1284_);
lean_dec_ref_known(v___x_1283_, 1);
v___x_1285_ = 0;
v___x_1286_ = l_Lean_Meta_forallMetaTelescope(v_a_1284_, v___x_1285_, v_a_1273_, v_a_1274_, v_a_1275_, v_a_1276_);
if (lean_obj_tag(v___x_1286_) == 0)
{
lean_object* v_a_1287_; lean_object* v_fst_1288_; lean_object* v_snd_1289_; lean_object* v___x_1291_; uint8_t v_isShared_1292_; uint8_t v_isSharedCheck_1345_; 
v_a_1287_ = lean_ctor_get(v___x_1286_, 0);
lean_inc(v_a_1287_);
lean_dec_ref_known(v___x_1286_, 1);
v_fst_1288_ = lean_ctor_get(v_a_1287_, 0);
v_snd_1289_ = lean_ctor_get(v_a_1287_, 1);
v_isSharedCheck_1345_ = !lean_is_exclusive(v_a_1287_);
if (v_isSharedCheck_1345_ == 0)
{
v___x_1291_ = v_a_1287_;
v_isShared_1292_ = v_isSharedCheck_1345_;
goto v_resetjp_1290_;
}
else
{
lean_inc(v_snd_1289_);
lean_inc(v_fst_1288_);
lean_dec(v_a_1287_);
v___x_1291_ = lean_box(0);
v_isShared_1292_ = v_isSharedCheck_1345_;
goto v_resetjp_1290_;
}
v_resetjp_1290_:
{
lean_object* v___y_1294_; lean_object* v___y_1295_; lean_object* v___y_1296_; lean_object* v___y_1297_; lean_object* v_snd_1300_; lean_object* v___x_1302_; uint8_t v_isShared_1303_; uint8_t v_isSharedCheck_1343_; 
v_snd_1300_ = lean_ctor_get(v_snd_1289_, 1);
v_isSharedCheck_1343_ = !lean_is_exclusive(v_snd_1289_);
if (v_isSharedCheck_1343_ == 0)
{
lean_object* v_unused_1344_; 
v_unused_1344_ = lean_ctor_get(v_snd_1289_, 0);
lean_dec(v_unused_1344_);
v___x_1302_ = v_snd_1289_;
v_isShared_1303_ = v_isSharedCheck_1343_;
goto v_resetjp_1301_;
}
else
{
lean_inc(v_snd_1300_);
lean_dec(v_snd_1289_);
v___x_1302_ = lean_box(0);
v_isShared_1303_ = v_isSharedCheck_1343_;
goto v_resetjp_1301_;
}
v___jp_1293_:
{
lean_object* v___x_1298_; lean_object* v___x_1299_; 
v___x_1298_ = l_Lean_mkAppN(v_a_1282_, v_fst_1288_);
lean_dec(v_fst_1288_);
v___x_1299_ = l_Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_instantiate(v_a_1280_, v_opAs_1270_, v_ss_1278_, v___x_1298_, v___y_1294_, v___y_1295_, v___y_1296_, v___y_1297_);
lean_dec_ref(v_ss_1278_);
lean_dec(v_a_1280_);
return v___x_1299_;
}
v_resetjp_1301_:
{
lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; 
v___x_1304_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__2));
v___x_1305_ = l_Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_frame(v_a_1280_);
v___x_1306_ = lean_unsigned_to_nat(2u);
v___x_1307_ = lean_mk_empty_array_with_capacity(v___x_1306_);
v___x_1308_ = lean_array_push(v___x_1307_, v___x_1305_);
lean_inc_ref(v_opAs_1270_);
v___x_1309_ = lean_array_push(v___x_1308_, v_opAs_1270_);
v___x_1310_ = l_Lean_Meta_mkAppM(v___x_1304_, v___x_1309_, v_a_1273_, v_a_1274_, v_a_1275_, v_a_1276_);
if (lean_obj_tag(v___x_1310_) == 0)
{
lean_object* v_a_1311_; lean_object* v___x_1312_; 
v_a_1311_ = lean_ctor_get(v___x_1310_, 0);
lean_inc_n(v_a_1311_, 2);
lean_dec_ref_known(v___x_1310_, 1);
v___x_1312_ = l_Lean_Meta_isExprDefEq(v_snd_1300_, v_a_1311_, v_a_1273_, v_a_1274_, v_a_1275_, v_a_1276_);
if (lean_obj_tag(v___x_1312_) == 0)
{
lean_object* v_a_1313_; uint8_t v___x_1314_; 
v_a_1313_ = lean_ctor_get(v___x_1312_, 0);
lean_inc(v_a_1313_);
lean_dec_ref_known(v___x_1312_, 1);
v___x_1314_ = lean_unbox(v_a_1313_);
lean_dec(v_a_1313_);
if (v___x_1314_ == 0)
{
lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1318_; 
lean_dec(v_fst_1288_);
lean_dec(v_a_1282_);
lean_dec(v_a_1280_);
lean_dec_ref(v_ss_1278_);
lean_dec_ref(v_opAs_1270_);
v___x_1315_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__4);
v___x_1316_ = l_Lean_MessageData_ofName(v_introThm_1269_);
if (v_isShared_1303_ == 0)
{
lean_ctor_set_tag(v___x_1302_, 7);
lean_ctor_set(v___x_1302_, 1, v___x_1316_);
lean_ctor_set(v___x_1302_, 0, v___x_1315_);
v___x_1318_ = v___x_1302_;
goto v_reusejp_1317_;
}
else
{
lean_object* v_reuseFailAlloc_1334_; 
v_reuseFailAlloc_1334_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1334_, 0, v___x_1315_);
lean_ctor_set(v_reuseFailAlloc_1334_, 1, v___x_1316_);
v___x_1318_ = v_reuseFailAlloc_1334_;
goto v_reusejp_1317_;
}
v_reusejp_1317_:
{
lean_object* v___x_1319_; lean_object* v___x_1321_; 
v___x_1319_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkExcessArgsFrameApply___closed__1, &l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkExcessArgsFrameApply___closed__1_once, _init_l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkExcessArgsFrameApply___closed__1);
if (v_isShared_1292_ == 0)
{
lean_ctor_set_tag(v___x_1291_, 7);
lean_ctor_set(v___x_1291_, 1, v___x_1319_);
lean_ctor_set(v___x_1291_, 0, v___x_1318_);
v___x_1321_ = v___x_1291_;
goto v_reusejp_1320_;
}
else
{
lean_object* v_reuseFailAlloc_1333_; 
v_reuseFailAlloc_1333_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1333_, 0, v___x_1318_);
lean_ctor_set(v_reuseFailAlloc_1333_, 1, v___x_1319_);
v___x_1321_ = v_reuseFailAlloc_1333_;
goto v_reusejp_1320_;
}
v_reusejp_1320_:
{
lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v_a_1325_; lean_object* v___x_1327_; uint8_t v_isShared_1328_; uint8_t v_isSharedCheck_1332_; 
v___x_1322_ = l_Lean_MessageData_ofExpr(v_a_1311_);
v___x_1323_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1323_, 0, v___x_1321_);
lean_ctor_set(v___x_1323_, 1, v___x_1322_);
v___x_1324_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__1___redArg(v___x_1323_, v_a_1273_, v_a_1274_, v_a_1275_, v_a_1276_);
v_a_1325_ = lean_ctor_get(v___x_1324_, 0);
v_isSharedCheck_1332_ = !lean_is_exclusive(v___x_1324_);
if (v_isSharedCheck_1332_ == 0)
{
v___x_1327_ = v___x_1324_;
v_isShared_1328_ = v_isSharedCheck_1332_;
goto v_resetjp_1326_;
}
else
{
lean_inc(v_a_1325_);
lean_dec(v___x_1324_);
v___x_1327_ = lean_box(0);
v_isShared_1328_ = v_isSharedCheck_1332_;
goto v_resetjp_1326_;
}
v_resetjp_1326_:
{
lean_object* v___x_1330_; 
if (v_isShared_1328_ == 0)
{
v___x_1330_ = v___x_1327_;
goto v_reusejp_1329_;
}
else
{
lean_object* v_reuseFailAlloc_1331_; 
v_reuseFailAlloc_1331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1331_, 0, v_a_1325_);
v___x_1330_ = v_reuseFailAlloc_1331_;
goto v_reusejp_1329_;
}
v_reusejp_1329_:
{
return v___x_1330_;
}
}
}
}
}
else
{
lean_dec(v_a_1311_);
lean_del_object(v___x_1302_);
lean_del_object(v___x_1291_);
lean_dec(v_introThm_1269_);
v___y_1294_ = v_a_1273_;
v___y_1295_ = v_a_1274_;
v___y_1296_ = v_a_1275_;
v___y_1297_ = v_a_1276_;
goto v___jp_1293_;
}
}
else
{
lean_object* v_a_1335_; lean_object* v___x_1337_; uint8_t v_isShared_1338_; uint8_t v_isSharedCheck_1342_; 
lean_dec(v_a_1311_);
lean_del_object(v___x_1302_);
lean_del_object(v___x_1291_);
lean_dec(v_fst_1288_);
lean_dec(v_a_1282_);
lean_dec(v_a_1280_);
lean_dec_ref(v_ss_1278_);
lean_dec_ref(v_opAs_1270_);
lean_dec(v_introThm_1269_);
v_a_1335_ = lean_ctor_get(v___x_1312_, 0);
v_isSharedCheck_1342_ = !lean_is_exclusive(v___x_1312_);
if (v_isSharedCheck_1342_ == 0)
{
v___x_1337_ = v___x_1312_;
v_isShared_1338_ = v_isSharedCheck_1342_;
goto v_resetjp_1336_;
}
else
{
lean_inc(v_a_1335_);
lean_dec(v___x_1312_);
v___x_1337_ = lean_box(0);
v_isShared_1338_ = v_isSharedCheck_1342_;
goto v_resetjp_1336_;
}
v_resetjp_1336_:
{
lean_object* v___x_1340_; 
if (v_isShared_1338_ == 0)
{
v___x_1340_ = v___x_1337_;
goto v_reusejp_1339_;
}
else
{
lean_object* v_reuseFailAlloc_1341_; 
v_reuseFailAlloc_1341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1341_, 0, v_a_1335_);
v___x_1340_ = v_reuseFailAlloc_1341_;
goto v_reusejp_1339_;
}
v_reusejp_1339_:
{
return v___x_1340_;
}
}
}
}
else
{
lean_del_object(v___x_1302_);
lean_dec(v_snd_1300_);
lean_del_object(v___x_1291_);
lean_dec(v_fst_1288_);
lean_dec(v_a_1282_);
lean_dec(v_a_1280_);
lean_dec_ref(v_ss_1278_);
lean_dec_ref(v_opAs_1270_);
lean_dec(v_introThm_1269_);
return v___x_1310_;
}
}
}
}
else
{
lean_object* v_a_1346_; lean_object* v___x_1348_; uint8_t v_isShared_1349_; uint8_t v_isSharedCheck_1353_; 
lean_dec(v_a_1282_);
lean_dec(v_a_1280_);
lean_dec_ref(v_ss_1278_);
lean_dec_ref(v_opAs_1270_);
lean_dec(v_introThm_1269_);
v_a_1346_ = lean_ctor_get(v___x_1286_, 0);
v_isSharedCheck_1353_ = !lean_is_exclusive(v___x_1286_);
if (v_isSharedCheck_1353_ == 0)
{
v___x_1348_ = v___x_1286_;
v_isShared_1349_ = v_isSharedCheck_1353_;
goto v_resetjp_1347_;
}
else
{
lean_inc(v_a_1346_);
lean_dec(v___x_1286_);
v___x_1348_ = lean_box(0);
v_isShared_1349_ = v_isSharedCheck_1353_;
goto v_resetjp_1347_;
}
v_resetjp_1347_:
{
lean_object* v___x_1351_; 
if (v_isShared_1349_ == 0)
{
v___x_1351_ = v___x_1348_;
goto v_reusejp_1350_;
}
else
{
lean_object* v_reuseFailAlloc_1352_; 
v_reuseFailAlloc_1352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1352_, 0, v_a_1346_);
v___x_1351_ = v_reuseFailAlloc_1352_;
goto v_reusejp_1350_;
}
v_reusejp_1350_:
{
return v___x_1351_;
}
}
}
}
else
{
lean_dec(v_a_1282_);
lean_dec(v_a_1280_);
lean_dec_ref(v_ss_1278_);
lean_dec_ref(v_opAs_1270_);
lean_dec(v_introThm_1269_);
return v___x_1283_;
}
}
else
{
lean_dec(v_a_1280_);
lean_dec_ref(v_ss_1278_);
lean_dec_ref(v_opAs_1270_);
lean_dec(v_introThm_1269_);
return v___x_1281_;
}
}
else
{
lean_object* v_a_1354_; lean_object* v___x_1356_; uint8_t v_isShared_1357_; uint8_t v_isSharedCheck_1361_; 
lean_dec_ref(v_ss_1278_);
lean_dec_ref(v_opAs_1270_);
lean_dec(v_introThm_1269_);
v_a_1354_ = lean_ctor_get(v___x_1279_, 0);
v_isSharedCheck_1361_ = !lean_is_exclusive(v___x_1279_);
if (v_isSharedCheck_1361_ == 0)
{
v___x_1356_ = v___x_1279_;
v_isShared_1357_ = v_isSharedCheck_1361_;
goto v_resetjp_1355_;
}
else
{
lean_inc(v_a_1354_);
lean_dec(v___x_1279_);
v___x_1356_ = lean_box(0);
v_isShared_1357_ = v_isSharedCheck_1361_;
goto v_resetjp_1355_;
}
v_resetjp_1355_:
{
lean_object* v___x_1359_; 
if (v_isShared_1357_ == 0)
{
v___x_1359_ = v___x_1356_;
goto v_reusejp_1358_;
}
else
{
lean_object* v_reuseFailAlloc_1360_; 
v_reuseFailAlloc_1360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1360_, 0, v_a_1354_);
v___x_1359_ = v_reuseFailAlloc_1360_;
goto v_reusejp_1358_;
}
v_reusejp_1358_:
{
return v___x_1359_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkExcessArgsFrameApply___boxed(lean_object* v_introThm_1362_, lean_object* v_opAs_1363_, lean_object* v_pre_1364_, lean_object* v_ss_1365_, lean_object* v_a_1366_, lean_object* v_a_1367_, lean_object* v_a_1368_, lean_object* v_a_1369_, lean_object* v_a_1370_){
_start:
{
lean_object* v_res_1371_; 
v_res_1371_ = l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkExcessArgsFrameApply(v_introThm_1362_, v_opAs_1363_, v_pre_1364_, v_ss_1365_, v_a_1366_, v_a_1367_, v_a_1368_, v_a_1369_);
lean_dec(v_a_1369_);
lean_dec_ref(v_a_1368_);
lean_dec(v_a_1367_);
lean_dec_ref(v_a_1366_);
return v_res_1371_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__0___redArg(size_t v_sz_1372_, size_t v_i_1373_, lean_object* v_bs_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_){
_start:
{
uint8_t v___x_1380_; 
v___x_1380_ = lean_usize_dec_lt(v_i_1373_, v_sz_1372_);
if (v___x_1380_ == 0)
{
lean_object* v___x_1381_; 
v___x_1381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1381_, 0, v_bs_1374_);
return v___x_1381_;
}
else
{
lean_object* v_v_1382_; lean_object* v___x_1383_; lean_object* v_bs_x27_1384_; lean_object* v___y_1386_; lean_object* v___x_1400_; 
v_v_1382_ = lean_array_uget(v_bs_1374_, v_i_1373_);
v___x_1383_ = lean_unsigned_to_nat(0u);
v_bs_x27_1384_ = lean_array_uset(v_bs_1374_, v_i_1373_, v___x_1383_);
lean_inc(v___y_1378_);
lean_inc_ref(v___y_1377_);
lean_inc(v___y_1376_);
lean_inc_ref(v___y_1375_);
v___x_1400_ = lean_infer_type(v_v_1382_, v___y_1375_, v___y_1376_, v___y_1377_, v___y_1378_);
if (lean_obj_tag(v___x_1400_) == 0)
{
lean_object* v_a_1401_; lean_object* v___x_1403_; uint8_t v_isShared_1404_; uint8_t v_isSharedCheck_1411_; 
v_a_1401_ = lean_ctor_get(v___x_1400_, 0);
v_isSharedCheck_1411_ = !lean_is_exclusive(v___x_1400_);
if (v_isSharedCheck_1411_ == 0)
{
v___x_1403_ = v___x_1400_;
v_isShared_1404_ = v_isSharedCheck_1411_;
goto v_resetjp_1402_;
}
else
{
lean_inc(v_a_1401_);
lean_dec(v___x_1400_);
v___x_1403_ = lean_box(0);
v_isShared_1404_ = v_isSharedCheck_1411_;
goto v_resetjp_1402_;
}
v_resetjp_1402_:
{
lean_object* v___x_1406_; 
if (v_isShared_1404_ == 0)
{
lean_ctor_set_tag(v___x_1403_, 1);
v___x_1406_ = v___x_1403_;
goto v_reusejp_1405_;
}
else
{
lean_object* v_reuseFailAlloc_1410_; 
v_reuseFailAlloc_1410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1410_, 0, v_a_1401_);
v___x_1406_ = v_reuseFailAlloc_1410_;
goto v_reusejp_1405_;
}
v_reusejp_1405_:
{
uint8_t v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; 
v___x_1407_ = 0;
v___x_1408_ = lean_box(0);
v___x_1409_ = l_Lean_Meta_mkFreshExprMVar(v___x_1406_, v___x_1407_, v___x_1408_, v___y_1375_, v___y_1376_, v___y_1377_, v___y_1378_);
v___y_1386_ = v___x_1409_;
goto v___jp_1385_;
}
}
}
else
{
v___y_1386_ = v___x_1400_;
goto v___jp_1385_;
}
v___jp_1385_:
{
if (lean_obj_tag(v___y_1386_) == 0)
{
lean_object* v_a_1387_; size_t v___x_1388_; size_t v___x_1389_; lean_object* v___x_1390_; 
v_a_1387_ = lean_ctor_get(v___y_1386_, 0);
lean_inc(v_a_1387_);
lean_dec_ref_known(v___y_1386_, 1);
v___x_1388_ = ((size_t)1ULL);
v___x_1389_ = lean_usize_add(v_i_1373_, v___x_1388_);
v___x_1390_ = lean_array_uset(v_bs_x27_1384_, v_i_1373_, v_a_1387_);
v_i_1373_ = v___x_1389_;
v_bs_1374_ = v___x_1390_;
goto _start;
}
else
{
lean_object* v_a_1392_; lean_object* v___x_1394_; uint8_t v_isShared_1395_; uint8_t v_isSharedCheck_1399_; 
lean_dec_ref(v_bs_x27_1384_);
v_a_1392_ = lean_ctor_get(v___y_1386_, 0);
v_isSharedCheck_1399_ = !lean_is_exclusive(v___y_1386_);
if (v_isSharedCheck_1399_ == 0)
{
v___x_1394_ = v___y_1386_;
v_isShared_1395_ = v_isSharedCheck_1399_;
goto v_resetjp_1393_;
}
else
{
lean_inc(v_a_1392_);
lean_dec(v___y_1386_);
v___x_1394_ = lean_box(0);
v_isShared_1395_ = v_isSharedCheck_1399_;
goto v_resetjp_1393_;
}
v_resetjp_1393_:
{
lean_object* v___x_1397_; 
if (v_isShared_1395_ == 0)
{
v___x_1397_ = v___x_1394_;
goto v_reusejp_1396_;
}
else
{
lean_object* v_reuseFailAlloc_1398_; 
v_reuseFailAlloc_1398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1398_, 0, v_a_1392_);
v___x_1397_ = v_reuseFailAlloc_1398_;
goto v_reusejp_1396_;
}
v_reusejp_1396_:
{
return v___x_1397_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__0___redArg___boxed(lean_object* v_sz_1412_, lean_object* v_i_1413_, lean_object* v_bs_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_){
_start:
{
size_t v_sz_boxed_1420_; size_t v_i_boxed_1421_; lean_object* v_res_1422_; 
v_sz_boxed_1420_ = lean_unbox_usize(v_sz_1412_);
lean_dec(v_sz_1412_);
v_i_boxed_1421_ = lean_unbox_usize(v_i_1413_);
lean_dec(v_i_1413_);
v_res_1422_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__0___redArg(v_sz_boxed_1420_, v_i_boxed_1421_, v_bs_1414_, v___y_1415_, v___y_1416_, v___y_1417_, v___y_1418_);
lean_dec(v___y_1418_);
lean_dec_ref(v___y_1417_);
lean_dec(v___y_1416_);
lean_dec_ref(v___y_1415_);
return v_res_1422_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__1_spec__1___redArg(lean_object* v_a_1423_, lean_object* v_x_1424_){
_start:
{
if (lean_obj_tag(v_x_1424_) == 0)
{
lean_object* v___x_1425_; 
v___x_1425_ = lean_box(0);
return v___x_1425_;
}
else
{
lean_object* v_key_1426_; lean_object* v_value_1427_; lean_object* v_tail_1428_; uint8_t v___x_1429_; 
v_key_1426_ = lean_ctor_get(v_x_1424_, 0);
v_value_1427_ = lean_ctor_get(v_x_1424_, 1);
v_tail_1428_ = lean_ctor_get(v_x_1424_, 2);
v___x_1429_ = lean_name_eq(v_key_1426_, v_a_1423_);
if (v___x_1429_ == 0)
{
v_x_1424_ = v_tail_1428_;
goto _start;
}
else
{
lean_object* v___x_1431_; 
lean_inc(v_value_1427_);
v___x_1431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1431_, 0, v_value_1427_);
return v___x_1431_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__1_spec__1___redArg___boxed(lean_object* v_a_1432_, lean_object* v_x_1433_){
_start:
{
lean_object* v_res_1434_; 
v_res_1434_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__1_spec__1___redArg(v_a_1432_, v_x_1433_);
lean_dec(v_x_1433_);
lean_dec(v_a_1432_);
return v_res_1434_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__1___redArg(lean_object* v_m_1435_, lean_object* v_a_1436_){
_start:
{
lean_object* v_buckets_1437_; lean_object* v___x_1438_; uint64_t v___y_1440_; 
v_buckets_1437_ = lean_ctor_get(v_m_1435_, 1);
v___x_1438_ = lean_array_get_size(v_buckets_1437_);
if (lean_obj_tag(v_a_1436_) == 0)
{
uint64_t v___x_1454_; 
v___x_1454_ = 1723ULL;
v___y_1440_ = v___x_1454_;
goto v___jp_1439_;
}
else
{
uint64_t v_hash_1455_; 
v_hash_1455_ = lean_ctor_get_uint64(v_a_1436_, sizeof(void*)*2);
v___y_1440_ = v_hash_1455_;
goto v___jp_1439_;
}
v___jp_1439_:
{
uint64_t v___x_1441_; uint64_t v___x_1442_; uint64_t v_fold_1443_; uint64_t v___x_1444_; uint64_t v___x_1445_; uint64_t v___x_1446_; size_t v___x_1447_; size_t v___x_1448_; size_t v___x_1449_; size_t v___x_1450_; size_t v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; 
v___x_1441_ = 32ULL;
v___x_1442_ = lean_uint64_shift_right(v___y_1440_, v___x_1441_);
v_fold_1443_ = lean_uint64_xor(v___y_1440_, v___x_1442_);
v___x_1444_ = 16ULL;
v___x_1445_ = lean_uint64_shift_right(v_fold_1443_, v___x_1444_);
v___x_1446_ = lean_uint64_xor(v_fold_1443_, v___x_1445_);
v___x_1447_ = lean_uint64_to_usize(v___x_1446_);
v___x_1448_ = lean_usize_of_nat(v___x_1438_);
v___x_1449_ = ((size_t)1ULL);
v___x_1450_ = lean_usize_sub(v___x_1448_, v___x_1449_);
v___x_1451_ = lean_usize_land(v___x_1447_, v___x_1450_);
v___x_1452_ = lean_array_uget_borrowed(v_buckets_1437_, v___x_1451_);
v___x_1453_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__1_spec__1___redArg(v_a_1436_, v___x_1452_);
return v___x_1453_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__1___redArg___boxed(lean_object* v_m_1456_, lean_object* v_a_1457_){
_start:
{
lean_object* v_res_1458_; 
v_res_1458_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__1___redArg(v_m_1456_, v_a_1457_);
lean_dec(v_a_1457_);
lean_dec_ref(v_m_1456_);
return v_res_1458_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__2___closed__4(void){
_start:
{
lean_object* v___x_1465_; lean_object* v___x_1466_; 
v___x_1465_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__2___closed__3));
v___x_1466_ = l_Lean_stringToMessageData(v___x_1465_);
return v___x_1466_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__2___closed__6(void){
_start:
{
lean_object* v___x_1468_; lean_object* v___x_1469_; 
v___x_1468_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__2___closed__5));
v___x_1469_ = l_Lean_stringToMessageData(v___x_1468_);
return v___x_1469_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__2(lean_object* v_op_1470_, lean_object* v___y_1471_, lean_object* v_a_1472_, lean_object* v_x_1473_, lean_object* v_x_1474_, lean_object* v_x_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_){
_start:
{
lean_object* v_prf_1484_; lean_object* v___y_1485_; lean_object* v___y_1486_; lean_object* v___y_1487_; lean_object* v___y_1488_; 
if (lean_obj_tag(v_x_1473_) == 5)
{
lean_object* v_fn_1505_; lean_object* v_arg_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; 
v_fn_1505_ = lean_ctor_get(v_x_1473_, 0);
lean_inc_ref(v_fn_1505_);
v_arg_1506_ = lean_ctor_get(v_x_1473_, 1);
lean_inc_ref(v_arg_1506_);
lean_dec_ref_known(v_x_1473_, 2);
v___x_1507_ = lean_array_set(v_x_1474_, v_x_1475_, v_arg_1506_);
v___x_1508_ = lean_unsigned_to_nat(1u);
v___x_1509_ = lean_nat_sub(v_x_1475_, v___x_1508_);
lean_dec(v_x_1475_);
v_x_1473_ = v_fn_1505_;
v_x_1474_ = v___x_1507_;
v_x_1475_ = v___x_1509_;
goto _start;
}
else
{
lean_object* v_head_1511_; lean_object* v_numConst_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; size_t v_sz_1516_; size_t v___x_1517_; lean_object* v___x_1518_; 
lean_dec(v_x_1475_);
v_head_1511_ = lean_ctor_get(v_op_1470_, 0);
lean_inc(v_head_1511_);
v_numConst_1512_ = lean_ctor_get(v_op_1470_, 1);
lean_inc_n(v_numConst_1512_, 2);
lean_dec_ref(v_op_1470_);
v___x_1513_ = lean_unsigned_to_nat(0u);
v___x_1514_ = lean_array_get_size(v_x_1474_);
v___x_1515_ = l_Array_extract___redArg(v_x_1474_, v_numConst_1512_, v___x_1514_);
v_sz_1516_ = lean_array_size(v___x_1515_);
v___x_1517_ = ((size_t)0ULL);
v___x_1518_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__0___redArg(v_sz_1516_, v___x_1517_, v___x_1515_, v___y_1478_, v___y_1479_, v___y_1480_, v___y_1481_);
if (lean_obj_tag(v___x_1518_) == 0)
{
lean_object* v_a_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; 
v_a_1519_ = lean_ctor_get(v___x_1518_, 0);
lean_inc(v_a_1519_);
lean_dec_ref_known(v___x_1518_, 1);
v___x_1520_ = l_Array_extract___redArg(v_x_1474_, v___x_1513_, v_numConst_1512_);
lean_dec_ref(v_x_1474_);
v___x_1521_ = l_Array_append___redArg(v___x_1520_, v_a_1519_);
lean_dec(v_a_1519_);
v___x_1522_ = l_Lean_mkAppN(v_x_1473_, v___x_1521_);
lean_dec_ref(v___x_1521_);
v___x_1523_ = lean_unsigned_to_nat(256u);
lean_inc_ref(v___x_1522_);
v___x_1524_ = l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp(v___y_1471_, v___x_1522_, v___x_1523_, v___y_1476_, v___y_1477_, v___y_1478_, v___y_1479_, v___y_1480_, v___y_1481_);
if (lean_obj_tag(v___x_1524_) == 0)
{
lean_object* v_a_1525_; lean_object* v_fst_1526_; lean_object* v_snd_1527_; lean_object* v___x_1529_; uint8_t v_isShared_1530_; uint8_t v_isSharedCheck_1699_; 
v_a_1525_ = lean_ctor_get(v___x_1524_, 0);
lean_inc(v_a_1525_);
lean_dec_ref_known(v___x_1524_, 1);
v_fst_1526_ = lean_ctor_get(v_a_1525_, 0);
v_snd_1527_ = lean_ctor_get(v_a_1525_, 1);
v_isSharedCheck_1699_ = !lean_is_exclusive(v_a_1525_);
if (v_isSharedCheck_1699_ == 0)
{
v___x_1529_ = v_a_1525_;
v_isShared_1530_ = v_isSharedCheck_1699_;
goto v_resetjp_1528_;
}
else
{
lean_inc(v_snd_1527_);
lean_inc(v_fst_1526_);
lean_dec(v_a_1525_);
v___x_1529_ = lean_box(0);
v_isShared_1530_ = v_isSharedCheck_1699_;
goto v_resetjp_1528_;
}
v_resetjp_1528_:
{
lean_object* v___x_1531_; 
lean_inc(v___y_1481_);
lean_inc_ref(v___y_1480_);
lean_inc(v___y_1479_);
lean_inc_ref(v___y_1478_);
v___x_1531_ = lean_infer_type(v___x_1522_, v___y_1478_, v___y_1479_, v___y_1480_, v___y_1481_);
if (lean_obj_tag(v___x_1531_) == 0)
{
lean_object* v_a_1532_; lean_object* v___x_1533_; uint8_t v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; 
v_a_1532_ = lean_ctor_get(v___x_1531_, 0);
lean_inc(v_a_1532_);
lean_dec_ref_known(v___x_1531_, 1);
v___x_1533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1533_, 0, v_a_1532_);
v___x_1534_ = 0;
v___x_1535_ = lean_box(0);
v___x_1536_ = l_Lean_Meta_mkFreshExprMVar(v___x_1533_, v___x_1534_, v___x_1535_, v___y_1478_, v___y_1479_, v___y_1480_, v___y_1481_);
if (lean_obj_tag(v___x_1536_) == 0)
{
lean_object* v_a_1537_; lean_object* v___y_1539_; lean_object* v___y_1540_; lean_object* v___y_1541_; lean_object* v___y_1542_; lean_object* v___y_1543_; lean_object* v___y_1544_; lean_object* v_a_1545_; lean_object* v___y_1593_; lean_object* v_eqProof_1594_; lean_object* v___y_1595_; lean_object* v___y_1596_; lean_object* v___y_1597_; lean_object* v___y_1598_; lean_object* v___x_1626_; lean_object* v___y_1628_; lean_object* v___x_1681_; 
v_a_1537_ = lean_ctor_get(v___x_1536_, 0);
lean_inc(v_a_1537_);
lean_dec_ref_known(v___x_1536_, 1);
v___x_1626_ = l_Lean_Expr_getAppFn(v_fst_1526_);
v___x_1681_ = l_Lean_Expr_constName_x3f(v___x_1626_);
if (lean_obj_tag(v___x_1681_) == 0)
{
v___y_1628_ = v___x_1535_;
goto v___jp_1627_;
}
else
{
lean_object* v_val_1682_; 
v_val_1682_ = lean_ctor_get(v___x_1681_, 0);
lean_inc(v_val_1682_);
lean_dec_ref_known(v___x_1681_, 1);
v___y_1628_ = v_val_1682_;
goto v___jp_1627_;
}
v___jp_1538_:
{
lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; 
v___x_1546_ = lean_unsigned_to_nat(1u);
v___x_1547_ = lean_mk_empty_array_with_capacity(v___x_1546_);
lean_inc_ref(v___x_1547_);
v___x_1548_ = lean_array_push(v___x_1547_, v_a_1537_);
v___x_1549_ = l_Lean_Meta_mkAppM(v___y_1541_, v___x_1548_, v___y_1540_, v___y_1539_, v___y_1543_, v___y_1542_);
if (lean_obj_tag(v___x_1549_) == 0)
{
lean_object* v_a_1550_; lean_object* v___x_1551_; 
v_a_1550_ = lean_ctor_get(v___x_1549_, 0);
lean_inc(v_a_1550_);
lean_dec_ref_known(v___x_1549_, 1);
v___x_1551_ = l_Lean_Meta_mkCongrArg(v_a_1550_, v___y_1544_, v___y_1540_, v___y_1539_, v___y_1543_, v___y_1542_);
if (lean_obj_tag(v___x_1551_) == 0)
{
lean_object* v_a_1552_; lean_object* v___x_1553_; 
v_a_1552_ = lean_ctor_get(v___x_1551_, 0);
lean_inc(v_a_1552_);
lean_dec_ref_known(v___x_1551_, 1);
v___x_1553_ = l_Lean_Meta_mkEqSymm(v_a_1552_, v___y_1540_, v___y_1539_, v___y_1543_, v___y_1542_);
if (lean_obj_tag(v___x_1553_) == 0)
{
lean_object* v_a_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; 
v_a_1554_ = lean_ctor_get(v___x_1553_, 0);
lean_inc(v_a_1554_);
lean_dec_ref_known(v___x_1553_, 1);
v___x_1555_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__2___closed__2));
v___x_1556_ = lean_array_push(v___x_1547_, v_a_1554_);
v___x_1557_ = l_Lean_Meta_mkAppM(v___x_1555_, v___x_1556_, v___y_1540_, v___y_1539_, v___y_1543_, v___y_1542_);
if (lean_obj_tag(v___x_1557_) == 0)
{
lean_object* v_a_1558_; lean_object* v___x_1559_; 
v_a_1558_ = lean_ctor_get(v___x_1557_, 0);
lean_inc(v_a_1558_);
lean_dec_ref_known(v___x_1557_, 1);
v___x_1559_ = l_Lean_Expr_app___override(v_a_1558_, v_a_1545_);
v_prf_1484_ = v___x_1559_;
v___y_1485_ = v___y_1540_;
v___y_1486_ = v___y_1539_;
v___y_1487_ = v___y_1543_;
v___y_1488_ = v___y_1542_;
goto v___jp_1483_;
}
else
{
lean_object* v_a_1560_; lean_object* v___x_1562_; uint8_t v_isShared_1563_; uint8_t v_isSharedCheck_1567_; 
lean_dec_ref(v_a_1545_);
v_a_1560_ = lean_ctor_get(v___x_1557_, 0);
v_isSharedCheck_1567_ = !lean_is_exclusive(v___x_1557_);
if (v_isSharedCheck_1567_ == 0)
{
v___x_1562_ = v___x_1557_;
v_isShared_1563_ = v_isSharedCheck_1567_;
goto v_resetjp_1561_;
}
else
{
lean_inc(v_a_1560_);
lean_dec(v___x_1557_);
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
else
{
lean_object* v_a_1568_; lean_object* v___x_1570_; uint8_t v_isShared_1571_; uint8_t v_isSharedCheck_1575_; 
lean_dec_ref(v___x_1547_);
lean_dec_ref(v_a_1545_);
v_a_1568_ = lean_ctor_get(v___x_1553_, 0);
v_isSharedCheck_1575_ = !lean_is_exclusive(v___x_1553_);
if (v_isSharedCheck_1575_ == 0)
{
v___x_1570_ = v___x_1553_;
v_isShared_1571_ = v_isSharedCheck_1575_;
goto v_resetjp_1569_;
}
else
{
lean_inc(v_a_1568_);
lean_dec(v___x_1553_);
v___x_1570_ = lean_box(0);
v_isShared_1571_ = v_isSharedCheck_1575_;
goto v_resetjp_1569_;
}
v_resetjp_1569_:
{
lean_object* v___x_1573_; 
if (v_isShared_1571_ == 0)
{
v___x_1573_ = v___x_1570_;
goto v_reusejp_1572_;
}
else
{
lean_object* v_reuseFailAlloc_1574_; 
v_reuseFailAlloc_1574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1574_, 0, v_a_1568_);
v___x_1573_ = v_reuseFailAlloc_1574_;
goto v_reusejp_1572_;
}
v_reusejp_1572_:
{
return v___x_1573_;
}
}
}
}
else
{
lean_object* v_a_1576_; lean_object* v___x_1578_; uint8_t v_isShared_1579_; uint8_t v_isSharedCheck_1583_; 
lean_dec_ref(v___x_1547_);
lean_dec_ref(v_a_1545_);
v_a_1576_ = lean_ctor_get(v___x_1551_, 0);
v_isSharedCheck_1583_ = !lean_is_exclusive(v___x_1551_);
if (v_isSharedCheck_1583_ == 0)
{
v___x_1578_ = v___x_1551_;
v_isShared_1579_ = v_isSharedCheck_1583_;
goto v_resetjp_1577_;
}
else
{
lean_inc(v_a_1576_);
lean_dec(v___x_1551_);
v___x_1578_ = lean_box(0);
v_isShared_1579_ = v_isSharedCheck_1583_;
goto v_resetjp_1577_;
}
v_resetjp_1577_:
{
lean_object* v___x_1581_; 
if (v_isShared_1579_ == 0)
{
v___x_1581_ = v___x_1578_;
goto v_reusejp_1580_;
}
else
{
lean_object* v_reuseFailAlloc_1582_; 
v_reuseFailAlloc_1582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1582_, 0, v_a_1576_);
v___x_1581_ = v_reuseFailAlloc_1582_;
goto v_reusejp_1580_;
}
v_reusejp_1580_:
{
return v___x_1581_;
}
}
}
}
else
{
lean_object* v_a_1584_; lean_object* v___x_1586_; uint8_t v_isShared_1587_; uint8_t v_isSharedCheck_1591_; 
lean_dec_ref(v___x_1547_);
lean_dec_ref(v_a_1545_);
lean_dec_ref(v___y_1544_);
v_a_1584_ = lean_ctor_get(v___x_1549_, 0);
v_isSharedCheck_1591_ = !lean_is_exclusive(v___x_1549_);
if (v_isSharedCheck_1591_ == 0)
{
v___x_1586_ = v___x_1549_;
v_isShared_1587_ = v_isSharedCheck_1591_;
goto v_resetjp_1585_;
}
else
{
lean_inc(v_a_1584_);
lean_dec(v___x_1549_);
v___x_1586_ = lean_box(0);
v_isShared_1587_ = v_isSharedCheck_1591_;
goto v_resetjp_1585_;
}
v_resetjp_1585_:
{
lean_object* v___x_1589_; 
if (v_isShared_1587_ == 0)
{
v___x_1589_ = v___x_1586_;
goto v_reusejp_1588_;
}
else
{
lean_object* v_reuseFailAlloc_1590_; 
v_reuseFailAlloc_1590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1590_, 0, v_a_1584_);
v___x_1589_ = v_reuseFailAlloc_1590_;
goto v_reusejp_1588_;
}
v_reusejp_1588_:
{
return v___x_1589_;
}
}
}
}
v___jp_1592_:
{
lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; 
v___x_1599_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals_spec__2___closed__2));
v___x_1600_ = lean_unsigned_to_nat(2u);
v___x_1601_ = lean_mk_empty_array_with_capacity(v___x_1600_);
lean_inc(v_a_1537_);
v___x_1602_ = lean_array_push(v___x_1601_, v_a_1537_);
v___x_1603_ = lean_array_push(v___x_1602_, v_fst_1526_);
v___x_1604_ = l_Lean_Meta_mkAppM(v___x_1599_, v___x_1603_, v___y_1595_, v___y_1596_, v___y_1597_, v___y_1598_);
if (lean_obj_tag(v___x_1604_) == 0)
{
if (lean_obj_tag(v___y_1593_) == 0)
{
lean_object* v_a_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; 
v_a_1605_ = lean_ctor_get(v___x_1604_, 0);
lean_inc(v_a_1605_);
lean_dec_ref_known(v___x_1604_, 1);
v___x_1606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1606_, 0, v_a_1605_);
v___x_1607_ = l_Lean_Meta_mkFreshExprMVar(v___x_1606_, v___x_1534_, v___x_1535_, v___y_1595_, v___y_1596_, v___y_1597_, v___y_1598_);
if (lean_obj_tag(v___x_1607_) == 0)
{
lean_object* v_a_1608_; 
v_a_1608_ = lean_ctor_get(v___x_1607_, 0);
lean_inc(v_a_1608_);
lean_dec_ref_known(v___x_1607_, 1);
v___y_1539_ = v___y_1596_;
v___y_1540_ = v___y_1595_;
v___y_1541_ = v___x_1599_;
v___y_1542_ = v___y_1598_;
v___y_1543_ = v___y_1597_;
v___y_1544_ = v_eqProof_1594_;
v_a_1545_ = v_a_1608_;
goto v___jp_1538_;
}
else
{
lean_object* v_a_1609_; lean_object* v___x_1611_; uint8_t v_isShared_1612_; uint8_t v_isSharedCheck_1616_; 
lean_dec_ref(v_eqProof_1594_);
lean_dec(v_a_1537_);
v_a_1609_ = lean_ctor_get(v___x_1607_, 0);
v_isSharedCheck_1616_ = !lean_is_exclusive(v___x_1607_);
if (v_isSharedCheck_1616_ == 0)
{
v___x_1611_ = v___x_1607_;
v_isShared_1612_ = v_isSharedCheck_1616_;
goto v_resetjp_1610_;
}
else
{
lean_inc(v_a_1609_);
lean_dec(v___x_1607_);
v___x_1611_ = lean_box(0);
v_isShared_1612_ = v_isSharedCheck_1616_;
goto v_resetjp_1610_;
}
v_resetjp_1610_:
{
lean_object* v___x_1614_; 
if (v_isShared_1612_ == 0)
{
v___x_1614_ = v___x_1611_;
goto v_reusejp_1613_;
}
else
{
lean_object* v_reuseFailAlloc_1615_; 
v_reuseFailAlloc_1615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1615_, 0, v_a_1609_);
v___x_1614_ = v_reuseFailAlloc_1615_;
goto v_reusejp_1613_;
}
v_reusejp_1613_:
{
return v___x_1614_;
}
}
}
}
else
{
lean_object* v_val_1617_; 
lean_dec_ref_known(v___x_1604_, 1);
v_val_1617_ = lean_ctor_get(v___y_1593_, 0);
lean_inc(v_val_1617_);
lean_dec_ref_known(v___y_1593_, 1);
v___y_1539_ = v___y_1596_;
v___y_1540_ = v___y_1595_;
v___y_1541_ = v___x_1599_;
v___y_1542_ = v___y_1598_;
v___y_1543_ = v___y_1597_;
v___y_1544_ = v_eqProof_1594_;
v_a_1545_ = v_val_1617_;
goto v___jp_1538_;
}
}
else
{
lean_object* v_a_1618_; lean_object* v___x_1620_; uint8_t v_isShared_1621_; uint8_t v_isSharedCheck_1625_; 
lean_dec_ref(v_eqProof_1594_);
lean_dec(v___y_1593_);
lean_dec(v_a_1537_);
v_a_1618_ = lean_ctor_get(v___x_1604_, 0);
v_isSharedCheck_1625_ = !lean_is_exclusive(v___x_1604_);
if (v_isSharedCheck_1625_ == 0)
{
v___x_1620_ = v___x_1604_;
v_isShared_1621_ = v_isSharedCheck_1625_;
goto v_resetjp_1619_;
}
else
{
lean_inc(v_a_1618_);
lean_dec(v___x_1604_);
v___x_1620_ = lean_box(0);
v_isShared_1621_ = v_isSharedCheck_1625_;
goto v_resetjp_1619_;
}
v_resetjp_1619_:
{
lean_object* v___x_1623_; 
if (v_isShared_1621_ == 0)
{
v___x_1623_ = v___x_1620_;
goto v_reusejp_1622_;
}
else
{
lean_object* v_reuseFailAlloc_1624_; 
v_reuseFailAlloc_1624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1624_, 0, v_a_1618_);
v___x_1623_ = v_reuseFailAlloc_1624_;
goto v_reusejp_1622_;
}
v_reusejp_1622_:
{
return v___x_1623_;
}
}
}
}
v___jp_1627_:
{
lean_object* v___x_1629_; 
v___x_1629_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__1___redArg(v_a_1472_, v___y_1628_);
lean_dec(v___y_1628_);
if (lean_obj_tag(v___x_1629_) == 0)
{
lean_dec_ref(v___x_1626_);
if (lean_obj_tag(v_snd_1527_) == 0)
{
lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1633_; 
lean_dec(v_a_1537_);
lean_dec(v_fst_1526_);
v___x_1630_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__2___closed__4, &l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__2___closed__4_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__2___closed__4);
v___x_1631_ = l_Lean_MessageData_ofName(v_head_1511_);
if (v_isShared_1530_ == 0)
{
lean_ctor_set_tag(v___x_1529_, 7);
lean_ctor_set(v___x_1529_, 1, v___x_1631_);
lean_ctor_set(v___x_1529_, 0, v___x_1630_);
v___x_1633_ = v___x_1529_;
goto v_reusejp_1632_;
}
else
{
lean_object* v_reuseFailAlloc_1645_; 
v_reuseFailAlloc_1645_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1645_, 0, v___x_1630_);
lean_ctor_set(v_reuseFailAlloc_1645_, 1, v___x_1631_);
v___x_1633_ = v_reuseFailAlloc_1645_;
goto v_reusejp_1632_;
}
v_reusejp_1632_:
{
lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v_a_1637_; lean_object* v___x_1639_; uint8_t v_isShared_1640_; uint8_t v_isSharedCheck_1644_; 
v___x_1634_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__2___closed__6, &l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__2___closed__6_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__2___closed__6);
v___x_1635_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1635_, 0, v___x_1633_);
lean_ctor_set(v___x_1635_, 1, v___x_1634_);
v___x_1636_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_saturateLatticeOp_go_spec__0___redArg(v___x_1635_, v___y_1478_, v___y_1479_, v___y_1480_, v___y_1481_);
v_a_1637_ = lean_ctor_get(v___x_1636_, 0);
v_isSharedCheck_1644_ = !lean_is_exclusive(v___x_1636_);
if (v_isSharedCheck_1644_ == 0)
{
v___x_1639_ = v___x_1636_;
v_isShared_1640_ = v_isSharedCheck_1644_;
goto v_resetjp_1638_;
}
else
{
lean_inc(v_a_1637_);
lean_dec(v___x_1636_);
v___x_1639_ = lean_box(0);
v_isShared_1640_ = v_isSharedCheck_1644_;
goto v_resetjp_1638_;
}
v_resetjp_1638_:
{
lean_object* v___x_1642_; 
if (v_isShared_1640_ == 0)
{
v___x_1642_ = v___x_1639_;
goto v_reusejp_1641_;
}
else
{
lean_object* v_reuseFailAlloc_1643_; 
v_reuseFailAlloc_1643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1643_, 0, v_a_1637_);
v___x_1642_ = v_reuseFailAlloc_1643_;
goto v_reusejp_1641_;
}
v_reusejp_1641_:
{
return v___x_1642_;
}
}
}
}
else
{
lean_object* v_val_1646_; lean_object* v___x_1647_; 
lean_del_object(v___x_1529_);
lean_dec(v_head_1511_);
v_val_1646_ = lean_ctor_get(v_snd_1527_, 0);
lean_inc(v_val_1646_);
lean_dec_ref_known(v_snd_1527_, 1);
v___x_1647_ = lean_box(0);
v___y_1593_ = v___x_1647_;
v_eqProof_1594_ = v_val_1646_;
v___y_1595_ = v___y_1478_;
v___y_1596_ = v___y_1479_;
v___y_1597_ = v___y_1480_;
v___y_1598_ = v___y_1481_;
goto v___jp_1592_;
}
}
else
{
lean_object* v_val_1648_; lean_object* v_fst_1649_; lean_object* v_snd_1650_; lean_object* v_dummy_1651_; lean_object* v_nargs_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; 
lean_del_object(v___x_1529_);
lean_dec(v_head_1511_);
v_val_1648_ = lean_ctor_get(v___x_1629_, 0);
lean_inc(v_val_1648_);
lean_dec_ref_known(v___x_1629_, 1);
v_fst_1649_ = lean_ctor_get(v_val_1648_, 0);
lean_inc(v_fst_1649_);
v_snd_1650_ = lean_ctor_get(v_val_1648_, 1);
lean_inc_n(v_snd_1650_, 2);
lean_dec(v_val_1648_);
v_dummy_1651_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_projectsRewritableOperand___closed__0, &l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_projectsRewritableOperand___closed__0_once, _init_l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_projectsRewritableOperand___closed__0);
v_nargs_1652_ = l_Lean_Expr_getAppNumArgs(v_fst_1526_);
lean_inc(v_nargs_1652_);
v___x_1653_ = lean_mk_array(v_nargs_1652_, v_dummy_1651_);
v___x_1654_ = lean_unsigned_to_nat(1u);
v___x_1655_ = lean_nat_sub(v_nargs_1652_, v___x_1654_);
lean_dec(v_nargs_1652_);
lean_inc(v_fst_1526_);
v___x_1656_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_fst_1526_, v___x_1653_, v___x_1655_);
v___x_1657_ = l_Array_extract___redArg(v___x_1656_, v___x_1513_, v_snd_1650_);
v___x_1658_ = l_Lean_mkAppN(v___x_1626_, v___x_1657_);
lean_dec_ref(v___x_1657_);
v___x_1659_ = lean_array_get_size(v___x_1656_);
v___x_1660_ = l_Array_extract___redArg(v___x_1656_, v_snd_1650_, v___x_1659_);
lean_dec_ref(v___x_1656_);
v___x_1661_ = lean_array_to_list(v___x_1660_);
lean_inc(v_a_1537_);
v___x_1662_ = l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkExcessArgsFrameApply(v_fst_1649_, v___x_1658_, v_a_1537_, v___x_1661_, v___y_1478_, v___y_1479_, v___y_1480_, v___y_1481_);
if (lean_obj_tag(v___x_1662_) == 0)
{
if (lean_obj_tag(v_snd_1527_) == 0)
{
lean_object* v_a_1663_; 
lean_dec(v_a_1537_);
lean_dec(v_fst_1526_);
v_a_1663_ = lean_ctor_get(v___x_1662_, 0);
lean_inc(v_a_1663_);
lean_dec_ref_known(v___x_1662_, 1);
v_prf_1484_ = v_a_1663_;
v___y_1485_ = v___y_1478_;
v___y_1486_ = v___y_1479_;
v___y_1487_ = v___y_1480_;
v___y_1488_ = v___y_1481_;
goto v___jp_1483_;
}
else
{
lean_object* v_a_1664_; lean_object* v_val_1665_; lean_object* v___x_1667_; uint8_t v_isShared_1668_; uint8_t v_isSharedCheck_1672_; 
v_a_1664_ = lean_ctor_get(v___x_1662_, 0);
lean_inc(v_a_1664_);
lean_dec_ref_known(v___x_1662_, 1);
v_val_1665_ = lean_ctor_get(v_snd_1527_, 0);
v_isSharedCheck_1672_ = !lean_is_exclusive(v_snd_1527_);
if (v_isSharedCheck_1672_ == 0)
{
v___x_1667_ = v_snd_1527_;
v_isShared_1668_ = v_isSharedCheck_1672_;
goto v_resetjp_1666_;
}
else
{
lean_inc(v_val_1665_);
lean_dec(v_snd_1527_);
v___x_1667_ = lean_box(0);
v_isShared_1668_ = v_isSharedCheck_1672_;
goto v_resetjp_1666_;
}
v_resetjp_1666_:
{
lean_object* v___x_1670_; 
if (v_isShared_1668_ == 0)
{
lean_ctor_set(v___x_1667_, 0, v_a_1664_);
v___x_1670_ = v___x_1667_;
goto v_reusejp_1669_;
}
else
{
lean_object* v_reuseFailAlloc_1671_; 
v_reuseFailAlloc_1671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1671_, 0, v_a_1664_);
v___x_1670_ = v_reuseFailAlloc_1671_;
goto v_reusejp_1669_;
}
v_reusejp_1669_:
{
v___y_1593_ = v___x_1670_;
v_eqProof_1594_ = v_val_1665_;
v___y_1595_ = v___y_1478_;
v___y_1596_ = v___y_1479_;
v___y_1597_ = v___y_1480_;
v___y_1598_ = v___y_1481_;
goto v___jp_1592_;
}
}
}
}
else
{
lean_object* v_a_1673_; lean_object* v___x_1675_; uint8_t v_isShared_1676_; uint8_t v_isSharedCheck_1680_; 
lean_dec(v_a_1537_);
lean_dec(v_snd_1527_);
lean_dec(v_fst_1526_);
v_a_1673_ = lean_ctor_get(v___x_1662_, 0);
v_isSharedCheck_1680_ = !lean_is_exclusive(v___x_1662_);
if (v_isSharedCheck_1680_ == 0)
{
v___x_1675_ = v___x_1662_;
v_isShared_1676_ = v_isSharedCheck_1680_;
goto v_resetjp_1674_;
}
else
{
lean_inc(v_a_1673_);
lean_dec(v___x_1662_);
v___x_1675_ = lean_box(0);
v_isShared_1676_ = v_isSharedCheck_1680_;
goto v_resetjp_1674_;
}
v_resetjp_1674_:
{
lean_object* v___x_1678_; 
if (v_isShared_1676_ == 0)
{
v___x_1678_ = v___x_1675_;
goto v_reusejp_1677_;
}
else
{
lean_object* v_reuseFailAlloc_1679_; 
v_reuseFailAlloc_1679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1679_, 0, v_a_1673_);
v___x_1678_ = v_reuseFailAlloc_1679_;
goto v_reusejp_1677_;
}
v_reusejp_1677_:
{
return v___x_1678_;
}
}
}
}
}
}
else
{
lean_object* v_a_1683_; lean_object* v___x_1685_; uint8_t v_isShared_1686_; uint8_t v_isSharedCheck_1690_; 
lean_del_object(v___x_1529_);
lean_dec(v_snd_1527_);
lean_dec(v_fst_1526_);
lean_dec(v_head_1511_);
v_a_1683_ = lean_ctor_get(v___x_1536_, 0);
v_isSharedCheck_1690_ = !lean_is_exclusive(v___x_1536_);
if (v_isSharedCheck_1690_ == 0)
{
v___x_1685_ = v___x_1536_;
v_isShared_1686_ = v_isSharedCheck_1690_;
goto v_resetjp_1684_;
}
else
{
lean_inc(v_a_1683_);
lean_dec(v___x_1536_);
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
else
{
lean_object* v_a_1691_; lean_object* v___x_1693_; uint8_t v_isShared_1694_; uint8_t v_isSharedCheck_1698_; 
lean_del_object(v___x_1529_);
lean_dec(v_snd_1527_);
lean_dec(v_fst_1526_);
lean_dec(v_head_1511_);
v_a_1691_ = lean_ctor_get(v___x_1531_, 0);
v_isSharedCheck_1698_ = !lean_is_exclusive(v___x_1531_);
if (v_isSharedCheck_1698_ == 0)
{
v___x_1693_ = v___x_1531_;
v_isShared_1694_ = v_isSharedCheck_1698_;
goto v_resetjp_1692_;
}
else
{
lean_inc(v_a_1691_);
lean_dec(v___x_1531_);
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
else
{
lean_object* v_a_1700_; lean_object* v___x_1702_; uint8_t v_isShared_1703_; uint8_t v_isSharedCheck_1707_; 
lean_dec_ref(v___x_1522_);
lean_dec(v_head_1511_);
v_a_1700_ = lean_ctor_get(v___x_1524_, 0);
v_isSharedCheck_1707_ = !lean_is_exclusive(v___x_1524_);
if (v_isSharedCheck_1707_ == 0)
{
v___x_1702_ = v___x_1524_;
v_isShared_1703_ = v_isSharedCheck_1707_;
goto v_resetjp_1701_;
}
else
{
lean_inc(v_a_1700_);
lean_dec(v___x_1524_);
v___x_1702_ = lean_box(0);
v_isShared_1703_ = v_isSharedCheck_1707_;
goto v_resetjp_1701_;
}
v_resetjp_1701_:
{
lean_object* v___x_1705_; 
if (v_isShared_1703_ == 0)
{
v___x_1705_ = v___x_1702_;
goto v_reusejp_1704_;
}
else
{
lean_object* v_reuseFailAlloc_1706_; 
v_reuseFailAlloc_1706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1706_, 0, v_a_1700_);
v___x_1705_ = v_reuseFailAlloc_1706_;
goto v_reusejp_1704_;
}
v_reusejp_1704_:
{
return v___x_1705_;
}
}
}
}
else
{
lean_object* v_a_1708_; lean_object* v___x_1710_; uint8_t v_isShared_1711_; uint8_t v_isSharedCheck_1715_; 
lean_dec(v_numConst_1512_);
lean_dec(v_head_1511_);
lean_dec_ref(v_x_1474_);
lean_dec_ref(v_x_1473_);
v_a_1708_ = lean_ctor_get(v___x_1518_, 0);
v_isSharedCheck_1715_ = !lean_is_exclusive(v___x_1518_);
if (v_isSharedCheck_1715_ == 0)
{
v___x_1710_ = v___x_1518_;
v_isShared_1711_ = v_isSharedCheck_1715_;
goto v_resetjp_1709_;
}
else
{
lean_inc(v_a_1708_);
lean_dec(v___x_1518_);
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
v___jp_1483_:
{
uint8_t v___x_1489_; lean_object* v___x_1490_; 
v___x_1489_ = 1;
v___x_1490_ = l_Lean_Meta_abstractMVars(v_prf_1484_, v___x_1489_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_);
if (lean_obj_tag(v___x_1490_) == 0)
{
lean_object* v_a_1491_; lean_object* v_paramNames_1492_; lean_object* v_expr_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; 
v_a_1491_ = lean_ctor_get(v___x_1490_, 0);
lean_inc(v_a_1491_);
lean_dec_ref_known(v___x_1490_, 1);
v_paramNames_1492_ = lean_ctor_get(v_a_1491_, 0);
lean_inc_ref(v_paramNames_1492_);
v_expr_1493_ = lean_ctor_get(v_a_1491_, 2);
lean_inc_ref(v_expr_1493_);
lean_dec(v_a_1491_);
v___x_1494_ = lean_array_to_list(v_paramNames_1492_);
v___x_1495_ = lean_box(0);
v___x_1496_ = l_Lean_Meta_Sym_mkBackwardRuleFromExpr(v_expr_1493_, v___x_1494_, v___x_1495_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_);
return v___x_1496_;
}
else
{
lean_object* v_a_1497_; lean_object* v___x_1499_; uint8_t v_isShared_1500_; uint8_t v_isSharedCheck_1504_; 
v_a_1497_ = lean_ctor_get(v___x_1490_, 0);
v_isSharedCheck_1504_ = !lean_is_exclusive(v___x_1490_);
if (v_isSharedCheck_1504_ == 0)
{
v___x_1499_ = v___x_1490_;
v_isShared_1500_ = v_isSharedCheck_1504_;
goto v_resetjp_1498_;
}
else
{
lean_inc(v_a_1497_);
lean_dec(v___x_1490_);
v___x_1499_ = lean_box(0);
v_isShared_1500_ = v_isSharedCheck_1504_;
goto v_resetjp_1498_;
}
v_resetjp_1498_:
{
lean_object* v___x_1502_; 
if (v_isShared_1500_ == 0)
{
v___x_1502_ = v___x_1499_;
goto v_reusejp_1501_;
}
else
{
lean_object* v_reuseFailAlloc_1503_; 
v_reuseFailAlloc_1503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1503_, 0, v_a_1497_);
v___x_1502_ = v_reuseFailAlloc_1503_;
goto v_reusejp_1501_;
}
v_reusejp_1501_:
{
return v___x_1502_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__2___boxed(lean_object* v_op_1716_, lean_object* v___y_1717_, lean_object* v_a_1718_, lean_object* v_x_1719_, lean_object* v_x_1720_, lean_object* v_x_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_){
_start:
{
lean_object* v_res_1729_; 
v_res_1729_ = l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__2(v_op_1716_, v___y_1717_, v_a_1718_, v_x_1719_, v_x_1720_, v_x_1721_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_, v___y_1726_, v___y_1727_);
lean_dec(v___y_1727_);
lean_dec_ref(v___y_1726_);
lean_dec(v___y_1725_);
lean_dec_ref(v___y_1724_);
lean_dec(v___y_1723_);
lean_dec_ref(v___y_1722_);
lean_dec_ref(v_a_1718_);
lean_dec_ref(v___y_1717_);
return v_res_1729_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__4(lean_object* v_as_1730_, size_t v_i_1731_, size_t v_stop_1732_, lean_object* v_b_1733_){
_start:
{
uint8_t v___x_1734_; 
v___x_1734_ = lean_usize_dec_eq(v_i_1731_, v_stop_1732_);
if (v___x_1734_ == 0)
{
lean_object* v___x_1735_; lean_object* v_rewrites_1736_; lean_object* v___x_1737_; size_t v___x_1738_; size_t v___x_1739_; 
v___x_1735_ = lean_array_uget_borrowed(v_as_1730_, v_i_1731_);
v_rewrites_1736_ = lean_ctor_get(v___x_1735_, 2);
v___x_1737_ = l_Array_append___redArg(v_b_1733_, v_rewrites_1736_);
v___x_1738_ = ((size_t)1ULL);
v___x_1739_ = lean_usize_add(v_i_1731_, v___x_1738_);
v_i_1731_ = v___x_1739_;
v_b_1733_ = v___x_1737_;
goto _start;
}
else
{
return v_b_1733_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__4___boxed(lean_object* v_as_1741_, lean_object* v_i_1742_, lean_object* v_stop_1743_, lean_object* v_b_1744_){
_start:
{
size_t v_i_boxed_1745_; size_t v_stop_boxed_1746_; lean_object* v_res_1747_; 
v_i_boxed_1745_ = lean_unbox_usize(v_i_1742_);
lean_dec(v_i_1742_);
v_stop_boxed_1746_ = lean_unbox_usize(v_stop_1743_);
lean_dec(v_stop_1743_);
v_res_1747_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__4(v_as_1741_, v_i_boxed_1745_, v_stop_boxed_1746_, v_b_1744_);
lean_dec_ref(v_as_1741_);
return v_res_1747_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__3(lean_object* v_as_1748_, size_t v_i_1749_, size_t v_stop_1750_, lean_object* v_b_1751_){
_start:
{
lean_object* v___y_1753_; uint8_t v___x_1757_; 
v___x_1757_ = lean_usize_dec_eq(v_i_1749_, v_stop_1750_);
if (v___x_1757_ == 0)
{
lean_object* v___x_1758_; lean_object* v_terminal_x3f_1759_; 
v___x_1758_ = lean_array_uget_borrowed(v_as_1748_, v_i_1749_);
v_terminal_x3f_1759_ = lean_ctor_get(v___x_1758_, 3);
if (lean_obj_tag(v_terminal_x3f_1759_) == 0)
{
lean_object* v___x_1760_; lean_object* v___x_1761_; 
v___x_1760_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_LatticeOp_and___closed__2));
v___x_1761_ = l_Array_append___redArg(v_b_1751_, v___x_1760_);
v___y_1753_ = v___x_1761_;
goto v___jp_1752_;
}
else
{
lean_object* v_val_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; 
v_val_1762_ = lean_ctor_get(v_terminal_x3f_1759_, 0);
v___x_1763_ = lean_unsigned_to_nat(1u);
v___x_1764_ = lean_mk_empty_array_with_capacity(v___x_1763_);
lean_inc(v_val_1762_);
v___x_1765_ = lean_array_push(v___x_1764_, v_val_1762_);
v___x_1766_ = l_Array_append___redArg(v_b_1751_, v___x_1765_);
lean_dec_ref(v___x_1765_);
v___y_1753_ = v___x_1766_;
goto v___jp_1752_;
}
}
else
{
return v_b_1751_;
}
v___jp_1752_:
{
size_t v___x_1754_; size_t v___x_1755_; 
v___x_1754_ = ((size_t)1ULL);
v___x_1755_ = lean_usize_add(v_i_1749_, v___x_1754_);
v_i_1749_ = v___x_1755_;
v_b_1751_ = v___y_1753_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__3___boxed(lean_object* v_as_1767_, lean_object* v_i_1768_, lean_object* v_stop_1769_, lean_object* v_b_1770_){
_start:
{
size_t v_i_boxed_1771_; size_t v_stop_boxed_1772_; lean_object* v_res_1773_; 
v_i_boxed_1771_ = lean_unbox_usize(v_i_1768_);
lean_dec(v_i_1768_);
v_stop_boxed_1772_ = lean_unbox_usize(v_stop_1769_);
lean_dec(v_stop_1769_);
v_res_1773_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__3(v_as_1767_, v_i_boxed_1771_, v_stop_boxed_1772_, v_b_1770_);
lean_dec_ref(v_as_1767_);
return v_res_1773_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_mkLatticeOpRule___closed__0(void){
_start:
{
lean_object* v___x_1774_; size_t v___x_1775_; size_t v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; 
v___x_1774_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_LatticeOp_and___closed__2));
v___x_1775_ = lean_usize_once(&l_Lean_Elab_Tactic_VCGen_latticeOps___closed__5, &l_Lean_Elab_Tactic_VCGen_latticeOps___closed__5_once, _init_l_Lean_Elab_Tactic_VCGen_latticeOps___closed__5);
v___x_1776_ = ((size_t)0ULL);
v___x_1777_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_builtinLatticeOps));
v___x_1778_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__3(v___x_1777_, v___x_1776_, v___x_1775_, v___x_1774_);
return v___x_1778_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_mkLatticeOpRule(lean_object* v_rhs_1779_, lean_object* v_op_1780_, lean_object* v_a_1781_, lean_object* v_a_1782_, lean_object* v_a_1783_, lean_object* v_a_1784_, lean_object* v_a_1785_, lean_object* v_a_1786_){
_start:
{
lean_object* v___y_1789_; lean_object* v___y_1790_; lean_object* v___y_1791_; lean_object* v_rewrites_1809_; lean_object* v_terminal_x3f_1810_; lean_object* v___x_1811_; lean_object* v___y_1813_; lean_object* v___y_1814_; lean_object* v___y_1821_; uint8_t v___x_1827_; 
v_rewrites_1809_ = lean_ctor_get(v_op_1780_, 2);
v_terminal_x3f_1810_ = lean_ctor_get(v_op_1780_, 3);
v___x_1811_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_builtinLatticeOps));
v___x_1827_ = lean_uint8_once(&l_Lean_Elab_Tactic_VCGen_latticeOps___closed__3, &l_Lean_Elab_Tactic_VCGen_latticeOps___closed__3_once, _init_l_Lean_Elab_Tactic_VCGen_latticeOps___closed__3);
if (v___x_1827_ == 0)
{
lean_inc_ref(v_rewrites_1809_);
v___y_1821_ = v_rewrites_1809_;
goto v___jp_1820_;
}
else
{
uint8_t v___x_1828_; 
v___x_1828_ = lean_uint8_once(&l_Lean_Elab_Tactic_VCGen_latticeOps___closed__4, &l_Lean_Elab_Tactic_VCGen_latticeOps___closed__4_once, _init_l_Lean_Elab_Tactic_VCGen_latticeOps___closed__4);
if (v___x_1828_ == 0)
{
if (v___x_1827_ == 0)
{
lean_inc_ref(v_rewrites_1809_);
v___y_1821_ = v_rewrites_1809_;
goto v___jp_1820_;
}
else
{
size_t v___x_1829_; size_t v___x_1830_; lean_object* v___x_1831_; 
v___x_1829_ = ((size_t)0ULL);
v___x_1830_ = lean_usize_once(&l_Lean_Elab_Tactic_VCGen_latticeOps___closed__5, &l_Lean_Elab_Tactic_VCGen_latticeOps___closed__5_once, _init_l_Lean_Elab_Tactic_VCGen_latticeOps___closed__5);
lean_inc_ref(v_rewrites_1809_);
v___x_1831_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__4(v___x_1811_, v___x_1829_, v___x_1830_, v_rewrites_1809_);
v___y_1821_ = v___x_1831_;
goto v___jp_1820_;
}
}
else
{
size_t v___x_1832_; size_t v___x_1833_; lean_object* v___x_1834_; 
v___x_1832_ = ((size_t)0ULL);
v___x_1833_ = lean_usize_once(&l_Lean_Elab_Tactic_VCGen_latticeOps___closed__5, &l_Lean_Elab_Tactic_VCGen_latticeOps___closed__5_once, _init_l_Lean_Elab_Tactic_VCGen_latticeOps___closed__5);
lean_inc_ref(v_rewrites_1809_);
v___x_1834_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__4(v___x_1811_, v___x_1832_, v___x_1833_, v_rewrites_1809_);
v___y_1821_ = v___x_1834_;
goto v___jp_1820_;
}
}
v___jp_1788_:
{
lean_object* v___x_1792_; lean_object* v___x_1793_; 
lean_inc_ref(v___y_1790_);
v___x_1792_ = l_Array_append___redArg(v___y_1790_, v___y_1791_);
lean_dec_ref(v___y_1791_);
v___x_1793_ = l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_mkLatticeTerminals(v___x_1792_, v_a_1783_, v_a_1784_, v_a_1785_, v_a_1786_);
lean_dec_ref(v___x_1792_);
if (lean_obj_tag(v___x_1793_) == 0)
{
lean_object* v_a_1794_; lean_object* v_dummy_1795_; lean_object* v_nargs_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; 
v_a_1794_ = lean_ctor_get(v___x_1793_, 0);
lean_inc(v_a_1794_);
lean_dec_ref_known(v___x_1793_, 1);
v_dummy_1795_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_projectsRewritableOperand___closed__0, &l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_projectsRewritableOperand___closed__0_once, _init_l___private_Lean_Elab_Tactic_VCGen_LatticeOp_0__Lean_Elab_Tactic_VCGen_projectsRewritableOperand___closed__0);
v_nargs_1796_ = l_Lean_Expr_getAppNumArgs(v_rhs_1779_);
lean_inc(v_nargs_1796_);
v___x_1797_ = lean_mk_array(v_nargs_1796_, v_dummy_1795_);
v___x_1798_ = lean_unsigned_to_nat(1u);
v___x_1799_ = lean_nat_sub(v_nargs_1796_, v___x_1798_);
lean_dec(v_nargs_1796_);
v___x_1800_ = l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__2(v_op_1780_, v___y_1789_, v_a_1794_, v_rhs_1779_, v___x_1797_, v___x_1799_, v_a_1781_, v_a_1782_, v_a_1783_, v_a_1784_, v_a_1785_, v_a_1786_);
lean_dec(v_a_1794_);
lean_dec_ref(v___y_1789_);
return v___x_1800_;
}
else
{
lean_object* v_a_1801_; lean_object* v___x_1803_; uint8_t v_isShared_1804_; uint8_t v_isSharedCheck_1808_; 
lean_dec_ref(v___y_1789_);
lean_dec_ref(v_op_1780_);
lean_dec_ref(v_rhs_1779_);
v_a_1801_ = lean_ctor_get(v___x_1793_, 0);
v_isSharedCheck_1808_ = !lean_is_exclusive(v___x_1793_);
if (v_isSharedCheck_1808_ == 0)
{
v___x_1803_ = v___x_1793_;
v_isShared_1804_ = v_isSharedCheck_1808_;
goto v_resetjp_1802_;
}
else
{
lean_inc(v_a_1801_);
lean_dec(v___x_1793_);
v___x_1803_ = lean_box(0);
v_isShared_1804_ = v_isSharedCheck_1808_;
goto v_resetjp_1802_;
}
v_resetjp_1802_:
{
lean_object* v___x_1806_; 
if (v_isShared_1804_ == 0)
{
v___x_1806_ = v___x_1803_;
goto v_reusejp_1805_;
}
else
{
lean_object* v_reuseFailAlloc_1807_; 
v_reuseFailAlloc_1807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1807_, 0, v_a_1801_);
v___x_1806_ = v_reuseFailAlloc_1807_;
goto v_reusejp_1805_;
}
v_reusejp_1805_:
{
return v___x_1806_;
}
}
}
}
v___jp_1812_:
{
if (lean_obj_tag(v_terminal_x3f_1810_) == 0)
{
lean_object* v___x_1815_; 
v___x_1815_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_LatticeOp_and___closed__2));
v___y_1789_ = v___y_1813_;
v___y_1790_ = v___y_1814_;
v___y_1791_ = v___x_1815_;
goto v___jp_1788_;
}
else
{
lean_object* v_val_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; 
v_val_1816_ = lean_ctor_get(v_terminal_x3f_1810_, 0);
v___x_1817_ = lean_unsigned_to_nat(1u);
v___x_1818_ = lean_mk_empty_array_with_capacity(v___x_1817_);
lean_inc(v_val_1816_);
v___x_1819_ = lean_array_push(v___x_1818_, v_val_1816_);
v___y_1789_ = v___y_1813_;
v___y_1790_ = v___y_1814_;
v___y_1791_ = v___x_1819_;
goto v___jp_1788_;
}
}
v___jp_1820_:
{
lean_object* v___x_1822_; uint8_t v___x_1823_; 
v___x_1822_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_LatticeOp_and___closed__2));
v___x_1823_ = lean_uint8_once(&l_Lean_Elab_Tactic_VCGen_latticeOps___closed__3, &l_Lean_Elab_Tactic_VCGen_latticeOps___closed__3_once, _init_l_Lean_Elab_Tactic_VCGen_latticeOps___closed__3);
if (v___x_1823_ == 0)
{
v___y_1813_ = v___y_1821_;
v___y_1814_ = v___x_1822_;
goto v___jp_1812_;
}
else
{
uint8_t v___x_1824_; 
v___x_1824_ = lean_uint8_once(&l_Lean_Elab_Tactic_VCGen_latticeOps___closed__4, &l_Lean_Elab_Tactic_VCGen_latticeOps___closed__4_once, _init_l_Lean_Elab_Tactic_VCGen_latticeOps___closed__4);
if (v___x_1824_ == 0)
{
if (v___x_1823_ == 0)
{
v___y_1813_ = v___y_1821_;
v___y_1814_ = v___x_1822_;
goto v___jp_1812_;
}
else
{
lean_object* v___x_1825_; 
v___x_1825_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_mkLatticeOpRule___closed__0, &l_Lean_Elab_Tactic_VCGen_mkLatticeOpRule___closed__0_once, _init_l_Lean_Elab_Tactic_VCGen_mkLatticeOpRule___closed__0);
v___y_1813_ = v___y_1821_;
v___y_1814_ = v___x_1825_;
goto v___jp_1812_;
}
}
else
{
lean_object* v___x_1826_; 
v___x_1826_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_mkLatticeOpRule___closed__0, &l_Lean_Elab_Tactic_VCGen_mkLatticeOpRule___closed__0_once, _init_l_Lean_Elab_Tactic_VCGen_mkLatticeOpRule___closed__0);
v___y_1813_ = v___y_1821_;
v___y_1814_ = v___x_1826_;
goto v___jp_1812_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_mkLatticeOpRule___boxed(lean_object* v_rhs_1835_, lean_object* v_op_1836_, lean_object* v_a_1837_, lean_object* v_a_1838_, lean_object* v_a_1839_, lean_object* v_a_1840_, lean_object* v_a_1841_, lean_object* v_a_1842_, lean_object* v_a_1843_){
_start:
{
lean_object* v_res_1844_; 
v_res_1844_ = l_Lean_Elab_Tactic_VCGen_mkLatticeOpRule(v_rhs_1835_, v_op_1836_, v_a_1837_, v_a_1838_, v_a_1839_, v_a_1840_, v_a_1841_, v_a_1842_);
lean_dec(v_a_1842_);
lean_dec_ref(v_a_1841_);
lean_dec(v_a_1840_);
lean_dec_ref(v_a_1839_);
lean_dec(v_a_1838_);
lean_dec_ref(v_a_1837_);
return v_res_1844_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__0(size_t v_sz_1845_, size_t v_i_1846_, lean_object* v_bs_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_){
_start:
{
lean_object* v___x_1855_; 
v___x_1855_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__0___redArg(v_sz_1845_, v_i_1846_, v_bs_1847_, v___y_1850_, v___y_1851_, v___y_1852_, v___y_1853_);
return v___x_1855_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__0___boxed(lean_object* v_sz_1856_, lean_object* v_i_1857_, lean_object* v_bs_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_){
_start:
{
size_t v_sz_boxed_1866_; size_t v_i_boxed_1867_; lean_object* v_res_1868_; 
v_sz_boxed_1866_ = lean_unbox_usize(v_sz_1856_);
lean_dec(v_sz_1856_);
v_i_boxed_1867_ = lean_unbox_usize(v_i_1857_);
lean_dec(v_i_1857_);
v_res_1868_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__0(v_sz_boxed_1866_, v_i_boxed_1867_, v_bs_1858_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_);
lean_dec(v___y_1864_);
lean_dec_ref(v___y_1863_);
lean_dec(v___y_1862_);
lean_dec_ref(v___y_1861_);
lean_dec(v___y_1860_);
lean_dec_ref(v___y_1859_);
return v_res_1868_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__1(lean_object* v_00_u03b2_1869_, lean_object* v_m_1870_, lean_object* v_a_1871_){
_start:
{
lean_object* v___x_1872_; 
v___x_1872_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__1___redArg(v_m_1870_, v_a_1871_);
return v___x_1872_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__1___boxed(lean_object* v_00_u03b2_1873_, lean_object* v_m_1874_, lean_object* v_a_1875_){
_start:
{
lean_object* v_res_1876_; 
v_res_1876_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__1(v_00_u03b2_1873_, v_m_1874_, v_a_1875_);
lean_dec(v_a_1875_);
lean_dec_ref(v_m_1874_);
return v_res_1876_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__1_spec__1(lean_object* v_00_u03b2_1877_, lean_object* v_a_1878_, lean_object* v_x_1879_){
_start:
{
lean_object* v___x_1880_; 
v___x_1880_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__1_spec__1___redArg(v_a_1878_, v_x_1879_);
return v___x_1880_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__1_spec__1___boxed(lean_object* v_00_u03b2_1881_, lean_object* v_a_1882_, lean_object* v_x_1883_){
_start:
{
lean_object* v_res_1884_; 
v_res_1884_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRule_spec__1_spec__1(v_00_u03b2_1881_, v_a_1882_, v_x_1883_);
lean_dec(v_x_1883_);
lean_dec(v_a_1882_);
return v_res_1884_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_Apply(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_Order_Heyting(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_Order_FrameClosure(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_Rewrite(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_AppBuilder(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_AbstractMVars(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_VCGen_ExcessArgsFrame(uint8_t builtin);
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
res = runtime_initialize_Lean_Elab_Tactic_VCGen_ExcessArgsFrame(builtin);
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
lean_object* initialize_Lean_Elab_Tactic_VCGen_ExcessArgsFrame(uint8_t builtin);
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
res = initialize_Lean_Elab_Tactic_VCGen_ExcessArgsFrame(builtin);
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
