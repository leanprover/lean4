// Lean compiler output
// Module: Lean.Elab.Tactic.Do.Internal.VCGen.FrameProc
// Imports: public import Lean.Elab.Tactic.Do.Internal.VCGen.WPApp public import Lean.Meta.Sym.Apply public import Lean.Meta.Sym.AlphaShareBuilder import Std.Internal.Do.Order.Basic import Lean.Meta.AppBuilder import Lean.Meta.AbstractMVars import Lean.Meta.Sym.InferType import Lean.Meta.Sym.InstantiateMVarsS import Lean.Meta.Tactic.Util
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
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Sym_share1___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Sym_assertShared(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_stripArgsN(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_WPApp_Pred(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAppOptM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_BackwardRule_apply(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* l_Lean_Meta_abstractMVars(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_mkMVar(lean_object*);
lean_object* l_Lean_Meta_openAbstractMVarsResult(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_instantiateMVarsS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_FrameSplit_instantiateMVarsS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_FrameSplit_instantiateMVarsS___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_FrameInferenceInfo_le___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_FrameInferenceInfo_le___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_FrameInferenceInfo_le(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_FrameInferenceInfo_le___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_FrameInferenceInfo_pre___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_FrameInferenceInfo_pre___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_FrameInferenceInfo_pre(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_FrameInferenceInfo_pre___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_FrameInferenceInfo_mkResidualPre___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_FrameInferenceInfo_mkResidualPre___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_FrameInferenceInfo_mkResidualPre(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_FrameInferenceInfo_mkResidualPre___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameInferenceInfo_specPre_x3f_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameInferenceInfo_specPre_x3f_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameInferenceInfo_specPre_x3f_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameInferenceInfo_specPre_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameInferenceInfo_specPre_x3f_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameInferenceInfo_specPre_x3f_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameInferenceInfo_specPre_x3f_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameInferenceInfo_specPre_x3f_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameInferenceInfo_specPre_x3f_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameInferenceInfo_specPre_x3f_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_findSomeM_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameInferenceInfo_specPre_x3f_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_List_findSomeM_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameInferenceInfo_specPre_x3f_spec__0___redArg___closed__0 = (const lean_object*)&l_List_findSomeM_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameInferenceInfo_specPre_x3f_spec__0___redArg___closed__0_value;
static const lean_string_object l_List_findSomeM_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameInferenceInfo_specPre_x3f_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Order"};
static const lean_object* l_List_findSomeM_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameInferenceInfo_specPre_x3f_spec__0___redArg___closed__1 = (const lean_object*)&l_List_findSomeM_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameInferenceInfo_specPre_x3f_spec__0___redArg___closed__1_value;
static const lean_string_object l_List_findSomeM_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameInferenceInfo_specPre_x3f_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "PartialOrder"};
static const lean_object* l_List_findSomeM_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameInferenceInfo_specPre_x3f_spec__0___redArg___closed__2 = (const lean_object*)&l_List_findSomeM_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameInferenceInfo_specPre_x3f_spec__0___redArg___closed__2_value;
static const lean_string_object l_List_findSomeM_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameInferenceInfo_specPre_x3f_spec__0___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "rel"};
static const lean_object* l_List_findSomeM_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameInferenceInfo_specPre_x3f_spec__0___redArg___closed__3 = (const lean_object*)&l_List_findSomeM_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameInferenceInfo_specPre_x3f_spec__0___redArg___closed__3_value;
static const lean_ctor_object l_List_findSomeM_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameInferenceInfo_specPre_x3f_spec__0___redArg___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_findSomeM_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameInferenceInfo_specPre_x3f_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_List_findSomeM_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameInferenceInfo_specPre_x3f_spec__0___redArg___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_findSomeM_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameInferenceInfo_specPre_x3f_spec__0___redArg___closed__4_value_aux_0),((lean_object*)&l_List_findSomeM_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameInferenceInfo_specPre_x3f_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_List_findSomeM_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameInferenceInfo_specPre_x3f_spec__0___redArg___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_findSomeM_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameInferenceInfo_specPre_x3f_spec__0___redArg___closed__4_value_aux_1),((lean_object*)&l_List_findSomeM_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameInferenceInfo_specPre_x3f_spec__0___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(179, 3, 218, 237, 219, 72, 94, 177)}};
static const lean_ctor_object l_List_findSomeM_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameInferenceInfo_specPre_x3f_spec__0___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_findSomeM_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameInferenceInfo_specPre_x3f_spec__0___redArg___closed__4_value_aux_2),((lean_object*)&l_List_findSomeM_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameInferenceInfo_specPre_x3f_spec__0___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(41, 174, 7, 105, 99, 77, 97, 125)}};
static const lean_object* l_List_findSomeM_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameInferenceInfo_specPre_x3f_spec__0___redArg___closed__4 = (const lean_object*)&l_List_findSomeM_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameInferenceInfo_specPre_x3f_spec__0___redArg___closed__4_value;
LEAN_EXPORT lean_object* l_List_findSomeM_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameInferenceInfo_specPre_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_findSomeM_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameInferenceInfo_specPre_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_FrameInferenceInfo_specPre_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_FrameInferenceInfo_specPre_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_FrameInferenceInfo_specPre_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_FrameInferenceInfo_specPre_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_findSomeM_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameInferenceInfo_specPre_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_findSomeM_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameInferenceInfo_specPre_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameInferenceInfo_mkSplitVCS_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameInferenceInfo_mkSplitVCS_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameInferenceInfo_mkSplitVCS_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameInferenceInfo_mkSplitVCS_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameInferenceInfo_mkSplitVCS_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameInferenceInfo_mkSplitVCS_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_FrameInferenceInfo_mkSplitVCS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_FrameInferenceInfo_mkSplitVCS___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_FrameSplit_withDeferredSplitVC(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_FrameSplit_withDeferredSplitVC___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_FrameSplit_withDischargedSplitVC(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_instInhabitedFrameProcs___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_instInhabitedFrameProcs___closed__0;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_instInhabitedFrameProcs___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_instInhabitedFrameProcs___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_instInhabitedFrameProcs;
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcs_insert_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcs_insert_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcs_insert_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcs_insert_spec__0_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcs_insert_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcs_insert_spec__0_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcs_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcs_insert(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcs_insert_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcs_insert_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcs_insert_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcs_insert_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcs_insert_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcs_insert_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcs_insert_spec__0_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_defaultFrameInferenceProc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_defaultFrameInferenceProc___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProc_0__Lean_Elab_Tactic_Do_Internal_meetOp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meet"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProc_0__Lean_Elab_Tactic_Do_Internal_meetOp___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProc_0__Lean_Elab_Tactic_Do_Internal_meetOp___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProc_0__Lean_Elab_Tactic_Do_Internal_meetOp___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_findSomeM_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameInferenceInfo_specPre_x3f_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProc_0__Lean_Elab_Tactic_Do_Internal_meetOp___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProc_0__Lean_Elab_Tactic_Do_Internal_meetOp___closed__1_value_aux_0),((lean_object*)&l_List_findSomeM_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameInferenceInfo_specPre_x3f_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProc_0__Lean_Elab_Tactic_Do_Internal_meetOp___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProc_0__Lean_Elab_Tactic_Do_Internal_meetOp___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProc_0__Lean_Elab_Tactic_Do_Internal_meetOp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(194, 193, 63, 6, 53, 61, 199, 176)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProc_0__Lean_Elab_Tactic_Do_Internal_meetOp___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProc_0__Lean_Elab_Tactic_Do_Internal_meetOp___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProc_0__Lean_Elab_Tactic_Do_Internal_meetOp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProc_0__Lean_Elab_Tactic_Do_Internal_meetOp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_meetFrameProc___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_meetFrameProc___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_Do_Internal_VCGen_meetFrameProc___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Do_Internal_VCGen_meetFrameProc___lam__0___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_meetFrameProc___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_meetFrameProc___closed__0_value;
static const lean_closure_object l_Lean_Elab_Tactic_Do_Internal_VCGen_meetFrameProc___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProc_0__Lean_Elab_Tactic_Do_Internal_meetOp___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_meetFrameProc___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_meetFrameProc___closed__1_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_VCGen_meetFrameProc___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_meetFrameProc___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_meetFrameProc;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_FrameSplit_instantiateMVarsS(lean_object* v_split_1_, lean_object* v_a_2_, lean_object* v_a_3_, lean_object* v_a_4_, lean_object* v_a_5_, lean_object* v_a_6_, lean_object* v_a_7_){
_start:
{
lean_object* v_frame_9_; lean_object* v_residualPre_10_; lean_object* v_splitVCProof_11_; lean_object* v_subgoals_12_; lean_object* v___x_14_; uint8_t v_isShared_15_; uint8_t v_isSharedCheck_46_; 
v_frame_9_ = lean_ctor_get(v_split_1_, 0);
v_residualPre_10_ = lean_ctor_get(v_split_1_, 1);
v_splitVCProof_11_ = lean_ctor_get(v_split_1_, 2);
v_subgoals_12_ = lean_ctor_get(v_split_1_, 3);
v_isSharedCheck_46_ = !lean_is_exclusive(v_split_1_);
if (v_isSharedCheck_46_ == 0)
{
v___x_14_ = v_split_1_;
v_isShared_15_ = v_isSharedCheck_46_;
goto v_resetjp_13_;
}
else
{
lean_inc(v_subgoals_12_);
lean_inc(v_splitVCProof_11_);
lean_inc(v_residualPre_10_);
lean_inc(v_frame_9_);
lean_dec(v_split_1_);
v___x_14_ = lean_box(0);
v_isShared_15_ = v_isSharedCheck_46_;
goto v_resetjp_13_;
}
v_resetjp_13_:
{
lean_object* v___x_16_; 
v___x_16_ = l_Lean_Meta_Sym_instantiateMVarsS(v_frame_9_, v_a_2_, v_a_3_, v_a_4_, v_a_5_, v_a_6_, v_a_7_);
if (lean_obj_tag(v___x_16_) == 0)
{
lean_object* v_a_17_; lean_object* v___x_18_; 
v_a_17_ = lean_ctor_get(v___x_16_, 0);
lean_inc(v_a_17_);
lean_dec_ref_known(v___x_16_, 1);
v___x_18_ = l_Lean_Meta_Sym_instantiateMVarsS(v_splitVCProof_11_, v_a_2_, v_a_3_, v_a_4_, v_a_5_, v_a_6_, v_a_7_);
if (lean_obj_tag(v___x_18_) == 0)
{
lean_object* v_a_19_; lean_object* v___x_21_; uint8_t v_isShared_22_; uint8_t v_isSharedCheck_29_; 
v_a_19_ = lean_ctor_get(v___x_18_, 0);
v_isSharedCheck_29_ = !lean_is_exclusive(v___x_18_);
if (v_isSharedCheck_29_ == 0)
{
v___x_21_ = v___x_18_;
v_isShared_22_ = v_isSharedCheck_29_;
goto v_resetjp_20_;
}
else
{
lean_inc(v_a_19_);
lean_dec(v___x_18_);
v___x_21_ = lean_box(0);
v_isShared_22_ = v_isSharedCheck_29_;
goto v_resetjp_20_;
}
v_resetjp_20_:
{
lean_object* v___x_24_; 
if (v_isShared_15_ == 0)
{
lean_ctor_set(v___x_14_, 2, v_a_19_);
lean_ctor_set(v___x_14_, 0, v_a_17_);
v___x_24_ = v___x_14_;
goto v_reusejp_23_;
}
else
{
lean_object* v_reuseFailAlloc_28_; 
v_reuseFailAlloc_28_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_28_, 0, v_a_17_);
lean_ctor_set(v_reuseFailAlloc_28_, 1, v_residualPre_10_);
lean_ctor_set(v_reuseFailAlloc_28_, 2, v_a_19_);
lean_ctor_set(v_reuseFailAlloc_28_, 3, v_subgoals_12_);
v___x_24_ = v_reuseFailAlloc_28_;
goto v_reusejp_23_;
}
v_reusejp_23_:
{
lean_object* v___x_26_; 
if (v_isShared_22_ == 0)
{
lean_ctor_set(v___x_21_, 0, v___x_24_);
v___x_26_ = v___x_21_;
goto v_reusejp_25_;
}
else
{
lean_object* v_reuseFailAlloc_27_; 
v_reuseFailAlloc_27_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_27_, 0, v___x_24_);
v___x_26_ = v_reuseFailAlloc_27_;
goto v_reusejp_25_;
}
v_reusejp_25_:
{
return v___x_26_;
}
}
}
}
else
{
lean_object* v_a_30_; lean_object* v___x_32_; uint8_t v_isShared_33_; uint8_t v_isSharedCheck_37_; 
lean_dec(v_a_17_);
lean_del_object(v___x_14_);
lean_dec(v_subgoals_12_);
lean_dec(v_residualPre_10_);
v_a_30_ = lean_ctor_get(v___x_18_, 0);
v_isSharedCheck_37_ = !lean_is_exclusive(v___x_18_);
if (v_isSharedCheck_37_ == 0)
{
v___x_32_ = v___x_18_;
v_isShared_33_ = v_isSharedCheck_37_;
goto v_resetjp_31_;
}
else
{
lean_inc(v_a_30_);
lean_dec(v___x_18_);
v___x_32_ = lean_box(0);
v_isShared_33_ = v_isSharedCheck_37_;
goto v_resetjp_31_;
}
v_resetjp_31_:
{
lean_object* v___x_35_; 
if (v_isShared_33_ == 0)
{
v___x_35_ = v___x_32_;
goto v_reusejp_34_;
}
else
{
lean_object* v_reuseFailAlloc_36_; 
v_reuseFailAlloc_36_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_36_, 0, v_a_30_);
v___x_35_ = v_reuseFailAlloc_36_;
goto v_reusejp_34_;
}
v_reusejp_34_:
{
return v___x_35_;
}
}
}
}
else
{
lean_object* v_a_38_; lean_object* v___x_40_; uint8_t v_isShared_41_; uint8_t v_isSharedCheck_45_; 
lean_del_object(v___x_14_);
lean_dec(v_subgoals_12_);
lean_dec_ref(v_splitVCProof_11_);
lean_dec(v_residualPre_10_);
v_a_38_ = lean_ctor_get(v___x_16_, 0);
v_isSharedCheck_45_ = !lean_is_exclusive(v___x_16_);
if (v_isSharedCheck_45_ == 0)
{
v___x_40_ = v___x_16_;
v_isShared_41_ = v_isSharedCheck_45_;
goto v_resetjp_39_;
}
else
{
lean_inc(v_a_38_);
lean_dec(v___x_16_);
v___x_40_ = lean_box(0);
v_isShared_41_ = v_isSharedCheck_45_;
goto v_resetjp_39_;
}
v_resetjp_39_:
{
lean_object* v___x_43_; 
if (v_isShared_41_ == 0)
{
v___x_43_ = v___x_40_;
goto v_reusejp_42_;
}
else
{
lean_object* v_reuseFailAlloc_44_; 
v_reuseFailAlloc_44_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_44_, 0, v_a_38_);
v___x_43_ = v_reuseFailAlloc_44_;
goto v_reusejp_42_;
}
v_reusejp_42_:
{
return v___x_43_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_FrameSplit_instantiateMVarsS___boxed(lean_object* v_split_47_, lean_object* v_a_48_, lean_object* v_a_49_, lean_object* v_a_50_, lean_object* v_a_51_, lean_object* v_a_52_, lean_object* v_a_53_, lean_object* v_a_54_){
_start:
{
lean_object* v_res_55_; 
v_res_55_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_FrameSplit_instantiateMVarsS(v_split_47_, v_a_48_, v_a_49_, v_a_50_, v_a_51_, v_a_52_, v_a_53_);
lean_dec(v_a_53_);
lean_dec_ref(v_a_52_);
lean_dec(v_a_51_);
lean_dec_ref(v_a_50_);
lean_dec(v_a_49_);
lean_dec_ref(v_a_48_);
return v_res_55_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_FrameInferenceInfo_le___redArg(lean_object* v_i_56_, lean_object* v_a_57_, lean_object* v_a_58_, lean_object* v_a_59_, lean_object* v_a_60_){
_start:
{
lean_object* v_goal_62_; lean_object* v___x_63_; 
v_goal_62_ = lean_ctor_get(v_i_56_, 1);
lean_inc(v_goal_62_);
lean_dec_ref(v_i_56_);
v___x_63_ = l_Lean_MVarId_getType(v_goal_62_, v_a_57_, v_a_58_, v_a_59_, v_a_60_);
if (lean_obj_tag(v___x_63_) == 0)
{
lean_object* v_a_64_; lean_object* v___x_66_; uint8_t v_isShared_67_; uint8_t v_isSharedCheck_73_; 
v_a_64_ = lean_ctor_get(v___x_63_, 0);
v_isSharedCheck_73_ = !lean_is_exclusive(v___x_63_);
if (v_isSharedCheck_73_ == 0)
{
v___x_66_ = v___x_63_;
v_isShared_67_ = v_isSharedCheck_73_;
goto v_resetjp_65_;
}
else
{
lean_inc(v_a_64_);
lean_dec(v___x_63_);
v___x_66_ = lean_box(0);
v_isShared_67_ = v_isSharedCheck_73_;
goto v_resetjp_65_;
}
v_resetjp_65_:
{
lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_71_; 
v___x_68_ = lean_unsigned_to_nat(2u);
v___x_69_ = l_Lean_Expr_stripArgsN(v_a_64_, v___x_68_);
lean_dec(v_a_64_);
if (v_isShared_67_ == 0)
{
lean_ctor_set(v___x_66_, 0, v___x_69_);
v___x_71_ = v___x_66_;
goto v_reusejp_70_;
}
else
{
lean_object* v_reuseFailAlloc_72_; 
v_reuseFailAlloc_72_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_72_, 0, v___x_69_);
v___x_71_ = v_reuseFailAlloc_72_;
goto v_reusejp_70_;
}
v_reusejp_70_:
{
return v___x_71_;
}
}
}
else
{
return v___x_63_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_FrameInferenceInfo_le___redArg___boxed(lean_object* v_i_74_, lean_object* v_a_75_, lean_object* v_a_76_, lean_object* v_a_77_, lean_object* v_a_78_, lean_object* v_a_79_){
_start:
{
lean_object* v_res_80_; 
v_res_80_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_FrameInferenceInfo_le___redArg(v_i_74_, v_a_75_, v_a_76_, v_a_77_, v_a_78_);
lean_dec(v_a_78_);
lean_dec_ref(v_a_77_);
lean_dec(v_a_76_);
lean_dec_ref(v_a_75_);
return v_res_80_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_FrameInferenceInfo_le(lean_object* v_i_81_, lean_object* v_a_82_, lean_object* v_a_83_, lean_object* v_a_84_, lean_object* v_a_85_, lean_object* v_a_86_, lean_object* v_a_87_){
_start:
{
lean_object* v___x_89_; 
v___x_89_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_FrameInferenceInfo_le___redArg(v_i_81_, v_a_84_, v_a_85_, v_a_86_, v_a_87_);
return v___x_89_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_FrameInferenceInfo_le___boxed(lean_object* v_i_90_, lean_object* v_a_91_, lean_object* v_a_92_, lean_object* v_a_93_, lean_object* v_a_94_, lean_object* v_a_95_, lean_object* v_a_96_, lean_object* v_a_97_){
_start:
{
lean_object* v_res_98_; 
v_res_98_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_FrameInferenceInfo_le(v_i_90_, v_a_91_, v_a_92_, v_a_93_, v_a_94_, v_a_95_, v_a_96_);
lean_dec(v_a_96_);
lean_dec_ref(v_a_95_);
lean_dec(v_a_94_);
lean_dec_ref(v_a_93_);
lean_dec(v_a_92_);
lean_dec_ref(v_a_91_);
return v_res_98_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_FrameInferenceInfo_pre___redArg(lean_object* v_i_99_, lean_object* v_a_100_, lean_object* v_a_101_, lean_object* v_a_102_, lean_object* v_a_103_){
_start:
{
lean_object* v_goal_105_; lean_object* v___x_106_; 
v_goal_105_ = lean_ctor_get(v_i_99_, 1);
lean_inc(v_goal_105_);
lean_dec_ref(v_i_99_);
v___x_106_ = l_Lean_MVarId_getType(v_goal_105_, v_a_100_, v_a_101_, v_a_102_, v_a_103_);
if (lean_obj_tag(v___x_106_) == 0)
{
lean_object* v_a_107_; lean_object* v___x_109_; uint8_t v_isShared_110_; uint8_t v_isSharedCheck_116_; 
v_a_107_ = lean_ctor_get(v___x_106_, 0);
v_isSharedCheck_116_ = !lean_is_exclusive(v___x_106_);
if (v_isSharedCheck_116_ == 0)
{
v___x_109_ = v___x_106_;
v_isShared_110_ = v_isSharedCheck_116_;
goto v_resetjp_108_;
}
else
{
lean_inc(v_a_107_);
lean_dec(v___x_106_);
v___x_109_ = lean_box(0);
v_isShared_110_ = v_isSharedCheck_116_;
goto v_resetjp_108_;
}
v_resetjp_108_:
{
lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_114_; 
v___x_111_ = l_Lean_Expr_appFn_x21(v_a_107_);
lean_dec(v_a_107_);
v___x_112_ = l_Lean_Expr_appArg_x21(v___x_111_);
lean_dec_ref(v___x_111_);
if (v_isShared_110_ == 0)
{
lean_ctor_set(v___x_109_, 0, v___x_112_);
v___x_114_ = v___x_109_;
goto v_reusejp_113_;
}
else
{
lean_object* v_reuseFailAlloc_115_; 
v_reuseFailAlloc_115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_115_, 0, v___x_112_);
v___x_114_ = v_reuseFailAlloc_115_;
goto v_reusejp_113_;
}
v_reusejp_113_:
{
return v___x_114_;
}
}
}
else
{
return v___x_106_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_FrameInferenceInfo_pre___redArg___boxed(lean_object* v_i_117_, lean_object* v_a_118_, lean_object* v_a_119_, lean_object* v_a_120_, lean_object* v_a_121_, lean_object* v_a_122_){
_start:
{
lean_object* v_res_123_; 
v_res_123_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_FrameInferenceInfo_pre___redArg(v_i_117_, v_a_118_, v_a_119_, v_a_120_, v_a_121_);
lean_dec(v_a_121_);
lean_dec_ref(v_a_120_);
lean_dec(v_a_119_);
lean_dec_ref(v_a_118_);
return v_res_123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_FrameInferenceInfo_pre(lean_object* v_i_124_, lean_object* v_a_125_, lean_object* v_a_126_, lean_object* v_a_127_, lean_object* v_a_128_, lean_object* v_a_129_, lean_object* v_a_130_){
_start:
{
lean_object* v___x_132_; 
v___x_132_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_FrameInferenceInfo_pre___redArg(v_i_124_, v_a_127_, v_a_128_, v_a_129_, v_a_130_);
return v___x_132_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_FrameInferenceInfo_pre___boxed(lean_object* v_i_133_, lean_object* v_a_134_, lean_object* v_a_135_, lean_object* v_a_136_, lean_object* v_a_137_, lean_object* v_a_138_, lean_object* v_a_139_, lean_object* v_a_140_){
_start:
{
lean_object* v_res_141_; 
v_res_141_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_FrameInferenceInfo_pre(v_i_133_, v_a_134_, v_a_135_, v_a_136_, v_a_137_, v_a_138_, v_a_139_);
lean_dec(v_a_139_);
lean_dec_ref(v_a_138_);
lean_dec(v_a_137_);
lean_dec_ref(v_a_136_);
lean_dec(v_a_135_);
lean_dec_ref(v_a_134_);
return v_res_141_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_FrameInferenceInfo_mkResidualPre___redArg(lean_object* v_i_142_, lean_object* v_a_143_, lean_object* v_a_144_, lean_object* v_a_145_, lean_object* v_a_146_){
_start:
{
lean_object* v_toWPApp_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; 
v_toWPApp_148_ = lean_ctor_get(v_i_142_, 0);
v___x_149_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_WPApp_Pred(v_toWPApp_148_);
v___x_150_ = lean_box(0);
v___x_151_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_149_, v___x_150_, v_a_143_, v_a_144_, v_a_145_, v_a_146_);
if (lean_obj_tag(v___x_151_) == 0)
{
lean_object* v_a_152_; lean_object* v___x_154_; uint8_t v_isShared_155_; uint8_t v_isSharedCheck_160_; 
v_a_152_ = lean_ctor_get(v___x_151_, 0);
v_isSharedCheck_160_ = !lean_is_exclusive(v___x_151_);
if (v_isSharedCheck_160_ == 0)
{
v___x_154_ = v___x_151_;
v_isShared_155_ = v_isSharedCheck_160_;
goto v_resetjp_153_;
}
else
{
lean_inc(v_a_152_);
lean_dec(v___x_151_);
v___x_154_ = lean_box(0);
v_isShared_155_ = v_isSharedCheck_160_;
goto v_resetjp_153_;
}
v_resetjp_153_:
{
lean_object* v___x_156_; lean_object* v___x_158_; 
v___x_156_ = l_Lean_Expr_mvarId_x21(v_a_152_);
lean_dec(v_a_152_);
if (v_isShared_155_ == 0)
{
lean_ctor_set(v___x_154_, 0, v___x_156_);
v___x_158_ = v___x_154_;
goto v_reusejp_157_;
}
else
{
lean_object* v_reuseFailAlloc_159_; 
v_reuseFailAlloc_159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_159_, 0, v___x_156_);
v___x_158_ = v_reuseFailAlloc_159_;
goto v_reusejp_157_;
}
v_reusejp_157_:
{
return v___x_158_;
}
}
}
else
{
lean_object* v_a_161_; lean_object* v___x_163_; uint8_t v_isShared_164_; uint8_t v_isSharedCheck_168_; 
v_a_161_ = lean_ctor_get(v___x_151_, 0);
v_isSharedCheck_168_ = !lean_is_exclusive(v___x_151_);
if (v_isSharedCheck_168_ == 0)
{
v___x_163_ = v___x_151_;
v_isShared_164_ = v_isSharedCheck_168_;
goto v_resetjp_162_;
}
else
{
lean_inc(v_a_161_);
lean_dec(v___x_151_);
v___x_163_ = lean_box(0);
v_isShared_164_ = v_isSharedCheck_168_;
goto v_resetjp_162_;
}
v_resetjp_162_:
{
lean_object* v___x_166_; 
if (v_isShared_164_ == 0)
{
v___x_166_ = v___x_163_;
goto v_reusejp_165_;
}
else
{
lean_object* v_reuseFailAlloc_167_; 
v_reuseFailAlloc_167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_167_, 0, v_a_161_);
v___x_166_ = v_reuseFailAlloc_167_;
goto v_reusejp_165_;
}
v_reusejp_165_:
{
return v___x_166_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_FrameInferenceInfo_mkResidualPre___redArg___boxed(lean_object* v_i_169_, lean_object* v_a_170_, lean_object* v_a_171_, lean_object* v_a_172_, lean_object* v_a_173_, lean_object* v_a_174_){
_start:
{
lean_object* v_res_175_; 
v_res_175_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_FrameInferenceInfo_mkResidualPre___redArg(v_i_169_, v_a_170_, v_a_171_, v_a_172_, v_a_173_);
lean_dec(v_a_173_);
lean_dec_ref(v_a_172_);
lean_dec(v_a_171_);
lean_dec_ref(v_a_170_);
lean_dec_ref(v_i_169_);
return v_res_175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_FrameInferenceInfo_mkResidualPre(lean_object* v_i_176_, lean_object* v_a_177_, lean_object* v_a_178_, lean_object* v_a_179_, lean_object* v_a_180_, lean_object* v_a_181_, lean_object* v_a_182_){
_start:
{
lean_object* v___x_184_; 
v___x_184_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_FrameInferenceInfo_mkResidualPre___redArg(v_i_176_, v_a_179_, v_a_180_, v_a_181_, v_a_182_);
return v___x_184_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_FrameInferenceInfo_mkResidualPre___boxed(lean_object* v_i_185_, lean_object* v_a_186_, lean_object* v_a_187_, lean_object* v_a_188_, lean_object* v_a_189_, lean_object* v_a_190_, lean_object* v_a_191_, lean_object* v_a_192_){
_start:
{
lean_object* v_res_193_; 
v_res_193_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_FrameInferenceInfo_mkResidualPre(v_i_185_, v_a_186_, v_a_187_, v_a_188_, v_a_189_, v_a_190_, v_a_191_);
lean_dec(v_a_191_);
lean_dec_ref(v_a_190_);
lean_dec(v_a_189_);
lean_dec_ref(v_a_188_);
lean_dec(v_a_187_);
lean_dec_ref(v_a_186_);
lean_dec_ref(v_i_185_);
return v_res_193_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameInferenceInfo_specPre_x3f_spec__1___redArg(lean_object* v_e_194_, lean_object* v___y_195_){
_start:
{
uint8_t v___x_197_; 
v___x_197_ = l_Lean_Expr_hasMVar(v_e_194_);
if (v___x_197_ == 0)
{
lean_object* v___x_198_; 
v___x_198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_198_, 0, v_e_194_);
return v___x_198_;
}
else
{
lean_object* v___x_199_; lean_object* v_mctx_200_; lean_object* v___x_201_; lean_object* v_fst_202_; lean_object* v_snd_203_; lean_object* v___x_204_; lean_object* v_cache_205_; lean_object* v_zetaDeltaFVarIds_206_; lean_object* v_postponed_207_; lean_object* v_diag_208_; lean_object* v___x_210_; uint8_t v_isShared_211_; uint8_t v_isSharedCheck_217_; 
v___x_199_ = lean_st_ref_get(v___y_195_);
v_mctx_200_ = lean_ctor_get(v___x_199_, 0);
lean_inc_ref(v_mctx_200_);
lean_dec(v___x_199_);
v___x_201_ = l_Lean_instantiateMVarsCore(v_mctx_200_, v_e_194_);
v_fst_202_ = lean_ctor_get(v___x_201_, 0);
lean_inc(v_fst_202_);
v_snd_203_ = lean_ctor_get(v___x_201_, 1);
lean_inc(v_snd_203_);
lean_dec_ref(v___x_201_);
v___x_204_ = lean_st_ref_take(v___y_195_);
v_cache_205_ = lean_ctor_get(v___x_204_, 1);
v_zetaDeltaFVarIds_206_ = lean_ctor_get(v___x_204_, 2);
v_postponed_207_ = lean_ctor_get(v___x_204_, 3);
v_diag_208_ = lean_ctor_get(v___x_204_, 4);
v_isSharedCheck_217_ = !lean_is_exclusive(v___x_204_);
if (v_isSharedCheck_217_ == 0)
{
lean_object* v_unused_218_; 
v_unused_218_ = lean_ctor_get(v___x_204_, 0);
lean_dec(v_unused_218_);
v___x_210_ = v___x_204_;
v_isShared_211_ = v_isSharedCheck_217_;
goto v_resetjp_209_;
}
else
{
lean_inc(v_diag_208_);
lean_inc(v_postponed_207_);
lean_inc(v_zetaDeltaFVarIds_206_);
lean_inc(v_cache_205_);
lean_dec(v___x_204_);
v___x_210_ = lean_box(0);
v_isShared_211_ = v_isSharedCheck_217_;
goto v_resetjp_209_;
}
v_resetjp_209_:
{
lean_object* v___x_213_; 
if (v_isShared_211_ == 0)
{
lean_ctor_set(v___x_210_, 0, v_snd_203_);
v___x_213_ = v___x_210_;
goto v_reusejp_212_;
}
else
{
lean_object* v_reuseFailAlloc_216_; 
v_reuseFailAlloc_216_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_216_, 0, v_snd_203_);
lean_ctor_set(v_reuseFailAlloc_216_, 1, v_cache_205_);
lean_ctor_set(v_reuseFailAlloc_216_, 2, v_zetaDeltaFVarIds_206_);
lean_ctor_set(v_reuseFailAlloc_216_, 3, v_postponed_207_);
lean_ctor_set(v_reuseFailAlloc_216_, 4, v_diag_208_);
v___x_213_ = v_reuseFailAlloc_216_;
goto v_reusejp_212_;
}
v_reusejp_212_:
{
lean_object* v___x_214_; lean_object* v___x_215_; 
v___x_214_ = lean_st_ref_set(v___y_195_, v___x_213_);
v___x_215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_215_, 0, v_fst_202_);
return v___x_215_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameInferenceInfo_specPre_x3f_spec__1___redArg___boxed(lean_object* v_e_219_, lean_object* v___y_220_, lean_object* v___y_221_){
_start:
{
lean_object* v_res_222_; 
v_res_222_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameInferenceInfo_specPre_x3f_spec__1___redArg(v_e_219_, v___y_220_);
lean_dec(v___y_220_);
return v_res_222_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameInferenceInfo_specPre_x3f_spec__1(lean_object* v_e_223_, lean_object* v___y_224_, lean_object* v___y_225_, lean_object* v___y_226_, lean_object* v___y_227_, lean_object* v___y_228_, lean_object* v___y_229_){
_start:
{
lean_object* v___x_231_; 
v___x_231_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameInferenceInfo_specPre_x3f_spec__1___redArg(v_e_223_, v___y_227_);
return v___x_231_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameInferenceInfo_specPre_x3f_spec__1___boxed(lean_object* v_e_232_, lean_object* v___y_233_, lean_object* v___y_234_, lean_object* v___y_235_, lean_object* v___y_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_){
_start:
{
lean_object* v_res_240_; 
v_res_240_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameInferenceInfo_specPre_x3f_spec__1(v_e_232_, v___y_233_, v___y_234_, v___y_235_, v___y_236_, v___y_237_, v___y_238_);
lean_dec(v___y_238_);
lean_dec_ref(v___y_237_);
lean_dec(v___y_236_);
lean_dec_ref(v___y_235_);
lean_dec(v___y_234_);
lean_dec_ref(v___y_233_);
return v_res_240_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameInferenceInfo_specPre_x3f_spec__2___redArg___lam__0(lean_object* v___y_241_, lean_object* v_mctx_242_, lean_object* v_cache_243_, lean_object* v_a_x3f_244_){
_start:
{
lean_object* v___x_246_; lean_object* v_zetaDeltaFVarIds_247_; lean_object* v_postponed_248_; lean_object* v_diag_249_; lean_object* v___x_251_; uint8_t v_isShared_252_; uint8_t v_isSharedCheck_259_; 
v___x_246_ = lean_st_ref_take(v___y_241_);
v_zetaDeltaFVarIds_247_ = lean_ctor_get(v___x_246_, 2);
v_postponed_248_ = lean_ctor_get(v___x_246_, 3);
v_diag_249_ = lean_ctor_get(v___x_246_, 4);
v_isSharedCheck_259_ = !lean_is_exclusive(v___x_246_);
if (v_isSharedCheck_259_ == 0)
{
lean_object* v_unused_260_; lean_object* v_unused_261_; 
v_unused_260_ = lean_ctor_get(v___x_246_, 1);
lean_dec(v_unused_260_);
v_unused_261_ = lean_ctor_get(v___x_246_, 0);
lean_dec(v_unused_261_);
v___x_251_ = v___x_246_;
v_isShared_252_ = v_isSharedCheck_259_;
goto v_resetjp_250_;
}
else
{
lean_inc(v_diag_249_);
lean_inc(v_postponed_248_);
lean_inc(v_zetaDeltaFVarIds_247_);
lean_dec(v___x_246_);
v___x_251_ = lean_box(0);
v_isShared_252_ = v_isSharedCheck_259_;
goto v_resetjp_250_;
}
v_resetjp_250_:
{
lean_object* v___x_254_; 
if (v_isShared_252_ == 0)
{
lean_ctor_set(v___x_251_, 1, v_cache_243_);
lean_ctor_set(v___x_251_, 0, v_mctx_242_);
v___x_254_ = v___x_251_;
goto v_reusejp_253_;
}
else
{
lean_object* v_reuseFailAlloc_258_; 
v_reuseFailAlloc_258_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_258_, 0, v_mctx_242_);
lean_ctor_set(v_reuseFailAlloc_258_, 1, v_cache_243_);
lean_ctor_set(v_reuseFailAlloc_258_, 2, v_zetaDeltaFVarIds_247_);
lean_ctor_set(v_reuseFailAlloc_258_, 3, v_postponed_248_);
lean_ctor_set(v_reuseFailAlloc_258_, 4, v_diag_249_);
v___x_254_ = v_reuseFailAlloc_258_;
goto v_reusejp_253_;
}
v_reusejp_253_:
{
lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; 
v___x_255_ = lean_st_ref_set(v___y_241_, v___x_254_);
v___x_256_ = lean_box(0);
v___x_257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_257_, 0, v___x_256_);
return v___x_257_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameInferenceInfo_specPre_x3f_spec__2___redArg___lam__0___boxed(lean_object* v___y_262_, lean_object* v_mctx_263_, lean_object* v_cache_264_, lean_object* v_a_x3f_265_, lean_object* v___y_266_){
_start:
{
lean_object* v_res_267_; 
v_res_267_ = l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameInferenceInfo_specPre_x3f_spec__2___redArg___lam__0(v___y_262_, v_mctx_263_, v_cache_264_, v_a_x3f_265_);
lean_dec(v_a_x3f_265_);
lean_dec(v___y_262_);
return v_res_267_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameInferenceInfo_specPre_x3f_spec__2___redArg(lean_object* v_x_268_, lean_object* v___y_269_, lean_object* v___y_270_, lean_object* v___y_271_, lean_object* v___y_272_, lean_object* v___y_273_, lean_object* v___y_274_){
_start:
{
lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v_mctx_278_; lean_object* v_cache_279_; lean_object* v___x_280_; 
v___x_276_ = lean_st_ref_get(v___y_272_);
v___x_277_ = lean_st_ref_get(v___y_272_);
v_mctx_278_ = lean_ctor_get(v___x_276_, 0);
lean_inc_ref(v_mctx_278_);
lean_dec(v___x_276_);
v_cache_279_ = lean_ctor_get(v___x_277_, 1);
lean_inc_ref(v_cache_279_);
lean_dec(v___x_277_);
lean_inc(v___y_274_);
lean_inc_ref(v___y_273_);
lean_inc(v___y_272_);
lean_inc_ref(v___y_271_);
lean_inc(v___y_270_);
lean_inc_ref(v___y_269_);
v___x_280_ = lean_apply_7(v_x_268_, v___y_269_, v___y_270_, v___y_271_, v___y_272_, v___y_273_, v___y_274_, lean_box(0));
if (lean_obj_tag(v___x_280_) == 0)
{
lean_object* v_a_281_; lean_object* v___x_283_; uint8_t v_isShared_284_; uint8_t v_isSharedCheck_297_; 
v_a_281_ = lean_ctor_get(v___x_280_, 0);
v_isSharedCheck_297_ = !lean_is_exclusive(v___x_280_);
if (v_isSharedCheck_297_ == 0)
{
v___x_283_ = v___x_280_;
v_isShared_284_ = v_isSharedCheck_297_;
goto v_resetjp_282_;
}
else
{
lean_inc(v_a_281_);
lean_dec(v___x_280_);
v___x_283_ = lean_box(0);
v_isShared_284_ = v_isSharedCheck_297_;
goto v_resetjp_282_;
}
v_resetjp_282_:
{
lean_object* v___x_286_; 
lean_inc(v_a_281_);
if (v_isShared_284_ == 0)
{
lean_ctor_set_tag(v___x_283_, 1);
v___x_286_ = v___x_283_;
goto v_reusejp_285_;
}
else
{
lean_object* v_reuseFailAlloc_296_; 
v_reuseFailAlloc_296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_296_, 0, v_a_281_);
v___x_286_ = v_reuseFailAlloc_296_;
goto v_reusejp_285_;
}
v_reusejp_285_:
{
lean_object* v___x_287_; lean_object* v___x_289_; uint8_t v_isShared_290_; uint8_t v_isSharedCheck_294_; 
v___x_287_ = l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameInferenceInfo_specPre_x3f_spec__2___redArg___lam__0(v___y_272_, v_mctx_278_, v_cache_279_, v___x_286_);
lean_dec_ref(v___x_286_);
v_isSharedCheck_294_ = !lean_is_exclusive(v___x_287_);
if (v_isSharedCheck_294_ == 0)
{
lean_object* v_unused_295_; 
v_unused_295_ = lean_ctor_get(v___x_287_, 0);
lean_dec(v_unused_295_);
v___x_289_ = v___x_287_;
v_isShared_290_ = v_isSharedCheck_294_;
goto v_resetjp_288_;
}
else
{
lean_dec(v___x_287_);
v___x_289_ = lean_box(0);
v_isShared_290_ = v_isSharedCheck_294_;
goto v_resetjp_288_;
}
v_resetjp_288_:
{
lean_object* v___x_292_; 
if (v_isShared_290_ == 0)
{
lean_ctor_set(v___x_289_, 0, v_a_281_);
v___x_292_ = v___x_289_;
goto v_reusejp_291_;
}
else
{
lean_object* v_reuseFailAlloc_293_; 
v_reuseFailAlloc_293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_293_, 0, v_a_281_);
v___x_292_ = v_reuseFailAlloc_293_;
goto v_reusejp_291_;
}
v_reusejp_291_:
{
return v___x_292_;
}
}
}
}
}
else
{
lean_object* v_a_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_302_; uint8_t v_isShared_303_; uint8_t v_isSharedCheck_307_; 
v_a_298_ = lean_ctor_get(v___x_280_, 0);
lean_inc(v_a_298_);
lean_dec_ref_known(v___x_280_, 1);
v___x_299_ = lean_box(0);
v___x_300_ = l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameInferenceInfo_specPre_x3f_spec__2___redArg___lam__0(v___y_272_, v_mctx_278_, v_cache_279_, v___x_299_);
v_isSharedCheck_307_ = !lean_is_exclusive(v___x_300_);
if (v_isSharedCheck_307_ == 0)
{
lean_object* v_unused_308_; 
v_unused_308_ = lean_ctor_get(v___x_300_, 0);
lean_dec(v_unused_308_);
v___x_302_ = v___x_300_;
v_isShared_303_ = v_isSharedCheck_307_;
goto v_resetjp_301_;
}
else
{
lean_dec(v___x_300_);
v___x_302_ = lean_box(0);
v_isShared_303_ = v_isSharedCheck_307_;
goto v_resetjp_301_;
}
v_resetjp_301_:
{
lean_object* v___x_305_; 
if (v_isShared_303_ == 0)
{
lean_ctor_set_tag(v___x_302_, 1);
lean_ctor_set(v___x_302_, 0, v_a_298_);
v___x_305_ = v___x_302_;
goto v_reusejp_304_;
}
else
{
lean_object* v_reuseFailAlloc_306_; 
v_reuseFailAlloc_306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_306_, 0, v_a_298_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameInferenceInfo_specPre_x3f_spec__2___redArg___boxed(lean_object* v_x_309_, lean_object* v___y_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_, lean_object* v___y_314_, lean_object* v___y_315_, lean_object* v___y_316_){
_start:
{
lean_object* v_res_317_; 
v_res_317_ = l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameInferenceInfo_specPre_x3f_spec__2___redArg(v_x_309_, v___y_310_, v___y_311_, v___y_312_, v___y_313_, v___y_314_, v___y_315_);
lean_dec(v___y_315_);
lean_dec_ref(v___y_314_);
lean_dec(v___y_313_);
lean_dec_ref(v___y_312_);
lean_dec(v___y_311_);
lean_dec_ref(v___y_310_);
return v_res_317_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameInferenceInfo_specPre_x3f_spec__2(lean_object* v_00_u03b1_318_, lean_object* v_x_319_, lean_object* v___y_320_, lean_object* v___y_321_, lean_object* v___y_322_, lean_object* v___y_323_, lean_object* v___y_324_, lean_object* v___y_325_){
_start:
{
lean_object* v___x_327_; 
v___x_327_ = l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameInferenceInfo_specPre_x3f_spec__2___redArg(v_x_319_, v___y_320_, v___y_321_, v___y_322_, v___y_323_, v___y_324_, v___y_325_);
return v___x_327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameInferenceInfo_specPre_x3f_spec__2___boxed(lean_object* v_00_u03b1_328_, lean_object* v_x_329_, lean_object* v___y_330_, lean_object* v___y_331_, lean_object* v___y_332_, lean_object* v___y_333_, lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v___y_336_){
_start:
{
lean_object* v_res_337_; 
v_res_337_ = l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameInferenceInfo_specPre_x3f_spec__2(v_00_u03b1_328_, v_x_329_, v___y_330_, v___y_331_, v___y_332_, v___y_333_, v___y_334_, v___y_335_);
lean_dec(v___y_335_);
lean_dec_ref(v___y_334_);
lean_dec(v___y_333_);
lean_dec_ref(v___y_332_);
lean_dec(v___y_331_);
lean_dec_ref(v___y_330_);
return v_res_337_;
}
}
LEAN_EXPORT lean_object* l_List_findSomeM_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameInferenceInfo_specPre_x3f_spec__0___redArg(lean_object* v_x_347_, lean_object* v___y_348_, lean_object* v___y_349_, lean_object* v___y_350_, lean_object* v___y_351_){
_start:
{
if (lean_obj_tag(v_x_347_) == 0)
{
lean_object* v___x_353_; lean_object* v___x_354_; 
v___x_353_ = lean_box(0);
v___x_354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_354_, 0, v___x_353_);
return v___x_354_;
}
else
{
lean_object* v_head_355_; lean_object* v_tail_356_; lean_object* v___x_357_; 
v_head_355_ = lean_ctor_get(v_x_347_, 0);
lean_inc(v_head_355_);
v_tail_356_ = lean_ctor_get(v_x_347_, 1);
lean_inc(v_tail_356_);
lean_dec_ref_known(v_x_347_, 2);
v___x_357_ = l_Lean_MVarId_getType(v_head_355_, v___y_348_, v___y_349_, v___y_350_, v___y_351_);
if (lean_obj_tag(v___x_357_) == 0)
{
lean_object* v_a_358_; lean_object* v___x_360_; uint8_t v_isShared_361_; uint8_t v_isSharedCheck_383_; 
v_a_358_ = lean_ctor_get(v___x_357_, 0);
v_isSharedCheck_383_ = !lean_is_exclusive(v___x_357_);
if (v_isSharedCheck_383_ == 0)
{
v___x_360_ = v___x_357_;
v_isShared_361_ = v_isSharedCheck_383_;
goto v_resetjp_359_;
}
else
{
lean_inc(v_a_358_);
lean_dec(v___x_357_);
v___x_360_ = lean_box(0);
v_isShared_361_ = v_isSharedCheck_383_;
goto v_resetjp_359_;
}
v_resetjp_359_:
{
lean_object* v___x_362_; uint8_t v___x_363_; 
v___x_362_ = l_Lean_Expr_cleanupAnnotations(v_a_358_);
v___x_363_ = l_Lean_Expr_isApp(v___x_362_);
if (v___x_363_ == 0)
{
lean_dec_ref(v___x_362_);
lean_del_object(v___x_360_);
v_x_347_ = v_tail_356_;
goto _start;
}
else
{
lean_object* v_arg_365_; lean_object* v___x_366_; uint8_t v___x_367_; 
v_arg_365_ = lean_ctor_get(v___x_362_, 1);
lean_inc_ref(v_arg_365_);
v___x_366_ = l_Lean_Expr_appFnCleanup___redArg(v___x_362_);
v___x_367_ = l_Lean_Expr_isApp(v___x_366_);
if (v___x_367_ == 0)
{
lean_dec_ref(v___x_366_);
lean_dec_ref(v_arg_365_);
lean_del_object(v___x_360_);
v_x_347_ = v_tail_356_;
goto _start;
}
else
{
lean_object* v___x_369_; uint8_t v___x_370_; 
v___x_369_ = l_Lean_Expr_appFnCleanup___redArg(v___x_366_);
v___x_370_ = l_Lean_Expr_isApp(v___x_369_);
if (v___x_370_ == 0)
{
lean_dec_ref(v___x_369_);
lean_dec_ref(v_arg_365_);
lean_del_object(v___x_360_);
v_x_347_ = v_tail_356_;
goto _start;
}
else
{
lean_object* v___x_372_; uint8_t v___x_373_; 
v___x_372_ = l_Lean_Expr_appFnCleanup___redArg(v___x_369_);
v___x_373_ = l_Lean_Expr_isApp(v___x_372_);
if (v___x_373_ == 0)
{
lean_dec_ref(v___x_372_);
lean_dec_ref(v_arg_365_);
lean_del_object(v___x_360_);
v_x_347_ = v_tail_356_;
goto _start;
}
else
{
lean_object* v___x_375_; lean_object* v___x_376_; uint8_t v___x_377_; 
v___x_375_ = l_Lean_Expr_appFnCleanup___redArg(v___x_372_);
v___x_376_ = ((lean_object*)(l_List_findSomeM_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameInferenceInfo_specPre_x3f_spec__0___redArg___closed__4));
v___x_377_ = l_Lean_Expr_isConstOf(v___x_375_, v___x_376_);
lean_dec_ref(v___x_375_);
if (v___x_377_ == 0)
{
lean_dec_ref(v_arg_365_);
lean_del_object(v___x_360_);
v_x_347_ = v_tail_356_;
goto _start;
}
else
{
lean_object* v___x_379_; lean_object* v___x_381_; 
lean_dec(v_tail_356_);
v___x_379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_379_, 0, v_arg_365_);
if (v_isShared_361_ == 0)
{
lean_ctor_set(v___x_360_, 0, v___x_379_);
v___x_381_ = v___x_360_;
goto v_reusejp_380_;
}
else
{
lean_object* v_reuseFailAlloc_382_; 
v_reuseFailAlloc_382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_382_, 0, v___x_379_);
v___x_381_ = v_reuseFailAlloc_382_;
goto v_reusejp_380_;
}
v_reusejp_380_:
{
return v___x_381_;
}
}
}
}
}
}
}
}
else
{
lean_object* v_a_384_; lean_object* v___x_386_; uint8_t v_isShared_387_; uint8_t v_isSharedCheck_391_; 
lean_dec(v_tail_356_);
v_a_384_ = lean_ctor_get(v___x_357_, 0);
v_isSharedCheck_391_ = !lean_is_exclusive(v___x_357_);
if (v_isSharedCheck_391_ == 0)
{
v___x_386_ = v___x_357_;
v_isShared_387_ = v_isSharedCheck_391_;
goto v_resetjp_385_;
}
else
{
lean_inc(v_a_384_);
lean_dec(v___x_357_);
v___x_386_ = lean_box(0);
v_isShared_387_ = v_isSharedCheck_391_;
goto v_resetjp_385_;
}
v_resetjp_385_:
{
lean_object* v___x_389_; 
if (v_isShared_387_ == 0)
{
v___x_389_ = v___x_386_;
goto v_reusejp_388_;
}
else
{
lean_object* v_reuseFailAlloc_390_; 
v_reuseFailAlloc_390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_390_, 0, v_a_384_);
v___x_389_ = v_reuseFailAlloc_390_;
goto v_reusejp_388_;
}
v_reusejp_388_:
{
return v___x_389_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_findSomeM_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameInferenceInfo_specPre_x3f_spec__0___redArg___boxed(lean_object* v_x_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_){
_start:
{
lean_object* v_res_398_; 
v_res_398_ = l_List_findSomeM_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameInferenceInfo_specPre_x3f_spec__0___redArg(v_x_392_, v___y_393_, v___y_394_, v___y_395_, v___y_396_);
lean_dec(v___y_396_);
lean_dec_ref(v___y_395_);
lean_dec(v___y_394_);
lean_dec_ref(v___y_393_);
return v_res_398_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_FrameInferenceInfo_specPre_x3f___lam__0(lean_object* v_goal_399_, lean_object* v_specRule_400_, lean_object* v___y_401_, lean_object* v___y_402_, lean_object* v___y_403_, lean_object* v___y_404_, lean_object* v___y_405_, lean_object* v___y_406_){
_start:
{
lean_object* v___x_408_; 
v___x_408_ = l_Lean_Meta_Sym_BackwardRule_apply(v_goal_399_, v_specRule_400_, v___y_401_, v___y_402_, v___y_403_, v___y_404_, v___y_405_, v___y_406_);
if (lean_obj_tag(v___x_408_) == 0)
{
lean_object* v_a_409_; lean_object* v___x_411_; uint8_t v_isShared_412_; uint8_t v_isSharedCheck_464_; 
v_a_409_ = lean_ctor_get(v___x_408_, 0);
v_isSharedCheck_464_ = !lean_is_exclusive(v___x_408_);
if (v_isSharedCheck_464_ == 0)
{
v___x_411_ = v___x_408_;
v_isShared_412_ = v_isSharedCheck_464_;
goto v_resetjp_410_;
}
else
{
lean_inc(v_a_409_);
lean_dec(v___x_408_);
v___x_411_ = lean_box(0);
v_isShared_412_ = v_isSharedCheck_464_;
goto v_resetjp_410_;
}
v_resetjp_410_:
{
if (lean_obj_tag(v_a_409_) == 1)
{
lean_object* v_mvarIds_413_; lean_object* v___x_414_; 
lean_del_object(v___x_411_);
v_mvarIds_413_ = lean_ctor_get(v_a_409_, 0);
lean_inc(v_mvarIds_413_);
lean_dec_ref_known(v_a_409_, 1);
v___x_414_ = l_List_findSomeM_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameInferenceInfo_specPre_x3f_spec__0___redArg(v_mvarIds_413_, v___y_403_, v___y_404_, v___y_405_, v___y_406_);
if (lean_obj_tag(v___x_414_) == 0)
{
lean_object* v_a_415_; lean_object* v___x_417_; uint8_t v_isShared_418_; uint8_t v_isSharedCheck_451_; 
v_a_415_ = lean_ctor_get(v___x_414_, 0);
v_isSharedCheck_451_ = !lean_is_exclusive(v___x_414_);
if (v_isSharedCheck_451_ == 0)
{
v___x_417_ = v___x_414_;
v_isShared_418_ = v_isSharedCheck_451_;
goto v_resetjp_416_;
}
else
{
lean_inc(v_a_415_);
lean_dec(v___x_414_);
v___x_417_ = lean_box(0);
v_isShared_418_ = v_isSharedCheck_451_;
goto v_resetjp_416_;
}
v_resetjp_416_:
{
if (lean_obj_tag(v_a_415_) == 1)
{
lean_object* v_val_419_; lean_object* v___x_421_; uint8_t v_isShared_422_; uint8_t v_isSharedCheck_446_; 
lean_del_object(v___x_417_);
v_val_419_ = lean_ctor_get(v_a_415_, 0);
v_isSharedCheck_446_ = !lean_is_exclusive(v_a_415_);
if (v_isSharedCheck_446_ == 0)
{
v___x_421_ = v_a_415_;
v_isShared_422_ = v_isSharedCheck_446_;
goto v_resetjp_420_;
}
else
{
lean_inc(v_val_419_);
lean_dec(v_a_415_);
v___x_421_ = lean_box(0);
v_isShared_422_ = v_isSharedCheck_446_;
goto v_resetjp_420_;
}
v_resetjp_420_:
{
lean_object* v___x_423_; lean_object* v_a_424_; uint8_t v___x_425_; lean_object* v___x_426_; 
v___x_423_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameInferenceInfo_specPre_x3f_spec__1___redArg(v_val_419_, v___y_404_);
v_a_424_ = lean_ctor_get(v___x_423_, 0);
lean_inc(v_a_424_);
lean_dec_ref(v___x_423_);
v___x_425_ = 1;
v___x_426_ = l_Lean_Meta_abstractMVars(v_a_424_, v___x_425_, v___y_403_, v___y_404_, v___y_405_, v___y_406_);
if (lean_obj_tag(v___x_426_) == 0)
{
lean_object* v_a_427_; lean_object* v___x_429_; uint8_t v_isShared_430_; uint8_t v_isSharedCheck_437_; 
v_a_427_ = lean_ctor_get(v___x_426_, 0);
v_isSharedCheck_437_ = !lean_is_exclusive(v___x_426_);
if (v_isSharedCheck_437_ == 0)
{
v___x_429_ = v___x_426_;
v_isShared_430_ = v_isSharedCheck_437_;
goto v_resetjp_428_;
}
else
{
lean_inc(v_a_427_);
lean_dec(v___x_426_);
v___x_429_ = lean_box(0);
v_isShared_430_ = v_isSharedCheck_437_;
goto v_resetjp_428_;
}
v_resetjp_428_:
{
lean_object* v___x_432_; 
if (v_isShared_422_ == 0)
{
lean_ctor_set(v___x_421_, 0, v_a_427_);
v___x_432_ = v___x_421_;
goto v_reusejp_431_;
}
else
{
lean_object* v_reuseFailAlloc_436_; 
v_reuseFailAlloc_436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_436_, 0, v_a_427_);
v___x_432_ = v_reuseFailAlloc_436_;
goto v_reusejp_431_;
}
v_reusejp_431_:
{
lean_object* v___x_434_; 
if (v_isShared_430_ == 0)
{
lean_ctor_set(v___x_429_, 0, v___x_432_);
v___x_434_ = v___x_429_;
goto v_reusejp_433_;
}
else
{
lean_object* v_reuseFailAlloc_435_; 
v_reuseFailAlloc_435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_435_, 0, v___x_432_);
v___x_434_ = v_reuseFailAlloc_435_;
goto v_reusejp_433_;
}
v_reusejp_433_:
{
return v___x_434_;
}
}
}
}
else
{
lean_object* v_a_438_; lean_object* v___x_440_; uint8_t v_isShared_441_; uint8_t v_isSharedCheck_445_; 
lean_del_object(v___x_421_);
v_a_438_ = lean_ctor_get(v___x_426_, 0);
v_isSharedCheck_445_ = !lean_is_exclusive(v___x_426_);
if (v_isSharedCheck_445_ == 0)
{
v___x_440_ = v___x_426_;
v_isShared_441_ = v_isSharedCheck_445_;
goto v_resetjp_439_;
}
else
{
lean_inc(v_a_438_);
lean_dec(v___x_426_);
v___x_440_ = lean_box(0);
v_isShared_441_ = v_isSharedCheck_445_;
goto v_resetjp_439_;
}
v_resetjp_439_:
{
lean_object* v___x_443_; 
if (v_isShared_441_ == 0)
{
v___x_443_ = v___x_440_;
goto v_reusejp_442_;
}
else
{
lean_object* v_reuseFailAlloc_444_; 
v_reuseFailAlloc_444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_444_, 0, v_a_438_);
v___x_443_ = v_reuseFailAlloc_444_;
goto v_reusejp_442_;
}
v_reusejp_442_:
{
return v___x_443_;
}
}
}
}
}
else
{
lean_object* v___x_447_; lean_object* v___x_449_; 
lean_dec(v_a_415_);
v___x_447_ = lean_box(0);
if (v_isShared_418_ == 0)
{
lean_ctor_set(v___x_417_, 0, v___x_447_);
v___x_449_ = v___x_417_;
goto v_reusejp_448_;
}
else
{
lean_object* v_reuseFailAlloc_450_; 
v_reuseFailAlloc_450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_450_, 0, v___x_447_);
v___x_449_ = v_reuseFailAlloc_450_;
goto v_reusejp_448_;
}
v_reusejp_448_:
{
return v___x_449_;
}
}
}
}
else
{
lean_object* v_a_452_; lean_object* v___x_454_; uint8_t v_isShared_455_; uint8_t v_isSharedCheck_459_; 
v_a_452_ = lean_ctor_get(v___x_414_, 0);
v_isSharedCheck_459_ = !lean_is_exclusive(v___x_414_);
if (v_isSharedCheck_459_ == 0)
{
v___x_454_ = v___x_414_;
v_isShared_455_ = v_isSharedCheck_459_;
goto v_resetjp_453_;
}
else
{
lean_inc(v_a_452_);
lean_dec(v___x_414_);
v___x_454_ = lean_box(0);
v_isShared_455_ = v_isSharedCheck_459_;
goto v_resetjp_453_;
}
v_resetjp_453_:
{
lean_object* v___x_457_; 
if (v_isShared_455_ == 0)
{
v___x_457_ = v___x_454_;
goto v_reusejp_456_;
}
else
{
lean_object* v_reuseFailAlloc_458_; 
v_reuseFailAlloc_458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_458_, 0, v_a_452_);
v___x_457_ = v_reuseFailAlloc_458_;
goto v_reusejp_456_;
}
v_reusejp_456_:
{
return v___x_457_;
}
}
}
}
else
{
lean_object* v___x_460_; lean_object* v___x_462_; 
lean_dec(v_a_409_);
v___x_460_ = lean_box(0);
if (v_isShared_412_ == 0)
{
lean_ctor_set(v___x_411_, 0, v___x_460_);
v___x_462_ = v___x_411_;
goto v_reusejp_461_;
}
else
{
lean_object* v_reuseFailAlloc_463_; 
v_reuseFailAlloc_463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_463_, 0, v___x_460_);
v___x_462_ = v_reuseFailAlloc_463_;
goto v_reusejp_461_;
}
v_reusejp_461_:
{
return v___x_462_;
}
}
}
}
else
{
lean_object* v_a_465_; lean_object* v___x_467_; uint8_t v_isShared_468_; uint8_t v_isSharedCheck_472_; 
v_a_465_ = lean_ctor_get(v___x_408_, 0);
v_isSharedCheck_472_ = !lean_is_exclusive(v___x_408_);
if (v_isSharedCheck_472_ == 0)
{
v___x_467_ = v___x_408_;
v_isShared_468_ = v_isSharedCheck_472_;
goto v_resetjp_466_;
}
else
{
lean_inc(v_a_465_);
lean_dec(v___x_408_);
v___x_467_ = lean_box(0);
v_isShared_468_ = v_isSharedCheck_472_;
goto v_resetjp_466_;
}
v_resetjp_466_:
{
lean_object* v___x_470_; 
if (v_isShared_468_ == 0)
{
v___x_470_ = v___x_467_;
goto v_reusejp_469_;
}
else
{
lean_object* v_reuseFailAlloc_471_; 
v_reuseFailAlloc_471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_471_, 0, v_a_465_);
v___x_470_ = v_reuseFailAlloc_471_;
goto v_reusejp_469_;
}
v_reusejp_469_:
{
return v___x_470_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_FrameInferenceInfo_specPre_x3f___lam__0___boxed(lean_object* v_goal_473_, lean_object* v_specRule_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_){
_start:
{
lean_object* v_res_482_; 
v_res_482_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_FrameInferenceInfo_specPre_x3f___lam__0(v_goal_473_, v_specRule_474_, v___y_475_, v___y_476_, v___y_477_, v___y_478_, v___y_479_, v___y_480_);
lean_dec(v___y_480_);
lean_dec_ref(v___y_479_);
lean_dec(v___y_478_);
lean_dec_ref(v___y_477_);
lean_dec(v___y_476_);
lean_dec_ref(v___y_475_);
return v_res_482_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_FrameInferenceInfo_specPre_x3f(lean_object* v_i_483_, lean_object* v_a_484_, lean_object* v_a_485_, lean_object* v_a_486_, lean_object* v_a_487_, lean_object* v_a_488_, lean_object* v_a_489_){
_start:
{
lean_object* v_goal_491_; lean_object* v_specRule_492_; lean_object* v___f_493_; lean_object* v___x_494_; 
v_goal_491_ = lean_ctor_get(v_i_483_, 1);
lean_inc(v_goal_491_);
v_specRule_492_ = lean_ctor_get(v_i_483_, 4);
lean_inc_ref(v_specRule_492_);
lean_dec_ref(v_i_483_);
v___f_493_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_FrameInferenceInfo_specPre_x3f___lam__0___boxed), 9, 2);
lean_closure_set(v___f_493_, 0, v_goal_491_);
lean_closure_set(v___f_493_, 1, v_specRule_492_);
v___x_494_ = l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameInferenceInfo_specPre_x3f_spec__2___redArg(v___f_493_, v_a_484_, v_a_485_, v_a_486_, v_a_487_, v_a_488_, v_a_489_);
if (lean_obj_tag(v___x_494_) == 0)
{
lean_object* v_a_495_; lean_object* v___x_497_; uint8_t v_isShared_498_; uint8_t v_isSharedCheck_540_; 
v_a_495_ = lean_ctor_get(v___x_494_, 0);
v_isSharedCheck_540_ = !lean_is_exclusive(v___x_494_);
if (v_isSharedCheck_540_ == 0)
{
v___x_497_ = v___x_494_;
v_isShared_498_ = v_isSharedCheck_540_;
goto v_resetjp_496_;
}
else
{
lean_inc(v_a_495_);
lean_dec(v___x_494_);
v___x_497_ = lean_box(0);
v_isShared_498_ = v_isSharedCheck_540_;
goto v_resetjp_496_;
}
v_resetjp_496_:
{
if (lean_obj_tag(v_a_495_) == 1)
{
lean_object* v_val_499_; lean_object* v___x_501_; uint8_t v_isShared_502_; uint8_t v_isSharedCheck_535_; 
lean_del_object(v___x_497_);
v_val_499_ = lean_ctor_get(v_a_495_, 0);
v_isSharedCheck_535_ = !lean_is_exclusive(v_a_495_);
if (v_isSharedCheck_535_ == 0)
{
v___x_501_ = v_a_495_;
v_isShared_502_ = v_isSharedCheck_535_;
goto v_resetjp_500_;
}
else
{
lean_inc(v_val_499_);
lean_dec(v_a_495_);
v___x_501_ = lean_box(0);
v_isShared_502_ = v_isSharedCheck_535_;
goto v_resetjp_500_;
}
v_resetjp_500_:
{
lean_object* v___x_503_; 
v___x_503_ = l_Lean_Meta_openAbstractMVarsResult(v_val_499_, v_a_486_, v_a_487_, v_a_488_, v_a_489_);
if (lean_obj_tag(v___x_503_) == 0)
{
lean_object* v_a_504_; lean_object* v_snd_505_; lean_object* v_snd_506_; lean_object* v___x_507_; 
v_a_504_ = lean_ctor_get(v___x_503_, 0);
lean_inc(v_a_504_);
lean_dec_ref_known(v___x_503_, 1);
v_snd_505_ = lean_ctor_get(v_a_504_, 1);
lean_inc(v_snd_505_);
lean_dec(v_a_504_);
v_snd_506_ = lean_ctor_get(v_snd_505_, 1);
lean_inc(v_snd_506_);
lean_dec(v_snd_505_);
v___x_507_ = l_Lean_Meta_Sym_shareCommon(v_snd_506_, v_a_484_, v_a_485_, v_a_486_, v_a_487_, v_a_488_, v_a_489_);
if (lean_obj_tag(v___x_507_) == 0)
{
lean_object* v_a_508_; lean_object* v___x_510_; uint8_t v_isShared_511_; uint8_t v_isSharedCheck_518_; 
v_a_508_ = lean_ctor_get(v___x_507_, 0);
v_isSharedCheck_518_ = !lean_is_exclusive(v___x_507_);
if (v_isSharedCheck_518_ == 0)
{
v___x_510_ = v___x_507_;
v_isShared_511_ = v_isSharedCheck_518_;
goto v_resetjp_509_;
}
else
{
lean_inc(v_a_508_);
lean_dec(v___x_507_);
v___x_510_ = lean_box(0);
v_isShared_511_ = v_isSharedCheck_518_;
goto v_resetjp_509_;
}
v_resetjp_509_:
{
lean_object* v___x_513_; 
if (v_isShared_502_ == 0)
{
lean_ctor_set(v___x_501_, 0, v_a_508_);
v___x_513_ = v___x_501_;
goto v_reusejp_512_;
}
else
{
lean_object* v_reuseFailAlloc_517_; 
v_reuseFailAlloc_517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_517_, 0, v_a_508_);
v___x_513_ = v_reuseFailAlloc_517_;
goto v_reusejp_512_;
}
v_reusejp_512_:
{
lean_object* v___x_515_; 
if (v_isShared_511_ == 0)
{
lean_ctor_set(v___x_510_, 0, v___x_513_);
v___x_515_ = v___x_510_;
goto v_reusejp_514_;
}
else
{
lean_object* v_reuseFailAlloc_516_; 
v_reuseFailAlloc_516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_516_, 0, v___x_513_);
v___x_515_ = v_reuseFailAlloc_516_;
goto v_reusejp_514_;
}
v_reusejp_514_:
{
return v___x_515_;
}
}
}
}
else
{
lean_object* v_a_519_; lean_object* v___x_521_; uint8_t v_isShared_522_; uint8_t v_isSharedCheck_526_; 
lean_del_object(v___x_501_);
v_a_519_ = lean_ctor_get(v___x_507_, 0);
v_isSharedCheck_526_ = !lean_is_exclusive(v___x_507_);
if (v_isSharedCheck_526_ == 0)
{
v___x_521_ = v___x_507_;
v_isShared_522_ = v_isSharedCheck_526_;
goto v_resetjp_520_;
}
else
{
lean_inc(v_a_519_);
lean_dec(v___x_507_);
v___x_521_ = lean_box(0);
v_isShared_522_ = v_isSharedCheck_526_;
goto v_resetjp_520_;
}
v_resetjp_520_:
{
lean_object* v___x_524_; 
if (v_isShared_522_ == 0)
{
v___x_524_ = v___x_521_;
goto v_reusejp_523_;
}
else
{
lean_object* v_reuseFailAlloc_525_; 
v_reuseFailAlloc_525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_525_, 0, v_a_519_);
v___x_524_ = v_reuseFailAlloc_525_;
goto v_reusejp_523_;
}
v_reusejp_523_:
{
return v___x_524_;
}
}
}
}
else
{
lean_object* v_a_527_; lean_object* v___x_529_; uint8_t v_isShared_530_; uint8_t v_isSharedCheck_534_; 
lean_del_object(v___x_501_);
v_a_527_ = lean_ctor_get(v___x_503_, 0);
v_isSharedCheck_534_ = !lean_is_exclusive(v___x_503_);
if (v_isSharedCheck_534_ == 0)
{
v___x_529_ = v___x_503_;
v_isShared_530_ = v_isSharedCheck_534_;
goto v_resetjp_528_;
}
else
{
lean_inc(v_a_527_);
lean_dec(v___x_503_);
v___x_529_ = lean_box(0);
v_isShared_530_ = v_isSharedCheck_534_;
goto v_resetjp_528_;
}
v_resetjp_528_:
{
lean_object* v___x_532_; 
if (v_isShared_530_ == 0)
{
v___x_532_ = v___x_529_;
goto v_reusejp_531_;
}
else
{
lean_object* v_reuseFailAlloc_533_; 
v_reuseFailAlloc_533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_533_, 0, v_a_527_);
v___x_532_ = v_reuseFailAlloc_533_;
goto v_reusejp_531_;
}
v_reusejp_531_:
{
return v___x_532_;
}
}
}
}
}
else
{
lean_object* v___x_536_; lean_object* v___x_538_; 
lean_dec(v_a_495_);
v___x_536_ = lean_box(0);
if (v_isShared_498_ == 0)
{
lean_ctor_set(v___x_497_, 0, v___x_536_);
v___x_538_ = v___x_497_;
goto v_reusejp_537_;
}
else
{
lean_object* v_reuseFailAlloc_539_; 
v_reuseFailAlloc_539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_539_, 0, v___x_536_);
v___x_538_ = v_reuseFailAlloc_539_;
goto v_reusejp_537_;
}
v_reusejp_537_:
{
return v___x_538_;
}
}
}
}
else
{
lean_object* v_a_541_; lean_object* v___x_543_; uint8_t v_isShared_544_; uint8_t v_isSharedCheck_548_; 
v_a_541_ = lean_ctor_get(v___x_494_, 0);
v_isSharedCheck_548_ = !lean_is_exclusive(v___x_494_);
if (v_isSharedCheck_548_ == 0)
{
v___x_543_ = v___x_494_;
v_isShared_544_ = v_isSharedCheck_548_;
goto v_resetjp_542_;
}
else
{
lean_inc(v_a_541_);
lean_dec(v___x_494_);
v___x_543_ = lean_box(0);
v_isShared_544_ = v_isSharedCheck_548_;
goto v_resetjp_542_;
}
v_resetjp_542_:
{
lean_object* v___x_546_; 
if (v_isShared_544_ == 0)
{
v___x_546_ = v___x_543_;
goto v_reusejp_545_;
}
else
{
lean_object* v_reuseFailAlloc_547_; 
v_reuseFailAlloc_547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_547_, 0, v_a_541_);
v___x_546_ = v_reuseFailAlloc_547_;
goto v_reusejp_545_;
}
v_reusejp_545_:
{
return v___x_546_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_FrameInferenceInfo_specPre_x3f___boxed(lean_object* v_i_549_, lean_object* v_a_550_, lean_object* v_a_551_, lean_object* v_a_552_, lean_object* v_a_553_, lean_object* v_a_554_, lean_object* v_a_555_, lean_object* v_a_556_){
_start:
{
lean_object* v_res_557_; 
v_res_557_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_FrameInferenceInfo_specPre_x3f(v_i_549_, v_a_550_, v_a_551_, v_a_552_, v_a_553_, v_a_554_, v_a_555_);
lean_dec(v_a_555_);
lean_dec_ref(v_a_554_);
lean_dec(v_a_553_);
lean_dec_ref(v_a_552_);
lean_dec(v_a_551_);
lean_dec_ref(v_a_550_);
return v_res_557_;
}
}
LEAN_EXPORT lean_object* l_List_findSomeM_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameInferenceInfo_specPre_x3f_spec__0(lean_object* v_x_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_){
_start:
{
lean_object* v___x_566_; 
v___x_566_ = l_List_findSomeM_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameInferenceInfo_specPre_x3f_spec__0___redArg(v_x_558_, v___y_561_, v___y_562_, v___y_563_, v___y_564_);
return v___x_566_;
}
}
LEAN_EXPORT lean_object* l_List_findSomeM_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameInferenceInfo_specPre_x3f_spec__0___boxed(lean_object* v_x_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_){
_start:
{
lean_object* v_res_575_; 
v_res_575_ = l_List_findSomeM_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameInferenceInfo_specPre_x3f_spec__0(v_x_567_, v___y_568_, v___y_569_, v___y_570_, v___y_571_, v___y_572_, v___y_573_);
lean_dec(v___y_573_);
lean_dec_ref(v___y_572_);
lean_dec(v___y_571_);
lean_dec_ref(v___y_570_);
lean_dec(v___y_569_);
lean_dec_ref(v___y_568_);
return v_res_575_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameInferenceInfo_mkSplitVCS_spec__0_spec__0_spec__1(lean_object* v_f_576_, lean_object* v_a_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_){
_start:
{
lean_object* v___y_586_; lean_object* v___x_589_; uint8_t v_debug_590_; 
v___x_589_ = lean_st_ref_get(v___y_579_);
v_debug_590_ = lean_ctor_get_uint8(v___x_589_, sizeof(void*)*11);
lean_dec(v___x_589_);
if (v_debug_590_ == 0)
{
v___y_586_ = v___y_579_;
goto v___jp_585_;
}
else
{
lean_object* v___x_591_; 
v___x_591_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_f_576_, v___y_578_, v___y_579_, v___y_580_, v___y_581_, v___y_582_, v___y_583_);
if (lean_obj_tag(v___x_591_) == 0)
{
lean_object* v___x_592_; 
lean_dec_ref_known(v___x_591_, 1);
v___x_592_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_a_577_, v___y_578_, v___y_579_, v___y_580_, v___y_581_, v___y_582_, v___y_583_);
if (lean_obj_tag(v___x_592_) == 0)
{
lean_dec_ref_known(v___x_592_, 1);
v___y_586_ = v___y_579_;
goto v___jp_585_;
}
else
{
lean_object* v_a_593_; lean_object* v___x_595_; uint8_t v_isShared_596_; uint8_t v_isSharedCheck_600_; 
lean_dec_ref(v_a_577_);
lean_dec_ref(v_f_576_);
v_a_593_ = lean_ctor_get(v___x_592_, 0);
v_isSharedCheck_600_ = !lean_is_exclusive(v___x_592_);
if (v_isSharedCheck_600_ == 0)
{
v___x_595_ = v___x_592_;
v_isShared_596_ = v_isSharedCheck_600_;
goto v_resetjp_594_;
}
else
{
lean_inc(v_a_593_);
lean_dec(v___x_592_);
v___x_595_ = lean_box(0);
v_isShared_596_ = v_isSharedCheck_600_;
goto v_resetjp_594_;
}
v_resetjp_594_:
{
lean_object* v___x_598_; 
if (v_isShared_596_ == 0)
{
v___x_598_ = v___x_595_;
goto v_reusejp_597_;
}
else
{
lean_object* v_reuseFailAlloc_599_; 
v_reuseFailAlloc_599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_599_, 0, v_a_593_);
v___x_598_ = v_reuseFailAlloc_599_;
goto v_reusejp_597_;
}
v_reusejp_597_:
{
return v___x_598_;
}
}
}
}
else
{
lean_object* v_a_601_; lean_object* v___x_603_; uint8_t v_isShared_604_; uint8_t v_isSharedCheck_608_; 
lean_dec_ref(v_a_577_);
lean_dec_ref(v_f_576_);
v_a_601_ = lean_ctor_get(v___x_591_, 0);
v_isSharedCheck_608_ = !lean_is_exclusive(v___x_591_);
if (v_isSharedCheck_608_ == 0)
{
v___x_603_ = v___x_591_;
v_isShared_604_ = v_isSharedCheck_608_;
goto v_resetjp_602_;
}
else
{
lean_inc(v_a_601_);
lean_dec(v___x_591_);
v___x_603_ = lean_box(0);
v_isShared_604_ = v_isSharedCheck_608_;
goto v_resetjp_602_;
}
v_resetjp_602_:
{
lean_object* v___x_606_; 
if (v_isShared_604_ == 0)
{
v___x_606_ = v___x_603_;
goto v_reusejp_605_;
}
else
{
lean_object* v_reuseFailAlloc_607_; 
v_reuseFailAlloc_607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_607_, 0, v_a_601_);
v___x_606_ = v_reuseFailAlloc_607_;
goto v_reusejp_605_;
}
v_reusejp_605_:
{
return v___x_606_;
}
}
}
}
v___jp_585_:
{
lean_object* v___x_587_; lean_object* v___x_588_; 
v___x_587_ = l_Lean_Expr_app___override(v_f_576_, v_a_577_);
v___x_588_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_587_, v___y_586_);
return v___x_588_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameInferenceInfo_mkSplitVCS_spec__0_spec__0_spec__1___boxed(lean_object* v_f_609_, lean_object* v_a_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_){
_start:
{
lean_object* v_res_618_; 
v_res_618_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameInferenceInfo_mkSplitVCS_spec__0_spec__0_spec__1(v_f_609_, v_a_610_, v___y_611_, v___y_612_, v___y_613_, v___y_614_, v___y_615_, v___y_616_);
lean_dec(v___y_616_);
lean_dec_ref(v___y_615_);
lean_dec(v___y_614_);
lean_dec_ref(v___y_613_);
lean_dec(v___y_612_);
lean_dec_ref(v___y_611_);
return v_res_618_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameInferenceInfo_mkSplitVCS_spec__0_spec__0(lean_object* v_args_619_, lean_object* v_endIdx_620_, lean_object* v_b_621_, lean_object* v_i_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_){
_start:
{
uint8_t v___x_630_; 
v___x_630_ = lean_nat_dec_le(v_endIdx_620_, v_i_622_);
if (v___x_630_ == 0)
{
lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; 
v___x_631_ = l_Lean_instInhabitedExpr;
v___x_632_ = lean_array_get_borrowed(v___x_631_, v_args_619_, v_i_622_);
lean_inc(v___x_632_);
v___x_633_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameInferenceInfo_mkSplitVCS_spec__0_spec__0_spec__1(v_b_621_, v___x_632_, v___y_623_, v___y_624_, v___y_625_, v___y_626_, v___y_627_, v___y_628_);
if (lean_obj_tag(v___x_633_) == 0)
{
lean_object* v_a_634_; lean_object* v___x_635_; lean_object* v___x_636_; 
v_a_634_ = lean_ctor_get(v___x_633_, 0);
lean_inc(v_a_634_);
lean_dec_ref_known(v___x_633_, 1);
v___x_635_ = lean_unsigned_to_nat(1u);
v___x_636_ = lean_nat_add(v_i_622_, v___x_635_);
lean_dec(v_i_622_);
v_b_621_ = v_a_634_;
v_i_622_ = v___x_636_;
goto _start;
}
else
{
lean_dec(v_i_622_);
return v___x_633_;
}
}
else
{
lean_object* v___x_638_; 
lean_dec(v_i_622_);
v___x_638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_638_, 0, v_b_621_);
return v___x_638_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameInferenceInfo_mkSplitVCS_spec__0_spec__0___boxed(lean_object* v_args_639_, lean_object* v_endIdx_640_, lean_object* v_b_641_, lean_object* v_i_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_, lean_object* v___y_646_, lean_object* v___y_647_, lean_object* v___y_648_, lean_object* v___y_649_){
_start:
{
lean_object* v_res_650_; 
v_res_650_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameInferenceInfo_mkSplitVCS_spec__0_spec__0(v_args_639_, v_endIdx_640_, v_b_641_, v_i_642_, v___y_643_, v___y_644_, v___y_645_, v___y_646_, v___y_647_, v___y_648_);
lean_dec(v___y_648_);
lean_dec_ref(v___y_647_);
lean_dec(v___y_646_);
lean_dec_ref(v___y_645_);
lean_dec(v___y_644_);
lean_dec_ref(v___y_643_);
lean_dec(v_endIdx_640_);
lean_dec_ref(v_args_639_);
return v_res_650_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameInferenceInfo_mkSplitVCS_spec__0(lean_object* v_f_651_, lean_object* v_args_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_){
_start:
{
lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; 
v___x_660_ = lean_unsigned_to_nat(0u);
v___x_661_ = lean_array_get_size(v_args_652_);
v___x_662_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameInferenceInfo_mkSplitVCS_spec__0_spec__0(v_args_652_, v___x_661_, v_f_651_, v___x_660_, v___y_653_, v___y_654_, v___y_655_, v___y_656_, v___y_657_, v___y_658_);
return v___x_662_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameInferenceInfo_mkSplitVCS_spec__0___boxed(lean_object* v_f_663_, lean_object* v_args_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_){
_start:
{
lean_object* v_res_672_; 
v_res_672_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameInferenceInfo_mkSplitVCS_spec__0(v_f_663_, v_args_664_, v___y_665_, v___y_666_, v___y_667_, v___y_668_, v___y_669_, v___y_670_);
lean_dec(v___y_670_);
lean_dec_ref(v___y_669_);
lean_dec(v___y_668_);
lean_dec_ref(v___y_667_);
lean_dec(v___y_666_);
lean_dec_ref(v___y_665_);
lean_dec_ref(v_args_664_);
return v_res_672_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_FrameInferenceInfo_mkSplitVCS(lean_object* v_i_673_, lean_object* v_frame_674_, lean_object* v_footprint_675_, lean_object* v_a_676_, lean_object* v_a_677_, lean_object* v_a_678_, lean_object* v_a_679_, lean_object* v_a_680_, lean_object* v_a_681_){
_start:
{
lean_object* v_toWPApp_683_; lean_object* v_goal_684_; lean_object* v_mkOpApp_685_; lean_object* v___x_686_; 
v_toWPApp_683_ = lean_ctor_get(v_i_673_, 0);
lean_inc_ref(v_toWPApp_683_);
v_goal_684_ = lean_ctor_get(v_i_673_, 1);
lean_inc(v_goal_684_);
v_mkOpApp_685_ = lean_ctor_get(v_i_673_, 5);
lean_inc_ref(v_mkOpApp_685_);
lean_dec_ref(v_i_673_);
lean_inc(v_a_681_);
lean_inc_ref(v_a_680_);
lean_inc(v_a_679_);
lean_inc_ref(v_a_678_);
lean_inc(v_a_677_);
lean_inc_ref(v_a_676_);
v___x_686_ = lean_apply_7(v_mkOpApp_685_, v_a_676_, v_a_677_, v_a_678_, v_a_679_, v_a_680_, v_a_681_, lean_box(0));
if (lean_obj_tag(v___x_686_) == 0)
{
lean_object* v_a_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; 
v_a_687_ = lean_ctor_get(v___x_686_, 0);
lean_inc(v_a_687_);
lean_dec_ref_known(v___x_686_, 1);
v___x_688_ = lean_unsigned_to_nat(2u);
v___x_689_ = lean_mk_empty_array_with_capacity(v___x_688_);
lean_inc_ref(v___x_689_);
v___x_690_ = lean_array_push(v___x_689_, v_frame_674_);
v___x_691_ = lean_array_push(v___x_690_, v_footprint_675_);
v___x_692_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameInferenceInfo_mkSplitVCS_spec__0(v_a_687_, v___x_691_, v_a_676_, v_a_677_, v_a_678_, v_a_679_, v_a_680_, v_a_681_);
lean_dec_ref(v___x_691_);
if (lean_obj_tag(v___x_692_) == 0)
{
lean_object* v_a_693_; lean_object* v_excessArgs_694_; lean_object* v___x_695_; 
v_a_693_ = lean_ctor_get(v___x_692_, 0);
lean_inc(v_a_693_);
lean_dec_ref_known(v___x_692_, 1);
v_excessArgs_694_ = lean_ctor_get(v_toWPApp_683_, 2);
lean_inc_ref(v_excessArgs_694_);
lean_dec_ref(v_toWPApp_683_);
v___x_695_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameInferenceInfo_mkSplitVCS_spec__0(v_a_693_, v_excessArgs_694_, v_a_676_, v_a_677_, v_a_678_, v_a_679_, v_a_680_, v_a_681_);
lean_dec_ref(v_excessArgs_694_);
if (lean_obj_tag(v___x_695_) == 0)
{
lean_object* v_a_696_; lean_object* v___x_697_; 
v_a_696_ = lean_ctor_get(v___x_695_, 0);
lean_inc(v_a_696_);
lean_dec_ref_known(v___x_695_, 1);
v___x_697_ = l_Lean_MVarId_getType(v_goal_684_, v_a_678_, v_a_679_, v_a_680_, v_a_681_);
if (lean_obj_tag(v___x_697_) == 0)
{
lean_object* v_a_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; 
v_a_698_ = lean_ctor_get(v___x_697_, 0);
lean_inc(v_a_698_);
lean_dec_ref_known(v___x_697_, 1);
v___x_699_ = l_Lean_Expr_stripArgsN(v_a_698_, v___x_688_);
v___x_700_ = l_Lean_Expr_appFn_x21(v_a_698_);
lean_dec(v_a_698_);
v___x_701_ = l_Lean_Expr_appArg_x21(v___x_700_);
lean_dec_ref(v___x_700_);
v___x_702_ = lean_array_push(v___x_689_, v___x_701_);
v___x_703_ = lean_array_push(v___x_702_, v_a_696_);
v___x_704_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameInferenceInfo_mkSplitVCS_spec__0(v___x_699_, v___x_703_, v_a_676_, v_a_677_, v_a_678_, v_a_679_, v_a_680_, v_a_681_);
lean_dec_ref(v___x_703_);
return v___x_704_;
}
else
{
lean_dec(v_a_696_);
lean_dec_ref(v___x_689_);
return v___x_697_;
}
}
else
{
lean_dec_ref(v___x_689_);
lean_dec(v_goal_684_);
return v___x_695_;
}
}
else
{
lean_dec_ref(v___x_689_);
lean_dec(v_goal_684_);
lean_dec_ref(v_toWPApp_683_);
return v___x_692_;
}
}
else
{
lean_dec(v_goal_684_);
lean_dec_ref(v_toWPApp_683_);
lean_dec_ref(v_footprint_675_);
lean_dec_ref(v_frame_674_);
return v___x_686_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_FrameInferenceInfo_mkSplitVCS___boxed(lean_object* v_i_705_, lean_object* v_frame_706_, lean_object* v_footprint_707_, lean_object* v_a_708_, lean_object* v_a_709_, lean_object* v_a_710_, lean_object* v_a_711_, lean_object* v_a_712_, lean_object* v_a_713_, lean_object* v_a_714_){
_start:
{
lean_object* v_res_715_; 
v_res_715_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_FrameInferenceInfo_mkSplitVCS(v_i_705_, v_frame_706_, v_footprint_707_, v_a_708_, v_a_709_, v_a_710_, v_a_711_, v_a_712_, v_a_713_);
lean_dec(v_a_713_);
lean_dec_ref(v_a_712_);
lean_dec(v_a_711_);
lean_dec_ref(v_a_710_);
lean_dec(v_a_709_);
lean_dec_ref(v_a_708_);
return v_res_715_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_FrameSplit_withDeferredSplitVC(lean_object* v_i_716_, lean_object* v_frame_717_, lean_object* v_a_718_, lean_object* v_a_719_, lean_object* v_a_720_, lean_object* v_a_721_, lean_object* v_a_722_, lean_object* v_a_723_){
_start:
{
lean_object* v___x_725_; 
v___x_725_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_FrameInferenceInfo_mkResidualPre___redArg(v_i_716_, v_a_720_, v_a_721_, v_a_722_, v_a_723_);
if (lean_obj_tag(v___x_725_) == 0)
{
lean_object* v_a_726_; lean_object* v___x_727_; lean_object* v___x_728_; 
v_a_726_ = lean_ctor_get(v___x_725_, 0);
lean_inc_n(v_a_726_, 2);
lean_dec_ref_known(v___x_725_, 1);
v___x_727_ = l_Lean_mkMVar(v_a_726_);
lean_inc_ref(v_frame_717_);
v___x_728_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_FrameInferenceInfo_mkSplitVCS(v_i_716_, v_frame_717_, v___x_727_, v_a_718_, v_a_719_, v_a_720_, v_a_721_, v_a_722_, v_a_723_);
if (lean_obj_tag(v___x_728_) == 0)
{
lean_object* v_a_729_; lean_object* v___x_730_; lean_object* v___x_731_; 
v_a_729_ = lean_ctor_get(v___x_728_, 0);
lean_inc(v_a_729_);
lean_dec_ref_known(v___x_728_, 1);
v___x_730_ = lean_box(0);
v___x_731_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_729_, v___x_730_, v_a_720_, v_a_721_, v_a_722_, v_a_723_);
if (lean_obj_tag(v___x_731_) == 0)
{
lean_object* v_a_732_; lean_object* v___x_734_; uint8_t v_isShared_735_; uint8_t v_isSharedCheck_743_; 
v_a_732_ = lean_ctor_get(v___x_731_, 0);
v_isSharedCheck_743_ = !lean_is_exclusive(v___x_731_);
if (v_isSharedCheck_743_ == 0)
{
v___x_734_ = v___x_731_;
v_isShared_735_ = v_isSharedCheck_743_;
goto v_resetjp_733_;
}
else
{
lean_inc(v_a_732_);
lean_dec(v___x_731_);
v___x_734_ = lean_box(0);
v_isShared_735_ = v_isSharedCheck_743_;
goto v_resetjp_733_;
}
v_resetjp_733_:
{
lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_741_; 
v___x_736_ = l_Lean_Expr_mvarId_x21(v_a_732_);
v___x_737_ = lean_box(0);
v___x_738_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_738_, 0, v___x_736_);
lean_ctor_set(v___x_738_, 1, v___x_737_);
v___x_739_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_739_, 0, v_frame_717_);
lean_ctor_set(v___x_739_, 1, v_a_726_);
lean_ctor_set(v___x_739_, 2, v_a_732_);
lean_ctor_set(v___x_739_, 3, v___x_738_);
if (v_isShared_735_ == 0)
{
lean_ctor_set(v___x_734_, 0, v___x_739_);
v___x_741_ = v___x_734_;
goto v_reusejp_740_;
}
else
{
lean_object* v_reuseFailAlloc_742_; 
v_reuseFailAlloc_742_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_742_, 0, v___x_739_);
v___x_741_ = v_reuseFailAlloc_742_;
goto v_reusejp_740_;
}
v_reusejp_740_:
{
return v___x_741_;
}
}
}
else
{
lean_object* v_a_744_; lean_object* v___x_746_; uint8_t v_isShared_747_; uint8_t v_isSharedCheck_751_; 
lean_dec(v_a_726_);
lean_dec_ref(v_frame_717_);
v_a_744_ = lean_ctor_get(v___x_731_, 0);
v_isSharedCheck_751_ = !lean_is_exclusive(v___x_731_);
if (v_isSharedCheck_751_ == 0)
{
v___x_746_ = v___x_731_;
v_isShared_747_ = v_isSharedCheck_751_;
goto v_resetjp_745_;
}
else
{
lean_inc(v_a_744_);
lean_dec(v___x_731_);
v___x_746_ = lean_box(0);
v_isShared_747_ = v_isSharedCheck_751_;
goto v_resetjp_745_;
}
v_resetjp_745_:
{
lean_object* v___x_749_; 
if (v_isShared_747_ == 0)
{
v___x_749_ = v___x_746_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_750_; 
v_reuseFailAlloc_750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_750_, 0, v_a_744_);
v___x_749_ = v_reuseFailAlloc_750_;
goto v_reusejp_748_;
}
v_reusejp_748_:
{
return v___x_749_;
}
}
}
}
else
{
lean_object* v_a_752_; lean_object* v___x_754_; uint8_t v_isShared_755_; uint8_t v_isSharedCheck_759_; 
lean_dec(v_a_726_);
lean_dec_ref(v_frame_717_);
v_a_752_ = lean_ctor_get(v___x_728_, 0);
v_isSharedCheck_759_ = !lean_is_exclusive(v___x_728_);
if (v_isSharedCheck_759_ == 0)
{
v___x_754_ = v___x_728_;
v_isShared_755_ = v_isSharedCheck_759_;
goto v_resetjp_753_;
}
else
{
lean_inc(v_a_752_);
lean_dec(v___x_728_);
v___x_754_ = lean_box(0);
v_isShared_755_ = v_isSharedCheck_759_;
goto v_resetjp_753_;
}
v_resetjp_753_:
{
lean_object* v___x_757_; 
if (v_isShared_755_ == 0)
{
v___x_757_ = v___x_754_;
goto v_reusejp_756_;
}
else
{
lean_object* v_reuseFailAlloc_758_; 
v_reuseFailAlloc_758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_758_, 0, v_a_752_);
v___x_757_ = v_reuseFailAlloc_758_;
goto v_reusejp_756_;
}
v_reusejp_756_:
{
return v___x_757_;
}
}
}
}
else
{
lean_object* v_a_760_; lean_object* v___x_762_; uint8_t v_isShared_763_; uint8_t v_isSharedCheck_767_; 
lean_dec_ref(v_frame_717_);
lean_dec_ref(v_i_716_);
v_a_760_ = lean_ctor_get(v___x_725_, 0);
v_isSharedCheck_767_ = !lean_is_exclusive(v___x_725_);
if (v_isSharedCheck_767_ == 0)
{
v___x_762_ = v___x_725_;
v_isShared_763_ = v_isSharedCheck_767_;
goto v_resetjp_761_;
}
else
{
lean_inc(v_a_760_);
lean_dec(v___x_725_);
v___x_762_ = lean_box(0);
v_isShared_763_ = v_isSharedCheck_767_;
goto v_resetjp_761_;
}
v_resetjp_761_:
{
lean_object* v___x_765_; 
if (v_isShared_763_ == 0)
{
v___x_765_ = v___x_762_;
goto v_reusejp_764_;
}
else
{
lean_object* v_reuseFailAlloc_766_; 
v_reuseFailAlloc_766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_766_, 0, v_a_760_);
v___x_765_ = v_reuseFailAlloc_766_;
goto v_reusejp_764_;
}
v_reusejp_764_:
{
return v___x_765_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_FrameSplit_withDeferredSplitVC___boxed(lean_object* v_i_768_, lean_object* v_frame_769_, lean_object* v_a_770_, lean_object* v_a_771_, lean_object* v_a_772_, lean_object* v_a_773_, lean_object* v_a_774_, lean_object* v_a_775_, lean_object* v_a_776_){
_start:
{
lean_object* v_res_777_; 
v_res_777_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_FrameSplit_withDeferredSplitVC(v_i_768_, v_frame_769_, v_a_770_, v_a_771_, v_a_772_, v_a_773_, v_a_774_, v_a_775_);
lean_dec(v_a_775_);
lean_dec_ref(v_a_774_);
lean_dec(v_a_773_);
lean_dec_ref(v_a_772_);
lean_dec(v_a_771_);
lean_dec_ref(v_a_770_);
return v_res_777_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_FrameSplit_withDischargedSplitVC(lean_object* v_frame_778_, lean_object* v_residualPre_779_, lean_object* v_splitVCProof_780_, lean_object* v_subgoals_781_){
_start:
{
lean_object* v___x_782_; 
v___x_782_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_782_, 0, v_frame_778_);
lean_ctor_set(v___x_782_, 1, v_residualPre_779_);
lean_ctor_set(v___x_782_, 2, v_splitVCProof_780_);
lean_ctor_set(v___x_782_, 3, v_subgoals_781_);
return v___x_782_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_instInhabitedFrameProcs___closed__0(void){
_start:
{
lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; 
v___x_783_ = lean_box(0);
v___x_784_ = lean_unsigned_to_nat(16u);
v___x_785_ = lean_mk_array(v___x_784_, v___x_783_);
return v___x_785_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_instInhabitedFrameProcs___closed__1(void){
_start:
{
lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; 
v___x_786_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_instInhabitedFrameProcs___closed__0, &l_Lean_Elab_Tactic_Do_Internal_instInhabitedFrameProcs___closed__0_once, _init_l_Lean_Elab_Tactic_Do_Internal_instInhabitedFrameProcs___closed__0);
v___x_787_ = lean_unsigned_to_nat(0u);
v___x_788_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_788_, 0, v___x_787_);
lean_ctor_set(v___x_788_, 1, v___x_786_);
return v___x_788_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_instInhabitedFrameProcs(void){
_start:
{
lean_object* v___x_789_; 
v___x_789_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_instInhabitedFrameProcs___closed__1, &l_Lean_Elab_Tactic_Do_Internal_instInhabitedFrameProcs___closed__1_once, _init_l_Lean_Elab_Tactic_Do_Internal_instInhabitedFrameProcs___closed__1);
return v___x_789_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcs_insert_spec__0_spec__0___redArg(lean_object* v_a_790_, lean_object* v_x_791_){
_start:
{
if (lean_obj_tag(v_x_791_) == 0)
{
uint8_t v___x_792_; 
v___x_792_ = 0;
return v___x_792_;
}
else
{
lean_object* v_key_793_; lean_object* v_tail_794_; uint8_t v___x_795_; 
v_key_793_ = lean_ctor_get(v_x_791_, 0);
v_tail_794_ = lean_ctor_get(v_x_791_, 2);
v___x_795_ = lean_name_eq(v_key_793_, v_a_790_);
if (v___x_795_ == 0)
{
v_x_791_ = v_tail_794_;
goto _start;
}
else
{
return v___x_795_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcs_insert_spec__0_spec__0___redArg___boxed(lean_object* v_a_797_, lean_object* v_x_798_){
_start:
{
uint8_t v_res_799_; lean_object* v_r_800_; 
v_res_799_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcs_insert_spec__0_spec__0___redArg(v_a_797_, v_x_798_);
lean_dec(v_x_798_);
lean_dec(v_a_797_);
v_r_800_ = lean_box(v_res_799_);
return v_r_800_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcs_insert_spec__0_spec__2___redArg(lean_object* v_a_801_, lean_object* v_b_802_, lean_object* v_x_803_){
_start:
{
if (lean_obj_tag(v_x_803_) == 0)
{
lean_dec(v_b_802_);
lean_dec(v_a_801_);
return v_x_803_;
}
else
{
lean_object* v_key_804_; lean_object* v_value_805_; lean_object* v_tail_806_; lean_object* v___x_808_; uint8_t v_isShared_809_; uint8_t v_isSharedCheck_818_; 
v_key_804_ = lean_ctor_get(v_x_803_, 0);
v_value_805_ = lean_ctor_get(v_x_803_, 1);
v_tail_806_ = lean_ctor_get(v_x_803_, 2);
v_isSharedCheck_818_ = !lean_is_exclusive(v_x_803_);
if (v_isSharedCheck_818_ == 0)
{
v___x_808_ = v_x_803_;
v_isShared_809_ = v_isSharedCheck_818_;
goto v_resetjp_807_;
}
else
{
lean_inc(v_tail_806_);
lean_inc(v_value_805_);
lean_inc(v_key_804_);
lean_dec(v_x_803_);
v___x_808_ = lean_box(0);
v_isShared_809_ = v_isSharedCheck_818_;
goto v_resetjp_807_;
}
v_resetjp_807_:
{
uint8_t v___x_810_; 
v___x_810_ = lean_name_eq(v_key_804_, v_a_801_);
if (v___x_810_ == 0)
{
lean_object* v___x_811_; lean_object* v___x_813_; 
v___x_811_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcs_insert_spec__0_spec__2___redArg(v_a_801_, v_b_802_, v_tail_806_);
if (v_isShared_809_ == 0)
{
lean_ctor_set(v___x_808_, 2, v___x_811_);
v___x_813_ = v___x_808_;
goto v_reusejp_812_;
}
else
{
lean_object* v_reuseFailAlloc_814_; 
v_reuseFailAlloc_814_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_814_, 0, v_key_804_);
lean_ctor_set(v_reuseFailAlloc_814_, 1, v_value_805_);
lean_ctor_set(v_reuseFailAlloc_814_, 2, v___x_811_);
v___x_813_ = v_reuseFailAlloc_814_;
goto v_reusejp_812_;
}
v_reusejp_812_:
{
return v___x_813_;
}
}
else
{
lean_object* v___x_816_; 
lean_dec(v_value_805_);
lean_dec(v_key_804_);
if (v_isShared_809_ == 0)
{
lean_ctor_set(v___x_808_, 1, v_b_802_);
lean_ctor_set(v___x_808_, 0, v_a_801_);
v___x_816_ = v___x_808_;
goto v_reusejp_815_;
}
else
{
lean_object* v_reuseFailAlloc_817_; 
v_reuseFailAlloc_817_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_817_, 0, v_a_801_);
lean_ctor_set(v_reuseFailAlloc_817_, 1, v_b_802_);
lean_ctor_set(v_reuseFailAlloc_817_, 2, v_tail_806_);
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
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcs_insert_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_819_, lean_object* v_x_820_){
_start:
{
if (lean_obj_tag(v_x_820_) == 0)
{
return v_x_819_;
}
else
{
lean_object* v_key_821_; lean_object* v_value_822_; lean_object* v_tail_823_; lean_object* v___x_825_; uint8_t v_isShared_826_; uint8_t v_isSharedCheck_849_; 
v_key_821_ = lean_ctor_get(v_x_820_, 0);
v_value_822_ = lean_ctor_get(v_x_820_, 1);
v_tail_823_ = lean_ctor_get(v_x_820_, 2);
v_isSharedCheck_849_ = !lean_is_exclusive(v_x_820_);
if (v_isSharedCheck_849_ == 0)
{
v___x_825_ = v_x_820_;
v_isShared_826_ = v_isSharedCheck_849_;
goto v_resetjp_824_;
}
else
{
lean_inc(v_tail_823_);
lean_inc(v_value_822_);
lean_inc(v_key_821_);
lean_dec(v_x_820_);
v___x_825_ = lean_box(0);
v_isShared_826_ = v_isSharedCheck_849_;
goto v_resetjp_824_;
}
v_resetjp_824_:
{
lean_object* v___x_827_; uint64_t v___y_829_; 
v___x_827_ = lean_array_get_size(v_x_819_);
if (lean_obj_tag(v_key_821_) == 0)
{
uint64_t v___x_847_; 
v___x_847_ = 1723ULL;
v___y_829_ = v___x_847_;
goto v___jp_828_;
}
else
{
uint64_t v_hash_848_; 
v_hash_848_ = lean_ctor_get_uint64(v_key_821_, sizeof(void*)*2);
v___y_829_ = v_hash_848_;
goto v___jp_828_;
}
v___jp_828_:
{
uint64_t v___x_830_; uint64_t v___x_831_; uint64_t v_fold_832_; uint64_t v___x_833_; uint64_t v___x_834_; uint64_t v___x_835_; size_t v___x_836_; size_t v___x_837_; size_t v___x_838_; size_t v___x_839_; size_t v___x_840_; lean_object* v___x_841_; lean_object* v___x_843_; 
v___x_830_ = 32ULL;
v___x_831_ = lean_uint64_shift_right(v___y_829_, v___x_830_);
v_fold_832_ = lean_uint64_xor(v___y_829_, v___x_831_);
v___x_833_ = 16ULL;
v___x_834_ = lean_uint64_shift_right(v_fold_832_, v___x_833_);
v___x_835_ = lean_uint64_xor(v_fold_832_, v___x_834_);
v___x_836_ = lean_uint64_to_usize(v___x_835_);
v___x_837_ = lean_usize_of_nat(v___x_827_);
v___x_838_ = ((size_t)1ULL);
v___x_839_ = lean_usize_sub(v___x_837_, v___x_838_);
v___x_840_ = lean_usize_land(v___x_836_, v___x_839_);
v___x_841_ = lean_array_uget_borrowed(v_x_819_, v___x_840_);
lean_inc(v___x_841_);
if (v_isShared_826_ == 0)
{
lean_ctor_set(v___x_825_, 2, v___x_841_);
v___x_843_ = v___x_825_;
goto v_reusejp_842_;
}
else
{
lean_object* v_reuseFailAlloc_846_; 
v_reuseFailAlloc_846_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_846_, 0, v_key_821_);
lean_ctor_set(v_reuseFailAlloc_846_, 1, v_value_822_);
lean_ctor_set(v_reuseFailAlloc_846_, 2, v___x_841_);
v___x_843_ = v_reuseFailAlloc_846_;
goto v_reusejp_842_;
}
v_reusejp_842_:
{
lean_object* v___x_844_; 
v___x_844_ = lean_array_uset(v_x_819_, v___x_840_, v___x_843_);
v_x_819_ = v___x_844_;
v_x_820_ = v_tail_823_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcs_insert_spec__0_spec__1_spec__2___redArg(lean_object* v_i_850_, lean_object* v_source_851_, lean_object* v_target_852_){
_start:
{
lean_object* v___x_853_; uint8_t v___x_854_; 
v___x_853_ = lean_array_get_size(v_source_851_);
v___x_854_ = lean_nat_dec_lt(v_i_850_, v___x_853_);
if (v___x_854_ == 0)
{
lean_dec_ref(v_source_851_);
lean_dec(v_i_850_);
return v_target_852_;
}
else
{
lean_object* v_es_855_; lean_object* v___x_856_; lean_object* v_source_857_; lean_object* v_target_858_; lean_object* v___x_859_; lean_object* v___x_860_; 
v_es_855_ = lean_array_fget(v_source_851_, v_i_850_);
v___x_856_ = lean_box(0);
v_source_857_ = lean_array_fset(v_source_851_, v_i_850_, v___x_856_);
v_target_858_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcs_insert_spec__0_spec__1_spec__2_spec__3___redArg(v_target_852_, v_es_855_);
v___x_859_ = lean_unsigned_to_nat(1u);
v___x_860_ = lean_nat_add(v_i_850_, v___x_859_);
lean_dec(v_i_850_);
v_i_850_ = v___x_860_;
v_source_851_ = v_source_857_;
v_target_852_ = v_target_858_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcs_insert_spec__0_spec__1___redArg(lean_object* v_data_862_){
_start:
{
lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v_nbuckets_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; 
v___x_863_ = lean_array_get_size(v_data_862_);
v___x_864_ = lean_unsigned_to_nat(2u);
v_nbuckets_865_ = lean_nat_mul(v___x_863_, v___x_864_);
v___x_866_ = lean_unsigned_to_nat(0u);
v___x_867_ = lean_box(0);
v___x_868_ = lean_mk_array(v_nbuckets_865_, v___x_867_);
v___x_869_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcs_insert_spec__0_spec__1_spec__2___redArg(v___x_866_, v_data_862_, v___x_868_);
return v___x_869_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcs_insert_spec__0___redArg(lean_object* v_m_870_, lean_object* v_a_871_, lean_object* v_b_872_){
_start:
{
lean_object* v_size_873_; lean_object* v_buckets_874_; lean_object* v___x_876_; uint8_t v_isShared_877_; uint8_t v_isSharedCheck_920_; 
v_size_873_ = lean_ctor_get(v_m_870_, 0);
v_buckets_874_ = lean_ctor_get(v_m_870_, 1);
v_isSharedCheck_920_ = !lean_is_exclusive(v_m_870_);
if (v_isSharedCheck_920_ == 0)
{
v___x_876_ = v_m_870_;
v_isShared_877_ = v_isSharedCheck_920_;
goto v_resetjp_875_;
}
else
{
lean_inc(v_buckets_874_);
lean_inc(v_size_873_);
lean_dec(v_m_870_);
v___x_876_ = lean_box(0);
v_isShared_877_ = v_isSharedCheck_920_;
goto v_resetjp_875_;
}
v_resetjp_875_:
{
lean_object* v___x_878_; uint64_t v___y_880_; 
v___x_878_ = lean_array_get_size(v_buckets_874_);
if (lean_obj_tag(v_a_871_) == 0)
{
uint64_t v___x_918_; 
v___x_918_ = 1723ULL;
v___y_880_ = v___x_918_;
goto v___jp_879_;
}
else
{
uint64_t v_hash_919_; 
v_hash_919_ = lean_ctor_get_uint64(v_a_871_, sizeof(void*)*2);
v___y_880_ = v_hash_919_;
goto v___jp_879_;
}
v___jp_879_:
{
uint64_t v___x_881_; uint64_t v___x_882_; uint64_t v_fold_883_; uint64_t v___x_884_; uint64_t v___x_885_; uint64_t v___x_886_; size_t v___x_887_; size_t v___x_888_; size_t v___x_889_; size_t v___x_890_; size_t v___x_891_; lean_object* v_bkt_892_; uint8_t v___x_893_; 
v___x_881_ = 32ULL;
v___x_882_ = lean_uint64_shift_right(v___y_880_, v___x_881_);
v_fold_883_ = lean_uint64_xor(v___y_880_, v___x_882_);
v___x_884_ = 16ULL;
v___x_885_ = lean_uint64_shift_right(v_fold_883_, v___x_884_);
v___x_886_ = lean_uint64_xor(v_fold_883_, v___x_885_);
v___x_887_ = lean_uint64_to_usize(v___x_886_);
v___x_888_ = lean_usize_of_nat(v___x_878_);
v___x_889_ = ((size_t)1ULL);
v___x_890_ = lean_usize_sub(v___x_888_, v___x_889_);
v___x_891_ = lean_usize_land(v___x_887_, v___x_890_);
v_bkt_892_ = lean_array_uget_borrowed(v_buckets_874_, v___x_891_);
v___x_893_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcs_insert_spec__0_spec__0___redArg(v_a_871_, v_bkt_892_);
if (v___x_893_ == 0)
{
lean_object* v___x_894_; lean_object* v_size_x27_895_; lean_object* v___x_896_; lean_object* v_buckets_x27_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; uint8_t v___x_903_; 
v___x_894_ = lean_unsigned_to_nat(1u);
v_size_x27_895_ = lean_nat_add(v_size_873_, v___x_894_);
lean_dec(v_size_873_);
lean_inc(v_bkt_892_);
v___x_896_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_896_, 0, v_a_871_);
lean_ctor_set(v___x_896_, 1, v_b_872_);
lean_ctor_set(v___x_896_, 2, v_bkt_892_);
v_buckets_x27_897_ = lean_array_uset(v_buckets_874_, v___x_891_, v___x_896_);
v___x_898_ = lean_unsigned_to_nat(4u);
v___x_899_ = lean_nat_mul(v_size_x27_895_, v___x_898_);
v___x_900_ = lean_unsigned_to_nat(3u);
v___x_901_ = lean_nat_div(v___x_899_, v___x_900_);
lean_dec(v___x_899_);
v___x_902_ = lean_array_get_size(v_buckets_x27_897_);
v___x_903_ = lean_nat_dec_le(v___x_901_, v___x_902_);
lean_dec(v___x_901_);
if (v___x_903_ == 0)
{
lean_object* v_val_904_; lean_object* v___x_906_; 
v_val_904_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcs_insert_spec__0_spec__1___redArg(v_buckets_x27_897_);
if (v_isShared_877_ == 0)
{
lean_ctor_set(v___x_876_, 1, v_val_904_);
lean_ctor_set(v___x_876_, 0, v_size_x27_895_);
v___x_906_ = v___x_876_;
goto v_reusejp_905_;
}
else
{
lean_object* v_reuseFailAlloc_907_; 
v_reuseFailAlloc_907_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_907_, 0, v_size_x27_895_);
lean_ctor_set(v_reuseFailAlloc_907_, 1, v_val_904_);
v___x_906_ = v_reuseFailAlloc_907_;
goto v_reusejp_905_;
}
v_reusejp_905_:
{
return v___x_906_;
}
}
else
{
lean_object* v___x_909_; 
if (v_isShared_877_ == 0)
{
lean_ctor_set(v___x_876_, 1, v_buckets_x27_897_);
lean_ctor_set(v___x_876_, 0, v_size_x27_895_);
v___x_909_ = v___x_876_;
goto v_reusejp_908_;
}
else
{
lean_object* v_reuseFailAlloc_910_; 
v_reuseFailAlloc_910_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_910_, 0, v_size_x27_895_);
lean_ctor_set(v_reuseFailAlloc_910_, 1, v_buckets_x27_897_);
v___x_909_ = v_reuseFailAlloc_910_;
goto v_reusejp_908_;
}
v_reusejp_908_:
{
return v___x_909_;
}
}
}
else
{
lean_object* v___x_911_; lean_object* v_buckets_x27_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_916_; 
lean_inc(v_bkt_892_);
v___x_911_ = lean_box(0);
v_buckets_x27_912_ = lean_array_uset(v_buckets_874_, v___x_891_, v___x_911_);
v___x_913_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcs_insert_spec__0_spec__2___redArg(v_a_871_, v_b_872_, v_bkt_892_);
v___x_914_ = lean_array_uset(v_buckets_x27_912_, v___x_891_, v___x_913_);
if (v_isShared_877_ == 0)
{
lean_ctor_set(v___x_876_, 1, v___x_914_);
v___x_916_ = v___x_876_;
goto v_reusejp_915_;
}
else
{
lean_object* v_reuseFailAlloc_917_; 
v_reuseFailAlloc_917_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_917_, 0, v_size_873_);
lean_ctor_set(v_reuseFailAlloc_917_, 1, v___x_914_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcs_insert(lean_object* v_s_921_, lean_object* v_fp_922_){
_start:
{
lean_object* v_prog_923_; lean_object* v___x_924_; 
v_prog_923_ = lean_ctor_get(v_fp_922_, 0);
lean_inc(v_prog_923_);
v___x_924_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcs_insert_spec__0___redArg(v_s_921_, v_prog_923_, v_fp_922_);
return v___x_924_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcs_insert_spec__0(lean_object* v_00_u03b2_925_, lean_object* v_m_926_, lean_object* v_a_927_, lean_object* v_b_928_){
_start:
{
lean_object* v___x_929_; 
v___x_929_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcs_insert_spec__0___redArg(v_m_926_, v_a_927_, v_b_928_);
return v___x_929_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcs_insert_spec__0_spec__0(lean_object* v_00_u03b2_930_, lean_object* v_a_931_, lean_object* v_x_932_){
_start:
{
uint8_t v___x_933_; 
v___x_933_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcs_insert_spec__0_spec__0___redArg(v_a_931_, v_x_932_);
return v___x_933_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcs_insert_spec__0_spec__0___boxed(lean_object* v_00_u03b2_934_, lean_object* v_a_935_, lean_object* v_x_936_){
_start:
{
uint8_t v_res_937_; lean_object* v_r_938_; 
v_res_937_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcs_insert_spec__0_spec__0(v_00_u03b2_934_, v_a_935_, v_x_936_);
lean_dec(v_x_936_);
lean_dec(v_a_935_);
v_r_938_ = lean_box(v_res_937_);
return v_r_938_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcs_insert_spec__0_spec__1(lean_object* v_00_u03b2_939_, lean_object* v_data_940_){
_start:
{
lean_object* v___x_941_; 
v___x_941_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcs_insert_spec__0_spec__1___redArg(v_data_940_);
return v___x_941_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcs_insert_spec__0_spec__2(lean_object* v_00_u03b2_942_, lean_object* v_a_943_, lean_object* v_b_944_, lean_object* v_x_945_){
_start:
{
lean_object* v___x_946_; 
v___x_946_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcs_insert_spec__0_spec__2___redArg(v_a_943_, v_b_944_, v_x_945_);
return v___x_946_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcs_insert_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_947_, lean_object* v_i_948_, lean_object* v_source_949_, lean_object* v_target_950_){
_start:
{
lean_object* v___x_951_; 
v___x_951_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcs_insert_spec__0_spec__1_spec__2___redArg(v_i_948_, v_source_949_, v_target_950_);
return v___x_951_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcs_insert_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_952_, lean_object* v_x_953_, lean_object* v_x_954_){
_start:
{
lean_object* v___x_955_; 
v___x_955_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcs_insert_spec__0_spec__1_spec__2_spec__3___redArg(v_x_953_, v_x_954_);
return v___x_955_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_defaultFrameInferenceProc(lean_object* v_i_956_, lean_object* v_a_957_, lean_object* v_a_958_, lean_object* v_a_959_, lean_object* v_a_960_, lean_object* v_a_961_, lean_object* v_a_962_){
_start:
{
lean_object* v_providedFrame_x3f_964_; 
v_providedFrame_x3f_964_ = lean_ctor_get(v_i_956_, 2);
lean_inc(v_providedFrame_x3f_964_);
if (lean_obj_tag(v_providedFrame_x3f_964_) == 1)
{
lean_object* v_val_965_; lean_object* v___x_967_; uint8_t v_isShared_968_; uint8_t v_isSharedCheck_989_; 
v_val_965_ = lean_ctor_get(v_providedFrame_x3f_964_, 0);
v_isSharedCheck_989_ = !lean_is_exclusive(v_providedFrame_x3f_964_);
if (v_isSharedCheck_989_ == 0)
{
v___x_967_ = v_providedFrame_x3f_964_;
v_isShared_968_ = v_isSharedCheck_989_;
goto v_resetjp_966_;
}
else
{
lean_inc(v_val_965_);
lean_dec(v_providedFrame_x3f_964_);
v___x_967_ = lean_box(0);
v_isShared_968_ = v_isSharedCheck_989_;
goto v_resetjp_966_;
}
v_resetjp_966_:
{
lean_object* v___x_969_; 
v___x_969_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_FrameSplit_withDeferredSplitVC(v_i_956_, v_val_965_, v_a_957_, v_a_958_, v_a_959_, v_a_960_, v_a_961_, v_a_962_);
if (lean_obj_tag(v___x_969_) == 0)
{
lean_object* v_a_970_; lean_object* v___x_972_; uint8_t v_isShared_973_; uint8_t v_isSharedCheck_980_; 
v_a_970_ = lean_ctor_get(v___x_969_, 0);
v_isSharedCheck_980_ = !lean_is_exclusive(v___x_969_);
if (v_isSharedCheck_980_ == 0)
{
v___x_972_ = v___x_969_;
v_isShared_973_ = v_isSharedCheck_980_;
goto v_resetjp_971_;
}
else
{
lean_inc(v_a_970_);
lean_dec(v___x_969_);
v___x_972_ = lean_box(0);
v_isShared_973_ = v_isSharedCheck_980_;
goto v_resetjp_971_;
}
v_resetjp_971_:
{
lean_object* v___x_975_; 
if (v_isShared_968_ == 0)
{
lean_ctor_set(v___x_967_, 0, v_a_970_);
v___x_975_ = v___x_967_;
goto v_reusejp_974_;
}
else
{
lean_object* v_reuseFailAlloc_979_; 
v_reuseFailAlloc_979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_979_, 0, v_a_970_);
v___x_975_ = v_reuseFailAlloc_979_;
goto v_reusejp_974_;
}
v_reusejp_974_:
{
lean_object* v___x_977_; 
if (v_isShared_973_ == 0)
{
lean_ctor_set(v___x_972_, 0, v___x_975_);
v___x_977_ = v___x_972_;
goto v_reusejp_976_;
}
else
{
lean_object* v_reuseFailAlloc_978_; 
v_reuseFailAlloc_978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_978_, 0, v___x_975_);
v___x_977_ = v_reuseFailAlloc_978_;
goto v_reusejp_976_;
}
v_reusejp_976_:
{
return v___x_977_;
}
}
}
}
else
{
lean_object* v_a_981_; lean_object* v___x_983_; uint8_t v_isShared_984_; uint8_t v_isSharedCheck_988_; 
lean_del_object(v___x_967_);
v_a_981_ = lean_ctor_get(v___x_969_, 0);
v_isSharedCheck_988_ = !lean_is_exclusive(v___x_969_);
if (v_isSharedCheck_988_ == 0)
{
v___x_983_ = v___x_969_;
v_isShared_984_ = v_isSharedCheck_988_;
goto v_resetjp_982_;
}
else
{
lean_inc(v_a_981_);
lean_dec(v___x_969_);
v___x_983_ = lean_box(0);
v_isShared_984_ = v_isSharedCheck_988_;
goto v_resetjp_982_;
}
v_resetjp_982_:
{
lean_object* v___x_986_; 
if (v_isShared_984_ == 0)
{
v___x_986_ = v___x_983_;
goto v_reusejp_985_;
}
else
{
lean_object* v_reuseFailAlloc_987_; 
v_reuseFailAlloc_987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_987_, 0, v_a_981_);
v___x_986_ = v_reuseFailAlloc_987_;
goto v_reusejp_985_;
}
v_reusejp_985_:
{
return v___x_986_;
}
}
}
}
}
else
{
lean_object* v___x_990_; lean_object* v___x_991_; 
lean_dec(v_providedFrame_x3f_964_);
lean_dec_ref(v_i_956_);
v___x_990_ = lean_box(0);
v___x_991_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_991_, 0, v___x_990_);
return v___x_991_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_defaultFrameInferenceProc___boxed(lean_object* v_i_992_, lean_object* v_a_993_, lean_object* v_a_994_, lean_object* v_a_995_, lean_object* v_a_996_, lean_object* v_a_997_, lean_object* v_a_998_, lean_object* v_a_999_){
_start:
{
lean_object* v_res_1000_; 
v_res_1000_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_defaultFrameInferenceProc(v_i_992_, v_a_993_, v_a_994_, v_a_995_, v_a_996_, v_a_997_, v_a_998_);
lean_dec(v_a_998_);
lean_dec_ref(v_a_997_);
lean_dec(v_a_996_);
lean_dec_ref(v_a_995_);
lean_dec(v_a_994_);
lean_dec_ref(v_a_993_);
return v_res_1000_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProc_0__Lean_Elab_Tactic_Do_Internal_meetOp(lean_object* v_info_1006_, lean_object* v_a_1007_, lean_object* v_a_1008_, lean_object* v_a_1009_, lean_object* v_a_1010_){
_start:
{
lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; 
v___x_1012_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProc_0__Lean_Elab_Tactic_Do_Internal_meetOp___closed__1));
v___x_1013_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_WPApp_Pred(v_info_1006_);
v___x_1014_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1014_, 0, v___x_1013_);
v___x_1015_ = lean_box(0);
v___x_1016_ = lean_unsigned_to_nat(2u);
v___x_1017_ = lean_mk_empty_array_with_capacity(v___x_1016_);
v___x_1018_ = lean_array_push(v___x_1017_, v___x_1014_);
v___x_1019_ = lean_array_push(v___x_1018_, v___x_1015_);
v___x_1020_ = l_Lean_Meta_mkAppOptM(v___x_1012_, v___x_1019_, v_a_1007_, v_a_1008_, v_a_1009_, v_a_1010_);
return v___x_1020_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProc_0__Lean_Elab_Tactic_Do_Internal_meetOp___boxed(lean_object* v_info_1021_, lean_object* v_a_1022_, lean_object* v_a_1023_, lean_object* v_a_1024_, lean_object* v_a_1025_, lean_object* v_a_1026_){
_start:
{
lean_object* v_res_1027_; 
v_res_1027_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProc_0__Lean_Elab_Tactic_Do_Internal_meetOp(v_info_1021_, v_a_1022_, v_a_1023_, v_a_1024_, v_a_1025_);
lean_dec(v_a_1025_);
lean_dec_ref(v_a_1024_);
lean_dec(v_a_1023_);
lean_dec_ref(v_a_1022_);
lean_dec_ref(v_info_1021_);
return v_res_1027_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_meetFrameProc___lam__0(lean_object* v_info_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_){
_start:
{
lean_object* v___x_1034_; lean_object* v___x_1035_; 
v___x_1034_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_WPApp_Pred(v_info_1028_);
v___x_1035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1035_, 0, v___x_1034_);
return v___x_1035_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_meetFrameProc___lam__0___boxed(lean_object* v_info_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_){
_start:
{
lean_object* v_res_1042_; 
v_res_1042_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_meetFrameProc___lam__0(v_info_1036_, v___y_1037_, v___y_1038_, v___y_1039_, v___y_1040_);
lean_dec(v___y_1040_);
lean_dec_ref(v___y_1039_);
lean_dec(v___y_1038_);
lean_dec_ref(v___y_1037_);
lean_dec_ref(v_info_1036_);
return v_res_1042_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_meetFrameProc___closed__2(void){
_start:
{
lean_object* v___x_1045_; lean_object* v___f_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; 
v___x_1045_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_defaultFrameInferenceProc___boxed), 8, 0);
v___f_1046_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_meetFrameProc___closed__0));
v___x_1047_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_meetFrameProc___closed__1));
v___x_1048_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProc_0__Lean_Elab_Tactic_Do_Internal_meetOp___closed__1));
v___x_1049_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1049_, 0, v___x_1048_);
lean_ctor_set(v___x_1049_, 1, v___x_1048_);
lean_ctor_set(v___x_1049_, 2, v___x_1047_);
lean_ctor_set(v___x_1049_, 3, v___f_1046_);
lean_ctor_set(v___x_1049_, 4, v___x_1045_);
return v___x_1049_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_meetFrameProc(void){
_start:
{
lean_object* v___x_1050_; 
v___x_1050_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_meetFrameProc___closed__2, &l_Lean_Elab_Tactic_Do_Internal_VCGen_meetFrameProc___closed__2_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_meetFrameProc___closed__2);
return v___x_1050_;
}
}
lean_object* runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_WPApp(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Apply(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_AlphaShareBuilder(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_Do_Order_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_AppBuilder(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_AbstractMVars(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_InferType(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_InstantiateMVarsS(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Util(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProc(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_WPApp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Apply(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_AlphaShareBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_Do_Order_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_AppBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_AbstractMVars(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_InferType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_InstantiateMVarsS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Tactic_Do_Internal_instInhabitedFrameProcs = _init_l_Lean_Elab_Tactic_Do_Internal_instInhabitedFrameProcs();
lean_mark_persistent(l_Lean_Elab_Tactic_Do_Internal_instInhabitedFrameProcs);
l_Lean_Elab_Tactic_Do_Internal_VCGen_meetFrameProc = _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_meetFrameProc();
lean_mark_persistent(l_Lean_Elab_Tactic_Do_Internal_VCGen_meetFrameProc);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProc(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Tactic_Do_Internal_VCGen_WPApp(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Apply(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_AlphaShareBuilder(uint8_t builtin);
lean_object* initialize_Std_Internal_Do_Order_Basic(uint8_t builtin);
lean_object* initialize_Lean_Meta_AppBuilder(uint8_t builtin);
lean_object* initialize_Lean_Meta_AbstractMVars(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_InferType(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_InstantiateMVarsS(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Util(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProc(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Tactic_Do_Internal_VCGen_WPApp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Apply(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_AlphaShareBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal_Do_Order_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_AppBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_AbstractMVars(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_InferType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_InstantiateMVarsS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProc(builtin);
}
#ifdef __cplusplus
}
#endif
