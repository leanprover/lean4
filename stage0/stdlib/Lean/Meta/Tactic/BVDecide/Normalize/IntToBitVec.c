// Lean compiler output
// Module: Lean.Meta.Tactic.BVDecide.Normalize.IntToBitVec
// Imports: public import Lean.Meta.Tactic.BVDecide.Normalize.Basic import Lean.Meta.Sym.Simp.Rewrite import Lean.Meta.Sym.InstantiateMVarsS import Lean.Meta.Sym.LitValues import Init.Data.UInt.IntToBitVec import Init.Data.SInt.IntToBitVec
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
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Target_mvarId(lean_object*);
extern lean_object* l_Lean_Meta_Tactic_BVDecide_symIntToBitVecExt;
lean_object* l_Lean_Meta_Sym_Simp_SymSimpExtension_getTheorems___redArg(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getNatValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_instantiateMVarsS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_getNatValue_x3f(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_dischargeNone___redArg();
lean_object* l_Lean_Meta_Sym_Simp_Theorems_rewrite(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_BitVec_ofNat(lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommonInc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_Result_withContextDependent(lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_mkEqTrans(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_instBEqFVarId_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_instHashableFVarId_hash___boxed(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Expr_eqv___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_hash___boxed(lean_object*);
static const lean_closure_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeTerm___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Expr_eqv___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeTerm___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeTerm___redArg___closed__0_value;
static const lean_closure_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeTerm___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Expr_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeTerm___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeTerm___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeTerm___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeTerm___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeTerm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeTerm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeHyp___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqFVarId_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeHyp___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeHyp___redArg___closed__0_value;
static const lean_closure_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeHyp___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instHashableFVarId_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeHyp___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeHyp___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeHyp___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeHyp___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeHyp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeHyp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc_runProc___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "BitVec"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc_runProc___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc_runProc___redArg___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc_runProc___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ofNat"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc_runProc___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc_runProc___redArg___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc_runProc___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc_runProc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc_runProc___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc_runProc___redArg___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc_runProc___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(101, 105, 192, 171, 214, 131, 43, 105)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc_runProc___redArg___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc_runProc___redArg___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc_runProc___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc_runProc___redArg___closed__3;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc_runProc___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc_runProc___redArg___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc_runProc___redArg___closed__4_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc_runProc___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc_runProc___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc_runProc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc_runProc___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Int64"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "toBitVec"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(67, 100, 38, 50, 157, 43, 83, 90)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(42, 26, 57, 165, 14, 135, 135, 191)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Int32"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__3_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(202, 24, 245, 188, 10, 96, 206, 241)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(231, 54, 185, 195, 30, 183, 107, 8)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__4_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Int16"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__5_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(61, 121, 89, 120, 57, 100, 28, 22)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(44, 210, 78, 221, 232, 52, 28, 161)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__6_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Int8"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__7_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(17, 171, 155, 218, 43, 77, 1, 67)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(144, 114, 73, 21, 161, 185, 192, 185)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__8_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UInt64"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__9_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__9_value),LEAN_SCALAR_PTR_LITERAL(58, 113, 45, 150, 103, 228, 0, 41)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__10_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(151, 144, 45, 221, 65, 48, 204, 242)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__10_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UInt32"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__11_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__11_value),LEAN_SCALAR_PTR_LITERAL(98, 192, 58, 241, 186, 14, 255, 186)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__12_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(95, 106, 42, 185, 61, 138, 17, 12)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__12 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__12_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UInt16"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__13 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__13_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__13_value),LEAN_SCALAR_PTR_LITERAL(6, 214, 154, 233, 192, 74, 99, 135)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__14_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(83, 21, 175, 117, 0, 32, 88, 5)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__14 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__14_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "UInt8"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__15 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__15_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__15_value),LEAN_SCALAR_PTR_LITERAL(144, 254, 64, 72, 7, 99, 197, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__16_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(165, 247, 174, 117, 226, 108, 136, 114)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__16 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__16_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ISize"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__17 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__17_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "toBitVec64"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__18 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__18_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__19_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__17_value),LEAN_SCALAR_PTR_LITERAL(110, 52, 237, 35, 121, 142, 86, 222)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__19_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__18_value),LEAN_SCALAR_PTR_LITERAL(51, 79, 88, 119, 92, 132, 69, 104)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__19 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__19_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "toBitVec32"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__20 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__20_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__21_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__17_value),LEAN_SCALAR_PTR_LITERAL(110, 52, 237, 35, 121, 142, 86, 222)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__21_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__20_value),LEAN_SCALAR_PTR_LITERAL(40, 3, 162, 24, 208, 1, 22, 97)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__21 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__21_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "USize"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__22 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__22_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__23_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__22_value),LEAN_SCALAR_PTR_LITERAL(109, 217, 26, 131, 232, 198, 207, 245)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__23_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__18_value),LEAN_SCALAR_PTR_LITERAL(116, 153, 59, 255, 117, 164, 81, 124)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__23 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__23_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__24_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__22_value),LEAN_SCALAR_PTR_LITERAL(109, 217, 26, 131, 232, 198, 207, 245)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__24_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__20_value),LEAN_SCALAR_PTR_LITERAL(231, 120, 16, 185, 133, 236, 22, 98)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__24 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__24_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "toBitVec32_ofNat"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__25 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__25_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__26_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__22_value),LEAN_SCALAR_PTR_LITERAL(109, 217, 26, 131, 232, 198, 207, 245)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__26_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__25_value),LEAN_SCALAR_PTR_LITERAL(36, 126, 106, 153, 203, 80, 154, 147)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__26 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__26_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__27;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "toBitVec64_ofNat"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__28 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__28_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__29_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__22_value),LEAN_SCALAR_PTR_LITERAL(109, 217, 26, 131, 232, 198, 207, 245)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__29_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__28_value),LEAN_SCALAR_PTR_LITERAL(8, 122, 79, 170, 199, 9, 205, 227)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__29 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__29_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__30;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__31_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__17_value),LEAN_SCALAR_PTR_LITERAL(110, 52, 237, 35, 121, 142, 86, 222)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__31_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__25_value),LEAN_SCALAR_PTR_LITERAL(227, 67, 19, 212, 150, 152, 220, 31)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__31 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__31_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__32_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__32;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__33_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__17_value),LEAN_SCALAR_PTR_LITERAL(110, 52, 237, 35, 121, 142, 86, 222)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__33_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__28_value),LEAN_SCALAR_PTR_LITERAL(199, 133, 200, 107, 224, 56, 254, 62)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__33 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__33_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__34_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__34;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "toBitVec_ofNat"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__35 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__35_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__36_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__15_value),LEAN_SCALAR_PTR_LITERAL(144, 254, 64, 72, 7, 99, 197, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__36_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__35_value),LEAN_SCALAR_PTR_LITERAL(247, 230, 213, 135, 10, 17, 158, 228)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__36 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__36_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__37_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__37;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__38_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__13_value),LEAN_SCALAR_PTR_LITERAL(6, 214, 154, 233, 192, 74, 99, 135)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__38_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__35_value),LEAN_SCALAR_PTR_LITERAL(81, 243, 247, 74, 243, 200, 60, 150)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__38 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__38_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__39_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__39;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__40_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__11_value),LEAN_SCALAR_PTR_LITERAL(98, 192, 58, 241, 186, 14, 255, 186)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__40_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__35_value),LEAN_SCALAR_PTR_LITERAL(93, 148, 255, 227, 8, 20, 120, 82)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__40 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__40_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__41_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__41;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__42_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__9_value),LEAN_SCALAR_PTR_LITERAL(58, 113, 45, 150, 103, 228, 0, 41)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__42_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__35_value),LEAN_SCALAR_PTR_LITERAL(69, 129, 9, 3, 239, 75, 70, 86)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__42 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__42_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__43_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__43;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__44_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(17, 171, 155, 218, 43, 77, 1, 67)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__44_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__35_value),LEAN_SCALAR_PTR_LITERAL(226, 22, 215, 85, 74, 102, 124, 27)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__44 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__44_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__45_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__45;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__46_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(61, 121, 89, 120, 57, 100, 28, 22)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__46_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__35_value),LEAN_SCALAR_PTR_LITERAL(46, 105, 154, 220, 47, 238, 251, 60)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__46 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__46_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__47_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__47;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__48_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(202, 24, 245, 188, 10, 96, 206, 241)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__48_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__35_value),LEAN_SCALAR_PTR_LITERAL(149, 18, 246, 1, 255, 137, 120, 221)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__48 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__48_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__49_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__49;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__50_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(67, 100, 38, 50, 157, 43, 83, 90)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__50_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__35_value),LEAN_SCALAR_PTR_LITERAL(40, 68, 102, 45, 83, 225, 185, 90)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__50 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__50_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__51_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__51;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_addIntToBitVecLemmas_findNumBitsEq_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_addIntToBitVecLemmas_findNumBitsEq_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_addIntToBitVecLemmas_findNumBitsEq_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_addIntToBitVecLemmas_findNumBitsEq_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_addIntToBitVecLemmas_findNumBitsEq_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_addIntToBitVecLemmas_findNumBitsEq_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_addIntToBitVecLemmas_findNumBitsEq_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_addIntToBitVecLemmas_findNumBitsEq_spec__0___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_addIntToBitVecLemmas_findNumBitsEq_spec__0___redArg___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_addIntToBitVecLemmas_findNumBitsEq_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_addIntToBitVecLemmas_findNumBitsEq_spec__0___redArg___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_addIntToBitVecLemmas_findNumBitsEq_spec__0___redArg___closed__1_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_addIntToBitVecLemmas_findNumBitsEq_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_addIntToBitVecLemmas_findNumBitsEq_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_addIntToBitVecLemmas_findNumBitsEq_spec__0___redArg___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_addIntToBitVecLemmas_findNumBitsEq_spec__0___redArg___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_addIntToBitVecLemmas_findNumBitsEq_spec__0___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "System"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_addIntToBitVecLemmas_findNumBitsEq_spec__0___redArg___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_addIntToBitVecLemmas_findNumBitsEq_spec__0___redArg___closed__3_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_addIntToBitVecLemmas_findNumBitsEq_spec__0___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Platform"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_addIntToBitVecLemmas_findNumBitsEq_spec__0___redArg___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_addIntToBitVecLemmas_findNumBitsEq_spec__0___redArg___closed__4_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_addIntToBitVecLemmas_findNumBitsEq_spec__0___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "numBits"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_addIntToBitVecLemmas_findNumBitsEq_spec__0___redArg___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_addIntToBitVecLemmas_findNumBitsEq_spec__0___redArg___closed__5_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_addIntToBitVecLemmas_findNumBitsEq_spec__0___redArg___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_addIntToBitVecLemmas_findNumBitsEq_spec__0___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(244, 7, 92, 194, 164, 177, 167, 52)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_addIntToBitVecLemmas_findNumBitsEq_spec__0___redArg___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_addIntToBitVecLemmas_findNumBitsEq_spec__0___redArg___closed__6_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_addIntToBitVecLemmas_findNumBitsEq_spec__0___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(128, 236, 129, 7, 244, 3, 115, 42)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_addIntToBitVecLemmas_findNumBitsEq_spec__0___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_addIntToBitVecLemmas_findNumBitsEq_spec__0___redArg___closed__6_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_addIntToBitVecLemmas_findNumBitsEq_spec__0___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(195, 13, 33, 186, 170, 198, 65, 128)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_addIntToBitVecLemmas_findNumBitsEq_spec__0___redArg___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_addIntToBitVecLemmas_findNumBitsEq_spec__0___redArg___closed__6_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_addIntToBitVecLemmas_findNumBitsEq_spec__0___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "symm"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_addIntToBitVecLemmas_findNumBitsEq_spec__0___redArg___closed__7 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_addIntToBitVecLemmas_findNumBitsEq_spec__0___redArg___closed__7_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_addIntToBitVecLemmas_findNumBitsEq_spec__0___redArg___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_addIntToBitVecLemmas_findNumBitsEq_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_addIntToBitVecLemmas_findNumBitsEq_spec__0___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_addIntToBitVecLemmas_findNumBitsEq_spec__0___redArg___closed__8_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_addIntToBitVecLemmas_findNumBitsEq_spec__0___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(220, 149, 144, 59, 77, 93, 25, 217)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_addIntToBitVecLemmas_findNumBitsEq_spec__0___redArg___closed__8 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_addIntToBitVecLemmas_findNumBitsEq_spec__0___redArg___closed__8_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_addIntToBitVecLemmas_findNumBitsEq_spec__0___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_addIntToBitVecLemmas_findNumBitsEq_spec__0___redArg___closed__9;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_addIntToBitVecLemmas_findNumBitsEq_spec__0___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_addIntToBitVecLemmas_findNumBitsEq_spec__0___redArg___closed__10;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_addIntToBitVecLemmas_findNumBitsEq_spec__0___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_addIntToBitVecLemmas_findNumBitsEq_spec__0___redArg___closed__11;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_addIntToBitVecLemmas_findNumBitsEq_spec__0___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_addIntToBitVecLemmas_findNumBitsEq_spec__0___redArg___closed__12 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_addIntToBitVecLemmas_findNumBitsEq_spec__0___redArg___closed__12_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_addIntToBitVecLemmas_findNumBitsEq_spec__0___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_addIntToBitVecLemmas_findNumBitsEq_spec__0___redArg___closed__12_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_addIntToBitVecLemmas_findNumBitsEq_spec__0___redArg___closed__13 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_addIntToBitVecLemmas_findNumBitsEq_spec__0___redArg___closed__13_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_addIntToBitVecLemmas_findNumBitsEq_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_addIntToBitVecLemmas_findNumBitsEq_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_addIntToBitVecLemmas_findNumBitsEq___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_addIntToBitVecLemmas_findNumBitsEq___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_addIntToBitVecLemmas_findNumBitsEq___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_addIntToBitVecLemmas_findNumBitsEq___lam__0___boxed, .m_arity = 12, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_addIntToBitVecLemmas_findNumBitsEq___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_addIntToBitVecLemmas_findNumBitsEq___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_addIntToBitVecLemmas_findNumBitsEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_addIntToBitVecLemmas_findNumBitsEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_addIntToBitVecLemmas_findNumBitsEq_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_addIntToBitVecLemmas_findNumBitsEq_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_addIntToBitVecLemmas___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_addIntToBitVecLemmas___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_addIntToBitVecLemmas___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_addIntToBitVecLemmas___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_addIntToBitVecLemmas___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_addIntToBitVecLemmas___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_addIntToBitVecLemmas___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_addIntToBitVecLemmas___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_addIntToBitVecLemmas___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_addIntToBitVecLemmas(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_addIntToBitVecLemmas___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___boxed, .m_arity = 11, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___closed__0_value;
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__1___boxed, .m_arity = 13, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___closed__0_value)} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___closed__1_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "intToBitVec"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___closed__2_value),LEAN_SCALAR_PTR_LITERAL(130, 217, 71, 86, 75, 235, 18, 78)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___closed__3 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___closed__3_value),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___closed__1_value)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___closed__4 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___closed__4_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___closed__4_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeTerm___redArg(lean_object* v_e_3_, lean_object* v_a_4_){
_start:
{
lean_object* v___x_6_; lean_object* v_relevantTerms_7_; lean_object* v_relevantHyps_8_; lean_object* v___x_10_; uint8_t v_isShared_11_; uint8_t v_isSharedCheck_21_; 
v___x_6_ = lean_st_ref_take(v_a_4_);
v_relevantTerms_7_ = lean_ctor_get(v___x_6_, 0);
v_relevantHyps_8_ = lean_ctor_get(v___x_6_, 1);
v_isSharedCheck_21_ = !lean_is_exclusive(v___x_6_);
if (v_isSharedCheck_21_ == 0)
{
v___x_10_ = v___x_6_;
v_isShared_11_ = v_isSharedCheck_21_;
goto v_resetjp_9_;
}
else
{
lean_inc(v_relevantHyps_8_);
lean_inc(v_relevantTerms_7_);
lean_dec(v___x_6_);
v___x_10_ = lean_box(0);
v_isShared_11_ = v_isSharedCheck_21_;
goto v_resetjp_9_;
}
v_resetjp_9_:
{
lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v___x_17_; 
v___x_12_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeTerm___redArg___closed__0));
v___x_13_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeTerm___redArg___closed__1));
v___x_14_ = lean_box(0);
v___x_15_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___x_12_, v___x_13_, v_relevantTerms_7_, v_e_3_, v___x_14_);
if (v_isShared_11_ == 0)
{
lean_ctor_set(v___x_10_, 0, v___x_15_);
v___x_17_ = v___x_10_;
goto v_reusejp_16_;
}
else
{
lean_object* v_reuseFailAlloc_20_; 
v_reuseFailAlloc_20_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_20_, 0, v___x_15_);
lean_ctor_set(v_reuseFailAlloc_20_, 1, v_relevantHyps_8_);
v___x_17_ = v_reuseFailAlloc_20_;
goto v_reusejp_16_;
}
v_reusejp_16_:
{
lean_object* v___x_18_; lean_object* v___x_19_; 
v___x_18_ = lean_st_ref_set(v_a_4_, v___x_17_);
v___x_19_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_19_, 0, v___x_14_);
return v___x_19_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeTerm___redArg___boxed(lean_object* v_e_22_, lean_object* v_a_23_, lean_object* v_a_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeTerm___redArg(v_e_22_, v_a_23_);
lean_dec(v_a_23_);
return v_res_25_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeTerm(lean_object* v_e_26_, lean_object* v_a_27_, lean_object* v_a_28_, lean_object* v_a_29_, lean_object* v_a_30_, lean_object* v_a_31_){
_start:
{
lean_object* v___x_33_; lean_object* v_relevantTerms_34_; lean_object* v_relevantHyps_35_; lean_object* v___x_37_; uint8_t v_isShared_38_; uint8_t v_isSharedCheck_48_; 
v___x_33_ = lean_st_ref_take(v_a_27_);
v_relevantTerms_34_ = lean_ctor_get(v___x_33_, 0);
v_relevantHyps_35_ = lean_ctor_get(v___x_33_, 1);
v_isSharedCheck_48_ = !lean_is_exclusive(v___x_33_);
if (v_isSharedCheck_48_ == 0)
{
v___x_37_ = v___x_33_;
v_isShared_38_ = v_isSharedCheck_48_;
goto v_resetjp_36_;
}
else
{
lean_inc(v_relevantHyps_35_);
lean_inc(v_relevantTerms_34_);
lean_dec(v___x_33_);
v___x_37_ = lean_box(0);
v_isShared_38_ = v_isSharedCheck_48_;
goto v_resetjp_36_;
}
v_resetjp_36_:
{
lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_44_; 
v___x_39_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeTerm___redArg___closed__0));
v___x_40_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeTerm___redArg___closed__1));
v___x_41_ = lean_box(0);
v___x_42_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___x_39_, v___x_40_, v_relevantTerms_34_, v_e_26_, v___x_41_);
if (v_isShared_38_ == 0)
{
lean_ctor_set(v___x_37_, 0, v___x_42_);
v___x_44_ = v___x_37_;
goto v_reusejp_43_;
}
else
{
lean_object* v_reuseFailAlloc_47_; 
v_reuseFailAlloc_47_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_47_, 0, v___x_42_);
lean_ctor_set(v_reuseFailAlloc_47_, 1, v_relevantHyps_35_);
v___x_44_ = v_reuseFailAlloc_47_;
goto v_reusejp_43_;
}
v_reusejp_43_:
{
lean_object* v___x_45_; lean_object* v___x_46_; 
v___x_45_ = lean_st_ref_set(v_a_27_, v___x_44_);
v___x_46_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_46_, 0, v___x_41_);
return v___x_46_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeTerm___boxed(lean_object* v_e_49_, lean_object* v_a_50_, lean_object* v_a_51_, lean_object* v_a_52_, lean_object* v_a_53_, lean_object* v_a_54_, lean_object* v_a_55_){
_start:
{
lean_object* v_res_56_; 
v_res_56_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeTerm(v_e_49_, v_a_50_, v_a_51_, v_a_52_, v_a_53_, v_a_54_);
lean_dec(v_a_54_);
lean_dec_ref(v_a_53_);
lean_dec(v_a_52_);
lean_dec_ref(v_a_51_);
lean_dec(v_a_50_);
return v_res_56_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeHyp___redArg(lean_object* v_f_59_, lean_object* v_a_60_){
_start:
{
lean_object* v___x_62_; lean_object* v_relevantTerms_63_; lean_object* v_relevantHyps_64_; lean_object* v___x_66_; uint8_t v_isShared_67_; uint8_t v_isSharedCheck_77_; 
v___x_62_ = lean_st_ref_take(v_a_60_);
v_relevantTerms_63_ = lean_ctor_get(v___x_62_, 0);
v_relevantHyps_64_ = lean_ctor_get(v___x_62_, 1);
v_isSharedCheck_77_ = !lean_is_exclusive(v___x_62_);
if (v_isSharedCheck_77_ == 0)
{
v___x_66_ = v___x_62_;
v_isShared_67_ = v_isSharedCheck_77_;
goto v_resetjp_65_;
}
else
{
lean_inc(v_relevantHyps_64_);
lean_inc(v_relevantTerms_63_);
lean_dec(v___x_62_);
v___x_66_ = lean_box(0);
v_isShared_67_ = v_isSharedCheck_77_;
goto v_resetjp_65_;
}
v_resetjp_65_:
{
lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_73_; 
v___x_68_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeHyp___redArg___closed__0));
v___x_69_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeHyp___redArg___closed__1));
v___x_70_ = lean_box(0);
v___x_71_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___x_68_, v___x_69_, v_relevantHyps_64_, v_f_59_, v___x_70_);
if (v_isShared_67_ == 0)
{
lean_ctor_set(v___x_66_, 1, v___x_71_);
v___x_73_ = v___x_66_;
goto v_reusejp_72_;
}
else
{
lean_object* v_reuseFailAlloc_76_; 
v_reuseFailAlloc_76_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_76_, 0, v_relevantTerms_63_);
lean_ctor_set(v_reuseFailAlloc_76_, 1, v___x_71_);
v___x_73_ = v_reuseFailAlloc_76_;
goto v_reusejp_72_;
}
v_reusejp_72_:
{
lean_object* v___x_74_; lean_object* v___x_75_; 
v___x_74_ = lean_st_ref_set(v_a_60_, v___x_73_);
v___x_75_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_75_, 0, v___x_70_);
return v___x_75_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeHyp___redArg___boxed(lean_object* v_f_78_, lean_object* v_a_79_, lean_object* v_a_80_){
_start:
{
lean_object* v_res_81_; 
v_res_81_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeHyp___redArg(v_f_78_, v_a_79_);
lean_dec(v_a_79_);
return v_res_81_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeHyp(lean_object* v_f_82_, lean_object* v_a_83_, lean_object* v_a_84_, lean_object* v_a_85_, lean_object* v_a_86_, lean_object* v_a_87_){
_start:
{
lean_object* v___x_89_; lean_object* v_relevantTerms_90_; lean_object* v_relevantHyps_91_; lean_object* v___x_93_; uint8_t v_isShared_94_; uint8_t v_isSharedCheck_104_; 
v___x_89_ = lean_st_ref_take(v_a_83_);
v_relevantTerms_90_ = lean_ctor_get(v___x_89_, 0);
v_relevantHyps_91_ = lean_ctor_get(v___x_89_, 1);
v_isSharedCheck_104_ = !lean_is_exclusive(v___x_89_);
if (v_isSharedCheck_104_ == 0)
{
v___x_93_ = v___x_89_;
v_isShared_94_ = v_isSharedCheck_104_;
goto v_resetjp_92_;
}
else
{
lean_inc(v_relevantHyps_91_);
lean_inc(v_relevantTerms_90_);
lean_dec(v___x_89_);
v___x_93_ = lean_box(0);
v_isShared_94_ = v_isSharedCheck_104_;
goto v_resetjp_92_;
}
v_resetjp_92_:
{
lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_100_; 
v___x_95_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeHyp___redArg___closed__0));
v___x_96_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeHyp___redArg___closed__1));
v___x_97_ = lean_box(0);
v___x_98_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___x_95_, v___x_96_, v_relevantHyps_91_, v_f_82_, v___x_97_);
if (v_isShared_94_ == 0)
{
lean_ctor_set(v___x_93_, 1, v___x_98_);
v___x_100_ = v___x_93_;
goto v_reusejp_99_;
}
else
{
lean_object* v_reuseFailAlloc_103_; 
v_reuseFailAlloc_103_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_103_, 0, v_relevantTerms_90_);
lean_ctor_set(v_reuseFailAlloc_103_, 1, v___x_98_);
v___x_100_ = v_reuseFailAlloc_103_;
goto v_reusejp_99_;
}
v_reusejp_99_:
{
lean_object* v___x_101_; lean_object* v___x_102_; 
v___x_101_ = lean_st_ref_set(v_a_83_, v___x_100_);
v___x_102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_102_, 0, v___x_97_);
return v___x_102_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeHyp___boxed(lean_object* v_f_105_, lean_object* v_a_106_, lean_object* v_a_107_, lean_object* v_a_108_, lean_object* v_a_109_, lean_object* v_a_110_, lean_object* v_a_111_){
_start:
{
lean_object* v_res_112_; 
v_res_112_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeHyp(v_f_105_, v_a_106_, v_a_107_, v_a_108_, v_a_109_, v_a_110_);
lean_dec(v_a_110_);
lean_dec_ref(v_a_109_);
lean_dec(v_a_108_);
lean_dec_ref(v_a_107_);
lean_dec(v_a_106_);
return v_res_112_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc_runProc___redArg___closed__3(void){
_start:
{
lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; 
v___x_118_ = lean_box(0);
v___x_119_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc_runProc___redArg___closed__2));
v___x_120_ = l_Lean_Expr_const___override(v___x_119_, v___x_118_);
return v___x_120_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc_runProc___redArg(lean_object* v_expr_123_, lean_object* v_width_124_, lean_object* v_thm_125_, lean_object* v_a_126_, lean_object* v_a_127_, lean_object* v_a_128_, lean_object* v_a_129_, lean_object* v_a_130_, lean_object* v_a_131_){
_start:
{
lean_object* v___x_133_; 
v___x_133_ = l_Lean_Meta_Sym_getNatValue_x3f(v_expr_123_);
if (lean_obj_tag(v___x_133_) == 1)
{
lean_object* v_val_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; 
v_val_134_ = lean_ctor_get(v___x_133_, 0);
lean_inc(v_val_134_);
lean_dec_ref_known(v___x_133_, 1);
v___x_135_ = l_BitVec_ofNat(v_width_124_, v_val_134_);
v___x_136_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc_runProc___redArg___closed__3, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc_runProc___redArg___closed__3_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc_runProc___redArg___closed__3);
v___x_137_ = l_Lean_mkNatLit(v_width_124_);
v___x_138_ = l_Lean_mkNatLit(v___x_135_);
v___x_139_ = l_Lean_mkAppB(v___x_136_, v___x_137_, v___x_138_);
v___x_140_ = l_Lean_Meta_Sym_shareCommonInc(v___x_139_, v_a_126_, v_a_127_, v_a_128_, v_a_129_, v_a_130_, v_a_131_);
if (lean_obj_tag(v___x_140_) == 0)
{
lean_object* v_a_141_; lean_object* v___x_143_; uint8_t v_isShared_144_; uint8_t v_isSharedCheck_152_; 
v_a_141_ = lean_ctor_get(v___x_140_, 0);
v_isSharedCheck_152_ = !lean_is_exclusive(v___x_140_);
if (v_isSharedCheck_152_ == 0)
{
v___x_143_ = v___x_140_;
v_isShared_144_ = v_isSharedCheck_152_;
goto v_resetjp_142_;
}
else
{
lean_inc(v_a_141_);
lean_dec(v___x_140_);
v___x_143_ = lean_box(0);
v_isShared_144_ = v_isSharedCheck_152_;
goto v_resetjp_142_;
}
v_resetjp_142_:
{
lean_object* v___x_145_; lean_object* v___x_146_; uint8_t v___x_147_; lean_object* v___x_148_; lean_object* v___x_150_; 
v___x_145_ = l_Lean_mkNatLit(v_val_134_);
v___x_146_ = l_Lean_Expr_app___override(v_thm_125_, v___x_145_);
v___x_147_ = 0;
v___x_148_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_148_, 0, v_a_141_);
lean_ctor_set(v___x_148_, 1, v___x_146_);
lean_ctor_set_uint8(v___x_148_, sizeof(void*)*2, v___x_147_);
lean_ctor_set_uint8(v___x_148_, sizeof(void*)*2 + 1, v___x_147_);
if (v_isShared_144_ == 0)
{
lean_ctor_set(v___x_143_, 0, v___x_148_);
v___x_150_ = v___x_143_;
goto v_reusejp_149_;
}
else
{
lean_object* v_reuseFailAlloc_151_; 
v_reuseFailAlloc_151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_151_, 0, v___x_148_);
v___x_150_ = v_reuseFailAlloc_151_;
goto v_reusejp_149_;
}
v_reusejp_149_:
{
return v___x_150_;
}
}
}
else
{
lean_object* v_a_153_; lean_object* v___x_155_; uint8_t v_isShared_156_; uint8_t v_isSharedCheck_160_; 
lean_dec(v_val_134_);
lean_dec_ref(v_thm_125_);
v_a_153_ = lean_ctor_get(v___x_140_, 0);
v_isSharedCheck_160_ = !lean_is_exclusive(v___x_140_);
if (v_isSharedCheck_160_ == 0)
{
v___x_155_ = v___x_140_;
v_isShared_156_ = v_isSharedCheck_160_;
goto v_resetjp_154_;
}
else
{
lean_inc(v_a_153_);
lean_dec(v___x_140_);
v___x_155_ = lean_box(0);
v_isShared_156_ = v_isSharedCheck_160_;
goto v_resetjp_154_;
}
v_resetjp_154_:
{
lean_object* v___x_158_; 
if (v_isShared_156_ == 0)
{
v___x_158_ = v___x_155_;
goto v_reusejp_157_;
}
else
{
lean_object* v_reuseFailAlloc_159_; 
v_reuseFailAlloc_159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_159_, 0, v_a_153_);
v___x_158_ = v_reuseFailAlloc_159_;
goto v_reusejp_157_;
}
v_reusejp_157_:
{
return v___x_158_;
}
}
}
}
else
{
lean_object* v___x_161_; lean_object* v___x_162_; 
lean_dec(v___x_133_);
lean_dec_ref(v_thm_125_);
lean_dec(v_width_124_);
v___x_161_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc_runProc___redArg___closed__4));
v___x_162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_162_, 0, v___x_161_);
return v___x_162_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc_runProc___redArg___boxed(lean_object* v_expr_163_, lean_object* v_width_164_, lean_object* v_thm_165_, lean_object* v_a_166_, lean_object* v_a_167_, lean_object* v_a_168_, lean_object* v_a_169_, lean_object* v_a_170_, lean_object* v_a_171_, lean_object* v_a_172_){
_start:
{
lean_object* v_res_173_; 
v_res_173_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc_runProc___redArg(v_expr_163_, v_width_164_, v_thm_165_, v_a_166_, v_a_167_, v_a_168_, v_a_169_, v_a_170_, v_a_171_);
lean_dec(v_a_171_);
lean_dec_ref(v_a_170_);
lean_dec(v_a_169_);
lean_dec_ref(v_a_168_);
lean_dec(v_a_167_);
lean_dec_ref(v_a_166_);
return v_res_173_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc_runProc(lean_object* v_expr_174_, lean_object* v_width_175_, lean_object* v_thm_176_, lean_object* v_a_177_, lean_object* v_a_178_, lean_object* v_a_179_, lean_object* v_a_180_, lean_object* v_a_181_, lean_object* v_a_182_, lean_object* v_a_183_, lean_object* v_a_184_, lean_object* v_a_185_){
_start:
{
lean_object* v___x_187_; 
v___x_187_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc_runProc___redArg(v_expr_174_, v_width_175_, v_thm_176_, v_a_180_, v_a_181_, v_a_182_, v_a_183_, v_a_184_, v_a_185_);
return v___x_187_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc_runProc___boxed(lean_object* v_expr_188_, lean_object* v_width_189_, lean_object* v_thm_190_, lean_object* v_a_191_, lean_object* v_a_192_, lean_object* v_a_193_, lean_object* v_a_194_, lean_object* v_a_195_, lean_object* v_a_196_, lean_object* v_a_197_, lean_object* v_a_198_, lean_object* v_a_199_, lean_object* v_a_200_){
_start:
{
lean_object* v_res_201_; 
v_res_201_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc_runProc(v_expr_188_, v_width_189_, v_thm_190_, v_a_191_, v_a_192_, v_a_193_, v_a_194_, v_a_195_, v_a_196_, v_a_197_, v_a_198_, v_a_199_);
lean_dec(v_a_199_);
lean_dec_ref(v_a_198_);
lean_dec(v_a_197_);
lean_dec_ref(v_a_196_);
lean_dec(v_a_195_);
lean_dec_ref(v_a_194_);
lean_dec(v_a_193_);
lean_dec_ref(v_a_192_);
lean_dec(v_a_191_);
return v_res_201_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__27(void){
_start:
{
lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; 
v___x_255_ = lean_box(0);
v___x_256_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__26));
v___x_257_ = l_Lean_mkConst(v___x_256_, v___x_255_);
return v___x_257_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__30(void){
_start:
{
lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; 
v___x_262_ = lean_box(0);
v___x_263_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__29));
v___x_264_ = l_Lean_mkConst(v___x_263_, v___x_262_);
return v___x_264_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__32(void){
_start:
{
lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; 
v___x_268_ = lean_box(0);
v___x_269_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__31));
v___x_270_ = l_Lean_mkConst(v___x_269_, v___x_268_);
return v___x_270_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__34(void){
_start:
{
lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; 
v___x_274_ = lean_box(0);
v___x_275_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__33));
v___x_276_ = l_Lean_mkConst(v___x_275_, v___x_274_);
return v___x_276_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__37(void){
_start:
{
lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; 
v___x_281_ = lean_box(0);
v___x_282_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__36));
v___x_283_ = l_Lean_mkConst(v___x_282_, v___x_281_);
return v___x_283_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__39(void){
_start:
{
lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; 
v___x_287_ = lean_box(0);
v___x_288_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__38));
v___x_289_ = l_Lean_mkConst(v___x_288_, v___x_287_);
return v___x_289_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__41(void){
_start:
{
lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; 
v___x_293_ = lean_box(0);
v___x_294_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__40));
v___x_295_ = l_Lean_mkConst(v___x_294_, v___x_293_);
return v___x_295_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__43(void){
_start:
{
lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; 
v___x_299_ = lean_box(0);
v___x_300_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__42));
v___x_301_ = l_Lean_mkConst(v___x_300_, v___x_299_);
return v___x_301_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__45(void){
_start:
{
lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; 
v___x_305_ = lean_box(0);
v___x_306_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__44));
v___x_307_ = l_Lean_mkConst(v___x_306_, v___x_305_);
return v___x_307_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__47(void){
_start:
{
lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; 
v___x_311_ = lean_box(0);
v___x_312_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__46));
v___x_313_ = l_Lean_mkConst(v___x_312_, v___x_311_);
return v___x_313_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__49(void){
_start:
{
lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; 
v___x_317_ = lean_box(0);
v___x_318_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__48));
v___x_319_ = l_Lean_mkConst(v___x_318_, v___x_317_);
return v___x_319_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__51(void){
_start:
{
lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; 
v___x_323_ = lean_box(0);
v___x_324_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__50));
v___x_325_ = l_Lean_mkConst(v___x_324_, v___x_323_);
return v___x_325_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg(lean_object* v_e_326_, lean_object* v_a_327_, lean_object* v_a_328_, lean_object* v_a_329_, lean_object* v_a_330_, lean_object* v_a_331_, lean_object* v_a_332_){
_start:
{
lean_object* v___x_334_; 
v___x_334_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_326_, v_a_330_);
if (lean_obj_tag(v___x_334_) == 0)
{
lean_object* v_a_335_; lean_object* v___x_337_; uint8_t v_isShared_338_; uint8_t v_isSharedCheck_415_; 
v_a_335_ = lean_ctor_get(v___x_334_, 0);
v_isSharedCheck_415_ = !lean_is_exclusive(v___x_334_);
if (v_isSharedCheck_415_ == 0)
{
v___x_337_ = v___x_334_;
v_isShared_338_ = v_isSharedCheck_415_;
goto v_resetjp_336_;
}
else
{
lean_inc(v_a_335_);
lean_dec(v___x_334_);
v___x_337_ = lean_box(0);
v_isShared_338_ = v_isSharedCheck_415_;
goto v_resetjp_336_;
}
v_resetjp_336_:
{
lean_object* v___x_344_; uint8_t v___x_345_; 
v___x_344_ = l_Lean_Expr_cleanupAnnotations(v_a_335_);
v___x_345_ = l_Lean_Expr_isApp(v___x_344_);
if (v___x_345_ == 0)
{
lean_dec_ref(v___x_344_);
goto v___jp_339_;
}
else
{
lean_object* v_arg_346_; lean_object* v___x_347_; lean_object* v___x_348_; uint8_t v___x_349_; 
v_arg_346_ = lean_ctor_get(v___x_344_, 1);
lean_inc_ref(v_arg_346_);
v___x_347_ = l_Lean_Expr_appFnCleanup___redArg(v___x_344_);
v___x_348_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__2));
v___x_349_ = l_Lean_Expr_isConstOf(v___x_347_, v___x_348_);
if (v___x_349_ == 0)
{
lean_object* v___x_350_; uint8_t v___x_351_; 
v___x_350_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__4));
v___x_351_ = l_Lean_Expr_isConstOf(v___x_347_, v___x_350_);
if (v___x_351_ == 0)
{
lean_object* v___x_352_; uint8_t v___x_353_; 
v___x_352_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__6));
v___x_353_ = l_Lean_Expr_isConstOf(v___x_347_, v___x_352_);
if (v___x_353_ == 0)
{
lean_object* v___x_354_; uint8_t v___x_355_; 
v___x_354_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__8));
v___x_355_ = l_Lean_Expr_isConstOf(v___x_347_, v___x_354_);
if (v___x_355_ == 0)
{
lean_object* v___x_356_; uint8_t v___x_357_; 
v___x_356_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__10));
v___x_357_ = l_Lean_Expr_isConstOf(v___x_347_, v___x_356_);
if (v___x_357_ == 0)
{
lean_object* v___x_358_; uint8_t v___x_359_; 
v___x_358_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__12));
v___x_359_ = l_Lean_Expr_isConstOf(v___x_347_, v___x_358_);
if (v___x_359_ == 0)
{
lean_object* v___x_360_; uint8_t v___x_361_; 
v___x_360_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__14));
v___x_361_ = l_Lean_Expr_isConstOf(v___x_347_, v___x_360_);
if (v___x_361_ == 0)
{
lean_object* v___x_362_; uint8_t v___x_363_; 
v___x_362_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__16));
v___x_363_ = l_Lean_Expr_isConstOf(v___x_347_, v___x_362_);
if (v___x_363_ == 0)
{
uint8_t v___x_364_; 
v___x_364_ = l_Lean_Expr_isApp(v___x_347_);
if (v___x_364_ == 0)
{
lean_dec_ref(v___x_347_);
lean_dec_ref(v_arg_346_);
goto v___jp_339_;
}
else
{
lean_object* v_arg_365_; lean_object* v___x_366_; lean_object* v___x_367_; uint8_t v___x_368_; 
v_arg_365_ = lean_ctor_get(v___x_347_, 1);
lean_inc_ref(v_arg_365_);
v___x_366_ = l_Lean_Expr_appFnCleanup___redArg(v___x_347_);
v___x_367_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__19));
v___x_368_ = l_Lean_Expr_isConstOf(v___x_366_, v___x_367_);
if (v___x_368_ == 0)
{
lean_object* v___x_369_; uint8_t v___x_370_; 
v___x_369_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__21));
v___x_370_ = l_Lean_Expr_isConstOf(v___x_366_, v___x_369_);
if (v___x_370_ == 0)
{
lean_object* v___x_371_; uint8_t v___x_372_; 
v___x_371_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__23));
v___x_372_ = l_Lean_Expr_isConstOf(v___x_366_, v___x_371_);
if (v___x_372_ == 0)
{
lean_object* v___x_373_; uint8_t v___x_374_; 
v___x_373_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__24));
v___x_374_ = l_Lean_Expr_isConstOf(v___x_366_, v___x_373_);
lean_dec_ref(v___x_366_);
if (v___x_374_ == 0)
{
lean_dec_ref(v_arg_365_);
lean_dec_ref(v_arg_346_);
goto v___jp_339_;
}
else
{
lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; 
lean_del_object(v___x_337_);
v___x_375_ = lean_unsigned_to_nat(32u);
v___x_376_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__27, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__27_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__27);
v___x_377_ = l_Lean_Expr_app___override(v___x_376_, v_arg_346_);
v___x_378_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc_runProc___redArg(v_arg_365_, v___x_375_, v___x_377_, v_a_327_, v_a_328_, v_a_329_, v_a_330_, v_a_331_, v_a_332_);
return v___x_378_;
}
}
else
{
lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; 
lean_dec_ref(v___x_366_);
lean_del_object(v___x_337_);
v___x_379_ = lean_unsigned_to_nat(64u);
v___x_380_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__30, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__30_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__30);
v___x_381_ = l_Lean_Expr_app___override(v___x_380_, v_arg_346_);
v___x_382_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc_runProc___redArg(v_arg_365_, v___x_379_, v___x_381_, v_a_327_, v_a_328_, v_a_329_, v_a_330_, v_a_331_, v_a_332_);
return v___x_382_;
}
}
else
{
lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; 
lean_dec_ref(v___x_366_);
lean_del_object(v___x_337_);
v___x_383_ = lean_unsigned_to_nat(32u);
v___x_384_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__32, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__32_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__32);
v___x_385_ = l_Lean_Expr_app___override(v___x_384_, v_arg_346_);
v___x_386_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc_runProc___redArg(v_arg_365_, v___x_383_, v___x_385_, v_a_327_, v_a_328_, v_a_329_, v_a_330_, v_a_331_, v_a_332_);
return v___x_386_;
}
}
else
{
lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; 
lean_dec_ref(v___x_366_);
lean_del_object(v___x_337_);
v___x_387_ = lean_unsigned_to_nat(64u);
v___x_388_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__34, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__34_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__34);
v___x_389_ = l_Lean_Expr_app___override(v___x_388_, v_arg_346_);
v___x_390_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc_runProc___redArg(v_arg_365_, v___x_387_, v___x_389_, v_a_327_, v_a_328_, v_a_329_, v_a_330_, v_a_331_, v_a_332_);
return v___x_390_;
}
}
}
else
{
lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; 
lean_dec_ref(v___x_347_);
lean_del_object(v___x_337_);
v___x_391_ = lean_unsigned_to_nat(8u);
v___x_392_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__37, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__37_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__37);
v___x_393_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc_runProc___redArg(v_arg_346_, v___x_391_, v___x_392_, v_a_327_, v_a_328_, v_a_329_, v_a_330_, v_a_331_, v_a_332_);
return v___x_393_;
}
}
else
{
lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; 
lean_dec_ref(v___x_347_);
lean_del_object(v___x_337_);
v___x_394_ = lean_unsigned_to_nat(16u);
v___x_395_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__39, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__39_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__39);
v___x_396_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc_runProc___redArg(v_arg_346_, v___x_394_, v___x_395_, v_a_327_, v_a_328_, v_a_329_, v_a_330_, v_a_331_, v_a_332_);
return v___x_396_;
}
}
else
{
lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; 
lean_dec_ref(v___x_347_);
lean_del_object(v___x_337_);
v___x_397_ = lean_unsigned_to_nat(32u);
v___x_398_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__41, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__41_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__41);
v___x_399_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc_runProc___redArg(v_arg_346_, v___x_397_, v___x_398_, v_a_327_, v_a_328_, v_a_329_, v_a_330_, v_a_331_, v_a_332_);
return v___x_399_;
}
}
else
{
lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; 
lean_dec_ref(v___x_347_);
lean_del_object(v___x_337_);
v___x_400_ = lean_unsigned_to_nat(64u);
v___x_401_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__43, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__43_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__43);
v___x_402_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc_runProc___redArg(v_arg_346_, v___x_400_, v___x_401_, v_a_327_, v_a_328_, v_a_329_, v_a_330_, v_a_331_, v_a_332_);
return v___x_402_;
}
}
else
{
lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; 
lean_dec_ref(v___x_347_);
lean_del_object(v___x_337_);
v___x_403_ = lean_unsigned_to_nat(8u);
v___x_404_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__45, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__45_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__45);
v___x_405_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc_runProc___redArg(v_arg_346_, v___x_403_, v___x_404_, v_a_327_, v_a_328_, v_a_329_, v_a_330_, v_a_331_, v_a_332_);
return v___x_405_;
}
}
else
{
lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; 
lean_dec_ref(v___x_347_);
lean_del_object(v___x_337_);
v___x_406_ = lean_unsigned_to_nat(16u);
v___x_407_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__47, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__47_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__47);
v___x_408_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc_runProc___redArg(v_arg_346_, v___x_406_, v___x_407_, v_a_327_, v_a_328_, v_a_329_, v_a_330_, v_a_331_, v_a_332_);
return v___x_408_;
}
}
else
{
lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; 
lean_dec_ref(v___x_347_);
lean_del_object(v___x_337_);
v___x_409_ = lean_unsigned_to_nat(32u);
v___x_410_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__49, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__49_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__49);
v___x_411_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc_runProc___redArg(v_arg_346_, v___x_409_, v___x_410_, v_a_327_, v_a_328_, v_a_329_, v_a_330_, v_a_331_, v_a_332_);
return v___x_411_;
}
}
else
{
lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; 
lean_dec_ref(v___x_347_);
lean_del_object(v___x_337_);
v___x_412_ = lean_unsigned_to_nat(64u);
v___x_413_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__51, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__51_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___closed__51);
v___x_414_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc_runProc___redArg(v_arg_346_, v___x_412_, v___x_413_, v_a_327_, v_a_328_, v_a_329_, v_a_330_, v_a_331_, v_a_332_);
return v___x_414_;
}
}
v___jp_339_:
{
lean_object* v___x_340_; lean_object* v___x_342_; 
v___x_340_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc_runProc___redArg___closed__4));
if (v_isShared_338_ == 0)
{
lean_ctor_set(v___x_337_, 0, v___x_340_);
v___x_342_ = v___x_337_;
goto v_reusejp_341_;
}
else
{
lean_object* v_reuseFailAlloc_343_; 
v_reuseFailAlloc_343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_343_, 0, v___x_340_);
v___x_342_ = v_reuseFailAlloc_343_;
goto v_reusejp_341_;
}
v_reusejp_341_:
{
return v___x_342_;
}
}
}
}
else
{
lean_object* v_a_416_; lean_object* v___x_418_; uint8_t v_isShared_419_; uint8_t v_isSharedCheck_423_; 
v_a_416_ = lean_ctor_get(v___x_334_, 0);
v_isSharedCheck_423_ = !lean_is_exclusive(v___x_334_);
if (v_isSharedCheck_423_ == 0)
{
v___x_418_ = v___x_334_;
v_isShared_419_ = v_isSharedCheck_423_;
goto v_resetjp_417_;
}
else
{
lean_inc(v_a_416_);
lean_dec(v___x_334_);
v___x_418_ = lean_box(0);
v_isShared_419_ = v_isSharedCheck_423_;
goto v_resetjp_417_;
}
v_resetjp_417_:
{
lean_object* v___x_421_; 
if (v_isShared_419_ == 0)
{
v___x_421_ = v___x_418_;
goto v_reusejp_420_;
}
else
{
lean_object* v_reuseFailAlloc_422_; 
v_reuseFailAlloc_422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_422_, 0, v_a_416_);
v___x_421_ = v_reuseFailAlloc_422_;
goto v_reusejp_420_;
}
v_reusejp_420_:
{
return v___x_421_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg___boxed(lean_object* v_e_424_, lean_object* v_a_425_, lean_object* v_a_426_, lean_object* v_a_427_, lean_object* v_a_428_, lean_object* v_a_429_, lean_object* v_a_430_, lean_object* v_a_431_){
_start:
{
lean_object* v_res_432_; 
v_res_432_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg(v_e_424_, v_a_425_, v_a_426_, v_a_427_, v_a_428_, v_a_429_, v_a_430_);
lean_dec(v_a_430_);
lean_dec_ref(v_a_429_);
lean_dec(v_a_428_);
lean_dec_ref(v_a_427_);
lean_dec(v_a_426_);
lean_dec_ref(v_a_425_);
return v_res_432_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc(lean_object* v_e_433_, lean_object* v_a_434_, lean_object* v_a_435_, lean_object* v_a_436_, lean_object* v_a_437_, lean_object* v_a_438_, lean_object* v_a_439_, lean_object* v_a_440_, lean_object* v_a_441_, lean_object* v_a_442_){
_start:
{
lean_object* v___x_444_; 
v___x_444_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg(v_e_433_, v_a_437_, v_a_438_, v_a_439_, v_a_440_, v_a_441_, v_a_442_);
return v___x_444_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___boxed(lean_object* v_e_445_, lean_object* v_a_446_, lean_object* v_a_447_, lean_object* v_a_448_, lean_object* v_a_449_, lean_object* v_a_450_, lean_object* v_a_451_, lean_object* v_a_452_, lean_object* v_a_453_, lean_object* v_a_454_, lean_object* v_a_455_){
_start:
{
lean_object* v_res_456_; 
v_res_456_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc(v_e_445_, v_a_446_, v_a_447_, v_a_448_, v_a_449_, v_a_450_, v_a_451_, v_a_452_, v_a_453_, v_a_454_);
lean_dec(v_a_454_);
lean_dec_ref(v_a_453_);
lean_dec(v_a_452_);
lean_dec_ref(v_a_451_);
lean_dec(v_a_450_);
lean_dec_ref(v_a_449_);
lean_dec(v_a_448_);
lean_dec_ref(v_a_447_);
lean_dec(v_a_446_);
return v_res_456_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_addIntToBitVecLemmas_findNumBitsEq_spec__1___redArg___lam__0(lean_object* v_x_457_, lean_object* v___y_458_, lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v___y_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_){
_start:
{
lean_object* v___x_470_; 
lean_inc(v___y_464_);
lean_inc_ref(v___y_463_);
lean_inc(v___y_462_);
lean_inc_ref(v___y_461_);
lean_inc(v___y_460_);
lean_inc(v___y_459_);
lean_inc_ref(v___y_458_);
v___x_470_ = lean_apply_12(v_x_457_, v___y_458_, v___y_459_, v___y_460_, v___y_461_, v___y_462_, v___y_463_, v___y_464_, v___y_465_, v___y_466_, v___y_467_, v___y_468_, lean_box(0));
return v___x_470_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_addIntToBitVecLemmas_findNumBitsEq_spec__1___redArg___lam__0___boxed(lean_object* v_x_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_){
_start:
{
lean_object* v_res_484_; 
v_res_484_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_addIntToBitVecLemmas_findNumBitsEq_spec__1___redArg___lam__0(v_x_471_, v___y_472_, v___y_473_, v___y_474_, v___y_475_, v___y_476_, v___y_477_, v___y_478_, v___y_479_, v___y_480_, v___y_481_, v___y_482_);
lean_dec(v___y_478_);
lean_dec_ref(v___y_477_);
lean_dec(v___y_476_);
lean_dec_ref(v___y_475_);
lean_dec(v___y_474_);
lean_dec(v___y_473_);
lean_dec_ref(v___y_472_);
return v_res_484_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_addIntToBitVecLemmas_findNumBitsEq_spec__1___redArg(lean_object* v_mvarId_485_, lean_object* v_x_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_){
_start:
{
lean_object* v___f_499_; lean_object* v___x_500_; 
lean_inc(v___y_493_);
lean_inc_ref(v___y_492_);
lean_inc(v___y_491_);
lean_inc_ref(v___y_490_);
lean_inc(v___y_489_);
lean_inc(v___y_488_);
lean_inc_ref(v___y_487_);
v___f_499_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_addIntToBitVecLemmas_findNumBitsEq_spec__1___redArg___lam__0___boxed), 13, 8);
lean_closure_set(v___f_499_, 0, v_x_486_);
lean_closure_set(v___f_499_, 1, v___y_487_);
lean_closure_set(v___f_499_, 2, v___y_488_);
lean_closure_set(v___f_499_, 3, v___y_489_);
lean_closure_set(v___f_499_, 4, v___y_490_);
lean_closure_set(v___f_499_, 5, v___y_491_);
lean_closure_set(v___f_499_, 6, v___y_492_);
lean_closure_set(v___f_499_, 7, v___y_493_);
v___x_500_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_485_, v___f_499_, v___y_494_, v___y_495_, v___y_496_, v___y_497_);
if (lean_obj_tag(v___x_500_) == 0)
{
return v___x_500_;
}
else
{
lean_object* v_a_501_; lean_object* v___x_503_; uint8_t v_isShared_504_; uint8_t v_isSharedCheck_508_; 
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
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_addIntToBitVecLemmas_findNumBitsEq_spec__1___redArg___boxed(lean_object* v_mvarId_509_, lean_object* v_x_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_){
_start:
{
lean_object* v_res_523_; 
v_res_523_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_addIntToBitVecLemmas_findNumBitsEq_spec__1___redArg(v_mvarId_509_, v_x_510_, v___y_511_, v___y_512_, v___y_513_, v___y_514_, v___y_515_, v___y_516_, v___y_517_, v___y_518_, v___y_519_, v___y_520_, v___y_521_);
lean_dec(v___y_521_);
lean_dec_ref(v___y_520_);
lean_dec(v___y_519_);
lean_dec_ref(v___y_518_);
lean_dec(v___y_517_);
lean_dec_ref(v___y_516_);
lean_dec(v___y_515_);
lean_dec_ref(v___y_514_);
lean_dec(v___y_513_);
lean_dec(v___y_512_);
lean_dec_ref(v___y_511_);
return v_res_523_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_addIntToBitVecLemmas_findNumBitsEq_spec__1(lean_object* v_00_u03b1_524_, lean_object* v_mvarId_525_, lean_object* v_x_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_){
_start:
{
lean_object* v___x_539_; 
v___x_539_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_addIntToBitVecLemmas_findNumBitsEq_spec__1___redArg(v_mvarId_525_, v_x_526_, v___y_527_, v___y_528_, v___y_529_, v___y_530_, v___y_531_, v___y_532_, v___y_533_, v___y_534_, v___y_535_, v___y_536_, v___y_537_);
return v___x_539_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_addIntToBitVecLemmas_findNumBitsEq_spec__1___boxed(lean_object* v_00_u03b1_540_, lean_object* v_mvarId_541_, lean_object* v_x_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_){
_start:
{
lean_object* v_res_555_; 
v_res_555_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_addIntToBitVecLemmas_findNumBitsEq_spec__1(v_00_u03b1_540_, v_mvarId_541_, v_x_542_, v___y_543_, v___y_544_, v___y_545_, v___y_546_, v___y_547_, v___y_548_, v___y_549_, v___y_550_, v___y_551_, v___y_552_, v___y_553_);
lean_dec(v___y_553_);
lean_dec_ref(v___y_552_);
lean_dec(v___y_551_);
lean_dec_ref(v___y_550_);
lean_dec(v___y_549_);
lean_dec_ref(v___y_548_);
lean_dec(v___y_547_);
lean_dec_ref(v___y_546_);
lean_dec(v___y_545_);
lean_dec(v___y_544_);
lean_dec_ref(v___y_543_);
return v_res_555_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_addIntToBitVecLemmas_findNumBitsEq_spec__0___redArg___closed__9(void){
_start:
{
lean_object* v___x_573_; lean_object* v___x_574_; 
v___x_573_ = lean_unsigned_to_nat(1u);
v___x_574_ = l_Lean_Level_ofNat(v___x_573_);
return v___x_574_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_addIntToBitVecLemmas_findNumBitsEq_spec__0___redArg___closed__10(void){
_start:
{
lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; 
v___x_575_ = lean_box(0);
v___x_576_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_addIntToBitVecLemmas_findNumBitsEq_spec__0___redArg___closed__9, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_addIntToBitVecLemmas_findNumBitsEq_spec__0___redArg___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_addIntToBitVecLemmas_findNumBitsEq_spec__0___redArg___closed__9);
v___x_577_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_577_, 0, v___x_576_);
lean_ctor_set(v___x_577_, 1, v___x_575_);
return v___x_577_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_addIntToBitVecLemmas_findNumBitsEq_spec__0___redArg___closed__11(void){
_start:
{
lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; 
v___x_578_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_addIntToBitVecLemmas_findNumBitsEq_spec__0___redArg___closed__10, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_addIntToBitVecLemmas_findNumBitsEq_spec__0___redArg___closed__10_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_addIntToBitVecLemmas_findNumBitsEq_spec__0___redArg___closed__10);
v___x_579_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_addIntToBitVecLemmas_findNumBitsEq_spec__0___redArg___closed__8));
v___x_580_ = l_Lean_mkConst(v___x_579_, v___x_578_);
return v___x_580_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_addIntToBitVecLemmas_findNumBitsEq_spec__0___redArg(lean_object* v_as_586_, size_t v_sz_587_, size_t v_i_588_, lean_object* v_b_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_){
_start:
{
uint8_t v___x_595_; 
v___x_595_ = lean_usize_dec_lt(v_i_588_, v_sz_587_);
if (v___x_595_ == 0)
{
lean_object* v___x_596_; 
v___x_596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_596_, 0, v_b_589_);
return v___x_596_;
}
else
{
lean_object* v_a_597_; lean_object* v_type_598_; lean_object* v_value_599_; lean_object* v___x_600_; 
lean_dec_ref(v_b_589_);
v_a_597_ = lean_array_uget_borrowed(v_as_586_, v_i_588_);
v_type_598_ = lean_ctor_get(v_a_597_, 1);
v_value_599_ = lean_ctor_get(v_a_597_, 2);
lean_inc_ref(v_type_598_);
v___x_600_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_type_598_, v___y_591_);
if (lean_obj_tag(v___x_600_) == 0)
{
lean_object* v_a_601_; lean_object* v_a_603_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; uint8_t v___x_610_; 
v_a_601_ = lean_ctor_get(v___x_600_, 0);
lean_inc(v_a_601_);
lean_dec_ref_known(v___x_600_, 1);
v___x_607_ = lean_box(0);
v___x_608_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_addIntToBitVecLemmas_findNumBitsEq_spec__0___redArg___closed__0));
v___x_609_ = l_Lean_Expr_cleanupAnnotations(v_a_601_);
v___x_610_ = l_Lean_Expr_isApp(v___x_609_);
if (v___x_610_ == 0)
{
lean_dec_ref(v___x_609_);
v_a_603_ = v___x_608_;
goto v___jp_602_;
}
else
{
lean_object* v_arg_611_; lean_object* v___x_612_; uint8_t v___x_613_; 
v_arg_611_ = lean_ctor_get(v___x_609_, 1);
lean_inc_ref(v_arg_611_);
v___x_612_ = l_Lean_Expr_appFnCleanup___redArg(v___x_609_);
v___x_613_ = l_Lean_Expr_isApp(v___x_612_);
if (v___x_613_ == 0)
{
lean_dec_ref(v___x_612_);
lean_dec_ref(v_arg_611_);
v_a_603_ = v___x_608_;
goto v___jp_602_;
}
else
{
lean_object* v_arg_614_; lean_object* v___x_615_; uint8_t v___x_616_; 
v_arg_614_ = lean_ctor_get(v___x_612_, 1);
lean_inc_ref(v_arg_614_);
v___x_615_ = l_Lean_Expr_appFnCleanup___redArg(v___x_612_);
v___x_616_ = l_Lean_Expr_isApp(v___x_615_);
if (v___x_616_ == 0)
{
lean_dec_ref(v___x_615_);
lean_dec_ref(v_arg_614_);
lean_dec_ref(v_arg_611_);
v_a_603_ = v___x_608_;
goto v___jp_602_;
}
else
{
lean_object* v_arg_617_; lean_object* v___x_618_; lean_object* v___x_619_; uint8_t v___x_620_; 
v_arg_617_ = lean_ctor_get(v___x_615_, 1);
lean_inc_ref(v_arg_617_);
v___x_618_ = l_Lean_Expr_appFnCleanup___redArg(v___x_615_);
v___x_619_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_addIntToBitVecLemmas_findNumBitsEq_spec__0___redArg___closed__2));
v___x_620_ = l_Lean_Expr_isConstOf(v___x_618_, v___x_619_);
lean_dec_ref(v___x_618_);
if (v___x_620_ == 0)
{
lean_dec_ref(v_arg_617_);
lean_dec_ref(v_arg_614_);
lean_dec_ref(v_arg_611_);
v_a_603_ = v___x_608_;
goto v___jp_602_;
}
else
{
lean_object* v___x_621_; uint8_t v___x_622_; 
v___x_621_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_addIntToBitVecLemmas_findNumBitsEq_spec__0___redArg___closed__6));
v___x_622_ = l_Lean_Expr_isConstOf(v_arg_614_, v___x_621_);
if (v___x_622_ == 0)
{
uint8_t v___x_623_; 
v___x_623_ = l_Lean_Expr_isConstOf(v_arg_611_, v___x_621_);
if (v___x_623_ == 0)
{
lean_dec_ref(v_arg_617_);
lean_dec_ref(v_arg_614_);
lean_dec_ref(v_arg_611_);
v_a_603_ = v___x_608_;
goto v___jp_602_;
}
else
{
lean_object* v___x_624_; 
v___x_624_ = l_Lean_Meta_getNatValue_x3f(v_arg_614_, v___y_590_, v___y_591_, v___y_592_, v___y_593_);
if (lean_obj_tag(v___x_624_) == 0)
{
lean_object* v_a_625_; lean_object* v___x_627_; uint8_t v_isShared_628_; uint8_t v_isSharedCheck_649_; 
v_a_625_ = lean_ctor_get(v___x_624_, 0);
v_isSharedCheck_649_ = !lean_is_exclusive(v___x_624_);
if (v_isSharedCheck_649_ == 0)
{
v___x_627_ = v___x_624_;
v_isShared_628_ = v_isSharedCheck_649_;
goto v_resetjp_626_;
}
else
{
lean_inc(v_a_625_);
lean_dec(v___x_624_);
v___x_627_ = lean_box(0);
v_isShared_628_ = v_isSharedCheck_649_;
goto v_resetjp_626_;
}
v_resetjp_626_:
{
if (lean_obj_tag(v_a_625_) == 1)
{
lean_object* v_val_629_; lean_object* v___x_631_; uint8_t v_isShared_632_; uint8_t v_isSharedCheck_644_; 
v_val_629_ = lean_ctor_get(v_a_625_, 0);
v_isSharedCheck_644_ = !lean_is_exclusive(v_a_625_);
if (v_isSharedCheck_644_ == 0)
{
v___x_631_ = v_a_625_;
v_isShared_632_ = v_isSharedCheck_644_;
goto v_resetjp_630_;
}
else
{
lean_inc(v_val_629_);
lean_dec(v_a_625_);
v___x_631_ = lean_box(0);
v_isShared_632_ = v_isSharedCheck_644_;
goto v_resetjp_630_;
}
v_resetjp_630_:
{
lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_637_; 
v___x_633_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_addIntToBitVecLemmas_findNumBitsEq_spec__0___redArg___closed__11, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_addIntToBitVecLemmas_findNumBitsEq_spec__0___redArg___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_addIntToBitVecLemmas_findNumBitsEq_spec__0___redArg___closed__11);
lean_inc_ref(v_value_599_);
v___x_634_ = l_Lean_mkApp4(v___x_633_, v_arg_617_, v_arg_614_, v_arg_611_, v_value_599_);
v___x_635_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_635_, 0, v_val_629_);
lean_ctor_set(v___x_635_, 1, v___x_634_);
if (v_isShared_632_ == 0)
{
lean_ctor_set(v___x_631_, 0, v___x_635_);
v___x_637_ = v___x_631_;
goto v_reusejp_636_;
}
else
{
lean_object* v_reuseFailAlloc_643_; 
v_reuseFailAlloc_643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_643_, 0, v___x_635_);
v___x_637_ = v_reuseFailAlloc_643_;
goto v_reusejp_636_;
}
v_reusejp_636_:
{
lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_641_; 
v___x_638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_638_, 0, v___x_637_);
v___x_639_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_639_, 0, v___x_638_);
lean_ctor_set(v___x_639_, 1, v___x_607_);
if (v_isShared_628_ == 0)
{
lean_ctor_set(v___x_627_, 0, v___x_639_);
v___x_641_ = v___x_627_;
goto v_reusejp_640_;
}
else
{
lean_object* v_reuseFailAlloc_642_; 
v_reuseFailAlloc_642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_642_, 0, v___x_639_);
v___x_641_ = v_reuseFailAlloc_642_;
goto v_reusejp_640_;
}
v_reusejp_640_:
{
return v___x_641_;
}
}
}
}
else
{
lean_object* v___x_645_; lean_object* v___x_647_; 
lean_dec(v_a_625_);
lean_dec_ref(v_arg_617_);
lean_dec_ref(v_arg_614_);
lean_dec_ref(v_arg_611_);
v___x_645_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_addIntToBitVecLemmas_findNumBitsEq_spec__0___redArg___closed__13));
if (v_isShared_628_ == 0)
{
lean_ctor_set(v___x_627_, 0, v___x_645_);
v___x_647_ = v___x_627_;
goto v_reusejp_646_;
}
else
{
lean_object* v_reuseFailAlloc_648_; 
v_reuseFailAlloc_648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_648_, 0, v___x_645_);
v___x_647_ = v_reuseFailAlloc_648_;
goto v_reusejp_646_;
}
v_reusejp_646_:
{
return v___x_647_;
}
}
}
}
else
{
lean_object* v_a_650_; lean_object* v___x_652_; uint8_t v_isShared_653_; uint8_t v_isSharedCheck_657_; 
lean_dec_ref(v_arg_617_);
lean_dec_ref(v_arg_614_);
lean_dec_ref(v_arg_611_);
v_a_650_ = lean_ctor_get(v___x_624_, 0);
v_isSharedCheck_657_ = !lean_is_exclusive(v___x_624_);
if (v_isSharedCheck_657_ == 0)
{
v___x_652_ = v___x_624_;
v_isShared_653_ = v_isSharedCheck_657_;
goto v_resetjp_651_;
}
else
{
lean_inc(v_a_650_);
lean_dec(v___x_624_);
v___x_652_ = lean_box(0);
v_isShared_653_ = v_isSharedCheck_657_;
goto v_resetjp_651_;
}
v_resetjp_651_:
{
lean_object* v___x_655_; 
if (v_isShared_653_ == 0)
{
v___x_655_ = v___x_652_;
goto v_reusejp_654_;
}
else
{
lean_object* v_reuseFailAlloc_656_; 
v_reuseFailAlloc_656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_656_, 0, v_a_650_);
v___x_655_ = v_reuseFailAlloc_656_;
goto v_reusejp_654_;
}
v_reusejp_654_:
{
return v___x_655_;
}
}
}
}
}
else
{
lean_object* v___x_658_; 
lean_dec_ref(v_arg_617_);
lean_dec_ref(v_arg_614_);
v___x_658_ = l_Lean_Meta_getNatValue_x3f(v_arg_611_, v___y_590_, v___y_591_, v___y_592_, v___y_593_);
lean_dec_ref(v_arg_611_);
if (lean_obj_tag(v___x_658_) == 0)
{
lean_object* v_a_659_; lean_object* v___x_661_; uint8_t v_isShared_662_; uint8_t v_isSharedCheck_681_; 
v_a_659_ = lean_ctor_get(v___x_658_, 0);
v_isSharedCheck_681_ = !lean_is_exclusive(v___x_658_);
if (v_isSharedCheck_681_ == 0)
{
v___x_661_ = v___x_658_;
v_isShared_662_ = v_isSharedCheck_681_;
goto v_resetjp_660_;
}
else
{
lean_inc(v_a_659_);
lean_dec(v___x_658_);
v___x_661_ = lean_box(0);
v_isShared_662_ = v_isSharedCheck_681_;
goto v_resetjp_660_;
}
v_resetjp_660_:
{
if (lean_obj_tag(v_a_659_) == 1)
{
lean_object* v_val_663_; lean_object* v___x_665_; uint8_t v_isShared_666_; uint8_t v_isSharedCheck_676_; 
v_val_663_ = lean_ctor_get(v_a_659_, 0);
v_isSharedCheck_676_ = !lean_is_exclusive(v_a_659_);
if (v_isSharedCheck_676_ == 0)
{
v___x_665_ = v_a_659_;
v_isShared_666_ = v_isSharedCheck_676_;
goto v_resetjp_664_;
}
else
{
lean_inc(v_val_663_);
lean_dec(v_a_659_);
v___x_665_ = lean_box(0);
v_isShared_666_ = v_isSharedCheck_676_;
goto v_resetjp_664_;
}
v_resetjp_664_:
{
lean_object* v___x_667_; lean_object* v___x_669_; 
lean_inc_ref(v_value_599_);
v___x_667_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_667_, 0, v_val_663_);
lean_ctor_set(v___x_667_, 1, v_value_599_);
if (v_isShared_666_ == 0)
{
lean_ctor_set(v___x_665_, 0, v___x_667_);
v___x_669_ = v___x_665_;
goto v_reusejp_668_;
}
else
{
lean_object* v_reuseFailAlloc_675_; 
v_reuseFailAlloc_675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_675_, 0, v___x_667_);
v___x_669_ = v_reuseFailAlloc_675_;
goto v_reusejp_668_;
}
v_reusejp_668_:
{
lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_673_; 
v___x_670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_670_, 0, v___x_669_);
v___x_671_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_671_, 0, v___x_670_);
lean_ctor_set(v___x_671_, 1, v___x_607_);
if (v_isShared_662_ == 0)
{
lean_ctor_set(v___x_661_, 0, v___x_671_);
v___x_673_ = v___x_661_;
goto v_reusejp_672_;
}
else
{
lean_object* v_reuseFailAlloc_674_; 
v_reuseFailAlloc_674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_674_, 0, v___x_671_);
v___x_673_ = v_reuseFailAlloc_674_;
goto v_reusejp_672_;
}
v_reusejp_672_:
{
return v___x_673_;
}
}
}
}
else
{
lean_object* v___x_677_; lean_object* v___x_679_; 
lean_dec(v_a_659_);
v___x_677_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_addIntToBitVecLemmas_findNumBitsEq_spec__0___redArg___closed__13));
if (v_isShared_662_ == 0)
{
lean_ctor_set(v___x_661_, 0, v___x_677_);
v___x_679_ = v___x_661_;
goto v_reusejp_678_;
}
else
{
lean_object* v_reuseFailAlloc_680_; 
v_reuseFailAlloc_680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_680_, 0, v___x_677_);
v___x_679_ = v_reuseFailAlloc_680_;
goto v_reusejp_678_;
}
v_reusejp_678_:
{
return v___x_679_;
}
}
}
}
else
{
lean_object* v_a_682_; lean_object* v___x_684_; uint8_t v_isShared_685_; uint8_t v_isSharedCheck_689_; 
v_a_682_ = lean_ctor_get(v___x_658_, 0);
v_isSharedCheck_689_ = !lean_is_exclusive(v___x_658_);
if (v_isSharedCheck_689_ == 0)
{
v___x_684_ = v___x_658_;
v_isShared_685_ = v_isSharedCheck_689_;
goto v_resetjp_683_;
}
else
{
lean_inc(v_a_682_);
lean_dec(v___x_658_);
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
}
}
v___jp_602_:
{
size_t v___x_604_; size_t v___x_605_; 
v___x_604_ = ((size_t)1ULL);
v___x_605_ = lean_usize_add(v_i_588_, v___x_604_);
lean_inc_ref(v_a_603_);
v_i_588_ = v___x_605_;
v_b_589_ = v_a_603_;
goto _start;
}
}
else
{
lean_object* v_a_690_; lean_object* v___x_692_; uint8_t v_isShared_693_; uint8_t v_isSharedCheck_697_; 
v_a_690_ = lean_ctor_get(v___x_600_, 0);
v_isSharedCheck_697_ = !lean_is_exclusive(v___x_600_);
if (v_isSharedCheck_697_ == 0)
{
v___x_692_ = v___x_600_;
v_isShared_693_ = v_isSharedCheck_697_;
goto v_resetjp_691_;
}
else
{
lean_inc(v_a_690_);
lean_dec(v___x_600_);
v___x_692_ = lean_box(0);
v_isShared_693_ = v_isSharedCheck_697_;
goto v_resetjp_691_;
}
v_resetjp_691_:
{
lean_object* v___x_695_; 
if (v_isShared_693_ == 0)
{
v___x_695_ = v___x_692_;
goto v_reusejp_694_;
}
else
{
lean_object* v_reuseFailAlloc_696_; 
v_reuseFailAlloc_696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_696_, 0, v_a_690_);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_addIntToBitVecLemmas_findNumBitsEq_spec__0___redArg___boxed(lean_object* v_as_698_, lean_object* v_sz_699_, lean_object* v_i_700_, lean_object* v_b_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_){
_start:
{
size_t v_sz_boxed_707_; size_t v_i_boxed_708_; lean_object* v_res_709_; 
v_sz_boxed_707_ = lean_unbox_usize(v_sz_699_);
lean_dec(v_sz_699_);
v_i_boxed_708_ = lean_unbox_usize(v_i_700_);
lean_dec(v_i_700_);
v_res_709_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_addIntToBitVecLemmas_findNumBitsEq_spec__0___redArg(v_as_698_, v_sz_boxed_707_, v_i_boxed_708_, v_b_701_, v___y_702_, v___y_703_, v___y_704_, v___y_705_);
lean_dec(v___y_705_);
lean_dec_ref(v___y_704_);
lean_dec(v___y_703_);
lean_dec_ref(v___y_702_);
lean_dec_ref(v_as_698_);
return v_res_709_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_addIntToBitVecLemmas_findNumBitsEq___lam__0(lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_){
_start:
{
lean_object* v___x_722_; lean_object* v_hypotheses_723_; lean_object* v___x_724_; lean_object* v___x_725_; size_t v_sz_726_; size_t v___x_727_; lean_object* v___x_728_; 
v___x_722_ = lean_st_ref_get(v___y_711_);
v_hypotheses_723_ = lean_ctor_get(v___x_722_, 5);
lean_inc_ref(v_hypotheses_723_);
lean_dec(v___x_722_);
v___x_724_ = lean_box(0);
v___x_725_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_addIntToBitVecLemmas_findNumBitsEq_spec__0___redArg___closed__0));
v_sz_726_ = lean_array_size(v_hypotheses_723_);
v___x_727_ = ((size_t)0ULL);
v___x_728_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_addIntToBitVecLemmas_findNumBitsEq_spec__0___redArg(v_hypotheses_723_, v_sz_726_, v___x_727_, v___x_725_, v___y_717_, v___y_718_, v___y_719_, v___y_720_);
lean_dec_ref(v_hypotheses_723_);
if (lean_obj_tag(v___x_728_) == 0)
{
lean_object* v_a_729_; lean_object* v___x_731_; uint8_t v_isShared_732_; uint8_t v_isSharedCheck_741_; 
v_a_729_ = lean_ctor_get(v___x_728_, 0);
v_isSharedCheck_741_ = !lean_is_exclusive(v___x_728_);
if (v_isSharedCheck_741_ == 0)
{
v___x_731_ = v___x_728_;
v_isShared_732_ = v_isSharedCheck_741_;
goto v_resetjp_730_;
}
else
{
lean_inc(v_a_729_);
lean_dec(v___x_728_);
v___x_731_ = lean_box(0);
v_isShared_732_ = v_isSharedCheck_741_;
goto v_resetjp_730_;
}
v_resetjp_730_:
{
lean_object* v_fst_733_; 
v_fst_733_ = lean_ctor_get(v_a_729_, 0);
lean_inc(v_fst_733_);
lean_dec(v_a_729_);
if (lean_obj_tag(v_fst_733_) == 0)
{
lean_object* v___x_735_; 
if (v_isShared_732_ == 0)
{
lean_ctor_set(v___x_731_, 0, v___x_724_);
v___x_735_ = v___x_731_;
goto v_reusejp_734_;
}
else
{
lean_object* v_reuseFailAlloc_736_; 
v_reuseFailAlloc_736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_736_, 0, v___x_724_);
v___x_735_ = v_reuseFailAlloc_736_;
goto v_reusejp_734_;
}
v_reusejp_734_:
{
return v___x_735_;
}
}
else
{
lean_object* v_val_737_; lean_object* v___x_739_; 
v_val_737_ = lean_ctor_get(v_fst_733_, 0);
lean_inc(v_val_737_);
lean_dec_ref_known(v_fst_733_, 1);
if (v_isShared_732_ == 0)
{
lean_ctor_set(v___x_731_, 0, v_val_737_);
v___x_739_ = v___x_731_;
goto v_reusejp_738_;
}
else
{
lean_object* v_reuseFailAlloc_740_; 
v_reuseFailAlloc_740_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_740_, 0, v_val_737_);
v___x_739_ = v_reuseFailAlloc_740_;
goto v_reusejp_738_;
}
v_reusejp_738_:
{
return v___x_739_;
}
}
}
}
else
{
lean_object* v_a_742_; lean_object* v___x_744_; uint8_t v_isShared_745_; uint8_t v_isSharedCheck_749_; 
v_a_742_ = lean_ctor_get(v___x_728_, 0);
v_isSharedCheck_749_ = !lean_is_exclusive(v___x_728_);
if (v_isSharedCheck_749_ == 0)
{
v___x_744_ = v___x_728_;
v_isShared_745_ = v_isSharedCheck_749_;
goto v_resetjp_743_;
}
else
{
lean_inc(v_a_742_);
lean_dec(v___x_728_);
v___x_744_ = lean_box(0);
v_isShared_745_ = v_isSharedCheck_749_;
goto v_resetjp_743_;
}
v_resetjp_743_:
{
lean_object* v___x_747_; 
if (v_isShared_745_ == 0)
{
v___x_747_ = v___x_744_;
goto v_reusejp_746_;
}
else
{
lean_object* v_reuseFailAlloc_748_; 
v_reuseFailAlloc_748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_748_, 0, v_a_742_);
v___x_747_ = v_reuseFailAlloc_748_;
goto v_reusejp_746_;
}
v_reusejp_746_:
{
return v___x_747_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_addIntToBitVecLemmas_findNumBitsEq___lam__0___boxed(lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_, lean_object* v___y_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_){
_start:
{
lean_object* v_res_762_; 
v_res_762_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_addIntToBitVecLemmas_findNumBitsEq___lam__0(v___y_750_, v___y_751_, v___y_752_, v___y_753_, v___y_754_, v___y_755_, v___y_756_, v___y_757_, v___y_758_, v___y_759_, v___y_760_);
lean_dec(v___y_760_);
lean_dec_ref(v___y_759_);
lean_dec(v___y_758_);
lean_dec_ref(v___y_757_);
lean_dec(v___y_756_);
lean_dec_ref(v___y_755_);
lean_dec(v___y_754_);
lean_dec_ref(v___y_753_);
lean_dec(v___y_752_);
lean_dec(v___y_751_);
lean_dec_ref(v___y_750_);
return v_res_762_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_addIntToBitVecLemmas_findNumBitsEq(lean_object* v_goal_764_, lean_object* v_a_765_, lean_object* v_a_766_, lean_object* v_a_767_, lean_object* v_a_768_, lean_object* v_a_769_, lean_object* v_a_770_, lean_object* v_a_771_, lean_object* v_a_772_, lean_object* v_a_773_, lean_object* v_a_774_, lean_object* v_a_775_){
_start:
{
lean_object* v___f_777_; lean_object* v___x_778_; 
v___f_777_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_addIntToBitVecLemmas_findNumBitsEq___closed__0));
v___x_778_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_addIntToBitVecLemmas_findNumBitsEq_spec__1___redArg(v_goal_764_, v___f_777_, v_a_765_, v_a_766_, v_a_767_, v_a_768_, v_a_769_, v_a_770_, v_a_771_, v_a_772_, v_a_773_, v_a_774_, v_a_775_);
return v___x_778_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_addIntToBitVecLemmas_findNumBitsEq___boxed(lean_object* v_goal_779_, lean_object* v_a_780_, lean_object* v_a_781_, lean_object* v_a_782_, lean_object* v_a_783_, lean_object* v_a_784_, lean_object* v_a_785_, lean_object* v_a_786_, lean_object* v_a_787_, lean_object* v_a_788_, lean_object* v_a_789_, lean_object* v_a_790_, lean_object* v_a_791_){
_start:
{
lean_object* v_res_792_; 
v_res_792_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_addIntToBitVecLemmas_findNumBitsEq(v_goal_779_, v_a_780_, v_a_781_, v_a_782_, v_a_783_, v_a_784_, v_a_785_, v_a_786_, v_a_787_, v_a_788_, v_a_789_, v_a_790_);
lean_dec(v_a_790_);
lean_dec_ref(v_a_789_);
lean_dec(v_a_788_);
lean_dec_ref(v_a_787_);
lean_dec(v_a_786_);
lean_dec_ref(v_a_785_);
lean_dec(v_a_784_);
lean_dec_ref(v_a_783_);
lean_dec(v_a_782_);
lean_dec(v_a_781_);
lean_dec_ref(v_a_780_);
return v_res_792_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_addIntToBitVecLemmas_findNumBitsEq_spec__0(lean_object* v_as_793_, size_t v_sz_794_, size_t v_i_795_, lean_object* v_b_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_){
_start:
{
lean_object* v___x_809_; 
v___x_809_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_addIntToBitVecLemmas_findNumBitsEq_spec__0___redArg(v_as_793_, v_sz_794_, v_i_795_, v_b_796_, v___y_804_, v___y_805_, v___y_806_, v___y_807_);
return v___x_809_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_addIntToBitVecLemmas_findNumBitsEq_spec__0___boxed(lean_object* v_as_810_, lean_object* v_sz_811_, lean_object* v_i_812_, lean_object* v_b_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_){
_start:
{
size_t v_sz_boxed_826_; size_t v_i_boxed_827_; lean_object* v_res_828_; 
v_sz_boxed_826_ = lean_unbox_usize(v_sz_811_);
lean_dec(v_sz_811_);
v_i_boxed_827_ = lean_unbox_usize(v_i_812_);
lean_dec(v_i_812_);
v_res_828_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_addIntToBitVecLemmas_findNumBitsEq_spec__0(v_as_810_, v_sz_boxed_826_, v_i_boxed_827_, v_b_813_, v___y_814_, v___y_815_, v___y_816_, v___y_817_, v___y_818_, v___y_819_, v___y_820_, v___y_821_, v___y_822_, v___y_823_, v___y_824_);
lean_dec(v___y_824_);
lean_dec_ref(v___y_823_);
lean_dec(v___y_822_);
lean_dec_ref(v___y_821_);
lean_dec(v___y_820_);
lean_dec_ref(v___y_819_);
lean_dec(v___y_818_);
lean_dec_ref(v___y_817_);
lean_dec(v___y_816_);
lean_dec(v___y_815_);
lean_dec_ref(v___y_814_);
lean_dec_ref(v_as_810_);
return v_res_828_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_addIntToBitVecLemmas___lam__0(lean_object* v_a_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_){
_start:
{
if (lean_obj_tag(v_a_831_) == 1)
{
lean_object* v_val_843_; lean_object* v___x_845_; uint8_t v_isShared_846_; uint8_t v_isSharedCheck_905_; 
v_val_843_ = lean_ctor_get(v_a_831_, 0);
v_isSharedCheck_905_ = !lean_is_exclusive(v_a_831_);
if (v_isSharedCheck_905_ == 0)
{
v___x_845_ = v_a_831_;
v_isShared_846_ = v_isSharedCheck_905_;
goto v_resetjp_844_;
}
else
{
lean_inc(v_val_843_);
lean_dec(v_a_831_);
v___x_845_ = lean_box(0);
v_isShared_846_ = v_isSharedCheck_905_;
goto v_resetjp_844_;
}
v_resetjp_844_:
{
lean_object* v_fst_847_; lean_object* v_snd_848_; lean_object* v___x_849_; 
v_fst_847_ = lean_ctor_get(v_val_843_, 0);
lean_inc(v_fst_847_);
v_snd_848_ = lean_ctor_get(v_val_843_, 1);
lean_inc(v_snd_848_);
lean_dec(v_val_843_);
v___x_849_ = l_Lean_Meta_Sym_instantiateMVarsS(v___y_832_, v___y_836_, v___y_837_, v___y_838_, v___y_839_, v___y_840_, v___y_841_);
if (lean_obj_tag(v___x_849_) == 0)
{
lean_object* v_a_850_; lean_object* v___x_852_; uint8_t v_isShared_853_; uint8_t v_isSharedCheck_896_; 
v_a_850_ = lean_ctor_get(v___x_849_, 0);
v_isSharedCheck_896_ = !lean_is_exclusive(v___x_849_);
if (v_isSharedCheck_896_ == 0)
{
v___x_852_ = v___x_849_;
v_isShared_853_ = v_isSharedCheck_896_;
goto v_resetjp_851_;
}
else
{
lean_inc(v_a_850_);
lean_dec(v___x_849_);
v___x_852_ = lean_box(0);
v_isShared_853_ = v_isSharedCheck_896_;
goto v_resetjp_851_;
}
v_resetjp_851_:
{
lean_object* v___x_859_; uint8_t v___x_860_; 
v___x_859_ = l_Lean_Expr_cleanupAnnotations(v_a_850_);
v___x_860_ = l_Lean_Expr_isApp(v___x_859_);
if (v___x_860_ == 0)
{
lean_dec_ref(v___x_859_);
lean_dec(v_snd_848_);
lean_dec(v_fst_847_);
lean_del_object(v___x_845_);
goto v___jp_854_;
}
else
{
lean_object* v_arg_861_; lean_object* v___x_862_; uint8_t v___x_863_; 
v_arg_861_ = lean_ctor_get(v___x_859_, 1);
lean_inc_ref(v_arg_861_);
v___x_862_ = l_Lean_Expr_appFnCleanup___redArg(v___x_859_);
v___x_863_ = l_Lean_Expr_isApp(v___x_862_);
if (v___x_863_ == 0)
{
lean_dec_ref(v___x_862_);
lean_dec_ref(v_arg_861_);
lean_dec(v_snd_848_);
lean_dec(v_fst_847_);
lean_del_object(v___x_845_);
goto v___jp_854_;
}
else
{
lean_object* v_arg_864_; lean_object* v___x_865_; uint8_t v___x_866_; 
v_arg_864_ = lean_ctor_get(v___x_862_, 1);
lean_inc_ref(v_arg_864_);
v___x_865_ = l_Lean_Expr_appFnCleanup___redArg(v___x_862_);
v___x_866_ = l_Lean_Expr_isApp(v___x_865_);
if (v___x_866_ == 0)
{
lean_dec_ref(v___x_865_);
lean_dec_ref(v_arg_864_);
lean_dec_ref(v_arg_861_);
lean_dec(v_snd_848_);
lean_dec(v_fst_847_);
lean_del_object(v___x_845_);
goto v___jp_854_;
}
else
{
lean_object* v___x_867_; lean_object* v___x_868_; uint8_t v___x_869_; 
v___x_867_ = l_Lean_Expr_appFnCleanup___redArg(v___x_865_);
v___x_868_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_addIntToBitVecLemmas_findNumBitsEq_spec__0___redArg___closed__2));
v___x_869_ = l_Lean_Expr_isConstOf(v___x_867_, v___x_868_);
lean_dec_ref(v___x_867_);
if (v___x_869_ == 0)
{
lean_dec_ref(v_arg_864_);
lean_dec_ref(v_arg_861_);
lean_dec(v_snd_848_);
lean_dec(v_fst_847_);
lean_del_object(v___x_845_);
goto v___jp_854_;
}
else
{
lean_object* v___x_870_; uint8_t v___x_871_; 
lean_del_object(v___x_852_);
v___x_870_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_addIntToBitVecLemmas_findNumBitsEq_spec__0___redArg___closed__6));
v___x_871_ = l_Lean_Expr_isConstOf(v_arg_864_, v___x_870_);
lean_dec_ref(v_arg_864_);
if (v___x_871_ == 0)
{
lean_object* v___x_872_; lean_object* v___x_874_; 
lean_dec_ref(v_arg_861_);
lean_dec(v_snd_848_);
lean_dec(v_fst_847_);
v___x_872_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_872_, 0, v___x_871_);
if (v_isShared_846_ == 0)
{
lean_ctor_set_tag(v___x_845_, 0);
lean_ctor_set(v___x_845_, 0, v___x_872_);
v___x_874_ = v___x_845_;
goto v_reusejp_873_;
}
else
{
lean_object* v_reuseFailAlloc_875_; 
v_reuseFailAlloc_875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_875_, 0, v___x_872_);
v___x_874_ = v_reuseFailAlloc_875_;
goto v_reusejp_873_;
}
v_reusejp_873_:
{
return v___x_874_;
}
}
else
{
lean_object* v___x_876_; 
v___x_876_ = l_Lean_Meta_Sym_getNatValue_x3f(v_arg_861_);
if (lean_obj_tag(v___x_876_) == 1)
{
lean_object* v_val_877_; lean_object* v___x_879_; uint8_t v_isShared_880_; uint8_t v_isSharedCheck_891_; 
lean_del_object(v___x_845_);
v_val_877_ = lean_ctor_get(v___x_876_, 0);
v_isSharedCheck_891_ = !lean_is_exclusive(v___x_876_);
if (v_isSharedCheck_891_ == 0)
{
v___x_879_ = v___x_876_;
v_isShared_880_ = v_isSharedCheck_891_;
goto v_resetjp_878_;
}
else
{
lean_inc(v_val_877_);
lean_dec(v___x_876_);
v___x_879_ = lean_box(0);
v_isShared_880_ = v_isSharedCheck_891_;
goto v_resetjp_878_;
}
v_resetjp_878_:
{
uint8_t v___x_881_; 
v___x_881_ = lean_nat_dec_eq(v_fst_847_, v_val_877_);
lean_dec(v_val_877_);
lean_dec(v_fst_847_);
if (v___x_881_ == 0)
{
lean_object* v___x_882_; lean_object* v___x_884_; 
lean_dec(v_snd_848_);
v___x_882_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_882_, 0, v___x_881_);
if (v_isShared_880_ == 0)
{
lean_ctor_set_tag(v___x_879_, 0);
lean_ctor_set(v___x_879_, 0, v___x_882_);
v___x_884_ = v___x_879_;
goto v_reusejp_883_;
}
else
{
lean_object* v_reuseFailAlloc_885_; 
v_reuseFailAlloc_885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_885_, 0, v___x_882_);
v___x_884_ = v_reuseFailAlloc_885_;
goto v_reusejp_883_;
}
v_reusejp_883_:
{
return v___x_884_;
}
}
else
{
uint8_t v___x_886_; lean_object* v___x_887_; lean_object* v___x_889_; 
v___x_886_ = 0;
v___x_887_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_887_, 0, v_snd_848_);
lean_ctor_set_uint8(v___x_887_, sizeof(void*)*1, v___x_886_);
if (v_isShared_880_ == 0)
{
lean_ctor_set_tag(v___x_879_, 0);
lean_ctor_set(v___x_879_, 0, v___x_887_);
v___x_889_ = v___x_879_;
goto v_reusejp_888_;
}
else
{
lean_object* v_reuseFailAlloc_890_; 
v_reuseFailAlloc_890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_890_, 0, v___x_887_);
v___x_889_ = v_reuseFailAlloc_890_;
goto v_reusejp_888_;
}
v_reusejp_888_:
{
return v___x_889_;
}
}
}
}
else
{
lean_object* v___x_892_; lean_object* v___x_894_; 
lean_dec(v___x_876_);
lean_dec(v_snd_848_);
lean_dec(v_fst_847_);
v___x_892_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_addIntToBitVecLemmas___lam__0___closed__0));
if (v_isShared_846_ == 0)
{
lean_ctor_set_tag(v___x_845_, 0);
lean_ctor_set(v___x_845_, 0, v___x_892_);
v___x_894_ = v___x_845_;
goto v_reusejp_893_;
}
else
{
lean_object* v_reuseFailAlloc_895_; 
v_reuseFailAlloc_895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_895_, 0, v___x_892_);
v___x_894_ = v_reuseFailAlloc_895_;
goto v_reusejp_893_;
}
v_reusejp_893_:
{
return v___x_894_;
}
}
}
}
}
}
}
v___jp_854_:
{
lean_object* v___x_855_; lean_object* v___x_857_; 
v___x_855_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_addIntToBitVecLemmas___lam__0___closed__0));
if (v_isShared_853_ == 0)
{
lean_ctor_set(v___x_852_, 0, v___x_855_);
v___x_857_ = v___x_852_;
goto v_reusejp_856_;
}
else
{
lean_object* v_reuseFailAlloc_858_; 
v_reuseFailAlloc_858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_858_, 0, v___x_855_);
v___x_857_ = v_reuseFailAlloc_858_;
goto v_reusejp_856_;
}
v_reusejp_856_:
{
return v___x_857_;
}
}
}
}
else
{
lean_object* v_a_897_; lean_object* v___x_899_; uint8_t v_isShared_900_; uint8_t v_isSharedCheck_904_; 
lean_dec(v_snd_848_);
lean_dec(v_fst_847_);
lean_del_object(v___x_845_);
v_a_897_ = lean_ctor_get(v___x_849_, 0);
v_isSharedCheck_904_ = !lean_is_exclusive(v___x_849_);
if (v_isSharedCheck_904_ == 0)
{
v___x_899_ = v___x_849_;
v_isShared_900_ = v_isSharedCheck_904_;
goto v_resetjp_898_;
}
else
{
lean_inc(v_a_897_);
lean_dec(v___x_849_);
v___x_899_ = lean_box(0);
v_isShared_900_ = v_isSharedCheck_904_;
goto v_resetjp_898_;
}
v_resetjp_898_:
{
lean_object* v___x_902_; 
if (v_isShared_900_ == 0)
{
v___x_902_ = v___x_899_;
goto v_reusejp_901_;
}
else
{
lean_object* v_reuseFailAlloc_903_; 
v_reuseFailAlloc_903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_903_, 0, v_a_897_);
v___x_902_ = v_reuseFailAlloc_903_;
goto v_reusejp_901_;
}
v_reusejp_901_:
{
return v___x_902_;
}
}
}
}
}
else
{
lean_object* v___x_906_; 
lean_dec_ref(v___y_832_);
lean_dec(v_a_831_);
v___x_906_ = l_Lean_Meta_Sym_Simp_dischargeNone___redArg();
return v___x_906_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_addIntToBitVecLemmas___lam__0___boxed(lean_object* v_a_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_){
_start:
{
lean_object* v_res_919_; 
v_res_919_ = l_Lean_Meta_Tactic_BVDecide_Normalize_addIntToBitVecLemmas___lam__0(v_a_907_, v___y_908_, v___y_909_, v___y_910_, v___y_911_, v___y_912_, v___y_913_, v___y_914_, v___y_915_, v___y_916_, v___y_917_);
lean_dec(v___y_917_);
lean_dec_ref(v___y_916_);
lean_dec(v___y_915_);
lean_dec_ref(v___y_914_);
lean_dec(v___y_913_);
lean_dec_ref(v___y_912_);
lean_dec(v___y_911_);
lean_dec_ref(v___y_910_);
lean_dec(v___y_909_);
return v_res_919_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_addIntToBitVecLemmas___lam__1(lean_object* v_a_920_, lean_object* v___y_921_, lean_object* v_x_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_){
_start:
{
lean_object* v___x_934_; 
lean_inc_ref(v___y_923_);
v___x_934_ = l_Lean_Meta_Sym_Simp_Theorems_rewrite(v_a_920_, v___y_921_, v___y_923_, v___y_924_, v___y_925_, v___y_926_, v___y_927_, v___y_928_, v___y_929_, v___y_930_, v___y_931_, v___y_932_);
if (lean_obj_tag(v___x_934_) == 0)
{
lean_object* v_a_935_; 
v_a_935_ = lean_ctor_get(v___x_934_, 0);
lean_inc(v_a_935_);
if (lean_obj_tag(v_a_935_) == 0)
{
uint8_t v_done_936_; 
v_done_936_ = lean_ctor_get_uint8(v_a_935_, 0);
if (v_done_936_ == 0)
{
lean_object* v___x_938_; uint8_t v_isShared_939_; uint8_t v_isSharedCheck_950_; 
v_isSharedCheck_950_ = !lean_is_exclusive(v___x_934_);
if (v_isSharedCheck_950_ == 0)
{
lean_object* v_unused_951_; 
v_unused_951_ = lean_ctor_get(v___x_934_, 0);
lean_dec(v_unused_951_);
v___x_938_ = v___x_934_;
v_isShared_939_ = v_isSharedCheck_950_;
goto v_resetjp_937_;
}
else
{
lean_dec(v___x_934_);
v___x_938_ = lean_box(0);
v_isShared_939_ = v_isSharedCheck_950_;
goto v_resetjp_937_;
}
v_resetjp_937_:
{
uint8_t v_contextDependent_940_; lean_object* v___x_941_; 
v_contextDependent_940_ = lean_ctor_get_uint8(v_a_935_, 1);
lean_dec_ref_known(v_a_935_, 0);
v___x_941_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg(v___y_923_, v___y_927_, v___y_928_, v___y_929_, v___y_930_, v___y_931_, v___y_932_);
if (lean_obj_tag(v___x_941_) == 0)
{
lean_object* v_a_942_; uint8_t v___y_944_; 
v_a_942_ = lean_ctor_get(v___x_941_, 0);
lean_inc(v_a_942_);
if (v_contextDependent_940_ == 0)
{
lean_dec(v_a_942_);
lean_del_object(v___x_938_);
return v___x_941_;
}
else
{
uint8_t v___x_949_; 
lean_dec_ref_known(v___x_941_, 1);
v___x_949_ = 0;
v___y_944_ = v___x_949_;
goto v___jp_943_;
}
v___jp_943_:
{
lean_object* v___x_945_; lean_object* v___x_947_; 
v___x_945_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_942_);
if (v_isShared_939_ == 0)
{
lean_ctor_set(v___x_938_, 0, v___x_945_);
v___x_947_ = v___x_938_;
goto v_reusejp_946_;
}
else
{
lean_object* v_reuseFailAlloc_948_; 
v_reuseFailAlloc_948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_948_, 0, v___x_945_);
v___x_947_ = v_reuseFailAlloc_948_;
goto v_reusejp_946_;
}
v_reusejp_946_:
{
return v___x_947_;
}
}
}
else
{
lean_del_object(v___x_938_);
return v___x_941_;
}
}
}
else
{
lean_dec_ref_known(v_a_935_, 0);
lean_dec_ref(v___y_923_);
return v___x_934_;
}
}
else
{
uint8_t v_done_952_; 
v_done_952_ = lean_ctor_get_uint8(v_a_935_, sizeof(void*)*2);
if (v_done_952_ == 0)
{
lean_object* v_e_x27_953_; lean_object* v_proof_954_; uint8_t v_contextDependent_955_; lean_object* v___x_957_; uint8_t v_isShared_958_; uint8_t v_isSharedCheck_1003_; 
lean_dec_ref_known(v___x_934_, 1);
v_e_x27_953_ = lean_ctor_get(v_a_935_, 0);
v_proof_954_ = lean_ctor_get(v_a_935_, 1);
v_contextDependent_955_ = lean_ctor_get_uint8(v_a_935_, sizeof(void*)*2 + 1);
v_isSharedCheck_1003_ = !lean_is_exclusive(v_a_935_);
if (v_isSharedCheck_1003_ == 0)
{
v___x_957_ = v_a_935_;
v_isShared_958_ = v_isSharedCheck_1003_;
goto v_resetjp_956_;
}
else
{
lean_inc(v_proof_954_);
lean_inc(v_e_x27_953_);
lean_dec(v_a_935_);
v___x_957_ = lean_box(0);
v_isShared_958_ = v_isSharedCheck_1003_;
goto v_resetjp_956_;
}
v_resetjp_956_:
{
lean_object* v___x_959_; 
lean_inc_ref(v_e_x27_953_);
v___x_959_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc___redArg(v_e_x27_953_, v___y_927_, v___y_928_, v___y_929_, v___y_930_, v___y_931_, v___y_932_);
if (lean_obj_tag(v___x_959_) == 0)
{
lean_object* v_a_960_; lean_object* v___x_962_; uint8_t v_isShared_963_; uint8_t v_isSharedCheck_1002_; 
v_a_960_ = lean_ctor_get(v___x_959_, 0);
v_isSharedCheck_1002_ = !lean_is_exclusive(v___x_959_);
if (v_isSharedCheck_1002_ == 0)
{
v___x_962_ = v___x_959_;
v_isShared_963_ = v_isSharedCheck_1002_;
goto v_resetjp_961_;
}
else
{
lean_inc(v_a_960_);
lean_dec(v___x_959_);
v___x_962_ = lean_box(0);
v_isShared_963_ = v_isSharedCheck_1002_;
goto v_resetjp_961_;
}
v_resetjp_961_:
{
if (lean_obj_tag(v_a_960_) == 0)
{
uint8_t v___x_964_; uint8_t v___y_966_; 
lean_dec_ref_known(v_a_960_, 0);
lean_dec_ref(v___y_923_);
v___x_964_ = 0;
if (v_contextDependent_955_ == 0)
{
v___y_966_ = v___x_964_;
goto v___jp_965_;
}
else
{
v___y_966_ = v_contextDependent_955_;
goto v___jp_965_;
}
v___jp_965_:
{
lean_object* v___x_968_; 
if (v_isShared_958_ == 0)
{
v___x_968_ = v___x_957_;
goto v_reusejp_967_;
}
else
{
lean_object* v_reuseFailAlloc_972_; 
v_reuseFailAlloc_972_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_972_, 0, v_e_x27_953_);
lean_ctor_set(v_reuseFailAlloc_972_, 1, v_proof_954_);
v___x_968_ = v_reuseFailAlloc_972_;
goto v_reusejp_967_;
}
v_reusejp_967_:
{
lean_object* v___x_970_; 
lean_ctor_set_uint8(v___x_968_, sizeof(void*)*2, v___x_964_);
lean_ctor_set_uint8(v___x_968_, sizeof(void*)*2 + 1, v___y_966_);
if (v_isShared_963_ == 0)
{
lean_ctor_set(v___x_962_, 0, v___x_968_);
v___x_970_ = v___x_962_;
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
}
}
else
{
lean_object* v_e_x27_973_; lean_object* v_proof_974_; lean_object* v___x_976_; uint8_t v_isShared_977_; uint8_t v_isSharedCheck_1001_; 
lean_del_object(v___x_962_);
lean_del_object(v___x_957_);
v_e_x27_973_ = lean_ctor_get(v_a_960_, 0);
v_proof_974_ = lean_ctor_get(v_a_960_, 1);
v_isSharedCheck_1001_ = !lean_is_exclusive(v_a_960_);
if (v_isSharedCheck_1001_ == 0)
{
v___x_976_ = v_a_960_;
v_isShared_977_ = v_isSharedCheck_1001_;
goto v_resetjp_975_;
}
else
{
lean_inc(v_proof_974_);
lean_inc(v_e_x27_973_);
lean_dec(v_a_960_);
v___x_976_ = lean_box(0);
v_isShared_977_ = v_isSharedCheck_1001_;
goto v_resetjp_975_;
}
v_resetjp_975_:
{
uint8_t v___x_978_; lean_object* v___x_979_; 
v___x_978_ = 0;
lean_inc_ref(v_e_x27_973_);
v___x_979_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___y_923_, v_e_x27_953_, v_proof_954_, v_e_x27_973_, v_proof_974_, v___y_927_, v___y_928_, v___y_929_, v___y_930_, v___y_931_, v___y_932_);
if (lean_obj_tag(v___x_979_) == 0)
{
lean_object* v_a_980_; lean_object* v___x_982_; uint8_t v_isShared_983_; uint8_t v_isSharedCheck_992_; 
v_a_980_ = lean_ctor_get(v___x_979_, 0);
v_isSharedCheck_992_ = !lean_is_exclusive(v___x_979_);
if (v_isSharedCheck_992_ == 0)
{
v___x_982_ = v___x_979_;
v_isShared_983_ = v_isSharedCheck_992_;
goto v_resetjp_981_;
}
else
{
lean_inc(v_a_980_);
lean_dec(v___x_979_);
v___x_982_ = lean_box(0);
v_isShared_983_ = v_isSharedCheck_992_;
goto v_resetjp_981_;
}
v_resetjp_981_:
{
uint8_t v___y_985_; 
if (v_contextDependent_955_ == 0)
{
v___y_985_ = v___x_978_;
goto v___jp_984_;
}
else
{
v___y_985_ = v_contextDependent_955_;
goto v___jp_984_;
}
v___jp_984_:
{
lean_object* v___x_987_; 
if (v_isShared_977_ == 0)
{
lean_ctor_set(v___x_976_, 1, v_a_980_);
v___x_987_ = v___x_976_;
goto v_reusejp_986_;
}
else
{
lean_object* v_reuseFailAlloc_991_; 
v_reuseFailAlloc_991_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_991_, 0, v_e_x27_973_);
lean_ctor_set(v_reuseFailAlloc_991_, 1, v_a_980_);
v___x_987_ = v_reuseFailAlloc_991_;
goto v_reusejp_986_;
}
v_reusejp_986_:
{
lean_object* v___x_989_; 
lean_ctor_set_uint8(v___x_987_, sizeof(void*)*2, v___x_978_);
lean_ctor_set_uint8(v___x_987_, sizeof(void*)*2 + 1, v___y_985_);
if (v_isShared_983_ == 0)
{
lean_ctor_set(v___x_982_, 0, v___x_987_);
v___x_989_ = v___x_982_;
goto v_reusejp_988_;
}
else
{
lean_object* v_reuseFailAlloc_990_; 
v_reuseFailAlloc_990_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_990_, 0, v___x_987_);
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
}
else
{
lean_object* v_a_993_; lean_object* v___x_995_; uint8_t v_isShared_996_; uint8_t v_isSharedCheck_1000_; 
lean_del_object(v___x_976_);
lean_dec_ref(v_e_x27_973_);
v_a_993_ = lean_ctor_get(v___x_979_, 0);
v_isSharedCheck_1000_ = !lean_is_exclusive(v___x_979_);
if (v_isSharedCheck_1000_ == 0)
{
v___x_995_ = v___x_979_;
v_isShared_996_ = v_isSharedCheck_1000_;
goto v_resetjp_994_;
}
else
{
lean_inc(v_a_993_);
lean_dec(v___x_979_);
v___x_995_ = lean_box(0);
v_isShared_996_ = v_isSharedCheck_1000_;
goto v_resetjp_994_;
}
v_resetjp_994_:
{
lean_object* v___x_998_; 
if (v_isShared_996_ == 0)
{
v___x_998_ = v___x_995_;
goto v_reusejp_997_;
}
else
{
lean_object* v_reuseFailAlloc_999_; 
v_reuseFailAlloc_999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_999_, 0, v_a_993_);
v___x_998_ = v_reuseFailAlloc_999_;
goto v_reusejp_997_;
}
v_reusejp_997_:
{
return v___x_998_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_957_);
lean_dec_ref(v_proof_954_);
lean_dec_ref(v_e_x27_953_);
lean_dec_ref(v___y_923_);
return v___x_959_;
}
}
}
else
{
lean_dec_ref_known(v_a_935_, 2);
lean_dec_ref(v___y_923_);
return v___x_934_;
}
}
}
else
{
lean_dec_ref(v___y_923_);
return v___x_934_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_addIntToBitVecLemmas___lam__1___boxed(lean_object* v_a_1004_, lean_object* v___y_1005_, lean_object* v_x_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_){
_start:
{
lean_object* v_res_1018_; 
v_res_1018_ = l_Lean_Meta_Tactic_BVDecide_Normalize_addIntToBitVecLemmas___lam__1(v_a_1004_, v___y_1005_, v_x_1006_, v___y_1007_, v___y_1008_, v___y_1009_, v___y_1010_, v___y_1011_, v___y_1012_, v___y_1013_, v___y_1014_, v___y_1015_, v___y_1016_);
lean_dec(v___y_1016_);
lean_dec_ref(v___y_1015_);
lean_dec(v___y_1014_);
lean_dec_ref(v___y_1013_);
lean_dec(v___y_1012_);
lean_dec_ref(v___y_1011_);
lean_dec(v___y_1010_);
lean_dec_ref(v___y_1009_);
lean_dec(v___y_1008_);
lean_dec_ref(v_a_1004_);
return v_res_1018_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_addIntToBitVecLemmas___lam__2(lean_object* v_pre_1019_, lean_object* v___f_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_){
_start:
{
lean_object* v___x_1032_; 
lean_inc(v___y_1030_);
lean_inc_ref(v___y_1029_);
lean_inc(v___y_1028_);
lean_inc_ref(v___y_1027_);
lean_inc(v___y_1026_);
lean_inc_ref(v___y_1025_);
lean_inc(v___y_1024_);
lean_inc_ref(v___y_1023_);
lean_inc(v___y_1022_);
lean_inc_ref(v___y_1021_);
v___x_1032_ = lean_apply_11(v_pre_1019_, v___y_1021_, v___y_1022_, v___y_1023_, v___y_1024_, v___y_1025_, v___y_1026_, v___y_1027_, v___y_1028_, v___y_1029_, v___y_1030_, lean_box(0));
if (lean_obj_tag(v___x_1032_) == 0)
{
lean_object* v_a_1033_; lean_object* v___x_1034_; 
v_a_1033_ = lean_ctor_get(v___x_1032_, 0);
lean_inc(v_a_1033_);
v___x_1034_ = lean_box(0);
if (lean_obj_tag(v_a_1033_) == 0)
{
uint8_t v_done_1035_; 
v_done_1035_ = lean_ctor_get_uint8(v_a_1033_, 0);
if (v_done_1035_ == 0)
{
uint8_t v_contextDependent_1036_; lean_object* v___x_1037_; 
lean_dec_ref_known(v___x_1032_, 1);
v_contextDependent_1036_ = lean_ctor_get_uint8(v_a_1033_, 1);
lean_dec_ref_known(v_a_1033_, 0);
v___x_1037_ = lean_apply_12(v___f_1020_, v___x_1034_, v___y_1021_, v___y_1022_, v___y_1023_, v___y_1024_, v___y_1025_, v___y_1026_, v___y_1027_, v___y_1028_, v___y_1029_, v___y_1030_, lean_box(0));
if (lean_obj_tag(v___x_1037_) == 0)
{
lean_object* v_a_1038_; uint8_t v___y_1040_; 
v_a_1038_ = lean_ctor_get(v___x_1037_, 0);
lean_inc(v_a_1038_);
if (v_contextDependent_1036_ == 0)
{
lean_dec(v_a_1038_);
return v___x_1037_;
}
else
{
if (lean_obj_tag(v_a_1038_) == 0)
{
uint8_t v_contextDependent_1050_; 
v_contextDependent_1050_ = lean_ctor_get_uint8(v_a_1038_, 1);
v___y_1040_ = v_contextDependent_1050_;
goto v___jp_1039_;
}
else
{
uint8_t v_contextDependent_1051_; 
v_contextDependent_1051_ = lean_ctor_get_uint8(v_a_1038_, sizeof(void*)*2 + 1);
v___y_1040_ = v_contextDependent_1051_;
goto v___jp_1039_;
}
}
v___jp_1039_:
{
if (v___y_1040_ == 0)
{
lean_object* v___x_1042_; uint8_t v_isShared_1043_; uint8_t v_isSharedCheck_1048_; 
v_isSharedCheck_1048_ = !lean_is_exclusive(v___x_1037_);
if (v_isSharedCheck_1048_ == 0)
{
lean_object* v_unused_1049_; 
v_unused_1049_ = lean_ctor_get(v___x_1037_, 0);
lean_dec(v_unused_1049_);
v___x_1042_ = v___x_1037_;
v_isShared_1043_ = v_isSharedCheck_1048_;
goto v_resetjp_1041_;
}
else
{
lean_dec(v___x_1037_);
v___x_1042_ = lean_box(0);
v_isShared_1043_ = v_isSharedCheck_1048_;
goto v_resetjp_1041_;
}
v_resetjp_1041_:
{
lean_object* v___x_1044_; lean_object* v___x_1046_; 
v___x_1044_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_1038_);
if (v_isShared_1043_ == 0)
{
lean_ctor_set(v___x_1042_, 0, v___x_1044_);
v___x_1046_ = v___x_1042_;
goto v_reusejp_1045_;
}
else
{
lean_object* v_reuseFailAlloc_1047_; 
v_reuseFailAlloc_1047_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1047_, 0, v___x_1044_);
v___x_1046_ = v_reuseFailAlloc_1047_;
goto v_reusejp_1045_;
}
v_reusejp_1045_:
{
return v___x_1046_;
}
}
}
else
{
lean_dec(v_a_1038_);
return v___x_1037_;
}
}
}
else
{
return v___x_1037_;
}
}
else
{
lean_dec_ref_known(v_a_1033_, 0);
lean_dec(v___y_1030_);
lean_dec_ref(v___y_1029_);
lean_dec(v___y_1028_);
lean_dec_ref(v___y_1027_);
lean_dec(v___y_1026_);
lean_dec_ref(v___y_1025_);
lean_dec(v___y_1024_);
lean_dec_ref(v___y_1023_);
lean_dec(v___y_1022_);
lean_dec_ref(v___y_1021_);
lean_dec_ref(v___f_1020_);
return v___x_1032_;
}
}
else
{
uint8_t v_done_1052_; 
v_done_1052_ = lean_ctor_get_uint8(v_a_1033_, sizeof(void*)*2);
if (v_done_1052_ == 0)
{
lean_object* v_e_x27_1053_; lean_object* v_proof_1054_; uint8_t v_contextDependent_1055_; lean_object* v___x_1057_; uint8_t v_isShared_1058_; uint8_t v_isSharedCheck_1105_; 
lean_dec_ref_known(v___x_1032_, 1);
v_e_x27_1053_ = lean_ctor_get(v_a_1033_, 0);
v_proof_1054_ = lean_ctor_get(v_a_1033_, 1);
v_contextDependent_1055_ = lean_ctor_get_uint8(v_a_1033_, sizeof(void*)*2 + 1);
v_isSharedCheck_1105_ = !lean_is_exclusive(v_a_1033_);
if (v_isSharedCheck_1105_ == 0)
{
v___x_1057_ = v_a_1033_;
v_isShared_1058_ = v_isSharedCheck_1105_;
goto v_resetjp_1056_;
}
else
{
lean_inc(v_proof_1054_);
lean_inc(v_e_x27_1053_);
lean_dec(v_a_1033_);
v___x_1057_ = lean_box(0);
v_isShared_1058_ = v_isSharedCheck_1105_;
goto v_resetjp_1056_;
}
v_resetjp_1056_:
{
lean_object* v___x_1059_; 
lean_inc(v___y_1030_);
lean_inc_ref(v___y_1029_);
lean_inc(v___y_1028_);
lean_inc_ref(v___y_1027_);
lean_inc(v___y_1026_);
lean_inc_ref(v___y_1025_);
lean_inc_ref(v_e_x27_1053_);
v___x_1059_ = lean_apply_12(v___f_1020_, v___x_1034_, v_e_x27_1053_, v___y_1022_, v___y_1023_, v___y_1024_, v___y_1025_, v___y_1026_, v___y_1027_, v___y_1028_, v___y_1029_, v___y_1030_, lean_box(0));
if (lean_obj_tag(v___x_1059_) == 0)
{
lean_object* v_a_1060_; lean_object* v___x_1062_; uint8_t v_isShared_1063_; uint8_t v_isSharedCheck_1104_; 
v_a_1060_ = lean_ctor_get(v___x_1059_, 0);
v_isSharedCheck_1104_ = !lean_is_exclusive(v___x_1059_);
if (v_isSharedCheck_1104_ == 0)
{
v___x_1062_ = v___x_1059_;
v_isShared_1063_ = v_isSharedCheck_1104_;
goto v_resetjp_1061_;
}
else
{
lean_inc(v_a_1060_);
lean_dec(v___x_1059_);
v___x_1062_ = lean_box(0);
v_isShared_1063_ = v_isSharedCheck_1104_;
goto v_resetjp_1061_;
}
v_resetjp_1061_:
{
if (lean_obj_tag(v_a_1060_) == 0)
{
uint8_t v_done_1064_; uint8_t v_contextDependent_1065_; uint8_t v___y_1067_; 
lean_dec(v___y_1030_);
lean_dec_ref(v___y_1029_);
lean_dec(v___y_1028_);
lean_dec_ref(v___y_1027_);
lean_dec(v___y_1026_);
lean_dec_ref(v___y_1025_);
lean_dec_ref(v___y_1021_);
v_done_1064_ = lean_ctor_get_uint8(v_a_1060_, 0);
v_contextDependent_1065_ = lean_ctor_get_uint8(v_a_1060_, 1);
lean_dec_ref_known(v_a_1060_, 0);
if (v_contextDependent_1055_ == 0)
{
v___y_1067_ = v_contextDependent_1065_;
goto v___jp_1066_;
}
else
{
v___y_1067_ = v_contextDependent_1055_;
goto v___jp_1066_;
}
v___jp_1066_:
{
lean_object* v___x_1069_; 
if (v_isShared_1058_ == 0)
{
v___x_1069_ = v___x_1057_;
goto v_reusejp_1068_;
}
else
{
lean_object* v_reuseFailAlloc_1073_; 
v_reuseFailAlloc_1073_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1073_, 0, v_e_x27_1053_);
lean_ctor_set(v_reuseFailAlloc_1073_, 1, v_proof_1054_);
v___x_1069_ = v_reuseFailAlloc_1073_;
goto v_reusejp_1068_;
}
v_reusejp_1068_:
{
lean_object* v___x_1071_; 
lean_ctor_set_uint8(v___x_1069_, sizeof(void*)*2, v_done_1064_);
lean_ctor_set_uint8(v___x_1069_, sizeof(void*)*2 + 1, v___y_1067_);
if (v_isShared_1063_ == 0)
{
lean_ctor_set(v___x_1062_, 0, v___x_1069_);
v___x_1071_ = v___x_1062_;
goto v_reusejp_1070_;
}
else
{
lean_object* v_reuseFailAlloc_1072_; 
v_reuseFailAlloc_1072_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1072_, 0, v___x_1069_);
v___x_1071_ = v_reuseFailAlloc_1072_;
goto v_reusejp_1070_;
}
v_reusejp_1070_:
{
return v___x_1071_;
}
}
}
}
else
{
lean_object* v_e_x27_1074_; lean_object* v_proof_1075_; uint8_t v_done_1076_; uint8_t v_contextDependent_1077_; lean_object* v___x_1079_; uint8_t v_isShared_1080_; uint8_t v_isSharedCheck_1103_; 
lean_del_object(v___x_1062_);
lean_del_object(v___x_1057_);
v_e_x27_1074_ = lean_ctor_get(v_a_1060_, 0);
v_proof_1075_ = lean_ctor_get(v_a_1060_, 1);
v_done_1076_ = lean_ctor_get_uint8(v_a_1060_, sizeof(void*)*2);
v_contextDependent_1077_ = lean_ctor_get_uint8(v_a_1060_, sizeof(void*)*2 + 1);
v_isSharedCheck_1103_ = !lean_is_exclusive(v_a_1060_);
if (v_isSharedCheck_1103_ == 0)
{
v___x_1079_ = v_a_1060_;
v_isShared_1080_ = v_isSharedCheck_1103_;
goto v_resetjp_1078_;
}
else
{
lean_inc(v_proof_1075_);
lean_inc(v_e_x27_1074_);
lean_dec(v_a_1060_);
v___x_1079_ = lean_box(0);
v_isShared_1080_ = v_isSharedCheck_1103_;
goto v_resetjp_1078_;
}
v_resetjp_1078_:
{
lean_object* v___x_1081_; 
lean_inc_ref(v_e_x27_1074_);
v___x_1081_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___y_1021_, v_e_x27_1053_, v_proof_1054_, v_e_x27_1074_, v_proof_1075_, v___y_1025_, v___y_1026_, v___y_1027_, v___y_1028_, v___y_1029_, v___y_1030_);
lean_dec(v___y_1030_);
lean_dec_ref(v___y_1029_);
lean_dec(v___y_1028_);
lean_dec_ref(v___y_1027_);
lean_dec(v___y_1026_);
lean_dec_ref(v___y_1025_);
if (lean_obj_tag(v___x_1081_) == 0)
{
lean_object* v_a_1082_; lean_object* v___x_1084_; uint8_t v_isShared_1085_; uint8_t v_isSharedCheck_1094_; 
v_a_1082_ = lean_ctor_get(v___x_1081_, 0);
v_isSharedCheck_1094_ = !lean_is_exclusive(v___x_1081_);
if (v_isSharedCheck_1094_ == 0)
{
v___x_1084_ = v___x_1081_;
v_isShared_1085_ = v_isSharedCheck_1094_;
goto v_resetjp_1083_;
}
else
{
lean_inc(v_a_1082_);
lean_dec(v___x_1081_);
v___x_1084_ = lean_box(0);
v_isShared_1085_ = v_isSharedCheck_1094_;
goto v_resetjp_1083_;
}
v_resetjp_1083_:
{
uint8_t v___y_1087_; 
if (v_contextDependent_1055_ == 0)
{
v___y_1087_ = v_contextDependent_1077_;
goto v___jp_1086_;
}
else
{
v___y_1087_ = v_contextDependent_1055_;
goto v___jp_1086_;
}
v___jp_1086_:
{
lean_object* v___x_1089_; 
if (v_isShared_1080_ == 0)
{
lean_ctor_set(v___x_1079_, 1, v_a_1082_);
v___x_1089_ = v___x_1079_;
goto v_reusejp_1088_;
}
else
{
lean_object* v_reuseFailAlloc_1093_; 
v_reuseFailAlloc_1093_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1093_, 0, v_e_x27_1074_);
lean_ctor_set(v_reuseFailAlloc_1093_, 1, v_a_1082_);
lean_ctor_set_uint8(v_reuseFailAlloc_1093_, sizeof(void*)*2, v_done_1076_);
v___x_1089_ = v_reuseFailAlloc_1093_;
goto v_reusejp_1088_;
}
v_reusejp_1088_:
{
lean_object* v___x_1091_; 
lean_ctor_set_uint8(v___x_1089_, sizeof(void*)*2 + 1, v___y_1087_);
if (v_isShared_1085_ == 0)
{
lean_ctor_set(v___x_1084_, 0, v___x_1089_);
v___x_1091_ = v___x_1084_;
goto v_reusejp_1090_;
}
else
{
lean_object* v_reuseFailAlloc_1092_; 
v_reuseFailAlloc_1092_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1092_, 0, v___x_1089_);
v___x_1091_ = v_reuseFailAlloc_1092_;
goto v_reusejp_1090_;
}
v_reusejp_1090_:
{
return v___x_1091_;
}
}
}
}
}
else
{
lean_object* v_a_1095_; lean_object* v___x_1097_; uint8_t v_isShared_1098_; uint8_t v_isSharedCheck_1102_; 
lean_del_object(v___x_1079_);
lean_dec_ref(v_e_x27_1074_);
v_a_1095_ = lean_ctor_get(v___x_1081_, 0);
v_isSharedCheck_1102_ = !lean_is_exclusive(v___x_1081_);
if (v_isSharedCheck_1102_ == 0)
{
v___x_1097_ = v___x_1081_;
v_isShared_1098_ = v_isSharedCheck_1102_;
goto v_resetjp_1096_;
}
else
{
lean_inc(v_a_1095_);
lean_dec(v___x_1081_);
v___x_1097_ = lean_box(0);
v_isShared_1098_ = v_isSharedCheck_1102_;
goto v_resetjp_1096_;
}
v_resetjp_1096_:
{
lean_object* v___x_1100_; 
if (v_isShared_1098_ == 0)
{
v___x_1100_ = v___x_1097_;
goto v_reusejp_1099_;
}
else
{
lean_object* v_reuseFailAlloc_1101_; 
v_reuseFailAlloc_1101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1101_, 0, v_a_1095_);
v___x_1100_ = v_reuseFailAlloc_1101_;
goto v_reusejp_1099_;
}
v_reusejp_1099_:
{
return v___x_1100_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_1057_);
lean_dec_ref(v_proof_1054_);
lean_dec_ref(v_e_x27_1053_);
lean_dec(v___y_1030_);
lean_dec_ref(v___y_1029_);
lean_dec(v___y_1028_);
lean_dec_ref(v___y_1027_);
lean_dec(v___y_1026_);
lean_dec_ref(v___y_1025_);
lean_dec_ref(v___y_1021_);
return v___x_1059_;
}
}
}
else
{
lean_dec_ref_known(v_a_1033_, 2);
lean_dec(v___y_1030_);
lean_dec_ref(v___y_1029_);
lean_dec(v___y_1028_);
lean_dec_ref(v___y_1027_);
lean_dec(v___y_1026_);
lean_dec_ref(v___y_1025_);
lean_dec(v___y_1024_);
lean_dec_ref(v___y_1023_);
lean_dec(v___y_1022_);
lean_dec_ref(v___y_1021_);
lean_dec_ref(v___f_1020_);
return v___x_1032_;
}
}
}
else
{
lean_dec(v___y_1030_);
lean_dec_ref(v___y_1029_);
lean_dec(v___y_1028_);
lean_dec_ref(v___y_1027_);
lean_dec(v___y_1026_);
lean_dec_ref(v___y_1025_);
lean_dec(v___y_1024_);
lean_dec_ref(v___y_1023_);
lean_dec(v___y_1022_);
lean_dec_ref(v___y_1021_);
lean_dec_ref(v___f_1020_);
return v___x_1032_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_addIntToBitVecLemmas___lam__2___boxed(lean_object* v_pre_1106_, lean_object* v___f_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_){
_start:
{
lean_object* v_res_1119_; 
v_res_1119_ = l_Lean_Meta_Tactic_BVDecide_Normalize_addIntToBitVecLemmas___lam__2(v_pre_1106_, v___f_1107_, v___y_1108_, v___y_1109_, v___y_1110_, v___y_1111_, v___y_1112_, v___y_1113_, v___y_1114_, v___y_1115_, v___y_1116_, v___y_1117_);
return v_res_1119_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_addIntToBitVecLemmas(lean_object* v_goal_1120_, lean_object* v_methods_1121_, lean_object* v_a_1122_, lean_object* v_a_1123_, lean_object* v_a_1124_, lean_object* v_a_1125_, lean_object* v_a_1126_, lean_object* v_a_1127_, lean_object* v_a_1128_, lean_object* v_a_1129_, lean_object* v_a_1130_, lean_object* v_a_1131_, lean_object* v_a_1132_){
_start:
{
lean_object* v___x_1134_; lean_object* v___x_1135_; 
v___x_1134_ = l_Lean_Meta_Tactic_BVDecide_symIntToBitVecExt;
v___x_1135_ = l_Lean_Meta_Sym_Simp_SymSimpExtension_getTheorems___redArg(v___x_1134_, v_a_1132_);
if (lean_obj_tag(v___x_1135_) == 0)
{
lean_object* v_a_1136_; lean_object* v___x_1137_; 
v_a_1136_ = lean_ctor_get(v___x_1135_, 0);
lean_inc(v_a_1136_);
lean_dec_ref_known(v___x_1135_, 1);
v___x_1137_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_addIntToBitVecLemmas_findNumBitsEq(v_goal_1120_, v_a_1122_, v_a_1123_, v_a_1124_, v_a_1125_, v_a_1126_, v_a_1127_, v_a_1128_, v_a_1129_, v_a_1130_, v_a_1131_, v_a_1132_);
if (lean_obj_tag(v___x_1137_) == 0)
{
lean_object* v_a_1138_; lean_object* v___x_1140_; uint8_t v_isShared_1141_; uint8_t v_isSharedCheck_1157_; 
v_a_1138_ = lean_ctor_get(v___x_1137_, 0);
v_isSharedCheck_1157_ = !lean_is_exclusive(v___x_1137_);
if (v_isSharedCheck_1157_ == 0)
{
v___x_1140_ = v___x_1137_;
v_isShared_1141_ = v_isSharedCheck_1157_;
goto v_resetjp_1139_;
}
else
{
lean_inc(v_a_1138_);
lean_dec(v___x_1137_);
v___x_1140_ = lean_box(0);
v_isShared_1141_ = v_isSharedCheck_1157_;
goto v_resetjp_1139_;
}
v_resetjp_1139_:
{
lean_object* v_pre_1142_; lean_object* v_post_1143_; lean_object* v___x_1145_; uint8_t v_isShared_1146_; uint8_t v_isSharedCheck_1156_; 
v_pre_1142_ = lean_ctor_get(v_methods_1121_, 0);
v_post_1143_ = lean_ctor_get(v_methods_1121_, 1);
v_isSharedCheck_1156_ = !lean_is_exclusive(v_methods_1121_);
if (v_isSharedCheck_1156_ == 0)
{
v___x_1145_ = v_methods_1121_;
v_isShared_1146_ = v_isSharedCheck_1156_;
goto v_resetjp_1144_;
}
else
{
lean_inc(v_post_1143_);
lean_inc(v_pre_1142_);
lean_dec(v_methods_1121_);
v___x_1145_ = lean_box(0);
v_isShared_1146_ = v_isSharedCheck_1156_;
goto v_resetjp_1144_;
}
v_resetjp_1144_:
{
lean_object* v___y_1147_; lean_object* v___f_1148_; lean_object* v___f_1149_; lean_object* v___x_1151_; 
v___y_1147_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_addIntToBitVecLemmas___lam__0___boxed), 12, 1);
lean_closure_set(v___y_1147_, 0, v_a_1138_);
v___f_1148_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_addIntToBitVecLemmas___lam__1___boxed), 14, 2);
lean_closure_set(v___f_1148_, 0, v_a_1136_);
lean_closure_set(v___f_1148_, 1, v___y_1147_);
v___f_1149_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_addIntToBitVecLemmas___lam__2___boxed), 13, 2);
lean_closure_set(v___f_1149_, 0, v_pre_1142_);
lean_closure_set(v___f_1149_, 1, v___f_1148_);
if (v_isShared_1146_ == 0)
{
lean_ctor_set(v___x_1145_, 0, v___f_1149_);
v___x_1151_ = v___x_1145_;
goto v_reusejp_1150_;
}
else
{
lean_object* v_reuseFailAlloc_1155_; 
v_reuseFailAlloc_1155_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1155_, 0, v___f_1149_);
lean_ctor_set(v_reuseFailAlloc_1155_, 1, v_post_1143_);
v___x_1151_ = v_reuseFailAlloc_1155_;
goto v_reusejp_1150_;
}
v_reusejp_1150_:
{
lean_object* v___x_1153_; 
if (v_isShared_1141_ == 0)
{
lean_ctor_set(v___x_1140_, 0, v___x_1151_);
v___x_1153_ = v___x_1140_;
goto v_reusejp_1152_;
}
else
{
lean_object* v_reuseFailAlloc_1154_; 
v_reuseFailAlloc_1154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1154_, 0, v___x_1151_);
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
}
else
{
lean_object* v_a_1158_; lean_object* v___x_1160_; uint8_t v_isShared_1161_; uint8_t v_isSharedCheck_1165_; 
lean_dec(v_a_1136_);
lean_dec_ref(v_methods_1121_);
v_a_1158_ = lean_ctor_get(v___x_1137_, 0);
v_isSharedCheck_1165_ = !lean_is_exclusive(v___x_1137_);
if (v_isSharedCheck_1165_ == 0)
{
v___x_1160_ = v___x_1137_;
v_isShared_1161_ = v_isSharedCheck_1165_;
goto v_resetjp_1159_;
}
else
{
lean_inc(v_a_1158_);
lean_dec(v___x_1137_);
v___x_1160_ = lean_box(0);
v_isShared_1161_ = v_isSharedCheck_1165_;
goto v_resetjp_1159_;
}
v_resetjp_1159_:
{
lean_object* v___x_1163_; 
if (v_isShared_1161_ == 0)
{
v___x_1163_ = v___x_1160_;
goto v_reusejp_1162_;
}
else
{
lean_object* v_reuseFailAlloc_1164_; 
v_reuseFailAlloc_1164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1164_, 0, v_a_1158_);
v___x_1163_ = v_reuseFailAlloc_1164_;
goto v_reusejp_1162_;
}
v_reusejp_1162_:
{
return v___x_1163_;
}
}
}
}
else
{
lean_object* v_a_1166_; lean_object* v___x_1168_; uint8_t v_isShared_1169_; uint8_t v_isSharedCheck_1173_; 
lean_dec_ref(v_methods_1121_);
lean_dec(v_goal_1120_);
v_a_1166_ = lean_ctor_get(v___x_1135_, 0);
v_isSharedCheck_1173_ = !lean_is_exclusive(v___x_1135_);
if (v_isSharedCheck_1173_ == 0)
{
v___x_1168_ = v___x_1135_;
v_isShared_1169_ = v_isSharedCheck_1173_;
goto v_resetjp_1167_;
}
else
{
lean_inc(v_a_1166_);
lean_dec(v___x_1135_);
v___x_1168_ = lean_box(0);
v_isShared_1169_ = v_isSharedCheck_1173_;
goto v_resetjp_1167_;
}
v_resetjp_1167_:
{
lean_object* v___x_1171_; 
if (v_isShared_1169_ == 0)
{
v___x_1171_ = v___x_1168_;
goto v_reusejp_1170_;
}
else
{
lean_object* v_reuseFailAlloc_1172_; 
v_reuseFailAlloc_1172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1172_, 0, v_a_1166_);
v___x_1171_ = v_reuseFailAlloc_1172_;
goto v_reusejp_1170_;
}
v_reusejp_1170_:
{
return v___x_1171_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_addIntToBitVecLemmas___boxed(lean_object* v_goal_1174_, lean_object* v_methods_1175_, lean_object* v_a_1176_, lean_object* v_a_1177_, lean_object* v_a_1178_, lean_object* v_a_1179_, lean_object* v_a_1180_, lean_object* v_a_1181_, lean_object* v_a_1182_, lean_object* v_a_1183_, lean_object* v_a_1184_, lean_object* v_a_1185_, lean_object* v_a_1186_, lean_object* v_a_1187_){
_start:
{
lean_object* v_res_1188_; 
v_res_1188_ = l_Lean_Meta_Tactic_BVDecide_Normalize_addIntToBitVecLemmas(v_goal_1174_, v_methods_1175_, v_a_1176_, v_a_1177_, v_a_1178_, v_a_1179_, v_a_1180_, v_a_1181_, v_a_1182_, v_a_1183_, v_a_1184_, v_a_1185_, v_a_1186_);
lean_dec(v_a_1186_);
lean_dec_ref(v_a_1185_);
lean_dec(v_a_1184_);
lean_dec_ref(v_a_1183_);
lean_dec(v_a_1182_);
lean_dec_ref(v_a_1181_);
lean_dec(v_a_1180_);
lean_dec_ref(v_a_1179_);
lean_dec(v_a_1178_);
lean_dec(v_a_1177_);
lean_dec_ref(v_a_1176_);
return v_res_1188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0(lean_object* v_x_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_){
_start:
{
lean_object* v___x_1200_; lean_object* v___x_1201_; 
v___x_1200_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_toBitVecOfNatProc_runProc___redArg___closed__4));
v___x_1201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1201_, 0, v___x_1200_);
return v___x_1201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___boxed(lean_object* v_x_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_){
_start:
{
lean_object* v_res_1213_; 
v_res_1213_ = l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0(v_x_1202_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_, v___y_1209_, v___y_1210_, v___y_1211_);
lean_dec(v___y_1211_);
lean_dec_ref(v___y_1210_);
lean_dec(v___y_1209_);
lean_dec_ref(v___y_1208_);
lean_dec(v___y_1207_);
lean_dec_ref(v___y_1206_);
lean_dec(v___y_1205_);
lean_dec_ref(v___y_1204_);
lean_dec(v___y_1203_);
lean_dec_ref(v_x_1202_);
return v_res_1213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__1(lean_object* v___f_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_){
_start:
{
lean_object* v_config_1227_; lean_object* v___x_1228_; lean_object* v_target_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; 
v_config_1227_ = lean_ctor_get(v___y_1215_, 0);
v___x_1228_ = lean_st_ref_get(v___y_1216_);
v_target_1229_ = lean_ctor_get(v___x_1228_, 4);
lean_inc_ref(v_target_1229_);
lean_dec(v___x_1228_);
v___x_1230_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Target_mvarId(v_target_1229_);
lean_dec_ref(v_target_1229_);
lean_inc_ref(v___f_1214_);
v___x_1231_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1231_, 0, v___f_1214_);
lean_ctor_set(v___x_1231_, 1, v___f_1214_);
lean_inc(v___x_1230_);
v___x_1232_ = l_Lean_Meta_Tactic_BVDecide_Normalize_addIntToBitVecLemmas(v___x_1230_, v___x_1231_, v___y_1215_, v___y_1216_, v___y_1217_, v___y_1218_, v___y_1219_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_);
if (lean_obj_tag(v___x_1232_) == 0)
{
lean_object* v_a_1233_; lean_object* v_maxSteps_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; 
v_a_1233_ = lean_ctor_get(v___x_1232_, 0);
lean_inc(v_a_1233_);
lean_dec_ref_known(v___x_1232_, 1);
v_maxSteps_1234_ = lean_ctor_get(v_config_1227_, 1);
v___x_1235_ = lean_unsigned_to_nat(2u);
lean_inc(v_maxSteps_1234_);
v___x_1236_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1236_, 0, v_maxSteps_1234_);
lean_ctor_set(v___x_1236_, 1, v___x_1235_);
v___x_1237_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps___boxed), 14, 2);
lean_closure_set(v___x_1237_, 0, v_a_1233_);
lean_closure_set(v___x_1237_, 1, v___x_1236_);
v___x_1238_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_addIntToBitVecLemmas_findNumBitsEq_spec__1___redArg(v___x_1230_, v___x_1237_, v___y_1215_, v___y_1216_, v___y_1217_, v___y_1218_, v___y_1219_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_);
return v___x_1238_;
}
else
{
lean_object* v_a_1239_; lean_object* v___x_1241_; uint8_t v_isShared_1242_; uint8_t v_isSharedCheck_1246_; 
lean_dec(v___x_1230_);
v_a_1239_ = lean_ctor_get(v___x_1232_, 0);
v_isSharedCheck_1246_ = !lean_is_exclusive(v___x_1232_);
if (v_isSharedCheck_1246_ == 0)
{
v___x_1241_ = v___x_1232_;
v_isShared_1242_ = v_isSharedCheck_1246_;
goto v_resetjp_1240_;
}
else
{
lean_inc(v_a_1239_);
lean_dec(v___x_1232_);
v___x_1241_ = lean_box(0);
v_isShared_1242_ = v_isSharedCheck_1246_;
goto v_resetjp_1240_;
}
v_resetjp_1240_:
{
lean_object* v___x_1244_; 
if (v_isShared_1242_ == 0)
{
v___x_1244_ = v___x_1241_;
goto v_reusejp_1243_;
}
else
{
lean_object* v_reuseFailAlloc_1245_; 
v_reuseFailAlloc_1245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1245_, 0, v_a_1239_);
v___x_1244_ = v_reuseFailAlloc_1245_;
goto v_reusejp_1243_;
}
v_reusejp_1243_:
{
return v___x_1244_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__1___boxed(lean_object* v___f_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_){
_start:
{
lean_object* v_res_1260_; 
v_res_1260_ = l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__1(v___f_1247_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_, v___y_1257_, v___y_1258_);
lean_dec(v___y_1258_);
lean_dec_ref(v___y_1257_);
lean_dec(v___y_1256_);
lean_dec_ref(v___y_1255_);
lean_dec(v___y_1254_);
lean_dec_ref(v___y_1253_);
lean_dec(v___y_1252_);
lean_dec_ref(v___y_1251_);
lean_dec(v___y_1250_);
lean_dec(v___y_1249_);
lean_dec_ref(v___y_1248_);
return v_res_1260_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_Rewrite(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_InstantiateMVarsS(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_LitValues(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_UInt_IntToBitVec(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_SInt_IntToBitVec(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Simp_Rewrite(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_InstantiateMVarsS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_LitValues(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_UInt_IntToBitVec(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_SInt_IntToBitVec(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_BVDecide_Normalize_Basic(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_Rewrite(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_InstantiateMVarsS(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_LitValues(uint8_t builtin);
lean_object* initialize_Init_Data_UInt_IntToBitVec(uint8_t builtin);
lean_object* initialize_Init_Data_SInt_IntToBitVec(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_BVDecide_Normalize_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Simp_Rewrite(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_InstantiateMVarsS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_LitValues(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_UInt_IntToBitVec(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_SInt_IntToBitVec(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec(builtin);
}
#ifdef __cplusplus
}
#endif
