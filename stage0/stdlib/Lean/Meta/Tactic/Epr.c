// Lean compiler output
// Module: Lean.Meta.Tactic.Epr
// Imports: public import Lean.Meta.Basic public import Std.Tactic.BVDecide.Syntax import Lean.Meta.Sym.Simp.NNF import Lean.Meta.Sym.Simp.Prenex import Lean.Meta.Tactic.BVDecide.Normalize.CollectHyps import Lean.Meta.Tactic.BVDecide.Main import Lean.Meta.Tactic.Grind.Main public import Lean.Meta.Tactic.BVDecide.TacticContext import Lean.Meta.Sym.Apply import Lean.Meta.Sym.InferType import Lean.Meta.Sym.Intro import Lean.Meta.Sym.InstantiateMVarsS import Lean.Meta.Sym.SynthInstance
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
lean_object* l_Lean_Meta_Sym_Simp_pullForall___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_simp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_SimpM_run_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
uint8_t l_Lean_LocalDecl_isImplementationDetail(lean_object*);
uint8_t l_Lean_LocalDecl_isLet(lean_object*, uint8_t);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Lean_Meta_Sym_instantiateMVarsS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t l_Lean_instHashableFVarId_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Sym_share1___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_getLevel___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Sym_assertShared(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_toExpr(lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommonInc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_registerInstance___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_synthInstance_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkDefaultParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_GrindM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_sym_simp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_instInhabitedSymM___redArg();
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_mkBackwardRuleFromExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_BackwardRule_apply_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_introN(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getType___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_nnf___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_pullExists___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_minscope___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* lean_find_expr(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_bvDecide(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_collectMVarHyps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkConstS___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkConstS___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkConstS___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkConstS___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__8___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__8___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__5_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__5_spec__6___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__5___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__6_spec__8_spec__10_spec__12___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__6_spec__8_spec__10___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__6_spec__8___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__6___redArg(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__7_spec__11_spec__16___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Nonempty"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__7_spec__11_spec__16___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__7_spec__11_spec__16___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__7_spec__11_spec__16___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__7_spec__11_spec__16___closed__0_value),LEAN_SCALAR_PTR_LITERAL(142, 191, 110, 220, 210, 100, 152, 183)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__7_spec__11_spec__16___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__7_spec__11_spec__16___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__7_spec__11_spec__16___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "intro"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__7_spec__11_spec__16___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__7_spec__11_spec__16___closed__2_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__7_spec__11_spec__16___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__7_spec__11_spec__16___closed__0_value),LEAN_SCALAR_PTR_LITERAL(142, 191, 110, 220, 210, 100, 152, 183)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__7_spec__11_spec__16___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__7_spec__11_spec__16___closed__3_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__7_spec__11_spec__16___closed__2_value),LEAN_SCALAR_PTR_LITERAL(113, 209, 180, 93, 84, 117, 67, 110)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__7_spec__11_spec__16___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__7_spec__11_spec__16___closed__3_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__7_spec__11_spec__16(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__7_spec__11_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__7_spec__11(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__7_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__7_spec__10_spec__14_spec__16(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__7_spec__10_spec__14_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__7_spec__10_spec__14(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__7_spec__10_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__7_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__7_spec__10_spec__13(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__7_spec__10_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__7_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty___closed__0;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty___closed__1;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__5_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__5_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__6_spec__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__6_spec__8_spec__10(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__6_spec__8_spec__10_spec__12(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_nnf___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_nnf___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_nnf___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_nnf___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_nnf___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_nnf_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_nnf_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_nnf___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_nnf___lam__0___boxed, .m_arity = 11, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_nnf___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_nnf___closed__0_value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_nnf___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_Simp_nnf___boxed, .m_arity = 11, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_nnf___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_nnf___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_nnf___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_nnf___closed__1_value),((lean_object*)&l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_nnf___closed__0_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_nnf___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_nnf___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_nnf___boxed__const__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + sizeof(size_t)*1, .m_other = 0, .m_tag = 0}, .m_objs = {(lean_object*)(size_t)(0ULL)}};
LEAN_EXPORT const lean_object* l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_nnf___boxed__const__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_nnf___boxed__const__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_nnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_nnf___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_andFlatten_flattenOne___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "And"};
static const lean_object* l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_andFlatten_flattenOne___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_andFlatten_flattenOne___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_andFlatten_flattenOne___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_andFlatten_flattenOne___closed__0_value),LEAN_SCALAR_PTR_LITERAL(49, 220, 212, 156, 122, 214, 55, 135)}};
static const lean_object* l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_andFlatten_flattenOne___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_andFlatten_flattenOne___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_andFlatten_flattenOne___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "left"};
static const lean_object* l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_andFlatten_flattenOne___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_andFlatten_flattenOne___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_andFlatten_flattenOne___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_andFlatten_flattenOne___closed__0_value),LEAN_SCALAR_PTR_LITERAL(49, 220, 212, 156, 122, 214, 55, 135)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_andFlatten_flattenOne___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_andFlatten_flattenOne___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_andFlatten_flattenOne___closed__2_value),LEAN_SCALAR_PTR_LITERAL(12, 252, 227, 83, 88, 185, 40, 148)}};
static const lean_object* l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_andFlatten_flattenOne___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_andFlatten_flattenOne___closed__3_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_andFlatten_flattenOne___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_andFlatten_flattenOne___closed__4;
static const lean_string_object l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_andFlatten_flattenOne___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "right"};
static const lean_object* l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_andFlatten_flattenOne___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_andFlatten_flattenOne___closed__5_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_andFlatten_flattenOne___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_andFlatten_flattenOne___closed__0_value),LEAN_SCALAR_PTR_LITERAL(49, 220, 212, 156, 122, 214, 55, 135)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_andFlatten_flattenOne___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_andFlatten_flattenOne___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_andFlatten_flattenOne___closed__5_value),LEAN_SCALAR_PTR_LITERAL(18, 204, 165, 192, 253, 41, 237, 145)}};
static const lean_object* l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_andFlatten_flattenOne___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_andFlatten_flattenOne___closed__6_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_andFlatten_flattenOne___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_andFlatten_flattenOne___closed__7;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_andFlatten_flattenOne(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_andFlatten_flattenOne___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_andFlatten_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_andFlatten_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_andFlatten_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_andFlatten_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_andFlatten_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_andFlatten___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_andFlatten___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_andFlatten___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_andFlatten(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_andFlatten___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_prenexWithExists___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_Simp_minscope___boxed, .m_arity = 11, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_prenexWithExists___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_prenexWithExists___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_prenexWithExists___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_prenexWithExists___closed__0_value),((lean_object*)&l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_nnf___closed__0_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_prenexWithExists___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_prenexWithExists___closed__1_value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_prenexWithExists___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_Simp_pullExists___boxed, .m_arity = 11, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_prenexWithExists___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_prenexWithExists___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_prenexWithExists___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_prenexWithExists___closed__2_value),((lean_object*)&l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_nnf___closed__0_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_prenexWithExists___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_prenexWithExists___closed__3_value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_prenexWithExists___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_Simp_pullForall___boxed, .m_arity = 11, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_prenexWithExists___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_prenexWithExists___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_prenexWithExists___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_prenexWithExists___closed__4_value),((lean_object*)&l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_nnf___closed__0_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_prenexWithExists___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_prenexWithExists___closed__5_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_prenexWithExists(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_prenexWithExists___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_prenexWithoutExists(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_prenexWithoutExists___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_skolemize_skolemStep_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_skolemize_skolemStep_spec__0___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_skolemize_skolemStep_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_skolemize_skolemStep_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_skolemize_skolemStep___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_skolemize_skolemStep___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_skolemize_skolemStep___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_skolemize_skolemStep___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_skolemize_skolemStep___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Lean.Meta.Tactic.Epr"};
static const lean_object* l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_skolemize_skolemStep___lam__2___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_skolemize_skolemStep___lam__2___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_skolemize_skolemStep___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 74, .m_capacity = 74, .m_length = 73, .m_data = "_private.Lean.Meta.Tactic.Epr.0.Lean.Meta.Tactic.Epr.skolemize.skolemStep"};
static const lean_object* l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_skolemize_skolemStep___lam__2___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_skolemize_skolemStep___lam__2___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_skolemize_skolemStep___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_skolemize_skolemStep___lam__2___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_skolemize_skolemStep___lam__2___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_skolemize_skolemStep___lam__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_skolemize_skolemStep___lam__2___closed__3;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_skolemize_skolemStep___lam__2___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_skolemize_skolemStep___lam__2___closed__4;
static const lean_string_object l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_skolemize_skolemStep___lam__2___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Exists"};
static const lean_object* l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_skolemize_skolemStep___lam__2___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_skolemize_skolemStep___lam__2___closed__5_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_skolemize_skolemStep___lam__2___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_skolemize_skolemStep___lam__2___closed__5_value),LEAN_SCALAR_PTR_LITERAL(65, 29, 48, 135, 199, 176, 149, 70)}};
static const lean_object* l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_skolemize_skolemStep___lam__2___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_skolemize_skolemStep___lam__2___closed__6_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_skolemize_skolemStep___lam__2___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "elim"};
static const lean_object* l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_skolemize_skolemStep___lam__2___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_skolemize_skolemStep___lam__2___closed__7_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_skolemize_skolemStep___lam__2___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_skolemize_skolemStep___lam__2___closed__5_value),LEAN_SCALAR_PTR_LITERAL(65, 29, 48, 135, 199, 176, 149, 70)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_skolemize_skolemStep___lam__2___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_skolemize_skolemStep___lam__2___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_skolemize_skolemStep___lam__2___closed__7_value),LEAN_SCALAR_PTR_LITERAL(233, 192, 106, 76, 156, 25, 23, 244)}};
static const lean_object* l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_skolemize_skolemStep___lam__2___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_skolemize_skolemStep___lam__2___closed__8_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_skolemize_skolemStep___lam__2___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "False"};
static const lean_object* l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_skolemize_skolemStep___lam__2___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_skolemize_skolemStep___lam__2___closed__9_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_skolemize_skolemStep___lam__2___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_skolemize_skolemStep___lam__2___closed__9_value),LEAN_SCALAR_PTR_LITERAL(227, 122, 176, 177, 50, 175, 152, 12)}};
static const lean_object* l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_skolemize_skolemStep___lam__2___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_skolemize_skolemStep___lam__2___closed__10_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_skolemize_skolemStep___lam__2___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_skolemize_skolemStep___lam__2___closed__11;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_skolemize_skolemStep___lam__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_skolemize_skolemStep___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_skolemize_skolemStep___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_skolemize_skolemStep___lam__0___boxed, .m_arity = 8, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_skolemize_skolemStep___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_skolemize_skolemStep___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_skolemize_skolemStep(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_skolemize_skolemStep___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_skolemize_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_skolemize_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_skolemize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_skolemize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_skolemize_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_skolemize_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_epr_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_epr_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_epr_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_epr_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_epr_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_epr_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_epr_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_epr_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_epr_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_epr_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_epr_spec__1___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_epr_spec__1___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_epr_spec__1___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_epr_spec__1___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_epr_spec__1___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_epr_spec__1___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_epr_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_epr_spec__1___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_epr_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_epr_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_epr_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_epr_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_epr___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_epr___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_epr___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_epr___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_epr___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_epr___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Tactic_epr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*18 + 40, .m_other = 18, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)(((size_t)(9) << 1) | 1)),((lean_object*)(((size_t)(5) << 1) | 1)),((lean_object*)(((size_t)(8) << 1) | 1)),((lean_object*)(((size_t)(8) << 1) | 1)),((lean_object*)(((size_t)(1000) << 1) | 1)),((lean_object*)(((size_t)(1000) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(100000) << 1) | 1)),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)(((size_t)(10000) << 1) | 1)),((lean_object*)(((size_t)(8) << 1) | 1)),((lean_object*)(((size_t)(16) << 1) | 1)),((lean_object*)(((size_t)(1000) << 1) | 1)),((lean_object*)(((size_t)(1048576) << 1) | 1)),((lean_object*)(((size_t)(10) << 1) | 1)),((lean_object*)(((size_t)(50) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 1, 1, 1),LEAN_SCALAR_PTR_LITERAL(0, 0, 1, 0, 1, 1, 1, 0),LEAN_SCALAR_PTR_LITERAL(1, 0, 1, 1, 1, 0, 1, 1),LEAN_SCALAR_PTR_LITERAL(1, 1, 1, 1, 1, 1, 1, 0),LEAN_SCALAR_PTR_LITERAL(1, 1, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Meta_Tactic_epr___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_epr___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_epr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_epr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__1___redArg(lean_object* v_fvarId_1_, lean_object* v___y_2_){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; 
v___x_4_ = l_Lean_Expr_fvar___override(v_fvarId_1_);
v___x_5_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_4_, v___y_2_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__1___redArg___boxed(lean_object* v_fvarId_6_, lean_object* v___y_7_, lean_object* v___y_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__1___redArg(v_fvarId_6_, v___y_7_);
lean_dec(v___y_7_);
return v_res_9_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__1(lean_object* v_fvarId_10_, lean_object* v___y_11_, lean_object* v___y_12_, lean_object* v___y_13_, lean_object* v___y_14_, lean_object* v___y_15_, lean_object* v___y_16_){
_start:
{
lean_object* v___x_18_; 
v___x_18_ = l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__1___redArg(v_fvarId_10_, v___y_12_);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__1___boxed(lean_object* v_fvarId_19_, lean_object* v___y_20_, lean_object* v___y_21_, lean_object* v___y_22_, lean_object* v___y_23_, lean_object* v___y_24_, lean_object* v___y_25_, lean_object* v___y_26_){
_start:
{
lean_object* v_res_27_; 
v_res_27_ = l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__1(v_fvarId_19_, v___y_20_, v___y_21_, v___y_22_, v___y_23_, v___y_24_, v___y_25_);
lean_dec(v___y_25_);
lean_dec_ref(v___y_24_);
lean_dec(v___y_23_);
lean_dec_ref(v___y_22_);
lean_dec(v___y_21_);
lean_dec_ref(v___y_20_);
return v_res_27_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkConstS___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__2___redArg(lean_object* v_declName_28_, lean_object* v_us_29_, lean_object* v___y_30_){
_start:
{
lean_object* v___x_32_; lean_object* v___x_33_; 
v___x_32_ = l_Lean_Expr_const___override(v_declName_28_, v_us_29_);
v___x_33_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_32_, v___y_30_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkConstS___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__2___redArg___boxed(lean_object* v_declName_34_, lean_object* v_us_35_, lean_object* v___y_36_, lean_object* v___y_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = l_Lean_Meta_Sym_Internal_mkConstS___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__2___redArg(v_declName_34_, v_us_35_, v___y_36_);
lean_dec(v___y_36_);
return v_res_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkConstS___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__2(lean_object* v_declName_39_, lean_object* v_us_40_, lean_object* v___y_41_, lean_object* v___y_42_, lean_object* v___y_43_, lean_object* v___y_44_, lean_object* v___y_45_, lean_object* v___y_46_){
_start:
{
lean_object* v___x_48_; 
v___x_48_ = l_Lean_Meta_Sym_Internal_mkConstS___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__2___redArg(v_declName_39_, v_us_40_, v___y_42_);
return v___x_48_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkConstS___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__2___boxed(lean_object* v_declName_49_, lean_object* v_us_50_, lean_object* v___y_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_, lean_object* v___y_55_, lean_object* v___y_56_, lean_object* v___y_57_){
_start:
{
lean_object* v_res_58_; 
v_res_58_ = l_Lean_Meta_Sym_Internal_mkConstS___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__2(v_declName_49_, v_us_50_, v___y_51_, v___y_52_, v___y_53_, v___y_54_, v___y_55_, v___y_56_);
lean_dec(v___y_56_);
lean_dec_ref(v___y_55_);
lean_dec(v___y_54_);
lean_dec_ref(v___y_53_);
lean_dec(v___y_52_);
lean_dec_ref(v___y_51_);
return v_res_58_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__3(lean_object* v_f_59_, lean_object* v_a_60_, lean_object* v___y_61_, lean_object* v___y_62_, lean_object* v___y_63_, lean_object* v___y_64_, lean_object* v___y_65_, lean_object* v___y_66_){
_start:
{
lean_object* v___y_69_; lean_object* v___x_72_; uint8_t v_debug_73_; 
v___x_72_ = lean_st_ref_get(v___y_62_);
v_debug_73_ = lean_ctor_get_uint8(v___x_72_, sizeof(void*)*13);
lean_dec(v___x_72_);
if (v_debug_73_ == 0)
{
v___y_69_ = v___y_62_;
goto v___jp_68_;
}
else
{
lean_object* v___x_74_; 
v___x_74_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_f_59_, v___y_61_, v___y_62_, v___y_63_, v___y_64_, v___y_65_, v___y_66_);
if (lean_obj_tag(v___x_74_) == 0)
{
lean_object* v___x_75_; 
lean_dec_ref_known(v___x_74_, 1);
v___x_75_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_a_60_, v___y_61_, v___y_62_, v___y_63_, v___y_64_, v___y_65_, v___y_66_);
if (lean_obj_tag(v___x_75_) == 0)
{
lean_dec_ref_known(v___x_75_, 1);
v___y_69_ = v___y_62_;
goto v___jp_68_;
}
else
{
lean_object* v_a_76_; lean_object* v___x_78_; uint8_t v_isShared_79_; uint8_t v_isSharedCheck_83_; 
lean_dec_ref(v_a_60_);
lean_dec_ref(v_f_59_);
v_a_76_ = lean_ctor_get(v___x_75_, 0);
v_isSharedCheck_83_ = !lean_is_exclusive(v___x_75_);
if (v_isSharedCheck_83_ == 0)
{
v___x_78_ = v___x_75_;
v_isShared_79_ = v_isSharedCheck_83_;
goto v_resetjp_77_;
}
else
{
lean_inc(v_a_76_);
lean_dec(v___x_75_);
v___x_78_ = lean_box(0);
v_isShared_79_ = v_isSharedCheck_83_;
goto v_resetjp_77_;
}
v_resetjp_77_:
{
lean_object* v___x_81_; 
if (v_isShared_79_ == 0)
{
v___x_81_ = v___x_78_;
goto v_reusejp_80_;
}
else
{
lean_object* v_reuseFailAlloc_82_; 
v_reuseFailAlloc_82_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_82_, 0, v_a_76_);
v___x_81_ = v_reuseFailAlloc_82_;
goto v_reusejp_80_;
}
v_reusejp_80_:
{
return v___x_81_;
}
}
}
}
else
{
lean_object* v_a_84_; lean_object* v___x_86_; uint8_t v_isShared_87_; uint8_t v_isSharedCheck_91_; 
lean_dec_ref(v_a_60_);
lean_dec_ref(v_f_59_);
v_a_84_ = lean_ctor_get(v___x_74_, 0);
v_isSharedCheck_91_ = !lean_is_exclusive(v___x_74_);
if (v_isSharedCheck_91_ == 0)
{
v___x_86_ = v___x_74_;
v_isShared_87_ = v_isSharedCheck_91_;
goto v_resetjp_85_;
}
else
{
lean_inc(v_a_84_);
lean_dec(v___x_74_);
v___x_86_ = lean_box(0);
v_isShared_87_ = v_isSharedCheck_91_;
goto v_resetjp_85_;
}
v_resetjp_85_:
{
lean_object* v___x_89_; 
if (v_isShared_87_ == 0)
{
v___x_89_ = v___x_86_;
goto v_reusejp_88_;
}
else
{
lean_object* v_reuseFailAlloc_90_; 
v_reuseFailAlloc_90_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_90_, 0, v_a_84_);
v___x_89_ = v_reuseFailAlloc_90_;
goto v_reusejp_88_;
}
v_reusejp_88_:
{
return v___x_89_;
}
}
}
}
v___jp_68_:
{
lean_object* v___x_70_; lean_object* v___x_71_; 
v___x_70_ = l_Lean_Expr_app___override(v_f_59_, v_a_60_);
v___x_71_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_70_, v___y_69_);
return v___x_71_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__3___boxed(lean_object* v_f_92_, lean_object* v_a_93_, lean_object* v___y_94_, lean_object* v___y_95_, lean_object* v___y_96_, lean_object* v___y_97_, lean_object* v___y_98_, lean_object* v___y_99_, lean_object* v___y_100_){
_start:
{
lean_object* v_res_101_; 
v_res_101_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__3(v_f_92_, v_a_93_, v___y_94_, v___y_95_, v___y_96_, v___y_97_, v___y_98_, v___y_99_);
lean_dec(v___y_99_);
lean_dec_ref(v___y_98_);
lean_dec(v___y_97_);
lean_dec_ref(v___y_96_);
lean_dec(v___y_95_);
lean_dec_ref(v___y_94_);
return v_res_101_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__8___redArg___lam__0(lean_object* v_x_102_, lean_object* v___y_103_, lean_object* v___y_104_, lean_object* v___y_105_, lean_object* v___y_106_, lean_object* v___y_107_, lean_object* v___y_108_){
_start:
{
lean_object* v___x_110_; 
lean_inc(v___y_104_);
lean_inc_ref(v___y_103_);
v___x_110_ = lean_apply_7(v_x_102_, v___y_103_, v___y_104_, v___y_105_, v___y_106_, v___y_107_, v___y_108_, lean_box(0));
return v___x_110_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__8___redArg___lam__0___boxed(lean_object* v_x_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_, lean_object* v___y_115_, lean_object* v___y_116_, lean_object* v___y_117_, lean_object* v___y_118_){
_start:
{
lean_object* v_res_119_; 
v_res_119_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__8___redArg___lam__0(v_x_111_, v___y_112_, v___y_113_, v___y_114_, v___y_115_, v___y_116_, v___y_117_);
lean_dec(v___y_113_);
lean_dec_ref(v___y_112_);
return v_res_119_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__8___redArg(lean_object* v_mvarId_120_, lean_object* v_x_121_, lean_object* v___y_122_, lean_object* v___y_123_, lean_object* v___y_124_, lean_object* v___y_125_, lean_object* v___y_126_, lean_object* v___y_127_){
_start:
{
lean_object* v___f_129_; lean_object* v___x_130_; 
lean_inc(v___y_123_);
lean_inc_ref(v___y_122_);
v___f_129_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__8___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_129_, 0, v_x_121_);
lean_closure_set(v___f_129_, 1, v___y_122_);
lean_closure_set(v___f_129_, 2, v___y_123_);
v___x_130_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_120_, v___f_129_, v___y_124_, v___y_125_, v___y_126_, v___y_127_);
if (lean_obj_tag(v___x_130_) == 0)
{
return v___x_130_;
}
else
{
lean_object* v_a_131_; lean_object* v___x_133_; uint8_t v_isShared_134_; uint8_t v_isSharedCheck_138_; 
v_a_131_ = lean_ctor_get(v___x_130_, 0);
v_isSharedCheck_138_ = !lean_is_exclusive(v___x_130_);
if (v_isSharedCheck_138_ == 0)
{
v___x_133_ = v___x_130_;
v_isShared_134_ = v_isSharedCheck_138_;
goto v_resetjp_132_;
}
else
{
lean_inc(v_a_131_);
lean_dec(v___x_130_);
v___x_133_ = lean_box(0);
v_isShared_134_ = v_isSharedCheck_138_;
goto v_resetjp_132_;
}
v_resetjp_132_:
{
lean_object* v___x_136_; 
if (v_isShared_134_ == 0)
{
v___x_136_ = v___x_133_;
goto v_reusejp_135_;
}
else
{
lean_object* v_reuseFailAlloc_137_; 
v_reuseFailAlloc_137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_137_, 0, v_a_131_);
v___x_136_ = v_reuseFailAlloc_137_;
goto v_reusejp_135_;
}
v_reusejp_135_:
{
return v___x_136_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__8___redArg___boxed(lean_object* v_mvarId_139_, lean_object* v_x_140_, lean_object* v___y_141_, lean_object* v___y_142_, lean_object* v___y_143_, lean_object* v___y_144_, lean_object* v___y_145_, lean_object* v___y_146_, lean_object* v___y_147_){
_start:
{
lean_object* v_res_148_; 
v_res_148_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__8___redArg(v_mvarId_139_, v_x_140_, v___y_141_, v___y_142_, v___y_143_, v___y_144_, v___y_145_, v___y_146_);
lean_dec(v___y_146_);
lean_dec_ref(v___y_145_);
lean_dec(v___y_144_);
lean_dec_ref(v___y_143_);
lean_dec(v___y_142_);
lean_dec_ref(v___y_141_);
return v_res_148_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__8(lean_object* v_00_u03b1_149_, lean_object* v_mvarId_150_, lean_object* v_x_151_, lean_object* v___y_152_, lean_object* v___y_153_, lean_object* v___y_154_, lean_object* v___y_155_, lean_object* v___y_156_, lean_object* v___y_157_){
_start:
{
lean_object* v___x_159_; 
v___x_159_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__8___redArg(v_mvarId_150_, v_x_151_, v___y_152_, v___y_153_, v___y_154_, v___y_155_, v___y_156_, v___y_157_);
return v___x_159_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__8___boxed(lean_object* v_00_u03b1_160_, lean_object* v_mvarId_161_, lean_object* v_x_162_, lean_object* v___y_163_, lean_object* v___y_164_, lean_object* v___y_165_, lean_object* v___y_166_, lean_object* v___y_167_, lean_object* v___y_168_, lean_object* v___y_169_){
_start:
{
lean_object* v_res_170_; 
v_res_170_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__8(v_00_u03b1_160_, v_mvarId_161_, v_x_162_, v___y_163_, v___y_164_, v___y_165_, v___y_166_, v___y_167_, v___y_168_);
lean_dec(v___y_168_);
lean_dec_ref(v___y_167_);
lean_dec(v___y_166_);
lean_dec_ref(v___y_165_);
lean_dec(v___y_164_);
lean_dec_ref(v___y_163_);
return v_res_170_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__0_spec__0___redArg(lean_object* v_a_171_, lean_object* v_x_172_){
_start:
{
if (lean_obj_tag(v_x_172_) == 0)
{
uint8_t v___x_173_; 
v___x_173_ = 0;
return v___x_173_;
}
else
{
lean_object* v_key_174_; lean_object* v_tail_175_; uint8_t v___x_176_; 
v_key_174_ = lean_ctor_get(v_x_172_, 0);
v_tail_175_ = lean_ctor_get(v_x_172_, 2);
v___x_176_ = l_Lean_instBEqFVarId_beq(v_key_174_, v_a_171_);
if (v___x_176_ == 0)
{
v_x_172_ = v_tail_175_;
goto _start;
}
else
{
return v___x_176_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__0_spec__0___redArg___boxed(lean_object* v_a_178_, lean_object* v_x_179_){
_start:
{
uint8_t v_res_180_; lean_object* v_r_181_; 
v_res_180_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__0_spec__0___redArg(v_a_178_, v_x_179_);
lean_dec(v_x_179_);
lean_dec(v_a_178_);
v_r_181_ = lean_box(v_res_180_);
return v_r_181_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__0___redArg(lean_object* v_m_182_, lean_object* v_a_183_){
_start:
{
lean_object* v_buckets_184_; lean_object* v___x_185_; uint64_t v___x_186_; uint64_t v___x_187_; uint64_t v___x_188_; uint64_t v_fold_189_; uint64_t v___x_190_; uint64_t v___x_191_; uint64_t v___x_192_; size_t v___x_193_; size_t v___x_194_; size_t v___x_195_; size_t v___x_196_; size_t v___x_197_; lean_object* v___x_198_; uint8_t v___x_199_; 
v_buckets_184_ = lean_ctor_get(v_m_182_, 1);
v___x_185_ = lean_array_get_size(v_buckets_184_);
v___x_186_ = l_Lean_instHashableFVarId_hash(v_a_183_);
v___x_187_ = 32ULL;
v___x_188_ = lean_uint64_shift_right(v___x_186_, v___x_187_);
v_fold_189_ = lean_uint64_xor(v___x_186_, v___x_188_);
v___x_190_ = 16ULL;
v___x_191_ = lean_uint64_shift_right(v_fold_189_, v___x_190_);
v___x_192_ = lean_uint64_xor(v_fold_189_, v___x_191_);
v___x_193_ = lean_uint64_to_usize(v___x_192_);
v___x_194_ = lean_usize_of_nat(v___x_185_);
v___x_195_ = ((size_t)1ULL);
v___x_196_ = lean_usize_sub(v___x_194_, v___x_195_);
v___x_197_ = lean_usize_land(v___x_193_, v___x_196_);
v___x_198_ = lean_array_uget_borrowed(v_buckets_184_, v___x_197_);
v___x_199_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__0_spec__0___redArg(v_a_183_, v___x_198_);
return v___x_199_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__0___redArg___boxed(lean_object* v_m_200_, lean_object* v_a_201_){
_start:
{
uint8_t v_res_202_; lean_object* v_r_203_; 
v_res_202_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__0___redArg(v_m_200_, v_a_201_);
lean_dec(v_a_201_);
lean_dec_ref(v_m_200_);
v_r_203_ = lean_box(v_res_202_);
return v_r_203_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__4(lean_object* v_f_204_, lean_object* v_a_u2081_205_, lean_object* v_a_u2082_206_, lean_object* v___y_207_, lean_object* v___y_208_, lean_object* v___y_209_, lean_object* v___y_210_, lean_object* v___y_211_, lean_object* v___y_212_){
_start:
{
lean_object* v___x_214_; 
v___x_214_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__3(v_f_204_, v_a_u2081_205_, v___y_207_, v___y_208_, v___y_209_, v___y_210_, v___y_211_, v___y_212_);
if (lean_obj_tag(v___x_214_) == 0)
{
lean_object* v_a_215_; lean_object* v___x_216_; 
v_a_215_ = lean_ctor_get(v___x_214_, 0);
lean_inc(v_a_215_);
lean_dec_ref_known(v___x_214_, 1);
v___x_216_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__3(v_a_215_, v_a_u2082_206_, v___y_207_, v___y_208_, v___y_209_, v___y_210_, v___y_211_, v___y_212_);
return v___x_216_;
}
else
{
lean_dec_ref(v_a_u2082_206_);
return v___x_214_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__4___boxed(lean_object* v_f_217_, lean_object* v_a_u2081_218_, lean_object* v_a_u2082_219_, lean_object* v___y_220_, lean_object* v___y_221_, lean_object* v___y_222_, lean_object* v___y_223_, lean_object* v___y_224_, lean_object* v___y_225_, lean_object* v___y_226_){
_start:
{
lean_object* v_res_227_; 
v_res_227_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__4(v_f_217_, v_a_u2081_218_, v_a_u2082_219_, v___y_220_, v___y_221_, v___y_222_, v___y_223_, v___y_224_, v___y_225_);
lean_dec(v___y_225_);
lean_dec_ref(v___y_224_);
lean_dec(v___y_223_);
lean_dec_ref(v___y_222_);
lean_dec(v___y_221_);
lean_dec_ref(v___y_220_);
return v_res_227_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__5_spec__6___redArg(lean_object* v_a_228_, lean_object* v_x_229_){
_start:
{
if (lean_obj_tag(v_x_229_) == 0)
{
return v_x_229_;
}
else
{
lean_object* v_key_230_; lean_object* v_value_231_; lean_object* v_tail_232_; lean_object* v___x_234_; uint8_t v_isShared_235_; uint8_t v_isSharedCheck_241_; 
v_key_230_ = lean_ctor_get(v_x_229_, 0);
v_value_231_ = lean_ctor_get(v_x_229_, 1);
v_tail_232_ = lean_ctor_get(v_x_229_, 2);
v_isSharedCheck_241_ = !lean_is_exclusive(v_x_229_);
if (v_isSharedCheck_241_ == 0)
{
v___x_234_ = v_x_229_;
v_isShared_235_ = v_isSharedCheck_241_;
goto v_resetjp_233_;
}
else
{
lean_inc(v_tail_232_);
lean_inc(v_value_231_);
lean_inc(v_key_230_);
lean_dec(v_x_229_);
v___x_234_ = lean_box(0);
v_isShared_235_ = v_isSharedCheck_241_;
goto v_resetjp_233_;
}
v_resetjp_233_:
{
uint8_t v___x_236_; 
v___x_236_ = l_Lean_instBEqFVarId_beq(v_key_230_, v_a_228_);
if (v___x_236_ == 0)
{
lean_object* v___x_237_; lean_object* v___x_239_; 
v___x_237_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__5_spec__6___redArg(v_a_228_, v_tail_232_);
if (v_isShared_235_ == 0)
{
lean_ctor_set(v___x_234_, 2, v___x_237_);
v___x_239_ = v___x_234_;
goto v_reusejp_238_;
}
else
{
lean_object* v_reuseFailAlloc_240_; 
v_reuseFailAlloc_240_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_240_, 0, v_key_230_);
lean_ctor_set(v_reuseFailAlloc_240_, 1, v_value_231_);
lean_ctor_set(v_reuseFailAlloc_240_, 2, v___x_237_);
v___x_239_ = v_reuseFailAlloc_240_;
goto v_reusejp_238_;
}
v_reusejp_238_:
{
return v___x_239_;
}
}
else
{
lean_del_object(v___x_234_);
lean_dec(v_value_231_);
lean_dec(v_key_230_);
return v_tail_232_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__5_spec__6___redArg___boxed(lean_object* v_a_242_, lean_object* v_x_243_){
_start:
{
lean_object* v_res_244_; 
v_res_244_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__5_spec__6___redArg(v_a_242_, v_x_243_);
lean_dec(v_a_242_);
return v_res_244_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__5___redArg(lean_object* v_m_245_, lean_object* v_a_246_){
_start:
{
lean_object* v_size_247_; lean_object* v_buckets_248_; lean_object* v___x_249_; uint64_t v___x_250_; uint64_t v___x_251_; uint64_t v___x_252_; uint64_t v_fold_253_; uint64_t v___x_254_; uint64_t v___x_255_; uint64_t v___x_256_; size_t v___x_257_; size_t v___x_258_; size_t v___x_259_; size_t v___x_260_; size_t v___x_261_; lean_object* v_bkt_262_; uint8_t v___x_263_; 
v_size_247_ = lean_ctor_get(v_m_245_, 0);
v_buckets_248_ = lean_ctor_get(v_m_245_, 1);
v___x_249_ = lean_array_get_size(v_buckets_248_);
v___x_250_ = l_Lean_instHashableFVarId_hash(v_a_246_);
v___x_251_ = 32ULL;
v___x_252_ = lean_uint64_shift_right(v___x_250_, v___x_251_);
v_fold_253_ = lean_uint64_xor(v___x_250_, v___x_252_);
v___x_254_ = 16ULL;
v___x_255_ = lean_uint64_shift_right(v_fold_253_, v___x_254_);
v___x_256_ = lean_uint64_xor(v_fold_253_, v___x_255_);
v___x_257_ = lean_uint64_to_usize(v___x_256_);
v___x_258_ = lean_usize_of_nat(v___x_249_);
v___x_259_ = ((size_t)1ULL);
v___x_260_ = lean_usize_sub(v___x_258_, v___x_259_);
v___x_261_ = lean_usize_land(v___x_257_, v___x_260_);
v_bkt_262_ = lean_array_uget_borrowed(v_buckets_248_, v___x_261_);
v___x_263_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__0_spec__0___redArg(v_a_246_, v_bkt_262_);
if (v___x_263_ == 0)
{
return v_m_245_;
}
else
{
lean_object* v___x_265_; uint8_t v_isShared_266_; uint8_t v_isSharedCheck_276_; 
lean_inc(v_bkt_262_);
lean_inc_ref(v_buckets_248_);
lean_inc(v_size_247_);
v_isSharedCheck_276_ = !lean_is_exclusive(v_m_245_);
if (v_isSharedCheck_276_ == 0)
{
lean_object* v_unused_277_; lean_object* v_unused_278_; 
v_unused_277_ = lean_ctor_get(v_m_245_, 1);
lean_dec(v_unused_277_);
v_unused_278_ = lean_ctor_get(v_m_245_, 0);
lean_dec(v_unused_278_);
v___x_265_ = v_m_245_;
v_isShared_266_ = v_isSharedCheck_276_;
goto v_resetjp_264_;
}
else
{
lean_dec(v_m_245_);
v___x_265_ = lean_box(0);
v_isShared_266_ = v_isSharedCheck_276_;
goto v_resetjp_264_;
}
v_resetjp_264_:
{
lean_object* v___x_267_; lean_object* v_buckets_x27_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_274_; 
v___x_267_ = lean_box(0);
v_buckets_x27_268_ = lean_array_uset(v_buckets_248_, v___x_261_, v___x_267_);
v___x_269_ = lean_unsigned_to_nat(1u);
v___x_270_ = lean_nat_sub(v_size_247_, v___x_269_);
lean_dec(v_size_247_);
v___x_271_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__5_spec__6___redArg(v_a_246_, v_bkt_262_);
v___x_272_ = lean_array_uset(v_buckets_x27_268_, v___x_261_, v___x_271_);
if (v_isShared_266_ == 0)
{
lean_ctor_set(v___x_265_, 1, v___x_272_);
lean_ctor_set(v___x_265_, 0, v___x_270_);
v___x_274_ = v___x_265_;
goto v_reusejp_273_;
}
else
{
lean_object* v_reuseFailAlloc_275_; 
v_reuseFailAlloc_275_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_275_, 0, v___x_270_);
lean_ctor_set(v_reuseFailAlloc_275_, 1, v___x_272_);
v___x_274_ = v_reuseFailAlloc_275_;
goto v_reusejp_273_;
}
v_reusejp_273_:
{
return v___x_274_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__5___redArg___boxed(lean_object* v_m_279_, lean_object* v_a_280_){
_start:
{
lean_object* v_res_281_; 
v_res_281_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__5___redArg(v_m_279_, v_a_280_);
lean_dec(v_a_280_);
return v_res_281_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__6_spec__8_spec__10_spec__12___redArg(lean_object* v_x_282_, lean_object* v_x_283_){
_start:
{
if (lean_obj_tag(v_x_283_) == 0)
{
return v_x_282_;
}
else
{
lean_object* v_key_284_; lean_object* v_value_285_; lean_object* v_tail_286_; lean_object* v___x_288_; uint8_t v_isShared_289_; uint8_t v_isSharedCheck_309_; 
v_key_284_ = lean_ctor_get(v_x_283_, 0);
v_value_285_ = lean_ctor_get(v_x_283_, 1);
v_tail_286_ = lean_ctor_get(v_x_283_, 2);
v_isSharedCheck_309_ = !lean_is_exclusive(v_x_283_);
if (v_isSharedCheck_309_ == 0)
{
v___x_288_ = v_x_283_;
v_isShared_289_ = v_isSharedCheck_309_;
goto v_resetjp_287_;
}
else
{
lean_inc(v_tail_286_);
lean_inc(v_value_285_);
lean_inc(v_key_284_);
lean_dec(v_x_283_);
v___x_288_ = lean_box(0);
v_isShared_289_ = v_isSharedCheck_309_;
goto v_resetjp_287_;
}
v_resetjp_287_:
{
lean_object* v___x_290_; uint64_t v___x_291_; uint64_t v___x_292_; uint64_t v___x_293_; uint64_t v_fold_294_; uint64_t v___x_295_; uint64_t v___x_296_; uint64_t v___x_297_; size_t v___x_298_; size_t v___x_299_; size_t v___x_300_; size_t v___x_301_; size_t v___x_302_; lean_object* v___x_303_; lean_object* v___x_305_; 
v___x_290_ = lean_array_get_size(v_x_282_);
v___x_291_ = l_Lean_instHashableFVarId_hash(v_key_284_);
v___x_292_ = 32ULL;
v___x_293_ = lean_uint64_shift_right(v___x_291_, v___x_292_);
v_fold_294_ = lean_uint64_xor(v___x_291_, v___x_293_);
v___x_295_ = 16ULL;
v___x_296_ = lean_uint64_shift_right(v_fold_294_, v___x_295_);
v___x_297_ = lean_uint64_xor(v_fold_294_, v___x_296_);
v___x_298_ = lean_uint64_to_usize(v___x_297_);
v___x_299_ = lean_usize_of_nat(v___x_290_);
v___x_300_ = ((size_t)1ULL);
v___x_301_ = lean_usize_sub(v___x_299_, v___x_300_);
v___x_302_ = lean_usize_land(v___x_298_, v___x_301_);
v___x_303_ = lean_array_uget_borrowed(v_x_282_, v___x_302_);
lean_inc(v___x_303_);
if (v_isShared_289_ == 0)
{
lean_ctor_set(v___x_288_, 2, v___x_303_);
v___x_305_ = v___x_288_;
goto v_reusejp_304_;
}
else
{
lean_object* v_reuseFailAlloc_308_; 
v_reuseFailAlloc_308_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_308_, 0, v_key_284_);
lean_ctor_set(v_reuseFailAlloc_308_, 1, v_value_285_);
lean_ctor_set(v_reuseFailAlloc_308_, 2, v___x_303_);
v___x_305_ = v_reuseFailAlloc_308_;
goto v_reusejp_304_;
}
v_reusejp_304_:
{
lean_object* v___x_306_; 
v___x_306_ = lean_array_uset(v_x_282_, v___x_302_, v___x_305_);
v_x_282_ = v___x_306_;
v_x_283_ = v_tail_286_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__6_spec__8_spec__10___redArg(lean_object* v_i_310_, lean_object* v_source_311_, lean_object* v_target_312_){
_start:
{
lean_object* v___x_313_; uint8_t v___x_314_; 
v___x_313_ = lean_array_get_size(v_source_311_);
v___x_314_ = lean_nat_dec_lt(v_i_310_, v___x_313_);
if (v___x_314_ == 0)
{
lean_dec_ref(v_source_311_);
lean_dec(v_i_310_);
return v_target_312_;
}
else
{
lean_object* v_es_315_; lean_object* v___x_316_; lean_object* v_source_317_; lean_object* v_target_318_; lean_object* v___x_319_; lean_object* v___x_320_; 
v_es_315_ = lean_array_fget(v_source_311_, v_i_310_);
v___x_316_ = lean_box(0);
v_source_317_ = lean_array_fset(v_source_311_, v_i_310_, v___x_316_);
v_target_318_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__6_spec__8_spec__10_spec__12___redArg(v_target_312_, v_es_315_);
v___x_319_ = lean_unsigned_to_nat(1u);
v___x_320_ = lean_nat_add(v_i_310_, v___x_319_);
lean_dec(v_i_310_);
v_i_310_ = v___x_320_;
v_source_311_ = v_source_317_;
v_target_312_ = v_target_318_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__6_spec__8___redArg(lean_object* v_data_322_){
_start:
{
lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v_nbuckets_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; 
v___x_323_ = lean_array_get_size(v_data_322_);
v___x_324_ = lean_unsigned_to_nat(2u);
v_nbuckets_325_ = lean_nat_mul(v___x_323_, v___x_324_);
v___x_326_ = lean_unsigned_to_nat(0u);
v___x_327_ = lean_box(0);
v___x_328_ = lean_mk_array(v_nbuckets_325_, v___x_327_);
v___x_329_ = lean_array_propagate_mark(v_data_322_, v___x_328_);
v___x_330_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__6_spec__8_spec__10___redArg(v___x_326_, v_data_322_, v___x_329_);
return v___x_330_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__6___redArg(lean_object* v_m_331_, lean_object* v_a_332_, lean_object* v_b_333_){
_start:
{
lean_object* v_size_334_; lean_object* v_buckets_335_; lean_object* v___x_336_; uint64_t v___x_337_; uint64_t v___x_338_; uint64_t v___x_339_; uint64_t v_fold_340_; uint64_t v___x_341_; uint64_t v___x_342_; uint64_t v___x_343_; size_t v___x_344_; size_t v___x_345_; size_t v___x_346_; size_t v___x_347_; size_t v___x_348_; lean_object* v_bkt_349_; uint8_t v___x_350_; 
v_size_334_ = lean_ctor_get(v_m_331_, 0);
v_buckets_335_ = lean_ctor_get(v_m_331_, 1);
v___x_336_ = lean_array_get_size(v_buckets_335_);
v___x_337_ = l_Lean_instHashableFVarId_hash(v_a_332_);
v___x_338_ = 32ULL;
v___x_339_ = lean_uint64_shift_right(v___x_337_, v___x_338_);
v_fold_340_ = lean_uint64_xor(v___x_337_, v___x_339_);
v___x_341_ = 16ULL;
v___x_342_ = lean_uint64_shift_right(v_fold_340_, v___x_341_);
v___x_343_ = lean_uint64_xor(v_fold_340_, v___x_342_);
v___x_344_ = lean_uint64_to_usize(v___x_343_);
v___x_345_ = lean_usize_of_nat(v___x_336_);
v___x_346_ = ((size_t)1ULL);
v___x_347_ = lean_usize_sub(v___x_345_, v___x_346_);
v___x_348_ = lean_usize_land(v___x_344_, v___x_347_);
v_bkt_349_ = lean_array_uget_borrowed(v_buckets_335_, v___x_348_);
v___x_350_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__0_spec__0___redArg(v_a_332_, v_bkt_349_);
if (v___x_350_ == 0)
{
lean_object* v___x_352_; uint8_t v_isShared_353_; uint8_t v_isSharedCheck_371_; 
lean_inc_ref(v_buckets_335_);
lean_inc(v_size_334_);
v_isSharedCheck_371_ = !lean_is_exclusive(v_m_331_);
if (v_isSharedCheck_371_ == 0)
{
lean_object* v_unused_372_; lean_object* v_unused_373_; 
v_unused_372_ = lean_ctor_get(v_m_331_, 1);
lean_dec(v_unused_372_);
v_unused_373_ = lean_ctor_get(v_m_331_, 0);
lean_dec(v_unused_373_);
v___x_352_ = v_m_331_;
v_isShared_353_ = v_isSharedCheck_371_;
goto v_resetjp_351_;
}
else
{
lean_dec(v_m_331_);
v___x_352_ = lean_box(0);
v_isShared_353_ = v_isSharedCheck_371_;
goto v_resetjp_351_;
}
v_resetjp_351_:
{
lean_object* v___x_354_; lean_object* v_size_x27_355_; lean_object* v___x_356_; lean_object* v_buckets_x27_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; uint8_t v___x_363_; 
v___x_354_ = lean_unsigned_to_nat(1u);
v_size_x27_355_ = lean_nat_add(v_size_334_, v___x_354_);
lean_dec(v_size_334_);
lean_inc(v_bkt_349_);
v___x_356_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_356_, 0, v_a_332_);
lean_ctor_set(v___x_356_, 1, v_b_333_);
lean_ctor_set(v___x_356_, 2, v_bkt_349_);
v_buckets_x27_357_ = lean_array_uset(v_buckets_335_, v___x_348_, v___x_356_);
v___x_358_ = lean_unsigned_to_nat(4u);
v___x_359_ = lean_nat_mul(v_size_x27_355_, v___x_358_);
v___x_360_ = lean_unsigned_to_nat(3u);
v___x_361_ = lean_nat_div(v___x_359_, v___x_360_);
lean_dec(v___x_359_);
v___x_362_ = lean_array_get_size(v_buckets_x27_357_);
v___x_363_ = lean_nat_dec_le(v___x_361_, v___x_362_);
lean_dec(v___x_361_);
if (v___x_363_ == 0)
{
lean_object* v_val_364_; lean_object* v___x_366_; 
v_val_364_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__6_spec__8___redArg(v_buckets_x27_357_);
if (v_isShared_353_ == 0)
{
lean_ctor_set(v___x_352_, 1, v_val_364_);
lean_ctor_set(v___x_352_, 0, v_size_x27_355_);
v___x_366_ = v___x_352_;
goto v_reusejp_365_;
}
else
{
lean_object* v_reuseFailAlloc_367_; 
v_reuseFailAlloc_367_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_367_, 0, v_size_x27_355_);
lean_ctor_set(v_reuseFailAlloc_367_, 1, v_val_364_);
v___x_366_ = v_reuseFailAlloc_367_;
goto v_reusejp_365_;
}
v_reusejp_365_:
{
return v___x_366_;
}
}
else
{
lean_object* v___x_369_; 
if (v_isShared_353_ == 0)
{
lean_ctor_set(v___x_352_, 1, v_buckets_x27_357_);
lean_ctor_set(v___x_352_, 0, v_size_x27_355_);
v___x_369_ = v___x_352_;
goto v_reusejp_368_;
}
else
{
lean_object* v_reuseFailAlloc_370_; 
v_reuseFailAlloc_370_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_370_, 0, v_size_x27_355_);
lean_ctor_set(v_reuseFailAlloc_370_, 1, v_buckets_x27_357_);
v___x_369_ = v_reuseFailAlloc_370_;
goto v_reusejp_368_;
}
v_reusejp_368_:
{
return v___x_369_;
}
}
}
}
else
{
lean_dec(v_b_333_);
lean_dec(v_a_332_);
return v_m_331_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__7_spec__11_spec__16(lean_object* v_as_381_, size_t v_sz_382_, size_t v_i_383_, lean_object* v_b_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_){
_start:
{
uint8_t v___x_392_; 
v___x_392_ = lean_usize_dec_lt(v_i_383_, v_sz_382_);
if (v___x_392_ == 0)
{
lean_object* v___x_393_; 
v___x_393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_393_, 0, v_b_384_);
return v___x_393_;
}
else
{
lean_object* v_snd_394_; lean_object* v___x_396_; uint8_t v_isShared_397_; uint8_t v_isSharedCheck_564_; 
v_snd_394_ = lean_ctor_get(v_b_384_, 1);
v_isSharedCheck_564_ = !lean_is_exclusive(v_b_384_);
if (v_isSharedCheck_564_ == 0)
{
lean_object* v_unused_565_; 
v_unused_565_ = lean_ctor_get(v_b_384_, 0);
lean_dec(v_unused_565_);
v___x_396_ = v_b_384_;
v_isShared_397_ = v_isSharedCheck_564_;
goto v_resetjp_395_;
}
else
{
lean_inc(v_snd_394_);
lean_dec(v_b_384_);
v___x_396_ = lean_box(0);
v_isShared_397_ = v_isSharedCheck_564_;
goto v_resetjp_395_;
}
v_resetjp_395_:
{
lean_object* v___x_398_; lean_object* v_a_400_; lean_object* v_a_407_; 
v___x_398_ = lean_box(0);
v_a_407_ = lean_array_uget_borrowed(v_as_381_, v_i_383_);
if (lean_obj_tag(v_a_407_) == 0)
{
v_a_400_ = v_snd_394_;
goto v___jp_399_;
}
else
{
lean_object* v_val_408_; uint8_t v___x_409_; 
v_val_408_ = lean_ctor_get(v_a_407_, 0);
v___x_409_ = l_Lean_LocalDecl_isImplementationDetail(v_val_408_);
if (v___x_409_ == 0)
{
uint8_t v___x_410_; 
v___x_410_ = l_Lean_LocalDecl_isLet(v_val_408_, v___x_409_);
if (v___x_410_ == 0)
{
lean_object* v___x_411_; lean_object* v___x_412_; 
v___x_411_ = l_Lean_LocalDecl_type(v_val_408_);
v___x_412_ = l_Lean_Meta_Sym_instantiateMVarsS(v___x_411_, v___y_385_, v___y_386_, v___y_387_, v___y_388_, v___y_389_, v___y_390_);
if (lean_obj_tag(v___x_412_) == 0)
{
lean_object* v_a_413_; lean_object* v___y_415_; lean_object* v___y_416_; lean_object* v___y_417_; lean_object* v___y_418_; lean_object* v___y_419_; lean_object* v___y_420_; 
v_a_413_ = lean_ctor_get(v___x_412_, 0);
lean_inc(v_a_413_);
lean_dec_ref_known(v___x_412_, 1);
if (lean_obj_tag(v_a_413_) == 3)
{
lean_object* v_u_508_; 
v_u_508_ = lean_ctor_get(v_a_413_, 0);
if (lean_obj_tag(v_u_508_) == 1)
{
lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; 
lean_inc_ref(v_u_508_);
lean_dec_ref_known(v_a_413_, 1);
v___x_509_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__7_spec__11_spec__16___closed__1));
v___x_510_ = lean_box(0);
v___x_511_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_511_, 0, v_u_508_);
lean_ctor_set(v___x_511_, 1, v___x_510_);
v___x_512_ = l_Lean_Meta_Sym_Internal_mkConstS___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__2___redArg(v___x_509_, v___x_511_, v___y_386_);
if (lean_obj_tag(v___x_512_) == 0)
{
lean_object* v_a_513_; lean_object* v___x_514_; lean_object* v___x_515_; 
v_a_513_ = lean_ctor_get(v___x_512_, 0);
lean_inc(v_a_513_);
lean_dec_ref_known(v___x_512_, 1);
lean_inc(v_val_408_);
v___x_514_ = l_Lean_LocalDecl_toExpr(v_val_408_);
v___x_515_ = l_Lean_Meta_Sym_shareCommonInc(v___x_514_, v___y_385_, v___y_386_, v___y_387_, v___y_388_, v___y_389_, v___y_390_);
if (lean_obj_tag(v___x_515_) == 0)
{
lean_object* v_a_516_; lean_object* v___x_517_; 
v_a_516_ = lean_ctor_get(v___x_515_, 0);
lean_inc(v_a_516_);
lean_dec_ref_known(v___x_515_, 1);
v___x_517_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__3(v_a_513_, v_a_516_, v___y_385_, v___y_386_, v___y_387_, v___y_388_, v___y_389_, v___y_390_);
if (lean_obj_tag(v___x_517_) == 0)
{
lean_object* v_a_518_; lean_object* v___x_519_; 
v_a_518_ = lean_ctor_get(v___x_517_, 0);
lean_inc(v_a_518_);
lean_dec_ref_known(v___x_517_, 1);
v___x_519_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v_a_518_, v___y_386_, v___y_387_, v___y_388_, v___y_389_, v___y_390_);
if (lean_obj_tag(v___x_519_) == 0)
{
lean_object* v_a_520_; 
v_a_520_ = lean_ctor_get(v___x_519_, 0);
lean_inc(v_a_520_);
lean_dec_ref_known(v___x_519_, 1);
if (lean_obj_tag(v_a_520_) == 0)
{
lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; 
v___x_521_ = l_Lean_LocalDecl_fvarId(v_val_408_);
v___x_522_ = lean_box(0);
v___x_523_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__6___redArg(v_snd_394_, v___x_521_, v___x_522_);
v_a_400_ = v___x_523_;
goto v___jp_399_;
}
else
{
lean_dec_ref_known(v_a_520_, 1);
v_a_400_ = v_snd_394_;
goto v___jp_399_;
}
}
else
{
lean_object* v_a_524_; lean_object* v___x_526_; uint8_t v_isShared_527_; uint8_t v_isSharedCheck_531_; 
lean_del_object(v___x_396_);
lean_dec(v_snd_394_);
v_a_524_ = lean_ctor_get(v___x_519_, 0);
v_isSharedCheck_531_ = !lean_is_exclusive(v___x_519_);
if (v_isSharedCheck_531_ == 0)
{
v___x_526_ = v___x_519_;
v_isShared_527_ = v_isSharedCheck_531_;
goto v_resetjp_525_;
}
else
{
lean_inc(v_a_524_);
lean_dec(v___x_519_);
v___x_526_ = lean_box(0);
v_isShared_527_ = v_isSharedCheck_531_;
goto v_resetjp_525_;
}
v_resetjp_525_:
{
lean_object* v___x_529_; 
if (v_isShared_527_ == 0)
{
v___x_529_ = v___x_526_;
goto v_reusejp_528_;
}
else
{
lean_object* v_reuseFailAlloc_530_; 
v_reuseFailAlloc_530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_530_, 0, v_a_524_);
v___x_529_ = v_reuseFailAlloc_530_;
goto v_reusejp_528_;
}
v_reusejp_528_:
{
return v___x_529_;
}
}
}
}
else
{
lean_object* v_a_532_; lean_object* v___x_534_; uint8_t v_isShared_535_; uint8_t v_isSharedCheck_539_; 
lean_del_object(v___x_396_);
lean_dec(v_snd_394_);
v_a_532_ = lean_ctor_get(v___x_517_, 0);
v_isSharedCheck_539_ = !lean_is_exclusive(v___x_517_);
if (v_isSharedCheck_539_ == 0)
{
v___x_534_ = v___x_517_;
v_isShared_535_ = v_isSharedCheck_539_;
goto v_resetjp_533_;
}
else
{
lean_inc(v_a_532_);
lean_dec(v___x_517_);
v___x_534_ = lean_box(0);
v_isShared_535_ = v_isSharedCheck_539_;
goto v_resetjp_533_;
}
v_resetjp_533_:
{
lean_object* v___x_537_; 
if (v_isShared_535_ == 0)
{
v___x_537_ = v___x_534_;
goto v_reusejp_536_;
}
else
{
lean_object* v_reuseFailAlloc_538_; 
v_reuseFailAlloc_538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_538_, 0, v_a_532_);
v___x_537_ = v_reuseFailAlloc_538_;
goto v_reusejp_536_;
}
v_reusejp_536_:
{
return v___x_537_;
}
}
}
}
else
{
lean_object* v_a_540_; lean_object* v___x_542_; uint8_t v_isShared_543_; uint8_t v_isSharedCheck_547_; 
lean_dec(v_a_513_);
lean_del_object(v___x_396_);
lean_dec(v_snd_394_);
v_a_540_ = lean_ctor_get(v___x_515_, 0);
v_isSharedCheck_547_ = !lean_is_exclusive(v___x_515_);
if (v_isSharedCheck_547_ == 0)
{
v___x_542_ = v___x_515_;
v_isShared_543_ = v_isSharedCheck_547_;
goto v_resetjp_541_;
}
else
{
lean_inc(v_a_540_);
lean_dec(v___x_515_);
v___x_542_ = lean_box(0);
v_isShared_543_ = v_isSharedCheck_547_;
goto v_resetjp_541_;
}
v_resetjp_541_:
{
lean_object* v___x_545_; 
if (v_isShared_543_ == 0)
{
v___x_545_ = v___x_542_;
goto v_reusejp_544_;
}
else
{
lean_object* v_reuseFailAlloc_546_; 
v_reuseFailAlloc_546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_546_, 0, v_a_540_);
v___x_545_ = v_reuseFailAlloc_546_;
goto v_reusejp_544_;
}
v_reusejp_544_:
{
return v___x_545_;
}
}
}
}
else
{
lean_object* v_a_548_; lean_object* v___x_550_; uint8_t v_isShared_551_; uint8_t v_isSharedCheck_555_; 
lean_del_object(v___x_396_);
lean_dec(v_snd_394_);
v_a_548_ = lean_ctor_get(v___x_512_, 0);
v_isSharedCheck_555_ = !lean_is_exclusive(v___x_512_);
if (v_isSharedCheck_555_ == 0)
{
v___x_550_ = v___x_512_;
v_isShared_551_ = v_isSharedCheck_555_;
goto v_resetjp_549_;
}
else
{
lean_inc(v_a_548_);
lean_dec(v___x_512_);
v___x_550_ = lean_box(0);
v_isShared_551_ = v_isSharedCheck_555_;
goto v_resetjp_549_;
}
v_resetjp_549_:
{
lean_object* v___x_553_; 
if (v_isShared_551_ == 0)
{
v___x_553_ = v___x_550_;
goto v_reusejp_552_;
}
else
{
lean_object* v_reuseFailAlloc_554_; 
v_reuseFailAlloc_554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_554_, 0, v_a_548_);
v___x_553_ = v_reuseFailAlloc_554_;
goto v_reusejp_552_;
}
v_reusejp_552_:
{
return v___x_553_;
}
}
}
}
else
{
v___y_415_ = v___y_385_;
v___y_416_ = v___y_386_;
v___y_417_ = v___y_387_;
v___y_418_ = v___y_388_;
v___y_419_ = v___y_389_;
v___y_420_ = v___y_390_;
goto v___jp_414_;
}
}
else
{
v___y_415_ = v___y_385_;
v___y_416_ = v___y_386_;
v___y_417_ = v___y_387_;
v___y_418_ = v___y_388_;
v___y_419_ = v___y_389_;
v___y_420_ = v___y_390_;
goto v___jp_414_;
}
v___jp_414_:
{
if (lean_obj_tag(v_a_413_) == 1)
{
lean_object* v_fvarId_421_; uint8_t v___x_422_; 
v_fvarId_421_ = lean_ctor_get(v_a_413_, 0);
lean_inc(v_fvarId_421_);
lean_dec_ref_known(v_a_413_, 1);
v___x_422_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__0___redArg(v_snd_394_, v_fvarId_421_);
if (v___x_422_ == 0)
{
lean_dec(v_fvarId_421_);
v_a_400_ = v_snd_394_;
goto v___jp_399_;
}
else
{
lean_object* v___x_423_; 
lean_inc(v_fvarId_421_);
v___x_423_ = l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__1___redArg(v_fvarId_421_, v___y_416_);
if (lean_obj_tag(v___x_423_) == 0)
{
lean_object* v_a_424_; lean_object* v___x_425_; 
v_a_424_ = lean_ctor_get(v___x_423_, 0);
lean_inc_n(v_a_424_, 2);
lean_dec_ref_known(v___x_423_, 1);
v___x_425_ = l_Lean_Meta_Sym_getLevel___redArg(v_a_424_, v___y_416_, v___y_417_, v___y_418_, v___y_419_, v___y_420_);
if (lean_obj_tag(v___x_425_) == 0)
{
lean_object* v_a_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; 
v_a_426_ = lean_ctor_get(v___x_425_, 0);
lean_inc(v_a_426_);
lean_dec_ref_known(v___x_425_, 1);
v___x_427_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__7_spec__11_spec__16___closed__1));
v___x_428_ = lean_box(0);
v___x_429_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_429_, 0, v_a_426_);
lean_ctor_set(v___x_429_, 1, v___x_428_);
lean_inc_ref(v___x_429_);
v___x_430_ = l_Lean_Meta_Sym_Internal_mkConstS___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__2___redArg(v___x_427_, v___x_429_, v___y_416_);
if (lean_obj_tag(v___x_430_) == 0)
{
lean_object* v_a_431_; lean_object* v___x_432_; 
v_a_431_ = lean_ctor_get(v___x_430_, 0);
lean_inc(v_a_431_);
lean_dec_ref_known(v___x_430_, 1);
lean_inc(v_a_424_);
v___x_432_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__3(v_a_431_, v_a_424_, v___y_415_, v___y_416_, v___y_417_, v___y_418_, v___y_419_, v___y_420_);
if (lean_obj_tag(v___x_432_) == 0)
{
lean_object* v_a_433_; lean_object* v___x_434_; lean_object* v___x_435_; 
v_a_433_ = lean_ctor_get(v___x_432_, 0);
lean_inc(v_a_433_);
lean_dec_ref_known(v___x_432_, 1);
v___x_434_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__7_spec__11_spec__16___closed__3));
v___x_435_ = l_Lean_Meta_Sym_Internal_mkConstS___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__2___redArg(v___x_434_, v___x_429_, v___y_416_);
if (lean_obj_tag(v___x_435_) == 0)
{
lean_object* v_a_436_; lean_object* v___x_437_; lean_object* v___x_438_; 
v_a_436_ = lean_ctor_get(v___x_435_, 0);
lean_inc(v_a_436_);
lean_dec_ref_known(v___x_435_, 1);
lean_inc(v_val_408_);
v___x_437_ = l_Lean_LocalDecl_toExpr(v_val_408_);
v___x_438_ = l_Lean_Meta_Sym_shareCommonInc(v___x_437_, v___y_415_, v___y_416_, v___y_417_, v___y_418_, v___y_419_, v___y_420_);
if (lean_obj_tag(v___x_438_) == 0)
{
lean_object* v_a_439_; lean_object* v___x_440_; 
v_a_439_ = lean_ctor_get(v___x_438_, 0);
lean_inc(v_a_439_);
lean_dec_ref_known(v___x_438_, 1);
v___x_440_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__4(v_a_436_, v_a_424_, v_a_439_, v___y_415_, v___y_416_, v___y_417_, v___y_418_, v___y_419_, v___y_420_);
if (lean_obj_tag(v___x_440_) == 0)
{
lean_object* v_a_441_; lean_object* v___x_442_; 
v_a_441_ = lean_ctor_get(v___x_440_, 0);
lean_inc(v_a_441_);
lean_dec_ref_known(v___x_440_, 1);
v___x_442_ = l_Lean_Meta_Sym_registerInstance___redArg(v_a_433_, v_a_441_, v___y_416_);
if (lean_obj_tag(v___x_442_) == 0)
{
lean_object* v___x_443_; 
lean_dec_ref_known(v___x_442_, 1);
v___x_443_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__5___redArg(v_snd_394_, v_fvarId_421_);
lean_dec(v_fvarId_421_);
v_a_400_ = v___x_443_;
goto v___jp_399_;
}
else
{
lean_object* v_a_444_; lean_object* v___x_446_; uint8_t v_isShared_447_; uint8_t v_isSharedCheck_451_; 
lean_dec(v_fvarId_421_);
lean_del_object(v___x_396_);
lean_dec(v_snd_394_);
v_a_444_ = lean_ctor_get(v___x_442_, 0);
v_isSharedCheck_451_ = !lean_is_exclusive(v___x_442_);
if (v_isSharedCheck_451_ == 0)
{
v___x_446_ = v___x_442_;
v_isShared_447_ = v_isSharedCheck_451_;
goto v_resetjp_445_;
}
else
{
lean_inc(v_a_444_);
lean_dec(v___x_442_);
v___x_446_ = lean_box(0);
v_isShared_447_ = v_isSharedCheck_451_;
goto v_resetjp_445_;
}
v_resetjp_445_:
{
lean_object* v___x_449_; 
if (v_isShared_447_ == 0)
{
v___x_449_ = v___x_446_;
goto v_reusejp_448_;
}
else
{
lean_object* v_reuseFailAlloc_450_; 
v_reuseFailAlloc_450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_450_, 0, v_a_444_);
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
lean_dec(v_a_433_);
lean_dec(v_fvarId_421_);
lean_del_object(v___x_396_);
lean_dec(v_snd_394_);
v_a_452_ = lean_ctor_get(v___x_440_, 0);
v_isSharedCheck_459_ = !lean_is_exclusive(v___x_440_);
if (v_isSharedCheck_459_ == 0)
{
v___x_454_ = v___x_440_;
v_isShared_455_ = v_isSharedCheck_459_;
goto v_resetjp_453_;
}
else
{
lean_inc(v_a_452_);
lean_dec(v___x_440_);
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
lean_object* v_a_460_; lean_object* v___x_462_; uint8_t v_isShared_463_; uint8_t v_isSharedCheck_467_; 
lean_dec(v_a_436_);
lean_dec(v_a_433_);
lean_dec(v_a_424_);
lean_dec(v_fvarId_421_);
lean_del_object(v___x_396_);
lean_dec(v_snd_394_);
v_a_460_ = lean_ctor_get(v___x_438_, 0);
v_isSharedCheck_467_ = !lean_is_exclusive(v___x_438_);
if (v_isSharedCheck_467_ == 0)
{
v___x_462_ = v___x_438_;
v_isShared_463_ = v_isSharedCheck_467_;
goto v_resetjp_461_;
}
else
{
lean_inc(v_a_460_);
lean_dec(v___x_438_);
v___x_462_ = lean_box(0);
v_isShared_463_ = v_isSharedCheck_467_;
goto v_resetjp_461_;
}
v_resetjp_461_:
{
lean_object* v___x_465_; 
if (v_isShared_463_ == 0)
{
v___x_465_ = v___x_462_;
goto v_reusejp_464_;
}
else
{
lean_object* v_reuseFailAlloc_466_; 
v_reuseFailAlloc_466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_466_, 0, v_a_460_);
v___x_465_ = v_reuseFailAlloc_466_;
goto v_reusejp_464_;
}
v_reusejp_464_:
{
return v___x_465_;
}
}
}
}
else
{
lean_object* v_a_468_; lean_object* v___x_470_; uint8_t v_isShared_471_; uint8_t v_isSharedCheck_475_; 
lean_dec(v_a_433_);
lean_dec(v_a_424_);
lean_dec(v_fvarId_421_);
lean_del_object(v___x_396_);
lean_dec(v_snd_394_);
v_a_468_ = lean_ctor_get(v___x_435_, 0);
v_isSharedCheck_475_ = !lean_is_exclusive(v___x_435_);
if (v_isSharedCheck_475_ == 0)
{
v___x_470_ = v___x_435_;
v_isShared_471_ = v_isSharedCheck_475_;
goto v_resetjp_469_;
}
else
{
lean_inc(v_a_468_);
lean_dec(v___x_435_);
v___x_470_ = lean_box(0);
v_isShared_471_ = v_isSharedCheck_475_;
goto v_resetjp_469_;
}
v_resetjp_469_:
{
lean_object* v___x_473_; 
if (v_isShared_471_ == 0)
{
v___x_473_ = v___x_470_;
goto v_reusejp_472_;
}
else
{
lean_object* v_reuseFailAlloc_474_; 
v_reuseFailAlloc_474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_474_, 0, v_a_468_);
v___x_473_ = v_reuseFailAlloc_474_;
goto v_reusejp_472_;
}
v_reusejp_472_:
{
return v___x_473_;
}
}
}
}
else
{
lean_object* v_a_476_; lean_object* v___x_478_; uint8_t v_isShared_479_; uint8_t v_isSharedCheck_483_; 
lean_dec_ref_known(v___x_429_, 2);
lean_dec(v_a_424_);
lean_dec(v_fvarId_421_);
lean_del_object(v___x_396_);
lean_dec(v_snd_394_);
v_a_476_ = lean_ctor_get(v___x_432_, 0);
v_isSharedCheck_483_ = !lean_is_exclusive(v___x_432_);
if (v_isSharedCheck_483_ == 0)
{
v___x_478_ = v___x_432_;
v_isShared_479_ = v_isSharedCheck_483_;
goto v_resetjp_477_;
}
else
{
lean_inc(v_a_476_);
lean_dec(v___x_432_);
v___x_478_ = lean_box(0);
v_isShared_479_ = v_isSharedCheck_483_;
goto v_resetjp_477_;
}
v_resetjp_477_:
{
lean_object* v___x_481_; 
if (v_isShared_479_ == 0)
{
v___x_481_ = v___x_478_;
goto v_reusejp_480_;
}
else
{
lean_object* v_reuseFailAlloc_482_; 
v_reuseFailAlloc_482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_482_, 0, v_a_476_);
v___x_481_ = v_reuseFailAlloc_482_;
goto v_reusejp_480_;
}
v_reusejp_480_:
{
return v___x_481_;
}
}
}
}
else
{
lean_object* v_a_484_; lean_object* v___x_486_; uint8_t v_isShared_487_; uint8_t v_isSharedCheck_491_; 
lean_dec_ref_known(v___x_429_, 2);
lean_dec(v_a_424_);
lean_dec(v_fvarId_421_);
lean_del_object(v___x_396_);
lean_dec(v_snd_394_);
v_a_484_ = lean_ctor_get(v___x_430_, 0);
v_isSharedCheck_491_ = !lean_is_exclusive(v___x_430_);
if (v_isSharedCheck_491_ == 0)
{
v___x_486_ = v___x_430_;
v_isShared_487_ = v_isSharedCheck_491_;
goto v_resetjp_485_;
}
else
{
lean_inc(v_a_484_);
lean_dec(v___x_430_);
v___x_486_ = lean_box(0);
v_isShared_487_ = v_isSharedCheck_491_;
goto v_resetjp_485_;
}
v_resetjp_485_:
{
lean_object* v___x_489_; 
if (v_isShared_487_ == 0)
{
v___x_489_ = v___x_486_;
goto v_reusejp_488_;
}
else
{
lean_object* v_reuseFailAlloc_490_; 
v_reuseFailAlloc_490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_490_, 0, v_a_484_);
v___x_489_ = v_reuseFailAlloc_490_;
goto v_reusejp_488_;
}
v_reusejp_488_:
{
return v___x_489_;
}
}
}
}
else
{
lean_object* v_a_492_; lean_object* v___x_494_; uint8_t v_isShared_495_; uint8_t v_isSharedCheck_499_; 
lean_dec(v_a_424_);
lean_dec(v_fvarId_421_);
lean_del_object(v___x_396_);
lean_dec(v_snd_394_);
v_a_492_ = lean_ctor_get(v___x_425_, 0);
v_isSharedCheck_499_ = !lean_is_exclusive(v___x_425_);
if (v_isSharedCheck_499_ == 0)
{
v___x_494_ = v___x_425_;
v_isShared_495_ = v_isSharedCheck_499_;
goto v_resetjp_493_;
}
else
{
lean_inc(v_a_492_);
lean_dec(v___x_425_);
v___x_494_ = lean_box(0);
v_isShared_495_ = v_isSharedCheck_499_;
goto v_resetjp_493_;
}
v_resetjp_493_:
{
lean_object* v___x_497_; 
if (v_isShared_495_ == 0)
{
v___x_497_ = v___x_494_;
goto v_reusejp_496_;
}
else
{
lean_object* v_reuseFailAlloc_498_; 
v_reuseFailAlloc_498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_498_, 0, v_a_492_);
v___x_497_ = v_reuseFailAlloc_498_;
goto v_reusejp_496_;
}
v_reusejp_496_:
{
return v___x_497_;
}
}
}
}
else
{
lean_object* v_a_500_; lean_object* v___x_502_; uint8_t v_isShared_503_; uint8_t v_isSharedCheck_507_; 
lean_dec(v_fvarId_421_);
lean_del_object(v___x_396_);
lean_dec(v_snd_394_);
v_a_500_ = lean_ctor_get(v___x_423_, 0);
v_isSharedCheck_507_ = !lean_is_exclusive(v___x_423_);
if (v_isSharedCheck_507_ == 0)
{
v___x_502_ = v___x_423_;
v_isShared_503_ = v_isSharedCheck_507_;
goto v_resetjp_501_;
}
else
{
lean_inc(v_a_500_);
lean_dec(v___x_423_);
v___x_502_ = lean_box(0);
v_isShared_503_ = v_isSharedCheck_507_;
goto v_resetjp_501_;
}
v_resetjp_501_:
{
lean_object* v___x_505_; 
if (v_isShared_503_ == 0)
{
v___x_505_ = v___x_502_;
goto v_reusejp_504_;
}
else
{
lean_object* v_reuseFailAlloc_506_; 
v_reuseFailAlloc_506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_506_, 0, v_a_500_);
v___x_505_ = v_reuseFailAlloc_506_;
goto v_reusejp_504_;
}
v_reusejp_504_:
{
return v___x_505_;
}
}
}
}
}
else
{
lean_dec(v_a_413_);
v_a_400_ = v_snd_394_;
goto v___jp_399_;
}
}
}
else
{
lean_object* v_a_556_; lean_object* v___x_558_; uint8_t v_isShared_559_; uint8_t v_isSharedCheck_563_; 
lean_del_object(v___x_396_);
lean_dec(v_snd_394_);
v_a_556_ = lean_ctor_get(v___x_412_, 0);
v_isSharedCheck_563_ = !lean_is_exclusive(v___x_412_);
if (v_isSharedCheck_563_ == 0)
{
v___x_558_ = v___x_412_;
v_isShared_559_ = v_isSharedCheck_563_;
goto v_resetjp_557_;
}
else
{
lean_inc(v_a_556_);
lean_dec(v___x_412_);
v___x_558_ = lean_box(0);
v_isShared_559_ = v_isSharedCheck_563_;
goto v_resetjp_557_;
}
v_resetjp_557_:
{
lean_object* v___x_561_; 
if (v_isShared_559_ == 0)
{
v___x_561_ = v___x_558_;
goto v_reusejp_560_;
}
else
{
lean_object* v_reuseFailAlloc_562_; 
v_reuseFailAlloc_562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_562_, 0, v_a_556_);
v___x_561_ = v_reuseFailAlloc_562_;
goto v_reusejp_560_;
}
v_reusejp_560_:
{
return v___x_561_;
}
}
}
}
else
{
v_a_400_ = v_snd_394_;
goto v___jp_399_;
}
}
else
{
v_a_400_ = v_snd_394_;
goto v___jp_399_;
}
}
v___jp_399_:
{
lean_object* v___x_402_; 
if (v_isShared_397_ == 0)
{
lean_ctor_set(v___x_396_, 1, v_a_400_);
lean_ctor_set(v___x_396_, 0, v___x_398_);
v___x_402_ = v___x_396_;
goto v_reusejp_401_;
}
else
{
lean_object* v_reuseFailAlloc_406_; 
v_reuseFailAlloc_406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_406_, 0, v___x_398_);
lean_ctor_set(v_reuseFailAlloc_406_, 1, v_a_400_);
v___x_402_ = v_reuseFailAlloc_406_;
goto v_reusejp_401_;
}
v_reusejp_401_:
{
size_t v___x_403_; size_t v___x_404_; 
v___x_403_ = ((size_t)1ULL);
v___x_404_ = lean_usize_add(v_i_383_, v___x_403_);
v_i_383_ = v___x_404_;
v_b_384_ = v___x_402_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__7_spec__11_spec__16___boxed(lean_object* v_as_566_, lean_object* v_sz_567_, lean_object* v_i_568_, lean_object* v_b_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_){
_start:
{
size_t v_sz_boxed_577_; size_t v_i_boxed_578_; lean_object* v_res_579_; 
v_sz_boxed_577_ = lean_unbox_usize(v_sz_567_);
lean_dec(v_sz_567_);
v_i_boxed_578_ = lean_unbox_usize(v_i_568_);
lean_dec(v_i_568_);
v_res_579_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__7_spec__11_spec__16(v_as_566_, v_sz_boxed_577_, v_i_boxed_578_, v_b_569_, v___y_570_, v___y_571_, v___y_572_, v___y_573_, v___y_574_, v___y_575_);
lean_dec(v___y_575_);
lean_dec_ref(v___y_574_);
lean_dec(v___y_573_);
lean_dec_ref(v___y_572_);
lean_dec(v___y_571_);
lean_dec_ref(v___y_570_);
lean_dec_ref(v_as_566_);
return v_res_579_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__7_spec__11(lean_object* v_as_580_, size_t v_sz_581_, size_t v_i_582_, lean_object* v_b_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_){
_start:
{
uint8_t v___x_591_; 
v___x_591_ = lean_usize_dec_lt(v_i_582_, v_sz_581_);
if (v___x_591_ == 0)
{
lean_object* v___x_592_; 
v___x_592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_592_, 0, v_b_583_);
return v___x_592_;
}
else
{
lean_object* v_snd_593_; lean_object* v___x_595_; uint8_t v_isShared_596_; uint8_t v_isSharedCheck_763_; 
v_snd_593_ = lean_ctor_get(v_b_583_, 1);
v_isSharedCheck_763_ = !lean_is_exclusive(v_b_583_);
if (v_isSharedCheck_763_ == 0)
{
lean_object* v_unused_764_; 
v_unused_764_ = lean_ctor_get(v_b_583_, 0);
lean_dec(v_unused_764_);
v___x_595_ = v_b_583_;
v_isShared_596_ = v_isSharedCheck_763_;
goto v_resetjp_594_;
}
else
{
lean_inc(v_snd_593_);
lean_dec(v_b_583_);
v___x_595_ = lean_box(0);
v_isShared_596_ = v_isSharedCheck_763_;
goto v_resetjp_594_;
}
v_resetjp_594_:
{
lean_object* v___x_597_; lean_object* v_a_599_; lean_object* v_a_606_; 
v___x_597_ = lean_box(0);
v_a_606_ = lean_array_uget_borrowed(v_as_580_, v_i_582_);
if (lean_obj_tag(v_a_606_) == 0)
{
v_a_599_ = v_snd_593_;
goto v___jp_598_;
}
else
{
lean_object* v_val_607_; uint8_t v___x_608_; 
v_val_607_ = lean_ctor_get(v_a_606_, 0);
v___x_608_ = l_Lean_LocalDecl_isImplementationDetail(v_val_607_);
if (v___x_608_ == 0)
{
uint8_t v___x_609_; 
v___x_609_ = l_Lean_LocalDecl_isLet(v_val_607_, v___x_608_);
if (v___x_609_ == 0)
{
lean_object* v___x_610_; lean_object* v___x_611_; 
v___x_610_ = l_Lean_LocalDecl_type(v_val_607_);
v___x_611_ = l_Lean_Meta_Sym_instantiateMVarsS(v___x_610_, v___y_584_, v___y_585_, v___y_586_, v___y_587_, v___y_588_, v___y_589_);
if (lean_obj_tag(v___x_611_) == 0)
{
lean_object* v_a_612_; lean_object* v___y_614_; lean_object* v___y_615_; lean_object* v___y_616_; lean_object* v___y_617_; lean_object* v___y_618_; lean_object* v___y_619_; 
v_a_612_ = lean_ctor_get(v___x_611_, 0);
lean_inc(v_a_612_);
lean_dec_ref_known(v___x_611_, 1);
if (lean_obj_tag(v_a_612_) == 3)
{
lean_object* v_u_707_; 
v_u_707_ = lean_ctor_get(v_a_612_, 0);
if (lean_obj_tag(v_u_707_) == 1)
{
lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; 
lean_inc_ref(v_u_707_);
lean_dec_ref_known(v_a_612_, 1);
v___x_708_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__7_spec__11_spec__16___closed__1));
v___x_709_ = lean_box(0);
v___x_710_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_710_, 0, v_u_707_);
lean_ctor_set(v___x_710_, 1, v___x_709_);
v___x_711_ = l_Lean_Meta_Sym_Internal_mkConstS___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__2___redArg(v___x_708_, v___x_710_, v___y_585_);
if (lean_obj_tag(v___x_711_) == 0)
{
lean_object* v_a_712_; lean_object* v___x_713_; lean_object* v___x_714_; 
v_a_712_ = lean_ctor_get(v___x_711_, 0);
lean_inc(v_a_712_);
lean_dec_ref_known(v___x_711_, 1);
lean_inc(v_val_607_);
v___x_713_ = l_Lean_LocalDecl_toExpr(v_val_607_);
v___x_714_ = l_Lean_Meta_Sym_shareCommonInc(v___x_713_, v___y_584_, v___y_585_, v___y_586_, v___y_587_, v___y_588_, v___y_589_);
if (lean_obj_tag(v___x_714_) == 0)
{
lean_object* v_a_715_; lean_object* v___x_716_; 
v_a_715_ = lean_ctor_get(v___x_714_, 0);
lean_inc(v_a_715_);
lean_dec_ref_known(v___x_714_, 1);
v___x_716_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__3(v_a_712_, v_a_715_, v___y_584_, v___y_585_, v___y_586_, v___y_587_, v___y_588_, v___y_589_);
if (lean_obj_tag(v___x_716_) == 0)
{
lean_object* v_a_717_; lean_object* v___x_718_; 
v_a_717_ = lean_ctor_get(v___x_716_, 0);
lean_inc(v_a_717_);
lean_dec_ref_known(v___x_716_, 1);
v___x_718_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v_a_717_, v___y_585_, v___y_586_, v___y_587_, v___y_588_, v___y_589_);
if (lean_obj_tag(v___x_718_) == 0)
{
lean_object* v_a_719_; 
v_a_719_ = lean_ctor_get(v___x_718_, 0);
lean_inc(v_a_719_);
lean_dec_ref_known(v___x_718_, 1);
if (lean_obj_tag(v_a_719_) == 0)
{
lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; 
v___x_720_ = l_Lean_LocalDecl_fvarId(v_val_607_);
v___x_721_ = lean_box(0);
v___x_722_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__6___redArg(v_snd_593_, v___x_720_, v___x_721_);
v_a_599_ = v___x_722_;
goto v___jp_598_;
}
else
{
lean_dec_ref_known(v_a_719_, 1);
v_a_599_ = v_snd_593_;
goto v___jp_598_;
}
}
else
{
lean_object* v_a_723_; lean_object* v___x_725_; uint8_t v_isShared_726_; uint8_t v_isSharedCheck_730_; 
lean_del_object(v___x_595_);
lean_dec(v_snd_593_);
v_a_723_ = lean_ctor_get(v___x_718_, 0);
v_isSharedCheck_730_ = !lean_is_exclusive(v___x_718_);
if (v_isSharedCheck_730_ == 0)
{
v___x_725_ = v___x_718_;
v_isShared_726_ = v_isSharedCheck_730_;
goto v_resetjp_724_;
}
else
{
lean_inc(v_a_723_);
lean_dec(v___x_718_);
v___x_725_ = lean_box(0);
v_isShared_726_ = v_isSharedCheck_730_;
goto v_resetjp_724_;
}
v_resetjp_724_:
{
lean_object* v___x_728_; 
if (v_isShared_726_ == 0)
{
v___x_728_ = v___x_725_;
goto v_reusejp_727_;
}
else
{
lean_object* v_reuseFailAlloc_729_; 
v_reuseFailAlloc_729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_729_, 0, v_a_723_);
v___x_728_ = v_reuseFailAlloc_729_;
goto v_reusejp_727_;
}
v_reusejp_727_:
{
return v___x_728_;
}
}
}
}
else
{
lean_object* v_a_731_; lean_object* v___x_733_; uint8_t v_isShared_734_; uint8_t v_isSharedCheck_738_; 
lean_del_object(v___x_595_);
lean_dec(v_snd_593_);
v_a_731_ = lean_ctor_get(v___x_716_, 0);
v_isSharedCheck_738_ = !lean_is_exclusive(v___x_716_);
if (v_isSharedCheck_738_ == 0)
{
v___x_733_ = v___x_716_;
v_isShared_734_ = v_isSharedCheck_738_;
goto v_resetjp_732_;
}
else
{
lean_inc(v_a_731_);
lean_dec(v___x_716_);
v___x_733_ = lean_box(0);
v_isShared_734_ = v_isSharedCheck_738_;
goto v_resetjp_732_;
}
v_resetjp_732_:
{
lean_object* v___x_736_; 
if (v_isShared_734_ == 0)
{
v___x_736_ = v___x_733_;
goto v_reusejp_735_;
}
else
{
lean_object* v_reuseFailAlloc_737_; 
v_reuseFailAlloc_737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_737_, 0, v_a_731_);
v___x_736_ = v_reuseFailAlloc_737_;
goto v_reusejp_735_;
}
v_reusejp_735_:
{
return v___x_736_;
}
}
}
}
else
{
lean_object* v_a_739_; lean_object* v___x_741_; uint8_t v_isShared_742_; uint8_t v_isSharedCheck_746_; 
lean_dec(v_a_712_);
lean_del_object(v___x_595_);
lean_dec(v_snd_593_);
v_a_739_ = lean_ctor_get(v___x_714_, 0);
v_isSharedCheck_746_ = !lean_is_exclusive(v___x_714_);
if (v_isSharedCheck_746_ == 0)
{
v___x_741_ = v___x_714_;
v_isShared_742_ = v_isSharedCheck_746_;
goto v_resetjp_740_;
}
else
{
lean_inc(v_a_739_);
lean_dec(v___x_714_);
v___x_741_ = lean_box(0);
v_isShared_742_ = v_isSharedCheck_746_;
goto v_resetjp_740_;
}
v_resetjp_740_:
{
lean_object* v___x_744_; 
if (v_isShared_742_ == 0)
{
v___x_744_ = v___x_741_;
goto v_reusejp_743_;
}
else
{
lean_object* v_reuseFailAlloc_745_; 
v_reuseFailAlloc_745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_745_, 0, v_a_739_);
v___x_744_ = v_reuseFailAlloc_745_;
goto v_reusejp_743_;
}
v_reusejp_743_:
{
return v___x_744_;
}
}
}
}
else
{
lean_object* v_a_747_; lean_object* v___x_749_; uint8_t v_isShared_750_; uint8_t v_isSharedCheck_754_; 
lean_del_object(v___x_595_);
lean_dec(v_snd_593_);
v_a_747_ = lean_ctor_get(v___x_711_, 0);
v_isSharedCheck_754_ = !lean_is_exclusive(v___x_711_);
if (v_isSharedCheck_754_ == 0)
{
v___x_749_ = v___x_711_;
v_isShared_750_ = v_isSharedCheck_754_;
goto v_resetjp_748_;
}
else
{
lean_inc(v_a_747_);
lean_dec(v___x_711_);
v___x_749_ = lean_box(0);
v_isShared_750_ = v_isSharedCheck_754_;
goto v_resetjp_748_;
}
v_resetjp_748_:
{
lean_object* v___x_752_; 
if (v_isShared_750_ == 0)
{
v___x_752_ = v___x_749_;
goto v_reusejp_751_;
}
else
{
lean_object* v_reuseFailAlloc_753_; 
v_reuseFailAlloc_753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_753_, 0, v_a_747_);
v___x_752_ = v_reuseFailAlloc_753_;
goto v_reusejp_751_;
}
v_reusejp_751_:
{
return v___x_752_;
}
}
}
}
else
{
v___y_614_ = v___y_584_;
v___y_615_ = v___y_585_;
v___y_616_ = v___y_586_;
v___y_617_ = v___y_587_;
v___y_618_ = v___y_588_;
v___y_619_ = v___y_589_;
goto v___jp_613_;
}
}
else
{
v___y_614_ = v___y_584_;
v___y_615_ = v___y_585_;
v___y_616_ = v___y_586_;
v___y_617_ = v___y_587_;
v___y_618_ = v___y_588_;
v___y_619_ = v___y_589_;
goto v___jp_613_;
}
v___jp_613_:
{
if (lean_obj_tag(v_a_612_) == 1)
{
lean_object* v_fvarId_620_; uint8_t v___x_621_; 
v_fvarId_620_ = lean_ctor_get(v_a_612_, 0);
lean_inc(v_fvarId_620_);
lean_dec_ref_known(v_a_612_, 1);
v___x_621_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__0___redArg(v_snd_593_, v_fvarId_620_);
if (v___x_621_ == 0)
{
lean_dec(v_fvarId_620_);
v_a_599_ = v_snd_593_;
goto v___jp_598_;
}
else
{
lean_object* v___x_622_; 
lean_inc(v_fvarId_620_);
v___x_622_ = l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__1___redArg(v_fvarId_620_, v___y_615_);
if (lean_obj_tag(v___x_622_) == 0)
{
lean_object* v_a_623_; lean_object* v___x_624_; 
v_a_623_ = lean_ctor_get(v___x_622_, 0);
lean_inc_n(v_a_623_, 2);
lean_dec_ref_known(v___x_622_, 1);
v___x_624_ = l_Lean_Meta_Sym_getLevel___redArg(v_a_623_, v___y_615_, v___y_616_, v___y_617_, v___y_618_, v___y_619_);
if (lean_obj_tag(v___x_624_) == 0)
{
lean_object* v_a_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; 
v_a_625_ = lean_ctor_get(v___x_624_, 0);
lean_inc(v_a_625_);
lean_dec_ref_known(v___x_624_, 1);
v___x_626_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__7_spec__11_spec__16___closed__1));
v___x_627_ = lean_box(0);
v___x_628_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_628_, 0, v_a_625_);
lean_ctor_set(v___x_628_, 1, v___x_627_);
lean_inc_ref(v___x_628_);
v___x_629_ = l_Lean_Meta_Sym_Internal_mkConstS___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__2___redArg(v___x_626_, v___x_628_, v___y_615_);
if (lean_obj_tag(v___x_629_) == 0)
{
lean_object* v_a_630_; lean_object* v___x_631_; 
v_a_630_ = lean_ctor_get(v___x_629_, 0);
lean_inc(v_a_630_);
lean_dec_ref_known(v___x_629_, 1);
lean_inc(v_a_623_);
v___x_631_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__3(v_a_630_, v_a_623_, v___y_614_, v___y_615_, v___y_616_, v___y_617_, v___y_618_, v___y_619_);
if (lean_obj_tag(v___x_631_) == 0)
{
lean_object* v_a_632_; lean_object* v___x_633_; lean_object* v___x_634_; 
v_a_632_ = lean_ctor_get(v___x_631_, 0);
lean_inc(v_a_632_);
lean_dec_ref_known(v___x_631_, 1);
v___x_633_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__7_spec__11_spec__16___closed__3));
v___x_634_ = l_Lean_Meta_Sym_Internal_mkConstS___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__2___redArg(v___x_633_, v___x_628_, v___y_615_);
if (lean_obj_tag(v___x_634_) == 0)
{
lean_object* v_a_635_; lean_object* v___x_636_; lean_object* v___x_637_; 
v_a_635_ = lean_ctor_get(v___x_634_, 0);
lean_inc(v_a_635_);
lean_dec_ref_known(v___x_634_, 1);
lean_inc(v_val_607_);
v___x_636_ = l_Lean_LocalDecl_toExpr(v_val_607_);
v___x_637_ = l_Lean_Meta_Sym_shareCommonInc(v___x_636_, v___y_614_, v___y_615_, v___y_616_, v___y_617_, v___y_618_, v___y_619_);
if (lean_obj_tag(v___x_637_) == 0)
{
lean_object* v_a_638_; lean_object* v___x_639_; 
v_a_638_ = lean_ctor_get(v___x_637_, 0);
lean_inc(v_a_638_);
lean_dec_ref_known(v___x_637_, 1);
v___x_639_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__4(v_a_635_, v_a_623_, v_a_638_, v___y_614_, v___y_615_, v___y_616_, v___y_617_, v___y_618_, v___y_619_);
if (lean_obj_tag(v___x_639_) == 0)
{
lean_object* v_a_640_; lean_object* v___x_641_; 
v_a_640_ = lean_ctor_get(v___x_639_, 0);
lean_inc(v_a_640_);
lean_dec_ref_known(v___x_639_, 1);
v___x_641_ = l_Lean_Meta_Sym_registerInstance___redArg(v_a_632_, v_a_640_, v___y_615_);
if (lean_obj_tag(v___x_641_) == 0)
{
lean_object* v___x_642_; 
lean_dec_ref_known(v___x_641_, 1);
v___x_642_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__5___redArg(v_snd_593_, v_fvarId_620_);
lean_dec(v_fvarId_620_);
v_a_599_ = v___x_642_;
goto v___jp_598_;
}
else
{
lean_object* v_a_643_; lean_object* v___x_645_; uint8_t v_isShared_646_; uint8_t v_isSharedCheck_650_; 
lean_dec(v_fvarId_620_);
lean_del_object(v___x_595_);
lean_dec(v_snd_593_);
v_a_643_ = lean_ctor_get(v___x_641_, 0);
v_isSharedCheck_650_ = !lean_is_exclusive(v___x_641_);
if (v_isSharedCheck_650_ == 0)
{
v___x_645_ = v___x_641_;
v_isShared_646_ = v_isSharedCheck_650_;
goto v_resetjp_644_;
}
else
{
lean_inc(v_a_643_);
lean_dec(v___x_641_);
v___x_645_ = lean_box(0);
v_isShared_646_ = v_isSharedCheck_650_;
goto v_resetjp_644_;
}
v_resetjp_644_:
{
lean_object* v___x_648_; 
if (v_isShared_646_ == 0)
{
v___x_648_ = v___x_645_;
goto v_reusejp_647_;
}
else
{
lean_object* v_reuseFailAlloc_649_; 
v_reuseFailAlloc_649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_649_, 0, v_a_643_);
v___x_648_ = v_reuseFailAlloc_649_;
goto v_reusejp_647_;
}
v_reusejp_647_:
{
return v___x_648_;
}
}
}
}
else
{
lean_object* v_a_651_; lean_object* v___x_653_; uint8_t v_isShared_654_; uint8_t v_isSharedCheck_658_; 
lean_dec(v_a_632_);
lean_dec(v_fvarId_620_);
lean_del_object(v___x_595_);
lean_dec(v_snd_593_);
v_a_651_ = lean_ctor_get(v___x_639_, 0);
v_isSharedCheck_658_ = !lean_is_exclusive(v___x_639_);
if (v_isSharedCheck_658_ == 0)
{
v___x_653_ = v___x_639_;
v_isShared_654_ = v_isSharedCheck_658_;
goto v_resetjp_652_;
}
else
{
lean_inc(v_a_651_);
lean_dec(v___x_639_);
v___x_653_ = lean_box(0);
v_isShared_654_ = v_isSharedCheck_658_;
goto v_resetjp_652_;
}
v_resetjp_652_:
{
lean_object* v___x_656_; 
if (v_isShared_654_ == 0)
{
v___x_656_ = v___x_653_;
goto v_reusejp_655_;
}
else
{
lean_object* v_reuseFailAlloc_657_; 
v_reuseFailAlloc_657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_657_, 0, v_a_651_);
v___x_656_ = v_reuseFailAlloc_657_;
goto v_reusejp_655_;
}
v_reusejp_655_:
{
return v___x_656_;
}
}
}
}
else
{
lean_object* v_a_659_; lean_object* v___x_661_; uint8_t v_isShared_662_; uint8_t v_isSharedCheck_666_; 
lean_dec(v_a_635_);
lean_dec(v_a_632_);
lean_dec(v_a_623_);
lean_dec(v_fvarId_620_);
lean_del_object(v___x_595_);
lean_dec(v_snd_593_);
v_a_659_ = lean_ctor_get(v___x_637_, 0);
v_isSharedCheck_666_ = !lean_is_exclusive(v___x_637_);
if (v_isSharedCheck_666_ == 0)
{
v___x_661_ = v___x_637_;
v_isShared_662_ = v_isSharedCheck_666_;
goto v_resetjp_660_;
}
else
{
lean_inc(v_a_659_);
lean_dec(v___x_637_);
v___x_661_ = lean_box(0);
v_isShared_662_ = v_isSharedCheck_666_;
goto v_resetjp_660_;
}
v_resetjp_660_:
{
lean_object* v___x_664_; 
if (v_isShared_662_ == 0)
{
v___x_664_ = v___x_661_;
goto v_reusejp_663_;
}
else
{
lean_object* v_reuseFailAlloc_665_; 
v_reuseFailAlloc_665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_665_, 0, v_a_659_);
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
else
{
lean_object* v_a_667_; lean_object* v___x_669_; uint8_t v_isShared_670_; uint8_t v_isSharedCheck_674_; 
lean_dec(v_a_632_);
lean_dec(v_a_623_);
lean_dec(v_fvarId_620_);
lean_del_object(v___x_595_);
lean_dec(v_snd_593_);
v_a_667_ = lean_ctor_get(v___x_634_, 0);
v_isSharedCheck_674_ = !lean_is_exclusive(v___x_634_);
if (v_isSharedCheck_674_ == 0)
{
v___x_669_ = v___x_634_;
v_isShared_670_ = v_isSharedCheck_674_;
goto v_resetjp_668_;
}
else
{
lean_inc(v_a_667_);
lean_dec(v___x_634_);
v___x_669_ = lean_box(0);
v_isShared_670_ = v_isSharedCheck_674_;
goto v_resetjp_668_;
}
v_resetjp_668_:
{
lean_object* v___x_672_; 
if (v_isShared_670_ == 0)
{
v___x_672_ = v___x_669_;
goto v_reusejp_671_;
}
else
{
lean_object* v_reuseFailAlloc_673_; 
v_reuseFailAlloc_673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_673_, 0, v_a_667_);
v___x_672_ = v_reuseFailAlloc_673_;
goto v_reusejp_671_;
}
v_reusejp_671_:
{
return v___x_672_;
}
}
}
}
else
{
lean_object* v_a_675_; lean_object* v___x_677_; uint8_t v_isShared_678_; uint8_t v_isSharedCheck_682_; 
lean_dec_ref_known(v___x_628_, 2);
lean_dec(v_a_623_);
lean_dec(v_fvarId_620_);
lean_del_object(v___x_595_);
lean_dec(v_snd_593_);
v_a_675_ = lean_ctor_get(v___x_631_, 0);
v_isSharedCheck_682_ = !lean_is_exclusive(v___x_631_);
if (v_isSharedCheck_682_ == 0)
{
v___x_677_ = v___x_631_;
v_isShared_678_ = v_isSharedCheck_682_;
goto v_resetjp_676_;
}
else
{
lean_inc(v_a_675_);
lean_dec(v___x_631_);
v___x_677_ = lean_box(0);
v_isShared_678_ = v_isSharedCheck_682_;
goto v_resetjp_676_;
}
v_resetjp_676_:
{
lean_object* v___x_680_; 
if (v_isShared_678_ == 0)
{
v___x_680_ = v___x_677_;
goto v_reusejp_679_;
}
else
{
lean_object* v_reuseFailAlloc_681_; 
v_reuseFailAlloc_681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_681_, 0, v_a_675_);
v___x_680_ = v_reuseFailAlloc_681_;
goto v_reusejp_679_;
}
v_reusejp_679_:
{
return v___x_680_;
}
}
}
}
else
{
lean_object* v_a_683_; lean_object* v___x_685_; uint8_t v_isShared_686_; uint8_t v_isSharedCheck_690_; 
lean_dec_ref_known(v___x_628_, 2);
lean_dec(v_a_623_);
lean_dec(v_fvarId_620_);
lean_del_object(v___x_595_);
lean_dec(v_snd_593_);
v_a_683_ = lean_ctor_get(v___x_629_, 0);
v_isSharedCheck_690_ = !lean_is_exclusive(v___x_629_);
if (v_isSharedCheck_690_ == 0)
{
v___x_685_ = v___x_629_;
v_isShared_686_ = v_isSharedCheck_690_;
goto v_resetjp_684_;
}
else
{
lean_inc(v_a_683_);
lean_dec(v___x_629_);
v___x_685_ = lean_box(0);
v_isShared_686_ = v_isSharedCheck_690_;
goto v_resetjp_684_;
}
v_resetjp_684_:
{
lean_object* v___x_688_; 
if (v_isShared_686_ == 0)
{
v___x_688_ = v___x_685_;
goto v_reusejp_687_;
}
else
{
lean_object* v_reuseFailAlloc_689_; 
v_reuseFailAlloc_689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_689_, 0, v_a_683_);
v___x_688_ = v_reuseFailAlloc_689_;
goto v_reusejp_687_;
}
v_reusejp_687_:
{
return v___x_688_;
}
}
}
}
else
{
lean_object* v_a_691_; lean_object* v___x_693_; uint8_t v_isShared_694_; uint8_t v_isSharedCheck_698_; 
lean_dec(v_a_623_);
lean_dec(v_fvarId_620_);
lean_del_object(v___x_595_);
lean_dec(v_snd_593_);
v_a_691_ = lean_ctor_get(v___x_624_, 0);
v_isSharedCheck_698_ = !lean_is_exclusive(v___x_624_);
if (v_isSharedCheck_698_ == 0)
{
v___x_693_ = v___x_624_;
v_isShared_694_ = v_isSharedCheck_698_;
goto v_resetjp_692_;
}
else
{
lean_inc(v_a_691_);
lean_dec(v___x_624_);
v___x_693_ = lean_box(0);
v_isShared_694_ = v_isSharedCheck_698_;
goto v_resetjp_692_;
}
v_resetjp_692_:
{
lean_object* v___x_696_; 
if (v_isShared_694_ == 0)
{
v___x_696_ = v___x_693_;
goto v_reusejp_695_;
}
else
{
lean_object* v_reuseFailAlloc_697_; 
v_reuseFailAlloc_697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_697_, 0, v_a_691_);
v___x_696_ = v_reuseFailAlloc_697_;
goto v_reusejp_695_;
}
v_reusejp_695_:
{
return v___x_696_;
}
}
}
}
else
{
lean_object* v_a_699_; lean_object* v___x_701_; uint8_t v_isShared_702_; uint8_t v_isSharedCheck_706_; 
lean_dec(v_fvarId_620_);
lean_del_object(v___x_595_);
lean_dec(v_snd_593_);
v_a_699_ = lean_ctor_get(v___x_622_, 0);
v_isSharedCheck_706_ = !lean_is_exclusive(v___x_622_);
if (v_isSharedCheck_706_ == 0)
{
v___x_701_ = v___x_622_;
v_isShared_702_ = v_isSharedCheck_706_;
goto v_resetjp_700_;
}
else
{
lean_inc(v_a_699_);
lean_dec(v___x_622_);
v___x_701_ = lean_box(0);
v_isShared_702_ = v_isSharedCheck_706_;
goto v_resetjp_700_;
}
v_resetjp_700_:
{
lean_object* v___x_704_; 
if (v_isShared_702_ == 0)
{
v___x_704_ = v___x_701_;
goto v_reusejp_703_;
}
else
{
lean_object* v_reuseFailAlloc_705_; 
v_reuseFailAlloc_705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_705_, 0, v_a_699_);
v___x_704_ = v_reuseFailAlloc_705_;
goto v_reusejp_703_;
}
v_reusejp_703_:
{
return v___x_704_;
}
}
}
}
}
else
{
lean_dec(v_a_612_);
v_a_599_ = v_snd_593_;
goto v___jp_598_;
}
}
}
else
{
lean_object* v_a_755_; lean_object* v___x_757_; uint8_t v_isShared_758_; uint8_t v_isSharedCheck_762_; 
lean_del_object(v___x_595_);
lean_dec(v_snd_593_);
v_a_755_ = lean_ctor_get(v___x_611_, 0);
v_isSharedCheck_762_ = !lean_is_exclusive(v___x_611_);
if (v_isSharedCheck_762_ == 0)
{
v___x_757_ = v___x_611_;
v_isShared_758_ = v_isSharedCheck_762_;
goto v_resetjp_756_;
}
else
{
lean_inc(v_a_755_);
lean_dec(v___x_611_);
v___x_757_ = lean_box(0);
v_isShared_758_ = v_isSharedCheck_762_;
goto v_resetjp_756_;
}
v_resetjp_756_:
{
lean_object* v___x_760_; 
if (v_isShared_758_ == 0)
{
v___x_760_ = v___x_757_;
goto v_reusejp_759_;
}
else
{
lean_object* v_reuseFailAlloc_761_; 
v_reuseFailAlloc_761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_761_, 0, v_a_755_);
v___x_760_ = v_reuseFailAlloc_761_;
goto v_reusejp_759_;
}
v_reusejp_759_:
{
return v___x_760_;
}
}
}
}
else
{
v_a_599_ = v_snd_593_;
goto v___jp_598_;
}
}
else
{
v_a_599_ = v_snd_593_;
goto v___jp_598_;
}
}
v___jp_598_:
{
lean_object* v___x_601_; 
if (v_isShared_596_ == 0)
{
lean_ctor_set(v___x_595_, 1, v_a_599_);
lean_ctor_set(v___x_595_, 0, v___x_597_);
v___x_601_ = v___x_595_;
goto v_reusejp_600_;
}
else
{
lean_object* v_reuseFailAlloc_605_; 
v_reuseFailAlloc_605_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_605_, 0, v___x_597_);
lean_ctor_set(v_reuseFailAlloc_605_, 1, v_a_599_);
v___x_601_ = v_reuseFailAlloc_605_;
goto v_reusejp_600_;
}
v_reusejp_600_:
{
size_t v___x_602_; size_t v___x_603_; lean_object* v___x_604_; 
v___x_602_ = ((size_t)1ULL);
v___x_603_ = lean_usize_add(v_i_582_, v___x_602_);
v___x_604_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__7_spec__11_spec__16(v_as_580_, v_sz_581_, v___x_603_, v___x_601_, v___y_584_, v___y_585_, v___y_586_, v___y_587_, v___y_588_, v___y_589_);
return v___x_604_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__7_spec__11___boxed(lean_object* v_as_765_, lean_object* v_sz_766_, lean_object* v_i_767_, lean_object* v_b_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_){
_start:
{
size_t v_sz_boxed_776_; size_t v_i_boxed_777_; lean_object* v_res_778_; 
v_sz_boxed_776_ = lean_unbox_usize(v_sz_766_);
lean_dec(v_sz_766_);
v_i_boxed_777_ = lean_unbox_usize(v_i_767_);
lean_dec(v_i_767_);
v_res_778_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__7_spec__11(v_as_765_, v_sz_boxed_776_, v_i_boxed_777_, v_b_768_, v___y_769_, v___y_770_, v___y_771_, v___y_772_, v___y_773_, v___y_774_);
lean_dec(v___y_774_);
lean_dec_ref(v___y_773_);
lean_dec(v___y_772_);
lean_dec_ref(v___y_771_);
lean_dec(v___y_770_);
lean_dec_ref(v___y_769_);
lean_dec_ref(v_as_765_);
return v_res_778_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__7_spec__10_spec__14_spec__16(lean_object* v_as_779_, size_t v_sz_780_, size_t v_i_781_, lean_object* v_b_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_){
_start:
{
uint8_t v___x_790_; 
v___x_790_ = lean_usize_dec_lt(v_i_781_, v_sz_780_);
if (v___x_790_ == 0)
{
lean_object* v___x_791_; 
v___x_791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_791_, 0, v_b_782_);
return v___x_791_;
}
else
{
lean_object* v_snd_792_; lean_object* v___x_794_; uint8_t v_isShared_795_; uint8_t v_isSharedCheck_962_; 
v_snd_792_ = lean_ctor_get(v_b_782_, 1);
v_isSharedCheck_962_ = !lean_is_exclusive(v_b_782_);
if (v_isSharedCheck_962_ == 0)
{
lean_object* v_unused_963_; 
v_unused_963_ = lean_ctor_get(v_b_782_, 0);
lean_dec(v_unused_963_);
v___x_794_ = v_b_782_;
v_isShared_795_ = v_isSharedCheck_962_;
goto v_resetjp_793_;
}
else
{
lean_inc(v_snd_792_);
lean_dec(v_b_782_);
v___x_794_ = lean_box(0);
v_isShared_795_ = v_isSharedCheck_962_;
goto v_resetjp_793_;
}
v_resetjp_793_:
{
lean_object* v___x_796_; lean_object* v_a_798_; lean_object* v_a_805_; 
v___x_796_ = lean_box(0);
v_a_805_ = lean_array_uget_borrowed(v_as_779_, v_i_781_);
if (lean_obj_tag(v_a_805_) == 0)
{
v_a_798_ = v_snd_792_;
goto v___jp_797_;
}
else
{
lean_object* v_val_806_; uint8_t v___x_807_; 
v_val_806_ = lean_ctor_get(v_a_805_, 0);
v___x_807_ = l_Lean_LocalDecl_isImplementationDetail(v_val_806_);
if (v___x_807_ == 0)
{
uint8_t v___x_808_; 
v___x_808_ = l_Lean_LocalDecl_isLet(v_val_806_, v___x_807_);
if (v___x_808_ == 0)
{
lean_object* v___x_809_; lean_object* v___x_810_; 
v___x_809_ = l_Lean_LocalDecl_type(v_val_806_);
v___x_810_ = l_Lean_Meta_Sym_instantiateMVarsS(v___x_809_, v___y_783_, v___y_784_, v___y_785_, v___y_786_, v___y_787_, v___y_788_);
if (lean_obj_tag(v___x_810_) == 0)
{
lean_object* v_a_811_; lean_object* v___y_813_; lean_object* v___y_814_; lean_object* v___y_815_; lean_object* v___y_816_; lean_object* v___y_817_; lean_object* v___y_818_; 
v_a_811_ = lean_ctor_get(v___x_810_, 0);
lean_inc(v_a_811_);
lean_dec_ref_known(v___x_810_, 1);
if (lean_obj_tag(v_a_811_) == 3)
{
lean_object* v_u_906_; 
v_u_906_ = lean_ctor_get(v_a_811_, 0);
if (lean_obj_tag(v_u_906_) == 1)
{
lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; 
lean_inc_ref(v_u_906_);
lean_dec_ref_known(v_a_811_, 1);
v___x_907_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__7_spec__11_spec__16___closed__1));
v___x_908_ = lean_box(0);
v___x_909_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_909_, 0, v_u_906_);
lean_ctor_set(v___x_909_, 1, v___x_908_);
v___x_910_ = l_Lean_Meta_Sym_Internal_mkConstS___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__2___redArg(v___x_907_, v___x_909_, v___y_784_);
if (lean_obj_tag(v___x_910_) == 0)
{
lean_object* v_a_911_; lean_object* v___x_912_; lean_object* v___x_913_; 
v_a_911_ = lean_ctor_get(v___x_910_, 0);
lean_inc(v_a_911_);
lean_dec_ref_known(v___x_910_, 1);
lean_inc(v_val_806_);
v___x_912_ = l_Lean_LocalDecl_toExpr(v_val_806_);
v___x_913_ = l_Lean_Meta_Sym_shareCommonInc(v___x_912_, v___y_783_, v___y_784_, v___y_785_, v___y_786_, v___y_787_, v___y_788_);
if (lean_obj_tag(v___x_913_) == 0)
{
lean_object* v_a_914_; lean_object* v___x_915_; 
v_a_914_ = lean_ctor_get(v___x_913_, 0);
lean_inc(v_a_914_);
lean_dec_ref_known(v___x_913_, 1);
v___x_915_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__3(v_a_911_, v_a_914_, v___y_783_, v___y_784_, v___y_785_, v___y_786_, v___y_787_, v___y_788_);
if (lean_obj_tag(v___x_915_) == 0)
{
lean_object* v_a_916_; lean_object* v___x_917_; 
v_a_916_ = lean_ctor_get(v___x_915_, 0);
lean_inc(v_a_916_);
lean_dec_ref_known(v___x_915_, 1);
v___x_917_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v_a_916_, v___y_784_, v___y_785_, v___y_786_, v___y_787_, v___y_788_);
if (lean_obj_tag(v___x_917_) == 0)
{
lean_object* v_a_918_; 
v_a_918_ = lean_ctor_get(v___x_917_, 0);
lean_inc(v_a_918_);
lean_dec_ref_known(v___x_917_, 1);
if (lean_obj_tag(v_a_918_) == 0)
{
lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; 
v___x_919_ = l_Lean_LocalDecl_fvarId(v_val_806_);
v___x_920_ = lean_box(0);
v___x_921_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__6___redArg(v_snd_792_, v___x_919_, v___x_920_);
v_a_798_ = v___x_921_;
goto v___jp_797_;
}
else
{
lean_dec_ref_known(v_a_918_, 1);
v_a_798_ = v_snd_792_;
goto v___jp_797_;
}
}
else
{
lean_object* v_a_922_; lean_object* v___x_924_; uint8_t v_isShared_925_; uint8_t v_isSharedCheck_929_; 
lean_del_object(v___x_794_);
lean_dec(v_snd_792_);
v_a_922_ = lean_ctor_get(v___x_917_, 0);
v_isSharedCheck_929_ = !lean_is_exclusive(v___x_917_);
if (v_isSharedCheck_929_ == 0)
{
v___x_924_ = v___x_917_;
v_isShared_925_ = v_isSharedCheck_929_;
goto v_resetjp_923_;
}
else
{
lean_inc(v_a_922_);
lean_dec(v___x_917_);
v___x_924_ = lean_box(0);
v_isShared_925_ = v_isSharedCheck_929_;
goto v_resetjp_923_;
}
v_resetjp_923_:
{
lean_object* v___x_927_; 
if (v_isShared_925_ == 0)
{
v___x_927_ = v___x_924_;
goto v_reusejp_926_;
}
else
{
lean_object* v_reuseFailAlloc_928_; 
v_reuseFailAlloc_928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_928_, 0, v_a_922_);
v___x_927_ = v_reuseFailAlloc_928_;
goto v_reusejp_926_;
}
v_reusejp_926_:
{
return v___x_927_;
}
}
}
}
else
{
lean_object* v_a_930_; lean_object* v___x_932_; uint8_t v_isShared_933_; uint8_t v_isSharedCheck_937_; 
lean_del_object(v___x_794_);
lean_dec(v_snd_792_);
v_a_930_ = lean_ctor_get(v___x_915_, 0);
v_isSharedCheck_937_ = !lean_is_exclusive(v___x_915_);
if (v_isSharedCheck_937_ == 0)
{
v___x_932_ = v___x_915_;
v_isShared_933_ = v_isSharedCheck_937_;
goto v_resetjp_931_;
}
else
{
lean_inc(v_a_930_);
lean_dec(v___x_915_);
v___x_932_ = lean_box(0);
v_isShared_933_ = v_isSharedCheck_937_;
goto v_resetjp_931_;
}
v_resetjp_931_:
{
lean_object* v___x_935_; 
if (v_isShared_933_ == 0)
{
v___x_935_ = v___x_932_;
goto v_reusejp_934_;
}
else
{
lean_object* v_reuseFailAlloc_936_; 
v_reuseFailAlloc_936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_936_, 0, v_a_930_);
v___x_935_ = v_reuseFailAlloc_936_;
goto v_reusejp_934_;
}
v_reusejp_934_:
{
return v___x_935_;
}
}
}
}
else
{
lean_object* v_a_938_; lean_object* v___x_940_; uint8_t v_isShared_941_; uint8_t v_isSharedCheck_945_; 
lean_dec(v_a_911_);
lean_del_object(v___x_794_);
lean_dec(v_snd_792_);
v_a_938_ = lean_ctor_get(v___x_913_, 0);
v_isSharedCheck_945_ = !lean_is_exclusive(v___x_913_);
if (v_isSharedCheck_945_ == 0)
{
v___x_940_ = v___x_913_;
v_isShared_941_ = v_isSharedCheck_945_;
goto v_resetjp_939_;
}
else
{
lean_inc(v_a_938_);
lean_dec(v___x_913_);
v___x_940_ = lean_box(0);
v_isShared_941_ = v_isSharedCheck_945_;
goto v_resetjp_939_;
}
v_resetjp_939_:
{
lean_object* v___x_943_; 
if (v_isShared_941_ == 0)
{
v___x_943_ = v___x_940_;
goto v_reusejp_942_;
}
else
{
lean_object* v_reuseFailAlloc_944_; 
v_reuseFailAlloc_944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_944_, 0, v_a_938_);
v___x_943_ = v_reuseFailAlloc_944_;
goto v_reusejp_942_;
}
v_reusejp_942_:
{
return v___x_943_;
}
}
}
}
else
{
lean_object* v_a_946_; lean_object* v___x_948_; uint8_t v_isShared_949_; uint8_t v_isSharedCheck_953_; 
lean_del_object(v___x_794_);
lean_dec(v_snd_792_);
v_a_946_ = lean_ctor_get(v___x_910_, 0);
v_isSharedCheck_953_ = !lean_is_exclusive(v___x_910_);
if (v_isSharedCheck_953_ == 0)
{
v___x_948_ = v___x_910_;
v_isShared_949_ = v_isSharedCheck_953_;
goto v_resetjp_947_;
}
else
{
lean_inc(v_a_946_);
lean_dec(v___x_910_);
v___x_948_ = lean_box(0);
v_isShared_949_ = v_isSharedCheck_953_;
goto v_resetjp_947_;
}
v_resetjp_947_:
{
lean_object* v___x_951_; 
if (v_isShared_949_ == 0)
{
v___x_951_ = v___x_948_;
goto v_reusejp_950_;
}
else
{
lean_object* v_reuseFailAlloc_952_; 
v_reuseFailAlloc_952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_952_, 0, v_a_946_);
v___x_951_ = v_reuseFailAlloc_952_;
goto v_reusejp_950_;
}
v_reusejp_950_:
{
return v___x_951_;
}
}
}
}
else
{
v___y_813_ = v___y_783_;
v___y_814_ = v___y_784_;
v___y_815_ = v___y_785_;
v___y_816_ = v___y_786_;
v___y_817_ = v___y_787_;
v___y_818_ = v___y_788_;
goto v___jp_812_;
}
}
else
{
v___y_813_ = v___y_783_;
v___y_814_ = v___y_784_;
v___y_815_ = v___y_785_;
v___y_816_ = v___y_786_;
v___y_817_ = v___y_787_;
v___y_818_ = v___y_788_;
goto v___jp_812_;
}
v___jp_812_:
{
if (lean_obj_tag(v_a_811_) == 1)
{
lean_object* v_fvarId_819_; uint8_t v___x_820_; 
v_fvarId_819_ = lean_ctor_get(v_a_811_, 0);
lean_inc(v_fvarId_819_);
lean_dec_ref_known(v_a_811_, 1);
v___x_820_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__0___redArg(v_snd_792_, v_fvarId_819_);
if (v___x_820_ == 0)
{
lean_dec(v_fvarId_819_);
v_a_798_ = v_snd_792_;
goto v___jp_797_;
}
else
{
lean_object* v___x_821_; 
lean_inc(v_fvarId_819_);
v___x_821_ = l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__1___redArg(v_fvarId_819_, v___y_814_);
if (lean_obj_tag(v___x_821_) == 0)
{
lean_object* v_a_822_; lean_object* v___x_823_; 
v_a_822_ = lean_ctor_get(v___x_821_, 0);
lean_inc_n(v_a_822_, 2);
lean_dec_ref_known(v___x_821_, 1);
v___x_823_ = l_Lean_Meta_Sym_getLevel___redArg(v_a_822_, v___y_814_, v___y_815_, v___y_816_, v___y_817_, v___y_818_);
if (lean_obj_tag(v___x_823_) == 0)
{
lean_object* v_a_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; 
v_a_824_ = lean_ctor_get(v___x_823_, 0);
lean_inc(v_a_824_);
lean_dec_ref_known(v___x_823_, 1);
v___x_825_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__7_spec__11_spec__16___closed__1));
v___x_826_ = lean_box(0);
v___x_827_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_827_, 0, v_a_824_);
lean_ctor_set(v___x_827_, 1, v___x_826_);
lean_inc_ref(v___x_827_);
v___x_828_ = l_Lean_Meta_Sym_Internal_mkConstS___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__2___redArg(v___x_825_, v___x_827_, v___y_814_);
if (lean_obj_tag(v___x_828_) == 0)
{
lean_object* v_a_829_; lean_object* v___x_830_; 
v_a_829_ = lean_ctor_get(v___x_828_, 0);
lean_inc(v_a_829_);
lean_dec_ref_known(v___x_828_, 1);
lean_inc(v_a_822_);
v___x_830_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__3(v_a_829_, v_a_822_, v___y_813_, v___y_814_, v___y_815_, v___y_816_, v___y_817_, v___y_818_);
if (lean_obj_tag(v___x_830_) == 0)
{
lean_object* v_a_831_; lean_object* v___x_832_; lean_object* v___x_833_; 
v_a_831_ = lean_ctor_get(v___x_830_, 0);
lean_inc(v_a_831_);
lean_dec_ref_known(v___x_830_, 1);
v___x_832_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__7_spec__11_spec__16___closed__3));
v___x_833_ = l_Lean_Meta_Sym_Internal_mkConstS___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__2___redArg(v___x_832_, v___x_827_, v___y_814_);
if (lean_obj_tag(v___x_833_) == 0)
{
lean_object* v_a_834_; lean_object* v___x_835_; lean_object* v___x_836_; 
v_a_834_ = lean_ctor_get(v___x_833_, 0);
lean_inc(v_a_834_);
lean_dec_ref_known(v___x_833_, 1);
lean_inc(v_val_806_);
v___x_835_ = l_Lean_LocalDecl_toExpr(v_val_806_);
v___x_836_ = l_Lean_Meta_Sym_shareCommonInc(v___x_835_, v___y_813_, v___y_814_, v___y_815_, v___y_816_, v___y_817_, v___y_818_);
if (lean_obj_tag(v___x_836_) == 0)
{
lean_object* v_a_837_; lean_object* v___x_838_; 
v_a_837_ = lean_ctor_get(v___x_836_, 0);
lean_inc(v_a_837_);
lean_dec_ref_known(v___x_836_, 1);
v___x_838_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__4(v_a_834_, v_a_822_, v_a_837_, v___y_813_, v___y_814_, v___y_815_, v___y_816_, v___y_817_, v___y_818_);
if (lean_obj_tag(v___x_838_) == 0)
{
lean_object* v_a_839_; lean_object* v___x_840_; 
v_a_839_ = lean_ctor_get(v___x_838_, 0);
lean_inc(v_a_839_);
lean_dec_ref_known(v___x_838_, 1);
v___x_840_ = l_Lean_Meta_Sym_registerInstance___redArg(v_a_831_, v_a_839_, v___y_814_);
if (lean_obj_tag(v___x_840_) == 0)
{
lean_object* v___x_841_; 
lean_dec_ref_known(v___x_840_, 1);
v___x_841_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__5___redArg(v_snd_792_, v_fvarId_819_);
lean_dec(v_fvarId_819_);
v_a_798_ = v___x_841_;
goto v___jp_797_;
}
else
{
lean_object* v_a_842_; lean_object* v___x_844_; uint8_t v_isShared_845_; uint8_t v_isSharedCheck_849_; 
lean_dec(v_fvarId_819_);
lean_del_object(v___x_794_);
lean_dec(v_snd_792_);
v_a_842_ = lean_ctor_get(v___x_840_, 0);
v_isSharedCheck_849_ = !lean_is_exclusive(v___x_840_);
if (v_isSharedCheck_849_ == 0)
{
v___x_844_ = v___x_840_;
v_isShared_845_ = v_isSharedCheck_849_;
goto v_resetjp_843_;
}
else
{
lean_inc(v_a_842_);
lean_dec(v___x_840_);
v___x_844_ = lean_box(0);
v_isShared_845_ = v_isSharedCheck_849_;
goto v_resetjp_843_;
}
v_resetjp_843_:
{
lean_object* v___x_847_; 
if (v_isShared_845_ == 0)
{
v___x_847_ = v___x_844_;
goto v_reusejp_846_;
}
else
{
lean_object* v_reuseFailAlloc_848_; 
v_reuseFailAlloc_848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_848_, 0, v_a_842_);
v___x_847_ = v_reuseFailAlloc_848_;
goto v_reusejp_846_;
}
v_reusejp_846_:
{
return v___x_847_;
}
}
}
}
else
{
lean_object* v_a_850_; lean_object* v___x_852_; uint8_t v_isShared_853_; uint8_t v_isSharedCheck_857_; 
lean_dec(v_a_831_);
lean_dec(v_fvarId_819_);
lean_del_object(v___x_794_);
lean_dec(v_snd_792_);
v_a_850_ = lean_ctor_get(v___x_838_, 0);
v_isSharedCheck_857_ = !lean_is_exclusive(v___x_838_);
if (v_isSharedCheck_857_ == 0)
{
v___x_852_ = v___x_838_;
v_isShared_853_ = v_isSharedCheck_857_;
goto v_resetjp_851_;
}
else
{
lean_inc(v_a_850_);
lean_dec(v___x_838_);
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
else
{
lean_object* v_a_858_; lean_object* v___x_860_; uint8_t v_isShared_861_; uint8_t v_isSharedCheck_865_; 
lean_dec(v_a_834_);
lean_dec(v_a_831_);
lean_dec(v_a_822_);
lean_dec(v_fvarId_819_);
lean_del_object(v___x_794_);
lean_dec(v_snd_792_);
v_a_858_ = lean_ctor_get(v___x_836_, 0);
v_isSharedCheck_865_ = !lean_is_exclusive(v___x_836_);
if (v_isSharedCheck_865_ == 0)
{
v___x_860_ = v___x_836_;
v_isShared_861_ = v_isSharedCheck_865_;
goto v_resetjp_859_;
}
else
{
lean_inc(v_a_858_);
lean_dec(v___x_836_);
v___x_860_ = lean_box(0);
v_isShared_861_ = v_isSharedCheck_865_;
goto v_resetjp_859_;
}
v_resetjp_859_:
{
lean_object* v___x_863_; 
if (v_isShared_861_ == 0)
{
v___x_863_ = v___x_860_;
goto v_reusejp_862_;
}
else
{
lean_object* v_reuseFailAlloc_864_; 
v_reuseFailAlloc_864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_864_, 0, v_a_858_);
v___x_863_ = v_reuseFailAlloc_864_;
goto v_reusejp_862_;
}
v_reusejp_862_:
{
return v___x_863_;
}
}
}
}
else
{
lean_object* v_a_866_; lean_object* v___x_868_; uint8_t v_isShared_869_; uint8_t v_isSharedCheck_873_; 
lean_dec(v_a_831_);
lean_dec(v_a_822_);
lean_dec(v_fvarId_819_);
lean_del_object(v___x_794_);
lean_dec(v_snd_792_);
v_a_866_ = lean_ctor_get(v___x_833_, 0);
v_isSharedCheck_873_ = !lean_is_exclusive(v___x_833_);
if (v_isSharedCheck_873_ == 0)
{
v___x_868_ = v___x_833_;
v_isShared_869_ = v_isSharedCheck_873_;
goto v_resetjp_867_;
}
else
{
lean_inc(v_a_866_);
lean_dec(v___x_833_);
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
else
{
lean_object* v_a_874_; lean_object* v___x_876_; uint8_t v_isShared_877_; uint8_t v_isSharedCheck_881_; 
lean_dec_ref_known(v___x_827_, 2);
lean_dec(v_a_822_);
lean_dec(v_fvarId_819_);
lean_del_object(v___x_794_);
lean_dec(v_snd_792_);
v_a_874_ = lean_ctor_get(v___x_830_, 0);
v_isSharedCheck_881_ = !lean_is_exclusive(v___x_830_);
if (v_isSharedCheck_881_ == 0)
{
v___x_876_ = v___x_830_;
v_isShared_877_ = v_isSharedCheck_881_;
goto v_resetjp_875_;
}
else
{
lean_inc(v_a_874_);
lean_dec(v___x_830_);
v___x_876_ = lean_box(0);
v_isShared_877_ = v_isSharedCheck_881_;
goto v_resetjp_875_;
}
v_resetjp_875_:
{
lean_object* v___x_879_; 
if (v_isShared_877_ == 0)
{
v___x_879_ = v___x_876_;
goto v_reusejp_878_;
}
else
{
lean_object* v_reuseFailAlloc_880_; 
v_reuseFailAlloc_880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_880_, 0, v_a_874_);
v___x_879_ = v_reuseFailAlloc_880_;
goto v_reusejp_878_;
}
v_reusejp_878_:
{
return v___x_879_;
}
}
}
}
else
{
lean_object* v_a_882_; lean_object* v___x_884_; uint8_t v_isShared_885_; uint8_t v_isSharedCheck_889_; 
lean_dec_ref_known(v___x_827_, 2);
lean_dec(v_a_822_);
lean_dec(v_fvarId_819_);
lean_del_object(v___x_794_);
lean_dec(v_snd_792_);
v_a_882_ = lean_ctor_get(v___x_828_, 0);
v_isSharedCheck_889_ = !lean_is_exclusive(v___x_828_);
if (v_isSharedCheck_889_ == 0)
{
v___x_884_ = v___x_828_;
v_isShared_885_ = v_isSharedCheck_889_;
goto v_resetjp_883_;
}
else
{
lean_inc(v_a_882_);
lean_dec(v___x_828_);
v___x_884_ = lean_box(0);
v_isShared_885_ = v_isSharedCheck_889_;
goto v_resetjp_883_;
}
v_resetjp_883_:
{
lean_object* v___x_887_; 
if (v_isShared_885_ == 0)
{
v___x_887_ = v___x_884_;
goto v_reusejp_886_;
}
else
{
lean_object* v_reuseFailAlloc_888_; 
v_reuseFailAlloc_888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_888_, 0, v_a_882_);
v___x_887_ = v_reuseFailAlloc_888_;
goto v_reusejp_886_;
}
v_reusejp_886_:
{
return v___x_887_;
}
}
}
}
else
{
lean_object* v_a_890_; lean_object* v___x_892_; uint8_t v_isShared_893_; uint8_t v_isSharedCheck_897_; 
lean_dec(v_a_822_);
lean_dec(v_fvarId_819_);
lean_del_object(v___x_794_);
lean_dec(v_snd_792_);
v_a_890_ = lean_ctor_get(v___x_823_, 0);
v_isSharedCheck_897_ = !lean_is_exclusive(v___x_823_);
if (v_isSharedCheck_897_ == 0)
{
v___x_892_ = v___x_823_;
v_isShared_893_ = v_isSharedCheck_897_;
goto v_resetjp_891_;
}
else
{
lean_inc(v_a_890_);
lean_dec(v___x_823_);
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
else
{
lean_object* v_a_898_; lean_object* v___x_900_; uint8_t v_isShared_901_; uint8_t v_isSharedCheck_905_; 
lean_dec(v_fvarId_819_);
lean_del_object(v___x_794_);
lean_dec(v_snd_792_);
v_a_898_ = lean_ctor_get(v___x_821_, 0);
v_isSharedCheck_905_ = !lean_is_exclusive(v___x_821_);
if (v_isSharedCheck_905_ == 0)
{
v___x_900_ = v___x_821_;
v_isShared_901_ = v_isSharedCheck_905_;
goto v_resetjp_899_;
}
else
{
lean_inc(v_a_898_);
lean_dec(v___x_821_);
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
else
{
lean_dec(v_a_811_);
v_a_798_ = v_snd_792_;
goto v___jp_797_;
}
}
}
else
{
lean_object* v_a_954_; lean_object* v___x_956_; uint8_t v_isShared_957_; uint8_t v_isSharedCheck_961_; 
lean_del_object(v___x_794_);
lean_dec(v_snd_792_);
v_a_954_ = lean_ctor_get(v___x_810_, 0);
v_isSharedCheck_961_ = !lean_is_exclusive(v___x_810_);
if (v_isSharedCheck_961_ == 0)
{
v___x_956_ = v___x_810_;
v_isShared_957_ = v_isSharedCheck_961_;
goto v_resetjp_955_;
}
else
{
lean_inc(v_a_954_);
lean_dec(v___x_810_);
v___x_956_ = lean_box(0);
v_isShared_957_ = v_isSharedCheck_961_;
goto v_resetjp_955_;
}
v_resetjp_955_:
{
lean_object* v___x_959_; 
if (v_isShared_957_ == 0)
{
v___x_959_ = v___x_956_;
goto v_reusejp_958_;
}
else
{
lean_object* v_reuseFailAlloc_960_; 
v_reuseFailAlloc_960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_960_, 0, v_a_954_);
v___x_959_ = v_reuseFailAlloc_960_;
goto v_reusejp_958_;
}
v_reusejp_958_:
{
return v___x_959_;
}
}
}
}
else
{
v_a_798_ = v_snd_792_;
goto v___jp_797_;
}
}
else
{
v_a_798_ = v_snd_792_;
goto v___jp_797_;
}
}
v___jp_797_:
{
lean_object* v___x_800_; 
if (v_isShared_795_ == 0)
{
lean_ctor_set(v___x_794_, 1, v_a_798_);
lean_ctor_set(v___x_794_, 0, v___x_796_);
v___x_800_ = v___x_794_;
goto v_reusejp_799_;
}
else
{
lean_object* v_reuseFailAlloc_804_; 
v_reuseFailAlloc_804_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_804_, 0, v___x_796_);
lean_ctor_set(v_reuseFailAlloc_804_, 1, v_a_798_);
v___x_800_ = v_reuseFailAlloc_804_;
goto v_reusejp_799_;
}
v_reusejp_799_:
{
size_t v___x_801_; size_t v___x_802_; 
v___x_801_ = ((size_t)1ULL);
v___x_802_ = lean_usize_add(v_i_781_, v___x_801_);
v_i_781_ = v___x_802_;
v_b_782_ = v___x_800_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__7_spec__10_spec__14_spec__16___boxed(lean_object* v_as_964_, lean_object* v_sz_965_, lean_object* v_i_966_, lean_object* v_b_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_){
_start:
{
size_t v_sz_boxed_975_; size_t v_i_boxed_976_; lean_object* v_res_977_; 
v_sz_boxed_975_ = lean_unbox_usize(v_sz_965_);
lean_dec(v_sz_965_);
v_i_boxed_976_ = lean_unbox_usize(v_i_966_);
lean_dec(v_i_966_);
v_res_977_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__7_spec__10_spec__14_spec__16(v_as_964_, v_sz_boxed_975_, v_i_boxed_976_, v_b_967_, v___y_968_, v___y_969_, v___y_970_, v___y_971_, v___y_972_, v___y_973_);
lean_dec(v___y_973_);
lean_dec_ref(v___y_972_);
lean_dec(v___y_971_);
lean_dec_ref(v___y_970_);
lean_dec(v___y_969_);
lean_dec_ref(v___y_968_);
lean_dec_ref(v_as_964_);
return v_res_977_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__7_spec__10_spec__14(lean_object* v_as_978_, size_t v_sz_979_, size_t v_i_980_, lean_object* v_b_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_){
_start:
{
uint8_t v___x_989_; 
v___x_989_ = lean_usize_dec_lt(v_i_980_, v_sz_979_);
if (v___x_989_ == 0)
{
lean_object* v___x_990_; 
v___x_990_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_990_, 0, v_b_981_);
return v___x_990_;
}
else
{
lean_object* v_snd_991_; lean_object* v___x_993_; uint8_t v_isShared_994_; uint8_t v_isSharedCheck_1161_; 
v_snd_991_ = lean_ctor_get(v_b_981_, 1);
v_isSharedCheck_1161_ = !lean_is_exclusive(v_b_981_);
if (v_isSharedCheck_1161_ == 0)
{
lean_object* v_unused_1162_; 
v_unused_1162_ = lean_ctor_get(v_b_981_, 0);
lean_dec(v_unused_1162_);
v___x_993_ = v_b_981_;
v_isShared_994_ = v_isSharedCheck_1161_;
goto v_resetjp_992_;
}
else
{
lean_inc(v_snd_991_);
lean_dec(v_b_981_);
v___x_993_ = lean_box(0);
v_isShared_994_ = v_isSharedCheck_1161_;
goto v_resetjp_992_;
}
v_resetjp_992_:
{
lean_object* v___x_995_; lean_object* v_a_997_; lean_object* v_a_1004_; 
v___x_995_ = lean_box(0);
v_a_1004_ = lean_array_uget_borrowed(v_as_978_, v_i_980_);
if (lean_obj_tag(v_a_1004_) == 0)
{
v_a_997_ = v_snd_991_;
goto v___jp_996_;
}
else
{
lean_object* v_val_1005_; uint8_t v___x_1006_; 
v_val_1005_ = lean_ctor_get(v_a_1004_, 0);
v___x_1006_ = l_Lean_LocalDecl_isImplementationDetail(v_val_1005_);
if (v___x_1006_ == 0)
{
uint8_t v___x_1007_; 
v___x_1007_ = l_Lean_LocalDecl_isLet(v_val_1005_, v___x_1006_);
if (v___x_1007_ == 0)
{
lean_object* v___x_1008_; lean_object* v___x_1009_; 
v___x_1008_ = l_Lean_LocalDecl_type(v_val_1005_);
v___x_1009_ = l_Lean_Meta_Sym_instantiateMVarsS(v___x_1008_, v___y_982_, v___y_983_, v___y_984_, v___y_985_, v___y_986_, v___y_987_);
if (lean_obj_tag(v___x_1009_) == 0)
{
lean_object* v_a_1010_; lean_object* v___y_1012_; lean_object* v___y_1013_; lean_object* v___y_1014_; lean_object* v___y_1015_; lean_object* v___y_1016_; lean_object* v___y_1017_; 
v_a_1010_ = lean_ctor_get(v___x_1009_, 0);
lean_inc(v_a_1010_);
lean_dec_ref_known(v___x_1009_, 1);
if (lean_obj_tag(v_a_1010_) == 3)
{
lean_object* v_u_1105_; 
v_u_1105_ = lean_ctor_get(v_a_1010_, 0);
if (lean_obj_tag(v_u_1105_) == 1)
{
lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; 
lean_inc_ref(v_u_1105_);
lean_dec_ref_known(v_a_1010_, 1);
v___x_1106_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__7_spec__11_spec__16___closed__1));
v___x_1107_ = lean_box(0);
v___x_1108_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1108_, 0, v_u_1105_);
lean_ctor_set(v___x_1108_, 1, v___x_1107_);
v___x_1109_ = l_Lean_Meta_Sym_Internal_mkConstS___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__2___redArg(v___x_1106_, v___x_1108_, v___y_983_);
if (lean_obj_tag(v___x_1109_) == 0)
{
lean_object* v_a_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; 
v_a_1110_ = lean_ctor_get(v___x_1109_, 0);
lean_inc(v_a_1110_);
lean_dec_ref_known(v___x_1109_, 1);
lean_inc(v_val_1005_);
v___x_1111_ = l_Lean_LocalDecl_toExpr(v_val_1005_);
v___x_1112_ = l_Lean_Meta_Sym_shareCommonInc(v___x_1111_, v___y_982_, v___y_983_, v___y_984_, v___y_985_, v___y_986_, v___y_987_);
if (lean_obj_tag(v___x_1112_) == 0)
{
lean_object* v_a_1113_; lean_object* v___x_1114_; 
v_a_1113_ = lean_ctor_get(v___x_1112_, 0);
lean_inc(v_a_1113_);
lean_dec_ref_known(v___x_1112_, 1);
v___x_1114_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__3(v_a_1110_, v_a_1113_, v___y_982_, v___y_983_, v___y_984_, v___y_985_, v___y_986_, v___y_987_);
if (lean_obj_tag(v___x_1114_) == 0)
{
lean_object* v_a_1115_; lean_object* v___x_1116_; 
v_a_1115_ = lean_ctor_get(v___x_1114_, 0);
lean_inc(v_a_1115_);
lean_dec_ref_known(v___x_1114_, 1);
v___x_1116_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v_a_1115_, v___y_983_, v___y_984_, v___y_985_, v___y_986_, v___y_987_);
if (lean_obj_tag(v___x_1116_) == 0)
{
lean_object* v_a_1117_; 
v_a_1117_ = lean_ctor_get(v___x_1116_, 0);
lean_inc(v_a_1117_);
lean_dec_ref_known(v___x_1116_, 1);
if (lean_obj_tag(v_a_1117_) == 0)
{
lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; 
v___x_1118_ = l_Lean_LocalDecl_fvarId(v_val_1005_);
v___x_1119_ = lean_box(0);
v___x_1120_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__6___redArg(v_snd_991_, v___x_1118_, v___x_1119_);
v_a_997_ = v___x_1120_;
goto v___jp_996_;
}
else
{
lean_dec_ref_known(v_a_1117_, 1);
v_a_997_ = v_snd_991_;
goto v___jp_996_;
}
}
else
{
lean_object* v_a_1121_; lean_object* v___x_1123_; uint8_t v_isShared_1124_; uint8_t v_isSharedCheck_1128_; 
lean_del_object(v___x_993_);
lean_dec(v_snd_991_);
v_a_1121_ = lean_ctor_get(v___x_1116_, 0);
v_isSharedCheck_1128_ = !lean_is_exclusive(v___x_1116_);
if (v_isSharedCheck_1128_ == 0)
{
v___x_1123_ = v___x_1116_;
v_isShared_1124_ = v_isSharedCheck_1128_;
goto v_resetjp_1122_;
}
else
{
lean_inc(v_a_1121_);
lean_dec(v___x_1116_);
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
lean_object* v_a_1129_; lean_object* v___x_1131_; uint8_t v_isShared_1132_; uint8_t v_isSharedCheck_1136_; 
lean_del_object(v___x_993_);
lean_dec(v_snd_991_);
v_a_1129_ = lean_ctor_get(v___x_1114_, 0);
v_isSharedCheck_1136_ = !lean_is_exclusive(v___x_1114_);
if (v_isSharedCheck_1136_ == 0)
{
v___x_1131_ = v___x_1114_;
v_isShared_1132_ = v_isSharedCheck_1136_;
goto v_resetjp_1130_;
}
else
{
lean_inc(v_a_1129_);
lean_dec(v___x_1114_);
v___x_1131_ = lean_box(0);
v_isShared_1132_ = v_isSharedCheck_1136_;
goto v_resetjp_1130_;
}
v_resetjp_1130_:
{
lean_object* v___x_1134_; 
if (v_isShared_1132_ == 0)
{
v___x_1134_ = v___x_1131_;
goto v_reusejp_1133_;
}
else
{
lean_object* v_reuseFailAlloc_1135_; 
v_reuseFailAlloc_1135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1135_, 0, v_a_1129_);
v___x_1134_ = v_reuseFailAlloc_1135_;
goto v_reusejp_1133_;
}
v_reusejp_1133_:
{
return v___x_1134_;
}
}
}
}
else
{
lean_object* v_a_1137_; lean_object* v___x_1139_; uint8_t v_isShared_1140_; uint8_t v_isSharedCheck_1144_; 
lean_dec(v_a_1110_);
lean_del_object(v___x_993_);
lean_dec(v_snd_991_);
v_a_1137_ = lean_ctor_get(v___x_1112_, 0);
v_isSharedCheck_1144_ = !lean_is_exclusive(v___x_1112_);
if (v_isSharedCheck_1144_ == 0)
{
v___x_1139_ = v___x_1112_;
v_isShared_1140_ = v_isSharedCheck_1144_;
goto v_resetjp_1138_;
}
else
{
lean_inc(v_a_1137_);
lean_dec(v___x_1112_);
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
else
{
lean_object* v_a_1145_; lean_object* v___x_1147_; uint8_t v_isShared_1148_; uint8_t v_isSharedCheck_1152_; 
lean_del_object(v___x_993_);
lean_dec(v_snd_991_);
v_a_1145_ = lean_ctor_get(v___x_1109_, 0);
v_isSharedCheck_1152_ = !lean_is_exclusive(v___x_1109_);
if (v_isSharedCheck_1152_ == 0)
{
v___x_1147_ = v___x_1109_;
v_isShared_1148_ = v_isSharedCheck_1152_;
goto v_resetjp_1146_;
}
else
{
lean_inc(v_a_1145_);
lean_dec(v___x_1109_);
v___x_1147_ = lean_box(0);
v_isShared_1148_ = v_isSharedCheck_1152_;
goto v_resetjp_1146_;
}
v_resetjp_1146_:
{
lean_object* v___x_1150_; 
if (v_isShared_1148_ == 0)
{
v___x_1150_ = v___x_1147_;
goto v_reusejp_1149_;
}
else
{
lean_object* v_reuseFailAlloc_1151_; 
v_reuseFailAlloc_1151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1151_, 0, v_a_1145_);
v___x_1150_ = v_reuseFailAlloc_1151_;
goto v_reusejp_1149_;
}
v_reusejp_1149_:
{
return v___x_1150_;
}
}
}
}
else
{
v___y_1012_ = v___y_982_;
v___y_1013_ = v___y_983_;
v___y_1014_ = v___y_984_;
v___y_1015_ = v___y_985_;
v___y_1016_ = v___y_986_;
v___y_1017_ = v___y_987_;
goto v___jp_1011_;
}
}
else
{
v___y_1012_ = v___y_982_;
v___y_1013_ = v___y_983_;
v___y_1014_ = v___y_984_;
v___y_1015_ = v___y_985_;
v___y_1016_ = v___y_986_;
v___y_1017_ = v___y_987_;
goto v___jp_1011_;
}
v___jp_1011_:
{
if (lean_obj_tag(v_a_1010_) == 1)
{
lean_object* v_fvarId_1018_; uint8_t v___x_1019_; 
v_fvarId_1018_ = lean_ctor_get(v_a_1010_, 0);
lean_inc(v_fvarId_1018_);
lean_dec_ref_known(v_a_1010_, 1);
v___x_1019_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__0___redArg(v_snd_991_, v_fvarId_1018_);
if (v___x_1019_ == 0)
{
lean_dec(v_fvarId_1018_);
v_a_997_ = v_snd_991_;
goto v___jp_996_;
}
else
{
lean_object* v___x_1020_; 
lean_inc(v_fvarId_1018_);
v___x_1020_ = l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__1___redArg(v_fvarId_1018_, v___y_1013_);
if (lean_obj_tag(v___x_1020_) == 0)
{
lean_object* v_a_1021_; lean_object* v___x_1022_; 
v_a_1021_ = lean_ctor_get(v___x_1020_, 0);
lean_inc_n(v_a_1021_, 2);
lean_dec_ref_known(v___x_1020_, 1);
v___x_1022_ = l_Lean_Meta_Sym_getLevel___redArg(v_a_1021_, v___y_1013_, v___y_1014_, v___y_1015_, v___y_1016_, v___y_1017_);
if (lean_obj_tag(v___x_1022_) == 0)
{
lean_object* v_a_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; 
v_a_1023_ = lean_ctor_get(v___x_1022_, 0);
lean_inc(v_a_1023_);
lean_dec_ref_known(v___x_1022_, 1);
v___x_1024_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__7_spec__11_spec__16___closed__1));
v___x_1025_ = lean_box(0);
v___x_1026_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1026_, 0, v_a_1023_);
lean_ctor_set(v___x_1026_, 1, v___x_1025_);
lean_inc_ref(v___x_1026_);
v___x_1027_ = l_Lean_Meta_Sym_Internal_mkConstS___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__2___redArg(v___x_1024_, v___x_1026_, v___y_1013_);
if (lean_obj_tag(v___x_1027_) == 0)
{
lean_object* v_a_1028_; lean_object* v___x_1029_; 
v_a_1028_ = lean_ctor_get(v___x_1027_, 0);
lean_inc(v_a_1028_);
lean_dec_ref_known(v___x_1027_, 1);
lean_inc(v_a_1021_);
v___x_1029_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__3(v_a_1028_, v_a_1021_, v___y_1012_, v___y_1013_, v___y_1014_, v___y_1015_, v___y_1016_, v___y_1017_);
if (lean_obj_tag(v___x_1029_) == 0)
{
lean_object* v_a_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; 
v_a_1030_ = lean_ctor_get(v___x_1029_, 0);
lean_inc(v_a_1030_);
lean_dec_ref_known(v___x_1029_, 1);
v___x_1031_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__7_spec__11_spec__16___closed__3));
v___x_1032_ = l_Lean_Meta_Sym_Internal_mkConstS___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__2___redArg(v___x_1031_, v___x_1026_, v___y_1013_);
if (lean_obj_tag(v___x_1032_) == 0)
{
lean_object* v_a_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; 
v_a_1033_ = lean_ctor_get(v___x_1032_, 0);
lean_inc(v_a_1033_);
lean_dec_ref_known(v___x_1032_, 1);
lean_inc(v_val_1005_);
v___x_1034_ = l_Lean_LocalDecl_toExpr(v_val_1005_);
v___x_1035_ = l_Lean_Meta_Sym_shareCommonInc(v___x_1034_, v___y_1012_, v___y_1013_, v___y_1014_, v___y_1015_, v___y_1016_, v___y_1017_);
if (lean_obj_tag(v___x_1035_) == 0)
{
lean_object* v_a_1036_; lean_object* v___x_1037_; 
v_a_1036_ = lean_ctor_get(v___x_1035_, 0);
lean_inc(v_a_1036_);
lean_dec_ref_known(v___x_1035_, 1);
v___x_1037_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__4(v_a_1033_, v_a_1021_, v_a_1036_, v___y_1012_, v___y_1013_, v___y_1014_, v___y_1015_, v___y_1016_, v___y_1017_);
if (lean_obj_tag(v___x_1037_) == 0)
{
lean_object* v_a_1038_; lean_object* v___x_1039_; 
v_a_1038_ = lean_ctor_get(v___x_1037_, 0);
lean_inc(v_a_1038_);
lean_dec_ref_known(v___x_1037_, 1);
v___x_1039_ = l_Lean_Meta_Sym_registerInstance___redArg(v_a_1030_, v_a_1038_, v___y_1013_);
if (lean_obj_tag(v___x_1039_) == 0)
{
lean_object* v___x_1040_; 
lean_dec_ref_known(v___x_1039_, 1);
v___x_1040_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__5___redArg(v_snd_991_, v_fvarId_1018_);
lean_dec(v_fvarId_1018_);
v_a_997_ = v___x_1040_;
goto v___jp_996_;
}
else
{
lean_object* v_a_1041_; lean_object* v___x_1043_; uint8_t v_isShared_1044_; uint8_t v_isSharedCheck_1048_; 
lean_dec(v_fvarId_1018_);
lean_del_object(v___x_993_);
lean_dec(v_snd_991_);
v_a_1041_ = lean_ctor_get(v___x_1039_, 0);
v_isSharedCheck_1048_ = !lean_is_exclusive(v___x_1039_);
if (v_isSharedCheck_1048_ == 0)
{
v___x_1043_ = v___x_1039_;
v_isShared_1044_ = v_isSharedCheck_1048_;
goto v_resetjp_1042_;
}
else
{
lean_inc(v_a_1041_);
lean_dec(v___x_1039_);
v___x_1043_ = lean_box(0);
v_isShared_1044_ = v_isSharedCheck_1048_;
goto v_resetjp_1042_;
}
v_resetjp_1042_:
{
lean_object* v___x_1046_; 
if (v_isShared_1044_ == 0)
{
v___x_1046_ = v___x_1043_;
goto v_reusejp_1045_;
}
else
{
lean_object* v_reuseFailAlloc_1047_; 
v_reuseFailAlloc_1047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1047_, 0, v_a_1041_);
v___x_1046_ = v_reuseFailAlloc_1047_;
goto v_reusejp_1045_;
}
v_reusejp_1045_:
{
return v___x_1046_;
}
}
}
}
else
{
lean_object* v_a_1049_; lean_object* v___x_1051_; uint8_t v_isShared_1052_; uint8_t v_isSharedCheck_1056_; 
lean_dec(v_a_1030_);
lean_dec(v_fvarId_1018_);
lean_del_object(v___x_993_);
lean_dec(v_snd_991_);
v_a_1049_ = lean_ctor_get(v___x_1037_, 0);
v_isSharedCheck_1056_ = !lean_is_exclusive(v___x_1037_);
if (v_isSharedCheck_1056_ == 0)
{
v___x_1051_ = v___x_1037_;
v_isShared_1052_ = v_isSharedCheck_1056_;
goto v_resetjp_1050_;
}
else
{
lean_inc(v_a_1049_);
lean_dec(v___x_1037_);
v___x_1051_ = lean_box(0);
v_isShared_1052_ = v_isSharedCheck_1056_;
goto v_resetjp_1050_;
}
v_resetjp_1050_:
{
lean_object* v___x_1054_; 
if (v_isShared_1052_ == 0)
{
v___x_1054_ = v___x_1051_;
goto v_reusejp_1053_;
}
else
{
lean_object* v_reuseFailAlloc_1055_; 
v_reuseFailAlloc_1055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1055_, 0, v_a_1049_);
v___x_1054_ = v_reuseFailAlloc_1055_;
goto v_reusejp_1053_;
}
v_reusejp_1053_:
{
return v___x_1054_;
}
}
}
}
else
{
lean_object* v_a_1057_; lean_object* v___x_1059_; uint8_t v_isShared_1060_; uint8_t v_isSharedCheck_1064_; 
lean_dec(v_a_1033_);
lean_dec(v_a_1030_);
lean_dec(v_a_1021_);
lean_dec(v_fvarId_1018_);
lean_del_object(v___x_993_);
lean_dec(v_snd_991_);
v_a_1057_ = lean_ctor_get(v___x_1035_, 0);
v_isSharedCheck_1064_ = !lean_is_exclusive(v___x_1035_);
if (v_isSharedCheck_1064_ == 0)
{
v___x_1059_ = v___x_1035_;
v_isShared_1060_ = v_isSharedCheck_1064_;
goto v_resetjp_1058_;
}
else
{
lean_inc(v_a_1057_);
lean_dec(v___x_1035_);
v___x_1059_ = lean_box(0);
v_isShared_1060_ = v_isSharedCheck_1064_;
goto v_resetjp_1058_;
}
v_resetjp_1058_:
{
lean_object* v___x_1062_; 
if (v_isShared_1060_ == 0)
{
v___x_1062_ = v___x_1059_;
goto v_reusejp_1061_;
}
else
{
lean_object* v_reuseFailAlloc_1063_; 
v_reuseFailAlloc_1063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1063_, 0, v_a_1057_);
v___x_1062_ = v_reuseFailAlloc_1063_;
goto v_reusejp_1061_;
}
v_reusejp_1061_:
{
return v___x_1062_;
}
}
}
}
else
{
lean_object* v_a_1065_; lean_object* v___x_1067_; uint8_t v_isShared_1068_; uint8_t v_isSharedCheck_1072_; 
lean_dec(v_a_1030_);
lean_dec(v_a_1021_);
lean_dec(v_fvarId_1018_);
lean_del_object(v___x_993_);
lean_dec(v_snd_991_);
v_a_1065_ = lean_ctor_get(v___x_1032_, 0);
v_isSharedCheck_1072_ = !lean_is_exclusive(v___x_1032_);
if (v_isSharedCheck_1072_ == 0)
{
v___x_1067_ = v___x_1032_;
v_isShared_1068_ = v_isSharedCheck_1072_;
goto v_resetjp_1066_;
}
else
{
lean_inc(v_a_1065_);
lean_dec(v___x_1032_);
v___x_1067_ = lean_box(0);
v_isShared_1068_ = v_isSharedCheck_1072_;
goto v_resetjp_1066_;
}
v_resetjp_1066_:
{
lean_object* v___x_1070_; 
if (v_isShared_1068_ == 0)
{
v___x_1070_ = v___x_1067_;
goto v_reusejp_1069_;
}
else
{
lean_object* v_reuseFailAlloc_1071_; 
v_reuseFailAlloc_1071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1071_, 0, v_a_1065_);
v___x_1070_ = v_reuseFailAlloc_1071_;
goto v_reusejp_1069_;
}
v_reusejp_1069_:
{
return v___x_1070_;
}
}
}
}
else
{
lean_object* v_a_1073_; lean_object* v___x_1075_; uint8_t v_isShared_1076_; uint8_t v_isSharedCheck_1080_; 
lean_dec_ref_known(v___x_1026_, 2);
lean_dec(v_a_1021_);
lean_dec(v_fvarId_1018_);
lean_del_object(v___x_993_);
lean_dec(v_snd_991_);
v_a_1073_ = lean_ctor_get(v___x_1029_, 0);
v_isSharedCheck_1080_ = !lean_is_exclusive(v___x_1029_);
if (v_isSharedCheck_1080_ == 0)
{
v___x_1075_ = v___x_1029_;
v_isShared_1076_ = v_isSharedCheck_1080_;
goto v_resetjp_1074_;
}
else
{
lean_inc(v_a_1073_);
lean_dec(v___x_1029_);
v___x_1075_ = lean_box(0);
v_isShared_1076_ = v_isSharedCheck_1080_;
goto v_resetjp_1074_;
}
v_resetjp_1074_:
{
lean_object* v___x_1078_; 
if (v_isShared_1076_ == 0)
{
v___x_1078_ = v___x_1075_;
goto v_reusejp_1077_;
}
else
{
lean_object* v_reuseFailAlloc_1079_; 
v_reuseFailAlloc_1079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1079_, 0, v_a_1073_);
v___x_1078_ = v_reuseFailAlloc_1079_;
goto v_reusejp_1077_;
}
v_reusejp_1077_:
{
return v___x_1078_;
}
}
}
}
else
{
lean_object* v_a_1081_; lean_object* v___x_1083_; uint8_t v_isShared_1084_; uint8_t v_isSharedCheck_1088_; 
lean_dec_ref_known(v___x_1026_, 2);
lean_dec(v_a_1021_);
lean_dec(v_fvarId_1018_);
lean_del_object(v___x_993_);
lean_dec(v_snd_991_);
v_a_1081_ = lean_ctor_get(v___x_1027_, 0);
v_isSharedCheck_1088_ = !lean_is_exclusive(v___x_1027_);
if (v_isSharedCheck_1088_ == 0)
{
v___x_1083_ = v___x_1027_;
v_isShared_1084_ = v_isSharedCheck_1088_;
goto v_resetjp_1082_;
}
else
{
lean_inc(v_a_1081_);
lean_dec(v___x_1027_);
v___x_1083_ = lean_box(0);
v_isShared_1084_ = v_isSharedCheck_1088_;
goto v_resetjp_1082_;
}
v_resetjp_1082_:
{
lean_object* v___x_1086_; 
if (v_isShared_1084_ == 0)
{
v___x_1086_ = v___x_1083_;
goto v_reusejp_1085_;
}
else
{
lean_object* v_reuseFailAlloc_1087_; 
v_reuseFailAlloc_1087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1087_, 0, v_a_1081_);
v___x_1086_ = v_reuseFailAlloc_1087_;
goto v_reusejp_1085_;
}
v_reusejp_1085_:
{
return v___x_1086_;
}
}
}
}
else
{
lean_object* v_a_1089_; lean_object* v___x_1091_; uint8_t v_isShared_1092_; uint8_t v_isSharedCheck_1096_; 
lean_dec(v_a_1021_);
lean_dec(v_fvarId_1018_);
lean_del_object(v___x_993_);
lean_dec(v_snd_991_);
v_a_1089_ = lean_ctor_get(v___x_1022_, 0);
v_isSharedCheck_1096_ = !lean_is_exclusive(v___x_1022_);
if (v_isSharedCheck_1096_ == 0)
{
v___x_1091_ = v___x_1022_;
v_isShared_1092_ = v_isSharedCheck_1096_;
goto v_resetjp_1090_;
}
else
{
lean_inc(v_a_1089_);
lean_dec(v___x_1022_);
v___x_1091_ = lean_box(0);
v_isShared_1092_ = v_isSharedCheck_1096_;
goto v_resetjp_1090_;
}
v_resetjp_1090_:
{
lean_object* v___x_1094_; 
if (v_isShared_1092_ == 0)
{
v___x_1094_ = v___x_1091_;
goto v_reusejp_1093_;
}
else
{
lean_object* v_reuseFailAlloc_1095_; 
v_reuseFailAlloc_1095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1095_, 0, v_a_1089_);
v___x_1094_ = v_reuseFailAlloc_1095_;
goto v_reusejp_1093_;
}
v_reusejp_1093_:
{
return v___x_1094_;
}
}
}
}
else
{
lean_object* v_a_1097_; lean_object* v___x_1099_; uint8_t v_isShared_1100_; uint8_t v_isSharedCheck_1104_; 
lean_dec(v_fvarId_1018_);
lean_del_object(v___x_993_);
lean_dec(v_snd_991_);
v_a_1097_ = lean_ctor_get(v___x_1020_, 0);
v_isSharedCheck_1104_ = !lean_is_exclusive(v___x_1020_);
if (v_isSharedCheck_1104_ == 0)
{
v___x_1099_ = v___x_1020_;
v_isShared_1100_ = v_isSharedCheck_1104_;
goto v_resetjp_1098_;
}
else
{
lean_inc(v_a_1097_);
lean_dec(v___x_1020_);
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
}
else
{
lean_dec(v_a_1010_);
v_a_997_ = v_snd_991_;
goto v___jp_996_;
}
}
}
else
{
lean_object* v_a_1153_; lean_object* v___x_1155_; uint8_t v_isShared_1156_; uint8_t v_isSharedCheck_1160_; 
lean_del_object(v___x_993_);
lean_dec(v_snd_991_);
v_a_1153_ = lean_ctor_get(v___x_1009_, 0);
v_isSharedCheck_1160_ = !lean_is_exclusive(v___x_1009_);
if (v_isSharedCheck_1160_ == 0)
{
v___x_1155_ = v___x_1009_;
v_isShared_1156_ = v_isSharedCheck_1160_;
goto v_resetjp_1154_;
}
else
{
lean_inc(v_a_1153_);
lean_dec(v___x_1009_);
v___x_1155_ = lean_box(0);
v_isShared_1156_ = v_isSharedCheck_1160_;
goto v_resetjp_1154_;
}
v_resetjp_1154_:
{
lean_object* v___x_1158_; 
if (v_isShared_1156_ == 0)
{
v___x_1158_ = v___x_1155_;
goto v_reusejp_1157_;
}
else
{
lean_object* v_reuseFailAlloc_1159_; 
v_reuseFailAlloc_1159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1159_, 0, v_a_1153_);
v___x_1158_ = v_reuseFailAlloc_1159_;
goto v_reusejp_1157_;
}
v_reusejp_1157_:
{
return v___x_1158_;
}
}
}
}
else
{
v_a_997_ = v_snd_991_;
goto v___jp_996_;
}
}
else
{
v_a_997_ = v_snd_991_;
goto v___jp_996_;
}
}
v___jp_996_:
{
lean_object* v___x_999_; 
if (v_isShared_994_ == 0)
{
lean_ctor_set(v___x_993_, 1, v_a_997_);
lean_ctor_set(v___x_993_, 0, v___x_995_);
v___x_999_ = v___x_993_;
goto v_reusejp_998_;
}
else
{
lean_object* v_reuseFailAlloc_1003_; 
v_reuseFailAlloc_1003_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1003_, 0, v___x_995_);
lean_ctor_set(v_reuseFailAlloc_1003_, 1, v_a_997_);
v___x_999_ = v_reuseFailAlloc_1003_;
goto v_reusejp_998_;
}
v_reusejp_998_:
{
size_t v___x_1000_; size_t v___x_1001_; lean_object* v___x_1002_; 
v___x_1000_ = ((size_t)1ULL);
v___x_1001_ = lean_usize_add(v_i_980_, v___x_1000_);
v___x_1002_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__7_spec__10_spec__14_spec__16(v_as_978_, v_sz_979_, v___x_1001_, v___x_999_, v___y_982_, v___y_983_, v___y_984_, v___y_985_, v___y_986_, v___y_987_);
return v___x_1002_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__7_spec__10_spec__14___boxed(lean_object* v_as_1163_, lean_object* v_sz_1164_, lean_object* v_i_1165_, lean_object* v_b_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_){
_start:
{
size_t v_sz_boxed_1174_; size_t v_i_boxed_1175_; lean_object* v_res_1176_; 
v_sz_boxed_1174_ = lean_unbox_usize(v_sz_1164_);
lean_dec(v_sz_1164_);
v_i_boxed_1175_ = lean_unbox_usize(v_i_1165_);
lean_dec(v_i_1165_);
v_res_1176_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__7_spec__10_spec__14(v_as_1163_, v_sz_boxed_1174_, v_i_boxed_1175_, v_b_1166_, v___y_1167_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_, v___y_1172_);
lean_dec(v___y_1172_);
lean_dec_ref(v___y_1171_);
lean_dec(v___y_1170_);
lean_dec_ref(v___y_1169_);
lean_dec(v___y_1168_);
lean_dec_ref(v___y_1167_);
lean_dec_ref(v_as_1163_);
return v_res_1176_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__7_spec__10(lean_object* v_init_1177_, lean_object* v_n_1178_, lean_object* v_b_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_){
_start:
{
if (lean_obj_tag(v_n_1178_) == 0)
{
lean_object* v_cs_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; size_t v_sz_1190_; size_t v___x_1191_; lean_object* v___x_1192_; 
v_cs_1187_ = lean_ctor_get(v_n_1178_, 0);
v___x_1188_ = lean_box(0);
v___x_1189_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1189_, 0, v___x_1188_);
lean_ctor_set(v___x_1189_, 1, v_b_1179_);
v_sz_1190_ = lean_array_size(v_cs_1187_);
v___x_1191_ = ((size_t)0ULL);
v___x_1192_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__7_spec__10_spec__13(v_init_1177_, v_cs_1187_, v_sz_1190_, v___x_1191_, v___x_1189_, v___y_1180_, v___y_1181_, v___y_1182_, v___y_1183_, v___y_1184_, v___y_1185_);
if (lean_obj_tag(v___x_1192_) == 0)
{
lean_object* v_a_1193_; lean_object* v___x_1195_; uint8_t v_isShared_1196_; uint8_t v_isSharedCheck_1207_; 
v_a_1193_ = lean_ctor_get(v___x_1192_, 0);
v_isSharedCheck_1207_ = !lean_is_exclusive(v___x_1192_);
if (v_isSharedCheck_1207_ == 0)
{
v___x_1195_ = v___x_1192_;
v_isShared_1196_ = v_isSharedCheck_1207_;
goto v_resetjp_1194_;
}
else
{
lean_inc(v_a_1193_);
lean_dec(v___x_1192_);
v___x_1195_ = lean_box(0);
v_isShared_1196_ = v_isSharedCheck_1207_;
goto v_resetjp_1194_;
}
v_resetjp_1194_:
{
lean_object* v_fst_1197_; 
v_fst_1197_ = lean_ctor_get(v_a_1193_, 0);
if (lean_obj_tag(v_fst_1197_) == 0)
{
lean_object* v_snd_1198_; lean_object* v___x_1199_; lean_object* v___x_1201_; 
v_snd_1198_ = lean_ctor_get(v_a_1193_, 1);
lean_inc(v_snd_1198_);
lean_dec(v_a_1193_);
v___x_1199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1199_, 0, v_snd_1198_);
if (v_isShared_1196_ == 0)
{
lean_ctor_set(v___x_1195_, 0, v___x_1199_);
v___x_1201_ = v___x_1195_;
goto v_reusejp_1200_;
}
else
{
lean_object* v_reuseFailAlloc_1202_; 
v_reuseFailAlloc_1202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1202_, 0, v___x_1199_);
v___x_1201_ = v_reuseFailAlloc_1202_;
goto v_reusejp_1200_;
}
v_reusejp_1200_:
{
return v___x_1201_;
}
}
else
{
lean_object* v_val_1203_; lean_object* v___x_1205_; 
lean_inc_ref(v_fst_1197_);
lean_dec(v_a_1193_);
v_val_1203_ = lean_ctor_get(v_fst_1197_, 0);
lean_inc(v_val_1203_);
lean_dec_ref_known(v_fst_1197_, 1);
if (v_isShared_1196_ == 0)
{
lean_ctor_set(v___x_1195_, 0, v_val_1203_);
v___x_1205_ = v___x_1195_;
goto v_reusejp_1204_;
}
else
{
lean_object* v_reuseFailAlloc_1206_; 
v_reuseFailAlloc_1206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1206_, 0, v_val_1203_);
v___x_1205_ = v_reuseFailAlloc_1206_;
goto v_reusejp_1204_;
}
v_reusejp_1204_:
{
return v___x_1205_;
}
}
}
}
else
{
lean_object* v_a_1208_; lean_object* v___x_1210_; uint8_t v_isShared_1211_; uint8_t v_isSharedCheck_1215_; 
v_a_1208_ = lean_ctor_get(v___x_1192_, 0);
v_isSharedCheck_1215_ = !lean_is_exclusive(v___x_1192_);
if (v_isSharedCheck_1215_ == 0)
{
v___x_1210_ = v___x_1192_;
v_isShared_1211_ = v_isSharedCheck_1215_;
goto v_resetjp_1209_;
}
else
{
lean_inc(v_a_1208_);
lean_dec(v___x_1192_);
v___x_1210_ = lean_box(0);
v_isShared_1211_ = v_isSharedCheck_1215_;
goto v_resetjp_1209_;
}
v_resetjp_1209_:
{
lean_object* v___x_1213_; 
if (v_isShared_1211_ == 0)
{
v___x_1213_ = v___x_1210_;
goto v_reusejp_1212_;
}
else
{
lean_object* v_reuseFailAlloc_1214_; 
v_reuseFailAlloc_1214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1214_, 0, v_a_1208_);
v___x_1213_ = v_reuseFailAlloc_1214_;
goto v_reusejp_1212_;
}
v_reusejp_1212_:
{
return v___x_1213_;
}
}
}
}
else
{
lean_object* v_vs_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; size_t v_sz_1219_; size_t v___x_1220_; lean_object* v___x_1221_; 
v_vs_1216_ = lean_ctor_get(v_n_1178_, 0);
v___x_1217_ = lean_box(0);
v___x_1218_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1218_, 0, v___x_1217_);
lean_ctor_set(v___x_1218_, 1, v_b_1179_);
v_sz_1219_ = lean_array_size(v_vs_1216_);
v___x_1220_ = ((size_t)0ULL);
v___x_1221_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__7_spec__10_spec__14(v_vs_1216_, v_sz_1219_, v___x_1220_, v___x_1218_, v___y_1180_, v___y_1181_, v___y_1182_, v___y_1183_, v___y_1184_, v___y_1185_);
if (lean_obj_tag(v___x_1221_) == 0)
{
lean_object* v_a_1222_; lean_object* v___x_1224_; uint8_t v_isShared_1225_; uint8_t v_isSharedCheck_1236_; 
v_a_1222_ = lean_ctor_get(v___x_1221_, 0);
v_isSharedCheck_1236_ = !lean_is_exclusive(v___x_1221_);
if (v_isSharedCheck_1236_ == 0)
{
v___x_1224_ = v___x_1221_;
v_isShared_1225_ = v_isSharedCheck_1236_;
goto v_resetjp_1223_;
}
else
{
lean_inc(v_a_1222_);
lean_dec(v___x_1221_);
v___x_1224_ = lean_box(0);
v_isShared_1225_ = v_isSharedCheck_1236_;
goto v_resetjp_1223_;
}
v_resetjp_1223_:
{
lean_object* v_fst_1226_; 
v_fst_1226_ = lean_ctor_get(v_a_1222_, 0);
if (lean_obj_tag(v_fst_1226_) == 0)
{
lean_object* v_snd_1227_; lean_object* v___x_1228_; lean_object* v___x_1230_; 
v_snd_1227_ = lean_ctor_get(v_a_1222_, 1);
lean_inc(v_snd_1227_);
lean_dec(v_a_1222_);
v___x_1228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1228_, 0, v_snd_1227_);
if (v_isShared_1225_ == 0)
{
lean_ctor_set(v___x_1224_, 0, v___x_1228_);
v___x_1230_ = v___x_1224_;
goto v_reusejp_1229_;
}
else
{
lean_object* v_reuseFailAlloc_1231_; 
v_reuseFailAlloc_1231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1231_, 0, v___x_1228_);
v___x_1230_ = v_reuseFailAlloc_1231_;
goto v_reusejp_1229_;
}
v_reusejp_1229_:
{
return v___x_1230_;
}
}
else
{
lean_object* v_val_1232_; lean_object* v___x_1234_; 
lean_inc_ref(v_fst_1226_);
lean_dec(v_a_1222_);
v_val_1232_ = lean_ctor_get(v_fst_1226_, 0);
lean_inc(v_val_1232_);
lean_dec_ref_known(v_fst_1226_, 1);
if (v_isShared_1225_ == 0)
{
lean_ctor_set(v___x_1224_, 0, v_val_1232_);
v___x_1234_ = v___x_1224_;
goto v_reusejp_1233_;
}
else
{
lean_object* v_reuseFailAlloc_1235_; 
v_reuseFailAlloc_1235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1235_, 0, v_val_1232_);
v___x_1234_ = v_reuseFailAlloc_1235_;
goto v_reusejp_1233_;
}
v_reusejp_1233_:
{
return v___x_1234_;
}
}
}
}
else
{
lean_object* v_a_1237_; lean_object* v___x_1239_; uint8_t v_isShared_1240_; uint8_t v_isSharedCheck_1244_; 
v_a_1237_ = lean_ctor_get(v___x_1221_, 0);
v_isSharedCheck_1244_ = !lean_is_exclusive(v___x_1221_);
if (v_isSharedCheck_1244_ == 0)
{
v___x_1239_ = v___x_1221_;
v_isShared_1240_ = v_isSharedCheck_1244_;
goto v_resetjp_1238_;
}
else
{
lean_inc(v_a_1237_);
lean_dec(v___x_1221_);
v___x_1239_ = lean_box(0);
v_isShared_1240_ = v_isSharedCheck_1244_;
goto v_resetjp_1238_;
}
v_resetjp_1238_:
{
lean_object* v___x_1242_; 
if (v_isShared_1240_ == 0)
{
v___x_1242_ = v___x_1239_;
goto v_reusejp_1241_;
}
else
{
lean_object* v_reuseFailAlloc_1243_; 
v_reuseFailAlloc_1243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1243_, 0, v_a_1237_);
v___x_1242_ = v_reuseFailAlloc_1243_;
goto v_reusejp_1241_;
}
v_reusejp_1241_:
{
return v___x_1242_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__7_spec__10_spec__13(lean_object* v_init_1245_, lean_object* v_as_1246_, size_t v_sz_1247_, size_t v_i_1248_, lean_object* v_b_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_){
_start:
{
uint8_t v___x_1257_; 
v___x_1257_ = lean_usize_dec_lt(v_i_1248_, v_sz_1247_);
if (v___x_1257_ == 0)
{
lean_object* v___x_1258_; 
v___x_1258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1258_, 0, v_b_1249_);
return v___x_1258_;
}
else
{
lean_object* v_snd_1259_; lean_object* v___x_1261_; uint8_t v_isShared_1262_; uint8_t v_isSharedCheck_1293_; 
v_snd_1259_ = lean_ctor_get(v_b_1249_, 1);
v_isSharedCheck_1293_ = !lean_is_exclusive(v_b_1249_);
if (v_isSharedCheck_1293_ == 0)
{
lean_object* v_unused_1294_; 
v_unused_1294_ = lean_ctor_get(v_b_1249_, 0);
lean_dec(v_unused_1294_);
v___x_1261_ = v_b_1249_;
v_isShared_1262_ = v_isSharedCheck_1293_;
goto v_resetjp_1260_;
}
else
{
lean_inc(v_snd_1259_);
lean_dec(v_b_1249_);
v___x_1261_ = lean_box(0);
v_isShared_1262_ = v_isSharedCheck_1293_;
goto v_resetjp_1260_;
}
v_resetjp_1260_:
{
lean_object* v___x_1263_; lean_object* v_a_1264_; lean_object* v___x_1265_; 
v___x_1263_ = lean_box(0);
v_a_1264_ = lean_array_uget_borrowed(v_as_1246_, v_i_1248_);
lean_inc(v_snd_1259_);
v___x_1265_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__7_spec__10(v_init_1245_, v_a_1264_, v_snd_1259_, v___y_1250_, v___y_1251_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_);
if (lean_obj_tag(v___x_1265_) == 0)
{
lean_object* v_a_1266_; lean_object* v___x_1268_; uint8_t v_isShared_1269_; uint8_t v_isSharedCheck_1284_; 
v_a_1266_ = lean_ctor_get(v___x_1265_, 0);
v_isSharedCheck_1284_ = !lean_is_exclusive(v___x_1265_);
if (v_isSharedCheck_1284_ == 0)
{
v___x_1268_ = v___x_1265_;
v_isShared_1269_ = v_isSharedCheck_1284_;
goto v_resetjp_1267_;
}
else
{
lean_inc(v_a_1266_);
lean_dec(v___x_1265_);
v___x_1268_ = lean_box(0);
v_isShared_1269_ = v_isSharedCheck_1284_;
goto v_resetjp_1267_;
}
v_resetjp_1267_:
{
if (lean_obj_tag(v_a_1266_) == 0)
{
lean_object* v___x_1270_; lean_object* v___x_1272_; 
v___x_1270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1270_, 0, v_a_1266_);
if (v_isShared_1262_ == 0)
{
lean_ctor_set(v___x_1261_, 0, v___x_1270_);
v___x_1272_ = v___x_1261_;
goto v_reusejp_1271_;
}
else
{
lean_object* v_reuseFailAlloc_1276_; 
v_reuseFailAlloc_1276_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1276_, 0, v___x_1270_);
lean_ctor_set(v_reuseFailAlloc_1276_, 1, v_snd_1259_);
v___x_1272_ = v_reuseFailAlloc_1276_;
goto v_reusejp_1271_;
}
v_reusejp_1271_:
{
lean_object* v___x_1274_; 
if (v_isShared_1269_ == 0)
{
lean_ctor_set(v___x_1268_, 0, v___x_1272_);
v___x_1274_ = v___x_1268_;
goto v_reusejp_1273_;
}
else
{
lean_object* v_reuseFailAlloc_1275_; 
v_reuseFailAlloc_1275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1275_, 0, v___x_1272_);
v___x_1274_ = v_reuseFailAlloc_1275_;
goto v_reusejp_1273_;
}
v_reusejp_1273_:
{
return v___x_1274_;
}
}
}
else
{
lean_object* v_a_1277_; lean_object* v___x_1279_; 
lean_del_object(v___x_1268_);
lean_dec(v_snd_1259_);
v_a_1277_ = lean_ctor_get(v_a_1266_, 0);
lean_inc(v_a_1277_);
lean_dec_ref_known(v_a_1266_, 1);
if (v_isShared_1262_ == 0)
{
lean_ctor_set(v___x_1261_, 1, v_a_1277_);
lean_ctor_set(v___x_1261_, 0, v___x_1263_);
v___x_1279_ = v___x_1261_;
goto v_reusejp_1278_;
}
else
{
lean_object* v_reuseFailAlloc_1283_; 
v_reuseFailAlloc_1283_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1283_, 0, v___x_1263_);
lean_ctor_set(v_reuseFailAlloc_1283_, 1, v_a_1277_);
v___x_1279_ = v_reuseFailAlloc_1283_;
goto v_reusejp_1278_;
}
v_reusejp_1278_:
{
size_t v___x_1280_; size_t v___x_1281_; 
v___x_1280_ = ((size_t)1ULL);
v___x_1281_ = lean_usize_add(v_i_1248_, v___x_1280_);
v_i_1248_ = v___x_1281_;
v_b_1249_ = v___x_1279_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1285_; lean_object* v___x_1287_; uint8_t v_isShared_1288_; uint8_t v_isSharedCheck_1292_; 
lean_del_object(v___x_1261_);
lean_dec(v_snd_1259_);
v_a_1285_ = lean_ctor_get(v___x_1265_, 0);
v_isSharedCheck_1292_ = !lean_is_exclusive(v___x_1265_);
if (v_isSharedCheck_1292_ == 0)
{
v___x_1287_ = v___x_1265_;
v_isShared_1288_ = v_isSharedCheck_1292_;
goto v_resetjp_1286_;
}
else
{
lean_inc(v_a_1285_);
lean_dec(v___x_1265_);
v___x_1287_ = lean_box(0);
v_isShared_1288_ = v_isSharedCheck_1292_;
goto v_resetjp_1286_;
}
v_resetjp_1286_:
{
lean_object* v___x_1290_; 
if (v_isShared_1288_ == 0)
{
v___x_1290_ = v___x_1287_;
goto v_reusejp_1289_;
}
else
{
lean_object* v_reuseFailAlloc_1291_; 
v_reuseFailAlloc_1291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1291_, 0, v_a_1285_);
v___x_1290_ = v_reuseFailAlloc_1291_;
goto v_reusejp_1289_;
}
v_reusejp_1289_:
{
return v___x_1290_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__7_spec__10_spec__13___boxed(lean_object* v_init_1295_, lean_object* v_as_1296_, lean_object* v_sz_1297_, lean_object* v_i_1298_, lean_object* v_b_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_){
_start:
{
size_t v_sz_boxed_1307_; size_t v_i_boxed_1308_; lean_object* v_res_1309_; 
v_sz_boxed_1307_ = lean_unbox_usize(v_sz_1297_);
lean_dec(v_sz_1297_);
v_i_boxed_1308_ = lean_unbox_usize(v_i_1298_);
lean_dec(v_i_1298_);
v_res_1309_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__7_spec__10_spec__13(v_init_1295_, v_as_1296_, v_sz_boxed_1307_, v_i_boxed_1308_, v_b_1299_, v___y_1300_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_);
lean_dec(v___y_1305_);
lean_dec_ref(v___y_1304_);
lean_dec(v___y_1303_);
lean_dec_ref(v___y_1302_);
lean_dec(v___y_1301_);
lean_dec_ref(v___y_1300_);
lean_dec_ref(v_as_1296_);
lean_dec_ref(v_init_1295_);
return v_res_1309_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__7_spec__10___boxed(lean_object* v_init_1310_, lean_object* v_n_1311_, lean_object* v_b_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_){
_start:
{
lean_object* v_res_1320_; 
v_res_1320_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__7_spec__10(v_init_1310_, v_n_1311_, v_b_1312_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_, v___y_1317_, v___y_1318_);
lean_dec(v___y_1318_);
lean_dec_ref(v___y_1317_);
lean_dec(v___y_1316_);
lean_dec_ref(v___y_1315_);
lean_dec(v___y_1314_);
lean_dec_ref(v___y_1313_);
lean_dec_ref(v_n_1311_);
lean_dec_ref(v_init_1310_);
return v_res_1320_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__7(lean_object* v_t_1321_, lean_object* v_init_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_){
_start:
{
lean_object* v_root_1330_; lean_object* v_tail_1331_; lean_object* v___x_1332_; 
v_root_1330_ = lean_ctor_get(v_t_1321_, 0);
v_tail_1331_ = lean_ctor_get(v_t_1321_, 1);
lean_inc_ref(v_init_1322_);
v___x_1332_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__7_spec__10(v_init_1322_, v_root_1330_, v_init_1322_, v___y_1323_, v___y_1324_, v___y_1325_, v___y_1326_, v___y_1327_, v___y_1328_);
lean_dec_ref(v_init_1322_);
if (lean_obj_tag(v___x_1332_) == 0)
{
lean_object* v_a_1333_; lean_object* v___x_1335_; uint8_t v_isShared_1336_; uint8_t v_isSharedCheck_1369_; 
v_a_1333_ = lean_ctor_get(v___x_1332_, 0);
v_isSharedCheck_1369_ = !lean_is_exclusive(v___x_1332_);
if (v_isSharedCheck_1369_ == 0)
{
v___x_1335_ = v___x_1332_;
v_isShared_1336_ = v_isSharedCheck_1369_;
goto v_resetjp_1334_;
}
else
{
lean_inc(v_a_1333_);
lean_dec(v___x_1332_);
v___x_1335_ = lean_box(0);
v_isShared_1336_ = v_isSharedCheck_1369_;
goto v_resetjp_1334_;
}
v_resetjp_1334_:
{
if (lean_obj_tag(v_a_1333_) == 0)
{
lean_object* v_a_1337_; lean_object* v___x_1339_; 
v_a_1337_ = lean_ctor_get(v_a_1333_, 0);
lean_inc(v_a_1337_);
lean_dec_ref_known(v_a_1333_, 1);
if (v_isShared_1336_ == 0)
{
lean_ctor_set(v___x_1335_, 0, v_a_1337_);
v___x_1339_ = v___x_1335_;
goto v_reusejp_1338_;
}
else
{
lean_object* v_reuseFailAlloc_1340_; 
v_reuseFailAlloc_1340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1340_, 0, v_a_1337_);
v___x_1339_ = v_reuseFailAlloc_1340_;
goto v_reusejp_1338_;
}
v_reusejp_1338_:
{
return v___x_1339_;
}
}
else
{
lean_object* v_a_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; size_t v_sz_1344_; size_t v___x_1345_; lean_object* v___x_1346_; 
lean_del_object(v___x_1335_);
v_a_1341_ = lean_ctor_get(v_a_1333_, 0);
lean_inc(v_a_1341_);
lean_dec_ref_known(v_a_1333_, 1);
v___x_1342_ = lean_box(0);
v___x_1343_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1343_, 0, v___x_1342_);
lean_ctor_set(v___x_1343_, 1, v_a_1341_);
v_sz_1344_ = lean_array_size(v_tail_1331_);
v___x_1345_ = ((size_t)0ULL);
v___x_1346_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__7_spec__11(v_tail_1331_, v_sz_1344_, v___x_1345_, v___x_1343_, v___y_1323_, v___y_1324_, v___y_1325_, v___y_1326_, v___y_1327_, v___y_1328_);
if (lean_obj_tag(v___x_1346_) == 0)
{
lean_object* v_a_1347_; lean_object* v___x_1349_; uint8_t v_isShared_1350_; uint8_t v_isSharedCheck_1360_; 
v_a_1347_ = lean_ctor_get(v___x_1346_, 0);
v_isSharedCheck_1360_ = !lean_is_exclusive(v___x_1346_);
if (v_isSharedCheck_1360_ == 0)
{
v___x_1349_ = v___x_1346_;
v_isShared_1350_ = v_isSharedCheck_1360_;
goto v_resetjp_1348_;
}
else
{
lean_inc(v_a_1347_);
lean_dec(v___x_1346_);
v___x_1349_ = lean_box(0);
v_isShared_1350_ = v_isSharedCheck_1360_;
goto v_resetjp_1348_;
}
v_resetjp_1348_:
{
lean_object* v_fst_1351_; 
v_fst_1351_ = lean_ctor_get(v_a_1347_, 0);
if (lean_obj_tag(v_fst_1351_) == 0)
{
lean_object* v_snd_1352_; lean_object* v___x_1354_; 
v_snd_1352_ = lean_ctor_get(v_a_1347_, 1);
lean_inc(v_snd_1352_);
lean_dec(v_a_1347_);
if (v_isShared_1350_ == 0)
{
lean_ctor_set(v___x_1349_, 0, v_snd_1352_);
v___x_1354_ = v___x_1349_;
goto v_reusejp_1353_;
}
else
{
lean_object* v_reuseFailAlloc_1355_; 
v_reuseFailAlloc_1355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1355_, 0, v_snd_1352_);
v___x_1354_ = v_reuseFailAlloc_1355_;
goto v_reusejp_1353_;
}
v_reusejp_1353_:
{
return v___x_1354_;
}
}
else
{
lean_object* v_val_1356_; lean_object* v___x_1358_; 
lean_inc_ref(v_fst_1351_);
lean_dec(v_a_1347_);
v_val_1356_ = lean_ctor_get(v_fst_1351_, 0);
lean_inc(v_val_1356_);
lean_dec_ref_known(v_fst_1351_, 1);
if (v_isShared_1350_ == 0)
{
lean_ctor_set(v___x_1349_, 0, v_val_1356_);
v___x_1358_ = v___x_1349_;
goto v_reusejp_1357_;
}
else
{
lean_object* v_reuseFailAlloc_1359_; 
v_reuseFailAlloc_1359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1359_, 0, v_val_1356_);
v___x_1358_ = v_reuseFailAlloc_1359_;
goto v_reusejp_1357_;
}
v_reusejp_1357_:
{
return v___x_1358_;
}
}
}
}
else
{
lean_object* v_a_1361_; lean_object* v___x_1363_; uint8_t v_isShared_1364_; uint8_t v_isSharedCheck_1368_; 
v_a_1361_ = lean_ctor_get(v___x_1346_, 0);
v_isSharedCheck_1368_ = !lean_is_exclusive(v___x_1346_);
if (v_isSharedCheck_1368_ == 0)
{
v___x_1363_ = v___x_1346_;
v_isShared_1364_ = v_isSharedCheck_1368_;
goto v_resetjp_1362_;
}
else
{
lean_inc(v_a_1361_);
lean_dec(v___x_1346_);
v___x_1363_ = lean_box(0);
v_isShared_1364_ = v_isSharedCheck_1368_;
goto v_resetjp_1362_;
}
v_resetjp_1362_:
{
lean_object* v___x_1366_; 
if (v_isShared_1364_ == 0)
{
v___x_1366_ = v___x_1363_;
goto v_reusejp_1365_;
}
else
{
lean_object* v_reuseFailAlloc_1367_; 
v_reuseFailAlloc_1367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1367_, 0, v_a_1361_);
v___x_1366_ = v_reuseFailAlloc_1367_;
goto v_reusejp_1365_;
}
v_reusejp_1365_:
{
return v___x_1366_;
}
}
}
}
}
}
else
{
lean_object* v_a_1370_; lean_object* v___x_1372_; uint8_t v_isShared_1373_; uint8_t v_isSharedCheck_1377_; 
v_a_1370_ = lean_ctor_get(v___x_1332_, 0);
v_isSharedCheck_1377_ = !lean_is_exclusive(v___x_1332_);
if (v_isSharedCheck_1377_ == 0)
{
v___x_1372_ = v___x_1332_;
v_isShared_1373_ = v_isSharedCheck_1377_;
goto v_resetjp_1371_;
}
else
{
lean_inc(v_a_1370_);
lean_dec(v___x_1332_);
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
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__7___boxed(lean_object* v_t_1378_, lean_object* v_init_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_){
_start:
{
lean_object* v_res_1387_; 
v_res_1387_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__7(v_t_1378_, v_init_1379_, v___y_1380_, v___y_1381_, v___y_1382_, v___y_1383_, v___y_1384_, v___y_1385_);
lean_dec(v___y_1385_);
lean_dec_ref(v___y_1384_);
lean_dec(v___y_1383_);
lean_dec_ref(v___y_1382_);
lean_dec(v___y_1381_);
lean_dec_ref(v___y_1380_);
lean_dec_ref(v_t_1378_);
return v_res_1387_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty___lam__0(lean_object* v_todo_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_){
_start:
{
lean_object* v_lctx_1396_; lean_object* v_decls_1397_; lean_object* v___x_1398_; 
v_lctx_1396_ = lean_ctor_get(v___y_1391_, 2);
v_decls_1397_ = lean_ctor_get(v_lctx_1396_, 1);
v___x_1398_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__7(v_decls_1397_, v_todo_1388_, v___y_1389_, v___y_1390_, v___y_1391_, v___y_1392_, v___y_1393_, v___y_1394_);
if (lean_obj_tag(v___x_1398_) == 0)
{
lean_object* v___x_1400_; uint8_t v_isShared_1401_; uint8_t v_isSharedCheck_1406_; 
v_isSharedCheck_1406_ = !lean_is_exclusive(v___x_1398_);
if (v_isSharedCheck_1406_ == 0)
{
lean_object* v_unused_1407_; 
v_unused_1407_ = lean_ctor_get(v___x_1398_, 0);
lean_dec(v_unused_1407_);
v___x_1400_ = v___x_1398_;
v_isShared_1401_ = v_isSharedCheck_1406_;
goto v_resetjp_1399_;
}
else
{
lean_dec(v___x_1398_);
v___x_1400_ = lean_box(0);
v_isShared_1401_ = v_isSharedCheck_1406_;
goto v_resetjp_1399_;
}
v_resetjp_1399_:
{
lean_object* v___x_1402_; lean_object* v___x_1404_; 
v___x_1402_ = lean_box(0);
if (v_isShared_1401_ == 0)
{
lean_ctor_set(v___x_1400_, 0, v___x_1402_);
v___x_1404_ = v___x_1400_;
goto v_reusejp_1403_;
}
else
{
lean_object* v_reuseFailAlloc_1405_; 
v_reuseFailAlloc_1405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1405_, 0, v___x_1402_);
v___x_1404_ = v_reuseFailAlloc_1405_;
goto v_reusejp_1403_;
}
v_reusejp_1403_:
{
return v___x_1404_;
}
}
}
else
{
lean_object* v_a_1408_; lean_object* v___x_1410_; uint8_t v_isShared_1411_; uint8_t v_isSharedCheck_1415_; 
v_a_1408_ = lean_ctor_get(v___x_1398_, 0);
v_isSharedCheck_1415_ = !lean_is_exclusive(v___x_1398_);
if (v_isSharedCheck_1415_ == 0)
{
v___x_1410_ = v___x_1398_;
v_isShared_1411_ = v_isSharedCheck_1415_;
goto v_resetjp_1409_;
}
else
{
lean_inc(v_a_1408_);
lean_dec(v___x_1398_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty___lam__0___boxed(lean_object* v_todo_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_){
_start:
{
lean_object* v_res_1424_; 
v_res_1424_ = l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty___lam__0(v_todo_1416_, v___y_1417_, v___y_1418_, v___y_1419_, v___y_1420_, v___y_1421_, v___y_1422_);
lean_dec(v___y_1422_);
lean_dec_ref(v___y_1421_);
lean_dec(v___y_1420_);
lean_dec_ref(v___y_1419_);
lean_dec(v___y_1418_);
lean_dec_ref(v___y_1417_);
return v_res_1424_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty___closed__0(void){
_start:
{
lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; 
v___x_1425_ = lean_box(0);
v___x_1426_ = lean_unsigned_to_nat(16u);
v___x_1427_ = lean_mk_array(v___x_1426_, v___x_1425_);
return v___x_1427_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty___closed__1(void){
_start:
{
lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v_todo_1430_; 
v___x_1428_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty___closed__0, &l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty___closed__0_once, _init_l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty___closed__0);
v___x_1429_ = lean_unsigned_to_nat(0u);
v_todo_1430_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_todo_1430_, 0, v___x_1429_);
lean_ctor_set(v_todo_1430_, 1, v___x_1428_);
return v_todo_1430_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty___closed__2(void){
_start:
{
lean_object* v_todo_1431_; lean_object* v___f_1432_; 
v_todo_1431_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty___closed__1, &l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty___closed__1_once, _init_l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty___closed__1);
v___f_1432_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1432_, 0, v_todo_1431_);
return v___f_1432_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty(lean_object* v_g_1433_, lean_object* v_a_1434_, lean_object* v_a_1435_, lean_object* v_a_1436_, lean_object* v_a_1437_, lean_object* v_a_1438_, lean_object* v_a_1439_){
_start:
{
lean_object* v___f_1441_; lean_object* v___x_1442_; 
v___f_1441_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty___closed__2, &l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty___closed__2_once, _init_l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty___closed__2);
v___x_1442_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__8___redArg(v_g_1433_, v___f_1441_, v_a_1434_, v_a_1435_, v_a_1436_, v_a_1437_, v_a_1438_, v_a_1439_);
return v___x_1442_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty___boxed(lean_object* v_g_1443_, lean_object* v_a_1444_, lean_object* v_a_1445_, lean_object* v_a_1446_, lean_object* v_a_1447_, lean_object* v_a_1448_, lean_object* v_a_1449_, lean_object* v_a_1450_){
_start:
{
lean_object* v_res_1451_; 
v_res_1451_ = l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty(v_g_1443_, v_a_1444_, v_a_1445_, v_a_1446_, v_a_1447_, v_a_1448_, v_a_1449_);
lean_dec(v_a_1449_);
lean_dec_ref(v_a_1448_);
lean_dec(v_a_1447_);
lean_dec_ref(v_a_1446_);
lean_dec(v_a_1445_);
lean_dec_ref(v_a_1444_);
return v_res_1451_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__0(lean_object* v_00_u03b2_1452_, lean_object* v_m_1453_, lean_object* v_a_1454_){
_start:
{
uint8_t v___x_1455_; 
v___x_1455_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__0___redArg(v_m_1453_, v_a_1454_);
return v___x_1455_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__0___boxed(lean_object* v_00_u03b2_1456_, lean_object* v_m_1457_, lean_object* v_a_1458_){
_start:
{
uint8_t v_res_1459_; lean_object* v_r_1460_; 
v_res_1459_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__0(v_00_u03b2_1456_, v_m_1457_, v_a_1458_);
lean_dec(v_a_1458_);
lean_dec_ref(v_m_1457_);
v_r_1460_ = lean_box(v_res_1459_);
return v_r_1460_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__5(lean_object* v_00_u03b2_1461_, lean_object* v_m_1462_, lean_object* v_a_1463_){
_start:
{
lean_object* v___x_1464_; 
v___x_1464_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__5___redArg(v_m_1462_, v_a_1463_);
return v___x_1464_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__5___boxed(lean_object* v_00_u03b2_1465_, lean_object* v_m_1466_, lean_object* v_a_1467_){
_start:
{
lean_object* v_res_1468_; 
v_res_1468_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__5(v_00_u03b2_1465_, v_m_1466_, v_a_1467_);
lean_dec(v_a_1467_);
return v_res_1468_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__6(lean_object* v_00_u03b2_1469_, lean_object* v_m_1470_, lean_object* v_a_1471_, lean_object* v_b_1472_){
_start:
{
lean_object* v___x_1473_; 
v___x_1473_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__6___redArg(v_m_1470_, v_a_1471_, v_b_1472_);
return v___x_1473_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__0_spec__0(lean_object* v_00_u03b2_1474_, lean_object* v_a_1475_, lean_object* v_x_1476_){
_start:
{
uint8_t v___x_1477_; 
v___x_1477_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__0_spec__0___redArg(v_a_1475_, v_x_1476_);
return v___x_1477_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1478_, lean_object* v_a_1479_, lean_object* v_x_1480_){
_start:
{
uint8_t v_res_1481_; lean_object* v_r_1482_; 
v_res_1481_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__0_spec__0(v_00_u03b2_1478_, v_a_1479_, v_x_1480_);
lean_dec(v_x_1480_);
lean_dec(v_a_1479_);
v_r_1482_ = lean_box(v_res_1481_);
return v_r_1482_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__5_spec__6(lean_object* v_00_u03b2_1483_, lean_object* v_a_1484_, lean_object* v_x_1485_){
_start:
{
lean_object* v___x_1486_; 
v___x_1486_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__5_spec__6___redArg(v_a_1484_, v_x_1485_);
return v___x_1486_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__5_spec__6___boxed(lean_object* v_00_u03b2_1487_, lean_object* v_a_1488_, lean_object* v_x_1489_){
_start:
{
lean_object* v_res_1490_; 
v_res_1490_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__5_spec__6(v_00_u03b2_1487_, v_a_1488_, v_x_1489_);
lean_dec(v_a_1488_);
return v_res_1490_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__6_spec__8(lean_object* v_00_u03b2_1491_, lean_object* v_data_1492_){
_start:
{
lean_object* v___x_1493_; 
v___x_1493_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__6_spec__8___redArg(v_data_1492_);
return v___x_1493_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__6_spec__8_spec__10(lean_object* v_00_u03b2_1494_, lean_object* v_i_1495_, lean_object* v_source_1496_, lean_object* v_target_1497_){
_start:
{
lean_object* v___x_1498_; 
v___x_1498_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__6_spec__8_spec__10___redArg(v_i_1495_, v_source_1496_, v_target_1497_);
return v___x_1498_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__6_spec__8_spec__10_spec__12(lean_object* v_00_u03b2_1499_, lean_object* v_x_1500_, lean_object* v_x_1501_){
_start:
{
lean_object* v___x_1502_; 
v___x_1502_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__6_spec__8_spec__10_spec__12___redArg(v_x_1500_, v_x_1501_);
return v___x_1502_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_nnf___lam__0(lean_object* v_x_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_){
_start:
{
lean_object* v___x_1516_; lean_object* v___x_1517_; 
v___x_1516_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_nnf___lam__0___closed__0));
v___x_1517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1517_, 0, v___x_1516_);
return v___x_1517_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_nnf___lam__0___boxed(lean_object* v_x_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_){
_start:
{
lean_object* v_res_1529_; 
v_res_1529_ = l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_nnf___lam__0(v_x_1518_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_, v___y_1523_, v___y_1524_, v___y_1525_, v___y_1526_, v___y_1527_);
lean_dec(v___y_1527_);
lean_dec_ref(v___y_1526_);
lean_dec(v___y_1525_);
lean_dec_ref(v___y_1524_);
lean_dec(v___y_1523_);
lean_dec_ref(v___y_1522_);
lean_dec(v___y_1521_);
lean_dec_ref(v___y_1520_);
lean_dec(v___y_1519_);
lean_dec_ref(v_x_1518_);
return v_res_1529_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_nnf_spec__0(size_t v_sz_1530_, size_t v_i_1531_, lean_object* v_bs_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_){
_start:
{
uint8_t v___x_1543_; 
v___x_1543_ = lean_usize_dec_lt(v_i_1531_, v_sz_1530_);
if (v___x_1543_ == 0)
{
lean_object* v___x_1544_; 
v___x_1544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1544_, 0, v_bs_1532_);
return v___x_1544_;
}
else
{
lean_object* v_v_1545_; lean_object* v_type_1546_; lean_object* v___x_1547_; lean_object* v_bs_x27_1548_; lean_object* v___x_1549_; 
v_v_1545_ = lean_array_uget(v_bs_1532_, v_i_1531_);
v_type_1546_ = lean_ctor_get(v_v_1545_, 1);
v___x_1547_ = lean_unsigned_to_nat(0u);
v_bs_x27_1548_ = lean_array_uset(v_bs_1532_, v_i_1531_, v___x_1547_);
lean_inc(v___y_1541_);
lean_inc_ref(v___y_1540_);
lean_inc(v___y_1539_);
lean_inc_ref(v___y_1538_);
lean_inc(v___y_1537_);
lean_inc_ref(v___y_1536_);
lean_inc(v___y_1535_);
lean_inc_ref(v___y_1534_);
lean_inc(v___y_1533_);
lean_inc_ref(v_type_1546_);
v___x_1549_ = lean_sym_simp(v_type_1546_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_);
if (lean_obj_tag(v___x_1549_) == 0)
{
lean_object* v_a_1550_; lean_object* v___x_1551_; 
v_a_1550_ = lean_ctor_get(v___x_1549_, 0);
lean_inc(v_a_1550_);
lean_dec_ref_known(v___x_1549_, 1);
v___x_1551_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult___redArg(v_v_1545_, v_a_1550_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_);
if (lean_obj_tag(v___x_1551_) == 0)
{
lean_object* v_a_1552_; size_t v___x_1553_; size_t v___x_1554_; lean_object* v___x_1555_; 
v_a_1552_ = lean_ctor_get(v___x_1551_, 0);
lean_inc(v_a_1552_);
lean_dec_ref_known(v___x_1551_, 1);
v___x_1553_ = ((size_t)1ULL);
v___x_1554_ = lean_usize_add(v_i_1531_, v___x_1553_);
v___x_1555_ = lean_array_uset(v_bs_x27_1548_, v_i_1531_, v_a_1552_);
v_i_1531_ = v___x_1554_;
v_bs_1532_ = v___x_1555_;
goto _start;
}
else
{
lean_object* v_a_1557_; lean_object* v___x_1559_; uint8_t v_isShared_1560_; uint8_t v_isSharedCheck_1564_; 
lean_dec_ref(v_bs_x27_1548_);
v_a_1557_ = lean_ctor_get(v___x_1551_, 0);
v_isSharedCheck_1564_ = !lean_is_exclusive(v___x_1551_);
if (v_isSharedCheck_1564_ == 0)
{
v___x_1559_ = v___x_1551_;
v_isShared_1560_ = v_isSharedCheck_1564_;
goto v_resetjp_1558_;
}
else
{
lean_inc(v_a_1557_);
lean_dec(v___x_1551_);
v___x_1559_ = lean_box(0);
v_isShared_1560_ = v_isSharedCheck_1564_;
goto v_resetjp_1558_;
}
v_resetjp_1558_:
{
lean_object* v___x_1562_; 
if (v_isShared_1560_ == 0)
{
v___x_1562_ = v___x_1559_;
goto v_reusejp_1561_;
}
else
{
lean_object* v_reuseFailAlloc_1563_; 
v_reuseFailAlloc_1563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1563_, 0, v_a_1557_);
v___x_1562_ = v_reuseFailAlloc_1563_;
goto v_reusejp_1561_;
}
v_reusejp_1561_:
{
return v___x_1562_;
}
}
}
}
else
{
lean_object* v_a_1565_; lean_object* v___x_1567_; uint8_t v_isShared_1568_; uint8_t v_isSharedCheck_1572_; 
lean_dec_ref(v_bs_x27_1548_);
lean_dec(v_v_1545_);
v_a_1565_ = lean_ctor_get(v___x_1549_, 0);
v_isSharedCheck_1572_ = !lean_is_exclusive(v___x_1549_);
if (v_isSharedCheck_1572_ == 0)
{
v___x_1567_ = v___x_1549_;
v_isShared_1568_ = v_isSharedCheck_1572_;
goto v_resetjp_1566_;
}
else
{
lean_inc(v_a_1565_);
lean_dec(v___x_1549_);
v___x_1567_ = lean_box(0);
v_isShared_1568_ = v_isSharedCheck_1572_;
goto v_resetjp_1566_;
}
v_resetjp_1566_:
{
lean_object* v___x_1570_; 
if (v_isShared_1568_ == 0)
{
v___x_1570_ = v___x_1567_;
goto v_reusejp_1569_;
}
else
{
lean_object* v_reuseFailAlloc_1571_; 
v_reuseFailAlloc_1571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1571_, 0, v_a_1565_);
v___x_1570_ = v_reuseFailAlloc_1571_;
goto v_reusejp_1569_;
}
v_reusejp_1569_:
{
return v___x_1570_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_nnf_spec__0___boxed(lean_object* v_sz_1573_, lean_object* v_i_1574_, lean_object* v_bs_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_){
_start:
{
size_t v_sz_boxed_1586_; size_t v_i_boxed_1587_; lean_object* v_res_1588_; 
v_sz_boxed_1586_ = lean_unbox_usize(v_sz_1573_);
lean_dec(v_sz_1573_);
v_i_boxed_1587_ = lean_unbox_usize(v_i_1574_);
lean_dec(v_i_1574_);
v_res_1588_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_nnf_spec__0(v_sz_boxed_1586_, v_i_boxed_1587_, v_bs_1575_, v___y_1576_, v___y_1577_, v___y_1578_, v___y_1579_, v___y_1580_, v___y_1581_, v___y_1582_, v___y_1583_, v___y_1584_);
lean_dec(v___y_1584_);
lean_dec_ref(v___y_1583_);
lean_dec(v___y_1582_);
lean_dec_ref(v___y_1581_);
lean_dec(v___y_1580_);
lean_dec_ref(v___y_1579_);
lean_dec(v___y_1578_);
lean_dec_ref(v___y_1577_);
lean_dec(v___y_1576_);
return v_res_1588_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_nnf(lean_object* v_hyps_1596_, lean_object* v_cfg_1597_, lean_object* v_a_1598_, lean_object* v_a_1599_, lean_object* v_a_1600_, lean_object* v_a_1601_, lean_object* v_a_1602_, lean_object* v_a_1603_){
_start:
{
lean_object* v_config_1605_; lean_object* v_maxSteps_1606_; size_t v_sz_1607_; lean_object* v_methods_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; 
v_config_1605_ = lean_ctor_get(v_cfg_1597_, 5);
v_maxSteps_1606_ = lean_ctor_get(v_config_1605_, 1);
v_sz_1607_ = lean_array_size(v_hyps_1596_);
v_methods_1608_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_nnf___closed__2));
v___x_1609_ = lean_box_usize(v_sz_1607_);
v___x_1610_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_nnf___boxed__const__1));
v___x_1611_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_nnf_spec__0___boxed), 13, 3);
lean_closure_set(v___x_1611_, 0, v___x_1609_);
lean_closure_set(v___x_1611_, 1, v___x_1610_);
lean_closure_set(v___x_1611_, 2, v_hyps_1596_);
v___x_1612_ = lean_unsigned_to_nat(2u);
lean_inc(v_maxSteps_1606_);
v___x_1613_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1613_, 0, v_maxSteps_1606_);
lean_ctor_set(v___x_1613_, 1, v___x_1612_);
v___x_1614_ = l_Lean_Meta_Sym_Simp_SimpM_run_x27___redArg(v___x_1611_, v_methods_1608_, v___x_1613_, v_a_1598_, v_a_1599_, v_a_1600_, v_a_1601_, v_a_1602_, v_a_1603_);
return v___x_1614_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_nnf___boxed(lean_object* v_hyps_1615_, lean_object* v_cfg_1616_, lean_object* v_a_1617_, lean_object* v_a_1618_, lean_object* v_a_1619_, lean_object* v_a_1620_, lean_object* v_a_1621_, lean_object* v_a_1622_, lean_object* v_a_1623_){
_start:
{
lean_object* v_res_1624_; 
v_res_1624_ = l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_nnf(v_hyps_1615_, v_cfg_1616_, v_a_1617_, v_a_1618_, v_a_1619_, v_a_1620_, v_a_1621_, v_a_1622_);
lean_dec(v_a_1622_);
lean_dec_ref(v_a_1621_);
lean_dec(v_a_1620_);
lean_dec_ref(v_a_1619_);
lean_dec(v_a_1618_);
lean_dec_ref(v_a_1617_);
lean_dec_ref(v_cfg_1616_);
return v_res_1624_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_andFlatten_flattenOne___closed__4(void){
_start:
{
lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; 
v___x_1632_ = lean_box(0);
v___x_1633_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_andFlatten_flattenOne___closed__3));
v___x_1634_ = l_Lean_mkConst(v___x_1633_, v___x_1632_);
return v___x_1634_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_andFlatten_flattenOne___closed__7(void){
_start:
{
lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; 
v___x_1639_ = lean_box(0);
v___x_1640_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_andFlatten_flattenOne___closed__6));
v___x_1641_ = l_Lean_mkConst(v___x_1640_, v___x_1639_);
return v___x_1641_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_andFlatten_flattenOne(lean_object* v_worklist_1642_, lean_object* v_acc_1643_, lean_object* v_a_1644_, lean_object* v_a_1645_, lean_object* v_a_1646_, lean_object* v_a_1647_, lean_object* v_a_1648_, lean_object* v_a_1649_){
_start:
{
if (lean_obj_tag(v_worklist_1642_) == 0)
{
lean_object* v___x_1651_; 
v___x_1651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1651_, 0, v_acc_1643_);
return v___x_1651_;
}
else
{
lean_object* v_head_1652_; lean_object* v_tail_1653_; lean_object* v___x_1655_; uint8_t v_isShared_1656_; uint8_t v_isSharedCheck_1711_; 
v_head_1652_ = lean_ctor_get(v_worklist_1642_, 0);
v_tail_1653_ = lean_ctor_get(v_worklist_1642_, 1);
v_isSharedCheck_1711_ = !lean_is_exclusive(v_worklist_1642_);
if (v_isSharedCheck_1711_ == 0)
{
v___x_1655_ = v_worklist_1642_;
v_isShared_1656_ = v_isSharedCheck_1711_;
goto v_resetjp_1654_;
}
else
{
lean_inc(v_tail_1653_);
lean_inc(v_head_1652_);
lean_dec(v_worklist_1642_);
v___x_1655_ = lean_box(0);
v_isShared_1656_ = v_isSharedCheck_1711_;
goto v_resetjp_1654_;
}
v_resetjp_1654_:
{
lean_object* v___y_1658_; lean_object* v___y_1659_; lean_object* v___y_1660_; lean_object* v___y_1661_; lean_object* v___y_1662_; lean_object* v___y_1663_; lean_object* v_name_1666_; lean_object* v_type_1667_; lean_object* v_value_1668_; lean_object* v_source_1669_; lean_object* v___x_1670_; 
v_name_1666_ = lean_ctor_get(v_head_1652_, 0);
v_type_1667_ = lean_ctor_get(v_head_1652_, 1);
v_value_1668_ = lean_ctor_get(v_head_1652_, 2);
v_source_1669_ = lean_ctor_get(v_head_1652_, 3);
lean_inc_ref(v_type_1667_);
v___x_1670_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_type_1667_, v_a_1647_);
if (lean_obj_tag(v___x_1670_) == 0)
{
lean_object* v_a_1671_; lean_object* v___x_1672_; uint8_t v___x_1673_; 
v_a_1671_ = lean_ctor_get(v___x_1670_, 0);
lean_inc(v_a_1671_);
lean_dec_ref_known(v___x_1670_, 1);
v___x_1672_ = l_Lean_Expr_cleanupAnnotations(v_a_1671_);
lean_dec(v_a_1671_);
v___x_1673_ = l_Lean_Expr_isApp(v___x_1672_);
if (v___x_1673_ == 0)
{
lean_dec_ref(v___x_1672_);
lean_del_object(v___x_1655_);
v___y_1658_ = v_a_1644_;
v___y_1659_ = v_a_1645_;
v___y_1660_ = v_a_1646_;
v___y_1661_ = v_a_1647_;
v___y_1662_ = v_a_1648_;
v___y_1663_ = v_a_1649_;
goto v___jp_1657_;
}
else
{
lean_object* v___x_1674_; uint8_t v___x_1675_; 
v___x_1674_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1672_);
v___x_1675_ = l_Lean_Expr_isApp(v___x_1674_);
if (v___x_1675_ == 0)
{
lean_dec_ref(v___x_1674_);
lean_dec_ref(v___x_1672_);
lean_del_object(v___x_1655_);
v___y_1658_ = v_a_1644_;
v___y_1659_ = v_a_1645_;
v___y_1660_ = v_a_1646_;
v___y_1661_ = v_a_1647_;
v___y_1662_ = v_a_1648_;
v___y_1663_ = v_a_1649_;
goto v___jp_1657_;
}
else
{
lean_object* v___x_1676_; lean_object* v___x_1677_; uint8_t v___x_1678_; 
v___x_1676_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1674_);
v___x_1677_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_andFlatten_flattenOne___closed__1));
v___x_1678_ = l_Lean_Expr_isConstOf(v___x_1676_, v___x_1677_);
lean_dec_ref(v___x_1676_);
if (v___x_1678_ == 0)
{
lean_dec_ref(v___x_1674_);
lean_dec_ref(v___x_1672_);
lean_del_object(v___x_1655_);
v___y_1658_ = v_a_1644_;
v___y_1659_ = v_a_1645_;
v___y_1660_ = v_a_1646_;
v___y_1661_ = v_a_1647_;
v___y_1662_ = v_a_1648_;
v___y_1663_ = v_a_1649_;
goto v___jp_1657_;
}
else
{
lean_object* v___x_1680_; uint8_t v_isShared_1681_; uint8_t v_isSharedCheck_1698_; 
lean_inc(v_source_1669_);
lean_inc_ref(v_value_1668_);
lean_inc(v_name_1666_);
v_isSharedCheck_1698_ = !lean_is_exclusive(v_head_1652_);
if (v_isSharedCheck_1698_ == 0)
{
lean_object* v_unused_1699_; lean_object* v_unused_1700_; lean_object* v_unused_1701_; lean_object* v_unused_1702_; 
v_unused_1699_ = lean_ctor_get(v_head_1652_, 3);
lean_dec(v_unused_1699_);
v_unused_1700_ = lean_ctor_get(v_head_1652_, 2);
lean_dec(v_unused_1700_);
v_unused_1701_ = lean_ctor_get(v_head_1652_, 1);
lean_dec(v_unused_1701_);
v_unused_1702_ = lean_ctor_get(v_head_1652_, 0);
lean_dec(v_unused_1702_);
v___x_1680_ = v_head_1652_;
v_isShared_1681_ = v_isSharedCheck_1698_;
goto v_resetjp_1679_;
}
else
{
lean_dec(v_head_1652_);
v___x_1680_ = lean_box(0);
v_isShared_1681_ = v_isSharedCheck_1698_;
goto v_resetjp_1679_;
}
v_resetjp_1679_:
{
lean_object* v_arg_1682_; lean_object* v_arg_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1688_; 
v_arg_1682_ = lean_ctor_get(v___x_1672_, 1);
lean_inc_ref_n(v_arg_1682_, 2);
lean_dec_ref(v___x_1672_);
v_arg_1683_ = lean_ctor_get(v___x_1674_, 1);
lean_inc_ref_n(v_arg_1683_, 3);
lean_dec_ref(v___x_1674_);
v___x_1684_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_andFlatten_flattenOne___closed__4, &l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_andFlatten_flattenOne___closed__4_once, _init_l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_andFlatten_flattenOne___closed__4);
lean_inc_ref(v_value_1668_);
v___x_1685_ = l_Lean_mkApp3(v___x_1684_, v_arg_1683_, v_arg_1682_, v_value_1668_);
v___x_1686_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1686_, 0, v_source_1669_);
lean_inc_ref(v___x_1686_);
lean_inc(v_name_1666_);
if (v_isShared_1681_ == 0)
{
lean_ctor_set(v___x_1680_, 3, v___x_1686_);
lean_ctor_set(v___x_1680_, 2, v___x_1685_);
lean_ctor_set(v___x_1680_, 1, v_arg_1683_);
v___x_1688_ = v___x_1680_;
goto v_reusejp_1687_;
}
else
{
lean_object* v_reuseFailAlloc_1697_; 
v_reuseFailAlloc_1697_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1697_, 0, v_name_1666_);
lean_ctor_set(v_reuseFailAlloc_1697_, 1, v_arg_1683_);
lean_ctor_set(v_reuseFailAlloc_1697_, 2, v___x_1685_);
lean_ctor_set(v_reuseFailAlloc_1697_, 3, v___x_1686_);
v___x_1688_ = v_reuseFailAlloc_1697_;
goto v_reusejp_1687_;
}
v_reusejp_1687_:
{
lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1693_; 
v___x_1689_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_andFlatten_flattenOne___closed__7, &l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_andFlatten_flattenOne___closed__7_once, _init_l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_andFlatten_flattenOne___closed__7);
lean_inc_ref(v_arg_1682_);
v___x_1690_ = l_Lean_mkApp3(v___x_1689_, v_arg_1683_, v_arg_1682_, v_value_1668_);
v___x_1691_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1691_, 0, v_name_1666_);
lean_ctor_set(v___x_1691_, 1, v_arg_1682_);
lean_ctor_set(v___x_1691_, 2, v___x_1690_);
lean_ctor_set(v___x_1691_, 3, v___x_1686_);
if (v_isShared_1656_ == 0)
{
lean_ctor_set(v___x_1655_, 0, v___x_1691_);
v___x_1693_ = v___x_1655_;
goto v_reusejp_1692_;
}
else
{
lean_object* v_reuseFailAlloc_1696_; 
v_reuseFailAlloc_1696_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1696_, 0, v___x_1691_);
lean_ctor_set(v_reuseFailAlloc_1696_, 1, v_tail_1653_);
v___x_1693_ = v_reuseFailAlloc_1696_;
goto v_reusejp_1692_;
}
v_reusejp_1692_:
{
lean_object* v___x_1694_; 
v___x_1694_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1694_, 0, v___x_1688_);
lean_ctor_set(v___x_1694_, 1, v___x_1693_);
v_worklist_1642_ = v___x_1694_;
goto _start;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1703_; lean_object* v___x_1705_; uint8_t v_isShared_1706_; uint8_t v_isSharedCheck_1710_; 
lean_del_object(v___x_1655_);
lean_dec(v_tail_1653_);
lean_dec(v_head_1652_);
lean_dec_ref(v_acc_1643_);
v_a_1703_ = lean_ctor_get(v___x_1670_, 0);
v_isSharedCheck_1710_ = !lean_is_exclusive(v___x_1670_);
if (v_isSharedCheck_1710_ == 0)
{
v___x_1705_ = v___x_1670_;
v_isShared_1706_ = v_isSharedCheck_1710_;
goto v_resetjp_1704_;
}
else
{
lean_inc(v_a_1703_);
lean_dec(v___x_1670_);
v___x_1705_ = lean_box(0);
v_isShared_1706_ = v_isSharedCheck_1710_;
goto v_resetjp_1704_;
}
v_resetjp_1704_:
{
lean_object* v___x_1708_; 
if (v_isShared_1706_ == 0)
{
v___x_1708_ = v___x_1705_;
goto v_reusejp_1707_;
}
else
{
lean_object* v_reuseFailAlloc_1709_; 
v_reuseFailAlloc_1709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1709_, 0, v_a_1703_);
v___x_1708_ = v_reuseFailAlloc_1709_;
goto v_reusejp_1707_;
}
v_reusejp_1707_:
{
return v___x_1708_;
}
}
}
v___jp_1657_:
{
lean_object* v___x_1664_; 
v___x_1664_ = lean_array_push(v_acc_1643_, v_head_1652_);
v_worklist_1642_ = v_tail_1653_;
v_acc_1643_ = v___x_1664_;
v_a_1644_ = v___y_1658_;
v_a_1645_ = v___y_1659_;
v_a_1646_ = v___y_1660_;
v_a_1647_ = v___y_1661_;
v_a_1648_ = v___y_1662_;
v_a_1649_ = v___y_1663_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_andFlatten_flattenOne___boxed(lean_object* v_worklist_1712_, lean_object* v_acc_1713_, lean_object* v_a_1714_, lean_object* v_a_1715_, lean_object* v_a_1716_, lean_object* v_a_1717_, lean_object* v_a_1718_, lean_object* v_a_1719_, lean_object* v_a_1720_){
_start:
{
lean_object* v_res_1721_; 
v_res_1721_ = l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_andFlatten_flattenOne(v_worklist_1712_, v_acc_1713_, v_a_1714_, v_a_1715_, v_a_1716_, v_a_1717_, v_a_1718_, v_a_1719_);
lean_dec(v_a_1719_);
lean_dec_ref(v_a_1718_);
lean_dec(v_a_1717_);
lean_dec_ref(v_a_1716_);
lean_dec(v_a_1715_);
lean_dec_ref(v_a_1714_);
return v_res_1721_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_andFlatten_spec__0(lean_object* v_as_1724_, size_t v_i_1725_, size_t v_stop_1726_, lean_object* v_b_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_){
_start:
{
uint8_t v___x_1735_; 
v___x_1735_ = lean_usize_dec_eq(v_i_1725_, v_stop_1726_);
if (v___x_1735_ == 0)
{
lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; 
v___x_1736_ = lean_array_uget_borrowed(v_as_1724_, v_i_1725_);
v___x_1737_ = lean_box(0);
lean_inc(v___x_1736_);
v___x_1738_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1738_, 0, v___x_1736_);
lean_ctor_set(v___x_1738_, 1, v___x_1737_);
v___x_1739_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_andFlatten_spec__0___closed__0));
v___x_1740_ = l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_andFlatten_flattenOne(v___x_1738_, v___x_1739_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_);
if (lean_obj_tag(v___x_1740_) == 0)
{
lean_object* v_a_1741_; lean_object* v___x_1742_; size_t v___x_1743_; size_t v___x_1744_; 
v_a_1741_ = lean_ctor_get(v___x_1740_, 0);
lean_inc(v_a_1741_);
lean_dec_ref_known(v___x_1740_, 1);
v___x_1742_ = l_Array_append___redArg(v_b_1727_, v_a_1741_);
lean_dec(v_a_1741_);
v___x_1743_ = ((size_t)1ULL);
v___x_1744_ = lean_usize_add(v_i_1725_, v___x_1743_);
v_i_1725_ = v___x_1744_;
v_b_1727_ = v___x_1742_;
goto _start;
}
else
{
lean_dec_ref(v_b_1727_);
return v___x_1740_;
}
}
else
{
lean_object* v___x_1746_; 
v___x_1746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1746_, 0, v_b_1727_);
return v___x_1746_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_andFlatten_spec__0___boxed(lean_object* v_as_1747_, lean_object* v_i_1748_, lean_object* v_stop_1749_, lean_object* v_b_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_){
_start:
{
size_t v_i_boxed_1758_; size_t v_stop_boxed_1759_; lean_object* v_res_1760_; 
v_i_boxed_1758_ = lean_unbox_usize(v_i_1748_);
lean_dec(v_i_1748_);
v_stop_boxed_1759_ = lean_unbox_usize(v_stop_1749_);
lean_dec(v_stop_1749_);
v_res_1760_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_andFlatten_spec__0(v_as_1747_, v_i_boxed_1758_, v_stop_boxed_1759_, v_b_1750_, v___y_1751_, v___y_1752_, v___y_1753_, v___y_1754_, v___y_1755_, v___y_1756_);
lean_dec(v___y_1756_);
lean_dec_ref(v___y_1755_);
lean_dec(v___y_1754_);
lean_dec_ref(v___y_1753_);
lean_dec(v___y_1752_);
lean_dec_ref(v___y_1751_);
lean_dec_ref(v_as_1747_);
return v_res_1760_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_andFlatten(lean_object* v_hyps_1763_, lean_object* v_a_1764_, lean_object* v_a_1765_, lean_object* v_a_1766_, lean_object* v_a_1767_, lean_object* v_a_1768_, lean_object* v_a_1769_){
_start:
{
lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; uint8_t v___x_1774_; 
v___x_1771_ = lean_unsigned_to_nat(0u);
v___x_1772_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_andFlatten___closed__0));
v___x_1773_ = lean_array_get_size(v_hyps_1763_);
v___x_1774_ = lean_nat_dec_lt(v___x_1771_, v___x_1773_);
if (v___x_1774_ == 0)
{
lean_object* v___x_1775_; 
v___x_1775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1775_, 0, v___x_1772_);
return v___x_1775_;
}
else
{
size_t v___x_1776_; size_t v___x_1777_; lean_object* v___x_1778_; 
v___x_1776_ = ((size_t)0ULL);
v___x_1777_ = lean_usize_of_nat(v___x_1773_);
v___x_1778_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_andFlatten_spec__0(v_hyps_1763_, v___x_1776_, v___x_1777_, v___x_1772_, v_a_1764_, v_a_1765_, v_a_1766_, v_a_1767_, v_a_1768_, v_a_1769_);
return v___x_1778_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_andFlatten___boxed(lean_object* v_hyps_1779_, lean_object* v_a_1780_, lean_object* v_a_1781_, lean_object* v_a_1782_, lean_object* v_a_1783_, lean_object* v_a_1784_, lean_object* v_a_1785_, lean_object* v_a_1786_){
_start:
{
lean_object* v_res_1787_; 
v_res_1787_ = l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_andFlatten(v_hyps_1779_, v_a_1780_, v_a_1781_, v_a_1782_, v_a_1783_, v_a_1784_, v_a_1785_);
lean_dec(v_a_1785_);
lean_dec_ref(v_a_1784_);
lean_dec(v_a_1783_);
lean_dec_ref(v_a_1782_);
lean_dec(v_a_1781_);
lean_dec_ref(v_a_1780_);
lean_dec_ref(v_hyps_1779_);
return v_res_1787_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_prenexWithExists(lean_object* v_hyp_1800_, lean_object* v_cfg_1801_, lean_object* v_a_1802_, lean_object* v_a_1803_, lean_object* v_a_1804_, lean_object* v_a_1805_, lean_object* v_a_1806_, lean_object* v_a_1807_){
_start:
{
lean_object* v_config_1809_; lean_object* v_maxSteps_1810_; lean_object* v_type_1811_; lean_object* v___x_1812_; lean_object* v_cfg_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; 
v_config_1809_ = lean_ctor_get(v_cfg_1801_, 5);
v_maxSteps_1810_ = lean_ctor_get(v_config_1809_, 1);
v_type_1811_ = lean_ctor_get(v_hyp_1800_, 1);
v___x_1812_ = lean_unsigned_to_nat(2u);
lean_inc(v_maxSteps_1810_);
v_cfg_1813_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_cfg_1813_, 0, v_maxSteps_1810_);
lean_ctor_set(v_cfg_1813_, 1, v___x_1812_);
v___x_1814_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_prenexWithExists___closed__1));
lean_inc_ref(v_type_1811_);
v___x_1815_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Simp_simp___boxed), 11, 1);
lean_closure_set(v___x_1815_, 0, v_type_1811_);
lean_inc_ref(v_cfg_1813_);
v___x_1816_ = l_Lean_Meta_Sym_Simp_SimpM_run_x27___redArg(v___x_1815_, v___x_1814_, v_cfg_1813_, v_a_1802_, v_a_1803_, v_a_1804_, v_a_1805_, v_a_1806_, v_a_1807_);
if (lean_obj_tag(v___x_1816_) == 0)
{
lean_object* v_a_1817_; lean_object* v___x_1818_; 
v_a_1817_ = lean_ctor_get(v___x_1816_, 0);
lean_inc(v_a_1817_);
lean_dec_ref_known(v___x_1816_, 1);
v___x_1818_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult___redArg(v_hyp_1800_, v_a_1817_, v_a_1803_, v_a_1804_, v_a_1805_, v_a_1806_, v_a_1807_);
if (lean_obj_tag(v___x_1818_) == 0)
{
lean_object* v_a_1819_; lean_object* v_type_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; 
v_a_1819_ = lean_ctor_get(v___x_1818_, 0);
lean_inc(v_a_1819_);
lean_dec_ref_known(v___x_1818_, 1);
v_type_1820_ = lean_ctor_get(v_a_1819_, 1);
v___x_1821_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_prenexWithExists___closed__3));
lean_inc_ref(v_type_1820_);
v___x_1822_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Simp_simp___boxed), 11, 1);
lean_closure_set(v___x_1822_, 0, v_type_1820_);
lean_inc_ref(v_cfg_1813_);
v___x_1823_ = l_Lean_Meta_Sym_Simp_SimpM_run_x27___redArg(v___x_1822_, v___x_1821_, v_cfg_1813_, v_a_1802_, v_a_1803_, v_a_1804_, v_a_1805_, v_a_1806_, v_a_1807_);
if (lean_obj_tag(v___x_1823_) == 0)
{
lean_object* v_a_1824_; lean_object* v___x_1825_; 
v_a_1824_ = lean_ctor_get(v___x_1823_, 0);
lean_inc(v_a_1824_);
lean_dec_ref_known(v___x_1823_, 1);
v___x_1825_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult___redArg(v_a_1819_, v_a_1824_, v_a_1803_, v_a_1804_, v_a_1805_, v_a_1806_, v_a_1807_);
if (lean_obj_tag(v___x_1825_) == 0)
{
lean_object* v_a_1826_; lean_object* v_type_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; 
v_a_1826_ = lean_ctor_get(v___x_1825_, 0);
lean_inc(v_a_1826_);
lean_dec_ref_known(v___x_1825_, 1);
v_type_1827_ = lean_ctor_get(v_a_1826_, 1);
v___x_1828_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_prenexWithExists___closed__5));
lean_inc_ref(v_type_1827_);
v___x_1829_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Simp_simp___boxed), 11, 1);
lean_closure_set(v___x_1829_, 0, v_type_1827_);
v___x_1830_ = l_Lean_Meta_Sym_Simp_SimpM_run_x27___redArg(v___x_1829_, v___x_1828_, v_cfg_1813_, v_a_1802_, v_a_1803_, v_a_1804_, v_a_1805_, v_a_1806_, v_a_1807_);
if (lean_obj_tag(v___x_1830_) == 0)
{
lean_object* v_a_1831_; lean_object* v___x_1832_; 
v_a_1831_ = lean_ctor_get(v___x_1830_, 0);
lean_inc(v_a_1831_);
lean_dec_ref_known(v___x_1830_, 1);
v___x_1832_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult___redArg(v_a_1826_, v_a_1831_, v_a_1803_, v_a_1804_, v_a_1805_, v_a_1806_, v_a_1807_);
return v___x_1832_;
}
else
{
lean_object* v_a_1833_; lean_object* v___x_1835_; uint8_t v_isShared_1836_; uint8_t v_isSharedCheck_1840_; 
lean_dec(v_a_1826_);
v_a_1833_ = lean_ctor_get(v___x_1830_, 0);
v_isSharedCheck_1840_ = !lean_is_exclusive(v___x_1830_);
if (v_isSharedCheck_1840_ == 0)
{
v___x_1835_ = v___x_1830_;
v_isShared_1836_ = v_isSharedCheck_1840_;
goto v_resetjp_1834_;
}
else
{
lean_inc(v_a_1833_);
lean_dec(v___x_1830_);
v___x_1835_ = lean_box(0);
v_isShared_1836_ = v_isSharedCheck_1840_;
goto v_resetjp_1834_;
}
v_resetjp_1834_:
{
lean_object* v___x_1838_; 
if (v_isShared_1836_ == 0)
{
v___x_1838_ = v___x_1835_;
goto v_reusejp_1837_;
}
else
{
lean_object* v_reuseFailAlloc_1839_; 
v_reuseFailAlloc_1839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1839_, 0, v_a_1833_);
v___x_1838_ = v_reuseFailAlloc_1839_;
goto v_reusejp_1837_;
}
v_reusejp_1837_:
{
return v___x_1838_;
}
}
}
}
else
{
lean_dec_ref_known(v_cfg_1813_, 2);
return v___x_1825_;
}
}
else
{
lean_object* v_a_1841_; lean_object* v___x_1843_; uint8_t v_isShared_1844_; uint8_t v_isSharedCheck_1848_; 
lean_dec(v_a_1819_);
lean_dec_ref_known(v_cfg_1813_, 2);
v_a_1841_ = lean_ctor_get(v___x_1823_, 0);
v_isSharedCheck_1848_ = !lean_is_exclusive(v___x_1823_);
if (v_isSharedCheck_1848_ == 0)
{
v___x_1843_ = v___x_1823_;
v_isShared_1844_ = v_isSharedCheck_1848_;
goto v_resetjp_1842_;
}
else
{
lean_inc(v_a_1841_);
lean_dec(v___x_1823_);
v___x_1843_ = lean_box(0);
v_isShared_1844_ = v_isSharedCheck_1848_;
goto v_resetjp_1842_;
}
v_resetjp_1842_:
{
lean_object* v___x_1846_; 
if (v_isShared_1844_ == 0)
{
v___x_1846_ = v___x_1843_;
goto v_reusejp_1845_;
}
else
{
lean_object* v_reuseFailAlloc_1847_; 
v_reuseFailAlloc_1847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1847_, 0, v_a_1841_);
v___x_1846_ = v_reuseFailAlloc_1847_;
goto v_reusejp_1845_;
}
v_reusejp_1845_:
{
return v___x_1846_;
}
}
}
}
else
{
lean_dec_ref_known(v_cfg_1813_, 2);
return v___x_1818_;
}
}
else
{
lean_object* v_a_1849_; lean_object* v___x_1851_; uint8_t v_isShared_1852_; uint8_t v_isSharedCheck_1856_; 
lean_dec_ref_known(v_cfg_1813_, 2);
lean_dec_ref(v_hyp_1800_);
v_a_1849_ = lean_ctor_get(v___x_1816_, 0);
v_isSharedCheck_1856_ = !lean_is_exclusive(v___x_1816_);
if (v_isSharedCheck_1856_ == 0)
{
v___x_1851_ = v___x_1816_;
v_isShared_1852_ = v_isSharedCheck_1856_;
goto v_resetjp_1850_;
}
else
{
lean_inc(v_a_1849_);
lean_dec(v___x_1816_);
v___x_1851_ = lean_box(0);
v_isShared_1852_ = v_isSharedCheck_1856_;
goto v_resetjp_1850_;
}
v_resetjp_1850_:
{
lean_object* v___x_1854_; 
if (v_isShared_1852_ == 0)
{
v___x_1854_ = v___x_1851_;
goto v_reusejp_1853_;
}
else
{
lean_object* v_reuseFailAlloc_1855_; 
v_reuseFailAlloc_1855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1855_, 0, v_a_1849_);
v___x_1854_ = v_reuseFailAlloc_1855_;
goto v_reusejp_1853_;
}
v_reusejp_1853_:
{
return v___x_1854_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_prenexWithExists___boxed(lean_object* v_hyp_1857_, lean_object* v_cfg_1858_, lean_object* v_a_1859_, lean_object* v_a_1860_, lean_object* v_a_1861_, lean_object* v_a_1862_, lean_object* v_a_1863_, lean_object* v_a_1864_, lean_object* v_a_1865_){
_start:
{
lean_object* v_res_1866_; 
v_res_1866_ = l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_prenexWithExists(v_hyp_1857_, v_cfg_1858_, v_a_1859_, v_a_1860_, v_a_1861_, v_a_1862_, v_a_1863_, v_a_1864_);
lean_dec(v_a_1864_);
lean_dec_ref(v_a_1863_);
lean_dec(v_a_1862_);
lean_dec_ref(v_a_1861_);
lean_dec(v_a_1860_);
lean_dec_ref(v_a_1859_);
lean_dec_ref(v_cfg_1858_);
return v_res_1866_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_prenexWithoutExists(lean_object* v_hyp_1867_, lean_object* v_cfg_1868_, lean_object* v_a_1869_, lean_object* v_a_1870_, lean_object* v_a_1871_, lean_object* v_a_1872_, lean_object* v_a_1873_, lean_object* v_a_1874_){
_start:
{
lean_object* v_config_1876_; lean_object* v_maxSteps_1877_; lean_object* v_type_1878_; lean_object* v___x_1879_; lean_object* v_cfg_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; 
v_config_1876_ = lean_ctor_get(v_cfg_1868_, 5);
v_maxSteps_1877_ = lean_ctor_get(v_config_1876_, 1);
v_type_1878_ = lean_ctor_get(v_hyp_1867_, 1);
v___x_1879_ = lean_unsigned_to_nat(2u);
lean_inc(v_maxSteps_1877_);
v_cfg_1880_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_cfg_1880_, 0, v_maxSteps_1877_);
lean_ctor_set(v_cfg_1880_, 1, v___x_1879_);
v___x_1881_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_prenexWithExists___closed__5));
lean_inc_ref(v_type_1878_);
v___x_1882_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Simp_simp___boxed), 11, 1);
lean_closure_set(v___x_1882_, 0, v_type_1878_);
v___x_1883_ = l_Lean_Meta_Sym_Simp_SimpM_run_x27___redArg(v___x_1882_, v___x_1881_, v_cfg_1880_, v_a_1869_, v_a_1870_, v_a_1871_, v_a_1872_, v_a_1873_, v_a_1874_);
if (lean_obj_tag(v___x_1883_) == 0)
{
lean_object* v_a_1884_; lean_object* v___x_1885_; 
v_a_1884_ = lean_ctor_get(v___x_1883_, 0);
lean_inc(v_a_1884_);
lean_dec_ref_known(v___x_1883_, 1);
v___x_1885_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult___redArg(v_hyp_1867_, v_a_1884_, v_a_1870_, v_a_1871_, v_a_1872_, v_a_1873_, v_a_1874_);
return v___x_1885_;
}
else
{
lean_object* v_a_1886_; lean_object* v___x_1888_; uint8_t v_isShared_1889_; uint8_t v_isSharedCheck_1893_; 
lean_dec_ref(v_hyp_1867_);
v_a_1886_ = lean_ctor_get(v___x_1883_, 0);
v_isSharedCheck_1893_ = !lean_is_exclusive(v___x_1883_);
if (v_isSharedCheck_1893_ == 0)
{
v___x_1888_ = v___x_1883_;
v_isShared_1889_ = v_isSharedCheck_1893_;
goto v_resetjp_1887_;
}
else
{
lean_inc(v_a_1886_);
lean_dec(v___x_1883_);
v___x_1888_ = lean_box(0);
v_isShared_1889_ = v_isSharedCheck_1893_;
goto v_resetjp_1887_;
}
v_resetjp_1887_:
{
lean_object* v___x_1891_; 
if (v_isShared_1889_ == 0)
{
v___x_1891_ = v___x_1888_;
goto v_reusejp_1890_;
}
else
{
lean_object* v_reuseFailAlloc_1892_; 
v_reuseFailAlloc_1892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1892_, 0, v_a_1886_);
v___x_1891_ = v_reuseFailAlloc_1892_;
goto v_reusejp_1890_;
}
v_reusejp_1890_:
{
return v___x_1891_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_prenexWithoutExists___boxed(lean_object* v_hyp_1894_, lean_object* v_cfg_1895_, lean_object* v_a_1896_, lean_object* v_a_1897_, lean_object* v_a_1898_, lean_object* v_a_1899_, lean_object* v_a_1900_, lean_object* v_a_1901_, lean_object* v_a_1902_){
_start:
{
lean_object* v_res_1903_; 
v_res_1903_ = l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_prenexWithoutExists(v_hyp_1894_, v_cfg_1895_, v_a_1896_, v_a_1897_, v_a_1898_, v_a_1899_, v_a_1900_, v_a_1901_);
lean_dec(v_a_1901_);
lean_dec_ref(v_a_1900_);
lean_dec(v_a_1899_);
lean_dec_ref(v_a_1898_);
lean_dec(v_a_1897_);
lean_dec_ref(v_a_1896_);
lean_dec_ref(v_cfg_1895_);
return v_res_1903_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_skolemize_skolemStep_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1904_; 
v___x_1904_ = l_Lean_Meta_Sym_instInhabitedSymM___redArg();
return v___x_1904_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_skolemize_skolemStep_spec__0(lean_object* v_msg_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_){
_start:
{
lean_object* v___x_1913_; lean_object* v___x_4390__overap_1914_; lean_object* v___x_1915_; 
v___x_1913_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_skolemize_skolemStep_spec__0___closed__0, &l_panic___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_skolemize_skolemStep_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_skolemize_skolemStep_spec__0___closed__0);
v___x_4390__overap_1914_ = lean_panic_fn_borrowed(v___x_1913_, v_msg_1905_);
lean_inc(v___y_1911_);
lean_inc_ref(v___y_1910_);
lean_inc(v___y_1909_);
lean_inc_ref(v___y_1908_);
lean_inc(v___y_1907_);
lean_inc_ref(v___y_1906_);
v___x_1915_ = lean_apply_7(v___x_4390__overap_1914_, v___y_1906_, v___y_1907_, v___y_1908_, v___y_1909_, v___y_1910_, v___y_1911_, lean_box(0));
return v___x_1915_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_skolemize_skolemStep_spec__0___boxed(lean_object* v_msg_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_){
_start:
{
lean_object* v_res_1924_; 
v_res_1924_ = l_panic___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_skolemize_skolemStep_spec__0(v_msg_1916_, v___y_1917_, v___y_1918_, v___y_1919_, v___y_1920_, v___y_1921_, v___y_1922_);
lean_dec(v___y_1922_);
lean_dec_ref(v___y_1921_);
lean_dec(v___y_1920_);
lean_dec_ref(v___y_1919_);
lean_dec(v___y_1918_);
lean_dec_ref(v___y_1917_);
return v_res_1924_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_skolemize_skolemStep___lam__0(lean_object* v_x_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_){
_start:
{
lean_object* v___x_1933_; lean_object* v___x_1934_; 
v___x_1933_ = lean_box(0);
v___x_1934_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1934_, 0, v___x_1933_);
return v___x_1934_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_skolemize_skolemStep___lam__0___boxed(lean_object* v_x_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_){
_start:
{
lean_object* v_res_1943_; 
v_res_1943_ = l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_skolemize_skolemStep___lam__0(v_x_1935_, v___y_1936_, v___y_1937_, v___y_1938_, v___y_1939_, v___y_1940_, v___y_1941_);
lean_dec(v___y_1941_);
lean_dec_ref(v___y_1940_);
lean_dec(v___y_1939_);
lean_dec_ref(v___y_1938_);
lean_dec(v___y_1937_);
lean_dec_ref(v___y_1936_);
return v_res_1943_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_skolemize_skolemStep___lam__1(lean_object* v___x_1944_, lean_object* v_name_1945_, lean_object* v_source_1946_, lean_object* v_mvarId_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_){
_start:
{
lean_object* v___x_1955_; 
lean_inc(v___x_1944_);
v___x_1955_ = l_Lean_FVarId_getType___redArg(v___x_1944_, v___y_1950_, v___y_1952_, v___y_1953_);
if (lean_obj_tag(v___x_1955_) == 0)
{
lean_object* v_a_1956_; lean_object* v___x_1958_; uint8_t v_isShared_1959_; uint8_t v_isSharedCheck_1967_; 
v_a_1956_ = lean_ctor_get(v___x_1955_, 0);
v_isSharedCheck_1967_ = !lean_is_exclusive(v___x_1955_);
if (v_isSharedCheck_1967_ == 0)
{
v___x_1958_ = v___x_1955_;
v_isShared_1959_ = v_isSharedCheck_1967_;
goto v_resetjp_1957_;
}
else
{
lean_inc(v_a_1956_);
lean_dec(v___x_1955_);
v___x_1958_ = lean_box(0);
v_isShared_1959_ = v_isSharedCheck_1967_;
goto v_resetjp_1957_;
}
v_resetjp_1957_:
{
lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1965_; 
v___x_1960_ = l_Lean_mkFVar(v___x_1944_);
v___x_1961_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1961_, 0, v_name_1945_);
lean_ctor_set(v___x_1961_, 1, v_a_1956_);
lean_ctor_set(v___x_1961_, 2, v___x_1960_);
lean_ctor_set(v___x_1961_, 3, v_source_1946_);
v___x_1962_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1962_, 0, v_mvarId_1947_);
lean_ctor_set(v___x_1962_, 1, v___x_1961_);
v___x_1963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1963_, 0, v___x_1962_);
if (v_isShared_1959_ == 0)
{
lean_ctor_set(v___x_1958_, 0, v___x_1963_);
v___x_1965_ = v___x_1958_;
goto v_reusejp_1964_;
}
else
{
lean_object* v_reuseFailAlloc_1966_; 
v_reuseFailAlloc_1966_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1966_, 0, v___x_1963_);
v___x_1965_ = v_reuseFailAlloc_1966_;
goto v_reusejp_1964_;
}
v_reusejp_1964_:
{
return v___x_1965_;
}
}
}
else
{
lean_object* v_a_1968_; lean_object* v___x_1970_; uint8_t v_isShared_1971_; uint8_t v_isSharedCheck_1975_; 
lean_dec(v_mvarId_1947_);
lean_dec(v_source_1946_);
lean_dec(v_name_1945_);
lean_dec(v___x_1944_);
v_a_1968_ = lean_ctor_get(v___x_1955_, 0);
v_isSharedCheck_1975_ = !lean_is_exclusive(v___x_1955_);
if (v_isSharedCheck_1975_ == 0)
{
v___x_1970_ = v___x_1955_;
v_isShared_1971_ = v_isSharedCheck_1975_;
goto v_resetjp_1969_;
}
else
{
lean_inc(v_a_1968_);
lean_dec(v___x_1955_);
v___x_1970_ = lean_box(0);
v_isShared_1971_ = v_isSharedCheck_1975_;
goto v_resetjp_1969_;
}
v_resetjp_1969_:
{
lean_object* v___x_1973_; 
if (v_isShared_1971_ == 0)
{
v___x_1973_ = v___x_1970_;
goto v_reusejp_1972_;
}
else
{
lean_object* v_reuseFailAlloc_1974_; 
v_reuseFailAlloc_1974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1974_, 0, v_a_1968_);
v___x_1973_ = v_reuseFailAlloc_1974_;
goto v_reusejp_1972_;
}
v_reusejp_1972_:
{
return v___x_1973_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_skolemize_skolemStep___lam__1___boxed(lean_object* v___x_1976_, lean_object* v_name_1977_, lean_object* v_source_1978_, lean_object* v_mvarId_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_){
_start:
{
lean_object* v_res_1987_; 
v_res_1987_ = l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_skolemize_skolemStep___lam__1(v___x_1976_, v_name_1977_, v_source_1978_, v_mvarId_1979_, v___y_1980_, v___y_1981_, v___y_1982_, v___y_1983_, v___y_1984_, v___y_1985_);
lean_dec(v___y_1985_);
lean_dec_ref(v___y_1984_);
lean_dec(v___y_1983_);
lean_dec_ref(v___y_1982_);
lean_dec(v___y_1981_);
lean_dec_ref(v___y_1980_);
return v_res_1987_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_skolemize_skolemStep___lam__2___closed__3(void){
_start:
{
lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; 
v___x_1991_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_skolemize_skolemStep___lam__2___closed__2));
v___x_1992_ = lean_unsigned_to_nat(30u);
v___x_1993_ = lean_unsigned_to_nat(126u);
v___x_1994_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_skolemize_skolemStep___lam__2___closed__1));
v___x_1995_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_skolemize_skolemStep___lam__2___closed__0));
v___x_1996_ = l_mkPanicMessageWithDecl(v___x_1995_, v___x_1994_, v___x_1993_, v___x_1992_, v___x_1991_);
return v___x_1996_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_skolemize_skolemStep___lam__2___closed__4(void){
_start:
{
lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; 
v___x_1997_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_skolemize_skolemStep___lam__2___closed__2));
v___x_1998_ = lean_unsigned_to_nat(54u);
v___x_1999_ = lean_unsigned_to_nat(127u);
v___x_2000_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_skolemize_skolemStep___lam__2___closed__1));
v___x_2001_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_skolemize_skolemStep___lam__2___closed__0));
v___x_2002_ = l_mkPanicMessageWithDecl(v___x_2001_, v___x_2000_, v___x_1999_, v___x_1998_, v___x_1997_);
return v___x_2002_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_skolemize_skolemStep___lam__2___closed__11(void){
_start:
{
lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; 
v___x_2013_ = lean_box(0);
v___x_2014_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_skolemize_skolemStep___lam__2___closed__10));
v___x_2015_ = l_Lean_mkConst(v___x_2014_, v___x_2013_);
return v___x_2015_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_skolemize_skolemStep___lam__2(uint8_t v___x_2016_, lean_object* v___f_2017_, lean_object* v___x_2018_, lean_object* v_value_2019_, lean_object* v_g_2020_, lean_object* v_name_2021_, lean_object* v_source_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_){
_start:
{
lean_object* v___y_2031_; lean_object* v___y_2032_; lean_object* v___y_2033_; lean_object* v___y_2034_; lean_object* v___y_2035_; lean_object* v___y_2036_; lean_object* v___y_2040_; lean_object* v___y_2041_; lean_object* v___y_2042_; lean_object* v___y_2043_; lean_object* v___y_2044_; lean_object* v___y_2045_; 
if (v___x_2016_ == 0)
{
lean_object* v___x_2048_; lean_object* v___x_2049_; 
lean_dec(v_source_2022_);
lean_dec(v_name_2021_);
lean_dec(v_g_2020_);
lean_dec_ref(v_value_2019_);
lean_dec_ref(v___x_2018_);
v___x_2048_ = lean_box(0);
lean_inc(v___y_2028_);
lean_inc_ref(v___y_2027_);
lean_inc(v___y_2026_);
lean_inc_ref(v___y_2025_);
lean_inc(v___y_2024_);
lean_inc_ref(v___y_2023_);
v___x_2049_ = lean_apply_8(v___f_2017_, v___x_2048_, v___y_2023_, v___y_2024_, v___y_2025_, v___y_2026_, v___y_2027_, v___y_2028_, lean_box(0));
return v___x_2049_;
}
else
{
lean_object* v___x_2050_; uint8_t v___x_2051_; 
v___x_2050_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2018_);
v___x_2051_ = l_Lean_Expr_isApp(v___x_2050_);
if (v___x_2051_ == 0)
{
lean_object* v___x_2052_; lean_object* v___x_2053_; 
lean_dec_ref(v___x_2050_);
lean_dec(v_source_2022_);
lean_dec(v_name_2021_);
lean_dec(v_g_2020_);
lean_dec_ref(v_value_2019_);
lean_dec_ref(v___x_2018_);
v___x_2052_ = lean_box(0);
lean_inc(v___y_2028_);
lean_inc_ref(v___y_2027_);
lean_inc(v___y_2026_);
lean_inc_ref(v___y_2025_);
lean_inc(v___y_2024_);
lean_inc_ref(v___y_2023_);
v___x_2053_ = lean_apply_8(v___f_2017_, v___x_2052_, v___y_2023_, v___y_2024_, v___y_2025_, v___y_2026_, v___y_2027_, v___y_2028_, lean_box(0));
return v___x_2053_;
}
else
{
lean_object* v___x_2054_; lean_object* v___x_2055_; uint8_t v___x_2056_; 
v___x_2054_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2050_);
v___x_2055_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_skolemize_skolemStep___lam__2___closed__6));
v___x_2056_ = l_Lean_Expr_isConstOf(v___x_2054_, v___x_2055_);
lean_dec_ref(v___x_2054_);
if (v___x_2056_ == 0)
{
lean_object* v___x_2057_; lean_object* v___x_2058_; 
lean_dec_ref(v___x_2050_);
lean_dec(v_source_2022_);
lean_dec(v_name_2021_);
lean_dec(v_g_2020_);
lean_dec_ref(v_value_2019_);
lean_dec_ref(v___x_2018_);
v___x_2057_ = lean_box(0);
lean_inc(v___y_2028_);
lean_inc_ref(v___y_2027_);
lean_inc(v___y_2026_);
lean_inc_ref(v___y_2025_);
lean_inc(v___y_2024_);
lean_inc_ref(v___y_2023_);
v___x_2058_ = lean_apply_8(v___f_2017_, v___x_2057_, v___y_2023_, v___y_2024_, v___y_2025_, v___y_2026_, v___y_2027_, v___y_2028_, lean_box(0));
return v___x_2058_;
}
else
{
lean_object* v_arg_2059_; lean_object* v_arg_2060_; lean_object* v___x_2061_; 
lean_dec_ref(v___f_2017_);
v_arg_2059_ = lean_ctor_get(v___x_2018_, 1);
lean_inc_ref(v_arg_2059_);
lean_dec_ref(v___x_2018_);
v_arg_2060_ = lean_ctor_get(v___x_2050_, 1);
lean_inc_ref_n(v_arg_2060_, 2);
lean_dec_ref(v___x_2050_);
v___x_2061_ = l_Lean_Meta_Sym_getLevel___redArg(v_arg_2060_, v___y_2024_, v___y_2025_, v___y_2026_, v___y_2027_, v___y_2028_);
if (lean_obj_tag(v___x_2061_) == 0)
{
lean_object* v_a_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; 
v_a_2062_ = lean_ctor_get(v___x_2061_, 0);
lean_inc(v_a_2062_);
lean_dec_ref_known(v___x_2061_, 1);
v___x_2063_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_skolemize_skolemStep___lam__2___closed__8));
v___x_2064_ = lean_box(0);
v___x_2065_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2065_, 0, v_a_2062_);
lean_ctor_set(v___x_2065_, 1, v___x_2064_);
v___x_2066_ = l_Lean_mkConst(v___x_2063_, v___x_2065_);
v___x_2067_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_skolemize_skolemStep___lam__2___closed__11, &l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_skolemize_skolemStep___lam__2___closed__11_once, _init_l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_skolemize_skolemStep___lam__2___closed__11);
v___x_2068_ = l_Lean_mkApp4(v___x_2066_, v_arg_2060_, v_arg_2059_, v___x_2067_, v_value_2019_);
v___x_2069_ = lean_box(0);
v___x_2070_ = l_Lean_Meta_Sym_mkBackwardRuleFromExpr(v___x_2068_, v___x_2064_, v___x_2069_, v___y_2025_, v___y_2026_, v___y_2027_, v___y_2028_);
if (lean_obj_tag(v___x_2070_) == 0)
{
lean_object* v_a_2071_; lean_object* v___x_2072_; 
v_a_2071_ = lean_ctor_get(v___x_2070_, 0);
lean_inc(v_a_2071_);
lean_dec_ref_known(v___x_2070_, 1);
v___x_2072_ = l_Lean_Meta_Sym_BackwardRule_apply_x27(v_g_2020_, v_a_2071_, v___y_2023_, v___y_2024_, v___y_2025_, v___y_2026_, v___y_2027_, v___y_2028_);
if (lean_obj_tag(v___x_2072_) == 0)
{
lean_object* v_a_2073_; 
v_a_2073_ = lean_ctor_get(v___x_2072_, 0);
lean_inc(v_a_2073_);
lean_dec_ref_known(v___x_2072_, 1);
if (lean_obj_tag(v_a_2073_) == 1)
{
lean_object* v_tail_2074_; 
v_tail_2074_ = lean_ctor_get(v_a_2073_, 1);
if (lean_obj_tag(v_tail_2074_) == 0)
{
lean_object* v_head_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; 
v_head_2075_ = lean_ctor_get(v_a_2073_, 0);
lean_inc(v_head_2075_);
lean_dec_ref_known(v_a_2073_, 2);
v___x_2076_ = lean_unsigned_to_nat(2u);
v___x_2077_ = l_Lean_Meta_Sym_introN(v_head_2075_, v___x_2076_, v___x_2056_, v___y_2023_, v___y_2024_, v___y_2025_, v___y_2026_, v___y_2027_, v___y_2028_);
if (lean_obj_tag(v___x_2077_) == 0)
{
lean_object* v_a_2078_; 
v_a_2078_ = lean_ctor_get(v___x_2077_, 0);
lean_inc(v_a_2078_);
lean_dec_ref_known(v___x_2077_, 1);
if (lean_obj_tag(v_a_2078_) == 1)
{
lean_object* v_newDecls_2079_; lean_object* v_mvarId_2080_; lean_object* v___x_2081_; uint8_t v___x_2082_; 
v_newDecls_2079_ = lean_ctor_get(v_a_2078_, 0);
lean_inc_ref(v_newDecls_2079_);
v_mvarId_2080_ = lean_ctor_get(v_a_2078_, 1);
lean_inc(v_mvarId_2080_);
lean_dec_ref_known(v_a_2078_, 2);
v___x_2081_ = lean_array_get_size(v_newDecls_2079_);
v___x_2082_ = lean_nat_dec_eq(v___x_2081_, v___x_2076_);
if (v___x_2082_ == 0)
{
lean_dec(v_mvarId_2080_);
lean_dec_ref(v_newDecls_2079_);
lean_dec(v_source_2022_);
lean_dec(v_name_2021_);
v___y_2040_ = v___y_2023_;
v___y_2041_ = v___y_2024_;
v___y_2042_ = v___y_2025_;
v___y_2043_ = v___y_2026_;
v___y_2044_ = v___y_2027_;
v___y_2045_ = v___y_2028_;
goto v___jp_2039_;
}
else
{
lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___f_2085_; lean_object* v___x_2086_; 
v___x_2083_ = lean_unsigned_to_nat(1u);
v___x_2084_ = lean_array_fget(v_newDecls_2079_, v___x_2083_);
lean_dec_ref(v_newDecls_2079_);
lean_inc(v_mvarId_2080_);
v___f_2085_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_skolemize_skolemStep___lam__1___boxed), 11, 4);
lean_closure_set(v___f_2085_, 0, v___x_2084_);
lean_closure_set(v___f_2085_, 1, v_name_2021_);
lean_closure_set(v___f_2085_, 2, v_source_2022_);
lean_closure_set(v___f_2085_, 3, v_mvarId_2080_);
v___x_2086_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__8___redArg(v_mvarId_2080_, v___f_2085_, v___y_2023_, v___y_2024_, v___y_2025_, v___y_2026_, v___y_2027_, v___y_2028_);
return v___x_2086_;
}
}
else
{
lean_dec(v_a_2078_);
lean_dec(v_source_2022_);
lean_dec(v_name_2021_);
v___y_2040_ = v___y_2023_;
v___y_2041_ = v___y_2024_;
v___y_2042_ = v___y_2025_;
v___y_2043_ = v___y_2026_;
v___y_2044_ = v___y_2027_;
v___y_2045_ = v___y_2028_;
goto v___jp_2039_;
}
}
else
{
lean_object* v_a_2087_; lean_object* v___x_2089_; uint8_t v_isShared_2090_; uint8_t v_isSharedCheck_2094_; 
lean_dec(v_source_2022_);
lean_dec(v_name_2021_);
v_a_2087_ = lean_ctor_get(v___x_2077_, 0);
v_isSharedCheck_2094_ = !lean_is_exclusive(v___x_2077_);
if (v_isSharedCheck_2094_ == 0)
{
v___x_2089_ = v___x_2077_;
v_isShared_2090_ = v_isSharedCheck_2094_;
goto v_resetjp_2088_;
}
else
{
lean_inc(v_a_2087_);
lean_dec(v___x_2077_);
v___x_2089_ = lean_box(0);
v_isShared_2090_ = v_isSharedCheck_2094_;
goto v_resetjp_2088_;
}
v_resetjp_2088_:
{
lean_object* v___x_2092_; 
if (v_isShared_2090_ == 0)
{
v___x_2092_ = v___x_2089_;
goto v_reusejp_2091_;
}
else
{
lean_object* v_reuseFailAlloc_2093_; 
v_reuseFailAlloc_2093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2093_, 0, v_a_2087_);
v___x_2092_ = v_reuseFailAlloc_2093_;
goto v_reusejp_2091_;
}
v_reusejp_2091_:
{
return v___x_2092_;
}
}
}
}
else
{
lean_dec_ref_known(v_a_2073_, 2);
lean_dec(v_source_2022_);
lean_dec(v_name_2021_);
v___y_2031_ = v___y_2023_;
v___y_2032_ = v___y_2024_;
v___y_2033_ = v___y_2025_;
v___y_2034_ = v___y_2026_;
v___y_2035_ = v___y_2027_;
v___y_2036_ = v___y_2028_;
goto v___jp_2030_;
}
}
else
{
lean_dec(v_a_2073_);
lean_dec(v_source_2022_);
lean_dec(v_name_2021_);
v___y_2031_ = v___y_2023_;
v___y_2032_ = v___y_2024_;
v___y_2033_ = v___y_2025_;
v___y_2034_ = v___y_2026_;
v___y_2035_ = v___y_2027_;
v___y_2036_ = v___y_2028_;
goto v___jp_2030_;
}
}
else
{
lean_object* v_a_2095_; lean_object* v___x_2097_; uint8_t v_isShared_2098_; uint8_t v_isSharedCheck_2102_; 
lean_dec(v_source_2022_);
lean_dec(v_name_2021_);
v_a_2095_ = lean_ctor_get(v___x_2072_, 0);
v_isSharedCheck_2102_ = !lean_is_exclusive(v___x_2072_);
if (v_isSharedCheck_2102_ == 0)
{
v___x_2097_ = v___x_2072_;
v_isShared_2098_ = v_isSharedCheck_2102_;
goto v_resetjp_2096_;
}
else
{
lean_inc(v_a_2095_);
lean_dec(v___x_2072_);
v___x_2097_ = lean_box(0);
v_isShared_2098_ = v_isSharedCheck_2102_;
goto v_resetjp_2096_;
}
v_resetjp_2096_:
{
lean_object* v___x_2100_; 
if (v_isShared_2098_ == 0)
{
v___x_2100_ = v___x_2097_;
goto v_reusejp_2099_;
}
else
{
lean_object* v_reuseFailAlloc_2101_; 
v_reuseFailAlloc_2101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2101_, 0, v_a_2095_);
v___x_2100_ = v_reuseFailAlloc_2101_;
goto v_reusejp_2099_;
}
v_reusejp_2099_:
{
return v___x_2100_;
}
}
}
}
else
{
lean_object* v_a_2103_; lean_object* v___x_2105_; uint8_t v_isShared_2106_; uint8_t v_isSharedCheck_2110_; 
lean_dec(v_source_2022_);
lean_dec(v_name_2021_);
lean_dec(v_g_2020_);
v_a_2103_ = lean_ctor_get(v___x_2070_, 0);
v_isSharedCheck_2110_ = !lean_is_exclusive(v___x_2070_);
if (v_isSharedCheck_2110_ == 0)
{
v___x_2105_ = v___x_2070_;
v_isShared_2106_ = v_isSharedCheck_2110_;
goto v_resetjp_2104_;
}
else
{
lean_inc(v_a_2103_);
lean_dec(v___x_2070_);
v___x_2105_ = lean_box(0);
v_isShared_2106_ = v_isSharedCheck_2110_;
goto v_resetjp_2104_;
}
v_resetjp_2104_:
{
lean_object* v___x_2108_; 
if (v_isShared_2106_ == 0)
{
v___x_2108_ = v___x_2105_;
goto v_reusejp_2107_;
}
else
{
lean_object* v_reuseFailAlloc_2109_; 
v_reuseFailAlloc_2109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2109_, 0, v_a_2103_);
v___x_2108_ = v_reuseFailAlloc_2109_;
goto v_reusejp_2107_;
}
v_reusejp_2107_:
{
return v___x_2108_;
}
}
}
}
else
{
lean_object* v_a_2111_; lean_object* v___x_2113_; uint8_t v_isShared_2114_; uint8_t v_isSharedCheck_2118_; 
lean_dec_ref(v_arg_2060_);
lean_dec_ref(v_arg_2059_);
lean_dec(v_source_2022_);
lean_dec(v_name_2021_);
lean_dec(v_g_2020_);
lean_dec_ref(v_value_2019_);
v_a_2111_ = lean_ctor_get(v___x_2061_, 0);
v_isSharedCheck_2118_ = !lean_is_exclusive(v___x_2061_);
if (v_isSharedCheck_2118_ == 0)
{
v___x_2113_ = v___x_2061_;
v_isShared_2114_ = v_isSharedCheck_2118_;
goto v_resetjp_2112_;
}
else
{
lean_inc(v_a_2111_);
lean_dec(v___x_2061_);
v___x_2113_ = lean_box(0);
v_isShared_2114_ = v_isSharedCheck_2118_;
goto v_resetjp_2112_;
}
v_resetjp_2112_:
{
lean_object* v___x_2116_; 
if (v_isShared_2114_ == 0)
{
v___x_2116_ = v___x_2113_;
goto v_reusejp_2115_;
}
else
{
lean_object* v_reuseFailAlloc_2117_; 
v_reuseFailAlloc_2117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2117_, 0, v_a_2111_);
v___x_2116_ = v_reuseFailAlloc_2117_;
goto v_reusejp_2115_;
}
v_reusejp_2115_:
{
return v___x_2116_;
}
}
}
}
}
}
v___jp_2030_:
{
lean_object* v___x_2037_; lean_object* v___x_2038_; 
v___x_2037_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_skolemize_skolemStep___lam__2___closed__3, &l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_skolemize_skolemStep___lam__2___closed__3_once, _init_l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_skolemize_skolemStep___lam__2___closed__3);
v___x_2038_ = l_panic___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_skolemize_skolemStep_spec__0(v___x_2037_, v___y_2031_, v___y_2032_, v___y_2033_, v___y_2034_, v___y_2035_, v___y_2036_);
return v___x_2038_;
}
v___jp_2039_:
{
lean_object* v___x_2046_; lean_object* v___x_2047_; 
v___x_2046_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_skolemize_skolemStep___lam__2___closed__4, &l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_skolemize_skolemStep___lam__2___closed__4_once, _init_l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_skolemize_skolemStep___lam__2___closed__4);
v___x_2047_ = l_panic___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_skolemize_skolemStep_spec__0(v___x_2046_, v___y_2040_, v___y_2041_, v___y_2042_, v___y_2043_, v___y_2044_, v___y_2045_);
return v___x_2047_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_skolemize_skolemStep___lam__2___boxed(lean_object* v___x_2119_, lean_object* v___f_2120_, lean_object* v___x_2121_, lean_object* v_value_2122_, lean_object* v_g_2123_, lean_object* v_name_2124_, lean_object* v_source_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_){
_start:
{
uint8_t v___x_4866__boxed_2133_; lean_object* v_res_2134_; 
v___x_4866__boxed_2133_ = lean_unbox(v___x_2119_);
v_res_2134_ = l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_skolemize_skolemStep___lam__2(v___x_4866__boxed_2133_, v___f_2120_, v___x_2121_, v_value_2122_, v_g_2123_, v_name_2124_, v_source_2125_, v___y_2126_, v___y_2127_, v___y_2128_, v___y_2129_, v___y_2130_, v___y_2131_);
lean_dec(v___y_2131_);
lean_dec_ref(v___y_2130_);
lean_dec(v___y_2129_);
lean_dec_ref(v___y_2128_);
lean_dec(v___y_2127_);
lean_dec_ref(v___y_2126_);
return v_res_2134_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_skolemize_skolemStep(lean_object* v_g_2136_, lean_object* v_hyp_2137_, lean_object* v_a_2138_, lean_object* v_a_2139_, lean_object* v_a_2140_, lean_object* v_a_2141_, lean_object* v_a_2142_, lean_object* v_a_2143_){
_start:
{
lean_object* v_name_2145_; lean_object* v_type_2146_; lean_object* v_value_2147_; lean_object* v_source_2148_; lean_object* v___f_2149_; lean_object* v___x_2150_; uint8_t v___x_2151_; lean_object* v___x_2152_; lean_object* v___y_2153_; lean_object* v___x_2154_; 
v_name_2145_ = lean_ctor_get(v_hyp_2137_, 0);
lean_inc(v_name_2145_);
v_type_2146_ = lean_ctor_get(v_hyp_2137_, 1);
lean_inc_ref(v_type_2146_);
v_value_2147_ = lean_ctor_get(v_hyp_2137_, 2);
lean_inc_ref(v_value_2147_);
v_source_2148_ = lean_ctor_get(v_hyp_2137_, 3);
lean_inc(v_source_2148_);
lean_dec_ref(v_hyp_2137_);
v___f_2149_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_skolemize_skolemStep___closed__0));
v___x_2150_ = l_Lean_Expr_cleanupAnnotations(v_type_2146_);
lean_dec_ref(v_type_2146_);
v___x_2151_ = l_Lean_Expr_isApp(v___x_2150_);
v___x_2152_ = lean_box(v___x_2151_);
lean_inc(v_g_2136_);
v___y_2153_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_skolemize_skolemStep___lam__2___boxed), 14, 7);
lean_closure_set(v___y_2153_, 0, v___x_2152_);
lean_closure_set(v___y_2153_, 1, v___f_2149_);
lean_closure_set(v___y_2153_, 2, v___x_2150_);
lean_closure_set(v___y_2153_, 3, v_value_2147_);
lean_closure_set(v___y_2153_, 4, v_g_2136_);
lean_closure_set(v___y_2153_, 5, v_name_2145_);
lean_closure_set(v___y_2153_, 6, v_source_2148_);
v___x_2154_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty_spec__8___redArg(v_g_2136_, v___y_2153_, v_a_2138_, v_a_2139_, v_a_2140_, v_a_2141_, v_a_2142_, v_a_2143_);
return v___x_2154_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_skolemize_skolemStep___boxed(lean_object* v_g_2155_, lean_object* v_hyp_2156_, lean_object* v_a_2157_, lean_object* v_a_2158_, lean_object* v_a_2159_, lean_object* v_a_2160_, lean_object* v_a_2161_, lean_object* v_a_2162_, lean_object* v_a_2163_){
_start:
{
lean_object* v_res_2164_; 
v_res_2164_ = l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_skolemize_skolemStep(v_g_2155_, v_hyp_2156_, v_a_2157_, v_a_2158_, v_a_2159_, v_a_2160_, v_a_2161_, v_a_2162_);
lean_dec(v_a_2162_);
lean_dec_ref(v_a_2161_);
lean_dec(v_a_2160_);
lean_dec_ref(v_a_2159_);
lean_dec(v_a_2158_);
lean_dec_ref(v_a_2157_);
return v_res_2164_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_skolemize_spec__0___redArg(lean_object* v_a_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_){
_start:
{
lean_object* v_fst_2173_; lean_object* v_snd_2174_; lean_object* v___x_2176_; uint8_t v_isShared_2177_; uint8_t v_isSharedCheck_2200_; 
v_fst_2173_ = lean_ctor_get(v_a_2165_, 0);
v_snd_2174_ = lean_ctor_get(v_a_2165_, 1);
v_isSharedCheck_2200_ = !lean_is_exclusive(v_a_2165_);
if (v_isSharedCheck_2200_ == 0)
{
v___x_2176_ = v_a_2165_;
v_isShared_2177_ = v_isSharedCheck_2200_;
goto v_resetjp_2175_;
}
else
{
lean_inc(v_snd_2174_);
lean_inc(v_fst_2173_);
lean_dec(v_a_2165_);
v___x_2176_ = lean_box(0);
v_isShared_2177_ = v_isSharedCheck_2200_;
goto v_resetjp_2175_;
}
v_resetjp_2175_:
{
lean_object* v___x_2178_; 
lean_inc(v_snd_2174_);
lean_inc(v_fst_2173_);
v___x_2178_ = l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_skolemize_skolemStep(v_fst_2173_, v_snd_2174_, v___y_2166_, v___y_2167_, v___y_2168_, v___y_2169_, v___y_2170_, v___y_2171_);
if (lean_obj_tag(v___x_2178_) == 0)
{
lean_object* v_a_2179_; lean_object* v___x_2181_; uint8_t v_isShared_2182_; uint8_t v_isSharedCheck_2191_; 
v_a_2179_ = lean_ctor_get(v___x_2178_, 0);
v_isSharedCheck_2191_ = !lean_is_exclusive(v___x_2178_);
if (v_isSharedCheck_2191_ == 0)
{
v___x_2181_ = v___x_2178_;
v_isShared_2182_ = v_isSharedCheck_2191_;
goto v_resetjp_2180_;
}
else
{
lean_inc(v_a_2179_);
lean_dec(v___x_2178_);
v___x_2181_ = lean_box(0);
v_isShared_2182_ = v_isSharedCheck_2191_;
goto v_resetjp_2180_;
}
v_resetjp_2180_:
{
if (lean_obj_tag(v_a_2179_) == 0)
{
lean_object* v___x_2184_; 
if (v_isShared_2177_ == 0)
{
v___x_2184_ = v___x_2176_;
goto v_reusejp_2183_;
}
else
{
lean_object* v_reuseFailAlloc_2188_; 
v_reuseFailAlloc_2188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2188_, 0, v_fst_2173_);
lean_ctor_set(v_reuseFailAlloc_2188_, 1, v_snd_2174_);
v___x_2184_ = v_reuseFailAlloc_2188_;
goto v_reusejp_2183_;
}
v_reusejp_2183_:
{
lean_object* v___x_2186_; 
if (v_isShared_2182_ == 0)
{
lean_ctor_set(v___x_2181_, 0, v___x_2184_);
v___x_2186_ = v___x_2181_;
goto v_reusejp_2185_;
}
else
{
lean_object* v_reuseFailAlloc_2187_; 
v_reuseFailAlloc_2187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2187_, 0, v___x_2184_);
v___x_2186_ = v_reuseFailAlloc_2187_;
goto v_reusejp_2185_;
}
v_reusejp_2185_:
{
return v___x_2186_;
}
}
}
else
{
lean_object* v_val_2189_; 
lean_del_object(v___x_2181_);
lean_del_object(v___x_2176_);
lean_dec(v_snd_2174_);
lean_dec(v_fst_2173_);
v_val_2189_ = lean_ctor_get(v_a_2179_, 0);
lean_inc(v_val_2189_);
lean_dec_ref_known(v_a_2179_, 1);
v_a_2165_ = v_val_2189_;
goto _start;
}
}
}
else
{
lean_object* v_a_2192_; lean_object* v___x_2194_; uint8_t v_isShared_2195_; uint8_t v_isSharedCheck_2199_; 
lean_del_object(v___x_2176_);
lean_dec(v_snd_2174_);
lean_dec(v_fst_2173_);
v_a_2192_ = lean_ctor_get(v___x_2178_, 0);
v_isSharedCheck_2199_ = !lean_is_exclusive(v___x_2178_);
if (v_isSharedCheck_2199_ == 0)
{
v___x_2194_ = v___x_2178_;
v_isShared_2195_ = v_isSharedCheck_2199_;
goto v_resetjp_2193_;
}
else
{
lean_inc(v_a_2192_);
lean_dec(v___x_2178_);
v___x_2194_ = lean_box(0);
v_isShared_2195_ = v_isSharedCheck_2199_;
goto v_resetjp_2193_;
}
v_resetjp_2193_:
{
lean_object* v___x_2197_; 
if (v_isShared_2195_ == 0)
{
v___x_2197_ = v___x_2194_;
goto v_reusejp_2196_;
}
else
{
lean_object* v_reuseFailAlloc_2198_; 
v_reuseFailAlloc_2198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2198_, 0, v_a_2192_);
v___x_2197_ = v_reuseFailAlloc_2198_;
goto v_reusejp_2196_;
}
v_reusejp_2196_:
{
return v___x_2197_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_skolemize_spec__0___redArg___boxed(lean_object* v_a_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_){
_start:
{
lean_object* v_res_2209_; 
v_res_2209_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_skolemize_spec__0___redArg(v_a_2201_, v___y_2202_, v___y_2203_, v___y_2204_, v___y_2205_, v___y_2206_, v___y_2207_);
lean_dec(v___y_2207_);
lean_dec_ref(v___y_2206_);
lean_dec(v___y_2205_);
lean_dec_ref(v___y_2204_);
lean_dec(v___y_2203_);
lean_dec_ref(v___y_2202_);
return v_res_2209_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_skolemize(lean_object* v_g_2210_, lean_object* v_hyp_2211_, lean_object* v_a_2212_, lean_object* v_a_2213_, lean_object* v_a_2214_, lean_object* v_a_2215_, lean_object* v_a_2216_, lean_object* v_a_2217_){
_start:
{
lean_object* v___x_2219_; lean_object* v___x_2220_; 
v___x_2219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2219_, 0, v_g_2210_);
lean_ctor_set(v___x_2219_, 1, v_hyp_2211_);
v___x_2220_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_skolemize_spec__0___redArg(v___x_2219_, v_a_2212_, v_a_2213_, v_a_2214_, v_a_2215_, v_a_2216_, v_a_2217_);
if (lean_obj_tag(v___x_2220_) == 0)
{
lean_object* v_a_2221_; lean_object* v___x_2223_; uint8_t v_isShared_2224_; uint8_t v_isSharedCheck_2237_; 
v_a_2221_ = lean_ctor_get(v___x_2220_, 0);
v_isSharedCheck_2237_ = !lean_is_exclusive(v___x_2220_);
if (v_isSharedCheck_2237_ == 0)
{
v___x_2223_ = v___x_2220_;
v_isShared_2224_ = v_isSharedCheck_2237_;
goto v_resetjp_2222_;
}
else
{
lean_inc(v_a_2221_);
lean_dec(v___x_2220_);
v___x_2223_ = lean_box(0);
v_isShared_2224_ = v_isSharedCheck_2237_;
goto v_resetjp_2222_;
}
v_resetjp_2222_:
{
lean_object* v_fst_2225_; lean_object* v_snd_2226_; lean_object* v___x_2228_; uint8_t v_isShared_2229_; uint8_t v_isSharedCheck_2236_; 
v_fst_2225_ = lean_ctor_get(v_a_2221_, 0);
v_snd_2226_ = lean_ctor_get(v_a_2221_, 1);
v_isSharedCheck_2236_ = !lean_is_exclusive(v_a_2221_);
if (v_isSharedCheck_2236_ == 0)
{
v___x_2228_ = v_a_2221_;
v_isShared_2229_ = v_isSharedCheck_2236_;
goto v_resetjp_2227_;
}
else
{
lean_inc(v_snd_2226_);
lean_inc(v_fst_2225_);
lean_dec(v_a_2221_);
v___x_2228_ = lean_box(0);
v_isShared_2229_ = v_isSharedCheck_2236_;
goto v_resetjp_2227_;
}
v_resetjp_2227_:
{
lean_object* v___x_2231_; 
if (v_isShared_2229_ == 0)
{
v___x_2231_ = v___x_2228_;
goto v_reusejp_2230_;
}
else
{
lean_object* v_reuseFailAlloc_2235_; 
v_reuseFailAlloc_2235_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2235_, 0, v_fst_2225_);
lean_ctor_set(v_reuseFailAlloc_2235_, 1, v_snd_2226_);
v___x_2231_ = v_reuseFailAlloc_2235_;
goto v_reusejp_2230_;
}
v_reusejp_2230_:
{
lean_object* v___x_2233_; 
if (v_isShared_2224_ == 0)
{
lean_ctor_set(v___x_2223_, 0, v___x_2231_);
v___x_2233_ = v___x_2223_;
goto v_reusejp_2232_;
}
else
{
lean_object* v_reuseFailAlloc_2234_; 
v_reuseFailAlloc_2234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2234_, 0, v___x_2231_);
v___x_2233_ = v_reuseFailAlloc_2234_;
goto v_reusejp_2232_;
}
v_reusejp_2232_:
{
return v___x_2233_;
}
}
}
}
}
else
{
return v___x_2220_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_skolemize___boxed(lean_object* v_g_2238_, lean_object* v_hyp_2239_, lean_object* v_a_2240_, lean_object* v_a_2241_, lean_object* v_a_2242_, lean_object* v_a_2243_, lean_object* v_a_2244_, lean_object* v_a_2245_, lean_object* v_a_2246_){
_start:
{
lean_object* v_res_2247_; 
v_res_2247_ = l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_skolemize(v_g_2238_, v_hyp_2239_, v_a_2240_, v_a_2241_, v_a_2242_, v_a_2243_, v_a_2244_, v_a_2245_);
lean_dec(v_a_2245_);
lean_dec_ref(v_a_2244_);
lean_dec(v_a_2243_);
lean_dec_ref(v_a_2242_);
lean_dec(v_a_2241_);
lean_dec_ref(v_a_2240_);
return v_res_2247_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_skolemize_spec__0(lean_object* v_inst_2248_, lean_object* v_a_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_){
_start:
{
lean_object* v___x_2257_; 
v___x_2257_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_skolemize_spec__0___redArg(v_a_2249_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_);
return v___x_2257_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_skolemize_spec__0___boxed(lean_object* v_inst_2258_, lean_object* v_a_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_){
_start:
{
lean_object* v_res_2267_; 
v_res_2267_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_skolemize_spec__0(v_inst_2258_, v_a_2259_, v___y_2260_, v___y_2261_, v___y_2262_, v___y_2263_, v___y_2264_, v___y_2265_);
lean_dec(v___y_2265_);
lean_dec_ref(v___y_2264_);
lean_dec(v___y_2263_);
lean_dec_ref(v___y_2262_);
lean_dec(v___y_2261_);
lean_dec_ref(v___y_2260_);
return v_res_2267_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_epr_spec__0___redArg___lam__0(lean_object* v_x_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_){
_start:
{
lean_object* v___x_2279_; 
lean_inc(v___y_2273_);
lean_inc_ref(v___y_2272_);
lean_inc(v___y_2271_);
lean_inc_ref(v___y_2270_);
lean_inc(v___y_2269_);
v___x_2279_ = lean_apply_10(v_x_2268_, v___y_2269_, v___y_2270_, v___y_2271_, v___y_2272_, v___y_2273_, v___y_2274_, v___y_2275_, v___y_2276_, v___y_2277_, lean_box(0));
return v___x_2279_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_epr_spec__0___redArg___lam__0___boxed(lean_object* v_x_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_){
_start:
{
lean_object* v_res_2291_; 
v_res_2291_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_epr_spec__0___redArg___lam__0(v_x_2280_, v___y_2281_, v___y_2282_, v___y_2283_, v___y_2284_, v___y_2285_, v___y_2286_, v___y_2287_, v___y_2288_, v___y_2289_);
lean_dec(v___y_2285_);
lean_dec_ref(v___y_2284_);
lean_dec(v___y_2283_);
lean_dec_ref(v___y_2282_);
lean_dec(v___y_2281_);
return v_res_2291_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_epr_spec__0___redArg(lean_object* v_mvarId_2292_, lean_object* v_x_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_){
_start:
{
lean_object* v___f_2304_; lean_object* v___x_2305_; 
lean_inc(v___y_2298_);
lean_inc_ref(v___y_2297_);
lean_inc(v___y_2296_);
lean_inc_ref(v___y_2295_);
lean_inc(v___y_2294_);
v___f_2304_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_epr_spec__0___redArg___lam__0___boxed), 11, 6);
lean_closure_set(v___f_2304_, 0, v_x_2293_);
lean_closure_set(v___f_2304_, 1, v___y_2294_);
lean_closure_set(v___f_2304_, 2, v___y_2295_);
lean_closure_set(v___f_2304_, 3, v___y_2296_);
lean_closure_set(v___f_2304_, 4, v___y_2297_);
lean_closure_set(v___f_2304_, 5, v___y_2298_);
v___x_2305_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_2292_, v___f_2304_, v___y_2299_, v___y_2300_, v___y_2301_, v___y_2302_);
if (lean_obj_tag(v___x_2305_) == 0)
{
return v___x_2305_;
}
else
{
lean_object* v_a_2306_; lean_object* v___x_2308_; uint8_t v_isShared_2309_; uint8_t v_isSharedCheck_2313_; 
v_a_2306_ = lean_ctor_get(v___x_2305_, 0);
v_isSharedCheck_2313_ = !lean_is_exclusive(v___x_2305_);
if (v_isSharedCheck_2313_ == 0)
{
v___x_2308_ = v___x_2305_;
v_isShared_2309_ = v_isSharedCheck_2313_;
goto v_resetjp_2307_;
}
else
{
lean_inc(v_a_2306_);
lean_dec(v___x_2305_);
v___x_2308_ = lean_box(0);
v_isShared_2309_ = v_isSharedCheck_2313_;
goto v_resetjp_2307_;
}
v_resetjp_2307_:
{
lean_object* v___x_2311_; 
if (v_isShared_2309_ == 0)
{
v___x_2311_ = v___x_2308_;
goto v_reusejp_2310_;
}
else
{
lean_object* v_reuseFailAlloc_2312_; 
v_reuseFailAlloc_2312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2312_, 0, v_a_2306_);
v___x_2311_ = v_reuseFailAlloc_2312_;
goto v_reusejp_2310_;
}
v_reusejp_2310_:
{
return v___x_2311_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_epr_spec__0___redArg___boxed(lean_object* v_mvarId_2314_, lean_object* v_x_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_){
_start:
{
lean_object* v_res_2326_; 
v_res_2326_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_epr_spec__0___redArg(v_mvarId_2314_, v_x_2315_, v___y_2316_, v___y_2317_, v___y_2318_, v___y_2319_, v___y_2320_, v___y_2321_, v___y_2322_, v___y_2323_, v___y_2324_);
lean_dec(v___y_2324_);
lean_dec_ref(v___y_2323_);
lean_dec(v___y_2322_);
lean_dec_ref(v___y_2321_);
lean_dec(v___y_2320_);
lean_dec_ref(v___y_2319_);
lean_dec(v___y_2318_);
lean_dec_ref(v___y_2317_);
lean_dec(v___y_2316_);
return v_res_2326_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_epr_spec__0(lean_object* v_00_u03b1_2327_, lean_object* v_mvarId_2328_, lean_object* v_x_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_){
_start:
{
lean_object* v___x_2340_; 
v___x_2340_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_epr_spec__0___redArg(v_mvarId_2328_, v_x_2329_, v___y_2330_, v___y_2331_, v___y_2332_, v___y_2333_, v___y_2334_, v___y_2335_, v___y_2336_, v___y_2337_, v___y_2338_);
return v___x_2340_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_epr_spec__0___boxed(lean_object* v_00_u03b1_2341_, lean_object* v_mvarId_2342_, lean_object* v_x_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_){
_start:
{
lean_object* v_res_2354_; 
v_res_2354_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_epr_spec__0(v_00_u03b1_2341_, v_mvarId_2342_, v_x_2343_, v___y_2344_, v___y_2345_, v___y_2346_, v___y_2347_, v___y_2348_, v___y_2349_, v___y_2350_, v___y_2351_, v___y_2352_);
lean_dec(v___y_2352_);
lean_dec_ref(v___y_2351_);
lean_dec(v___y_2350_);
lean_dec_ref(v___y_2349_);
lean_dec(v___y_2348_);
lean_dec_ref(v___y_2347_);
lean_dec(v___y_2346_);
lean_dec_ref(v___y_2345_);
lean_dec(v___y_2344_);
return v_res_2354_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_epr_spec__2___redArg(lean_object* v_mvarId_2355_, lean_object* v_x_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_){
_start:
{
lean_object* v___x_2362_; 
v___x_2362_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_2355_, v_x_2356_, v___y_2357_, v___y_2358_, v___y_2359_, v___y_2360_);
if (lean_obj_tag(v___x_2362_) == 0)
{
lean_object* v_a_2363_; lean_object* v___x_2365_; uint8_t v_isShared_2366_; uint8_t v_isSharedCheck_2370_; 
v_a_2363_ = lean_ctor_get(v___x_2362_, 0);
v_isSharedCheck_2370_ = !lean_is_exclusive(v___x_2362_);
if (v_isSharedCheck_2370_ == 0)
{
v___x_2365_ = v___x_2362_;
v_isShared_2366_ = v_isSharedCheck_2370_;
goto v_resetjp_2364_;
}
else
{
lean_inc(v_a_2363_);
lean_dec(v___x_2362_);
v___x_2365_ = lean_box(0);
v_isShared_2366_ = v_isSharedCheck_2370_;
goto v_resetjp_2364_;
}
v_resetjp_2364_:
{
lean_object* v___x_2368_; 
if (v_isShared_2366_ == 0)
{
v___x_2368_ = v___x_2365_;
goto v_reusejp_2367_;
}
else
{
lean_object* v_reuseFailAlloc_2369_; 
v_reuseFailAlloc_2369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2369_, 0, v_a_2363_);
v___x_2368_ = v_reuseFailAlloc_2369_;
goto v_reusejp_2367_;
}
v_reusejp_2367_:
{
return v___x_2368_;
}
}
}
else
{
lean_object* v_a_2371_; lean_object* v___x_2373_; uint8_t v_isShared_2374_; uint8_t v_isSharedCheck_2378_; 
v_a_2371_ = lean_ctor_get(v___x_2362_, 0);
v_isSharedCheck_2378_ = !lean_is_exclusive(v___x_2362_);
if (v_isSharedCheck_2378_ == 0)
{
v___x_2373_ = v___x_2362_;
v_isShared_2374_ = v_isSharedCheck_2378_;
goto v_resetjp_2372_;
}
else
{
lean_inc(v_a_2371_);
lean_dec(v___x_2362_);
v___x_2373_ = lean_box(0);
v_isShared_2374_ = v_isSharedCheck_2378_;
goto v_resetjp_2372_;
}
v_resetjp_2372_:
{
lean_object* v___x_2376_; 
if (v_isShared_2374_ == 0)
{
v___x_2376_ = v___x_2373_;
goto v_reusejp_2375_;
}
else
{
lean_object* v_reuseFailAlloc_2377_; 
v_reuseFailAlloc_2377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2377_, 0, v_a_2371_);
v___x_2376_ = v_reuseFailAlloc_2377_;
goto v_reusejp_2375_;
}
v_reusejp_2375_:
{
return v___x_2376_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_epr_spec__2___redArg___boxed(lean_object* v_mvarId_2379_, lean_object* v_x_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_){
_start:
{
lean_object* v_res_2386_; 
v_res_2386_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_epr_spec__2___redArg(v_mvarId_2379_, v_x_2380_, v___y_2381_, v___y_2382_, v___y_2383_, v___y_2384_);
lean_dec(v___y_2384_);
lean_dec_ref(v___y_2383_);
lean_dec(v___y_2382_);
lean_dec_ref(v___y_2381_);
return v_res_2386_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_epr_spec__2(lean_object* v_00_u03b1_2387_, lean_object* v_mvarId_2388_, lean_object* v_x_2389_, lean_object* v___y_2390_, lean_object* v___y_2391_, lean_object* v___y_2392_, lean_object* v___y_2393_){
_start:
{
lean_object* v___x_2395_; 
v___x_2395_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_epr_spec__2___redArg(v_mvarId_2388_, v_x_2389_, v___y_2390_, v___y_2391_, v___y_2392_, v___y_2393_);
return v___x_2395_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_epr_spec__2___boxed(lean_object* v_00_u03b1_2396_, lean_object* v_mvarId_2397_, lean_object* v_x_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_){
_start:
{
lean_object* v_res_2404_; 
v_res_2404_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_epr_spec__2(v_00_u03b1_2396_, v_mvarId_2397_, v_x_2398_, v___y_2399_, v___y_2400_, v___y_2401_, v___y_2402_);
lean_dec(v___y_2402_);
lean_dec_ref(v___y_2401_);
lean_dec(v___y_2400_);
lean_dec_ref(v___y_2399_);
return v_res_2404_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_epr_spec__1___lam__2(lean_object* v_a_2405_, lean_object* v_cfg_2406_, lean_object* v_snd_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_){
_start:
{
lean_object* v___x_2418_; 
v___x_2418_ = l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_prenexWithExists(v_a_2405_, v_cfg_2406_, v___y_2411_, v___y_2412_, v___y_2413_, v___y_2414_, v___y_2415_, v___y_2416_);
if (lean_obj_tag(v___x_2418_) == 0)
{
lean_object* v_a_2419_; lean_object* v___x_2420_; 
v_a_2419_ = lean_ctor_get(v___x_2418_, 0);
lean_inc(v_a_2419_);
lean_dec_ref_known(v___x_2418_, 1);
v___x_2420_ = l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_skolemize(v_snd_2407_, v_a_2419_, v___y_2411_, v___y_2412_, v___y_2413_, v___y_2414_, v___y_2415_, v___y_2416_);
return v___x_2420_;
}
else
{
lean_object* v_a_2421_; lean_object* v___x_2423_; uint8_t v_isShared_2424_; uint8_t v_isSharedCheck_2428_; 
lean_dec(v_snd_2407_);
v_a_2421_ = lean_ctor_get(v___x_2418_, 0);
v_isSharedCheck_2428_ = !lean_is_exclusive(v___x_2418_);
if (v_isSharedCheck_2428_ == 0)
{
v___x_2423_ = v___x_2418_;
v_isShared_2424_ = v_isSharedCheck_2428_;
goto v_resetjp_2422_;
}
else
{
lean_inc(v_a_2421_);
lean_dec(v___x_2418_);
v___x_2423_ = lean_box(0);
v_isShared_2424_ = v_isSharedCheck_2428_;
goto v_resetjp_2422_;
}
v_resetjp_2422_:
{
lean_object* v___x_2426_; 
if (v_isShared_2424_ == 0)
{
v___x_2426_ = v___x_2423_;
goto v_reusejp_2425_;
}
else
{
lean_object* v_reuseFailAlloc_2427_; 
v_reuseFailAlloc_2427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2427_, 0, v_a_2421_);
v___x_2426_ = v_reuseFailAlloc_2427_;
goto v_reusejp_2425_;
}
v_reusejp_2425_:
{
return v___x_2426_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_epr_spec__1___lam__2___boxed(lean_object* v_a_2429_, lean_object* v_cfg_2430_, lean_object* v_snd_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_, lean_object* v___y_2434_, lean_object* v___y_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_){
_start:
{
lean_object* v_res_2442_; 
v_res_2442_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_epr_spec__1___lam__2(v_a_2429_, v_cfg_2430_, v_snd_2431_, v___y_2432_, v___y_2433_, v___y_2434_, v___y_2435_, v___y_2436_, v___y_2437_, v___y_2438_, v___y_2439_, v___y_2440_);
lean_dec(v___y_2440_);
lean_dec_ref(v___y_2439_);
lean_dec(v___y_2438_);
lean_dec_ref(v___y_2437_);
lean_dec(v___y_2436_);
lean_dec_ref(v___y_2435_);
lean_dec(v___y_2434_);
lean_dec_ref(v___y_2433_);
lean_dec(v___y_2432_);
lean_dec_ref(v_cfg_2430_);
return v_res_2442_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_epr_spec__1___lam__0(lean_object* v_e_2443_){
_start:
{
lean_object* v___x_2444_; uint8_t v___x_2445_; 
v___x_2444_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_skolemize_skolemStep___lam__2___closed__6));
v___x_2445_ = l_Lean_Expr_isConstOf(v_e_2443_, v___x_2444_);
return v___x_2445_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_epr_spec__1___lam__0___boxed(lean_object* v_e_2446_){
_start:
{
uint8_t v_res_2447_; lean_object* v_r_2448_; 
v_res_2447_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_epr_spec__1___lam__0(v_e_2446_);
lean_dec_ref(v_e_2446_);
v_r_2448_ = lean_box(v_res_2447_);
return v_r_2448_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_epr_spec__1___lam__1(lean_object* v_a_2449_, lean_object* v_cfg_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_, lean_object* v___y_2459_){
_start:
{
lean_object* v___x_2461_; 
v___x_2461_ = l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_prenexWithoutExists(v_a_2449_, v_cfg_2450_, v___y_2454_, v___y_2455_, v___y_2456_, v___y_2457_, v___y_2458_, v___y_2459_);
return v___x_2461_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_epr_spec__1___lam__1___boxed(lean_object* v_a_2462_, lean_object* v_cfg_2463_, lean_object* v___y_2464_, lean_object* v___y_2465_, lean_object* v___y_2466_, lean_object* v___y_2467_, lean_object* v___y_2468_, lean_object* v___y_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_){
_start:
{
lean_object* v_res_2474_; 
v_res_2474_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_epr_spec__1___lam__1(v_a_2462_, v_cfg_2463_, v___y_2464_, v___y_2465_, v___y_2466_, v___y_2467_, v___y_2468_, v___y_2469_, v___y_2470_, v___y_2471_, v___y_2472_);
lean_dec(v___y_2472_);
lean_dec_ref(v___y_2471_);
lean_dec(v___y_2470_);
lean_dec_ref(v___y_2469_);
lean_dec(v___y_2468_);
lean_dec_ref(v___y_2467_);
lean_dec(v___y_2466_);
lean_dec_ref(v___y_2465_);
lean_dec(v___y_2464_);
lean_dec_ref(v_cfg_2463_);
return v_res_2474_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_epr_spec__1(lean_object* v_cfg_2476_, lean_object* v_as_2477_, size_t v_sz_2478_, size_t v_i_2479_, lean_object* v_b_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_){
_start:
{
lean_object* v_a_2492_; uint8_t v___x_2496_; 
v___x_2496_ = lean_usize_dec_lt(v_i_2479_, v_sz_2478_);
if (v___x_2496_ == 0)
{
lean_object* v___x_2497_; 
lean_dec_ref(v_cfg_2476_);
v___x_2497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2497_, 0, v_b_2480_);
return v___x_2497_;
}
else
{
lean_object* v_fst_2498_; lean_object* v_snd_2499_; lean_object* v___x_2501_; uint8_t v_isShared_2502_; uint8_t v_isSharedCheck_2543_; 
v_fst_2498_ = lean_ctor_get(v_b_2480_, 0);
v_snd_2499_ = lean_ctor_get(v_b_2480_, 1);
v_isSharedCheck_2543_ = !lean_is_exclusive(v_b_2480_);
if (v_isSharedCheck_2543_ == 0)
{
v___x_2501_ = v_b_2480_;
v_isShared_2502_ = v_isSharedCheck_2543_;
goto v_resetjp_2500_;
}
else
{
lean_inc(v_snd_2499_);
lean_inc(v_fst_2498_);
lean_dec(v_b_2480_);
v___x_2501_ = lean_box(0);
v_isShared_2502_ = v_isSharedCheck_2543_;
goto v_resetjp_2500_;
}
v_resetjp_2500_:
{
lean_object* v_a_2503_; lean_object* v_type_2504_; lean_object* v___f_2505_; lean_object* v___x_2506_; 
v_a_2503_ = lean_array_uget_borrowed(v_as_2477_, v_i_2479_);
v_type_2504_ = lean_ctor_get(v_a_2503_, 1);
v___f_2505_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_epr_spec__1___closed__0));
v___x_2506_ = lean_find_expr(v___f_2505_, v_type_2504_);
if (lean_obj_tag(v___x_2506_) == 0)
{
lean_object* v___f_2507_; lean_object* v___x_2508_; 
lean_inc_ref(v_cfg_2476_);
lean_inc(v_a_2503_);
v___f_2507_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_epr_spec__1___lam__1___boxed), 12, 2);
lean_closure_set(v___f_2507_, 0, v_a_2503_);
lean_closure_set(v___f_2507_, 1, v_cfg_2476_);
lean_inc(v_snd_2499_);
v___x_2508_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_epr_spec__0___redArg(v_snd_2499_, v___f_2507_, v___y_2481_, v___y_2482_, v___y_2483_, v___y_2484_, v___y_2485_, v___y_2486_, v___y_2487_, v___y_2488_, v___y_2489_);
if (lean_obj_tag(v___x_2508_) == 0)
{
lean_object* v_a_2509_; lean_object* v___x_2510_; lean_object* v___x_2512_; 
v_a_2509_ = lean_ctor_get(v___x_2508_, 0);
lean_inc(v_a_2509_);
lean_dec_ref_known(v___x_2508_, 1);
v___x_2510_ = lean_array_push(v_fst_2498_, v_a_2509_);
if (v_isShared_2502_ == 0)
{
lean_ctor_set(v___x_2501_, 0, v___x_2510_);
v___x_2512_ = v___x_2501_;
goto v_reusejp_2511_;
}
else
{
lean_object* v_reuseFailAlloc_2513_; 
v_reuseFailAlloc_2513_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2513_, 0, v___x_2510_);
lean_ctor_set(v_reuseFailAlloc_2513_, 1, v_snd_2499_);
v___x_2512_ = v_reuseFailAlloc_2513_;
goto v_reusejp_2511_;
}
v_reusejp_2511_:
{
v_a_2492_ = v___x_2512_;
goto v___jp_2491_;
}
}
else
{
lean_object* v_a_2514_; lean_object* v___x_2516_; uint8_t v_isShared_2517_; uint8_t v_isSharedCheck_2521_; 
lean_del_object(v___x_2501_);
lean_dec(v_snd_2499_);
lean_dec(v_fst_2498_);
lean_dec_ref(v_cfg_2476_);
v_a_2514_ = lean_ctor_get(v___x_2508_, 0);
v_isSharedCheck_2521_ = !lean_is_exclusive(v___x_2508_);
if (v_isSharedCheck_2521_ == 0)
{
v___x_2516_ = v___x_2508_;
v_isShared_2517_ = v_isSharedCheck_2521_;
goto v_resetjp_2515_;
}
else
{
lean_inc(v_a_2514_);
lean_dec(v___x_2508_);
v___x_2516_ = lean_box(0);
v_isShared_2517_ = v_isSharedCheck_2521_;
goto v_resetjp_2515_;
}
v_resetjp_2515_:
{
lean_object* v___x_2519_; 
if (v_isShared_2517_ == 0)
{
v___x_2519_ = v___x_2516_;
goto v_reusejp_2518_;
}
else
{
lean_object* v_reuseFailAlloc_2520_; 
v_reuseFailAlloc_2520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2520_, 0, v_a_2514_);
v___x_2519_ = v_reuseFailAlloc_2520_;
goto v_reusejp_2518_;
}
v_reusejp_2518_:
{
return v___x_2519_;
}
}
}
}
else
{
lean_object* v___f_2522_; lean_object* v___x_2523_; 
lean_dec_ref_known(v___x_2506_, 1);
lean_del_object(v___x_2501_);
lean_inc(v_snd_2499_);
lean_inc_ref(v_cfg_2476_);
lean_inc(v_a_2503_);
v___f_2522_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_epr_spec__1___lam__2___boxed), 13, 3);
lean_closure_set(v___f_2522_, 0, v_a_2503_);
lean_closure_set(v___f_2522_, 1, v_cfg_2476_);
lean_closure_set(v___f_2522_, 2, v_snd_2499_);
v___x_2523_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_epr_spec__0___redArg(v_snd_2499_, v___f_2522_, v___y_2481_, v___y_2482_, v___y_2483_, v___y_2484_, v___y_2485_, v___y_2486_, v___y_2487_, v___y_2488_, v___y_2489_);
if (lean_obj_tag(v___x_2523_) == 0)
{
lean_object* v_a_2524_; lean_object* v_fst_2525_; lean_object* v_snd_2526_; lean_object* v___x_2528_; uint8_t v_isShared_2529_; uint8_t v_isSharedCheck_2534_; 
v_a_2524_ = lean_ctor_get(v___x_2523_, 0);
lean_inc(v_a_2524_);
lean_dec_ref_known(v___x_2523_, 1);
v_fst_2525_ = lean_ctor_get(v_a_2524_, 0);
v_snd_2526_ = lean_ctor_get(v_a_2524_, 1);
v_isSharedCheck_2534_ = !lean_is_exclusive(v_a_2524_);
if (v_isSharedCheck_2534_ == 0)
{
v___x_2528_ = v_a_2524_;
v_isShared_2529_ = v_isSharedCheck_2534_;
goto v_resetjp_2527_;
}
else
{
lean_inc(v_snd_2526_);
lean_inc(v_fst_2525_);
lean_dec(v_a_2524_);
v___x_2528_ = lean_box(0);
v_isShared_2529_ = v_isSharedCheck_2534_;
goto v_resetjp_2527_;
}
v_resetjp_2527_:
{
lean_object* v___x_2530_; lean_object* v___x_2532_; 
v___x_2530_ = lean_array_push(v_fst_2498_, v_snd_2526_);
if (v_isShared_2529_ == 0)
{
lean_ctor_set(v___x_2528_, 1, v_fst_2525_);
lean_ctor_set(v___x_2528_, 0, v___x_2530_);
v___x_2532_ = v___x_2528_;
goto v_reusejp_2531_;
}
else
{
lean_object* v_reuseFailAlloc_2533_; 
v_reuseFailAlloc_2533_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2533_, 0, v___x_2530_);
lean_ctor_set(v_reuseFailAlloc_2533_, 1, v_fst_2525_);
v___x_2532_ = v_reuseFailAlloc_2533_;
goto v_reusejp_2531_;
}
v_reusejp_2531_:
{
v_a_2492_ = v___x_2532_;
goto v___jp_2491_;
}
}
}
else
{
lean_object* v_a_2535_; lean_object* v___x_2537_; uint8_t v_isShared_2538_; uint8_t v_isSharedCheck_2542_; 
lean_dec(v_fst_2498_);
lean_dec_ref(v_cfg_2476_);
v_a_2535_ = lean_ctor_get(v___x_2523_, 0);
v_isSharedCheck_2542_ = !lean_is_exclusive(v___x_2523_);
if (v_isSharedCheck_2542_ == 0)
{
v___x_2537_ = v___x_2523_;
v_isShared_2538_ = v_isSharedCheck_2542_;
goto v_resetjp_2536_;
}
else
{
lean_inc(v_a_2535_);
lean_dec(v___x_2523_);
v___x_2537_ = lean_box(0);
v_isShared_2538_ = v_isSharedCheck_2542_;
goto v_resetjp_2536_;
}
v_resetjp_2536_:
{
lean_object* v___x_2540_; 
if (v_isShared_2538_ == 0)
{
v___x_2540_ = v___x_2537_;
goto v_reusejp_2539_;
}
else
{
lean_object* v_reuseFailAlloc_2541_; 
v_reuseFailAlloc_2541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2541_, 0, v_a_2535_);
v___x_2540_ = v_reuseFailAlloc_2541_;
goto v_reusejp_2539_;
}
v_reusejp_2539_:
{
return v___x_2540_;
}
}
}
}
}
}
v___jp_2491_:
{
size_t v___x_2493_; size_t v___x_2494_; 
v___x_2493_ = ((size_t)1ULL);
v___x_2494_ = lean_usize_add(v_i_2479_, v___x_2493_);
v_i_2479_ = v___x_2494_;
v_b_2480_ = v_a_2492_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_epr_spec__1___boxed(lean_object* v_cfg_2544_, lean_object* v_as_2545_, lean_object* v_sz_2546_, lean_object* v_i_2547_, lean_object* v_b_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_, lean_object* v___y_2552_, lean_object* v___y_2553_, lean_object* v___y_2554_, lean_object* v___y_2555_, lean_object* v___y_2556_, lean_object* v___y_2557_, lean_object* v___y_2558_){
_start:
{
size_t v_sz_boxed_2559_; size_t v_i_boxed_2560_; lean_object* v_res_2561_; 
v_sz_boxed_2559_ = lean_unbox_usize(v_sz_2546_);
lean_dec(v_sz_2546_);
v_i_boxed_2560_ = lean_unbox_usize(v_i_2547_);
lean_dec(v_i_2547_);
v_res_2561_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_epr_spec__1(v_cfg_2544_, v_as_2545_, v_sz_boxed_2559_, v_i_boxed_2560_, v_b_2548_, v___y_2549_, v___y_2550_, v___y_2551_, v___y_2552_, v___y_2553_, v___y_2554_, v___y_2555_, v___y_2556_, v___y_2557_);
lean_dec(v___y_2557_);
lean_dec_ref(v___y_2556_);
lean_dec(v___y_2555_);
lean_dec_ref(v___y_2554_);
lean_dec(v___y_2553_);
lean_dec_ref(v___y_2552_);
lean_dec(v___y_2551_);
lean_dec_ref(v___y_2550_);
lean_dec(v___y_2549_);
lean_dec_ref(v_as_2545_);
return v_res_2561_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_epr___lam__0(lean_object* v_fst_2562_, lean_object* v_cfg_2563_, lean_object* v_snd_2564_, lean_object* v___y_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_){
_start:
{
lean_object* v___x_2575_; 
v___x_2575_ = l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_nnf(v_fst_2562_, v_cfg_2563_, v___y_2568_, v___y_2569_, v___y_2570_, v___y_2571_, v___y_2572_, v___y_2573_);
if (lean_obj_tag(v___x_2575_) == 0)
{
lean_object* v_a_2576_; lean_object* v___x_2577_; 
v_a_2576_ = lean_ctor_get(v___x_2575_, 0);
lean_inc(v_a_2576_);
lean_dec_ref_known(v___x_2575_, 1);
v___x_2577_ = l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_andFlatten(v_a_2576_, v___y_2568_, v___y_2569_, v___y_2570_, v___y_2571_, v___y_2572_, v___y_2573_);
lean_dec(v_a_2576_);
if (lean_obj_tag(v___x_2577_) == 0)
{
lean_object* v_a_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; size_t v_sz_2582_; size_t v___x_2583_; lean_object* v___x_2584_; 
v_a_2578_ = lean_ctor_get(v___x_2577_, 0);
lean_inc(v_a_2578_);
lean_dec_ref_known(v___x_2577_, 1);
v___x_2579_ = lean_array_get_size(v_a_2578_);
v___x_2580_ = lean_mk_empty_array_with_capacity(v___x_2579_);
v___x_2581_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2581_, 0, v___x_2580_);
lean_ctor_set(v___x_2581_, 1, v_snd_2564_);
v_sz_2582_ = lean_array_size(v_a_2578_);
v___x_2583_ = ((size_t)0ULL);
lean_inc_ref(v_cfg_2563_);
v___x_2584_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_epr_spec__1(v_cfg_2563_, v_a_2578_, v_sz_2582_, v___x_2583_, v___x_2581_, v___y_2565_, v___y_2566_, v___y_2567_, v___y_2568_, v___y_2569_, v___y_2570_, v___y_2571_, v___y_2572_, v___y_2573_);
lean_dec(v_a_2578_);
if (lean_obj_tag(v___x_2584_) == 0)
{
lean_object* v_a_2585_; lean_object* v_fst_2586_; lean_object* v_snd_2587_; lean_object* v___x_2589_; uint8_t v_isShared_2590_; uint8_t v_isSharedCheck_2612_; 
v_a_2585_ = lean_ctor_get(v___x_2584_, 0);
lean_inc(v_a_2585_);
lean_dec_ref_known(v___x_2584_, 1);
v_fst_2586_ = lean_ctor_get(v_a_2585_, 0);
v_snd_2587_ = lean_ctor_get(v_a_2585_, 1);
v_isSharedCheck_2612_ = !lean_is_exclusive(v_a_2585_);
if (v_isSharedCheck_2612_ == 0)
{
v___x_2589_ = v_a_2585_;
v_isShared_2590_ = v_isSharedCheck_2612_;
goto v_resetjp_2588_;
}
else
{
lean_inc(v_snd_2587_);
lean_inc(v_fst_2586_);
lean_dec(v_a_2585_);
v___x_2589_ = lean_box(0);
v_isShared_2590_ = v_isSharedCheck_2612_;
goto v_resetjp_2588_;
}
v_resetjp_2588_:
{
lean_object* v___x_2592_; 
if (v_isShared_2590_ == 0)
{
lean_ctor_set(v___x_2589_, 1, v_fst_2586_);
lean_ctor_set(v___x_2589_, 0, v_snd_2587_);
v___x_2592_ = v___x_2589_;
goto v_reusejp_2591_;
}
else
{
lean_object* v_reuseFailAlloc_2611_; 
v_reuseFailAlloc_2611_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2611_, 0, v_snd_2587_);
lean_ctor_set(v_reuseFailAlloc_2611_, 1, v_fst_2586_);
v___x_2592_ = v_reuseFailAlloc_2611_;
goto v_reusejp_2591_;
}
v_reusejp_2591_:
{
lean_object* v___x_2593_; lean_object* v___x_2594_; 
v___x_2593_ = lean_box(0);
v___x_2594_ = l_Lean_Meta_Tactic_BVDecide_bvDecide(v___x_2592_, v_cfg_2563_, v___y_2565_, v___y_2566_, v___y_2567_, v___y_2568_, v___y_2569_, v___y_2570_, v___y_2571_, v___y_2572_, v___y_2573_);
if (lean_obj_tag(v___x_2594_) == 0)
{
lean_object* v___x_2596_; uint8_t v_isShared_2597_; uint8_t v_isSharedCheck_2601_; 
v_isSharedCheck_2601_ = !lean_is_exclusive(v___x_2594_);
if (v_isSharedCheck_2601_ == 0)
{
lean_object* v_unused_2602_; 
v_unused_2602_ = lean_ctor_get(v___x_2594_, 0);
lean_dec(v_unused_2602_);
v___x_2596_ = v___x_2594_;
v_isShared_2597_ = v_isSharedCheck_2601_;
goto v_resetjp_2595_;
}
else
{
lean_dec(v___x_2594_);
v___x_2596_ = lean_box(0);
v_isShared_2597_ = v_isSharedCheck_2601_;
goto v_resetjp_2595_;
}
v_resetjp_2595_:
{
lean_object* v___x_2599_; 
if (v_isShared_2597_ == 0)
{
lean_ctor_set(v___x_2596_, 0, v___x_2593_);
v___x_2599_ = v___x_2596_;
goto v_reusejp_2598_;
}
else
{
lean_object* v_reuseFailAlloc_2600_; 
v_reuseFailAlloc_2600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2600_, 0, v___x_2593_);
v___x_2599_ = v_reuseFailAlloc_2600_;
goto v_reusejp_2598_;
}
v_reusejp_2598_:
{
return v___x_2599_;
}
}
}
else
{
lean_object* v_a_2603_; lean_object* v___x_2605_; uint8_t v_isShared_2606_; uint8_t v_isSharedCheck_2610_; 
v_a_2603_ = lean_ctor_get(v___x_2594_, 0);
v_isSharedCheck_2610_ = !lean_is_exclusive(v___x_2594_);
if (v_isSharedCheck_2610_ == 0)
{
v___x_2605_ = v___x_2594_;
v_isShared_2606_ = v_isSharedCheck_2610_;
goto v_resetjp_2604_;
}
else
{
lean_inc(v_a_2603_);
lean_dec(v___x_2594_);
v___x_2605_ = lean_box(0);
v_isShared_2606_ = v_isSharedCheck_2610_;
goto v_resetjp_2604_;
}
v_resetjp_2604_:
{
lean_object* v___x_2608_; 
if (v_isShared_2606_ == 0)
{
v___x_2608_ = v___x_2605_;
goto v_reusejp_2607_;
}
else
{
lean_object* v_reuseFailAlloc_2609_; 
v_reuseFailAlloc_2609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2609_, 0, v_a_2603_);
v___x_2608_ = v_reuseFailAlloc_2609_;
goto v_reusejp_2607_;
}
v_reusejp_2607_:
{
return v___x_2608_;
}
}
}
}
}
}
else
{
lean_object* v_a_2613_; lean_object* v___x_2615_; uint8_t v_isShared_2616_; uint8_t v_isSharedCheck_2620_; 
lean_dec_ref(v_cfg_2563_);
v_a_2613_ = lean_ctor_get(v___x_2584_, 0);
v_isSharedCheck_2620_ = !lean_is_exclusive(v___x_2584_);
if (v_isSharedCheck_2620_ == 0)
{
v___x_2615_ = v___x_2584_;
v_isShared_2616_ = v_isSharedCheck_2620_;
goto v_resetjp_2614_;
}
else
{
lean_inc(v_a_2613_);
lean_dec(v___x_2584_);
v___x_2615_ = lean_box(0);
v_isShared_2616_ = v_isSharedCheck_2620_;
goto v_resetjp_2614_;
}
v_resetjp_2614_:
{
lean_object* v___x_2618_; 
if (v_isShared_2616_ == 0)
{
v___x_2618_ = v___x_2615_;
goto v_reusejp_2617_;
}
else
{
lean_object* v_reuseFailAlloc_2619_; 
v_reuseFailAlloc_2619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2619_, 0, v_a_2613_);
v___x_2618_ = v_reuseFailAlloc_2619_;
goto v_reusejp_2617_;
}
v_reusejp_2617_:
{
return v___x_2618_;
}
}
}
}
else
{
lean_object* v_a_2621_; lean_object* v___x_2623_; uint8_t v_isShared_2624_; uint8_t v_isSharedCheck_2628_; 
lean_dec(v_snd_2564_);
lean_dec_ref(v_cfg_2563_);
v_a_2621_ = lean_ctor_get(v___x_2577_, 0);
v_isSharedCheck_2628_ = !lean_is_exclusive(v___x_2577_);
if (v_isSharedCheck_2628_ == 0)
{
v___x_2623_ = v___x_2577_;
v_isShared_2624_ = v_isSharedCheck_2628_;
goto v_resetjp_2622_;
}
else
{
lean_inc(v_a_2621_);
lean_dec(v___x_2577_);
v___x_2623_ = lean_box(0);
v_isShared_2624_ = v_isSharedCheck_2628_;
goto v_resetjp_2622_;
}
v_resetjp_2622_:
{
lean_object* v___x_2626_; 
if (v_isShared_2624_ == 0)
{
v___x_2626_ = v___x_2623_;
goto v_reusejp_2625_;
}
else
{
lean_object* v_reuseFailAlloc_2627_; 
v_reuseFailAlloc_2627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2627_, 0, v_a_2621_);
v___x_2626_ = v_reuseFailAlloc_2627_;
goto v_reusejp_2625_;
}
v_reusejp_2625_:
{
return v___x_2626_;
}
}
}
}
else
{
lean_object* v_a_2629_; lean_object* v___x_2631_; uint8_t v_isShared_2632_; uint8_t v_isSharedCheck_2636_; 
lean_dec(v_snd_2564_);
lean_dec_ref(v_cfg_2563_);
v_a_2629_ = lean_ctor_get(v___x_2575_, 0);
v_isSharedCheck_2636_ = !lean_is_exclusive(v___x_2575_);
if (v_isSharedCheck_2636_ == 0)
{
v___x_2631_ = v___x_2575_;
v_isShared_2632_ = v_isSharedCheck_2636_;
goto v_resetjp_2630_;
}
else
{
lean_inc(v_a_2629_);
lean_dec(v___x_2575_);
v___x_2631_ = lean_box(0);
v_isShared_2632_ = v_isSharedCheck_2636_;
goto v_resetjp_2630_;
}
v_resetjp_2630_:
{
lean_object* v___x_2634_; 
if (v_isShared_2632_ == 0)
{
v___x_2634_ = v___x_2631_;
goto v_reusejp_2633_;
}
else
{
lean_object* v_reuseFailAlloc_2635_; 
v_reuseFailAlloc_2635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2635_, 0, v_a_2629_);
v___x_2634_ = v_reuseFailAlloc_2635_;
goto v_reusejp_2633_;
}
v_reusejp_2633_:
{
return v___x_2634_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_epr___lam__0___boxed(lean_object* v_fst_2637_, lean_object* v_cfg_2638_, lean_object* v_snd_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_){
_start:
{
lean_object* v_res_2650_; 
v_res_2650_ = l_Lean_Meta_Tactic_epr___lam__0(v_fst_2637_, v_cfg_2638_, v_snd_2639_, v___y_2640_, v___y_2641_, v___y_2642_, v___y_2643_, v___y_2644_, v___y_2645_, v___y_2646_, v___y_2647_, v___y_2648_);
lean_dec(v___y_2648_);
lean_dec_ref(v___y_2647_);
lean_dec(v___y_2646_);
lean_dec_ref(v___y_2645_);
lean_dec(v___y_2644_);
lean_dec_ref(v___y_2643_);
lean_dec(v___y_2642_);
lean_dec_ref(v___y_2641_);
lean_dec(v___y_2640_);
return v_res_2650_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_epr___lam__1(lean_object* v_g_2651_, lean_object* v_cfg_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_, lean_object* v___y_2656_, lean_object* v___y_2657_, lean_object* v___y_2658_, lean_object* v___y_2659_, lean_object* v___y_2660_, lean_object* v___y_2661_){
_start:
{
lean_object* v___x_2663_; 
v___x_2663_ = l_Lean_Meta_Tactic_BVDecide_Normalize_collectMVarHyps(v_g_2651_, v___y_2656_, v___y_2657_, v___y_2658_, v___y_2659_, v___y_2660_, v___y_2661_);
if (lean_obj_tag(v___x_2663_) == 0)
{
lean_object* v_a_2664_; lean_object* v_fst_2665_; lean_object* v_snd_2666_; lean_object* v___f_2667_; lean_object* v___x_2668_; 
v_a_2664_ = lean_ctor_get(v___x_2663_, 0);
lean_inc(v_a_2664_);
lean_dec_ref_known(v___x_2663_, 1);
v_fst_2665_ = lean_ctor_get(v_a_2664_, 0);
lean_inc(v_fst_2665_);
v_snd_2666_ = lean_ctor_get(v_a_2664_, 1);
lean_inc_n(v_snd_2666_, 3);
lean_dec(v_a_2664_);
v___f_2667_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_epr___lam__0___boxed), 13, 3);
lean_closure_set(v___f_2667_, 0, v_fst_2665_);
lean_closure_set(v___f_2667_, 1, v_cfg_2652_);
lean_closure_set(v___f_2667_, 2, v_snd_2666_);
v___x_2668_ = l___private_Lean_Meta_Tactic_Epr_0__Lean_Meta_Tactic_Epr_addNonempty(v_snd_2666_, v___y_2656_, v___y_2657_, v___y_2658_, v___y_2659_, v___y_2660_, v___y_2661_);
if (lean_obj_tag(v___x_2668_) == 0)
{
lean_object* v___x_2669_; 
lean_dec_ref_known(v___x_2668_, 1);
v___x_2669_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_epr_spec__0___redArg(v_snd_2666_, v___f_2667_, v___y_2653_, v___y_2654_, v___y_2655_, v___y_2656_, v___y_2657_, v___y_2658_, v___y_2659_, v___y_2660_, v___y_2661_);
return v___x_2669_;
}
else
{
lean_dec_ref(v___f_2667_);
lean_dec(v_snd_2666_);
return v___x_2668_;
}
}
else
{
lean_object* v_a_2670_; lean_object* v___x_2672_; uint8_t v_isShared_2673_; uint8_t v_isSharedCheck_2677_; 
lean_dec_ref(v_cfg_2652_);
v_a_2670_ = lean_ctor_get(v___x_2663_, 0);
v_isSharedCheck_2677_ = !lean_is_exclusive(v___x_2663_);
if (v_isSharedCheck_2677_ == 0)
{
v___x_2672_ = v___x_2663_;
v_isShared_2673_ = v_isSharedCheck_2677_;
goto v_resetjp_2671_;
}
else
{
lean_inc(v_a_2670_);
lean_dec(v___x_2663_);
v___x_2672_ = lean_box(0);
v_isShared_2673_ = v_isSharedCheck_2677_;
goto v_resetjp_2671_;
}
v_resetjp_2671_:
{
lean_object* v___x_2675_; 
if (v_isShared_2673_ == 0)
{
v___x_2675_ = v___x_2672_;
goto v_reusejp_2674_;
}
else
{
lean_object* v_reuseFailAlloc_2676_; 
v_reuseFailAlloc_2676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2676_, 0, v_a_2670_);
v___x_2675_ = v_reuseFailAlloc_2676_;
goto v_reusejp_2674_;
}
v_reusejp_2674_:
{
return v___x_2675_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_epr___lam__1___boxed(lean_object* v_g_2678_, lean_object* v_cfg_2679_, lean_object* v___y_2680_, lean_object* v___y_2681_, lean_object* v___y_2682_, lean_object* v___y_2683_, lean_object* v___y_2684_, lean_object* v___y_2685_, lean_object* v___y_2686_, lean_object* v___y_2687_, lean_object* v___y_2688_, lean_object* v___y_2689_){
_start:
{
lean_object* v_res_2690_; 
v_res_2690_ = l_Lean_Meta_Tactic_epr___lam__1(v_g_2678_, v_cfg_2679_, v___y_2680_, v___y_2681_, v___y_2682_, v___y_2683_, v___y_2684_, v___y_2685_, v___y_2686_, v___y_2687_, v___y_2688_);
lean_dec(v___y_2688_);
lean_dec_ref(v___y_2687_);
lean_dec(v___y_2686_);
lean_dec_ref(v___y_2685_);
lean_dec(v___y_2684_);
lean_dec_ref(v___y_2683_);
lean_dec(v___y_2682_);
lean_dec_ref(v___y_2681_);
lean_dec(v___y_2680_);
return v_res_2690_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_epr___lam__2(lean_object* v___x_2691_, lean_object* v___f_2692_, lean_object* v___y_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_){
_start:
{
lean_object* v___x_2698_; 
v___x_2698_ = l_Lean_Meta_Grind_mkDefaultParams(v___x_2691_, v___y_2693_, v___y_2694_, v___y_2695_, v___y_2696_);
if (lean_obj_tag(v___x_2698_) == 0)
{
lean_object* v_a_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; 
v_a_2699_ = lean_ctor_get(v___x_2698_, 0);
lean_inc(v_a_2699_);
lean_dec_ref_known(v___x_2698_, 1);
v___x_2700_ = lean_box(0);
v___x_2701_ = l_Lean_Meta_Grind_GrindM_run___redArg(v___f_2692_, v_a_2699_, v___x_2700_, v___y_2693_, v___y_2694_, v___y_2695_, v___y_2696_);
return v___x_2701_;
}
else
{
lean_object* v_a_2702_; lean_object* v___x_2704_; uint8_t v_isShared_2705_; uint8_t v_isSharedCheck_2709_; 
lean_dec_ref(v___f_2692_);
v_a_2702_ = lean_ctor_get(v___x_2698_, 0);
v_isSharedCheck_2709_ = !lean_is_exclusive(v___x_2698_);
if (v_isSharedCheck_2709_ == 0)
{
v___x_2704_ = v___x_2698_;
v_isShared_2705_ = v_isSharedCheck_2709_;
goto v_resetjp_2703_;
}
else
{
lean_inc(v_a_2702_);
lean_dec(v___x_2698_);
v___x_2704_ = lean_box(0);
v_isShared_2705_ = v_isSharedCheck_2709_;
goto v_resetjp_2703_;
}
v_resetjp_2703_:
{
lean_object* v___x_2707_; 
if (v_isShared_2705_ == 0)
{
v___x_2707_ = v___x_2704_;
goto v_reusejp_2706_;
}
else
{
lean_object* v_reuseFailAlloc_2708_; 
v_reuseFailAlloc_2708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2708_, 0, v_a_2702_);
v___x_2707_ = v_reuseFailAlloc_2708_;
goto v_reusejp_2706_;
}
v_reusejp_2706_:
{
return v___x_2707_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_epr___lam__2___boxed(lean_object* v___x_2710_, lean_object* v___f_2711_, lean_object* v___y_2712_, lean_object* v___y_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_){
_start:
{
lean_object* v_res_2717_; 
v_res_2717_ = l_Lean_Meta_Tactic_epr___lam__2(v___x_2710_, v___f_2711_, v___y_2712_, v___y_2713_, v___y_2714_, v___y_2715_);
lean_dec(v___y_2715_);
lean_dec_ref(v___y_2714_);
lean_dec(v___y_2713_);
lean_dec_ref(v___y_2712_);
return v_res_2717_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_epr(lean_object* v_g_2734_, lean_object* v_cfg_2735_, lean_object* v_a_2736_, lean_object* v_a_2737_, lean_object* v_a_2738_, lean_object* v_a_2739_){
_start:
{
lean_object* v___f_2741_; lean_object* v___x_2742_; lean_object* v___f_2743_; lean_object* v___x_2744_; 
lean_inc(v_g_2734_);
v___f_2741_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_epr___lam__1___boxed), 12, 2);
lean_closure_set(v___f_2741_, 0, v_g_2734_);
lean_closure_set(v___f_2741_, 1, v_cfg_2735_);
v___x_2742_ = ((lean_object*)(l_Lean_Meta_Tactic_epr___closed__0));
v___f_2743_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_epr___lam__2___boxed), 7, 2);
lean_closure_set(v___f_2743_, 0, v___x_2742_);
lean_closure_set(v___f_2743_, 1, v___f_2741_);
v___x_2744_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_epr_spec__2___redArg(v_g_2734_, v___f_2743_, v_a_2736_, v_a_2737_, v_a_2738_, v_a_2739_);
return v___x_2744_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_epr___boxed(lean_object* v_g_2745_, lean_object* v_cfg_2746_, lean_object* v_a_2747_, lean_object* v_a_2748_, lean_object* v_a_2749_, lean_object* v_a_2750_, lean_object* v_a_2751_){
_start:
{
lean_object* v_res_2752_; 
v_res_2752_ = l_Lean_Meta_Tactic_epr(v_g_2745_, v_cfg_2746_, v_a_2747_, v_a_2748_, v_a_2749_, v_a_2750_);
lean_dec(v_a_2750_);
lean_dec_ref(v_a_2749_);
lean_dec(v_a_2748_);
lean_dec_ref(v_a_2747_);
return v_res_2752_;
}
}
lean_object* runtime_initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* runtime_initialize_Std_Tactic_BVDecide_Syntax(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_NNF(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_Prenex(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Main(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Main(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_TacticContext(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Apply(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_InferType(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Intro(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_InstantiateMVarsS(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_SynthInstance(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Epr(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_BVDecide_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Simp_NNF(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Simp_Prenex(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Main(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Main(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_TacticContext(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Apply(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_InferType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Intro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_InstantiateMVarsS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_SynthInstance(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Epr(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* initialize_Std_Tactic_BVDecide_Syntax(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_NNF(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_Prenex(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_BVDecide_Main(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Main(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_BVDecide_TacticContext(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Apply(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_InferType(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Intro(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_InstantiateMVarsS(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_SynthInstance(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Epr(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Simp_NNF(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Simp_Prenex(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_BVDecide_Main(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Main(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_BVDecide_TacticContext(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Apply(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_InferType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Intro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_InstantiateMVarsS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_SynthInstance(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Epr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Epr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Epr(builtin);
}
#ifdef __cplusplus
}
#endif
