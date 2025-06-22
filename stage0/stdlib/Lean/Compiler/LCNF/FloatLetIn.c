// Lean compiler output
// Module: Lean.Compiler.LCNF.FloatLetIn
// Imports: Lean.Compiler.LCNF.CompilerM Lean.Compiler.LCNF.FVarUtil Lean.Compiler.LCNF.PassManager Lean.Compiler.LCNF.Types
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_instInhabitedDecision;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__10____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2285_;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_Compiler_LCNF_FloatLetIn_float_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Param_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__2;
lean_object* l_Lean_Name_reprPrec(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_withNewCandidate___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_forFVarM___at___Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__2_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_forCodeM___at___Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FunDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__7_spec__8_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_Compiler_LCNF_FloatLetIn_float_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goCases___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__5____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2285_;
lean_object* l_Array_reverse___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Param_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_FloatLetIn_reprDecision___closed__2____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_171_;
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
static lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0___redArg___closed__3;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_LetValue_forFVarM___at___Lean_Compiler_LCNF_LetDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_floatLetIn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_FloatLetIn_reprDecision___closed__5____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_171_;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_instHashableDecision;
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___boxed(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
static size_t l_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___closed__5;
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__2_spec__2___closed__2;
LEAN_EXPORT lean_object* l_List_foldlM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_isArrowClass_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__3_spec__9___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__3___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___closed__6;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_LetValue_forFVarM___at___Lean_Compiler_LCNF_LetDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__3_spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__11____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2285_;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goCases_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FunDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__7_spec__8___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__7____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2285_;
static lean_object* l_Lean_addTrace___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___redArg___closed__1;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__3____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2285_;
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Param_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_ignore_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_ignore_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_171____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_forFVarM___at___Lean_Compiler_LCNF_LetDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_toLocalContext(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_LetValue_forFVarM___at___Lean_Compiler_LCNF_LetDecl_forFVarM___at___Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__3_spec__6_spec__6_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_floatLetIn___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Param_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__0___closed__1;
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__4____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2285_;
static uint64_t l_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___closed__4;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_float_goFVar___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FunDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__7_spec__8_spec__10___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__7___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_171_(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__1(lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__2___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addTrace___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___redArg___closed__3;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_LetValue_forFVarM___at___Lean_Compiler_LCNF_LetDecl_forFVarM___at___Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__3_spec__6_spec__6_spec__6(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addTrace___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___redArg___closed__10;
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__14____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2285_;
size_t lean_usize_of_nat(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision___closed__0;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision;
static lean_object* l_Lean_addTrace___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___redArg___closed__6;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_forFVarM___at___Lean_Compiler_LCNF_LetDecl_forFVarM___at___Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__3_spec__6_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static uint64_t l_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___closed__0;
static lean_object* l_Lean_Compiler_LCNF_FloatLetIn_reprDecision___closed__8____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_171_;
static lean_object* l_Lean_Compiler_LCNF_FloatLetIn_dontFloat___closed__0;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_LetDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__12____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2285_;
static lean_object* l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Param_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__0___closed__3;
static lean_object* l_Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Param_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__0;
static lean_object* l_Lean_Compiler_LCNF_FloatLetIn_instInhabitedDecision___closed__0;
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_LetDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FunDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__7_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_float___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_floatLetIn___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_float_goFVar___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addTrace___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___redArg___closed__2;
lean_object* l_instMonadEIO(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_withNewScope___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_floatLetIn___closed__0;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FunDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__7_spec__8___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static double l_Lean_addTrace___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___redArg___closed__8;
static lean_object* l_Lean_Compiler_LCNF_FloatLetIn_reprDecision___closed__1____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_171_;
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FunDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__7_spec__8_spec__10(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__2_spec__2___closed__6;
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
uint8_t l_Lean_checkTraceOption(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_beqDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_73____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_floatLetIn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FunDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__7_spec__8_spec__9(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goCases_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addTrace___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_float_goFVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FunDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__7_spec__8_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___closed__7;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__3_spec__9(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Lean_Compiler_LCNF_FloatLetIn_hashDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_26_(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__1_spec__1_spec__1___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_FloatLetIn_reprDecision___closed__6____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_171_;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FunDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__7_spec__8_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_forCodeM___at___Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__3_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_forFVarM___at___Lean_Compiler_LCNF_LetValue_forFVarM___at___Lean_Compiler_LCNF_LetDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__3_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2285_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_floatLetIn(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__5___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lean_addTrace___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___redArg___closed__9;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_forFVarM___at___Lean_Compiler_LCNF_FunDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__7_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_hashFVarId____x40_Lean_Expr___hyg_1561_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__1___redArg(lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseCodeDecl___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_FloatLetIn_reprDecision___closed__0____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_171_;
static lean_object* l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__2_spec__2___closed__0;
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__2____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2285_;
static lean_object* l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__2_spec__2___closed__4;
lean_object* l_Lean_Compiler_LCNF_attachCodeDecls(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_FloatLetIn_reprDecision___closed__3____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_171_;
static lean_object* l_Lean_Compiler_LCNF_FloatLetIn_instHashableDecision___closed__0;
static lean_object* l_Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Param_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_hashDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_26____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__0___redArg(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
static lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_float_goFVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_withNewScope___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_initialNewArms(lean_object*);
static uint64_t l_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___closed__1;
static lean_object* l_Lean_Compiler_LCNF_FloatLetIn_reprDecision___closed__4____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_171_;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__16____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2285_;
static lean_object* l_Lean_Compiler_LCNF_FloatLetIn_reprDecision___closed__10____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_171_;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_dontFloat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_forFVarM___at___Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__3_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__15____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2285_;
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__8____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2285_;
static lean_object* l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__2_spec__2___closed__7;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goCases(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_ignore_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_FloatLetIn_floatLetIn___closed__0;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__3_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Name_hash___override(lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__2_spec__2___closed__5;
uint64_t lean_uint64_xor(uint64_t, uint64_t);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_CodeDecl_fvarId(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_Compiler_LCNF_FloatLetIn_float_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_withNewScope(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
static lean_object* l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Param_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__0___closed__4;
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__7___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static uint64_t l_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___closed__2;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_LCtx_addParam_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__1_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_float(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addTrace___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___redArg___closed__4;
static lean_object* l_Lean_Compiler_LCNF_FloatLetIn_reprDecision___closed__7____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_171_;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_Compiler_LCNF_FloatLetIn_float_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__3___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_mk(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_FloatLetIn_beqDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_73_(lean_object*, lean_object*);
static lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0___redArg___closed__2;
LEAN_EXPORT lean_object* l_List_foldlM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_instBEqDecision;
lean_object* l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_FloatLetIn_reprDecision___closed__9____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_171_;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_withNewCandidate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_float___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
static lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0___redArg___closed__1;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__3_spec__5(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Compiler_LCNF_getType_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__9____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2285_;
LEAN_EXPORT lean_object* l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Param_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__2_spec__2___closed__1;
static uint64_t l_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___closed__3;
static lean_object* l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Param_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__0___closed__0;
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__13____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2285_;
static lean_object* l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__2_spec__2___closed__3;
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_ignore_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__0____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2285_;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__6____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2285_;
uint8_t lean_usize_dec_lt(size_t, size_t);
static lean_object* l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Param_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__0___closed__2;
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_Decision_ofAlt___boxed(lean_object*);
static lean_object* l_Lean_addTrace___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___redArg___closed__7;
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__1____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2285_;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_addTrace___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___redArg___closed__5;
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT lean_object* l_List_foldlM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_Decision_ofAlt(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__1___redArg(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_FloatLetIn_instBEqDecision___closed__0;
LEAN_EXPORT uint64_t l_Lean_Compiler_LCNF_FloatLetIn_hashDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_26_(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; uint64_t x_3; uint64_t x_4; uint64_t x_5; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = 0;
x_4 = l_Lean_Name_hash___override(x_2);
x_5 = lean_uint64_mix_hash(x_3, x_4);
return x_5;
}
case 1:
{
uint64_t x_6; 
x_6 = 1;
return x_6;
}
case 2:
{
uint64_t x_7; 
x_7 = 2;
return x_7;
}
default: 
{
uint64_t x_8; 
x_8 = 3;
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_hashDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_26____boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l_Lean_Compiler_LCNF_FloatLetIn_hashDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_26_(x_1);
lean_dec(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_FloatLetIn_instHashableDecision___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_FloatLetIn_hashDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_26____boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_FloatLetIn_instHashableDecision() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Compiler_LCNF_FloatLetIn_instHashableDecision___closed__0;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_FloatLetIn_beqDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_73_(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_name_eq(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_box(0);
x_7 = lean_unbox(x_6);
return x_7;
}
}
case 1:
{
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_box(1);
x_9 = lean_unbox(x_8);
return x_9;
}
else
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_box(0);
x_11 = lean_unbox(x_10);
return x_11;
}
}
case 2:
{
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_box(1);
x_13 = lean_unbox(x_12);
return x_13;
}
else
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_box(0);
x_15 = lean_unbox(x_14);
return x_15;
}
}
default: 
{
if (lean_obj_tag(x_2) == 3)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_box(1);
x_17 = lean_unbox(x_16);
return x_17;
}
else
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_box(0);
x_19 = lean_unbox(x_18);
return x_19;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_beqDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_73____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Compiler_LCNF_FloatLetIn_beqDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_73_(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_FloatLetIn_instBEqDecision___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_FloatLetIn_beqDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_73____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_FloatLetIn_instBEqDecision() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Compiler_LCNF_FloatLetIn_instBEqDecision___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_FloatLetIn_instInhabitedDecision___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_FloatLetIn_instInhabitedDecision() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Compiler_LCNF_FloatLetIn_instInhabitedDecision___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_FloatLetIn_reprDecision___closed__0____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_171_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Compiler.LCNF.FloatLetIn.Decision.default", 46, 46);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_FloatLetIn_reprDecision___closed__1____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_171_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_FloatLetIn_reprDecision___closed__0____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_171_;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_FloatLetIn_reprDecision___closed__2____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_171_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Compiler.LCNF.FloatLetIn.Decision.dont", 43, 43);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_FloatLetIn_reprDecision___closed__3____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_171_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_FloatLetIn_reprDecision___closed__2____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_171_;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_FloatLetIn_reprDecision___closed__4____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_171_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Compiler.LCNF.FloatLetIn.Decision.unknown", 46, 46);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_FloatLetIn_reprDecision___closed__5____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_171_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_FloatLetIn_reprDecision___closed__4____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_171_;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_FloatLetIn_reprDecision___closed__6____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_171_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Compiler.LCNF.FloatLetIn.Decision.arm", 42, 42);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_FloatLetIn_reprDecision___closed__7____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_171_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_FloatLetIn_reprDecision___closed__6____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_171_;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_FloatLetIn_reprDecision___closed__8____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_171_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(1);
x_2 = l_Lean_Compiler_LCNF_FloatLetIn_reprDecision___closed__7____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_171_;
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_FloatLetIn_reprDecision___closed__9____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_171_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_FloatLetIn_reprDecision___closed__10____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_171_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_171_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_11; lean_object* x_19; 
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_27; lean_object* x_28; lean_object* x_39; uint8_t x_40; 
x_27 = lean_ctor_get(x_1, 0);
lean_inc(x_27);
lean_dec(x_1);
x_39 = lean_unsigned_to_nat(1024u);
x_40 = lean_nat_dec_le(x_39, x_2);
if (x_40 == 0)
{
lean_object* x_41; 
x_41 = l_Lean_Compiler_LCNF_FloatLetIn_reprDecision___closed__9____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_171_;
x_28 = x_41;
goto block_38;
}
else
{
lean_object* x_42; 
x_42 = l_Lean_Compiler_LCNF_FloatLetIn_reprDecision___closed__10____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_171_;
x_28 = x_42;
goto block_38;
}
block_38:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; 
x_29 = l_Lean_Compiler_LCNF_FloatLetIn_reprDecision___closed__8____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_171_;
x_30 = lean_unsigned_to_nat(1024u);
x_31 = l_Lean_Name_reprPrec(x_27, x_30);
x_32 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_32, 0, x_29);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_33, 0, x_28);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_box(0);
x_35 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_35, 0, x_33);
x_36 = lean_unbox(x_34);
lean_ctor_set_uint8(x_35, sizeof(void*)*1, x_36);
x_37 = l_Repr_addAppParen(x_35, x_2);
return x_37;
}
}
case 1:
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_unsigned_to_nat(1024u);
x_44 = lean_nat_dec_le(x_43, x_2);
if (x_44 == 0)
{
lean_object* x_45; 
x_45 = l_Lean_Compiler_LCNF_FloatLetIn_reprDecision___closed__9____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_171_;
x_3 = x_45;
goto block_10;
}
else
{
lean_object* x_46; 
x_46 = l_Lean_Compiler_LCNF_FloatLetIn_reprDecision___closed__10____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_171_;
x_3 = x_46;
goto block_10;
}
}
case 2:
{
lean_object* x_47; uint8_t x_48; 
x_47 = lean_unsigned_to_nat(1024u);
x_48 = lean_nat_dec_le(x_47, x_2);
if (x_48 == 0)
{
lean_object* x_49; 
x_49 = l_Lean_Compiler_LCNF_FloatLetIn_reprDecision___closed__9____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_171_;
x_11 = x_49;
goto block_18;
}
else
{
lean_object* x_50; 
x_50 = l_Lean_Compiler_LCNF_FloatLetIn_reprDecision___closed__10____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_171_;
x_11 = x_50;
goto block_18;
}
}
default: 
{
lean_object* x_51; uint8_t x_52; 
x_51 = lean_unsigned_to_nat(1024u);
x_52 = lean_nat_dec_le(x_51, x_2);
if (x_52 == 0)
{
lean_object* x_53; 
x_53 = l_Lean_Compiler_LCNF_FloatLetIn_reprDecision___closed__9____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_171_;
x_19 = x_53;
goto block_26;
}
else
{
lean_object* x_54; 
x_54 = l_Lean_Compiler_LCNF_FloatLetIn_reprDecision___closed__10____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_171_;
x_19 = x_54;
goto block_26;
}
}
}
block_10:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_4 = l_Lean_Compiler_LCNF_FloatLetIn_reprDecision___closed__1____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_171_;
x_5 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_7, 0, x_5);
x_8 = lean_unbox(x_6);
lean_ctor_set_uint8(x_7, sizeof(void*)*1, x_8);
x_9 = l_Repr_addAppParen(x_7, x_2);
return x_9;
}
block_18:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_12 = l_Lean_Compiler_LCNF_FloatLetIn_reprDecision___closed__3____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_171_;
x_13 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_15, 0, x_13);
x_16 = lean_unbox(x_14);
lean_ctor_set_uint8(x_15, sizeof(void*)*1, x_16);
x_17 = l_Repr_addAppParen(x_15, x_2);
return x_17;
}
block_26:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; 
x_20 = l_Lean_Compiler_LCNF_FloatLetIn_reprDecision___closed__5____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_171_;
x_21 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_23, 0, x_21);
x_24 = lean_unbox(x_22);
lean_ctor_set_uint8(x_23, sizeof(void*)*1, x_24);
x_25 = l_Repr_addAppParen(x_23, x_2);
return x_25;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_171____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_171_(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_171____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_Decision_ofAlt(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
else
{
lean_object* x_4; 
x_4 = lean_box(1);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_Decision_ofAlt___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Compiler_LCNF_FloatLetIn_Decision_ofAlt(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_withNewCandidate___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_3);
x_10 = lean_apply_6(x_2, x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_withNewCandidate(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_FloatLetIn_withNewCandidate___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_withNewScope___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_box(0);
x_8 = lean_apply_6(x_1, x_7, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_withNewScope(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_FloatLetIn_withNewScope___redArg(x_2, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_withNewScope___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_FloatLetIn_withNewScope(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_ignore_x3f___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_1, 2);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 3);
lean_inc(x_8);
lean_dec(x_1);
x_9 = l_Lean_Compiler_LCNF_isArrowClass_x3f___redArg(x_7, x_5, x_6);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_9, 1);
x_13 = lean_ctor_get(x_9, 0);
lean_dec(x_13);
x_14 = lean_box(0);
if (lean_obj_tag(x_8) == 2)
{
lean_object* x_15; lean_object* x_16; 
lean_free_object(x_9);
x_15 = lean_ctor_get(x_8, 2);
lean_inc(x_15);
lean_dec(x_8);
x_16 = l_Lean_Compiler_LCNF_getType(x_15, x_2, x_3, x_4, x_5, x_12);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_Compiler_LCNF_isArrowClass_x3f___redArg(x_17, x_5, x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_19);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_19, 0);
lean_dec(x_22);
lean_ctor_set(x_19, 0, x_14);
return x_19;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_19, 1);
lean_inc(x_23);
lean_dec(x_19);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_14);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
else
{
uint8_t x_25; 
lean_dec(x_20);
x_25 = !lean_is_exclusive(x_19);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_19, 0);
lean_dec(x_26);
x_27 = lean_box(1);
lean_ctor_set(x_19, 0, x_27);
return x_19;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_19, 1);
lean_inc(x_28);
lean_dec(x_19);
x_29 = lean_box(1);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
}
}
else
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_16);
if (x_31 == 0)
{
return x_16;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_16, 0);
x_33 = lean_ctor_get(x_16, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_16);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
lean_dec(x_8);
lean_ctor_set(x_9, 0, x_14);
return x_9;
}
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_9, 1);
lean_inc(x_35);
lean_dec(x_9);
x_36 = lean_box(0);
if (lean_obj_tag(x_8) == 2)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_8, 2);
lean_inc(x_37);
lean_dec(x_8);
x_38 = l_Lean_Compiler_LCNF_getType(x_37, x_2, x_3, x_4, x_5, x_35);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = l_Lean_Compiler_LCNF_isArrowClass_x3f___redArg(x_39, x_5, x_40);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_44 = x_41;
} else {
 lean_dec_ref(x_41);
 x_44 = lean_box(0);
}
if (lean_is_scalar(x_44)) {
 x_45 = lean_alloc_ctor(0, 2, 0);
} else {
 x_45 = x_44;
}
lean_ctor_set(x_45, 0, x_36);
lean_ctor_set(x_45, 1, x_43);
return x_45;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_42);
x_46 = lean_ctor_get(x_41, 1);
lean_inc(x_46);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_47 = x_41;
} else {
 lean_dec_ref(x_41);
 x_47 = lean_box(0);
}
x_48 = lean_box(1);
if (lean_is_scalar(x_47)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_47;
}
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_46);
return x_49;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_50 = lean_ctor_get(x_38, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_38, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_52 = x_38;
} else {
 lean_dec_ref(x_38);
 x_52 = lean_box(0);
}
if (lean_is_scalar(x_52)) {
 x_53 = lean_alloc_ctor(1, 2, 0);
} else {
 x_53 = x_52;
}
lean_ctor_set(x_53, 0, x_50);
lean_ctor_set(x_53, 1, x_51);
return x_53;
}
}
else
{
lean_object* x_54; 
lean_dec(x_8);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_36);
lean_ctor_set(x_54, 1, x_35);
return x_54;
}
}
}
else
{
uint8_t x_55; 
lean_dec(x_10);
lean_dec(x_8);
x_55 = !lean_is_exclusive(x_9);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_9, 0);
lean_dec(x_56);
x_57 = lean_box(1);
lean_ctor_set(x_9, 0, x_57);
return x_9;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_9, 1);
lean_inc(x_58);
lean_dec(x_9);
x_59 = lean_box(1);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_58);
return x_60;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_ignore_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_FloatLetIn_ignore_x3f___redArg(x_1, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_ignore_x3f___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_FloatLetIn_ignore_x3f___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_ignore_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_FloatLetIn_ignore_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_14; uint8_t x_15; 
x_14 = lean_st_ref_get(x_3, x_4);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_94; lean_object* x_95; uint64_t x_96; uint64_t x_97; uint64_t x_98; uint64_t x_99; uint64_t x_100; uint64_t x_101; uint64_t x_102; size_t x_103; size_t x_104; size_t x_105; size_t x_106; size_t x_107; lean_object* x_108; lean_object* x_109; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
x_94 = lean_ctor_get(x_16, 1);
lean_inc(x_94);
lean_dec(x_16);
x_95 = lean_array_get_size(x_94);
x_96 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1561_(x_2);
x_97 = 32;
x_98 = lean_uint64_shift_right(x_96, x_97);
x_99 = lean_uint64_xor(x_96, x_98);
x_100 = 16;
x_101 = lean_uint64_shift_right(x_99, x_100);
x_102 = lean_uint64_xor(x_99, x_101);
x_103 = lean_uint64_to_usize(x_102);
x_104 = lean_usize_of_nat(x_95);
lean_dec(x_95);
x_105 = 1;
x_106 = lean_usize_sub(x_104, x_105);
x_107 = lean_usize_land(x_103, x_106);
x_108 = lean_array_uget(x_94, x_107);
lean_dec(x_94);
x_109 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Compiler_LCNF_getType_spec__0___redArg(x_2, x_108);
lean_dec(x_108);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; 
lean_dec(x_2);
lean_dec(x_1);
x_110 = lean_box(0);
lean_ctor_set(x_14, 0, x_110);
return x_14;
}
else
{
lean_object* x_111; lean_object* x_112; uint8_t x_113; 
x_111 = lean_ctor_get(x_109, 0);
lean_inc(x_111);
lean_dec(x_109);
x_112 = lean_box(3);
x_113 = l_Lean_Compiler_LCNF_FloatLetIn_beqDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_73_(x_111, x_112);
if (x_113 == 0)
{
uint8_t x_114; 
x_114 = l_Lean_Compiler_LCNF_FloatLetIn_beqDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_73_(x_111, x_1);
lean_dec(x_1);
lean_dec(x_111);
if (x_114 == 0)
{
lean_free_object(x_14);
goto block_93;
}
else
{
if (x_113 == 0)
{
lean_object* x_115; 
lean_dec(x_2);
x_115 = lean_box(0);
lean_ctor_set(x_14, 0, x_115);
return x_14;
}
else
{
lean_free_object(x_14);
goto block_93;
}
}
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; uint8_t x_119; 
lean_dec(x_111);
lean_free_object(x_14);
x_116 = lean_st_ref_take(x_3, x_17);
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_116, 1);
lean_inc(x_118);
lean_dec(x_116);
x_119 = !lean_is_exclusive(x_117);
if (x_119 == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_130; size_t x_131; size_t x_132; size_t x_133; lean_object* x_134; uint8_t x_135; 
x_120 = lean_ctor_get(x_117, 0);
x_121 = lean_ctor_get(x_117, 1);
x_122 = lean_box(0);
x_130 = lean_array_get_size(x_121);
x_131 = lean_usize_of_nat(x_130);
lean_dec(x_130);
x_132 = lean_usize_sub(x_131, x_105);
x_133 = lean_usize_land(x_103, x_132);
x_134 = lean_array_uget(x_121, x_133);
x_135 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__0___redArg(x_2, x_134);
if (x_135 == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; uint8_t x_145; 
x_136 = lean_unsigned_to_nat(1u);
x_137 = lean_nat_add(x_120, x_136);
lean_dec(x_120);
x_138 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_138, 0, x_2);
lean_ctor_set(x_138, 1, x_1);
lean_ctor_set(x_138, 2, x_134);
x_139 = lean_array_uset(x_121, x_133, x_138);
x_140 = lean_unsigned_to_nat(4u);
x_141 = lean_nat_mul(x_137, x_140);
x_142 = lean_unsigned_to_nat(3u);
x_143 = lean_nat_div(x_141, x_142);
lean_dec(x_141);
x_144 = lean_array_get_size(x_139);
x_145 = lean_nat_dec_le(x_143, x_144);
lean_dec(x_144);
lean_dec(x_143);
if (x_145 == 0)
{
lean_object* x_146; 
x_146 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__1___redArg(x_139);
lean_ctor_set(x_117, 1, x_146);
lean_ctor_set(x_117, 0, x_137);
x_123 = x_117;
goto block_129;
}
else
{
lean_ctor_set(x_117, 1, x_139);
lean_ctor_set(x_117, 0, x_137);
x_123 = x_117;
goto block_129;
}
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_147 = lean_box(0);
x_148 = lean_array_uset(x_121, x_133, x_147);
x_149 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_LCtx_addParam_spec__0___redArg(x_2, x_1, x_134);
x_150 = lean_array_uset(x_148, x_133, x_149);
lean_ctor_set(x_117, 1, x_150);
x_123 = x_117;
goto block_129;
}
block_129:
{
lean_object* x_124; uint8_t x_125; 
x_124 = lean_st_ref_set(x_3, x_123, x_118);
x_125 = !lean_is_exclusive(x_124);
if (x_125 == 0)
{
lean_object* x_126; 
x_126 = lean_ctor_get(x_124, 0);
lean_dec(x_126);
lean_ctor_set(x_124, 0, x_122);
return x_124;
}
else
{
lean_object* x_127; lean_object* x_128; 
x_127 = lean_ctor_get(x_124, 1);
lean_inc(x_127);
lean_dec(x_124);
x_128 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_128, 0, x_122);
lean_ctor_set(x_128, 1, x_127);
return x_128;
}
}
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_160; size_t x_161; size_t x_162; size_t x_163; lean_object* x_164; uint8_t x_165; 
x_151 = lean_ctor_get(x_117, 0);
x_152 = lean_ctor_get(x_117, 1);
lean_inc(x_152);
lean_inc(x_151);
lean_dec(x_117);
x_153 = lean_box(0);
x_160 = lean_array_get_size(x_152);
x_161 = lean_usize_of_nat(x_160);
lean_dec(x_160);
x_162 = lean_usize_sub(x_161, x_105);
x_163 = lean_usize_land(x_103, x_162);
x_164 = lean_array_uget(x_152, x_163);
x_165 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__0___redArg(x_2, x_164);
if (x_165 == 0)
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; uint8_t x_175; 
x_166 = lean_unsigned_to_nat(1u);
x_167 = lean_nat_add(x_151, x_166);
lean_dec(x_151);
x_168 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_168, 0, x_2);
lean_ctor_set(x_168, 1, x_1);
lean_ctor_set(x_168, 2, x_164);
x_169 = lean_array_uset(x_152, x_163, x_168);
x_170 = lean_unsigned_to_nat(4u);
x_171 = lean_nat_mul(x_167, x_170);
x_172 = lean_unsigned_to_nat(3u);
x_173 = lean_nat_div(x_171, x_172);
lean_dec(x_171);
x_174 = lean_array_get_size(x_169);
x_175 = lean_nat_dec_le(x_173, x_174);
lean_dec(x_174);
lean_dec(x_173);
if (x_175 == 0)
{
lean_object* x_176; lean_object* x_177; 
x_176 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__1___redArg(x_169);
x_177 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_177, 0, x_167);
lean_ctor_set(x_177, 1, x_176);
x_154 = x_177;
goto block_159;
}
else
{
lean_object* x_178; 
x_178 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_178, 0, x_167);
lean_ctor_set(x_178, 1, x_169);
x_154 = x_178;
goto block_159;
}
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_179 = lean_box(0);
x_180 = lean_array_uset(x_152, x_163, x_179);
x_181 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_LCtx_addParam_spec__0___redArg(x_2, x_1, x_164);
x_182 = lean_array_uset(x_180, x_163, x_181);
x_183 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_183, 0, x_151);
lean_ctor_set(x_183, 1, x_182);
x_154 = x_183;
goto block_159;
}
block_159:
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_155 = lean_st_ref_set(x_3, x_154, x_118);
x_156 = lean_ctor_get(x_155, 1);
lean_inc(x_156);
if (lean_is_exclusive(x_155)) {
 lean_ctor_release(x_155, 0);
 lean_ctor_release(x_155, 1);
 x_157 = x_155;
} else {
 lean_dec_ref(x_155);
 x_157 = lean_box(0);
}
if (lean_is_scalar(x_157)) {
 x_158 = lean_alloc_ctor(0, 2, 0);
} else {
 x_158 = x_157;
}
lean_ctor_set(x_158, 0, x_153);
lean_ctor_set(x_158, 1, x_156);
return x_158;
}
}
}
}
block_93:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_st_ref_take(x_3, x_17);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = !lean_is_exclusive(x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint64_t x_27; uint64_t x_28; uint64_t x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; uint64_t x_33; size_t x_34; size_t x_35; size_t x_36; size_t x_37; size_t x_38; lean_object* x_39; uint8_t x_40; 
x_22 = lean_ctor_get(x_19, 0);
x_23 = lean_ctor_get(x_19, 1);
x_24 = lean_box(0);
x_25 = lean_box(2);
x_26 = lean_array_get_size(x_23);
x_27 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1561_(x_2);
x_28 = 32;
x_29 = lean_uint64_shift_right(x_27, x_28);
x_30 = lean_uint64_xor(x_27, x_29);
x_31 = 16;
x_32 = lean_uint64_shift_right(x_30, x_31);
x_33 = lean_uint64_xor(x_30, x_32);
x_34 = lean_uint64_to_usize(x_33);
x_35 = lean_usize_of_nat(x_26);
lean_dec(x_26);
x_36 = 1;
x_37 = lean_usize_sub(x_35, x_36);
x_38 = lean_usize_land(x_34, x_37);
x_39 = lean_array_uget(x_23, x_38);
x_40 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__0___redArg(x_2, x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_41 = lean_unsigned_to_nat(1u);
x_42 = lean_nat_add(x_22, x_41);
lean_dec(x_22);
x_43 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_43, 0, x_2);
lean_ctor_set(x_43, 1, x_25);
lean_ctor_set(x_43, 2, x_39);
x_44 = lean_array_uset(x_23, x_38, x_43);
x_45 = lean_unsigned_to_nat(4u);
x_46 = lean_nat_mul(x_42, x_45);
x_47 = lean_unsigned_to_nat(3u);
x_48 = lean_nat_div(x_46, x_47);
lean_dec(x_46);
x_49 = lean_array_get_size(x_44);
x_50 = lean_nat_dec_le(x_48, x_49);
lean_dec(x_49);
lean_dec(x_48);
if (x_50 == 0)
{
lean_object* x_51; 
x_51 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__1___redArg(x_44);
lean_ctor_set(x_19, 1, x_51);
lean_ctor_set(x_19, 0, x_42);
x_5 = x_24;
x_6 = x_20;
x_7 = x_19;
goto block_13;
}
else
{
lean_ctor_set(x_19, 1, x_44);
lean_ctor_set(x_19, 0, x_42);
x_5 = x_24;
x_6 = x_20;
x_7 = x_19;
goto block_13;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_52 = lean_box(0);
x_53 = lean_array_uset(x_23, x_38, x_52);
x_54 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_LCtx_addParam_spec__0___redArg(x_2, x_25, x_39);
x_55 = lean_array_uset(x_53, x_38, x_54);
lean_ctor_set(x_19, 1, x_55);
x_5 = x_24;
x_6 = x_20;
x_7 = x_19;
goto block_13;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint64_t x_61; uint64_t x_62; uint64_t x_63; uint64_t x_64; uint64_t x_65; uint64_t x_66; uint64_t x_67; size_t x_68; size_t x_69; size_t x_70; size_t x_71; size_t x_72; lean_object* x_73; uint8_t x_74; 
x_56 = lean_ctor_get(x_19, 0);
x_57 = lean_ctor_get(x_19, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_19);
x_58 = lean_box(0);
x_59 = lean_box(2);
x_60 = lean_array_get_size(x_57);
x_61 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1561_(x_2);
x_62 = 32;
x_63 = lean_uint64_shift_right(x_61, x_62);
x_64 = lean_uint64_xor(x_61, x_63);
x_65 = 16;
x_66 = lean_uint64_shift_right(x_64, x_65);
x_67 = lean_uint64_xor(x_64, x_66);
x_68 = lean_uint64_to_usize(x_67);
x_69 = lean_usize_of_nat(x_60);
lean_dec(x_60);
x_70 = 1;
x_71 = lean_usize_sub(x_69, x_70);
x_72 = lean_usize_land(x_68, x_71);
x_73 = lean_array_uget(x_57, x_72);
x_74 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__0___redArg(x_2, x_73);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_75 = lean_unsigned_to_nat(1u);
x_76 = lean_nat_add(x_56, x_75);
lean_dec(x_56);
x_77 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_77, 0, x_2);
lean_ctor_set(x_77, 1, x_59);
lean_ctor_set(x_77, 2, x_73);
x_78 = lean_array_uset(x_57, x_72, x_77);
x_79 = lean_unsigned_to_nat(4u);
x_80 = lean_nat_mul(x_76, x_79);
x_81 = lean_unsigned_to_nat(3u);
x_82 = lean_nat_div(x_80, x_81);
lean_dec(x_80);
x_83 = lean_array_get_size(x_78);
x_84 = lean_nat_dec_le(x_82, x_83);
lean_dec(x_83);
lean_dec(x_82);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; 
x_85 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__1___redArg(x_78);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_76);
lean_ctor_set(x_86, 1, x_85);
x_5 = x_58;
x_6 = x_20;
x_7 = x_86;
goto block_13;
}
else
{
lean_object* x_87; 
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_76);
lean_ctor_set(x_87, 1, x_78);
x_5 = x_58;
x_6 = x_20;
x_7 = x_87;
goto block_13;
}
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_88 = lean_box(0);
x_89 = lean_array_uset(x_57, x_72, x_88);
x_90 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_LCtx_addParam_spec__0___redArg(x_2, x_59, x_73);
x_91 = lean_array_uset(x_89, x_72, x_90);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_56);
lean_ctor_set(x_92, 1, x_91);
x_5 = x_58;
x_6 = x_20;
x_7 = x_92;
goto block_13;
}
}
}
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_228; lean_object* x_229; uint64_t x_230; uint64_t x_231; uint64_t x_232; uint64_t x_233; uint64_t x_234; uint64_t x_235; uint64_t x_236; size_t x_237; size_t x_238; size_t x_239; size_t x_240; size_t x_241; lean_object* x_242; lean_object* x_243; 
x_184 = lean_ctor_get(x_14, 0);
x_185 = lean_ctor_get(x_14, 1);
lean_inc(x_185);
lean_inc(x_184);
lean_dec(x_14);
x_228 = lean_ctor_get(x_184, 1);
lean_inc(x_228);
lean_dec(x_184);
x_229 = lean_array_get_size(x_228);
x_230 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1561_(x_2);
x_231 = 32;
x_232 = lean_uint64_shift_right(x_230, x_231);
x_233 = lean_uint64_xor(x_230, x_232);
x_234 = 16;
x_235 = lean_uint64_shift_right(x_233, x_234);
x_236 = lean_uint64_xor(x_233, x_235);
x_237 = lean_uint64_to_usize(x_236);
x_238 = lean_usize_of_nat(x_229);
lean_dec(x_229);
x_239 = 1;
x_240 = lean_usize_sub(x_238, x_239);
x_241 = lean_usize_land(x_237, x_240);
x_242 = lean_array_uget(x_228, x_241);
lean_dec(x_228);
x_243 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Compiler_LCNF_getType_spec__0___redArg(x_2, x_242);
lean_dec(x_242);
if (lean_obj_tag(x_243) == 0)
{
lean_object* x_244; lean_object* x_245; 
lean_dec(x_2);
lean_dec(x_1);
x_244 = lean_box(0);
x_245 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_245, 0, x_244);
lean_ctor_set(x_245, 1, x_185);
return x_245;
}
else
{
lean_object* x_246; lean_object* x_247; uint8_t x_248; 
x_246 = lean_ctor_get(x_243, 0);
lean_inc(x_246);
lean_dec(x_243);
x_247 = lean_box(3);
x_248 = l_Lean_Compiler_LCNF_FloatLetIn_beqDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_73_(x_246, x_247);
if (x_248 == 0)
{
uint8_t x_249; 
x_249 = l_Lean_Compiler_LCNF_FloatLetIn_beqDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_73_(x_246, x_1);
lean_dec(x_1);
lean_dec(x_246);
if (x_249 == 0)
{
goto block_227;
}
else
{
if (x_248 == 0)
{
lean_object* x_250; lean_object* x_251; 
lean_dec(x_2);
x_250 = lean_box(0);
x_251 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_251, 0, x_250);
lean_ctor_set(x_251, 1, x_185);
return x_251;
}
else
{
goto block_227;
}
}
}
else
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_265; size_t x_266; size_t x_267; size_t x_268; lean_object* x_269; uint8_t x_270; 
lean_dec(x_246);
x_252 = lean_st_ref_take(x_3, x_185);
x_253 = lean_ctor_get(x_252, 0);
lean_inc(x_253);
x_254 = lean_ctor_get(x_252, 1);
lean_inc(x_254);
lean_dec(x_252);
x_255 = lean_ctor_get(x_253, 0);
lean_inc(x_255);
x_256 = lean_ctor_get(x_253, 1);
lean_inc(x_256);
if (lean_is_exclusive(x_253)) {
 lean_ctor_release(x_253, 0);
 lean_ctor_release(x_253, 1);
 x_257 = x_253;
} else {
 lean_dec_ref(x_253);
 x_257 = lean_box(0);
}
x_258 = lean_box(0);
x_265 = lean_array_get_size(x_256);
x_266 = lean_usize_of_nat(x_265);
lean_dec(x_265);
x_267 = lean_usize_sub(x_266, x_239);
x_268 = lean_usize_land(x_237, x_267);
x_269 = lean_array_uget(x_256, x_268);
x_270 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__0___redArg(x_2, x_269);
if (x_270 == 0)
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; uint8_t x_280; 
x_271 = lean_unsigned_to_nat(1u);
x_272 = lean_nat_add(x_255, x_271);
lean_dec(x_255);
x_273 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_273, 0, x_2);
lean_ctor_set(x_273, 1, x_1);
lean_ctor_set(x_273, 2, x_269);
x_274 = lean_array_uset(x_256, x_268, x_273);
x_275 = lean_unsigned_to_nat(4u);
x_276 = lean_nat_mul(x_272, x_275);
x_277 = lean_unsigned_to_nat(3u);
x_278 = lean_nat_div(x_276, x_277);
lean_dec(x_276);
x_279 = lean_array_get_size(x_274);
x_280 = lean_nat_dec_le(x_278, x_279);
lean_dec(x_279);
lean_dec(x_278);
if (x_280 == 0)
{
lean_object* x_281; lean_object* x_282; 
x_281 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__1___redArg(x_274);
if (lean_is_scalar(x_257)) {
 x_282 = lean_alloc_ctor(0, 2, 0);
} else {
 x_282 = x_257;
}
lean_ctor_set(x_282, 0, x_272);
lean_ctor_set(x_282, 1, x_281);
x_259 = x_282;
goto block_264;
}
else
{
lean_object* x_283; 
if (lean_is_scalar(x_257)) {
 x_283 = lean_alloc_ctor(0, 2, 0);
} else {
 x_283 = x_257;
}
lean_ctor_set(x_283, 0, x_272);
lean_ctor_set(x_283, 1, x_274);
x_259 = x_283;
goto block_264;
}
}
else
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; 
x_284 = lean_box(0);
x_285 = lean_array_uset(x_256, x_268, x_284);
x_286 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_LCtx_addParam_spec__0___redArg(x_2, x_1, x_269);
x_287 = lean_array_uset(x_285, x_268, x_286);
if (lean_is_scalar(x_257)) {
 x_288 = lean_alloc_ctor(0, 2, 0);
} else {
 x_288 = x_257;
}
lean_ctor_set(x_288, 0, x_255);
lean_ctor_set(x_288, 1, x_287);
x_259 = x_288;
goto block_264;
}
block_264:
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; 
x_260 = lean_st_ref_set(x_3, x_259, x_254);
x_261 = lean_ctor_get(x_260, 1);
lean_inc(x_261);
if (lean_is_exclusive(x_260)) {
 lean_ctor_release(x_260, 0);
 lean_ctor_release(x_260, 1);
 x_262 = x_260;
} else {
 lean_dec_ref(x_260);
 x_262 = lean_box(0);
}
if (lean_is_scalar(x_262)) {
 x_263 = lean_alloc_ctor(0, 2, 0);
} else {
 x_263 = x_262;
}
lean_ctor_set(x_263, 0, x_258);
lean_ctor_set(x_263, 1, x_261);
return x_263;
}
}
}
block_227:
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; uint64_t x_195; uint64_t x_196; uint64_t x_197; uint64_t x_198; uint64_t x_199; uint64_t x_200; uint64_t x_201; size_t x_202; size_t x_203; size_t x_204; size_t x_205; size_t x_206; lean_object* x_207; uint8_t x_208; 
x_186 = lean_st_ref_take(x_3, x_185);
x_187 = lean_ctor_get(x_186, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_186, 1);
lean_inc(x_188);
lean_dec(x_186);
x_189 = lean_ctor_get(x_187, 0);
lean_inc(x_189);
x_190 = lean_ctor_get(x_187, 1);
lean_inc(x_190);
if (lean_is_exclusive(x_187)) {
 lean_ctor_release(x_187, 0);
 lean_ctor_release(x_187, 1);
 x_191 = x_187;
} else {
 lean_dec_ref(x_187);
 x_191 = lean_box(0);
}
x_192 = lean_box(0);
x_193 = lean_box(2);
x_194 = lean_array_get_size(x_190);
x_195 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1561_(x_2);
x_196 = 32;
x_197 = lean_uint64_shift_right(x_195, x_196);
x_198 = lean_uint64_xor(x_195, x_197);
x_199 = 16;
x_200 = lean_uint64_shift_right(x_198, x_199);
x_201 = lean_uint64_xor(x_198, x_200);
x_202 = lean_uint64_to_usize(x_201);
x_203 = lean_usize_of_nat(x_194);
lean_dec(x_194);
x_204 = 1;
x_205 = lean_usize_sub(x_203, x_204);
x_206 = lean_usize_land(x_202, x_205);
x_207 = lean_array_uget(x_190, x_206);
x_208 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__0___redArg(x_2, x_207);
if (x_208 == 0)
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; uint8_t x_218; 
x_209 = lean_unsigned_to_nat(1u);
x_210 = lean_nat_add(x_189, x_209);
lean_dec(x_189);
x_211 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_211, 0, x_2);
lean_ctor_set(x_211, 1, x_193);
lean_ctor_set(x_211, 2, x_207);
x_212 = lean_array_uset(x_190, x_206, x_211);
x_213 = lean_unsigned_to_nat(4u);
x_214 = lean_nat_mul(x_210, x_213);
x_215 = lean_unsigned_to_nat(3u);
x_216 = lean_nat_div(x_214, x_215);
lean_dec(x_214);
x_217 = lean_array_get_size(x_212);
x_218 = lean_nat_dec_le(x_216, x_217);
lean_dec(x_217);
lean_dec(x_216);
if (x_218 == 0)
{
lean_object* x_219; lean_object* x_220; 
x_219 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__1___redArg(x_212);
if (lean_is_scalar(x_191)) {
 x_220 = lean_alloc_ctor(0, 2, 0);
} else {
 x_220 = x_191;
}
lean_ctor_set(x_220, 0, x_210);
lean_ctor_set(x_220, 1, x_219);
x_5 = x_192;
x_6 = x_188;
x_7 = x_220;
goto block_13;
}
else
{
lean_object* x_221; 
if (lean_is_scalar(x_191)) {
 x_221 = lean_alloc_ctor(0, 2, 0);
} else {
 x_221 = x_191;
}
lean_ctor_set(x_221, 0, x_210);
lean_ctor_set(x_221, 1, x_212);
x_5 = x_192;
x_6 = x_188;
x_7 = x_221;
goto block_13;
}
}
else
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; 
x_222 = lean_box(0);
x_223 = lean_array_uset(x_190, x_206, x_222);
x_224 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_LCtx_addParam_spec__0___redArg(x_2, x_193, x_207);
x_225 = lean_array_uset(x_223, x_206, x_224);
if (lean_is_scalar(x_191)) {
 x_226 = lean_alloc_ctor(0, 2, 0);
} else {
 x_226 = x_191;
}
lean_ctor_set(x_226, 0, x_189);
lean_ctor_set(x_226, 1, x_225);
x_5 = x_192;
x_6 = x_188;
x_7 = x_226;
goto block_13;
}
}
}
block_13:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_st_ref_set(x_3, x_7, x_6);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_8, 0);
lean_dec(x_10);
lean_ctor_set(x_8, 0, x_5);
return x_8;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_dec(x_8);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_5);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___redArg(x_1, x_2, x_3, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
static lean_object* _init_l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Param_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_instMonadEIO(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Param_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__0___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__0___boxed), 5, 0);
return x_1;
}
}
static lean_object* _init_l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Param_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__0___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__1), 7, 0);
return x_1;
}
}
static lean_object* _init_l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Param_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__0___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed), 7, 0);
return x_1;
}
}
static lean_object* _init_l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Param_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__0___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Param_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Param_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__0___closed__0;
x_10 = l_ReaderT_instMonad___redArg(x_9);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
lean_dec(x_13);
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_15 = lean_ctor_get(x_12, 0);
x_16 = lean_ctor_get(x_12, 2);
x_17 = lean_ctor_get(x_12, 3);
x_18 = lean_ctor_get(x_12, 4);
x_19 = lean_ctor_get(x_12, 1);
lean_dec(x_19);
x_20 = l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Param_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__0___closed__1;
x_21 = l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Param_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__0___closed__2;
lean_inc(x_15);
x_22 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_22, 0, x_15);
x_23 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_23, 0, x_15);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_25, 0, x_18);
x_26 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_26, 0, x_17);
x_27 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_27, 0, x_16);
lean_ctor_set(x_12, 4, x_25);
lean_ctor_set(x_12, 3, x_26);
lean_ctor_set(x_12, 2, x_27);
lean_ctor_set(x_12, 1, x_20);
lean_ctor_set(x_12, 0, x_24);
lean_ctor_set(x_10, 1, x_21);
x_28 = l_ReaderT_instMonad___redArg(x_10);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_30 = lean_ctor_get(x_28, 0);
x_31 = lean_ctor_get(x_28, 1);
lean_dec(x_31);
x_32 = !lean_is_exclusive(x_30);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_33 = lean_ctor_get(x_30, 0);
x_34 = lean_ctor_get(x_30, 2);
x_35 = lean_ctor_get(x_30, 3);
x_36 = lean_ctor_get(x_30, 4);
x_37 = lean_ctor_get(x_30, 1);
lean_dec(x_37);
x_38 = l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Param_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__0___closed__3;
x_39 = l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Param_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__0___closed__4;
lean_inc(x_33);
x_40 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_40, 0, x_33);
x_41 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_41, 0, x_33);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_43, 0, x_36);
x_44 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_44, 0, x_35);
x_45 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_45, 0, x_34);
lean_ctor_set(x_30, 4, x_43);
lean_ctor_set(x_30, 3, x_44);
lean_ctor_set(x_30, 2, x_45);
lean_ctor_set(x_30, 1, x_38);
lean_ctor_set(x_30, 0, x_42);
lean_ctor_set(x_28, 1, x_39);
x_46 = l_ReaderT_instMonad___redArg(x_28);
x_47 = l_ReaderT_instMonad___redArg(x_46);
x_48 = lean_box(0);
x_49 = l_instInhabitedOfMonad___redArg(x_47, x_48);
x_50 = lean_panic_fn(x_49, x_1);
x_51 = lean_apply_7(x_50, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_51;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_52 = lean_ctor_get(x_30, 0);
x_53 = lean_ctor_get(x_30, 2);
x_54 = lean_ctor_get(x_30, 3);
x_55 = lean_ctor_get(x_30, 4);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_30);
x_56 = l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Param_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__0___closed__3;
x_57 = l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Param_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__0___closed__4;
lean_inc(x_52);
x_58 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_58, 0, x_52);
x_59 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_59, 0, x_52);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
x_61 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_61, 0, x_55);
x_62 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_62, 0, x_54);
x_63 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_63, 0, x_53);
x_64 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_64, 0, x_60);
lean_ctor_set(x_64, 1, x_56);
lean_ctor_set(x_64, 2, x_63);
lean_ctor_set(x_64, 3, x_62);
lean_ctor_set(x_64, 4, x_61);
lean_ctor_set(x_28, 1, x_57);
lean_ctor_set(x_28, 0, x_64);
x_65 = l_ReaderT_instMonad___redArg(x_28);
x_66 = l_ReaderT_instMonad___redArg(x_65);
x_67 = lean_box(0);
x_68 = l_instInhabitedOfMonad___redArg(x_66, x_67);
x_69 = lean_panic_fn(x_68, x_1);
x_70 = lean_apply_7(x_69, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_70;
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_71 = lean_ctor_get(x_28, 0);
lean_inc(x_71);
lean_dec(x_28);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 2);
lean_inc(x_73);
x_74 = lean_ctor_get(x_71, 3);
lean_inc(x_74);
x_75 = lean_ctor_get(x_71, 4);
lean_inc(x_75);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 lean_ctor_release(x_71, 2);
 lean_ctor_release(x_71, 3);
 lean_ctor_release(x_71, 4);
 x_76 = x_71;
} else {
 lean_dec_ref(x_71);
 x_76 = lean_box(0);
}
x_77 = l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Param_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__0___closed__3;
x_78 = l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Param_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__0___closed__4;
lean_inc(x_72);
x_79 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_79, 0, x_72);
x_80 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_80, 0, x_72);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
x_82 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_82, 0, x_75);
x_83 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_83, 0, x_74);
x_84 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_84, 0, x_73);
if (lean_is_scalar(x_76)) {
 x_85 = lean_alloc_ctor(0, 5, 0);
} else {
 x_85 = x_76;
}
lean_ctor_set(x_85, 0, x_81);
lean_ctor_set(x_85, 1, x_77);
lean_ctor_set(x_85, 2, x_84);
lean_ctor_set(x_85, 3, x_83);
lean_ctor_set(x_85, 4, x_82);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_78);
x_87 = l_ReaderT_instMonad___redArg(x_86);
x_88 = l_ReaderT_instMonad___redArg(x_87);
x_89 = lean_box(0);
x_90 = l_instInhabitedOfMonad___redArg(x_88, x_89);
x_91 = lean_panic_fn(x_90, x_1);
x_92 = lean_apply_7(x_91, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_92;
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_93 = lean_ctor_get(x_12, 0);
x_94 = lean_ctor_get(x_12, 2);
x_95 = lean_ctor_get(x_12, 3);
x_96 = lean_ctor_get(x_12, 4);
lean_inc(x_96);
lean_inc(x_95);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_12);
x_97 = l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Param_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__0___closed__1;
x_98 = l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Param_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__0___closed__2;
lean_inc(x_93);
x_99 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_99, 0, x_93);
x_100 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_100, 0, x_93);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
x_102 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_102, 0, x_96);
x_103 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_103, 0, x_95);
x_104 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_104, 0, x_94);
x_105 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_105, 0, x_101);
lean_ctor_set(x_105, 1, x_97);
lean_ctor_set(x_105, 2, x_104);
lean_ctor_set(x_105, 3, x_103);
lean_ctor_set(x_105, 4, x_102);
lean_ctor_set(x_10, 1, x_98);
lean_ctor_set(x_10, 0, x_105);
x_106 = l_ReaderT_instMonad___redArg(x_10);
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
if (lean_is_exclusive(x_106)) {
 lean_ctor_release(x_106, 0);
 lean_ctor_release(x_106, 1);
 x_108 = x_106;
} else {
 lean_dec_ref(x_106);
 x_108 = lean_box(0);
}
x_109 = lean_ctor_get(x_107, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_107, 2);
lean_inc(x_110);
x_111 = lean_ctor_get(x_107, 3);
lean_inc(x_111);
x_112 = lean_ctor_get(x_107, 4);
lean_inc(x_112);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 lean_ctor_release(x_107, 2);
 lean_ctor_release(x_107, 3);
 lean_ctor_release(x_107, 4);
 x_113 = x_107;
} else {
 lean_dec_ref(x_107);
 x_113 = lean_box(0);
}
x_114 = l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Param_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__0___closed__3;
x_115 = l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Param_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__0___closed__4;
lean_inc(x_109);
x_116 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_116, 0, x_109);
x_117 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_117, 0, x_109);
x_118 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set(x_118, 1, x_117);
x_119 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_119, 0, x_112);
x_120 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_120, 0, x_111);
x_121 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_121, 0, x_110);
if (lean_is_scalar(x_113)) {
 x_122 = lean_alloc_ctor(0, 5, 0);
} else {
 x_122 = x_113;
}
lean_ctor_set(x_122, 0, x_118);
lean_ctor_set(x_122, 1, x_114);
lean_ctor_set(x_122, 2, x_121);
lean_ctor_set(x_122, 3, x_120);
lean_ctor_set(x_122, 4, x_119);
if (lean_is_scalar(x_108)) {
 x_123 = lean_alloc_ctor(0, 2, 0);
} else {
 x_123 = x_108;
}
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_115);
x_124 = l_ReaderT_instMonad___redArg(x_123);
x_125 = l_ReaderT_instMonad___redArg(x_124);
x_126 = lean_box(0);
x_127 = l_instInhabitedOfMonad___redArg(x_125, x_126);
x_128 = lean_panic_fn(x_127, x_1);
x_129 = lean_apply_7(x_128, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_129;
}
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_130 = lean_ctor_get(x_10, 0);
lean_inc(x_130);
lean_dec(x_10);
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_130, 2);
lean_inc(x_132);
x_133 = lean_ctor_get(x_130, 3);
lean_inc(x_133);
x_134 = lean_ctor_get(x_130, 4);
lean_inc(x_134);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 lean_ctor_release(x_130, 2);
 lean_ctor_release(x_130, 3);
 lean_ctor_release(x_130, 4);
 x_135 = x_130;
} else {
 lean_dec_ref(x_130);
 x_135 = lean_box(0);
}
x_136 = l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Param_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__0___closed__1;
x_137 = l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Param_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__0___closed__2;
lean_inc(x_131);
x_138 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_138, 0, x_131);
x_139 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_139, 0, x_131);
x_140 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_140, 0, x_138);
lean_ctor_set(x_140, 1, x_139);
x_141 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_141, 0, x_134);
x_142 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_142, 0, x_133);
x_143 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_143, 0, x_132);
if (lean_is_scalar(x_135)) {
 x_144 = lean_alloc_ctor(0, 5, 0);
} else {
 x_144 = x_135;
}
lean_ctor_set(x_144, 0, x_140);
lean_ctor_set(x_144, 1, x_136);
lean_ctor_set(x_144, 2, x_143);
lean_ctor_set(x_144, 3, x_142);
lean_ctor_set(x_144, 4, x_141);
x_145 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_145, 0, x_144);
lean_ctor_set(x_145, 1, x_137);
x_146 = l_ReaderT_instMonad___redArg(x_145);
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
if (lean_is_exclusive(x_146)) {
 lean_ctor_release(x_146, 0);
 lean_ctor_release(x_146, 1);
 x_148 = x_146;
} else {
 lean_dec_ref(x_146);
 x_148 = lean_box(0);
}
x_149 = lean_ctor_get(x_147, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_147, 2);
lean_inc(x_150);
x_151 = lean_ctor_get(x_147, 3);
lean_inc(x_151);
x_152 = lean_ctor_get(x_147, 4);
lean_inc(x_152);
if (lean_is_exclusive(x_147)) {
 lean_ctor_release(x_147, 0);
 lean_ctor_release(x_147, 1);
 lean_ctor_release(x_147, 2);
 lean_ctor_release(x_147, 3);
 lean_ctor_release(x_147, 4);
 x_153 = x_147;
} else {
 lean_dec_ref(x_147);
 x_153 = lean_box(0);
}
x_154 = l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Param_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__0___closed__3;
x_155 = l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Param_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__0___closed__4;
lean_inc(x_149);
x_156 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_156, 0, x_149);
x_157 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_157, 0, x_149);
x_158 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_158, 0, x_156);
lean_ctor_set(x_158, 1, x_157);
x_159 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_159, 0, x_152);
x_160 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_160, 0, x_151);
x_161 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_161, 0, x_150);
if (lean_is_scalar(x_153)) {
 x_162 = lean_alloc_ctor(0, 5, 0);
} else {
 x_162 = x_153;
}
lean_ctor_set(x_162, 0, x_158);
lean_ctor_set(x_162, 1, x_154);
lean_ctor_set(x_162, 2, x_161);
lean_ctor_set(x_162, 3, x_160);
lean_ctor_set(x_162, 4, x_159);
if (lean_is_scalar(x_148)) {
 x_163 = lean_alloc_ctor(0, 2, 0);
} else {
 x_163 = x_148;
}
lean_ctor_set(x_163, 0, x_162);
lean_ctor_set(x_163, 1, x_155);
x_164 = l_ReaderT_instMonad___redArg(x_163);
x_165 = l_ReaderT_instMonad___redArg(x_164);
x_166 = lean_box(0);
x_167 = l_instInhabitedOfMonad___redArg(x_165, x_166);
x_168 = lean_panic_fn(x_167, x_1);
x_169 = lean_apply_7(x_168, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_169;
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Param_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Compiler.LCNF.FVarUtil", 27, 27);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Param_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Compiler.LCNF.Expr.forFVarM", 32, 32);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Param_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Param_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Param_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__2;
x_2 = lean_unsigned_to_nat(38u);
x_3 = lean_unsigned_to_nat(43u);
x_4 = l_Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Param_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__1;
x_5 = l_Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Param_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Param_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
switch (lean_obj_tag(x_2)) {
case 1:
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_2, 0);
lean_inc(x_16);
lean_dec(x_2);
x_17 = lean_apply_8(x_1, x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_17;
}
case 2:
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_2);
lean_dec(x_1);
x_18 = l_Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Param_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3;
x_19 = l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Param_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__0(x_18, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_19;
}
case 5:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_2, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_2, 1);
lean_inc(x_21);
lean_dec(x_2);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_22 = l_Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Param_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0(x_1, x_20, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_2 = x_21;
x_9 = x_23;
goto _start;
}
else
{
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_22;
}
}
case 6:
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_2, 1);
lean_inc(x_25);
x_26 = lean_ctor_get(x_2, 2);
lean_inc(x_26);
lean_dec(x_2);
x_10 = x_25;
x_11 = x_26;
goto block_15;
}
case 7:
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_2, 1);
lean_inc(x_27);
x_28 = lean_ctor_get(x_2, 2);
lean_inc(x_28);
lean_dec(x_2);
x_10 = x_27;
x_11 = x_28;
goto block_15;
}
case 8:
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_2);
lean_dec(x_1);
x_29 = l_Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Param_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3;
x_30 = l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Param_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__0(x_29, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_30;
}
case 11:
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_2);
lean_dec(x_1);
x_31 = l_Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Param_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3;
x_32 = l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Param_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__0(x_31, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_32;
}
default: 
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_9);
return x_34;
}
}
block_15:
{
lean_object* x_12; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_12 = l_Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Param_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_2 = x_11;
x_9 = x_13;
goto _start;
}
else
{
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_2, 2);
lean_inc(x_10);
lean_dec(x_2);
x_11 = l_Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Param_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_forCodeM___at___Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__3_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_1, 2);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_apply_8(x_2, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_apply_8(x_2, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_forFVarM___at___Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__3_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
case 1:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
lean_dec(x_2);
x_13 = lean_apply_8(x_1, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_13;
}
default: 
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_2, 0);
lean_inc(x_14);
lean_dec(x_2);
x_15 = l_Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Param_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0(x_1, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__3_spec__5(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_eq(x_3, x_4);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_5);
x_14 = lean_array_uget(x_2, x_3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_15 = l_Lean_Compiler_LCNF_Param_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0(x_1, x_14, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = 1;
x_19 = lean_usize_add(x_3, x_18);
x_3 = x_19;
x_5 = x_16;
x_12 = x_17;
goto _start;
}
else
{
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
return x_15;
}
}
else
{
lean_object* x_21; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_5);
lean_ctor_set(x_21, 1, x_12);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_LetValue_forFVarM___at___Lean_Compiler_LCNF_LetDecl_forFVarM___at___Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__3_spec__6_spec__6_spec__6(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_eq(x_3, x_4);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_5);
x_14 = lean_array_uget(x_2, x_3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_15 = l_Lean_Compiler_LCNF_Arg_forFVarM___at___Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__3_spec__4(x_1, x_14, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = 1;
x_19 = lean_usize_add(x_3, x_18);
x_3 = x_19;
x_5 = x_16;
x_12 = x_17;
goto _start;
}
else
{
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
return x_15;
}
}
else
{
lean_object* x_21; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_5);
lean_ctor_set(x_21, 1, x_12);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_forFVarM___at___Lean_Compiler_LCNF_LetDecl_forFVarM___at___Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__3_spec__6_spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 2:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_2, 2);
lean_inc(x_10);
lean_dec(x_2);
x_11 = lean_apply_8(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
case 3:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_ctor_get(x_2, 2);
lean_inc(x_12);
lean_dec(x_2);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_array_get_size(x_12);
x_15 = lean_box(0);
x_16 = lean_nat_dec_lt(x_13, x_14);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_9);
return x_17;
}
else
{
uint8_t x_18; 
x_18 = lean_nat_dec_le(x_14, x_14);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_15);
lean_ctor_set(x_19, 1, x_9);
return x_19;
}
else
{
size_t x_20; size_t x_21; lean_object* x_22; 
x_20 = 0;
x_21 = lean_usize_of_nat(x_14);
lean_dec(x_14);
x_22 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_LetValue_forFVarM___at___Lean_Compiler_LCNF_LetDecl_forFVarM___at___Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__3_spec__6_spec__6_spec__6(x_1, x_12, x_20, x_21, x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_12);
return x_22;
}
}
}
case 4:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_2, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_2, 1);
lean_inc(x_24);
lean_dec(x_2);
lean_inc(x_1);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_25 = lean_apply_8(x_1, x_23, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_27 = lean_ctor_get(x_25, 1);
x_28 = lean_ctor_get(x_25, 0);
lean_dec(x_28);
x_29 = lean_unsigned_to_nat(0u);
x_30 = lean_array_get_size(x_24);
x_31 = lean_box(0);
x_32 = lean_nat_dec_lt(x_29, x_30);
if (x_32 == 0)
{
lean_dec(x_30);
lean_dec(x_24);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
lean_ctor_set(x_25, 0, x_31);
return x_25;
}
else
{
uint8_t x_33; 
x_33 = lean_nat_dec_le(x_30, x_30);
if (x_33 == 0)
{
lean_dec(x_30);
lean_dec(x_24);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
lean_ctor_set(x_25, 0, x_31);
return x_25;
}
else
{
size_t x_34; size_t x_35; lean_object* x_36; 
lean_free_object(x_25);
x_34 = 0;
x_35 = lean_usize_of_nat(x_30);
lean_dec(x_30);
x_36 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_LetValue_forFVarM___at___Lean_Compiler_LCNF_LetDecl_forFVarM___at___Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__3_spec__6_spec__6_spec__6(x_1, x_24, x_34, x_35, x_31, x_3, x_4, x_5, x_6, x_7, x_8, x_27);
lean_dec(x_24);
return x_36;
}
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_37 = lean_ctor_get(x_25, 1);
lean_inc(x_37);
lean_dec(x_25);
x_38 = lean_unsigned_to_nat(0u);
x_39 = lean_array_get_size(x_24);
x_40 = lean_box(0);
x_41 = lean_nat_dec_lt(x_38, x_39);
if (x_41 == 0)
{
lean_object* x_42; 
lean_dec(x_39);
lean_dec(x_24);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_37);
return x_42;
}
else
{
uint8_t x_43; 
x_43 = lean_nat_dec_le(x_39, x_39);
if (x_43 == 0)
{
lean_object* x_44; 
lean_dec(x_39);
lean_dec(x_24);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_40);
lean_ctor_set(x_44, 1, x_37);
return x_44;
}
else
{
size_t x_45; size_t x_46; lean_object* x_47; 
x_45 = 0;
x_46 = lean_usize_of_nat(x_39);
lean_dec(x_39);
x_47 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_LetValue_forFVarM___at___Lean_Compiler_LCNF_LetDecl_forFVarM___at___Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__3_spec__6_spec__6_spec__6(x_1, x_24, x_45, x_46, x_40, x_3, x_4, x_5, x_6, x_7, x_8, x_37);
lean_dec(x_24);
return x_47;
}
}
}
}
else
{
lean_dec(x_24);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_25;
}
}
default: 
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_48 = lean_box(0);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_9);
return x_49;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_forFVarM___at___Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__3_spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_2, 2);
lean_inc(x_10);
x_11 = lean_ctor_get(x_2, 3);
lean_inc(x_11);
lean_dec(x_2);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_12 = l_Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Param_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = l_Lean_Compiler_LCNF_LetValue_forFVarM___at___Lean_Compiler_LCNF_LetDecl_forFVarM___at___Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__3_spec__6_spec__6(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_13);
return x_14;
}
else
{
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__3_spec__9___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__3_spec__9(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_eq(x_3, x_4);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_5);
lean_inc(x_1);
x_14 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__3_spec__9___lam__0), 9, 1);
lean_closure_set(x_14, 0, x_1);
x_15 = lean_array_uget(x_2, x_3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_16 = l_Lean_Compiler_LCNF_Alt_forCodeM___at___Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__3_spec__3(x_15, x_14, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = 1;
x_20 = lean_usize_add(x_3, x_19);
x_3 = x_20;
x_5 = x_17;
x_12 = x_18;
goto _start;
}
else
{
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
return x_16;
}
}
else
{
lean_object* x_22; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_5);
lean_ctor_set(x_22, 1, x_12);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__3___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_13 = l_Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Param_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0(x_1, x_2, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_15 = l_Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__3(x_1, x_3, x_6, x_7, x_8, x_9, x_10, x_11, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = l_Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__3(x_1, x_4, x_6, x_7, x_8, x_9, x_10, x_11, x_16);
return x_17;
}
else
{
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
return x_15;
}
}
else
{
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_2, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_2, 1);
lean_inc(x_34);
lean_dec(x_2);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_35 = l_Lean_Compiler_LCNF_LetDecl_forFVarM___at___Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__3_spec__6(x_1, x_33, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec(x_35);
x_2 = x_34;
x_9 = x_36;
goto _start;
}
else
{
lean_dec(x_34);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_35;
}
}
case 3:
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_2, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_2, 1);
lean_inc(x_39);
lean_dec(x_2);
lean_inc(x_1);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_40 = lean_apply_8(x_1, x_38, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_40) == 0)
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_42 = lean_ctor_get(x_40, 1);
x_43 = lean_ctor_get(x_40, 0);
lean_dec(x_43);
x_44 = lean_unsigned_to_nat(0u);
x_45 = lean_array_get_size(x_39);
x_46 = lean_box(0);
x_47 = lean_nat_dec_lt(x_44, x_45);
if (x_47 == 0)
{
lean_dec(x_45);
lean_dec(x_39);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
lean_ctor_set(x_40, 0, x_46);
return x_40;
}
else
{
uint8_t x_48; 
x_48 = lean_nat_dec_le(x_45, x_45);
if (x_48 == 0)
{
lean_dec(x_45);
lean_dec(x_39);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
lean_ctor_set(x_40, 0, x_46);
return x_40;
}
else
{
size_t x_49; size_t x_50; lean_object* x_51; 
lean_free_object(x_40);
x_49 = 0;
x_50 = lean_usize_of_nat(x_45);
lean_dec(x_45);
x_51 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_LetValue_forFVarM___at___Lean_Compiler_LCNF_LetDecl_forFVarM___at___Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__3_spec__6_spec__6_spec__6(x_1, x_39, x_49, x_50, x_46, x_3, x_4, x_5, x_6, x_7, x_8, x_42);
lean_dec(x_39);
return x_51;
}
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_52 = lean_ctor_get(x_40, 1);
lean_inc(x_52);
lean_dec(x_40);
x_53 = lean_unsigned_to_nat(0u);
x_54 = lean_array_get_size(x_39);
x_55 = lean_box(0);
x_56 = lean_nat_dec_lt(x_53, x_54);
if (x_56 == 0)
{
lean_object* x_57; 
lean_dec(x_54);
lean_dec(x_39);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_52);
return x_57;
}
else
{
uint8_t x_58; 
x_58 = lean_nat_dec_le(x_54, x_54);
if (x_58 == 0)
{
lean_object* x_59; 
lean_dec(x_54);
lean_dec(x_39);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_55);
lean_ctor_set(x_59, 1, x_52);
return x_59;
}
else
{
size_t x_60; size_t x_61; lean_object* x_62; 
x_60 = 0;
x_61 = lean_usize_of_nat(x_54);
lean_dec(x_54);
x_62 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_LetValue_forFVarM___at___Lean_Compiler_LCNF_LetDecl_forFVarM___at___Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__3_spec__6_spec__6_spec__6(x_1, x_39, x_60, x_61, x_55, x_3, x_4, x_5, x_6, x_7, x_8, x_52);
lean_dec(x_39);
return x_62;
}
}
}
}
else
{
lean_dec(x_39);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_40;
}
}
case 4:
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_63 = lean_ctor_get(x_2, 0);
lean_inc(x_63);
lean_dec(x_2);
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 2);
lean_inc(x_65);
x_66 = lean_ctor_get(x_63, 3);
lean_inc(x_66);
lean_dec(x_63);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_67 = l_Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Param_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0(x_1, x_64, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_67, 1);
lean_inc(x_68);
lean_dec(x_67);
lean_inc(x_1);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_69 = lean_apply_8(x_1, x_65, x_3, x_4, x_5, x_6, x_7, x_8, x_68);
if (lean_obj_tag(x_69) == 0)
{
uint8_t x_70; 
x_70 = !lean_is_exclusive(x_69);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_71 = lean_ctor_get(x_69, 1);
x_72 = lean_ctor_get(x_69, 0);
lean_dec(x_72);
x_73 = lean_unsigned_to_nat(0u);
x_74 = lean_array_get_size(x_66);
x_75 = lean_box(0);
x_76 = lean_nat_dec_lt(x_73, x_74);
if (x_76 == 0)
{
lean_dec(x_74);
lean_dec(x_66);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
lean_ctor_set(x_69, 0, x_75);
return x_69;
}
else
{
uint8_t x_77; 
x_77 = lean_nat_dec_le(x_74, x_74);
if (x_77 == 0)
{
lean_dec(x_74);
lean_dec(x_66);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
lean_ctor_set(x_69, 0, x_75);
return x_69;
}
else
{
size_t x_78; size_t x_79; lean_object* x_80; 
lean_free_object(x_69);
x_78 = 0;
x_79 = lean_usize_of_nat(x_74);
lean_dec(x_74);
x_80 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__3_spec__9(x_1, x_66, x_78, x_79, x_75, x_3, x_4, x_5, x_6, x_7, x_8, x_71);
lean_dec(x_66);
return x_80;
}
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; 
x_81 = lean_ctor_get(x_69, 1);
lean_inc(x_81);
lean_dec(x_69);
x_82 = lean_unsigned_to_nat(0u);
x_83 = lean_array_get_size(x_66);
x_84 = lean_box(0);
x_85 = lean_nat_dec_lt(x_82, x_83);
if (x_85 == 0)
{
lean_object* x_86; 
lean_dec(x_83);
lean_dec(x_66);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_81);
return x_86;
}
else
{
uint8_t x_87; 
x_87 = lean_nat_dec_le(x_83, x_83);
if (x_87 == 0)
{
lean_object* x_88; 
lean_dec(x_83);
lean_dec(x_66);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_84);
lean_ctor_set(x_88, 1, x_81);
return x_88;
}
else
{
size_t x_89; size_t x_90; lean_object* x_91; 
x_89 = 0;
x_90 = lean_usize_of_nat(x_83);
lean_dec(x_83);
x_91 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__3_spec__9(x_1, x_66, x_89, x_90, x_84, x_3, x_4, x_5, x_6, x_7, x_8, x_81);
lean_dec(x_66);
return x_91;
}
}
}
}
else
{
lean_dec(x_66);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_69;
}
}
else
{
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_67;
}
}
case 5:
{
lean_object* x_92; lean_object* x_93; 
x_92 = lean_ctor_get(x_2, 0);
lean_inc(x_92);
lean_dec(x_2);
x_93 = lean_apply_8(x_1, x_92, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_93;
}
case 6:
{
lean_object* x_94; lean_object* x_95; 
x_94 = lean_ctor_get(x_2, 0);
lean_inc(x_94);
lean_dec(x_2);
x_95 = l_Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Param_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0(x_1, x_94, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_95;
}
default: 
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_ctor_get(x_2, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_2, 1);
lean_inc(x_97);
lean_dec(x_2);
x_10 = x_96;
x_11 = x_97;
goto block_32;
}
}
block_32:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_12 = lean_ctor_get(x_10, 2);
lean_inc(x_12);
x_13 = lean_ctor_get(x_10, 3);
lean_inc(x_13);
x_14 = lean_ctor_get(x_10, 4);
lean_inc(x_14);
lean_dec(x_10);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_array_get_size(x_12);
x_17 = lean_nat_dec_lt(x_15, x_16);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_16);
lean_dec(x_12);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_18 = l_Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Param_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_20 = l_Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__3(x_1, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_2 = x_11;
x_9 = x_21;
goto _start;
}
else
{
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_20;
}
}
else
{
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_18;
}
}
else
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_box(0);
x_24 = lean_nat_dec_le(x_16, x_16);
if (x_24 == 0)
{
lean_object* x_25; 
lean_dec(x_16);
lean_dec(x_12);
x_25 = l_Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__3___lam__0(x_1, x_13, x_14, x_11, x_23, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_25;
}
else
{
size_t x_26; size_t x_27; lean_object* x_28; 
x_26 = 0;
x_27 = lean_usize_of_nat(x_16);
lean_dec(x_16);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_28 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__3_spec__5(x_1, x_12, x_26, x_27, x_23, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_12);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = l_Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__3___lam__0(x_1, x_13, x_14, x_11, x_29, x_3, x_4, x_5, x_6, x_7, x_8, x_30);
lean_dec(x_29);
return x_31;
}
else
{
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_28;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = l_Lean_Compiler_LCNF_FloatLetIn_Decision_ofAlt(x_1);
x_10 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___boxed), 9, 1);
lean_closure_set(x_10, 0, x_9);
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 2);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_array_get_size(x_11);
x_15 = lean_nat_dec_lt(x_13, x_14);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_14);
lean_dec(x_11);
x_16 = l_Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__3(x_10, x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_16;
}
else
{
uint8_t x_17; 
x_17 = lean_nat_dec_le(x_14, x_14);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_14);
lean_dec(x_11);
x_18 = l_Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__3(x_10, x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_18;
}
else
{
lean_object* x_19; size_t x_20; size_t x_21; lean_object* x_22; 
x_19 = lean_box(0);
x_20 = 0;
x_21 = lean_usize_of_nat(x_14);
lean_dec(x_14);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_10);
x_22 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__3_spec__5(x_10, x_11, x_20, x_21, x_19, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_11);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = l_Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__3(x_10, x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_23);
return x_24;
}
else
{
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_22;
}
}
}
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_1, 0);
lean_inc(x_25);
lean_dec(x_1);
x_26 = l_Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__3(x_10, x_25, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__3_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__3_spec__5(x_1, x_2, x_13, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_LetValue_forFVarM___at___Lean_Compiler_LCNF_LetDecl_forFVarM___at___Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__3_spec__6_spec__6_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_LetValue_forFVarM___at___Lean_Compiler_LCNF_LetDecl_forFVarM___at___Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__3_spec__6_spec__6_spec__6(x_1, x_2, x_13, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__3_spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__3_spec__9(x_1, x_2, x_13, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__3___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__3___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_5);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goCases_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_eq(x_2, x_3);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_4);
x_13 = lean_array_uget(x_1, x_2);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_14 = l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt(x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = 1;
x_18 = lean_usize_add(x_2, x_17);
x_2 = x_18;
x_4 = x_15;
x_11 = x_16;
goto _start;
}
else
{
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_14;
}
}
else
{
lean_object* x_20; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_4);
lean_ctor_set(x_20, 1, x_11);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goCases(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_ctor_get(x_1, 3);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_array_get_size(x_9);
x_12 = lean_box(0);
x_13 = lean_nat_dec_lt(x_10, x_11);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_8);
return x_14;
}
else
{
uint8_t x_15; 
x_15 = lean_nat_dec_le(x_11, x_11);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_12);
lean_ctor_set(x_16, 1, x_8);
return x_16;
}
else
{
size_t x_17; size_t x_18; lean_object* x_19; 
x_17 = 0;
x_18 = lean_usize_of_nat(x_11);
lean_dec(x_11);
x_19 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goCases_spec__0(x_9, x_17, x_18, x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goCases_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goCases_spec__0(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goCases___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goCases(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_2, 1);
lean_inc(x_10);
lean_dec(x_2);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_91; lean_object* x_92; 
x_91 = lean_ctor_get(x_9, 0);
lean_inc(x_91);
lean_inc(x_91);
x_92 = l_Lean_Compiler_LCNF_FloatLetIn_ignore_x3f___redArg(x_91, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; uint8_t x_94; 
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_unbox(x_93);
lean_dec(x_93);
if (x_94 == 0)
{
lean_object* x_95; 
lean_dec(x_91);
x_95 = lean_ctor_get(x_92, 1);
lean_inc(x_95);
lean_dec(x_92);
x_11 = x_95;
goto block_90;
}
else
{
lean_object* x_96; uint8_t x_97; 
lean_dec(x_9);
x_96 = lean_ctor_get(x_92, 1);
lean_inc(x_96);
lean_dec(x_92);
x_97 = !lean_is_exclusive(x_1);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint64_t x_103; uint64_t x_104; uint64_t x_105; uint64_t x_106; uint64_t x_107; uint64_t x_108; uint64_t x_109; size_t x_110; size_t x_111; size_t x_112; size_t x_113; size_t x_114; lean_object* x_115; uint8_t x_116; 
x_98 = lean_ctor_get(x_1, 0);
x_99 = lean_ctor_get(x_1, 1);
x_100 = lean_ctor_get(x_91, 0);
lean_inc(x_100);
lean_dec(x_91);
x_101 = lean_box(2);
x_102 = lean_array_get_size(x_99);
x_103 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1561_(x_100);
x_104 = 32;
x_105 = lean_uint64_shift_right(x_103, x_104);
x_106 = lean_uint64_xor(x_103, x_105);
x_107 = 16;
x_108 = lean_uint64_shift_right(x_106, x_107);
x_109 = lean_uint64_xor(x_106, x_108);
x_110 = lean_uint64_to_usize(x_109);
x_111 = lean_usize_of_nat(x_102);
lean_dec(x_102);
x_112 = 1;
x_113 = lean_usize_sub(x_111, x_112);
x_114 = lean_usize_land(x_110, x_113);
x_115 = lean_array_uget(x_99, x_114);
x_116 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__0___redArg(x_100, x_115);
if (x_116 == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; 
x_117 = lean_unsigned_to_nat(1u);
x_118 = lean_nat_add(x_98, x_117);
lean_dec(x_98);
x_119 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_119, 0, x_100);
lean_ctor_set(x_119, 1, x_101);
lean_ctor_set(x_119, 2, x_115);
x_120 = lean_array_uset(x_99, x_114, x_119);
x_121 = lean_unsigned_to_nat(4u);
x_122 = lean_nat_mul(x_118, x_121);
x_123 = lean_unsigned_to_nat(3u);
x_124 = lean_nat_div(x_122, x_123);
lean_dec(x_122);
x_125 = lean_array_get_size(x_120);
x_126 = lean_nat_dec_le(x_124, x_125);
lean_dec(x_125);
lean_dec(x_124);
if (x_126 == 0)
{
lean_object* x_127; 
x_127 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__1___redArg(x_120);
lean_ctor_set(x_1, 1, x_127);
lean_ctor_set(x_1, 0, x_118);
x_2 = x_10;
x_7 = x_96;
goto _start;
}
else
{
lean_ctor_set(x_1, 1, x_120);
lean_ctor_set(x_1, 0, x_118);
x_2 = x_10;
x_7 = x_96;
goto _start;
}
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_130 = lean_box(0);
x_131 = lean_array_uset(x_99, x_114, x_130);
x_132 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_LCtx_addParam_spec__0___redArg(x_100, x_101, x_115);
x_133 = lean_array_uset(x_131, x_114, x_132);
lean_ctor_set(x_1, 1, x_133);
x_2 = x_10;
x_7 = x_96;
goto _start;
}
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; uint64_t x_140; uint64_t x_141; uint64_t x_142; uint64_t x_143; uint64_t x_144; uint64_t x_145; uint64_t x_146; size_t x_147; size_t x_148; size_t x_149; size_t x_150; size_t x_151; lean_object* x_152; uint8_t x_153; 
x_135 = lean_ctor_get(x_1, 0);
x_136 = lean_ctor_get(x_1, 1);
lean_inc(x_136);
lean_inc(x_135);
lean_dec(x_1);
x_137 = lean_ctor_get(x_91, 0);
lean_inc(x_137);
lean_dec(x_91);
x_138 = lean_box(2);
x_139 = lean_array_get_size(x_136);
x_140 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1561_(x_137);
x_141 = 32;
x_142 = lean_uint64_shift_right(x_140, x_141);
x_143 = lean_uint64_xor(x_140, x_142);
x_144 = 16;
x_145 = lean_uint64_shift_right(x_143, x_144);
x_146 = lean_uint64_xor(x_143, x_145);
x_147 = lean_uint64_to_usize(x_146);
x_148 = lean_usize_of_nat(x_139);
lean_dec(x_139);
x_149 = 1;
x_150 = lean_usize_sub(x_148, x_149);
x_151 = lean_usize_land(x_147, x_150);
x_152 = lean_array_uget(x_136, x_151);
x_153 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__0___redArg(x_137, x_152);
if (x_153 == 0)
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; uint8_t x_163; 
x_154 = lean_unsigned_to_nat(1u);
x_155 = lean_nat_add(x_135, x_154);
lean_dec(x_135);
x_156 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_156, 0, x_137);
lean_ctor_set(x_156, 1, x_138);
lean_ctor_set(x_156, 2, x_152);
x_157 = lean_array_uset(x_136, x_151, x_156);
x_158 = lean_unsigned_to_nat(4u);
x_159 = lean_nat_mul(x_155, x_158);
x_160 = lean_unsigned_to_nat(3u);
x_161 = lean_nat_div(x_159, x_160);
lean_dec(x_159);
x_162 = lean_array_get_size(x_157);
x_163 = lean_nat_dec_le(x_161, x_162);
lean_dec(x_162);
lean_dec(x_161);
if (x_163 == 0)
{
lean_object* x_164; lean_object* x_165; 
x_164 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__1___redArg(x_157);
x_165 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_165, 0, x_155);
lean_ctor_set(x_165, 1, x_164);
x_1 = x_165;
x_2 = x_10;
x_7 = x_96;
goto _start;
}
else
{
lean_object* x_167; 
x_167 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_167, 0, x_155);
lean_ctor_set(x_167, 1, x_157);
x_1 = x_167;
x_2 = x_10;
x_7 = x_96;
goto _start;
}
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_169 = lean_box(0);
x_170 = lean_array_uset(x_136, x_151, x_169);
x_171 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_LCtx_addParam_spec__0___redArg(x_137, x_138, x_152);
x_172 = lean_array_uset(x_170, x_151, x_171);
x_173 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_173, 0, x_135);
lean_ctor_set(x_173, 1, x_172);
x_1 = x_173;
x_2 = x_10;
x_7 = x_96;
goto _start;
}
}
}
}
else
{
uint8_t x_175; 
lean_dec(x_91);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_175 = !lean_is_exclusive(x_92);
if (x_175 == 0)
{
return x_92;
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_176 = lean_ctor_get(x_92, 0);
x_177 = lean_ctor_get(x_92, 1);
lean_inc(x_177);
lean_inc(x_176);
lean_dec(x_92);
x_178 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_178, 0, x_176);
lean_ctor_set(x_178, 1, x_177);
return x_178;
}
}
}
else
{
x_11 = x_7;
goto block_90;
}
block_90:
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_1);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint64_t x_18; uint64_t x_19; uint64_t x_20; uint64_t x_21; uint64_t x_22; uint64_t x_23; uint64_t x_24; size_t x_25; size_t x_26; size_t x_27; size_t x_28; size_t x_29; lean_object* x_30; uint8_t x_31; 
x_13 = lean_ctor_get(x_1, 0);
x_14 = lean_ctor_get(x_1, 1);
x_15 = l_Lean_Compiler_LCNF_CodeDecl_fvarId(x_9);
lean_dec(x_9);
x_16 = lean_box(3);
x_17 = lean_array_get_size(x_14);
x_18 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1561_(x_15);
x_19 = 32;
x_20 = lean_uint64_shift_right(x_18, x_19);
x_21 = lean_uint64_xor(x_18, x_20);
x_22 = 16;
x_23 = lean_uint64_shift_right(x_21, x_22);
x_24 = lean_uint64_xor(x_21, x_23);
x_25 = lean_uint64_to_usize(x_24);
x_26 = lean_usize_of_nat(x_17);
lean_dec(x_17);
x_27 = 1;
x_28 = lean_usize_sub(x_26, x_27);
x_29 = lean_usize_land(x_25, x_28);
x_30 = lean_array_uget(x_14, x_29);
x_31 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__0___redArg(x_15, x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_32 = lean_unsigned_to_nat(1u);
x_33 = lean_nat_add(x_13, x_32);
lean_dec(x_13);
x_34 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_34, 0, x_15);
lean_ctor_set(x_34, 1, x_16);
lean_ctor_set(x_34, 2, x_30);
x_35 = lean_array_uset(x_14, x_29, x_34);
x_36 = lean_unsigned_to_nat(4u);
x_37 = lean_nat_mul(x_33, x_36);
x_38 = lean_unsigned_to_nat(3u);
x_39 = lean_nat_div(x_37, x_38);
lean_dec(x_37);
x_40 = lean_array_get_size(x_35);
x_41 = lean_nat_dec_le(x_39, x_40);
lean_dec(x_40);
lean_dec(x_39);
if (x_41 == 0)
{
lean_object* x_42; 
x_42 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__1___redArg(x_35);
lean_ctor_set(x_1, 1, x_42);
lean_ctor_set(x_1, 0, x_33);
x_2 = x_10;
x_7 = x_11;
goto _start;
}
else
{
lean_ctor_set(x_1, 1, x_35);
lean_ctor_set(x_1, 0, x_33);
x_2 = x_10;
x_7 = x_11;
goto _start;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_45 = lean_box(0);
x_46 = lean_array_uset(x_14, x_29, x_45);
x_47 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_LCtx_addParam_spec__0___redArg(x_15, x_16, x_30);
x_48 = lean_array_uset(x_46, x_29, x_47);
lean_ctor_set(x_1, 1, x_48);
x_2 = x_10;
x_7 = x_11;
goto _start;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint64_t x_55; uint64_t x_56; uint64_t x_57; uint64_t x_58; uint64_t x_59; uint64_t x_60; uint64_t x_61; size_t x_62; size_t x_63; size_t x_64; size_t x_65; size_t x_66; lean_object* x_67; uint8_t x_68; 
x_50 = lean_ctor_get(x_1, 0);
x_51 = lean_ctor_get(x_1, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_1);
x_52 = l_Lean_Compiler_LCNF_CodeDecl_fvarId(x_9);
lean_dec(x_9);
x_53 = lean_box(3);
x_54 = lean_array_get_size(x_51);
x_55 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1561_(x_52);
x_56 = 32;
x_57 = lean_uint64_shift_right(x_55, x_56);
x_58 = lean_uint64_xor(x_55, x_57);
x_59 = 16;
x_60 = lean_uint64_shift_right(x_58, x_59);
x_61 = lean_uint64_xor(x_58, x_60);
x_62 = lean_uint64_to_usize(x_61);
x_63 = lean_usize_of_nat(x_54);
lean_dec(x_54);
x_64 = 1;
x_65 = lean_usize_sub(x_63, x_64);
x_66 = lean_usize_land(x_62, x_65);
x_67 = lean_array_uget(x_51, x_66);
x_68 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__0___redArg(x_52, x_67);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; 
x_69 = lean_unsigned_to_nat(1u);
x_70 = lean_nat_add(x_50, x_69);
lean_dec(x_50);
x_71 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_71, 0, x_52);
lean_ctor_set(x_71, 1, x_53);
lean_ctor_set(x_71, 2, x_67);
x_72 = lean_array_uset(x_51, x_66, x_71);
x_73 = lean_unsigned_to_nat(4u);
x_74 = lean_nat_mul(x_70, x_73);
x_75 = lean_unsigned_to_nat(3u);
x_76 = lean_nat_div(x_74, x_75);
lean_dec(x_74);
x_77 = lean_array_get_size(x_72);
x_78 = lean_nat_dec_le(x_76, x_77);
lean_dec(x_77);
lean_dec(x_76);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; 
x_79 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__1___redArg(x_72);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_70);
lean_ctor_set(x_80, 1, x_79);
x_1 = x_80;
x_2 = x_10;
x_7 = x_11;
goto _start;
}
else
{
lean_object* x_82; 
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_70);
lean_ctor_set(x_82, 1, x_72);
x_1 = x_82;
x_2 = x_10;
x_7 = x_11;
goto _start;
}
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_84 = lean_box(0);
x_85 = lean_array_uset(x_51, x_66, x_84);
x_86 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_LCtx_addParam_spec__0___redArg(x_52, x_53, x_67);
x_87 = lean_array_uset(x_85, x_66, x_86);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_50);
lean_ctor_set(x_88, 1, x_87);
x_1 = x_88;
x_2 = x_10;
x_7 = x_11;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_List_foldlM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__0___redArg(x_3, x_4, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_30 = l_List_lengthTR___redArg(x_2);
x_31 = lean_unsigned_to_nat(0u);
x_32 = lean_unsigned_to_nat(4u);
x_33 = lean_nat_mul(x_30, x_32);
lean_dec(x_30);
x_34 = lean_unsigned_to_nat(3u);
x_35 = lean_nat_div(x_33, x_34);
lean_dec(x_33);
x_36 = l_Nat_nextPowerOfTwo(x_35);
lean_dec(x_35);
x_37 = lean_box(0);
x_38 = lean_mk_array(x_36, x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_31);
lean_ctor_set(x_39, 1, x_38);
lean_inc(x_2);
x_40 = l_List_reverse___redArg(x_2);
x_41 = l_List_foldlM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__0___redArg(x_39, x_40, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint64_t x_48; uint64_t x_49; uint64_t x_50; uint64_t x_51; uint64_t x_52; uint64_t x_53; uint64_t x_54; size_t x_55; size_t x_56; size_t x_57; size_t x_58; size_t x_59; lean_object* x_60; uint8_t x_61; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = lean_ctor_get(x_42, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_42, 1);
lean_inc(x_45);
x_46 = lean_ctor_get(x_1, 2);
lean_inc(x_46);
x_47 = lean_array_get_size(x_45);
x_48 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1561_(x_46);
x_49 = 32;
x_50 = lean_uint64_shift_right(x_48, x_49);
x_51 = lean_uint64_xor(x_48, x_50);
x_52 = 16;
x_53 = lean_uint64_shift_right(x_51, x_52);
x_54 = lean_uint64_xor(x_51, x_53);
x_55 = lean_uint64_to_usize(x_54);
x_56 = lean_usize_of_nat(x_47);
lean_dec(x_47);
x_57 = 1;
x_58 = lean_usize_sub(x_56, x_57);
x_59 = lean_usize_land(x_55, x_58);
x_60 = lean_array_uget(x_45, x_59);
x_61 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__0___redArg(x_46, x_60);
if (x_61 == 0)
{
lean_dec(x_60);
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_44);
x_8 = x_42;
x_9 = x_2;
x_10 = x_3;
x_11 = x_4;
x_12 = x_5;
x_13 = x_6;
x_14 = x_43;
goto block_29;
}
else
{
uint8_t x_62; 
x_62 = !lean_is_exclusive(x_42);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_42, 1);
lean_dec(x_63);
x_64 = lean_ctor_get(x_42, 0);
lean_dec(x_64);
x_65 = lean_box(2);
if (x_61 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_66 = lean_unsigned_to_nat(1u);
x_67 = lean_nat_add(x_44, x_66);
lean_dec(x_44);
x_68 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_68, 0, x_46);
lean_ctor_set(x_68, 1, x_65);
lean_ctor_set(x_68, 2, x_60);
x_69 = lean_array_uset(x_45, x_59, x_68);
x_70 = lean_nat_mul(x_67, x_32);
x_71 = lean_nat_div(x_70, x_34);
lean_dec(x_70);
x_72 = lean_array_get_size(x_69);
x_73 = lean_nat_dec_le(x_71, x_72);
lean_dec(x_72);
lean_dec(x_71);
if (x_73 == 0)
{
lean_object* x_74; 
x_74 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__1___redArg(x_69);
lean_ctor_set(x_42, 1, x_74);
lean_ctor_set(x_42, 0, x_67);
x_8 = x_42;
x_9 = x_2;
x_10 = x_3;
x_11 = x_4;
x_12 = x_5;
x_13 = x_6;
x_14 = x_43;
goto block_29;
}
else
{
lean_ctor_set(x_42, 1, x_69);
lean_ctor_set(x_42, 0, x_67);
x_8 = x_42;
x_9 = x_2;
x_10 = x_3;
x_11 = x_4;
x_12 = x_5;
x_13 = x_6;
x_14 = x_43;
goto block_29;
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_array_uset(x_45, x_59, x_37);
x_76 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_LCtx_addParam_spec__0___redArg(x_46, x_65, x_60);
x_77 = lean_array_uset(x_75, x_59, x_76);
lean_ctor_set(x_42, 1, x_77);
x_8 = x_42;
x_9 = x_2;
x_10 = x_3;
x_11 = x_4;
x_12 = x_5;
x_13 = x_6;
x_14 = x_43;
goto block_29;
}
}
else
{
lean_object* x_78; 
lean_dec(x_42);
x_78 = lean_box(2);
if (x_61 == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_79 = lean_unsigned_to_nat(1u);
x_80 = lean_nat_add(x_44, x_79);
lean_dec(x_44);
x_81 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_81, 0, x_46);
lean_ctor_set(x_81, 1, x_78);
lean_ctor_set(x_81, 2, x_60);
x_82 = lean_array_uset(x_45, x_59, x_81);
x_83 = lean_nat_mul(x_80, x_32);
x_84 = lean_nat_div(x_83, x_34);
lean_dec(x_83);
x_85 = lean_array_get_size(x_82);
x_86 = lean_nat_dec_le(x_84, x_85);
lean_dec(x_85);
lean_dec(x_84);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; 
x_87 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__1___redArg(x_82);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_80);
lean_ctor_set(x_88, 1, x_87);
x_8 = x_88;
x_9 = x_2;
x_10 = x_3;
x_11 = x_4;
x_12 = x_5;
x_13 = x_6;
x_14 = x_43;
goto block_29;
}
else
{
lean_object* x_89; 
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_80);
lean_ctor_set(x_89, 1, x_82);
x_8 = x_89;
x_9 = x_2;
x_10 = x_3;
x_11 = x_4;
x_12 = x_5;
x_13 = x_6;
x_14 = x_43;
goto block_29;
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_90 = lean_array_uset(x_45, x_59, x_37);
x_91 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_LCtx_addParam_spec__0___redArg(x_46, x_78, x_60);
x_92 = lean_array_uset(x_90, x_59, x_91);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_44);
lean_ctor_set(x_93, 1, x_92);
x_8 = x_93;
x_9 = x_2;
x_10 = x_3;
x_11 = x_4;
x_12 = x_5;
x_13 = x_6;
x_14 = x_43;
goto block_29;
}
}
}
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_41;
}
block_29:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_st_mk_ref(x_8, x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_16);
x_18 = l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goCases(x_1, x_16, x_9, x_10, x_11, x_12, x_13, x_17);
lean_dec(x_1);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_st_ref_get(x_16, x_19);
lean_dec(x_16);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
return x_20;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_20);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
else
{
uint8_t x_25; 
lean_dec(x_16);
x_25 = !lean_is_exclusive(x_18);
if (x_25 == 0)
{
return x_18;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_18, 0);
x_27 = lean_ctor_get(x_18, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_18);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_List_foldlM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_List_foldlM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_box(0);
x_4 = lean_unbox(x_3);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 2);
x_7 = l_Lean_Compiler_LCNF_FloatLetIn_beqDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_73_(x_5, x_1);
if (x_7 == 0)
{
x_2 = x_6;
goto _start;
}
else
{
return x_7;
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__1_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_array_get_size(x_1);
x_7 = l_Lean_Compiler_LCNF_FloatLetIn_hashDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_26_(x_4);
x_8 = 32;
x_9 = lean_uint64_shift_right(x_7, x_8);
x_10 = lean_uint64_xor(x_7, x_9);
x_11 = 16;
x_12 = lean_uint64_shift_right(x_10, x_11);
x_13 = lean_uint64_xor(x_10, x_12);
x_14 = lean_uint64_to_usize(x_13);
x_15 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_16 = 1;
x_17 = lean_usize_sub(x_15, x_16);
x_18 = lean_usize_land(x_14, x_17);
x_19 = lean_array_uget(x_1, x_18);
lean_ctor_set(x_2, 2, x_19);
x_20 = lean_array_uset(x_1, x_18, x_2);
x_1 = x_20;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint64_t x_26; uint64_t x_27; uint64_t x_28; uint64_t x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; size_t x_33; size_t x_34; size_t x_35; size_t x_36; size_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_22 = lean_ctor_get(x_2, 0);
x_23 = lean_ctor_get(x_2, 1);
x_24 = lean_ctor_get(x_2, 2);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_2);
x_25 = lean_array_get_size(x_1);
x_26 = l_Lean_Compiler_LCNF_FloatLetIn_hashDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_26_(x_22);
x_27 = 32;
x_28 = lean_uint64_shift_right(x_26, x_27);
x_29 = lean_uint64_xor(x_26, x_28);
x_30 = 16;
x_31 = lean_uint64_shift_right(x_29, x_30);
x_32 = lean_uint64_xor(x_29, x_31);
x_33 = lean_uint64_to_usize(x_32);
x_34 = lean_usize_of_nat(x_25);
lean_dec(x_25);
x_35 = 1;
x_36 = lean_usize_sub(x_34, x_35);
x_37 = lean_usize_land(x_33, x_36);
x_38 = lean_array_uget(x_1, x_37);
x_39 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_39, 0, x_22);
lean_ctor_set(x_39, 1, x_23);
lean_ctor_set(x_39, 2, x_38);
x_40 = lean_array_uset(x_1, x_37, x_39);
x_1 = x_40;
x_2 = x_24;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__1_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__1_spec__1_spec__1___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_1, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean_box(0);
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__1_spec__1_spec__1___redArg(x_3, x_6);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_1, x_10);
lean_dec(x_1);
x_1 = x_11;
x_2 = x_8;
x_3 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__1_spec__1___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__1___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(2u);
x_4 = lean_nat_mul(x_2, x_3);
lean_dec(x_2);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_box(0);
x_7 = lean_mk_array(x_4, x_6);
x_8 = l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__1_spec__1___redArg(x_5, x_1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__1___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__4___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_ctor_get(x_3, 2);
x_8 = l_Lean_Compiler_LCNF_FloatLetIn_beqDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_73_(x_5, x_1);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__4___redArg(x_1, x_2, x_7);
lean_ctor_set(x_3, 2, x_9);
return x_3;
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_ctor_get(x_3, 1);
x_12 = lean_ctor_get(x_3, 2);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_3);
x_13 = l_Lean_Compiler_LCNF_FloatLetIn_beqDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_73_(x_10, x_1);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__4___redArg(x_1, x_2, x_12);
x_15 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_11);
lean_ctor_set(x_15, 2, x_14);
return x_15;
}
else
{
lean_object* x_16; 
lean_dec(x_11);
lean_dec(x_10);
x_16 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_2);
lean_ctor_set(x_16, 2, x_12);
return x_16;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__4___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__5___redArg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint64_t x_15; uint64_t x_16; uint64_t x_17; uint64_t x_18; uint64_t x_19; uint64_t x_20; uint64_t x_21; size_t x_22; size_t x_23; size_t x_24; size_t x_25; lean_object* x_26; uint8_t x_27; 
x_8 = lean_ctor_get(x_5, 0);
x_9 = lean_ctor_get(x_5, 1);
x_10 = 1;
x_11 = lean_usize_sub(x_3, x_10);
x_12 = lean_array_uget(x_2, x_11);
x_13 = l_Lean_Compiler_LCNF_FloatLetIn_Decision_ofAlt(x_12);
lean_dec(x_12);
x_14 = lean_array_get_size(x_9);
x_15 = l_Lean_Compiler_LCNF_FloatLetIn_hashDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_26_(x_13);
x_16 = 32;
x_17 = lean_uint64_shift_right(x_15, x_16);
x_18 = lean_uint64_xor(x_15, x_17);
x_19 = 16;
x_20 = lean_uint64_shift_right(x_18, x_19);
x_21 = lean_uint64_xor(x_18, x_20);
x_22 = lean_uint64_to_usize(x_21);
x_23 = lean_usize_of_nat(x_14);
lean_dec(x_14);
x_24 = lean_usize_sub(x_23, x_10);
x_25 = lean_usize_land(x_22, x_24);
x_26 = lean_array_uget(x_9, x_25);
x_27 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0___redArg(x_13, x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_add(x_8, x_28);
lean_dec(x_8);
lean_inc(x_1);
x_30 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_30, 0, x_13);
lean_ctor_set(x_30, 1, x_1);
lean_ctor_set(x_30, 2, x_26);
x_31 = lean_array_uset(x_9, x_25, x_30);
x_32 = lean_unsigned_to_nat(4u);
x_33 = lean_nat_mul(x_29, x_32);
x_34 = lean_unsigned_to_nat(3u);
x_35 = lean_nat_div(x_33, x_34);
lean_dec(x_33);
x_36 = lean_array_get_size(x_31);
x_37 = lean_nat_dec_le(x_35, x_36);
lean_dec(x_36);
lean_dec(x_35);
if (x_37 == 0)
{
lean_object* x_38; 
x_38 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__1___redArg(x_31);
lean_ctor_set(x_5, 1, x_38);
lean_ctor_set(x_5, 0, x_29);
x_3 = x_11;
goto _start;
}
else
{
lean_ctor_set(x_5, 1, x_31);
lean_ctor_set(x_5, 0, x_29);
x_3 = x_11;
goto _start;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_41 = lean_box(0);
x_42 = lean_array_uset(x_9, x_25, x_41);
lean_inc(x_1);
x_43 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__4___redArg(x_13, x_1, x_26);
x_44 = lean_array_uset(x_42, x_25, x_43);
lean_ctor_set(x_5, 1, x_44);
x_3 = x_11;
goto _start;
}
}
else
{
lean_object* x_46; lean_object* x_47; size_t x_48; size_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint64_t x_53; uint64_t x_54; uint64_t x_55; uint64_t x_56; uint64_t x_57; uint64_t x_58; uint64_t x_59; size_t x_60; size_t x_61; size_t x_62; size_t x_63; lean_object* x_64; uint8_t x_65; 
x_46 = lean_ctor_get(x_5, 0);
x_47 = lean_ctor_get(x_5, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_5);
x_48 = 1;
x_49 = lean_usize_sub(x_3, x_48);
x_50 = lean_array_uget(x_2, x_49);
x_51 = l_Lean_Compiler_LCNF_FloatLetIn_Decision_ofAlt(x_50);
lean_dec(x_50);
x_52 = lean_array_get_size(x_47);
x_53 = l_Lean_Compiler_LCNF_FloatLetIn_hashDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_26_(x_51);
x_54 = 32;
x_55 = lean_uint64_shift_right(x_53, x_54);
x_56 = lean_uint64_xor(x_53, x_55);
x_57 = 16;
x_58 = lean_uint64_shift_right(x_56, x_57);
x_59 = lean_uint64_xor(x_56, x_58);
x_60 = lean_uint64_to_usize(x_59);
x_61 = lean_usize_of_nat(x_52);
lean_dec(x_52);
x_62 = lean_usize_sub(x_61, x_48);
x_63 = lean_usize_land(x_60, x_62);
x_64 = lean_array_uget(x_47, x_63);
x_65 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0___redArg(x_51, x_64);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_66 = lean_unsigned_to_nat(1u);
x_67 = lean_nat_add(x_46, x_66);
lean_dec(x_46);
lean_inc(x_1);
x_68 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_68, 0, x_51);
lean_ctor_set(x_68, 1, x_1);
lean_ctor_set(x_68, 2, x_64);
x_69 = lean_array_uset(x_47, x_63, x_68);
x_70 = lean_unsigned_to_nat(4u);
x_71 = lean_nat_mul(x_67, x_70);
x_72 = lean_unsigned_to_nat(3u);
x_73 = lean_nat_div(x_71, x_72);
lean_dec(x_71);
x_74 = lean_array_get_size(x_69);
x_75 = lean_nat_dec_le(x_73, x_74);
lean_dec(x_74);
lean_dec(x_73);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; 
x_76 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__1___redArg(x_69);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_67);
lean_ctor_set(x_77, 1, x_76);
x_3 = x_49;
x_5 = x_77;
goto _start;
}
else
{
lean_object* x_79; 
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_67);
lean_ctor_set(x_79, 1, x_69);
x_3 = x_49;
x_5 = x_79;
goto _start;
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_81 = lean_box(0);
x_82 = lean_array_uset(x_47, x_63, x_81);
lean_inc(x_1);
x_83 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__4___redArg(x_51, x_1, x_64);
x_84 = lean_array_uset(x_82, x_63, x_83);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_46);
lean_ctor_set(x_85, 1, x_84);
x_3 = x_49;
x_5 = x_85;
goto _start;
}
}
}
else
{
lean_dec(x_1);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_foldrMUnsafe_fold___at___Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__5___redArg(x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
static uint64_t _init_l_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___closed__0() {
_start:
{
lean_object* x_1; uint64_t x_2; 
x_1 = lean_box(2);
x_2 = l_Lean_Compiler_LCNF_FloatLetIn_hashDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_26_(x_1);
return x_2;
}
}
static uint64_t _init_l_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___closed__1() {
_start:
{
uint64_t x_1; uint64_t x_2; uint64_t x_3; 
x_1 = 32;
x_2 = l_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___closed__0;
x_3 = lean_uint64_shift_right(x_2, x_1);
return x_3;
}
}
static uint64_t _init_l_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___closed__2() {
_start:
{
uint64_t x_1; uint64_t x_2; uint64_t x_3; 
x_1 = l_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___closed__1;
x_2 = l_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___closed__0;
x_3 = lean_uint64_xor(x_2, x_1);
return x_3;
}
}
static uint64_t _init_l_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___closed__3() {
_start:
{
uint64_t x_1; uint64_t x_2; uint64_t x_3; 
x_1 = 16;
x_2 = l_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___closed__2;
x_3 = lean_uint64_shift_right(x_2, x_1);
return x_3;
}
}
static uint64_t _init_l_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___closed__4() {
_start:
{
uint64_t x_1; uint64_t x_2; uint64_t x_3; 
x_1 = l_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___closed__3;
x_2 = l_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___closed__2;
x_3 = lean_uint64_xor(x_2, x_1);
return x_3;
}
}
static size_t _init_l_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___closed__5() {
_start:
{
uint64_t x_1; size_t x_2; 
x_1 = l_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___closed__4;
x_2 = lean_uint64_to_usize(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_nat_mul(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = l_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___closed__6;
x_3 = lean_nat_div(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_initialNewArms(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_22; size_t x_23; size_t x_24; size_t x_25; size_t x_26; size_t x_27; lean_object* x_28; uint8_t x_29; 
x_2 = lean_ctor_get(x_1, 3);
x_3 = lean_array_get_size(x_2);
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_add(x_3, x_4);
x_6 = lean_unsigned_to_nat(4u);
x_7 = lean_nat_mul(x_5, x_6);
lean_dec(x_5);
x_8 = lean_unsigned_to_nat(3u);
x_9 = lean_nat_div(x_7, x_8);
lean_dec(x_7);
x_10 = l_Nat_nextPowerOfTwo(x_9);
lean_dec(x_9);
x_11 = lean_box(0);
x_12 = lean_mk_array(x_10, x_11);
x_13 = lean_box(2);
x_14 = lean_box(0);
x_22 = lean_array_get_size(x_12);
x_23 = l_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___closed__5;
x_24 = lean_usize_of_nat(x_22);
lean_dec(x_22);
x_25 = 1;
x_26 = lean_usize_sub(x_24, x_25);
x_27 = lean_usize_land(x_23, x_26);
x_28 = lean_array_uget(x_12, x_27);
x_29 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0___redArg(x_13, x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_30 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_30, 0, x_13);
lean_ctor_set(x_30, 1, x_14);
lean_ctor_set(x_30, 2, x_28);
x_31 = lean_array_uset(x_12, x_27, x_30);
x_32 = l_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___closed__7;
x_33 = lean_array_get_size(x_31);
x_34 = lean_nat_dec_le(x_32, x_33);
lean_dec(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__1___redArg(x_31);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_4);
lean_ctor_set(x_36, 1, x_35);
x_15 = x_36;
goto block_21;
}
else
{
lean_object* x_37; 
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_4);
lean_ctor_set(x_37, 1, x_31);
x_15 = x_37;
goto block_21;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_38 = lean_unsigned_to_nat(0u);
x_39 = lean_array_uset(x_12, x_27, x_11);
x_40 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__4___redArg(x_13, x_14, x_28);
x_41 = lean_array_uset(x_39, x_27, x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_38);
lean_ctor_set(x_42, 1, x_41);
x_15 = x_42;
goto block_21;
}
block_21:
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_nat_dec_lt(x_16, x_3);
if (x_17 == 0)
{
lean_dec(x_3);
return x_15;
}
else
{
size_t x_18; size_t x_19; lean_object* x_20; 
x_18 = lean_usize_of_nat(x_3);
lean_dec(x_3);
x_19 = 0;
x_20 = l_Array_foldrMUnsafe_fold___at___Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__5___redArg(x_14, x_2, x_18, x_19, x_15);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__5___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldrMUnsafe_fold___at___Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__5___redArg(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = l_Array_foldrMUnsafe_fold___at___Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__5(x_1, x_2, x_3, x_4, x_8, x_9, x_7);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Compiler_LCNF_FloatLetIn_initialNewArms(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_st_ref_get(x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = !lean_is_exclusive(x_4);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; uint64_t x_16; uint64_t x_17; uint64_t x_18; size_t x_19; size_t x_20; size_t x_21; size_t x_22; size_t x_23; lean_object* x_24; uint8_t x_25; 
x_8 = lean_ctor_get(x_4, 1);
x_9 = lean_ctor_get(x_4, 0);
lean_dec(x_9);
x_10 = lean_ctor_get(x_6, 1);
lean_inc(x_10);
lean_dec(x_6);
x_11 = lean_array_get_size(x_10);
x_12 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1561_(x_1);
x_13 = 32;
x_14 = lean_uint64_shift_right(x_12, x_13);
x_15 = lean_uint64_xor(x_12, x_14);
x_16 = 16;
x_17 = lean_uint64_shift_right(x_15, x_16);
x_18 = lean_uint64_xor(x_15, x_17);
x_19 = lean_uint64_to_usize(x_18);
x_20 = lean_usize_of_nat(x_11);
lean_dec(x_11);
x_21 = 1;
x_22 = lean_usize_sub(x_20, x_21);
x_23 = lean_usize_land(x_19, x_22);
x_24 = lean_array_uget(x_10, x_23);
lean_dec(x_10);
x_25 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__0___redArg(x_1, x_24);
lean_dec(x_24);
if (x_25 == 0)
{
lean_object* x_26; 
lean_dec(x_1);
x_26 = lean_box(0);
lean_ctor_set(x_4, 0, x_26);
return x_4;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
lean_free_object(x_4);
x_27 = lean_st_ref_take(x_2, x_8);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_dec(x_27);
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_32 = x_28;
} else {
 lean_dec_ref(x_28);
 x_32 = lean_box(0);
}
x_33 = !lean_is_exclusive(x_29);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_45; lean_object* x_46; size_t x_47; size_t x_48; size_t x_49; lean_object* x_50; uint8_t x_51; 
x_34 = lean_ctor_get(x_29, 0);
x_35 = lean_ctor_get(x_29, 1);
x_36 = lean_box(0);
x_45 = lean_box(2);
x_46 = lean_array_get_size(x_35);
x_47 = lean_usize_of_nat(x_46);
lean_dec(x_46);
x_48 = lean_usize_sub(x_47, x_21);
x_49 = lean_usize_land(x_19, x_48);
x_50 = lean_array_uget(x_35, x_49);
x_51 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__0___redArg(x_1, x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_52 = lean_unsigned_to_nat(1u);
x_53 = lean_nat_add(x_34, x_52);
lean_dec(x_34);
x_54 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_54, 0, x_1);
lean_ctor_set(x_54, 1, x_45);
lean_ctor_set(x_54, 2, x_50);
x_55 = lean_array_uset(x_35, x_49, x_54);
x_56 = lean_unsigned_to_nat(4u);
x_57 = lean_nat_mul(x_53, x_56);
x_58 = lean_unsigned_to_nat(3u);
x_59 = lean_nat_div(x_57, x_58);
lean_dec(x_57);
x_60 = lean_array_get_size(x_55);
x_61 = lean_nat_dec_le(x_59, x_60);
lean_dec(x_60);
lean_dec(x_59);
if (x_61 == 0)
{
lean_object* x_62; 
x_62 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__1___redArg(x_55);
lean_ctor_set(x_29, 1, x_62);
lean_ctor_set(x_29, 0, x_53);
x_37 = x_29;
goto block_44;
}
else
{
lean_ctor_set(x_29, 1, x_55);
lean_ctor_set(x_29, 0, x_53);
x_37 = x_29;
goto block_44;
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_63 = lean_box(0);
x_64 = lean_array_uset(x_35, x_49, x_63);
x_65 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_LCtx_addParam_spec__0___redArg(x_1, x_45, x_50);
x_66 = lean_array_uset(x_64, x_49, x_65);
lean_ctor_set(x_29, 1, x_66);
x_37 = x_29;
goto block_44;
}
block_44:
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; 
if (lean_is_scalar(x_32)) {
 x_38 = lean_alloc_ctor(0, 2, 0);
} else {
 x_38 = x_32;
}
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_31);
x_39 = lean_st_ref_set(x_2, x_38, x_30);
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_39, 0);
lean_dec(x_41);
lean_ctor_set(x_39, 0, x_36);
return x_39;
}
else
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_39, 1);
lean_inc(x_42);
lean_dec(x_39);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_36);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_77; lean_object* x_78; size_t x_79; size_t x_80; size_t x_81; lean_object* x_82; uint8_t x_83; 
x_67 = lean_ctor_get(x_29, 0);
x_68 = lean_ctor_get(x_29, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_29);
x_69 = lean_box(0);
x_77 = lean_box(2);
x_78 = lean_array_get_size(x_68);
x_79 = lean_usize_of_nat(x_78);
lean_dec(x_78);
x_80 = lean_usize_sub(x_79, x_21);
x_81 = lean_usize_land(x_19, x_80);
x_82 = lean_array_uget(x_68, x_81);
x_83 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__0___redArg(x_1, x_82);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; 
x_84 = lean_unsigned_to_nat(1u);
x_85 = lean_nat_add(x_67, x_84);
lean_dec(x_67);
x_86 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_86, 0, x_1);
lean_ctor_set(x_86, 1, x_77);
lean_ctor_set(x_86, 2, x_82);
x_87 = lean_array_uset(x_68, x_81, x_86);
x_88 = lean_unsigned_to_nat(4u);
x_89 = lean_nat_mul(x_85, x_88);
x_90 = lean_unsigned_to_nat(3u);
x_91 = lean_nat_div(x_89, x_90);
lean_dec(x_89);
x_92 = lean_array_get_size(x_87);
x_93 = lean_nat_dec_le(x_91, x_92);
lean_dec(x_92);
lean_dec(x_91);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; 
x_94 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__1___redArg(x_87);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_85);
lean_ctor_set(x_95, 1, x_94);
x_70 = x_95;
goto block_76;
}
else
{
lean_object* x_96; 
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_85);
lean_ctor_set(x_96, 1, x_87);
x_70 = x_96;
goto block_76;
}
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_97 = lean_box(0);
x_98 = lean_array_uset(x_68, x_81, x_97);
x_99 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_LCtx_addParam_spec__0___redArg(x_1, x_77, x_82);
x_100 = lean_array_uset(x_98, x_81, x_99);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_67);
lean_ctor_set(x_101, 1, x_100);
x_70 = x_101;
goto block_76;
}
block_76:
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
if (lean_is_scalar(x_32)) {
 x_71 = lean_alloc_ctor(0, 2, 0);
} else {
 x_71 = x_32;
}
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_31);
x_72 = lean_st_ref_set(x_2, x_71, x_30);
x_73 = lean_ctor_get(x_72, 1);
lean_inc(x_73);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_74 = x_72;
} else {
 lean_dec_ref(x_72);
 x_74 = lean_box(0);
}
if (lean_is_scalar(x_74)) {
 x_75 = lean_alloc_ctor(0, 2, 0);
} else {
 x_75 = x_74;
}
lean_ctor_set(x_75, 0, x_69);
lean_ctor_set(x_75, 1, x_73);
return x_75;
}
}
}
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; uint64_t x_105; uint64_t x_106; uint64_t x_107; uint64_t x_108; uint64_t x_109; uint64_t x_110; uint64_t x_111; size_t x_112; size_t x_113; size_t x_114; size_t x_115; size_t x_116; lean_object* x_117; uint8_t x_118; 
x_102 = lean_ctor_get(x_4, 1);
lean_inc(x_102);
lean_dec(x_4);
x_103 = lean_ctor_get(x_6, 1);
lean_inc(x_103);
lean_dec(x_6);
x_104 = lean_array_get_size(x_103);
x_105 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1561_(x_1);
x_106 = 32;
x_107 = lean_uint64_shift_right(x_105, x_106);
x_108 = lean_uint64_xor(x_105, x_107);
x_109 = 16;
x_110 = lean_uint64_shift_right(x_108, x_109);
x_111 = lean_uint64_xor(x_108, x_110);
x_112 = lean_uint64_to_usize(x_111);
x_113 = lean_usize_of_nat(x_104);
lean_dec(x_104);
x_114 = 1;
x_115 = lean_usize_sub(x_113, x_114);
x_116 = lean_usize_land(x_112, x_115);
x_117 = lean_array_uget(x_103, x_116);
lean_dec(x_103);
x_118 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__0___redArg(x_1, x_117);
lean_dec(x_117);
if (x_118 == 0)
{
lean_object* x_119; lean_object* x_120; 
lean_dec(x_1);
x_119 = lean_box(0);
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_102);
return x_120;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_138; lean_object* x_139; size_t x_140; size_t x_141; size_t x_142; lean_object* x_143; uint8_t x_144; 
x_121 = lean_st_ref_take(x_2, x_102);
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_121, 1);
lean_inc(x_124);
lean_dec(x_121);
x_125 = lean_ctor_get(x_122, 1);
lean_inc(x_125);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 lean_ctor_release(x_122, 1);
 x_126 = x_122;
} else {
 lean_dec_ref(x_122);
 x_126 = lean_box(0);
}
x_127 = lean_ctor_get(x_123, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_123, 1);
lean_inc(x_128);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 lean_ctor_release(x_123, 1);
 x_129 = x_123;
} else {
 lean_dec_ref(x_123);
 x_129 = lean_box(0);
}
x_130 = lean_box(0);
x_138 = lean_box(2);
x_139 = lean_array_get_size(x_128);
x_140 = lean_usize_of_nat(x_139);
lean_dec(x_139);
x_141 = lean_usize_sub(x_140, x_114);
x_142 = lean_usize_land(x_112, x_141);
x_143 = lean_array_uget(x_128, x_142);
x_144 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__0___redArg(x_1, x_143);
if (x_144 == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; uint8_t x_154; 
x_145 = lean_unsigned_to_nat(1u);
x_146 = lean_nat_add(x_127, x_145);
lean_dec(x_127);
x_147 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_147, 0, x_1);
lean_ctor_set(x_147, 1, x_138);
lean_ctor_set(x_147, 2, x_143);
x_148 = lean_array_uset(x_128, x_142, x_147);
x_149 = lean_unsigned_to_nat(4u);
x_150 = lean_nat_mul(x_146, x_149);
x_151 = lean_unsigned_to_nat(3u);
x_152 = lean_nat_div(x_150, x_151);
lean_dec(x_150);
x_153 = lean_array_get_size(x_148);
x_154 = lean_nat_dec_le(x_152, x_153);
lean_dec(x_153);
lean_dec(x_152);
if (x_154 == 0)
{
lean_object* x_155; lean_object* x_156; 
x_155 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__1___redArg(x_148);
if (lean_is_scalar(x_129)) {
 x_156 = lean_alloc_ctor(0, 2, 0);
} else {
 x_156 = x_129;
}
lean_ctor_set(x_156, 0, x_146);
lean_ctor_set(x_156, 1, x_155);
x_131 = x_156;
goto block_137;
}
else
{
lean_object* x_157; 
if (lean_is_scalar(x_129)) {
 x_157 = lean_alloc_ctor(0, 2, 0);
} else {
 x_157 = x_129;
}
lean_ctor_set(x_157, 0, x_146);
lean_ctor_set(x_157, 1, x_148);
x_131 = x_157;
goto block_137;
}
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_158 = lean_box(0);
x_159 = lean_array_uset(x_128, x_142, x_158);
x_160 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_LCtx_addParam_spec__0___redArg(x_1, x_138, x_143);
x_161 = lean_array_uset(x_159, x_142, x_160);
if (lean_is_scalar(x_129)) {
 x_162 = lean_alloc_ctor(0, 2, 0);
} else {
 x_162 = x_129;
}
lean_ctor_set(x_162, 0, x_127);
lean_ctor_set(x_162, 1, x_161);
x_131 = x_162;
goto block_137;
}
block_137:
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
if (lean_is_scalar(x_126)) {
 x_132 = lean_alloc_ctor(0, 2, 0);
} else {
 x_132 = x_126;
}
lean_ctor_set(x_132, 0, x_131);
lean_ctor_set(x_132, 1, x_125);
x_133 = lean_st_ref_set(x_2, x_132, x_124);
x_134 = lean_ctor_get(x_133, 1);
lean_inc(x_134);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 lean_ctor_release(x_133, 1);
 x_135 = x_133;
} else {
 lean_dec_ref(x_133);
 x_135 = lean_box(0);
}
if (lean_is_scalar(x_135)) {
 x_136 = lean_alloc_ctor(0, 2, 0);
} else {
 x_136 = x_135;
}
lean_ctor_set(x_136, 0, x_130);
lean_ctor_set(x_136, 1, x_134);
return x_136;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar___redArg(x_1, x_2, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Std.Data.DHashMap.Internal.AssocList.Basic", 42, 42);
return x_1;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Std.DHashMap.Internal.AssocList.get!", 36, 36);
return x_1;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("key is not present in hash table", 32, 32);
return x_1;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0___redArg___closed__2;
x_2 = lean_unsigned_to_nat(11u);
x_3 = lean_unsigned_to_nat(138u);
x_4 = l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0___redArg___closed__1;
x_5 = l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0___redArg___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0___redArg___closed__3;
x_5 = lean_panic_fn(x_1, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_3, 1);
x_8 = lean_ctor_get(x_3, 2);
x_9 = l_Lean_Compiler_LCNF_FloatLetIn_beqDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_73_(x_6, x_2);
if (x_9 == 0)
{
x_3 = x_8;
goto _start;
}
else
{
lean_dec(x_1);
lean_inc(x_7);
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_LetDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Param_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__0___closed__0;
x_10 = l_ReaderT_instMonad___redArg(x_9);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
lean_dec(x_13);
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_15 = lean_ctor_get(x_12, 0);
x_16 = lean_ctor_get(x_12, 2);
x_17 = lean_ctor_get(x_12, 3);
x_18 = lean_ctor_get(x_12, 4);
x_19 = lean_ctor_get(x_12, 1);
lean_dec(x_19);
x_20 = l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Param_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__0___closed__1;
x_21 = l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Param_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__0___closed__2;
lean_inc(x_15);
x_22 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_22, 0, x_15);
x_23 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_23, 0, x_15);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_25, 0, x_18);
x_26 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_26, 0, x_17);
x_27 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_27, 0, x_16);
lean_ctor_set(x_12, 4, x_25);
lean_ctor_set(x_12, 3, x_26);
lean_ctor_set(x_12, 2, x_27);
lean_ctor_set(x_12, 1, x_20);
lean_ctor_set(x_12, 0, x_24);
lean_ctor_set(x_10, 1, x_21);
x_28 = l_ReaderT_instMonad___redArg(x_10);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_30 = lean_ctor_get(x_28, 0);
x_31 = lean_ctor_get(x_28, 1);
lean_dec(x_31);
x_32 = !lean_is_exclusive(x_30);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_33 = lean_ctor_get(x_30, 0);
x_34 = lean_ctor_get(x_30, 2);
x_35 = lean_ctor_get(x_30, 3);
x_36 = lean_ctor_get(x_30, 4);
x_37 = lean_ctor_get(x_30, 1);
lean_dec(x_37);
x_38 = l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Param_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__0___closed__3;
x_39 = l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Param_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__0___closed__4;
lean_inc(x_33);
x_40 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_40, 0, x_33);
x_41 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_41, 0, x_33);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_43, 0, x_36);
x_44 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_44, 0, x_35);
x_45 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_45, 0, x_34);
lean_ctor_set(x_30, 4, x_43);
lean_ctor_set(x_30, 3, x_44);
lean_ctor_set(x_30, 2, x_45);
lean_ctor_set(x_30, 1, x_38);
lean_ctor_set(x_30, 0, x_42);
lean_ctor_set(x_28, 1, x_39);
x_46 = l_ReaderT_instMonad___redArg(x_28);
x_47 = l_ReaderT_instMonad___redArg(x_46);
x_48 = lean_box(0);
x_49 = l_instInhabitedOfMonad___redArg(x_47, x_48);
x_50 = lean_panic_fn(x_49, x_1);
x_51 = lean_apply_7(x_50, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_51;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_52 = lean_ctor_get(x_30, 0);
x_53 = lean_ctor_get(x_30, 2);
x_54 = lean_ctor_get(x_30, 3);
x_55 = lean_ctor_get(x_30, 4);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_30);
x_56 = l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Param_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__0___closed__3;
x_57 = l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Param_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__0___closed__4;
lean_inc(x_52);
x_58 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_58, 0, x_52);
x_59 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_59, 0, x_52);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
x_61 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_61, 0, x_55);
x_62 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_62, 0, x_54);
x_63 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_63, 0, x_53);
x_64 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_64, 0, x_60);
lean_ctor_set(x_64, 1, x_56);
lean_ctor_set(x_64, 2, x_63);
lean_ctor_set(x_64, 3, x_62);
lean_ctor_set(x_64, 4, x_61);
lean_ctor_set(x_28, 1, x_57);
lean_ctor_set(x_28, 0, x_64);
x_65 = l_ReaderT_instMonad___redArg(x_28);
x_66 = l_ReaderT_instMonad___redArg(x_65);
x_67 = lean_box(0);
x_68 = l_instInhabitedOfMonad___redArg(x_66, x_67);
x_69 = lean_panic_fn(x_68, x_1);
x_70 = lean_apply_7(x_69, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_70;
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_71 = lean_ctor_get(x_28, 0);
lean_inc(x_71);
lean_dec(x_28);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 2);
lean_inc(x_73);
x_74 = lean_ctor_get(x_71, 3);
lean_inc(x_74);
x_75 = lean_ctor_get(x_71, 4);
lean_inc(x_75);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 lean_ctor_release(x_71, 2);
 lean_ctor_release(x_71, 3);
 lean_ctor_release(x_71, 4);
 x_76 = x_71;
} else {
 lean_dec_ref(x_71);
 x_76 = lean_box(0);
}
x_77 = l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Param_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__0___closed__3;
x_78 = l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Param_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__0___closed__4;
lean_inc(x_72);
x_79 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_79, 0, x_72);
x_80 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_80, 0, x_72);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
x_82 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_82, 0, x_75);
x_83 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_83, 0, x_74);
x_84 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_84, 0, x_73);
if (lean_is_scalar(x_76)) {
 x_85 = lean_alloc_ctor(0, 5, 0);
} else {
 x_85 = x_76;
}
lean_ctor_set(x_85, 0, x_81);
lean_ctor_set(x_85, 1, x_77);
lean_ctor_set(x_85, 2, x_84);
lean_ctor_set(x_85, 3, x_83);
lean_ctor_set(x_85, 4, x_82);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_78);
x_87 = l_ReaderT_instMonad___redArg(x_86);
x_88 = l_ReaderT_instMonad___redArg(x_87);
x_89 = lean_box(0);
x_90 = l_instInhabitedOfMonad___redArg(x_88, x_89);
x_91 = lean_panic_fn(x_90, x_1);
x_92 = lean_apply_7(x_91, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_92;
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_93 = lean_ctor_get(x_12, 0);
x_94 = lean_ctor_get(x_12, 2);
x_95 = lean_ctor_get(x_12, 3);
x_96 = lean_ctor_get(x_12, 4);
lean_inc(x_96);
lean_inc(x_95);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_12);
x_97 = l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Param_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__0___closed__1;
x_98 = l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Param_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__0___closed__2;
lean_inc(x_93);
x_99 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_99, 0, x_93);
x_100 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_100, 0, x_93);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
x_102 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_102, 0, x_96);
x_103 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_103, 0, x_95);
x_104 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_104, 0, x_94);
x_105 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_105, 0, x_101);
lean_ctor_set(x_105, 1, x_97);
lean_ctor_set(x_105, 2, x_104);
lean_ctor_set(x_105, 3, x_103);
lean_ctor_set(x_105, 4, x_102);
lean_ctor_set(x_10, 1, x_98);
lean_ctor_set(x_10, 0, x_105);
x_106 = l_ReaderT_instMonad___redArg(x_10);
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
if (lean_is_exclusive(x_106)) {
 lean_ctor_release(x_106, 0);
 lean_ctor_release(x_106, 1);
 x_108 = x_106;
} else {
 lean_dec_ref(x_106);
 x_108 = lean_box(0);
}
x_109 = lean_ctor_get(x_107, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_107, 2);
lean_inc(x_110);
x_111 = lean_ctor_get(x_107, 3);
lean_inc(x_111);
x_112 = lean_ctor_get(x_107, 4);
lean_inc(x_112);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 lean_ctor_release(x_107, 2);
 lean_ctor_release(x_107, 3);
 lean_ctor_release(x_107, 4);
 x_113 = x_107;
} else {
 lean_dec_ref(x_107);
 x_113 = lean_box(0);
}
x_114 = l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Param_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__0___closed__3;
x_115 = l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Param_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__0___closed__4;
lean_inc(x_109);
x_116 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_116, 0, x_109);
x_117 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_117, 0, x_109);
x_118 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set(x_118, 1, x_117);
x_119 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_119, 0, x_112);
x_120 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_120, 0, x_111);
x_121 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_121, 0, x_110);
if (lean_is_scalar(x_113)) {
 x_122 = lean_alloc_ctor(0, 5, 0);
} else {
 x_122 = x_113;
}
lean_ctor_set(x_122, 0, x_118);
lean_ctor_set(x_122, 1, x_114);
lean_ctor_set(x_122, 2, x_121);
lean_ctor_set(x_122, 3, x_120);
lean_ctor_set(x_122, 4, x_119);
if (lean_is_scalar(x_108)) {
 x_123 = lean_alloc_ctor(0, 2, 0);
} else {
 x_123 = x_108;
}
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_115);
x_124 = l_ReaderT_instMonad___redArg(x_123);
x_125 = l_ReaderT_instMonad___redArg(x_124);
x_126 = lean_box(0);
x_127 = l_instInhabitedOfMonad___redArg(x_125, x_126);
x_128 = lean_panic_fn(x_127, x_1);
x_129 = lean_apply_7(x_128, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_129;
}
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_130 = lean_ctor_get(x_10, 0);
lean_inc(x_130);
lean_dec(x_10);
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_130, 2);
lean_inc(x_132);
x_133 = lean_ctor_get(x_130, 3);
lean_inc(x_133);
x_134 = lean_ctor_get(x_130, 4);
lean_inc(x_134);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 lean_ctor_release(x_130, 2);
 lean_ctor_release(x_130, 3);
 lean_ctor_release(x_130, 4);
 x_135 = x_130;
} else {
 lean_dec_ref(x_130);
 x_135 = lean_box(0);
}
x_136 = l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Param_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__0___closed__1;
x_137 = l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Param_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__0___closed__2;
lean_inc(x_131);
x_138 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_138, 0, x_131);
x_139 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_139, 0, x_131);
x_140 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_140, 0, x_138);
lean_ctor_set(x_140, 1, x_139);
x_141 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_141, 0, x_134);
x_142 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_142, 0, x_133);
x_143 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_143, 0, x_132);
if (lean_is_scalar(x_135)) {
 x_144 = lean_alloc_ctor(0, 5, 0);
} else {
 x_144 = x_135;
}
lean_ctor_set(x_144, 0, x_140);
lean_ctor_set(x_144, 1, x_136);
lean_ctor_set(x_144, 2, x_143);
lean_ctor_set(x_144, 3, x_142);
lean_ctor_set(x_144, 4, x_141);
x_145 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_145, 0, x_144);
lean_ctor_set(x_145, 1, x_137);
x_146 = l_ReaderT_instMonad___redArg(x_145);
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
if (lean_is_exclusive(x_146)) {
 lean_ctor_release(x_146, 0);
 lean_ctor_release(x_146, 1);
 x_148 = x_146;
} else {
 lean_dec_ref(x_146);
 x_148 = lean_box(0);
}
x_149 = lean_ctor_get(x_147, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_147, 2);
lean_inc(x_150);
x_151 = lean_ctor_get(x_147, 3);
lean_inc(x_151);
x_152 = lean_ctor_get(x_147, 4);
lean_inc(x_152);
if (lean_is_exclusive(x_147)) {
 lean_ctor_release(x_147, 0);
 lean_ctor_release(x_147, 1);
 lean_ctor_release(x_147, 2);
 lean_ctor_release(x_147, 3);
 lean_ctor_release(x_147, 4);
 x_153 = x_147;
} else {
 lean_dec_ref(x_147);
 x_153 = lean_box(0);
}
x_154 = l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Param_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__0___closed__3;
x_155 = l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Param_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__0___closed__4;
lean_inc(x_149);
x_156 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_156, 0, x_149);
x_157 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_157, 0, x_149);
x_158 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_158, 0, x_156);
lean_ctor_set(x_158, 1, x_157);
x_159 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_159, 0, x_152);
x_160 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_160, 0, x_151);
x_161 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_161, 0, x_150);
if (lean_is_scalar(x_153)) {
 x_162 = lean_alloc_ctor(0, 5, 0);
} else {
 x_162 = x_153;
}
lean_ctor_set(x_162, 0, x_158);
lean_ctor_set(x_162, 1, x_154);
lean_ctor_set(x_162, 2, x_161);
lean_ctor_set(x_162, 3, x_160);
lean_ctor_set(x_162, 4, x_159);
if (lean_is_scalar(x_148)) {
 x_163 = lean_alloc_ctor(0, 2, 0);
} else {
 x_163 = x_148;
}
lean_ctor_set(x_163, 0, x_162);
lean_ctor_set(x_163, 1, x_155);
x_164 = l_ReaderT_instMonad___redArg(x_163);
x_165 = l_ReaderT_instMonad___redArg(x_164);
x_166 = lean_box(0);
x_167 = l_instInhabitedOfMonad___redArg(x_165, x_166);
x_168 = lean_panic_fn(x_167, x_1);
x_169 = lean_apply_7(x_168, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_169;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_LetDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
switch (lean_obj_tag(x_2)) {
case 1:
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_2, 0);
lean_inc(x_16);
lean_dec(x_2);
x_17 = lean_apply_8(x_1, x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_17;
}
case 2:
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_2);
lean_dec(x_1);
x_18 = l_Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Param_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3;
x_19 = l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_LetDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__1_spec__1(x_18, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_19;
}
case 5:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_2, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_2, 1);
lean_inc(x_21);
lean_dec(x_2);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_22 = l_Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_LetDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__1(x_1, x_20, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_2 = x_21;
x_9 = x_23;
goto _start;
}
else
{
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_22;
}
}
case 6:
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_2, 1);
lean_inc(x_25);
x_26 = lean_ctor_get(x_2, 2);
lean_inc(x_26);
lean_dec(x_2);
x_10 = x_25;
x_11 = x_26;
goto block_15;
}
case 7:
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_2, 1);
lean_inc(x_27);
x_28 = lean_ctor_get(x_2, 2);
lean_inc(x_28);
lean_dec(x_2);
x_10 = x_27;
x_11 = x_28;
goto block_15;
}
case 8:
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_2);
lean_dec(x_1);
x_29 = l_Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Param_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3;
x_30 = l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_LetDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__1_spec__1(x_29, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_30;
}
case 11:
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_2);
lean_dec(x_1);
x_31 = l_Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Param_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3;
x_32 = l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_LetDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__1_spec__1(x_31, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_32;
}
default: 
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_9);
return x_34;
}
}
block_15:
{
lean_object* x_12; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_12 = l_Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_LetDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__1(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_2 = x_11;
x_9 = x_13;
goto _start;
}
else
{
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_forFVarM___at___Lean_Compiler_LCNF_LetValue_forFVarM___at___Lean_Compiler_LCNF_LetDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__3_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
case 1:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
lean_dec(x_2);
x_13 = lean_apply_8(x_1, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_13;
}
default: 
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_2, 0);
lean_inc(x_14);
lean_dec(x_2);
x_15 = l_Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_LetDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__1(x_1, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_LetValue_forFVarM___at___Lean_Compiler_LCNF_LetDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__3_spec__4(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_eq(x_3, x_4);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_5);
x_14 = lean_array_uget(x_2, x_3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_15 = l_Lean_Compiler_LCNF_Arg_forFVarM___at___Lean_Compiler_LCNF_LetValue_forFVarM___at___Lean_Compiler_LCNF_LetDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__3_spec__3(x_1, x_14, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = 1;
x_19 = lean_usize_add(x_3, x_18);
x_3 = x_19;
x_5 = x_16;
x_12 = x_17;
goto _start;
}
else
{
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
return x_15;
}
}
else
{
lean_object* x_21; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_5);
lean_ctor_set(x_21, 1, x_12);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_forFVarM___at___Lean_Compiler_LCNF_LetDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 2:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_2, 2);
lean_inc(x_10);
lean_dec(x_2);
x_11 = lean_apply_8(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
case 3:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_ctor_get(x_2, 2);
lean_inc(x_12);
lean_dec(x_2);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_array_get_size(x_12);
x_15 = lean_box(0);
x_16 = lean_nat_dec_lt(x_13, x_14);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_9);
return x_17;
}
else
{
uint8_t x_18; 
x_18 = lean_nat_dec_le(x_14, x_14);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_15);
lean_ctor_set(x_19, 1, x_9);
return x_19;
}
else
{
size_t x_20; size_t x_21; lean_object* x_22; 
x_20 = 0;
x_21 = lean_usize_of_nat(x_14);
lean_dec(x_14);
x_22 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_LetValue_forFVarM___at___Lean_Compiler_LCNF_LetDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__3_spec__4(x_1, x_12, x_20, x_21, x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_12);
return x_22;
}
}
}
case 4:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_2, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_2, 1);
lean_inc(x_24);
lean_dec(x_2);
lean_inc(x_1);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_25 = lean_apply_8(x_1, x_23, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_27 = lean_ctor_get(x_25, 1);
x_28 = lean_ctor_get(x_25, 0);
lean_dec(x_28);
x_29 = lean_unsigned_to_nat(0u);
x_30 = lean_array_get_size(x_24);
x_31 = lean_box(0);
x_32 = lean_nat_dec_lt(x_29, x_30);
if (x_32 == 0)
{
lean_dec(x_30);
lean_dec(x_24);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
lean_ctor_set(x_25, 0, x_31);
return x_25;
}
else
{
uint8_t x_33; 
x_33 = lean_nat_dec_le(x_30, x_30);
if (x_33 == 0)
{
lean_dec(x_30);
lean_dec(x_24);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
lean_ctor_set(x_25, 0, x_31);
return x_25;
}
else
{
size_t x_34; size_t x_35; lean_object* x_36; 
lean_free_object(x_25);
x_34 = 0;
x_35 = lean_usize_of_nat(x_30);
lean_dec(x_30);
x_36 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_LetValue_forFVarM___at___Lean_Compiler_LCNF_LetDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__3_spec__4(x_1, x_24, x_34, x_35, x_31, x_3, x_4, x_5, x_6, x_7, x_8, x_27);
lean_dec(x_24);
return x_36;
}
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_37 = lean_ctor_get(x_25, 1);
lean_inc(x_37);
lean_dec(x_25);
x_38 = lean_unsigned_to_nat(0u);
x_39 = lean_array_get_size(x_24);
x_40 = lean_box(0);
x_41 = lean_nat_dec_lt(x_38, x_39);
if (x_41 == 0)
{
lean_object* x_42; 
lean_dec(x_39);
lean_dec(x_24);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_37);
return x_42;
}
else
{
uint8_t x_43; 
x_43 = lean_nat_dec_le(x_39, x_39);
if (x_43 == 0)
{
lean_object* x_44; 
lean_dec(x_39);
lean_dec(x_24);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_40);
lean_ctor_set(x_44, 1, x_37);
return x_44;
}
else
{
size_t x_45; size_t x_46; lean_object* x_47; 
x_45 = 0;
x_46 = lean_usize_of_nat(x_39);
lean_dec(x_39);
x_47 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_LetValue_forFVarM___at___Lean_Compiler_LCNF_LetDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__3_spec__4(x_1, x_24, x_45, x_46, x_40, x_3, x_4, x_5, x_6, x_7, x_8, x_37);
lean_dec(x_24);
return x_47;
}
}
}
}
else
{
lean_dec(x_24);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_25;
}
}
default: 
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_48 = lean_box(0);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_9);
return x_49;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_2, 2);
lean_inc(x_10);
x_11 = lean_ctor_get(x_2, 3);
lean_inc(x_11);
lean_dec(x_2);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_12 = l_Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_LetDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__1(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = l_Lean_Compiler_LCNF_LetValue_forFVarM___at___Lean_Compiler_LCNF_LetDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__3(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_13);
return x_14;
}
else
{
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_forFVarM___at___Lean_Compiler_LCNF_FunDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__7_spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_2, 2);
lean_inc(x_10);
lean_dec(x_2);
x_11 = l_Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_LetDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__1(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_forCodeM___at___Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FunDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__7_spec__8_spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_1, 2);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_apply_8(x_2, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_apply_8(x_2, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FunDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__7_spec__8_spec__9(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_eq(x_3, x_4);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_5);
x_14 = lean_array_uget(x_2, x_3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_15 = l_Lean_Compiler_LCNF_Param_forFVarM___at___Lean_Compiler_LCNF_FunDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__7_spec__7(x_1, x_14, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = 1;
x_19 = lean_usize_add(x_3, x_18);
x_3 = x_19;
x_5 = x_16;
x_12 = x_17;
goto _start;
}
else
{
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
return x_15;
}
}
else
{
lean_object* x_21; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_5);
lean_ctor_set(x_21, 1, x_12);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FunDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__7_spec__8_spec__10___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FunDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__7_spec__8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FunDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__7_spec__8_spec__10(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_eq(x_3, x_4);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_5);
lean_inc(x_1);
x_14 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FunDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__7_spec__8_spec__10___lam__0), 9, 1);
lean_closure_set(x_14, 0, x_1);
x_15 = lean_array_uget(x_2, x_3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_16 = l_Lean_Compiler_LCNF_Alt_forCodeM___at___Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FunDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__7_spec__8_spec__8(x_15, x_14, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = 1;
x_20 = lean_usize_add(x_3, x_19);
x_3 = x_20;
x_5 = x_17;
x_12 = x_18;
goto _start;
}
else
{
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
return x_16;
}
}
else
{
lean_object* x_22; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_5);
lean_ctor_set(x_22, 1, x_12);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FunDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__7_spec__8___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_13 = l_Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_LetDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__1(x_1, x_2, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_15 = l_Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FunDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__7_spec__8(x_1, x_3, x_6, x_7, x_8, x_9, x_10, x_11, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = l_Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FunDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__7_spec__8(x_1, x_4, x_6, x_7, x_8, x_9, x_10, x_11, x_16);
return x_17;
}
else
{
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
return x_15;
}
}
else
{
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FunDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__7_spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_2, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_2, 1);
lean_inc(x_34);
lean_dec(x_2);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_35 = l_Lean_Compiler_LCNF_LetDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1(x_1, x_33, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec(x_35);
x_2 = x_34;
x_9 = x_36;
goto _start;
}
else
{
lean_dec(x_34);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_35;
}
}
case 3:
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_2, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_2, 1);
lean_inc(x_39);
lean_dec(x_2);
lean_inc(x_1);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_40 = lean_apply_8(x_1, x_38, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_40) == 0)
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_42 = lean_ctor_get(x_40, 1);
x_43 = lean_ctor_get(x_40, 0);
lean_dec(x_43);
x_44 = lean_unsigned_to_nat(0u);
x_45 = lean_array_get_size(x_39);
x_46 = lean_box(0);
x_47 = lean_nat_dec_lt(x_44, x_45);
if (x_47 == 0)
{
lean_dec(x_45);
lean_dec(x_39);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
lean_ctor_set(x_40, 0, x_46);
return x_40;
}
else
{
uint8_t x_48; 
x_48 = lean_nat_dec_le(x_45, x_45);
if (x_48 == 0)
{
lean_dec(x_45);
lean_dec(x_39);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
lean_ctor_set(x_40, 0, x_46);
return x_40;
}
else
{
size_t x_49; size_t x_50; lean_object* x_51; 
lean_free_object(x_40);
x_49 = 0;
x_50 = lean_usize_of_nat(x_45);
lean_dec(x_45);
x_51 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_LetValue_forFVarM___at___Lean_Compiler_LCNF_LetDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__3_spec__4(x_1, x_39, x_49, x_50, x_46, x_3, x_4, x_5, x_6, x_7, x_8, x_42);
lean_dec(x_39);
return x_51;
}
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_52 = lean_ctor_get(x_40, 1);
lean_inc(x_52);
lean_dec(x_40);
x_53 = lean_unsigned_to_nat(0u);
x_54 = lean_array_get_size(x_39);
x_55 = lean_box(0);
x_56 = lean_nat_dec_lt(x_53, x_54);
if (x_56 == 0)
{
lean_object* x_57; 
lean_dec(x_54);
lean_dec(x_39);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_52);
return x_57;
}
else
{
uint8_t x_58; 
x_58 = lean_nat_dec_le(x_54, x_54);
if (x_58 == 0)
{
lean_object* x_59; 
lean_dec(x_54);
lean_dec(x_39);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_55);
lean_ctor_set(x_59, 1, x_52);
return x_59;
}
else
{
size_t x_60; size_t x_61; lean_object* x_62; 
x_60 = 0;
x_61 = lean_usize_of_nat(x_54);
lean_dec(x_54);
x_62 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_LetValue_forFVarM___at___Lean_Compiler_LCNF_LetDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__3_spec__4(x_1, x_39, x_60, x_61, x_55, x_3, x_4, x_5, x_6, x_7, x_8, x_52);
lean_dec(x_39);
return x_62;
}
}
}
}
else
{
lean_dec(x_39);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_40;
}
}
case 4:
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_63 = lean_ctor_get(x_2, 0);
lean_inc(x_63);
lean_dec(x_2);
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 2);
lean_inc(x_65);
x_66 = lean_ctor_get(x_63, 3);
lean_inc(x_66);
lean_dec(x_63);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_67 = l_Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_LetDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__1(x_1, x_64, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_67, 1);
lean_inc(x_68);
lean_dec(x_67);
lean_inc(x_1);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_69 = lean_apply_8(x_1, x_65, x_3, x_4, x_5, x_6, x_7, x_8, x_68);
if (lean_obj_tag(x_69) == 0)
{
uint8_t x_70; 
x_70 = !lean_is_exclusive(x_69);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_71 = lean_ctor_get(x_69, 1);
x_72 = lean_ctor_get(x_69, 0);
lean_dec(x_72);
x_73 = lean_unsigned_to_nat(0u);
x_74 = lean_array_get_size(x_66);
x_75 = lean_box(0);
x_76 = lean_nat_dec_lt(x_73, x_74);
if (x_76 == 0)
{
lean_dec(x_74);
lean_dec(x_66);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
lean_ctor_set(x_69, 0, x_75);
return x_69;
}
else
{
uint8_t x_77; 
x_77 = lean_nat_dec_le(x_74, x_74);
if (x_77 == 0)
{
lean_dec(x_74);
lean_dec(x_66);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
lean_ctor_set(x_69, 0, x_75);
return x_69;
}
else
{
size_t x_78; size_t x_79; lean_object* x_80; 
lean_free_object(x_69);
x_78 = 0;
x_79 = lean_usize_of_nat(x_74);
lean_dec(x_74);
x_80 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FunDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__7_spec__8_spec__10(x_1, x_66, x_78, x_79, x_75, x_3, x_4, x_5, x_6, x_7, x_8, x_71);
lean_dec(x_66);
return x_80;
}
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; 
x_81 = lean_ctor_get(x_69, 1);
lean_inc(x_81);
lean_dec(x_69);
x_82 = lean_unsigned_to_nat(0u);
x_83 = lean_array_get_size(x_66);
x_84 = lean_box(0);
x_85 = lean_nat_dec_lt(x_82, x_83);
if (x_85 == 0)
{
lean_object* x_86; 
lean_dec(x_83);
lean_dec(x_66);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_81);
return x_86;
}
else
{
uint8_t x_87; 
x_87 = lean_nat_dec_le(x_83, x_83);
if (x_87 == 0)
{
lean_object* x_88; 
lean_dec(x_83);
lean_dec(x_66);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_84);
lean_ctor_set(x_88, 1, x_81);
return x_88;
}
else
{
size_t x_89; size_t x_90; lean_object* x_91; 
x_89 = 0;
x_90 = lean_usize_of_nat(x_83);
lean_dec(x_83);
x_91 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FunDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__7_spec__8_spec__10(x_1, x_66, x_89, x_90, x_84, x_3, x_4, x_5, x_6, x_7, x_8, x_81);
lean_dec(x_66);
return x_91;
}
}
}
}
else
{
lean_dec(x_66);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_69;
}
}
else
{
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_67;
}
}
case 5:
{
lean_object* x_92; lean_object* x_93; 
x_92 = lean_ctor_get(x_2, 0);
lean_inc(x_92);
lean_dec(x_2);
x_93 = lean_apply_8(x_1, x_92, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_93;
}
case 6:
{
lean_object* x_94; lean_object* x_95; 
x_94 = lean_ctor_get(x_2, 0);
lean_inc(x_94);
lean_dec(x_2);
x_95 = l_Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_LetDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__1(x_1, x_94, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_95;
}
default: 
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_ctor_get(x_2, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_2, 1);
lean_inc(x_97);
lean_dec(x_2);
x_10 = x_96;
x_11 = x_97;
goto block_32;
}
}
block_32:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_12 = lean_ctor_get(x_10, 2);
lean_inc(x_12);
x_13 = lean_ctor_get(x_10, 3);
lean_inc(x_13);
x_14 = lean_ctor_get(x_10, 4);
lean_inc(x_14);
lean_dec(x_10);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_array_get_size(x_12);
x_17 = lean_nat_dec_lt(x_15, x_16);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_16);
lean_dec(x_12);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_18 = l_Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_LetDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__1(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_20 = l_Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FunDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__7_spec__8(x_1, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_2 = x_11;
x_9 = x_21;
goto _start;
}
else
{
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_20;
}
}
else
{
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_18;
}
}
else
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_box(0);
x_24 = lean_nat_dec_le(x_16, x_16);
if (x_24 == 0)
{
lean_object* x_25; 
lean_dec(x_16);
lean_dec(x_12);
x_25 = l_Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FunDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__7_spec__8___lam__0(x_1, x_13, x_14, x_11, x_23, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_25;
}
else
{
size_t x_26; size_t x_27; lean_object* x_28; 
x_26 = 0;
x_27 = lean_usize_of_nat(x_16);
lean_dec(x_16);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_28 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FunDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__7_spec__8_spec__9(x_1, x_12, x_26, x_27, x_23, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_12);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = l_Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FunDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__7_spec__8___lam__0(x_1, x_13, x_14, x_11, x_29, x_3, x_4, x_5, x_6, x_7, x_8, x_30);
lean_dec(x_29);
return x_31;
}
else
{
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_28;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__7___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_12 = l_Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_LetDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__1(x_1, x_2, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = l_Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FunDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__7_spec__8(x_1, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_13);
return x_14;
}
else
{
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_10 = lean_ctor_get(x_2, 2);
lean_inc(x_10);
x_11 = lean_ctor_get(x_2, 3);
lean_inc(x_11);
x_12 = lean_ctor_get(x_2, 4);
lean_inc(x_12);
lean_dec(x_2);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_array_get_size(x_10);
x_15 = lean_nat_dec_lt(x_13, x_14);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_14);
lean_dec(x_10);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_16 = l_Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_LetDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__1(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = l_Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FunDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__7_spec__8(x_1, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_17);
return x_18;
}
else
{
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_16;
}
}
else
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_box(0);
x_20 = lean_nat_dec_le(x_14, x_14);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_14);
lean_dec(x_10);
x_21 = l_Lean_Compiler_LCNF_FunDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__7___lam__0(x_1, x_11, x_12, x_19, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_21;
}
else
{
size_t x_22; size_t x_23; lean_object* x_24; 
x_22 = 0;
x_23 = lean_usize_of_nat(x_14);
lean_dec(x_14);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_24 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FunDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__7_spec__8_spec__9(x_1, x_10, x_22, x_23, x_19, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_10);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_Lean_Compiler_LCNF_FunDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__7___lam__0(x_1, x_11, x_12, x_25, x_3, x_4, x_5, x_6, x_7, x_8, x_26);
lean_dec(x_25);
return x_27;
}
else
{
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_24;
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_FloatLetIn_dontFloat___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar___boxed), 8, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_dontFloat(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_20; lean_object* x_21; lean_object* x_125; 
x_20 = lean_box(0);
x_125 = l_Lean_Compiler_LCNF_FloatLetIn_dontFloat___closed__0;
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_126; lean_object* x_127; 
x_126 = lean_ctor_get(x_1, 0);
lean_inc(x_126);
lean_inc(x_2);
x_127 = l_Lean_Compiler_LCNF_LetDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1(x_125, x_126, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
x_21 = x_127;
goto block_124;
}
else
{
lean_object* x_128; lean_object* x_129; 
x_128 = lean_ctor_get(x_1, 0);
lean_inc(x_128);
lean_inc(x_2);
x_129 = l_Lean_Compiler_LCNF_FunDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__7(x_125, x_128, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
x_21 = x_129;
goto block_124;
}
block_19:
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_st_ref_set(x_2, x_13, x_9);
lean_dec(x_2);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_14, 0);
lean_dec(x_16);
lean_ctor_set(x_14, 0, x_10);
return x_14;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_10);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
block_124:
{
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_st_ref_take(x_2, x_22);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
x_27 = !lean_is_exclusive(x_24);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_28 = lean_ctor_get(x_24, 0);
x_29 = lean_ctor_get(x_24, 1);
lean_dec(x_29);
x_30 = !lean_is_exclusive(x_25);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; size_t x_36; size_t x_37; size_t x_38; size_t x_39; size_t x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_31 = lean_ctor_get(x_25, 0);
x_32 = lean_ctor_get(x_25, 1);
x_33 = lean_box(0);
x_34 = lean_box(2);
x_35 = lean_array_get_size(x_32);
x_36 = l_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___closed__5;
x_37 = lean_usize_of_nat(x_35);
lean_dec(x_35);
x_38 = 1;
x_39 = lean_usize_sub(x_37, x_38);
x_40 = lean_usize_land(x_36, x_39);
x_41 = lean_array_uget(x_32, x_40);
x_42 = l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0___redArg(x_20, x_34, x_41);
lean_ctor_set_tag(x_24, 1);
lean_ctor_set(x_24, 1, x_42);
lean_ctor_set(x_24, 0, x_1);
x_43 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0___redArg(x_34, x_41);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_44 = lean_unsigned_to_nat(1u);
x_45 = lean_nat_add(x_31, x_44);
lean_dec(x_31);
x_46 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_46, 0, x_34);
lean_ctor_set(x_46, 1, x_24);
lean_ctor_set(x_46, 2, x_41);
x_47 = lean_array_uset(x_32, x_40, x_46);
x_48 = lean_unsigned_to_nat(4u);
x_49 = lean_nat_mul(x_45, x_48);
x_50 = lean_unsigned_to_nat(3u);
x_51 = lean_nat_div(x_49, x_50);
lean_dec(x_49);
x_52 = lean_array_get_size(x_47);
x_53 = lean_nat_dec_le(x_51, x_52);
lean_dec(x_52);
lean_dec(x_51);
if (x_53 == 0)
{
lean_object* x_54; 
x_54 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__1___redArg(x_47);
lean_ctor_set(x_25, 1, x_54);
lean_ctor_set(x_25, 0, x_45);
x_9 = x_26;
x_10 = x_33;
x_11 = x_28;
x_12 = x_25;
goto block_19;
}
else
{
lean_ctor_set(x_25, 1, x_47);
lean_ctor_set(x_25, 0, x_45);
x_9 = x_26;
x_10 = x_33;
x_11 = x_28;
x_12 = x_25;
goto block_19;
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_55 = lean_box(0);
x_56 = lean_array_uset(x_32, x_40, x_55);
x_57 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__4___redArg(x_34, x_24, x_41);
x_58 = lean_array_uset(x_56, x_40, x_57);
lean_ctor_set(x_25, 1, x_58);
x_9 = x_26;
x_10 = x_33;
x_11 = x_28;
x_12 = x_25;
goto block_19;
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; size_t x_64; size_t x_65; size_t x_66; size_t x_67; size_t x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_59 = lean_ctor_get(x_25, 0);
x_60 = lean_ctor_get(x_25, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_25);
x_61 = lean_box(0);
x_62 = lean_box(2);
x_63 = lean_array_get_size(x_60);
x_64 = l_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___closed__5;
x_65 = lean_usize_of_nat(x_63);
lean_dec(x_63);
x_66 = 1;
x_67 = lean_usize_sub(x_65, x_66);
x_68 = lean_usize_land(x_64, x_67);
x_69 = lean_array_uget(x_60, x_68);
x_70 = l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0___redArg(x_20, x_62, x_69);
lean_ctor_set_tag(x_24, 1);
lean_ctor_set(x_24, 1, x_70);
lean_ctor_set(x_24, 0, x_1);
x_71 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0___redArg(x_62, x_69);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; 
x_72 = lean_unsigned_to_nat(1u);
x_73 = lean_nat_add(x_59, x_72);
lean_dec(x_59);
x_74 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_74, 0, x_62);
lean_ctor_set(x_74, 1, x_24);
lean_ctor_set(x_74, 2, x_69);
x_75 = lean_array_uset(x_60, x_68, x_74);
x_76 = lean_unsigned_to_nat(4u);
x_77 = lean_nat_mul(x_73, x_76);
x_78 = lean_unsigned_to_nat(3u);
x_79 = lean_nat_div(x_77, x_78);
lean_dec(x_77);
x_80 = lean_array_get_size(x_75);
x_81 = lean_nat_dec_le(x_79, x_80);
lean_dec(x_80);
lean_dec(x_79);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; 
x_82 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__1___redArg(x_75);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_73);
lean_ctor_set(x_83, 1, x_82);
x_9 = x_26;
x_10 = x_61;
x_11 = x_28;
x_12 = x_83;
goto block_19;
}
else
{
lean_object* x_84; 
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_73);
lean_ctor_set(x_84, 1, x_75);
x_9 = x_26;
x_10 = x_61;
x_11 = x_28;
x_12 = x_84;
goto block_19;
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_85 = lean_box(0);
x_86 = lean_array_uset(x_60, x_68, x_85);
x_87 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__4___redArg(x_62, x_24, x_69);
x_88 = lean_array_uset(x_86, x_68, x_87);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_59);
lean_ctor_set(x_89, 1, x_88);
x_9 = x_26;
x_10 = x_61;
x_11 = x_28;
x_12 = x_89;
goto block_19;
}
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; size_t x_97; size_t x_98; size_t x_99; size_t x_100; size_t x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; 
x_90 = lean_ctor_get(x_24, 0);
lean_inc(x_90);
lean_dec(x_24);
x_91 = lean_ctor_get(x_25, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_25, 1);
lean_inc(x_92);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_93 = x_25;
} else {
 lean_dec_ref(x_25);
 x_93 = lean_box(0);
}
x_94 = lean_box(0);
x_95 = lean_box(2);
x_96 = lean_array_get_size(x_92);
x_97 = l_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___closed__5;
x_98 = lean_usize_of_nat(x_96);
lean_dec(x_96);
x_99 = 1;
x_100 = lean_usize_sub(x_98, x_99);
x_101 = lean_usize_land(x_97, x_100);
x_102 = lean_array_uget(x_92, x_101);
x_103 = l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0___redArg(x_20, x_95, x_102);
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_1);
lean_ctor_set(x_104, 1, x_103);
x_105 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0___redArg(x_95, x_102);
if (x_105 == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; 
x_106 = lean_unsigned_to_nat(1u);
x_107 = lean_nat_add(x_91, x_106);
lean_dec(x_91);
x_108 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_108, 0, x_95);
lean_ctor_set(x_108, 1, x_104);
lean_ctor_set(x_108, 2, x_102);
x_109 = lean_array_uset(x_92, x_101, x_108);
x_110 = lean_unsigned_to_nat(4u);
x_111 = lean_nat_mul(x_107, x_110);
x_112 = lean_unsigned_to_nat(3u);
x_113 = lean_nat_div(x_111, x_112);
lean_dec(x_111);
x_114 = lean_array_get_size(x_109);
x_115 = lean_nat_dec_le(x_113, x_114);
lean_dec(x_114);
lean_dec(x_113);
if (x_115 == 0)
{
lean_object* x_116; lean_object* x_117; 
x_116 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__1___redArg(x_109);
if (lean_is_scalar(x_93)) {
 x_117 = lean_alloc_ctor(0, 2, 0);
} else {
 x_117 = x_93;
}
lean_ctor_set(x_117, 0, x_107);
lean_ctor_set(x_117, 1, x_116);
x_9 = x_26;
x_10 = x_94;
x_11 = x_90;
x_12 = x_117;
goto block_19;
}
else
{
lean_object* x_118; 
if (lean_is_scalar(x_93)) {
 x_118 = lean_alloc_ctor(0, 2, 0);
} else {
 x_118 = x_93;
}
lean_ctor_set(x_118, 0, x_107);
lean_ctor_set(x_118, 1, x_109);
x_9 = x_26;
x_10 = x_94;
x_11 = x_90;
x_12 = x_118;
goto block_19;
}
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_119 = lean_box(0);
x_120 = lean_array_uset(x_92, x_101, x_119);
x_121 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__4___redArg(x_95, x_104, x_102);
x_122 = lean_array_uset(x_120, x_101, x_121);
if (lean_is_scalar(x_93)) {
 x_123 = lean_alloc_ctor(0, 2, 0);
} else {
 x_123 = x_93;
}
lean_ctor_set(x_123, 0, x_91);
lean_ctor_set(x_123, 1, x_122);
x_9 = x_26;
x_10 = x_94;
x_11 = x_90;
x_12 = x_123;
goto block_19;
}
}
}
else
{
lean_dec(x_2);
lean_dec(x_1);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0___redArg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_LetValue_forFVarM___at___Lean_Compiler_LCNF_LetDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__3_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_LetValue_forFVarM___at___Lean_Compiler_LCNF_LetDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__3_spec__4(x_1, x_2, x_13, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FunDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__7_spec__8_spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FunDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__7_spec__8_spec__9(x_1, x_2, x_13, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FunDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__7_spec__8_spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FunDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__7_spec__8_spec__10(x_1, x_2, x_13, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FunDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__7_spec__8___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FunDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__7_spec__8___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_5);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__7___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Compiler_LCNF_FunDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__7___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_4);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_float_goFVar___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_16; uint8_t x_17; 
x_16 = lean_st_ref_get(x_3, x_4);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_98; lean_object* x_99; lean_object* x_100; uint64_t x_101; uint64_t x_102; uint64_t x_103; uint64_t x_104; uint64_t x_105; uint64_t x_106; uint64_t x_107; size_t x_108; size_t x_109; size_t x_110; size_t x_111; size_t x_112; lean_object* x_113; lean_object* x_114; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_16, 1);
x_98 = lean_ctor_get(x_18, 0);
lean_inc(x_98);
lean_dec(x_18);
x_99 = lean_ctor_get(x_98, 1);
lean_inc(x_99);
lean_dec(x_98);
x_100 = lean_array_get_size(x_99);
x_101 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1561_(x_1);
x_102 = 32;
x_103 = lean_uint64_shift_right(x_101, x_102);
x_104 = lean_uint64_xor(x_101, x_103);
x_105 = 16;
x_106 = lean_uint64_shift_right(x_104, x_105);
x_107 = lean_uint64_xor(x_104, x_106);
x_108 = lean_uint64_to_usize(x_107);
x_109 = lean_usize_of_nat(x_100);
lean_dec(x_100);
x_110 = 1;
x_111 = lean_usize_sub(x_109, x_110);
x_112 = lean_usize_land(x_108, x_111);
x_113 = lean_array_uget(x_99, x_112);
lean_dec(x_99);
x_114 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Compiler_LCNF_getType_spec__0___redArg(x_1, x_113);
lean_dec(x_113);
if (lean_obj_tag(x_114) == 0)
{
lean_object* x_115; 
lean_dec(x_2);
lean_dec(x_1);
x_115 = lean_box(0);
lean_ctor_set(x_16, 0, x_115);
return x_16;
}
else
{
lean_object* x_116; lean_object* x_117; uint8_t x_118; 
x_116 = lean_ctor_get(x_114, 0);
lean_inc(x_116);
lean_dec(x_114);
x_117 = lean_box(3);
x_118 = l_Lean_Compiler_LCNF_FloatLetIn_beqDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_73_(x_116, x_117);
if (x_118 == 0)
{
uint8_t x_119; 
x_119 = l_Lean_Compiler_LCNF_FloatLetIn_beqDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_73_(x_116, x_2);
lean_dec(x_2);
lean_dec(x_116);
if (x_119 == 0)
{
lean_free_object(x_16);
goto block_97;
}
else
{
if (x_118 == 0)
{
lean_object* x_120; 
lean_dec(x_1);
x_120 = lean_box(0);
lean_ctor_set(x_16, 0, x_120);
return x_16;
}
else
{
lean_free_object(x_16);
goto block_97;
}
}
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; uint8_t x_127; 
lean_dec(x_116);
lean_free_object(x_16);
x_121 = lean_st_ref_take(x_3, x_19);
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_121, 1);
lean_inc(x_124);
lean_dec(x_121);
x_125 = lean_ctor_get(x_122, 1);
lean_inc(x_125);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 lean_ctor_release(x_122, 1);
 x_126 = x_122;
} else {
 lean_dec_ref(x_122);
 x_126 = lean_box(0);
}
x_127 = !lean_is_exclusive(x_123);
if (x_127 == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_139; size_t x_140; size_t x_141; size_t x_142; lean_object* x_143; uint8_t x_144; 
x_128 = lean_ctor_get(x_123, 0);
x_129 = lean_ctor_get(x_123, 1);
x_130 = lean_box(0);
x_139 = lean_array_get_size(x_129);
x_140 = lean_usize_of_nat(x_139);
lean_dec(x_139);
x_141 = lean_usize_sub(x_140, x_110);
x_142 = lean_usize_land(x_108, x_141);
x_143 = lean_array_uget(x_129, x_142);
x_144 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__0___redArg(x_1, x_143);
if (x_144 == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; uint8_t x_154; 
x_145 = lean_unsigned_to_nat(1u);
x_146 = lean_nat_add(x_128, x_145);
lean_dec(x_128);
x_147 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_147, 0, x_1);
lean_ctor_set(x_147, 1, x_2);
lean_ctor_set(x_147, 2, x_143);
x_148 = lean_array_uset(x_129, x_142, x_147);
x_149 = lean_unsigned_to_nat(4u);
x_150 = lean_nat_mul(x_146, x_149);
x_151 = lean_unsigned_to_nat(3u);
x_152 = lean_nat_div(x_150, x_151);
lean_dec(x_150);
x_153 = lean_array_get_size(x_148);
x_154 = lean_nat_dec_le(x_152, x_153);
lean_dec(x_153);
lean_dec(x_152);
if (x_154 == 0)
{
lean_object* x_155; 
x_155 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__1___redArg(x_148);
lean_ctor_set(x_123, 1, x_155);
lean_ctor_set(x_123, 0, x_146);
x_131 = x_123;
goto block_138;
}
else
{
lean_ctor_set(x_123, 1, x_148);
lean_ctor_set(x_123, 0, x_146);
x_131 = x_123;
goto block_138;
}
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_156 = lean_box(0);
x_157 = lean_array_uset(x_129, x_142, x_156);
x_158 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_LCtx_addParam_spec__0___redArg(x_1, x_2, x_143);
x_159 = lean_array_uset(x_157, x_142, x_158);
lean_ctor_set(x_123, 1, x_159);
x_131 = x_123;
goto block_138;
}
block_138:
{
lean_object* x_132; lean_object* x_133; uint8_t x_134; 
if (lean_is_scalar(x_126)) {
 x_132 = lean_alloc_ctor(0, 2, 0);
} else {
 x_132 = x_126;
}
lean_ctor_set(x_132, 0, x_131);
lean_ctor_set(x_132, 1, x_125);
x_133 = lean_st_ref_set(x_3, x_132, x_124);
x_134 = !lean_is_exclusive(x_133);
if (x_134 == 0)
{
lean_object* x_135; 
x_135 = lean_ctor_get(x_133, 0);
lean_dec(x_135);
lean_ctor_set(x_133, 0, x_130);
return x_133;
}
else
{
lean_object* x_136; lean_object* x_137; 
x_136 = lean_ctor_get(x_133, 1);
lean_inc(x_136);
lean_dec(x_133);
x_137 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_137, 0, x_130);
lean_ctor_set(x_137, 1, x_136);
return x_137;
}
}
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_170; size_t x_171; size_t x_172; size_t x_173; lean_object* x_174; uint8_t x_175; 
x_160 = lean_ctor_get(x_123, 0);
x_161 = lean_ctor_get(x_123, 1);
lean_inc(x_161);
lean_inc(x_160);
lean_dec(x_123);
x_162 = lean_box(0);
x_170 = lean_array_get_size(x_161);
x_171 = lean_usize_of_nat(x_170);
lean_dec(x_170);
x_172 = lean_usize_sub(x_171, x_110);
x_173 = lean_usize_land(x_108, x_172);
x_174 = lean_array_uget(x_161, x_173);
x_175 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__0___redArg(x_1, x_174);
if (x_175 == 0)
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; uint8_t x_185; 
x_176 = lean_unsigned_to_nat(1u);
x_177 = lean_nat_add(x_160, x_176);
lean_dec(x_160);
x_178 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_178, 0, x_1);
lean_ctor_set(x_178, 1, x_2);
lean_ctor_set(x_178, 2, x_174);
x_179 = lean_array_uset(x_161, x_173, x_178);
x_180 = lean_unsigned_to_nat(4u);
x_181 = lean_nat_mul(x_177, x_180);
x_182 = lean_unsigned_to_nat(3u);
x_183 = lean_nat_div(x_181, x_182);
lean_dec(x_181);
x_184 = lean_array_get_size(x_179);
x_185 = lean_nat_dec_le(x_183, x_184);
lean_dec(x_184);
lean_dec(x_183);
if (x_185 == 0)
{
lean_object* x_186; lean_object* x_187; 
x_186 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__1___redArg(x_179);
x_187 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_187, 0, x_177);
lean_ctor_set(x_187, 1, x_186);
x_163 = x_187;
goto block_169;
}
else
{
lean_object* x_188; 
x_188 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_188, 0, x_177);
lean_ctor_set(x_188, 1, x_179);
x_163 = x_188;
goto block_169;
}
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_189 = lean_box(0);
x_190 = lean_array_uset(x_161, x_173, x_189);
x_191 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_LCtx_addParam_spec__0___redArg(x_1, x_2, x_174);
x_192 = lean_array_uset(x_190, x_173, x_191);
x_193 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_193, 0, x_160);
lean_ctor_set(x_193, 1, x_192);
x_163 = x_193;
goto block_169;
}
block_169:
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
if (lean_is_scalar(x_126)) {
 x_164 = lean_alloc_ctor(0, 2, 0);
} else {
 x_164 = x_126;
}
lean_ctor_set(x_164, 0, x_163);
lean_ctor_set(x_164, 1, x_125);
x_165 = lean_st_ref_set(x_3, x_164, x_124);
x_166 = lean_ctor_get(x_165, 1);
lean_inc(x_166);
if (lean_is_exclusive(x_165)) {
 lean_ctor_release(x_165, 0);
 lean_ctor_release(x_165, 1);
 x_167 = x_165;
} else {
 lean_dec_ref(x_165);
 x_167 = lean_box(0);
}
if (lean_is_scalar(x_167)) {
 x_168 = lean_alloc_ctor(0, 2, 0);
} else {
 x_168 = x_167;
}
lean_ctor_set(x_168, 0, x_162);
lean_ctor_set(x_168, 1, x_166);
return x_168;
}
}
}
}
block_97:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_20 = lean_st_ref_take(x_3, x_19);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = !lean_is_exclusive(x_22);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint64_t x_31; uint64_t x_32; uint64_t x_33; uint64_t x_34; uint64_t x_35; uint64_t x_36; uint64_t x_37; size_t x_38; size_t x_39; size_t x_40; size_t x_41; size_t x_42; lean_object* x_43; uint8_t x_44; 
x_26 = lean_ctor_get(x_22, 0);
x_27 = lean_ctor_get(x_22, 1);
x_28 = lean_box(0);
x_29 = lean_box(2);
x_30 = lean_array_get_size(x_27);
x_31 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1561_(x_1);
x_32 = 32;
x_33 = lean_uint64_shift_right(x_31, x_32);
x_34 = lean_uint64_xor(x_31, x_33);
x_35 = 16;
x_36 = lean_uint64_shift_right(x_34, x_35);
x_37 = lean_uint64_xor(x_34, x_36);
x_38 = lean_uint64_to_usize(x_37);
x_39 = lean_usize_of_nat(x_30);
lean_dec(x_30);
x_40 = 1;
x_41 = lean_usize_sub(x_39, x_40);
x_42 = lean_usize_land(x_38, x_41);
x_43 = lean_array_uget(x_27, x_42);
x_44 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__0___redArg(x_1, x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_45 = lean_unsigned_to_nat(1u);
x_46 = lean_nat_add(x_26, x_45);
lean_dec(x_26);
x_47 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_47, 0, x_1);
lean_ctor_set(x_47, 1, x_29);
lean_ctor_set(x_47, 2, x_43);
x_48 = lean_array_uset(x_27, x_42, x_47);
x_49 = lean_unsigned_to_nat(4u);
x_50 = lean_nat_mul(x_46, x_49);
x_51 = lean_unsigned_to_nat(3u);
x_52 = lean_nat_div(x_50, x_51);
lean_dec(x_50);
x_53 = lean_array_get_size(x_48);
x_54 = lean_nat_dec_le(x_52, x_53);
lean_dec(x_53);
lean_dec(x_52);
if (x_54 == 0)
{
lean_object* x_55; 
x_55 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__1___redArg(x_48);
lean_ctor_set(x_22, 1, x_55);
lean_ctor_set(x_22, 0, x_46);
x_5 = x_24;
x_6 = x_28;
x_7 = x_23;
x_8 = x_22;
goto block_15;
}
else
{
lean_ctor_set(x_22, 1, x_48);
lean_ctor_set(x_22, 0, x_46);
x_5 = x_24;
x_6 = x_28;
x_7 = x_23;
x_8 = x_22;
goto block_15;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_56 = lean_box(0);
x_57 = lean_array_uset(x_27, x_42, x_56);
x_58 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_LCtx_addParam_spec__0___redArg(x_1, x_29, x_43);
x_59 = lean_array_uset(x_57, x_42, x_58);
lean_ctor_set(x_22, 1, x_59);
x_5 = x_24;
x_6 = x_28;
x_7 = x_23;
x_8 = x_22;
goto block_15;
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint64_t x_65; uint64_t x_66; uint64_t x_67; uint64_t x_68; uint64_t x_69; uint64_t x_70; uint64_t x_71; size_t x_72; size_t x_73; size_t x_74; size_t x_75; size_t x_76; lean_object* x_77; uint8_t x_78; 
x_60 = lean_ctor_get(x_22, 0);
x_61 = lean_ctor_get(x_22, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_22);
x_62 = lean_box(0);
x_63 = lean_box(2);
x_64 = lean_array_get_size(x_61);
x_65 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1561_(x_1);
x_66 = 32;
x_67 = lean_uint64_shift_right(x_65, x_66);
x_68 = lean_uint64_xor(x_65, x_67);
x_69 = 16;
x_70 = lean_uint64_shift_right(x_68, x_69);
x_71 = lean_uint64_xor(x_68, x_70);
x_72 = lean_uint64_to_usize(x_71);
x_73 = lean_usize_of_nat(x_64);
lean_dec(x_64);
x_74 = 1;
x_75 = lean_usize_sub(x_73, x_74);
x_76 = lean_usize_land(x_72, x_75);
x_77 = lean_array_uget(x_61, x_76);
x_78 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__0___redArg(x_1, x_77);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; 
x_79 = lean_unsigned_to_nat(1u);
x_80 = lean_nat_add(x_60, x_79);
lean_dec(x_60);
x_81 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_81, 0, x_1);
lean_ctor_set(x_81, 1, x_63);
lean_ctor_set(x_81, 2, x_77);
x_82 = lean_array_uset(x_61, x_76, x_81);
x_83 = lean_unsigned_to_nat(4u);
x_84 = lean_nat_mul(x_80, x_83);
x_85 = lean_unsigned_to_nat(3u);
x_86 = lean_nat_div(x_84, x_85);
lean_dec(x_84);
x_87 = lean_array_get_size(x_82);
x_88 = lean_nat_dec_le(x_86, x_87);
lean_dec(x_87);
lean_dec(x_86);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; 
x_89 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__1___redArg(x_82);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_80);
lean_ctor_set(x_90, 1, x_89);
x_5 = x_24;
x_6 = x_62;
x_7 = x_23;
x_8 = x_90;
goto block_15;
}
else
{
lean_object* x_91; 
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_80);
lean_ctor_set(x_91, 1, x_82);
x_5 = x_24;
x_6 = x_62;
x_7 = x_23;
x_8 = x_91;
goto block_15;
}
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_92 = lean_box(0);
x_93 = lean_array_uset(x_61, x_76, x_92);
x_94 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_LCtx_addParam_spec__0___redArg(x_1, x_63, x_77);
x_95 = lean_array_uset(x_93, x_76, x_94);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_60);
lean_ctor_set(x_96, 1, x_95);
x_5 = x_24;
x_6 = x_62;
x_7 = x_23;
x_8 = x_96;
goto block_15;
}
}
}
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_240; lean_object* x_241; lean_object* x_242; uint64_t x_243; uint64_t x_244; uint64_t x_245; uint64_t x_246; uint64_t x_247; uint64_t x_248; uint64_t x_249; size_t x_250; size_t x_251; size_t x_252; size_t x_253; size_t x_254; lean_object* x_255; lean_object* x_256; 
x_194 = lean_ctor_get(x_16, 0);
x_195 = lean_ctor_get(x_16, 1);
lean_inc(x_195);
lean_inc(x_194);
lean_dec(x_16);
x_240 = lean_ctor_get(x_194, 0);
lean_inc(x_240);
lean_dec(x_194);
x_241 = lean_ctor_get(x_240, 1);
lean_inc(x_241);
lean_dec(x_240);
x_242 = lean_array_get_size(x_241);
x_243 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1561_(x_1);
x_244 = 32;
x_245 = lean_uint64_shift_right(x_243, x_244);
x_246 = lean_uint64_xor(x_243, x_245);
x_247 = 16;
x_248 = lean_uint64_shift_right(x_246, x_247);
x_249 = lean_uint64_xor(x_246, x_248);
x_250 = lean_uint64_to_usize(x_249);
x_251 = lean_usize_of_nat(x_242);
lean_dec(x_242);
x_252 = 1;
x_253 = lean_usize_sub(x_251, x_252);
x_254 = lean_usize_land(x_250, x_253);
x_255 = lean_array_uget(x_241, x_254);
lean_dec(x_241);
x_256 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Compiler_LCNF_getType_spec__0___redArg(x_1, x_255);
lean_dec(x_255);
if (lean_obj_tag(x_256) == 0)
{
lean_object* x_257; lean_object* x_258; 
lean_dec(x_2);
lean_dec(x_1);
x_257 = lean_box(0);
x_258 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_258, 0, x_257);
lean_ctor_set(x_258, 1, x_195);
return x_258;
}
else
{
lean_object* x_259; lean_object* x_260; uint8_t x_261; 
x_259 = lean_ctor_get(x_256, 0);
lean_inc(x_259);
lean_dec(x_256);
x_260 = lean_box(3);
x_261 = l_Lean_Compiler_LCNF_FloatLetIn_beqDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_73_(x_259, x_260);
if (x_261 == 0)
{
uint8_t x_262; 
x_262 = l_Lean_Compiler_LCNF_FloatLetIn_beqDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_73_(x_259, x_2);
lean_dec(x_2);
lean_dec(x_259);
if (x_262 == 0)
{
goto block_239;
}
else
{
if (x_261 == 0)
{
lean_object* x_263; lean_object* x_264; 
lean_dec(x_1);
x_263 = lean_box(0);
x_264 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_264, 0, x_263);
lean_ctor_set(x_264, 1, x_195);
return x_264;
}
else
{
goto block_239;
}
}
}
else
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_282; size_t x_283; size_t x_284; size_t x_285; lean_object* x_286; uint8_t x_287; 
lean_dec(x_259);
x_265 = lean_st_ref_take(x_3, x_195);
x_266 = lean_ctor_get(x_265, 0);
lean_inc(x_266);
x_267 = lean_ctor_get(x_266, 0);
lean_inc(x_267);
x_268 = lean_ctor_get(x_265, 1);
lean_inc(x_268);
lean_dec(x_265);
x_269 = lean_ctor_get(x_266, 1);
lean_inc(x_269);
if (lean_is_exclusive(x_266)) {
 lean_ctor_release(x_266, 0);
 lean_ctor_release(x_266, 1);
 x_270 = x_266;
} else {
 lean_dec_ref(x_266);
 x_270 = lean_box(0);
}
x_271 = lean_ctor_get(x_267, 0);
lean_inc(x_271);
x_272 = lean_ctor_get(x_267, 1);
lean_inc(x_272);
if (lean_is_exclusive(x_267)) {
 lean_ctor_release(x_267, 0);
 lean_ctor_release(x_267, 1);
 x_273 = x_267;
} else {
 lean_dec_ref(x_267);
 x_273 = lean_box(0);
}
x_274 = lean_box(0);
x_282 = lean_array_get_size(x_272);
x_283 = lean_usize_of_nat(x_282);
lean_dec(x_282);
x_284 = lean_usize_sub(x_283, x_252);
x_285 = lean_usize_land(x_250, x_284);
x_286 = lean_array_uget(x_272, x_285);
x_287 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__0___redArg(x_1, x_286);
if (x_287 == 0)
{
lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; uint8_t x_297; 
x_288 = lean_unsigned_to_nat(1u);
x_289 = lean_nat_add(x_271, x_288);
lean_dec(x_271);
x_290 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_290, 0, x_1);
lean_ctor_set(x_290, 1, x_2);
lean_ctor_set(x_290, 2, x_286);
x_291 = lean_array_uset(x_272, x_285, x_290);
x_292 = lean_unsigned_to_nat(4u);
x_293 = lean_nat_mul(x_289, x_292);
x_294 = lean_unsigned_to_nat(3u);
x_295 = lean_nat_div(x_293, x_294);
lean_dec(x_293);
x_296 = lean_array_get_size(x_291);
x_297 = lean_nat_dec_le(x_295, x_296);
lean_dec(x_296);
lean_dec(x_295);
if (x_297 == 0)
{
lean_object* x_298; lean_object* x_299; 
x_298 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__1___redArg(x_291);
if (lean_is_scalar(x_273)) {
 x_299 = lean_alloc_ctor(0, 2, 0);
} else {
 x_299 = x_273;
}
lean_ctor_set(x_299, 0, x_289);
lean_ctor_set(x_299, 1, x_298);
x_275 = x_299;
goto block_281;
}
else
{
lean_object* x_300; 
if (lean_is_scalar(x_273)) {
 x_300 = lean_alloc_ctor(0, 2, 0);
} else {
 x_300 = x_273;
}
lean_ctor_set(x_300, 0, x_289);
lean_ctor_set(x_300, 1, x_291);
x_275 = x_300;
goto block_281;
}
}
else
{
lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; 
x_301 = lean_box(0);
x_302 = lean_array_uset(x_272, x_285, x_301);
x_303 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_LCtx_addParam_spec__0___redArg(x_1, x_2, x_286);
x_304 = lean_array_uset(x_302, x_285, x_303);
if (lean_is_scalar(x_273)) {
 x_305 = lean_alloc_ctor(0, 2, 0);
} else {
 x_305 = x_273;
}
lean_ctor_set(x_305, 0, x_271);
lean_ctor_set(x_305, 1, x_304);
x_275 = x_305;
goto block_281;
}
block_281:
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; 
if (lean_is_scalar(x_270)) {
 x_276 = lean_alloc_ctor(0, 2, 0);
} else {
 x_276 = x_270;
}
lean_ctor_set(x_276, 0, x_275);
lean_ctor_set(x_276, 1, x_269);
x_277 = lean_st_ref_set(x_3, x_276, x_268);
x_278 = lean_ctor_get(x_277, 1);
lean_inc(x_278);
if (lean_is_exclusive(x_277)) {
 lean_ctor_release(x_277, 0);
 lean_ctor_release(x_277, 1);
 x_279 = x_277;
} else {
 lean_dec_ref(x_277);
 x_279 = lean_box(0);
}
if (lean_is_scalar(x_279)) {
 x_280 = lean_alloc_ctor(0, 2, 0);
} else {
 x_280 = x_279;
}
lean_ctor_set(x_280, 0, x_274);
lean_ctor_set(x_280, 1, x_278);
return x_280;
}
}
}
block_239:
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; uint64_t x_207; uint64_t x_208; uint64_t x_209; uint64_t x_210; uint64_t x_211; uint64_t x_212; uint64_t x_213; size_t x_214; size_t x_215; size_t x_216; size_t x_217; size_t x_218; lean_object* x_219; uint8_t x_220; 
x_196 = lean_st_ref_take(x_3, x_195);
x_197 = lean_ctor_get(x_196, 0);
lean_inc(x_197);
x_198 = lean_ctor_get(x_197, 0);
lean_inc(x_198);
x_199 = lean_ctor_get(x_196, 1);
lean_inc(x_199);
lean_dec(x_196);
x_200 = lean_ctor_get(x_197, 1);
lean_inc(x_200);
lean_dec(x_197);
x_201 = lean_ctor_get(x_198, 0);
lean_inc(x_201);
x_202 = lean_ctor_get(x_198, 1);
lean_inc(x_202);
if (lean_is_exclusive(x_198)) {
 lean_ctor_release(x_198, 0);
 lean_ctor_release(x_198, 1);
 x_203 = x_198;
} else {
 lean_dec_ref(x_198);
 x_203 = lean_box(0);
}
x_204 = lean_box(0);
x_205 = lean_box(2);
x_206 = lean_array_get_size(x_202);
x_207 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1561_(x_1);
x_208 = 32;
x_209 = lean_uint64_shift_right(x_207, x_208);
x_210 = lean_uint64_xor(x_207, x_209);
x_211 = 16;
x_212 = lean_uint64_shift_right(x_210, x_211);
x_213 = lean_uint64_xor(x_210, x_212);
x_214 = lean_uint64_to_usize(x_213);
x_215 = lean_usize_of_nat(x_206);
lean_dec(x_206);
x_216 = 1;
x_217 = lean_usize_sub(x_215, x_216);
x_218 = lean_usize_land(x_214, x_217);
x_219 = lean_array_uget(x_202, x_218);
x_220 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__0___redArg(x_1, x_219);
if (x_220 == 0)
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; uint8_t x_230; 
x_221 = lean_unsigned_to_nat(1u);
x_222 = lean_nat_add(x_201, x_221);
lean_dec(x_201);
x_223 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_223, 0, x_1);
lean_ctor_set(x_223, 1, x_205);
lean_ctor_set(x_223, 2, x_219);
x_224 = lean_array_uset(x_202, x_218, x_223);
x_225 = lean_unsigned_to_nat(4u);
x_226 = lean_nat_mul(x_222, x_225);
x_227 = lean_unsigned_to_nat(3u);
x_228 = lean_nat_div(x_226, x_227);
lean_dec(x_226);
x_229 = lean_array_get_size(x_224);
x_230 = lean_nat_dec_le(x_228, x_229);
lean_dec(x_229);
lean_dec(x_228);
if (x_230 == 0)
{
lean_object* x_231; lean_object* x_232; 
x_231 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__1___redArg(x_224);
if (lean_is_scalar(x_203)) {
 x_232 = lean_alloc_ctor(0, 2, 0);
} else {
 x_232 = x_203;
}
lean_ctor_set(x_232, 0, x_222);
lean_ctor_set(x_232, 1, x_231);
x_5 = x_200;
x_6 = x_204;
x_7 = x_199;
x_8 = x_232;
goto block_15;
}
else
{
lean_object* x_233; 
if (lean_is_scalar(x_203)) {
 x_233 = lean_alloc_ctor(0, 2, 0);
} else {
 x_233 = x_203;
}
lean_ctor_set(x_233, 0, x_222);
lean_ctor_set(x_233, 1, x_224);
x_5 = x_200;
x_6 = x_204;
x_7 = x_199;
x_8 = x_233;
goto block_15;
}
}
else
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; 
x_234 = lean_box(0);
x_235 = lean_array_uset(x_202, x_218, x_234);
x_236 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_LCtx_addParam_spec__0___redArg(x_1, x_205, x_219);
x_237 = lean_array_uset(x_235, x_218, x_236);
if (lean_is_scalar(x_203)) {
 x_238 = lean_alloc_ctor(0, 2, 0);
} else {
 x_238 = x_203;
}
lean_ctor_set(x_238, 0, x_201);
lean_ctor_set(x_238, 1, x_237);
x_5 = x_200;
x_6 = x_204;
x_7 = x_199;
x_8 = x_238;
goto block_15;
}
}
}
block_15:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_5);
x_10 = lean_st_ref_set(x_3, x_9, x_7);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_10, 0);
lean_dec(x_12);
lean_ctor_set(x_10, 0, x_6);
return x_10;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_6);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_float_goFVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_FloatLetIn_float_goFVar___redArg(x_1, x_2, x_3, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_float_goFVar___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Compiler_LCNF_FloatLetIn_float_goFVar___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_float_goFVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_FloatLetIn_float_goFVar(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_Compiler_LCNF_FloatLetIn_float_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0___redArg___closed__3;
x_5 = lean_panic_fn(x_1, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_3, 1);
x_8 = lean_ctor_get(x_3, 2);
x_9 = lean_name_eq(x_6, x_2);
if (x_9 == 0)
{
x_3 = x_8;
goto _start;
}
else
{
lean_dec(x_1);
lean_inc(x_7);
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_Compiler_LCNF_FloatLetIn_float_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_Compiler_LCNF_FloatLetIn_float_spec__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_float___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_FloatLetIn_float_goFVar___redArg(x_2, x_1, x_3, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_float(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint64_t x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; uint64_t x_33; uint64_t x_34; uint64_t x_35; size_t x_36; size_t x_37; size_t x_38; size_t x_39; size_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_156; 
x_20 = lean_st_ref_get(x_2, x_8);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Lean_Compiler_LCNF_FloatLetIn_instInhabitedDecision;
x_26 = lean_box(0);
x_27 = l_Lean_Compiler_LCNF_CodeDecl_fvarId(x_1);
x_28 = lean_array_get_size(x_24);
x_29 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1561_(x_27);
x_30 = 32;
x_31 = lean_uint64_shift_right(x_29, x_30);
x_32 = lean_uint64_xor(x_29, x_31);
x_33 = 16;
x_34 = lean_uint64_shift_right(x_32, x_33);
x_35 = lean_uint64_xor(x_32, x_34);
x_36 = lean_uint64_to_usize(x_35);
x_37 = lean_usize_of_nat(x_28);
lean_dec(x_28);
x_38 = 1;
x_39 = lean_usize_sub(x_37, x_38);
x_40 = lean_usize_land(x_36, x_39);
x_41 = lean_array_uget(x_24, x_40);
lean_dec(x_24);
x_42 = l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_Compiler_LCNF_FloatLetIn_float_spec__0___redArg(x_25, x_27, x_41);
lean_dec(x_41);
lean_dec(x_27);
lean_inc(x_42);
x_156 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_FloatLetIn_float___lam__0___boxed), 9, 1);
lean_closure_set(x_156, 0, x_42);
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_157; lean_object* x_158; 
x_157 = lean_ctor_get(x_1, 0);
lean_inc(x_157);
lean_inc(x_2);
x_158 = l_Lean_Compiler_LCNF_LetDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1(x_156, x_157, x_2, x_3, x_4, x_5, x_6, x_7, x_23);
x_43 = x_158;
goto block_155;
}
else
{
lean_object* x_159; lean_object* x_160; 
x_159 = lean_ctor_get(x_1, 0);
lean_inc(x_159);
lean_inc(x_2);
x_160 = l_Lean_Compiler_LCNF_FunDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__7(x_156, x_159, x_2, x_3, x_4, x_5, x_6, x_7, x_23);
x_43 = x_160;
goto block_155;
}
block_19:
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_st_ref_set(x_2, x_13, x_11);
lean_dec(x_2);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_14, 0);
lean_dec(x_16);
lean_ctor_set(x_14, 0, x_10);
return x_14;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_10);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
block_155:
{
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
lean_dec(x_43);
x_45 = lean_st_ref_take(x_2, x_44);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
x_48 = lean_ctor_get(x_45, 1);
lean_inc(x_48);
lean_dec(x_45);
x_49 = !lean_is_exclusive(x_46);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_50 = lean_ctor_get(x_46, 0);
x_51 = lean_ctor_get(x_46, 1);
lean_dec(x_51);
x_52 = !lean_is_exclusive(x_47);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint64_t x_57; uint64_t x_58; uint64_t x_59; uint64_t x_60; uint64_t x_61; size_t x_62; size_t x_63; size_t x_64; size_t x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_53 = lean_ctor_get(x_47, 0);
x_54 = lean_ctor_get(x_47, 1);
x_55 = lean_box(0);
x_56 = lean_array_get_size(x_54);
x_57 = l_Lean_Compiler_LCNF_FloatLetIn_hashDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_26_(x_42);
x_58 = lean_uint64_shift_right(x_57, x_30);
x_59 = lean_uint64_xor(x_57, x_58);
x_60 = lean_uint64_shift_right(x_59, x_33);
x_61 = lean_uint64_xor(x_59, x_60);
x_62 = lean_uint64_to_usize(x_61);
x_63 = lean_usize_of_nat(x_56);
lean_dec(x_56);
x_64 = lean_usize_sub(x_63, x_38);
x_65 = lean_usize_land(x_62, x_64);
x_66 = lean_array_uget(x_54, x_65);
x_67 = l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0___redArg(x_26, x_42, x_66);
lean_ctor_set_tag(x_46, 1);
lean_ctor_set(x_46, 1, x_67);
lean_ctor_set(x_46, 0, x_1);
x_68 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0___redArg(x_42, x_66);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; 
x_69 = lean_unsigned_to_nat(1u);
x_70 = lean_nat_add(x_53, x_69);
lean_dec(x_53);
x_71 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_71, 0, x_42);
lean_ctor_set(x_71, 1, x_46);
lean_ctor_set(x_71, 2, x_66);
x_72 = lean_array_uset(x_54, x_65, x_71);
x_73 = lean_unsigned_to_nat(4u);
x_74 = lean_nat_mul(x_70, x_73);
x_75 = lean_unsigned_to_nat(3u);
x_76 = lean_nat_div(x_74, x_75);
lean_dec(x_74);
x_77 = lean_array_get_size(x_72);
x_78 = lean_nat_dec_le(x_76, x_77);
lean_dec(x_77);
lean_dec(x_76);
if (x_78 == 0)
{
lean_object* x_79; 
x_79 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__1___redArg(x_72);
lean_ctor_set(x_47, 1, x_79);
lean_ctor_set(x_47, 0, x_70);
x_9 = x_50;
x_10 = x_55;
x_11 = x_48;
x_12 = x_47;
goto block_19;
}
else
{
lean_ctor_set(x_47, 1, x_72);
lean_ctor_set(x_47, 0, x_70);
x_9 = x_50;
x_10 = x_55;
x_11 = x_48;
x_12 = x_47;
goto block_19;
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_80 = lean_box(0);
x_81 = lean_array_uset(x_54, x_65, x_80);
x_82 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__4___redArg(x_42, x_46, x_66);
x_83 = lean_array_uset(x_81, x_65, x_82);
lean_ctor_set(x_47, 1, x_83);
x_9 = x_50;
x_10 = x_55;
x_11 = x_48;
x_12 = x_47;
goto block_19;
}
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; uint64_t x_88; uint64_t x_89; uint64_t x_90; uint64_t x_91; uint64_t x_92; size_t x_93; size_t x_94; size_t x_95; size_t x_96; lean_object* x_97; lean_object* x_98; uint8_t x_99; 
x_84 = lean_ctor_get(x_47, 0);
x_85 = lean_ctor_get(x_47, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_47);
x_86 = lean_box(0);
x_87 = lean_array_get_size(x_85);
x_88 = l_Lean_Compiler_LCNF_FloatLetIn_hashDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_26_(x_42);
x_89 = lean_uint64_shift_right(x_88, x_30);
x_90 = lean_uint64_xor(x_88, x_89);
x_91 = lean_uint64_shift_right(x_90, x_33);
x_92 = lean_uint64_xor(x_90, x_91);
x_93 = lean_uint64_to_usize(x_92);
x_94 = lean_usize_of_nat(x_87);
lean_dec(x_87);
x_95 = lean_usize_sub(x_94, x_38);
x_96 = lean_usize_land(x_93, x_95);
x_97 = lean_array_uget(x_85, x_96);
x_98 = l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0___redArg(x_26, x_42, x_97);
lean_ctor_set_tag(x_46, 1);
lean_ctor_set(x_46, 1, x_98);
lean_ctor_set(x_46, 0, x_1);
x_99 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0___redArg(x_42, x_97);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; uint8_t x_109; 
x_100 = lean_unsigned_to_nat(1u);
x_101 = lean_nat_add(x_84, x_100);
lean_dec(x_84);
x_102 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_102, 0, x_42);
lean_ctor_set(x_102, 1, x_46);
lean_ctor_set(x_102, 2, x_97);
x_103 = lean_array_uset(x_85, x_96, x_102);
x_104 = lean_unsigned_to_nat(4u);
x_105 = lean_nat_mul(x_101, x_104);
x_106 = lean_unsigned_to_nat(3u);
x_107 = lean_nat_div(x_105, x_106);
lean_dec(x_105);
x_108 = lean_array_get_size(x_103);
x_109 = lean_nat_dec_le(x_107, x_108);
lean_dec(x_108);
lean_dec(x_107);
if (x_109 == 0)
{
lean_object* x_110; lean_object* x_111; 
x_110 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__1___redArg(x_103);
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_101);
lean_ctor_set(x_111, 1, x_110);
x_9 = x_50;
x_10 = x_86;
x_11 = x_48;
x_12 = x_111;
goto block_19;
}
else
{
lean_object* x_112; 
x_112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_112, 0, x_101);
lean_ctor_set(x_112, 1, x_103);
x_9 = x_50;
x_10 = x_86;
x_11 = x_48;
x_12 = x_112;
goto block_19;
}
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_113 = lean_box(0);
x_114 = lean_array_uset(x_85, x_96, x_113);
x_115 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__4___redArg(x_42, x_46, x_97);
x_116 = lean_array_uset(x_114, x_96, x_115);
x_117 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_117, 0, x_84);
lean_ctor_set(x_117, 1, x_116);
x_9 = x_50;
x_10 = x_86;
x_11 = x_48;
x_12 = x_117;
goto block_19;
}
}
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; uint64_t x_124; uint64_t x_125; uint64_t x_126; uint64_t x_127; uint64_t x_128; size_t x_129; size_t x_130; size_t x_131; size_t x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; uint8_t x_136; 
x_118 = lean_ctor_get(x_46, 0);
lean_inc(x_118);
lean_dec(x_46);
x_119 = lean_ctor_get(x_47, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_47, 1);
lean_inc(x_120);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_121 = x_47;
} else {
 lean_dec_ref(x_47);
 x_121 = lean_box(0);
}
x_122 = lean_box(0);
x_123 = lean_array_get_size(x_120);
x_124 = l_Lean_Compiler_LCNF_FloatLetIn_hashDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_26_(x_42);
x_125 = lean_uint64_shift_right(x_124, x_30);
x_126 = lean_uint64_xor(x_124, x_125);
x_127 = lean_uint64_shift_right(x_126, x_33);
x_128 = lean_uint64_xor(x_126, x_127);
x_129 = lean_uint64_to_usize(x_128);
x_130 = lean_usize_of_nat(x_123);
lean_dec(x_123);
x_131 = lean_usize_sub(x_130, x_38);
x_132 = lean_usize_land(x_129, x_131);
x_133 = lean_array_uget(x_120, x_132);
x_134 = l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0___redArg(x_26, x_42, x_133);
x_135 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_135, 0, x_1);
lean_ctor_set(x_135, 1, x_134);
x_136 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0___redArg(x_42, x_133);
if (x_136 == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; uint8_t x_146; 
x_137 = lean_unsigned_to_nat(1u);
x_138 = lean_nat_add(x_119, x_137);
lean_dec(x_119);
x_139 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_139, 0, x_42);
lean_ctor_set(x_139, 1, x_135);
lean_ctor_set(x_139, 2, x_133);
x_140 = lean_array_uset(x_120, x_132, x_139);
x_141 = lean_unsigned_to_nat(4u);
x_142 = lean_nat_mul(x_138, x_141);
x_143 = lean_unsigned_to_nat(3u);
x_144 = lean_nat_div(x_142, x_143);
lean_dec(x_142);
x_145 = lean_array_get_size(x_140);
x_146 = lean_nat_dec_le(x_144, x_145);
lean_dec(x_145);
lean_dec(x_144);
if (x_146 == 0)
{
lean_object* x_147; lean_object* x_148; 
x_147 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__1___redArg(x_140);
if (lean_is_scalar(x_121)) {
 x_148 = lean_alloc_ctor(0, 2, 0);
} else {
 x_148 = x_121;
}
lean_ctor_set(x_148, 0, x_138);
lean_ctor_set(x_148, 1, x_147);
x_9 = x_118;
x_10 = x_122;
x_11 = x_48;
x_12 = x_148;
goto block_19;
}
else
{
lean_object* x_149; 
if (lean_is_scalar(x_121)) {
 x_149 = lean_alloc_ctor(0, 2, 0);
} else {
 x_149 = x_121;
}
lean_ctor_set(x_149, 0, x_138);
lean_ctor_set(x_149, 1, x_140);
x_9 = x_118;
x_10 = x_122;
x_11 = x_48;
x_12 = x_149;
goto block_19;
}
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_150 = lean_box(0);
x_151 = lean_array_uset(x_120, x_132, x_150);
x_152 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__4___redArg(x_42, x_135, x_133);
x_153 = lean_array_uset(x_151, x_132, x_152);
if (lean_is_scalar(x_121)) {
 x_154 = lean_alloc_ctor(0, 2, 0);
} else {
 x_154 = x_121;
}
lean_ctor_set(x_154, 0, x_119);
lean_ctor_set(x_154, 1, x_153);
x_9 = x_118;
x_10 = x_122;
x_11 = x_48;
x_12 = x_154;
goto block_19;
}
}
}
else
{
lean_dec(x_42);
lean_dec(x_2);
lean_dec(x_1);
return x_43;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_Compiler_LCNF_FloatLetIn_float_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_Compiler_LCNF_FloatLetIn_float_spec__0___redArg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_Compiler_LCNF_FloatLetIn_float_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_Compiler_LCNF_FloatLetIn_float_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_float___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_FloatLetIn_float___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_12; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_4);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint64_t x_22; uint64_t x_23; uint64_t x_24; uint64_t x_25; uint64_t x_26; uint64_t x_27; uint64_t x_28; size_t x_29; size_t x_30; size_t x_31; size_t x_32; size_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
lean_dec(x_4);
x_13 = lean_ctor_get(x_3, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_3, 1);
lean_inc(x_14);
lean_dec(x_3);
x_15 = lean_st_ref_get(x_5, x_11);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_Compiler_LCNF_CodeDecl_fvarId(x_13);
x_21 = lean_array_get_size(x_19);
x_22 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1561_(x_20);
x_23 = 32;
x_24 = lean_uint64_shift_right(x_22, x_23);
x_25 = lean_uint64_xor(x_22, x_24);
x_26 = 16;
x_27 = lean_uint64_shift_right(x_25, x_26);
x_28 = lean_uint64_xor(x_25, x_27);
x_29 = lean_uint64_to_usize(x_28);
x_30 = lean_usize_of_nat(x_21);
lean_dec(x_21);
x_31 = 1;
x_32 = lean_usize_sub(x_30, x_31);
x_33 = lean_usize_land(x_29, x_32);
x_34 = lean_array_uget(x_19, x_33);
lean_dec(x_19);
lean_inc(x_1);
x_35 = l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_Compiler_LCNF_FloatLetIn_float_spec__0___redArg(x_1, x_20, x_34);
lean_dec(x_34);
lean_dec(x_20);
x_36 = lean_box(3);
x_37 = l_Lean_Compiler_LCNF_FloatLetIn_beqDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_73_(x_35, x_36);
if (x_37 == 0)
{
lean_object* x_38; uint8_t x_39; 
x_38 = lean_box(2);
x_39 = l_Lean_Compiler_LCNF_FloatLetIn_beqDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_73_(x_35, x_38);
lean_dec(x_35);
if (x_39 == 0)
{
lean_object* x_40; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_40 = l_Lean_Compiler_LCNF_FloatLetIn_float(x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_18);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
lean_dec(x_40);
lean_inc(x_2);
{
lean_object* _tmp_2 = x_14;
lean_object* _tmp_3 = x_2;
lean_object* _tmp_10 = x_41;
x_3 = _tmp_2;
x_4 = _tmp_3;
x_11 = _tmp_10;
}
goto _start;
}
else
{
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_40;
}
}
else
{
lean_object* x_43; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_43 = l_Lean_Compiler_LCNF_FloatLetIn_dontFloat(x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_18);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; 
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
lean_dec(x_43);
lean_inc(x_2);
{
lean_object* _tmp_2 = x_14;
lean_object* _tmp_3 = x_2;
lean_object* _tmp_10 = x_44;
x_3 = _tmp_2;
x_4 = _tmp_3;
x_11 = _tmp_10;
}
goto _start;
}
else
{
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_43;
}
}
}
else
{
lean_object* x_46; lean_object* x_47; 
lean_dec(x_35);
x_46 = l_Lean_Compiler_LCNF_eraseCodeDecl___redArg(x_13, x_8, x_18);
lean_dec(x_13);
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
lean_dec(x_46);
lean_inc(x_2);
{
lean_object* _tmp_2 = x_14;
lean_object* _tmp_3 = x_2;
lean_object* _tmp_10 = x_47;
x_3 = _tmp_2;
x_4 = _tmp_3;
x_11 = _tmp_10;
}
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_List_forIn_x27_loop___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases_spec__0___redArg(x_1, x_2, x_4, x_5, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = l_Lean_Compiler_LCNF_FloatLetIn_instInhabitedDecision;
x_9 = lean_box(0);
lean_inc(x_2);
x_10 = l_List_forIn_x27_loop___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases_spec__0___redArg(x_8, x_9, x_2, x_9, x_1, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_10, 0);
lean_dec(x_12);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_9);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
else
{
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_List_forIn_x27_loop___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_2, 2);
x_5 = lean_ctor_get(x_2, 12);
x_6 = l_Lean_checkTraceOption(x_5, x_4, x_1);
x_7 = lean_box(x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_isTracingEnabledFor___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg(x_1, x_5, x_7);
return x_8;
}
}
static lean_object* _init_l_Lean_addTrace___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_addTrace___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_addTrace___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___redArg___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addTrace___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_addTrace___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___redArg___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addTrace___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_addTrace___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___redArg___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addTrace___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___redArg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_addTrace___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___redArg___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addTrace___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___redArg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_addTrace___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___redArg___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addTrace___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___redArg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_addTrace___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___redArg___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addTrace___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___redArg___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_1 = l_Lean_addTrace___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___redArg___closed__6;
x_2 = l_Lean_addTrace___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___redArg___closed__5;
x_3 = l_Lean_addTrace___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___redArg___closed__4;
x_4 = l_Lean_addTrace___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___redArg___closed__3;
x_5 = l_Lean_addTrace___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___redArg___closed__2;
x_6 = l_Lean_addTrace___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___redArg___closed__1;
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_7);
lean_ctor_set(x_8, 2, x_7);
lean_ctor_set(x_8, 3, x_6);
lean_ctor_set(x_8, 4, x_5);
lean_ctor_set(x_8, 5, x_4);
lean_ctor_set(x_8, 6, x_3);
lean_ctor_set(x_8, 7, x_2);
lean_ctor_set(x_8, 8, x_1);
return x_8;
}
}
static double _init_l_Lean_addTrace___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___redArg___closed__8() {
_start:
{
lean_object* x_1; double x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_float_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addTrace___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___redArg___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_addTrace___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___redArg___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_7 = lean_ctor_get(x_4, 2);
x_8 = lean_ctor_get(x_4, 5);
x_9 = lean_st_ref_get(x_5, x_6);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_st_ref_get(x_3, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_10, 0);
lean_inc(x_15);
lean_dec(x_10);
x_16 = !lean_is_exclusive(x_13);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_17 = lean_ctor_get(x_13, 0);
x_18 = lean_ctor_get(x_13, 1);
lean_dec(x_18);
x_19 = lean_st_ref_take(x_5, x_14);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_20, 4);
lean_inc(x_21);
x_22 = !lean_is_exclusive(x_19);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_ctor_get(x_19, 1);
x_24 = lean_ctor_get(x_19, 0);
lean_dec(x_24);
x_25 = !lean_is_exclusive(x_20);
if (x_25 == 0)
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_ctor_get(x_20, 4);
lean_dec(x_26);
x_27 = !lean_is_exclusive(x_21);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; double x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_28 = lean_ctor_get(x_21, 0);
x_29 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_17);
lean_dec(x_17);
x_30 = l_Lean_addTrace___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___redArg___closed__7;
lean_inc(x_7);
x_31 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_31, 0, x_15);
lean_ctor_set(x_31, 1, x_30);
lean_ctor_set(x_31, 2, x_29);
lean_ctor_set(x_31, 3, x_7);
lean_ctor_set_tag(x_19, 3);
lean_ctor_set(x_19, 1, x_2);
lean_ctor_set(x_19, 0, x_31);
x_32 = l_Lean_addTrace___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___redArg___closed__8;
x_33 = lean_box(0);
x_34 = l_Lean_addTrace___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___redArg___closed__9;
x_35 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_35, 0, x_1);
lean_ctor_set(x_35, 1, x_34);
lean_ctor_set_float(x_35, sizeof(void*)*2, x_32);
lean_ctor_set_float(x_35, sizeof(void*)*2 + 8, x_32);
x_36 = lean_unbox(x_33);
lean_ctor_set_uint8(x_35, sizeof(void*)*2 + 16, x_36);
x_37 = l_Lean_addTrace___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___redArg___closed__10;
x_38 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_38, 0, x_35);
lean_ctor_set(x_38, 1, x_19);
lean_ctor_set(x_38, 2, x_37);
lean_inc(x_8);
lean_ctor_set(x_13, 1, x_38);
lean_ctor_set(x_13, 0, x_8);
x_39 = l_Lean_PersistentArray_push___redArg(x_28, x_13);
lean_ctor_set(x_21, 0, x_39);
x_40 = lean_st_ref_set(x_5, x_20, x_23);
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_40, 0);
lean_dec(x_42);
x_43 = lean_box(0);
lean_ctor_set(x_40, 0, x_43);
return x_40;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_40, 1);
lean_inc(x_44);
lean_dec(x_40);
x_45 = lean_box(0);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_44);
return x_46;
}
}
else
{
uint64_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; double x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_47 = lean_ctor_get_uint64(x_21, sizeof(void*)*1);
x_48 = lean_ctor_get(x_21, 0);
lean_inc(x_48);
lean_dec(x_21);
x_49 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_17);
lean_dec(x_17);
x_50 = l_Lean_addTrace___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___redArg___closed__7;
lean_inc(x_7);
x_51 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_51, 0, x_15);
lean_ctor_set(x_51, 1, x_50);
lean_ctor_set(x_51, 2, x_49);
lean_ctor_set(x_51, 3, x_7);
lean_ctor_set_tag(x_19, 3);
lean_ctor_set(x_19, 1, x_2);
lean_ctor_set(x_19, 0, x_51);
x_52 = l_Lean_addTrace___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___redArg___closed__8;
x_53 = lean_box(0);
x_54 = l_Lean_addTrace___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___redArg___closed__9;
x_55 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_55, 0, x_1);
lean_ctor_set(x_55, 1, x_54);
lean_ctor_set_float(x_55, sizeof(void*)*2, x_52);
lean_ctor_set_float(x_55, sizeof(void*)*2 + 8, x_52);
x_56 = lean_unbox(x_53);
lean_ctor_set_uint8(x_55, sizeof(void*)*2 + 16, x_56);
x_57 = l_Lean_addTrace___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___redArg___closed__10;
x_58 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_58, 0, x_55);
lean_ctor_set(x_58, 1, x_19);
lean_ctor_set(x_58, 2, x_57);
lean_inc(x_8);
lean_ctor_set(x_13, 1, x_58);
lean_ctor_set(x_13, 0, x_8);
x_59 = l_Lean_PersistentArray_push___redArg(x_48, x_13);
x_60 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set_uint64(x_60, sizeof(void*)*1, x_47);
lean_ctor_set(x_20, 4, x_60);
x_61 = lean_st_ref_set(x_5, x_20, x_23);
x_62 = lean_ctor_get(x_61, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_63 = x_61;
} else {
 lean_dec_ref(x_61);
 x_63 = lean_box(0);
}
x_64 = lean_box(0);
if (lean_is_scalar(x_63)) {
 x_65 = lean_alloc_ctor(0, 2, 0);
} else {
 x_65 = x_63;
}
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_62);
return x_65;
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint64_t x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; double x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_66 = lean_ctor_get(x_20, 0);
x_67 = lean_ctor_get(x_20, 1);
x_68 = lean_ctor_get(x_20, 2);
x_69 = lean_ctor_get(x_20, 3);
x_70 = lean_ctor_get(x_20, 5);
x_71 = lean_ctor_get(x_20, 6);
x_72 = lean_ctor_get(x_20, 7);
x_73 = lean_ctor_get(x_20, 8);
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_71);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_20);
x_74 = lean_ctor_get_uint64(x_21, sizeof(void*)*1);
x_75 = lean_ctor_get(x_21, 0);
lean_inc(x_75);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 x_76 = x_21;
} else {
 lean_dec_ref(x_21);
 x_76 = lean_box(0);
}
x_77 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_17);
lean_dec(x_17);
x_78 = l_Lean_addTrace___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___redArg___closed__7;
lean_inc(x_7);
x_79 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_79, 0, x_15);
lean_ctor_set(x_79, 1, x_78);
lean_ctor_set(x_79, 2, x_77);
lean_ctor_set(x_79, 3, x_7);
lean_ctor_set_tag(x_19, 3);
lean_ctor_set(x_19, 1, x_2);
lean_ctor_set(x_19, 0, x_79);
x_80 = l_Lean_addTrace___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___redArg___closed__8;
x_81 = lean_box(0);
x_82 = l_Lean_addTrace___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___redArg___closed__9;
x_83 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_83, 0, x_1);
lean_ctor_set(x_83, 1, x_82);
lean_ctor_set_float(x_83, sizeof(void*)*2, x_80);
lean_ctor_set_float(x_83, sizeof(void*)*2 + 8, x_80);
x_84 = lean_unbox(x_81);
lean_ctor_set_uint8(x_83, sizeof(void*)*2 + 16, x_84);
x_85 = l_Lean_addTrace___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___redArg___closed__10;
x_86 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_86, 0, x_83);
lean_ctor_set(x_86, 1, x_19);
lean_ctor_set(x_86, 2, x_85);
lean_inc(x_8);
lean_ctor_set(x_13, 1, x_86);
lean_ctor_set(x_13, 0, x_8);
x_87 = l_Lean_PersistentArray_push___redArg(x_75, x_13);
if (lean_is_scalar(x_76)) {
 x_88 = lean_alloc_ctor(0, 1, 8);
} else {
 x_88 = x_76;
}
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set_uint64(x_88, sizeof(void*)*1, x_74);
x_89 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_89, 0, x_66);
lean_ctor_set(x_89, 1, x_67);
lean_ctor_set(x_89, 2, x_68);
lean_ctor_set(x_89, 3, x_69);
lean_ctor_set(x_89, 4, x_88);
lean_ctor_set(x_89, 5, x_70);
lean_ctor_set(x_89, 6, x_71);
lean_ctor_set(x_89, 7, x_72);
lean_ctor_set(x_89, 8, x_73);
x_90 = lean_st_ref_set(x_5, x_89, x_23);
x_91 = lean_ctor_get(x_90, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_92 = x_90;
} else {
 lean_dec_ref(x_90);
 x_92 = lean_box(0);
}
x_93 = lean_box(0);
if (lean_is_scalar(x_92)) {
 x_94 = lean_alloc_ctor(0, 2, 0);
} else {
 x_94 = x_92;
}
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_91);
return x_94;
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; uint64_t x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; double x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_95 = lean_ctor_get(x_19, 1);
lean_inc(x_95);
lean_dec(x_19);
x_96 = lean_ctor_get(x_20, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_20, 1);
lean_inc(x_97);
x_98 = lean_ctor_get(x_20, 2);
lean_inc(x_98);
x_99 = lean_ctor_get(x_20, 3);
lean_inc(x_99);
x_100 = lean_ctor_get(x_20, 5);
lean_inc(x_100);
x_101 = lean_ctor_get(x_20, 6);
lean_inc(x_101);
x_102 = lean_ctor_get(x_20, 7);
lean_inc(x_102);
x_103 = lean_ctor_get(x_20, 8);
lean_inc(x_103);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 lean_ctor_release(x_20, 2);
 lean_ctor_release(x_20, 3);
 lean_ctor_release(x_20, 4);
 lean_ctor_release(x_20, 5);
 lean_ctor_release(x_20, 6);
 lean_ctor_release(x_20, 7);
 lean_ctor_release(x_20, 8);
 x_104 = x_20;
} else {
 lean_dec_ref(x_20);
 x_104 = lean_box(0);
}
x_105 = lean_ctor_get_uint64(x_21, sizeof(void*)*1);
x_106 = lean_ctor_get(x_21, 0);
lean_inc(x_106);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 x_107 = x_21;
} else {
 lean_dec_ref(x_21);
 x_107 = lean_box(0);
}
x_108 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_17);
lean_dec(x_17);
x_109 = l_Lean_addTrace___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___redArg___closed__7;
lean_inc(x_7);
x_110 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_110, 0, x_15);
lean_ctor_set(x_110, 1, x_109);
lean_ctor_set(x_110, 2, x_108);
lean_ctor_set(x_110, 3, x_7);
x_111 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_2);
x_112 = l_Lean_addTrace___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___redArg___closed__8;
x_113 = lean_box(0);
x_114 = l_Lean_addTrace___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___redArg___closed__9;
x_115 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_115, 0, x_1);
lean_ctor_set(x_115, 1, x_114);
lean_ctor_set_float(x_115, sizeof(void*)*2, x_112);
lean_ctor_set_float(x_115, sizeof(void*)*2 + 8, x_112);
x_116 = lean_unbox(x_113);
lean_ctor_set_uint8(x_115, sizeof(void*)*2 + 16, x_116);
x_117 = l_Lean_addTrace___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___redArg___closed__10;
x_118 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_118, 0, x_115);
lean_ctor_set(x_118, 1, x_111);
lean_ctor_set(x_118, 2, x_117);
lean_inc(x_8);
lean_ctor_set(x_13, 1, x_118);
lean_ctor_set(x_13, 0, x_8);
x_119 = l_Lean_PersistentArray_push___redArg(x_106, x_13);
if (lean_is_scalar(x_107)) {
 x_120 = lean_alloc_ctor(0, 1, 8);
} else {
 x_120 = x_107;
}
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set_uint64(x_120, sizeof(void*)*1, x_105);
if (lean_is_scalar(x_104)) {
 x_121 = lean_alloc_ctor(0, 9, 0);
} else {
 x_121 = x_104;
}
lean_ctor_set(x_121, 0, x_96);
lean_ctor_set(x_121, 1, x_97);
lean_ctor_set(x_121, 2, x_98);
lean_ctor_set(x_121, 3, x_99);
lean_ctor_set(x_121, 4, x_120);
lean_ctor_set(x_121, 5, x_100);
lean_ctor_set(x_121, 6, x_101);
lean_ctor_set(x_121, 7, x_102);
lean_ctor_set(x_121, 8, x_103);
x_122 = lean_st_ref_set(x_5, x_121, x_95);
x_123 = lean_ctor_get(x_122, 1);
lean_inc(x_123);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 lean_ctor_release(x_122, 1);
 x_124 = x_122;
} else {
 lean_dec_ref(x_122);
 x_124 = lean_box(0);
}
x_125 = lean_box(0);
if (lean_is_scalar(x_124)) {
 x_126 = lean_alloc_ctor(0, 2, 0);
} else {
 x_126 = x_124;
}
lean_ctor_set(x_126, 0, x_125);
lean_ctor_set(x_126, 1, x_123);
return x_126;
}
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; uint64_t x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; double x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; uint8_t x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_127 = lean_ctor_get(x_13, 0);
lean_inc(x_127);
lean_dec(x_13);
x_128 = lean_st_ref_take(x_5, x_14);
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_129, 4);
lean_inc(x_130);
x_131 = lean_ctor_get(x_128, 1);
lean_inc(x_131);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 lean_ctor_release(x_128, 1);
 x_132 = x_128;
} else {
 lean_dec_ref(x_128);
 x_132 = lean_box(0);
}
x_133 = lean_ctor_get(x_129, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_129, 1);
lean_inc(x_134);
x_135 = lean_ctor_get(x_129, 2);
lean_inc(x_135);
x_136 = lean_ctor_get(x_129, 3);
lean_inc(x_136);
x_137 = lean_ctor_get(x_129, 5);
lean_inc(x_137);
x_138 = lean_ctor_get(x_129, 6);
lean_inc(x_138);
x_139 = lean_ctor_get(x_129, 7);
lean_inc(x_139);
x_140 = lean_ctor_get(x_129, 8);
lean_inc(x_140);
if (lean_is_exclusive(x_129)) {
 lean_ctor_release(x_129, 0);
 lean_ctor_release(x_129, 1);
 lean_ctor_release(x_129, 2);
 lean_ctor_release(x_129, 3);
 lean_ctor_release(x_129, 4);
 lean_ctor_release(x_129, 5);
 lean_ctor_release(x_129, 6);
 lean_ctor_release(x_129, 7);
 lean_ctor_release(x_129, 8);
 x_141 = x_129;
} else {
 lean_dec_ref(x_129);
 x_141 = lean_box(0);
}
x_142 = lean_ctor_get_uint64(x_130, sizeof(void*)*1);
x_143 = lean_ctor_get(x_130, 0);
lean_inc(x_143);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 x_144 = x_130;
} else {
 lean_dec_ref(x_130);
 x_144 = lean_box(0);
}
x_145 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_127);
lean_dec(x_127);
x_146 = l_Lean_addTrace___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___redArg___closed__7;
lean_inc(x_7);
x_147 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_147, 0, x_15);
lean_ctor_set(x_147, 1, x_146);
lean_ctor_set(x_147, 2, x_145);
lean_ctor_set(x_147, 3, x_7);
if (lean_is_scalar(x_132)) {
 x_148 = lean_alloc_ctor(3, 2, 0);
} else {
 x_148 = x_132;
 lean_ctor_set_tag(x_148, 3);
}
lean_ctor_set(x_148, 0, x_147);
lean_ctor_set(x_148, 1, x_2);
x_149 = l_Lean_addTrace___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___redArg___closed__8;
x_150 = lean_box(0);
x_151 = l_Lean_addTrace___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___redArg___closed__9;
x_152 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_152, 0, x_1);
lean_ctor_set(x_152, 1, x_151);
lean_ctor_set_float(x_152, sizeof(void*)*2, x_149);
lean_ctor_set_float(x_152, sizeof(void*)*2 + 8, x_149);
x_153 = lean_unbox(x_150);
lean_ctor_set_uint8(x_152, sizeof(void*)*2 + 16, x_153);
x_154 = l_Lean_addTrace___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___redArg___closed__10;
x_155 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_155, 0, x_152);
lean_ctor_set(x_155, 1, x_148);
lean_ctor_set(x_155, 2, x_154);
lean_inc(x_8);
x_156 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_156, 0, x_8);
lean_ctor_set(x_156, 1, x_155);
x_157 = l_Lean_PersistentArray_push___redArg(x_143, x_156);
if (lean_is_scalar(x_144)) {
 x_158 = lean_alloc_ctor(0, 1, 8);
} else {
 x_158 = x_144;
}
lean_ctor_set(x_158, 0, x_157);
lean_ctor_set_uint64(x_158, sizeof(void*)*1, x_142);
if (lean_is_scalar(x_141)) {
 x_159 = lean_alloc_ctor(0, 9, 0);
} else {
 x_159 = x_141;
}
lean_ctor_set(x_159, 0, x_133);
lean_ctor_set(x_159, 1, x_134);
lean_ctor_set(x_159, 2, x_135);
lean_ctor_set(x_159, 3, x_136);
lean_ctor_set(x_159, 4, x_158);
lean_ctor_set(x_159, 5, x_137);
lean_ctor_set(x_159, 6, x_138);
lean_ctor_set(x_159, 7, x_139);
lean_ctor_set(x_159, 8, x_140);
x_160 = lean_st_ref_set(x_5, x_159, x_131);
x_161 = lean_ctor_get(x_160, 1);
lean_inc(x_161);
if (lean_is_exclusive(x_160)) {
 lean_ctor_release(x_160, 0);
 lean_ctor_release(x_160, 1);
 x_162 = x_160;
} else {
 lean_dec_ref(x_160);
 x_162 = lean_box(0);
}
x_163 = lean_box(0);
if (lean_is_scalar(x_162)) {
 x_164 = lean_alloc_ctor(0, 2, 0);
} else {
 x_164 = x_162;
}
lean_ctor_set(x_164, 0, x_163);
lean_ctor_set(x_164, 1, x_161);
return x_164;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_addTrace___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___redArg(x_1, x_2, x_5, x_6, x_7, x_8);
return x_9;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__2_spec__2___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Compiler", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__2_spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("floatLetIn", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__2_spec__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__2_spec__2___closed__1;
x_2 = l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__2_spec__2___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__2_spec__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Size of code that was pushed into arm: ", 39, 39);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__2_spec__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__2_spec__2___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__2_spec__2___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" ", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__2_spec__2___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__2_spec__2___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__2_spec__2___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_addTrace___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___redArg___closed__9;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__2_spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_4, x_3);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_5);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_1, 1);
x_15 = l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__2_spec__2___closed__2;
x_16 = l_Lean_isTracingEnabledFor___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg(x_15, x_9, x_11);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint64_t x_25; uint64_t x_26; uint64_t x_27; uint64_t x_28; uint64_t x_29; uint64_t x_30; uint64_t x_31; size_t x_32; size_t x_33; size_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; size_t x_56; size_t x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_69; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_16, 1);
x_20 = lean_array_uget(x_5, x_4);
x_21 = lean_box(0);
x_22 = lean_array_uset(x_5, x_4, x_21);
x_23 = l_Lean_Compiler_LCNF_FloatLetIn_Decision_ofAlt(x_20);
x_24 = lean_array_get_size(x_14);
x_25 = l_Lean_Compiler_LCNF_FloatLetIn_hashDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_26_(x_23);
x_26 = 32;
x_27 = lean_uint64_shift_right(x_25, x_26);
x_28 = lean_uint64_xor(x_25, x_27);
x_29 = 16;
x_30 = lean_uint64_shift_right(x_28, x_29);
x_31 = lean_uint64_xor(x_28, x_30);
x_32 = lean_uint64_to_usize(x_31);
x_33 = lean_usize_of_nat(x_24);
lean_dec(x_24);
x_34 = 1;
x_56 = lean_usize_sub(x_33, x_34);
x_57 = lean_usize_land(x_32, x_56);
x_58 = lean_array_uget(x_14, x_57);
lean_inc(x_2);
x_59 = l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0___redArg(x_2, x_23, x_58);
lean_dec(x_58);
x_69 = lean_unbox(x_18);
lean_dec(x_18);
if (x_69 == 0)
{
lean_dec(x_23);
lean_free_object(x_16);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_60 = x_7;
x_61 = x_8;
x_62 = x_9;
x_63 = x_10;
x_64 = x_19;
goto block_68;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_70 = l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__2_spec__2___closed__4;
x_71 = lean_unsigned_to_nat(0u);
x_72 = l_Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_171_(x_23, x_71);
x_73 = l_Lean_MessageData_ofFormat(x_72);
lean_ctor_set_tag(x_16, 7);
lean_ctor_set(x_16, 1, x_73);
lean_ctor_set(x_16, 0, x_70);
x_74 = l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__2_spec__2___closed__6;
x_75 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_75, 0, x_16);
lean_ctor_set(x_75, 1, x_74);
x_76 = l_List_lengthTR___redArg(x_59);
x_77 = l_Nat_reprFast(x_76);
x_78 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_78, 0, x_77);
x_79 = l_Lean_MessageData_ofFormat(x_78);
x_80 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_80, 0, x_75);
lean_ctor_set(x_80, 1, x_79);
x_81 = l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__2_spec__2___closed__7;
x_82 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
x_83 = l_Lean_addTrace___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___redArg(x_15, x_82, x_8, x_9, x_10, x_19);
x_84 = lean_ctor_get(x_83, 1);
lean_inc(x_84);
lean_dec(x_83);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_60 = x_7;
x_61 = x_8;
x_62 = x_9;
x_63 = x_10;
x_64 = x_84;
goto block_68;
}
block_55:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = l_Lean_Compiler_LCNF_attachCodeDecls(x_36, x_41);
lean_dec(x_36);
x_43 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go), 7, 1);
lean_closure_set(x_43, 0, x_42);
x_44 = l_Lean_Compiler_LCNF_FloatLetIn_withNewScope___redArg(x_43, x_39, x_35, x_37, x_38, x_40);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; size_t x_48; lean_object* x_49; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(x_20, x_45);
x_48 = lean_usize_add(x_4, x_34);
x_49 = lean_array_uset(x_22, x_4, x_47);
x_4 = x_48;
x_5 = x_49;
x_11 = x_46;
goto _start;
}
else
{
uint8_t x_51; 
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_51 = !lean_is_exclusive(x_44);
if (x_51 == 0)
{
return x_44;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_44, 0);
x_53 = lean_ctor_get(x_44, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_44);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
block_68:
{
lean_object* x_65; 
x_65 = lean_array_mk(x_59);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_66; 
x_66 = lean_ctor_get(x_20, 2);
lean_inc(x_66);
x_35 = x_61;
x_36 = x_65;
x_37 = x_62;
x_38 = x_63;
x_39 = x_60;
x_40 = x_64;
x_41 = x_66;
goto block_55;
}
else
{
lean_object* x_67; 
x_67 = lean_ctor_get(x_20, 0);
lean_inc(x_67);
x_35 = x_61;
x_36 = x_65;
x_37 = x_62;
x_38 = x_63;
x_39 = x_60;
x_40 = x_64;
x_41 = x_67;
goto block_55;
}
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; uint64_t x_92; uint64_t x_93; uint64_t x_94; uint64_t x_95; uint64_t x_96; uint64_t x_97; uint64_t x_98; size_t x_99; size_t x_100; size_t x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; size_t x_123; size_t x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; uint8_t x_136; 
x_85 = lean_ctor_get(x_16, 0);
x_86 = lean_ctor_get(x_16, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_16);
x_87 = lean_array_uget(x_5, x_4);
x_88 = lean_box(0);
x_89 = lean_array_uset(x_5, x_4, x_88);
x_90 = l_Lean_Compiler_LCNF_FloatLetIn_Decision_ofAlt(x_87);
x_91 = lean_array_get_size(x_14);
x_92 = l_Lean_Compiler_LCNF_FloatLetIn_hashDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_26_(x_90);
x_93 = 32;
x_94 = lean_uint64_shift_right(x_92, x_93);
x_95 = lean_uint64_xor(x_92, x_94);
x_96 = 16;
x_97 = lean_uint64_shift_right(x_95, x_96);
x_98 = lean_uint64_xor(x_95, x_97);
x_99 = lean_uint64_to_usize(x_98);
x_100 = lean_usize_of_nat(x_91);
lean_dec(x_91);
x_101 = 1;
x_123 = lean_usize_sub(x_100, x_101);
x_124 = lean_usize_land(x_99, x_123);
x_125 = lean_array_uget(x_14, x_124);
lean_inc(x_2);
x_126 = l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0___redArg(x_2, x_90, x_125);
lean_dec(x_125);
x_136 = lean_unbox(x_85);
lean_dec(x_85);
if (x_136 == 0)
{
lean_dec(x_90);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_127 = x_7;
x_128 = x_8;
x_129 = x_9;
x_130 = x_10;
x_131 = x_86;
goto block_135;
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_137 = l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__2_spec__2___closed__4;
x_138 = lean_unsigned_to_nat(0u);
x_139 = l_Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_171_(x_90, x_138);
x_140 = l_Lean_MessageData_ofFormat(x_139);
x_141 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_141, 0, x_137);
lean_ctor_set(x_141, 1, x_140);
x_142 = l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__2_spec__2___closed__6;
x_143 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_143, 0, x_141);
lean_ctor_set(x_143, 1, x_142);
x_144 = l_List_lengthTR___redArg(x_126);
x_145 = l_Nat_reprFast(x_144);
x_146 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_146, 0, x_145);
x_147 = l_Lean_MessageData_ofFormat(x_146);
x_148 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_148, 0, x_143);
lean_ctor_set(x_148, 1, x_147);
x_149 = l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__2_spec__2___closed__7;
x_150 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_150, 0, x_148);
lean_ctor_set(x_150, 1, x_149);
x_151 = l_Lean_addTrace___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___redArg(x_15, x_150, x_8, x_9, x_10, x_86);
x_152 = lean_ctor_get(x_151, 1);
lean_inc(x_152);
lean_dec(x_151);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_127 = x_7;
x_128 = x_8;
x_129 = x_9;
x_130 = x_10;
x_131 = x_152;
goto block_135;
}
block_122:
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = l_Lean_Compiler_LCNF_attachCodeDecls(x_103, x_108);
lean_dec(x_103);
x_110 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go), 7, 1);
lean_closure_set(x_110, 0, x_109);
x_111 = l_Lean_Compiler_LCNF_FloatLetIn_withNewScope___redArg(x_110, x_106, x_102, x_104, x_105, x_107);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; size_t x_115; lean_object* x_116; 
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_111, 1);
lean_inc(x_113);
lean_dec(x_111);
x_114 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(x_87, x_112);
x_115 = lean_usize_add(x_4, x_101);
x_116 = lean_array_uset(x_89, x_4, x_114);
x_4 = x_115;
x_5 = x_116;
x_11 = x_113;
goto _start;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
lean_dec(x_89);
lean_dec(x_87);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_118 = lean_ctor_get(x_111, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_111, 1);
lean_inc(x_119);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 x_120 = x_111;
} else {
 lean_dec_ref(x_111);
 x_120 = lean_box(0);
}
if (lean_is_scalar(x_120)) {
 x_121 = lean_alloc_ctor(1, 2, 0);
} else {
 x_121 = x_120;
}
lean_ctor_set(x_121, 0, x_118);
lean_ctor_set(x_121, 1, x_119);
return x_121;
}
}
block_135:
{
lean_object* x_132; 
x_132 = lean_array_mk(x_126);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_133; 
x_133 = lean_ctor_get(x_87, 2);
lean_inc(x_133);
x_102 = x_128;
x_103 = x_132;
x_104 = x_129;
x_105 = x_130;
x_106 = x_127;
x_107 = x_131;
x_108 = x_133;
goto block_122;
}
else
{
lean_object* x_134; 
x_134 = lean_ctor_get(x_87, 0);
lean_inc(x_134);
x_102 = x_128;
x_103 = x_132;
x_104 = x_129;
x_105 = x_130;
x_106 = x_127;
x_107 = x_131;
x_108 = x_134;
goto block_122;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__2___redArg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_4, x_3);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_5);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_1, 1);
x_15 = l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__2_spec__2___closed__2;
x_16 = l_Lean_isTracingEnabledFor___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg(x_15, x_9, x_11);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint64_t x_25; uint64_t x_26; uint64_t x_27; uint64_t x_28; uint64_t x_29; uint64_t x_30; uint64_t x_31; size_t x_32; size_t x_33; size_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; size_t x_56; size_t x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_69; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_16, 1);
x_20 = lean_array_uget(x_5, x_4);
x_21 = lean_box(0);
x_22 = lean_array_uset(x_5, x_4, x_21);
x_23 = l_Lean_Compiler_LCNF_FloatLetIn_Decision_ofAlt(x_20);
x_24 = lean_array_get_size(x_14);
x_25 = l_Lean_Compiler_LCNF_FloatLetIn_hashDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_26_(x_23);
x_26 = 32;
x_27 = lean_uint64_shift_right(x_25, x_26);
x_28 = lean_uint64_xor(x_25, x_27);
x_29 = 16;
x_30 = lean_uint64_shift_right(x_28, x_29);
x_31 = lean_uint64_xor(x_28, x_30);
x_32 = lean_uint64_to_usize(x_31);
x_33 = lean_usize_of_nat(x_24);
lean_dec(x_24);
x_34 = 1;
x_56 = lean_usize_sub(x_33, x_34);
x_57 = lean_usize_land(x_32, x_56);
x_58 = lean_array_uget(x_14, x_57);
lean_inc(x_2);
x_59 = l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0___redArg(x_2, x_23, x_58);
lean_dec(x_58);
x_69 = lean_unbox(x_18);
lean_dec(x_18);
if (x_69 == 0)
{
lean_dec(x_23);
lean_free_object(x_16);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_60 = x_7;
x_61 = x_8;
x_62 = x_9;
x_63 = x_10;
x_64 = x_19;
goto block_68;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_70 = l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__2_spec__2___closed__4;
x_71 = lean_unsigned_to_nat(0u);
x_72 = l_Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_171_(x_23, x_71);
x_73 = l_Lean_MessageData_ofFormat(x_72);
lean_ctor_set_tag(x_16, 7);
lean_ctor_set(x_16, 1, x_73);
lean_ctor_set(x_16, 0, x_70);
x_74 = l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__2_spec__2___closed__6;
x_75 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_75, 0, x_16);
lean_ctor_set(x_75, 1, x_74);
x_76 = l_List_lengthTR___redArg(x_59);
x_77 = l_Nat_reprFast(x_76);
x_78 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_78, 0, x_77);
x_79 = l_Lean_MessageData_ofFormat(x_78);
x_80 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_80, 0, x_75);
lean_ctor_set(x_80, 1, x_79);
x_81 = l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__2_spec__2___closed__7;
x_82 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
x_83 = l_Lean_addTrace___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___redArg(x_15, x_82, x_8, x_9, x_10, x_19);
x_84 = lean_ctor_get(x_83, 1);
lean_inc(x_84);
lean_dec(x_83);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_60 = x_7;
x_61 = x_8;
x_62 = x_9;
x_63 = x_10;
x_64 = x_84;
goto block_68;
}
block_55:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = l_Lean_Compiler_LCNF_attachCodeDecls(x_37, x_41);
lean_dec(x_37);
x_43 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go), 7, 1);
lean_closure_set(x_43, 0, x_42);
x_44 = l_Lean_Compiler_LCNF_FloatLetIn_withNewScope___redArg(x_43, x_38, x_35, x_36, x_40, x_39);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; size_t x_48; lean_object* x_49; lean_object* x_50; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(x_20, x_45);
x_48 = lean_usize_add(x_4, x_34);
x_49 = lean_array_uset(x_22, x_4, x_47);
x_50 = l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__2_spec__2(x_1, x_2, x_3, x_48, x_49, x_6, x_7, x_8, x_9, x_10, x_46);
return x_50;
}
else
{
uint8_t x_51; 
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_51 = !lean_is_exclusive(x_44);
if (x_51 == 0)
{
return x_44;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_44, 0);
x_53 = lean_ctor_get(x_44, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_44);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
block_68:
{
lean_object* x_65; 
x_65 = lean_array_mk(x_59);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_66; 
x_66 = lean_ctor_get(x_20, 2);
lean_inc(x_66);
x_35 = x_61;
x_36 = x_62;
x_37 = x_65;
x_38 = x_60;
x_39 = x_64;
x_40 = x_63;
x_41 = x_66;
goto block_55;
}
else
{
lean_object* x_67; 
x_67 = lean_ctor_get(x_20, 0);
lean_inc(x_67);
x_35 = x_61;
x_36 = x_62;
x_37 = x_65;
x_38 = x_60;
x_39 = x_64;
x_40 = x_63;
x_41 = x_67;
goto block_55;
}
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; uint64_t x_92; uint64_t x_93; uint64_t x_94; uint64_t x_95; uint64_t x_96; uint64_t x_97; uint64_t x_98; size_t x_99; size_t x_100; size_t x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; size_t x_123; size_t x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; uint8_t x_136; 
x_85 = lean_ctor_get(x_16, 0);
x_86 = lean_ctor_get(x_16, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_16);
x_87 = lean_array_uget(x_5, x_4);
x_88 = lean_box(0);
x_89 = lean_array_uset(x_5, x_4, x_88);
x_90 = l_Lean_Compiler_LCNF_FloatLetIn_Decision_ofAlt(x_87);
x_91 = lean_array_get_size(x_14);
x_92 = l_Lean_Compiler_LCNF_FloatLetIn_hashDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_26_(x_90);
x_93 = 32;
x_94 = lean_uint64_shift_right(x_92, x_93);
x_95 = lean_uint64_xor(x_92, x_94);
x_96 = 16;
x_97 = lean_uint64_shift_right(x_95, x_96);
x_98 = lean_uint64_xor(x_95, x_97);
x_99 = lean_uint64_to_usize(x_98);
x_100 = lean_usize_of_nat(x_91);
lean_dec(x_91);
x_101 = 1;
x_123 = lean_usize_sub(x_100, x_101);
x_124 = lean_usize_land(x_99, x_123);
x_125 = lean_array_uget(x_14, x_124);
lean_inc(x_2);
x_126 = l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0___redArg(x_2, x_90, x_125);
lean_dec(x_125);
x_136 = lean_unbox(x_85);
lean_dec(x_85);
if (x_136 == 0)
{
lean_dec(x_90);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_127 = x_7;
x_128 = x_8;
x_129 = x_9;
x_130 = x_10;
x_131 = x_86;
goto block_135;
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_137 = l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__2_spec__2___closed__4;
x_138 = lean_unsigned_to_nat(0u);
x_139 = l_Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_171_(x_90, x_138);
x_140 = l_Lean_MessageData_ofFormat(x_139);
x_141 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_141, 0, x_137);
lean_ctor_set(x_141, 1, x_140);
x_142 = l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__2_spec__2___closed__6;
x_143 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_143, 0, x_141);
lean_ctor_set(x_143, 1, x_142);
x_144 = l_List_lengthTR___redArg(x_126);
x_145 = l_Nat_reprFast(x_144);
x_146 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_146, 0, x_145);
x_147 = l_Lean_MessageData_ofFormat(x_146);
x_148 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_148, 0, x_143);
lean_ctor_set(x_148, 1, x_147);
x_149 = l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__2_spec__2___closed__7;
x_150 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_150, 0, x_148);
lean_ctor_set(x_150, 1, x_149);
x_151 = l_Lean_addTrace___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___redArg(x_15, x_150, x_8, x_9, x_10, x_86);
x_152 = lean_ctor_get(x_151, 1);
lean_inc(x_152);
lean_dec(x_151);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_127 = x_7;
x_128 = x_8;
x_129 = x_9;
x_130 = x_10;
x_131 = x_152;
goto block_135;
}
block_122:
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = l_Lean_Compiler_LCNF_attachCodeDecls(x_104, x_108);
lean_dec(x_104);
x_110 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go), 7, 1);
lean_closure_set(x_110, 0, x_109);
x_111 = l_Lean_Compiler_LCNF_FloatLetIn_withNewScope___redArg(x_110, x_105, x_102, x_103, x_107, x_106);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; size_t x_115; lean_object* x_116; lean_object* x_117; 
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_111, 1);
lean_inc(x_113);
lean_dec(x_111);
x_114 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(x_87, x_112);
x_115 = lean_usize_add(x_4, x_101);
x_116 = lean_array_uset(x_89, x_4, x_114);
x_117 = l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__2_spec__2(x_1, x_2, x_3, x_115, x_116, x_6, x_7, x_8, x_9, x_10, x_113);
return x_117;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
lean_dec(x_89);
lean_dec(x_87);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_118 = lean_ctor_get(x_111, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_111, 1);
lean_inc(x_119);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 x_120 = x_111;
} else {
 lean_dec_ref(x_111);
 x_120 = lean_box(0);
}
if (lean_is_scalar(x_120)) {
 x_121 = lean_alloc_ctor(1, 2, 0);
} else {
 x_121 = x_120;
}
lean_ctor_set(x_121, 0, x_118);
lean_ctor_set(x_121, 1, x_119);
return x_121;
}
}
block_135:
{
lean_object* x_132; 
x_132 = lean_array_mk(x_126);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_133; 
x_133 = lean_ctor_get(x_87, 2);
lean_inc(x_133);
x_102 = x_128;
x_103 = x_129;
x_104 = x_132;
x_105 = x_127;
x_106 = x_131;
x_107 = x_130;
x_108 = x_133;
goto block_122;
}
else
{
lean_object* x_134; 
x_134 = lean_ctor_get(x_87, 0);
lean_inc(x_134);
x_102 = x_128;
x_103 = x_129;
x_104 = x_132;
x_105 = x_127;
x_106 = x_131;
x_107 = x_130;
x_108 = x_134;
goto block_122;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__2___redArg(x_1, x_2, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_8);
x_11 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go), 7, 1);
lean_closure_set(x_11, 0, x_9);
x_12 = l_Lean_Compiler_LCNF_FloatLetIn_withNewCandidate___redArg(x_10, x_11, x_2, x_3, x_4, x_5, x_6, x_7);
return x_12;
}
case 1:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
lean_dec(x_1);
x_15 = lean_ctor_get(x_13, 2);
lean_inc(x_15);
x_16 = lean_ctor_get(x_13, 3);
lean_inc(x_16);
x_17 = lean_ctor_get(x_13, 4);
lean_inc(x_17);
x_18 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go), 7, 1);
lean_closure_set(x_18, 0, x_17);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_19 = l_Lean_Compiler_LCNF_FloatLetIn_withNewScope___redArg(x_18, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(x_13, x_16, x_15, x_20, x_4, x_21);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_23);
x_26 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go), 7, 1);
lean_closure_set(x_26, 0, x_14);
x_27 = l_Lean_Compiler_LCNF_FloatLetIn_withNewCandidate___redArg(x_25, x_26, x_2, x_3, x_4, x_5, x_6, x_24);
return x_27;
}
else
{
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_19;
}
}
case 2:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_28 = lean_ctor_get(x_1, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_1, 1);
lean_inc(x_29);
lean_dec(x_1);
x_30 = lean_ctor_get(x_28, 2);
lean_inc(x_30);
x_31 = lean_ctor_get(x_28, 3);
lean_inc(x_31);
x_32 = lean_ctor_get(x_28, 4);
lean_inc(x_32);
x_33 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go), 7, 1);
lean_closure_set(x_33, 0, x_32);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_34 = l_Lean_Compiler_LCNF_FloatLetIn_withNewScope___redArg(x_33, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(x_28, x_31, x_30, x_35, x_4, x_36);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_40, 0, x_38);
x_41 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go), 7, 1);
lean_closure_set(x_41, 0, x_29);
x_42 = l_Lean_Compiler_LCNF_FloatLetIn_withNewCandidate___redArg(x_40, x_41, x_2, x_3, x_4, x_5, x_6, x_39);
return x_42;
}
else
{
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_34;
}
}
case 4:
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_1, 0);
lean_inc(x_43);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_43);
x_44 = l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions(x_43, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = l_Lean_Compiler_LCNF_FloatLetIn_initialNewArms(x_43);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_45);
lean_ctor_set(x_48, 1, x_47);
x_49 = lean_st_mk_ref(x_48, x_46);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_50);
x_52 = l_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases(x_50, x_2, x_3, x_4, x_5, x_6, x_51);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; size_t x_65; size_t x_66; lean_object* x_67; 
x_53 = lean_ctor_get(x_52, 1);
lean_inc(x_53);
lean_dec(x_52);
x_54 = lean_st_ref_get(x_50, x_53);
lean_dec(x_50);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
lean_dec(x_55);
x_57 = lean_ctor_get(x_54, 1);
lean_inc(x_57);
lean_dec(x_54);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
x_59 = lean_ctor_get(x_43, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_43, 1);
lean_inc(x_60);
x_61 = lean_ctor_get(x_43, 2);
lean_inc(x_61);
x_62 = lean_ctor_get(x_43, 3);
lean_inc(x_62);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 lean_ctor_release(x_43, 2);
 lean_ctor_release(x_43, 3);
 x_63 = x_43;
} else {
 lean_dec_ref(x_43);
 x_63 = lean_box(0);
}
x_64 = lean_box(0);
x_65 = lean_array_size(x_62);
x_66 = 0;
lean_inc(x_62);
x_67 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__2___redArg(x_56, x_64, x_65, x_66, x_62, x_2, x_3, x_4, x_5, x_6, x_57);
lean_dec(x_2);
lean_dec(x_56);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; size_t x_73; size_t x_74; size_t x_75; size_t x_76; size_t x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_88; size_t x_91; size_t x_92; uint8_t x_93; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_70 = x_67;
} else {
 lean_dec_ref(x_67);
 x_70 = lean_box(0);
}
x_71 = lean_box(2);
x_72 = lean_array_get_size(x_58);
x_73 = l_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___closed__5;
x_74 = lean_usize_of_nat(x_72);
lean_dec(x_72);
x_75 = 1;
x_76 = lean_usize_sub(x_74, x_75);
x_77 = lean_usize_land(x_73, x_76);
x_78 = lean_array_uget(x_58, x_77);
lean_dec(x_58);
x_79 = l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0___redArg(x_64, x_71, x_78);
lean_dec(x_78);
x_91 = lean_ptr_addr(x_62);
lean_dec(x_62);
x_92 = lean_ptr_addr(x_68);
x_93 = lean_usize_dec_eq(x_91, x_92);
if (x_93 == 0)
{
x_88 = x_93;
goto block_90;
}
else
{
size_t x_94; uint8_t x_95; 
x_94 = lean_ptr_addr(x_60);
x_95 = lean_usize_dec_eq(x_94, x_94);
x_88 = x_95;
goto block_90;
}
block_84:
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_array_mk(x_79);
x_82 = l_Lean_Compiler_LCNF_attachCodeDecls(x_81, x_80);
lean_dec(x_81);
if (lean_is_scalar(x_70)) {
 x_83 = lean_alloc_ctor(0, 2, 0);
} else {
 x_83 = x_70;
}
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_69);
return x_83;
}
block_87:
{
lean_object* x_85; lean_object* x_86; 
if (lean_is_scalar(x_63)) {
 x_85 = lean_alloc_ctor(0, 4, 0);
} else {
 x_85 = x_63;
}
lean_ctor_set(x_85, 0, x_59);
lean_ctor_set(x_85, 1, x_60);
lean_ctor_set(x_85, 2, x_61);
lean_ctor_set(x_85, 3, x_68);
x_86 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_86, 0, x_85);
x_80 = x_86;
goto block_84;
}
block_90:
{
if (x_88 == 0)
{
lean_dec(x_1);
goto block_87;
}
else
{
uint8_t x_89; 
x_89 = lean_name_eq(x_61, x_61);
if (x_89 == 0)
{
lean_dec(x_1);
goto block_87;
}
else
{
lean_dec(x_68);
lean_dec(x_63);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
x_80 = x_1;
goto block_84;
}
}
}
}
else
{
uint8_t x_96; 
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_1);
x_96 = !lean_is_exclusive(x_67);
if (x_96 == 0)
{
return x_67;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_67, 0);
x_98 = lean_ctor_get(x_67, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_67);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
return x_99;
}
}
}
else
{
uint8_t x_100; 
lean_dec(x_50);
lean_dec(x_43);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_100 = !lean_is_exclusive(x_52);
if (x_100 == 0)
{
return x_52;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_52, 0);
x_102 = lean_ctor_get(x_52, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_52);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
}
}
else
{
uint8_t x_104; 
lean_dec(x_43);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_104 = !lean_is_exclusive(x_44);
if (x_104 == 0)
{
return x_44;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_44, 0);
x_106 = lean_ctor_get(x_44, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_44);
x_107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
return x_107;
}
}
}
default: 
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_108 = lean_array_mk(x_2);
x_109 = l_Array_reverse___redArg(x_108);
x_110 = l_Lean_Compiler_LCNF_attachCodeDecls(x_109, x_1);
lean_dec(x_109);
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_7);
return x_111;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_isTracingEnabledFor___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_isTracingEnabledFor___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_addTrace___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_addTrace___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__2_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_14 = l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__2_spec__2(x_1, x_2, x_12, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_14 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__2___redArg(x_1, x_2, x_12, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
size_t x_15; size_t x_16; lean_object* x_17; 
x_15 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_16 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_17 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__2(x_1, x_2, x_3, x_4, x_5, x_15, x_16, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_2);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_apply_7(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_11, 0);
lean_ctor_set(x_2, 0, x_13);
lean_ctor_set(x_11, 0, x_2);
return x_11;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_11, 0);
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_11);
lean_ctor_set(x_2, 0, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_2);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
uint8_t x_17; 
lean_free_object(x_2);
x_17 = !lean_is_exclusive(x_11);
if (x_17 == 0)
{
return x_11;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_11, 0);
x_19 = lean_ctor_get(x_11, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_11);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_2, 0);
lean_inc(x_21);
lean_dec(x_2);
x_22 = lean_apply_7(x_1, x_21, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 x_25 = x_22;
} else {
 lean_dec_ref(x_22);
 x_25 = lean_box(0);
}
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_23);
if (lean_is_scalar(x_25)) {
 x_27 = lean_alloc_ctor(0, 2, 0);
} else {
 x_27 = x_25;
}
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_24);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_22, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_22, 1);
lean_inc(x_29);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 x_30 = x_22;
} else {
 lean_dec_ref(x_22);
 x_30 = lean_box(0);
}
if (lean_is_scalar(x_30)) {
 x_31 = lean_alloc_ctor(1, 2, 0);
} else {
 x_31 = x_30;
}
lean_ctor_set(x_31, 0, x_28);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
}
else
{
lean_object* x_32; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_2);
lean_ctor_set(x_32, 1, x_8);
return x_32;
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_FloatLetIn_floatLetIn___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go), 7, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_floatLetIn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_1);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
x_10 = lean_ctor_get(x_1, 2);
x_11 = lean_ctor_get(x_1, 3);
x_12 = lean_ctor_get(x_1, 4);
x_13 = lean_ctor_get(x_1, 5);
x_14 = l_Lean_Compiler_LCNF_FloatLetIn_floatLetIn___closed__0;
x_15 = lean_box(0);
x_16 = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_spec__0(x_14, x_12, x_15, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_16, 0);
lean_ctor_set(x_1, 4, x_18);
lean_ctor_set(x_16, 0, x_1);
return x_16;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_16, 0);
x_20 = lean_ctor_get(x_16, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_16);
lean_ctor_set(x_1, 4, x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_1);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
else
{
uint8_t x_22; 
lean_free_object(x_1);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_22 = !lean_is_exclusive(x_16);
if (x_22 == 0)
{
return x_16;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_16, 0);
x_24 = lean_ctor_get(x_16, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_16);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_26 = lean_ctor_get(x_1, 0);
x_27 = lean_ctor_get(x_1, 1);
x_28 = lean_ctor_get(x_1, 2);
x_29 = lean_ctor_get(x_1, 3);
x_30 = lean_ctor_get(x_1, 4);
x_31 = lean_ctor_get_uint8(x_1, sizeof(void*)*6);
x_32 = lean_ctor_get_uint8(x_1, sizeof(void*)*6 + 1);
x_33 = lean_ctor_get(x_1, 5);
lean_inc(x_33);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_1);
x_34 = l_Lean_Compiler_LCNF_FloatLetIn_floatLetIn___closed__0;
x_35 = lean_box(0);
x_36 = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_spec__0(x_34, x_30, x_35, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_39 = x_36;
} else {
 lean_dec_ref(x_36);
 x_39 = lean_box(0);
}
x_40 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_40, 0, x_26);
lean_ctor_set(x_40, 1, x_27);
lean_ctor_set(x_40, 2, x_28);
lean_ctor_set(x_40, 3, x_29);
lean_ctor_set(x_40, 4, x_37);
lean_ctor_set(x_40, 5, x_33);
lean_ctor_set_uint8(x_40, sizeof(void*)*6, x_31);
lean_ctor_set_uint8(x_40, sizeof(void*)*6 + 1, x_32);
if (lean_is_scalar(x_39)) {
 x_41 = lean_alloc_ctor(0, 2, 0);
} else {
 x_41 = x_39;
}
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_38);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_33);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
x_42 = lean_ctor_get(x_36, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_36, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_44 = x_36;
} else {
 lean_dec_ref(x_36);
 x_44 = lean_box(0);
}
if (lean_is_scalar(x_44)) {
 x_45 = lean_alloc_ctor(1, 2, 0);
} else {
 x_45 = x_44;
}
lean_ctor_set(x_45, 0, x_42);
lean_ctor_set(x_45, 1, x_43);
return x_45;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_floatLetIn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_FloatLetIn_floatLetIn(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_floatLetIn___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_FloatLetIn_floatLetIn(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_floatLetIn___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__2_spec__2___closed__1;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_floatLetIn(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_floatLetIn___lam__0), 6, 0);
x_4 = l_Lean_Compiler_LCNF_floatLetIn___closed__0;
x_5 = l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(x_4, x_3, x_1, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_floatLetIn___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lean_Compiler_LCNF_floatLetIn(x_3, x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__0____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2285_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__1____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2285_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn___closed__0____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2285_;
x_2 = lean_box(0);
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__2____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2285_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__2_spec__2___closed__0;
x_2 = l_Lean_Compiler_LCNF_initFn___closed__1____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2285_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__3____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2285_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("LCNF", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__4____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2285_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn___closed__3____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2285_;
x_2 = l_Lean_Compiler_LCNF_initFn___closed__2____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2285_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__5____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2285_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("initFn", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__6____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2285_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn___closed__5____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2285_;
x_2 = l_Lean_Compiler_LCNF_initFn___closed__4____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2285_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__7____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2285_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_@", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__8____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2285_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn___closed__7____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2285_;
x_2 = l_Lean_Compiler_LCNF_initFn___closed__6____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2285_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__9____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2285_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn___closed__0____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2285_;
x_2 = l_Lean_Compiler_LCNF_initFn___closed__8____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2285_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__10____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2285_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__2_spec__2___closed__0;
x_2 = l_Lean_Compiler_LCNF_initFn___closed__9____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2285_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__11____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2285_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn___closed__3____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2285_;
x_2 = l_Lean_Compiler_LCNF_initFn___closed__10____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2285_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__12____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2285_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("FloatLetIn", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__13____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2285_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn___closed__12____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2285_;
x_2 = l_Lean_Compiler_LCNF_initFn___closed__11____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2285_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__14____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2285_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_hyg", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__15____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2285_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn___closed__14____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2285_;
x_2 = l_Lean_Compiler_LCNF_initFn___closed__13____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2285_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__16____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2285_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(2285u);
x_2 = l_Lean_Compiler_LCNF_initFn___closed__15____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2285_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2285_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_2 = l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__2_spec__2___closed__2;
x_3 = lean_box(1);
x_4 = l_Lean_Compiler_LCNF_initFn___closed__16____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2285_;
x_5 = lean_unbox(x_3);
x_6 = l_Lean_registerTraceClass(x_2, x_5, x_4, x_1);
return x_6;
}
}
lean_object* initialize_Lean_Compiler_LCNF_CompilerM(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_FVarUtil(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_PassManager(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_Types(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_FloatLetIn(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_LCNF_CompilerM(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_FVarUtil(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_PassManager(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Types(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Compiler_LCNF_FloatLetIn_instHashableDecision___closed__0 = _init_l_Lean_Compiler_LCNF_FloatLetIn_instHashableDecision___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_FloatLetIn_instHashableDecision___closed__0);
l_Lean_Compiler_LCNF_FloatLetIn_instHashableDecision = _init_l_Lean_Compiler_LCNF_FloatLetIn_instHashableDecision();
lean_mark_persistent(l_Lean_Compiler_LCNF_FloatLetIn_instHashableDecision);
l_Lean_Compiler_LCNF_FloatLetIn_instBEqDecision___closed__0 = _init_l_Lean_Compiler_LCNF_FloatLetIn_instBEqDecision___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_FloatLetIn_instBEqDecision___closed__0);
l_Lean_Compiler_LCNF_FloatLetIn_instBEqDecision = _init_l_Lean_Compiler_LCNF_FloatLetIn_instBEqDecision();
lean_mark_persistent(l_Lean_Compiler_LCNF_FloatLetIn_instBEqDecision);
l_Lean_Compiler_LCNF_FloatLetIn_instInhabitedDecision___closed__0 = _init_l_Lean_Compiler_LCNF_FloatLetIn_instInhabitedDecision___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_FloatLetIn_instInhabitedDecision___closed__0);
l_Lean_Compiler_LCNF_FloatLetIn_instInhabitedDecision = _init_l_Lean_Compiler_LCNF_FloatLetIn_instInhabitedDecision();
lean_mark_persistent(l_Lean_Compiler_LCNF_FloatLetIn_instInhabitedDecision);
l_Lean_Compiler_LCNF_FloatLetIn_reprDecision___closed__0____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_171_ = _init_l_Lean_Compiler_LCNF_FloatLetIn_reprDecision___closed__0____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_171_();
lean_mark_persistent(l_Lean_Compiler_LCNF_FloatLetIn_reprDecision___closed__0____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_171_);
l_Lean_Compiler_LCNF_FloatLetIn_reprDecision___closed__1____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_171_ = _init_l_Lean_Compiler_LCNF_FloatLetIn_reprDecision___closed__1____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_171_();
lean_mark_persistent(l_Lean_Compiler_LCNF_FloatLetIn_reprDecision___closed__1____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_171_);
l_Lean_Compiler_LCNF_FloatLetIn_reprDecision___closed__2____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_171_ = _init_l_Lean_Compiler_LCNF_FloatLetIn_reprDecision___closed__2____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_171_();
lean_mark_persistent(l_Lean_Compiler_LCNF_FloatLetIn_reprDecision___closed__2____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_171_);
l_Lean_Compiler_LCNF_FloatLetIn_reprDecision___closed__3____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_171_ = _init_l_Lean_Compiler_LCNF_FloatLetIn_reprDecision___closed__3____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_171_();
lean_mark_persistent(l_Lean_Compiler_LCNF_FloatLetIn_reprDecision___closed__3____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_171_);
l_Lean_Compiler_LCNF_FloatLetIn_reprDecision___closed__4____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_171_ = _init_l_Lean_Compiler_LCNF_FloatLetIn_reprDecision___closed__4____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_171_();
lean_mark_persistent(l_Lean_Compiler_LCNF_FloatLetIn_reprDecision___closed__4____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_171_);
l_Lean_Compiler_LCNF_FloatLetIn_reprDecision___closed__5____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_171_ = _init_l_Lean_Compiler_LCNF_FloatLetIn_reprDecision___closed__5____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_171_();
lean_mark_persistent(l_Lean_Compiler_LCNF_FloatLetIn_reprDecision___closed__5____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_171_);
l_Lean_Compiler_LCNF_FloatLetIn_reprDecision___closed__6____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_171_ = _init_l_Lean_Compiler_LCNF_FloatLetIn_reprDecision___closed__6____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_171_();
lean_mark_persistent(l_Lean_Compiler_LCNF_FloatLetIn_reprDecision___closed__6____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_171_);
l_Lean_Compiler_LCNF_FloatLetIn_reprDecision___closed__7____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_171_ = _init_l_Lean_Compiler_LCNF_FloatLetIn_reprDecision___closed__7____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_171_();
lean_mark_persistent(l_Lean_Compiler_LCNF_FloatLetIn_reprDecision___closed__7____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_171_);
l_Lean_Compiler_LCNF_FloatLetIn_reprDecision___closed__8____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_171_ = _init_l_Lean_Compiler_LCNF_FloatLetIn_reprDecision___closed__8____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_171_();
lean_mark_persistent(l_Lean_Compiler_LCNF_FloatLetIn_reprDecision___closed__8____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_171_);
l_Lean_Compiler_LCNF_FloatLetIn_reprDecision___closed__9____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_171_ = _init_l_Lean_Compiler_LCNF_FloatLetIn_reprDecision___closed__9____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_171_();
lean_mark_persistent(l_Lean_Compiler_LCNF_FloatLetIn_reprDecision___closed__9____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_171_);
l_Lean_Compiler_LCNF_FloatLetIn_reprDecision___closed__10____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_171_ = _init_l_Lean_Compiler_LCNF_FloatLetIn_reprDecision___closed__10____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_171_();
lean_mark_persistent(l_Lean_Compiler_LCNF_FloatLetIn_reprDecision___closed__10____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_171_);
l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision___closed__0 = _init_l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision___closed__0);
l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision = _init_l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision();
lean_mark_persistent(l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision);
l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Param_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__0___closed__0 = _init_l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Param_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__0___closed__0();
lean_mark_persistent(l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Param_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__0___closed__0);
l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Param_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__0___closed__1 = _init_l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Param_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__0___closed__1();
lean_mark_persistent(l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Param_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__0___closed__1);
l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Param_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__0___closed__2 = _init_l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Param_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__0___closed__2();
lean_mark_persistent(l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Param_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__0___closed__2);
l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Param_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__0___closed__3 = _init_l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Param_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__0___closed__3();
lean_mark_persistent(l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Param_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__0___closed__3);
l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Param_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__0___closed__4 = _init_l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Param_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__0___closed__4();
lean_mark_persistent(l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Param_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__0___closed__4);
l_Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Param_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__0 = _init_l_Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Param_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Param_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__0);
l_Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Param_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__1 = _init_l_Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Param_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Param_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__1);
l_Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Param_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__2 = _init_l_Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Param_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Param_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__2);
l_Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Param_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3 = _init_l_Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Param_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Param_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3);
l_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___closed__0 = _init_l_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___closed__0();
l_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___closed__1 = _init_l_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___closed__1();
l_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___closed__2 = _init_l_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___closed__2();
l_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___closed__3 = _init_l_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___closed__3();
l_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___closed__4 = _init_l_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___closed__4();
l_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___closed__5 = _init_l_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___closed__5();
l_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___closed__6 = _init_l_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___closed__6();
lean_mark_persistent(l_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___closed__6);
l_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___closed__7 = _init_l_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___closed__7();
lean_mark_persistent(l_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___closed__7);
l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0___redArg___closed__0 = _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0___redArg___closed__0();
lean_mark_persistent(l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0___redArg___closed__0);
l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0___redArg___closed__1 = _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0___redArg___closed__1();
lean_mark_persistent(l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0___redArg___closed__1);
l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0___redArg___closed__2 = _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0___redArg___closed__2();
lean_mark_persistent(l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0___redArg___closed__2);
l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0___redArg___closed__3 = _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0___redArg___closed__3();
lean_mark_persistent(l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0___redArg___closed__3);
l_Lean_Compiler_LCNF_FloatLetIn_dontFloat___closed__0 = _init_l_Lean_Compiler_LCNF_FloatLetIn_dontFloat___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_FloatLetIn_dontFloat___closed__0);
l_Lean_addTrace___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___redArg___closed__0 = _init_l_Lean_addTrace___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___redArg___closed__0();
lean_mark_persistent(l_Lean_addTrace___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___redArg___closed__0);
l_Lean_addTrace___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___redArg___closed__1 = _init_l_Lean_addTrace___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___redArg___closed__1();
lean_mark_persistent(l_Lean_addTrace___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___redArg___closed__1);
l_Lean_addTrace___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___redArg___closed__2 = _init_l_Lean_addTrace___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___redArg___closed__2();
lean_mark_persistent(l_Lean_addTrace___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___redArg___closed__2);
l_Lean_addTrace___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___redArg___closed__3 = _init_l_Lean_addTrace___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___redArg___closed__3();
lean_mark_persistent(l_Lean_addTrace___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___redArg___closed__3);
l_Lean_addTrace___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___redArg___closed__4 = _init_l_Lean_addTrace___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___redArg___closed__4();
lean_mark_persistent(l_Lean_addTrace___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___redArg___closed__4);
l_Lean_addTrace___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___redArg___closed__5 = _init_l_Lean_addTrace___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___redArg___closed__5();
lean_mark_persistent(l_Lean_addTrace___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___redArg___closed__5);
l_Lean_addTrace___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___redArg___closed__6 = _init_l_Lean_addTrace___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___redArg___closed__6();
lean_mark_persistent(l_Lean_addTrace___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___redArg___closed__6);
l_Lean_addTrace___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___redArg___closed__7 = _init_l_Lean_addTrace___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___redArg___closed__7();
lean_mark_persistent(l_Lean_addTrace___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___redArg___closed__7);
l_Lean_addTrace___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___redArg___closed__8 = _init_l_Lean_addTrace___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___redArg___closed__8();
l_Lean_addTrace___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___redArg___closed__9 = _init_l_Lean_addTrace___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___redArg___closed__9();
lean_mark_persistent(l_Lean_addTrace___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___redArg___closed__9);
l_Lean_addTrace___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___redArg___closed__10 = _init_l_Lean_addTrace___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___redArg___closed__10();
lean_mark_persistent(l_Lean_addTrace___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___redArg___closed__10);
l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__2_spec__2___closed__0 = _init_l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__2_spec__2___closed__0();
lean_mark_persistent(l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__2_spec__2___closed__0);
l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__2_spec__2___closed__1 = _init_l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__2_spec__2___closed__1();
lean_mark_persistent(l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__2_spec__2___closed__1);
l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__2_spec__2___closed__2 = _init_l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__2_spec__2___closed__2();
lean_mark_persistent(l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__2_spec__2___closed__2);
l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__2_spec__2___closed__3 = _init_l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__2_spec__2___closed__3();
lean_mark_persistent(l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__2_spec__2___closed__3);
l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__2_spec__2___closed__4 = _init_l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__2_spec__2___closed__4();
lean_mark_persistent(l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__2_spec__2___closed__4);
l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__2_spec__2___closed__5 = _init_l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__2_spec__2___closed__5();
lean_mark_persistent(l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__2_spec__2___closed__5);
l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__2_spec__2___closed__6 = _init_l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__2_spec__2___closed__6();
lean_mark_persistent(l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__2_spec__2___closed__6);
l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__2_spec__2___closed__7 = _init_l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__2_spec__2___closed__7();
lean_mark_persistent(l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__2_spec__2___closed__7);
l_Lean_Compiler_LCNF_FloatLetIn_floatLetIn___closed__0 = _init_l_Lean_Compiler_LCNF_FloatLetIn_floatLetIn___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_FloatLetIn_floatLetIn___closed__0);
l_Lean_Compiler_LCNF_floatLetIn___closed__0 = _init_l_Lean_Compiler_LCNF_floatLetIn___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_floatLetIn___closed__0);
l_Lean_Compiler_LCNF_initFn___closed__0____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2285_ = _init_l_Lean_Compiler_LCNF_initFn___closed__0____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2285_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__0____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2285_);
l_Lean_Compiler_LCNF_initFn___closed__1____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2285_ = _init_l_Lean_Compiler_LCNF_initFn___closed__1____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2285_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__1____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2285_);
l_Lean_Compiler_LCNF_initFn___closed__2____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2285_ = _init_l_Lean_Compiler_LCNF_initFn___closed__2____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2285_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__2____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2285_);
l_Lean_Compiler_LCNF_initFn___closed__3____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2285_ = _init_l_Lean_Compiler_LCNF_initFn___closed__3____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2285_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__3____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2285_);
l_Lean_Compiler_LCNF_initFn___closed__4____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2285_ = _init_l_Lean_Compiler_LCNF_initFn___closed__4____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2285_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__4____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2285_);
l_Lean_Compiler_LCNF_initFn___closed__5____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2285_ = _init_l_Lean_Compiler_LCNF_initFn___closed__5____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2285_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__5____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2285_);
l_Lean_Compiler_LCNF_initFn___closed__6____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2285_ = _init_l_Lean_Compiler_LCNF_initFn___closed__6____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2285_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__6____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2285_);
l_Lean_Compiler_LCNF_initFn___closed__7____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2285_ = _init_l_Lean_Compiler_LCNF_initFn___closed__7____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2285_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__7____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2285_);
l_Lean_Compiler_LCNF_initFn___closed__8____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2285_ = _init_l_Lean_Compiler_LCNF_initFn___closed__8____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2285_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__8____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2285_);
l_Lean_Compiler_LCNF_initFn___closed__9____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2285_ = _init_l_Lean_Compiler_LCNF_initFn___closed__9____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2285_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__9____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2285_);
l_Lean_Compiler_LCNF_initFn___closed__10____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2285_ = _init_l_Lean_Compiler_LCNF_initFn___closed__10____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2285_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__10____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2285_);
l_Lean_Compiler_LCNF_initFn___closed__11____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2285_ = _init_l_Lean_Compiler_LCNF_initFn___closed__11____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2285_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__11____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2285_);
l_Lean_Compiler_LCNF_initFn___closed__12____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2285_ = _init_l_Lean_Compiler_LCNF_initFn___closed__12____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2285_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__12____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2285_);
l_Lean_Compiler_LCNF_initFn___closed__13____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2285_ = _init_l_Lean_Compiler_LCNF_initFn___closed__13____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2285_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__13____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2285_);
l_Lean_Compiler_LCNF_initFn___closed__14____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2285_ = _init_l_Lean_Compiler_LCNF_initFn___closed__14____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2285_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__14____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2285_);
l_Lean_Compiler_LCNF_initFn___closed__15____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2285_ = _init_l_Lean_Compiler_LCNF_initFn___closed__15____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2285_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__15____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2285_);
l_Lean_Compiler_LCNF_initFn___closed__16____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2285_ = _init_l_Lean_Compiler_LCNF_initFn___closed__16____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2285_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__16____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2285_);
if (builtin) {res = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2285_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
