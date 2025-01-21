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
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_instInhabitedDecision;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_withNewCandidate___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_reprPrec(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__12(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__15___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__16(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__1___closed__3;
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2298____closed__3;
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__6(lean_object*, lean_object*, uint64_t, uint64_t, size_t, lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2298____closed__17;
static lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__20;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at_Lean_Compiler_LCNF_FloatLetIn_float___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goCases___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__7;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint64_t l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_hashDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_15_(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2298____closed__14;
size_t lean_uint64_to_usize(uint64_t);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2298____closed__6;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_hashDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_15____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__15;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2298____closed__12;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_withNewScope___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__5(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_push___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_floatLetIn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_instHashableDecision;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___boxed(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
static uint64_t l_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___closed__5;
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2298____closed__15;
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static size_t l_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___closed__6;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo_go(lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__3___closed__1;
lean_object* l_Lean_stringToMessageData(lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__7(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__2___closed__3;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_ignore_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_ignore_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__13;
static lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__17;
lean_object* l_Lean_Compiler_LCNF_LCtx_toLocalContext(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2298____closed__11;
static lean_object* l_Lean_addTrace___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__2___closed__2;
static lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__22;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__16;
static uint64_t l_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___closed__4;
extern lean_object* l_instInhabitedPUnit;
static lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__21;
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__3___closed__8;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addTrace___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__2___closed__5;
size_t lean_ptr_addr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__11;
lean_object* l_panic___rarg(lean_object*, lean_object*);
lean_object* l_Array_reverse___rarg(lean_object*);
static lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__19;
LEAN_EXPORT lean_object* l_panic___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_floatLetIn___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1724_(lean_object*);
static lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__9;
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__11(lean_object*, lean_object*, uint64_t, uint64_t, size_t, lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_floatLetIn___closed__2;
static lean_object* l_Lean_Compiler_LCNF_floatLetIn___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__15___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_FloatLetIn_instHashableDecision___closed__1;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__3___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_beqDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_62_(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2298____closed__5;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160_(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_AltCore_getCode(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_FloatLetIn_instInhabitedDecision___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_floatLetIn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2298____closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2298____closed__1;
static lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__12;
LEAN_EXPORT lean_object* l_panic___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at_Lean_Compiler_LCNF_FloatLetIn_float___spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__16(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_lengthTRAux___rarg(lean_object*, lean_object*);
static lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__1___closed__1;
static lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__10;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_float_goFVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__3___closed__6;
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__9(lean_object*, lean_object*, uint64_t, uint64_t, size_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__2___boxed(lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__8;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__11(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__3___closed__4;
static lean_object* l_Lean_addTrace___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__2___closed__3;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__8(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__1___closed__4;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_floatLetIn(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2298____closed__13;
static lean_object* l_Lean_isTracingEnabledFor___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static double l_Lean_addTrace___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__2___closed__4;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__9(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_inheritedTraceOptions;
static lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__1;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__6(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_attachCodeDecls(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_FloatLetIn_dontFloat___closed__1;
static lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__4;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
double l_Float_ofScientific(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_AltCore_forCodeM___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__3___closed__2;
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_float___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__14(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_float___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addTrace___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__2___closed__1;
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_float_goFVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__3___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__17(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_initialNewArms(lean_object*);
static uint64_t l_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___closed__1;
static lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__6;
static lean_object* l_panic___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__3___closed__2;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__3___closed__7;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__3___closed__3;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__3(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_dontFloat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__14;
static lean_object* l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goCases(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2298____closed__7;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_beqDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_62____boxed(lean_object*, lean_object*);
uint64_t l_Lean_Name_hash___override(lean_object*);
static lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__3;
uint64_t lean_uint64_xor(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__12(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_CodeDecl_fvarId(lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__3___closed__3;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_withNewScope(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__3(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2298____closed__4;
static uint64_t l_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___closed__2;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__18;
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__3___closed__5;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseCodeDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2298____closed__16;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__15(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_float(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___rarg(lean_object*);
static lean_object* l_Lean_addTrace___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__2___closed__6;
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__7(lean_object*, lean_object*, uint64_t, uint64_t, size_t, lean_object*, size_t, size_t, lean_object*);
static lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__23;
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2298____closed__8;
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_mk(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__2___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_instBEqDecision;
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
static lean_object* l_Lean_Compiler_LCNF_FloatLetIn_instBEqDecision___closed__1;
size_t lean_array_size(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2298____closed__10;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2298_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_withNewCandidate(lean_object*);
lean_object* l_instInhabitedOfMonad___rarg(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_AltCore_forCodeM___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_withNewScope___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2298____closed__9;
static uint64_t l_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___closed__3;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goCases___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__3___closed__1;
static lean_object* l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__2___closed__4;
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__8(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__5;
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__14(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__13(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_Decision_ofAlt___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__10(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_isArrowClass_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goCases___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___rarg(lean_object*);
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__10(lean_object*, lean_object*, uint64_t, uint64_t, size_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_Decision_ofAlt(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__8(lean_object*, lean_object*, uint64_t, uint64_t, size_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision___closed__1;
LEAN_EXPORT uint64_t l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_hashDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_15_(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_hashDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_15____boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_hashDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_15_(x_1);
lean_dec(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_FloatLetIn_instHashableDecision___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_hashDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_15____boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_FloatLetIn_instHashableDecision() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Compiler_LCNF_FloatLetIn_instHashableDecision___closed__1;
return x_1;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_beqDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_62_(lean_object* x_1, lean_object* x_2) {
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
uint8_t x_6; 
x_6 = 0;
return x_6;
}
}
case 1:
{
if (lean_obj_tag(x_2) == 1)
{
uint8_t x_7; 
x_7 = 1;
return x_7;
}
else
{
uint8_t x_8; 
x_8 = 0;
return x_8;
}
}
case 2:
{
if (lean_obj_tag(x_2) == 2)
{
uint8_t x_9; 
x_9 = 1;
return x_9;
}
else
{
uint8_t x_10; 
x_10 = 0;
return x_10;
}
}
default: 
{
if (lean_obj_tag(x_2) == 3)
{
uint8_t x_11; 
x_11 = 1;
return x_11;
}
else
{
uint8_t x_12; 
x_12 = 0;
return x_12;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_beqDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_62____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_beqDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_62_(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_FloatLetIn_instBEqDecision___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_beqDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_62____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_FloatLetIn_instBEqDecision() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Compiler_LCNF_FloatLetIn_instBEqDecision___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_FloatLetIn_instInhabitedDecision___closed__1() {
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
x_1 = l_Lean_Compiler_LCNF_FloatLetIn_instInhabitedDecision___closed__1;
return x_1;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Compiler.LCNF.FloatLetIn.Decision.arm", 42, 42);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__2;
x_2 = lean_box(1);
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Compiler.LCNF.FloatLetIn.Decision.default", 46, 46);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__6;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__4;
x_2 = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__7;
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__9() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__8;
x_2 = 0;
x_3 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__5;
x_2 = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__7;
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__11() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__10;
x_2 = 0;
x_3 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Compiler.LCNF.FloatLetIn.Decision.dont", 43, 43);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__12;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__4;
x_2 = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__13;
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__15() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__14;
x_2 = 0;
x_3 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__5;
x_2 = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__13;
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__17() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__16;
x_2 = 0;
x_3 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__18() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Compiler.LCNF.FloatLetIn.Decision.unknown", 46, 46);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__18;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__4;
x_2 = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__19;
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__21() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__20;
x_2 = 0;
x_3 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__5;
x_2 = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__19;
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__23() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__22;
x_2 = 0;
x_3 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160_(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_unsigned_to_nat(1024u);
x_5 = lean_nat_dec_le(x_4, x_2);
x_6 = l_Lean_Name_reprPrec(x_3, x_4);
x_7 = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__3;
x_8 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
if (x_5 == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_9 = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__4;
x_10 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
x_11 = 0;
x_12 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set_uint8(x_12, sizeof(void*)*1, x_11);
x_13 = l_Repr_addAppParen(x_12, x_2);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
x_14 = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__5;
x_15 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_8);
x_16 = 0;
x_17 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set_uint8(x_17, sizeof(void*)*1, x_16);
x_18 = l_Repr_addAppParen(x_17, x_2);
return x_18;
}
}
case 1:
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_unsigned_to_nat(1024u);
x_20 = lean_nat_dec_le(x_19, x_2);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__9;
x_22 = l_Repr_addAppParen(x_21, x_2);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__11;
x_24 = l_Repr_addAppParen(x_23, x_2);
return x_24;
}
}
case 2:
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_unsigned_to_nat(1024u);
x_26 = lean_nat_dec_le(x_25, x_2);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__15;
x_28 = l_Repr_addAppParen(x_27, x_2);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__17;
x_30 = l_Repr_addAppParen(x_29, x_2);
return x_30;
}
}
default: 
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_unsigned_to_nat(1024u);
x_32 = lean_nat_dec_le(x_31, x_2);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__21;
x_34 = l_Repr_addAppParen(x_33, x_2);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__23;
x_36 = l_Repr_addAppParen(x_35, x_2);
return x_36;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160_(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision___closed__1;
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_withNewCandidate___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_withNewCandidate(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_FloatLetIn_withNewCandidate___rarg), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_withNewScope___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_box(0);
x_9 = lean_apply_6(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_withNewScope(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_FloatLetIn_withNewScope___rarg___boxed), 7, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_withNewScope___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_FloatLetIn_withNewScope___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_ignore_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_1, 2);
lean_inc(x_8);
x_9 = l_Lean_Compiler_LCNF_isArrowClass_x3f(x_8, x_5, x_6, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_1, 3);
lean_inc(x_11);
lean_dec(x_1);
if (lean_obj_tag(x_11) == 2)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_dec(x_9);
x_13 = lean_ctor_get(x_11, 2);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Compiler_LCNF_getType(x_13, x_3, x_4, x_5, x_6, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_Compiler_LCNF_isArrowClass_x3f(x_15, x_5, x_6, x_16);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_17);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_17, 0);
lean_dec(x_20);
x_21 = 0;
x_22 = lean_box(x_21);
lean_ctor_set(x_17, 0, x_22);
return x_17;
}
else
{
lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_17, 1);
lean_inc(x_23);
lean_dec(x_17);
x_24 = 0;
x_25 = lean_box(x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_23);
return x_26;
}
}
else
{
uint8_t x_27; 
lean_dec(x_18);
x_27 = !lean_is_exclusive(x_17);
if (x_27 == 0)
{
lean_object* x_28; uint8_t x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_17, 0);
lean_dec(x_28);
x_29 = 1;
x_30 = lean_box(x_29);
lean_ctor_set(x_17, 0, x_30);
return x_17;
}
else
{
lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_17, 1);
lean_inc(x_31);
lean_dec(x_17);
x_32 = 1;
x_33 = lean_box(x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_31);
return x_34;
}
}
}
else
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_14);
if (x_35 == 0)
{
return x_14;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_14, 0);
x_37 = lean_ctor_get(x_14, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_14);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
else
{
uint8_t x_39; 
lean_dec(x_11);
x_39 = !lean_is_exclusive(x_9);
if (x_39 == 0)
{
lean_object* x_40; uint8_t x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_9, 0);
lean_dec(x_40);
x_41 = 0;
x_42 = lean_box(x_41);
lean_ctor_set(x_9, 0, x_42);
return x_9;
}
else
{
lean_object* x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; 
x_43 = lean_ctor_get(x_9, 1);
lean_inc(x_43);
lean_dec(x_9);
x_44 = 0;
x_45 = lean_box(x_44);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_43);
return x_46;
}
}
}
else
{
uint8_t x_47; 
lean_dec(x_10);
lean_dec(x_1);
x_47 = !lean_is_exclusive(x_9);
if (x_47 == 0)
{
lean_object* x_48; uint8_t x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_9, 0);
lean_dec(x_48);
x_49 = 1;
x_50 = lean_box(x_49);
lean_ctor_set(x_9, 0, x_50);
return x_9;
}
else
{
lean_object* x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; 
x_51 = lean_ctor_get(x_9, 1);
lean_inc(x_51);
lean_dec(x_9);
x_52 = 1;
x_53 = lean_box(x_52);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_51);
return x_54;
}
}
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_name_eq(x_4, x_1);
if (x_7 == 0)
{
x_2 = x_6;
goto _start;
}
else
{
lean_object* x_9; 
lean_inc(x_5);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_5);
return x_9;
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_name_eq(x_4, x_1);
if (x_6 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
uint8_t x_8; 
x_8 = 1;
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__5(lean_object* x_1, lean_object* x_2) {
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
x_7 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1724_(x_4);
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
x_26 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1724_(x_22);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__5(x_3, x_6);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(2u);
x_4 = lean_nat_mul(x_2, x_3);
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = lean_mk_array(x_4, x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Std_DHashMap_Internal_Raw_u2080_expand_go___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__4(x_7, x_1, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(0);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_3, 1);
x_8 = lean_ctor_get(x_3, 2);
x_9 = lean_name_eq(x_6, x_1);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__6(x_1, x_2, x_8);
lean_ctor_set(x_3, 2, x_10);
return x_3;
}
else
{
lean_dec(x_7);
lean_dec(x_6);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_3, 1);
x_13 = lean_ctor_get(x_3, 2);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_3);
x_14 = lean_name_eq(x_11, x_1);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__6(x_1, x_2, x_13);
x_16 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_16, 0, x_11);
lean_ctor_set(x_16, 1, x_12);
lean_ctor_set(x_16, 2, x_15);
return x_16;
}
else
{
lean_object* x_17; 
lean_dec(x_12);
lean_dec(x_11);
x_17 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_2);
lean_ctor_set(x_17, 2, x_13);
return x_17;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_st_ref_get(x_3, x_9);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint64_t x_16; uint64_t x_17; uint64_t x_18; uint64_t x_19; uint64_t x_20; uint64_t x_21; uint64_t x_22; size_t x_23; size_t x_24; size_t x_25; size_t x_26; size_t x_27; lean_object* x_28; lean_object* x_29; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_array_get_size(x_14);
x_16 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1724_(x_2);
x_17 = 32;
x_18 = lean_uint64_shift_right(x_16, x_17);
x_19 = lean_uint64_xor(x_16, x_18);
x_20 = 16;
x_21 = lean_uint64_shift_right(x_19, x_20);
x_22 = lean_uint64_xor(x_19, x_21);
x_23 = lean_uint64_to_usize(x_22);
x_24 = lean_usize_of_nat(x_15);
lean_dec(x_15);
x_25 = 1;
x_26 = lean_usize_sub(x_24, x_25);
x_27 = lean_usize_land(x_23, x_26);
x_28 = lean_array_uget(x_14, x_27);
lean_dec(x_14);
x_29 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__1(x_2, x_28);
lean_dec(x_28);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; 
lean_dec(x_2);
lean_dec(x_1);
x_30 = lean_box(0);
lean_ctor_set(x_10, 0, x_30);
return x_10;
}
else
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_31 = lean_ctor_get(x_29, 0);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_box(3);
x_33 = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_beqDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_62_(x_31, x_32);
if (x_33 == 0)
{
uint8_t x_34; 
x_34 = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_beqDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_62_(x_31, x_1);
lean_dec(x_1);
lean_dec(x_31);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
lean_free_object(x_10);
x_35 = lean_st_ref_take(x_3, x_13);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = !lean_is_exclusive(x_36);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; size_t x_42; size_t x_43; size_t x_44; lean_object* x_45; uint8_t x_46; 
x_39 = lean_ctor_get(x_36, 0);
x_40 = lean_ctor_get(x_36, 1);
x_41 = lean_array_get_size(x_40);
x_42 = lean_usize_of_nat(x_41);
lean_dec(x_41);
x_43 = lean_usize_sub(x_42, x_25);
x_44 = lean_usize_land(x_23, x_43);
x_45 = lean_array_uget(x_40, x_44);
x_46 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__2(x_2, x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_47 = lean_unsigned_to_nat(1u);
x_48 = lean_nat_add(x_39, x_47);
lean_dec(x_39);
x_49 = lean_box(2);
x_50 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_50, 0, x_2);
lean_ctor_set(x_50, 1, x_49);
lean_ctor_set(x_50, 2, x_45);
x_51 = lean_array_uset(x_40, x_44, x_50);
x_52 = lean_unsigned_to_nat(4u);
x_53 = lean_nat_mul(x_48, x_52);
x_54 = lean_unsigned_to_nat(3u);
x_55 = lean_nat_div(x_53, x_54);
lean_dec(x_53);
x_56 = lean_array_get_size(x_51);
x_57 = lean_nat_dec_le(x_55, x_56);
lean_dec(x_56);
lean_dec(x_55);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_58 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__3(x_51);
lean_ctor_set(x_36, 1, x_58);
lean_ctor_set(x_36, 0, x_48);
x_59 = lean_st_ref_set(x_3, x_36, x_37);
x_60 = !lean_is_exclusive(x_59);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_59, 0);
lean_dec(x_61);
x_62 = lean_box(0);
lean_ctor_set(x_59, 0, x_62);
return x_59;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_59, 1);
lean_inc(x_63);
lean_dec(x_59);
x_64 = lean_box(0);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_63);
return x_65;
}
}
else
{
lean_object* x_66; uint8_t x_67; 
lean_ctor_set(x_36, 1, x_51);
lean_ctor_set(x_36, 0, x_48);
x_66 = lean_st_ref_set(x_3, x_36, x_37);
x_67 = !lean_is_exclusive(x_66);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_66, 0);
lean_dec(x_68);
x_69 = lean_box(0);
lean_ctor_set(x_66, 0, x_69);
return x_66;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_66, 1);
lean_inc(x_70);
lean_dec(x_66);
x_71 = lean_box(0);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_70);
return x_72;
}
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; 
x_73 = lean_box(0);
x_74 = lean_array_uset(x_40, x_44, x_73);
x_75 = lean_box(2);
x_76 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__6(x_2, x_75, x_45);
x_77 = lean_array_uset(x_74, x_44, x_76);
lean_ctor_set(x_36, 1, x_77);
x_78 = lean_st_ref_set(x_3, x_36, x_37);
x_79 = !lean_is_exclusive(x_78);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; 
x_80 = lean_ctor_get(x_78, 0);
lean_dec(x_80);
x_81 = lean_box(0);
lean_ctor_set(x_78, 0, x_81);
return x_78;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_78, 1);
lean_inc(x_82);
lean_dec(x_78);
x_83 = lean_box(0);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_82);
return x_84;
}
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; size_t x_88; size_t x_89; size_t x_90; lean_object* x_91; uint8_t x_92; 
x_85 = lean_ctor_get(x_36, 0);
x_86 = lean_ctor_get(x_36, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_36);
x_87 = lean_array_get_size(x_86);
x_88 = lean_usize_of_nat(x_87);
lean_dec(x_87);
x_89 = lean_usize_sub(x_88, x_25);
x_90 = lean_usize_land(x_23, x_89);
x_91 = lean_array_uget(x_86, x_90);
x_92 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__2(x_2, x_91);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_93 = lean_unsigned_to_nat(1u);
x_94 = lean_nat_add(x_85, x_93);
lean_dec(x_85);
x_95 = lean_box(2);
x_96 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_96, 0, x_2);
lean_ctor_set(x_96, 1, x_95);
lean_ctor_set(x_96, 2, x_91);
x_97 = lean_array_uset(x_86, x_90, x_96);
x_98 = lean_unsigned_to_nat(4u);
x_99 = lean_nat_mul(x_94, x_98);
x_100 = lean_unsigned_to_nat(3u);
x_101 = lean_nat_div(x_99, x_100);
lean_dec(x_99);
x_102 = lean_array_get_size(x_97);
x_103 = lean_nat_dec_le(x_101, x_102);
lean_dec(x_102);
lean_dec(x_101);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_104 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__3(x_97);
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_94);
lean_ctor_set(x_105, 1, x_104);
x_106 = lean_st_ref_set(x_3, x_105, x_37);
x_107 = lean_ctor_get(x_106, 1);
lean_inc(x_107);
if (lean_is_exclusive(x_106)) {
 lean_ctor_release(x_106, 0);
 lean_ctor_release(x_106, 1);
 x_108 = x_106;
} else {
 lean_dec_ref(x_106);
 x_108 = lean_box(0);
}
x_109 = lean_box(0);
if (lean_is_scalar(x_108)) {
 x_110 = lean_alloc_ctor(0, 2, 0);
} else {
 x_110 = x_108;
}
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_107);
return x_110;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_94);
lean_ctor_set(x_111, 1, x_97);
x_112 = lean_st_ref_set(x_3, x_111, x_37);
x_113 = lean_ctor_get(x_112, 1);
lean_inc(x_113);
if (lean_is_exclusive(x_112)) {
 lean_ctor_release(x_112, 0);
 lean_ctor_release(x_112, 1);
 x_114 = x_112;
} else {
 lean_dec_ref(x_112);
 x_114 = lean_box(0);
}
x_115 = lean_box(0);
if (lean_is_scalar(x_114)) {
 x_116 = lean_alloc_ctor(0, 2, 0);
} else {
 x_116 = x_114;
}
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_113);
return x_116;
}
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_117 = lean_box(0);
x_118 = lean_array_uset(x_86, x_90, x_117);
x_119 = lean_box(2);
x_120 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__6(x_2, x_119, x_91);
x_121 = lean_array_uset(x_118, x_90, x_120);
x_122 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_122, 0, x_85);
lean_ctor_set(x_122, 1, x_121);
x_123 = lean_st_ref_set(x_3, x_122, x_37);
x_124 = lean_ctor_get(x_123, 1);
lean_inc(x_124);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 lean_ctor_release(x_123, 1);
 x_125 = x_123;
} else {
 lean_dec_ref(x_123);
 x_125 = lean_box(0);
}
x_126 = lean_box(0);
if (lean_is_scalar(x_125)) {
 x_127 = lean_alloc_ctor(0, 2, 0);
} else {
 x_127 = x_125;
}
lean_ctor_set(x_127, 0, x_126);
lean_ctor_set(x_127, 1, x_124);
return x_127;
}
}
}
else
{
lean_object* x_128; 
lean_dec(x_2);
x_128 = lean_box(0);
lean_ctor_set(x_10, 0, x_128);
return x_10;
}
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; uint8_t x_132; 
lean_dec(x_31);
lean_free_object(x_10);
x_129 = lean_st_ref_take(x_3, x_13);
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_129, 1);
lean_inc(x_131);
lean_dec(x_129);
x_132 = !lean_is_exclusive(x_130);
if (x_132 == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; size_t x_136; size_t x_137; size_t x_138; lean_object* x_139; uint8_t x_140; 
x_133 = lean_ctor_get(x_130, 0);
x_134 = lean_ctor_get(x_130, 1);
x_135 = lean_array_get_size(x_134);
x_136 = lean_usize_of_nat(x_135);
lean_dec(x_135);
x_137 = lean_usize_sub(x_136, x_25);
x_138 = lean_usize_land(x_23, x_137);
x_139 = lean_array_uget(x_134, x_138);
x_140 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__2(x_2, x_139);
if (x_140 == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; uint8_t x_150; 
x_141 = lean_unsigned_to_nat(1u);
x_142 = lean_nat_add(x_133, x_141);
lean_dec(x_133);
x_143 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_143, 0, x_2);
lean_ctor_set(x_143, 1, x_1);
lean_ctor_set(x_143, 2, x_139);
x_144 = lean_array_uset(x_134, x_138, x_143);
x_145 = lean_unsigned_to_nat(4u);
x_146 = lean_nat_mul(x_142, x_145);
x_147 = lean_unsigned_to_nat(3u);
x_148 = lean_nat_div(x_146, x_147);
lean_dec(x_146);
x_149 = lean_array_get_size(x_144);
x_150 = lean_nat_dec_le(x_148, x_149);
lean_dec(x_149);
lean_dec(x_148);
if (x_150 == 0)
{
lean_object* x_151; lean_object* x_152; uint8_t x_153; 
x_151 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__3(x_144);
lean_ctor_set(x_130, 1, x_151);
lean_ctor_set(x_130, 0, x_142);
x_152 = lean_st_ref_set(x_3, x_130, x_131);
x_153 = !lean_is_exclusive(x_152);
if (x_153 == 0)
{
lean_object* x_154; lean_object* x_155; 
x_154 = lean_ctor_get(x_152, 0);
lean_dec(x_154);
x_155 = lean_box(0);
lean_ctor_set(x_152, 0, x_155);
return x_152;
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_156 = lean_ctor_get(x_152, 1);
lean_inc(x_156);
lean_dec(x_152);
x_157 = lean_box(0);
x_158 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_158, 0, x_157);
lean_ctor_set(x_158, 1, x_156);
return x_158;
}
}
else
{
lean_object* x_159; uint8_t x_160; 
lean_ctor_set(x_130, 1, x_144);
lean_ctor_set(x_130, 0, x_142);
x_159 = lean_st_ref_set(x_3, x_130, x_131);
x_160 = !lean_is_exclusive(x_159);
if (x_160 == 0)
{
lean_object* x_161; lean_object* x_162; 
x_161 = lean_ctor_get(x_159, 0);
lean_dec(x_161);
x_162 = lean_box(0);
lean_ctor_set(x_159, 0, x_162);
return x_159;
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_163 = lean_ctor_get(x_159, 1);
lean_inc(x_163);
lean_dec(x_159);
x_164 = lean_box(0);
x_165 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_165, 0, x_164);
lean_ctor_set(x_165, 1, x_163);
return x_165;
}
}
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; uint8_t x_171; 
x_166 = lean_box(0);
x_167 = lean_array_uset(x_134, x_138, x_166);
x_168 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__6(x_2, x_1, x_139);
x_169 = lean_array_uset(x_167, x_138, x_168);
lean_ctor_set(x_130, 1, x_169);
x_170 = lean_st_ref_set(x_3, x_130, x_131);
x_171 = !lean_is_exclusive(x_170);
if (x_171 == 0)
{
lean_object* x_172; lean_object* x_173; 
x_172 = lean_ctor_get(x_170, 0);
lean_dec(x_172);
x_173 = lean_box(0);
lean_ctor_set(x_170, 0, x_173);
return x_170;
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_174 = lean_ctor_get(x_170, 1);
lean_inc(x_174);
lean_dec(x_170);
x_175 = lean_box(0);
x_176 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_176, 0, x_175);
lean_ctor_set(x_176, 1, x_174);
return x_176;
}
}
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; size_t x_180; size_t x_181; size_t x_182; lean_object* x_183; uint8_t x_184; 
x_177 = lean_ctor_get(x_130, 0);
x_178 = lean_ctor_get(x_130, 1);
lean_inc(x_178);
lean_inc(x_177);
lean_dec(x_130);
x_179 = lean_array_get_size(x_178);
x_180 = lean_usize_of_nat(x_179);
lean_dec(x_179);
x_181 = lean_usize_sub(x_180, x_25);
x_182 = lean_usize_land(x_23, x_181);
x_183 = lean_array_uget(x_178, x_182);
x_184 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__2(x_2, x_183);
if (x_184 == 0)
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; uint8_t x_194; 
x_185 = lean_unsigned_to_nat(1u);
x_186 = lean_nat_add(x_177, x_185);
lean_dec(x_177);
x_187 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_187, 0, x_2);
lean_ctor_set(x_187, 1, x_1);
lean_ctor_set(x_187, 2, x_183);
x_188 = lean_array_uset(x_178, x_182, x_187);
x_189 = lean_unsigned_to_nat(4u);
x_190 = lean_nat_mul(x_186, x_189);
x_191 = lean_unsigned_to_nat(3u);
x_192 = lean_nat_div(x_190, x_191);
lean_dec(x_190);
x_193 = lean_array_get_size(x_188);
x_194 = lean_nat_dec_le(x_192, x_193);
lean_dec(x_193);
lean_dec(x_192);
if (x_194 == 0)
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_195 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__3(x_188);
x_196 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_196, 0, x_186);
lean_ctor_set(x_196, 1, x_195);
x_197 = lean_st_ref_set(x_3, x_196, x_131);
x_198 = lean_ctor_get(x_197, 1);
lean_inc(x_198);
if (lean_is_exclusive(x_197)) {
 lean_ctor_release(x_197, 0);
 lean_ctor_release(x_197, 1);
 x_199 = x_197;
} else {
 lean_dec_ref(x_197);
 x_199 = lean_box(0);
}
x_200 = lean_box(0);
if (lean_is_scalar(x_199)) {
 x_201 = lean_alloc_ctor(0, 2, 0);
} else {
 x_201 = x_199;
}
lean_ctor_set(x_201, 0, x_200);
lean_ctor_set(x_201, 1, x_198);
return x_201;
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; 
x_202 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_202, 0, x_186);
lean_ctor_set(x_202, 1, x_188);
x_203 = lean_st_ref_set(x_3, x_202, x_131);
x_204 = lean_ctor_get(x_203, 1);
lean_inc(x_204);
if (lean_is_exclusive(x_203)) {
 lean_ctor_release(x_203, 0);
 lean_ctor_release(x_203, 1);
 x_205 = x_203;
} else {
 lean_dec_ref(x_203);
 x_205 = lean_box(0);
}
x_206 = lean_box(0);
if (lean_is_scalar(x_205)) {
 x_207 = lean_alloc_ctor(0, 2, 0);
} else {
 x_207 = x_205;
}
lean_ctor_set(x_207, 0, x_206);
lean_ctor_set(x_207, 1, x_204);
return x_207;
}
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; 
x_208 = lean_box(0);
x_209 = lean_array_uset(x_178, x_182, x_208);
x_210 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__6(x_2, x_1, x_183);
x_211 = lean_array_uset(x_209, x_182, x_210);
x_212 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_212, 0, x_177);
lean_ctor_set(x_212, 1, x_211);
x_213 = lean_st_ref_set(x_3, x_212, x_131);
x_214 = lean_ctor_get(x_213, 1);
lean_inc(x_214);
if (lean_is_exclusive(x_213)) {
 lean_ctor_release(x_213, 0);
 lean_ctor_release(x_213, 1);
 x_215 = x_213;
} else {
 lean_dec_ref(x_213);
 x_215 = lean_box(0);
}
x_216 = lean_box(0);
if (lean_is_scalar(x_215)) {
 x_217 = lean_alloc_ctor(0, 2, 0);
} else {
 x_217 = x_215;
}
lean_ctor_set(x_217, 0, x_216);
lean_ctor_set(x_217, 1, x_214);
return x_217;
}
}
}
}
}
else
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; uint64_t x_222; uint64_t x_223; uint64_t x_224; uint64_t x_225; uint64_t x_226; uint64_t x_227; uint64_t x_228; size_t x_229; size_t x_230; size_t x_231; size_t x_232; size_t x_233; lean_object* x_234; lean_object* x_235; 
x_218 = lean_ctor_get(x_10, 0);
x_219 = lean_ctor_get(x_10, 1);
lean_inc(x_219);
lean_inc(x_218);
lean_dec(x_10);
x_220 = lean_ctor_get(x_218, 1);
lean_inc(x_220);
lean_dec(x_218);
x_221 = lean_array_get_size(x_220);
x_222 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1724_(x_2);
x_223 = 32;
x_224 = lean_uint64_shift_right(x_222, x_223);
x_225 = lean_uint64_xor(x_222, x_224);
x_226 = 16;
x_227 = lean_uint64_shift_right(x_225, x_226);
x_228 = lean_uint64_xor(x_225, x_227);
x_229 = lean_uint64_to_usize(x_228);
x_230 = lean_usize_of_nat(x_221);
lean_dec(x_221);
x_231 = 1;
x_232 = lean_usize_sub(x_230, x_231);
x_233 = lean_usize_land(x_229, x_232);
x_234 = lean_array_uget(x_220, x_233);
lean_dec(x_220);
x_235 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__1(x_2, x_234);
lean_dec(x_234);
if (lean_obj_tag(x_235) == 0)
{
lean_object* x_236; lean_object* x_237; 
lean_dec(x_2);
lean_dec(x_1);
x_236 = lean_box(0);
x_237 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_237, 0, x_236);
lean_ctor_set(x_237, 1, x_219);
return x_237;
}
else
{
lean_object* x_238; lean_object* x_239; uint8_t x_240; 
x_238 = lean_ctor_get(x_235, 0);
lean_inc(x_238);
lean_dec(x_235);
x_239 = lean_box(3);
x_240 = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_beqDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_62_(x_238, x_239);
if (x_240 == 0)
{
uint8_t x_241; 
x_241 = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_beqDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_62_(x_238, x_1);
lean_dec(x_1);
lean_dec(x_238);
if (x_241 == 0)
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; size_t x_249; size_t x_250; size_t x_251; lean_object* x_252; uint8_t x_253; 
x_242 = lean_st_ref_take(x_3, x_219);
x_243 = lean_ctor_get(x_242, 0);
lean_inc(x_243);
x_244 = lean_ctor_get(x_242, 1);
lean_inc(x_244);
lean_dec(x_242);
x_245 = lean_ctor_get(x_243, 0);
lean_inc(x_245);
x_246 = lean_ctor_get(x_243, 1);
lean_inc(x_246);
if (lean_is_exclusive(x_243)) {
 lean_ctor_release(x_243, 0);
 lean_ctor_release(x_243, 1);
 x_247 = x_243;
} else {
 lean_dec_ref(x_243);
 x_247 = lean_box(0);
}
x_248 = lean_array_get_size(x_246);
x_249 = lean_usize_of_nat(x_248);
lean_dec(x_248);
x_250 = lean_usize_sub(x_249, x_231);
x_251 = lean_usize_land(x_229, x_250);
x_252 = lean_array_uget(x_246, x_251);
x_253 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__2(x_2, x_252);
if (x_253 == 0)
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; uint8_t x_264; 
x_254 = lean_unsigned_to_nat(1u);
x_255 = lean_nat_add(x_245, x_254);
lean_dec(x_245);
x_256 = lean_box(2);
x_257 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_257, 0, x_2);
lean_ctor_set(x_257, 1, x_256);
lean_ctor_set(x_257, 2, x_252);
x_258 = lean_array_uset(x_246, x_251, x_257);
x_259 = lean_unsigned_to_nat(4u);
x_260 = lean_nat_mul(x_255, x_259);
x_261 = lean_unsigned_to_nat(3u);
x_262 = lean_nat_div(x_260, x_261);
lean_dec(x_260);
x_263 = lean_array_get_size(x_258);
x_264 = lean_nat_dec_le(x_262, x_263);
lean_dec(x_263);
lean_dec(x_262);
if (x_264 == 0)
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; 
x_265 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__3(x_258);
if (lean_is_scalar(x_247)) {
 x_266 = lean_alloc_ctor(0, 2, 0);
} else {
 x_266 = x_247;
}
lean_ctor_set(x_266, 0, x_255);
lean_ctor_set(x_266, 1, x_265);
x_267 = lean_st_ref_set(x_3, x_266, x_244);
x_268 = lean_ctor_get(x_267, 1);
lean_inc(x_268);
if (lean_is_exclusive(x_267)) {
 lean_ctor_release(x_267, 0);
 lean_ctor_release(x_267, 1);
 x_269 = x_267;
} else {
 lean_dec_ref(x_267);
 x_269 = lean_box(0);
}
x_270 = lean_box(0);
if (lean_is_scalar(x_269)) {
 x_271 = lean_alloc_ctor(0, 2, 0);
} else {
 x_271 = x_269;
}
lean_ctor_set(x_271, 0, x_270);
lean_ctor_set(x_271, 1, x_268);
return x_271;
}
else
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; 
if (lean_is_scalar(x_247)) {
 x_272 = lean_alloc_ctor(0, 2, 0);
} else {
 x_272 = x_247;
}
lean_ctor_set(x_272, 0, x_255);
lean_ctor_set(x_272, 1, x_258);
x_273 = lean_st_ref_set(x_3, x_272, x_244);
x_274 = lean_ctor_get(x_273, 1);
lean_inc(x_274);
if (lean_is_exclusive(x_273)) {
 lean_ctor_release(x_273, 0);
 lean_ctor_release(x_273, 1);
 x_275 = x_273;
} else {
 lean_dec_ref(x_273);
 x_275 = lean_box(0);
}
x_276 = lean_box(0);
if (lean_is_scalar(x_275)) {
 x_277 = lean_alloc_ctor(0, 2, 0);
} else {
 x_277 = x_275;
}
lean_ctor_set(x_277, 0, x_276);
lean_ctor_set(x_277, 1, x_274);
return x_277;
}
}
else
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; 
x_278 = lean_box(0);
x_279 = lean_array_uset(x_246, x_251, x_278);
x_280 = lean_box(2);
x_281 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__6(x_2, x_280, x_252);
x_282 = lean_array_uset(x_279, x_251, x_281);
if (lean_is_scalar(x_247)) {
 x_283 = lean_alloc_ctor(0, 2, 0);
} else {
 x_283 = x_247;
}
lean_ctor_set(x_283, 0, x_245);
lean_ctor_set(x_283, 1, x_282);
x_284 = lean_st_ref_set(x_3, x_283, x_244);
x_285 = lean_ctor_get(x_284, 1);
lean_inc(x_285);
if (lean_is_exclusive(x_284)) {
 lean_ctor_release(x_284, 0);
 lean_ctor_release(x_284, 1);
 x_286 = x_284;
} else {
 lean_dec_ref(x_284);
 x_286 = lean_box(0);
}
x_287 = lean_box(0);
if (lean_is_scalar(x_286)) {
 x_288 = lean_alloc_ctor(0, 2, 0);
} else {
 x_288 = x_286;
}
lean_ctor_set(x_288, 0, x_287);
lean_ctor_set(x_288, 1, x_285);
return x_288;
}
}
else
{
lean_object* x_289; lean_object* x_290; 
lean_dec(x_2);
x_289 = lean_box(0);
x_290 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_290, 0, x_289);
lean_ctor_set(x_290, 1, x_219);
return x_290;
}
}
else
{
lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; size_t x_298; size_t x_299; size_t x_300; lean_object* x_301; uint8_t x_302; 
lean_dec(x_238);
x_291 = lean_st_ref_take(x_3, x_219);
x_292 = lean_ctor_get(x_291, 0);
lean_inc(x_292);
x_293 = lean_ctor_get(x_291, 1);
lean_inc(x_293);
lean_dec(x_291);
x_294 = lean_ctor_get(x_292, 0);
lean_inc(x_294);
x_295 = lean_ctor_get(x_292, 1);
lean_inc(x_295);
if (lean_is_exclusive(x_292)) {
 lean_ctor_release(x_292, 0);
 lean_ctor_release(x_292, 1);
 x_296 = x_292;
} else {
 lean_dec_ref(x_292);
 x_296 = lean_box(0);
}
x_297 = lean_array_get_size(x_295);
x_298 = lean_usize_of_nat(x_297);
lean_dec(x_297);
x_299 = lean_usize_sub(x_298, x_231);
x_300 = lean_usize_land(x_229, x_299);
x_301 = lean_array_uget(x_295, x_300);
x_302 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__2(x_2, x_301);
if (x_302 == 0)
{
lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; uint8_t x_312; 
x_303 = lean_unsigned_to_nat(1u);
x_304 = lean_nat_add(x_294, x_303);
lean_dec(x_294);
x_305 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_305, 0, x_2);
lean_ctor_set(x_305, 1, x_1);
lean_ctor_set(x_305, 2, x_301);
x_306 = lean_array_uset(x_295, x_300, x_305);
x_307 = lean_unsigned_to_nat(4u);
x_308 = lean_nat_mul(x_304, x_307);
x_309 = lean_unsigned_to_nat(3u);
x_310 = lean_nat_div(x_308, x_309);
lean_dec(x_308);
x_311 = lean_array_get_size(x_306);
x_312 = lean_nat_dec_le(x_310, x_311);
lean_dec(x_311);
lean_dec(x_310);
if (x_312 == 0)
{
lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; 
x_313 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__3(x_306);
if (lean_is_scalar(x_296)) {
 x_314 = lean_alloc_ctor(0, 2, 0);
} else {
 x_314 = x_296;
}
lean_ctor_set(x_314, 0, x_304);
lean_ctor_set(x_314, 1, x_313);
x_315 = lean_st_ref_set(x_3, x_314, x_293);
x_316 = lean_ctor_get(x_315, 1);
lean_inc(x_316);
if (lean_is_exclusive(x_315)) {
 lean_ctor_release(x_315, 0);
 lean_ctor_release(x_315, 1);
 x_317 = x_315;
} else {
 lean_dec_ref(x_315);
 x_317 = lean_box(0);
}
x_318 = lean_box(0);
if (lean_is_scalar(x_317)) {
 x_319 = lean_alloc_ctor(0, 2, 0);
} else {
 x_319 = x_317;
}
lean_ctor_set(x_319, 0, x_318);
lean_ctor_set(x_319, 1, x_316);
return x_319;
}
else
{
lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; 
if (lean_is_scalar(x_296)) {
 x_320 = lean_alloc_ctor(0, 2, 0);
} else {
 x_320 = x_296;
}
lean_ctor_set(x_320, 0, x_304);
lean_ctor_set(x_320, 1, x_306);
x_321 = lean_st_ref_set(x_3, x_320, x_293);
x_322 = lean_ctor_get(x_321, 1);
lean_inc(x_322);
if (lean_is_exclusive(x_321)) {
 lean_ctor_release(x_321, 0);
 lean_ctor_release(x_321, 1);
 x_323 = x_321;
} else {
 lean_dec_ref(x_321);
 x_323 = lean_box(0);
}
x_324 = lean_box(0);
if (lean_is_scalar(x_323)) {
 x_325 = lean_alloc_ctor(0, 2, 0);
} else {
 x_325 = x_323;
}
lean_ctor_set(x_325, 0, x_324);
lean_ctor_set(x_325, 1, x_322);
return x_325;
}
}
else
{
lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; 
x_326 = lean_box(0);
x_327 = lean_array_uset(x_295, x_300, x_326);
x_328 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__6(x_2, x_1, x_301);
x_329 = lean_array_uset(x_327, x_300, x_328);
if (lean_is_scalar(x_296)) {
 x_330 = lean_alloc_ctor(0, 2, 0);
} else {
 x_330 = x_296;
}
lean_ctor_set(x_330, 0, x_294);
lean_ctor_set(x_330, 1, x_329);
x_331 = lean_st_ref_set(x_3, x_330, x_293);
x_332 = lean_ctor_get(x_331, 1);
lean_inc(x_332);
if (lean_is_exclusive(x_331)) {
 lean_ctor_release(x_331, 0);
 lean_ctor_release(x_331, 1);
 x_333 = x_331;
} else {
 lean_dec_ref(x_331);
 x_333 = lean_box(0);
}
x_334 = lean_box(0);
if (lean_is_scalar(x_333)) {
 x_335 = lean_alloc_ctor(0, 2, 0);
} else {
 x_335 = x_333;
}
lean_ctor_set(x_335, 0, x_334);
lean_ctor_set(x_335, 1, x_332);
return x_335;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
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
static lean_object* _init_l_panic___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__3___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_instMonadCompilerM;
x_2 = l_ReaderT_instMonad___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_panic___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_panic___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__3___closed__1;
x_2 = l_ReaderT_instMonad___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_panic___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_panic___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__3___closed__2;
x_2 = l_instInhabitedPUnit;
x_3 = l_instInhabitedOfMonad___rarg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = l_panic___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__3___closed__3;
x_10 = lean_panic_fn(x_9, x_1);
x_11 = lean_apply_7(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Compiler.LCNF.FVarUtil", 27, 27);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Compiler.LCNF.Expr.forFVarM", 32, 32);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__2___closed__1;
x_2 = l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__2___closed__2;
x_3 = lean_unsigned_to_nat(43u);
x_4 = lean_unsigned_to_nat(38u);
x_5 = l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__2___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 1:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
lean_dec(x_2);
x_11 = lean_apply_8(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
case 2:
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_2);
lean_dec(x_1);
x_12 = l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__2___closed__4;
x_13 = l_panic___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__3(x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_13;
}
case 5:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_2, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_2, 1);
lean_inc(x_15);
lean_dec(x_2);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_16 = l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__2(x_1, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_2 = x_15;
x_9 = x_17;
goto _start;
}
else
{
uint8_t x_19; 
lean_dec(x_15);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_19 = !lean_is_exclusive(x_16);
if (x_19 == 0)
{
return x_16;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_16, 0);
x_21 = lean_ctor_get(x_16, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_16);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
case 6:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_2, 1);
lean_inc(x_23);
x_24 = lean_ctor_get(x_2, 2);
lean_inc(x_24);
lean_dec(x_2);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_25 = l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__2(x_1, x_23, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_2 = x_24;
x_9 = x_26;
goto _start;
}
else
{
uint8_t x_28; 
lean_dec(x_24);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_25);
if (x_28 == 0)
{
return x_25;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_25, 0);
x_30 = lean_ctor_get(x_25, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_25);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
case 7:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_2, 1);
lean_inc(x_32);
x_33 = lean_ctor_get(x_2, 2);
lean_inc(x_33);
lean_dec(x_2);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_34 = l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__2(x_1, x_32, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
x_2 = x_33;
x_9 = x_35;
goto _start;
}
else
{
uint8_t x_37; 
lean_dec(x_33);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_37 = !lean_is_exclusive(x_34);
if (x_37 == 0)
{
return x_34;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_34, 0);
x_39 = lean_ctor_get(x_34, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_34);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
case 8:
{
lean_object* x_41; lean_object* x_42; 
lean_dec(x_2);
lean_dec(x_1);
x_41 = l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__2___closed__4;
x_42 = l_panic___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__3(x_41, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_42;
}
case 11:
{
lean_object* x_43; lean_object* x_44; 
lean_dec(x_2);
lean_dec(x_1);
x_43 = l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__2___closed__4;
x_44 = l_panic___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__3(x_43, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_44;
}
default: 
{
lean_object* x_45; lean_object* x_46; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_45 = lean_box(0);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_9);
return x_46;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_2, 2);
lean_inc(x_10);
lean_dec(x_2);
x_11 = l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__2(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
x_15 = l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__2(x_1, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__8(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
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
x_15 = l_Lean_Compiler_LCNF_Arg_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__7(x_1, x_14, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
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
uint8_t x_21; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_15);
if (x_21 == 0)
{
return x_15;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_15, 0);
x_23 = lean_ctor_get(x_15, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_15);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
else
{
lean_object* x_25; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_5);
lean_ctor_set(x_25, 1, x_12);
return x_25;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__9(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
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
x_15 = l_Lean_Compiler_LCNF_Arg_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__7(x_1, x_14, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
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
uint8_t x_21; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_15);
if (x_21 == 0)
{
return x_15;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_15, 0);
x_23 = lean_ctor_get(x_15, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_15);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
else
{
lean_object* x_25; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_5);
lean_ctor_set(x_25, 1, x_12);
return x_25;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_2, 2);
lean_inc(x_12);
lean_dec(x_2);
x_13 = lean_array_get_size(x_12);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_dec_lt(x_14, x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_9);
return x_17;
}
else
{
uint8_t x_18; 
x_18 = lean_nat_dec_le(x_13, x_13);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_9);
return x_20;
}
else
{
size_t x_21; size_t x_22; lean_object* x_23; lean_object* x_24; 
x_21 = 0;
x_22 = lean_usize_of_nat(x_13);
lean_dec(x_13);
x_23 = lean_box(0);
x_24 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__8(x_1, x_12, x_21, x_22, x_23, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_12);
return x_24;
}
}
}
case 4:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_2, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_2, 1);
lean_inc(x_26);
lean_dec(x_2);
lean_inc(x_1);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_27 = lean_apply_8(x_1, x_25, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_29 = lean_ctor_get(x_27, 1);
x_30 = lean_ctor_get(x_27, 0);
lean_dec(x_30);
x_31 = lean_array_get_size(x_26);
x_32 = lean_unsigned_to_nat(0u);
x_33 = lean_nat_dec_lt(x_32, x_31);
if (x_33 == 0)
{
lean_object* x_34; 
lean_dec(x_31);
lean_dec(x_26);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_34 = lean_box(0);
lean_ctor_set(x_27, 0, x_34);
return x_27;
}
else
{
uint8_t x_35; 
x_35 = lean_nat_dec_le(x_31, x_31);
if (x_35 == 0)
{
lean_object* x_36; 
lean_dec(x_31);
lean_dec(x_26);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_36 = lean_box(0);
lean_ctor_set(x_27, 0, x_36);
return x_27;
}
else
{
size_t x_37; size_t x_38; lean_object* x_39; lean_object* x_40; 
lean_free_object(x_27);
x_37 = 0;
x_38 = lean_usize_of_nat(x_31);
lean_dec(x_31);
x_39 = lean_box(0);
x_40 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__9(x_1, x_26, x_37, x_38, x_39, x_3, x_4, x_5, x_6, x_7, x_8, x_29);
lean_dec(x_26);
return x_40;
}
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_41 = lean_ctor_get(x_27, 1);
lean_inc(x_41);
lean_dec(x_27);
x_42 = lean_array_get_size(x_26);
x_43 = lean_unsigned_to_nat(0u);
x_44 = lean_nat_dec_lt(x_43, x_42);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
lean_dec(x_42);
lean_dec(x_26);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_45 = lean_box(0);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_41);
return x_46;
}
else
{
uint8_t x_47; 
x_47 = lean_nat_dec_le(x_42, x_42);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_42);
lean_dec(x_26);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_48 = lean_box(0);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_41);
return x_49;
}
else
{
size_t x_50; size_t x_51; lean_object* x_52; lean_object* x_53; 
x_50 = 0;
x_51 = lean_usize_of_nat(x_42);
lean_dec(x_42);
x_52 = lean_box(0);
x_53 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__9(x_1, x_26, x_50, x_51, x_52, x_3, x_4, x_5, x_6, x_7, x_8, x_41);
lean_dec(x_26);
return x_53;
}
}
}
}
else
{
uint8_t x_54; 
lean_dec(x_26);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_54 = !lean_is_exclusive(x_27);
if (x_54 == 0)
{
return x_27;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_27, 0);
x_56 = lean_ctor_get(x_27, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_27);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
default: 
{
lean_object* x_58; lean_object* x_59; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_58 = lean_box(0);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_9);
return x_59;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_2, 2);
lean_inc(x_10);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_11 = l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__2(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_ctor_get(x_2, 3);
lean_inc(x_13);
lean_dec(x_2);
x_14 = l_Lean_Compiler_LCNF_LetValue_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__6(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
return x_14;
}
else
{
uint8_t x_15; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_15 = !lean_is_exclusive(x_11);
if (x_15 == 0)
{
return x_11;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_11, 0);
x_17 = lean_ctor_get(x_11, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_11);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__10(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
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
x_15 = l_Lean_Compiler_LCNF_Param_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__1(x_1, x_14, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
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
uint8_t x_21; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_15);
if (x_21 == 0)
{
return x_15;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_15, 0);
x_23 = lean_ctor_get(x_15, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_15);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
else
{
lean_object* x_25; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_5);
lean_ctor_set(x_25, 1, x_12);
return x_25;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__11(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
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
x_15 = l_Lean_Compiler_LCNF_Param_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__1(x_1, x_14, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
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
uint8_t x_21; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_15);
if (x_21 == 0)
{
return x_15;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_15, 0);
x_23 = lean_ctor_get(x_15, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_15);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
else
{
lean_object* x_25; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_5);
lean_ctor_set(x_25, 1, x_12);
return x_25;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__12(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
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
x_15 = l_Lean_Compiler_LCNF_Arg_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__7(x_1, x_14, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
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
uint8_t x_21; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_15);
if (x_21 == 0)
{
return x_15;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_15, 0);
x_23 = lean_ctor_get(x_15, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_15);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
else
{
lean_object* x_25; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_5);
lean_ctor_set(x_25, 1, x_12);
return x_25;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_AltCore_forCodeM___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__13(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__14(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_eq(x_3, x_4);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_5);
x_14 = lean_array_uget(x_2, x_3);
lean_inc(x_1);
x_15 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__4), 9, 1);
lean_closure_set(x_15, 0, x_1);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_16 = l_Lean_Compiler_LCNF_AltCore_forCodeM___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__13(x_14, x_15, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
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
uint8_t x_22; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
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
lean_object* x_26; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_5);
lean_ctor_set(x_26, 1, x_12);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
lean_dec(x_2);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_12 = l_Lean_Compiler_LCNF_LetDecl_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__5(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
uint8_t x_15; 
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_15 = !lean_is_exclusive(x_12);
if (x_15 == 0)
{
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_12, 0);
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_12);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
case 1:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_19 = lean_ctor_get(x_2, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_2, 1);
lean_inc(x_20);
lean_dec(x_2);
x_21 = lean_ctor_get(x_19, 2);
lean_inc(x_21);
x_22 = lean_array_get_size(x_21);
x_23 = lean_unsigned_to_nat(0u);
x_24 = lean_nat_dec_lt(x_23, x_22);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_22);
lean_dec(x_21);
x_25 = lean_ctor_get(x_19, 3);
lean_inc(x_25);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_26 = l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__2(x_1, x_25, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = lean_ctor_get(x_19, 4);
lean_inc(x_28);
lean_dec(x_19);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_29 = l_Lean_Compiler_LCNF_Code_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__4(x_1, x_28, x_3, x_4, x_5, x_6, x_7, x_8, x_27);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
x_2 = x_20;
x_9 = x_30;
goto _start;
}
else
{
uint8_t x_32; 
lean_dec(x_20);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_29);
if (x_32 == 0)
{
return x_29;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_29, 0);
x_34 = lean_ctor_get(x_29, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_29);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
else
{
uint8_t x_36; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_36 = !lean_is_exclusive(x_26);
if (x_36 == 0)
{
return x_26;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_26, 0);
x_38 = lean_ctor_get(x_26, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_26);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
uint8_t x_40; 
x_40 = lean_nat_dec_le(x_22, x_22);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
lean_dec(x_22);
lean_dec(x_21);
x_41 = lean_ctor_get(x_19, 3);
lean_inc(x_41);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_42 = l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__2(x_1, x_41, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec(x_42);
x_44 = lean_ctor_get(x_19, 4);
lean_inc(x_44);
lean_dec(x_19);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_45 = l_Lean_Compiler_LCNF_Code_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__4(x_1, x_44, x_3, x_4, x_5, x_6, x_7, x_8, x_43);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
lean_dec(x_45);
x_2 = x_20;
x_9 = x_46;
goto _start;
}
else
{
uint8_t x_48; 
lean_dec(x_20);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_48 = !lean_is_exclusive(x_45);
if (x_48 == 0)
{
return x_45;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_45, 0);
x_50 = lean_ctor_get(x_45, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_45);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
else
{
uint8_t x_52; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_52 = !lean_is_exclusive(x_42);
if (x_52 == 0)
{
return x_42;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_42, 0);
x_54 = lean_ctor_get(x_42, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_42);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
else
{
size_t x_56; size_t x_57; lean_object* x_58; lean_object* x_59; 
x_56 = 0;
x_57 = lean_usize_of_nat(x_22);
lean_dec(x_22);
x_58 = lean_box(0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_59 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__10(x_1, x_21, x_56, x_57, x_58, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_21);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_59, 1);
lean_inc(x_60);
lean_dec(x_59);
x_61 = lean_ctor_get(x_19, 3);
lean_inc(x_61);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_62 = l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__2(x_1, x_61, x_3, x_4, x_5, x_6, x_7, x_8, x_60);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_62, 1);
lean_inc(x_63);
lean_dec(x_62);
x_64 = lean_ctor_get(x_19, 4);
lean_inc(x_64);
lean_dec(x_19);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_65 = l_Lean_Compiler_LCNF_Code_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__4(x_1, x_64, x_3, x_4, x_5, x_6, x_7, x_8, x_63);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; 
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
lean_dec(x_65);
x_2 = x_20;
x_9 = x_66;
goto _start;
}
else
{
uint8_t x_68; 
lean_dec(x_20);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_68 = !lean_is_exclusive(x_65);
if (x_68 == 0)
{
return x_65;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_65, 0);
x_70 = lean_ctor_get(x_65, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_65);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
else
{
uint8_t x_72; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_72 = !lean_is_exclusive(x_62);
if (x_72 == 0)
{
return x_62;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_62, 0);
x_74 = lean_ctor_get(x_62, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_62);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
}
else
{
uint8_t x_76; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_76 = !lean_is_exclusive(x_59);
if (x_76 == 0)
{
return x_59;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_59, 0);
x_78 = lean_ctor_get(x_59, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_59);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
}
}
case 2:
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; 
x_80 = lean_ctor_get(x_2, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_2, 1);
lean_inc(x_81);
lean_dec(x_2);
x_82 = lean_ctor_get(x_80, 2);
lean_inc(x_82);
x_83 = lean_array_get_size(x_82);
x_84 = lean_unsigned_to_nat(0u);
x_85 = lean_nat_dec_lt(x_84, x_83);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; 
lean_dec(x_83);
lean_dec(x_82);
x_86 = lean_ctor_get(x_80, 3);
lean_inc(x_86);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_87 = l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__2(x_1, x_86, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_87, 1);
lean_inc(x_88);
lean_dec(x_87);
x_89 = lean_ctor_get(x_80, 4);
lean_inc(x_89);
lean_dec(x_80);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_90 = l_Lean_Compiler_LCNF_Code_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__4(x_1, x_89, x_3, x_4, x_5, x_6, x_7, x_8, x_88);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; 
x_91 = lean_ctor_get(x_90, 1);
lean_inc(x_91);
lean_dec(x_90);
x_2 = x_81;
x_9 = x_91;
goto _start;
}
else
{
uint8_t x_93; 
lean_dec(x_81);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_93 = !lean_is_exclusive(x_90);
if (x_93 == 0)
{
return x_90;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_90, 0);
x_95 = lean_ctor_get(x_90, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_90);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
return x_96;
}
}
}
else
{
uint8_t x_97; 
lean_dec(x_81);
lean_dec(x_80);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_97 = !lean_is_exclusive(x_87);
if (x_97 == 0)
{
return x_87;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_87, 0);
x_99 = lean_ctor_get(x_87, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_87);
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
return x_100;
}
}
}
else
{
uint8_t x_101; 
x_101 = lean_nat_dec_le(x_83, x_83);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; 
lean_dec(x_83);
lean_dec(x_82);
x_102 = lean_ctor_get(x_80, 3);
lean_inc(x_102);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_103 = l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__2(x_1, x_102, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_103, 1);
lean_inc(x_104);
lean_dec(x_103);
x_105 = lean_ctor_get(x_80, 4);
lean_inc(x_105);
lean_dec(x_80);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_106 = l_Lean_Compiler_LCNF_Code_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__4(x_1, x_105, x_3, x_4, x_5, x_6, x_7, x_8, x_104);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; 
x_107 = lean_ctor_get(x_106, 1);
lean_inc(x_107);
lean_dec(x_106);
x_2 = x_81;
x_9 = x_107;
goto _start;
}
else
{
uint8_t x_109; 
lean_dec(x_81);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_109 = !lean_is_exclusive(x_106);
if (x_109 == 0)
{
return x_106;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_106, 0);
x_111 = lean_ctor_get(x_106, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_106);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
return x_112;
}
}
}
else
{
uint8_t x_113; 
lean_dec(x_81);
lean_dec(x_80);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_113 = !lean_is_exclusive(x_103);
if (x_113 == 0)
{
return x_103;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_103, 0);
x_115 = lean_ctor_get(x_103, 1);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_103);
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
return x_116;
}
}
}
else
{
size_t x_117; size_t x_118; lean_object* x_119; lean_object* x_120; 
x_117 = 0;
x_118 = lean_usize_of_nat(x_83);
lean_dec(x_83);
x_119 = lean_box(0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_120 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__11(x_1, x_82, x_117, x_118, x_119, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_82);
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_ctor_get(x_120, 1);
lean_inc(x_121);
lean_dec(x_120);
x_122 = lean_ctor_get(x_80, 3);
lean_inc(x_122);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_123 = l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__2(x_1, x_122, x_3, x_4, x_5, x_6, x_7, x_8, x_121);
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_124 = lean_ctor_get(x_123, 1);
lean_inc(x_124);
lean_dec(x_123);
x_125 = lean_ctor_get(x_80, 4);
lean_inc(x_125);
lean_dec(x_80);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_126 = l_Lean_Compiler_LCNF_Code_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__4(x_1, x_125, x_3, x_4, x_5, x_6, x_7, x_8, x_124);
if (lean_obj_tag(x_126) == 0)
{
lean_object* x_127; 
x_127 = lean_ctor_get(x_126, 1);
lean_inc(x_127);
lean_dec(x_126);
x_2 = x_81;
x_9 = x_127;
goto _start;
}
else
{
uint8_t x_129; 
lean_dec(x_81);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_129 = !lean_is_exclusive(x_126);
if (x_129 == 0)
{
return x_126;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_130 = lean_ctor_get(x_126, 0);
x_131 = lean_ctor_get(x_126, 1);
lean_inc(x_131);
lean_inc(x_130);
lean_dec(x_126);
x_132 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_132, 0, x_130);
lean_ctor_set(x_132, 1, x_131);
return x_132;
}
}
}
else
{
uint8_t x_133; 
lean_dec(x_81);
lean_dec(x_80);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_133 = !lean_is_exclusive(x_123);
if (x_133 == 0)
{
return x_123;
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_134 = lean_ctor_get(x_123, 0);
x_135 = lean_ctor_get(x_123, 1);
lean_inc(x_135);
lean_inc(x_134);
lean_dec(x_123);
x_136 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_136, 0, x_134);
lean_ctor_set(x_136, 1, x_135);
return x_136;
}
}
}
else
{
uint8_t x_137; 
lean_dec(x_81);
lean_dec(x_80);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_137 = !lean_is_exclusive(x_120);
if (x_137 == 0)
{
return x_120;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_138 = lean_ctor_get(x_120, 0);
x_139 = lean_ctor_get(x_120, 1);
lean_inc(x_139);
lean_inc(x_138);
lean_dec(x_120);
x_140 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_140, 0, x_138);
lean_ctor_set(x_140, 1, x_139);
return x_140;
}
}
}
}
}
case 3:
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_141 = lean_ctor_get(x_2, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_2, 1);
lean_inc(x_142);
lean_dec(x_2);
lean_inc(x_1);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_143 = lean_apply_8(x_1, x_141, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_143) == 0)
{
uint8_t x_144; 
x_144 = !lean_is_exclusive(x_143);
if (x_144 == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; uint8_t x_149; 
x_145 = lean_ctor_get(x_143, 1);
x_146 = lean_ctor_get(x_143, 0);
lean_dec(x_146);
x_147 = lean_array_get_size(x_142);
x_148 = lean_unsigned_to_nat(0u);
x_149 = lean_nat_dec_lt(x_148, x_147);
if (x_149 == 0)
{
lean_object* x_150; 
lean_dec(x_147);
lean_dec(x_142);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_150 = lean_box(0);
lean_ctor_set(x_143, 0, x_150);
return x_143;
}
else
{
uint8_t x_151; 
x_151 = lean_nat_dec_le(x_147, x_147);
if (x_151 == 0)
{
lean_object* x_152; 
lean_dec(x_147);
lean_dec(x_142);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_152 = lean_box(0);
lean_ctor_set(x_143, 0, x_152);
return x_143;
}
else
{
size_t x_153; size_t x_154; lean_object* x_155; lean_object* x_156; 
lean_free_object(x_143);
x_153 = 0;
x_154 = lean_usize_of_nat(x_147);
lean_dec(x_147);
x_155 = lean_box(0);
x_156 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__12(x_1, x_142, x_153, x_154, x_155, x_3, x_4, x_5, x_6, x_7, x_8, x_145);
lean_dec(x_142);
return x_156;
}
}
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; uint8_t x_160; 
x_157 = lean_ctor_get(x_143, 1);
lean_inc(x_157);
lean_dec(x_143);
x_158 = lean_array_get_size(x_142);
x_159 = lean_unsigned_to_nat(0u);
x_160 = lean_nat_dec_lt(x_159, x_158);
if (x_160 == 0)
{
lean_object* x_161; lean_object* x_162; 
lean_dec(x_158);
lean_dec(x_142);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_161 = lean_box(0);
x_162 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_162, 0, x_161);
lean_ctor_set(x_162, 1, x_157);
return x_162;
}
else
{
uint8_t x_163; 
x_163 = lean_nat_dec_le(x_158, x_158);
if (x_163 == 0)
{
lean_object* x_164; lean_object* x_165; 
lean_dec(x_158);
lean_dec(x_142);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_164 = lean_box(0);
x_165 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_165, 0, x_164);
lean_ctor_set(x_165, 1, x_157);
return x_165;
}
else
{
size_t x_166; size_t x_167; lean_object* x_168; lean_object* x_169; 
x_166 = 0;
x_167 = lean_usize_of_nat(x_158);
lean_dec(x_158);
x_168 = lean_box(0);
x_169 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__12(x_1, x_142, x_166, x_167, x_168, x_3, x_4, x_5, x_6, x_7, x_8, x_157);
lean_dec(x_142);
return x_169;
}
}
}
}
else
{
uint8_t x_170; 
lean_dec(x_142);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_170 = !lean_is_exclusive(x_143);
if (x_170 == 0)
{
return x_143;
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_171 = lean_ctor_get(x_143, 0);
x_172 = lean_ctor_get(x_143, 1);
lean_inc(x_172);
lean_inc(x_171);
lean_dec(x_143);
x_173 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_173, 0, x_171);
lean_ctor_set(x_173, 1, x_172);
return x_173;
}
}
}
case 4:
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_174 = lean_ctor_get(x_2, 0);
lean_inc(x_174);
lean_dec(x_2);
x_175 = lean_ctor_get(x_174, 1);
lean_inc(x_175);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_176 = l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__2(x_1, x_175, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_176) == 0)
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_177 = lean_ctor_get(x_176, 1);
lean_inc(x_177);
lean_dec(x_176);
x_178 = lean_ctor_get(x_174, 2);
lean_inc(x_178);
lean_inc(x_1);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_179 = lean_apply_8(x_1, x_178, x_3, x_4, x_5, x_6, x_7, x_8, x_177);
if (lean_obj_tag(x_179) == 0)
{
uint8_t x_180; 
x_180 = !lean_is_exclusive(x_179);
if (x_180 == 0)
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; uint8_t x_186; 
x_181 = lean_ctor_get(x_179, 1);
x_182 = lean_ctor_get(x_179, 0);
lean_dec(x_182);
x_183 = lean_ctor_get(x_174, 3);
lean_inc(x_183);
lean_dec(x_174);
x_184 = lean_array_get_size(x_183);
x_185 = lean_unsigned_to_nat(0u);
x_186 = lean_nat_dec_lt(x_185, x_184);
if (x_186 == 0)
{
lean_object* x_187; 
lean_dec(x_184);
lean_dec(x_183);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_187 = lean_box(0);
lean_ctor_set(x_179, 0, x_187);
return x_179;
}
else
{
uint8_t x_188; 
x_188 = lean_nat_dec_le(x_184, x_184);
if (x_188 == 0)
{
lean_object* x_189; 
lean_dec(x_184);
lean_dec(x_183);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_189 = lean_box(0);
lean_ctor_set(x_179, 0, x_189);
return x_179;
}
else
{
size_t x_190; size_t x_191; lean_object* x_192; lean_object* x_193; 
lean_free_object(x_179);
x_190 = 0;
x_191 = lean_usize_of_nat(x_184);
lean_dec(x_184);
x_192 = lean_box(0);
x_193 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__14(x_1, x_183, x_190, x_191, x_192, x_3, x_4, x_5, x_6, x_7, x_8, x_181);
lean_dec(x_183);
return x_193;
}
}
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; uint8_t x_198; 
x_194 = lean_ctor_get(x_179, 1);
lean_inc(x_194);
lean_dec(x_179);
x_195 = lean_ctor_get(x_174, 3);
lean_inc(x_195);
lean_dec(x_174);
x_196 = lean_array_get_size(x_195);
x_197 = lean_unsigned_to_nat(0u);
x_198 = lean_nat_dec_lt(x_197, x_196);
if (x_198 == 0)
{
lean_object* x_199; lean_object* x_200; 
lean_dec(x_196);
lean_dec(x_195);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_199 = lean_box(0);
x_200 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_200, 0, x_199);
lean_ctor_set(x_200, 1, x_194);
return x_200;
}
else
{
uint8_t x_201; 
x_201 = lean_nat_dec_le(x_196, x_196);
if (x_201 == 0)
{
lean_object* x_202; lean_object* x_203; 
lean_dec(x_196);
lean_dec(x_195);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_202 = lean_box(0);
x_203 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_203, 0, x_202);
lean_ctor_set(x_203, 1, x_194);
return x_203;
}
else
{
size_t x_204; size_t x_205; lean_object* x_206; lean_object* x_207; 
x_204 = 0;
x_205 = lean_usize_of_nat(x_196);
lean_dec(x_196);
x_206 = lean_box(0);
x_207 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__14(x_1, x_195, x_204, x_205, x_206, x_3, x_4, x_5, x_6, x_7, x_8, x_194);
lean_dec(x_195);
return x_207;
}
}
}
}
else
{
uint8_t x_208; 
lean_dec(x_174);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_208 = !lean_is_exclusive(x_179);
if (x_208 == 0)
{
return x_179;
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; 
x_209 = lean_ctor_get(x_179, 0);
x_210 = lean_ctor_get(x_179, 1);
lean_inc(x_210);
lean_inc(x_209);
lean_dec(x_179);
x_211 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_211, 0, x_209);
lean_ctor_set(x_211, 1, x_210);
return x_211;
}
}
}
else
{
uint8_t x_212; 
lean_dec(x_174);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_212 = !lean_is_exclusive(x_176);
if (x_212 == 0)
{
return x_176;
}
else
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; 
x_213 = lean_ctor_get(x_176, 0);
x_214 = lean_ctor_get(x_176, 1);
lean_inc(x_214);
lean_inc(x_213);
lean_dec(x_176);
x_215 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_215, 0, x_213);
lean_ctor_set(x_215, 1, x_214);
return x_215;
}
}
}
case 5:
{
lean_object* x_216; lean_object* x_217; 
x_216 = lean_ctor_get(x_2, 0);
lean_inc(x_216);
lean_dec(x_2);
x_217 = lean_apply_8(x_1, x_216, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_217;
}
default: 
{
lean_object* x_218; lean_object* x_219; 
x_218 = lean_ctor_get(x_2, 0);
lean_inc(x_218);
lean_dec(x_2);
x_219 = l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__2(x_1, x_218, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_219;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__15(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
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
x_15 = l_Lean_Compiler_LCNF_Param_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__1(x_1, x_14, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
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
uint8_t x_21; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_15);
if (x_21 == 0)
{
return x_15;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_15, 0);
x_23 = lean_ctor_get(x_15, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_15);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
else
{
lean_object* x_25; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_5);
lean_ctor_set(x_25, 1, x_12);
return x_25;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__15___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__16(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; uint8_t x_14; 
lean_inc(x_1);
x_13 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___boxed), 9, 1);
lean_closure_set(x_13, 0, x_1);
x_14 = lean_usize_dec_eq(x_3, x_4);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_5);
x_15 = lean_array_uget(x_2, x_3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_16 = l_Lean_Compiler_LCNF_Param_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__1(x_13, x_15, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
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
uint8_t x_22; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
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
lean_object* x_26; 
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_5);
lean_ctor_set(x_26, 1, x_12);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = l_Lean_Compiler_LCNF_FloatLetIn_Decision_ofAlt(x_1);
lean_inc(x_9);
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
x_13 = lean_array_get_size(x_11);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_dec_lt(x_14, x_13);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_9);
x_16 = l_Lean_Compiler_LCNF_Code_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__4(x_10, x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_16;
}
else
{
uint8_t x_17; 
x_17 = lean_nat_dec_le(x_13, x_13);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_9);
x_18 = l_Lean_Compiler_LCNF_Code_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__4(x_10, x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_18;
}
else
{
size_t x_19; size_t x_20; lean_object* x_21; lean_object* x_22; 
x_19 = 0;
x_20 = lean_usize_of_nat(x_13);
lean_dec(x_13);
x_21 = lean_box(0);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_22 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__15___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__16(x_9, x_11, x_19, x_20, x_21, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_11);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = l_Lean_Compiler_LCNF_Code_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__4(x_10, x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_23);
return x_24;
}
else
{
uint8_t x_25; 
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_25 = !lean_is_exclusive(x_22);
if (x_25 == 0)
{
return x_22;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_22, 0);
x_27 = lean_ctor_get(x_22, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_22);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
}
else
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_9);
x_29 = lean_ctor_get(x_1, 0);
lean_inc(x_29);
lean_dec(x_1);
x_30 = l_Lean_Compiler_LCNF_Code_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__4(x_10, x_29, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_30;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__8(x_1, x_2, x_13, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__9(x_1, x_2, x_13, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__10(x_1, x_2, x_13, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__11(x_1, x_2, x_13, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__12(x_1, x_2, x_13, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__14___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__14(x_1, x_2, x_13, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__15___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__15(x_1, x_2, x_13, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__15___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__16___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__15___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__16(x_1, x_2, x_13, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goCases___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
uint8_t x_20; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_20 = !lean_is_exclusive(x_14);
if (x_20 == 0)
{
return x_14;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_14, 0);
x_22 = lean_ctor_get(x_14, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_14);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
else
{
lean_object* x_24; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_4);
lean_ctor_set(x_24, 1, x_11);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goCases(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_1, 3);
x_10 = lean_array_get_size(x_9);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_nat_dec_lt(x_11, x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_8);
return x_14;
}
else
{
uint8_t x_15; 
x_15 = lean_nat_dec_le(x_10, x_10);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_8);
return x_17;
}
else
{
size_t x_18; size_t x_19; lean_object* x_20; lean_object* x_21; 
x_18 = 0;
x_19 = lean_usize_of_nat(x_10);
lean_dec(x_10);
x_20 = lean_box(0);
x_21 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goCases___spec__1(x_9, x_18, x_19, x_20, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goCases___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goCases___spec__1(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_Lean_Compiler_LCNF_CodeDecl_fvarId(x_1);
x_12 = !lean_is_exclusive(x_2);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint64_t x_16; uint64_t x_17; uint64_t x_18; uint64_t x_19; uint64_t x_20; uint64_t x_21; uint64_t x_22; size_t x_23; size_t x_24; size_t x_25; size_t x_26; size_t x_27; lean_object* x_28; uint8_t x_29; 
x_13 = lean_ctor_get(x_2, 0);
x_14 = lean_ctor_get(x_2, 1);
x_15 = lean_array_get_size(x_14);
x_16 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1724_(x_11);
x_17 = 32;
x_18 = lean_uint64_shift_right(x_16, x_17);
x_19 = lean_uint64_xor(x_16, x_18);
x_20 = 16;
x_21 = lean_uint64_shift_right(x_19, x_20);
x_22 = lean_uint64_xor(x_19, x_21);
x_23 = lean_uint64_to_usize(x_22);
x_24 = lean_usize_of_nat(x_15);
lean_dec(x_15);
x_25 = 1;
x_26 = lean_usize_sub(x_24, x_25);
x_27 = lean_usize_land(x_23, x_26);
x_28 = lean_array_uget(x_14, x_27);
x_29 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__2(x_11, x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
lean_dec(x_3);
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_nat_add(x_13, x_30);
lean_dec(x_13);
x_32 = lean_box(3);
x_33 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_33, 0, x_11);
lean_ctor_set(x_33, 1, x_32);
lean_ctor_set(x_33, 2, x_28);
x_34 = lean_array_uset(x_14, x_27, x_33);
x_35 = lean_unsigned_to_nat(4u);
x_36 = lean_nat_mul(x_31, x_35);
x_37 = lean_unsigned_to_nat(3u);
x_38 = lean_nat_div(x_36, x_37);
lean_dec(x_36);
x_39 = lean_array_get_size(x_34);
x_40 = lean_nat_dec_le(x_38, x_39);
lean_dec(x_39);
lean_dec(x_38);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__3(x_34);
lean_ctor_set(x_2, 1, x_41);
lean_ctor_set(x_2, 0, x_31);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_2);
lean_ctor_set(x_42, 1, x_10);
return x_42;
}
else
{
lean_object* x_43; 
lean_ctor_set(x_2, 1, x_34);
lean_ctor_set(x_2, 0, x_31);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_2);
lean_ctor_set(x_43, 1, x_10);
return x_43;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_44 = lean_array_uset(x_14, x_27, x_3);
x_45 = lean_box(3);
x_46 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__6(x_11, x_45, x_28);
x_47 = lean_array_uset(x_44, x_27, x_46);
lean_ctor_set(x_2, 1, x_47);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_2);
lean_ctor_set(x_48, 1, x_10);
return x_48;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; uint64_t x_52; uint64_t x_53; uint64_t x_54; uint64_t x_55; uint64_t x_56; uint64_t x_57; uint64_t x_58; size_t x_59; size_t x_60; size_t x_61; size_t x_62; size_t x_63; lean_object* x_64; uint8_t x_65; 
x_49 = lean_ctor_get(x_2, 0);
x_50 = lean_ctor_get(x_2, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_2);
x_51 = lean_array_get_size(x_50);
x_52 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1724_(x_11);
x_53 = 32;
x_54 = lean_uint64_shift_right(x_52, x_53);
x_55 = lean_uint64_xor(x_52, x_54);
x_56 = 16;
x_57 = lean_uint64_shift_right(x_55, x_56);
x_58 = lean_uint64_xor(x_55, x_57);
x_59 = lean_uint64_to_usize(x_58);
x_60 = lean_usize_of_nat(x_51);
lean_dec(x_51);
x_61 = 1;
x_62 = lean_usize_sub(x_60, x_61);
x_63 = lean_usize_land(x_59, x_62);
x_64 = lean_array_uget(x_50, x_63);
x_65 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__2(x_11, x_64);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; 
lean_dec(x_3);
x_66 = lean_unsigned_to_nat(1u);
x_67 = lean_nat_add(x_49, x_66);
lean_dec(x_49);
x_68 = lean_box(3);
x_69 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_69, 0, x_11);
lean_ctor_set(x_69, 1, x_68);
lean_ctor_set(x_69, 2, x_64);
x_70 = lean_array_uset(x_50, x_63, x_69);
x_71 = lean_unsigned_to_nat(4u);
x_72 = lean_nat_mul(x_67, x_71);
x_73 = lean_unsigned_to_nat(3u);
x_74 = lean_nat_div(x_72, x_73);
lean_dec(x_72);
x_75 = lean_array_get_size(x_70);
x_76 = lean_nat_dec_le(x_74, x_75);
lean_dec(x_75);
lean_dec(x_74);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__3(x_70);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_67);
lean_ctor_set(x_78, 1, x_77);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_10);
return x_79;
}
else
{
lean_object* x_80; lean_object* x_81; 
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_67);
lean_ctor_set(x_80, 1, x_70);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_10);
return x_81;
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_82 = lean_array_uset(x_50, x_63, x_3);
x_83 = lean_box(3);
x_84 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__6(x_11, x_83, x_64);
x_85 = lean_array_uset(x_82, x_63, x_84);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_49);
lean_ctor_set(x_86, 1, x_85);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_10);
return x_87;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_10; 
lean_dec(x_1);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_2);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
else
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_3, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_12);
lean_dec(x_3);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_inc(x_13);
x_14 = l_Lean_Compiler_LCNF_FloatLetIn_ignore_x3f(x_13, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_unbox(x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_13);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_box(0);
lean_inc(x_1);
x_19 = l_List_foldlM___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___spec__1___lambda__1(x_11, x_2, x_1, x_18, x_4, x_5, x_6, x_7, x_8, x_17);
lean_dec(x_11);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_2 = x_20;
x_3 = x_12;
x_9 = x_21;
goto _start;
}
else
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
lean_dec(x_11);
x_23 = lean_ctor_get(x_14, 1);
lean_inc(x_23);
lean_dec(x_14);
x_24 = lean_ctor_get(x_13, 0);
lean_inc(x_24);
lean_dec(x_13);
x_25 = !lean_is_exclusive(x_2);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint64_t x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; uint64_t x_33; uint64_t x_34; uint64_t x_35; size_t x_36; size_t x_37; size_t x_38; size_t x_39; size_t x_40; lean_object* x_41; uint8_t x_42; 
x_26 = lean_ctor_get(x_2, 0);
x_27 = lean_ctor_get(x_2, 1);
x_28 = lean_array_get_size(x_27);
x_29 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1724_(x_24);
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
x_41 = lean_array_uget(x_27, x_40);
x_42 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__2(x_24, x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_43 = lean_unsigned_to_nat(1u);
x_44 = lean_nat_add(x_26, x_43);
lean_dec(x_26);
x_45 = lean_box(2);
x_46 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_46, 0, x_24);
lean_ctor_set(x_46, 1, x_45);
lean_ctor_set(x_46, 2, x_41);
x_47 = lean_array_uset(x_27, x_40, x_46);
x_48 = lean_unsigned_to_nat(4u);
x_49 = lean_nat_mul(x_44, x_48);
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
x_54 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__3(x_47);
lean_ctor_set(x_2, 1, x_54);
lean_ctor_set(x_2, 0, x_44);
x_3 = x_12;
x_9 = x_23;
goto _start;
}
else
{
lean_ctor_set(x_2, 1, x_47);
lean_ctor_set(x_2, 0, x_44);
x_3 = x_12;
x_9 = x_23;
goto _start;
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_inc(x_1);
x_57 = lean_array_uset(x_27, x_40, x_1);
x_58 = lean_box(2);
x_59 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__6(x_24, x_58, x_41);
x_60 = lean_array_uset(x_57, x_40, x_59);
lean_ctor_set(x_2, 1, x_60);
x_3 = x_12;
x_9 = x_23;
goto _start;
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; uint64_t x_65; uint64_t x_66; uint64_t x_67; uint64_t x_68; uint64_t x_69; uint64_t x_70; uint64_t x_71; size_t x_72; size_t x_73; size_t x_74; size_t x_75; size_t x_76; lean_object* x_77; uint8_t x_78; 
x_62 = lean_ctor_get(x_2, 0);
x_63 = lean_ctor_get(x_2, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_2);
x_64 = lean_array_get_size(x_63);
x_65 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1724_(x_24);
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
x_77 = lean_array_uget(x_63, x_76);
x_78 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__2(x_24, x_77);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_79 = lean_unsigned_to_nat(1u);
x_80 = lean_nat_add(x_62, x_79);
lean_dec(x_62);
x_81 = lean_box(2);
x_82 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_82, 0, x_24);
lean_ctor_set(x_82, 1, x_81);
lean_ctor_set(x_82, 2, x_77);
x_83 = lean_array_uset(x_63, x_76, x_82);
x_84 = lean_unsigned_to_nat(4u);
x_85 = lean_nat_mul(x_80, x_84);
x_86 = lean_unsigned_to_nat(3u);
x_87 = lean_nat_div(x_85, x_86);
lean_dec(x_85);
x_88 = lean_array_get_size(x_83);
x_89 = lean_nat_dec_le(x_87, x_88);
lean_dec(x_88);
lean_dec(x_87);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; 
x_90 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__3(x_83);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_80);
lean_ctor_set(x_91, 1, x_90);
x_2 = x_91;
x_3 = x_12;
x_9 = x_23;
goto _start;
}
else
{
lean_object* x_93; 
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_80);
lean_ctor_set(x_93, 1, x_83);
x_2 = x_93;
x_3 = x_12;
x_9 = x_23;
goto _start;
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
lean_inc(x_1);
x_95 = lean_array_uset(x_63, x_76, x_1);
x_96 = lean_box(2);
x_97 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__6(x_24, x_96, x_77);
x_98 = lean_array_uset(x_95, x_76, x_97);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_62);
lean_ctor_set(x_99, 1, x_98);
x_2 = x_99;
x_3 = x_12;
x_9 = x_23;
goto _start;
}
}
}
}
else
{
uint8_t x_101; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_2);
lean_dec(x_1);
x_101 = !lean_is_exclusive(x_14);
if (x_101 == 0)
{
return x_14;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_14, 0);
x_103 = lean_ctor_get(x_14, 1);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_14);
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_103);
return x_104;
}
}
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_105 = lean_ctor_get(x_3, 1);
lean_inc(x_105);
lean_dec(x_3);
x_106 = lean_box(0);
lean_inc(x_1);
x_107 = l_List_foldlM___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___spec__1___lambda__1(x_11, x_2, x_1, x_106, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_11);
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_107, 1);
lean_inc(x_109);
lean_dec(x_107);
x_2 = x_108;
x_3 = x_105;
x_9 = x_109;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_st_mk_ref(x_2, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_11);
x_13 = l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goCases(x_1, x_11, x_4, x_5, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_st_ref_get(x_11, x_14);
lean_dec(x_11);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
return x_15;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_15);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
else
{
uint8_t x_20; 
lean_dec(x_11);
x_20 = !lean_is_exclusive(x_13);
if (x_20 == 0)
{
return x_13;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_13, 0);
x_22 = lean_ctor_get(x_13, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_13);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_List_lengthTRAux___rarg(x_2, x_8);
x_10 = lean_unsigned_to_nat(4u);
x_11 = lean_nat_mul(x_9, x_10);
lean_dec(x_9);
x_12 = lean_unsigned_to_nat(3u);
x_13 = lean_nat_div(x_11, x_12);
lean_dec(x_11);
x_14 = lean_unsigned_to_nat(1u);
x_15 = l_Nat_nextPowerOfTwo_go(x_13, x_14, lean_box(0));
lean_dec(x_13);
x_16 = lean_box(0);
x_17 = lean_mk_array(x_15, x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_8);
lean_ctor_set(x_18, 1, x_17);
lean_inc(x_2);
x_19 = l_List_reverse___rarg(x_2);
x_20 = l_List_foldlM___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___spec__1(x_16, x_18, x_19, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint64_t x_27; uint64_t x_28; uint64_t x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; uint64_t x_33; size_t x_34; size_t x_35; size_t x_36; size_t x_37; size_t x_38; lean_object* x_39; uint8_t x_40; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_ctor_get(x_1, 2);
lean_inc(x_23);
x_24 = lean_ctor_get(x_21, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_21, 1);
lean_inc(x_25);
x_26 = lean_array_get_size(x_25);
x_27 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1724_(x_23);
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
x_39 = lean_array_uget(x_25, x_38);
x_40 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__2(x_23, x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
lean_dec(x_39);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
x_41 = lean_box(0);
x_42 = l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___lambda__1(x_1, x_21, x_41, x_2, x_3, x_4, x_5, x_6, x_22);
lean_dec(x_1);
return x_42;
}
else
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_21);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_44 = lean_ctor_get(x_21, 1);
lean_dec(x_44);
x_45 = lean_ctor_get(x_21, 0);
lean_dec(x_45);
x_46 = lean_array_uset(x_25, x_38, x_16);
x_47 = lean_box(2);
x_48 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__6(x_23, x_47, x_39);
x_49 = lean_array_uset(x_46, x_38, x_48);
lean_ctor_set(x_21, 1, x_49);
x_50 = lean_box(0);
x_51 = l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___lambda__1(x_1, x_21, x_50, x_2, x_3, x_4, x_5, x_6, x_22);
lean_dec(x_1);
return x_51;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_21);
x_52 = lean_array_uset(x_25, x_38, x_16);
x_53 = lean_box(2);
x_54 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__6(x_23, x_53, x_39);
x_55 = lean_array_uset(x_52, x_38, x_54);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_24);
lean_ctor_set(x_56, 1, x_55);
x_57 = lean_box(0);
x_58 = l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___lambda__1(x_1, x_56, x_57, x_2, x_3, x_4, x_5, x_6, x_22);
lean_dec(x_1);
return x_58;
}
}
}
else
{
uint8_t x_59; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_59 = !lean_is_exclusive(x_20);
if (x_59 == 0)
{
return x_20;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_20, 0);
x_61 = lean_ctor_get(x_20, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_20);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_List_foldlM___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___spec__1___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_List_foldlM___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_3);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_beqDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_62_(x_4, x_1);
if (x_6 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
uint8_t x_8; 
x_8 = 1;
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__4(lean_object* x_1, lean_object* x_2) {
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
x_7 = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_hashDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_15_(x_4);
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
x_26 = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_hashDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_15_(x_22);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__4(x_3, x_6);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(2u);
x_4 = lean_nat_mul(x_2, x_3);
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = lean_mk_array(x_4, x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Std_DHashMap_Internal_Raw_u2080_expand_go___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__3(x_7, x_1, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(0);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_3, 1);
x_8 = lean_ctor_get(x_3, 2);
x_9 = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_beqDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_62_(x_6, x_1);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__5(x_1, x_2, x_8);
lean_ctor_set(x_3, 2, x_10);
return x_3;
}
else
{
lean_dec(x_7);
lean_dec(x_6);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_3, 1);
x_13 = lean_ctor_get(x_3, 2);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_3);
x_14 = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_beqDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_62_(x_11, x_1);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__5(x_1, x_2, x_13);
x_16 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_16, 0, x_11);
lean_ctor_set(x_16, 1, x_12);
lean_ctor_set(x_16, 2, x_15);
return x_16;
}
else
{
lean_object* x_17; 
lean_dec(x_12);
lean_dec(x_11);
x_17 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_2);
lean_ctor_set(x_17, 2, x_13);
return x_17;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__6(lean_object* x_1, lean_object* x_2, uint64_t x_3, uint64_t x_4, size_t x_5, lean_object* x_6, size_t x_7, size_t x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_eq(x_7, x_8);
if (x_10 == 0)
{
size_t x_11; size_t x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = 1;
x_12 = lean_usize_sub(x_7, x_11);
x_13 = lean_array_uget(x_6, x_12);
x_14 = l_Lean_Compiler_LCNF_FloatLetIn_Decision_ofAlt(x_13);
lean_dec(x_13);
x_15 = !lean_is_exclusive(x_9);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint64_t x_19; uint64_t x_20; uint64_t x_21; uint64_t x_22; uint64_t x_23; size_t x_24; size_t x_25; size_t x_26; size_t x_27; lean_object* x_28; uint8_t x_29; 
x_16 = lean_ctor_get(x_9, 0);
x_17 = lean_ctor_get(x_9, 1);
x_18 = lean_array_get_size(x_17);
x_19 = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_hashDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_15_(x_14);
x_20 = lean_uint64_shift_right(x_19, x_3);
x_21 = lean_uint64_xor(x_19, x_20);
x_22 = lean_uint64_shift_right(x_21, x_4);
x_23 = lean_uint64_xor(x_21, x_22);
x_24 = lean_uint64_to_usize(x_23);
x_25 = lean_usize_of_nat(x_18);
lean_dec(x_18);
x_26 = lean_usize_sub(x_25, x_5);
x_27 = lean_usize_land(x_24, x_26);
x_28 = lean_array_uget(x_17, x_27);
x_29 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__1(x_14, x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_nat_add(x_16, x_30);
lean_dec(x_16);
lean_inc(x_2);
x_32 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_32, 0, x_14);
lean_ctor_set(x_32, 1, x_2);
lean_ctor_set(x_32, 2, x_28);
x_33 = lean_array_uset(x_17, x_27, x_32);
x_34 = lean_unsigned_to_nat(4u);
x_35 = lean_nat_mul(x_31, x_34);
x_36 = lean_unsigned_to_nat(3u);
x_37 = lean_nat_div(x_35, x_36);
lean_dec(x_35);
x_38 = lean_array_get_size(x_33);
x_39 = lean_nat_dec_le(x_37, x_38);
lean_dec(x_38);
lean_dec(x_37);
if (x_39 == 0)
{
lean_object* x_40; 
x_40 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__2(x_33);
lean_ctor_set(x_9, 1, x_40);
lean_ctor_set(x_9, 0, x_31);
x_7 = x_12;
goto _start;
}
else
{
lean_ctor_set(x_9, 1, x_33);
lean_ctor_set(x_9, 0, x_31);
x_7 = x_12;
goto _start;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_inc(x_1);
x_43 = lean_array_uset(x_17, x_27, x_1);
lean_inc(x_2);
x_44 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__5(x_14, x_2, x_28);
x_45 = lean_array_uset(x_43, x_27, x_44);
lean_ctor_set(x_9, 1, x_45);
x_7 = x_12;
goto _start;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; uint64_t x_50; uint64_t x_51; uint64_t x_52; uint64_t x_53; uint64_t x_54; size_t x_55; size_t x_56; size_t x_57; size_t x_58; lean_object* x_59; uint8_t x_60; 
x_47 = lean_ctor_get(x_9, 0);
x_48 = lean_ctor_get(x_9, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_9);
x_49 = lean_array_get_size(x_48);
x_50 = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_hashDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_15_(x_14);
x_51 = lean_uint64_shift_right(x_50, x_3);
x_52 = lean_uint64_xor(x_50, x_51);
x_53 = lean_uint64_shift_right(x_52, x_4);
x_54 = lean_uint64_xor(x_52, x_53);
x_55 = lean_uint64_to_usize(x_54);
x_56 = lean_usize_of_nat(x_49);
lean_dec(x_49);
x_57 = lean_usize_sub(x_56, x_5);
x_58 = lean_usize_land(x_55, x_57);
x_59 = lean_array_uget(x_48, x_58);
x_60 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__1(x_14, x_59);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_61 = lean_unsigned_to_nat(1u);
x_62 = lean_nat_add(x_47, x_61);
lean_dec(x_47);
lean_inc(x_2);
x_63 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_63, 0, x_14);
lean_ctor_set(x_63, 1, x_2);
lean_ctor_set(x_63, 2, x_59);
x_64 = lean_array_uset(x_48, x_58, x_63);
x_65 = lean_unsigned_to_nat(4u);
x_66 = lean_nat_mul(x_62, x_65);
x_67 = lean_unsigned_to_nat(3u);
x_68 = lean_nat_div(x_66, x_67);
lean_dec(x_66);
x_69 = lean_array_get_size(x_64);
x_70 = lean_nat_dec_le(x_68, x_69);
lean_dec(x_69);
lean_dec(x_68);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; 
x_71 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__2(x_64);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_62);
lean_ctor_set(x_72, 1, x_71);
x_7 = x_12;
x_9 = x_72;
goto _start;
}
else
{
lean_object* x_74; 
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_62);
lean_ctor_set(x_74, 1, x_64);
x_7 = x_12;
x_9 = x_74;
goto _start;
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
lean_inc(x_1);
x_76 = lean_array_uset(x_48, x_58, x_1);
lean_inc(x_2);
x_77 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__5(x_14, x_2, x_59);
x_78 = lean_array_uset(x_76, x_58, x_77);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_47);
lean_ctor_set(x_79, 1, x_78);
x_7 = x_12;
x_9 = x_79;
goto _start;
}
}
}
else
{
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__7(lean_object* x_1, lean_object* x_2, uint64_t x_3, uint64_t x_4, size_t x_5, lean_object* x_6, size_t x_7, size_t x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_eq(x_7, x_8);
if (x_10 == 0)
{
size_t x_11; size_t x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = 1;
x_12 = lean_usize_sub(x_7, x_11);
x_13 = lean_array_uget(x_6, x_12);
x_14 = l_Lean_Compiler_LCNF_FloatLetIn_Decision_ofAlt(x_13);
lean_dec(x_13);
x_15 = !lean_is_exclusive(x_9);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint64_t x_19; uint64_t x_20; uint64_t x_21; uint64_t x_22; uint64_t x_23; size_t x_24; size_t x_25; size_t x_26; size_t x_27; lean_object* x_28; uint8_t x_29; 
x_16 = lean_ctor_get(x_9, 0);
x_17 = lean_ctor_get(x_9, 1);
x_18 = lean_array_get_size(x_17);
x_19 = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_hashDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_15_(x_14);
x_20 = lean_uint64_shift_right(x_19, x_3);
x_21 = lean_uint64_xor(x_19, x_20);
x_22 = lean_uint64_shift_right(x_21, x_4);
x_23 = lean_uint64_xor(x_21, x_22);
x_24 = lean_uint64_to_usize(x_23);
x_25 = lean_usize_of_nat(x_18);
lean_dec(x_18);
x_26 = lean_usize_sub(x_25, x_5);
x_27 = lean_usize_land(x_24, x_26);
x_28 = lean_array_uget(x_17, x_27);
x_29 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__1(x_14, x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_nat_add(x_16, x_30);
lean_dec(x_16);
lean_inc(x_2);
x_32 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_32, 0, x_14);
lean_ctor_set(x_32, 1, x_2);
lean_ctor_set(x_32, 2, x_28);
x_33 = lean_array_uset(x_17, x_27, x_32);
x_34 = lean_unsigned_to_nat(4u);
x_35 = lean_nat_mul(x_31, x_34);
x_36 = lean_unsigned_to_nat(3u);
x_37 = lean_nat_div(x_35, x_36);
lean_dec(x_35);
x_38 = lean_array_get_size(x_33);
x_39 = lean_nat_dec_le(x_37, x_38);
lean_dec(x_38);
lean_dec(x_37);
if (x_39 == 0)
{
lean_object* x_40; 
x_40 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__2(x_33);
lean_ctor_set(x_9, 1, x_40);
lean_ctor_set(x_9, 0, x_31);
x_7 = x_12;
goto _start;
}
else
{
lean_ctor_set(x_9, 1, x_33);
lean_ctor_set(x_9, 0, x_31);
x_7 = x_12;
goto _start;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_inc(x_1);
x_43 = lean_array_uset(x_17, x_27, x_1);
lean_inc(x_2);
x_44 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__5(x_14, x_2, x_28);
x_45 = lean_array_uset(x_43, x_27, x_44);
lean_ctor_set(x_9, 1, x_45);
x_7 = x_12;
goto _start;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; uint64_t x_50; uint64_t x_51; uint64_t x_52; uint64_t x_53; uint64_t x_54; size_t x_55; size_t x_56; size_t x_57; size_t x_58; lean_object* x_59; uint8_t x_60; 
x_47 = lean_ctor_get(x_9, 0);
x_48 = lean_ctor_get(x_9, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_9);
x_49 = lean_array_get_size(x_48);
x_50 = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_hashDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_15_(x_14);
x_51 = lean_uint64_shift_right(x_50, x_3);
x_52 = lean_uint64_xor(x_50, x_51);
x_53 = lean_uint64_shift_right(x_52, x_4);
x_54 = lean_uint64_xor(x_52, x_53);
x_55 = lean_uint64_to_usize(x_54);
x_56 = lean_usize_of_nat(x_49);
lean_dec(x_49);
x_57 = lean_usize_sub(x_56, x_5);
x_58 = lean_usize_land(x_55, x_57);
x_59 = lean_array_uget(x_48, x_58);
x_60 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__1(x_14, x_59);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_61 = lean_unsigned_to_nat(1u);
x_62 = lean_nat_add(x_47, x_61);
lean_dec(x_47);
lean_inc(x_2);
x_63 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_63, 0, x_14);
lean_ctor_set(x_63, 1, x_2);
lean_ctor_set(x_63, 2, x_59);
x_64 = lean_array_uset(x_48, x_58, x_63);
x_65 = lean_unsigned_to_nat(4u);
x_66 = lean_nat_mul(x_62, x_65);
x_67 = lean_unsigned_to_nat(3u);
x_68 = lean_nat_div(x_66, x_67);
lean_dec(x_66);
x_69 = lean_array_get_size(x_64);
x_70 = lean_nat_dec_le(x_68, x_69);
lean_dec(x_69);
lean_dec(x_68);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; 
x_71 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__2(x_64);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_62);
lean_ctor_set(x_72, 1, x_71);
x_7 = x_12;
x_9 = x_72;
goto _start;
}
else
{
lean_object* x_74; 
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_62);
lean_ctor_set(x_74, 1, x_64);
x_7 = x_12;
x_9 = x_74;
goto _start;
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
lean_inc(x_1);
x_76 = lean_array_uset(x_48, x_58, x_1);
lean_inc(x_2);
x_77 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__5(x_14, x_2, x_59);
x_78 = lean_array_uset(x_76, x_58, x_77);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_47);
lean_ctor_set(x_79, 1, x_78);
x_7 = x_12;
x_9 = x_79;
goto _start;
}
}
}
else
{
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__8(lean_object* x_1, lean_object* x_2, uint64_t x_3, uint64_t x_4, size_t x_5, lean_object* x_6, size_t x_7, size_t x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_eq(x_7, x_8);
if (x_10 == 0)
{
size_t x_11; size_t x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = 1;
x_12 = lean_usize_sub(x_7, x_11);
x_13 = lean_array_uget(x_6, x_12);
x_14 = l_Lean_Compiler_LCNF_FloatLetIn_Decision_ofAlt(x_13);
lean_dec(x_13);
x_15 = !lean_is_exclusive(x_9);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint64_t x_19; uint64_t x_20; uint64_t x_21; uint64_t x_22; uint64_t x_23; size_t x_24; size_t x_25; size_t x_26; size_t x_27; lean_object* x_28; uint8_t x_29; 
x_16 = lean_ctor_get(x_9, 0);
x_17 = lean_ctor_get(x_9, 1);
x_18 = lean_array_get_size(x_17);
x_19 = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_hashDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_15_(x_14);
x_20 = lean_uint64_shift_right(x_19, x_3);
x_21 = lean_uint64_xor(x_19, x_20);
x_22 = lean_uint64_shift_right(x_21, x_4);
x_23 = lean_uint64_xor(x_21, x_22);
x_24 = lean_uint64_to_usize(x_23);
x_25 = lean_usize_of_nat(x_18);
lean_dec(x_18);
x_26 = lean_usize_sub(x_25, x_5);
x_27 = lean_usize_land(x_24, x_26);
x_28 = lean_array_uget(x_17, x_27);
x_29 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__1(x_14, x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_nat_add(x_16, x_30);
lean_dec(x_16);
lean_inc(x_2);
x_32 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_32, 0, x_14);
lean_ctor_set(x_32, 1, x_2);
lean_ctor_set(x_32, 2, x_28);
x_33 = lean_array_uset(x_17, x_27, x_32);
x_34 = lean_unsigned_to_nat(4u);
x_35 = lean_nat_mul(x_31, x_34);
x_36 = lean_unsigned_to_nat(3u);
x_37 = lean_nat_div(x_35, x_36);
lean_dec(x_35);
x_38 = lean_array_get_size(x_33);
x_39 = lean_nat_dec_le(x_37, x_38);
lean_dec(x_38);
lean_dec(x_37);
if (x_39 == 0)
{
lean_object* x_40; 
x_40 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__2(x_33);
lean_ctor_set(x_9, 1, x_40);
lean_ctor_set(x_9, 0, x_31);
x_7 = x_12;
goto _start;
}
else
{
lean_ctor_set(x_9, 1, x_33);
lean_ctor_set(x_9, 0, x_31);
x_7 = x_12;
goto _start;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_inc(x_1);
x_43 = lean_array_uset(x_17, x_27, x_1);
lean_inc(x_2);
x_44 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__5(x_14, x_2, x_28);
x_45 = lean_array_uset(x_43, x_27, x_44);
lean_ctor_set(x_9, 1, x_45);
x_7 = x_12;
goto _start;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; uint64_t x_50; uint64_t x_51; uint64_t x_52; uint64_t x_53; uint64_t x_54; size_t x_55; size_t x_56; size_t x_57; size_t x_58; lean_object* x_59; uint8_t x_60; 
x_47 = lean_ctor_get(x_9, 0);
x_48 = lean_ctor_get(x_9, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_9);
x_49 = lean_array_get_size(x_48);
x_50 = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_hashDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_15_(x_14);
x_51 = lean_uint64_shift_right(x_50, x_3);
x_52 = lean_uint64_xor(x_50, x_51);
x_53 = lean_uint64_shift_right(x_52, x_4);
x_54 = lean_uint64_xor(x_52, x_53);
x_55 = lean_uint64_to_usize(x_54);
x_56 = lean_usize_of_nat(x_49);
lean_dec(x_49);
x_57 = lean_usize_sub(x_56, x_5);
x_58 = lean_usize_land(x_55, x_57);
x_59 = lean_array_uget(x_48, x_58);
x_60 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__1(x_14, x_59);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_61 = lean_unsigned_to_nat(1u);
x_62 = lean_nat_add(x_47, x_61);
lean_dec(x_47);
lean_inc(x_2);
x_63 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_63, 0, x_14);
lean_ctor_set(x_63, 1, x_2);
lean_ctor_set(x_63, 2, x_59);
x_64 = lean_array_uset(x_48, x_58, x_63);
x_65 = lean_unsigned_to_nat(4u);
x_66 = lean_nat_mul(x_62, x_65);
x_67 = lean_unsigned_to_nat(3u);
x_68 = lean_nat_div(x_66, x_67);
lean_dec(x_66);
x_69 = lean_array_get_size(x_64);
x_70 = lean_nat_dec_le(x_68, x_69);
lean_dec(x_69);
lean_dec(x_68);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; 
x_71 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__2(x_64);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_62);
lean_ctor_set(x_72, 1, x_71);
x_7 = x_12;
x_9 = x_72;
goto _start;
}
else
{
lean_object* x_74; 
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_62);
lean_ctor_set(x_74, 1, x_64);
x_7 = x_12;
x_9 = x_74;
goto _start;
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
lean_inc(x_1);
x_76 = lean_array_uset(x_48, x_58, x_1);
lean_inc(x_2);
x_77 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__5(x_14, x_2, x_59);
x_78 = lean_array_uset(x_76, x_58, x_77);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_47);
lean_ctor_set(x_79, 1, x_78);
x_7 = x_12;
x_9 = x_79;
goto _start;
}
}
}
else
{
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__9(lean_object* x_1, lean_object* x_2, uint64_t x_3, uint64_t x_4, size_t x_5, lean_object* x_6, size_t x_7, size_t x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_eq(x_7, x_8);
if (x_10 == 0)
{
size_t x_11; size_t x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = 1;
x_12 = lean_usize_sub(x_7, x_11);
x_13 = lean_array_uget(x_6, x_12);
x_14 = l_Lean_Compiler_LCNF_FloatLetIn_Decision_ofAlt(x_13);
lean_dec(x_13);
x_15 = !lean_is_exclusive(x_9);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint64_t x_19; uint64_t x_20; uint64_t x_21; uint64_t x_22; uint64_t x_23; size_t x_24; size_t x_25; size_t x_26; size_t x_27; lean_object* x_28; uint8_t x_29; 
x_16 = lean_ctor_get(x_9, 0);
x_17 = lean_ctor_get(x_9, 1);
x_18 = lean_array_get_size(x_17);
x_19 = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_hashDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_15_(x_14);
x_20 = lean_uint64_shift_right(x_19, x_3);
x_21 = lean_uint64_xor(x_19, x_20);
x_22 = lean_uint64_shift_right(x_21, x_4);
x_23 = lean_uint64_xor(x_21, x_22);
x_24 = lean_uint64_to_usize(x_23);
x_25 = lean_usize_of_nat(x_18);
lean_dec(x_18);
x_26 = lean_usize_sub(x_25, x_5);
x_27 = lean_usize_land(x_24, x_26);
x_28 = lean_array_uget(x_17, x_27);
x_29 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__1(x_14, x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_nat_add(x_16, x_30);
lean_dec(x_16);
lean_inc(x_2);
x_32 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_32, 0, x_14);
lean_ctor_set(x_32, 1, x_2);
lean_ctor_set(x_32, 2, x_28);
x_33 = lean_array_uset(x_17, x_27, x_32);
x_34 = lean_unsigned_to_nat(4u);
x_35 = lean_nat_mul(x_31, x_34);
x_36 = lean_unsigned_to_nat(3u);
x_37 = lean_nat_div(x_35, x_36);
lean_dec(x_35);
x_38 = lean_array_get_size(x_33);
x_39 = lean_nat_dec_le(x_37, x_38);
lean_dec(x_38);
lean_dec(x_37);
if (x_39 == 0)
{
lean_object* x_40; 
x_40 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__2(x_33);
lean_ctor_set(x_9, 1, x_40);
lean_ctor_set(x_9, 0, x_31);
x_7 = x_12;
goto _start;
}
else
{
lean_ctor_set(x_9, 1, x_33);
lean_ctor_set(x_9, 0, x_31);
x_7 = x_12;
goto _start;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_inc(x_1);
x_43 = lean_array_uset(x_17, x_27, x_1);
lean_inc(x_2);
x_44 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__5(x_14, x_2, x_28);
x_45 = lean_array_uset(x_43, x_27, x_44);
lean_ctor_set(x_9, 1, x_45);
x_7 = x_12;
goto _start;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; uint64_t x_50; uint64_t x_51; uint64_t x_52; uint64_t x_53; uint64_t x_54; size_t x_55; size_t x_56; size_t x_57; size_t x_58; lean_object* x_59; uint8_t x_60; 
x_47 = lean_ctor_get(x_9, 0);
x_48 = lean_ctor_get(x_9, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_9);
x_49 = lean_array_get_size(x_48);
x_50 = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_hashDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_15_(x_14);
x_51 = lean_uint64_shift_right(x_50, x_3);
x_52 = lean_uint64_xor(x_50, x_51);
x_53 = lean_uint64_shift_right(x_52, x_4);
x_54 = lean_uint64_xor(x_52, x_53);
x_55 = lean_uint64_to_usize(x_54);
x_56 = lean_usize_of_nat(x_49);
lean_dec(x_49);
x_57 = lean_usize_sub(x_56, x_5);
x_58 = lean_usize_land(x_55, x_57);
x_59 = lean_array_uget(x_48, x_58);
x_60 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__1(x_14, x_59);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_61 = lean_unsigned_to_nat(1u);
x_62 = lean_nat_add(x_47, x_61);
lean_dec(x_47);
lean_inc(x_2);
x_63 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_63, 0, x_14);
lean_ctor_set(x_63, 1, x_2);
lean_ctor_set(x_63, 2, x_59);
x_64 = lean_array_uset(x_48, x_58, x_63);
x_65 = lean_unsigned_to_nat(4u);
x_66 = lean_nat_mul(x_62, x_65);
x_67 = lean_unsigned_to_nat(3u);
x_68 = lean_nat_div(x_66, x_67);
lean_dec(x_66);
x_69 = lean_array_get_size(x_64);
x_70 = lean_nat_dec_le(x_68, x_69);
lean_dec(x_69);
lean_dec(x_68);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; 
x_71 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__2(x_64);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_62);
lean_ctor_set(x_72, 1, x_71);
x_7 = x_12;
x_9 = x_72;
goto _start;
}
else
{
lean_object* x_74; 
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_62);
lean_ctor_set(x_74, 1, x_64);
x_7 = x_12;
x_9 = x_74;
goto _start;
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
lean_inc(x_1);
x_76 = lean_array_uset(x_48, x_58, x_1);
lean_inc(x_2);
x_77 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__5(x_14, x_2, x_59);
x_78 = lean_array_uset(x_76, x_58, x_77);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_47);
lean_ctor_set(x_79, 1, x_78);
x_7 = x_12;
x_9 = x_79;
goto _start;
}
}
}
else
{
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__10(lean_object* x_1, lean_object* x_2, uint64_t x_3, uint64_t x_4, size_t x_5, lean_object* x_6, size_t x_7, size_t x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_eq(x_7, x_8);
if (x_10 == 0)
{
size_t x_11; size_t x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = 1;
x_12 = lean_usize_sub(x_7, x_11);
x_13 = lean_array_uget(x_6, x_12);
x_14 = l_Lean_Compiler_LCNF_FloatLetIn_Decision_ofAlt(x_13);
lean_dec(x_13);
x_15 = !lean_is_exclusive(x_9);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint64_t x_19; uint64_t x_20; uint64_t x_21; uint64_t x_22; uint64_t x_23; size_t x_24; size_t x_25; size_t x_26; size_t x_27; lean_object* x_28; uint8_t x_29; 
x_16 = lean_ctor_get(x_9, 0);
x_17 = lean_ctor_get(x_9, 1);
x_18 = lean_array_get_size(x_17);
x_19 = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_hashDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_15_(x_14);
x_20 = lean_uint64_shift_right(x_19, x_3);
x_21 = lean_uint64_xor(x_19, x_20);
x_22 = lean_uint64_shift_right(x_21, x_4);
x_23 = lean_uint64_xor(x_21, x_22);
x_24 = lean_uint64_to_usize(x_23);
x_25 = lean_usize_of_nat(x_18);
lean_dec(x_18);
x_26 = lean_usize_sub(x_25, x_5);
x_27 = lean_usize_land(x_24, x_26);
x_28 = lean_array_uget(x_17, x_27);
x_29 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__1(x_14, x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_nat_add(x_16, x_30);
lean_dec(x_16);
lean_inc(x_2);
x_32 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_32, 0, x_14);
lean_ctor_set(x_32, 1, x_2);
lean_ctor_set(x_32, 2, x_28);
x_33 = lean_array_uset(x_17, x_27, x_32);
x_34 = lean_unsigned_to_nat(4u);
x_35 = lean_nat_mul(x_31, x_34);
x_36 = lean_unsigned_to_nat(3u);
x_37 = lean_nat_div(x_35, x_36);
lean_dec(x_35);
x_38 = lean_array_get_size(x_33);
x_39 = lean_nat_dec_le(x_37, x_38);
lean_dec(x_38);
lean_dec(x_37);
if (x_39 == 0)
{
lean_object* x_40; 
x_40 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__2(x_33);
lean_ctor_set(x_9, 1, x_40);
lean_ctor_set(x_9, 0, x_31);
x_7 = x_12;
goto _start;
}
else
{
lean_ctor_set(x_9, 1, x_33);
lean_ctor_set(x_9, 0, x_31);
x_7 = x_12;
goto _start;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_inc(x_1);
x_43 = lean_array_uset(x_17, x_27, x_1);
lean_inc(x_2);
x_44 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__5(x_14, x_2, x_28);
x_45 = lean_array_uset(x_43, x_27, x_44);
lean_ctor_set(x_9, 1, x_45);
x_7 = x_12;
goto _start;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; uint64_t x_50; uint64_t x_51; uint64_t x_52; uint64_t x_53; uint64_t x_54; size_t x_55; size_t x_56; size_t x_57; size_t x_58; lean_object* x_59; uint8_t x_60; 
x_47 = lean_ctor_get(x_9, 0);
x_48 = lean_ctor_get(x_9, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_9);
x_49 = lean_array_get_size(x_48);
x_50 = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_hashDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_15_(x_14);
x_51 = lean_uint64_shift_right(x_50, x_3);
x_52 = lean_uint64_xor(x_50, x_51);
x_53 = lean_uint64_shift_right(x_52, x_4);
x_54 = lean_uint64_xor(x_52, x_53);
x_55 = lean_uint64_to_usize(x_54);
x_56 = lean_usize_of_nat(x_49);
lean_dec(x_49);
x_57 = lean_usize_sub(x_56, x_5);
x_58 = lean_usize_land(x_55, x_57);
x_59 = lean_array_uget(x_48, x_58);
x_60 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__1(x_14, x_59);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_61 = lean_unsigned_to_nat(1u);
x_62 = lean_nat_add(x_47, x_61);
lean_dec(x_47);
lean_inc(x_2);
x_63 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_63, 0, x_14);
lean_ctor_set(x_63, 1, x_2);
lean_ctor_set(x_63, 2, x_59);
x_64 = lean_array_uset(x_48, x_58, x_63);
x_65 = lean_unsigned_to_nat(4u);
x_66 = lean_nat_mul(x_62, x_65);
x_67 = lean_unsigned_to_nat(3u);
x_68 = lean_nat_div(x_66, x_67);
lean_dec(x_66);
x_69 = lean_array_get_size(x_64);
x_70 = lean_nat_dec_le(x_68, x_69);
lean_dec(x_69);
lean_dec(x_68);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; 
x_71 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__2(x_64);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_62);
lean_ctor_set(x_72, 1, x_71);
x_7 = x_12;
x_9 = x_72;
goto _start;
}
else
{
lean_object* x_74; 
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_62);
lean_ctor_set(x_74, 1, x_64);
x_7 = x_12;
x_9 = x_74;
goto _start;
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
lean_inc(x_1);
x_76 = lean_array_uset(x_48, x_58, x_1);
lean_inc(x_2);
x_77 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__5(x_14, x_2, x_59);
x_78 = lean_array_uset(x_76, x_58, x_77);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_47);
lean_ctor_set(x_79, 1, x_78);
x_7 = x_12;
x_9 = x_79;
goto _start;
}
}
}
else
{
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__11(lean_object* x_1, lean_object* x_2, uint64_t x_3, uint64_t x_4, size_t x_5, lean_object* x_6, size_t x_7, size_t x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_eq(x_7, x_8);
if (x_10 == 0)
{
size_t x_11; size_t x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = 1;
x_12 = lean_usize_sub(x_7, x_11);
x_13 = lean_array_uget(x_6, x_12);
x_14 = l_Lean_Compiler_LCNF_FloatLetIn_Decision_ofAlt(x_13);
lean_dec(x_13);
x_15 = !lean_is_exclusive(x_9);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint64_t x_19; uint64_t x_20; uint64_t x_21; uint64_t x_22; uint64_t x_23; size_t x_24; size_t x_25; size_t x_26; size_t x_27; lean_object* x_28; uint8_t x_29; 
x_16 = lean_ctor_get(x_9, 0);
x_17 = lean_ctor_get(x_9, 1);
x_18 = lean_array_get_size(x_17);
x_19 = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_hashDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_15_(x_14);
x_20 = lean_uint64_shift_right(x_19, x_3);
x_21 = lean_uint64_xor(x_19, x_20);
x_22 = lean_uint64_shift_right(x_21, x_4);
x_23 = lean_uint64_xor(x_21, x_22);
x_24 = lean_uint64_to_usize(x_23);
x_25 = lean_usize_of_nat(x_18);
lean_dec(x_18);
x_26 = lean_usize_sub(x_25, x_5);
x_27 = lean_usize_land(x_24, x_26);
x_28 = lean_array_uget(x_17, x_27);
x_29 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__1(x_14, x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_nat_add(x_16, x_30);
lean_dec(x_16);
lean_inc(x_2);
x_32 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_32, 0, x_14);
lean_ctor_set(x_32, 1, x_2);
lean_ctor_set(x_32, 2, x_28);
x_33 = lean_array_uset(x_17, x_27, x_32);
x_34 = lean_unsigned_to_nat(4u);
x_35 = lean_nat_mul(x_31, x_34);
x_36 = lean_unsigned_to_nat(3u);
x_37 = lean_nat_div(x_35, x_36);
lean_dec(x_35);
x_38 = lean_array_get_size(x_33);
x_39 = lean_nat_dec_le(x_37, x_38);
lean_dec(x_38);
lean_dec(x_37);
if (x_39 == 0)
{
lean_object* x_40; 
x_40 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__2(x_33);
lean_ctor_set(x_9, 1, x_40);
lean_ctor_set(x_9, 0, x_31);
x_7 = x_12;
goto _start;
}
else
{
lean_ctor_set(x_9, 1, x_33);
lean_ctor_set(x_9, 0, x_31);
x_7 = x_12;
goto _start;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_inc(x_1);
x_43 = lean_array_uset(x_17, x_27, x_1);
lean_inc(x_2);
x_44 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__5(x_14, x_2, x_28);
x_45 = lean_array_uset(x_43, x_27, x_44);
lean_ctor_set(x_9, 1, x_45);
x_7 = x_12;
goto _start;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; uint64_t x_50; uint64_t x_51; uint64_t x_52; uint64_t x_53; uint64_t x_54; size_t x_55; size_t x_56; size_t x_57; size_t x_58; lean_object* x_59; uint8_t x_60; 
x_47 = lean_ctor_get(x_9, 0);
x_48 = lean_ctor_get(x_9, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_9);
x_49 = lean_array_get_size(x_48);
x_50 = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_hashDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_15_(x_14);
x_51 = lean_uint64_shift_right(x_50, x_3);
x_52 = lean_uint64_xor(x_50, x_51);
x_53 = lean_uint64_shift_right(x_52, x_4);
x_54 = lean_uint64_xor(x_52, x_53);
x_55 = lean_uint64_to_usize(x_54);
x_56 = lean_usize_of_nat(x_49);
lean_dec(x_49);
x_57 = lean_usize_sub(x_56, x_5);
x_58 = lean_usize_land(x_55, x_57);
x_59 = lean_array_uget(x_48, x_58);
x_60 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__1(x_14, x_59);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_61 = lean_unsigned_to_nat(1u);
x_62 = lean_nat_add(x_47, x_61);
lean_dec(x_47);
lean_inc(x_2);
x_63 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_63, 0, x_14);
lean_ctor_set(x_63, 1, x_2);
lean_ctor_set(x_63, 2, x_59);
x_64 = lean_array_uset(x_48, x_58, x_63);
x_65 = lean_unsigned_to_nat(4u);
x_66 = lean_nat_mul(x_62, x_65);
x_67 = lean_unsigned_to_nat(3u);
x_68 = lean_nat_div(x_66, x_67);
lean_dec(x_66);
x_69 = lean_array_get_size(x_64);
x_70 = lean_nat_dec_le(x_68, x_69);
lean_dec(x_69);
lean_dec(x_68);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; 
x_71 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__2(x_64);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_62);
lean_ctor_set(x_72, 1, x_71);
x_7 = x_12;
x_9 = x_72;
goto _start;
}
else
{
lean_object* x_74; 
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_62);
lean_ctor_set(x_74, 1, x_64);
x_7 = x_12;
x_9 = x_74;
goto _start;
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
lean_inc(x_1);
x_76 = lean_array_uset(x_48, x_58, x_1);
lean_inc(x_2);
x_77 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__5(x_14, x_2, x_59);
x_78 = lean_array_uset(x_76, x_58, x_77);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_47);
lean_ctor_set(x_79, 1, x_78);
x_7 = x_12;
x_9 = x_79;
goto _start;
}
}
}
else
{
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
}
static uint64_t _init_l_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___closed__1() {
_start:
{
lean_object* x_1; uint64_t x_2; 
x_1 = lean_box(2);
x_2 = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_hashDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_15_(x_1);
return x_2;
}
}
static uint64_t _init_l_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___closed__2() {
_start:
{
uint64_t x_1; uint64_t x_2; uint64_t x_3; 
x_1 = 32;
x_2 = l_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___closed__1;
x_3 = lean_uint64_shift_right(x_2, x_1);
return x_3;
}
}
static uint64_t _init_l_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___closed__3() {
_start:
{
uint64_t x_1; uint64_t x_2; uint64_t x_3; 
x_1 = l_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___closed__1;
x_2 = l_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___closed__2;
x_3 = lean_uint64_xor(x_1, x_2);
return x_3;
}
}
static uint64_t _init_l_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___closed__4() {
_start:
{
uint64_t x_1; uint64_t x_2; uint64_t x_3; 
x_1 = 16;
x_2 = l_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___closed__3;
x_3 = lean_uint64_shift_right(x_2, x_1);
return x_3;
}
}
static uint64_t _init_l_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___closed__5() {
_start:
{
uint64_t x_1; uint64_t x_2; uint64_t x_3; 
x_1 = l_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___closed__3;
x_2 = l_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___closed__4;
x_3 = lean_uint64_xor(x_1, x_2);
return x_3;
}
}
static size_t _init_l_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___closed__6() {
_start:
{
uint64_t x_1; size_t x_2; 
x_1 = l_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___closed__5;
x_2 = lean_uint64_to_usize(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_initialNewArms(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint64_t x_15; uint64_t x_16; size_t x_17; size_t x_18; size_t x_19; size_t x_20; size_t x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_25; 
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
x_10 = l_Nat_nextPowerOfTwo_go(x_9, x_4, lean_box(0));
lean_dec(x_9);
x_11 = lean_box(0);
x_12 = lean_mk_array(x_10, x_11);
x_13 = lean_box(0);
x_14 = lean_array_get_size(x_12);
x_15 = 32;
x_16 = 16;
x_17 = lean_usize_of_nat(x_14);
lean_dec(x_14);
x_18 = 1;
x_19 = lean_usize_sub(x_17, x_18);
x_20 = l_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___closed__6;
x_21 = lean_usize_land(x_20, x_19);
x_22 = lean_array_uget(x_12, x_21);
x_23 = lean_box(2);
x_24 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__1(x_23, x_22);
x_25 = lean_nat_dec_le(x_3, x_3);
if (x_24 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_26 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_26, 0, x_23);
lean_ctor_set(x_26, 1, x_13);
lean_ctor_set(x_26, 2, x_22);
x_27 = lean_array_uset(x_12, x_21, x_26);
x_28 = lean_array_get_size(x_27);
x_29 = lean_nat_dec_le(x_4, x_28);
lean_dec(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__2(x_27);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_4);
lean_ctor_set(x_31, 1, x_30);
if (x_25 == 0)
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_unsigned_to_nat(0u);
x_33 = lean_nat_dec_lt(x_32, x_3);
if (x_33 == 0)
{
lean_dec(x_3);
return x_31;
}
else
{
size_t x_34; size_t x_35; lean_object* x_36; 
x_34 = lean_usize_of_nat(x_3);
lean_dec(x_3);
x_35 = 0;
x_36 = l_Array_foldrMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__6(x_11, x_13, x_15, x_16, x_18, x_2, x_34, x_35, x_31);
return x_36;
}
}
else
{
lean_object* x_37; uint8_t x_38; 
x_37 = lean_unsigned_to_nat(0u);
x_38 = lean_nat_dec_lt(x_37, x_3);
if (x_38 == 0)
{
lean_dec(x_3);
return x_31;
}
else
{
size_t x_39; size_t x_40; lean_object* x_41; 
x_39 = lean_usize_of_nat(x_3);
lean_dec(x_3);
x_40 = 0;
x_41 = l_Array_foldrMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__7(x_11, x_13, x_15, x_16, x_18, x_2, x_39, x_40, x_31);
return x_41;
}
}
}
else
{
lean_object* x_42; 
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_4);
lean_ctor_set(x_42, 1, x_27);
if (x_25 == 0)
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_unsigned_to_nat(0u);
x_44 = lean_nat_dec_lt(x_43, x_3);
if (x_44 == 0)
{
lean_dec(x_3);
return x_42;
}
else
{
size_t x_45; size_t x_46; lean_object* x_47; 
x_45 = lean_usize_of_nat(x_3);
lean_dec(x_3);
x_46 = 0;
x_47 = l_Array_foldrMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__8(x_11, x_13, x_15, x_16, x_18, x_2, x_45, x_46, x_42);
return x_47;
}
}
else
{
lean_object* x_48; uint8_t x_49; 
x_48 = lean_unsigned_to_nat(0u);
x_49 = lean_nat_dec_lt(x_48, x_3);
if (x_49 == 0)
{
lean_dec(x_3);
return x_42;
}
else
{
size_t x_50; size_t x_51; lean_object* x_52; 
x_50 = lean_usize_of_nat(x_3);
lean_dec(x_3);
x_51 = 0;
x_52 = l_Array_foldrMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__9(x_11, x_13, x_15, x_16, x_18, x_2, x_50, x_51, x_42);
return x_52;
}
}
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_53 = lean_array_uset(x_12, x_21, x_11);
x_54 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__5(x_23, x_13, x_22);
x_55 = lean_array_uset(x_53, x_21, x_54);
x_56 = lean_unsigned_to_nat(0u);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_55);
if (x_25 == 0)
{
uint8_t x_58; 
x_58 = lean_nat_dec_lt(x_56, x_3);
if (x_58 == 0)
{
lean_dec(x_3);
return x_57;
}
else
{
size_t x_59; size_t x_60; lean_object* x_61; 
x_59 = lean_usize_of_nat(x_3);
lean_dec(x_3);
x_60 = 0;
x_61 = l_Array_foldrMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__10(x_11, x_13, x_15, x_16, x_18, x_2, x_59, x_60, x_57);
return x_61;
}
}
else
{
uint8_t x_62; 
x_62 = lean_nat_dec_lt(x_56, x_3);
if (x_62 == 0)
{
lean_dec(x_3);
return x_57;
}
else
{
size_t x_63; size_t x_64; lean_object* x_65; 
x_63 = lean_usize_of_nat(x_3);
lean_dec(x_3);
x_64 = 0;
x_65 = l_Array_foldrMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__11(x_11, x_13, x_15, x_16, x_18, x_2, x_63, x_64, x_57);
return x_65;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint64_t x_10; uint64_t x_11; size_t x_12; size_t x_13; size_t x_14; lean_object* x_15; 
x_10 = lean_unbox_uint64(x_3);
lean_dec(x_3);
x_11 = lean_unbox_uint64(x_4);
lean_dec(x_4);
x_12 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_13 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_14 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_15 = l_Array_foldrMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__6(x_1, x_2, x_10, x_11, x_12, x_6, x_13, x_14, x_9);
lean_dec(x_6);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint64_t x_10; uint64_t x_11; size_t x_12; size_t x_13; size_t x_14; lean_object* x_15; 
x_10 = lean_unbox_uint64(x_3);
lean_dec(x_3);
x_11 = lean_unbox_uint64(x_4);
lean_dec(x_4);
x_12 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_13 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_14 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_15 = l_Array_foldrMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__7(x_1, x_2, x_10, x_11, x_12, x_6, x_13, x_14, x_9);
lean_dec(x_6);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint64_t x_10; uint64_t x_11; size_t x_12; size_t x_13; size_t x_14; lean_object* x_15; 
x_10 = lean_unbox_uint64(x_3);
lean_dec(x_3);
x_11 = lean_unbox_uint64(x_4);
lean_dec(x_4);
x_12 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_13 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_14 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_15 = l_Array_foldrMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__8(x_1, x_2, x_10, x_11, x_12, x_6, x_13, x_14, x_9);
lean_dec(x_6);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint64_t x_10; uint64_t x_11; size_t x_12; size_t x_13; size_t x_14; lean_object* x_15; 
x_10 = lean_unbox_uint64(x_3);
lean_dec(x_3);
x_11 = lean_unbox_uint64(x_4);
lean_dec(x_4);
x_12 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_13 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_14 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_15 = l_Array_foldrMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__9(x_1, x_2, x_10, x_11, x_12, x_6, x_13, x_14, x_9);
lean_dec(x_6);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint64_t x_10; uint64_t x_11; size_t x_12; size_t x_13; size_t x_14; lean_object* x_15; 
x_10 = lean_unbox_uint64(x_3);
lean_dec(x_3);
x_11 = lean_unbox_uint64(x_4);
lean_dec(x_4);
x_12 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_13 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_14 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_15 = l_Array_foldrMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__10(x_1, x_2, x_10, x_11, x_12, x_6, x_13, x_14, x_9);
lean_dec(x_6);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint64_t x_10; uint64_t x_11; size_t x_12; size_t x_13; size_t x_14; lean_object* x_15; 
x_10 = lean_unbox_uint64(x_3);
lean_dec(x_3);
x_11 = lean_unbox_uint64(x_4);
lean_dec(x_4);
x_12 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_13 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_14 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_15 = l_Array_foldrMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__11(x_1, x_2, x_10, x_11, x_12, x_6, x_13, x_14, x_9);
lean_dec(x_6);
return x_15;
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_st_ref_get(x_2, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
x_12 = !lean_is_exclusive(x_9);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint64_t x_17; uint64_t x_18; uint64_t x_19; uint64_t x_20; uint64_t x_21; uint64_t x_22; uint64_t x_23; size_t x_24; size_t x_25; size_t x_26; size_t x_27; size_t x_28; lean_object* x_29; uint8_t x_30; 
x_13 = lean_ctor_get(x_9, 1);
x_14 = lean_ctor_get(x_9, 0);
lean_dec(x_14);
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_15);
lean_dec(x_11);
x_16 = lean_array_get_size(x_15);
x_17 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1724_(x_1);
x_18 = 32;
x_19 = lean_uint64_shift_right(x_17, x_18);
x_20 = lean_uint64_xor(x_17, x_19);
x_21 = 16;
x_22 = lean_uint64_shift_right(x_20, x_21);
x_23 = lean_uint64_xor(x_20, x_22);
x_24 = lean_uint64_to_usize(x_23);
x_25 = lean_usize_of_nat(x_16);
lean_dec(x_16);
x_26 = 1;
x_27 = lean_usize_sub(x_25, x_26);
x_28 = lean_usize_land(x_24, x_27);
x_29 = lean_array_uget(x_15, x_28);
lean_dec(x_15);
x_30 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__2(x_1, x_29);
lean_dec(x_29);
if (x_30 == 0)
{
lean_object* x_31; 
lean_dec(x_1);
x_31 = lean_box(0);
lean_ctor_set(x_9, 0, x_31);
return x_9;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
lean_free_object(x_9);
x_32 = lean_st_ref_take(x_2, x_13);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
lean_dec(x_32);
x_36 = !lean_is_exclusive(x_33);
if (x_36 == 0)
{
lean_object* x_37; uint8_t x_38; 
x_37 = lean_ctor_get(x_33, 0);
lean_dec(x_37);
x_38 = !lean_is_exclusive(x_34);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; size_t x_42; size_t x_43; size_t x_44; lean_object* x_45; uint8_t x_46; 
x_39 = lean_ctor_get(x_34, 0);
x_40 = lean_ctor_get(x_34, 1);
x_41 = lean_array_get_size(x_40);
x_42 = lean_usize_of_nat(x_41);
lean_dec(x_41);
x_43 = lean_usize_sub(x_42, x_26);
x_44 = lean_usize_land(x_24, x_43);
x_45 = lean_array_uget(x_40, x_44);
x_46 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__2(x_1, x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_47 = lean_unsigned_to_nat(1u);
x_48 = lean_nat_add(x_39, x_47);
lean_dec(x_39);
x_49 = lean_box(2);
x_50 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_50, 0, x_1);
lean_ctor_set(x_50, 1, x_49);
lean_ctor_set(x_50, 2, x_45);
x_51 = lean_array_uset(x_40, x_44, x_50);
x_52 = lean_unsigned_to_nat(4u);
x_53 = lean_nat_mul(x_48, x_52);
x_54 = lean_unsigned_to_nat(3u);
x_55 = lean_nat_div(x_53, x_54);
lean_dec(x_53);
x_56 = lean_array_get_size(x_51);
x_57 = lean_nat_dec_le(x_55, x_56);
lean_dec(x_56);
lean_dec(x_55);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_58 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__3(x_51);
lean_ctor_set(x_34, 1, x_58);
lean_ctor_set(x_34, 0, x_48);
x_59 = lean_st_ref_set(x_2, x_33, x_35);
x_60 = !lean_is_exclusive(x_59);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_59, 0);
lean_dec(x_61);
x_62 = lean_box(0);
lean_ctor_set(x_59, 0, x_62);
return x_59;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_59, 1);
lean_inc(x_63);
lean_dec(x_59);
x_64 = lean_box(0);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_63);
return x_65;
}
}
else
{
lean_object* x_66; uint8_t x_67; 
lean_ctor_set(x_34, 1, x_51);
lean_ctor_set(x_34, 0, x_48);
x_66 = lean_st_ref_set(x_2, x_33, x_35);
x_67 = !lean_is_exclusive(x_66);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_66, 0);
lean_dec(x_68);
x_69 = lean_box(0);
lean_ctor_set(x_66, 0, x_69);
return x_66;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_66, 1);
lean_inc(x_70);
lean_dec(x_66);
x_71 = lean_box(0);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_70);
return x_72;
}
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; 
x_73 = lean_box(0);
x_74 = lean_array_uset(x_40, x_44, x_73);
x_75 = lean_box(2);
x_76 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__6(x_1, x_75, x_45);
x_77 = lean_array_uset(x_74, x_44, x_76);
lean_ctor_set(x_34, 1, x_77);
x_78 = lean_st_ref_set(x_2, x_33, x_35);
x_79 = !lean_is_exclusive(x_78);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; 
x_80 = lean_ctor_get(x_78, 0);
lean_dec(x_80);
x_81 = lean_box(0);
lean_ctor_set(x_78, 0, x_81);
return x_78;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_78, 1);
lean_inc(x_82);
lean_dec(x_78);
x_83 = lean_box(0);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_82);
return x_84;
}
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; size_t x_88; size_t x_89; size_t x_90; lean_object* x_91; uint8_t x_92; 
x_85 = lean_ctor_get(x_34, 0);
x_86 = lean_ctor_get(x_34, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_34);
x_87 = lean_array_get_size(x_86);
x_88 = lean_usize_of_nat(x_87);
lean_dec(x_87);
x_89 = lean_usize_sub(x_88, x_26);
x_90 = lean_usize_land(x_24, x_89);
x_91 = lean_array_uget(x_86, x_90);
x_92 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__2(x_1, x_91);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_93 = lean_unsigned_to_nat(1u);
x_94 = lean_nat_add(x_85, x_93);
lean_dec(x_85);
x_95 = lean_box(2);
x_96 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_96, 0, x_1);
lean_ctor_set(x_96, 1, x_95);
lean_ctor_set(x_96, 2, x_91);
x_97 = lean_array_uset(x_86, x_90, x_96);
x_98 = lean_unsigned_to_nat(4u);
x_99 = lean_nat_mul(x_94, x_98);
x_100 = lean_unsigned_to_nat(3u);
x_101 = lean_nat_div(x_99, x_100);
lean_dec(x_99);
x_102 = lean_array_get_size(x_97);
x_103 = lean_nat_dec_le(x_101, x_102);
lean_dec(x_102);
lean_dec(x_101);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_104 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__3(x_97);
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_94);
lean_ctor_set(x_105, 1, x_104);
lean_ctor_set(x_33, 0, x_105);
x_106 = lean_st_ref_set(x_2, x_33, x_35);
x_107 = lean_ctor_get(x_106, 1);
lean_inc(x_107);
if (lean_is_exclusive(x_106)) {
 lean_ctor_release(x_106, 0);
 lean_ctor_release(x_106, 1);
 x_108 = x_106;
} else {
 lean_dec_ref(x_106);
 x_108 = lean_box(0);
}
x_109 = lean_box(0);
if (lean_is_scalar(x_108)) {
 x_110 = lean_alloc_ctor(0, 2, 0);
} else {
 x_110 = x_108;
}
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_107);
return x_110;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_94);
lean_ctor_set(x_111, 1, x_97);
lean_ctor_set(x_33, 0, x_111);
x_112 = lean_st_ref_set(x_2, x_33, x_35);
x_113 = lean_ctor_get(x_112, 1);
lean_inc(x_113);
if (lean_is_exclusive(x_112)) {
 lean_ctor_release(x_112, 0);
 lean_ctor_release(x_112, 1);
 x_114 = x_112;
} else {
 lean_dec_ref(x_112);
 x_114 = lean_box(0);
}
x_115 = lean_box(0);
if (lean_is_scalar(x_114)) {
 x_116 = lean_alloc_ctor(0, 2, 0);
} else {
 x_116 = x_114;
}
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_113);
return x_116;
}
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_117 = lean_box(0);
x_118 = lean_array_uset(x_86, x_90, x_117);
x_119 = lean_box(2);
x_120 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__6(x_1, x_119, x_91);
x_121 = lean_array_uset(x_118, x_90, x_120);
x_122 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_122, 0, x_85);
lean_ctor_set(x_122, 1, x_121);
lean_ctor_set(x_33, 0, x_122);
x_123 = lean_st_ref_set(x_2, x_33, x_35);
x_124 = lean_ctor_get(x_123, 1);
lean_inc(x_124);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 lean_ctor_release(x_123, 1);
 x_125 = x_123;
} else {
 lean_dec_ref(x_123);
 x_125 = lean_box(0);
}
x_126 = lean_box(0);
if (lean_is_scalar(x_125)) {
 x_127 = lean_alloc_ctor(0, 2, 0);
} else {
 x_127 = x_125;
}
lean_ctor_set(x_127, 0, x_126);
lean_ctor_set(x_127, 1, x_124);
return x_127;
}
}
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; size_t x_133; size_t x_134; size_t x_135; lean_object* x_136; uint8_t x_137; 
x_128 = lean_ctor_get(x_33, 1);
lean_inc(x_128);
lean_dec(x_33);
x_129 = lean_ctor_get(x_34, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_34, 1);
lean_inc(x_130);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_131 = x_34;
} else {
 lean_dec_ref(x_34);
 x_131 = lean_box(0);
}
x_132 = lean_array_get_size(x_130);
x_133 = lean_usize_of_nat(x_132);
lean_dec(x_132);
x_134 = lean_usize_sub(x_133, x_26);
x_135 = lean_usize_land(x_24, x_134);
x_136 = lean_array_uget(x_130, x_135);
x_137 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__2(x_1, x_136);
if (x_137 == 0)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; uint8_t x_148; 
x_138 = lean_unsigned_to_nat(1u);
x_139 = lean_nat_add(x_129, x_138);
lean_dec(x_129);
x_140 = lean_box(2);
x_141 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_141, 0, x_1);
lean_ctor_set(x_141, 1, x_140);
lean_ctor_set(x_141, 2, x_136);
x_142 = lean_array_uset(x_130, x_135, x_141);
x_143 = lean_unsigned_to_nat(4u);
x_144 = lean_nat_mul(x_139, x_143);
x_145 = lean_unsigned_to_nat(3u);
x_146 = lean_nat_div(x_144, x_145);
lean_dec(x_144);
x_147 = lean_array_get_size(x_142);
x_148 = lean_nat_dec_le(x_146, x_147);
lean_dec(x_147);
lean_dec(x_146);
if (x_148 == 0)
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_149 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__3(x_142);
if (lean_is_scalar(x_131)) {
 x_150 = lean_alloc_ctor(0, 2, 0);
} else {
 x_150 = x_131;
}
lean_ctor_set(x_150, 0, x_139);
lean_ctor_set(x_150, 1, x_149);
x_151 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_151, 0, x_150);
lean_ctor_set(x_151, 1, x_128);
x_152 = lean_st_ref_set(x_2, x_151, x_35);
x_153 = lean_ctor_get(x_152, 1);
lean_inc(x_153);
if (lean_is_exclusive(x_152)) {
 lean_ctor_release(x_152, 0);
 lean_ctor_release(x_152, 1);
 x_154 = x_152;
} else {
 lean_dec_ref(x_152);
 x_154 = lean_box(0);
}
x_155 = lean_box(0);
if (lean_is_scalar(x_154)) {
 x_156 = lean_alloc_ctor(0, 2, 0);
} else {
 x_156 = x_154;
}
lean_ctor_set(x_156, 0, x_155);
lean_ctor_set(x_156, 1, x_153);
return x_156;
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
if (lean_is_scalar(x_131)) {
 x_157 = lean_alloc_ctor(0, 2, 0);
} else {
 x_157 = x_131;
}
lean_ctor_set(x_157, 0, x_139);
lean_ctor_set(x_157, 1, x_142);
x_158 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_158, 0, x_157);
lean_ctor_set(x_158, 1, x_128);
x_159 = lean_st_ref_set(x_2, x_158, x_35);
x_160 = lean_ctor_get(x_159, 1);
lean_inc(x_160);
if (lean_is_exclusive(x_159)) {
 lean_ctor_release(x_159, 0);
 lean_ctor_release(x_159, 1);
 x_161 = x_159;
} else {
 lean_dec_ref(x_159);
 x_161 = lean_box(0);
}
x_162 = lean_box(0);
if (lean_is_scalar(x_161)) {
 x_163 = lean_alloc_ctor(0, 2, 0);
} else {
 x_163 = x_161;
}
lean_ctor_set(x_163, 0, x_162);
lean_ctor_set(x_163, 1, x_160);
return x_163;
}
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_164 = lean_box(0);
x_165 = lean_array_uset(x_130, x_135, x_164);
x_166 = lean_box(2);
x_167 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__6(x_1, x_166, x_136);
x_168 = lean_array_uset(x_165, x_135, x_167);
if (lean_is_scalar(x_131)) {
 x_169 = lean_alloc_ctor(0, 2, 0);
} else {
 x_169 = x_131;
}
lean_ctor_set(x_169, 0, x_129);
lean_ctor_set(x_169, 1, x_168);
x_170 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_170, 0, x_169);
lean_ctor_set(x_170, 1, x_128);
x_171 = lean_st_ref_set(x_2, x_170, x_35);
x_172 = lean_ctor_get(x_171, 1);
lean_inc(x_172);
if (lean_is_exclusive(x_171)) {
 lean_ctor_release(x_171, 0);
 lean_ctor_release(x_171, 1);
 x_173 = x_171;
} else {
 lean_dec_ref(x_171);
 x_173 = lean_box(0);
}
x_174 = lean_box(0);
if (lean_is_scalar(x_173)) {
 x_175 = lean_alloc_ctor(0, 2, 0);
} else {
 x_175 = x_173;
}
lean_ctor_set(x_175, 0, x_174);
lean_ctor_set(x_175, 1, x_172);
return x_175;
}
}
}
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; uint64_t x_179; uint64_t x_180; uint64_t x_181; uint64_t x_182; uint64_t x_183; uint64_t x_184; uint64_t x_185; size_t x_186; size_t x_187; size_t x_188; size_t x_189; size_t x_190; lean_object* x_191; uint8_t x_192; 
x_176 = lean_ctor_get(x_9, 1);
lean_inc(x_176);
lean_dec(x_9);
x_177 = lean_ctor_get(x_11, 1);
lean_inc(x_177);
lean_dec(x_11);
x_178 = lean_array_get_size(x_177);
x_179 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1724_(x_1);
x_180 = 32;
x_181 = lean_uint64_shift_right(x_179, x_180);
x_182 = lean_uint64_xor(x_179, x_181);
x_183 = 16;
x_184 = lean_uint64_shift_right(x_182, x_183);
x_185 = lean_uint64_xor(x_182, x_184);
x_186 = lean_uint64_to_usize(x_185);
x_187 = lean_usize_of_nat(x_178);
lean_dec(x_178);
x_188 = 1;
x_189 = lean_usize_sub(x_187, x_188);
x_190 = lean_usize_land(x_186, x_189);
x_191 = lean_array_uget(x_177, x_190);
lean_dec(x_177);
x_192 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__2(x_1, x_191);
lean_dec(x_191);
if (x_192 == 0)
{
lean_object* x_193; lean_object* x_194; 
lean_dec(x_1);
x_193 = lean_box(0);
x_194 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_194, 0, x_193);
lean_ctor_set(x_194, 1, x_176);
return x_194;
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; size_t x_205; size_t x_206; size_t x_207; lean_object* x_208; uint8_t x_209; 
x_195 = lean_st_ref_take(x_2, x_176);
x_196 = lean_ctor_get(x_195, 0);
lean_inc(x_196);
x_197 = lean_ctor_get(x_196, 0);
lean_inc(x_197);
x_198 = lean_ctor_get(x_195, 1);
lean_inc(x_198);
lean_dec(x_195);
x_199 = lean_ctor_get(x_196, 1);
lean_inc(x_199);
if (lean_is_exclusive(x_196)) {
 lean_ctor_release(x_196, 0);
 lean_ctor_release(x_196, 1);
 x_200 = x_196;
} else {
 lean_dec_ref(x_196);
 x_200 = lean_box(0);
}
x_201 = lean_ctor_get(x_197, 0);
lean_inc(x_201);
x_202 = lean_ctor_get(x_197, 1);
lean_inc(x_202);
if (lean_is_exclusive(x_197)) {
 lean_ctor_release(x_197, 0);
 lean_ctor_release(x_197, 1);
 x_203 = x_197;
} else {
 lean_dec_ref(x_197);
 x_203 = lean_box(0);
}
x_204 = lean_array_get_size(x_202);
x_205 = lean_usize_of_nat(x_204);
lean_dec(x_204);
x_206 = lean_usize_sub(x_205, x_188);
x_207 = lean_usize_land(x_186, x_206);
x_208 = lean_array_uget(x_202, x_207);
x_209 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__2(x_1, x_208);
if (x_209 == 0)
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; uint8_t x_220; 
x_210 = lean_unsigned_to_nat(1u);
x_211 = lean_nat_add(x_201, x_210);
lean_dec(x_201);
x_212 = lean_box(2);
x_213 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_213, 0, x_1);
lean_ctor_set(x_213, 1, x_212);
lean_ctor_set(x_213, 2, x_208);
x_214 = lean_array_uset(x_202, x_207, x_213);
x_215 = lean_unsigned_to_nat(4u);
x_216 = lean_nat_mul(x_211, x_215);
x_217 = lean_unsigned_to_nat(3u);
x_218 = lean_nat_div(x_216, x_217);
lean_dec(x_216);
x_219 = lean_array_get_size(x_214);
x_220 = lean_nat_dec_le(x_218, x_219);
lean_dec(x_219);
lean_dec(x_218);
if (x_220 == 0)
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; 
x_221 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__3(x_214);
if (lean_is_scalar(x_203)) {
 x_222 = lean_alloc_ctor(0, 2, 0);
} else {
 x_222 = x_203;
}
lean_ctor_set(x_222, 0, x_211);
lean_ctor_set(x_222, 1, x_221);
if (lean_is_scalar(x_200)) {
 x_223 = lean_alloc_ctor(0, 2, 0);
} else {
 x_223 = x_200;
}
lean_ctor_set(x_223, 0, x_222);
lean_ctor_set(x_223, 1, x_199);
x_224 = lean_st_ref_set(x_2, x_223, x_198);
x_225 = lean_ctor_get(x_224, 1);
lean_inc(x_225);
if (lean_is_exclusive(x_224)) {
 lean_ctor_release(x_224, 0);
 lean_ctor_release(x_224, 1);
 x_226 = x_224;
} else {
 lean_dec_ref(x_224);
 x_226 = lean_box(0);
}
x_227 = lean_box(0);
if (lean_is_scalar(x_226)) {
 x_228 = lean_alloc_ctor(0, 2, 0);
} else {
 x_228 = x_226;
}
lean_ctor_set(x_228, 0, x_227);
lean_ctor_set(x_228, 1, x_225);
return x_228;
}
else
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; 
if (lean_is_scalar(x_203)) {
 x_229 = lean_alloc_ctor(0, 2, 0);
} else {
 x_229 = x_203;
}
lean_ctor_set(x_229, 0, x_211);
lean_ctor_set(x_229, 1, x_214);
if (lean_is_scalar(x_200)) {
 x_230 = lean_alloc_ctor(0, 2, 0);
} else {
 x_230 = x_200;
}
lean_ctor_set(x_230, 0, x_229);
lean_ctor_set(x_230, 1, x_199);
x_231 = lean_st_ref_set(x_2, x_230, x_198);
x_232 = lean_ctor_get(x_231, 1);
lean_inc(x_232);
if (lean_is_exclusive(x_231)) {
 lean_ctor_release(x_231, 0);
 lean_ctor_release(x_231, 1);
 x_233 = x_231;
} else {
 lean_dec_ref(x_231);
 x_233 = lean_box(0);
}
x_234 = lean_box(0);
if (lean_is_scalar(x_233)) {
 x_235 = lean_alloc_ctor(0, 2, 0);
} else {
 x_235 = x_233;
}
lean_ctor_set(x_235, 0, x_234);
lean_ctor_set(x_235, 1, x_232);
return x_235;
}
}
else
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; 
x_236 = lean_box(0);
x_237 = lean_array_uset(x_202, x_207, x_236);
x_238 = lean_box(2);
x_239 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__6(x_1, x_238, x_208);
x_240 = lean_array_uset(x_237, x_207, x_239);
if (lean_is_scalar(x_203)) {
 x_241 = lean_alloc_ctor(0, 2, 0);
} else {
 x_241 = x_203;
}
lean_ctor_set(x_241, 0, x_201);
lean_ctor_set(x_241, 1, x_240);
if (lean_is_scalar(x_200)) {
 x_242 = lean_alloc_ctor(0, 2, 0);
} else {
 x_242 = x_200;
}
lean_ctor_set(x_242, 0, x_241);
lean_ctor_set(x_242, 1, x_199);
x_243 = lean_st_ref_set(x_2, x_242, x_198);
x_244 = lean_ctor_get(x_243, 1);
lean_inc(x_244);
if (lean_is_exclusive(x_243)) {
 lean_ctor_release(x_243, 0);
 lean_ctor_release(x_243, 1);
 x_245 = x_243;
} else {
 lean_dec_ref(x_243);
 x_245 = lean_box(0);
}
x_246 = lean_box(0);
if (lean_is_scalar(x_245)) {
 x_247 = lean_alloc_ctor(0, 2, 0);
} else {
 x_247 = x_245;
}
lean_ctor_set(x_247, 0, x_246);
lean_ctor_set(x_247, 1, x_244);
return x_247;
}
}
}
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
static lean_object* _init_l_Std_DHashMap_Internal_AssocList_get_x21___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Std.Data.DHashMap.Internal.AssocList.Basic", 42, 42);
return x_1;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_AssocList_get_x21___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Std.DHashMap.Internal.AssocList.get!", 36, 36);
return x_1;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_AssocList_get_x21___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("key is not present in hash table", 32, 32);
return x_1;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_AssocList_get_x21___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Std_DHashMap_Internal_AssocList_get_x21___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__1___closed__1;
x_2 = l_Std_DHashMap_Internal_AssocList_get_x21___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__1___closed__2;
x_3 = lean_unsigned_to_nat(122u);
x_4 = lean_unsigned_to_nat(11u);
x_5 = l_Std_DHashMap_Internal_AssocList_get_x21___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__1___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x21___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__1___closed__4;
x_5 = l_panic___rarg(x_1, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_3, 1);
x_8 = lean_ctor_get(x_3, 2);
x_9 = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_beqDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_62_(x_6, x_2);
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
LEAN_EXPORT lean_object* l_panic___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = l_panic___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__3___closed__3;
x_10 = lean_panic_fn(x_9, x_1);
x_11 = lean_apply_7(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 1:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
lean_dec(x_2);
x_11 = lean_apply_8(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
case 2:
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_2);
lean_dec(x_1);
x_12 = l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__2___closed__4;
x_13 = l_panic___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__4(x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_13;
}
case 5:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_2, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_2, 1);
lean_inc(x_15);
lean_dec(x_2);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_16 = l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__3(x_1, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_2 = x_15;
x_9 = x_17;
goto _start;
}
else
{
uint8_t x_19; 
lean_dec(x_15);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_19 = !lean_is_exclusive(x_16);
if (x_19 == 0)
{
return x_16;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_16, 0);
x_21 = lean_ctor_get(x_16, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_16);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
case 6:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_2, 1);
lean_inc(x_23);
x_24 = lean_ctor_get(x_2, 2);
lean_inc(x_24);
lean_dec(x_2);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_25 = l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__3(x_1, x_23, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_2 = x_24;
x_9 = x_26;
goto _start;
}
else
{
uint8_t x_28; 
lean_dec(x_24);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_25);
if (x_28 == 0)
{
return x_25;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_25, 0);
x_30 = lean_ctor_get(x_25, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_25);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
case 7:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_2, 1);
lean_inc(x_32);
x_33 = lean_ctor_get(x_2, 2);
lean_inc(x_33);
lean_dec(x_2);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_34 = l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__3(x_1, x_32, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
x_2 = x_33;
x_9 = x_35;
goto _start;
}
else
{
uint8_t x_37; 
lean_dec(x_33);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_37 = !lean_is_exclusive(x_34);
if (x_37 == 0)
{
return x_34;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_34, 0);
x_39 = lean_ctor_get(x_34, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_34);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
case 8:
{
lean_object* x_41; lean_object* x_42; 
lean_dec(x_2);
lean_dec(x_1);
x_41 = l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__2___closed__4;
x_42 = l_panic___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__4(x_41, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_42;
}
case 11:
{
lean_object* x_43; lean_object* x_44; 
lean_dec(x_2);
lean_dec(x_1);
x_43 = l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__2___closed__4;
x_44 = l_panic___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__4(x_43, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_44;
}
default: 
{
lean_object* x_45; lean_object* x_46; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_45 = lean_box(0);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_9);
return x_46;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
x_15 = l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__3(x_1, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__7(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
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
x_15 = l_Lean_Compiler_LCNF_Arg_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__6(x_1, x_14, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
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
uint8_t x_21; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_15);
if (x_21 == 0)
{
return x_15;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_15, 0);
x_23 = lean_ctor_get(x_15, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_15);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
else
{
lean_object* x_25; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_5);
lean_ctor_set(x_25, 1, x_12);
return x_25;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__8(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
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
x_15 = l_Lean_Compiler_LCNF_Arg_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__6(x_1, x_14, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
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
uint8_t x_21; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_15);
if (x_21 == 0)
{
return x_15;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_15, 0);
x_23 = lean_ctor_get(x_15, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_15);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
else
{
lean_object* x_25; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_5);
lean_ctor_set(x_25, 1, x_12);
return x_25;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_2, 2);
lean_inc(x_12);
lean_dec(x_2);
x_13 = lean_array_get_size(x_12);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_dec_lt(x_14, x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_9);
return x_17;
}
else
{
uint8_t x_18; 
x_18 = lean_nat_dec_le(x_13, x_13);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_9);
return x_20;
}
else
{
size_t x_21; size_t x_22; lean_object* x_23; lean_object* x_24; 
x_21 = 0;
x_22 = lean_usize_of_nat(x_13);
lean_dec(x_13);
x_23 = lean_box(0);
x_24 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__7(x_1, x_12, x_21, x_22, x_23, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_12);
return x_24;
}
}
}
case 4:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_2, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_2, 1);
lean_inc(x_26);
lean_dec(x_2);
lean_inc(x_1);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_27 = lean_apply_8(x_1, x_25, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_29 = lean_ctor_get(x_27, 1);
x_30 = lean_ctor_get(x_27, 0);
lean_dec(x_30);
x_31 = lean_array_get_size(x_26);
x_32 = lean_unsigned_to_nat(0u);
x_33 = lean_nat_dec_lt(x_32, x_31);
if (x_33 == 0)
{
lean_object* x_34; 
lean_dec(x_31);
lean_dec(x_26);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_34 = lean_box(0);
lean_ctor_set(x_27, 0, x_34);
return x_27;
}
else
{
uint8_t x_35; 
x_35 = lean_nat_dec_le(x_31, x_31);
if (x_35 == 0)
{
lean_object* x_36; 
lean_dec(x_31);
lean_dec(x_26);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_36 = lean_box(0);
lean_ctor_set(x_27, 0, x_36);
return x_27;
}
else
{
size_t x_37; size_t x_38; lean_object* x_39; lean_object* x_40; 
lean_free_object(x_27);
x_37 = 0;
x_38 = lean_usize_of_nat(x_31);
lean_dec(x_31);
x_39 = lean_box(0);
x_40 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__8(x_1, x_26, x_37, x_38, x_39, x_3, x_4, x_5, x_6, x_7, x_8, x_29);
lean_dec(x_26);
return x_40;
}
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_41 = lean_ctor_get(x_27, 1);
lean_inc(x_41);
lean_dec(x_27);
x_42 = lean_array_get_size(x_26);
x_43 = lean_unsigned_to_nat(0u);
x_44 = lean_nat_dec_lt(x_43, x_42);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
lean_dec(x_42);
lean_dec(x_26);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_45 = lean_box(0);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_41);
return x_46;
}
else
{
uint8_t x_47; 
x_47 = lean_nat_dec_le(x_42, x_42);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_42);
lean_dec(x_26);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_48 = lean_box(0);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_41);
return x_49;
}
else
{
size_t x_50; size_t x_51; lean_object* x_52; lean_object* x_53; 
x_50 = 0;
x_51 = lean_usize_of_nat(x_42);
lean_dec(x_42);
x_52 = lean_box(0);
x_53 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__8(x_1, x_26, x_50, x_51, x_52, x_3, x_4, x_5, x_6, x_7, x_8, x_41);
lean_dec(x_26);
return x_53;
}
}
}
}
else
{
uint8_t x_54; 
lean_dec(x_26);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_54 = !lean_is_exclusive(x_27);
if (x_54 == 0)
{
return x_27;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_27, 0);
x_56 = lean_ctor_get(x_27, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_27);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
default: 
{
lean_object* x_58; lean_object* x_59; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_58 = lean_box(0);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_9);
return x_59;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_2, 2);
lean_inc(x_10);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_11 = l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__3(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_ctor_get(x_2, 3);
lean_inc(x_13);
lean_dec(x_2);
x_14 = l_Lean_Compiler_LCNF_LetValue_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__5(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
return x_14;
}
else
{
uint8_t x_15; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_15 = !lean_is_exclusive(x_11);
if (x_15 == 0)
{
return x_11;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_11, 0);
x_17 = lean_ctor_get(x_11, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_11);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_2, 2);
lean_inc(x_10);
lean_dec(x_2);
x_11 = l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__3(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__12(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
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
x_15 = l_Lean_Compiler_LCNF_Param_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__10(x_1, x_14, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
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
uint8_t x_21; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_15);
if (x_21 == 0)
{
return x_15;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_15, 0);
x_23 = lean_ctor_get(x_15, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_15);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
else
{
lean_object* x_25; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_5);
lean_ctor_set(x_25, 1, x_12);
return x_25;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__13(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
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
x_15 = l_Lean_Compiler_LCNF_Param_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__10(x_1, x_14, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
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
uint8_t x_21; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_15);
if (x_21 == 0)
{
return x_15;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_15, 0);
x_23 = lean_ctor_get(x_15, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_15);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
else
{
lean_object* x_25; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_5);
lean_ctor_set(x_25, 1, x_12);
return x_25;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__14(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
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
x_15 = l_Lean_Compiler_LCNF_Arg_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__6(x_1, x_14, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
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
uint8_t x_21; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_15);
if (x_21 == 0)
{
return x_15;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_15, 0);
x_23 = lean_ctor_get(x_15, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_15);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
else
{
lean_object* x_25; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_5);
lean_ctor_set(x_25, 1, x_12);
return x_25;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_AltCore_forCodeM___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__15(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__16(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_eq(x_3, x_4);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_5);
x_14 = lean_array_uget(x_2, x_3);
lean_inc(x_1);
x_15 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__11), 9, 1);
lean_closure_set(x_15, 0, x_1);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_16 = l_Lean_Compiler_LCNF_AltCore_forCodeM___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__15(x_14, x_15, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
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
uint8_t x_22; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
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
lean_object* x_26; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_5);
lean_ctor_set(x_26, 1, x_12);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
lean_dec(x_2);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_12 = l_Lean_Compiler_LCNF_LetDecl_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__2(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
uint8_t x_15; 
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_15 = !lean_is_exclusive(x_12);
if (x_15 == 0)
{
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_12, 0);
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_12);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
case 1:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_19 = lean_ctor_get(x_2, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_2, 1);
lean_inc(x_20);
lean_dec(x_2);
x_21 = lean_ctor_get(x_19, 2);
lean_inc(x_21);
x_22 = lean_array_get_size(x_21);
x_23 = lean_unsigned_to_nat(0u);
x_24 = lean_nat_dec_lt(x_23, x_22);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_22);
lean_dec(x_21);
x_25 = lean_ctor_get(x_19, 3);
lean_inc(x_25);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_26 = l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__3(x_1, x_25, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = lean_ctor_get(x_19, 4);
lean_inc(x_28);
lean_dec(x_19);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_29 = l_Lean_Compiler_LCNF_Code_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__11(x_1, x_28, x_3, x_4, x_5, x_6, x_7, x_8, x_27);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
x_2 = x_20;
x_9 = x_30;
goto _start;
}
else
{
uint8_t x_32; 
lean_dec(x_20);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_29);
if (x_32 == 0)
{
return x_29;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_29, 0);
x_34 = lean_ctor_get(x_29, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_29);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
else
{
uint8_t x_36; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_36 = !lean_is_exclusive(x_26);
if (x_36 == 0)
{
return x_26;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_26, 0);
x_38 = lean_ctor_get(x_26, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_26);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
uint8_t x_40; 
x_40 = lean_nat_dec_le(x_22, x_22);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
lean_dec(x_22);
lean_dec(x_21);
x_41 = lean_ctor_get(x_19, 3);
lean_inc(x_41);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_42 = l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__3(x_1, x_41, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec(x_42);
x_44 = lean_ctor_get(x_19, 4);
lean_inc(x_44);
lean_dec(x_19);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_45 = l_Lean_Compiler_LCNF_Code_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__11(x_1, x_44, x_3, x_4, x_5, x_6, x_7, x_8, x_43);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
lean_dec(x_45);
x_2 = x_20;
x_9 = x_46;
goto _start;
}
else
{
uint8_t x_48; 
lean_dec(x_20);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_48 = !lean_is_exclusive(x_45);
if (x_48 == 0)
{
return x_45;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_45, 0);
x_50 = lean_ctor_get(x_45, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_45);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
else
{
uint8_t x_52; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_52 = !lean_is_exclusive(x_42);
if (x_52 == 0)
{
return x_42;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_42, 0);
x_54 = lean_ctor_get(x_42, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_42);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
else
{
size_t x_56; size_t x_57; lean_object* x_58; lean_object* x_59; 
x_56 = 0;
x_57 = lean_usize_of_nat(x_22);
lean_dec(x_22);
x_58 = lean_box(0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_59 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__12(x_1, x_21, x_56, x_57, x_58, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_21);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_59, 1);
lean_inc(x_60);
lean_dec(x_59);
x_61 = lean_ctor_get(x_19, 3);
lean_inc(x_61);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_62 = l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__3(x_1, x_61, x_3, x_4, x_5, x_6, x_7, x_8, x_60);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_62, 1);
lean_inc(x_63);
lean_dec(x_62);
x_64 = lean_ctor_get(x_19, 4);
lean_inc(x_64);
lean_dec(x_19);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_65 = l_Lean_Compiler_LCNF_Code_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__11(x_1, x_64, x_3, x_4, x_5, x_6, x_7, x_8, x_63);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; 
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
lean_dec(x_65);
x_2 = x_20;
x_9 = x_66;
goto _start;
}
else
{
uint8_t x_68; 
lean_dec(x_20);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_68 = !lean_is_exclusive(x_65);
if (x_68 == 0)
{
return x_65;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_65, 0);
x_70 = lean_ctor_get(x_65, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_65);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
else
{
uint8_t x_72; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_72 = !lean_is_exclusive(x_62);
if (x_72 == 0)
{
return x_62;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_62, 0);
x_74 = lean_ctor_get(x_62, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_62);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
}
else
{
uint8_t x_76; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_76 = !lean_is_exclusive(x_59);
if (x_76 == 0)
{
return x_59;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_59, 0);
x_78 = lean_ctor_get(x_59, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_59);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
}
}
case 2:
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; 
x_80 = lean_ctor_get(x_2, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_2, 1);
lean_inc(x_81);
lean_dec(x_2);
x_82 = lean_ctor_get(x_80, 2);
lean_inc(x_82);
x_83 = lean_array_get_size(x_82);
x_84 = lean_unsigned_to_nat(0u);
x_85 = lean_nat_dec_lt(x_84, x_83);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; 
lean_dec(x_83);
lean_dec(x_82);
x_86 = lean_ctor_get(x_80, 3);
lean_inc(x_86);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_87 = l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__3(x_1, x_86, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_87, 1);
lean_inc(x_88);
lean_dec(x_87);
x_89 = lean_ctor_get(x_80, 4);
lean_inc(x_89);
lean_dec(x_80);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_90 = l_Lean_Compiler_LCNF_Code_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__11(x_1, x_89, x_3, x_4, x_5, x_6, x_7, x_8, x_88);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; 
x_91 = lean_ctor_get(x_90, 1);
lean_inc(x_91);
lean_dec(x_90);
x_2 = x_81;
x_9 = x_91;
goto _start;
}
else
{
uint8_t x_93; 
lean_dec(x_81);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_93 = !lean_is_exclusive(x_90);
if (x_93 == 0)
{
return x_90;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_90, 0);
x_95 = lean_ctor_get(x_90, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_90);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
return x_96;
}
}
}
else
{
uint8_t x_97; 
lean_dec(x_81);
lean_dec(x_80);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_97 = !lean_is_exclusive(x_87);
if (x_97 == 0)
{
return x_87;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_87, 0);
x_99 = lean_ctor_get(x_87, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_87);
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
return x_100;
}
}
}
else
{
uint8_t x_101; 
x_101 = lean_nat_dec_le(x_83, x_83);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; 
lean_dec(x_83);
lean_dec(x_82);
x_102 = lean_ctor_get(x_80, 3);
lean_inc(x_102);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_103 = l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__3(x_1, x_102, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_103, 1);
lean_inc(x_104);
lean_dec(x_103);
x_105 = lean_ctor_get(x_80, 4);
lean_inc(x_105);
lean_dec(x_80);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_106 = l_Lean_Compiler_LCNF_Code_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__11(x_1, x_105, x_3, x_4, x_5, x_6, x_7, x_8, x_104);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; 
x_107 = lean_ctor_get(x_106, 1);
lean_inc(x_107);
lean_dec(x_106);
x_2 = x_81;
x_9 = x_107;
goto _start;
}
else
{
uint8_t x_109; 
lean_dec(x_81);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_109 = !lean_is_exclusive(x_106);
if (x_109 == 0)
{
return x_106;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_106, 0);
x_111 = lean_ctor_get(x_106, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_106);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
return x_112;
}
}
}
else
{
uint8_t x_113; 
lean_dec(x_81);
lean_dec(x_80);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_113 = !lean_is_exclusive(x_103);
if (x_113 == 0)
{
return x_103;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_103, 0);
x_115 = lean_ctor_get(x_103, 1);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_103);
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
return x_116;
}
}
}
else
{
size_t x_117; size_t x_118; lean_object* x_119; lean_object* x_120; 
x_117 = 0;
x_118 = lean_usize_of_nat(x_83);
lean_dec(x_83);
x_119 = lean_box(0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_120 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__13(x_1, x_82, x_117, x_118, x_119, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_82);
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_ctor_get(x_120, 1);
lean_inc(x_121);
lean_dec(x_120);
x_122 = lean_ctor_get(x_80, 3);
lean_inc(x_122);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_123 = l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__3(x_1, x_122, x_3, x_4, x_5, x_6, x_7, x_8, x_121);
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_124 = lean_ctor_get(x_123, 1);
lean_inc(x_124);
lean_dec(x_123);
x_125 = lean_ctor_get(x_80, 4);
lean_inc(x_125);
lean_dec(x_80);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_126 = l_Lean_Compiler_LCNF_Code_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__11(x_1, x_125, x_3, x_4, x_5, x_6, x_7, x_8, x_124);
if (lean_obj_tag(x_126) == 0)
{
lean_object* x_127; 
x_127 = lean_ctor_get(x_126, 1);
lean_inc(x_127);
lean_dec(x_126);
x_2 = x_81;
x_9 = x_127;
goto _start;
}
else
{
uint8_t x_129; 
lean_dec(x_81);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_129 = !lean_is_exclusive(x_126);
if (x_129 == 0)
{
return x_126;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_130 = lean_ctor_get(x_126, 0);
x_131 = lean_ctor_get(x_126, 1);
lean_inc(x_131);
lean_inc(x_130);
lean_dec(x_126);
x_132 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_132, 0, x_130);
lean_ctor_set(x_132, 1, x_131);
return x_132;
}
}
}
else
{
uint8_t x_133; 
lean_dec(x_81);
lean_dec(x_80);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_133 = !lean_is_exclusive(x_123);
if (x_133 == 0)
{
return x_123;
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_134 = lean_ctor_get(x_123, 0);
x_135 = lean_ctor_get(x_123, 1);
lean_inc(x_135);
lean_inc(x_134);
lean_dec(x_123);
x_136 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_136, 0, x_134);
lean_ctor_set(x_136, 1, x_135);
return x_136;
}
}
}
else
{
uint8_t x_137; 
lean_dec(x_81);
lean_dec(x_80);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_137 = !lean_is_exclusive(x_120);
if (x_137 == 0)
{
return x_120;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_138 = lean_ctor_get(x_120, 0);
x_139 = lean_ctor_get(x_120, 1);
lean_inc(x_139);
lean_inc(x_138);
lean_dec(x_120);
x_140 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_140, 0, x_138);
lean_ctor_set(x_140, 1, x_139);
return x_140;
}
}
}
}
}
case 3:
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_141 = lean_ctor_get(x_2, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_2, 1);
lean_inc(x_142);
lean_dec(x_2);
lean_inc(x_1);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_143 = lean_apply_8(x_1, x_141, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_143) == 0)
{
uint8_t x_144; 
x_144 = !lean_is_exclusive(x_143);
if (x_144 == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; uint8_t x_149; 
x_145 = lean_ctor_get(x_143, 1);
x_146 = lean_ctor_get(x_143, 0);
lean_dec(x_146);
x_147 = lean_array_get_size(x_142);
x_148 = lean_unsigned_to_nat(0u);
x_149 = lean_nat_dec_lt(x_148, x_147);
if (x_149 == 0)
{
lean_object* x_150; 
lean_dec(x_147);
lean_dec(x_142);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_150 = lean_box(0);
lean_ctor_set(x_143, 0, x_150);
return x_143;
}
else
{
uint8_t x_151; 
x_151 = lean_nat_dec_le(x_147, x_147);
if (x_151 == 0)
{
lean_object* x_152; 
lean_dec(x_147);
lean_dec(x_142);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_152 = lean_box(0);
lean_ctor_set(x_143, 0, x_152);
return x_143;
}
else
{
size_t x_153; size_t x_154; lean_object* x_155; lean_object* x_156; 
lean_free_object(x_143);
x_153 = 0;
x_154 = lean_usize_of_nat(x_147);
lean_dec(x_147);
x_155 = lean_box(0);
x_156 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__14(x_1, x_142, x_153, x_154, x_155, x_3, x_4, x_5, x_6, x_7, x_8, x_145);
lean_dec(x_142);
return x_156;
}
}
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; uint8_t x_160; 
x_157 = lean_ctor_get(x_143, 1);
lean_inc(x_157);
lean_dec(x_143);
x_158 = lean_array_get_size(x_142);
x_159 = lean_unsigned_to_nat(0u);
x_160 = lean_nat_dec_lt(x_159, x_158);
if (x_160 == 0)
{
lean_object* x_161; lean_object* x_162; 
lean_dec(x_158);
lean_dec(x_142);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_161 = lean_box(0);
x_162 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_162, 0, x_161);
lean_ctor_set(x_162, 1, x_157);
return x_162;
}
else
{
uint8_t x_163; 
x_163 = lean_nat_dec_le(x_158, x_158);
if (x_163 == 0)
{
lean_object* x_164; lean_object* x_165; 
lean_dec(x_158);
lean_dec(x_142);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_164 = lean_box(0);
x_165 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_165, 0, x_164);
lean_ctor_set(x_165, 1, x_157);
return x_165;
}
else
{
size_t x_166; size_t x_167; lean_object* x_168; lean_object* x_169; 
x_166 = 0;
x_167 = lean_usize_of_nat(x_158);
lean_dec(x_158);
x_168 = lean_box(0);
x_169 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__14(x_1, x_142, x_166, x_167, x_168, x_3, x_4, x_5, x_6, x_7, x_8, x_157);
lean_dec(x_142);
return x_169;
}
}
}
}
else
{
uint8_t x_170; 
lean_dec(x_142);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_170 = !lean_is_exclusive(x_143);
if (x_170 == 0)
{
return x_143;
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_171 = lean_ctor_get(x_143, 0);
x_172 = lean_ctor_get(x_143, 1);
lean_inc(x_172);
lean_inc(x_171);
lean_dec(x_143);
x_173 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_173, 0, x_171);
lean_ctor_set(x_173, 1, x_172);
return x_173;
}
}
}
case 4:
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_174 = lean_ctor_get(x_2, 0);
lean_inc(x_174);
lean_dec(x_2);
x_175 = lean_ctor_get(x_174, 1);
lean_inc(x_175);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_176 = l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__3(x_1, x_175, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_176) == 0)
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_177 = lean_ctor_get(x_176, 1);
lean_inc(x_177);
lean_dec(x_176);
x_178 = lean_ctor_get(x_174, 2);
lean_inc(x_178);
lean_inc(x_1);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_179 = lean_apply_8(x_1, x_178, x_3, x_4, x_5, x_6, x_7, x_8, x_177);
if (lean_obj_tag(x_179) == 0)
{
uint8_t x_180; 
x_180 = !lean_is_exclusive(x_179);
if (x_180 == 0)
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; uint8_t x_186; 
x_181 = lean_ctor_get(x_179, 1);
x_182 = lean_ctor_get(x_179, 0);
lean_dec(x_182);
x_183 = lean_ctor_get(x_174, 3);
lean_inc(x_183);
lean_dec(x_174);
x_184 = lean_array_get_size(x_183);
x_185 = lean_unsigned_to_nat(0u);
x_186 = lean_nat_dec_lt(x_185, x_184);
if (x_186 == 0)
{
lean_object* x_187; 
lean_dec(x_184);
lean_dec(x_183);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_187 = lean_box(0);
lean_ctor_set(x_179, 0, x_187);
return x_179;
}
else
{
uint8_t x_188; 
x_188 = lean_nat_dec_le(x_184, x_184);
if (x_188 == 0)
{
lean_object* x_189; 
lean_dec(x_184);
lean_dec(x_183);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_189 = lean_box(0);
lean_ctor_set(x_179, 0, x_189);
return x_179;
}
else
{
size_t x_190; size_t x_191; lean_object* x_192; lean_object* x_193; 
lean_free_object(x_179);
x_190 = 0;
x_191 = lean_usize_of_nat(x_184);
lean_dec(x_184);
x_192 = lean_box(0);
x_193 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__16(x_1, x_183, x_190, x_191, x_192, x_3, x_4, x_5, x_6, x_7, x_8, x_181);
lean_dec(x_183);
return x_193;
}
}
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; uint8_t x_198; 
x_194 = lean_ctor_get(x_179, 1);
lean_inc(x_194);
lean_dec(x_179);
x_195 = lean_ctor_get(x_174, 3);
lean_inc(x_195);
lean_dec(x_174);
x_196 = lean_array_get_size(x_195);
x_197 = lean_unsigned_to_nat(0u);
x_198 = lean_nat_dec_lt(x_197, x_196);
if (x_198 == 0)
{
lean_object* x_199; lean_object* x_200; 
lean_dec(x_196);
lean_dec(x_195);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_199 = lean_box(0);
x_200 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_200, 0, x_199);
lean_ctor_set(x_200, 1, x_194);
return x_200;
}
else
{
uint8_t x_201; 
x_201 = lean_nat_dec_le(x_196, x_196);
if (x_201 == 0)
{
lean_object* x_202; lean_object* x_203; 
lean_dec(x_196);
lean_dec(x_195);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_202 = lean_box(0);
x_203 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_203, 0, x_202);
lean_ctor_set(x_203, 1, x_194);
return x_203;
}
else
{
size_t x_204; size_t x_205; lean_object* x_206; lean_object* x_207; 
x_204 = 0;
x_205 = lean_usize_of_nat(x_196);
lean_dec(x_196);
x_206 = lean_box(0);
x_207 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__16(x_1, x_195, x_204, x_205, x_206, x_3, x_4, x_5, x_6, x_7, x_8, x_194);
lean_dec(x_195);
return x_207;
}
}
}
}
else
{
uint8_t x_208; 
lean_dec(x_174);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_208 = !lean_is_exclusive(x_179);
if (x_208 == 0)
{
return x_179;
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; 
x_209 = lean_ctor_get(x_179, 0);
x_210 = lean_ctor_get(x_179, 1);
lean_inc(x_210);
lean_inc(x_209);
lean_dec(x_179);
x_211 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_211, 0, x_209);
lean_ctor_set(x_211, 1, x_210);
return x_211;
}
}
}
else
{
uint8_t x_212; 
lean_dec(x_174);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_212 = !lean_is_exclusive(x_176);
if (x_212 == 0)
{
return x_176;
}
else
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; 
x_213 = lean_ctor_get(x_176, 0);
x_214 = lean_ctor_get(x_176, 1);
lean_inc(x_214);
lean_inc(x_213);
lean_dec(x_176);
x_215 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_215, 0, x_213);
lean_ctor_set(x_215, 1, x_214);
return x_215;
}
}
}
case 5:
{
lean_object* x_216; lean_object* x_217; 
x_216 = lean_ctor_get(x_2, 0);
lean_inc(x_216);
lean_dec(x_2);
x_217 = lean_apply_8(x_1, x_216, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_217;
}
default: 
{
lean_object* x_218; lean_object* x_219; 
x_218 = lean_ctor_get(x_2, 0);
lean_inc(x_218);
lean_dec(x_2);
x_219 = l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__3(x_1, x_218, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_219;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__17(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
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
x_15 = l_Lean_Compiler_LCNF_Param_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__10(x_1, x_14, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
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
uint8_t x_21; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_15);
if (x_21 == 0)
{
return x_15;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_15, 0);
x_23 = lean_ctor_get(x_15, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_15);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
else
{
lean_object* x_25; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_5);
lean_ctor_set(x_25, 1, x_12);
return x_25;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_2, 2);
lean_inc(x_10);
x_11 = lean_array_get_size(x_10);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_nat_dec_lt(x_12, x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_11);
lean_dec(x_10);
x_14 = lean_ctor_get(x_2, 3);
lean_inc(x_14);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_15 = l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__3(x_1, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_ctor_get(x_2, 4);
lean_inc(x_17);
lean_dec(x_2);
x_18 = l_Lean_Compiler_LCNF_Code_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__11(x_1, x_17, x_3, x_4, x_5, x_6, x_7, x_8, x_16);
return x_18;
}
else
{
uint8_t x_19; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_19 = !lean_is_exclusive(x_15);
if (x_19 == 0)
{
return x_15;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_15, 0);
x_21 = lean_ctor_get(x_15, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_15);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
else
{
uint8_t x_23; 
x_23 = lean_nat_dec_le(x_11, x_11);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_11);
lean_dec(x_10);
x_24 = lean_ctor_get(x_2, 3);
lean_inc(x_24);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_25 = l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__3(x_1, x_24, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_27 = lean_ctor_get(x_2, 4);
lean_inc(x_27);
lean_dec(x_2);
x_28 = l_Lean_Compiler_LCNF_Code_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__11(x_1, x_27, x_3, x_4, x_5, x_6, x_7, x_8, x_26);
return x_28;
}
else
{
uint8_t x_29; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_25);
if (x_29 == 0)
{
return x_25;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_25, 0);
x_31 = lean_ctor_get(x_25, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_25);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
size_t x_33; size_t x_34; lean_object* x_35; lean_object* x_36; 
x_33 = 0;
x_34 = lean_usize_of_nat(x_11);
lean_dec(x_11);
x_35 = lean_box(0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_36 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__17(x_1, x_10, x_33, x_34, x_35, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_10);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec(x_36);
x_38 = lean_ctor_get(x_2, 3);
lean_inc(x_38);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_39 = l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__3(x_1, x_38, x_3, x_4, x_5, x_6, x_7, x_8, x_37);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
lean_dec(x_39);
x_41 = lean_ctor_get(x_2, 4);
lean_inc(x_41);
lean_dec(x_2);
x_42 = l_Lean_Compiler_LCNF_Code_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__11(x_1, x_41, x_3, x_4, x_5, x_6, x_7, x_8, x_40);
return x_42;
}
else
{
uint8_t x_43; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_39);
if (x_43 == 0)
{
return x_39;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_39, 0);
x_45 = lean_ctor_get(x_39, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_39);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
else
{
uint8_t x_47; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_47 = !lean_is_exclusive(x_36);
if (x_47 == 0)
{
return x_36;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_36, 0);
x_49 = lean_ctor_get(x_36, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_36);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_FloatLetIn_dontFloat___closed__1() {
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
lean_object* x_9; 
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; 
x_221 = lean_ctor_get(x_1, 0);
lean_inc(x_221);
x_222 = l_Lean_Compiler_LCNF_FloatLetIn_dontFloat___closed__1;
lean_inc(x_2);
x_223 = l_Lean_Compiler_LCNF_LetDecl_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__2(x_222, x_221, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_223) == 0)
{
lean_object* x_224; 
x_224 = lean_ctor_get(x_223, 1);
lean_inc(x_224);
lean_dec(x_223);
x_9 = x_224;
goto block_220;
}
else
{
uint8_t x_225; 
lean_dec(x_2);
lean_dec(x_1);
x_225 = !lean_is_exclusive(x_223);
if (x_225 == 0)
{
return x_223;
}
else
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; 
x_226 = lean_ctor_get(x_223, 0);
x_227 = lean_ctor_get(x_223, 1);
lean_inc(x_227);
lean_inc(x_226);
lean_dec(x_223);
x_228 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_228, 0, x_226);
lean_ctor_set(x_228, 1, x_227);
return x_228;
}
}
}
else
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; 
x_229 = lean_ctor_get(x_1, 0);
lean_inc(x_229);
x_230 = l_Lean_Compiler_LCNF_FloatLetIn_dontFloat___closed__1;
lean_inc(x_2);
x_231 = l_Lean_Compiler_LCNF_FunDecl_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__9(x_230, x_229, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_231) == 0)
{
lean_object* x_232; 
x_232 = lean_ctor_get(x_231, 1);
lean_inc(x_232);
lean_dec(x_231);
x_9 = x_232;
goto block_220;
}
else
{
uint8_t x_233; 
lean_dec(x_2);
lean_dec(x_1);
x_233 = !lean_is_exclusive(x_231);
if (x_233 == 0)
{
return x_231;
}
else
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; 
x_234 = lean_ctor_get(x_231, 0);
x_235 = lean_ctor_get(x_231, 1);
lean_inc(x_235);
lean_inc(x_234);
lean_dec(x_231);
x_236 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_236, 0, x_234);
lean_ctor_set(x_236, 1, x_235);
return x_236;
}
}
}
block_220:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_st_ref_take(x_2, x_9);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_10, 1);
x_15 = lean_ctor_get(x_12, 1);
x_16 = lean_box(0);
x_17 = !lean_is_exclusive(x_15);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; size_t x_21; size_t x_22; size_t x_23; size_t x_24; size_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_18 = lean_ctor_get(x_15, 0);
x_19 = lean_ctor_get(x_15, 1);
x_20 = lean_array_get_size(x_19);
x_21 = lean_usize_of_nat(x_20);
lean_dec(x_20);
x_22 = 1;
x_23 = lean_usize_sub(x_21, x_22);
x_24 = l_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___closed__6;
x_25 = lean_usize_land(x_24, x_23);
x_26 = lean_array_uget(x_19, x_25);
x_27 = lean_box(2);
x_28 = l_Std_DHashMap_Internal_AssocList_get_x21___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__1(x_16, x_27, x_26);
lean_ctor_set_tag(x_10, 1);
lean_ctor_set(x_10, 1, x_28);
lean_ctor_set(x_10, 0, x_1);
x_29 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__1(x_27, x_26);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_nat_add(x_18, x_30);
lean_dec(x_18);
x_32 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_32, 0, x_27);
lean_ctor_set(x_32, 1, x_10);
lean_ctor_set(x_32, 2, x_26);
x_33 = lean_array_uset(x_19, x_25, x_32);
x_34 = lean_unsigned_to_nat(4u);
x_35 = lean_nat_mul(x_31, x_34);
x_36 = lean_unsigned_to_nat(3u);
x_37 = lean_nat_div(x_35, x_36);
lean_dec(x_35);
x_38 = lean_array_get_size(x_33);
x_39 = lean_nat_dec_le(x_37, x_38);
lean_dec(x_38);
lean_dec(x_37);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_40 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__2(x_33);
lean_ctor_set(x_15, 1, x_40);
lean_ctor_set(x_15, 0, x_31);
x_41 = lean_st_ref_set(x_2, x_12, x_14);
lean_dec(x_2);
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_41, 0);
lean_dec(x_43);
x_44 = lean_box(0);
lean_ctor_set(x_41, 0, x_44);
return x_41;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_41, 1);
lean_inc(x_45);
lean_dec(x_41);
x_46 = lean_box(0);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_45);
return x_47;
}
}
else
{
lean_object* x_48; uint8_t x_49; 
lean_ctor_set(x_15, 1, x_33);
lean_ctor_set(x_15, 0, x_31);
x_48 = lean_st_ref_set(x_2, x_12, x_14);
lean_dec(x_2);
x_49 = !lean_is_exclusive(x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_48, 0);
lean_dec(x_50);
x_51 = lean_box(0);
lean_ctor_set(x_48, 0, x_51);
return x_48;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_48, 1);
lean_inc(x_52);
lean_dec(x_48);
x_53 = lean_box(0);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_52);
return x_54;
}
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_55 = lean_box(0);
x_56 = lean_array_uset(x_19, x_25, x_55);
x_57 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__5(x_27, x_10, x_26);
x_58 = lean_array_uset(x_56, x_25, x_57);
lean_ctor_set(x_15, 1, x_58);
x_59 = lean_st_ref_set(x_2, x_12, x_14);
lean_dec(x_2);
x_60 = !lean_is_exclusive(x_59);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_59, 0);
lean_dec(x_61);
x_62 = lean_box(0);
lean_ctor_set(x_59, 0, x_62);
return x_59;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_59, 1);
lean_inc(x_63);
lean_dec(x_59);
x_64 = lean_box(0);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_63);
return x_65;
}
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; size_t x_69; size_t x_70; size_t x_71; size_t x_72; size_t x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_66 = lean_ctor_get(x_15, 0);
x_67 = lean_ctor_get(x_15, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_15);
x_68 = lean_array_get_size(x_67);
x_69 = lean_usize_of_nat(x_68);
lean_dec(x_68);
x_70 = 1;
x_71 = lean_usize_sub(x_69, x_70);
x_72 = l_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___closed__6;
x_73 = lean_usize_land(x_72, x_71);
x_74 = lean_array_uget(x_67, x_73);
x_75 = lean_box(2);
x_76 = l_Std_DHashMap_Internal_AssocList_get_x21___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__1(x_16, x_75, x_74);
lean_ctor_set_tag(x_10, 1);
lean_ctor_set(x_10, 1, x_76);
lean_ctor_set(x_10, 0, x_1);
x_77 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__1(x_75, x_74);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_78 = lean_unsigned_to_nat(1u);
x_79 = lean_nat_add(x_66, x_78);
lean_dec(x_66);
x_80 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_80, 0, x_75);
lean_ctor_set(x_80, 1, x_10);
lean_ctor_set(x_80, 2, x_74);
x_81 = lean_array_uset(x_67, x_73, x_80);
x_82 = lean_unsigned_to_nat(4u);
x_83 = lean_nat_mul(x_79, x_82);
x_84 = lean_unsigned_to_nat(3u);
x_85 = lean_nat_div(x_83, x_84);
lean_dec(x_83);
x_86 = lean_array_get_size(x_81);
x_87 = lean_nat_dec_le(x_85, x_86);
lean_dec(x_86);
lean_dec(x_85);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_88 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__2(x_81);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_79);
lean_ctor_set(x_89, 1, x_88);
lean_ctor_set(x_12, 1, x_89);
x_90 = lean_st_ref_set(x_2, x_12, x_14);
lean_dec(x_2);
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
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_79);
lean_ctor_set(x_95, 1, x_81);
lean_ctor_set(x_12, 1, x_95);
x_96 = lean_st_ref_set(x_2, x_12, x_14);
lean_dec(x_2);
x_97 = lean_ctor_get(x_96, 1);
lean_inc(x_97);
if (lean_is_exclusive(x_96)) {
 lean_ctor_release(x_96, 0);
 lean_ctor_release(x_96, 1);
 x_98 = x_96;
} else {
 lean_dec_ref(x_96);
 x_98 = lean_box(0);
}
x_99 = lean_box(0);
if (lean_is_scalar(x_98)) {
 x_100 = lean_alloc_ctor(0, 2, 0);
} else {
 x_100 = x_98;
}
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_97);
return x_100;
}
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_101 = lean_box(0);
x_102 = lean_array_uset(x_67, x_73, x_101);
x_103 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__5(x_75, x_10, x_74);
x_104 = lean_array_uset(x_102, x_73, x_103);
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_66);
lean_ctor_set(x_105, 1, x_104);
lean_ctor_set(x_12, 1, x_105);
x_106 = lean_st_ref_set(x_2, x_12, x_14);
lean_dec(x_2);
x_107 = lean_ctor_get(x_106, 1);
lean_inc(x_107);
if (lean_is_exclusive(x_106)) {
 lean_ctor_release(x_106, 0);
 lean_ctor_release(x_106, 1);
 x_108 = x_106;
} else {
 lean_dec_ref(x_106);
 x_108 = lean_box(0);
}
x_109 = lean_box(0);
if (lean_is_scalar(x_108)) {
 x_110 = lean_alloc_ctor(0, 2, 0);
} else {
 x_110 = x_108;
}
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_107);
return x_110;
}
}
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; size_t x_119; size_t x_120; size_t x_121; size_t x_122; size_t x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; uint8_t x_127; 
x_111 = lean_ctor_get(x_10, 1);
x_112 = lean_ctor_get(x_12, 0);
x_113 = lean_ctor_get(x_12, 1);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_12);
x_114 = lean_box(0);
x_115 = lean_ctor_get(x_113, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_113, 1);
lean_inc(x_116);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 lean_ctor_release(x_113, 1);
 x_117 = x_113;
} else {
 lean_dec_ref(x_113);
 x_117 = lean_box(0);
}
x_118 = lean_array_get_size(x_116);
x_119 = lean_usize_of_nat(x_118);
lean_dec(x_118);
x_120 = 1;
x_121 = lean_usize_sub(x_119, x_120);
x_122 = l_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___closed__6;
x_123 = lean_usize_land(x_122, x_121);
x_124 = lean_array_uget(x_116, x_123);
x_125 = lean_box(2);
x_126 = l_Std_DHashMap_Internal_AssocList_get_x21___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__1(x_114, x_125, x_124);
lean_ctor_set_tag(x_10, 1);
lean_ctor_set(x_10, 1, x_126);
lean_ctor_set(x_10, 0, x_1);
x_127 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__1(x_125, x_124);
if (x_127 == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; uint8_t x_137; 
x_128 = lean_unsigned_to_nat(1u);
x_129 = lean_nat_add(x_115, x_128);
lean_dec(x_115);
x_130 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_130, 0, x_125);
lean_ctor_set(x_130, 1, x_10);
lean_ctor_set(x_130, 2, x_124);
x_131 = lean_array_uset(x_116, x_123, x_130);
x_132 = lean_unsigned_to_nat(4u);
x_133 = lean_nat_mul(x_129, x_132);
x_134 = lean_unsigned_to_nat(3u);
x_135 = lean_nat_div(x_133, x_134);
lean_dec(x_133);
x_136 = lean_array_get_size(x_131);
x_137 = lean_nat_dec_le(x_135, x_136);
lean_dec(x_136);
lean_dec(x_135);
if (x_137 == 0)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_138 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__2(x_131);
if (lean_is_scalar(x_117)) {
 x_139 = lean_alloc_ctor(0, 2, 0);
} else {
 x_139 = x_117;
}
lean_ctor_set(x_139, 0, x_129);
lean_ctor_set(x_139, 1, x_138);
x_140 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_140, 0, x_112);
lean_ctor_set(x_140, 1, x_139);
x_141 = lean_st_ref_set(x_2, x_140, x_111);
lean_dec(x_2);
x_142 = lean_ctor_get(x_141, 1);
lean_inc(x_142);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 lean_ctor_release(x_141, 1);
 x_143 = x_141;
} else {
 lean_dec_ref(x_141);
 x_143 = lean_box(0);
}
x_144 = lean_box(0);
if (lean_is_scalar(x_143)) {
 x_145 = lean_alloc_ctor(0, 2, 0);
} else {
 x_145 = x_143;
}
lean_ctor_set(x_145, 0, x_144);
lean_ctor_set(x_145, 1, x_142);
return x_145;
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
if (lean_is_scalar(x_117)) {
 x_146 = lean_alloc_ctor(0, 2, 0);
} else {
 x_146 = x_117;
}
lean_ctor_set(x_146, 0, x_129);
lean_ctor_set(x_146, 1, x_131);
x_147 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_147, 0, x_112);
lean_ctor_set(x_147, 1, x_146);
x_148 = lean_st_ref_set(x_2, x_147, x_111);
lean_dec(x_2);
x_149 = lean_ctor_get(x_148, 1);
lean_inc(x_149);
if (lean_is_exclusive(x_148)) {
 lean_ctor_release(x_148, 0);
 lean_ctor_release(x_148, 1);
 x_150 = x_148;
} else {
 lean_dec_ref(x_148);
 x_150 = lean_box(0);
}
x_151 = lean_box(0);
if (lean_is_scalar(x_150)) {
 x_152 = lean_alloc_ctor(0, 2, 0);
} else {
 x_152 = x_150;
}
lean_ctor_set(x_152, 0, x_151);
lean_ctor_set(x_152, 1, x_149);
return x_152;
}
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_153 = lean_box(0);
x_154 = lean_array_uset(x_116, x_123, x_153);
x_155 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__5(x_125, x_10, x_124);
x_156 = lean_array_uset(x_154, x_123, x_155);
if (lean_is_scalar(x_117)) {
 x_157 = lean_alloc_ctor(0, 2, 0);
} else {
 x_157 = x_117;
}
lean_ctor_set(x_157, 0, x_115);
lean_ctor_set(x_157, 1, x_156);
x_158 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_158, 0, x_112);
lean_ctor_set(x_158, 1, x_157);
x_159 = lean_st_ref_set(x_2, x_158, x_111);
lean_dec(x_2);
x_160 = lean_ctor_get(x_159, 1);
lean_inc(x_160);
if (lean_is_exclusive(x_159)) {
 lean_ctor_release(x_159, 0);
 lean_ctor_release(x_159, 1);
 x_161 = x_159;
} else {
 lean_dec_ref(x_159);
 x_161 = lean_box(0);
}
x_162 = lean_box(0);
if (lean_is_scalar(x_161)) {
 x_163 = lean_alloc_ctor(0, 2, 0);
} else {
 x_163 = x_161;
}
lean_ctor_set(x_163, 0, x_162);
lean_ctor_set(x_163, 1, x_160);
return x_163;
}
}
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; size_t x_174; size_t x_175; size_t x_176; size_t x_177; size_t x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; uint8_t x_183; 
x_164 = lean_ctor_get(x_10, 0);
x_165 = lean_ctor_get(x_10, 1);
lean_inc(x_165);
lean_inc(x_164);
lean_dec(x_10);
x_166 = lean_ctor_get(x_164, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_164, 1);
lean_inc(x_167);
if (lean_is_exclusive(x_164)) {
 lean_ctor_release(x_164, 0);
 lean_ctor_release(x_164, 1);
 x_168 = x_164;
} else {
 lean_dec_ref(x_164);
 x_168 = lean_box(0);
}
x_169 = lean_box(0);
x_170 = lean_ctor_get(x_167, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_167, 1);
lean_inc(x_171);
if (lean_is_exclusive(x_167)) {
 lean_ctor_release(x_167, 0);
 lean_ctor_release(x_167, 1);
 x_172 = x_167;
} else {
 lean_dec_ref(x_167);
 x_172 = lean_box(0);
}
x_173 = lean_array_get_size(x_171);
x_174 = lean_usize_of_nat(x_173);
lean_dec(x_173);
x_175 = 1;
x_176 = lean_usize_sub(x_174, x_175);
x_177 = l_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___closed__6;
x_178 = lean_usize_land(x_177, x_176);
x_179 = lean_array_uget(x_171, x_178);
x_180 = lean_box(2);
x_181 = l_Std_DHashMap_Internal_AssocList_get_x21___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__1(x_169, x_180, x_179);
x_182 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_182, 0, x_1);
lean_ctor_set(x_182, 1, x_181);
x_183 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__1(x_180, x_179);
if (x_183 == 0)
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; uint8_t x_193; 
x_184 = lean_unsigned_to_nat(1u);
x_185 = lean_nat_add(x_170, x_184);
lean_dec(x_170);
x_186 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_186, 0, x_180);
lean_ctor_set(x_186, 1, x_182);
lean_ctor_set(x_186, 2, x_179);
x_187 = lean_array_uset(x_171, x_178, x_186);
x_188 = lean_unsigned_to_nat(4u);
x_189 = lean_nat_mul(x_185, x_188);
x_190 = lean_unsigned_to_nat(3u);
x_191 = lean_nat_div(x_189, x_190);
lean_dec(x_189);
x_192 = lean_array_get_size(x_187);
x_193 = lean_nat_dec_le(x_191, x_192);
lean_dec(x_192);
lean_dec(x_191);
if (x_193 == 0)
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_194 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__2(x_187);
if (lean_is_scalar(x_172)) {
 x_195 = lean_alloc_ctor(0, 2, 0);
} else {
 x_195 = x_172;
}
lean_ctor_set(x_195, 0, x_185);
lean_ctor_set(x_195, 1, x_194);
if (lean_is_scalar(x_168)) {
 x_196 = lean_alloc_ctor(0, 2, 0);
} else {
 x_196 = x_168;
}
lean_ctor_set(x_196, 0, x_166);
lean_ctor_set(x_196, 1, x_195);
x_197 = lean_st_ref_set(x_2, x_196, x_165);
lean_dec(x_2);
x_198 = lean_ctor_get(x_197, 1);
lean_inc(x_198);
if (lean_is_exclusive(x_197)) {
 lean_ctor_release(x_197, 0);
 lean_ctor_release(x_197, 1);
 x_199 = x_197;
} else {
 lean_dec_ref(x_197);
 x_199 = lean_box(0);
}
x_200 = lean_box(0);
if (lean_is_scalar(x_199)) {
 x_201 = lean_alloc_ctor(0, 2, 0);
} else {
 x_201 = x_199;
}
lean_ctor_set(x_201, 0, x_200);
lean_ctor_set(x_201, 1, x_198);
return x_201;
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
if (lean_is_scalar(x_172)) {
 x_202 = lean_alloc_ctor(0, 2, 0);
} else {
 x_202 = x_172;
}
lean_ctor_set(x_202, 0, x_185);
lean_ctor_set(x_202, 1, x_187);
if (lean_is_scalar(x_168)) {
 x_203 = lean_alloc_ctor(0, 2, 0);
} else {
 x_203 = x_168;
}
lean_ctor_set(x_203, 0, x_166);
lean_ctor_set(x_203, 1, x_202);
x_204 = lean_st_ref_set(x_2, x_203, x_165);
lean_dec(x_2);
x_205 = lean_ctor_get(x_204, 1);
lean_inc(x_205);
if (lean_is_exclusive(x_204)) {
 lean_ctor_release(x_204, 0);
 lean_ctor_release(x_204, 1);
 x_206 = x_204;
} else {
 lean_dec_ref(x_204);
 x_206 = lean_box(0);
}
x_207 = lean_box(0);
if (lean_is_scalar(x_206)) {
 x_208 = lean_alloc_ctor(0, 2, 0);
} else {
 x_208 = x_206;
}
lean_ctor_set(x_208, 0, x_207);
lean_ctor_set(x_208, 1, x_205);
return x_208;
}
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; 
x_209 = lean_box(0);
x_210 = lean_array_uset(x_171, x_178, x_209);
x_211 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__5(x_180, x_182, x_179);
x_212 = lean_array_uset(x_210, x_178, x_211);
if (lean_is_scalar(x_172)) {
 x_213 = lean_alloc_ctor(0, 2, 0);
} else {
 x_213 = x_172;
}
lean_ctor_set(x_213, 0, x_170);
lean_ctor_set(x_213, 1, x_212);
if (lean_is_scalar(x_168)) {
 x_214 = lean_alloc_ctor(0, 2, 0);
} else {
 x_214 = x_168;
}
lean_ctor_set(x_214, 0, x_166);
lean_ctor_set(x_214, 1, x_213);
x_215 = lean_st_ref_set(x_2, x_214, x_165);
lean_dec(x_2);
x_216 = lean_ctor_get(x_215, 1);
lean_inc(x_216);
if (lean_is_exclusive(x_215)) {
 lean_ctor_release(x_215, 0);
 lean_ctor_release(x_215, 1);
 x_217 = x_215;
} else {
 lean_dec_ref(x_215);
 x_217 = lean_box(0);
}
x_218 = lean_box(0);
if (lean_is_scalar(x_217)) {
 x_219 = lean_alloc_ctor(0, 2, 0);
} else {
 x_219 = x_217;
}
lean_ctor_set(x_219, 0, x_218);
lean_ctor_set(x_219, 1, x_216);
return x_219;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x21___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__7(x_1, x_2, x_13, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__8(x_1, x_2, x_13, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__12(x_1, x_2, x_13, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__13___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__13(x_1, x_2, x_13, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__14___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__14(x_1, x_2, x_13, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__16___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__16(x_1, x_2, x_13, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__17___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__17(x_1, x_2, x_13, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_float_goFVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_st_ref_get(x_3, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
x_13 = !lean_is_exclusive(x_10);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint64_t x_18; uint64_t x_19; uint64_t x_20; uint64_t x_21; uint64_t x_22; uint64_t x_23; uint64_t x_24; size_t x_25; size_t x_26; size_t x_27; size_t x_28; size_t x_29; lean_object* x_30; lean_object* x_31; 
x_14 = lean_ctor_get(x_10, 1);
x_15 = lean_ctor_get(x_10, 0);
lean_dec(x_15);
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
lean_dec(x_12);
x_17 = lean_array_get_size(x_16);
x_18 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1724_(x_1);
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
x_30 = lean_array_uget(x_16, x_29);
lean_dec(x_16);
x_31 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__1(x_1, x_30);
lean_dec(x_30);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; 
lean_dec(x_2);
lean_dec(x_1);
x_32 = lean_box(0);
lean_ctor_set(x_10, 0, x_32);
return x_10;
}
else
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_31, 0);
lean_inc(x_33);
lean_dec(x_31);
x_34 = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_beqDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_62_(x_33, x_2);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
lean_dec(x_33);
lean_free_object(x_10);
lean_dec(x_2);
x_35 = lean_st_ref_take(x_3, x_14);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
lean_dec(x_35);
x_39 = !lean_is_exclusive(x_36);
if (x_39 == 0)
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_ctor_get(x_36, 0);
lean_dec(x_40);
x_41 = !lean_is_exclusive(x_37);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; size_t x_45; size_t x_46; size_t x_47; lean_object* x_48; uint8_t x_49; 
x_42 = lean_ctor_get(x_37, 0);
x_43 = lean_ctor_get(x_37, 1);
x_44 = lean_array_get_size(x_43);
x_45 = lean_usize_of_nat(x_44);
lean_dec(x_44);
x_46 = lean_usize_sub(x_45, x_27);
x_47 = lean_usize_land(x_25, x_46);
x_48 = lean_array_uget(x_43, x_47);
x_49 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__2(x_1, x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_50 = lean_unsigned_to_nat(1u);
x_51 = lean_nat_add(x_42, x_50);
lean_dec(x_42);
x_52 = lean_box(2);
x_53 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_53, 0, x_1);
lean_ctor_set(x_53, 1, x_52);
lean_ctor_set(x_53, 2, x_48);
x_54 = lean_array_uset(x_43, x_47, x_53);
x_55 = lean_unsigned_to_nat(4u);
x_56 = lean_nat_mul(x_51, x_55);
x_57 = lean_unsigned_to_nat(3u);
x_58 = lean_nat_div(x_56, x_57);
lean_dec(x_56);
x_59 = lean_array_get_size(x_54);
x_60 = lean_nat_dec_le(x_58, x_59);
lean_dec(x_59);
lean_dec(x_58);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_61 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__3(x_54);
lean_ctor_set(x_37, 1, x_61);
lean_ctor_set(x_37, 0, x_51);
x_62 = lean_st_ref_set(x_3, x_36, x_38);
x_63 = !lean_is_exclusive(x_62);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_62, 0);
lean_dec(x_64);
x_65 = lean_box(0);
lean_ctor_set(x_62, 0, x_65);
return x_62;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_62, 1);
lean_inc(x_66);
lean_dec(x_62);
x_67 = lean_box(0);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_66);
return x_68;
}
}
else
{
lean_object* x_69; uint8_t x_70; 
lean_ctor_set(x_37, 1, x_54);
lean_ctor_set(x_37, 0, x_51);
x_69 = lean_st_ref_set(x_3, x_36, x_38);
x_70 = !lean_is_exclusive(x_69);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_ctor_get(x_69, 0);
lean_dec(x_71);
x_72 = lean_box(0);
lean_ctor_set(x_69, 0, x_72);
return x_69;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_69, 1);
lean_inc(x_73);
lean_dec(x_69);
x_74 = lean_box(0);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_73);
return x_75;
}
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; 
x_76 = lean_box(0);
x_77 = lean_array_uset(x_43, x_47, x_76);
x_78 = lean_box(2);
x_79 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__6(x_1, x_78, x_48);
x_80 = lean_array_uset(x_77, x_47, x_79);
lean_ctor_set(x_37, 1, x_80);
x_81 = lean_st_ref_set(x_3, x_36, x_38);
x_82 = !lean_is_exclusive(x_81);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_81, 0);
lean_dec(x_83);
x_84 = lean_box(0);
lean_ctor_set(x_81, 0, x_84);
return x_81;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_81, 1);
lean_inc(x_85);
lean_dec(x_81);
x_86 = lean_box(0);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_85);
return x_87;
}
}
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; size_t x_91; size_t x_92; size_t x_93; lean_object* x_94; uint8_t x_95; 
x_88 = lean_ctor_get(x_37, 0);
x_89 = lean_ctor_get(x_37, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_37);
x_90 = lean_array_get_size(x_89);
x_91 = lean_usize_of_nat(x_90);
lean_dec(x_90);
x_92 = lean_usize_sub(x_91, x_27);
x_93 = lean_usize_land(x_25, x_92);
x_94 = lean_array_uget(x_89, x_93);
x_95 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__2(x_1, x_94);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; uint8_t x_106; 
x_96 = lean_unsigned_to_nat(1u);
x_97 = lean_nat_add(x_88, x_96);
lean_dec(x_88);
x_98 = lean_box(2);
x_99 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_99, 0, x_1);
lean_ctor_set(x_99, 1, x_98);
lean_ctor_set(x_99, 2, x_94);
x_100 = lean_array_uset(x_89, x_93, x_99);
x_101 = lean_unsigned_to_nat(4u);
x_102 = lean_nat_mul(x_97, x_101);
x_103 = lean_unsigned_to_nat(3u);
x_104 = lean_nat_div(x_102, x_103);
lean_dec(x_102);
x_105 = lean_array_get_size(x_100);
x_106 = lean_nat_dec_le(x_104, x_105);
lean_dec(x_105);
lean_dec(x_104);
if (x_106 == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_107 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__3(x_100);
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_97);
lean_ctor_set(x_108, 1, x_107);
lean_ctor_set(x_36, 0, x_108);
x_109 = lean_st_ref_set(x_3, x_36, x_38);
x_110 = lean_ctor_get(x_109, 1);
lean_inc(x_110);
if (lean_is_exclusive(x_109)) {
 lean_ctor_release(x_109, 0);
 lean_ctor_release(x_109, 1);
 x_111 = x_109;
} else {
 lean_dec_ref(x_109);
 x_111 = lean_box(0);
}
x_112 = lean_box(0);
if (lean_is_scalar(x_111)) {
 x_113 = lean_alloc_ctor(0, 2, 0);
} else {
 x_113 = x_111;
}
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_110);
return x_113;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_97);
lean_ctor_set(x_114, 1, x_100);
lean_ctor_set(x_36, 0, x_114);
x_115 = lean_st_ref_set(x_3, x_36, x_38);
x_116 = lean_ctor_get(x_115, 1);
lean_inc(x_116);
if (lean_is_exclusive(x_115)) {
 lean_ctor_release(x_115, 0);
 lean_ctor_release(x_115, 1);
 x_117 = x_115;
} else {
 lean_dec_ref(x_115);
 x_117 = lean_box(0);
}
x_118 = lean_box(0);
if (lean_is_scalar(x_117)) {
 x_119 = lean_alloc_ctor(0, 2, 0);
} else {
 x_119 = x_117;
}
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_116);
return x_119;
}
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_120 = lean_box(0);
x_121 = lean_array_uset(x_89, x_93, x_120);
x_122 = lean_box(2);
x_123 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__6(x_1, x_122, x_94);
x_124 = lean_array_uset(x_121, x_93, x_123);
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_88);
lean_ctor_set(x_125, 1, x_124);
lean_ctor_set(x_36, 0, x_125);
x_126 = lean_st_ref_set(x_3, x_36, x_38);
x_127 = lean_ctor_get(x_126, 1);
lean_inc(x_127);
if (lean_is_exclusive(x_126)) {
 lean_ctor_release(x_126, 0);
 lean_ctor_release(x_126, 1);
 x_128 = x_126;
} else {
 lean_dec_ref(x_126);
 x_128 = lean_box(0);
}
x_129 = lean_box(0);
if (lean_is_scalar(x_128)) {
 x_130 = lean_alloc_ctor(0, 2, 0);
} else {
 x_130 = x_128;
}
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_127);
return x_130;
}
}
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; size_t x_136; size_t x_137; size_t x_138; lean_object* x_139; uint8_t x_140; 
x_131 = lean_ctor_get(x_36, 1);
lean_inc(x_131);
lean_dec(x_36);
x_132 = lean_ctor_get(x_37, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_37, 1);
lean_inc(x_133);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_134 = x_37;
} else {
 lean_dec_ref(x_37);
 x_134 = lean_box(0);
}
x_135 = lean_array_get_size(x_133);
x_136 = lean_usize_of_nat(x_135);
lean_dec(x_135);
x_137 = lean_usize_sub(x_136, x_27);
x_138 = lean_usize_land(x_25, x_137);
x_139 = lean_array_uget(x_133, x_138);
x_140 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__2(x_1, x_139);
if (x_140 == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; uint8_t x_151; 
x_141 = lean_unsigned_to_nat(1u);
x_142 = lean_nat_add(x_132, x_141);
lean_dec(x_132);
x_143 = lean_box(2);
x_144 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_144, 0, x_1);
lean_ctor_set(x_144, 1, x_143);
lean_ctor_set(x_144, 2, x_139);
x_145 = lean_array_uset(x_133, x_138, x_144);
x_146 = lean_unsigned_to_nat(4u);
x_147 = lean_nat_mul(x_142, x_146);
x_148 = lean_unsigned_to_nat(3u);
x_149 = lean_nat_div(x_147, x_148);
lean_dec(x_147);
x_150 = lean_array_get_size(x_145);
x_151 = lean_nat_dec_le(x_149, x_150);
lean_dec(x_150);
lean_dec(x_149);
if (x_151 == 0)
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_152 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__3(x_145);
if (lean_is_scalar(x_134)) {
 x_153 = lean_alloc_ctor(0, 2, 0);
} else {
 x_153 = x_134;
}
lean_ctor_set(x_153, 0, x_142);
lean_ctor_set(x_153, 1, x_152);
x_154 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_154, 0, x_153);
lean_ctor_set(x_154, 1, x_131);
x_155 = lean_st_ref_set(x_3, x_154, x_38);
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
x_158 = lean_box(0);
if (lean_is_scalar(x_157)) {
 x_159 = lean_alloc_ctor(0, 2, 0);
} else {
 x_159 = x_157;
}
lean_ctor_set(x_159, 0, x_158);
lean_ctor_set(x_159, 1, x_156);
return x_159;
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
if (lean_is_scalar(x_134)) {
 x_160 = lean_alloc_ctor(0, 2, 0);
} else {
 x_160 = x_134;
}
lean_ctor_set(x_160, 0, x_142);
lean_ctor_set(x_160, 1, x_145);
x_161 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_161, 0, x_160);
lean_ctor_set(x_161, 1, x_131);
x_162 = lean_st_ref_set(x_3, x_161, x_38);
x_163 = lean_ctor_get(x_162, 1);
lean_inc(x_163);
if (lean_is_exclusive(x_162)) {
 lean_ctor_release(x_162, 0);
 lean_ctor_release(x_162, 1);
 x_164 = x_162;
} else {
 lean_dec_ref(x_162);
 x_164 = lean_box(0);
}
x_165 = lean_box(0);
if (lean_is_scalar(x_164)) {
 x_166 = lean_alloc_ctor(0, 2, 0);
} else {
 x_166 = x_164;
}
lean_ctor_set(x_166, 0, x_165);
lean_ctor_set(x_166, 1, x_163);
return x_166;
}
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_167 = lean_box(0);
x_168 = lean_array_uset(x_133, x_138, x_167);
x_169 = lean_box(2);
x_170 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__6(x_1, x_169, x_139);
x_171 = lean_array_uset(x_168, x_138, x_170);
if (lean_is_scalar(x_134)) {
 x_172 = lean_alloc_ctor(0, 2, 0);
} else {
 x_172 = x_134;
}
lean_ctor_set(x_172, 0, x_132);
lean_ctor_set(x_172, 1, x_171);
x_173 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_173, 0, x_172);
lean_ctor_set(x_173, 1, x_131);
x_174 = lean_st_ref_set(x_3, x_173, x_38);
x_175 = lean_ctor_get(x_174, 1);
lean_inc(x_175);
if (lean_is_exclusive(x_174)) {
 lean_ctor_release(x_174, 0);
 lean_ctor_release(x_174, 1);
 x_176 = x_174;
} else {
 lean_dec_ref(x_174);
 x_176 = lean_box(0);
}
x_177 = lean_box(0);
if (lean_is_scalar(x_176)) {
 x_178 = lean_alloc_ctor(0, 2, 0);
} else {
 x_178 = x_176;
}
lean_ctor_set(x_178, 0, x_177);
lean_ctor_set(x_178, 1, x_175);
return x_178;
}
}
}
else
{
lean_object* x_179; uint8_t x_180; 
x_179 = lean_box(3);
x_180 = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_beqDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_62_(x_33, x_179);
lean_dec(x_33);
if (x_180 == 0)
{
lean_object* x_181; 
lean_dec(x_2);
lean_dec(x_1);
x_181 = lean_box(0);
lean_ctor_set(x_10, 0, x_181);
return x_10;
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; uint8_t x_186; 
lean_free_object(x_10);
x_182 = lean_st_ref_take(x_3, x_14);
x_183 = lean_ctor_get(x_182, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_183, 0);
lean_inc(x_184);
x_185 = lean_ctor_get(x_182, 1);
lean_inc(x_185);
lean_dec(x_182);
x_186 = !lean_is_exclusive(x_183);
if (x_186 == 0)
{
lean_object* x_187; uint8_t x_188; 
x_187 = lean_ctor_get(x_183, 0);
lean_dec(x_187);
x_188 = !lean_is_exclusive(x_184);
if (x_188 == 0)
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; size_t x_192; size_t x_193; size_t x_194; lean_object* x_195; uint8_t x_196; 
x_189 = lean_ctor_get(x_184, 0);
x_190 = lean_ctor_get(x_184, 1);
x_191 = lean_array_get_size(x_190);
x_192 = lean_usize_of_nat(x_191);
lean_dec(x_191);
x_193 = lean_usize_sub(x_192, x_27);
x_194 = lean_usize_land(x_25, x_193);
x_195 = lean_array_uget(x_190, x_194);
x_196 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__2(x_1, x_195);
if (x_196 == 0)
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; uint8_t x_206; 
x_197 = lean_unsigned_to_nat(1u);
x_198 = lean_nat_add(x_189, x_197);
lean_dec(x_189);
x_199 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_199, 0, x_1);
lean_ctor_set(x_199, 1, x_2);
lean_ctor_set(x_199, 2, x_195);
x_200 = lean_array_uset(x_190, x_194, x_199);
x_201 = lean_unsigned_to_nat(4u);
x_202 = lean_nat_mul(x_198, x_201);
x_203 = lean_unsigned_to_nat(3u);
x_204 = lean_nat_div(x_202, x_203);
lean_dec(x_202);
x_205 = lean_array_get_size(x_200);
x_206 = lean_nat_dec_le(x_204, x_205);
lean_dec(x_205);
lean_dec(x_204);
if (x_206 == 0)
{
lean_object* x_207; lean_object* x_208; uint8_t x_209; 
x_207 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__3(x_200);
lean_ctor_set(x_184, 1, x_207);
lean_ctor_set(x_184, 0, x_198);
x_208 = lean_st_ref_set(x_3, x_183, x_185);
x_209 = !lean_is_exclusive(x_208);
if (x_209 == 0)
{
lean_object* x_210; lean_object* x_211; 
x_210 = lean_ctor_get(x_208, 0);
lean_dec(x_210);
x_211 = lean_box(0);
lean_ctor_set(x_208, 0, x_211);
return x_208;
}
else
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; 
x_212 = lean_ctor_get(x_208, 1);
lean_inc(x_212);
lean_dec(x_208);
x_213 = lean_box(0);
x_214 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_214, 0, x_213);
lean_ctor_set(x_214, 1, x_212);
return x_214;
}
}
else
{
lean_object* x_215; uint8_t x_216; 
lean_ctor_set(x_184, 1, x_200);
lean_ctor_set(x_184, 0, x_198);
x_215 = lean_st_ref_set(x_3, x_183, x_185);
x_216 = !lean_is_exclusive(x_215);
if (x_216 == 0)
{
lean_object* x_217; lean_object* x_218; 
x_217 = lean_ctor_get(x_215, 0);
lean_dec(x_217);
x_218 = lean_box(0);
lean_ctor_set(x_215, 0, x_218);
return x_215;
}
else
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; 
x_219 = lean_ctor_get(x_215, 1);
lean_inc(x_219);
lean_dec(x_215);
x_220 = lean_box(0);
x_221 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_221, 0, x_220);
lean_ctor_set(x_221, 1, x_219);
return x_221;
}
}
}
else
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; uint8_t x_227; 
x_222 = lean_box(0);
x_223 = lean_array_uset(x_190, x_194, x_222);
x_224 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__6(x_1, x_2, x_195);
x_225 = lean_array_uset(x_223, x_194, x_224);
lean_ctor_set(x_184, 1, x_225);
x_226 = lean_st_ref_set(x_3, x_183, x_185);
x_227 = !lean_is_exclusive(x_226);
if (x_227 == 0)
{
lean_object* x_228; lean_object* x_229; 
x_228 = lean_ctor_get(x_226, 0);
lean_dec(x_228);
x_229 = lean_box(0);
lean_ctor_set(x_226, 0, x_229);
return x_226;
}
else
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; 
x_230 = lean_ctor_get(x_226, 1);
lean_inc(x_230);
lean_dec(x_226);
x_231 = lean_box(0);
x_232 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_232, 0, x_231);
lean_ctor_set(x_232, 1, x_230);
return x_232;
}
}
}
else
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; size_t x_236; size_t x_237; size_t x_238; lean_object* x_239; uint8_t x_240; 
x_233 = lean_ctor_get(x_184, 0);
x_234 = lean_ctor_get(x_184, 1);
lean_inc(x_234);
lean_inc(x_233);
lean_dec(x_184);
x_235 = lean_array_get_size(x_234);
x_236 = lean_usize_of_nat(x_235);
lean_dec(x_235);
x_237 = lean_usize_sub(x_236, x_27);
x_238 = lean_usize_land(x_25, x_237);
x_239 = lean_array_uget(x_234, x_238);
x_240 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__2(x_1, x_239);
if (x_240 == 0)
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; uint8_t x_250; 
x_241 = lean_unsigned_to_nat(1u);
x_242 = lean_nat_add(x_233, x_241);
lean_dec(x_233);
x_243 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_243, 0, x_1);
lean_ctor_set(x_243, 1, x_2);
lean_ctor_set(x_243, 2, x_239);
x_244 = lean_array_uset(x_234, x_238, x_243);
x_245 = lean_unsigned_to_nat(4u);
x_246 = lean_nat_mul(x_242, x_245);
x_247 = lean_unsigned_to_nat(3u);
x_248 = lean_nat_div(x_246, x_247);
lean_dec(x_246);
x_249 = lean_array_get_size(x_244);
x_250 = lean_nat_dec_le(x_248, x_249);
lean_dec(x_249);
lean_dec(x_248);
if (x_250 == 0)
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; 
x_251 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__3(x_244);
x_252 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_252, 0, x_242);
lean_ctor_set(x_252, 1, x_251);
lean_ctor_set(x_183, 0, x_252);
x_253 = lean_st_ref_set(x_3, x_183, x_185);
x_254 = lean_ctor_get(x_253, 1);
lean_inc(x_254);
if (lean_is_exclusive(x_253)) {
 lean_ctor_release(x_253, 0);
 lean_ctor_release(x_253, 1);
 x_255 = x_253;
} else {
 lean_dec_ref(x_253);
 x_255 = lean_box(0);
}
x_256 = lean_box(0);
if (lean_is_scalar(x_255)) {
 x_257 = lean_alloc_ctor(0, 2, 0);
} else {
 x_257 = x_255;
}
lean_ctor_set(x_257, 0, x_256);
lean_ctor_set(x_257, 1, x_254);
return x_257;
}
else
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; 
x_258 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_258, 0, x_242);
lean_ctor_set(x_258, 1, x_244);
lean_ctor_set(x_183, 0, x_258);
x_259 = lean_st_ref_set(x_3, x_183, x_185);
x_260 = lean_ctor_get(x_259, 1);
lean_inc(x_260);
if (lean_is_exclusive(x_259)) {
 lean_ctor_release(x_259, 0);
 lean_ctor_release(x_259, 1);
 x_261 = x_259;
} else {
 lean_dec_ref(x_259);
 x_261 = lean_box(0);
}
x_262 = lean_box(0);
if (lean_is_scalar(x_261)) {
 x_263 = lean_alloc_ctor(0, 2, 0);
} else {
 x_263 = x_261;
}
lean_ctor_set(x_263, 0, x_262);
lean_ctor_set(x_263, 1, x_260);
return x_263;
}
}
else
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; 
x_264 = lean_box(0);
x_265 = lean_array_uset(x_234, x_238, x_264);
x_266 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__6(x_1, x_2, x_239);
x_267 = lean_array_uset(x_265, x_238, x_266);
x_268 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_268, 0, x_233);
lean_ctor_set(x_268, 1, x_267);
lean_ctor_set(x_183, 0, x_268);
x_269 = lean_st_ref_set(x_3, x_183, x_185);
x_270 = lean_ctor_get(x_269, 1);
lean_inc(x_270);
if (lean_is_exclusive(x_269)) {
 lean_ctor_release(x_269, 0);
 lean_ctor_release(x_269, 1);
 x_271 = x_269;
} else {
 lean_dec_ref(x_269);
 x_271 = lean_box(0);
}
x_272 = lean_box(0);
if (lean_is_scalar(x_271)) {
 x_273 = lean_alloc_ctor(0, 2, 0);
} else {
 x_273 = x_271;
}
lean_ctor_set(x_273, 0, x_272);
lean_ctor_set(x_273, 1, x_270);
return x_273;
}
}
}
else
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; size_t x_279; size_t x_280; size_t x_281; lean_object* x_282; uint8_t x_283; 
x_274 = lean_ctor_get(x_183, 1);
lean_inc(x_274);
lean_dec(x_183);
x_275 = lean_ctor_get(x_184, 0);
lean_inc(x_275);
x_276 = lean_ctor_get(x_184, 1);
lean_inc(x_276);
if (lean_is_exclusive(x_184)) {
 lean_ctor_release(x_184, 0);
 lean_ctor_release(x_184, 1);
 x_277 = x_184;
} else {
 lean_dec_ref(x_184);
 x_277 = lean_box(0);
}
x_278 = lean_array_get_size(x_276);
x_279 = lean_usize_of_nat(x_278);
lean_dec(x_278);
x_280 = lean_usize_sub(x_279, x_27);
x_281 = lean_usize_land(x_25, x_280);
x_282 = lean_array_uget(x_276, x_281);
x_283 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__2(x_1, x_282);
if (x_283 == 0)
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; uint8_t x_293; 
x_284 = lean_unsigned_to_nat(1u);
x_285 = lean_nat_add(x_275, x_284);
lean_dec(x_275);
x_286 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_286, 0, x_1);
lean_ctor_set(x_286, 1, x_2);
lean_ctor_set(x_286, 2, x_282);
x_287 = lean_array_uset(x_276, x_281, x_286);
x_288 = lean_unsigned_to_nat(4u);
x_289 = lean_nat_mul(x_285, x_288);
x_290 = lean_unsigned_to_nat(3u);
x_291 = lean_nat_div(x_289, x_290);
lean_dec(x_289);
x_292 = lean_array_get_size(x_287);
x_293 = lean_nat_dec_le(x_291, x_292);
lean_dec(x_292);
lean_dec(x_291);
if (x_293 == 0)
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; 
x_294 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__3(x_287);
if (lean_is_scalar(x_277)) {
 x_295 = lean_alloc_ctor(0, 2, 0);
} else {
 x_295 = x_277;
}
lean_ctor_set(x_295, 0, x_285);
lean_ctor_set(x_295, 1, x_294);
x_296 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_296, 0, x_295);
lean_ctor_set(x_296, 1, x_274);
x_297 = lean_st_ref_set(x_3, x_296, x_185);
x_298 = lean_ctor_get(x_297, 1);
lean_inc(x_298);
if (lean_is_exclusive(x_297)) {
 lean_ctor_release(x_297, 0);
 lean_ctor_release(x_297, 1);
 x_299 = x_297;
} else {
 lean_dec_ref(x_297);
 x_299 = lean_box(0);
}
x_300 = lean_box(0);
if (lean_is_scalar(x_299)) {
 x_301 = lean_alloc_ctor(0, 2, 0);
} else {
 x_301 = x_299;
}
lean_ctor_set(x_301, 0, x_300);
lean_ctor_set(x_301, 1, x_298);
return x_301;
}
else
{
lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; 
if (lean_is_scalar(x_277)) {
 x_302 = lean_alloc_ctor(0, 2, 0);
} else {
 x_302 = x_277;
}
lean_ctor_set(x_302, 0, x_285);
lean_ctor_set(x_302, 1, x_287);
x_303 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_303, 0, x_302);
lean_ctor_set(x_303, 1, x_274);
x_304 = lean_st_ref_set(x_3, x_303, x_185);
x_305 = lean_ctor_get(x_304, 1);
lean_inc(x_305);
if (lean_is_exclusive(x_304)) {
 lean_ctor_release(x_304, 0);
 lean_ctor_release(x_304, 1);
 x_306 = x_304;
} else {
 lean_dec_ref(x_304);
 x_306 = lean_box(0);
}
x_307 = lean_box(0);
if (lean_is_scalar(x_306)) {
 x_308 = lean_alloc_ctor(0, 2, 0);
} else {
 x_308 = x_306;
}
lean_ctor_set(x_308, 0, x_307);
lean_ctor_set(x_308, 1, x_305);
return x_308;
}
}
else
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; 
x_309 = lean_box(0);
x_310 = lean_array_uset(x_276, x_281, x_309);
x_311 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__6(x_1, x_2, x_282);
x_312 = lean_array_uset(x_310, x_281, x_311);
if (lean_is_scalar(x_277)) {
 x_313 = lean_alloc_ctor(0, 2, 0);
} else {
 x_313 = x_277;
}
lean_ctor_set(x_313, 0, x_275);
lean_ctor_set(x_313, 1, x_312);
x_314 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_314, 0, x_313);
lean_ctor_set(x_314, 1, x_274);
x_315 = lean_st_ref_set(x_3, x_314, x_185);
x_316 = lean_ctor_get(x_315, 1);
lean_inc(x_316);
if (lean_is_exclusive(x_315)) {
 lean_ctor_release(x_315, 0);
 lean_ctor_release(x_315, 1);
 x_317 = x_315;
} else {
 lean_dec_ref(x_315);
 x_317 = lean_box(0);
}
x_318 = lean_box(0);
if (lean_is_scalar(x_317)) {
 x_319 = lean_alloc_ctor(0, 2, 0);
} else {
 x_319 = x_317;
}
lean_ctor_set(x_319, 0, x_318);
lean_ctor_set(x_319, 1, x_316);
return x_319;
}
}
}
}
}
}
else
{
lean_object* x_320; lean_object* x_321; lean_object* x_322; uint64_t x_323; uint64_t x_324; uint64_t x_325; uint64_t x_326; uint64_t x_327; uint64_t x_328; uint64_t x_329; size_t x_330; size_t x_331; size_t x_332; size_t x_333; size_t x_334; lean_object* x_335; lean_object* x_336; 
x_320 = lean_ctor_get(x_10, 1);
lean_inc(x_320);
lean_dec(x_10);
x_321 = lean_ctor_get(x_12, 1);
lean_inc(x_321);
lean_dec(x_12);
x_322 = lean_array_get_size(x_321);
x_323 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1724_(x_1);
x_324 = 32;
x_325 = lean_uint64_shift_right(x_323, x_324);
x_326 = lean_uint64_xor(x_323, x_325);
x_327 = 16;
x_328 = lean_uint64_shift_right(x_326, x_327);
x_329 = lean_uint64_xor(x_326, x_328);
x_330 = lean_uint64_to_usize(x_329);
x_331 = lean_usize_of_nat(x_322);
lean_dec(x_322);
x_332 = 1;
x_333 = lean_usize_sub(x_331, x_332);
x_334 = lean_usize_land(x_330, x_333);
x_335 = lean_array_uget(x_321, x_334);
lean_dec(x_321);
x_336 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__1(x_1, x_335);
lean_dec(x_335);
if (lean_obj_tag(x_336) == 0)
{
lean_object* x_337; lean_object* x_338; 
lean_dec(x_2);
lean_dec(x_1);
x_337 = lean_box(0);
x_338 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_338, 0, x_337);
lean_ctor_set(x_338, 1, x_320);
return x_338;
}
else
{
lean_object* x_339; uint8_t x_340; 
x_339 = lean_ctor_get(x_336, 0);
lean_inc(x_339);
lean_dec(x_336);
x_340 = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_beqDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_62_(x_339, x_2);
if (x_340 == 0)
{
lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; size_t x_351; size_t x_352; size_t x_353; lean_object* x_354; uint8_t x_355; 
lean_dec(x_339);
lean_dec(x_2);
x_341 = lean_st_ref_take(x_3, x_320);
x_342 = lean_ctor_get(x_341, 0);
lean_inc(x_342);
x_343 = lean_ctor_get(x_342, 0);
lean_inc(x_343);
x_344 = lean_ctor_get(x_341, 1);
lean_inc(x_344);
lean_dec(x_341);
x_345 = lean_ctor_get(x_342, 1);
lean_inc(x_345);
if (lean_is_exclusive(x_342)) {
 lean_ctor_release(x_342, 0);
 lean_ctor_release(x_342, 1);
 x_346 = x_342;
} else {
 lean_dec_ref(x_342);
 x_346 = lean_box(0);
}
x_347 = lean_ctor_get(x_343, 0);
lean_inc(x_347);
x_348 = lean_ctor_get(x_343, 1);
lean_inc(x_348);
if (lean_is_exclusive(x_343)) {
 lean_ctor_release(x_343, 0);
 lean_ctor_release(x_343, 1);
 x_349 = x_343;
} else {
 lean_dec_ref(x_343);
 x_349 = lean_box(0);
}
x_350 = lean_array_get_size(x_348);
x_351 = lean_usize_of_nat(x_350);
lean_dec(x_350);
x_352 = lean_usize_sub(x_351, x_332);
x_353 = lean_usize_land(x_330, x_352);
x_354 = lean_array_uget(x_348, x_353);
x_355 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__2(x_1, x_354);
if (x_355 == 0)
{
lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; uint8_t x_366; 
x_356 = lean_unsigned_to_nat(1u);
x_357 = lean_nat_add(x_347, x_356);
lean_dec(x_347);
x_358 = lean_box(2);
x_359 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_359, 0, x_1);
lean_ctor_set(x_359, 1, x_358);
lean_ctor_set(x_359, 2, x_354);
x_360 = lean_array_uset(x_348, x_353, x_359);
x_361 = lean_unsigned_to_nat(4u);
x_362 = lean_nat_mul(x_357, x_361);
x_363 = lean_unsigned_to_nat(3u);
x_364 = lean_nat_div(x_362, x_363);
lean_dec(x_362);
x_365 = lean_array_get_size(x_360);
x_366 = lean_nat_dec_le(x_364, x_365);
lean_dec(x_365);
lean_dec(x_364);
if (x_366 == 0)
{
lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; 
x_367 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__3(x_360);
if (lean_is_scalar(x_349)) {
 x_368 = lean_alloc_ctor(0, 2, 0);
} else {
 x_368 = x_349;
}
lean_ctor_set(x_368, 0, x_357);
lean_ctor_set(x_368, 1, x_367);
if (lean_is_scalar(x_346)) {
 x_369 = lean_alloc_ctor(0, 2, 0);
} else {
 x_369 = x_346;
}
lean_ctor_set(x_369, 0, x_368);
lean_ctor_set(x_369, 1, x_345);
x_370 = lean_st_ref_set(x_3, x_369, x_344);
x_371 = lean_ctor_get(x_370, 1);
lean_inc(x_371);
if (lean_is_exclusive(x_370)) {
 lean_ctor_release(x_370, 0);
 lean_ctor_release(x_370, 1);
 x_372 = x_370;
} else {
 lean_dec_ref(x_370);
 x_372 = lean_box(0);
}
x_373 = lean_box(0);
if (lean_is_scalar(x_372)) {
 x_374 = lean_alloc_ctor(0, 2, 0);
} else {
 x_374 = x_372;
}
lean_ctor_set(x_374, 0, x_373);
lean_ctor_set(x_374, 1, x_371);
return x_374;
}
else
{
lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; 
if (lean_is_scalar(x_349)) {
 x_375 = lean_alloc_ctor(0, 2, 0);
} else {
 x_375 = x_349;
}
lean_ctor_set(x_375, 0, x_357);
lean_ctor_set(x_375, 1, x_360);
if (lean_is_scalar(x_346)) {
 x_376 = lean_alloc_ctor(0, 2, 0);
} else {
 x_376 = x_346;
}
lean_ctor_set(x_376, 0, x_375);
lean_ctor_set(x_376, 1, x_345);
x_377 = lean_st_ref_set(x_3, x_376, x_344);
x_378 = lean_ctor_get(x_377, 1);
lean_inc(x_378);
if (lean_is_exclusive(x_377)) {
 lean_ctor_release(x_377, 0);
 lean_ctor_release(x_377, 1);
 x_379 = x_377;
} else {
 lean_dec_ref(x_377);
 x_379 = lean_box(0);
}
x_380 = lean_box(0);
if (lean_is_scalar(x_379)) {
 x_381 = lean_alloc_ctor(0, 2, 0);
} else {
 x_381 = x_379;
}
lean_ctor_set(x_381, 0, x_380);
lean_ctor_set(x_381, 1, x_378);
return x_381;
}
}
else
{
lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; 
x_382 = lean_box(0);
x_383 = lean_array_uset(x_348, x_353, x_382);
x_384 = lean_box(2);
x_385 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__6(x_1, x_384, x_354);
x_386 = lean_array_uset(x_383, x_353, x_385);
if (lean_is_scalar(x_349)) {
 x_387 = lean_alloc_ctor(0, 2, 0);
} else {
 x_387 = x_349;
}
lean_ctor_set(x_387, 0, x_347);
lean_ctor_set(x_387, 1, x_386);
if (lean_is_scalar(x_346)) {
 x_388 = lean_alloc_ctor(0, 2, 0);
} else {
 x_388 = x_346;
}
lean_ctor_set(x_388, 0, x_387);
lean_ctor_set(x_388, 1, x_345);
x_389 = lean_st_ref_set(x_3, x_388, x_344);
x_390 = lean_ctor_get(x_389, 1);
lean_inc(x_390);
if (lean_is_exclusive(x_389)) {
 lean_ctor_release(x_389, 0);
 lean_ctor_release(x_389, 1);
 x_391 = x_389;
} else {
 lean_dec_ref(x_389);
 x_391 = lean_box(0);
}
x_392 = lean_box(0);
if (lean_is_scalar(x_391)) {
 x_393 = lean_alloc_ctor(0, 2, 0);
} else {
 x_393 = x_391;
}
lean_ctor_set(x_393, 0, x_392);
lean_ctor_set(x_393, 1, x_390);
return x_393;
}
}
else
{
lean_object* x_394; uint8_t x_395; 
x_394 = lean_box(3);
x_395 = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_beqDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_62_(x_339, x_394);
lean_dec(x_339);
if (x_395 == 0)
{
lean_object* x_396; lean_object* x_397; 
lean_dec(x_2);
lean_dec(x_1);
x_396 = lean_box(0);
x_397 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_397, 0, x_396);
lean_ctor_set(x_397, 1, x_320);
return x_397;
}
else
{
lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; size_t x_408; size_t x_409; size_t x_410; lean_object* x_411; uint8_t x_412; 
x_398 = lean_st_ref_take(x_3, x_320);
x_399 = lean_ctor_get(x_398, 0);
lean_inc(x_399);
x_400 = lean_ctor_get(x_399, 0);
lean_inc(x_400);
x_401 = lean_ctor_get(x_398, 1);
lean_inc(x_401);
lean_dec(x_398);
x_402 = lean_ctor_get(x_399, 1);
lean_inc(x_402);
if (lean_is_exclusive(x_399)) {
 lean_ctor_release(x_399, 0);
 lean_ctor_release(x_399, 1);
 x_403 = x_399;
} else {
 lean_dec_ref(x_399);
 x_403 = lean_box(0);
}
x_404 = lean_ctor_get(x_400, 0);
lean_inc(x_404);
x_405 = lean_ctor_get(x_400, 1);
lean_inc(x_405);
if (lean_is_exclusive(x_400)) {
 lean_ctor_release(x_400, 0);
 lean_ctor_release(x_400, 1);
 x_406 = x_400;
} else {
 lean_dec_ref(x_400);
 x_406 = lean_box(0);
}
x_407 = lean_array_get_size(x_405);
x_408 = lean_usize_of_nat(x_407);
lean_dec(x_407);
x_409 = lean_usize_sub(x_408, x_332);
x_410 = lean_usize_land(x_330, x_409);
x_411 = lean_array_uget(x_405, x_410);
x_412 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__2(x_1, x_411);
if (x_412 == 0)
{
lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; uint8_t x_422; 
x_413 = lean_unsigned_to_nat(1u);
x_414 = lean_nat_add(x_404, x_413);
lean_dec(x_404);
x_415 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_415, 0, x_1);
lean_ctor_set(x_415, 1, x_2);
lean_ctor_set(x_415, 2, x_411);
x_416 = lean_array_uset(x_405, x_410, x_415);
x_417 = lean_unsigned_to_nat(4u);
x_418 = lean_nat_mul(x_414, x_417);
x_419 = lean_unsigned_to_nat(3u);
x_420 = lean_nat_div(x_418, x_419);
lean_dec(x_418);
x_421 = lean_array_get_size(x_416);
x_422 = lean_nat_dec_le(x_420, x_421);
lean_dec(x_421);
lean_dec(x_420);
if (x_422 == 0)
{
lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; 
x_423 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__3(x_416);
if (lean_is_scalar(x_406)) {
 x_424 = lean_alloc_ctor(0, 2, 0);
} else {
 x_424 = x_406;
}
lean_ctor_set(x_424, 0, x_414);
lean_ctor_set(x_424, 1, x_423);
if (lean_is_scalar(x_403)) {
 x_425 = lean_alloc_ctor(0, 2, 0);
} else {
 x_425 = x_403;
}
lean_ctor_set(x_425, 0, x_424);
lean_ctor_set(x_425, 1, x_402);
x_426 = lean_st_ref_set(x_3, x_425, x_401);
x_427 = lean_ctor_get(x_426, 1);
lean_inc(x_427);
if (lean_is_exclusive(x_426)) {
 lean_ctor_release(x_426, 0);
 lean_ctor_release(x_426, 1);
 x_428 = x_426;
} else {
 lean_dec_ref(x_426);
 x_428 = lean_box(0);
}
x_429 = lean_box(0);
if (lean_is_scalar(x_428)) {
 x_430 = lean_alloc_ctor(0, 2, 0);
} else {
 x_430 = x_428;
}
lean_ctor_set(x_430, 0, x_429);
lean_ctor_set(x_430, 1, x_427);
return x_430;
}
else
{
lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; 
if (lean_is_scalar(x_406)) {
 x_431 = lean_alloc_ctor(0, 2, 0);
} else {
 x_431 = x_406;
}
lean_ctor_set(x_431, 0, x_414);
lean_ctor_set(x_431, 1, x_416);
if (lean_is_scalar(x_403)) {
 x_432 = lean_alloc_ctor(0, 2, 0);
} else {
 x_432 = x_403;
}
lean_ctor_set(x_432, 0, x_431);
lean_ctor_set(x_432, 1, x_402);
x_433 = lean_st_ref_set(x_3, x_432, x_401);
x_434 = lean_ctor_get(x_433, 1);
lean_inc(x_434);
if (lean_is_exclusive(x_433)) {
 lean_ctor_release(x_433, 0);
 lean_ctor_release(x_433, 1);
 x_435 = x_433;
} else {
 lean_dec_ref(x_433);
 x_435 = lean_box(0);
}
x_436 = lean_box(0);
if (lean_is_scalar(x_435)) {
 x_437 = lean_alloc_ctor(0, 2, 0);
} else {
 x_437 = x_435;
}
lean_ctor_set(x_437, 0, x_436);
lean_ctor_set(x_437, 1, x_434);
return x_437;
}
}
else
{
lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; 
x_438 = lean_box(0);
x_439 = lean_array_uset(x_405, x_410, x_438);
x_440 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__6(x_1, x_2, x_411);
x_441 = lean_array_uset(x_439, x_410, x_440);
if (lean_is_scalar(x_406)) {
 x_442 = lean_alloc_ctor(0, 2, 0);
} else {
 x_442 = x_406;
}
lean_ctor_set(x_442, 0, x_404);
lean_ctor_set(x_442, 1, x_441);
if (lean_is_scalar(x_403)) {
 x_443 = lean_alloc_ctor(0, 2, 0);
} else {
 x_443 = x_403;
}
lean_ctor_set(x_443, 0, x_442);
lean_ctor_set(x_443, 1, x_402);
x_444 = lean_st_ref_set(x_3, x_443, x_401);
x_445 = lean_ctor_get(x_444, 1);
lean_inc(x_445);
if (lean_is_exclusive(x_444)) {
 lean_ctor_release(x_444, 0);
 lean_ctor_release(x_444, 1);
 x_446 = x_444;
} else {
 lean_dec_ref(x_444);
 x_446 = lean_box(0);
}
x_447 = lean_box(0);
if (lean_is_scalar(x_446)) {
 x_448 = lean_alloc_ctor(0, 2, 0);
} else {
 x_448 = x_446;
}
lean_ctor_set(x_448, 0, x_447);
lean_ctor_set(x_448, 1, x_445);
return x_448;
}
}
}
}
}
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at_Lean_Compiler_LCNF_FloatLetIn_float___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x21___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__1___closed__4;
x_5 = l_panic___rarg(x_1, x_4);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_float___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_FloatLetIn_float_goFVar(x_2, x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_float(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint64_t x_16; uint64_t x_17; uint64_t x_18; uint64_t x_19; uint64_t x_20; uint64_t x_21; uint64_t x_22; size_t x_23; size_t x_24; size_t x_25; size_t x_26; size_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_255; 
x_9 = lean_st_ref_get(x_2, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Compiler_LCNF_CodeDecl_fvarId(x_1);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_array_get_size(x_14);
x_16 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1724_(x_13);
x_17 = 32;
x_18 = lean_uint64_shift_right(x_16, x_17);
x_19 = lean_uint64_xor(x_16, x_18);
x_20 = 16;
x_21 = lean_uint64_shift_right(x_19, x_20);
x_22 = lean_uint64_xor(x_19, x_21);
x_23 = lean_uint64_to_usize(x_22);
x_24 = lean_usize_of_nat(x_15);
lean_dec(x_15);
x_25 = 1;
x_26 = lean_usize_sub(x_24, x_25);
x_27 = lean_usize_land(x_23, x_26);
x_28 = lean_array_uget(x_14, x_27);
lean_dec(x_14);
x_29 = l_Lean_Compiler_LCNF_FloatLetIn_instInhabitedDecision;
x_30 = l_Std_DHashMap_Internal_AssocList_get_x21___at_Lean_Compiler_LCNF_FloatLetIn_float___spec__1(x_29, x_13, x_28);
lean_dec(x_28);
lean_dec(x_13);
lean_inc(x_30);
x_255 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_FloatLetIn_float___lambda__1___boxed), 9, 1);
lean_closure_set(x_255, 0, x_30);
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_256; lean_object* x_257; 
x_256 = lean_ctor_get(x_1, 0);
lean_inc(x_256);
lean_inc(x_2);
x_257 = l_Lean_Compiler_LCNF_LetDecl_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__2(x_255, x_256, x_2, x_3, x_4, x_5, x_6, x_7, x_11);
if (lean_obj_tag(x_257) == 0)
{
lean_object* x_258; 
x_258 = lean_ctor_get(x_257, 1);
lean_inc(x_258);
lean_dec(x_257);
x_31 = x_258;
goto block_254;
}
else
{
uint8_t x_259; 
lean_dec(x_30);
lean_dec(x_2);
lean_dec(x_1);
x_259 = !lean_is_exclusive(x_257);
if (x_259 == 0)
{
return x_257;
}
else
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; 
x_260 = lean_ctor_get(x_257, 0);
x_261 = lean_ctor_get(x_257, 1);
lean_inc(x_261);
lean_inc(x_260);
lean_dec(x_257);
x_262 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_262, 0, x_260);
lean_ctor_set(x_262, 1, x_261);
return x_262;
}
}
}
else
{
lean_object* x_263; lean_object* x_264; 
x_263 = lean_ctor_get(x_1, 0);
lean_inc(x_263);
lean_inc(x_2);
x_264 = l_Lean_Compiler_LCNF_FunDecl_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__9(x_255, x_263, x_2, x_3, x_4, x_5, x_6, x_7, x_11);
if (lean_obj_tag(x_264) == 0)
{
lean_object* x_265; 
x_265 = lean_ctor_get(x_264, 1);
lean_inc(x_265);
lean_dec(x_264);
x_31 = x_265;
goto block_254;
}
else
{
uint8_t x_266; 
lean_dec(x_30);
lean_dec(x_2);
lean_dec(x_1);
x_266 = !lean_is_exclusive(x_264);
if (x_266 == 0)
{
return x_264;
}
else
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; 
x_267 = lean_ctor_get(x_264, 0);
x_268 = lean_ctor_get(x_264, 1);
lean_inc(x_268);
lean_inc(x_267);
lean_dec(x_264);
x_269 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_269, 0, x_267);
lean_ctor_set(x_269, 1, x_268);
return x_269;
}
}
}
block_254:
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_st_ref_take(x_2, x_31);
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; uint8_t x_35; 
x_34 = lean_ctor_get(x_32, 0);
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_36 = lean_ctor_get(x_32, 1);
x_37 = lean_ctor_get(x_34, 1);
x_38 = lean_box(0);
x_39 = !lean_is_exclusive(x_37);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; uint64_t x_43; uint64_t x_44; uint64_t x_45; uint64_t x_46; uint64_t x_47; size_t x_48; size_t x_49; size_t x_50; size_t x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_40 = lean_ctor_get(x_37, 0);
x_41 = lean_ctor_get(x_37, 1);
x_42 = lean_array_get_size(x_41);
x_43 = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_hashDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_15_(x_30);
x_44 = lean_uint64_shift_right(x_43, x_17);
x_45 = lean_uint64_xor(x_43, x_44);
x_46 = lean_uint64_shift_right(x_45, x_20);
x_47 = lean_uint64_xor(x_45, x_46);
x_48 = lean_uint64_to_usize(x_47);
x_49 = lean_usize_of_nat(x_42);
lean_dec(x_42);
x_50 = lean_usize_sub(x_49, x_25);
x_51 = lean_usize_land(x_48, x_50);
x_52 = lean_array_uget(x_41, x_51);
x_53 = l_Std_DHashMap_Internal_AssocList_get_x21___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__1(x_38, x_30, x_52);
lean_ctor_set_tag(x_32, 1);
lean_ctor_set(x_32, 1, x_53);
lean_ctor_set(x_32, 0, x_1);
x_54 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__1(x_30, x_52);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_55 = lean_unsigned_to_nat(1u);
x_56 = lean_nat_add(x_40, x_55);
lean_dec(x_40);
x_57 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_57, 0, x_30);
lean_ctor_set(x_57, 1, x_32);
lean_ctor_set(x_57, 2, x_52);
x_58 = lean_array_uset(x_41, x_51, x_57);
x_59 = lean_unsigned_to_nat(4u);
x_60 = lean_nat_mul(x_56, x_59);
x_61 = lean_unsigned_to_nat(3u);
x_62 = lean_nat_div(x_60, x_61);
lean_dec(x_60);
x_63 = lean_array_get_size(x_58);
x_64 = lean_nat_dec_le(x_62, x_63);
lean_dec(x_63);
lean_dec(x_62);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_65 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__2(x_58);
lean_ctor_set(x_37, 1, x_65);
lean_ctor_set(x_37, 0, x_56);
x_66 = lean_st_ref_set(x_2, x_34, x_36);
lean_dec(x_2);
x_67 = !lean_is_exclusive(x_66);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_66, 0);
lean_dec(x_68);
x_69 = lean_box(0);
lean_ctor_set(x_66, 0, x_69);
return x_66;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_66, 1);
lean_inc(x_70);
lean_dec(x_66);
x_71 = lean_box(0);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_70);
return x_72;
}
}
else
{
lean_object* x_73; uint8_t x_74; 
lean_ctor_set(x_37, 1, x_58);
lean_ctor_set(x_37, 0, x_56);
x_73 = lean_st_ref_set(x_2, x_34, x_36);
lean_dec(x_2);
x_74 = !lean_is_exclusive(x_73);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_73, 0);
lean_dec(x_75);
x_76 = lean_box(0);
lean_ctor_set(x_73, 0, x_76);
return x_73;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_73, 1);
lean_inc(x_77);
lean_dec(x_73);
x_78 = lean_box(0);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_77);
return x_79;
}
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; 
x_80 = lean_box(0);
x_81 = lean_array_uset(x_41, x_51, x_80);
x_82 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__5(x_30, x_32, x_52);
x_83 = lean_array_uset(x_81, x_51, x_82);
lean_ctor_set(x_37, 1, x_83);
x_84 = lean_st_ref_set(x_2, x_34, x_36);
lean_dec(x_2);
x_85 = !lean_is_exclusive(x_84);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_ctor_get(x_84, 0);
lean_dec(x_86);
x_87 = lean_box(0);
lean_ctor_set(x_84, 0, x_87);
return x_84;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_84, 1);
lean_inc(x_88);
lean_dec(x_84);
x_89 = lean_box(0);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_88);
return x_90;
}
}
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; uint64_t x_94; uint64_t x_95; uint64_t x_96; uint64_t x_97; uint64_t x_98; size_t x_99; size_t x_100; size_t x_101; size_t x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; 
x_91 = lean_ctor_get(x_37, 0);
x_92 = lean_ctor_get(x_37, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_37);
x_93 = lean_array_get_size(x_92);
x_94 = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_hashDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_15_(x_30);
x_95 = lean_uint64_shift_right(x_94, x_17);
x_96 = lean_uint64_xor(x_94, x_95);
x_97 = lean_uint64_shift_right(x_96, x_20);
x_98 = lean_uint64_xor(x_96, x_97);
x_99 = lean_uint64_to_usize(x_98);
x_100 = lean_usize_of_nat(x_93);
lean_dec(x_93);
x_101 = lean_usize_sub(x_100, x_25);
x_102 = lean_usize_land(x_99, x_101);
x_103 = lean_array_uget(x_92, x_102);
x_104 = l_Std_DHashMap_Internal_AssocList_get_x21___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__1(x_38, x_30, x_103);
lean_ctor_set_tag(x_32, 1);
lean_ctor_set(x_32, 1, x_104);
lean_ctor_set(x_32, 0, x_1);
x_105 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__1(x_30, x_103);
if (x_105 == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; 
x_106 = lean_unsigned_to_nat(1u);
x_107 = lean_nat_add(x_91, x_106);
lean_dec(x_91);
x_108 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_108, 0, x_30);
lean_ctor_set(x_108, 1, x_32);
lean_ctor_set(x_108, 2, x_103);
x_109 = lean_array_uset(x_92, x_102, x_108);
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
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_116 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__2(x_109);
x_117 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_117, 0, x_107);
lean_ctor_set(x_117, 1, x_116);
lean_ctor_set(x_34, 1, x_117);
x_118 = lean_st_ref_set(x_2, x_34, x_36);
lean_dec(x_2);
x_119 = lean_ctor_get(x_118, 1);
lean_inc(x_119);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 lean_ctor_release(x_118, 1);
 x_120 = x_118;
} else {
 lean_dec_ref(x_118);
 x_120 = lean_box(0);
}
x_121 = lean_box(0);
if (lean_is_scalar(x_120)) {
 x_122 = lean_alloc_ctor(0, 2, 0);
} else {
 x_122 = x_120;
}
lean_ctor_set(x_122, 0, x_121);
lean_ctor_set(x_122, 1, x_119);
return x_122;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_107);
lean_ctor_set(x_123, 1, x_109);
lean_ctor_set(x_34, 1, x_123);
x_124 = lean_st_ref_set(x_2, x_34, x_36);
lean_dec(x_2);
x_125 = lean_ctor_get(x_124, 1);
lean_inc(x_125);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 lean_ctor_release(x_124, 1);
 x_126 = x_124;
} else {
 lean_dec_ref(x_124);
 x_126 = lean_box(0);
}
x_127 = lean_box(0);
if (lean_is_scalar(x_126)) {
 x_128 = lean_alloc_ctor(0, 2, 0);
} else {
 x_128 = x_126;
}
lean_ctor_set(x_128, 0, x_127);
lean_ctor_set(x_128, 1, x_125);
return x_128;
}
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_129 = lean_box(0);
x_130 = lean_array_uset(x_92, x_102, x_129);
x_131 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__5(x_30, x_32, x_103);
x_132 = lean_array_uset(x_130, x_102, x_131);
x_133 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_133, 0, x_91);
lean_ctor_set(x_133, 1, x_132);
lean_ctor_set(x_34, 1, x_133);
x_134 = lean_st_ref_set(x_2, x_34, x_36);
lean_dec(x_2);
x_135 = lean_ctor_get(x_134, 1);
lean_inc(x_135);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 lean_ctor_release(x_134, 1);
 x_136 = x_134;
} else {
 lean_dec_ref(x_134);
 x_136 = lean_box(0);
}
x_137 = lean_box(0);
if (lean_is_scalar(x_136)) {
 x_138 = lean_alloc_ctor(0, 2, 0);
} else {
 x_138 = x_136;
}
lean_ctor_set(x_138, 0, x_137);
lean_ctor_set(x_138, 1, x_135);
return x_138;
}
}
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; uint64_t x_147; uint64_t x_148; uint64_t x_149; uint64_t x_150; uint64_t x_151; size_t x_152; size_t x_153; size_t x_154; size_t x_155; lean_object* x_156; lean_object* x_157; uint8_t x_158; 
x_139 = lean_ctor_get(x_32, 1);
x_140 = lean_ctor_get(x_34, 0);
x_141 = lean_ctor_get(x_34, 1);
lean_inc(x_141);
lean_inc(x_140);
lean_dec(x_34);
x_142 = lean_box(0);
x_143 = lean_ctor_get(x_141, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_141, 1);
lean_inc(x_144);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 lean_ctor_release(x_141, 1);
 x_145 = x_141;
} else {
 lean_dec_ref(x_141);
 x_145 = lean_box(0);
}
x_146 = lean_array_get_size(x_144);
x_147 = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_hashDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_15_(x_30);
x_148 = lean_uint64_shift_right(x_147, x_17);
x_149 = lean_uint64_xor(x_147, x_148);
x_150 = lean_uint64_shift_right(x_149, x_20);
x_151 = lean_uint64_xor(x_149, x_150);
x_152 = lean_uint64_to_usize(x_151);
x_153 = lean_usize_of_nat(x_146);
lean_dec(x_146);
x_154 = lean_usize_sub(x_153, x_25);
x_155 = lean_usize_land(x_152, x_154);
x_156 = lean_array_uget(x_144, x_155);
x_157 = l_Std_DHashMap_Internal_AssocList_get_x21___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__1(x_142, x_30, x_156);
lean_ctor_set_tag(x_32, 1);
lean_ctor_set(x_32, 1, x_157);
lean_ctor_set(x_32, 0, x_1);
x_158 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__1(x_30, x_156);
if (x_158 == 0)
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; uint8_t x_168; 
x_159 = lean_unsigned_to_nat(1u);
x_160 = lean_nat_add(x_143, x_159);
lean_dec(x_143);
x_161 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_161, 0, x_30);
lean_ctor_set(x_161, 1, x_32);
lean_ctor_set(x_161, 2, x_156);
x_162 = lean_array_uset(x_144, x_155, x_161);
x_163 = lean_unsigned_to_nat(4u);
x_164 = lean_nat_mul(x_160, x_163);
x_165 = lean_unsigned_to_nat(3u);
x_166 = lean_nat_div(x_164, x_165);
lean_dec(x_164);
x_167 = lean_array_get_size(x_162);
x_168 = lean_nat_dec_le(x_166, x_167);
lean_dec(x_167);
lean_dec(x_166);
if (x_168 == 0)
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_169 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__2(x_162);
if (lean_is_scalar(x_145)) {
 x_170 = lean_alloc_ctor(0, 2, 0);
} else {
 x_170 = x_145;
}
lean_ctor_set(x_170, 0, x_160);
lean_ctor_set(x_170, 1, x_169);
x_171 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_171, 0, x_140);
lean_ctor_set(x_171, 1, x_170);
x_172 = lean_st_ref_set(x_2, x_171, x_139);
lean_dec(x_2);
x_173 = lean_ctor_get(x_172, 1);
lean_inc(x_173);
if (lean_is_exclusive(x_172)) {
 lean_ctor_release(x_172, 0);
 lean_ctor_release(x_172, 1);
 x_174 = x_172;
} else {
 lean_dec_ref(x_172);
 x_174 = lean_box(0);
}
x_175 = lean_box(0);
if (lean_is_scalar(x_174)) {
 x_176 = lean_alloc_ctor(0, 2, 0);
} else {
 x_176 = x_174;
}
lean_ctor_set(x_176, 0, x_175);
lean_ctor_set(x_176, 1, x_173);
return x_176;
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
if (lean_is_scalar(x_145)) {
 x_177 = lean_alloc_ctor(0, 2, 0);
} else {
 x_177 = x_145;
}
lean_ctor_set(x_177, 0, x_160);
lean_ctor_set(x_177, 1, x_162);
x_178 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_178, 0, x_140);
lean_ctor_set(x_178, 1, x_177);
x_179 = lean_st_ref_set(x_2, x_178, x_139);
lean_dec(x_2);
x_180 = lean_ctor_get(x_179, 1);
lean_inc(x_180);
if (lean_is_exclusive(x_179)) {
 lean_ctor_release(x_179, 0);
 lean_ctor_release(x_179, 1);
 x_181 = x_179;
} else {
 lean_dec_ref(x_179);
 x_181 = lean_box(0);
}
x_182 = lean_box(0);
if (lean_is_scalar(x_181)) {
 x_183 = lean_alloc_ctor(0, 2, 0);
} else {
 x_183 = x_181;
}
lean_ctor_set(x_183, 0, x_182);
lean_ctor_set(x_183, 1, x_180);
return x_183;
}
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; 
x_184 = lean_box(0);
x_185 = lean_array_uset(x_144, x_155, x_184);
x_186 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__5(x_30, x_32, x_156);
x_187 = lean_array_uset(x_185, x_155, x_186);
if (lean_is_scalar(x_145)) {
 x_188 = lean_alloc_ctor(0, 2, 0);
} else {
 x_188 = x_145;
}
lean_ctor_set(x_188, 0, x_143);
lean_ctor_set(x_188, 1, x_187);
x_189 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_189, 0, x_140);
lean_ctor_set(x_189, 1, x_188);
x_190 = lean_st_ref_set(x_2, x_189, x_139);
lean_dec(x_2);
x_191 = lean_ctor_get(x_190, 1);
lean_inc(x_191);
if (lean_is_exclusive(x_190)) {
 lean_ctor_release(x_190, 0);
 lean_ctor_release(x_190, 1);
 x_192 = x_190;
} else {
 lean_dec_ref(x_190);
 x_192 = lean_box(0);
}
x_193 = lean_box(0);
if (lean_is_scalar(x_192)) {
 x_194 = lean_alloc_ctor(0, 2, 0);
} else {
 x_194 = x_192;
}
lean_ctor_set(x_194, 0, x_193);
lean_ctor_set(x_194, 1, x_191);
return x_194;
}
}
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; uint64_t x_205; uint64_t x_206; uint64_t x_207; uint64_t x_208; uint64_t x_209; size_t x_210; size_t x_211; size_t x_212; size_t x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; uint8_t x_217; 
x_195 = lean_ctor_get(x_32, 0);
x_196 = lean_ctor_get(x_32, 1);
lean_inc(x_196);
lean_inc(x_195);
lean_dec(x_32);
x_197 = lean_ctor_get(x_195, 0);
lean_inc(x_197);
x_198 = lean_ctor_get(x_195, 1);
lean_inc(x_198);
if (lean_is_exclusive(x_195)) {
 lean_ctor_release(x_195, 0);
 lean_ctor_release(x_195, 1);
 x_199 = x_195;
} else {
 lean_dec_ref(x_195);
 x_199 = lean_box(0);
}
x_200 = lean_box(0);
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
x_204 = lean_array_get_size(x_202);
x_205 = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_hashDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_15_(x_30);
x_206 = lean_uint64_shift_right(x_205, x_17);
x_207 = lean_uint64_xor(x_205, x_206);
x_208 = lean_uint64_shift_right(x_207, x_20);
x_209 = lean_uint64_xor(x_207, x_208);
x_210 = lean_uint64_to_usize(x_209);
x_211 = lean_usize_of_nat(x_204);
lean_dec(x_204);
x_212 = lean_usize_sub(x_211, x_25);
x_213 = lean_usize_land(x_210, x_212);
x_214 = lean_array_uget(x_202, x_213);
x_215 = l_Std_DHashMap_Internal_AssocList_get_x21___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__1(x_200, x_30, x_214);
x_216 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_216, 0, x_1);
lean_ctor_set(x_216, 1, x_215);
x_217 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__1(x_30, x_214);
if (x_217 == 0)
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; uint8_t x_227; 
x_218 = lean_unsigned_to_nat(1u);
x_219 = lean_nat_add(x_201, x_218);
lean_dec(x_201);
x_220 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_220, 0, x_30);
lean_ctor_set(x_220, 1, x_216);
lean_ctor_set(x_220, 2, x_214);
x_221 = lean_array_uset(x_202, x_213, x_220);
x_222 = lean_unsigned_to_nat(4u);
x_223 = lean_nat_mul(x_219, x_222);
x_224 = lean_unsigned_to_nat(3u);
x_225 = lean_nat_div(x_223, x_224);
lean_dec(x_223);
x_226 = lean_array_get_size(x_221);
x_227 = lean_nat_dec_le(x_225, x_226);
lean_dec(x_226);
lean_dec(x_225);
if (x_227 == 0)
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; 
x_228 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__2(x_221);
if (lean_is_scalar(x_203)) {
 x_229 = lean_alloc_ctor(0, 2, 0);
} else {
 x_229 = x_203;
}
lean_ctor_set(x_229, 0, x_219);
lean_ctor_set(x_229, 1, x_228);
if (lean_is_scalar(x_199)) {
 x_230 = lean_alloc_ctor(0, 2, 0);
} else {
 x_230 = x_199;
}
lean_ctor_set(x_230, 0, x_197);
lean_ctor_set(x_230, 1, x_229);
x_231 = lean_st_ref_set(x_2, x_230, x_196);
lean_dec(x_2);
x_232 = lean_ctor_get(x_231, 1);
lean_inc(x_232);
if (lean_is_exclusive(x_231)) {
 lean_ctor_release(x_231, 0);
 lean_ctor_release(x_231, 1);
 x_233 = x_231;
} else {
 lean_dec_ref(x_231);
 x_233 = lean_box(0);
}
x_234 = lean_box(0);
if (lean_is_scalar(x_233)) {
 x_235 = lean_alloc_ctor(0, 2, 0);
} else {
 x_235 = x_233;
}
lean_ctor_set(x_235, 0, x_234);
lean_ctor_set(x_235, 1, x_232);
return x_235;
}
else
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; 
if (lean_is_scalar(x_203)) {
 x_236 = lean_alloc_ctor(0, 2, 0);
} else {
 x_236 = x_203;
}
lean_ctor_set(x_236, 0, x_219);
lean_ctor_set(x_236, 1, x_221);
if (lean_is_scalar(x_199)) {
 x_237 = lean_alloc_ctor(0, 2, 0);
} else {
 x_237 = x_199;
}
lean_ctor_set(x_237, 0, x_197);
lean_ctor_set(x_237, 1, x_236);
x_238 = lean_st_ref_set(x_2, x_237, x_196);
lean_dec(x_2);
x_239 = lean_ctor_get(x_238, 1);
lean_inc(x_239);
if (lean_is_exclusive(x_238)) {
 lean_ctor_release(x_238, 0);
 lean_ctor_release(x_238, 1);
 x_240 = x_238;
} else {
 lean_dec_ref(x_238);
 x_240 = lean_box(0);
}
x_241 = lean_box(0);
if (lean_is_scalar(x_240)) {
 x_242 = lean_alloc_ctor(0, 2, 0);
} else {
 x_242 = x_240;
}
lean_ctor_set(x_242, 0, x_241);
lean_ctor_set(x_242, 1, x_239);
return x_242;
}
}
else
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; 
x_243 = lean_box(0);
x_244 = lean_array_uset(x_202, x_213, x_243);
x_245 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__5(x_30, x_216, x_214);
x_246 = lean_array_uset(x_244, x_213, x_245);
if (lean_is_scalar(x_203)) {
 x_247 = lean_alloc_ctor(0, 2, 0);
} else {
 x_247 = x_203;
}
lean_ctor_set(x_247, 0, x_201);
lean_ctor_set(x_247, 1, x_246);
if (lean_is_scalar(x_199)) {
 x_248 = lean_alloc_ctor(0, 2, 0);
} else {
 x_248 = x_199;
}
lean_ctor_set(x_248, 0, x_197);
lean_ctor_set(x_248, 1, x_247);
x_249 = lean_st_ref_set(x_2, x_248, x_196);
lean_dec(x_2);
x_250 = lean_ctor_get(x_249, 1);
lean_inc(x_250);
if (lean_is_exclusive(x_249)) {
 lean_ctor_release(x_249, 0);
 lean_ctor_release(x_249, 1);
 x_251 = x_249;
} else {
 lean_dec_ref(x_249);
 x_251 = lean_box(0);
}
x_252 = lean_box(0);
if (lean_is_scalar(x_251)) {
 x_253 = lean_alloc_ctor(0, 2, 0);
} else {
 x_253 = x_251;
}
lean_ctor_set(x_253, 0, x_252);
lean_ctor_set(x_253, 1, x_250);
return x_253;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at_Lean_Compiler_LCNF_FloatLetIn_float___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x21___at_Lean_Compiler_LCNF_FloatLetIn_float___spec__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_float___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_FloatLetIn_float___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_14; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_5);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint64_t x_24; uint64_t x_25; uint64_t x_26; uint64_t x_27; uint64_t x_28; uint64_t x_29; uint64_t x_30; size_t x_31; size_t x_32; size_t x_33; size_t x_34; size_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
lean_dec(x_5);
x_15 = lean_ctor_get(x_4, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_4, 1);
lean_inc(x_16);
lean_dec(x_4);
x_17 = lean_st_ref_get(x_7, x_13);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_Compiler_LCNF_CodeDecl_fvarId(x_15);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_array_get_size(x_22);
x_24 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1724_(x_21);
x_25 = 32;
x_26 = lean_uint64_shift_right(x_24, x_25);
x_27 = lean_uint64_xor(x_24, x_26);
x_28 = 16;
x_29 = lean_uint64_shift_right(x_27, x_28);
x_30 = lean_uint64_xor(x_27, x_29);
x_31 = lean_uint64_to_usize(x_30);
x_32 = lean_usize_of_nat(x_23);
lean_dec(x_23);
x_33 = 1;
x_34 = lean_usize_sub(x_32, x_33);
x_35 = lean_usize_land(x_31, x_34);
x_36 = lean_array_uget(x_22, x_35);
lean_dec(x_22);
x_37 = l_Lean_Compiler_LCNF_FloatLetIn_instInhabitedDecision;
x_38 = l_Std_DHashMap_Internal_AssocList_get_x21___at_Lean_Compiler_LCNF_FloatLetIn_float___spec__1(x_37, x_21, x_36);
lean_dec(x_36);
lean_dec(x_21);
x_39 = lean_box(3);
x_40 = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_beqDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_62_(x_38, x_39);
if (x_40 == 0)
{
lean_object* x_41; uint8_t x_42; 
x_41 = lean_box(2);
x_42 = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_beqDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_62_(x_38, x_41);
lean_dec(x_38);
if (x_42 == 0)
{
lean_object* x_43; 
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_43 = l_Lean_Compiler_LCNF_FloatLetIn_float(x_15, x_7, x_8, x_9, x_10, x_11, x_12, x_19);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
lean_dec(x_43);
x_45 = lean_box(0);
x_4 = x_16;
x_5 = x_45;
x_6 = lean_box(0);
x_13 = x_44;
goto _start;
}
else
{
uint8_t x_47; 
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_47 = !lean_is_exclusive(x_43);
if (x_47 == 0)
{
return x_43;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_43, 0);
x_49 = lean_ctor_get(x_43, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_43);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
else
{
lean_object* x_51; 
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_51 = l_Lean_Compiler_LCNF_FloatLetIn_dontFloat(x_15, x_7, x_8, x_9, x_10, x_11, x_12, x_19);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
lean_dec(x_51);
x_53 = lean_box(0);
x_4 = x_16;
x_5 = x_53;
x_6 = lean_box(0);
x_13 = x_52;
goto _start;
}
else
{
uint8_t x_55; 
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_55 = !lean_is_exclusive(x_51);
if (x_55 == 0)
{
return x_51;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_51, 0);
x_57 = lean_ctor_get(x_51, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_51);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_38);
x_59 = l_Lean_Compiler_LCNF_eraseCodeDecl(x_15, x_9, x_10, x_11, x_12, x_19);
lean_dec(x_15);
x_60 = lean_ctor_get(x_59, 1);
lean_inc(x_60);
lean_dec(x_59);
x_61 = lean_box(0);
x_4 = x_16;
x_5 = x_61;
x_6 = lean_box(0);
x_13 = x_60;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_box(0);
x_9 = lean_box(0);
lean_inc_n(x_2, 2);
x_10 = l_List_forIn_x27_loop___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases___spec__1(x_2, x_8, x_2, x_2, x_9, lean_box(0), x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
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
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_10);
if (x_15 == 0)
{
return x_10;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_10, 0);
x_17 = lean_ctor_get(x_10, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_10);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_List_forIn_x27_loop___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_14;
}
}
static lean_object* _init_l_Lean_isTracingEnabledFor___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_inheritedTraceOptions;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = l_Lean_isTracingEnabledFor___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__1___closed__1;
x_9 = lean_st_ref_get(x_8, x_7);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_5, 2);
x_13 = l___private_Lean_Util_Trace_0__Lean_checkTraceOption(x_11, x_12, x_1);
lean_dec(x_11);
x_14 = lean_box(x_13);
lean_ctor_set(x_9, 0, x_14);
return x_9;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_9, 0);
x_16 = lean_ctor_get(x_9, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_9);
x_17 = lean_ctor_get(x_5, 2);
x_18 = l___private_Lean_Util_Trace_0__Lean_checkTraceOption(x_15, x_17, x_1);
lean_dec(x_15);
x_19 = lean_box(x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_16);
return x_20;
}
}
}
static lean_object* _init_l_Lean_addTrace___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_addTrace___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_addTrace___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__2___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addTrace___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_addTrace___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__2___closed__2;
x_3 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 2, x_1);
lean_ctor_set(x_3, 3, x_2);
lean_ctor_set(x_3, 4, x_2);
lean_ctor_set(x_3, 5, x_2);
lean_ctor_set(x_3, 6, x_2);
lean_ctor_set(x_3, 7, x_2);
lean_ctor_set(x_3, 8, x_2);
return x_3;
}
}
static double _init_l_Lean_addTrace___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__2___closed__4() {
_start:
{
lean_object* x_1; uint8_t x_2; double x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = 0;
x_3 = l_Float_ofScientific(x_1, x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_addTrace___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__2___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_addTrace___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__2___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_array_mk(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_9 = lean_ctor_get(x_6, 5);
x_10 = lean_st_ref_get(x_7, x_8);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_st_ref_get(x_5, x_12);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_18);
lean_dec(x_18);
x_20 = lean_ctor_get(x_6, 2);
x_21 = l_Lean_addTrace___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__2___closed__3;
lean_inc(x_20);
x_22 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_22, 0, x_13);
lean_ctor_set(x_22, 1, x_21);
lean_ctor_set(x_22, 2, x_19);
lean_ctor_set(x_22, 3, x_20);
lean_ctor_set_tag(x_14, 3);
lean_ctor_set(x_14, 1, x_2);
lean_ctor_set(x_14, 0, x_22);
x_23 = lean_st_ref_take(x_7, x_17);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_24, 3);
lean_inc(x_25);
x_26 = !lean_is_exclusive(x_23);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_23, 1);
x_28 = lean_ctor_get(x_23, 0);
lean_dec(x_28);
x_29 = !lean_is_exclusive(x_24);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; 
x_30 = lean_ctor_get(x_24, 3);
lean_dec(x_30);
x_31 = !lean_is_exclusive(x_25);
if (x_31 == 0)
{
lean_object* x_32; double x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_32 = lean_ctor_get(x_25, 0);
x_33 = l_Lean_addTrace___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__2___closed__4;
x_34 = 0;
x_35 = l_Lean_addTrace___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__2___closed__5;
x_36 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_36, 0, x_1);
lean_ctor_set(x_36, 1, x_35);
lean_ctor_set_float(x_36, sizeof(void*)*2, x_33);
lean_ctor_set_float(x_36, sizeof(void*)*2 + 8, x_33);
lean_ctor_set_uint8(x_36, sizeof(void*)*2 + 16, x_34);
x_37 = l_Lean_addTrace___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__2___closed__6;
x_38 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_14);
lean_ctor_set(x_38, 2, x_37);
lean_inc(x_9);
lean_ctor_set(x_23, 1, x_38);
lean_ctor_set(x_23, 0, x_9);
x_39 = l_Lean_PersistentArray_push___rarg(x_32, x_23);
lean_ctor_set(x_25, 0, x_39);
x_40 = lean_st_ref_set(x_7, x_24, x_27);
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
uint64_t x_47; lean_object* x_48; double x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_47 = lean_ctor_get_uint64(x_25, sizeof(void*)*1);
x_48 = lean_ctor_get(x_25, 0);
lean_inc(x_48);
lean_dec(x_25);
x_49 = l_Lean_addTrace___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__2___closed__4;
x_50 = 0;
x_51 = l_Lean_addTrace___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__2___closed__5;
x_52 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_52, 0, x_1);
lean_ctor_set(x_52, 1, x_51);
lean_ctor_set_float(x_52, sizeof(void*)*2, x_49);
lean_ctor_set_float(x_52, sizeof(void*)*2 + 8, x_49);
lean_ctor_set_uint8(x_52, sizeof(void*)*2 + 16, x_50);
x_53 = l_Lean_addTrace___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__2___closed__6;
x_54 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_14);
lean_ctor_set(x_54, 2, x_53);
lean_inc(x_9);
lean_ctor_set(x_23, 1, x_54);
lean_ctor_set(x_23, 0, x_9);
x_55 = l_Lean_PersistentArray_push___rarg(x_48, x_23);
x_56 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set_uint64(x_56, sizeof(void*)*1, x_47);
lean_ctor_set(x_24, 3, x_56);
x_57 = lean_st_ref_set(x_7, x_24, x_27);
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_59 = x_57;
} else {
 lean_dec_ref(x_57);
 x_59 = lean_box(0);
}
x_60 = lean_box(0);
if (lean_is_scalar(x_59)) {
 x_61 = lean_alloc_ctor(0, 2, 0);
} else {
 x_61 = x_59;
}
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_58);
return x_61;
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint64_t x_68; lean_object* x_69; lean_object* x_70; double x_71; uint8_t x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_62 = lean_ctor_get(x_24, 0);
x_63 = lean_ctor_get(x_24, 1);
x_64 = lean_ctor_get(x_24, 2);
x_65 = lean_ctor_get(x_24, 4);
x_66 = lean_ctor_get(x_24, 5);
x_67 = lean_ctor_get(x_24, 6);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_24);
x_68 = lean_ctor_get_uint64(x_25, sizeof(void*)*1);
x_69 = lean_ctor_get(x_25, 0);
lean_inc(x_69);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 x_70 = x_25;
} else {
 lean_dec_ref(x_25);
 x_70 = lean_box(0);
}
x_71 = l_Lean_addTrace___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__2___closed__4;
x_72 = 0;
x_73 = l_Lean_addTrace___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__2___closed__5;
x_74 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_74, 0, x_1);
lean_ctor_set(x_74, 1, x_73);
lean_ctor_set_float(x_74, sizeof(void*)*2, x_71);
lean_ctor_set_float(x_74, sizeof(void*)*2 + 8, x_71);
lean_ctor_set_uint8(x_74, sizeof(void*)*2 + 16, x_72);
x_75 = l_Lean_addTrace___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__2___closed__6;
x_76 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_14);
lean_ctor_set(x_76, 2, x_75);
lean_inc(x_9);
lean_ctor_set(x_23, 1, x_76);
lean_ctor_set(x_23, 0, x_9);
x_77 = l_Lean_PersistentArray_push___rarg(x_69, x_23);
if (lean_is_scalar(x_70)) {
 x_78 = lean_alloc_ctor(0, 1, 8);
} else {
 x_78 = x_70;
}
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set_uint64(x_78, sizeof(void*)*1, x_68);
x_79 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_79, 0, x_62);
lean_ctor_set(x_79, 1, x_63);
lean_ctor_set(x_79, 2, x_64);
lean_ctor_set(x_79, 3, x_78);
lean_ctor_set(x_79, 4, x_65);
lean_ctor_set(x_79, 5, x_66);
lean_ctor_set(x_79, 6, x_67);
x_80 = lean_st_ref_set(x_7, x_79, x_27);
x_81 = lean_ctor_get(x_80, 1);
lean_inc(x_81);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 lean_ctor_release(x_80, 1);
 x_82 = x_80;
} else {
 lean_dec_ref(x_80);
 x_82 = lean_box(0);
}
x_83 = lean_box(0);
if (lean_is_scalar(x_82)) {
 x_84 = lean_alloc_ctor(0, 2, 0);
} else {
 x_84 = x_82;
}
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_81);
return x_84;
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; uint64_t x_93; lean_object* x_94; lean_object* x_95; double x_96; uint8_t x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_85 = lean_ctor_get(x_23, 1);
lean_inc(x_85);
lean_dec(x_23);
x_86 = lean_ctor_get(x_24, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_24, 1);
lean_inc(x_87);
x_88 = lean_ctor_get(x_24, 2);
lean_inc(x_88);
x_89 = lean_ctor_get(x_24, 4);
lean_inc(x_89);
x_90 = lean_ctor_get(x_24, 5);
lean_inc(x_90);
x_91 = lean_ctor_get(x_24, 6);
lean_inc(x_91);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 lean_ctor_release(x_24, 2);
 lean_ctor_release(x_24, 3);
 lean_ctor_release(x_24, 4);
 lean_ctor_release(x_24, 5);
 lean_ctor_release(x_24, 6);
 x_92 = x_24;
} else {
 lean_dec_ref(x_24);
 x_92 = lean_box(0);
}
x_93 = lean_ctor_get_uint64(x_25, sizeof(void*)*1);
x_94 = lean_ctor_get(x_25, 0);
lean_inc(x_94);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 x_95 = x_25;
} else {
 lean_dec_ref(x_25);
 x_95 = lean_box(0);
}
x_96 = l_Lean_addTrace___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__2___closed__4;
x_97 = 0;
x_98 = l_Lean_addTrace___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__2___closed__5;
x_99 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_99, 0, x_1);
lean_ctor_set(x_99, 1, x_98);
lean_ctor_set_float(x_99, sizeof(void*)*2, x_96);
lean_ctor_set_float(x_99, sizeof(void*)*2 + 8, x_96);
lean_ctor_set_uint8(x_99, sizeof(void*)*2 + 16, x_97);
x_100 = l_Lean_addTrace___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__2___closed__6;
x_101 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_14);
lean_ctor_set(x_101, 2, x_100);
lean_inc(x_9);
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_9);
lean_ctor_set(x_102, 1, x_101);
x_103 = l_Lean_PersistentArray_push___rarg(x_94, x_102);
if (lean_is_scalar(x_95)) {
 x_104 = lean_alloc_ctor(0, 1, 8);
} else {
 x_104 = x_95;
}
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set_uint64(x_104, sizeof(void*)*1, x_93);
if (lean_is_scalar(x_92)) {
 x_105 = lean_alloc_ctor(0, 7, 0);
} else {
 x_105 = x_92;
}
lean_ctor_set(x_105, 0, x_86);
lean_ctor_set(x_105, 1, x_87);
lean_ctor_set(x_105, 2, x_88);
lean_ctor_set(x_105, 3, x_104);
lean_ctor_set(x_105, 4, x_89);
lean_ctor_set(x_105, 5, x_90);
lean_ctor_set(x_105, 6, x_91);
x_106 = lean_st_ref_set(x_7, x_105, x_85);
x_107 = lean_ctor_get(x_106, 1);
lean_inc(x_107);
if (lean_is_exclusive(x_106)) {
 lean_ctor_release(x_106, 0);
 lean_ctor_release(x_106, 1);
 x_108 = x_106;
} else {
 lean_dec_ref(x_106);
 x_108 = lean_box(0);
}
x_109 = lean_box(0);
if (lean_is_scalar(x_108)) {
 x_110 = lean_alloc_ctor(0, 2, 0);
} else {
 x_110 = x_108;
}
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_107);
return x_110;
}
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; uint64_t x_131; lean_object* x_132; lean_object* x_133; double x_134; uint8_t x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_111 = lean_ctor_get(x_14, 0);
x_112 = lean_ctor_get(x_14, 1);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_14);
x_113 = lean_ctor_get(x_111, 0);
lean_inc(x_113);
lean_dec(x_111);
x_114 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_113);
lean_dec(x_113);
x_115 = lean_ctor_get(x_6, 2);
x_116 = l_Lean_addTrace___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__2___closed__3;
lean_inc(x_115);
x_117 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_117, 0, x_13);
lean_ctor_set(x_117, 1, x_116);
lean_ctor_set(x_117, 2, x_114);
lean_ctor_set(x_117, 3, x_115);
x_118 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_2);
x_119 = lean_st_ref_take(x_7, x_112);
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_120, 3);
lean_inc(x_121);
x_122 = lean_ctor_get(x_119, 1);
lean_inc(x_122);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 lean_ctor_release(x_119, 1);
 x_123 = x_119;
} else {
 lean_dec_ref(x_119);
 x_123 = lean_box(0);
}
x_124 = lean_ctor_get(x_120, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_120, 1);
lean_inc(x_125);
x_126 = lean_ctor_get(x_120, 2);
lean_inc(x_126);
x_127 = lean_ctor_get(x_120, 4);
lean_inc(x_127);
x_128 = lean_ctor_get(x_120, 5);
lean_inc(x_128);
x_129 = lean_ctor_get(x_120, 6);
lean_inc(x_129);
if (lean_is_exclusive(x_120)) {
 lean_ctor_release(x_120, 0);
 lean_ctor_release(x_120, 1);
 lean_ctor_release(x_120, 2);
 lean_ctor_release(x_120, 3);
 lean_ctor_release(x_120, 4);
 lean_ctor_release(x_120, 5);
 lean_ctor_release(x_120, 6);
 x_130 = x_120;
} else {
 lean_dec_ref(x_120);
 x_130 = lean_box(0);
}
x_131 = lean_ctor_get_uint64(x_121, sizeof(void*)*1);
x_132 = lean_ctor_get(x_121, 0);
lean_inc(x_132);
if (lean_is_exclusive(x_121)) {
 lean_ctor_release(x_121, 0);
 x_133 = x_121;
} else {
 lean_dec_ref(x_121);
 x_133 = lean_box(0);
}
x_134 = l_Lean_addTrace___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__2___closed__4;
x_135 = 0;
x_136 = l_Lean_addTrace___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__2___closed__5;
x_137 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_137, 0, x_1);
lean_ctor_set(x_137, 1, x_136);
lean_ctor_set_float(x_137, sizeof(void*)*2, x_134);
lean_ctor_set_float(x_137, sizeof(void*)*2 + 8, x_134);
lean_ctor_set_uint8(x_137, sizeof(void*)*2 + 16, x_135);
x_138 = l_Lean_addTrace___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__2___closed__6;
x_139 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_139, 0, x_137);
lean_ctor_set(x_139, 1, x_118);
lean_ctor_set(x_139, 2, x_138);
lean_inc(x_9);
if (lean_is_scalar(x_123)) {
 x_140 = lean_alloc_ctor(0, 2, 0);
} else {
 x_140 = x_123;
}
lean_ctor_set(x_140, 0, x_9);
lean_ctor_set(x_140, 1, x_139);
x_141 = l_Lean_PersistentArray_push___rarg(x_132, x_140);
if (lean_is_scalar(x_133)) {
 x_142 = lean_alloc_ctor(0, 1, 8);
} else {
 x_142 = x_133;
}
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set_uint64(x_142, sizeof(void*)*1, x_131);
if (lean_is_scalar(x_130)) {
 x_143 = lean_alloc_ctor(0, 7, 0);
} else {
 x_143 = x_130;
}
lean_ctor_set(x_143, 0, x_124);
lean_ctor_set(x_143, 1, x_125);
lean_ctor_set(x_143, 2, x_126);
lean_ctor_set(x_143, 3, x_142);
lean_ctor_set(x_143, 4, x_127);
lean_ctor_set(x_143, 5, x_128);
lean_ctor_set(x_143, 6, x_129);
x_144 = lean_st_ref_set(x_7, x_143, x_122);
x_145 = lean_ctor_get(x_144, 1);
lean_inc(x_145);
if (lean_is_exclusive(x_144)) {
 lean_ctor_release(x_144, 0);
 lean_ctor_release(x_144, 1);
 x_146 = x_144;
} else {
 lean_dec_ref(x_144);
 x_146 = lean_box(0);
}
x_147 = lean_box(0);
if (lean_is_scalar(x_146)) {
 x_148 = lean_alloc_ctor(0, 2, 0);
} else {
 x_148 = x_146;
}
lean_ctor_set(x_148, 0, x_147);
lean_ctor_set(x_148, 1, x_145);
return x_148;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__3___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_array_mk(x_1);
x_11 = l_Lean_Compiler_LCNF_AltCore_getCode(x_2);
x_12 = l_Lean_Compiler_LCNF_attachCodeDecls(x_10, x_11);
lean_dec(x_10);
x_13 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go), 7, 1);
lean_closure_set(x_13, 0, x_12);
x_14 = l_Lean_Compiler_LCNF_FloatLetIn_withNewScope___rarg(x_13, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(x_2, x_16);
lean_ctor_set(x_14, 0, x_17);
return x_14;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_14, 0);
x_19 = lean_ctor_get(x_14, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_14);
x_20 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(x_2, x_18);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
else
{
uint8_t x_22; 
lean_dec(x_2);
x_22 = !lean_is_exclusive(x_14);
if (x_22 == 0)
{
return x_14;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_14, 0);
x_24 = lean_ctor_get(x_14, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_14);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Compiler", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__3___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("floatLetIn", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__3___closed__1;
x_2 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__3___closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__3___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Size of code that was pushed into arm: ", 39, 39);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__3___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__3___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__3___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" ", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__3___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__3___closed__6;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__3___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_addTrace___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__2___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_lt(x_5, x_4);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_6);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_15 = lean_array_uget(x_6, x_5);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_array_uset(x_6, x_5, x_16);
x_18 = l_Lean_Compiler_LCNF_FloatLetIn_Decision_ofAlt(x_15);
x_19 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__3___closed__3;
x_20 = l_Lean_isTracingEnabledFor___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__1(x_19, x_7, x_8, x_9, x_10, x_11, x_12);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint64_t x_26; uint64_t x_27; uint64_t x_28; uint64_t x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; size_t x_33; size_t x_34; size_t x_35; size_t x_36; size_t x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_22 = lean_ctor_get(x_3, 1);
x_23 = lean_ctor_get(x_20, 0);
x_24 = lean_ctor_get(x_20, 1);
x_25 = lean_array_get_size(x_22);
x_26 = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_hashDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_15_(x_18);
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
x_38 = lean_array_uget(x_22, x_37);
lean_inc(x_1);
x_39 = l_Std_DHashMap_Internal_AssocList_get_x21___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__1(x_1, x_18, x_38);
lean_dec(x_38);
x_40 = lean_unbox(x_23);
lean_dec(x_23);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
lean_free_object(x_20);
lean_dec(x_18);
x_41 = lean_box(0);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_42 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__3___lambda__1(x_39, x_15, x_41, x_7, x_8, x_9, x_10, x_11, x_24);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; size_t x_45; lean_object* x_46; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = lean_usize_add(x_5, x_35);
x_46 = lean_array_uset(x_17, x_5, x_43);
x_5 = x_45;
x_6 = x_46;
x_12 = x_44;
goto _start;
}
else
{
uint8_t x_48; 
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_48 = !lean_is_exclusive(x_42);
if (x_48 == 0)
{
return x_42;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_42, 0);
x_50 = lean_ctor_get(x_42, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_42);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_52 = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160_(x_18, x_16);
x_53 = l_Lean_MessageData_ofFormat(x_52);
x_54 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__3___closed__5;
lean_ctor_set_tag(x_20, 7);
lean_ctor_set(x_20, 1, x_53);
lean_ctor_set(x_20, 0, x_54);
x_55 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__3___closed__7;
x_56 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_56, 0, x_20);
lean_ctor_set(x_56, 1, x_55);
x_57 = l_List_lengthTRAux___rarg(x_39, x_16);
x_58 = l___private_Init_Data_Repr_0__Nat_reprFast(x_57);
x_59 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_59, 0, x_58);
x_60 = l_Lean_MessageData_ofFormat(x_59);
x_61 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_61, 0, x_56);
lean_ctor_set(x_61, 1, x_60);
x_62 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__3___closed__8;
x_63 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
x_64 = l_Lean_addTrace___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__2(x_19, x_63, x_7, x_8, x_9, x_10, x_11, x_24);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_67 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__3___lambda__1(x_39, x_15, x_65, x_7, x_8, x_9, x_10, x_11, x_66);
lean_dec(x_65);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; size_t x_70; lean_object* x_71; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_70 = lean_usize_add(x_5, x_35);
x_71 = lean_array_uset(x_17, x_5, x_68);
x_5 = x_70;
x_6 = x_71;
x_12 = x_69;
goto _start;
}
else
{
uint8_t x_73; 
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_73 = !lean_is_exclusive(x_67);
if (x_73 == 0)
{
return x_67;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_67, 0);
x_75 = lean_ctor_get(x_67, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_67);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint64_t x_81; uint64_t x_82; uint64_t x_83; uint64_t x_84; uint64_t x_85; uint64_t x_86; uint64_t x_87; size_t x_88; size_t x_89; size_t x_90; size_t x_91; size_t x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; 
x_77 = lean_ctor_get(x_3, 1);
x_78 = lean_ctor_get(x_20, 0);
x_79 = lean_ctor_get(x_20, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_20);
x_80 = lean_array_get_size(x_77);
x_81 = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_hashDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_15_(x_18);
x_82 = 32;
x_83 = lean_uint64_shift_right(x_81, x_82);
x_84 = lean_uint64_xor(x_81, x_83);
x_85 = 16;
x_86 = lean_uint64_shift_right(x_84, x_85);
x_87 = lean_uint64_xor(x_84, x_86);
x_88 = lean_uint64_to_usize(x_87);
x_89 = lean_usize_of_nat(x_80);
lean_dec(x_80);
x_90 = 1;
x_91 = lean_usize_sub(x_89, x_90);
x_92 = lean_usize_land(x_88, x_91);
x_93 = lean_array_uget(x_77, x_92);
lean_inc(x_1);
x_94 = l_Std_DHashMap_Internal_AssocList_get_x21___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__1(x_1, x_18, x_93);
lean_dec(x_93);
x_95 = lean_unbox(x_78);
lean_dec(x_78);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; 
lean_dec(x_18);
x_96 = lean_box(0);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_97 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__3___lambda__1(x_94, x_15, x_96, x_7, x_8, x_9, x_10, x_11, x_79);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; lean_object* x_99; size_t x_100; lean_object* x_101; 
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_97, 1);
lean_inc(x_99);
lean_dec(x_97);
x_100 = lean_usize_add(x_5, x_90);
x_101 = lean_array_uset(x_17, x_5, x_98);
x_5 = x_100;
x_6 = x_101;
x_12 = x_99;
goto _start;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_103 = lean_ctor_get(x_97, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_97, 1);
lean_inc(x_104);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 lean_ctor_release(x_97, 1);
 x_105 = x_97;
} else {
 lean_dec_ref(x_97);
 x_105 = lean_box(0);
}
if (lean_is_scalar(x_105)) {
 x_106 = lean_alloc_ctor(1, 2, 0);
} else {
 x_106 = x_105;
}
lean_ctor_set(x_106, 0, x_103);
lean_ctor_set(x_106, 1, x_104);
return x_106;
}
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_107 = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160_(x_18, x_16);
x_108 = l_Lean_MessageData_ofFormat(x_107);
x_109 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__3___closed__5;
x_110 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_108);
x_111 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__3___closed__7;
x_112 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
x_113 = l_List_lengthTRAux___rarg(x_94, x_16);
x_114 = l___private_Init_Data_Repr_0__Nat_reprFast(x_113);
x_115 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_115, 0, x_114);
x_116 = l_Lean_MessageData_ofFormat(x_115);
x_117 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_117, 0, x_112);
lean_ctor_set(x_117, 1, x_116);
x_118 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__3___closed__8;
x_119 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_118);
x_120 = l_Lean_addTrace___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__2(x_19, x_119, x_7, x_8, x_9, x_10, x_11, x_79);
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_120, 1);
lean_inc(x_122);
lean_dec(x_120);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_123 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__3___lambda__1(x_94, x_15, x_121, x_7, x_8, x_9, x_10, x_11, x_122);
lean_dec(x_121);
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_124; lean_object* x_125; size_t x_126; lean_object* x_127; 
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_123, 1);
lean_inc(x_125);
lean_dec(x_123);
x_126 = lean_usize_add(x_5, x_90);
x_127 = lean_array_uset(x_17, x_5, x_124);
x_5 = x_126;
x_6 = x_127;
x_12 = x_125;
goto _start;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_129 = lean_ctor_get(x_123, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_123, 1);
lean_inc(x_130);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 lean_ctor_release(x_123, 1);
 x_131 = x_123;
} else {
 lean_dec_ref(x_123);
 x_131 = lean_box(0);
}
if (lean_is_scalar(x_131)) {
 x_132 = lean_alloc_ctor(1, 2, 0);
} else {
 x_132 = x_131;
}
lean_ctor_set(x_132, 0, x_129);
lean_ctor_set(x_132, 1, x_130);
return x_132;
}
}
}
}
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
x_12 = l_Lean_Compiler_LCNF_FloatLetIn_withNewCandidate___rarg(x_10, x_11, x_2, x_3, x_4, x_5, x_6, x_7);
return x_12;
}
case 1:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
lean_dec(x_1);
x_15 = lean_ctor_get(x_13, 4);
lean_inc(x_15);
x_16 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go), 7, 1);
lean_closure_set(x_16, 0, x_15);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_17 = l_Lean_Compiler_LCNF_FloatLetIn_withNewScope___rarg(x_16, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_ctor_get(x_13, 3);
lean_inc(x_20);
x_21 = lean_ctor_get(x_13, 2);
lean_inc(x_21);
x_22 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp(x_13, x_20, x_21, x_18, x_3, x_4, x_5, x_6, x_19);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_23);
x_26 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go), 7, 1);
lean_closure_set(x_26, 0, x_14);
x_27 = l_Lean_Compiler_LCNF_FloatLetIn_withNewCandidate___rarg(x_25, x_26, x_2, x_3, x_4, x_5, x_6, x_24);
return x_27;
}
else
{
uint8_t x_28; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_28 = !lean_is_exclusive(x_17);
if (x_28 == 0)
{
return x_17;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_17, 0);
x_30 = lean_ctor_get(x_17, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_17);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
case 2:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_32 = lean_ctor_get(x_1, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_1, 1);
lean_inc(x_33);
lean_dec(x_1);
x_34 = lean_ctor_get(x_32, 4);
lean_inc(x_34);
x_35 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go), 7, 1);
lean_closure_set(x_35, 0, x_34);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_36 = l_Lean_Compiler_LCNF_FloatLetIn_withNewScope___rarg(x_35, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_ctor_get(x_32, 3);
lean_inc(x_39);
x_40 = lean_ctor_get(x_32, 2);
lean_inc(x_40);
x_41 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp(x_32, x_39, x_40, x_37, x_3, x_4, x_5, x_6, x_38);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_44, 0, x_42);
x_45 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go), 7, 1);
lean_closure_set(x_45, 0, x_33);
x_46 = l_Lean_Compiler_LCNF_FloatLetIn_withNewCandidate___rarg(x_44, x_45, x_2, x_3, x_4, x_5, x_6, x_43);
return x_46;
}
else
{
uint8_t x_47; 
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_47 = !lean_is_exclusive(x_36);
if (x_47 == 0)
{
return x_36;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_36, 0);
x_49 = lean_ctor_get(x_36, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_36);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
case 4:
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_1, 0);
lean_inc(x_51);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_51);
x_52 = l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions(x_51, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = l_Lean_Compiler_LCNF_FloatLetIn_initialNewArms(x_51);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_53);
lean_ctor_set(x_56, 1, x_55);
x_57 = lean_st_mk_ref(x_56, x_54);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_58);
x_60 = l_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases(x_58, x_2, x_3, x_4, x_5, x_6, x_59);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_61 = lean_ctor_get(x_60, 1);
lean_inc(x_61);
lean_dec(x_60);
x_62 = lean_st_ref_get(x_58, x_61);
lean_dec(x_58);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
x_65 = lean_box(0);
x_66 = lean_ctor_get(x_63, 1);
lean_inc(x_66);
lean_dec(x_63);
x_67 = !lean_is_exclusive(x_51);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; size_t x_72; size_t x_73; lean_object* x_74; lean_object* x_75; size_t x_76; size_t x_77; size_t x_78; size_t x_79; size_t x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_68 = lean_ctor_get(x_51, 0);
x_69 = lean_ctor_get(x_51, 1);
x_70 = lean_ctor_get(x_51, 2);
x_71 = lean_ctor_get(x_51, 3);
x_72 = lean_array_size(x_71);
x_73 = 0;
x_74 = lean_ctor_get(x_66, 1);
lean_inc(x_74);
x_75 = lean_array_get_size(x_74);
x_76 = lean_usize_of_nat(x_75);
lean_dec(x_75);
x_77 = 1;
x_78 = lean_usize_sub(x_76, x_77);
x_79 = l_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___closed__6;
x_80 = lean_usize_land(x_79, x_78);
x_81 = lean_array_uget(x_74, x_80);
lean_dec(x_74);
x_82 = lean_box(2);
x_83 = l_Std_DHashMap_Internal_AssocList_get_x21___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__1(x_65, x_82, x_81);
lean_dec(x_81);
lean_inc(x_71);
x_84 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__3(x_65, x_66, x_66, x_72, x_73, x_71, x_2, x_3, x_4, x_5, x_6, x_64);
lean_dec(x_2);
lean_dec(x_66);
if (lean_obj_tag(x_84) == 0)
{
uint8_t x_85; 
x_85 = !lean_is_exclusive(x_84);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; size_t x_88; size_t x_89; uint8_t x_90; 
x_86 = lean_ctor_get(x_84, 0);
x_87 = lean_array_mk(x_83);
x_88 = lean_ptr_addr(x_71);
lean_dec(x_71);
x_89 = lean_ptr_addr(x_86);
x_90 = lean_usize_dec_eq(x_88, x_89);
if (x_90 == 0)
{
uint8_t x_91; 
x_91 = !lean_is_exclusive(x_1);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; 
x_92 = lean_ctor_get(x_1, 0);
lean_dec(x_92);
lean_ctor_set(x_51, 3, x_86);
x_93 = l_Lean_Compiler_LCNF_attachCodeDecls(x_87, x_1);
lean_dec(x_87);
lean_ctor_set(x_84, 0, x_93);
return x_84;
}
else
{
lean_object* x_94; lean_object* x_95; 
lean_dec(x_1);
lean_ctor_set(x_51, 3, x_86);
x_94 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_94, 0, x_51);
x_95 = l_Lean_Compiler_LCNF_attachCodeDecls(x_87, x_94);
lean_dec(x_87);
lean_ctor_set(x_84, 0, x_95);
return x_84;
}
}
else
{
size_t x_96; uint8_t x_97; 
x_96 = lean_ptr_addr(x_69);
x_97 = lean_usize_dec_eq(x_96, x_96);
if (x_97 == 0)
{
uint8_t x_98; 
x_98 = !lean_is_exclusive(x_1);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; 
x_99 = lean_ctor_get(x_1, 0);
lean_dec(x_99);
lean_ctor_set(x_51, 3, x_86);
x_100 = l_Lean_Compiler_LCNF_attachCodeDecls(x_87, x_1);
lean_dec(x_87);
lean_ctor_set(x_84, 0, x_100);
return x_84;
}
else
{
lean_object* x_101; lean_object* x_102; 
lean_dec(x_1);
lean_ctor_set(x_51, 3, x_86);
x_101 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_101, 0, x_51);
x_102 = l_Lean_Compiler_LCNF_attachCodeDecls(x_87, x_101);
lean_dec(x_87);
lean_ctor_set(x_84, 0, x_102);
return x_84;
}
}
else
{
uint8_t x_103; 
x_103 = lean_name_eq(x_70, x_70);
if (x_103 == 0)
{
uint8_t x_104; 
x_104 = !lean_is_exclusive(x_1);
if (x_104 == 0)
{
lean_object* x_105; lean_object* x_106; 
x_105 = lean_ctor_get(x_1, 0);
lean_dec(x_105);
lean_ctor_set(x_51, 3, x_86);
x_106 = l_Lean_Compiler_LCNF_attachCodeDecls(x_87, x_1);
lean_dec(x_87);
lean_ctor_set(x_84, 0, x_106);
return x_84;
}
else
{
lean_object* x_107; lean_object* x_108; 
lean_dec(x_1);
lean_ctor_set(x_51, 3, x_86);
x_107 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_107, 0, x_51);
x_108 = l_Lean_Compiler_LCNF_attachCodeDecls(x_87, x_107);
lean_dec(x_87);
lean_ctor_set(x_84, 0, x_108);
return x_84;
}
}
else
{
lean_object* x_109; 
lean_dec(x_86);
lean_free_object(x_51);
lean_dec(x_70);
lean_dec(x_69);
lean_dec(x_68);
x_109 = l_Lean_Compiler_LCNF_attachCodeDecls(x_87, x_1);
lean_dec(x_87);
lean_ctor_set(x_84, 0, x_109);
return x_84;
}
}
}
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; size_t x_113; size_t x_114; uint8_t x_115; 
x_110 = lean_ctor_get(x_84, 0);
x_111 = lean_ctor_get(x_84, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_84);
x_112 = lean_array_mk(x_83);
x_113 = lean_ptr_addr(x_71);
lean_dec(x_71);
x_114 = lean_ptr_addr(x_110);
x_115 = lean_usize_dec_eq(x_113, x_114);
if (x_115 == 0)
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_116 = x_1;
} else {
 lean_dec_ref(x_1);
 x_116 = lean_box(0);
}
lean_ctor_set(x_51, 3, x_110);
if (lean_is_scalar(x_116)) {
 x_117 = lean_alloc_ctor(4, 1, 0);
} else {
 x_117 = x_116;
}
lean_ctor_set(x_117, 0, x_51);
x_118 = l_Lean_Compiler_LCNF_attachCodeDecls(x_112, x_117);
lean_dec(x_112);
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_111);
return x_119;
}
else
{
size_t x_120; uint8_t x_121; 
x_120 = lean_ptr_addr(x_69);
x_121 = lean_usize_dec_eq(x_120, x_120);
if (x_121 == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_122 = x_1;
} else {
 lean_dec_ref(x_1);
 x_122 = lean_box(0);
}
lean_ctor_set(x_51, 3, x_110);
if (lean_is_scalar(x_122)) {
 x_123 = lean_alloc_ctor(4, 1, 0);
} else {
 x_123 = x_122;
}
lean_ctor_set(x_123, 0, x_51);
x_124 = l_Lean_Compiler_LCNF_attachCodeDecls(x_112, x_123);
lean_dec(x_112);
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_124);
lean_ctor_set(x_125, 1, x_111);
return x_125;
}
else
{
uint8_t x_126; 
x_126 = lean_name_eq(x_70, x_70);
if (x_126 == 0)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_127 = x_1;
} else {
 lean_dec_ref(x_1);
 x_127 = lean_box(0);
}
lean_ctor_set(x_51, 3, x_110);
if (lean_is_scalar(x_127)) {
 x_128 = lean_alloc_ctor(4, 1, 0);
} else {
 x_128 = x_127;
}
lean_ctor_set(x_128, 0, x_51);
x_129 = l_Lean_Compiler_LCNF_attachCodeDecls(x_112, x_128);
lean_dec(x_112);
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_111);
return x_130;
}
else
{
lean_object* x_131; lean_object* x_132; 
lean_dec(x_110);
lean_free_object(x_51);
lean_dec(x_70);
lean_dec(x_69);
lean_dec(x_68);
x_131 = l_Lean_Compiler_LCNF_attachCodeDecls(x_112, x_1);
lean_dec(x_112);
x_132 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_132, 0, x_131);
lean_ctor_set(x_132, 1, x_111);
return x_132;
}
}
}
}
}
else
{
uint8_t x_133; 
lean_dec(x_83);
lean_free_object(x_51);
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_1);
x_133 = !lean_is_exclusive(x_84);
if (x_133 == 0)
{
return x_84;
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_134 = lean_ctor_get(x_84, 0);
x_135 = lean_ctor_get(x_84, 1);
lean_inc(x_135);
lean_inc(x_134);
lean_dec(x_84);
x_136 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_136, 0, x_134);
lean_ctor_set(x_136, 1, x_135);
return x_136;
}
}
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; size_t x_141; size_t x_142; lean_object* x_143; lean_object* x_144; size_t x_145; size_t x_146; size_t x_147; size_t x_148; size_t x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_137 = lean_ctor_get(x_51, 0);
x_138 = lean_ctor_get(x_51, 1);
x_139 = lean_ctor_get(x_51, 2);
x_140 = lean_ctor_get(x_51, 3);
lean_inc(x_140);
lean_inc(x_139);
lean_inc(x_138);
lean_inc(x_137);
lean_dec(x_51);
x_141 = lean_array_size(x_140);
x_142 = 0;
x_143 = lean_ctor_get(x_66, 1);
lean_inc(x_143);
x_144 = lean_array_get_size(x_143);
x_145 = lean_usize_of_nat(x_144);
lean_dec(x_144);
x_146 = 1;
x_147 = lean_usize_sub(x_145, x_146);
x_148 = l_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___closed__6;
x_149 = lean_usize_land(x_148, x_147);
x_150 = lean_array_uget(x_143, x_149);
lean_dec(x_143);
x_151 = lean_box(2);
x_152 = l_Std_DHashMap_Internal_AssocList_get_x21___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__1(x_65, x_151, x_150);
lean_dec(x_150);
lean_inc(x_140);
x_153 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__3(x_65, x_66, x_66, x_141, x_142, x_140, x_2, x_3, x_4, x_5, x_6, x_64);
lean_dec(x_2);
lean_dec(x_66);
if (lean_obj_tag(x_153) == 0)
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; size_t x_158; size_t x_159; uint8_t x_160; 
x_154 = lean_ctor_get(x_153, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_153, 1);
lean_inc(x_155);
if (lean_is_exclusive(x_153)) {
 lean_ctor_release(x_153, 0);
 lean_ctor_release(x_153, 1);
 x_156 = x_153;
} else {
 lean_dec_ref(x_153);
 x_156 = lean_box(0);
}
x_157 = lean_array_mk(x_152);
x_158 = lean_ptr_addr(x_140);
lean_dec(x_140);
x_159 = lean_ptr_addr(x_154);
x_160 = lean_usize_dec_eq(x_158, x_159);
if (x_160 == 0)
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_161 = x_1;
} else {
 lean_dec_ref(x_1);
 x_161 = lean_box(0);
}
x_162 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_162, 0, x_137);
lean_ctor_set(x_162, 1, x_138);
lean_ctor_set(x_162, 2, x_139);
lean_ctor_set(x_162, 3, x_154);
if (lean_is_scalar(x_161)) {
 x_163 = lean_alloc_ctor(4, 1, 0);
} else {
 x_163 = x_161;
}
lean_ctor_set(x_163, 0, x_162);
x_164 = l_Lean_Compiler_LCNF_attachCodeDecls(x_157, x_163);
lean_dec(x_157);
if (lean_is_scalar(x_156)) {
 x_165 = lean_alloc_ctor(0, 2, 0);
} else {
 x_165 = x_156;
}
lean_ctor_set(x_165, 0, x_164);
lean_ctor_set(x_165, 1, x_155);
return x_165;
}
else
{
size_t x_166; uint8_t x_167; 
x_166 = lean_ptr_addr(x_138);
x_167 = lean_usize_dec_eq(x_166, x_166);
if (x_167 == 0)
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_168 = x_1;
} else {
 lean_dec_ref(x_1);
 x_168 = lean_box(0);
}
x_169 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_169, 0, x_137);
lean_ctor_set(x_169, 1, x_138);
lean_ctor_set(x_169, 2, x_139);
lean_ctor_set(x_169, 3, x_154);
if (lean_is_scalar(x_168)) {
 x_170 = lean_alloc_ctor(4, 1, 0);
} else {
 x_170 = x_168;
}
lean_ctor_set(x_170, 0, x_169);
x_171 = l_Lean_Compiler_LCNF_attachCodeDecls(x_157, x_170);
lean_dec(x_157);
if (lean_is_scalar(x_156)) {
 x_172 = lean_alloc_ctor(0, 2, 0);
} else {
 x_172 = x_156;
}
lean_ctor_set(x_172, 0, x_171);
lean_ctor_set(x_172, 1, x_155);
return x_172;
}
else
{
uint8_t x_173; 
x_173 = lean_name_eq(x_139, x_139);
if (x_173 == 0)
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_174 = x_1;
} else {
 lean_dec_ref(x_1);
 x_174 = lean_box(0);
}
x_175 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_175, 0, x_137);
lean_ctor_set(x_175, 1, x_138);
lean_ctor_set(x_175, 2, x_139);
lean_ctor_set(x_175, 3, x_154);
if (lean_is_scalar(x_174)) {
 x_176 = lean_alloc_ctor(4, 1, 0);
} else {
 x_176 = x_174;
}
lean_ctor_set(x_176, 0, x_175);
x_177 = l_Lean_Compiler_LCNF_attachCodeDecls(x_157, x_176);
lean_dec(x_157);
if (lean_is_scalar(x_156)) {
 x_178 = lean_alloc_ctor(0, 2, 0);
} else {
 x_178 = x_156;
}
lean_ctor_set(x_178, 0, x_177);
lean_ctor_set(x_178, 1, x_155);
return x_178;
}
else
{
lean_object* x_179; lean_object* x_180; 
lean_dec(x_154);
lean_dec(x_139);
lean_dec(x_138);
lean_dec(x_137);
x_179 = l_Lean_Compiler_LCNF_attachCodeDecls(x_157, x_1);
lean_dec(x_157);
if (lean_is_scalar(x_156)) {
 x_180 = lean_alloc_ctor(0, 2, 0);
} else {
 x_180 = x_156;
}
lean_ctor_set(x_180, 0, x_179);
lean_ctor_set(x_180, 1, x_155);
return x_180;
}
}
}
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
lean_dec(x_152);
lean_dec(x_140);
lean_dec(x_139);
lean_dec(x_138);
lean_dec(x_137);
lean_dec(x_1);
x_181 = lean_ctor_get(x_153, 0);
lean_inc(x_181);
x_182 = lean_ctor_get(x_153, 1);
lean_inc(x_182);
if (lean_is_exclusive(x_153)) {
 lean_ctor_release(x_153, 0);
 lean_ctor_release(x_153, 1);
 x_183 = x_153;
} else {
 lean_dec_ref(x_153);
 x_183 = lean_box(0);
}
if (lean_is_scalar(x_183)) {
 x_184 = lean_alloc_ctor(1, 2, 0);
} else {
 x_184 = x_183;
}
lean_ctor_set(x_184, 0, x_181);
lean_ctor_set(x_184, 1, x_182);
return x_184;
}
}
}
else
{
uint8_t x_185; 
lean_dec(x_58);
lean_dec(x_51);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_185 = !lean_is_exclusive(x_60);
if (x_185 == 0)
{
return x_60;
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_186 = lean_ctor_get(x_60, 0);
x_187 = lean_ctor_get(x_60, 1);
lean_inc(x_187);
lean_inc(x_186);
lean_dec(x_60);
x_188 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_188, 0, x_186);
lean_ctor_set(x_188, 1, x_187);
return x_188;
}
}
}
else
{
uint8_t x_189; 
lean_dec(x_51);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_189 = !lean_is_exclusive(x_52);
if (x_189 == 0)
{
return x_52;
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_190 = lean_ctor_get(x_52, 0);
x_191 = lean_ctor_get(x_52, 1);
lean_inc(x_191);
lean_inc(x_190);
lean_dec(x_52);
x_192 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_192, 0, x_190);
lean_ctor_set(x_192, 1, x_191);
return x_192;
}
}
}
default: 
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_193 = lean_array_mk(x_2);
x_194 = l_Array_reverse___rarg(x_193);
x_195 = l_Lean_Compiler_LCNF_attachCodeDecls(x_194, x_1);
lean_dec(x_194);
x_196 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_196, 0, x_195);
lean_ctor_set(x_196, 1, x_7);
return x_196;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_isTracingEnabledFor___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_addTrace___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__3___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__3___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_14 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_15 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__3(x_1, x_2, x_3, x_13, x_14, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_floatLetIn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_1);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
x_10 = lean_ctor_get(x_1, 2);
x_11 = lean_ctor_get(x_1, 3);
x_12 = lean_ctor_get(x_1, 4);
x_13 = lean_ctor_get(x_1, 5);
x_14 = lean_box(0);
x_15 = l_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go(x_12, x_14, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_15, 0);
lean_ctor_set(x_1, 4, x_17);
lean_ctor_set(x_15, 0, x_1);
return x_15;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_15, 0);
x_19 = lean_ctor_get(x_15, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_15);
lean_ctor_set(x_1, 4, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_1);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
else
{
uint8_t x_21; 
lean_free_object(x_1);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_21 = !lean_is_exclusive(x_15);
if (x_21 == 0)
{
return x_15;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_15, 0);
x_23 = lean_ctor_get(x_15, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_15);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_25 = lean_ctor_get(x_1, 0);
x_26 = lean_ctor_get(x_1, 1);
x_27 = lean_ctor_get(x_1, 2);
x_28 = lean_ctor_get(x_1, 3);
x_29 = lean_ctor_get(x_1, 4);
x_30 = lean_ctor_get_uint8(x_1, sizeof(void*)*6);
x_31 = lean_ctor_get_uint8(x_1, sizeof(void*)*6 + 1);
x_32 = lean_ctor_get(x_1, 5);
lean_inc(x_32);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_1);
x_33 = lean_box(0);
x_34 = l_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go(x_29, x_33, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_37 = x_34;
} else {
 lean_dec_ref(x_34);
 x_37 = lean_box(0);
}
x_38 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_38, 0, x_25);
lean_ctor_set(x_38, 1, x_26);
lean_ctor_set(x_38, 2, x_27);
lean_ctor_set(x_38, 3, x_28);
lean_ctor_set(x_38, 4, x_35);
lean_ctor_set(x_38, 5, x_32);
lean_ctor_set_uint8(x_38, sizeof(void*)*6, x_30);
lean_ctor_set_uint8(x_38, sizeof(void*)*6 + 1, x_31);
if (lean_is_scalar(x_37)) {
 x_39 = lean_alloc_ctor(0, 2, 0);
} else {
 x_39 = x_37;
}
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_36);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_32);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
x_40 = lean_ctor_get(x_34, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_34, 1);
lean_inc(x_41);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_42 = x_34;
} else {
 lean_dec_ref(x_34);
 x_42 = lean_box(0);
}
if (lean_is_scalar(x_42)) {
 x_43 = lean_alloc_ctor(1, 2, 0);
} else {
 x_43 = x_42;
}
lean_ctor_set(x_43, 0, x_40);
lean_ctor_set(x_43, 1, x_41);
return x_43;
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
static lean_object* _init_l_Lean_Compiler_LCNF_floatLetIn___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__3___closed__2;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_floatLetIn___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Decl_floatLetIn), 6, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_floatLetIn(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Lean_Compiler_LCNF_floatLetIn___closed__1;
x_4 = l_Lean_Compiler_LCNF_floatLetIn___closed__2;
x_5 = l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(x_3, x_4, x_1, x_2);
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
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2298____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2298____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2298____closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2298____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2298____closed__2;
x_2 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__3___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2298____closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("LCNF", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2298____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2298____closed__3;
x_2 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2298____closed__4;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2298____closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("initFn", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2298____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2298____closed__5;
x_2 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2298____closed__6;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2298____closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_@", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2298____closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2298____closed__7;
x_2 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2298____closed__8;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2298____closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2298____closed__9;
x_2 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2298____closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2298____closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2298____closed__10;
x_2 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__3___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2298____closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2298____closed__11;
x_2 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2298____closed__4;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2298____closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("FloatLetIn", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2298____closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2298____closed__12;
x_2 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2298____closed__13;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2298____closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_hyg", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2298____closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2298____closed__14;
x_2 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2298____closed__15;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2298____closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2298____closed__16;
x_2 = lean_unsigned_to_nat(2298u);
x_3 = l_Lean_Name_num___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2298_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__3___closed__3;
x_3 = 1;
x_4 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2298____closed__17;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
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
l_Lean_Compiler_LCNF_FloatLetIn_instHashableDecision___closed__1 = _init_l_Lean_Compiler_LCNF_FloatLetIn_instHashableDecision___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_FloatLetIn_instHashableDecision___closed__1);
l_Lean_Compiler_LCNF_FloatLetIn_instHashableDecision = _init_l_Lean_Compiler_LCNF_FloatLetIn_instHashableDecision();
lean_mark_persistent(l_Lean_Compiler_LCNF_FloatLetIn_instHashableDecision);
l_Lean_Compiler_LCNF_FloatLetIn_instBEqDecision___closed__1 = _init_l_Lean_Compiler_LCNF_FloatLetIn_instBEqDecision___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_FloatLetIn_instBEqDecision___closed__1);
l_Lean_Compiler_LCNF_FloatLetIn_instBEqDecision = _init_l_Lean_Compiler_LCNF_FloatLetIn_instBEqDecision();
lean_mark_persistent(l_Lean_Compiler_LCNF_FloatLetIn_instBEqDecision);
l_Lean_Compiler_LCNF_FloatLetIn_instInhabitedDecision___closed__1 = _init_l_Lean_Compiler_LCNF_FloatLetIn_instInhabitedDecision___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_FloatLetIn_instInhabitedDecision___closed__1);
l_Lean_Compiler_LCNF_FloatLetIn_instInhabitedDecision = _init_l_Lean_Compiler_LCNF_FloatLetIn_instInhabitedDecision();
lean_mark_persistent(l_Lean_Compiler_LCNF_FloatLetIn_instInhabitedDecision);
l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__1 = _init_l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__1();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__1);
l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__2 = _init_l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__2();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__2);
l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__3 = _init_l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__3();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__3);
l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__4 = _init_l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__4();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__4);
l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__5 = _init_l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__5();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__5);
l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__6 = _init_l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__6();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__6);
l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__7 = _init_l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__7();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__7);
l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__8 = _init_l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__8();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__8);
l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__9 = _init_l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__9();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__9);
l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__10 = _init_l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__10();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__10);
l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__11 = _init_l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__11();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__11);
l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__12 = _init_l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__12();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__12);
l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__13 = _init_l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__13();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__13);
l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__14 = _init_l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__14();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__14);
l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__15 = _init_l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__15();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__15);
l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__16 = _init_l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__16();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__16);
l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__17 = _init_l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__17();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__17);
l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__18 = _init_l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__18();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__18);
l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__19 = _init_l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__19();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__19);
l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__20 = _init_l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__20();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__20);
l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__21 = _init_l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__21();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__21);
l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__22 = _init_l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__22();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__22);
l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__23 = _init_l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__23();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__23);
l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision___closed__1 = _init_l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision___closed__1);
l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision = _init_l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision();
lean_mark_persistent(l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision);
l_panic___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__3___closed__1 = _init_l_panic___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__3___closed__1();
lean_mark_persistent(l_panic___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__3___closed__1);
l_panic___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__3___closed__2 = _init_l_panic___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__3___closed__2();
lean_mark_persistent(l_panic___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__3___closed__2);
l_panic___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__3___closed__3 = _init_l_panic___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__3___closed__3();
lean_mark_persistent(l_panic___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__3___closed__3);
l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__2___closed__1 = _init_l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__2___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__2___closed__1);
l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__2___closed__2 = _init_l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__2___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__2___closed__2);
l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__2___closed__3 = _init_l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__2___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__2___closed__3);
l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__2___closed__4 = _init_l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__2___closed__4();
lean_mark_persistent(l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__2___closed__4);
l_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___closed__1 = _init_l_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___closed__1();
l_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___closed__2 = _init_l_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___closed__2();
l_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___closed__3 = _init_l_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___closed__3();
l_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___closed__4 = _init_l_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___closed__4();
l_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___closed__5 = _init_l_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___closed__5();
l_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___closed__6 = _init_l_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___closed__6();
l_Std_DHashMap_Internal_AssocList_get_x21___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__1___closed__1 = _init_l_Std_DHashMap_Internal_AssocList_get_x21___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__1___closed__1();
lean_mark_persistent(l_Std_DHashMap_Internal_AssocList_get_x21___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__1___closed__1);
l_Std_DHashMap_Internal_AssocList_get_x21___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__1___closed__2 = _init_l_Std_DHashMap_Internal_AssocList_get_x21___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__1___closed__2();
lean_mark_persistent(l_Std_DHashMap_Internal_AssocList_get_x21___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__1___closed__2);
l_Std_DHashMap_Internal_AssocList_get_x21___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__1___closed__3 = _init_l_Std_DHashMap_Internal_AssocList_get_x21___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__1___closed__3();
lean_mark_persistent(l_Std_DHashMap_Internal_AssocList_get_x21___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__1___closed__3);
l_Std_DHashMap_Internal_AssocList_get_x21___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__1___closed__4 = _init_l_Std_DHashMap_Internal_AssocList_get_x21___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__1___closed__4();
lean_mark_persistent(l_Std_DHashMap_Internal_AssocList_get_x21___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__1___closed__4);
l_Lean_Compiler_LCNF_FloatLetIn_dontFloat___closed__1 = _init_l_Lean_Compiler_LCNF_FloatLetIn_dontFloat___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_FloatLetIn_dontFloat___closed__1);
l_Lean_isTracingEnabledFor___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__1___closed__1 = _init_l_Lean_isTracingEnabledFor___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__1___closed__1();
lean_mark_persistent(l_Lean_isTracingEnabledFor___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__1___closed__1);
l_Lean_addTrace___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__2___closed__1 = _init_l_Lean_addTrace___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__2___closed__1();
lean_mark_persistent(l_Lean_addTrace___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__2___closed__1);
l_Lean_addTrace___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__2___closed__2 = _init_l_Lean_addTrace___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__2___closed__2();
lean_mark_persistent(l_Lean_addTrace___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__2___closed__2);
l_Lean_addTrace___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__2___closed__3 = _init_l_Lean_addTrace___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__2___closed__3();
lean_mark_persistent(l_Lean_addTrace___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__2___closed__3);
l_Lean_addTrace___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__2___closed__4 = _init_l_Lean_addTrace___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__2___closed__4();
l_Lean_addTrace___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__2___closed__5 = _init_l_Lean_addTrace___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__2___closed__5();
lean_mark_persistent(l_Lean_addTrace___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__2___closed__5);
l_Lean_addTrace___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__2___closed__6 = _init_l_Lean_addTrace___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__2___closed__6();
lean_mark_persistent(l_Lean_addTrace___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__2___closed__6);
l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__3___closed__1 = _init_l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__3___closed__1();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__3___closed__1);
l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__3___closed__2 = _init_l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__3___closed__2();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__3___closed__2);
l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__3___closed__3 = _init_l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__3___closed__3();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__3___closed__3);
l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__3___closed__4 = _init_l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__3___closed__4();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__3___closed__4);
l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__3___closed__5 = _init_l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__3___closed__5();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__3___closed__5);
l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__3___closed__6 = _init_l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__3___closed__6();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__3___closed__6);
l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__3___closed__7 = _init_l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__3___closed__7();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__3___closed__7);
l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__3___closed__8 = _init_l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__3___closed__8();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__3___closed__8);
l_Lean_Compiler_LCNF_floatLetIn___closed__1 = _init_l_Lean_Compiler_LCNF_floatLetIn___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_floatLetIn___closed__1);
l_Lean_Compiler_LCNF_floatLetIn___closed__2 = _init_l_Lean_Compiler_LCNF_floatLetIn___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_floatLetIn___closed__2);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2298____closed__1 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2298____closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2298____closed__1);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2298____closed__2 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2298____closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2298____closed__2);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2298____closed__3 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2298____closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2298____closed__3);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2298____closed__4 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2298____closed__4();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2298____closed__4);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2298____closed__5 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2298____closed__5();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2298____closed__5);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2298____closed__6 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2298____closed__6();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2298____closed__6);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2298____closed__7 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2298____closed__7();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2298____closed__7);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2298____closed__8 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2298____closed__8();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2298____closed__8);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2298____closed__9 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2298____closed__9();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2298____closed__9);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2298____closed__10 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2298____closed__10();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2298____closed__10);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2298____closed__11 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2298____closed__11();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2298____closed__11);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2298____closed__12 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2298____closed__12();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2298____closed__12);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2298____closed__13 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2298____closed__13();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2298____closed__13);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2298____closed__14 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2298____closed__14();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2298____closed__14);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2298____closed__15 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2298____closed__15();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2298____closed__15);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2298____closed__16 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2298____closed__16();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2298____closed__16);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2298____closed__17 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2298____closed__17();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2298____closed__17);
if (builtin) {res = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2298_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
