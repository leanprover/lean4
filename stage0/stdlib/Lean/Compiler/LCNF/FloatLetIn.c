// Lean compiler output
// Module: Lean.Compiler.LCNF.FloatLetIn
// Imports: Init Lean.Compiler.LCNF.CompilerM Lean.Compiler.LCNF.FVarUtil Lean.Compiler.LCNF.PassManager Lean.Compiler.LCNF.Types
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_withNewCandidate___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_reprPrec(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___spec__2___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__15___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__16(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_beqDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_60____boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2249____closed__17;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__20;
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2249____closed__4;
LEAN_EXPORT lean_object* l_Lean_mkHashMap___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___spec__1(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2249____closed__10;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__18(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__9(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__2;
static lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__7;
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___spec__2___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_foldlM___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
LEAN_EXPORT uint8_t l_Lean_HashMapImp_contains___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__15;
LEAN_EXPORT lean_object* l_Lean_AssocList_find_x3f___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__2___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2249____closed__16;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_withNewScope___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_push___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_floatLetIn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_instHashableDecision;
LEAN_EXPORT lean_object* l_Lean_HashMapImp_moveEntries___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__6(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadReaderT___rarg(lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkHashMap___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2249____closed__12;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_hashDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_14____boxed(lean_object*);
static lean_object* l_panic___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__3___closed__1;
lean_object* l_Lean_stringToMessageData(lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__2___closed__3;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_ignore_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_ignore_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__13;
static lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__17;
lean_object* l_Lean_Compiler_LCNF_LCtx_toLocalContext(lean_object*);
static lean_object* l_Lean_addTrace___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__2___closed__2;
LEAN_EXPORT uint8_t l_Lean_AssocList_contains___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__3(lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__22;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__16;
extern lean_object* l_instInhabitedPUnit;
static lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__21;
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__3___closed__8;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addTrace___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__2___closed__5;
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2249____closed__3;
LEAN_EXPORT lean_object* l_Lean_AssocList_contains___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__3___boxed(lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
static lean_object* l_Lean_addTrace___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__2___closed__7;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_BaseFloatContext_decls___default;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkHashMap___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___spec__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__11;
lean_object* l_Array_reverse___rarg(lean_object*);
static lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__19;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__10(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_floatLetIn___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkHashMap___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__1(lean_object*);
static lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__9;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashMapImp_contains___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashMapImp_moveEntries___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__3(lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_find_x3f___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__2(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_floatLetIn___closed__2;
static lean_object* l_Lean_Compiler_LCNF_floatLetIn___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__15___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_FloatLetIn_instHashableDecision___closed__1;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__3___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2249____closed__15;
uint64_t l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1674_(lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160_(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabited___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_AltCore_getCode(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_FloatLetIn_instInhabitedDecision___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_floatLetIn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2249____closed__8;
static lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__12;
LEAN_EXPORT lean_object* l_panic___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2249____closed__6;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__15(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_FloatLetIn_dontFloat___closed__3;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__16(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_lengthTRAux___rarg(lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__10;
LEAN_EXPORT uint64_t l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_hashDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_14_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_float_goFVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__3___closed__9;
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__3___closed__6;
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__9(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__8;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__11(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__3___closed__4;
static lean_object* l_Lean_addTrace___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__2___closed__3;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__19(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_contains___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_floatLetIn(uint8_t, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2249____closed__14;
static lean_object* l_Lean_isTracingEnabledFor___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__1___closed__1;
static lean_object* l_Lean_addTrace___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__2___closed__4;
static lean_object* l_List_forIn_loop___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases___spec__1___closed__1;
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2249____closed__9;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__9(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_hashmap_mk_idx(lean_object*, uint64_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashMap_insert___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__2(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_inheritedTraceOptions;
static lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__1;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_attachCodeDecls(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_find_x3f___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__2(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_FloatLetIn_dontFloat___closed__1;
static lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__4;
LEAN_EXPORT lean_object* l_Lean_AssocList_replace___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__8(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2249____closed__13;
static lean_object* l_Lean_Compiler_LCNF_FloatLetIn_dontFloat___closed__2;
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__3___closed__2;
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_float___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__14(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_float___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addTrace___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__2___closed__1;
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_float_goFVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__3___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_AltCore_forCodeM___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_initialNewArms(lean_object*);
static lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__6;
static lean_object* l_panic___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__3___closed__2;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__3___closed__7;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2249____closed__1;
LEAN_EXPORT lean_object* l_Lean_HashMap_insert___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__3(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_FloatLetIn_dontFloat___closed__4;
static lean_object* l_panic___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__3___closed__3;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_dontFloat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__14;
static lean_object* l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_HashMapImp_find_x3f___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goCases(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashMapImp_expand___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2249_(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2249____closed__2;
uint64_t l_Lean_Name_hash___override(lean_object*);
static lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__3;
LEAN_EXPORT lean_object* l_Lean_AssocList_find_x3f___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__12(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_CodeDecl_fvarId(lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__3___closed__3;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_withNewScope(lean_object*);
LEAN_EXPORT uint8_t l_Lean_AssocList_contains___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__18;
LEAN_EXPORT lean_object* l_Lean_HashMapImp_expand___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__5(lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__3___closed__5;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_beqDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_60_(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseCodeDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashMapImp_find_x3f___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__15(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_float(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___rarg(lean_object*);
static lean_object* l_Lean_addTrace___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__2___closed__6;
static lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__23;
size_t lean_usize_sub(size_t, size_t);
static lean_object* l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__2___closed__2;
lean_object* l_Lean_mkHashMapImp___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_FloatLetIn_dontFloat___closed__5;
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_instBEqDecision;
lean_object* l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_Compiler_LCNF_FloatLetIn_float___spec__1(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
static lean_object* l_Lean_Compiler_LCNF_FloatLetIn_instBEqDecision___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_withNewCandidate(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_foldlM___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__7(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_redLength___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_AltCore_forCodeM___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_withNewScope___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2249____closed__7;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goCases___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__3___closed__1;
static lean_object* l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__2___closed__4;
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__8(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160____closed__5;
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__14(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_Decision_ofAlt___boxed(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2249____closed__11;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__10(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_isArrowClass_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_replace___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__7(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_repr(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goCases___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_toArrayAux___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_Decision_ofAlt(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__8(lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l___private_Lean_Data_HashMap_0__Lean_numBucketsForCapacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2249____closed__5;
static lean_object* l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision___closed__1;
LEAN_EXPORT uint64_t l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_hashDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_14_(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_hashDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_14____boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_hashDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_14_(x_1);
lean_dec(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_FloatLetIn_instHashableDecision___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_hashDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_14____boxed), 1, 0);
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
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_beqDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_60_(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_beqDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_60____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_beqDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_60_(x_1, x_2);
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
x_1 = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_beqDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_60____boxed), 2, 0);
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
x_1 = lean_mk_string_from_bytes("Lean.Compiler.LCNF.FloatLetIn.Decision.arm", 42);
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
x_1 = lean_mk_string_from_bytes("Lean.Compiler.LCNF.FloatLetIn.Decision.default", 46);
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
x_1 = lean_mk_string_from_bytes("Lean.Compiler.LCNF.FloatLetIn.Decision.dont", 43);
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
x_1 = lean_mk_string_from_bytes("Lean.Compiler.LCNF.FloatLetIn.Decision.unknown", 46);
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
static lean_object* _init_l_Lean_Compiler_LCNF_FloatLetIn_BaseFloatContext_decls___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
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
LEAN_EXPORT lean_object* l_Lean_AssocList_find_x3f___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__2(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_HashMapImp_find_x3f___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint64_t x_5; size_t x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_array_get_size(x_3);
x_5 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1674_(x_2);
x_6 = lean_hashmap_mk_idx(x_4, x_5);
x_7 = lean_array_uget(x_3, x_6);
lean_dec(x_3);
x_8 = l_Lean_AssocList_find_x3f___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__2(x_2, x_7);
lean_dec(x_7);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT uint8_t l_Lean_AssocList_contains___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__4(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_AssocList_foldlM___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__7(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_array_get_size(x_1);
x_7 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1674_(x_4);
x_8 = lean_hashmap_mk_idx(x_6, x_7);
x_9 = lean_array_uget(x_1, x_8);
lean_ctor_set(x_2, 2, x_9);
x_10 = lean_array_uset(x_1, x_8, x_2);
x_1 = x_10;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint64_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_ctor_get(x_2, 1);
x_14 = lean_ctor_get(x_2, 2);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_2);
x_15 = lean_array_get_size(x_1);
x_16 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1674_(x_12);
x_17 = lean_hashmap_mk_idx(x_15, x_16);
x_18 = lean_array_uget(x_1, x_17);
x_19 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_19, 0, x_12);
lean_ctor_set(x_19, 1, x_13);
lean_ctor_set(x_19, 2, x_18);
x_20 = lean_array_uset(x_1, x_17, x_19);
x_1 = x_20;
x_2 = x_14;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_HashMapImp_moveEntries___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_Lean_AssocList_foldlM___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__7(x_3, x_6);
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
LEAN_EXPORT lean_object* l_Lean_HashMapImp_expand___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_unsigned_to_nat(2u);
x_5 = lean_nat_mul(x_3, x_4);
lean_dec(x_3);
x_6 = lean_box(0);
x_7 = lean_mk_array(x_5, x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Lean_HashMapImp_moveEntries___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__6(x_8, x_2, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_replace___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_10 = l_Lean_AssocList_replace___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__8(x_1, x_2, x_8);
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
x_15 = l_Lean_AssocList_replace___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__8(x_1, x_2, x_13);
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
LEAN_EXPORT lean_object* l_Lean_HashMap_insert___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint64_t x_8; size_t x_9; lean_object* x_10; uint8_t x_11; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_array_get_size(x_6);
x_8 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1674_(x_2);
lean_inc(x_7);
x_9 = lean_hashmap_mk_idx(x_7, x_8);
x_10 = lean_array_uget(x_6, x_9);
x_11 = l_Lean_AssocList_contains___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__4(x_2, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_5, x_12);
lean_dec(x_5);
x_14 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_14, 0, x_2);
lean_ctor_set(x_14, 1, x_3);
lean_ctor_set(x_14, 2, x_10);
x_15 = lean_array_uset(x_6, x_9, x_14);
x_16 = l___private_Lean_Data_HashMap_0__Lean_numBucketsForCapacity(x_13);
x_17 = lean_nat_dec_le(x_16, x_7);
lean_dec(x_7);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
lean_free_object(x_1);
x_18 = l_Lean_HashMapImp_expand___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__5(x_13, x_15);
return x_18;
}
else
{
lean_ctor_set(x_1, 1, x_15);
lean_ctor_set(x_1, 0, x_13);
return x_1;
}
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_7);
x_19 = l_Lean_AssocList_replace___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__8(x_2, x_3, x_10);
x_20 = lean_array_uset(x_6, x_9, x_19);
lean_ctor_set(x_1, 1, x_20);
return x_1;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint64_t x_24; size_t x_25; lean_object* x_26; uint8_t x_27; 
x_21 = lean_ctor_get(x_1, 0);
x_22 = lean_ctor_get(x_1, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_1);
x_23 = lean_array_get_size(x_22);
x_24 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1674_(x_2);
lean_inc(x_23);
x_25 = lean_hashmap_mk_idx(x_23, x_24);
x_26 = lean_array_uget(x_22, x_25);
x_27 = l_Lean_AssocList_contains___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__4(x_2, x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_add(x_21, x_28);
lean_dec(x_21);
x_30 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_30, 0, x_2);
lean_ctor_set(x_30, 1, x_3);
lean_ctor_set(x_30, 2, x_26);
x_31 = lean_array_uset(x_22, x_25, x_30);
x_32 = l___private_Lean_Data_HashMap_0__Lean_numBucketsForCapacity(x_29);
x_33 = lean_nat_dec_le(x_32, x_23);
lean_dec(x_23);
lean_dec(x_32);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = l_Lean_HashMapImp_expand___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__5(x_29, x_31);
return x_34;
}
else
{
lean_object* x_35; 
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_29);
lean_ctor_set(x_35, 1, x_31);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_23);
x_36 = l_Lean_AssocList_replace___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__8(x_2, x_3, x_26);
x_37 = lean_array_uset(x_22, x_25, x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_21);
lean_ctor_set(x_38, 1, x_37);
return x_38;
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
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_2);
x_14 = l_Lean_HashMapImp_find_x3f___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__1(x_12, x_2);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
lean_dec(x_2);
lean_dec(x_1);
x_15 = lean_box(0);
lean_ctor_set(x_10, 0, x_15);
return x_10;
}
else
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_box(3);
x_18 = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_beqDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_60_(x_16, x_17);
if (x_18 == 0)
{
uint8_t x_19; 
x_19 = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_beqDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_60_(x_16, x_1);
lean_dec(x_1);
lean_dec(x_16);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
lean_free_object(x_10);
x_20 = lean_st_ref_take(x_3, x_13);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_box(2);
x_24 = l_Lean_HashMap_insert___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__3(x_21, x_2, x_23);
x_25 = lean_st_ref_set(x_3, x_24, x_22);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_25, 0);
lean_dec(x_27);
x_28 = lean_box(0);
lean_ctor_set(x_25, 0, x_28);
return x_25;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_25, 1);
lean_inc(x_29);
lean_dec(x_25);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
else
{
lean_object* x_32; 
lean_dec(x_2);
x_32 = lean_box(0);
lean_ctor_set(x_10, 0, x_32);
return x_10;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
lean_dec(x_16);
lean_free_object(x_10);
x_33 = lean_st_ref_take(x_3, x_13);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = l_Lean_HashMap_insert___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__3(x_34, x_2, x_1);
x_37 = lean_st_ref_set(x_3, x_36, x_35);
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_37, 0);
lean_dec(x_39);
x_40 = lean_box(0);
lean_ctor_set(x_37, 0, x_40);
return x_37;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_37, 1);
lean_inc(x_41);
lean_dec(x_37);
x_42 = lean_box(0);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_41);
return x_43;
}
}
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_10, 0);
x_45 = lean_ctor_get(x_10, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_10);
lean_inc(x_2);
x_46 = l_Lean_HashMapImp_find_x3f___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__1(x_44, x_2);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; 
lean_dec(x_2);
lean_dec(x_1);
x_47 = lean_box(0);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_45);
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_49 = lean_ctor_get(x_46, 0);
lean_inc(x_49);
lean_dec(x_46);
x_50 = lean_box(3);
x_51 = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_beqDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_60_(x_49, x_50);
if (x_51 == 0)
{
uint8_t x_52; 
x_52 = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_beqDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_60_(x_49, x_1);
lean_dec(x_1);
lean_dec(x_49);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_53 = lean_st_ref_take(x_3, x_45);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = lean_box(2);
x_57 = l_Lean_HashMap_insert___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__3(x_54, x_2, x_56);
x_58 = lean_st_ref_set(x_3, x_57, x_55);
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_60 = x_58;
} else {
 lean_dec_ref(x_58);
 x_60 = lean_box(0);
}
x_61 = lean_box(0);
if (lean_is_scalar(x_60)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_60;
}
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_59);
return x_62;
}
else
{
lean_object* x_63; lean_object* x_64; 
lean_dec(x_2);
x_63 = lean_box(0);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_45);
return x_64;
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_49);
x_65 = lean_st_ref_take(x_3, x_45);
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
x_68 = l_Lean_HashMap_insert___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__3(x_66, x_2, x_1);
x_69 = lean_st_ref_set(x_3, x_68, x_67);
x_70 = lean_ctor_get(x_69, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_71 = x_69;
} else {
 lean_dec_ref(x_69);
 x_71 = lean_box(0);
}
x_72 = lean_box(0);
if (lean_is_scalar(x_71)) {
 x_73 = lean_alloc_ctor(0, 2, 0);
} else {
 x_73 = x_71;
}
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_70);
return x_73;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_find_x3f___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_AssocList_find_x3f___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_contains___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_AssocList_contains___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__4(x_1, x_2);
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
x_2 = l_ReaderT_instMonadReaderT___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_panic___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_panic___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__3___closed__1;
x_2 = l_ReaderT_instMonadReaderT___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_panic___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_panic___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__3___closed__2;
x_2 = l_instInhabitedPUnit;
x_3 = l_instInhabited___rarg(x_1, x_2);
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
x_1 = lean_mk_string_from_bytes("Lean.Compiler.LCNF.FVarUtil", 27);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Compiler.LCNF.Expr.forFVarM", 32);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("unreachable code has been reached", 33);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__2___closed__1;
x_2 = l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__2___closed__2;
x_3 = lean_unsigned_to_nat(42u);
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
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_array_get_size(x_9);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_nat_dec_lt(x_11, x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_10);
lean_dec(x_9);
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
lean_dec(x_9);
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
lean_dec(x_9);
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
LEAN_EXPORT lean_object* l_Lean_mkHashMap___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_mkHashMapImp___rarg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___spec__2___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = l_Lean_Compiler_LCNF_CodeDecl_fvarId(x_1);
x_11 = lean_box(3);
x_12 = l_Lean_HashMap_insert___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__3(x_2, x_10, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_9; 
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
else
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
lean_dec(x_2);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_inc(x_12);
x_13 = l_Lean_Compiler_LCNF_FloatLetIn_ignore_x3f(x_12, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_unbox(x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_12);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_box(0);
x_18 = l_List_foldlM___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___spec__2___lambda__1(x_10, x_1, x_17, x_3, x_4, x_5, x_6, x_7, x_16);
lean_dec(x_10);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_1 = x_19;
x_2 = x_11;
x_8 = x_20;
goto _start;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_10);
x_22 = lean_ctor_get(x_13, 1);
lean_inc(x_22);
lean_dec(x_13);
x_23 = lean_ctor_get(x_12, 0);
lean_inc(x_23);
lean_dec(x_12);
x_24 = lean_box(2);
x_25 = l_Lean_HashMap_insert___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__3(x_1, x_23, x_24);
x_1 = x_25;
x_2 = x_11;
x_8 = x_22;
goto _start;
}
}
else
{
uint8_t x_27; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_13);
if (x_27 == 0)
{
return x_13;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_13, 0);
x_29 = lean_ctor_get(x_13, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_13);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_31 = lean_ctor_get(x_2, 1);
lean_inc(x_31);
lean_dec(x_2);
x_32 = lean_box(0);
x_33 = l_List_foldlM___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___spec__2___lambda__1(x_10, x_1, x_32, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_10);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_1 = x_34;
x_2 = x_31;
x_8 = x_35;
goto _start;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_HashMapImp_contains___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint64_t x_5; size_t x_6; lean_object* x_7; uint8_t x_8; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1674_(x_2);
x_6 = lean_hashmap_mk_idx(x_4, x_5);
x_7 = lean_array_uget(x_3, x_6);
x_8 = l_Lean_AssocList_contains___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__4(x_2, x_7);
lean_dec(x_7);
return x_8;
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
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_List_lengthTRAux___rarg(x_2, x_8);
x_10 = l_Lean_mkHashMapImp___rarg(x_9);
lean_dec(x_9);
lean_inc(x_2);
x_11 = l_List_reverse___rarg(x_2);
x_12 = l_List_foldlM___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___spec__2(x_10, x_11, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_1, 2);
lean_inc(x_15);
x_16 = l_Lean_HashMapImp_contains___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___spec__3(x_13, x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_15);
x_17 = lean_box(0);
x_18 = l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___lambda__1(x_1, x_13, x_17, x_2, x_3, x_4, x_5, x_6, x_14);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_box(2);
x_20 = l_Lean_HashMap_insert___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__3(x_13, x_15, x_19);
x_21 = lean_box(0);
x_22 = l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___lambda__1(x_1, x_20, x_21, x_2, x_3, x_4, x_5, x_6, x_14);
return x_22;
}
}
else
{
uint8_t x_23; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_12);
if (x_23 == 0)
{
return x_12;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_12, 0);
x_25 = lean_ctor_get(x_12, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_12);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkHashMap___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___spec__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_mkHashMap___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___spec__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___spec__2___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_List_foldlM___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___spec__2___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_List_foldlM___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_HashMapImp_contains___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___spec__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_HashMapImp_contains___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___spec__3(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_mkHashMap___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_mkHashMapImp___rarg(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Lean_AssocList_contains___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__3(lean_object* x_1, lean_object* x_2) {
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
x_6 = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_beqDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_60_(x_4, x_1);
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
LEAN_EXPORT lean_object* l_Lean_AssocList_foldlM___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__6(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_array_get_size(x_1);
x_7 = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_hashDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_14_(x_4);
x_8 = lean_hashmap_mk_idx(x_6, x_7);
x_9 = lean_array_uget(x_1, x_8);
lean_ctor_set(x_2, 2, x_9);
x_10 = lean_array_uset(x_1, x_8, x_2);
x_1 = x_10;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint64_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_ctor_get(x_2, 1);
x_14 = lean_ctor_get(x_2, 2);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_2);
x_15 = lean_array_get_size(x_1);
x_16 = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_hashDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_14_(x_12);
x_17 = lean_hashmap_mk_idx(x_15, x_16);
x_18 = lean_array_uget(x_1, x_17);
x_19 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_19, 0, x_12);
lean_ctor_set(x_19, 1, x_13);
lean_ctor_set(x_19, 2, x_18);
x_20 = lean_array_uset(x_1, x_17, x_19);
x_1 = x_20;
x_2 = x_14;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_HashMapImp_moveEntries___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_Lean_AssocList_foldlM___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__6(x_3, x_6);
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
LEAN_EXPORT lean_object* l_Lean_HashMapImp_expand___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_unsigned_to_nat(2u);
x_5 = lean_nat_mul(x_3, x_4);
lean_dec(x_3);
x_6 = lean_box(0);
x_7 = lean_mk_array(x_5, x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Lean_HashMapImp_moveEntries___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__5(x_8, x_2, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_replace___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_beqDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_60_(x_6, x_1);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = l_Lean_AssocList_replace___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__7(x_1, x_2, x_8);
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
x_14 = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_beqDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_60_(x_11, x_1);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = l_Lean_AssocList_replace___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__7(x_1, x_2, x_13);
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
LEAN_EXPORT lean_object* l_Lean_HashMap_insert___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint64_t x_8; size_t x_9; lean_object* x_10; uint8_t x_11; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_array_get_size(x_6);
x_8 = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_hashDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_14_(x_2);
lean_inc(x_7);
x_9 = lean_hashmap_mk_idx(x_7, x_8);
x_10 = lean_array_uget(x_6, x_9);
x_11 = l_Lean_AssocList_contains___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__3(x_2, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_5, x_12);
lean_dec(x_5);
x_14 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_14, 0, x_2);
lean_ctor_set(x_14, 1, x_3);
lean_ctor_set(x_14, 2, x_10);
x_15 = lean_array_uset(x_6, x_9, x_14);
x_16 = l___private_Lean_Data_HashMap_0__Lean_numBucketsForCapacity(x_13);
x_17 = lean_nat_dec_le(x_16, x_7);
lean_dec(x_7);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
lean_free_object(x_1);
x_18 = l_Lean_HashMapImp_expand___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__4(x_13, x_15);
return x_18;
}
else
{
lean_ctor_set(x_1, 1, x_15);
lean_ctor_set(x_1, 0, x_13);
return x_1;
}
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_7);
x_19 = l_Lean_AssocList_replace___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__7(x_2, x_3, x_10);
x_20 = lean_array_uset(x_6, x_9, x_19);
lean_ctor_set(x_1, 1, x_20);
return x_1;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint64_t x_24; size_t x_25; lean_object* x_26; uint8_t x_27; 
x_21 = lean_ctor_get(x_1, 0);
x_22 = lean_ctor_get(x_1, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_1);
x_23 = lean_array_get_size(x_22);
x_24 = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_hashDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_14_(x_2);
lean_inc(x_23);
x_25 = lean_hashmap_mk_idx(x_23, x_24);
x_26 = lean_array_uget(x_22, x_25);
x_27 = l_Lean_AssocList_contains___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__3(x_2, x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_add(x_21, x_28);
lean_dec(x_21);
x_30 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_30, 0, x_2);
lean_ctor_set(x_30, 1, x_3);
lean_ctor_set(x_30, 2, x_26);
x_31 = lean_array_uset(x_22, x_25, x_30);
x_32 = l___private_Lean_Data_HashMap_0__Lean_numBucketsForCapacity(x_29);
x_33 = lean_nat_dec_le(x_32, x_23);
lean_dec(x_23);
lean_dec(x_32);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = l_Lean_HashMapImp_expand___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__4(x_29, x_31);
return x_34;
}
else
{
lean_object* x_35; 
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_29);
lean_ctor_set(x_35, 1, x_31);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_23);
x_36 = l_Lean_AssocList_replace___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__7(x_2, x_3, x_26);
x_37 = lean_array_uset(x_22, x_25, x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_21);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__8(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = 1;
x_8 = lean_usize_sub(x_3, x_7);
x_9 = lean_array_uget(x_2, x_8);
x_10 = l_Lean_Compiler_LCNF_FloatLetIn_Decision_ofAlt(x_9);
lean_dec(x_9);
lean_inc(x_1);
x_11 = l_Lean_HashMap_insert___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__2(x_5, x_10, x_1);
x_3 = x_8;
x_5 = x_11;
goto _start;
}
else
{
lean_dec(x_1);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__9(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = 1;
x_8 = lean_usize_sub(x_3, x_7);
x_9 = lean_array_uget(x_2, x_8);
x_10 = l_Lean_Compiler_LCNF_FloatLetIn_Decision_ofAlt(x_9);
lean_dec(x_9);
lean_inc(x_1);
x_11 = l_Lean_HashMap_insert___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__2(x_5, x_10, x_1);
x_3 = x_8;
x_5 = x_11;
goto _start;
}
else
{
lean_dec(x_1);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_initialNewArms(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_2 = lean_ctor_get(x_1, 3);
lean_inc(x_2);
lean_dec(x_1);
x_3 = lean_array_get_size(x_2);
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_add(x_3, x_4);
x_6 = l_Lean_mkHashMapImp___rarg(x_5);
lean_dec(x_5);
x_7 = lean_box(0);
x_8 = lean_box(2);
x_9 = l_Lean_HashMap_insert___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__2(x_6, x_8, x_7);
x_10 = lean_nat_dec_le(x_3, x_3);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_nat_dec_lt(x_11, x_3);
if (x_12 == 0)
{
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
else
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_usize_of_nat(x_3);
lean_dec(x_3);
x_14 = 0;
x_15 = l_Array_foldrMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__8(x_7, x_2, x_13, x_14, x_9);
lean_dec(x_2);
return x_15;
}
}
else
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_nat_dec_lt(x_16, x_3);
if (x_17 == 0)
{
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
else
{
size_t x_18; size_t x_19; lean_object* x_20; 
x_18 = lean_usize_of_nat(x_3);
lean_dec(x_3);
x_19 = 0;
x_20 = l_Array_foldrMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__9(x_7, x_2, x_18, x_19, x_9);
lean_dec(x_2);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkHashMap___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_mkHashMap___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_contains___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_AssocList_contains___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__3(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldrMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__8(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldrMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__9(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_st_ref_get(x_2, x_8);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_HashMapImp_contains___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___spec__3(x_13, x_1);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_1);
x_15 = lean_box(0);
lean_ctor_set(x_9, 0, x_15);
return x_9;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
lean_free_object(x_9);
x_16 = lean_st_ref_take(x_2, x_12);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = !lean_is_exclusive(x_17);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_20 = lean_ctor_get(x_17, 0);
x_21 = lean_box(2);
x_22 = l_Lean_HashMap_insert___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__3(x_20, x_1, x_21);
lean_ctor_set(x_17, 0, x_22);
x_23 = lean_st_ref_set(x_2, x_17, x_18);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_23, 0);
lean_dec(x_25);
x_26 = lean_box(0);
lean_ctor_set(x_23, 0, x_26);
return x_23;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_23, 1);
lean_inc(x_27);
lean_dec(x_23);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_30 = lean_ctor_get(x_17, 0);
x_31 = lean_ctor_get(x_17, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_17);
x_32 = lean_box(2);
x_33 = l_Lean_HashMap_insert___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__3(x_30, x_1, x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_31);
x_35 = lean_st_ref_set(x_2, x_34, x_18);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_37 = x_35;
} else {
 lean_dec_ref(x_35);
 x_37 = lean_box(0);
}
x_38 = lean_box(0);
if (lean_is_scalar(x_37)) {
 x_39 = lean_alloc_ctor(0, 2, 0);
} else {
 x_39 = x_37;
}
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_36);
return x_39;
}
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_40 = lean_ctor_get(x_9, 0);
x_41 = lean_ctor_get(x_9, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_9);
x_42 = lean_ctor_get(x_40, 0);
lean_inc(x_42);
lean_dec(x_40);
x_43 = l_Lean_HashMapImp_contains___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___spec__3(x_42, x_1);
lean_dec(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
lean_dec(x_1);
x_44 = lean_box(0);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_41);
return x_45;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_46 = lean_st_ref_take(x_2, x_41);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = lean_ctor_get(x_47, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_47, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_51 = x_47;
} else {
 lean_dec_ref(x_47);
 x_51 = lean_box(0);
}
x_52 = lean_box(2);
x_53 = l_Lean_HashMap_insert___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__3(x_49, x_1, x_52);
if (lean_is_scalar(x_51)) {
 x_54 = lean_alloc_ctor(0, 2, 0);
} else {
 x_54 = x_51;
}
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_50);
x_55 = lean_st_ref_set(x_2, x_54, x_48);
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_57 = x_55;
} else {
 lean_dec_ref(x_55);
 x_57 = lean_box(0);
}
x_58 = lean_box(0);
if (lean_is_scalar(x_57)) {
 x_59 = lean_alloc_ctor(0, 2, 0);
} else {
 x_59 = x_57;
}
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_56);
return x_59;
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
LEAN_EXPORT lean_object* l_Lean_AssocList_find_x3f___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__2(lean_object* x_1, lean_object* x_2) {
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
x_7 = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_beqDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_60_(x_4, x_1);
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
LEAN_EXPORT lean_object* l_Lean_HashMapImp_find_x3f___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint64_t x_5; size_t x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_array_get_size(x_3);
x_5 = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_hashDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_14_(x_2);
x_6 = lean_hashmap_mk_idx(x_4, x_5);
x_7 = lean_array_uget(x_3, x_6);
lean_dec(x_3);
x_8 = l_Lean_AssocList_find_x3f___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__2(x_2, x_7);
lean_dec(x_7);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = l_panic___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__3___closed__3;
x_10 = lean_panic_fn(x_9, x_1);
x_11 = lean_apply_7(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
x_13 = l_panic___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__6(x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
x_16 = l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__5(x_1, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
x_25 = l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__5(x_1, x_23, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
x_34 = l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__5(x_1, x_32, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
x_42 = l_panic___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__6(x_41, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_42;
}
case 11:
{
lean_object* x_43; lean_object* x_44; 
lean_dec(x_2);
lean_dec(x_1);
x_43 = l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___spec__2___closed__4;
x_44 = l_panic___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__6(x_43, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
x_15 = l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__5(x_1, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__9(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
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
x_15 = l_Lean_Compiler_LCNF_Arg_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__8(x_1, x_14, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__10(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
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
x_15 = l_Lean_Compiler_LCNF_Arg_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__8(x_1, x_14, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
x_24 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__9(x_1, x_12, x_21, x_22, x_23, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
x_40 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__10(x_1, x_26, x_37, x_38, x_39, x_3, x_4, x_5, x_6, x_7, x_8, x_29);
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
x_53 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__10(x_1, x_26, x_50, x_51, x_52, x_3, x_4, x_5, x_6, x_7, x_8, x_41);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
x_11 = l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__5(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_ctor_get(x_2, 3);
lean_inc(x_13);
lean_dec(x_2);
x_14 = l_Lean_Compiler_LCNF_LetValue_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__7(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__12(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_2, 2);
lean_inc(x_10);
lean_dec(x_2);
x_11 = l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__5(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
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
x_15 = l_Lean_Compiler_LCNF_Param_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__12(x_1, x_14, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__15(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
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
x_15 = l_Lean_Compiler_LCNF_Param_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__12(x_1, x_14, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__16(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
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
x_15 = l_Lean_Compiler_LCNF_Arg_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__8(x_1, x_14, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_AltCore_forCodeM___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__17(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__18(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
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
x_15 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__13), 9, 1);
lean_closure_set(x_15, 0, x_1);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_16 = l_Lean_Compiler_LCNF_AltCore_forCodeM___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__17(x_14, x_15, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__13(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
x_12 = l_Lean_Compiler_LCNF_LetDecl_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__4(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
x_26 = l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__5(x_1, x_25, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
x_29 = l_Lean_Compiler_LCNF_Code_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__13(x_1, x_28, x_3, x_4, x_5, x_6, x_7, x_8, x_27);
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
x_42 = l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__5(x_1, x_41, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
x_45 = l_Lean_Compiler_LCNF_Code_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__13(x_1, x_44, x_3, x_4, x_5, x_6, x_7, x_8, x_43);
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
x_59 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__14(x_1, x_21, x_56, x_57, x_58, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
x_62 = l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__5(x_1, x_61, x_3, x_4, x_5, x_6, x_7, x_8, x_60);
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
x_65 = l_Lean_Compiler_LCNF_Code_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__13(x_1, x_64, x_3, x_4, x_5, x_6, x_7, x_8, x_63);
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
x_87 = l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__5(x_1, x_86, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
x_90 = l_Lean_Compiler_LCNF_Code_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__13(x_1, x_89, x_3, x_4, x_5, x_6, x_7, x_8, x_88);
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
x_103 = l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__5(x_1, x_102, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
x_106 = l_Lean_Compiler_LCNF_Code_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__13(x_1, x_105, x_3, x_4, x_5, x_6, x_7, x_8, x_104);
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
x_120 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__15(x_1, x_82, x_117, x_118, x_119, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
x_123 = l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__5(x_1, x_122, x_3, x_4, x_5, x_6, x_7, x_8, x_121);
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
x_126 = l_Lean_Compiler_LCNF_Code_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__13(x_1, x_125, x_3, x_4, x_5, x_6, x_7, x_8, x_124);
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
x_156 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__16(x_1, x_142, x_153, x_154, x_155, x_3, x_4, x_5, x_6, x_7, x_8, x_145);
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
x_169 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__16(x_1, x_142, x_166, x_167, x_168, x_3, x_4, x_5, x_6, x_7, x_8, x_157);
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
x_176 = l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__5(x_1, x_175, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
x_193 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__18(x_1, x_183, x_190, x_191, x_192, x_3, x_4, x_5, x_6, x_7, x_8, x_181);
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
x_207 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__18(x_1, x_195, x_204, x_205, x_206, x_3, x_4, x_5, x_6, x_7, x_8, x_194);
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
x_219 = l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__5(x_1, x_218, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_219;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__19(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
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
x_15 = l_Lean_Compiler_LCNF_Param_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__12(x_1, x_14, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
x_15 = l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__5(x_1, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_ctor_get(x_2, 4);
lean_inc(x_17);
lean_dec(x_2);
x_18 = l_Lean_Compiler_LCNF_Code_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__13(x_1, x_17, x_3, x_4, x_5, x_6, x_7, x_8, x_16);
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
x_25 = l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__5(x_1, x_24, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_27 = lean_ctor_get(x_2, 4);
lean_inc(x_27);
lean_dec(x_2);
x_28 = l_Lean_Compiler_LCNF_Code_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__13(x_1, x_27, x_3, x_4, x_5, x_6, x_7, x_8, x_26);
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
x_36 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__19(x_1, x_10, x_33, x_34, x_35, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
x_39 = l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__5(x_1, x_38, x_3, x_4, x_5, x_6, x_7, x_8, x_37);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
lean_dec(x_39);
x_41 = lean_ctor_get(x_2, 4);
lean_inc(x_41);
lean_dec(x_2);
x_42 = l_Lean_Compiler_LCNF_Code_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__13(x_1, x_41, x_3, x_4, x_5, x_6, x_7, x_8, x_40);
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
x_1 = lean_mk_string_from_bytes("Lean.Data.HashMap", 17);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_FloatLetIn_dontFloat___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.HashMap.find!", 18);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_FloatLetIn_dontFloat___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("key is not in the map", 21);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_FloatLetIn_dontFloat___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Compiler_LCNF_FloatLetIn_dontFloat___closed__1;
x_2 = l_Lean_Compiler_LCNF_FloatLetIn_dontFloat___closed__2;
x_3 = lean_unsigned_to_nat(182u);
x_4 = lean_unsigned_to_nat(14u);
x_5 = l_Lean_Compiler_LCNF_FloatLetIn_dontFloat___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_FloatLetIn_dontFloat___closed__5() {
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
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_1, 0);
lean_inc(x_62);
x_63 = l_Lean_Compiler_LCNF_FloatLetIn_dontFloat___closed__5;
lean_inc(x_2);
x_64 = l_Lean_Compiler_LCNF_LetDecl_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__4(x_63, x_62, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; 
x_65 = lean_ctor_get(x_64, 1);
lean_inc(x_65);
lean_dec(x_64);
x_9 = x_65;
goto block_61;
}
else
{
uint8_t x_66; 
lean_dec(x_2);
lean_dec(x_1);
x_66 = !lean_is_exclusive(x_64);
if (x_66 == 0)
{
return x_64;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_64, 0);
x_68 = lean_ctor_get(x_64, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_64);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_1, 0);
lean_inc(x_70);
x_71 = l_Lean_Compiler_LCNF_FloatLetIn_dontFloat___closed__5;
lean_inc(x_2);
x_72 = l_Lean_Compiler_LCNF_FunDecl_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__11(x_71, x_70, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; 
x_73 = lean_ctor_get(x_72, 1);
lean_inc(x_73);
lean_dec(x_72);
x_9 = x_73;
goto block_61;
}
else
{
uint8_t x_74; 
lean_dec(x_2);
lean_dec(x_1);
x_74 = !lean_is_exclusive(x_72);
if (x_74 == 0)
{
return x_72;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_72, 0);
x_76 = lean_ctor_get(x_72, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_72);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
}
block_61:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_st_ref_take(x_2, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_11, 1);
x_15 = lean_box(2);
lean_inc(x_14);
x_16 = l_Lean_HashMapImp_find_x3f___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__1(x_14, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_17 = l_Lean_Compiler_LCNF_FloatLetIn_dontFloat___closed__4;
x_18 = l_panic___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__3(x_17);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_1);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Lean_HashMap_insert___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__2(x_14, x_15, x_19);
lean_ctor_set(x_11, 1, x_20);
x_21 = lean_st_ref_set(x_2, x_11, x_12);
lean_dec(x_2);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_21, 0);
lean_dec(x_23);
x_24 = lean_box(0);
lean_ctor_set(x_21, 0, x_24);
return x_21;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_21, 1);
lean_inc(x_25);
lean_dec(x_21);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_28 = lean_ctor_get(x_16, 0);
lean_inc(x_28);
lean_dec(x_16);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_1);
lean_ctor_set(x_29, 1, x_28);
x_30 = l_Lean_HashMap_insert___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__2(x_14, x_15, x_29);
lean_ctor_set(x_11, 1, x_30);
x_31 = lean_st_ref_set(x_2, x_11, x_12);
lean_dec(x_2);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_31, 0);
lean_dec(x_33);
x_34 = lean_box(0);
lean_ctor_set(x_31, 0, x_34);
return x_31;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_31, 1);
lean_inc(x_35);
lean_dec(x_31);
x_36 = lean_box(0);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_ctor_get(x_11, 0);
x_39 = lean_ctor_get(x_11, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_11);
x_40 = lean_box(2);
lean_inc(x_39);
x_41 = l_Lean_HashMapImp_find_x3f___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__1(x_39, x_40);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_42 = l_Lean_Compiler_LCNF_FloatLetIn_dontFloat___closed__4;
x_43 = l_panic___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__3(x_42);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_1);
lean_ctor_set(x_44, 1, x_43);
x_45 = l_Lean_HashMap_insert___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__2(x_39, x_40, x_44);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_38);
lean_ctor_set(x_46, 1, x_45);
x_47 = lean_st_ref_set(x_2, x_46, x_12);
lean_dec(x_2);
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_49 = x_47;
} else {
 lean_dec_ref(x_47);
 x_49 = lean_box(0);
}
x_50 = lean_box(0);
if (lean_is_scalar(x_49)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_49;
}
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_48);
return x_51;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_52 = lean_ctor_get(x_41, 0);
lean_inc(x_52);
lean_dec(x_41);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_1);
lean_ctor_set(x_53, 1, x_52);
x_54 = l_Lean_HashMap_insert___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__2(x_39, x_40, x_53);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_38);
lean_ctor_set(x_55, 1, x_54);
x_56 = lean_st_ref_set(x_2, x_55, x_12);
lean_dec(x_2);
x_57 = lean_ctor_get(x_56, 1);
lean_inc(x_57);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_58 = x_56;
} else {
 lean_dec_ref(x_56);
 x_58 = lean_box(0);
}
x_59 = lean_box(0);
if (lean_is_scalar(x_58)) {
 x_60 = lean_alloc_ctor(0, 2, 0);
} else {
 x_60 = x_58;
}
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_57);
return x_60;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_find_x3f___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_AssocList_find_x3f___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__9(x_1, x_2, x_13, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__10(x_1, x_2, x_13, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__15___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__15(x_1, x_2, x_13, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__18___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__18(x_1, x_2, x_13, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__19___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__19(x_1, x_2, x_13, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_float_goFVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_st_ref_get(x_3, x_9);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
lean_inc(x_1);
x_15 = l_Lean_HashMapImp_find_x3f___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__1(x_14, x_1);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
lean_dec(x_2);
lean_dec(x_1);
x_16 = lean_box(0);
lean_ctor_set(x_10, 0, x_16);
return x_10;
}
else
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_beqDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_60_(x_17, x_2);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
lean_dec(x_17);
lean_free_object(x_10);
lean_dec(x_2);
x_19 = lean_st_ref_take(x_3, x_13);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = !lean_is_exclusive(x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_23 = lean_ctor_get(x_20, 0);
x_24 = lean_box(2);
x_25 = l_Lean_HashMap_insert___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__3(x_23, x_1, x_24);
lean_ctor_set(x_20, 0, x_25);
x_26 = lean_st_ref_set(x_3, x_20, x_21);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_26, 0);
lean_dec(x_28);
x_29 = lean_box(0);
lean_ctor_set(x_26, 0, x_29);
return x_26;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_26, 1);
lean_inc(x_30);
lean_dec(x_26);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_33 = lean_ctor_get(x_20, 0);
x_34 = lean_ctor_get(x_20, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_20);
x_35 = lean_box(2);
x_36 = l_Lean_HashMap_insert___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__3(x_33, x_1, x_35);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_34);
x_38 = lean_st_ref_set(x_3, x_37, x_21);
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_40 = x_38;
} else {
 lean_dec_ref(x_38);
 x_40 = lean_box(0);
}
x_41 = lean_box(0);
if (lean_is_scalar(x_40)) {
 x_42 = lean_alloc_ctor(0, 2, 0);
} else {
 x_42 = x_40;
}
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_39);
return x_42;
}
}
else
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_box(3);
x_44 = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_beqDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_60_(x_17, x_43);
lean_dec(x_17);
if (x_44 == 0)
{
lean_object* x_45; 
lean_dec(x_2);
lean_dec(x_1);
x_45 = lean_box(0);
lean_ctor_set(x_10, 0, x_45);
return x_10;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
lean_free_object(x_10);
x_46 = lean_st_ref_take(x_3, x_13);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = !lean_is_exclusive(x_47);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_50 = lean_ctor_get(x_47, 0);
x_51 = l_Lean_HashMap_insert___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__3(x_50, x_1, x_2);
lean_ctor_set(x_47, 0, x_51);
x_52 = lean_st_ref_set(x_3, x_47, x_48);
x_53 = !lean_is_exclusive(x_52);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_52, 0);
lean_dec(x_54);
x_55 = lean_box(0);
lean_ctor_set(x_52, 0, x_55);
return x_52;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_52, 1);
lean_inc(x_56);
lean_dec(x_52);
x_57 = lean_box(0);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_56);
return x_58;
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_59 = lean_ctor_get(x_47, 0);
x_60 = lean_ctor_get(x_47, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_47);
x_61 = l_Lean_HashMap_insert___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__3(x_59, x_1, x_2);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_60);
x_63 = lean_st_ref_set(x_3, x_62, x_48);
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_65 = x_63;
} else {
 lean_dec_ref(x_63);
 x_65 = lean_box(0);
}
x_66 = lean_box(0);
if (lean_is_scalar(x_65)) {
 x_67 = lean_alloc_ctor(0, 2, 0);
} else {
 x_67 = x_65;
}
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_64);
return x_67;
}
}
}
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_68 = lean_ctor_get(x_10, 0);
x_69 = lean_ctor_get(x_10, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_10);
x_70 = lean_ctor_get(x_68, 0);
lean_inc(x_70);
lean_dec(x_68);
lean_inc(x_1);
x_71 = l_Lean_HashMapImp_find_x3f___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__1(x_70, x_1);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; 
lean_dec(x_2);
lean_dec(x_1);
x_72 = lean_box(0);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_69);
return x_73;
}
else
{
lean_object* x_74; uint8_t x_75; 
x_74 = lean_ctor_get(x_71, 0);
lean_inc(x_74);
lean_dec(x_71);
x_75 = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_beqDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_60_(x_74, x_2);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_dec(x_74);
lean_dec(x_2);
x_76 = lean_st_ref_take(x_3, x_69);
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
x_79 = lean_ctor_get(x_77, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_77, 1);
lean_inc(x_80);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 x_81 = x_77;
} else {
 lean_dec_ref(x_77);
 x_81 = lean_box(0);
}
x_82 = lean_box(2);
x_83 = l_Lean_HashMap_insert___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__3(x_79, x_1, x_82);
if (lean_is_scalar(x_81)) {
 x_84 = lean_alloc_ctor(0, 2, 0);
} else {
 x_84 = x_81;
}
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_80);
x_85 = lean_st_ref_set(x_3, x_84, x_78);
x_86 = lean_ctor_get(x_85, 1);
lean_inc(x_86);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 lean_ctor_release(x_85, 1);
 x_87 = x_85;
} else {
 lean_dec_ref(x_85);
 x_87 = lean_box(0);
}
x_88 = lean_box(0);
if (lean_is_scalar(x_87)) {
 x_89 = lean_alloc_ctor(0, 2, 0);
} else {
 x_89 = x_87;
}
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_86);
return x_89;
}
else
{
lean_object* x_90; uint8_t x_91; 
x_90 = lean_box(3);
x_91 = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_beqDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_60_(x_74, x_90);
lean_dec(x_74);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; 
lean_dec(x_2);
lean_dec(x_1);
x_92 = lean_box(0);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_69);
return x_93;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_94 = lean_st_ref_take(x_3, x_69);
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
lean_dec(x_94);
x_97 = lean_ctor_get(x_95, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_95, 1);
lean_inc(x_98);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 lean_ctor_release(x_95, 1);
 x_99 = x_95;
} else {
 lean_dec_ref(x_95);
 x_99 = lean_box(0);
}
x_100 = l_Lean_HashMap_insert___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__3(x_97, x_1, x_2);
if (lean_is_scalar(x_99)) {
 x_101 = lean_alloc_ctor(0, 2, 0);
} else {
 x_101 = x_99;
}
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_98);
x_102 = lean_st_ref_set(x_3, x_101, x_96);
x_103 = lean_ctor_get(x_102, 1);
lean_inc(x_103);
if (lean_is_exclusive(x_102)) {
 lean_ctor_release(x_102, 0);
 lean_ctor_release(x_102, 1);
 x_104 = x_102;
} else {
 lean_dec_ref(x_102);
 x_104 = lean_box(0);
}
x_105 = lean_box(0);
if (lean_is_scalar(x_104)) {
 x_106 = lean_alloc_ctor(0, 2, 0);
} else {
 x_106 = x_104;
}
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_103);
return x_106;
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
LEAN_EXPORT lean_object* l_panic___at_Lean_Compiler_LCNF_FloatLetIn_float___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Compiler_LCNF_FloatLetIn_instInhabitedDecision;
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
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
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_9 = lean_st_ref_get(x_2, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_80 = lean_ctor_get(x_10, 0);
lean_inc(x_80);
lean_dec(x_10);
x_81 = l_Lean_Compiler_LCNF_CodeDecl_fvarId(x_1);
x_82 = l_Lean_HashMapImp_find_x3f___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__1(x_80, x_81);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; 
x_83 = l_Lean_Compiler_LCNF_FloatLetIn_dontFloat___closed__4;
x_84 = l_panic___at_Lean_Compiler_LCNF_FloatLetIn_float___spec__1(x_83);
x_12 = x_84;
goto block_79;
}
else
{
lean_object* x_85; 
x_85 = lean_ctor_get(x_82, 0);
lean_inc(x_85);
lean_dec(x_82);
x_12 = x_85;
goto block_79;
}
block_79:
{
lean_object* x_13; lean_object* x_64; 
lean_inc(x_12);
x_64 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_FloatLetIn_float___lambda__1___boxed), 9, 1);
lean_closure_set(x_64, 0, x_12);
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_1, 0);
lean_inc(x_65);
lean_inc(x_2);
x_66 = l_Lean_Compiler_LCNF_LetDecl_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__4(x_64, x_65, x_2, x_3, x_4, x_5, x_6, x_7, x_11);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; 
x_67 = lean_ctor_get(x_66, 1);
lean_inc(x_67);
lean_dec(x_66);
x_13 = x_67;
goto block_63;
}
else
{
uint8_t x_68; 
lean_dec(x_12);
lean_dec(x_2);
lean_dec(x_1);
x_68 = !lean_is_exclusive(x_66);
if (x_68 == 0)
{
return x_66;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_66, 0);
x_70 = lean_ctor_get(x_66, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_66);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
else
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_1, 0);
lean_inc(x_72);
lean_inc(x_2);
x_73 = l_Lean_Compiler_LCNF_FunDecl_forFVarM___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__11(x_64, x_72, x_2, x_3, x_4, x_5, x_6, x_7, x_11);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; 
x_74 = lean_ctor_get(x_73, 1);
lean_inc(x_74);
lean_dec(x_73);
x_13 = x_74;
goto block_63;
}
else
{
uint8_t x_75; 
lean_dec(x_12);
lean_dec(x_2);
lean_dec(x_1);
x_75 = !lean_is_exclusive(x_73);
if (x_75 == 0)
{
return x_73;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_73, 0);
x_77 = lean_ctor_get(x_73, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_73);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
}
block_63:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_st_ref_take(x_2, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = !lean_is_exclusive(x_15);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_12);
lean_inc(x_18);
x_19 = l_Lean_HashMapImp_find_x3f___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__1(x_18, x_12);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_20 = l_Lean_Compiler_LCNF_FloatLetIn_dontFloat___closed__4;
x_21 = l_panic___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__3(x_20);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_1);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Lean_HashMap_insert___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__2(x_18, x_12, x_22);
lean_ctor_set(x_15, 1, x_23);
x_24 = lean_st_ref_set(x_2, x_15, x_16);
lean_dec(x_2);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_24, 0);
lean_dec(x_26);
x_27 = lean_box(0);
lean_ctor_set(x_24, 0, x_27);
return x_24;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_24, 1);
lean_inc(x_28);
lean_dec(x_24);
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_31 = lean_ctor_get(x_19, 0);
lean_inc(x_31);
lean_dec(x_19);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_1);
lean_ctor_set(x_32, 1, x_31);
x_33 = l_Lean_HashMap_insert___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__2(x_18, x_12, x_32);
lean_ctor_set(x_15, 1, x_33);
x_34 = lean_st_ref_set(x_2, x_15, x_16);
lean_dec(x_2);
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_34, 0);
lean_dec(x_36);
x_37 = lean_box(0);
lean_ctor_set(x_34, 0, x_37);
return x_34;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_34, 1);
lean_inc(x_38);
lean_dec(x_34);
x_39 = lean_box(0);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
return x_40;
}
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_15, 0);
x_42 = lean_ctor_get(x_15, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_15);
lean_inc(x_12);
lean_inc(x_42);
x_43 = l_Lean_HashMapImp_find_x3f___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__1(x_42, x_12);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_44 = l_Lean_Compiler_LCNF_FloatLetIn_dontFloat___closed__4;
x_45 = l_panic___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__3(x_44);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_1);
lean_ctor_set(x_46, 1, x_45);
x_47 = l_Lean_HashMap_insert___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__2(x_42, x_12, x_46);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_41);
lean_ctor_set(x_48, 1, x_47);
x_49 = lean_st_ref_set(x_2, x_48, x_16);
lean_dec(x_2);
x_50 = lean_ctor_get(x_49, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 x_51 = x_49;
} else {
 lean_dec_ref(x_49);
 x_51 = lean_box(0);
}
x_52 = lean_box(0);
if (lean_is_scalar(x_51)) {
 x_53 = lean_alloc_ctor(0, 2, 0);
} else {
 x_53 = x_51;
}
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_50);
return x_53;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_54 = lean_ctor_get(x_43, 0);
lean_inc(x_54);
lean_dec(x_43);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_1);
lean_ctor_set(x_55, 1, x_54);
x_56 = l_Lean_HashMap_insert___at_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___spec__2(x_42, x_12, x_55);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_41);
lean_ctor_set(x_57, 1, x_56);
x_58 = lean_st_ref_set(x_2, x_57, x_16);
lean_dec(x_2);
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_60 = x_58;
} else {
 lean_dec_ref(x_58);
 x_60 = lean_box(0);
}
x_61 = lean_box(0);
if (lean_is_scalar(x_60)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_60;
}
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_59);
return x_62;
}
}
}
}
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
static lean_object* _init_l_List_forIn_loop___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_10; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_2);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_2);
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_dec(x_1);
x_18 = lean_st_ref_get(x_3, x_9);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_Compiler_LCNF_CodeDecl_fvarId(x_11);
x_23 = l_Lean_HashMapImp_find_x3f___at_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___spec__1(x_21, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = l_Lean_Compiler_LCNF_FloatLetIn_dontFloat___closed__4;
x_25 = l_panic___at_Lean_Compiler_LCNF_FloatLetIn_float___spec__1(x_24);
x_26 = lean_box(3);
x_27 = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_beqDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_60_(x_25, x_26);
if (x_27 == 0)
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_box(2);
x_29 = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_beqDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_60_(x_25, x_28);
lean_dec(x_25);
if (x_29 == 0)
{
lean_object* x_30; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_30 = l_Lean_Compiler_LCNF_FloatLetIn_float(x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_20);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_dec(x_30);
x_32 = l_List_forIn_loop___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases___spec__1___closed__1;
x_13 = x_32;
x_14 = x_31;
goto block_17;
}
else
{
uint8_t x_33; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_33 = !lean_is_exclusive(x_30);
if (x_33 == 0)
{
return x_30;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_30, 0);
x_35 = lean_ctor_get(x_30, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_30);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
lean_object* x_37; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_37 = l_Lean_Compiler_LCNF_FloatLetIn_dontFloat(x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_20);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
lean_dec(x_37);
x_39 = l_List_forIn_loop___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases___spec__1___closed__1;
x_13 = x_39;
x_14 = x_38;
goto block_17;
}
else
{
uint8_t x_40; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_40 = !lean_is_exclusive(x_37);
if (x_40 == 0)
{
return x_37;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_37, 0);
x_42 = lean_ctor_get(x_37, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_37);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_25);
x_44 = l_Lean_Compiler_LCNF_eraseCodeDecl(x_11, x_5, x_6, x_7, x_8, x_20);
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec(x_44);
x_46 = l_List_forIn_loop___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases___spec__1___closed__1;
x_13 = x_46;
x_14 = x_45;
goto block_17;
}
}
else
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_47 = lean_ctor_get(x_23, 0);
lean_inc(x_47);
lean_dec(x_23);
x_48 = lean_box(3);
x_49 = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_beqDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_60_(x_47, x_48);
if (x_49 == 0)
{
lean_object* x_50; uint8_t x_51; 
x_50 = lean_box(2);
x_51 = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_beqDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_60_(x_47, x_50);
lean_dec(x_47);
if (x_51 == 0)
{
lean_object* x_52; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_52 = l_Lean_Compiler_LCNF_FloatLetIn_float(x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_20);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_52, 1);
lean_inc(x_53);
lean_dec(x_52);
x_54 = l_List_forIn_loop___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases___spec__1___closed__1;
x_13 = x_54;
x_14 = x_53;
goto block_17;
}
else
{
uint8_t x_55; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_55 = !lean_is_exclusive(x_52);
if (x_55 == 0)
{
return x_52;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_52, 0);
x_57 = lean_ctor_get(x_52, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_52);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
else
{
lean_object* x_59; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_59 = l_Lean_Compiler_LCNF_FloatLetIn_dontFloat(x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_20);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_59, 1);
lean_inc(x_60);
lean_dec(x_59);
x_61 = l_List_forIn_loop___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases___spec__1___closed__1;
x_13 = x_61;
x_14 = x_60;
goto block_17;
}
else
{
uint8_t x_62; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_62 = !lean_is_exclusive(x_59);
if (x_62 == 0)
{
return x_59;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_59, 0);
x_64 = lean_ctor_get(x_59, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_59);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_47);
x_66 = l_Lean_Compiler_LCNF_eraseCodeDecl(x_11, x_5, x_6, x_7, x_8, x_20);
x_67 = lean_ctor_get(x_66, 1);
lean_inc(x_67);
lean_dec(x_66);
x_68 = l_List_forIn_loop___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases___spec__1___closed__1;
x_13 = x_68;
x_14 = x_67;
goto block_17;
}
}
block_17:
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
x_1 = x_12;
x_2 = x_15;
x_9 = x_14;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_box(0);
lean_inc(x_2);
x_9 = l_List_forIn_loop___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases___spec__1(x_2, x_8, x_1, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_9, 0);
lean_dec(x_11);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_dec(x_9);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_8);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_9);
if (x_14 == 0)
{
return x_9;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_9, 0);
x_16 = lean_ctor_get(x_9, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_9);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
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
x_1 = l_Lean_addTrace___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__2___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_addTrace___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_addTrace___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__2___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_addTrace___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__2___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_addTrace___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__2___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_addTrace___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__2___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_addTrace___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__2___closed__3;
x_3 = l_Lean_addTrace___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__2___closed__4;
x_4 = l_Lean_addTrace___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__2___closed__5;
x_5 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_1);
lean_ctor_set(x_5, 2, x_1);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set(x_5, 4, x_3);
lean_ctor_set(x_5, 5, x_4);
lean_ctor_set(x_5, 6, x_2);
lean_ctor_set(x_5, 7, x_3);
lean_ctor_set(x_5, 8, x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_addTrace___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__2___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
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
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_17);
x_19 = lean_ctor_get(x_6, 2);
x_20 = l_Lean_addTrace___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__2___closed__6;
lean_inc(x_19);
x_21 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_21, 0, x_13);
lean_ctor_set(x_21, 1, x_20);
lean_ctor_set(x_21, 2, x_18);
lean_ctor_set(x_21, 3, x_19);
x_22 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_2);
x_23 = lean_st_ref_take(x_7, x_16);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = !lean_is_exclusive(x_24);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_27 = lean_ctor_get(x_24, 3);
x_28 = l_Lean_addTrace___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__2___closed__7;
x_29 = 0;
x_30 = lean_alloc_ctor(9, 3, 1);
lean_ctor_set(x_30, 0, x_1);
lean_ctor_set(x_30, 1, x_22);
lean_ctor_set(x_30, 2, x_28);
lean_ctor_set_uint8(x_30, sizeof(void*)*3, x_29);
lean_inc(x_9);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_9);
lean_ctor_set(x_31, 1, x_30);
x_32 = l_Lean_PersistentArray_push___rarg(x_27, x_31);
lean_ctor_set(x_24, 3, x_32);
x_33 = lean_st_ref_set(x_7, x_24, x_25);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_33, 0);
lean_dec(x_35);
x_36 = lean_box(0);
lean_ctor_set(x_33, 0, x_36);
return x_33;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_33, 1);
lean_inc(x_37);
lean_dec(x_33);
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
return x_39;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_40 = lean_ctor_get(x_24, 0);
x_41 = lean_ctor_get(x_24, 1);
x_42 = lean_ctor_get(x_24, 2);
x_43 = lean_ctor_get(x_24, 3);
x_44 = lean_ctor_get(x_24, 4);
x_45 = lean_ctor_get(x_24, 5);
x_46 = lean_ctor_get(x_24, 6);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_24);
x_47 = l_Lean_addTrace___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__2___closed__7;
x_48 = 0;
x_49 = lean_alloc_ctor(9, 3, 1);
lean_ctor_set(x_49, 0, x_1);
lean_ctor_set(x_49, 1, x_22);
lean_ctor_set(x_49, 2, x_47);
lean_ctor_set_uint8(x_49, sizeof(void*)*3, x_48);
lean_inc(x_9);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_9);
lean_ctor_set(x_50, 1, x_49);
x_51 = l_Lean_PersistentArray_push___rarg(x_43, x_50);
x_52 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_52, 0, x_40);
lean_ctor_set(x_52, 1, x_41);
lean_ctor_set(x_52, 2, x_42);
lean_ctor_set(x_52, 3, x_51);
lean_ctor_set(x_52, 4, x_44);
lean_ctor_set(x_52, 5, x_45);
lean_ctor_set(x_52, 6, x_46);
x_53 = lean_st_ref_set(x_7, x_52, x_25);
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_55 = x_53;
} else {
 lean_dec_ref(x_53);
 x_55 = lean_box(0);
}
x_56 = lean_box(0);
if (lean_is_scalar(x_55)) {
 x_57 = lean_alloc_ctor(0, 2, 0);
} else {
 x_57 = x_55;
}
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_54);
return x_57;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__3___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = l_List_redLength___rarg(x_1);
x_11 = lean_mk_empty_array_with_capacity(x_10);
lean_dec(x_10);
x_12 = l_List_toArrayAux___rarg(x_1, x_11);
x_13 = l_Lean_Compiler_LCNF_AltCore_getCode(x_2);
x_14 = l_Lean_Compiler_LCNF_attachCodeDecls(x_12, x_13);
lean_dec(x_12);
x_15 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go), 7, 1);
lean_closure_set(x_15, 0, x_14);
x_16 = l_Lean_Compiler_LCNF_FloatLetIn_withNewScope___rarg(x_15, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(x_2, x_18);
lean_ctor_set(x_16, 0, x_19);
return x_16;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_16, 0);
x_21 = lean_ctor_get(x_16, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_16);
x_22 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(x_2, x_20);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
else
{
uint8_t x_24; 
lean_dec(x_2);
x_24 = !lean_is_exclusive(x_16);
if (x_24 == 0)
{
return x_16;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_16, 0);
x_26 = lean_ctor_get(x_16, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_16);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Compiler", 8);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__3___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("floatLetIn", 10);
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
x_1 = lean_mk_string_from_bytes("Size of code that was pushed into arm: ", 39);
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
x_1 = lean_mk_string_from_bytes(" ", 1);
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
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("", 0);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__3___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__3___closed__8;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__3(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_3, x_2);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_4);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_61; lean_object* x_62; 
x_13 = lean_array_uget(x_4, x_3);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_array_uset(x_4, x_3, x_14);
x_16 = l_Lean_Compiler_LCNF_FloatLetIn_Decision_ofAlt(x_13);
x_17 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__3___closed__3;
x_61 = l_Lean_isTracingEnabledFor___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__1(x_17, x_5, x_6, x_7, x_8, x_9, x_10);
lean_inc(x_16);
lean_inc(x_1);
x_62 = l_Lean_HashMapImp_find_x3f___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__1(x_1, x_16);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_63 = lean_ctor_get(x_61, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_61, 1);
lean_inc(x_64);
lean_dec(x_61);
x_65 = l_Lean_Compiler_LCNF_FloatLetIn_dontFloat___closed__4;
x_66 = l_panic___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__3(x_65);
x_67 = lean_unbox(x_63);
lean_dec(x_63);
x_18 = x_66;
x_19 = x_67;
x_20 = x_64;
goto block_60;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_68 = lean_ctor_get(x_62, 0);
lean_inc(x_68);
lean_dec(x_62);
x_69 = lean_ctor_get(x_61, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_61, 1);
lean_inc(x_70);
lean_dec(x_61);
x_71 = lean_unbox(x_69);
lean_dec(x_69);
x_18 = x_68;
x_19 = x_71;
x_20 = x_70;
goto block_60;
}
block_60:
{
if (x_19 == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_16);
x_21 = lean_box(0);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_22 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__3___lambda__1(x_18, x_13, x_21, x_5, x_6, x_7, x_8, x_9, x_20);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; size_t x_25; size_t x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = 1;
x_26 = lean_usize_add(x_3, x_25);
x_27 = lean_array_uset(x_15, x_3, x_23);
x_3 = x_26;
x_4 = x_27;
x_10 = x_24;
goto _start;
}
else
{
uint8_t x_29; 
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_22);
if (x_29 == 0)
{
return x_22;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_22, 0);
x_31 = lean_ctor_get(x_22, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_22);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_33 = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_160_(x_16, x_14);
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_33);
x_35 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__3___closed__5;
x_36 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
x_37 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__3___closed__7;
x_38 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_39 = l_List_lengthTRAux___rarg(x_18, x_14);
x_40 = l_Nat_repr(x_39);
x_41 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_41, 0, x_40);
x_42 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_42, 0, x_41);
x_43 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_43, 0, x_38);
lean_ctor_set(x_43, 1, x_42);
x_44 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__3___closed__9;
x_45 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
x_46 = l_Lean_addTrace___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__2(x_17, x_45, x_5, x_6, x_7, x_8, x_9, x_20);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_49 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__3___lambda__1(x_18, x_13, x_47, x_5, x_6, x_7, x_8, x_9, x_48);
lean_dec(x_47);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; size_t x_52; size_t x_53; lean_object* x_54; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = 1;
x_53 = lean_usize_add(x_3, x_52);
x_54 = lean_array_uset(x_15, x_3, x_50);
x_3 = x_53;
x_4 = x_54;
x_10 = x_51;
goto _start;
}
else
{
uint8_t x_56; 
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_56 = !lean_is_exclusive(x_49);
if (x_56 == 0)
{
return x_49;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_49, 0);
x_58 = lean_ctor_get(x_49, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_49);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
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
lean_inc(x_51);
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
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; size_t x_68; size_t x_69; lean_object* x_70; lean_object* x_172; lean_object* x_173; 
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
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
x_66 = lean_ctor_get(x_51, 3);
lean_inc(x_66);
x_67 = lean_array_get_size(x_66);
x_68 = lean_usize_of_nat(x_67);
lean_dec(x_67);
x_69 = 0;
x_172 = lean_box(2);
lean_inc(x_65);
x_173 = l_Lean_HashMapImp_find_x3f___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__1(x_65, x_172);
if (lean_obj_tag(x_173) == 0)
{
lean_object* x_174; lean_object* x_175; 
x_174 = l_Lean_Compiler_LCNF_FloatLetIn_dontFloat___closed__4;
x_175 = l_panic___at_Lean_Compiler_LCNF_FloatLetIn_dontFloat___spec__3(x_174);
x_70 = x_175;
goto block_171;
}
else
{
lean_object* x_176; 
x_176 = lean_ctor_get(x_173, 0);
lean_inc(x_176);
lean_dec(x_173);
x_70 = x_176;
goto block_171;
}
block_171:
{
lean_object* x_71; 
lean_inc(x_66);
x_71 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__3(x_65, x_68, x_69, x_66, x_2, x_3, x_4, x_5, x_6, x_64);
lean_dec(x_2);
if (lean_obj_tag(x_71) == 0)
{
uint8_t x_72; 
x_72 = !lean_is_exclusive(x_71);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; size_t x_79; size_t x_80; uint8_t x_81; 
x_73 = lean_ctor_get(x_71, 0);
x_74 = lean_ctor_get(x_51, 1);
lean_inc(x_74);
x_75 = lean_ctor_get(x_51, 2);
lean_inc(x_75);
x_76 = l_List_redLength___rarg(x_70);
x_77 = lean_mk_empty_array_with_capacity(x_76);
lean_dec(x_76);
x_78 = l_List_toArrayAux___rarg(x_70, x_77);
x_79 = lean_ptr_addr(x_66);
lean_dec(x_66);
x_80 = lean_ptr_addr(x_73);
x_81 = lean_usize_dec_eq(x_79, x_80);
if (x_81 == 0)
{
uint8_t x_82; 
x_82 = !lean_is_exclusive(x_1);
if (x_82 == 0)
{
lean_object* x_83; uint8_t x_84; 
x_83 = lean_ctor_get(x_1, 0);
lean_dec(x_83);
x_84 = !lean_is_exclusive(x_51);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_85 = lean_ctor_get(x_51, 3);
lean_dec(x_85);
x_86 = lean_ctor_get(x_51, 2);
lean_dec(x_86);
x_87 = lean_ctor_get(x_51, 1);
lean_dec(x_87);
lean_ctor_set(x_51, 3, x_73);
x_88 = l_Lean_Compiler_LCNF_attachCodeDecls(x_78, x_1);
lean_dec(x_78);
lean_ctor_set(x_71, 0, x_88);
return x_71;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_51, 0);
lean_inc(x_89);
lean_dec(x_51);
x_90 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_74);
lean_ctor_set(x_90, 2, x_75);
lean_ctor_set(x_90, 3, x_73);
lean_ctor_set(x_1, 0, x_90);
x_91 = l_Lean_Compiler_LCNF_attachCodeDecls(x_78, x_1);
lean_dec(x_78);
lean_ctor_set(x_71, 0, x_91);
return x_71;
}
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_1);
x_92 = lean_ctor_get(x_51, 0);
lean_inc(x_92);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 lean_ctor_release(x_51, 1);
 lean_ctor_release(x_51, 2);
 lean_ctor_release(x_51, 3);
 x_93 = x_51;
} else {
 lean_dec_ref(x_51);
 x_93 = lean_box(0);
}
if (lean_is_scalar(x_93)) {
 x_94 = lean_alloc_ctor(0, 4, 0);
} else {
 x_94 = x_93;
}
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_74);
lean_ctor_set(x_94, 2, x_75);
lean_ctor_set(x_94, 3, x_73);
x_95 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_95, 0, x_94);
x_96 = l_Lean_Compiler_LCNF_attachCodeDecls(x_78, x_95);
lean_dec(x_78);
lean_ctor_set(x_71, 0, x_96);
return x_71;
}
}
else
{
size_t x_97; uint8_t x_98; 
x_97 = lean_ptr_addr(x_74);
x_98 = lean_usize_dec_eq(x_97, x_97);
if (x_98 == 0)
{
uint8_t x_99; 
x_99 = !lean_is_exclusive(x_1);
if (x_99 == 0)
{
lean_object* x_100; uint8_t x_101; 
x_100 = lean_ctor_get(x_1, 0);
lean_dec(x_100);
x_101 = !lean_is_exclusive(x_51);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_102 = lean_ctor_get(x_51, 3);
lean_dec(x_102);
x_103 = lean_ctor_get(x_51, 2);
lean_dec(x_103);
x_104 = lean_ctor_get(x_51, 1);
lean_dec(x_104);
lean_ctor_set(x_51, 3, x_73);
x_105 = l_Lean_Compiler_LCNF_attachCodeDecls(x_78, x_1);
lean_dec(x_78);
lean_ctor_set(x_71, 0, x_105);
return x_71;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_51, 0);
lean_inc(x_106);
lean_dec(x_51);
x_107 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_74);
lean_ctor_set(x_107, 2, x_75);
lean_ctor_set(x_107, 3, x_73);
lean_ctor_set(x_1, 0, x_107);
x_108 = l_Lean_Compiler_LCNF_attachCodeDecls(x_78, x_1);
lean_dec(x_78);
lean_ctor_set(x_71, 0, x_108);
return x_71;
}
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
lean_dec(x_1);
x_109 = lean_ctor_get(x_51, 0);
lean_inc(x_109);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 lean_ctor_release(x_51, 1);
 lean_ctor_release(x_51, 2);
 lean_ctor_release(x_51, 3);
 x_110 = x_51;
} else {
 lean_dec_ref(x_51);
 x_110 = lean_box(0);
}
if (lean_is_scalar(x_110)) {
 x_111 = lean_alloc_ctor(0, 4, 0);
} else {
 x_111 = x_110;
}
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_74);
lean_ctor_set(x_111, 2, x_75);
lean_ctor_set(x_111, 3, x_73);
x_112 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_112, 0, x_111);
x_113 = l_Lean_Compiler_LCNF_attachCodeDecls(x_78, x_112);
lean_dec(x_78);
lean_ctor_set(x_71, 0, x_113);
return x_71;
}
}
else
{
uint8_t x_114; 
x_114 = lean_name_eq(x_75, x_75);
if (x_114 == 0)
{
uint8_t x_115; 
x_115 = !lean_is_exclusive(x_1);
if (x_115 == 0)
{
lean_object* x_116; uint8_t x_117; 
x_116 = lean_ctor_get(x_1, 0);
lean_dec(x_116);
x_117 = !lean_is_exclusive(x_51);
if (x_117 == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_118 = lean_ctor_get(x_51, 3);
lean_dec(x_118);
x_119 = lean_ctor_get(x_51, 2);
lean_dec(x_119);
x_120 = lean_ctor_get(x_51, 1);
lean_dec(x_120);
lean_ctor_set(x_51, 3, x_73);
x_121 = l_Lean_Compiler_LCNF_attachCodeDecls(x_78, x_1);
lean_dec(x_78);
lean_ctor_set(x_71, 0, x_121);
return x_71;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_122 = lean_ctor_get(x_51, 0);
lean_inc(x_122);
lean_dec(x_51);
x_123 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_74);
lean_ctor_set(x_123, 2, x_75);
lean_ctor_set(x_123, 3, x_73);
lean_ctor_set(x_1, 0, x_123);
x_124 = l_Lean_Compiler_LCNF_attachCodeDecls(x_78, x_1);
lean_dec(x_78);
lean_ctor_set(x_71, 0, x_124);
return x_71;
}
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
lean_dec(x_1);
x_125 = lean_ctor_get(x_51, 0);
lean_inc(x_125);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 lean_ctor_release(x_51, 1);
 lean_ctor_release(x_51, 2);
 lean_ctor_release(x_51, 3);
 x_126 = x_51;
} else {
 lean_dec_ref(x_51);
 x_126 = lean_box(0);
}
if (lean_is_scalar(x_126)) {
 x_127 = lean_alloc_ctor(0, 4, 0);
} else {
 x_127 = x_126;
}
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set(x_127, 1, x_74);
lean_ctor_set(x_127, 2, x_75);
lean_ctor_set(x_127, 3, x_73);
x_128 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_128, 0, x_127);
x_129 = l_Lean_Compiler_LCNF_attachCodeDecls(x_78, x_128);
lean_dec(x_78);
lean_ctor_set(x_71, 0, x_129);
return x_71;
}
}
else
{
lean_object* x_130; 
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_51);
x_130 = l_Lean_Compiler_LCNF_attachCodeDecls(x_78, x_1);
lean_dec(x_78);
lean_ctor_set(x_71, 0, x_130);
return x_71;
}
}
}
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; size_t x_138; size_t x_139; uint8_t x_140; 
x_131 = lean_ctor_get(x_71, 0);
x_132 = lean_ctor_get(x_71, 1);
lean_inc(x_132);
lean_inc(x_131);
lean_dec(x_71);
x_133 = lean_ctor_get(x_51, 1);
lean_inc(x_133);
x_134 = lean_ctor_get(x_51, 2);
lean_inc(x_134);
x_135 = l_List_redLength___rarg(x_70);
x_136 = lean_mk_empty_array_with_capacity(x_135);
lean_dec(x_135);
x_137 = l_List_toArrayAux___rarg(x_70, x_136);
x_138 = lean_ptr_addr(x_66);
lean_dec(x_66);
x_139 = lean_ptr_addr(x_131);
x_140 = lean_usize_dec_eq(x_138, x_139);
if (x_140 == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_141 = x_1;
} else {
 lean_dec_ref(x_1);
 x_141 = lean_box(0);
}
x_142 = lean_ctor_get(x_51, 0);
lean_inc(x_142);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 lean_ctor_release(x_51, 1);
 lean_ctor_release(x_51, 2);
 lean_ctor_release(x_51, 3);
 x_143 = x_51;
} else {
 lean_dec_ref(x_51);
 x_143 = lean_box(0);
}
if (lean_is_scalar(x_143)) {
 x_144 = lean_alloc_ctor(0, 4, 0);
} else {
 x_144 = x_143;
}
lean_ctor_set(x_144, 0, x_142);
lean_ctor_set(x_144, 1, x_133);
lean_ctor_set(x_144, 2, x_134);
lean_ctor_set(x_144, 3, x_131);
if (lean_is_scalar(x_141)) {
 x_145 = lean_alloc_ctor(4, 1, 0);
} else {
 x_145 = x_141;
}
lean_ctor_set(x_145, 0, x_144);
x_146 = l_Lean_Compiler_LCNF_attachCodeDecls(x_137, x_145);
lean_dec(x_137);
x_147 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_147, 1, x_132);
return x_147;
}
else
{
size_t x_148; uint8_t x_149; 
x_148 = lean_ptr_addr(x_133);
x_149 = lean_usize_dec_eq(x_148, x_148);
if (x_149 == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_150 = x_1;
} else {
 lean_dec_ref(x_1);
 x_150 = lean_box(0);
}
x_151 = lean_ctor_get(x_51, 0);
lean_inc(x_151);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 lean_ctor_release(x_51, 1);
 lean_ctor_release(x_51, 2);
 lean_ctor_release(x_51, 3);
 x_152 = x_51;
} else {
 lean_dec_ref(x_51);
 x_152 = lean_box(0);
}
if (lean_is_scalar(x_152)) {
 x_153 = lean_alloc_ctor(0, 4, 0);
} else {
 x_153 = x_152;
}
lean_ctor_set(x_153, 0, x_151);
lean_ctor_set(x_153, 1, x_133);
lean_ctor_set(x_153, 2, x_134);
lean_ctor_set(x_153, 3, x_131);
if (lean_is_scalar(x_150)) {
 x_154 = lean_alloc_ctor(4, 1, 0);
} else {
 x_154 = x_150;
}
lean_ctor_set(x_154, 0, x_153);
x_155 = l_Lean_Compiler_LCNF_attachCodeDecls(x_137, x_154);
lean_dec(x_137);
x_156 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_156, 0, x_155);
lean_ctor_set(x_156, 1, x_132);
return x_156;
}
else
{
uint8_t x_157; 
x_157 = lean_name_eq(x_134, x_134);
if (x_157 == 0)
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_158 = x_1;
} else {
 lean_dec_ref(x_1);
 x_158 = lean_box(0);
}
x_159 = lean_ctor_get(x_51, 0);
lean_inc(x_159);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 lean_ctor_release(x_51, 1);
 lean_ctor_release(x_51, 2);
 lean_ctor_release(x_51, 3);
 x_160 = x_51;
} else {
 lean_dec_ref(x_51);
 x_160 = lean_box(0);
}
if (lean_is_scalar(x_160)) {
 x_161 = lean_alloc_ctor(0, 4, 0);
} else {
 x_161 = x_160;
}
lean_ctor_set(x_161, 0, x_159);
lean_ctor_set(x_161, 1, x_133);
lean_ctor_set(x_161, 2, x_134);
lean_ctor_set(x_161, 3, x_131);
if (lean_is_scalar(x_158)) {
 x_162 = lean_alloc_ctor(4, 1, 0);
} else {
 x_162 = x_158;
}
lean_ctor_set(x_162, 0, x_161);
x_163 = l_Lean_Compiler_LCNF_attachCodeDecls(x_137, x_162);
lean_dec(x_137);
x_164 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_164, 0, x_163);
lean_ctor_set(x_164, 1, x_132);
return x_164;
}
else
{
lean_object* x_165; lean_object* x_166; 
lean_dec(x_134);
lean_dec(x_133);
lean_dec(x_131);
lean_dec(x_51);
x_165 = l_Lean_Compiler_LCNF_attachCodeDecls(x_137, x_1);
lean_dec(x_137);
x_166 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_166, 0, x_165);
lean_ctor_set(x_166, 1, x_132);
return x_166;
}
}
}
}
}
else
{
uint8_t x_167; 
lean_dec(x_70);
lean_dec(x_66);
lean_dec(x_51);
lean_dec(x_1);
x_167 = !lean_is_exclusive(x_71);
if (x_167 == 0)
{
return x_71;
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_168 = lean_ctor_get(x_71, 0);
x_169 = lean_ctor_get(x_71, 1);
lean_inc(x_169);
lean_inc(x_168);
lean_dec(x_71);
x_170 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_170, 0, x_168);
lean_ctor_set(x_170, 1, x_169);
return x_170;
}
}
}
}
else
{
uint8_t x_177; 
lean_dec(x_58);
lean_dec(x_51);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_177 = !lean_is_exclusive(x_60);
if (x_177 == 0)
{
return x_60;
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_178 = lean_ctor_get(x_60, 0);
x_179 = lean_ctor_get(x_60, 1);
lean_inc(x_179);
lean_inc(x_178);
lean_dec(x_60);
x_180 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_180, 0, x_178);
lean_ctor_set(x_180, 1, x_179);
return x_180;
}
}
}
else
{
uint8_t x_181; 
lean_dec(x_51);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_181 = !lean_is_exclusive(x_52);
if (x_181 == 0)
{
return x_52;
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_182 = lean_ctor_get(x_52, 0);
x_183 = lean_ctor_get(x_52, 1);
lean_inc(x_183);
lean_inc(x_182);
lean_dec(x_52);
x_184 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_184, 0, x_182);
lean_ctor_set(x_184, 1, x_183);
return x_184;
}
}
}
default: 
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_185 = l_List_redLength___rarg(x_2);
x_186 = lean_mk_empty_array_with_capacity(x_185);
lean_dec(x_185);
x_187 = l_List_toArrayAux___rarg(x_2, x_186);
x_188 = l_Array_reverse___rarg(x_187);
x_189 = l_Lean_Compiler_LCNF_attachCodeDecls(x_188, x_1);
lean_dec(x_188);
x_190 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_190, 0, x_189);
lean_ctor_set(x_190, 1, x_7);
return x_190;
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__3(x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
return x_13;
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
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2249____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2249____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2249____closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2249____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2249____closed__2;
x_2 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__3___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2249____closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("LCNF", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2249____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2249____closed__3;
x_2 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2249____closed__4;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2249____closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("initFn", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2249____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2249____closed__5;
x_2 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2249____closed__6;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2249____closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_@", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2249____closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2249____closed__7;
x_2 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2249____closed__8;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2249____closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2249____closed__9;
x_2 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2249____closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2249____closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2249____closed__10;
x_2 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__3___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2249____closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2249____closed__11;
x_2 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2249____closed__4;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2249____closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("FloatLetIn", 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2249____closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2249____closed__12;
x_2 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2249____closed__13;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2249____closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_hyg", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2249____closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2249____closed__14;
x_2 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2249____closed__15;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2249____closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2249____closed__16;
x_2 = lean_unsigned_to_nat(2249u);
x_3 = l_Lean_Name_num___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2249_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__3___closed__3;
x_3 = 1;
x_4 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2249____closed__17;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_CompilerM(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_FVarUtil(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_PassManager(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_Types(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_FloatLetIn(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
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
l_Lean_Compiler_LCNF_FloatLetIn_BaseFloatContext_decls___default = _init_l_Lean_Compiler_LCNF_FloatLetIn_BaseFloatContext_decls___default();
lean_mark_persistent(l_Lean_Compiler_LCNF_FloatLetIn_BaseFloatContext_decls___default);
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
l_Lean_Compiler_LCNF_FloatLetIn_dontFloat___closed__1 = _init_l_Lean_Compiler_LCNF_FloatLetIn_dontFloat___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_FloatLetIn_dontFloat___closed__1);
l_Lean_Compiler_LCNF_FloatLetIn_dontFloat___closed__2 = _init_l_Lean_Compiler_LCNF_FloatLetIn_dontFloat___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_FloatLetIn_dontFloat___closed__2);
l_Lean_Compiler_LCNF_FloatLetIn_dontFloat___closed__3 = _init_l_Lean_Compiler_LCNF_FloatLetIn_dontFloat___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_FloatLetIn_dontFloat___closed__3);
l_Lean_Compiler_LCNF_FloatLetIn_dontFloat___closed__4 = _init_l_Lean_Compiler_LCNF_FloatLetIn_dontFloat___closed__4();
lean_mark_persistent(l_Lean_Compiler_LCNF_FloatLetIn_dontFloat___closed__4);
l_Lean_Compiler_LCNF_FloatLetIn_dontFloat___closed__5 = _init_l_Lean_Compiler_LCNF_FloatLetIn_dontFloat___closed__5();
lean_mark_persistent(l_Lean_Compiler_LCNF_FloatLetIn_dontFloat___closed__5);
l_List_forIn_loop___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases___spec__1___closed__1 = _init_l_List_forIn_loop___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases___spec__1___closed__1();
lean_mark_persistent(l_List_forIn_loop___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases___spec__1___closed__1);
l_Lean_isTracingEnabledFor___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__1___closed__1 = _init_l_Lean_isTracingEnabledFor___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__1___closed__1();
lean_mark_persistent(l_Lean_isTracingEnabledFor___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__1___closed__1);
l_Lean_addTrace___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__2___closed__1 = _init_l_Lean_addTrace___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__2___closed__1();
lean_mark_persistent(l_Lean_addTrace___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__2___closed__1);
l_Lean_addTrace___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__2___closed__2 = _init_l_Lean_addTrace___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__2___closed__2();
lean_mark_persistent(l_Lean_addTrace___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__2___closed__2);
l_Lean_addTrace___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__2___closed__3 = _init_l_Lean_addTrace___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__2___closed__3();
lean_mark_persistent(l_Lean_addTrace___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__2___closed__3);
l_Lean_addTrace___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__2___closed__4 = _init_l_Lean_addTrace___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__2___closed__4();
lean_mark_persistent(l_Lean_addTrace___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__2___closed__4);
l_Lean_addTrace___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__2___closed__5 = _init_l_Lean_addTrace___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__2___closed__5();
lean_mark_persistent(l_Lean_addTrace___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__2___closed__5);
l_Lean_addTrace___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__2___closed__6 = _init_l_Lean_addTrace___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__2___closed__6();
lean_mark_persistent(l_Lean_addTrace___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__2___closed__6);
l_Lean_addTrace___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__2___closed__7 = _init_l_Lean_addTrace___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__2___closed__7();
lean_mark_persistent(l_Lean_addTrace___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__2___closed__7);
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
l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__3___closed__9 = _init_l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__3___closed__9();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___spec__3___closed__9);
l_Lean_Compiler_LCNF_floatLetIn___closed__1 = _init_l_Lean_Compiler_LCNF_floatLetIn___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_floatLetIn___closed__1);
l_Lean_Compiler_LCNF_floatLetIn___closed__2 = _init_l_Lean_Compiler_LCNF_floatLetIn___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_floatLetIn___closed__2);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2249____closed__1 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2249____closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2249____closed__1);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2249____closed__2 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2249____closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2249____closed__2);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2249____closed__3 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2249____closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2249____closed__3);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2249____closed__4 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2249____closed__4();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2249____closed__4);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2249____closed__5 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2249____closed__5();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2249____closed__5);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2249____closed__6 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2249____closed__6();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2249____closed__6);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2249____closed__7 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2249____closed__7();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2249____closed__7);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2249____closed__8 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2249____closed__8();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2249____closed__8);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2249____closed__9 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2249____closed__9();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2249____closed__9);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2249____closed__10 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2249____closed__10();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2249____closed__10);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2249____closed__11 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2249____closed__11();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2249____closed__11);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2249____closed__12 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2249____closed__12();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2249____closed__12);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2249____closed__13 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2249____closed__13();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2249____closed__13);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2249____closed__14 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2249____closed__14();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2249____closed__14);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2249____closed__15 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2249____closed__15();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2249____closed__15);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2249____closed__16 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2249____closed__16();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2249____closed__16);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2249____closed__17 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2249____closed__17();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2249____closed__17);
if (builtin) {res = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2249_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
