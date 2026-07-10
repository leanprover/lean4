// Lean compiler output
// Module: Lean.Meta.Tactic.BVDecide.Normalize.Structures
// Imports: public import Lean.Meta.Tactic.BVDecide.Normalize.TypeAnalysis import Lean.Meta.Tactic.BVDecide.Normalize.ApplyControlFlow import Lean.Meta.Tactic.Ext
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
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkConstWithFreshMVarLevels(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallMetaTelescopeReducing(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_getStructureInfo(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_isInductiveCore_x3f(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Environment_findAsync_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_AsyncConstantInfo_toConstantInfo(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO(lean_object*);
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* lean_array_pop(lean_object*);
lean_object* l_Lean_Meta_mkProjFn___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_st_ref_take(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_mkApplyProjControlDiscrPath(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_Simprocs_addCore(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_isLet(lean_object*, uint8_t);
uint8_t l_Lean_LocalDecl_isImplementationDetail(lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_MVarId_assertHypotheses(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_empty(lean_object*);
extern lean_object* l_Lean_Meta_Ext_instInhabitedExtTheorem_default;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_Meta_Ext_extExtension;
extern lean_object* l_Lean_Meta_Ext_instInhabitedExtTheorems_default;
lean_object* l_Lean_ScopedEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_getMatch___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_reverse___redArg(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
uint8_t lean_bool_not(uint8_t);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_simpGlobalConfig;
lean_object* l_Lean_Meta_SimpTheoremsArray_addTheorem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_addDefaultTypeAnalysisLemmas(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getSimpCongrTheorems___redArg(lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Meta_Simp_mkContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getPropHyps(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_simpGoal(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_mkConstAppWithMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_mkConstAppWithMVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_swapLoop___at___00__private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_findExtIff_x3f_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_findExtIff_x3f_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_findExtIff_x3f_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_findExtIff_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_findExtIff_x3f_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_findExtIff_x3f_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_findExtIff_x3f_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_findExtIff_x3f_spec__0___redArg___closed__0;
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_findExtIff_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_findExtIff_x3f_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_findExtIff_x3f_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_findExtIff_x3f_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_findExtIff_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_iff"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_findExtIff_x3f___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_findExtIff_x3f___closed__0_value;
static const lean_array_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_findExtIff_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_findExtIff_x3f___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_findExtIff_x3f___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_findExtIff_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_findExtIff_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_findExtIff_x3f_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_findExtIff_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_findExtIff_x3f_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_findExtIff_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_swapLoop___at___00__private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_findExtIff_x3f_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_findExtIff_x3f_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_findExtIff_x3f_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_getConstInfoInduct___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_getConstInfoInduct___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__0___closed__0 = (const lean_object*)&l_Lean_getConstInfoInduct___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__0___closed__0_value;
static lean_once_cell_t l_Lean_getConstInfoInduct___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoInduct___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__0___closed__1;
static const lean_string_object l_Lean_getConstInfoInduct___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "` is not an inductive type"};
static const lean_object* l_Lean_getConstInfoInduct___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__0___closed__2 = (const lean_object*)&l_Lean_getConstInfoInduct___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__0___closed__2_value;
static lean_once_cell_t l_Lean_getConstInfoInduct___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoInduct___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__0___closed__3;
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "ite"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___redArg___closed__0_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(15, 2, 151, 246, 61, 29, 192, 254)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___redArg___closed__1 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___redArg___closed__1_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___redArg___closed__2 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___redArg___closed__2_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___redArg___closed__3 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___redArg___closed__3_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___redArg___closed__4 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___redArg___closed__4_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "BVDecide"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___redArg___closed__5 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___redArg___closed__5_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Normalize"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___redArg___closed__6 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___redArg___closed__6_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "applyIteSimproc"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___redArg___closed__7 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___redArg___closed__7_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___redArg___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___redArg___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___redArg___closed__8_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___redArg___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___redArg___closed__8_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(7, 212, 55, 101, 104, 194, 19, 213)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___redArg___closed__8_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___redArg___closed__8_value_aux_2),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(178, 14, 254, 151, 151, 84, 196, 42)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___redArg___closed__8_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___redArg___closed__8_value_aux_3),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___redArg___closed__6_value),LEAN_SCALAR_PTR_LITERAL(227, 54, 65, 115, 92, 106, 117, 217)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___redArg___closed__8_value_aux_4),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(84, 239, 46, 245, 153, 49, 212, 168)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___redArg___closed__8 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___redArg___closed__8_value;
static const lean_closure_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___redArg___closed__9 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___redArg___closed__9_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___redArg___closed__9_value)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___redArg___closed__10 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___redArg___closed__10_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "cond"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___redArg___closed__11 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___redArg___closed__11_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___redArg___closed__11_value),LEAN_SCALAR_PTR_LITERAL(130, 140, 200, 235, 144, 197, 118, 1)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___redArg___closed__12 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___redArg___closed__12_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "applyCondSimproc"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___redArg___closed__13 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___redArg___closed__13_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___redArg___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___redArg___closed__14_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___redArg___closed__14_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___redArg___closed__14_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___redArg___closed__14_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(7, 212, 55, 101, 104, 194, 19, 213)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___redArg___closed__14_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___redArg___closed__14_value_aux_2),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(178, 14, 254, 151, 151, 84, 196, 42)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___redArg___closed__14_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___redArg___closed__14_value_aux_3),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___redArg___closed__6_value),LEAN_SCALAR_PTR_LITERAL(227, 54, 65, 115, 92, 106, 117, 217)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___redArg___closed__14_value_aux_4),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___redArg___closed__13_value),LEAN_SCALAR_PTR_LITERAL(223, 15, 140, 191, 132, 164, 133, 159)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___redArg___closed__14 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___redArg___closed__14_value;
static const lean_closure_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___redArg___closed__15 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___redArg___closed__15_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___redArg___closed__15_value)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___redArg___closed__16 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___redArg___closed__16_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "bv"};
static const lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__3___closed__0 = (const lean_object*)&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__3___closed__0_value;
static const lean_ctor_object l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__3___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__3___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__3___closed__1_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(194, 95, 140, 15, 16, 100, 236, 219)}};
static const lean_ctor_object l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__3___closed__1_value_aux_1),((lean_object*)&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(139, 41, 106, 94, 234, 34, 111, 146)}};
static const lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__3___closed__1 = (const lean_object*)&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__3___closed__1_value;
static const lean_string_object l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__3___closed__2 = (const lean_object*)&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__3___closed__2_value;
static const lean_ctor_object l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__3___closed__3 = (const lean_object*)&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__3___closed__3_value;
static lean_once_cell_t l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__3___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__3___closed__4;
static const lean_string_object l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "Using ext_iff: "};
static const lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__3___closed__5 = (const lean_object*)&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__3___closed__5_value;
static lean_once_cell_t l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__3___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__3___closed__6;
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess_spec__0___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess_spec__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess___lam__0___closed__0;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess___lam__0___closed__1;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess___lam__0___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess___closed__0;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess___closed__1;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess___closed__2;
static const lean_array_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__2_spec__5___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__2_spec__5___closed__0;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__2_spec__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__2_spec__5___closed__1 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__2_spec__5___closed__1_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__2_spec__5___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__2_spec__5___closed__2 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__2_spec__5___closed__2_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__2_spec__5___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__2_spec__5___closed__3 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__2_spec__5___closed__3_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__2_spec__5___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__2_spec__5___closed__4 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__2_spec__5___closed__4_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__2_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "` is not a constructor"};
static const lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__2___closed__0 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__2___closed__0_value;
static lean_once_cell_t l_Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__2___closed__1;
static const lean_string_object l_Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Lean.MonadEnv"};
static const lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__2___closed__2 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__2___closed__2_value;
static const lean_string_object l_Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Lean.isCtor\?"};
static const lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__2___closed__3 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__2___closed__3_value;
static const lean_string_object l_Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__2___closed__4 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__2___closed__4_value;
static lean_once_cell_t l_Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__2___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__2___closed__5;
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__0___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__3___redArg___closed__0;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__3___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "h"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__3___redArg___closed__1 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__3___redArg___closed__1_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__3___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__3___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(176, 181, 207, 77, 197, 87, 68, 121)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__3___redArg___closed__2 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__3___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__1_spec__3_spec__6___redArg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__1_spec__3_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__1_spec__3(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__1_spec__2_spec__4_spec__9___redArg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__1_spec__2_spec__4_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__1_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__1_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_structuresPass___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_structuresPass___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_Tactic_BVDecide_Normalize_structuresPass___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_structuresPass___lam__1___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_structuresPass___lam__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_structuresPass___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_structuresPass___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_structuresPass___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_Normalize_structuresPass___lam__1___boxed, .m_arity = 8, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_structuresPass___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_structuresPass___closed__0_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_structuresPass___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "structures"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_structuresPass___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_structuresPass___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_structuresPass___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_structuresPass___closed__1_value),LEAN_SCALAR_PTR_LITERAL(74, 214, 82, 86, 36, 11, 245, 232)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_structuresPass___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_structuresPass___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_structuresPass___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_structuresPass___closed__2_value),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_structuresPass___closed__0_value)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_structuresPass___closed__3 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_structuresPass___closed__3_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_structuresPass = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_structuresPass___closed__3_value;
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__3___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__1_spec__3_spec__6(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__1_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__1_spec__2_spec__4_spec__9(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__1_spec__2_spec__4_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_mkConstAppWithMVars(lean_object* v_declName_1_, lean_object* v_a_2_, lean_object* v_a_3_, lean_object* v_a_4_, lean_object* v_a_5_){
_start:
{
lean_object* v___x_7_; 
v___x_7_ = l_Lean_Meta_mkConstWithFreshMVarLevels(v_declName_1_, v_a_2_, v_a_3_, v_a_4_, v_a_5_);
if (lean_obj_tag(v___x_7_) == 0)
{
lean_object* v_a_8_; lean_object* v___x_9_; 
v_a_8_ = lean_ctor_get(v___x_7_, 0);
lean_inc_n(v_a_8_, 2);
lean_dec_ref_known(v___x_7_, 1);
lean_inc(v_a_5_);
lean_inc_ref(v_a_4_);
lean_inc(v_a_3_);
lean_inc_ref(v_a_2_);
v___x_9_ = lean_infer_type(v_a_8_, v_a_2_, v_a_3_, v_a_4_, v_a_5_);
if (lean_obj_tag(v___x_9_) == 0)
{
lean_object* v_a_10_; lean_object* v___x_11_; uint8_t v___x_12_; lean_object* v___x_13_; 
v_a_10_ = lean_ctor_get(v___x_9_, 0);
lean_inc(v_a_10_);
lean_dec_ref_known(v___x_9_, 1);
v___x_11_ = lean_box(0);
v___x_12_ = 0;
v___x_13_ = l_Lean_Meta_forallMetaTelescopeReducing(v_a_10_, v___x_11_, v___x_12_, v_a_2_, v_a_3_, v_a_4_, v_a_5_);
if (lean_obj_tag(v___x_13_) == 0)
{
lean_object* v_a_14_; lean_object* v___x_16_; uint8_t v_isShared_17_; uint8_t v_isSharedCheck_23_; 
v_a_14_ = lean_ctor_get(v___x_13_, 0);
v_isSharedCheck_23_ = !lean_is_exclusive(v___x_13_);
if (v_isSharedCheck_23_ == 0)
{
v___x_16_ = v___x_13_;
v_isShared_17_ = v_isSharedCheck_23_;
goto v_resetjp_15_;
}
else
{
lean_inc(v_a_14_);
lean_dec(v___x_13_);
v___x_16_ = lean_box(0);
v_isShared_17_ = v_isSharedCheck_23_;
goto v_resetjp_15_;
}
v_resetjp_15_:
{
lean_object* v_fst_18_; lean_object* v___x_19_; lean_object* v___x_21_; 
v_fst_18_ = lean_ctor_get(v_a_14_, 0);
lean_inc(v_fst_18_);
lean_dec(v_a_14_);
v___x_19_ = l_Lean_mkAppN(v_a_8_, v_fst_18_);
lean_dec(v_fst_18_);
if (v_isShared_17_ == 0)
{
lean_ctor_set(v___x_16_, 0, v___x_19_);
v___x_21_ = v___x_16_;
goto v_reusejp_20_;
}
else
{
lean_object* v_reuseFailAlloc_22_; 
v_reuseFailAlloc_22_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_22_, 0, v___x_19_);
v___x_21_ = v_reuseFailAlloc_22_;
goto v_reusejp_20_;
}
v_reusejp_20_:
{
return v___x_21_;
}
}
}
else
{
lean_object* v_a_24_; lean_object* v___x_26_; uint8_t v_isShared_27_; uint8_t v_isSharedCheck_31_; 
lean_dec(v_a_8_);
v_a_24_ = lean_ctor_get(v___x_13_, 0);
v_isSharedCheck_31_ = !lean_is_exclusive(v___x_13_);
if (v_isSharedCheck_31_ == 0)
{
v___x_26_ = v___x_13_;
v_isShared_27_ = v_isSharedCheck_31_;
goto v_resetjp_25_;
}
else
{
lean_inc(v_a_24_);
lean_dec(v___x_13_);
v___x_26_ = lean_box(0);
v_isShared_27_ = v_isSharedCheck_31_;
goto v_resetjp_25_;
}
v_resetjp_25_:
{
lean_object* v___x_29_; 
if (v_isShared_27_ == 0)
{
v___x_29_ = v___x_26_;
goto v_reusejp_28_;
}
else
{
lean_object* v_reuseFailAlloc_30_; 
v_reuseFailAlloc_30_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_30_, 0, v_a_24_);
v___x_29_ = v_reuseFailAlloc_30_;
goto v_reusejp_28_;
}
v_reusejp_28_:
{
return v___x_29_;
}
}
}
}
else
{
lean_dec(v_a_8_);
return v___x_9_;
}
}
else
{
return v___x_7_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_mkConstAppWithMVars___boxed(lean_object* v_declName_32_, lean_object* v_a_33_, lean_object* v_a_34_, lean_object* v_a_35_, lean_object* v_a_36_, lean_object* v_a_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_mkConstAppWithMVars(v_declName_32_, v_a_33_, v_a_34_, v_a_35_, v_a_36_);
lean_dec(v_a_36_);
lean_dec_ref(v_a_35_);
lean_dec(v_a_34_);
lean_dec_ref(v_a_33_);
return v_res_38_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_swapLoop___at___00__private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_findExtIff_x3f_spec__1_spec__2___redArg(lean_object* v_xs_39_, lean_object* v_j_40_){
_start:
{
lean_object* v_zero_41_; uint8_t v_isZero_42_; 
v_zero_41_ = lean_unsigned_to_nat(0u);
v_isZero_42_ = lean_nat_dec_eq(v_j_40_, v_zero_41_);
if (v_isZero_42_ == 1)
{
lean_dec(v_j_40_);
return v_xs_39_;
}
else
{
lean_object* v___x_43_; lean_object* v_priority_44_; lean_object* v_one_45_; lean_object* v_n_46_; lean_object* v___x_47_; lean_object* v_priority_48_; uint8_t v___x_49_; 
v___x_43_ = lean_array_fget_borrowed(v_xs_39_, v_j_40_);
v_priority_44_ = lean_ctor_get(v___x_43_, 1);
v_one_45_ = lean_unsigned_to_nat(1u);
v_n_46_ = lean_nat_sub(v_j_40_, v_one_45_);
v___x_47_ = lean_array_fget_borrowed(v_xs_39_, v_n_46_);
v_priority_48_ = lean_ctor_get(v___x_47_, 1);
v___x_49_ = lean_nat_dec_lt(v_priority_44_, v_priority_48_);
if (v___x_49_ == 0)
{
lean_dec(v_n_46_);
lean_dec(v_j_40_);
return v_xs_39_;
}
else
{
lean_object* v___x_50_; 
v___x_50_ = lean_array_fswap(v_xs_39_, v_j_40_, v_n_46_);
lean_dec(v_j_40_);
v_xs_39_ = v___x_50_;
v_j_40_ = v_n_46_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_findExtIff_x3f_spec__1(lean_object* v_xs_52_, lean_object* v_i_53_, lean_object* v_fuel_54_){
_start:
{
lean_object* v_zero_55_; uint8_t v_isZero_56_; 
v_zero_55_ = lean_unsigned_to_nat(0u);
v_isZero_56_ = lean_nat_dec_eq(v_fuel_54_, v_zero_55_);
if (v_isZero_56_ == 1)
{
lean_dec(v_fuel_54_);
lean_dec(v_i_53_);
return v_xs_52_;
}
else
{
lean_object* v___x_57_; uint8_t v___x_58_; 
v___x_57_ = lean_array_get_size(v_xs_52_);
v___x_58_ = lean_nat_dec_lt(v_i_53_, v___x_57_);
if (v___x_58_ == 0)
{
lean_dec(v_fuel_54_);
lean_dec(v_i_53_);
return v_xs_52_;
}
else
{
lean_object* v_one_59_; lean_object* v_n_60_; lean_object* v___x_61_; lean_object* v___x_62_; 
v_one_59_ = lean_unsigned_to_nat(1u);
v_n_60_ = lean_nat_sub(v_fuel_54_, v_one_59_);
lean_dec(v_fuel_54_);
lean_inc(v_i_53_);
v___x_61_ = l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_swapLoop___at___00__private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_findExtIff_x3f_spec__1_spec__2___redArg(v_xs_52_, v_i_53_);
v___x_62_ = lean_nat_add(v_i_53_, v_one_59_);
lean_dec(v_i_53_);
v_xs_52_ = v___x_61_;
v_i_53_ = v___x_62_;
v_fuel_54_ = v_n_60_;
goto _start;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_findExtIff_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_64_, lean_object* v_i_65_, lean_object* v_k_66_){
_start:
{
lean_object* v___x_67_; uint8_t v___x_68_; 
v___x_67_ = lean_array_get_size(v_keys_64_);
v___x_68_ = lean_nat_dec_lt(v_i_65_, v___x_67_);
if (v___x_68_ == 0)
{
lean_dec(v_i_65_);
return v___x_68_;
}
else
{
lean_object* v_k_x27_69_; uint8_t v___x_70_; 
v_k_x27_69_ = lean_array_fget_borrowed(v_keys_64_, v_i_65_);
v___x_70_ = lean_name_eq(v_k_66_, v_k_x27_69_);
if (v___x_70_ == 0)
{
lean_object* v___x_71_; lean_object* v___x_72_; 
v___x_71_ = lean_unsigned_to_nat(1u);
v___x_72_ = lean_nat_add(v_i_65_, v___x_71_);
lean_dec(v_i_65_);
v_i_65_ = v___x_72_;
goto _start;
}
else
{
lean_dec(v_i_65_);
return v___x_70_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_findExtIff_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_74_, lean_object* v_i_75_, lean_object* v_k_76_){
_start:
{
uint8_t v_res_77_; lean_object* v_r_78_; 
v_res_77_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_findExtIff_x3f_spec__0_spec__0_spec__1___redArg(v_keys_74_, v_i_75_, v_k_76_);
lean_dec(v_k_76_);
lean_dec_ref(v_keys_74_);
v_r_78_ = lean_box(v_res_77_);
return v_r_78_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_findExtIff_x3f_spec__0_spec__0___redArg(lean_object* v_x_79_, size_t v_x_80_, lean_object* v_x_81_){
_start:
{
if (lean_obj_tag(v_x_79_) == 0)
{
lean_object* v_es_82_; lean_object* v___x_83_; size_t v___x_84_; size_t v___x_85_; lean_object* v_j_86_; lean_object* v___x_87_; 
v_es_82_ = lean_ctor_get(v_x_79_, 0);
v___x_83_ = lean_box(2);
v___x_84_ = ((size_t)31ULL);
v___x_85_ = lean_usize_land(v_x_80_, v___x_84_);
v_j_86_ = lean_usize_to_nat(v___x_85_);
v___x_87_ = lean_array_get_borrowed(v___x_83_, v_es_82_, v_j_86_);
lean_dec(v_j_86_);
switch(lean_obj_tag(v___x_87_))
{
case 0:
{
lean_object* v_key_88_; uint8_t v___x_89_; 
v_key_88_ = lean_ctor_get(v___x_87_, 0);
v___x_89_ = lean_name_eq(v_x_81_, v_key_88_);
return v___x_89_;
}
case 1:
{
lean_object* v_node_90_; size_t v___x_91_; size_t v___x_92_; 
v_node_90_ = lean_ctor_get(v___x_87_, 0);
v___x_91_ = ((size_t)5ULL);
v___x_92_ = lean_usize_shift_right(v_x_80_, v___x_91_);
v_x_79_ = v_node_90_;
v_x_80_ = v___x_92_;
goto _start;
}
default: 
{
uint8_t v___x_94_; 
v___x_94_ = 0;
return v___x_94_;
}
}
}
else
{
lean_object* v_ks_95_; lean_object* v___x_96_; uint8_t v___x_97_; 
v_ks_95_ = lean_ctor_get(v_x_79_, 0);
v___x_96_ = lean_unsigned_to_nat(0u);
v___x_97_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_findExtIff_x3f_spec__0_spec__0_spec__1___redArg(v_ks_95_, v___x_96_, v_x_81_);
return v___x_97_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_findExtIff_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_98_, lean_object* v_x_99_, lean_object* v_x_100_){
_start:
{
size_t v_x_1615__boxed_101_; uint8_t v_res_102_; lean_object* v_r_103_; 
v_x_1615__boxed_101_ = lean_unbox_usize(v_x_99_);
lean_dec(v_x_99_);
v_res_102_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_findExtIff_x3f_spec__0_spec__0___redArg(v_x_98_, v_x_1615__boxed_101_, v_x_100_);
lean_dec(v_x_100_);
lean_dec_ref(v_x_98_);
v_r_103_ = lean_box(v_res_102_);
return v_r_103_;
}
}
static uint64_t _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_findExtIff_x3f_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_104_; uint64_t v___x_105_; 
v___x_104_ = lean_unsigned_to_nat(1723u);
v___x_105_ = lean_uint64_of_nat(v___x_104_);
return v___x_105_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_findExtIff_x3f_spec__0___redArg(lean_object* v_x_106_, lean_object* v_x_107_){
_start:
{
uint64_t v___y_109_; 
if (lean_obj_tag(v_x_107_) == 0)
{
uint64_t v___x_112_; 
v___x_112_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_findExtIff_x3f_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_findExtIff_x3f_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_findExtIff_x3f_spec__0___redArg___closed__0);
v___y_109_ = v___x_112_;
goto v___jp_108_;
}
else
{
uint64_t v_hash_113_; 
v_hash_113_ = lean_ctor_get_uint64(v_x_107_, sizeof(void*)*2);
v___y_109_ = v_hash_113_;
goto v___jp_108_;
}
v___jp_108_:
{
size_t v___x_110_; uint8_t v___x_111_; 
v___x_110_ = lean_uint64_to_usize(v___y_109_);
v___x_111_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_findExtIff_x3f_spec__0_spec__0___redArg(v_x_106_, v___x_110_, v_x_107_);
return v___x_111_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_findExtIff_x3f_spec__0___redArg___boxed(lean_object* v_x_114_, lean_object* v_x_115_){
_start:
{
uint8_t v_res_116_; lean_object* v_r_117_; 
v_res_116_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_findExtIff_x3f_spec__0___redArg(v_x_114_, v_x_115_);
lean_dec(v_x_115_);
lean_dec_ref(v_x_114_);
v_r_117_ = lean_box(v_res_116_);
return v_r_117_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_findExtIff_x3f_spec__2(lean_object* v___x_118_, lean_object* v_as_119_, size_t v_i_120_, size_t v_stop_121_, lean_object* v_b_122_){
_start:
{
lean_object* v___y_124_; uint8_t v___x_128_; 
v___x_128_ = lean_usize_dec_eq(v_i_120_, v_stop_121_);
if (v___x_128_ == 0)
{
lean_object* v_erased_129_; lean_object* v___x_130_; lean_object* v_declName_131_; uint8_t v___x_132_; uint8_t v___x_133_; 
v_erased_129_ = lean_ctor_get(v___x_118_, 1);
v___x_130_ = lean_array_uget_borrowed(v_as_119_, v_i_120_);
v_declName_131_ = lean_ctor_get(v___x_130_, 0);
v___x_132_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_findExtIff_x3f_spec__0___redArg(v_erased_129_, v_declName_131_);
v___x_133_ = lean_bool_not(v___x_132_);
if (v___x_133_ == 0)
{
v___y_124_ = v_b_122_;
goto v___jp_123_;
}
else
{
lean_object* v___x_134_; 
lean_inc(v___x_130_);
v___x_134_ = lean_array_push(v_b_122_, v___x_130_);
v___y_124_ = v___x_134_;
goto v___jp_123_;
}
}
else
{
return v_b_122_;
}
v___jp_123_:
{
size_t v___x_125_; size_t v___x_126_; 
v___x_125_ = ((size_t)1ULL);
v___x_126_ = lean_usize_add(v_i_120_, v___x_125_);
v_i_120_ = v___x_126_;
v_b_122_ = v___y_124_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_findExtIff_x3f_spec__2___boxed(lean_object* v___x_135_, lean_object* v_as_136_, lean_object* v_i_137_, lean_object* v_stop_138_, lean_object* v_b_139_){
_start:
{
size_t v_i_boxed_140_; size_t v_stop_boxed_141_; lean_object* v_res_142_; 
v_i_boxed_140_ = lean_unbox_usize(v_i_137_);
lean_dec(v_i_137_);
v_stop_boxed_141_ = lean_unbox_usize(v_stop_138_);
lean_dec(v_stop_138_);
v_res_142_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_findExtIff_x3f_spec__2(v___x_135_, v_as_136_, v_i_boxed_140_, v_stop_boxed_141_, v_b_139_);
lean_dec_ref(v_as_136_);
lean_dec_ref(v___x_135_);
return v_res_142_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_findExtIff_x3f(lean_object* v_info_146_, lean_object* v_a_147_, lean_object* v_a_148_, lean_object* v_a_149_, lean_object* v_a_150_){
_start:
{
lean_object* v_a_153_; lean_object* v_toConstantVal_177_; lean_object* v_name_178_; lean_object* v___x_179_; 
v_toConstantVal_177_ = lean_ctor_get(v_info_146_, 0);
lean_inc_ref(v_toConstantVal_177_);
lean_dec_ref(v_info_146_);
v_name_178_ = lean_ctor_get(v_toConstantVal_177_, 0);
lean_inc(v_name_178_);
lean_dec_ref(v_toConstantVal_177_);
v___x_179_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_mkConstAppWithMVars(v_name_178_, v_a_147_, v_a_148_, v_a_149_, v_a_150_);
if (lean_obj_tag(v___x_179_) == 0)
{
lean_object* v_a_180_; lean_object* v___x_181_; lean_object* v_env_182_; lean_object* v___x_183_; lean_object* v_ext_184_; lean_object* v_toEnvExtension_185_; lean_object* v_asyncMode_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v_tree_189_; lean_object* v___x_190_; 
v_a_180_ = lean_ctor_get(v___x_179_, 0);
lean_inc(v_a_180_);
lean_dec_ref_known(v___x_179_, 1);
v___x_181_ = lean_st_ref_get(v_a_150_);
v_env_182_ = lean_ctor_get(v___x_181_, 0);
lean_inc_ref(v_env_182_);
lean_dec(v___x_181_);
v___x_183_ = l_Lean_Meta_Ext_extExtension;
v_ext_184_ = lean_ctor_get(v___x_183_, 1);
v_toEnvExtension_185_ = lean_ctor_get(v_ext_184_, 0);
v_asyncMode_186_ = lean_ctor_get(v_toEnvExtension_185_, 2);
v___x_187_ = l_Lean_Meta_Ext_instInhabitedExtTheorems_default;
v___x_188_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_187_, v___x_183_, v_env_182_, v_asyncMode_186_);
v_tree_189_ = lean_ctor_get(v___x_188_, 0);
lean_inc_ref(v_tree_189_);
v___x_190_ = l_Lean_Meta_DiscrTree_getMatch___redArg(v_tree_189_, v_a_180_, v_a_147_, v_a_148_, v_a_149_, v_a_150_);
lean_dec_ref(v_tree_189_);
if (lean_obj_tag(v___x_190_) == 0)
{
lean_object* v_a_191_; lean_object* v___y_193_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; uint8_t v___x_201_; 
v_a_191_ = lean_ctor_get(v___x_190_, 0);
lean_inc(v_a_191_);
lean_dec_ref_known(v___x_190_, 1);
v___x_198_ = lean_unsigned_to_nat(0u);
v___x_199_ = lean_array_get_size(v_a_191_);
v___x_200_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_findExtIff_x3f___closed__1));
v___x_201_ = lean_nat_dec_lt(v___x_198_, v___x_199_);
if (v___x_201_ == 0)
{
lean_dec(v_a_191_);
lean_dec(v___x_188_);
v___y_193_ = v___x_200_;
goto v___jp_192_;
}
else
{
uint8_t v___x_202_; 
v___x_202_ = lean_nat_dec_le(v___x_199_, v___x_199_);
if (v___x_202_ == 0)
{
if (v___x_201_ == 0)
{
lean_dec(v_a_191_);
lean_dec(v___x_188_);
v___y_193_ = v___x_200_;
goto v___jp_192_;
}
else
{
size_t v___x_203_; size_t v___x_204_; lean_object* v___x_205_; 
v___x_203_ = ((size_t)0ULL);
v___x_204_ = lean_usize_of_nat(v___x_199_);
v___x_205_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_findExtIff_x3f_spec__2(v___x_188_, v_a_191_, v___x_203_, v___x_204_, v___x_200_);
lean_dec(v_a_191_);
lean_dec(v___x_188_);
v___y_193_ = v___x_205_;
goto v___jp_192_;
}
}
else
{
size_t v___x_206_; size_t v___x_207_; lean_object* v___x_208_; 
v___x_206_ = ((size_t)0ULL);
v___x_207_ = lean_usize_of_nat(v___x_199_);
v___x_208_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_findExtIff_x3f_spec__2(v___x_188_, v_a_191_, v___x_206_, v___x_207_, v___x_200_);
lean_dec(v_a_191_);
lean_dec(v___x_188_);
v___y_193_ = v___x_208_;
goto v___jp_192_;
}
}
v___jp_192_:
{
lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; 
v___x_194_ = lean_unsigned_to_nat(0u);
v___x_195_ = lean_array_get_size(v___y_193_);
v___x_196_ = l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_findExtIff_x3f_spec__1(v___y_193_, v___x_194_, v___x_195_);
v___x_197_ = l_Array_reverse___redArg(v___x_196_);
v_a_153_ = v___x_197_;
goto v___jp_152_;
}
}
else
{
lean_dec(v___x_188_);
if (lean_obj_tag(v___x_190_) == 0)
{
lean_object* v_a_209_; 
v_a_209_ = lean_ctor_get(v___x_190_, 0);
lean_inc(v_a_209_);
lean_dec_ref_known(v___x_190_, 1);
v_a_153_ = v_a_209_;
goto v___jp_152_;
}
else
{
lean_object* v_a_210_; lean_object* v___x_212_; uint8_t v_isShared_213_; uint8_t v_isSharedCheck_217_; 
v_a_210_ = lean_ctor_get(v___x_190_, 0);
v_isSharedCheck_217_ = !lean_is_exclusive(v___x_190_);
if (v_isSharedCheck_217_ == 0)
{
v___x_212_ = v___x_190_;
v_isShared_213_ = v_isSharedCheck_217_;
goto v_resetjp_211_;
}
else
{
lean_inc(v_a_210_);
lean_dec(v___x_190_);
v___x_212_ = lean_box(0);
v_isShared_213_ = v_isSharedCheck_217_;
goto v_resetjp_211_;
}
v_resetjp_211_:
{
lean_object* v___x_215_; 
if (v_isShared_213_ == 0)
{
v___x_215_ = v___x_212_;
goto v_reusejp_214_;
}
else
{
lean_object* v_reuseFailAlloc_216_; 
v_reuseFailAlloc_216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_216_, 0, v_a_210_);
v___x_215_ = v_reuseFailAlloc_216_;
goto v_reusejp_214_;
}
v_reusejp_214_:
{
return v___x_215_;
}
}
}
}
}
else
{
lean_object* v_a_218_; lean_object* v___x_220_; uint8_t v_isShared_221_; uint8_t v_isSharedCheck_225_; 
v_a_218_ = lean_ctor_get(v___x_179_, 0);
v_isSharedCheck_225_ = !lean_is_exclusive(v___x_179_);
if (v_isSharedCheck_225_ == 0)
{
v___x_220_ = v___x_179_;
v_isShared_221_ = v_isSharedCheck_225_;
goto v_resetjp_219_;
}
else
{
lean_inc(v_a_218_);
lean_dec(v___x_179_);
v___x_220_ = lean_box(0);
v_isShared_221_ = v_isSharedCheck_225_;
goto v_resetjp_219_;
}
v_resetjp_219_:
{
lean_object* v___x_223_; 
if (v_isShared_221_ == 0)
{
v___x_223_ = v___x_220_;
goto v_reusejp_222_;
}
else
{
lean_object* v_reuseFailAlloc_224_; 
v_reuseFailAlloc_224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_224_, 0, v_a_218_);
v___x_223_ = v_reuseFailAlloc_224_;
goto v_reusejp_222_;
}
v_reusejp_222_:
{
return v___x_223_;
}
}
}
v___jp_152_:
{
lean_object* v___x_154_; lean_object* v___x_155_; uint8_t v___x_156_; 
v___x_154_ = lean_array_get_size(v_a_153_);
v___x_155_ = lean_unsigned_to_nat(0u);
v___x_156_ = lean_nat_dec_eq(v___x_154_, v___x_155_);
if (v___x_156_ == 0)
{
lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v_declName_159_; 
v___x_157_ = l_Lean_Meta_Ext_instInhabitedExtTheorem_default;
v___x_158_ = lean_array_get(v___x_157_, v_a_153_, v___x_155_);
lean_dec_ref(v_a_153_);
v_declName_159_ = lean_ctor_get(v___x_158_, 0);
lean_inc(v_declName_159_);
lean_dec(v___x_158_);
if (lean_obj_tag(v_declName_159_) == 1)
{
lean_object* v_pre_160_; lean_object* v_str_161_; lean_object* v___x_162_; lean_object* v_env_163_; uint8_t v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; uint8_t v___x_168_; 
v_pre_160_ = lean_ctor_get(v_declName_159_, 0);
lean_inc(v_pre_160_);
v_str_161_ = lean_ctor_get(v_declName_159_, 1);
lean_inc_ref(v_str_161_);
lean_dec_ref_known(v_declName_159_, 2);
v___x_162_ = lean_st_ref_get(v_a_150_);
v_env_163_ = lean_ctor_get(v___x_162_, 0);
lean_inc_ref(v_env_163_);
lean_dec(v___x_162_);
v___x_164_ = 1;
v___x_165_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_findExtIff_x3f___closed__0));
v___x_166_ = lean_string_append(v_str_161_, v___x_165_);
v___x_167_ = l_Lean_Name_str___override(v_pre_160_, v___x_166_);
lean_inc(v___x_167_);
v___x_168_ = l_Lean_Environment_contains(v_env_163_, v___x_167_, v___x_164_);
if (v___x_168_ == 0)
{
lean_object* v___x_169_; lean_object* v___x_170_; 
lean_dec(v___x_167_);
v___x_169_ = lean_box(0);
v___x_170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_170_, 0, v___x_169_);
return v___x_170_;
}
else
{
lean_object* v___x_171_; lean_object* v___x_172_; 
v___x_171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_171_, 0, v___x_167_);
v___x_172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_172_, 0, v___x_171_);
return v___x_172_;
}
}
else
{
lean_object* v___x_173_; lean_object* v___x_174_; 
lean_dec(v_declName_159_);
v___x_173_ = lean_box(0);
v___x_174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_174_, 0, v___x_173_);
return v___x_174_;
}
}
else
{
lean_object* v___x_175_; lean_object* v___x_176_; 
lean_dec_ref(v_a_153_);
v___x_175_ = lean_box(0);
v___x_176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_176_, 0, v___x_175_);
return v___x_176_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_findExtIff_x3f___boxed(lean_object* v_info_226_, lean_object* v_a_227_, lean_object* v_a_228_, lean_object* v_a_229_, lean_object* v_a_230_, lean_object* v_a_231_){
_start:
{
lean_object* v_res_232_; 
v_res_232_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_findExtIff_x3f(v_info_226_, v_a_227_, v_a_228_, v_a_229_, v_a_230_);
lean_dec(v_a_230_);
lean_dec_ref(v_a_229_);
lean_dec(v_a_228_);
lean_dec_ref(v_a_227_);
return v_res_232_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_findExtIff_x3f_spec__0(lean_object* v_00_u03b2_233_, lean_object* v_x_234_, lean_object* v_x_235_){
_start:
{
uint8_t v___x_236_; 
v___x_236_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_findExtIff_x3f_spec__0___redArg(v_x_234_, v_x_235_);
return v___x_236_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_findExtIff_x3f_spec__0___boxed(lean_object* v_00_u03b2_237_, lean_object* v_x_238_, lean_object* v_x_239_){
_start:
{
uint8_t v_res_240_; lean_object* v_r_241_; 
v_res_240_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_findExtIff_x3f_spec__0(v_00_u03b2_237_, v_x_238_, v_x_239_);
lean_dec(v_x_239_);
lean_dec_ref(v_x_238_);
v_r_241_ = lean_box(v_res_240_);
return v_r_241_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_findExtIff_x3f_spec__0_spec__0(lean_object* v_00_u03b2_242_, lean_object* v_x_243_, size_t v_x_244_, lean_object* v_x_245_){
_start:
{
uint8_t v___x_246_; 
v___x_246_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_findExtIff_x3f_spec__0_spec__0___redArg(v_x_243_, v_x_244_, v_x_245_);
return v___x_246_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_findExtIff_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_247_, lean_object* v_x_248_, lean_object* v_x_249_, lean_object* v_x_250_){
_start:
{
size_t v_x_1851__boxed_251_; uint8_t v_res_252_; lean_object* v_r_253_; 
v_x_1851__boxed_251_ = lean_unbox_usize(v_x_249_);
lean_dec(v_x_249_);
v_res_252_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_findExtIff_x3f_spec__0_spec__0(v_00_u03b2_247_, v_x_248_, v_x_1851__boxed_251_, v_x_250_);
lean_dec(v_x_250_);
lean_dec_ref(v_x_248_);
v_r_253_ = lean_box(v_res_252_);
return v_r_253_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_swapLoop___at___00__private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_findExtIff_x3f_spec__1_spec__2(lean_object* v_xs_254_, lean_object* v_j_255_, lean_object* v_h_256_){
_start:
{
lean_object* v___x_257_; 
v___x_257_ = l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_swapLoop___at___00__private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_findExtIff_x3f_spec__1_spec__2___redArg(v_xs_254_, v_j_255_);
return v___x_257_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_findExtIff_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_258_, lean_object* v_keys_259_, lean_object* v_vals_260_, lean_object* v_heq_261_, lean_object* v_i_262_, lean_object* v_k_263_){
_start:
{
uint8_t v___x_264_; 
v___x_264_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_findExtIff_x3f_spec__0_spec__0_spec__1___redArg(v_keys_259_, v_i_262_, v_k_263_);
return v___x_264_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_findExtIff_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_265_, lean_object* v_keys_266_, lean_object* v_vals_267_, lean_object* v_heq_268_, lean_object* v_i_269_, lean_object* v_k_270_){
_start:
{
uint8_t v_res_271_; lean_object* v_r_272_; 
v_res_271_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_findExtIff_x3f_spec__0_spec__0_spec__1(v_00_u03b2_265_, v_keys_266_, v_vals_267_, v_heq_268_, v_i_269_, v_k_270_);
lean_dec(v_k_270_);
lean_dec_ref(v_vals_267_);
lean_dec_ref(v_keys_266_);
v_r_272_ = lean_box(v_res_271_);
return v_r_272_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2_spec__3(lean_object* v_msgData_273_, lean_object* v___y_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_){
_start:
{
lean_object* v___x_279_; lean_object* v_env_280_; lean_object* v___x_281_; lean_object* v_mctx_282_; lean_object* v_lctx_283_; lean_object* v_options_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; 
v___x_279_ = lean_st_ref_get(v___y_277_);
v_env_280_ = lean_ctor_get(v___x_279_, 0);
lean_inc_ref(v_env_280_);
lean_dec(v___x_279_);
v___x_281_ = lean_st_ref_get(v___y_275_);
v_mctx_282_ = lean_ctor_get(v___x_281_, 0);
lean_inc_ref(v_mctx_282_);
lean_dec(v___x_281_);
v_lctx_283_ = lean_ctor_get(v___y_274_, 2);
v_options_284_ = lean_ctor_get(v___y_276_, 2);
lean_inc_ref(v_options_284_);
lean_inc_ref(v_lctx_283_);
v___x_285_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_285_, 0, v_env_280_);
lean_ctor_set(v___x_285_, 1, v_mctx_282_);
lean_ctor_set(v___x_285_, 2, v_lctx_283_);
lean_ctor_set(v___x_285_, 3, v_options_284_);
v___x_286_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_286_, 0, v___x_285_);
lean_ctor_set(v___x_286_, 1, v_msgData_273_);
v___x_287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_287_, 0, v___x_286_);
return v___x_287_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2_spec__3___boxed(lean_object* v_msgData_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_){
_start:
{
lean_object* v_res_294_; 
v_res_294_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2_spec__3(v_msgData_288_, v___y_289_, v___y_290_, v___y_291_, v___y_292_);
lean_dec(v___y_292_);
lean_dec_ref(v___y_291_);
lean_dec(v___y_290_);
lean_dec_ref(v___y_289_);
return v_res_294_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__0_spec__0___redArg(lean_object* v_msg_295_, lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_){
_start:
{
lean_object* v_ref_301_; lean_object* v___x_302_; lean_object* v_a_303_; lean_object* v___x_305_; uint8_t v_isShared_306_; uint8_t v_isSharedCheck_311_; 
v_ref_301_ = lean_ctor_get(v___y_298_, 5);
v___x_302_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2_spec__3(v_msg_295_, v___y_296_, v___y_297_, v___y_298_, v___y_299_);
v_a_303_ = lean_ctor_get(v___x_302_, 0);
v_isSharedCheck_311_ = !lean_is_exclusive(v___x_302_);
if (v_isSharedCheck_311_ == 0)
{
v___x_305_ = v___x_302_;
v_isShared_306_ = v_isSharedCheck_311_;
goto v_resetjp_304_;
}
else
{
lean_inc(v_a_303_);
lean_dec(v___x_302_);
v___x_305_ = lean_box(0);
v_isShared_306_ = v_isSharedCheck_311_;
goto v_resetjp_304_;
}
v_resetjp_304_:
{
lean_object* v___x_307_; lean_object* v___x_309_; 
lean_inc(v_ref_301_);
v___x_307_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_307_, 0, v_ref_301_);
lean_ctor_set(v___x_307_, 1, v_a_303_);
if (v_isShared_306_ == 0)
{
lean_ctor_set_tag(v___x_305_, 1);
lean_ctor_set(v___x_305_, 0, v___x_307_);
v___x_309_ = v___x_305_;
goto v_reusejp_308_;
}
else
{
lean_object* v_reuseFailAlloc_310_; 
v_reuseFailAlloc_310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_310_, 0, v___x_307_);
v___x_309_ = v_reuseFailAlloc_310_;
goto v_reusejp_308_;
}
v_reusejp_308_:
{
return v___x_309_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__0_spec__0___redArg___boxed(lean_object* v_msg_312_, lean_object* v___y_313_, lean_object* v___y_314_, lean_object* v___y_315_, lean_object* v___y_316_, lean_object* v___y_317_){
_start:
{
lean_object* v_res_318_; 
v_res_318_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__0_spec__0___redArg(v_msg_312_, v___y_313_, v___y_314_, v___y_315_, v___y_316_);
lean_dec(v___y_316_);
lean_dec_ref(v___y_315_);
lean_dec(v___y_314_);
lean_dec_ref(v___y_313_);
return v_res_318_;
}
}
static lean_object* _init_l_Lean_getConstInfoInduct___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__0___closed__1(void){
_start:
{
lean_object* v___x_320_; lean_object* v___x_321_; 
v___x_320_ = ((lean_object*)(l_Lean_getConstInfoInduct___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__0___closed__0));
v___x_321_ = l_Lean_stringToMessageData(v___x_320_);
return v___x_321_;
}
}
static lean_object* _init_l_Lean_getConstInfoInduct___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__0___closed__3(void){
_start:
{
lean_object* v___x_323_; lean_object* v___x_324_; 
v___x_323_ = ((lean_object*)(l_Lean_getConstInfoInduct___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__0___closed__2));
v___x_324_ = l_Lean_stringToMessageData(v___x_323_);
return v___x_324_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__0(lean_object* v_constName_325_, lean_object* v___y_326_, lean_object* v___y_327_, lean_object* v___y_328_, lean_object* v___y_329_, lean_object* v___y_330_, lean_object* v___y_331_){
_start:
{
lean_object* v___x_333_; lean_object* v_env_334_; lean_object* v___x_335_; 
v___x_333_ = lean_st_ref_get(v___y_331_);
v_env_334_ = lean_ctor_get(v___x_333_, 0);
lean_inc_ref(v_env_334_);
lean_dec(v___x_333_);
lean_inc(v_constName_325_);
v___x_335_ = l_Lean_isInductiveCore_x3f(v_env_334_, v_constName_325_);
if (lean_obj_tag(v___x_335_) == 0)
{
lean_object* v___x_336_; uint8_t v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; 
v___x_336_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__0___closed__1, &l_Lean_getConstInfoInduct___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__0___closed__1_once, _init_l_Lean_getConstInfoInduct___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__0___closed__1);
v___x_337_ = 0;
v___x_338_ = l_Lean_MessageData_ofConstName(v_constName_325_, v___x_337_);
v___x_339_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_339_, 0, v___x_336_);
lean_ctor_set(v___x_339_, 1, v___x_338_);
v___x_340_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__0___closed__3, &l_Lean_getConstInfoInduct___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__0___closed__3_once, _init_l_Lean_getConstInfoInduct___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__0___closed__3);
v___x_341_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_341_, 0, v___x_339_);
lean_ctor_set(v___x_341_, 1, v___x_340_);
v___x_342_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__0_spec__0___redArg(v___x_341_, v___y_328_, v___y_329_, v___y_330_, v___y_331_);
return v___x_342_;
}
else
{
lean_object* v_val_343_; lean_object* v___x_345_; uint8_t v_isShared_346_; uint8_t v_isSharedCheck_350_; 
lean_dec(v_constName_325_);
v_val_343_ = lean_ctor_get(v___x_335_, 0);
v_isSharedCheck_350_ = !lean_is_exclusive(v___x_335_);
if (v_isSharedCheck_350_ == 0)
{
v___x_345_ = v___x_335_;
v_isShared_346_ = v_isSharedCheck_350_;
goto v_resetjp_344_;
}
else
{
lean_inc(v_val_343_);
lean_dec(v___x_335_);
v___x_345_ = lean_box(0);
v_isShared_346_ = v_isSharedCheck_350_;
goto v_resetjp_344_;
}
v_resetjp_344_:
{
lean_object* v___x_348_; 
if (v_isShared_346_ == 0)
{
lean_ctor_set_tag(v___x_345_, 0);
v___x_348_ = v___x_345_;
goto v_reusejp_347_;
}
else
{
lean_object* v_reuseFailAlloc_349_; 
v_reuseFailAlloc_349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_349_, 0, v_val_343_);
v___x_348_ = v_reuseFailAlloc_349_;
goto v_reusejp_347_;
}
v_reusejp_347_:
{
return v___x_348_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__0___boxed(lean_object* v_constName_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_){
_start:
{
lean_object* v_res_359_; 
v_res_359_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__0(v_constName_351_, v___y_352_, v___y_353_, v___y_354_, v___y_355_, v___y_356_, v___y_357_);
lean_dec(v___y_357_);
lean_dec_ref(v___y_356_);
lean_dec(v___y_355_);
lean_dec_ref(v___y_354_);
lean_dec(v___y_353_);
lean_dec_ref(v___y_352_);
return v_res_359_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___redArg(lean_object* v_upperBound_393_, lean_object* v_a_394_, lean_object* v___x_395_, lean_object* v_a_396_, lean_object* v_b_397_){
_start:
{
uint8_t v___x_399_; 
v___x_399_ = lean_nat_dec_lt(v_a_396_, v_upperBound_393_);
if (v___x_399_ == 0)
{
lean_object* v___x_400_; 
lean_dec(v_a_396_);
lean_dec(v___x_395_);
lean_dec(v_a_394_);
v___x_400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_400_, 0, v_b_397_);
return v___x_400_;
}
else
{
lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; uint8_t v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; 
v___x_401_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___redArg___closed__1));
v___x_402_ = lean_unsigned_to_nat(5u);
lean_inc_n(v_a_396_, 2);
lean_inc_n(v___x_395_, 2);
lean_inc_n(v_a_394_, 2);
v___x_403_ = l_Lean_Meta_Tactic_BVDecide_Normalize_mkApplyProjControlDiscrPath(v_a_394_, v___x_395_, v_a_396_, v___x_401_, v___x_402_);
v___x_404_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___redArg___closed__8));
v___x_405_ = 0;
v___x_406_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___redArg___closed__10));
v___x_407_ = l_Lean_Meta_Simp_Simprocs_addCore(v_b_397_, v___x_403_, v___x_404_, v___x_405_, v___x_406_);
v___x_408_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___redArg___closed__12));
v___x_409_ = lean_unsigned_to_nat(4u);
v___x_410_ = l_Lean_Meta_Tactic_BVDecide_Normalize_mkApplyProjControlDiscrPath(v_a_394_, v___x_395_, v_a_396_, v___x_408_, v___x_409_);
v___x_411_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___redArg___closed__14));
v___x_412_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___redArg___closed__16));
v___x_413_ = l_Lean_Meta_Simp_Simprocs_addCore(v___x_407_, v___x_410_, v___x_411_, v___x_405_, v___x_412_);
v___x_414_ = lean_unsigned_to_nat(1u);
v___x_415_ = lean_nat_add(v_a_396_, v___x_414_);
lean_dec(v_a_396_);
v_a_396_ = v___x_415_;
v_b_397_ = v___x_413_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___redArg___boxed(lean_object* v_upperBound_417_, lean_object* v_a_418_, lean_object* v___x_419_, lean_object* v_a_420_, lean_object* v_b_421_, lean_object* v___y_422_){
_start:
{
lean_object* v_res_423_; 
v_res_423_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___redArg(v_upperBound_417_, v_a_418_, v___x_419_, v_a_420_, v_b_421_);
lean_dec(v_upperBound_417_);
return v_res_423_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_424_; double v___x_425_; 
v___x_424_ = lean_unsigned_to_nat(0u);
v___x_425_ = lean_float_of_nat(v___x_424_);
return v___x_425_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg(lean_object* v_cls_429_, lean_object* v_msg_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_){
_start:
{
lean_object* v_ref_436_; lean_object* v___x_437_; lean_object* v_a_438_; lean_object* v___x_440_; uint8_t v_isShared_441_; uint8_t v_isSharedCheck_482_; 
v_ref_436_ = lean_ctor_get(v___y_433_, 5);
v___x_437_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2_spec__3(v_msg_430_, v___y_431_, v___y_432_, v___y_433_, v___y_434_);
v_a_438_ = lean_ctor_get(v___x_437_, 0);
v_isSharedCheck_482_ = !lean_is_exclusive(v___x_437_);
if (v_isSharedCheck_482_ == 0)
{
v___x_440_ = v___x_437_;
v_isShared_441_ = v_isSharedCheck_482_;
goto v_resetjp_439_;
}
else
{
lean_inc(v_a_438_);
lean_dec(v___x_437_);
v___x_440_ = lean_box(0);
v_isShared_441_ = v_isSharedCheck_482_;
goto v_resetjp_439_;
}
v_resetjp_439_:
{
lean_object* v___x_442_; lean_object* v_traceState_443_; lean_object* v_env_444_; lean_object* v_nextMacroScope_445_; lean_object* v_ngen_446_; lean_object* v_auxDeclNGen_447_; lean_object* v_cache_448_; lean_object* v_messages_449_; lean_object* v_infoState_450_; lean_object* v_snapshotTasks_451_; lean_object* v___x_453_; uint8_t v_isShared_454_; uint8_t v_isSharedCheck_481_; 
v___x_442_ = lean_st_ref_take(v___y_434_);
v_traceState_443_ = lean_ctor_get(v___x_442_, 4);
v_env_444_ = lean_ctor_get(v___x_442_, 0);
v_nextMacroScope_445_ = lean_ctor_get(v___x_442_, 1);
v_ngen_446_ = lean_ctor_get(v___x_442_, 2);
v_auxDeclNGen_447_ = lean_ctor_get(v___x_442_, 3);
v_cache_448_ = lean_ctor_get(v___x_442_, 5);
v_messages_449_ = lean_ctor_get(v___x_442_, 6);
v_infoState_450_ = lean_ctor_get(v___x_442_, 7);
v_snapshotTasks_451_ = lean_ctor_get(v___x_442_, 8);
v_isSharedCheck_481_ = !lean_is_exclusive(v___x_442_);
if (v_isSharedCheck_481_ == 0)
{
v___x_453_ = v___x_442_;
v_isShared_454_ = v_isSharedCheck_481_;
goto v_resetjp_452_;
}
else
{
lean_inc(v_snapshotTasks_451_);
lean_inc(v_infoState_450_);
lean_inc(v_messages_449_);
lean_inc(v_cache_448_);
lean_inc(v_traceState_443_);
lean_inc(v_auxDeclNGen_447_);
lean_inc(v_ngen_446_);
lean_inc(v_nextMacroScope_445_);
lean_inc(v_env_444_);
lean_dec(v___x_442_);
v___x_453_ = lean_box(0);
v_isShared_454_ = v_isSharedCheck_481_;
goto v_resetjp_452_;
}
v_resetjp_452_:
{
uint64_t v_tid_455_; lean_object* v_traces_456_; lean_object* v___x_458_; uint8_t v_isShared_459_; uint8_t v_isSharedCheck_480_; 
v_tid_455_ = lean_ctor_get_uint64(v_traceState_443_, sizeof(void*)*1);
v_traces_456_ = lean_ctor_get(v_traceState_443_, 0);
v_isSharedCheck_480_ = !lean_is_exclusive(v_traceState_443_);
if (v_isSharedCheck_480_ == 0)
{
v___x_458_ = v_traceState_443_;
v_isShared_459_ = v_isSharedCheck_480_;
goto v_resetjp_457_;
}
else
{
lean_inc(v_traces_456_);
lean_dec(v_traceState_443_);
v___x_458_ = lean_box(0);
v_isShared_459_ = v_isSharedCheck_480_;
goto v_resetjp_457_;
}
v_resetjp_457_:
{
lean_object* v___x_460_; double v___x_461_; uint8_t v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_470_; 
v___x_460_ = lean_box(0);
v___x_461_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__0);
v___x_462_ = 0;
v___x_463_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__1));
v___x_464_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_464_, 0, v_cls_429_);
lean_ctor_set(v___x_464_, 1, v___x_460_);
lean_ctor_set(v___x_464_, 2, v___x_463_);
lean_ctor_set_float(v___x_464_, sizeof(void*)*3, v___x_461_);
lean_ctor_set_float(v___x_464_, sizeof(void*)*3 + 8, v___x_461_);
lean_ctor_set_uint8(v___x_464_, sizeof(void*)*3 + 16, v___x_462_);
v___x_465_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__2));
v___x_466_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_466_, 0, v___x_464_);
lean_ctor_set(v___x_466_, 1, v_a_438_);
lean_ctor_set(v___x_466_, 2, v___x_465_);
lean_inc(v_ref_436_);
v___x_467_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_467_, 0, v_ref_436_);
lean_ctor_set(v___x_467_, 1, v___x_466_);
v___x_468_ = l_Lean_PersistentArray_push___redArg(v_traces_456_, v___x_467_);
if (v_isShared_459_ == 0)
{
lean_ctor_set(v___x_458_, 0, v___x_468_);
v___x_470_ = v___x_458_;
goto v_reusejp_469_;
}
else
{
lean_object* v_reuseFailAlloc_479_; 
v_reuseFailAlloc_479_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_479_, 0, v___x_468_);
lean_ctor_set_uint64(v_reuseFailAlloc_479_, sizeof(void*)*1, v_tid_455_);
v___x_470_ = v_reuseFailAlloc_479_;
goto v_reusejp_469_;
}
v_reusejp_469_:
{
lean_object* v___x_472_; 
if (v_isShared_454_ == 0)
{
lean_ctor_set(v___x_453_, 4, v___x_470_);
v___x_472_ = v___x_453_;
goto v_reusejp_471_;
}
else
{
lean_object* v_reuseFailAlloc_478_; 
v_reuseFailAlloc_478_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_478_, 0, v_env_444_);
lean_ctor_set(v_reuseFailAlloc_478_, 1, v_nextMacroScope_445_);
lean_ctor_set(v_reuseFailAlloc_478_, 2, v_ngen_446_);
lean_ctor_set(v_reuseFailAlloc_478_, 3, v_auxDeclNGen_447_);
lean_ctor_set(v_reuseFailAlloc_478_, 4, v___x_470_);
lean_ctor_set(v_reuseFailAlloc_478_, 5, v_cache_448_);
lean_ctor_set(v_reuseFailAlloc_478_, 6, v_messages_449_);
lean_ctor_set(v_reuseFailAlloc_478_, 7, v_infoState_450_);
lean_ctor_set(v_reuseFailAlloc_478_, 8, v_snapshotTasks_451_);
v___x_472_ = v_reuseFailAlloc_478_;
goto v_reusejp_471_;
}
v_reusejp_471_:
{
lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_476_; 
v___x_473_ = lean_st_ref_set(v___y_434_, v___x_472_);
v___x_474_ = lean_box(0);
if (v_isShared_441_ == 0)
{
lean_ctor_set(v___x_440_, 0, v___x_474_);
v___x_476_ = v___x_440_;
goto v_reusejp_475_;
}
else
{
lean_object* v_reuseFailAlloc_477_; 
v_reuseFailAlloc_477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_477_, 0, v___x_474_);
v___x_476_ = v_reuseFailAlloc_477_;
goto v_reusejp_475_;
}
v_reusejp_475_:
{
return v___x_476_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___boxed(lean_object* v_cls_483_, lean_object* v_msg_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_){
_start:
{
lean_object* v_res_490_; 
v_res_490_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg(v_cls_483_, v_msg_484_, v___y_485_, v___y_486_, v___y_487_, v___y_488_);
lean_dec(v___y_488_);
lean_dec_ref(v___y_487_);
lean_dec(v___y_486_);
lean_dec_ref(v___y_485_);
return v_res_490_;
}
}
static lean_object* _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__3___closed__4(void){
_start:
{
lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; 
v___x_499_ = ((lean_object*)(l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__3___closed__1));
v___x_500_ = ((lean_object*)(l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__3___closed__3));
v___x_501_ = l_Lean_Name_append(v___x_500_, v___x_499_);
return v___x_501_;
}
}
static lean_object* _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__3___closed__6(void){
_start:
{
lean_object* v___x_503_; lean_object* v___x_504_; 
v___x_503_ = ((lean_object*)(l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__3___closed__5));
v___x_504_ = l_Lean_stringToMessageData(v___x_503_);
return v___x_504_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__3(lean_object* v___x_505_, lean_object* v_a_506_, lean_object* v_a_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_){
_start:
{
if (lean_obj_tag(v_a_506_) == 0)
{
lean_object* v___x_515_; lean_object* v___x_516_; 
lean_dec_ref(v___x_505_);
v___x_515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_515_, 0, v_a_507_);
v___x_516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_516_, 0, v___x_515_);
return v___x_516_;
}
else
{
lean_object* v_key_517_; lean_object* v_tail_518_; lean_object* v___x_519_; 
v_key_517_ = lean_ctor_get(v_a_506_, 0);
lean_inc_n(v_key_517_, 2);
v_tail_518_ = lean_ctor_get(v_a_506_, 2);
lean_inc(v_tail_518_);
lean_dec_ref_known(v_a_506_, 3);
v___x_519_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__0(v_key_517_, v___y_508_, v___y_509_, v___y_510_, v___y_511_, v___y_512_, v___y_513_);
if (lean_obj_tag(v___x_519_) == 0)
{
lean_object* v_a_520_; lean_object* v___x_521_; 
v_a_520_ = lean_ctor_get(v___x_519_, 0);
lean_inc_n(v_a_520_, 2);
lean_dec_ref_known(v___x_519_, 1);
v___x_521_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_findExtIff_x3f(v_a_520_, v___y_510_, v___y_511_, v___y_512_, v___y_513_);
if (lean_obj_tag(v___x_521_) == 0)
{
lean_object* v_a_522_; lean_object* v_fst_523_; lean_object* v_snd_524_; lean_object* v___x_526_; uint8_t v_isShared_527_; uint8_t v_isSharedCheck_597_; 
v_a_522_ = lean_ctor_get(v___x_521_, 0);
lean_inc(v_a_522_);
lean_dec_ref_known(v___x_521_, 1);
v_fst_523_ = lean_ctor_get(v_a_507_, 0);
v_snd_524_ = lean_ctor_get(v_a_507_, 1);
v_isSharedCheck_597_ = !lean_is_exclusive(v_a_507_);
if (v_isSharedCheck_597_ == 0)
{
v___x_526_ = v_a_507_;
v_isShared_527_ = v_isSharedCheck_597_;
goto v_resetjp_525_;
}
else
{
lean_inc(v_snd_524_);
lean_inc(v_fst_523_);
lean_dec(v_a_507_);
v___x_526_ = lean_box(0);
v_isShared_527_ = v_isSharedCheck_597_;
goto v_resetjp_525_;
}
v_resetjp_525_:
{
lean_object* v_theorems_529_; lean_object* v___y_530_; lean_object* v___y_531_; lean_object* v___y_532_; lean_object* v___y_533_; lean_object* v___y_534_; lean_object* v___y_535_; 
if (lean_obj_tag(v_a_522_) == 1)
{
lean_object* v_val_555_; lean_object* v___y_557_; lean_object* v___y_558_; lean_object* v___y_559_; lean_object* v___y_560_; lean_object* v___y_561_; lean_object* v___y_562_; lean_object* v_options_579_; uint8_t v_hasTrace_580_; 
v_val_555_ = lean_ctor_get(v_a_522_, 0);
lean_inc(v_val_555_);
lean_dec_ref_known(v_a_522_, 1);
v_options_579_ = lean_ctor_get(v___y_512_, 2);
v_hasTrace_580_ = lean_ctor_get_uint8(v_options_579_, sizeof(void*)*1);
if (v_hasTrace_580_ == 0)
{
v___y_557_ = v___y_508_;
v___y_558_ = v___y_509_;
v___y_559_ = v___y_510_;
v___y_560_ = v___y_511_;
v___y_561_ = v___y_512_;
v___y_562_ = v___y_513_;
goto v___jp_556_;
}
else
{
lean_object* v_inheritedTraceOptions_581_; lean_object* v___x_582_; lean_object* v___x_583_; uint8_t v___x_584_; 
v_inheritedTraceOptions_581_ = lean_ctor_get(v___y_512_, 13);
v___x_582_ = ((lean_object*)(l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__3___closed__1));
v___x_583_ = lean_obj_once(&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__3___closed__4, &l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__3___closed__4_once, _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__3___closed__4);
v___x_584_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_581_, v_options_579_, v___x_583_);
if (v___x_584_ == 0)
{
v___y_557_ = v___y_508_;
v___y_558_ = v___y_509_;
v___y_559_ = v___y_510_;
v___y_560_ = v___y_511_;
v___y_561_ = v___y_512_;
v___y_562_ = v___y_513_;
goto v___jp_556_;
}
else
{
lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; 
v___x_585_ = lean_obj_once(&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__3___closed__6, &l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__3___closed__6_once, _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__3___closed__6);
lean_inc(v_val_555_);
v___x_586_ = l_Lean_MessageData_ofName(v_val_555_);
v___x_587_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_587_, 0, v___x_585_);
lean_ctor_set(v___x_587_, 1, v___x_586_);
v___x_588_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg(v___x_582_, v___x_587_, v___y_510_, v___y_511_, v___y_512_, v___y_513_);
if (lean_obj_tag(v___x_588_) == 0)
{
lean_dec_ref_known(v___x_588_, 1);
v___y_557_ = v___y_508_;
v___y_558_ = v___y_509_;
v___y_559_ = v___y_510_;
v___y_560_ = v___y_511_;
v___y_561_ = v___y_512_;
v___y_562_ = v___y_513_;
goto v___jp_556_;
}
else
{
lean_object* v_a_589_; lean_object* v___x_591_; uint8_t v_isShared_592_; uint8_t v_isSharedCheck_596_; 
lean_dec(v_val_555_);
lean_del_object(v___x_526_);
lean_dec(v_snd_524_);
lean_dec(v_fst_523_);
lean_dec(v_a_520_);
lean_dec(v_tail_518_);
lean_dec(v_key_517_);
lean_dec_ref(v___x_505_);
v_a_589_ = lean_ctor_get(v___x_588_, 0);
v_isSharedCheck_596_ = !lean_is_exclusive(v___x_588_);
if (v_isSharedCheck_596_ == 0)
{
v___x_591_ = v___x_588_;
v_isShared_592_ = v_isSharedCheck_596_;
goto v_resetjp_590_;
}
else
{
lean_inc(v_a_589_);
lean_dec(v___x_588_);
v___x_591_ = lean_box(0);
v_isShared_592_ = v_isSharedCheck_596_;
goto v_resetjp_590_;
}
v_resetjp_590_:
{
lean_object* v___x_594_; 
if (v_isShared_592_ == 0)
{
v___x_594_ = v___x_591_;
goto v_reusejp_593_;
}
else
{
lean_object* v_reuseFailAlloc_595_; 
v_reuseFailAlloc_595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_595_, 0, v_a_589_);
v___x_594_ = v_reuseFailAlloc_595_;
goto v_reusejp_593_;
}
v_reusejp_593_:
{
return v___x_594_;
}
}
}
}
}
v___jp_556_:
{
uint8_t v___x_563_; uint8_t v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; 
v___x_563_ = 1;
v___x_564_ = 0;
lean_inc(v_val_555_);
v___x_565_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_565_, 0, v_val_555_);
lean_ctor_set_uint8(v___x_565_, sizeof(void*)*1, v___x_563_);
lean_ctor_set_uint8(v___x_565_, sizeof(void*)*1 + 1, v___x_564_);
v___x_566_ = lean_box(0);
v___x_567_ = l_Lean_mkConst(v_val_555_, v___x_566_);
v___x_568_ = l_Lean_Meta_simpGlobalConfig;
v___x_569_ = l_Lean_Meta_SimpTheoremsArray_addTheorem(v_snd_524_, v___x_565_, v___x_567_, v___x_568_, v___y_559_, v___y_560_, v___y_561_, v___y_562_);
if (lean_obj_tag(v___x_569_) == 0)
{
lean_object* v_a_570_; 
v_a_570_ = lean_ctor_get(v___x_569_, 0);
lean_inc(v_a_570_);
lean_dec_ref_known(v___x_569_, 1);
v_theorems_529_ = v_a_570_;
v___y_530_ = v___y_557_;
v___y_531_ = v___y_558_;
v___y_532_ = v___y_559_;
v___y_533_ = v___y_560_;
v___y_534_ = v___y_561_;
v___y_535_ = v___y_562_;
goto v___jp_528_;
}
else
{
lean_object* v_a_571_; lean_object* v___x_573_; uint8_t v_isShared_574_; uint8_t v_isSharedCheck_578_; 
lean_del_object(v___x_526_);
lean_dec(v_fst_523_);
lean_dec(v_a_520_);
lean_dec(v_tail_518_);
lean_dec(v_key_517_);
lean_dec_ref(v___x_505_);
v_a_571_ = lean_ctor_get(v___x_569_, 0);
v_isSharedCheck_578_ = !lean_is_exclusive(v___x_569_);
if (v_isSharedCheck_578_ == 0)
{
v___x_573_ = v___x_569_;
v_isShared_574_ = v_isSharedCheck_578_;
goto v_resetjp_572_;
}
else
{
lean_inc(v_a_571_);
lean_dec(v___x_569_);
v___x_573_ = lean_box(0);
v_isShared_574_ = v_isSharedCheck_578_;
goto v_resetjp_572_;
}
v_resetjp_572_:
{
lean_object* v___x_576_; 
if (v_isShared_574_ == 0)
{
v___x_576_ = v___x_573_;
goto v_reusejp_575_;
}
else
{
lean_object* v_reuseFailAlloc_577_; 
v_reuseFailAlloc_577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_577_, 0, v_a_571_);
v___x_576_ = v_reuseFailAlloc_577_;
goto v_reusejp_575_;
}
v_reusejp_575_:
{
return v___x_576_;
}
}
}
}
}
else
{
lean_dec(v_a_522_);
v_theorems_529_ = v_snd_524_;
v___y_530_ = v___y_508_;
v___y_531_ = v___y_509_;
v___y_532_ = v___y_510_;
v___y_533_ = v___y_511_;
v___y_534_ = v___y_512_;
v___y_535_ = v___y_513_;
goto v___jp_528_;
}
v___jp_528_:
{
lean_object* v___x_536_; lean_object* v_fieldNames_537_; lean_object* v_numParams_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; 
lean_inc(v_key_517_);
lean_inc_ref(v___x_505_);
v___x_536_ = l_Lean_getStructureInfo(v___x_505_, v_key_517_);
v_fieldNames_537_ = lean_ctor_get(v___x_536_, 1);
lean_inc_ref(v_fieldNames_537_);
lean_dec_ref(v___x_536_);
v_numParams_538_ = lean_ctor_get(v_a_520_, 1);
lean_inc(v_numParams_538_);
lean_dec(v_a_520_);
v___x_539_ = lean_array_get_size(v_fieldNames_537_);
lean_dec_ref(v_fieldNames_537_);
v___x_540_ = lean_unsigned_to_nat(0u);
v___x_541_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___redArg(v___x_539_, v_key_517_, v_numParams_538_, v___x_540_, v_fst_523_);
if (lean_obj_tag(v___x_541_) == 0)
{
lean_object* v_a_542_; lean_object* v___x_544_; 
v_a_542_ = lean_ctor_get(v___x_541_, 0);
lean_inc(v_a_542_);
lean_dec_ref_known(v___x_541_, 1);
if (v_isShared_527_ == 0)
{
lean_ctor_set(v___x_526_, 1, v_theorems_529_);
lean_ctor_set(v___x_526_, 0, v_a_542_);
v___x_544_ = v___x_526_;
goto v_reusejp_543_;
}
else
{
lean_object* v_reuseFailAlloc_546_; 
v_reuseFailAlloc_546_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_546_, 0, v_a_542_);
lean_ctor_set(v_reuseFailAlloc_546_, 1, v_theorems_529_);
v___x_544_ = v_reuseFailAlloc_546_;
goto v_reusejp_543_;
}
v_reusejp_543_:
{
v_a_506_ = v_tail_518_;
v_a_507_ = v___x_544_;
goto _start;
}
}
else
{
lean_object* v_a_547_; lean_object* v___x_549_; uint8_t v_isShared_550_; uint8_t v_isSharedCheck_554_; 
lean_dec_ref(v_theorems_529_);
lean_del_object(v___x_526_);
lean_dec(v_tail_518_);
lean_dec_ref(v___x_505_);
v_a_547_ = lean_ctor_get(v___x_541_, 0);
v_isSharedCheck_554_ = !lean_is_exclusive(v___x_541_);
if (v_isSharedCheck_554_ == 0)
{
v___x_549_ = v___x_541_;
v_isShared_550_ = v_isSharedCheck_554_;
goto v_resetjp_548_;
}
else
{
lean_inc(v_a_547_);
lean_dec(v___x_541_);
v___x_549_ = lean_box(0);
v_isShared_550_ = v_isSharedCheck_554_;
goto v_resetjp_548_;
}
v_resetjp_548_:
{
lean_object* v___x_552_; 
if (v_isShared_550_ == 0)
{
v___x_552_ = v___x_549_;
goto v_reusejp_551_;
}
else
{
lean_object* v_reuseFailAlloc_553_; 
v_reuseFailAlloc_553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_553_, 0, v_a_547_);
v___x_552_ = v_reuseFailAlloc_553_;
goto v_reusejp_551_;
}
v_reusejp_551_:
{
return v___x_552_;
}
}
}
}
}
}
else
{
lean_object* v_a_598_; lean_object* v___x_600_; uint8_t v_isShared_601_; uint8_t v_isSharedCheck_605_; 
lean_dec(v_a_520_);
lean_dec(v_tail_518_);
lean_dec(v_key_517_);
lean_dec_ref(v_a_507_);
lean_dec_ref(v___x_505_);
v_a_598_ = lean_ctor_get(v___x_521_, 0);
v_isSharedCheck_605_ = !lean_is_exclusive(v___x_521_);
if (v_isSharedCheck_605_ == 0)
{
v___x_600_ = v___x_521_;
v_isShared_601_ = v_isSharedCheck_605_;
goto v_resetjp_599_;
}
else
{
lean_inc(v_a_598_);
lean_dec(v___x_521_);
v___x_600_ = lean_box(0);
v_isShared_601_ = v_isSharedCheck_605_;
goto v_resetjp_599_;
}
v_resetjp_599_:
{
lean_object* v___x_603_; 
if (v_isShared_601_ == 0)
{
v___x_603_ = v___x_600_;
goto v_reusejp_602_;
}
else
{
lean_object* v_reuseFailAlloc_604_; 
v_reuseFailAlloc_604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_604_, 0, v_a_598_);
v___x_603_ = v_reuseFailAlloc_604_;
goto v_reusejp_602_;
}
v_reusejp_602_:
{
return v___x_603_;
}
}
}
}
else
{
lean_object* v_a_606_; lean_object* v___x_608_; uint8_t v_isShared_609_; uint8_t v_isSharedCheck_613_; 
lean_dec(v_tail_518_);
lean_dec(v_key_517_);
lean_dec_ref(v_a_507_);
lean_dec_ref(v___x_505_);
v_a_606_ = lean_ctor_get(v___x_519_, 0);
v_isSharedCheck_613_ = !lean_is_exclusive(v___x_519_);
if (v_isSharedCheck_613_ == 0)
{
v___x_608_ = v___x_519_;
v_isShared_609_ = v_isSharedCheck_613_;
goto v_resetjp_607_;
}
else
{
lean_inc(v_a_606_);
lean_dec(v___x_519_);
v___x_608_ = lean_box(0);
v_isShared_609_ = v_isSharedCheck_613_;
goto v_resetjp_607_;
}
v_resetjp_607_:
{
lean_object* v___x_611_; 
if (v_isShared_609_ == 0)
{
v___x_611_ = v___x_608_;
goto v_reusejp_610_;
}
else
{
lean_object* v_reuseFailAlloc_612_; 
v_reuseFailAlloc_612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_612_, 0, v_a_606_);
v___x_611_ = v_reuseFailAlloc_612_;
goto v_reusejp_610_;
}
v_reusejp_610_:
{
return v___x_611_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__3___boxed(lean_object* v___x_614_, lean_object* v_a_615_, lean_object* v_a_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_){
_start:
{
lean_object* v_res_624_; 
v_res_624_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__3(v___x_614_, v_a_615_, v_a_616_, v___y_617_, v___y_618_, v___y_619_, v___y_620_, v___y_621_, v___y_622_);
lean_dec(v___y_622_);
lean_dec_ref(v___y_621_);
lean_dec(v___y_620_);
lean_dec_ref(v___y_619_);
lean_dec(v___y_618_);
lean_dec_ref(v___y_617_);
return v_res_624_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__4(lean_object* v___x_625_, lean_object* v_as_626_, size_t v_sz_627_, size_t v_i_628_, lean_object* v_b_629_, lean_object* v___y_630_, lean_object* v___y_631_, lean_object* v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_){
_start:
{
uint8_t v___x_637_; 
v___x_637_ = lean_usize_dec_lt(v_i_628_, v_sz_627_);
if (v___x_637_ == 0)
{
lean_object* v___x_638_; 
lean_dec_ref(v___x_625_);
v___x_638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_638_, 0, v_b_629_);
return v___x_638_;
}
else
{
lean_object* v_a_639_; lean_object* v___x_640_; 
v_a_639_ = lean_array_uget_borrowed(v_as_626_, v_i_628_);
lean_inc(v_a_639_);
lean_inc_ref(v___x_625_);
v___x_640_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__3(v___x_625_, v_a_639_, v_b_629_, v___y_630_, v___y_631_, v___y_632_, v___y_633_, v___y_634_, v___y_635_);
if (lean_obj_tag(v___x_640_) == 0)
{
lean_object* v_a_641_; lean_object* v___x_643_; uint8_t v_isShared_644_; uint8_t v_isSharedCheck_653_; 
v_a_641_ = lean_ctor_get(v___x_640_, 0);
v_isSharedCheck_653_ = !lean_is_exclusive(v___x_640_);
if (v_isSharedCheck_653_ == 0)
{
v___x_643_ = v___x_640_;
v_isShared_644_ = v_isSharedCheck_653_;
goto v_resetjp_642_;
}
else
{
lean_inc(v_a_641_);
lean_dec(v___x_640_);
v___x_643_ = lean_box(0);
v_isShared_644_ = v_isSharedCheck_653_;
goto v_resetjp_642_;
}
v_resetjp_642_:
{
if (lean_obj_tag(v_a_641_) == 0)
{
lean_object* v_a_645_; lean_object* v___x_647_; 
lean_dec_ref(v___x_625_);
v_a_645_ = lean_ctor_get(v_a_641_, 0);
lean_inc(v_a_645_);
lean_dec_ref_known(v_a_641_, 1);
if (v_isShared_644_ == 0)
{
lean_ctor_set(v___x_643_, 0, v_a_645_);
v___x_647_ = v___x_643_;
goto v_reusejp_646_;
}
else
{
lean_object* v_reuseFailAlloc_648_; 
v_reuseFailAlloc_648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_648_, 0, v_a_645_);
v___x_647_ = v_reuseFailAlloc_648_;
goto v_reusejp_646_;
}
v_reusejp_646_:
{
return v___x_647_;
}
}
else
{
lean_object* v_a_649_; size_t v___x_650_; size_t v___x_651_; 
lean_del_object(v___x_643_);
v_a_649_ = lean_ctor_get(v_a_641_, 0);
lean_inc(v_a_649_);
lean_dec_ref_known(v_a_641_, 1);
v___x_650_ = ((size_t)1ULL);
v___x_651_ = lean_usize_add(v_i_628_, v___x_650_);
v_i_628_ = v___x_651_;
v_b_629_ = v_a_649_;
goto _start;
}
}
}
else
{
lean_object* v_a_654_; lean_object* v___x_656_; uint8_t v_isShared_657_; uint8_t v_isSharedCheck_661_; 
lean_dec_ref(v___x_625_);
v_a_654_ = lean_ctor_get(v___x_640_, 0);
v_isSharedCheck_661_ = !lean_is_exclusive(v___x_640_);
if (v_isSharedCheck_661_ == 0)
{
v___x_656_ = v___x_640_;
v_isShared_657_ = v_isSharedCheck_661_;
goto v_resetjp_655_;
}
else
{
lean_inc(v_a_654_);
lean_dec(v___x_640_);
v___x_656_ = lean_box(0);
v_isShared_657_ = v_isSharedCheck_661_;
goto v_resetjp_655_;
}
v_resetjp_655_:
{
lean_object* v___x_659_; 
if (v_isShared_657_ == 0)
{
v___x_659_ = v___x_656_;
goto v_reusejp_658_;
}
else
{
lean_object* v_reuseFailAlloc_660_; 
v_reuseFailAlloc_660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_660_, 0, v_a_654_);
v___x_659_ = v_reuseFailAlloc_660_;
goto v_reusejp_658_;
}
v_reusejp_658_:
{
return v___x_659_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__4___boxed(lean_object* v___x_662_, lean_object* v_as_663_, lean_object* v_sz_664_, lean_object* v_i_665_, lean_object* v_b_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_){
_start:
{
size_t v_sz_boxed_674_; size_t v_i_boxed_675_; lean_object* v_res_676_; 
v_sz_boxed_674_ = lean_unbox_usize(v_sz_664_);
lean_dec(v_sz_664_);
v_i_boxed_675_ = lean_unbox_usize(v_i_665_);
lean_dec(v_i_665_);
v_res_676_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__4(v___x_662_, v_as_663_, v_sz_boxed_674_, v_i_boxed_675_, v_b_666_, v___y_667_, v___y_668_, v___y_669_, v___y_670_, v___y_671_, v___y_672_);
lean_dec(v___y_672_);
lean_dec_ref(v___y_671_);
lean_dec(v___y_670_);
lean_dec_ref(v___y_669_);
lean_dec(v___y_668_);
lean_dec_ref(v___y_667_);
lean_dec_ref(v_as_663_);
return v_res_676_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas(lean_object* v_simprocs_677_, lean_object* v_theorems_678_, lean_object* v_a_679_, lean_object* v_a_680_, lean_object* v_a_681_, lean_object* v_a_682_, lean_object* v_a_683_, lean_object* v_a_684_){
_start:
{
lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v_typeAnalysis_688_; lean_object* v_interestingStructures_689_; lean_object* v_env_690_; lean_object* v_buckets_691_; lean_object* v___x_693_; uint8_t v_isShared_694_; uint8_t v_isSharedCheck_718_; 
v___x_686_ = lean_st_ref_get(v_a_680_);
v___x_687_ = lean_st_ref_get(v_a_684_);
v_typeAnalysis_688_ = lean_ctor_get(v___x_686_, 2);
lean_inc_ref(v_typeAnalysis_688_);
lean_dec(v___x_686_);
v_interestingStructures_689_ = lean_ctor_get(v_typeAnalysis_688_, 0);
lean_inc_ref(v_interestingStructures_689_);
lean_dec_ref(v_typeAnalysis_688_);
v_env_690_ = lean_ctor_get(v___x_687_, 0);
lean_inc_ref(v_env_690_);
lean_dec(v___x_687_);
v_buckets_691_ = lean_ctor_get(v_interestingStructures_689_, 1);
v_isSharedCheck_718_ = !lean_is_exclusive(v_interestingStructures_689_);
if (v_isSharedCheck_718_ == 0)
{
lean_object* v_unused_719_; 
v_unused_719_ = lean_ctor_get(v_interestingStructures_689_, 0);
lean_dec(v_unused_719_);
v___x_693_ = v_interestingStructures_689_;
v_isShared_694_ = v_isSharedCheck_718_;
goto v_resetjp_692_;
}
else
{
lean_inc(v_buckets_691_);
lean_dec(v_interestingStructures_689_);
v___x_693_ = lean_box(0);
v_isShared_694_ = v_isSharedCheck_718_;
goto v_resetjp_692_;
}
v_resetjp_692_:
{
lean_object* v___x_696_; 
if (v_isShared_694_ == 0)
{
lean_ctor_set(v___x_693_, 1, v_theorems_678_);
lean_ctor_set(v___x_693_, 0, v_simprocs_677_);
v___x_696_ = v___x_693_;
goto v_reusejp_695_;
}
else
{
lean_object* v_reuseFailAlloc_717_; 
v_reuseFailAlloc_717_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_717_, 0, v_simprocs_677_);
lean_ctor_set(v_reuseFailAlloc_717_, 1, v_theorems_678_);
v___x_696_ = v_reuseFailAlloc_717_;
goto v_reusejp_695_;
}
v_reusejp_695_:
{
size_t v_sz_697_; size_t v___x_698_; lean_object* v___x_699_; 
v_sz_697_ = lean_array_size(v_buckets_691_);
v___x_698_ = ((size_t)0ULL);
v___x_699_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__4(v_env_690_, v_buckets_691_, v_sz_697_, v___x_698_, v___x_696_, v_a_679_, v_a_680_, v_a_681_, v_a_682_, v_a_683_, v_a_684_);
lean_dec_ref(v_buckets_691_);
if (lean_obj_tag(v___x_699_) == 0)
{
lean_object* v_a_700_; lean_object* v___x_702_; uint8_t v_isShared_703_; uint8_t v_isSharedCheck_716_; 
v_a_700_ = lean_ctor_get(v___x_699_, 0);
v_isSharedCheck_716_ = !lean_is_exclusive(v___x_699_);
if (v_isSharedCheck_716_ == 0)
{
v___x_702_ = v___x_699_;
v_isShared_703_ = v_isSharedCheck_716_;
goto v_resetjp_701_;
}
else
{
lean_inc(v_a_700_);
lean_dec(v___x_699_);
v___x_702_ = lean_box(0);
v_isShared_703_ = v_isSharedCheck_716_;
goto v_resetjp_701_;
}
v_resetjp_701_:
{
lean_object* v_fst_704_; lean_object* v_snd_705_; lean_object* v___x_707_; uint8_t v_isShared_708_; uint8_t v_isSharedCheck_715_; 
v_fst_704_ = lean_ctor_get(v_a_700_, 0);
v_snd_705_ = lean_ctor_get(v_a_700_, 1);
v_isSharedCheck_715_ = !lean_is_exclusive(v_a_700_);
if (v_isSharedCheck_715_ == 0)
{
v___x_707_ = v_a_700_;
v_isShared_708_ = v_isSharedCheck_715_;
goto v_resetjp_706_;
}
else
{
lean_inc(v_snd_705_);
lean_inc(v_fst_704_);
lean_dec(v_a_700_);
v___x_707_ = lean_box(0);
v_isShared_708_ = v_isSharedCheck_715_;
goto v_resetjp_706_;
}
v_resetjp_706_:
{
lean_object* v___x_710_; 
if (v_isShared_708_ == 0)
{
v___x_710_ = v___x_707_;
goto v_reusejp_709_;
}
else
{
lean_object* v_reuseFailAlloc_714_; 
v_reuseFailAlloc_714_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_714_, 0, v_fst_704_);
lean_ctor_set(v_reuseFailAlloc_714_, 1, v_snd_705_);
v___x_710_ = v_reuseFailAlloc_714_;
goto v_reusejp_709_;
}
v_reusejp_709_:
{
lean_object* v___x_712_; 
if (v_isShared_703_ == 0)
{
lean_ctor_set(v___x_702_, 0, v___x_710_);
v___x_712_ = v___x_702_;
goto v_reusejp_711_;
}
else
{
lean_object* v_reuseFailAlloc_713_; 
v_reuseFailAlloc_713_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_713_, 0, v___x_710_);
v___x_712_ = v_reuseFailAlloc_713_;
goto v_reusejp_711_;
}
v_reusejp_711_:
{
return v___x_712_;
}
}
}
}
}
else
{
return v___x_699_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas___boxed(lean_object* v_simprocs_720_, lean_object* v_theorems_721_, lean_object* v_a_722_, lean_object* v_a_723_, lean_object* v_a_724_, lean_object* v_a_725_, lean_object* v_a_726_, lean_object* v_a_727_, lean_object* v_a_728_){
_start:
{
lean_object* v_res_729_; 
v_res_729_ = l_Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas(v_simprocs_720_, v_theorems_721_, v_a_722_, v_a_723_, v_a_724_, v_a_725_, v_a_726_, v_a_727_);
lean_dec(v_a_727_);
lean_dec_ref(v_a_726_);
lean_dec(v_a_725_);
lean_dec_ref(v_a_724_);
lean_dec(v_a_723_);
lean_dec_ref(v_a_722_);
return v_res_729_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1(lean_object* v_upperBound_730_, lean_object* v_a_731_, lean_object* v___x_732_, lean_object* v_inst_733_, lean_object* v_R_734_, lean_object* v_a_735_, lean_object* v_b_736_, lean_object* v_c_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_){
_start:
{
lean_object* v___x_745_; 
v___x_745_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___redArg(v_upperBound_730_, v_a_731_, v___x_732_, v_a_735_, v_b_736_);
return v___x_745_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___boxed(lean_object* v_upperBound_746_, lean_object* v_a_747_, lean_object* v___x_748_, lean_object* v_inst_749_, lean_object* v_R_750_, lean_object* v_a_751_, lean_object* v_b_752_, lean_object* v_c_753_, lean_object* v___y_754_, lean_object* v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_, lean_object* v___y_758_, lean_object* v___y_759_, lean_object* v___y_760_){
_start:
{
lean_object* v_res_761_; 
v_res_761_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1(v_upperBound_746_, v_a_747_, v___x_748_, v_inst_749_, v_R_750_, v_a_751_, v_b_752_, v_c_753_, v___y_754_, v___y_755_, v___y_756_, v___y_757_, v___y_758_, v___y_759_);
lean_dec(v___y_759_);
lean_dec_ref(v___y_758_);
lean_dec(v___y_757_);
lean_dec_ref(v___y_756_);
lean_dec(v___y_755_);
lean_dec_ref(v___y_754_);
lean_dec(v_upperBound_746_);
return v_res_761_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2(lean_object* v_cls_762_, lean_object* v_msg_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_){
_start:
{
lean_object* v___x_771_; 
v___x_771_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg(v_cls_762_, v_msg_763_, v___y_766_, v___y_767_, v___y_768_, v___y_769_);
return v___x_771_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___boxed(lean_object* v_cls_772_, lean_object* v_msg_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_, lean_object* v___y_780_){
_start:
{
lean_object* v_res_781_; 
v_res_781_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2(v_cls_772_, v_msg_773_, v___y_774_, v___y_775_, v___y_776_, v___y_777_, v___y_778_, v___y_779_);
lean_dec(v___y_779_);
lean_dec_ref(v___y_778_);
lean_dec(v___y_777_);
lean_dec_ref(v___y_776_);
lean_dec(v___y_775_);
lean_dec_ref(v___y_774_);
return v_res_781_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__0_spec__0(lean_object* v_00_u03b1_782_, lean_object* v_msg_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_){
_start:
{
lean_object* v___x_791_; 
v___x_791_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__0_spec__0___redArg(v_msg_783_, v___y_786_, v___y_787_, v___y_788_, v___y_789_);
return v___x_791_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__0_spec__0___boxed(lean_object* v_00_u03b1_792_, lean_object* v_msg_793_, lean_object* v___y_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_){
_start:
{
lean_object* v_res_801_; 
v_res_801_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__0_spec__0(v_00_u03b1_792_, v_msg_793_, v___y_794_, v___y_795_, v___y_796_, v___y_797_, v___y_798_, v___y_799_);
lean_dec(v___y_799_);
lean_dec_ref(v___y_798_);
lean_dec(v___y_797_);
lean_dec_ref(v___y_796_);
lean_dec(v___y_795_);
lean_dec_ref(v___y_794_);
return v_res_801_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess_spec__0___closed__0(void){
_start:
{
lean_object* v___x_802_; 
v___x_802_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_802_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess_spec__0___closed__1(void){
_start:
{
lean_object* v___x_803_; lean_object* v___x_804_; 
v___x_803_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess_spec__0___closed__0, &l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess_spec__0___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess_spec__0___closed__0);
v___x_804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_804_, 0, v___x_803_);
return v___x_804_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess_spec__0(lean_object* v_00_u03b2_805_){
_start:
{
lean_object* v___x_806_; 
v___x_806_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess_spec__0___closed__1, &l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess_spec__0___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess_spec__0___closed__1);
return v___x_806_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess_spec__1___redArg___lam__0(lean_object* v_x_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_){
_start:
{
lean_object* v___x_815_; 
lean_inc(v___y_809_);
lean_inc_ref(v___y_808_);
v___x_815_ = lean_apply_7(v_x_807_, v___y_808_, v___y_809_, v___y_810_, v___y_811_, v___y_812_, v___y_813_, lean_box(0));
return v___x_815_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess_spec__1___redArg___lam__0___boxed(lean_object* v_x_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_, lean_object* v___y_823_){
_start:
{
lean_object* v_res_824_; 
v_res_824_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess_spec__1___redArg___lam__0(v_x_816_, v___y_817_, v___y_818_, v___y_819_, v___y_820_, v___y_821_, v___y_822_);
lean_dec(v___y_818_);
lean_dec_ref(v___y_817_);
return v_res_824_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess_spec__1___redArg(lean_object* v_mvarId_825_, lean_object* v_x_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_){
_start:
{
lean_object* v___f_834_; lean_object* v___x_835_; 
lean_inc(v___y_828_);
lean_inc_ref(v___y_827_);
v___f_834_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess_spec__1___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_834_, 0, v_x_826_);
lean_closure_set(v___f_834_, 1, v___y_827_);
lean_closure_set(v___f_834_, 2, v___y_828_);
v___x_835_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_825_, v___f_834_, v___y_829_, v___y_830_, v___y_831_, v___y_832_);
if (lean_obj_tag(v___x_835_) == 0)
{
return v___x_835_;
}
else
{
lean_object* v_a_836_; lean_object* v___x_838_; uint8_t v_isShared_839_; uint8_t v_isSharedCheck_843_; 
v_a_836_ = lean_ctor_get(v___x_835_, 0);
v_isSharedCheck_843_ = !lean_is_exclusive(v___x_835_);
if (v_isSharedCheck_843_ == 0)
{
v___x_838_ = v___x_835_;
v_isShared_839_ = v_isSharedCheck_843_;
goto v_resetjp_837_;
}
else
{
lean_inc(v_a_836_);
lean_dec(v___x_835_);
v___x_838_ = lean_box(0);
v_isShared_839_ = v_isSharedCheck_843_;
goto v_resetjp_837_;
}
v_resetjp_837_:
{
lean_object* v___x_841_; 
if (v_isShared_839_ == 0)
{
v___x_841_ = v___x_838_;
goto v_reusejp_840_;
}
else
{
lean_object* v_reuseFailAlloc_842_; 
v_reuseFailAlloc_842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_842_, 0, v_a_836_);
v___x_841_ = v_reuseFailAlloc_842_;
goto v_reusejp_840_;
}
v_reusejp_840_:
{
return v___x_841_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess_spec__1___redArg___boxed(lean_object* v_mvarId_844_, lean_object* v_x_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_){
_start:
{
lean_object* v_res_853_; 
v_res_853_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess_spec__1___redArg(v_mvarId_844_, v_x_845_, v___y_846_, v___y_847_, v___y_848_, v___y_849_, v___y_850_, v___y_851_);
lean_dec(v___y_851_);
lean_dec_ref(v___y_850_);
lean_dec(v___y_849_);
lean_dec_ref(v___y_848_);
lean_dec(v___y_847_);
lean_dec_ref(v___y_846_);
return v_res_853_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess_spec__1(lean_object* v_00_u03b1_854_, lean_object* v_mvarId_855_, lean_object* v_x_856_, lean_object* v___y_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_){
_start:
{
lean_object* v___x_864_; 
v___x_864_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess_spec__1___redArg(v_mvarId_855_, v_x_856_, v___y_857_, v___y_858_, v___y_859_, v___y_860_, v___y_861_, v___y_862_);
return v___x_864_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess_spec__1___boxed(lean_object* v_00_u03b1_865_, lean_object* v_mvarId_866_, lean_object* v_x_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_){
_start:
{
lean_object* v_res_875_; 
v_res_875_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess_spec__1(v_00_u03b1_865_, v_mvarId_866_, v_x_867_, v___y_868_, v___y_869_, v___y_870_, v___y_871_, v___y_872_, v___y_873_);
lean_dec(v___y_873_);
lean_dec_ref(v___y_872_);
lean_dec(v___y_871_);
lean_dec_ref(v___y_870_);
lean_dec(v___y_869_);
lean_dec_ref(v___y_868_);
return v_res_875_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess___lam__0___closed__0(void){
_start:
{
lean_object* v___x_876_; 
v___x_876_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_876_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess___lam__0___closed__1(void){
_start:
{
lean_object* v___x_877_; lean_object* v___x_878_; 
v___x_877_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess___lam__0___closed__0, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess___lam__0___closed__0_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess___lam__0___closed__0);
v___x_878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_878_, 0, v___x_877_);
return v___x_878_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess___lam__0___closed__2(void){
_start:
{
lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; 
v___x_879_ = lean_unsigned_to_nat(32u);
v___x_880_ = lean_mk_empty_array_with_capacity(v___x_879_);
v___x_881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_881_, 0, v___x_880_);
return v___x_881_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess___lam__0(lean_object* v_simprocs_882_, lean_object* v_relevantLemmas_883_, lean_object* v___x_884_, lean_object* v_goal_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_){
_start:
{
lean_object* v___x_893_; 
v___x_893_ = l_Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas(v_simprocs_882_, v_relevantLemmas_883_, v___y_886_, v___y_887_, v___y_888_, v___y_889_, v___y_890_, v___y_891_);
if (lean_obj_tag(v___x_893_) == 0)
{
lean_object* v_a_894_; lean_object* v_fst_895_; lean_object* v_snd_896_; lean_object* v___x_898_; uint8_t v_isShared_899_; uint8_t v_isSharedCheck_992_; 
v_a_894_ = lean_ctor_get(v___x_893_, 0);
lean_inc(v_a_894_);
lean_dec_ref_known(v___x_893_, 1);
v_fst_895_ = lean_ctor_get(v_a_894_, 0);
v_snd_896_ = lean_ctor_get(v_a_894_, 1);
v_isSharedCheck_992_ = !lean_is_exclusive(v_a_894_);
if (v_isSharedCheck_992_ == 0)
{
v___x_898_ = v_a_894_;
v_isShared_899_ = v_isSharedCheck_992_;
goto v_resetjp_897_;
}
else
{
lean_inc(v_snd_896_);
lean_inc(v_fst_895_);
lean_dec(v_a_894_);
v___x_898_ = lean_box(0);
v_isShared_899_ = v_isSharedCheck_992_;
goto v_resetjp_897_;
}
v_resetjp_897_:
{
lean_object* v___x_900_; 
v___x_900_ = l_Lean_Meta_Tactic_BVDecide_Normalize_addDefaultTypeAnalysisLemmas(v_snd_896_, v___y_886_, v___y_887_, v___y_888_, v___y_889_, v___y_890_, v___y_891_);
if (lean_obj_tag(v___x_900_) == 0)
{
lean_object* v_a_901_; lean_object* v___x_902_; 
v_a_901_ = lean_ctor_get(v___x_900_, 0);
lean_inc(v_a_901_);
lean_dec_ref_known(v___x_900_, 1);
v___x_902_ = l_Lean_Meta_getSimpCongrTheorems___redArg(v___y_891_);
if (lean_obj_tag(v___x_902_) == 0)
{
lean_object* v_a_903_; lean_object* v_maxSteps_904_; lean_object* v___x_905_; uint8_t v___x_906_; uint8_t v___x_907_; uint8_t v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; 
v_a_903_ = lean_ctor_get(v___x_902_, 0);
lean_inc(v_a_903_);
lean_dec_ref_known(v___x_902_, 1);
v_maxSteps_904_ = lean_ctor_get(v___y_886_, 1);
v___x_905_ = lean_unsigned_to_nat(2u);
v___x_906_ = 0;
v___x_907_ = 1;
v___x_908_ = 0;
v___x_909_ = lean_box(0);
lean_inc(v_maxSteps_904_);
v___x_910_ = lean_alloc_ctor(0, 3, 29);
lean_ctor_set(v___x_910_, 0, v_maxSteps_904_);
lean_ctor_set(v___x_910_, 1, v___x_905_);
lean_ctor_set(v___x_910_, 2, v___x_909_);
lean_ctor_set_uint8(v___x_910_, sizeof(void*)*3, v___x_906_);
lean_ctor_set_uint8(v___x_910_, sizeof(void*)*3 + 1, v___x_907_);
lean_ctor_set_uint8(v___x_910_, sizeof(void*)*3 + 2, v___x_906_);
lean_ctor_set_uint8(v___x_910_, sizeof(void*)*3 + 3, v___x_907_);
lean_ctor_set_uint8(v___x_910_, sizeof(void*)*3 + 4, v___x_907_);
lean_ctor_set_uint8(v___x_910_, sizeof(void*)*3 + 5, v___x_907_);
lean_ctor_set_uint8(v___x_910_, sizeof(void*)*3 + 6, v___x_908_);
lean_ctor_set_uint8(v___x_910_, sizeof(void*)*3 + 7, v___x_907_);
lean_ctor_set_uint8(v___x_910_, sizeof(void*)*3 + 8, v___x_907_);
lean_ctor_set_uint8(v___x_910_, sizeof(void*)*3 + 9, v___x_906_);
lean_ctor_set_uint8(v___x_910_, sizeof(void*)*3 + 10, v___x_906_);
lean_ctor_set_uint8(v___x_910_, sizeof(void*)*3 + 11, v___x_906_);
lean_ctor_set_uint8(v___x_910_, sizeof(void*)*3 + 12, v___x_907_);
lean_ctor_set_uint8(v___x_910_, sizeof(void*)*3 + 13, v___x_906_);
lean_ctor_set_uint8(v___x_910_, sizeof(void*)*3 + 14, v___x_906_);
lean_ctor_set_uint8(v___x_910_, sizeof(void*)*3 + 15, v___x_906_);
lean_ctor_set_uint8(v___x_910_, sizeof(void*)*3 + 16, v___x_906_);
lean_ctor_set_uint8(v___x_910_, sizeof(void*)*3 + 17, v___x_907_);
lean_ctor_set_uint8(v___x_910_, sizeof(void*)*3 + 18, v___x_906_);
lean_ctor_set_uint8(v___x_910_, sizeof(void*)*3 + 19, v___x_907_);
lean_ctor_set_uint8(v___x_910_, sizeof(void*)*3 + 20, v___x_907_);
lean_ctor_set_uint8(v___x_910_, sizeof(void*)*3 + 21, v___x_907_);
lean_ctor_set_uint8(v___x_910_, sizeof(void*)*3 + 22, v___x_907_);
lean_ctor_set_uint8(v___x_910_, sizeof(void*)*3 + 23, v___x_907_);
lean_ctor_set_uint8(v___x_910_, sizeof(void*)*3 + 24, v___x_907_);
lean_ctor_set_uint8(v___x_910_, sizeof(void*)*3 + 25, v___x_907_);
lean_ctor_set_uint8(v___x_910_, sizeof(void*)*3 + 26, v___x_906_);
lean_ctor_set_uint8(v___x_910_, sizeof(void*)*3 + 27, v___x_906_);
lean_ctor_set_uint8(v___x_910_, sizeof(void*)*3 + 28, v___x_906_);
v___x_911_ = l_Lean_Options_empty;
v___x_912_ = l_Lean_Meta_Simp_mkContext___redArg(v___x_910_, v_a_901_, v_a_903_, v___x_911_, v___y_888_, v___y_890_, v___y_891_);
if (lean_obj_tag(v___x_912_) == 0)
{
lean_object* v_a_913_; lean_object* v___x_914_; 
v_a_913_ = lean_ctor_get(v___x_912_, 0);
lean_inc(v_a_913_);
lean_dec_ref_known(v___x_912_, 1);
v___x_914_ = l_Lean_Meta_getPropHyps(v___y_888_, v___y_889_, v___y_890_, v___y_891_);
if (lean_obj_tag(v___x_914_) == 0)
{
lean_object* v_a_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_921_; 
v_a_915_ = lean_ctor_get(v___x_914_, 0);
lean_inc(v_a_915_);
lean_dec_ref_known(v___x_914_, 1);
v___x_916_ = lean_unsigned_to_nat(1u);
v___x_917_ = lean_mk_empty_array_with_capacity(v___x_916_);
v___x_918_ = lean_array_push(v___x_917_, v_fst_895_);
v___x_919_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess___lam__0___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess___lam__0___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess___lam__0___closed__1);
lean_inc(v___x_884_);
if (v_isShared_899_ == 0)
{
lean_ctor_set(v___x_898_, 1, v___x_884_);
lean_ctor_set(v___x_898_, 0, v___x_919_);
v___x_921_ = v___x_898_;
goto v_reusejp_920_;
}
else
{
lean_object* v_reuseFailAlloc_959_; 
v_reuseFailAlloc_959_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_959_, 0, v___x_919_);
lean_ctor_set(v_reuseFailAlloc_959_, 1, v___x_884_);
v___x_921_ = v_reuseFailAlloc_959_;
goto v_reusejp_920_;
}
v_reusejp_920_:
{
lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; size_t v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; 
v___x_922_ = lean_unsigned_to_nat(32u);
v___x_923_ = lean_mk_empty_array_with_capacity(v___x_922_);
v___x_924_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess___lam__0___closed__2, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess___lam__0___closed__2_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess___lam__0___closed__2);
v___x_925_ = ((size_t)5ULL);
lean_inc(v___x_884_);
v___x_926_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_926_, 0, v___x_924_);
lean_ctor_set(v___x_926_, 1, v___x_923_);
lean_ctor_set(v___x_926_, 2, v___x_884_);
lean_ctor_set(v___x_926_, 3, v___x_884_);
lean_ctor_set_usize(v___x_926_, 4, v___x_925_);
v___x_927_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_927_, 0, v___x_919_);
lean_ctor_set(v___x_927_, 1, v___x_919_);
lean_ctor_set(v___x_927_, 2, v___x_919_);
lean_ctor_set(v___x_927_, 3, v___x_926_);
v___x_928_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_928_, 0, v___x_921_);
lean_ctor_set(v___x_928_, 1, v___x_927_);
v___x_929_ = l_Lean_Meta_simpGoal(v_goal_885_, v_a_913_, v___x_918_, v___x_909_, v___x_907_, v_a_915_, v___x_928_, v___y_888_, v___y_889_, v___y_890_, v___y_891_);
if (lean_obj_tag(v___x_929_) == 0)
{
lean_object* v_a_930_; lean_object* v___x_932_; uint8_t v_isShared_933_; uint8_t v_isSharedCheck_950_; 
v_a_930_ = lean_ctor_get(v___x_929_, 0);
v_isSharedCheck_950_ = !lean_is_exclusive(v___x_929_);
if (v_isSharedCheck_950_ == 0)
{
v___x_932_ = v___x_929_;
v_isShared_933_ = v_isSharedCheck_950_;
goto v_resetjp_931_;
}
else
{
lean_inc(v_a_930_);
lean_dec(v___x_929_);
v___x_932_ = lean_box(0);
v_isShared_933_ = v_isSharedCheck_950_;
goto v_resetjp_931_;
}
v_resetjp_931_:
{
lean_object* v_fst_934_; 
v_fst_934_ = lean_ctor_get(v_a_930_, 0);
lean_inc(v_fst_934_);
lean_dec(v_a_930_);
if (lean_obj_tag(v_fst_934_) == 1)
{
lean_object* v_val_935_; lean_object* v___x_937_; uint8_t v_isShared_938_; uint8_t v_isSharedCheck_946_; 
v_val_935_ = lean_ctor_get(v_fst_934_, 0);
v_isSharedCheck_946_ = !lean_is_exclusive(v_fst_934_);
if (v_isSharedCheck_946_ == 0)
{
v___x_937_ = v_fst_934_;
v_isShared_938_ = v_isSharedCheck_946_;
goto v_resetjp_936_;
}
else
{
lean_inc(v_val_935_);
lean_dec(v_fst_934_);
v___x_937_ = lean_box(0);
v_isShared_938_ = v_isSharedCheck_946_;
goto v_resetjp_936_;
}
v_resetjp_936_:
{
lean_object* v_snd_939_; lean_object* v___x_941_; 
v_snd_939_ = lean_ctor_get(v_val_935_, 1);
lean_inc(v_snd_939_);
lean_dec(v_val_935_);
if (v_isShared_938_ == 0)
{
lean_ctor_set(v___x_937_, 0, v_snd_939_);
v___x_941_ = v___x_937_;
goto v_reusejp_940_;
}
else
{
lean_object* v_reuseFailAlloc_945_; 
v_reuseFailAlloc_945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_945_, 0, v_snd_939_);
v___x_941_ = v_reuseFailAlloc_945_;
goto v_reusejp_940_;
}
v_reusejp_940_:
{
lean_object* v___x_943_; 
if (v_isShared_933_ == 0)
{
lean_ctor_set(v___x_932_, 0, v___x_941_);
v___x_943_ = v___x_932_;
goto v_reusejp_942_;
}
else
{
lean_object* v_reuseFailAlloc_944_; 
v_reuseFailAlloc_944_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_944_, 0, v___x_941_);
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
lean_object* v___x_948_; 
lean_dec(v_fst_934_);
if (v_isShared_933_ == 0)
{
lean_ctor_set(v___x_932_, 0, v___x_909_);
v___x_948_ = v___x_932_;
goto v_reusejp_947_;
}
else
{
lean_object* v_reuseFailAlloc_949_; 
v_reuseFailAlloc_949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_949_, 0, v___x_909_);
v___x_948_ = v_reuseFailAlloc_949_;
goto v_reusejp_947_;
}
v_reusejp_947_:
{
return v___x_948_;
}
}
}
}
else
{
lean_object* v_a_951_; lean_object* v___x_953_; uint8_t v_isShared_954_; uint8_t v_isSharedCheck_958_; 
v_a_951_ = lean_ctor_get(v___x_929_, 0);
v_isSharedCheck_958_ = !lean_is_exclusive(v___x_929_);
if (v_isSharedCheck_958_ == 0)
{
v___x_953_ = v___x_929_;
v_isShared_954_ = v_isSharedCheck_958_;
goto v_resetjp_952_;
}
else
{
lean_inc(v_a_951_);
lean_dec(v___x_929_);
v___x_953_ = lean_box(0);
v_isShared_954_ = v_isSharedCheck_958_;
goto v_resetjp_952_;
}
v_resetjp_952_:
{
lean_object* v___x_956_; 
if (v_isShared_954_ == 0)
{
v___x_956_ = v___x_953_;
goto v_reusejp_955_;
}
else
{
lean_object* v_reuseFailAlloc_957_; 
v_reuseFailAlloc_957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_957_, 0, v_a_951_);
v___x_956_ = v_reuseFailAlloc_957_;
goto v_reusejp_955_;
}
v_reusejp_955_:
{
return v___x_956_;
}
}
}
}
}
else
{
lean_object* v_a_960_; lean_object* v___x_962_; uint8_t v_isShared_963_; uint8_t v_isSharedCheck_967_; 
lean_dec(v_a_913_);
lean_del_object(v___x_898_);
lean_dec(v_fst_895_);
lean_dec(v_goal_885_);
lean_dec(v___x_884_);
v_a_960_ = lean_ctor_get(v___x_914_, 0);
v_isSharedCheck_967_ = !lean_is_exclusive(v___x_914_);
if (v_isSharedCheck_967_ == 0)
{
v___x_962_ = v___x_914_;
v_isShared_963_ = v_isSharedCheck_967_;
goto v_resetjp_961_;
}
else
{
lean_inc(v_a_960_);
lean_dec(v___x_914_);
v___x_962_ = lean_box(0);
v_isShared_963_ = v_isSharedCheck_967_;
goto v_resetjp_961_;
}
v_resetjp_961_:
{
lean_object* v___x_965_; 
if (v_isShared_963_ == 0)
{
v___x_965_ = v___x_962_;
goto v_reusejp_964_;
}
else
{
lean_object* v_reuseFailAlloc_966_; 
v_reuseFailAlloc_966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_966_, 0, v_a_960_);
v___x_965_ = v_reuseFailAlloc_966_;
goto v_reusejp_964_;
}
v_reusejp_964_:
{
return v___x_965_;
}
}
}
}
else
{
lean_object* v_a_968_; lean_object* v___x_970_; uint8_t v_isShared_971_; uint8_t v_isSharedCheck_975_; 
lean_del_object(v___x_898_);
lean_dec(v_fst_895_);
lean_dec(v_goal_885_);
lean_dec(v___x_884_);
v_a_968_ = lean_ctor_get(v___x_912_, 0);
v_isSharedCheck_975_ = !lean_is_exclusive(v___x_912_);
if (v_isSharedCheck_975_ == 0)
{
v___x_970_ = v___x_912_;
v_isShared_971_ = v_isSharedCheck_975_;
goto v_resetjp_969_;
}
else
{
lean_inc(v_a_968_);
lean_dec(v___x_912_);
v___x_970_ = lean_box(0);
v_isShared_971_ = v_isSharedCheck_975_;
goto v_resetjp_969_;
}
v_resetjp_969_:
{
lean_object* v___x_973_; 
if (v_isShared_971_ == 0)
{
v___x_973_ = v___x_970_;
goto v_reusejp_972_;
}
else
{
lean_object* v_reuseFailAlloc_974_; 
v_reuseFailAlloc_974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_974_, 0, v_a_968_);
v___x_973_ = v_reuseFailAlloc_974_;
goto v_reusejp_972_;
}
v_reusejp_972_:
{
return v___x_973_;
}
}
}
}
else
{
lean_object* v_a_976_; lean_object* v___x_978_; uint8_t v_isShared_979_; uint8_t v_isSharedCheck_983_; 
lean_dec(v_a_901_);
lean_del_object(v___x_898_);
lean_dec(v_fst_895_);
lean_dec(v_goal_885_);
lean_dec(v___x_884_);
v_a_976_ = lean_ctor_get(v___x_902_, 0);
v_isSharedCheck_983_ = !lean_is_exclusive(v___x_902_);
if (v_isSharedCheck_983_ == 0)
{
v___x_978_ = v___x_902_;
v_isShared_979_ = v_isSharedCheck_983_;
goto v_resetjp_977_;
}
else
{
lean_inc(v_a_976_);
lean_dec(v___x_902_);
v___x_978_ = lean_box(0);
v_isShared_979_ = v_isSharedCheck_983_;
goto v_resetjp_977_;
}
v_resetjp_977_:
{
lean_object* v___x_981_; 
if (v_isShared_979_ == 0)
{
v___x_981_ = v___x_978_;
goto v_reusejp_980_;
}
else
{
lean_object* v_reuseFailAlloc_982_; 
v_reuseFailAlloc_982_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_982_, 0, v_a_976_);
v___x_981_ = v_reuseFailAlloc_982_;
goto v_reusejp_980_;
}
v_reusejp_980_:
{
return v___x_981_;
}
}
}
}
else
{
lean_object* v_a_984_; lean_object* v___x_986_; uint8_t v_isShared_987_; uint8_t v_isSharedCheck_991_; 
lean_del_object(v___x_898_);
lean_dec(v_fst_895_);
lean_dec(v_goal_885_);
lean_dec(v___x_884_);
v_a_984_ = lean_ctor_get(v___x_900_, 0);
v_isSharedCheck_991_ = !lean_is_exclusive(v___x_900_);
if (v_isSharedCheck_991_ == 0)
{
v___x_986_ = v___x_900_;
v_isShared_987_ = v_isSharedCheck_991_;
goto v_resetjp_985_;
}
else
{
lean_inc(v_a_984_);
lean_dec(v___x_900_);
v___x_986_ = lean_box(0);
v_isShared_987_ = v_isSharedCheck_991_;
goto v_resetjp_985_;
}
v_resetjp_985_:
{
lean_object* v___x_989_; 
if (v_isShared_987_ == 0)
{
v___x_989_ = v___x_986_;
goto v_reusejp_988_;
}
else
{
lean_object* v_reuseFailAlloc_990_; 
v_reuseFailAlloc_990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_990_, 0, v_a_984_);
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
lean_dec(v_goal_885_);
lean_dec(v___x_884_);
v_a_993_ = lean_ctor_get(v___x_893_, 0);
v_isSharedCheck_1000_ = !lean_is_exclusive(v___x_893_);
if (v_isSharedCheck_1000_ == 0)
{
v___x_995_ = v___x_893_;
v_isShared_996_ = v_isSharedCheck_1000_;
goto v_resetjp_994_;
}
else
{
lean_inc(v_a_993_);
lean_dec(v___x_893_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess___lam__0___boxed(lean_object* v_simprocs_1001_, lean_object* v_relevantLemmas_1002_, lean_object* v___x_1003_, lean_object* v_goal_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_){
_start:
{
lean_object* v_res_1012_; 
v_res_1012_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess___lam__0(v_simprocs_1001_, v_relevantLemmas_1002_, v___x_1003_, v_goal_1004_, v___y_1005_, v___y_1006_, v___y_1007_, v___y_1008_, v___y_1009_, v___y_1010_);
lean_dec(v___y_1010_);
lean_dec_ref(v___y_1009_);
lean_dec(v___y_1008_);
lean_dec_ref(v___y_1007_);
lean_dec(v___y_1006_);
lean_dec_ref(v___y_1005_);
return v_res_1012_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess___closed__0(void){
_start:
{
lean_object* v___x_1013_; 
v___x_1013_ = l_Lean_Meta_DiscrTree_empty(lean_box(0));
return v___x_1013_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess___closed__1(void){
_start:
{
lean_object* v___x_1014_; 
v___x_1014_ = l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess_spec__0(lean_box(0));
return v___x_1014_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess___closed__2(void){
_start:
{
lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v_simprocs_1017_; 
v___x_1015_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess___closed__1);
v___x_1016_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess___closed__0, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess___closed__0_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess___closed__0);
v_simprocs_1017_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_simprocs_1017_, 0, v___x_1016_);
lean_ctor_set(v_simprocs_1017_, 1, v___x_1016_);
lean_ctor_set(v_simprocs_1017_, 2, v___x_1015_);
lean_ctor_set(v_simprocs_1017_, 3, v___x_1015_);
return v_simprocs_1017_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess(lean_object* v_goal_1020_, lean_object* v_a_1021_, lean_object* v_a_1022_, lean_object* v_a_1023_, lean_object* v_a_1024_, lean_object* v_a_1025_, lean_object* v_a_1026_){
_start:
{
lean_object* v_simprocs_1028_; lean_object* v___x_1029_; lean_object* v_relevantLemmas_1030_; lean_object* v___f_1031_; lean_object* v___x_1032_; 
v_simprocs_1028_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess___closed__2, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess___closed__2_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess___closed__2);
v___x_1029_ = lean_unsigned_to_nat(0u);
v_relevantLemmas_1030_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess___closed__3));
lean_inc(v_goal_1020_);
v___f_1031_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess___lam__0___boxed), 11, 4);
lean_closure_set(v___f_1031_, 0, v_simprocs_1028_);
lean_closure_set(v___f_1031_, 1, v_relevantLemmas_1030_);
lean_closure_set(v___f_1031_, 2, v___x_1029_);
lean_closure_set(v___f_1031_, 3, v_goal_1020_);
v___x_1032_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess_spec__1___redArg(v_goal_1020_, v___f_1031_, v_a_1021_, v_a_1022_, v_a_1023_, v_a_1024_, v_a_1025_, v_a_1026_);
return v___x_1032_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess___boxed(lean_object* v_goal_1033_, lean_object* v_a_1034_, lean_object* v_a_1035_, lean_object* v_a_1036_, lean_object* v_a_1037_, lean_object* v_a_1038_, lean_object* v_a_1039_, lean_object* v_a_1040_){
_start:
{
lean_object* v_res_1041_; 
v_res_1041_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess(v_goal_1033_, v_a_1034_, v_a_1035_, v_a_1036_, v_a_1037_, v_a_1038_, v_a_1039_);
lean_dec(v_a_1039_);
lean_dec_ref(v_a_1038_);
lean_dec(v_a_1037_);
lean_dec_ref(v_a_1036_);
lean_dec(v_a_1035_);
lean_dec_ref(v_a_1034_);
return v_res_1041_;
}
}
static lean_object* _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__2_spec__5___closed__0(void){
_start:
{
lean_object* v___x_1042_; 
v___x_1042_ = l_instMonadEIO(lean_box(0));
return v___x_1042_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__2_spec__5(lean_object* v_msg_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_){
_start:
{
lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v_toApplicative_1057_; lean_object* v___x_1059_; uint8_t v_isShared_1060_; uint8_t v_isSharedCheck_1120_; 
v___x_1055_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__2_spec__5___closed__0, &l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__2_spec__5___closed__0_once, _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__2_spec__5___closed__0);
v___x_1056_ = l_StateRefT_x27_instMonad___redArg(v___x_1055_);
v_toApplicative_1057_ = lean_ctor_get(v___x_1056_, 0);
v_isSharedCheck_1120_ = !lean_is_exclusive(v___x_1056_);
if (v_isSharedCheck_1120_ == 0)
{
lean_object* v_unused_1121_; 
v_unused_1121_ = lean_ctor_get(v___x_1056_, 1);
lean_dec(v_unused_1121_);
v___x_1059_ = v___x_1056_;
v_isShared_1060_ = v_isSharedCheck_1120_;
goto v_resetjp_1058_;
}
else
{
lean_inc(v_toApplicative_1057_);
lean_dec(v___x_1056_);
v___x_1059_ = lean_box(0);
v_isShared_1060_ = v_isSharedCheck_1120_;
goto v_resetjp_1058_;
}
v_resetjp_1058_:
{
lean_object* v_toFunctor_1061_; lean_object* v_toSeq_1062_; lean_object* v_toSeqLeft_1063_; lean_object* v_toSeqRight_1064_; lean_object* v___x_1066_; uint8_t v_isShared_1067_; uint8_t v_isSharedCheck_1118_; 
v_toFunctor_1061_ = lean_ctor_get(v_toApplicative_1057_, 0);
v_toSeq_1062_ = lean_ctor_get(v_toApplicative_1057_, 2);
v_toSeqLeft_1063_ = lean_ctor_get(v_toApplicative_1057_, 3);
v_toSeqRight_1064_ = lean_ctor_get(v_toApplicative_1057_, 4);
v_isSharedCheck_1118_ = !lean_is_exclusive(v_toApplicative_1057_);
if (v_isSharedCheck_1118_ == 0)
{
lean_object* v_unused_1119_; 
v_unused_1119_ = lean_ctor_get(v_toApplicative_1057_, 1);
lean_dec(v_unused_1119_);
v___x_1066_ = v_toApplicative_1057_;
v_isShared_1067_ = v_isSharedCheck_1118_;
goto v_resetjp_1065_;
}
else
{
lean_inc(v_toSeqRight_1064_);
lean_inc(v_toSeqLeft_1063_);
lean_inc(v_toSeq_1062_);
lean_inc(v_toFunctor_1061_);
lean_dec(v_toApplicative_1057_);
v___x_1066_ = lean_box(0);
v_isShared_1067_ = v_isSharedCheck_1118_;
goto v_resetjp_1065_;
}
v_resetjp_1065_:
{
lean_object* v___f_1068_; lean_object* v___f_1069_; lean_object* v___f_1070_; lean_object* v___f_1071_; lean_object* v___x_1072_; lean_object* v___f_1073_; lean_object* v___f_1074_; lean_object* v___f_1075_; lean_object* v___x_1077_; 
v___f_1068_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__2_spec__5___closed__1));
v___f_1069_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__2_spec__5___closed__2));
lean_inc_ref(v_toFunctor_1061_);
v___f_1070_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1070_, 0, v_toFunctor_1061_);
v___f_1071_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1071_, 0, v_toFunctor_1061_);
v___x_1072_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1072_, 0, v___f_1070_);
lean_ctor_set(v___x_1072_, 1, v___f_1071_);
v___f_1073_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1073_, 0, v_toSeqRight_1064_);
v___f_1074_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1074_, 0, v_toSeqLeft_1063_);
v___f_1075_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1075_, 0, v_toSeq_1062_);
if (v_isShared_1067_ == 0)
{
lean_ctor_set(v___x_1066_, 4, v___f_1073_);
lean_ctor_set(v___x_1066_, 3, v___f_1074_);
lean_ctor_set(v___x_1066_, 2, v___f_1075_);
lean_ctor_set(v___x_1066_, 1, v___f_1068_);
lean_ctor_set(v___x_1066_, 0, v___x_1072_);
v___x_1077_ = v___x_1066_;
goto v_reusejp_1076_;
}
else
{
lean_object* v_reuseFailAlloc_1117_; 
v_reuseFailAlloc_1117_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1117_, 0, v___x_1072_);
lean_ctor_set(v_reuseFailAlloc_1117_, 1, v___f_1068_);
lean_ctor_set(v_reuseFailAlloc_1117_, 2, v___f_1075_);
lean_ctor_set(v_reuseFailAlloc_1117_, 3, v___f_1074_);
lean_ctor_set(v_reuseFailAlloc_1117_, 4, v___f_1073_);
v___x_1077_ = v_reuseFailAlloc_1117_;
goto v_reusejp_1076_;
}
v_reusejp_1076_:
{
lean_object* v___x_1079_; 
if (v_isShared_1060_ == 0)
{
lean_ctor_set(v___x_1059_, 1, v___f_1069_);
lean_ctor_set(v___x_1059_, 0, v___x_1077_);
v___x_1079_ = v___x_1059_;
goto v_reusejp_1078_;
}
else
{
lean_object* v_reuseFailAlloc_1116_; 
v_reuseFailAlloc_1116_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1116_, 0, v___x_1077_);
lean_ctor_set(v_reuseFailAlloc_1116_, 1, v___f_1069_);
v___x_1079_ = v_reuseFailAlloc_1116_;
goto v_reusejp_1078_;
}
v_reusejp_1078_:
{
lean_object* v___x_1080_; lean_object* v_toApplicative_1081_; lean_object* v___x_1083_; uint8_t v_isShared_1084_; uint8_t v_isSharedCheck_1114_; 
v___x_1080_ = l_StateRefT_x27_instMonad___redArg(v___x_1079_);
v_toApplicative_1081_ = lean_ctor_get(v___x_1080_, 0);
v_isSharedCheck_1114_ = !lean_is_exclusive(v___x_1080_);
if (v_isSharedCheck_1114_ == 0)
{
lean_object* v_unused_1115_; 
v_unused_1115_ = lean_ctor_get(v___x_1080_, 1);
lean_dec(v_unused_1115_);
v___x_1083_ = v___x_1080_;
v_isShared_1084_ = v_isSharedCheck_1114_;
goto v_resetjp_1082_;
}
else
{
lean_inc(v_toApplicative_1081_);
lean_dec(v___x_1080_);
v___x_1083_ = lean_box(0);
v_isShared_1084_ = v_isSharedCheck_1114_;
goto v_resetjp_1082_;
}
v_resetjp_1082_:
{
lean_object* v_toFunctor_1085_; lean_object* v_toSeq_1086_; lean_object* v_toSeqLeft_1087_; lean_object* v_toSeqRight_1088_; lean_object* v___x_1090_; uint8_t v_isShared_1091_; uint8_t v_isSharedCheck_1112_; 
v_toFunctor_1085_ = lean_ctor_get(v_toApplicative_1081_, 0);
v_toSeq_1086_ = lean_ctor_get(v_toApplicative_1081_, 2);
v_toSeqLeft_1087_ = lean_ctor_get(v_toApplicative_1081_, 3);
v_toSeqRight_1088_ = lean_ctor_get(v_toApplicative_1081_, 4);
v_isSharedCheck_1112_ = !lean_is_exclusive(v_toApplicative_1081_);
if (v_isSharedCheck_1112_ == 0)
{
lean_object* v_unused_1113_; 
v_unused_1113_ = lean_ctor_get(v_toApplicative_1081_, 1);
lean_dec(v_unused_1113_);
v___x_1090_ = v_toApplicative_1081_;
v_isShared_1091_ = v_isSharedCheck_1112_;
goto v_resetjp_1089_;
}
else
{
lean_inc(v_toSeqRight_1088_);
lean_inc(v_toSeqLeft_1087_);
lean_inc(v_toSeq_1086_);
lean_inc(v_toFunctor_1085_);
lean_dec(v_toApplicative_1081_);
v___x_1090_ = lean_box(0);
v_isShared_1091_ = v_isSharedCheck_1112_;
goto v_resetjp_1089_;
}
v_resetjp_1089_:
{
lean_object* v___f_1092_; lean_object* v___f_1093_; lean_object* v___f_1094_; lean_object* v___f_1095_; lean_object* v___x_1096_; lean_object* v___f_1097_; lean_object* v___f_1098_; lean_object* v___f_1099_; lean_object* v___x_1101_; 
v___f_1092_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__2_spec__5___closed__3));
v___f_1093_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__2_spec__5___closed__4));
lean_inc_ref(v_toFunctor_1085_);
v___f_1094_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1094_, 0, v_toFunctor_1085_);
v___f_1095_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1095_, 0, v_toFunctor_1085_);
v___x_1096_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1096_, 0, v___f_1094_);
lean_ctor_set(v___x_1096_, 1, v___f_1095_);
v___f_1097_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1097_, 0, v_toSeqRight_1088_);
v___f_1098_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1098_, 0, v_toSeqLeft_1087_);
v___f_1099_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1099_, 0, v_toSeq_1086_);
if (v_isShared_1091_ == 0)
{
lean_ctor_set(v___x_1090_, 4, v___f_1097_);
lean_ctor_set(v___x_1090_, 3, v___f_1098_);
lean_ctor_set(v___x_1090_, 2, v___f_1099_);
lean_ctor_set(v___x_1090_, 1, v___f_1092_);
lean_ctor_set(v___x_1090_, 0, v___x_1096_);
v___x_1101_ = v___x_1090_;
goto v_reusejp_1100_;
}
else
{
lean_object* v_reuseFailAlloc_1111_; 
v_reuseFailAlloc_1111_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1111_, 0, v___x_1096_);
lean_ctor_set(v_reuseFailAlloc_1111_, 1, v___f_1092_);
lean_ctor_set(v_reuseFailAlloc_1111_, 2, v___f_1099_);
lean_ctor_set(v_reuseFailAlloc_1111_, 3, v___f_1098_);
lean_ctor_set(v_reuseFailAlloc_1111_, 4, v___f_1097_);
v___x_1101_ = v_reuseFailAlloc_1111_;
goto v_reusejp_1100_;
}
v_reusejp_1100_:
{
lean_object* v___x_1103_; 
if (v_isShared_1084_ == 0)
{
lean_ctor_set(v___x_1083_, 1, v___f_1093_);
lean_ctor_set(v___x_1083_, 0, v___x_1101_);
v___x_1103_ = v___x_1083_;
goto v_reusejp_1102_;
}
else
{
lean_object* v_reuseFailAlloc_1110_; 
v_reuseFailAlloc_1110_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1110_, 0, v___x_1101_);
lean_ctor_set(v_reuseFailAlloc_1110_, 1, v___f_1093_);
v___x_1103_ = v_reuseFailAlloc_1110_;
goto v_reusejp_1102_;
}
v_reusejp_1102_:
{
lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_26420__overap_1108_; lean_object* v___x_1109_; 
v___x_1104_ = l_StateRefT_x27_instMonad___redArg(v___x_1103_);
v___x_1105_ = l_ReaderT_instMonad___redArg(v___x_1104_);
v___x_1106_ = lean_box(0);
v___x_1107_ = l_instInhabitedOfMonad___redArg(v___x_1105_, v___x_1106_);
v___x_26420__overap_1108_ = lean_panic_fn_borrowed(v___x_1107_, v_msg_1047_);
lean_dec(v___x_1107_);
lean_inc(v___y_1053_);
lean_inc_ref(v___y_1052_);
lean_inc(v___y_1051_);
lean_inc_ref(v___y_1050_);
lean_inc(v___y_1049_);
lean_inc_ref(v___y_1048_);
v___x_1109_ = lean_apply_7(v___x_26420__overap_1108_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_, v___y_1052_, v___y_1053_, lean_box(0));
return v___x_1109_;
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__2_spec__5___boxed(lean_object* v_msg_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_){
_start:
{
lean_object* v_res_1130_; 
v_res_1130_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__2_spec__5(v_msg_1122_, v___y_1123_, v___y_1124_, v___y_1125_, v___y_1126_, v___y_1127_, v___y_1128_);
lean_dec(v___y_1128_);
lean_dec_ref(v___y_1127_);
lean_dec(v___y_1126_);
lean_dec_ref(v___y_1125_);
lean_dec(v___y_1124_);
lean_dec_ref(v___y_1123_);
return v_res_1130_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__2___closed__1(void){
_start:
{
lean_object* v___x_1132_; lean_object* v___x_1133_; 
v___x_1132_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__2___closed__0));
v___x_1133_ = l_Lean_stringToMessageData(v___x_1132_);
return v___x_1133_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__2___closed__5(void){
_start:
{
lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; 
v___x_1137_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__2___closed__4));
v___x_1138_ = lean_unsigned_to_nat(11u);
v___x_1139_ = lean_unsigned_to_nat(122u);
v___x_1140_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__2___closed__3));
v___x_1141_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__2___closed__2));
v___x_1142_ = l_mkPanicMessageWithDecl(v___x_1141_, v___x_1140_, v___x_1139_, v___x_1138_, v___x_1137_);
return v___x_1142_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__2(lean_object* v_constName_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_){
_start:
{
lean_object* v___x_1159_; lean_object* v_env_1160_; uint8_t v___x_1161_; lean_object* v___x_1162_; 
v___x_1159_ = lean_st_ref_get(v___y_1149_);
v_env_1160_ = lean_ctor_get(v___x_1159_, 0);
lean_inc_ref(v_env_1160_);
lean_dec(v___x_1159_);
v___x_1161_ = 0;
lean_inc(v_constName_1143_);
v___x_1162_ = l_Lean_Environment_findAsync_x3f(v_env_1160_, v_constName_1143_, v___x_1161_);
if (lean_obj_tag(v___x_1162_) == 1)
{
lean_object* v_val_1163_; uint8_t v_kind_1164_; 
v_val_1163_ = lean_ctor_get(v___x_1162_, 0);
lean_inc(v_val_1163_);
lean_dec_ref_known(v___x_1162_, 1);
v_kind_1164_ = lean_ctor_get_uint8(v_val_1163_, sizeof(void*)*3);
if (v_kind_1164_ == 6)
{
lean_object* v___x_1165_; 
v___x_1165_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_1163_);
if (lean_obj_tag(v___x_1165_) == 6)
{
lean_object* v_val_1166_; lean_object* v___x_1168_; uint8_t v_isShared_1169_; uint8_t v_isSharedCheck_1173_; 
lean_dec(v_constName_1143_);
v_val_1166_ = lean_ctor_get(v___x_1165_, 0);
v_isSharedCheck_1173_ = !lean_is_exclusive(v___x_1165_);
if (v_isSharedCheck_1173_ == 0)
{
v___x_1168_ = v___x_1165_;
v_isShared_1169_ = v_isSharedCheck_1173_;
goto v_resetjp_1167_;
}
else
{
lean_inc(v_val_1166_);
lean_dec(v___x_1165_);
v___x_1168_ = lean_box(0);
v_isShared_1169_ = v_isSharedCheck_1173_;
goto v_resetjp_1167_;
}
v_resetjp_1167_:
{
lean_object* v___x_1171_; 
if (v_isShared_1169_ == 0)
{
lean_ctor_set_tag(v___x_1168_, 0);
v___x_1171_ = v___x_1168_;
goto v_reusejp_1170_;
}
else
{
lean_object* v_reuseFailAlloc_1172_; 
v_reuseFailAlloc_1172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1172_, 0, v_val_1166_);
v___x_1171_ = v_reuseFailAlloc_1172_;
goto v_reusejp_1170_;
}
v_reusejp_1170_:
{
return v___x_1171_;
}
}
}
else
{
lean_object* v___x_1174_; lean_object* v___x_1175_; 
lean_dec_ref(v___x_1165_);
v___x_1174_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__2___closed__5, &l_Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__2___closed__5_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__2___closed__5);
v___x_1175_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__2_spec__5(v___x_1174_, v___y_1144_, v___y_1145_, v___y_1146_, v___y_1147_, v___y_1148_, v___y_1149_);
if (lean_obj_tag(v___x_1175_) == 0)
{
lean_object* v_a_1176_; lean_object* v___x_1178_; uint8_t v_isShared_1179_; uint8_t v_isSharedCheck_1184_; 
v_a_1176_ = lean_ctor_get(v___x_1175_, 0);
v_isSharedCheck_1184_ = !lean_is_exclusive(v___x_1175_);
if (v_isSharedCheck_1184_ == 0)
{
v___x_1178_ = v___x_1175_;
v_isShared_1179_ = v_isSharedCheck_1184_;
goto v_resetjp_1177_;
}
else
{
lean_inc(v_a_1176_);
lean_dec(v___x_1175_);
v___x_1178_ = lean_box(0);
v_isShared_1179_ = v_isSharedCheck_1184_;
goto v_resetjp_1177_;
}
v_resetjp_1177_:
{
if (lean_obj_tag(v_a_1176_) == 0)
{
lean_del_object(v___x_1178_);
goto v___jp_1151_;
}
else
{
lean_object* v_val_1180_; lean_object* v___x_1182_; 
lean_dec(v_constName_1143_);
v_val_1180_ = lean_ctor_get(v_a_1176_, 0);
lean_inc(v_val_1180_);
lean_dec_ref_known(v_a_1176_, 1);
if (v_isShared_1179_ == 0)
{
lean_ctor_set(v___x_1178_, 0, v_val_1180_);
v___x_1182_ = v___x_1178_;
goto v_reusejp_1181_;
}
else
{
lean_object* v_reuseFailAlloc_1183_; 
v_reuseFailAlloc_1183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1183_, 0, v_val_1180_);
v___x_1182_ = v_reuseFailAlloc_1183_;
goto v_reusejp_1181_;
}
v_reusejp_1181_:
{
return v___x_1182_;
}
}
}
}
else
{
lean_object* v_a_1185_; lean_object* v___x_1187_; uint8_t v_isShared_1188_; uint8_t v_isSharedCheck_1192_; 
lean_dec(v_constName_1143_);
v_a_1185_ = lean_ctor_get(v___x_1175_, 0);
v_isSharedCheck_1192_ = !lean_is_exclusive(v___x_1175_);
if (v_isSharedCheck_1192_ == 0)
{
v___x_1187_ = v___x_1175_;
v_isShared_1188_ = v_isSharedCheck_1192_;
goto v_resetjp_1186_;
}
else
{
lean_inc(v_a_1185_);
lean_dec(v___x_1175_);
v___x_1187_ = lean_box(0);
v_isShared_1188_ = v_isSharedCheck_1192_;
goto v_resetjp_1186_;
}
v_resetjp_1186_:
{
lean_object* v___x_1190_; 
if (v_isShared_1188_ == 0)
{
v___x_1190_ = v___x_1187_;
goto v_reusejp_1189_;
}
else
{
lean_object* v_reuseFailAlloc_1191_; 
v_reuseFailAlloc_1191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1191_, 0, v_a_1185_);
v___x_1190_ = v_reuseFailAlloc_1191_;
goto v_reusejp_1189_;
}
v_reusejp_1189_:
{
return v___x_1190_;
}
}
}
}
}
else
{
lean_dec(v_val_1163_);
goto v___jp_1151_;
}
}
else
{
lean_dec(v___x_1162_);
goto v___jp_1151_;
}
v___jp_1151_:
{
lean_object* v___x_1152_; uint8_t v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; 
v___x_1152_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__0___closed__1, &l_Lean_getConstInfoInduct___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__0___closed__1_once, _init_l_Lean_getConstInfoInduct___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__0___closed__1);
v___x_1153_ = 0;
v___x_1154_ = l_Lean_MessageData_ofConstName(v_constName_1143_, v___x_1153_);
v___x_1155_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1155_, 0, v___x_1152_);
lean_ctor_set(v___x_1155_, 1, v___x_1154_);
v___x_1156_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__2___closed__1, &l_Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__2___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__2___closed__1);
v___x_1157_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1157_, 0, v___x_1155_);
lean_ctor_set(v___x_1157_, 1, v___x_1156_);
v___x_1158_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__0_spec__0___redArg(v___x_1157_, v___y_1146_, v___y_1147_, v___y_1148_, v___y_1149_);
return v___x_1158_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__2___boxed(lean_object* v_constName_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_){
_start:
{
lean_object* v_res_1201_; 
v_res_1201_ = l_Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__2(v_constName_1193_, v___y_1194_, v___y_1195_, v___y_1196_, v___y_1197_, v___y_1198_, v___y_1199_);
lean_dec(v___y_1199_);
lean_dec_ref(v___y_1198_);
lean_dec(v___y_1197_);
lean_dec_ref(v___y_1196_);
lean_dec(v___y_1195_);
lean_dec_ref(v___y_1194_);
return v_res_1201_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__0_spec__0___redArg(lean_object* v_a_1202_, lean_object* v_x_1203_){
_start:
{
if (lean_obj_tag(v_x_1203_) == 0)
{
uint8_t v___x_1204_; 
v___x_1204_ = 0;
return v___x_1204_;
}
else
{
lean_object* v_key_1205_; lean_object* v_tail_1206_; uint8_t v___x_1207_; 
v_key_1205_ = lean_ctor_get(v_x_1203_, 0);
v_tail_1206_ = lean_ctor_get(v_x_1203_, 2);
v___x_1207_ = lean_name_eq(v_key_1205_, v_a_1202_);
if (v___x_1207_ == 0)
{
v_x_1203_ = v_tail_1206_;
goto _start;
}
else
{
return v___x_1207_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__0_spec__0___redArg___boxed(lean_object* v_a_1209_, lean_object* v_x_1210_){
_start:
{
uint8_t v_res_1211_; lean_object* v_r_1212_; 
v_res_1211_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__0_spec__0___redArg(v_a_1209_, v_x_1210_);
lean_dec(v_x_1210_);
lean_dec(v_a_1209_);
v_r_1212_ = lean_box(v_res_1211_);
return v_r_1212_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__0___redArg(lean_object* v_m_1213_, lean_object* v_a_1214_){
_start:
{
lean_object* v_buckets_1215_; lean_object* v___x_1216_; uint64_t v___y_1218_; 
v_buckets_1215_ = lean_ctor_get(v_m_1213_, 1);
v___x_1216_ = lean_array_get_size(v_buckets_1215_);
if (lean_obj_tag(v_a_1214_) == 0)
{
uint64_t v___x_1232_; 
v___x_1232_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_findExtIff_x3f_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_findExtIff_x3f_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_findExtIff_x3f_spec__0___redArg___closed__0);
v___y_1218_ = v___x_1232_;
goto v___jp_1217_;
}
else
{
uint64_t v_hash_1233_; 
v_hash_1233_ = lean_ctor_get_uint64(v_a_1214_, sizeof(void*)*2);
v___y_1218_ = v_hash_1233_;
goto v___jp_1217_;
}
v___jp_1217_:
{
uint64_t v___x_1219_; uint64_t v___x_1220_; uint64_t v_fold_1221_; uint64_t v___x_1222_; uint64_t v___x_1223_; uint64_t v___x_1224_; size_t v___x_1225_; size_t v___x_1226_; size_t v___x_1227_; size_t v___x_1228_; size_t v___x_1229_; lean_object* v___x_1230_; uint8_t v___x_1231_; 
v___x_1219_ = 32ULL;
v___x_1220_ = lean_uint64_shift_right(v___y_1218_, v___x_1219_);
v_fold_1221_ = lean_uint64_xor(v___y_1218_, v___x_1220_);
v___x_1222_ = 16ULL;
v___x_1223_ = lean_uint64_shift_right(v_fold_1221_, v___x_1222_);
v___x_1224_ = lean_uint64_xor(v_fold_1221_, v___x_1223_);
v___x_1225_ = lean_uint64_to_usize(v___x_1224_);
v___x_1226_ = lean_usize_of_nat(v___x_1216_);
v___x_1227_ = ((size_t)1ULL);
v___x_1228_ = lean_usize_sub(v___x_1226_, v___x_1227_);
v___x_1229_ = lean_usize_land(v___x_1225_, v___x_1228_);
v___x_1230_ = lean_array_uget_borrowed(v_buckets_1215_, v___x_1229_);
v___x_1231_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__0_spec__0___redArg(v_a_1214_, v___x_1230_);
return v___x_1231_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__0___redArg___boxed(lean_object* v_m_1234_, lean_object* v_a_1235_){
_start:
{
uint8_t v_res_1236_; lean_object* v_r_1237_; 
v_res_1236_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__0___redArg(v_m_1234_, v_a_1235_);
lean_dec(v_a_1235_);
lean_dec_ref(v_m_1234_);
v_r_1237_ = lean_box(v_res_1236_);
return v_r_1237_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_1238_; lean_object* v_dummy_1239_; 
v___x_1238_ = lean_box(0);
v_dummy_1239_ = l_Lean_Expr_sort___override(v___x_1238_);
return v_dummy_1239_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__3___redArg(lean_object* v_upperBound_1243_, lean_object* v_a_1244_, lean_object* v_fst_1245_, lean_object* v_snd_1246_, lean_object* v_fst_1247_, lean_object* v___x_1248_, lean_object* v_a_1249_, lean_object* v_b_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_){
_start:
{
lean_object* v_a_1257_; uint8_t v___x_1261_; 
v___x_1261_ = lean_nat_dec_lt(v_a_1249_, v_upperBound_1243_);
if (v___x_1261_ == 0)
{
lean_object* v___x_1262_; 
lean_dec(v_a_1249_);
lean_dec_ref(v_fst_1247_);
lean_dec(v_fst_1245_);
lean_dec_ref(v_a_1244_);
v___x_1262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1262_, 0, v_b_1250_);
return v___x_1262_;
}
else
{
lean_object* v___x_1263_; 
lean_inc_ref(v_fst_1247_);
lean_inc(v_a_1249_);
lean_inc(v_fst_1245_);
lean_inc_ref(v_a_1244_);
v___x_1263_ = l_Lean_Meta_mkProjFn___redArg(v_a_1244_, v_fst_1245_, v_snd_1246_, v_a_1249_, v_fst_1247_, v___y_1254_);
if (lean_obj_tag(v___x_1263_) == 0)
{
lean_object* v_a_1264_; lean_object* v___x_1265_; 
v_a_1264_ = lean_ctor_get(v___x_1263_, 0);
lean_inc_n(v_a_1264_, 2);
lean_dec_ref_known(v___x_1263_, 1);
lean_inc(v___y_1254_);
lean_inc_ref(v___y_1253_);
lean_inc(v___y_1252_);
lean_inc_ref(v___y_1251_);
v___x_1265_ = lean_infer_type(v_a_1264_, v___y_1251_, v___y_1252_, v___y_1253_, v___y_1254_);
if (lean_obj_tag(v___x_1265_) == 0)
{
lean_object* v_a_1266_; lean_object* v___x_1267_; 
v_a_1266_ = lean_ctor_get(v___x_1265_, 0);
lean_inc_n(v_a_1266_, 2);
lean_dec_ref_known(v___x_1265_, 1);
v___x_1267_ = l_Lean_Meta_isProp(v_a_1266_, v___y_1251_, v___y_1252_, v___y_1253_, v___y_1254_);
if (lean_obj_tag(v___x_1267_) == 0)
{
lean_object* v_a_1268_; uint8_t v___x_1269_; 
v_a_1268_ = lean_ctor_get(v___x_1267_, 0);
lean_inc(v_a_1268_);
lean_dec_ref_known(v___x_1267_, 1);
v___x_1269_ = lean_unbox(v_a_1268_);
lean_dec(v_a_1268_);
if (v___x_1269_ == 0)
{
lean_object* v_fst_1270_; lean_object* v_snd_1271_; lean_object* v___x_1273_; uint8_t v_isShared_1274_; uint8_t v_isSharedCheck_1298_; 
v_fst_1270_ = lean_ctor_get(v_b_1250_, 0);
v_snd_1271_ = lean_ctor_get(v_b_1250_, 1);
v_isSharedCheck_1298_ = !lean_is_exclusive(v_b_1250_);
if (v_isSharedCheck_1298_ == 0)
{
v___x_1273_ = v_b_1250_;
v_isShared_1274_ = v_isSharedCheck_1298_;
goto v_resetjp_1272_;
}
else
{
lean_inc(v_snd_1271_);
lean_inc(v_fst_1270_);
lean_dec(v_b_1250_);
v___x_1273_ = lean_box(0);
v_isShared_1274_ = v_isSharedCheck_1298_;
goto v_resetjp_1272_;
}
v_resetjp_1272_:
{
lean_object* v___x_1275_; 
v___x_1275_ = l_Lean_Expr_getAppFn(v_a_1266_);
if (lean_obj_tag(v___x_1275_) == 4)
{
lean_object* v_declName_1276_; lean_object* v_us_1277_; uint8_t v___x_1278_; 
v_declName_1276_ = lean_ctor_get(v___x_1275_, 0);
lean_inc(v_declName_1276_);
v_us_1277_ = lean_ctor_get(v___x_1275_, 1);
lean_inc(v_us_1277_);
lean_dec_ref_known(v___x_1275_, 2);
v___x_1278_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__0___redArg(v___x_1248_, v_declName_1276_);
if (v___x_1278_ == 0)
{
lean_object* v___x_1280_; 
lean_dec(v_us_1277_);
lean_dec(v_declName_1276_);
lean_dec(v_a_1266_);
lean_dec(v_a_1264_);
if (v_isShared_1274_ == 0)
{
v___x_1280_ = v___x_1273_;
goto v_reusejp_1279_;
}
else
{
lean_object* v_reuseFailAlloc_1281_; 
v_reuseFailAlloc_1281_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1281_, 0, v_fst_1270_);
lean_ctor_set(v_reuseFailAlloc_1281_, 1, v_snd_1271_);
v___x_1280_ = v_reuseFailAlloc_1281_;
goto v_reusejp_1279_;
}
v_reusejp_1279_:
{
v_a_1257_ = v___x_1280_;
goto v___jp_1256_;
}
}
else
{
lean_object* v_dummy_1282_; lean_object* v_nargs_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1289_; 
v_dummy_1282_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__3___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__3___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__3___redArg___closed__0);
v_nargs_1283_ = l_Lean_Expr_getAppNumArgs(v_a_1266_);
lean_inc(v_nargs_1283_);
v___x_1284_ = lean_mk_array(v_nargs_1283_, v_dummy_1282_);
v___x_1285_ = lean_unsigned_to_nat(1u);
v___x_1286_ = lean_nat_sub(v_nargs_1283_, v___x_1285_);
lean_dec(v_nargs_1283_);
v___x_1287_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_1266_, v___x_1284_, v___x_1286_);
if (v_isShared_1274_ == 0)
{
lean_ctor_set(v___x_1273_, 1, v___x_1287_);
lean_ctor_set(v___x_1273_, 0, v_us_1277_);
v___x_1289_ = v___x_1273_;
goto v_reusejp_1288_;
}
else
{
lean_object* v_reuseFailAlloc_1294_; 
v_reuseFailAlloc_1294_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1294_, 0, v_us_1277_);
lean_ctor_set(v_reuseFailAlloc_1294_, 1, v___x_1287_);
v___x_1289_ = v_reuseFailAlloc_1294_;
goto v_reusejp_1288_;
}
v_reusejp_1288_:
{
lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; 
v___x_1290_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1290_, 0, v_declName_1276_);
lean_ctor_set(v___x_1290_, 1, v___x_1289_);
v___x_1291_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1291_, 0, v_a_1264_);
lean_ctor_set(v___x_1291_, 1, v___x_1290_);
v___x_1292_ = lean_array_push(v_fst_1270_, v___x_1291_);
v___x_1293_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1293_, 0, v___x_1292_);
lean_ctor_set(v___x_1293_, 1, v_snd_1271_);
v_a_1257_ = v___x_1293_;
goto v___jp_1256_;
}
}
}
else
{
lean_object* v___x_1296_; 
lean_dec_ref(v___x_1275_);
lean_dec(v_a_1266_);
lean_dec(v_a_1264_);
if (v_isShared_1274_ == 0)
{
v___x_1296_ = v___x_1273_;
goto v_reusejp_1295_;
}
else
{
lean_object* v_reuseFailAlloc_1297_; 
v_reuseFailAlloc_1297_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1297_, 0, v_fst_1270_);
lean_ctor_set(v_reuseFailAlloc_1297_, 1, v_snd_1271_);
v___x_1296_ = v_reuseFailAlloc_1297_;
goto v_reusejp_1295_;
}
v_reusejp_1295_:
{
v_a_1257_ = v___x_1296_;
goto v___jp_1256_;
}
}
}
}
else
{
lean_object* v_fst_1299_; lean_object* v_snd_1300_; lean_object* v___x_1302_; uint8_t v_isShared_1303_; uint8_t v_isSharedCheck_1312_; 
v_fst_1299_ = lean_ctor_get(v_b_1250_, 0);
v_snd_1300_ = lean_ctor_get(v_b_1250_, 1);
v_isSharedCheck_1312_ = !lean_is_exclusive(v_b_1250_);
if (v_isSharedCheck_1312_ == 0)
{
v___x_1302_ = v_b_1250_;
v_isShared_1303_ = v_isSharedCheck_1312_;
goto v_resetjp_1301_;
}
else
{
lean_inc(v_snd_1300_);
lean_inc(v_fst_1299_);
lean_dec(v_b_1250_);
v___x_1302_ = lean_box(0);
v_isShared_1303_ = v_isSharedCheck_1312_;
goto v_resetjp_1301_;
}
v_resetjp_1301_:
{
lean_object* v___x_1304_; uint8_t v___x_1305_; uint8_t v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1310_; 
v___x_1304_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__3___redArg___closed__2));
v___x_1305_ = 0;
v___x_1306_ = 0;
v___x_1307_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1307_, 0, v___x_1304_);
lean_ctor_set(v___x_1307_, 1, v_a_1266_);
lean_ctor_set(v___x_1307_, 2, v_a_1264_);
lean_ctor_set_uint8(v___x_1307_, sizeof(void*)*3, v___x_1305_);
lean_ctor_set_uint8(v___x_1307_, sizeof(void*)*3 + 1, v___x_1306_);
v___x_1308_ = lean_array_push(v_snd_1300_, v___x_1307_);
if (v_isShared_1303_ == 0)
{
lean_ctor_set(v___x_1302_, 1, v___x_1308_);
v___x_1310_ = v___x_1302_;
goto v_reusejp_1309_;
}
else
{
lean_object* v_reuseFailAlloc_1311_; 
v_reuseFailAlloc_1311_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1311_, 0, v_fst_1299_);
lean_ctor_set(v_reuseFailAlloc_1311_, 1, v___x_1308_);
v___x_1310_ = v_reuseFailAlloc_1311_;
goto v_reusejp_1309_;
}
v_reusejp_1309_:
{
v_a_1257_ = v___x_1310_;
goto v___jp_1256_;
}
}
}
}
else
{
lean_object* v_a_1313_; lean_object* v___x_1315_; uint8_t v_isShared_1316_; uint8_t v_isSharedCheck_1320_; 
lean_dec(v_a_1266_);
lean_dec(v_a_1264_);
lean_dec_ref(v_b_1250_);
lean_dec(v_a_1249_);
lean_dec_ref(v_fst_1247_);
lean_dec(v_fst_1245_);
lean_dec_ref(v_a_1244_);
v_a_1313_ = lean_ctor_get(v___x_1267_, 0);
v_isSharedCheck_1320_ = !lean_is_exclusive(v___x_1267_);
if (v_isSharedCheck_1320_ == 0)
{
v___x_1315_ = v___x_1267_;
v_isShared_1316_ = v_isSharedCheck_1320_;
goto v_resetjp_1314_;
}
else
{
lean_inc(v_a_1313_);
lean_dec(v___x_1267_);
v___x_1315_ = lean_box(0);
v_isShared_1316_ = v_isSharedCheck_1320_;
goto v_resetjp_1314_;
}
v_resetjp_1314_:
{
lean_object* v___x_1318_; 
if (v_isShared_1316_ == 0)
{
v___x_1318_ = v___x_1315_;
goto v_reusejp_1317_;
}
else
{
lean_object* v_reuseFailAlloc_1319_; 
v_reuseFailAlloc_1319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1319_, 0, v_a_1313_);
v___x_1318_ = v_reuseFailAlloc_1319_;
goto v_reusejp_1317_;
}
v_reusejp_1317_:
{
return v___x_1318_;
}
}
}
}
else
{
lean_object* v_a_1321_; lean_object* v___x_1323_; uint8_t v_isShared_1324_; uint8_t v_isSharedCheck_1328_; 
lean_dec(v_a_1264_);
lean_dec_ref(v_b_1250_);
lean_dec(v_a_1249_);
lean_dec_ref(v_fst_1247_);
lean_dec(v_fst_1245_);
lean_dec_ref(v_a_1244_);
v_a_1321_ = lean_ctor_get(v___x_1265_, 0);
v_isSharedCheck_1328_ = !lean_is_exclusive(v___x_1265_);
if (v_isSharedCheck_1328_ == 0)
{
v___x_1323_ = v___x_1265_;
v_isShared_1324_ = v_isSharedCheck_1328_;
goto v_resetjp_1322_;
}
else
{
lean_inc(v_a_1321_);
lean_dec(v___x_1265_);
v___x_1323_ = lean_box(0);
v_isShared_1324_ = v_isSharedCheck_1328_;
goto v_resetjp_1322_;
}
v_resetjp_1322_:
{
lean_object* v___x_1326_; 
if (v_isShared_1324_ == 0)
{
v___x_1326_ = v___x_1323_;
goto v_reusejp_1325_;
}
else
{
lean_object* v_reuseFailAlloc_1327_; 
v_reuseFailAlloc_1327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1327_, 0, v_a_1321_);
v___x_1326_ = v_reuseFailAlloc_1327_;
goto v_reusejp_1325_;
}
v_reusejp_1325_:
{
return v___x_1326_;
}
}
}
}
else
{
lean_object* v_a_1329_; lean_object* v___x_1331_; uint8_t v_isShared_1332_; uint8_t v_isSharedCheck_1336_; 
lean_dec_ref(v_b_1250_);
lean_dec(v_a_1249_);
lean_dec_ref(v_fst_1247_);
lean_dec(v_fst_1245_);
lean_dec_ref(v_a_1244_);
v_a_1329_ = lean_ctor_get(v___x_1263_, 0);
v_isSharedCheck_1336_ = !lean_is_exclusive(v___x_1263_);
if (v_isSharedCheck_1336_ == 0)
{
v___x_1331_ = v___x_1263_;
v_isShared_1332_ = v_isSharedCheck_1336_;
goto v_resetjp_1330_;
}
else
{
lean_inc(v_a_1329_);
lean_dec(v___x_1263_);
v___x_1331_ = lean_box(0);
v_isShared_1332_ = v_isSharedCheck_1336_;
goto v_resetjp_1330_;
}
v_resetjp_1330_:
{
lean_object* v___x_1334_; 
if (v_isShared_1332_ == 0)
{
v___x_1334_ = v___x_1331_;
goto v_reusejp_1333_;
}
else
{
lean_object* v_reuseFailAlloc_1335_; 
v_reuseFailAlloc_1335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1335_, 0, v_a_1329_);
v___x_1334_ = v_reuseFailAlloc_1335_;
goto v_reusejp_1333_;
}
v_reusejp_1333_:
{
return v___x_1334_;
}
}
}
}
v___jp_1256_:
{
lean_object* v___x_1258_; lean_object* v___x_1259_; 
v___x_1258_ = lean_unsigned_to_nat(1u);
v___x_1259_ = lean_nat_add(v_a_1249_, v___x_1258_);
lean_dec(v_a_1249_);
v_a_1249_ = v___x_1259_;
v_b_1250_ = v_a_1257_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__3___redArg___boxed(lean_object* v_upperBound_1337_, lean_object* v_a_1338_, lean_object* v_fst_1339_, lean_object* v_snd_1340_, lean_object* v_fst_1341_, lean_object* v___x_1342_, lean_object* v_a_1343_, lean_object* v_b_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_){
_start:
{
lean_object* v_res_1350_; 
v_res_1350_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__3___redArg(v_upperBound_1337_, v_a_1338_, v_fst_1339_, v_snd_1340_, v_fst_1341_, v___x_1342_, v_a_1343_, v_b_1344_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_);
lean_dec(v___y_1348_);
lean_dec_ref(v___y_1347_);
lean_dec(v___y_1346_);
lean_dec_ref(v___y_1345_);
lean_dec_ref(v___x_1342_);
lean_dec_ref(v_snd_1340_);
lean_dec(v_upperBound_1337_);
return v_res_1350_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__4___redArg(lean_object* v___x_1351_, lean_object* v___x_1352_, lean_object* v_a_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_){
_start:
{
lean_object* v_fst_1361_; lean_object* v_snd_1362_; lean_object* v___x_1364_; uint8_t v_isShared_1365_; uint8_t v_isSharedCheck_1428_; 
v_fst_1361_ = lean_ctor_get(v_a_1353_, 0);
v_snd_1362_ = lean_ctor_get(v_a_1353_, 1);
v_isSharedCheck_1428_ = !lean_is_exclusive(v_a_1353_);
if (v_isSharedCheck_1428_ == 0)
{
v___x_1364_ = v_a_1353_;
v_isShared_1365_ = v_isSharedCheck_1428_;
goto v_resetjp_1363_;
}
else
{
lean_inc(v_snd_1362_);
lean_inc(v_fst_1361_);
lean_dec(v_a_1353_);
v___x_1364_ = lean_box(0);
v_isShared_1365_ = v_isSharedCheck_1428_;
goto v_resetjp_1363_;
}
v_resetjp_1363_:
{
lean_object* v___x_1366_; lean_object* v___x_1367_; uint8_t v___x_1368_; 
v___x_1366_ = lean_unsigned_to_nat(0u);
v___x_1367_ = lean_array_get_size(v_fst_1361_);
v___x_1368_ = lean_nat_dec_lt(v___x_1366_, v___x_1367_);
if (v___x_1368_ == 0)
{
lean_object* v___x_1370_; 
lean_dec_ref(v___x_1351_);
if (v_isShared_1365_ == 0)
{
v___x_1370_ = v___x_1364_;
goto v_reusejp_1369_;
}
else
{
lean_object* v_reuseFailAlloc_1372_; 
v_reuseFailAlloc_1372_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1372_, 0, v_fst_1361_);
lean_ctor_set(v_reuseFailAlloc_1372_, 1, v_snd_1362_);
v___x_1370_ = v_reuseFailAlloc_1372_;
goto v_reusejp_1369_;
}
v_reusejp_1369_:
{
lean_object* v___x_1371_; 
v___x_1371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1371_, 0, v___x_1370_);
return v___x_1371_;
}
}
else
{
lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v_snd_1376_; lean_object* v_snd_1377_; lean_object* v_fst_1378_; lean_object* v_fst_1379_; lean_object* v_fst_1380_; lean_object* v_snd_1381_; lean_object* v___x_1383_; uint8_t v_isShared_1384_; uint8_t v_isSharedCheck_1427_; 
lean_del_object(v___x_1364_);
v___x_1373_ = lean_unsigned_to_nat(1u);
v___x_1374_ = lean_nat_sub(v___x_1367_, v___x_1373_);
v___x_1375_ = lean_array_fget_borrowed(v_fst_1361_, v___x_1374_);
lean_dec(v___x_1374_);
v_snd_1376_ = lean_ctor_get(v___x_1375_, 1);
v_snd_1377_ = lean_ctor_get(v_snd_1376_, 1);
lean_inc(v_snd_1377_);
v_fst_1378_ = lean_ctor_get(v___x_1375_, 0);
lean_inc(v_fst_1378_);
v_fst_1379_ = lean_ctor_get(v_snd_1376_, 0);
v_fst_1380_ = lean_ctor_get(v_snd_1377_, 0);
v_snd_1381_ = lean_ctor_get(v_snd_1377_, 1);
v_isSharedCheck_1427_ = !lean_is_exclusive(v_snd_1377_);
if (v_isSharedCheck_1427_ == 0)
{
v___x_1383_ = v_snd_1377_;
v_isShared_1384_ = v_isSharedCheck_1427_;
goto v_resetjp_1382_;
}
else
{
lean_inc(v_snd_1381_);
lean_inc(v_fst_1380_);
lean_dec(v_snd_1377_);
v___x_1383_ = lean_box(0);
v_isShared_1384_ = v_isSharedCheck_1427_;
goto v_resetjp_1382_;
}
v_resetjp_1382_:
{
lean_object* v___x_1385_; lean_object* v___x_1386_; 
lean_inc_n(v_fst_1379_, 2);
lean_inc_ref(v___x_1351_);
v___x_1385_ = l_Lean_getStructureInfo(v___x_1351_, v_fst_1379_);
v___x_1386_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__0(v_fst_1379_, v___y_1354_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_, v___y_1359_);
if (lean_obj_tag(v___x_1386_) == 0)
{
lean_object* v_a_1387_; lean_object* v_ctors_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; 
v_a_1387_ = lean_ctor_get(v___x_1386_, 0);
lean_inc(v_a_1387_);
lean_dec_ref_known(v___x_1386_, 1);
v_ctors_1388_ = lean_ctor_get(v_a_1387_, 4);
lean_inc(v_ctors_1388_);
lean_dec(v_a_1387_);
v___x_1389_ = lean_box(0);
v___x_1390_ = l_List_head_x21___redArg(v___x_1389_, v_ctors_1388_);
lean_dec(v_ctors_1388_);
v___x_1391_ = l_Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__2(v___x_1390_, v___y_1354_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_, v___y_1359_);
if (lean_obj_tag(v___x_1391_) == 0)
{
lean_object* v_a_1392_; lean_object* v_fieldNames_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1397_; 
v_a_1392_ = lean_ctor_get(v___x_1391_, 0);
lean_inc(v_a_1392_);
lean_dec_ref_known(v___x_1391_, 1);
v_fieldNames_1393_ = lean_ctor_get(v___x_1385_, 1);
lean_inc_ref(v_fieldNames_1393_);
lean_dec_ref(v___x_1385_);
v___x_1394_ = lean_array_get_size(v_fieldNames_1393_);
lean_dec_ref(v_fieldNames_1393_);
v___x_1395_ = lean_array_pop(v_fst_1361_);
if (v_isShared_1384_ == 0)
{
lean_ctor_set(v___x_1383_, 1, v_snd_1362_);
lean_ctor_set(v___x_1383_, 0, v___x_1395_);
v___x_1397_ = v___x_1383_;
goto v_reusejp_1396_;
}
else
{
lean_object* v_reuseFailAlloc_1410_; 
v_reuseFailAlloc_1410_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1410_, 0, v___x_1395_);
lean_ctor_set(v_reuseFailAlloc_1410_, 1, v_snd_1362_);
v___x_1397_ = v_reuseFailAlloc_1410_;
goto v_reusejp_1396_;
}
v_reusejp_1396_:
{
lean_object* v___x_1398_; 
v___x_1398_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__3___redArg(v___x_1394_, v_a_1392_, v_fst_1380_, v_snd_1381_, v_fst_1378_, v___x_1352_, v___x_1366_, v___x_1397_, v___y_1356_, v___y_1357_, v___y_1358_, v___y_1359_);
lean_dec(v_snd_1381_);
if (lean_obj_tag(v___x_1398_) == 0)
{
lean_object* v_a_1399_; lean_object* v_fst_1400_; lean_object* v_snd_1401_; lean_object* v___x_1403_; uint8_t v_isShared_1404_; uint8_t v_isSharedCheck_1409_; 
v_a_1399_ = lean_ctor_get(v___x_1398_, 0);
lean_inc(v_a_1399_);
lean_dec_ref_known(v___x_1398_, 1);
v_fst_1400_ = lean_ctor_get(v_a_1399_, 0);
v_snd_1401_ = lean_ctor_get(v_a_1399_, 1);
v_isSharedCheck_1409_ = !lean_is_exclusive(v_a_1399_);
if (v_isSharedCheck_1409_ == 0)
{
v___x_1403_ = v_a_1399_;
v_isShared_1404_ = v_isSharedCheck_1409_;
goto v_resetjp_1402_;
}
else
{
lean_inc(v_snd_1401_);
lean_inc(v_fst_1400_);
lean_dec(v_a_1399_);
v___x_1403_ = lean_box(0);
v_isShared_1404_ = v_isSharedCheck_1409_;
goto v_resetjp_1402_;
}
v_resetjp_1402_:
{
lean_object* v___x_1406_; 
if (v_isShared_1404_ == 0)
{
v___x_1406_ = v___x_1403_;
goto v_reusejp_1405_;
}
else
{
lean_object* v_reuseFailAlloc_1408_; 
v_reuseFailAlloc_1408_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1408_, 0, v_fst_1400_);
lean_ctor_set(v_reuseFailAlloc_1408_, 1, v_snd_1401_);
v___x_1406_ = v_reuseFailAlloc_1408_;
goto v_reusejp_1405_;
}
v_reusejp_1405_:
{
v_a_1353_ = v___x_1406_;
goto _start;
}
}
}
else
{
lean_dec_ref(v___x_1351_);
return v___x_1398_;
}
}
}
else
{
lean_object* v_a_1411_; lean_object* v___x_1413_; uint8_t v_isShared_1414_; uint8_t v_isSharedCheck_1418_; 
lean_dec_ref(v___x_1385_);
lean_del_object(v___x_1383_);
lean_dec(v_snd_1381_);
lean_dec(v_fst_1380_);
lean_dec(v_fst_1378_);
lean_dec(v_snd_1362_);
lean_dec(v_fst_1361_);
lean_dec_ref(v___x_1351_);
v_a_1411_ = lean_ctor_get(v___x_1391_, 0);
v_isSharedCheck_1418_ = !lean_is_exclusive(v___x_1391_);
if (v_isSharedCheck_1418_ == 0)
{
v___x_1413_ = v___x_1391_;
v_isShared_1414_ = v_isSharedCheck_1418_;
goto v_resetjp_1412_;
}
else
{
lean_inc(v_a_1411_);
lean_dec(v___x_1391_);
v___x_1413_ = lean_box(0);
v_isShared_1414_ = v_isSharedCheck_1418_;
goto v_resetjp_1412_;
}
v_resetjp_1412_:
{
lean_object* v___x_1416_; 
if (v_isShared_1414_ == 0)
{
v___x_1416_ = v___x_1413_;
goto v_reusejp_1415_;
}
else
{
lean_object* v_reuseFailAlloc_1417_; 
v_reuseFailAlloc_1417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1417_, 0, v_a_1411_);
v___x_1416_ = v_reuseFailAlloc_1417_;
goto v_reusejp_1415_;
}
v_reusejp_1415_:
{
return v___x_1416_;
}
}
}
}
else
{
lean_object* v_a_1419_; lean_object* v___x_1421_; uint8_t v_isShared_1422_; uint8_t v_isSharedCheck_1426_; 
lean_dec_ref(v___x_1385_);
lean_del_object(v___x_1383_);
lean_dec(v_snd_1381_);
lean_dec(v_fst_1380_);
lean_dec(v_fst_1378_);
lean_dec(v_snd_1362_);
lean_dec(v_fst_1361_);
lean_dec_ref(v___x_1351_);
v_a_1419_ = lean_ctor_get(v___x_1386_, 0);
v_isSharedCheck_1426_ = !lean_is_exclusive(v___x_1386_);
if (v_isSharedCheck_1426_ == 0)
{
v___x_1421_ = v___x_1386_;
v_isShared_1422_ = v_isSharedCheck_1426_;
goto v_resetjp_1420_;
}
else
{
lean_inc(v_a_1419_);
lean_dec(v___x_1386_);
v___x_1421_ = lean_box(0);
v_isShared_1422_ = v_isSharedCheck_1426_;
goto v_resetjp_1420_;
}
v_resetjp_1420_:
{
lean_object* v___x_1424_; 
if (v_isShared_1422_ == 0)
{
v___x_1424_ = v___x_1421_;
goto v_reusejp_1423_;
}
else
{
lean_object* v_reuseFailAlloc_1425_; 
v_reuseFailAlloc_1425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1425_, 0, v_a_1419_);
v___x_1424_ = v_reuseFailAlloc_1425_;
goto v_reusejp_1423_;
}
v_reusejp_1423_:
{
return v___x_1424_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__4___redArg___boxed(lean_object* v___x_1429_, lean_object* v___x_1430_, lean_object* v_a_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_){
_start:
{
lean_object* v_res_1439_; 
v_res_1439_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__4___redArg(v___x_1429_, v___x_1430_, v_a_1431_, v___y_1432_, v___y_1433_, v___y_1434_, v___y_1435_, v___y_1436_, v___y_1437_);
lean_dec(v___y_1437_);
lean_dec_ref(v___y_1436_);
lean_dec(v___y_1435_);
lean_dec_ref(v___y_1434_);
lean_dec(v___y_1433_);
lean_dec_ref(v___y_1432_);
lean_dec_ref(v___x_1430_);
return v_res_1439_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__1_spec__3_spec__6___redArg(lean_object* v___x_1440_, lean_object* v___x_1441_, lean_object* v_as_1442_, size_t v_sz_1443_, size_t v_i_1444_, lean_object* v_b_1445_){
_start:
{
uint8_t v___x_1447_; 
v___x_1447_ = lean_usize_dec_lt(v_i_1444_, v_sz_1443_);
if (v___x_1447_ == 0)
{
lean_object* v___x_1448_; 
v___x_1448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1448_, 0, v_b_1445_);
return v___x_1448_;
}
else
{
lean_object* v_snd_1449_; lean_object* v___x_1451_; uint8_t v_isShared_1452_; uint8_t v_isSharedCheck_1485_; 
v_snd_1449_ = lean_ctor_get(v_b_1445_, 1);
v_isSharedCheck_1485_ = !lean_is_exclusive(v_b_1445_);
if (v_isSharedCheck_1485_ == 0)
{
lean_object* v_unused_1486_; 
v_unused_1486_ = lean_ctor_get(v_b_1445_, 0);
lean_dec(v_unused_1486_);
v___x_1451_ = v_b_1445_;
v_isShared_1452_ = v_isSharedCheck_1485_;
goto v_resetjp_1450_;
}
else
{
lean_inc(v_snd_1449_);
lean_dec(v_b_1445_);
v___x_1451_ = lean_box(0);
v_isShared_1452_ = v_isSharedCheck_1485_;
goto v_resetjp_1450_;
}
v_resetjp_1450_:
{
lean_object* v___x_1453_; lean_object* v_a_1455_; lean_object* v_a_1462_; 
v___x_1453_ = lean_box(0);
v_a_1462_ = lean_array_uget_borrowed(v_as_1442_, v_i_1444_);
if (lean_obj_tag(v_a_1462_) == 0)
{
v_a_1455_ = v_snd_1449_;
goto v___jp_1454_;
}
else
{
lean_object* v_val_1463_; lean_object* v___x_1464_; uint8_t v___x_1465_; uint8_t v___x_1466_; 
v_val_1463_ = lean_ctor_get(v_a_1462_, 0);
v___x_1464_ = lean_unsigned_to_nat(0u);
v___x_1465_ = lean_nat_dec_eq(v___x_1440_, v___x_1464_);
v___x_1466_ = l_Lean_LocalDecl_isLet(v_val_1463_, v___x_1465_);
if (v___x_1466_ == 0)
{
uint8_t v___x_1467_; 
v___x_1467_ = l_Lean_LocalDecl_isImplementationDetail(v_val_1463_);
if (v___x_1467_ == 0)
{
lean_object* v___x_1468_; lean_object* v___x_1469_; 
v___x_1468_ = l_Lean_LocalDecl_type(v_val_1463_);
v___x_1469_ = l_Lean_Expr_getAppFn(v___x_1468_);
if (lean_obj_tag(v___x_1469_) == 4)
{
lean_object* v_declName_1470_; lean_object* v_us_1471_; uint8_t v___x_1472_; 
v_declName_1470_ = lean_ctor_get(v___x_1469_, 0);
lean_inc(v_declName_1470_);
v_us_1471_ = lean_ctor_get(v___x_1469_, 1);
lean_inc(v_us_1471_);
lean_dec_ref_known(v___x_1469_, 2);
v___x_1472_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__0___redArg(v___x_1441_, v_declName_1470_);
if (v___x_1472_ == 0)
{
lean_dec(v_us_1471_);
lean_dec(v_declName_1470_);
lean_dec_ref(v___x_1468_);
v_a_1455_ = v_snd_1449_;
goto v___jp_1454_;
}
else
{
lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v_dummy_1475_; lean_object* v_nargs_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; 
v___x_1473_ = l_Lean_LocalDecl_fvarId(v_val_1463_);
v___x_1474_ = l_Lean_mkFVar(v___x_1473_);
v_dummy_1475_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__3___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__3___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__3___redArg___closed__0);
v_nargs_1476_ = l_Lean_Expr_getAppNumArgs(v___x_1468_);
lean_inc(v_nargs_1476_);
v___x_1477_ = lean_mk_array(v_nargs_1476_, v_dummy_1475_);
v___x_1478_ = lean_unsigned_to_nat(1u);
v___x_1479_ = lean_nat_sub(v_nargs_1476_, v___x_1478_);
lean_dec(v_nargs_1476_);
v___x_1480_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v___x_1468_, v___x_1477_, v___x_1479_);
v___x_1481_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1481_, 0, v_us_1471_);
lean_ctor_set(v___x_1481_, 1, v___x_1480_);
v___x_1482_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1482_, 0, v_declName_1470_);
lean_ctor_set(v___x_1482_, 1, v___x_1481_);
v___x_1483_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1483_, 0, v___x_1474_);
lean_ctor_set(v___x_1483_, 1, v___x_1482_);
v___x_1484_ = lean_array_push(v_snd_1449_, v___x_1483_);
v_a_1455_ = v___x_1484_;
goto v___jp_1454_;
}
}
else
{
lean_dec_ref(v___x_1469_);
lean_dec_ref(v___x_1468_);
v_a_1455_ = v_snd_1449_;
goto v___jp_1454_;
}
}
else
{
v_a_1455_ = v_snd_1449_;
goto v___jp_1454_;
}
}
else
{
v_a_1455_ = v_snd_1449_;
goto v___jp_1454_;
}
}
v___jp_1454_:
{
lean_object* v___x_1457_; 
if (v_isShared_1452_ == 0)
{
lean_ctor_set(v___x_1451_, 1, v_a_1455_);
lean_ctor_set(v___x_1451_, 0, v___x_1453_);
v___x_1457_ = v___x_1451_;
goto v_reusejp_1456_;
}
else
{
lean_object* v_reuseFailAlloc_1461_; 
v_reuseFailAlloc_1461_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1461_, 0, v___x_1453_);
lean_ctor_set(v_reuseFailAlloc_1461_, 1, v_a_1455_);
v___x_1457_ = v_reuseFailAlloc_1461_;
goto v_reusejp_1456_;
}
v_reusejp_1456_:
{
size_t v___x_1458_; size_t v___x_1459_; 
v___x_1458_ = ((size_t)1ULL);
v___x_1459_ = lean_usize_add(v_i_1444_, v___x_1458_);
v_i_1444_ = v___x_1459_;
v_b_1445_ = v___x_1457_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__1_spec__3_spec__6___redArg___boxed(lean_object* v___x_1487_, lean_object* v___x_1488_, lean_object* v_as_1489_, lean_object* v_sz_1490_, lean_object* v_i_1491_, lean_object* v_b_1492_, lean_object* v___y_1493_){
_start:
{
size_t v_sz_boxed_1494_; size_t v_i_boxed_1495_; lean_object* v_res_1496_; 
v_sz_boxed_1494_ = lean_unbox_usize(v_sz_1490_);
lean_dec(v_sz_1490_);
v_i_boxed_1495_ = lean_unbox_usize(v_i_1491_);
lean_dec(v_i_1491_);
v_res_1496_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__1_spec__3_spec__6___redArg(v___x_1487_, v___x_1488_, v_as_1489_, v_sz_boxed_1494_, v_i_boxed_1495_, v_b_1492_);
lean_dec_ref(v_as_1489_);
lean_dec_ref(v___x_1488_);
lean_dec(v___x_1487_);
return v_res_1496_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__1_spec__3(lean_object* v___x_1497_, lean_object* v___x_1498_, lean_object* v_as_1499_, size_t v_sz_1500_, size_t v_i_1501_, lean_object* v_b_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_){
_start:
{
uint8_t v___x_1510_; 
v___x_1510_ = lean_usize_dec_lt(v_i_1501_, v_sz_1500_);
if (v___x_1510_ == 0)
{
lean_object* v___x_1511_; 
v___x_1511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1511_, 0, v_b_1502_);
return v___x_1511_;
}
else
{
lean_object* v_snd_1512_; lean_object* v___x_1514_; uint8_t v_isShared_1515_; uint8_t v_isSharedCheck_1548_; 
v_snd_1512_ = lean_ctor_get(v_b_1502_, 1);
v_isSharedCheck_1548_ = !lean_is_exclusive(v_b_1502_);
if (v_isSharedCheck_1548_ == 0)
{
lean_object* v_unused_1549_; 
v_unused_1549_ = lean_ctor_get(v_b_1502_, 0);
lean_dec(v_unused_1549_);
v___x_1514_ = v_b_1502_;
v_isShared_1515_ = v_isSharedCheck_1548_;
goto v_resetjp_1513_;
}
else
{
lean_inc(v_snd_1512_);
lean_dec(v_b_1502_);
v___x_1514_ = lean_box(0);
v_isShared_1515_ = v_isSharedCheck_1548_;
goto v_resetjp_1513_;
}
v_resetjp_1513_:
{
lean_object* v___x_1516_; lean_object* v_a_1518_; lean_object* v_a_1525_; 
v___x_1516_ = lean_box(0);
v_a_1525_ = lean_array_uget_borrowed(v_as_1499_, v_i_1501_);
if (lean_obj_tag(v_a_1525_) == 0)
{
v_a_1518_ = v_snd_1512_;
goto v___jp_1517_;
}
else
{
lean_object* v_val_1526_; lean_object* v___x_1527_; uint8_t v___x_1528_; uint8_t v___x_1529_; 
v_val_1526_ = lean_ctor_get(v_a_1525_, 0);
v___x_1527_ = lean_unsigned_to_nat(0u);
v___x_1528_ = lean_nat_dec_eq(v___x_1497_, v___x_1527_);
v___x_1529_ = l_Lean_LocalDecl_isLet(v_val_1526_, v___x_1528_);
if (v___x_1529_ == 0)
{
uint8_t v___x_1530_; 
v___x_1530_ = l_Lean_LocalDecl_isImplementationDetail(v_val_1526_);
if (v___x_1530_ == 0)
{
lean_object* v___x_1531_; lean_object* v___x_1532_; 
v___x_1531_ = l_Lean_LocalDecl_type(v_val_1526_);
v___x_1532_ = l_Lean_Expr_getAppFn(v___x_1531_);
if (lean_obj_tag(v___x_1532_) == 4)
{
lean_object* v_declName_1533_; lean_object* v_us_1534_; uint8_t v___x_1535_; 
v_declName_1533_ = lean_ctor_get(v___x_1532_, 0);
lean_inc(v_declName_1533_);
v_us_1534_ = lean_ctor_get(v___x_1532_, 1);
lean_inc(v_us_1534_);
lean_dec_ref_known(v___x_1532_, 2);
v___x_1535_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__0___redArg(v___x_1498_, v_declName_1533_);
if (v___x_1535_ == 0)
{
lean_dec(v_us_1534_);
lean_dec(v_declName_1533_);
lean_dec_ref(v___x_1531_);
v_a_1518_ = v_snd_1512_;
goto v___jp_1517_;
}
else
{
lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v_dummy_1538_; lean_object* v_nargs_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; 
v___x_1536_ = l_Lean_LocalDecl_fvarId(v_val_1526_);
v___x_1537_ = l_Lean_mkFVar(v___x_1536_);
v_dummy_1538_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__3___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__3___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__3___redArg___closed__0);
v_nargs_1539_ = l_Lean_Expr_getAppNumArgs(v___x_1531_);
lean_inc(v_nargs_1539_);
v___x_1540_ = lean_mk_array(v_nargs_1539_, v_dummy_1538_);
v___x_1541_ = lean_unsigned_to_nat(1u);
v___x_1542_ = lean_nat_sub(v_nargs_1539_, v___x_1541_);
lean_dec(v_nargs_1539_);
v___x_1543_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v___x_1531_, v___x_1540_, v___x_1542_);
v___x_1544_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1544_, 0, v_us_1534_);
lean_ctor_set(v___x_1544_, 1, v___x_1543_);
v___x_1545_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1545_, 0, v_declName_1533_);
lean_ctor_set(v___x_1545_, 1, v___x_1544_);
v___x_1546_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1546_, 0, v___x_1537_);
lean_ctor_set(v___x_1546_, 1, v___x_1545_);
v___x_1547_ = lean_array_push(v_snd_1512_, v___x_1546_);
v_a_1518_ = v___x_1547_;
goto v___jp_1517_;
}
}
else
{
lean_dec_ref(v___x_1532_);
lean_dec_ref(v___x_1531_);
v_a_1518_ = v_snd_1512_;
goto v___jp_1517_;
}
}
else
{
v_a_1518_ = v_snd_1512_;
goto v___jp_1517_;
}
}
else
{
v_a_1518_ = v_snd_1512_;
goto v___jp_1517_;
}
}
v___jp_1517_:
{
lean_object* v___x_1520_; 
if (v_isShared_1515_ == 0)
{
lean_ctor_set(v___x_1514_, 1, v_a_1518_);
lean_ctor_set(v___x_1514_, 0, v___x_1516_);
v___x_1520_ = v___x_1514_;
goto v_reusejp_1519_;
}
else
{
lean_object* v_reuseFailAlloc_1524_; 
v_reuseFailAlloc_1524_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1524_, 0, v___x_1516_);
lean_ctor_set(v_reuseFailAlloc_1524_, 1, v_a_1518_);
v___x_1520_ = v_reuseFailAlloc_1524_;
goto v_reusejp_1519_;
}
v_reusejp_1519_:
{
size_t v___x_1521_; size_t v___x_1522_; lean_object* v___x_1523_; 
v___x_1521_ = ((size_t)1ULL);
v___x_1522_ = lean_usize_add(v_i_1501_, v___x_1521_);
v___x_1523_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__1_spec__3_spec__6___redArg(v___x_1497_, v___x_1498_, v_as_1499_, v_sz_1500_, v___x_1522_, v___x_1520_);
return v___x_1523_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__1_spec__3___boxed(lean_object* v___x_1550_, lean_object* v___x_1551_, lean_object* v_as_1552_, lean_object* v_sz_1553_, lean_object* v_i_1554_, lean_object* v_b_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_){
_start:
{
size_t v_sz_boxed_1563_; size_t v_i_boxed_1564_; lean_object* v_res_1565_; 
v_sz_boxed_1563_ = lean_unbox_usize(v_sz_1553_);
lean_dec(v_sz_1553_);
v_i_boxed_1564_ = lean_unbox_usize(v_i_1554_);
lean_dec(v_i_1554_);
v_res_1565_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__1_spec__3(v___x_1550_, v___x_1551_, v_as_1552_, v_sz_boxed_1563_, v_i_boxed_1564_, v_b_1555_, v___y_1556_, v___y_1557_, v___y_1558_, v___y_1559_, v___y_1560_, v___y_1561_);
lean_dec(v___y_1561_);
lean_dec_ref(v___y_1560_);
lean_dec(v___y_1559_);
lean_dec_ref(v___y_1558_);
lean_dec(v___y_1557_);
lean_dec_ref(v___y_1556_);
lean_dec_ref(v_as_1552_);
lean_dec_ref(v___x_1551_);
lean_dec(v___x_1550_);
return v_res_1565_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__1_spec__2_spec__4_spec__9___redArg(lean_object* v___x_1566_, lean_object* v___x_1567_, lean_object* v_as_1568_, size_t v_sz_1569_, size_t v_i_1570_, lean_object* v_b_1571_){
_start:
{
uint8_t v___x_1573_; 
v___x_1573_ = lean_usize_dec_lt(v_i_1570_, v_sz_1569_);
if (v___x_1573_ == 0)
{
lean_object* v___x_1574_; 
v___x_1574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1574_, 0, v_b_1571_);
return v___x_1574_;
}
else
{
lean_object* v_snd_1575_; lean_object* v___x_1577_; uint8_t v_isShared_1578_; uint8_t v_isSharedCheck_1611_; 
v_snd_1575_ = lean_ctor_get(v_b_1571_, 1);
v_isSharedCheck_1611_ = !lean_is_exclusive(v_b_1571_);
if (v_isSharedCheck_1611_ == 0)
{
lean_object* v_unused_1612_; 
v_unused_1612_ = lean_ctor_get(v_b_1571_, 0);
lean_dec(v_unused_1612_);
v___x_1577_ = v_b_1571_;
v_isShared_1578_ = v_isSharedCheck_1611_;
goto v_resetjp_1576_;
}
else
{
lean_inc(v_snd_1575_);
lean_dec(v_b_1571_);
v___x_1577_ = lean_box(0);
v_isShared_1578_ = v_isSharedCheck_1611_;
goto v_resetjp_1576_;
}
v_resetjp_1576_:
{
lean_object* v___x_1579_; lean_object* v_a_1581_; lean_object* v_a_1588_; 
v___x_1579_ = lean_box(0);
v_a_1588_ = lean_array_uget_borrowed(v_as_1568_, v_i_1570_);
if (lean_obj_tag(v_a_1588_) == 0)
{
v_a_1581_ = v_snd_1575_;
goto v___jp_1580_;
}
else
{
lean_object* v_val_1589_; lean_object* v___x_1590_; uint8_t v___x_1591_; uint8_t v___x_1592_; 
v_val_1589_ = lean_ctor_get(v_a_1588_, 0);
v___x_1590_ = lean_unsigned_to_nat(0u);
v___x_1591_ = lean_nat_dec_eq(v___x_1566_, v___x_1590_);
v___x_1592_ = l_Lean_LocalDecl_isLet(v_val_1589_, v___x_1591_);
if (v___x_1592_ == 0)
{
uint8_t v___x_1593_; 
v___x_1593_ = l_Lean_LocalDecl_isImplementationDetail(v_val_1589_);
if (v___x_1593_ == 0)
{
lean_object* v___x_1594_; lean_object* v___x_1595_; 
v___x_1594_ = l_Lean_LocalDecl_type(v_val_1589_);
v___x_1595_ = l_Lean_Expr_getAppFn(v___x_1594_);
if (lean_obj_tag(v___x_1595_) == 4)
{
lean_object* v_declName_1596_; lean_object* v_us_1597_; uint8_t v___x_1598_; 
v_declName_1596_ = lean_ctor_get(v___x_1595_, 0);
lean_inc(v_declName_1596_);
v_us_1597_ = lean_ctor_get(v___x_1595_, 1);
lean_inc(v_us_1597_);
lean_dec_ref_known(v___x_1595_, 2);
v___x_1598_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__0___redArg(v___x_1567_, v_declName_1596_);
if (v___x_1598_ == 0)
{
lean_dec(v_us_1597_);
lean_dec(v_declName_1596_);
lean_dec_ref(v___x_1594_);
v_a_1581_ = v_snd_1575_;
goto v___jp_1580_;
}
else
{
lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v_dummy_1601_; lean_object* v_nargs_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; 
v___x_1599_ = l_Lean_LocalDecl_fvarId(v_val_1589_);
v___x_1600_ = l_Lean_mkFVar(v___x_1599_);
v_dummy_1601_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__3___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__3___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__3___redArg___closed__0);
v_nargs_1602_ = l_Lean_Expr_getAppNumArgs(v___x_1594_);
lean_inc(v_nargs_1602_);
v___x_1603_ = lean_mk_array(v_nargs_1602_, v_dummy_1601_);
v___x_1604_ = lean_unsigned_to_nat(1u);
v___x_1605_ = lean_nat_sub(v_nargs_1602_, v___x_1604_);
lean_dec(v_nargs_1602_);
v___x_1606_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v___x_1594_, v___x_1603_, v___x_1605_);
v___x_1607_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1607_, 0, v_us_1597_);
lean_ctor_set(v___x_1607_, 1, v___x_1606_);
v___x_1608_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1608_, 0, v_declName_1596_);
lean_ctor_set(v___x_1608_, 1, v___x_1607_);
v___x_1609_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1609_, 0, v___x_1600_);
lean_ctor_set(v___x_1609_, 1, v___x_1608_);
v___x_1610_ = lean_array_push(v_snd_1575_, v___x_1609_);
v_a_1581_ = v___x_1610_;
goto v___jp_1580_;
}
}
else
{
lean_dec_ref(v___x_1595_);
lean_dec_ref(v___x_1594_);
v_a_1581_ = v_snd_1575_;
goto v___jp_1580_;
}
}
else
{
v_a_1581_ = v_snd_1575_;
goto v___jp_1580_;
}
}
else
{
v_a_1581_ = v_snd_1575_;
goto v___jp_1580_;
}
}
v___jp_1580_:
{
lean_object* v___x_1583_; 
if (v_isShared_1578_ == 0)
{
lean_ctor_set(v___x_1577_, 1, v_a_1581_);
lean_ctor_set(v___x_1577_, 0, v___x_1579_);
v___x_1583_ = v___x_1577_;
goto v_reusejp_1582_;
}
else
{
lean_object* v_reuseFailAlloc_1587_; 
v_reuseFailAlloc_1587_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1587_, 0, v___x_1579_);
lean_ctor_set(v_reuseFailAlloc_1587_, 1, v_a_1581_);
v___x_1583_ = v_reuseFailAlloc_1587_;
goto v_reusejp_1582_;
}
v_reusejp_1582_:
{
size_t v___x_1584_; size_t v___x_1585_; 
v___x_1584_ = ((size_t)1ULL);
v___x_1585_ = lean_usize_add(v_i_1570_, v___x_1584_);
v_i_1570_ = v___x_1585_;
v_b_1571_ = v___x_1583_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__1_spec__2_spec__4_spec__9___redArg___boxed(lean_object* v___x_1613_, lean_object* v___x_1614_, lean_object* v_as_1615_, lean_object* v_sz_1616_, lean_object* v_i_1617_, lean_object* v_b_1618_, lean_object* v___y_1619_){
_start:
{
size_t v_sz_boxed_1620_; size_t v_i_boxed_1621_; lean_object* v_res_1622_; 
v_sz_boxed_1620_ = lean_unbox_usize(v_sz_1616_);
lean_dec(v_sz_1616_);
v_i_boxed_1621_ = lean_unbox_usize(v_i_1617_);
lean_dec(v_i_1617_);
v_res_1622_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__1_spec__2_spec__4_spec__9___redArg(v___x_1613_, v___x_1614_, v_as_1615_, v_sz_boxed_1620_, v_i_boxed_1621_, v_b_1618_);
lean_dec_ref(v_as_1615_);
lean_dec_ref(v___x_1614_);
lean_dec(v___x_1613_);
return v_res_1622_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__1_spec__2_spec__4(lean_object* v___x_1623_, lean_object* v___x_1624_, lean_object* v_as_1625_, size_t v_sz_1626_, size_t v_i_1627_, lean_object* v_b_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_){
_start:
{
uint8_t v___x_1636_; 
v___x_1636_ = lean_usize_dec_lt(v_i_1627_, v_sz_1626_);
if (v___x_1636_ == 0)
{
lean_object* v___x_1637_; 
v___x_1637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1637_, 0, v_b_1628_);
return v___x_1637_;
}
else
{
lean_object* v_snd_1638_; lean_object* v___x_1640_; uint8_t v_isShared_1641_; uint8_t v_isSharedCheck_1674_; 
v_snd_1638_ = lean_ctor_get(v_b_1628_, 1);
v_isSharedCheck_1674_ = !lean_is_exclusive(v_b_1628_);
if (v_isSharedCheck_1674_ == 0)
{
lean_object* v_unused_1675_; 
v_unused_1675_ = lean_ctor_get(v_b_1628_, 0);
lean_dec(v_unused_1675_);
v___x_1640_ = v_b_1628_;
v_isShared_1641_ = v_isSharedCheck_1674_;
goto v_resetjp_1639_;
}
else
{
lean_inc(v_snd_1638_);
lean_dec(v_b_1628_);
v___x_1640_ = lean_box(0);
v_isShared_1641_ = v_isSharedCheck_1674_;
goto v_resetjp_1639_;
}
v_resetjp_1639_:
{
lean_object* v___x_1642_; lean_object* v_a_1644_; lean_object* v_a_1651_; 
v___x_1642_ = lean_box(0);
v_a_1651_ = lean_array_uget_borrowed(v_as_1625_, v_i_1627_);
if (lean_obj_tag(v_a_1651_) == 0)
{
v_a_1644_ = v_snd_1638_;
goto v___jp_1643_;
}
else
{
lean_object* v_val_1652_; lean_object* v___x_1653_; uint8_t v___x_1654_; uint8_t v___x_1655_; 
v_val_1652_ = lean_ctor_get(v_a_1651_, 0);
v___x_1653_ = lean_unsigned_to_nat(0u);
v___x_1654_ = lean_nat_dec_eq(v___x_1623_, v___x_1653_);
v___x_1655_ = l_Lean_LocalDecl_isLet(v_val_1652_, v___x_1654_);
if (v___x_1655_ == 0)
{
uint8_t v___x_1656_; 
v___x_1656_ = l_Lean_LocalDecl_isImplementationDetail(v_val_1652_);
if (v___x_1656_ == 0)
{
lean_object* v___x_1657_; lean_object* v___x_1658_; 
v___x_1657_ = l_Lean_LocalDecl_type(v_val_1652_);
v___x_1658_ = l_Lean_Expr_getAppFn(v___x_1657_);
if (lean_obj_tag(v___x_1658_) == 4)
{
lean_object* v_declName_1659_; lean_object* v_us_1660_; uint8_t v___x_1661_; 
v_declName_1659_ = lean_ctor_get(v___x_1658_, 0);
lean_inc(v_declName_1659_);
v_us_1660_ = lean_ctor_get(v___x_1658_, 1);
lean_inc(v_us_1660_);
lean_dec_ref_known(v___x_1658_, 2);
v___x_1661_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__0___redArg(v___x_1624_, v_declName_1659_);
if (v___x_1661_ == 0)
{
lean_dec(v_us_1660_);
lean_dec(v_declName_1659_);
lean_dec_ref(v___x_1657_);
v_a_1644_ = v_snd_1638_;
goto v___jp_1643_;
}
else
{
lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v_dummy_1664_; lean_object* v_nargs_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; 
v___x_1662_ = l_Lean_LocalDecl_fvarId(v_val_1652_);
v___x_1663_ = l_Lean_mkFVar(v___x_1662_);
v_dummy_1664_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__3___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__3___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__3___redArg___closed__0);
v_nargs_1665_ = l_Lean_Expr_getAppNumArgs(v___x_1657_);
lean_inc(v_nargs_1665_);
v___x_1666_ = lean_mk_array(v_nargs_1665_, v_dummy_1664_);
v___x_1667_ = lean_unsigned_to_nat(1u);
v___x_1668_ = lean_nat_sub(v_nargs_1665_, v___x_1667_);
lean_dec(v_nargs_1665_);
v___x_1669_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v___x_1657_, v___x_1666_, v___x_1668_);
v___x_1670_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1670_, 0, v_us_1660_);
lean_ctor_set(v___x_1670_, 1, v___x_1669_);
v___x_1671_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1671_, 0, v_declName_1659_);
lean_ctor_set(v___x_1671_, 1, v___x_1670_);
v___x_1672_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1672_, 0, v___x_1663_);
lean_ctor_set(v___x_1672_, 1, v___x_1671_);
v___x_1673_ = lean_array_push(v_snd_1638_, v___x_1672_);
v_a_1644_ = v___x_1673_;
goto v___jp_1643_;
}
}
else
{
lean_dec_ref(v___x_1658_);
lean_dec_ref(v___x_1657_);
v_a_1644_ = v_snd_1638_;
goto v___jp_1643_;
}
}
else
{
v_a_1644_ = v_snd_1638_;
goto v___jp_1643_;
}
}
else
{
v_a_1644_ = v_snd_1638_;
goto v___jp_1643_;
}
}
v___jp_1643_:
{
lean_object* v___x_1646_; 
if (v_isShared_1641_ == 0)
{
lean_ctor_set(v___x_1640_, 1, v_a_1644_);
lean_ctor_set(v___x_1640_, 0, v___x_1642_);
v___x_1646_ = v___x_1640_;
goto v_reusejp_1645_;
}
else
{
lean_object* v_reuseFailAlloc_1650_; 
v_reuseFailAlloc_1650_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1650_, 0, v___x_1642_);
lean_ctor_set(v_reuseFailAlloc_1650_, 1, v_a_1644_);
v___x_1646_ = v_reuseFailAlloc_1650_;
goto v_reusejp_1645_;
}
v_reusejp_1645_:
{
size_t v___x_1647_; size_t v___x_1648_; lean_object* v___x_1649_; 
v___x_1647_ = ((size_t)1ULL);
v___x_1648_ = lean_usize_add(v_i_1627_, v___x_1647_);
v___x_1649_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__1_spec__2_spec__4_spec__9___redArg(v___x_1623_, v___x_1624_, v_as_1625_, v_sz_1626_, v___x_1648_, v___x_1646_);
return v___x_1649_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__1_spec__2_spec__4___boxed(lean_object* v___x_1676_, lean_object* v___x_1677_, lean_object* v_as_1678_, lean_object* v_sz_1679_, lean_object* v_i_1680_, lean_object* v_b_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_){
_start:
{
size_t v_sz_boxed_1689_; size_t v_i_boxed_1690_; lean_object* v_res_1691_; 
v_sz_boxed_1689_ = lean_unbox_usize(v_sz_1679_);
lean_dec(v_sz_1679_);
v_i_boxed_1690_ = lean_unbox_usize(v_i_1680_);
lean_dec(v_i_1680_);
v_res_1691_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__1_spec__2_spec__4(v___x_1676_, v___x_1677_, v_as_1678_, v_sz_boxed_1689_, v_i_boxed_1690_, v_b_1681_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_);
lean_dec(v___y_1687_);
lean_dec_ref(v___y_1686_);
lean_dec(v___y_1685_);
lean_dec_ref(v___y_1684_);
lean_dec(v___y_1683_);
lean_dec_ref(v___y_1682_);
lean_dec_ref(v_as_1678_);
lean_dec_ref(v___x_1677_);
lean_dec(v___x_1676_);
return v_res_1691_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__1_spec__2(lean_object* v_init_1692_, lean_object* v___x_1693_, lean_object* v___x_1694_, lean_object* v_n_1695_, lean_object* v_b_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_){
_start:
{
if (lean_obj_tag(v_n_1695_) == 0)
{
lean_object* v_cs_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; size_t v_sz_1707_; size_t v___x_1708_; lean_object* v___x_1709_; 
v_cs_1704_ = lean_ctor_get(v_n_1695_, 0);
v___x_1705_ = lean_box(0);
v___x_1706_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1706_, 0, v___x_1705_);
lean_ctor_set(v___x_1706_, 1, v_b_1696_);
v_sz_1707_ = lean_array_size(v_cs_1704_);
v___x_1708_ = ((size_t)0ULL);
v___x_1709_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__1_spec__2_spec__3(v_init_1692_, v___x_1693_, v___x_1694_, v_cs_1704_, v_sz_1707_, v___x_1708_, v___x_1706_, v___y_1697_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_);
if (lean_obj_tag(v___x_1709_) == 0)
{
lean_object* v_a_1710_; lean_object* v___x_1712_; uint8_t v_isShared_1713_; uint8_t v_isSharedCheck_1724_; 
v_a_1710_ = lean_ctor_get(v___x_1709_, 0);
v_isSharedCheck_1724_ = !lean_is_exclusive(v___x_1709_);
if (v_isSharedCheck_1724_ == 0)
{
v___x_1712_ = v___x_1709_;
v_isShared_1713_ = v_isSharedCheck_1724_;
goto v_resetjp_1711_;
}
else
{
lean_inc(v_a_1710_);
lean_dec(v___x_1709_);
v___x_1712_ = lean_box(0);
v_isShared_1713_ = v_isSharedCheck_1724_;
goto v_resetjp_1711_;
}
v_resetjp_1711_:
{
lean_object* v_fst_1714_; 
v_fst_1714_ = lean_ctor_get(v_a_1710_, 0);
if (lean_obj_tag(v_fst_1714_) == 0)
{
lean_object* v_snd_1715_; lean_object* v___x_1716_; lean_object* v___x_1718_; 
v_snd_1715_ = lean_ctor_get(v_a_1710_, 1);
lean_inc(v_snd_1715_);
lean_dec(v_a_1710_);
v___x_1716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1716_, 0, v_snd_1715_);
if (v_isShared_1713_ == 0)
{
lean_ctor_set(v___x_1712_, 0, v___x_1716_);
v___x_1718_ = v___x_1712_;
goto v_reusejp_1717_;
}
else
{
lean_object* v_reuseFailAlloc_1719_; 
v_reuseFailAlloc_1719_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1719_, 0, v___x_1716_);
v___x_1718_ = v_reuseFailAlloc_1719_;
goto v_reusejp_1717_;
}
v_reusejp_1717_:
{
return v___x_1718_;
}
}
else
{
lean_object* v_val_1720_; lean_object* v___x_1722_; 
lean_inc_ref(v_fst_1714_);
lean_dec(v_a_1710_);
v_val_1720_ = lean_ctor_get(v_fst_1714_, 0);
lean_inc(v_val_1720_);
lean_dec_ref_known(v_fst_1714_, 1);
if (v_isShared_1713_ == 0)
{
lean_ctor_set(v___x_1712_, 0, v_val_1720_);
v___x_1722_ = v___x_1712_;
goto v_reusejp_1721_;
}
else
{
lean_object* v_reuseFailAlloc_1723_; 
v_reuseFailAlloc_1723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1723_, 0, v_val_1720_);
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
else
{
lean_object* v_a_1725_; lean_object* v___x_1727_; uint8_t v_isShared_1728_; uint8_t v_isSharedCheck_1732_; 
v_a_1725_ = lean_ctor_get(v___x_1709_, 0);
v_isSharedCheck_1732_ = !lean_is_exclusive(v___x_1709_);
if (v_isSharedCheck_1732_ == 0)
{
v___x_1727_ = v___x_1709_;
v_isShared_1728_ = v_isSharedCheck_1732_;
goto v_resetjp_1726_;
}
else
{
lean_inc(v_a_1725_);
lean_dec(v___x_1709_);
v___x_1727_ = lean_box(0);
v_isShared_1728_ = v_isSharedCheck_1732_;
goto v_resetjp_1726_;
}
v_resetjp_1726_:
{
lean_object* v___x_1730_; 
if (v_isShared_1728_ == 0)
{
v___x_1730_ = v___x_1727_;
goto v_reusejp_1729_;
}
else
{
lean_object* v_reuseFailAlloc_1731_; 
v_reuseFailAlloc_1731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1731_, 0, v_a_1725_);
v___x_1730_ = v_reuseFailAlloc_1731_;
goto v_reusejp_1729_;
}
v_reusejp_1729_:
{
return v___x_1730_;
}
}
}
}
else
{
lean_object* v_vs_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; size_t v_sz_1736_; size_t v___x_1737_; lean_object* v___x_1738_; 
v_vs_1733_ = lean_ctor_get(v_n_1695_, 0);
v___x_1734_ = lean_box(0);
v___x_1735_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1735_, 0, v___x_1734_);
lean_ctor_set(v___x_1735_, 1, v_b_1696_);
v_sz_1736_ = lean_array_size(v_vs_1733_);
v___x_1737_ = ((size_t)0ULL);
v___x_1738_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__1_spec__2_spec__4(v___x_1693_, v___x_1694_, v_vs_1733_, v_sz_1736_, v___x_1737_, v___x_1735_, v___y_1697_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_);
if (lean_obj_tag(v___x_1738_) == 0)
{
lean_object* v_a_1739_; lean_object* v___x_1741_; uint8_t v_isShared_1742_; uint8_t v_isSharedCheck_1753_; 
v_a_1739_ = lean_ctor_get(v___x_1738_, 0);
v_isSharedCheck_1753_ = !lean_is_exclusive(v___x_1738_);
if (v_isSharedCheck_1753_ == 0)
{
v___x_1741_ = v___x_1738_;
v_isShared_1742_ = v_isSharedCheck_1753_;
goto v_resetjp_1740_;
}
else
{
lean_inc(v_a_1739_);
lean_dec(v___x_1738_);
v___x_1741_ = lean_box(0);
v_isShared_1742_ = v_isSharedCheck_1753_;
goto v_resetjp_1740_;
}
v_resetjp_1740_:
{
lean_object* v_fst_1743_; 
v_fst_1743_ = lean_ctor_get(v_a_1739_, 0);
if (lean_obj_tag(v_fst_1743_) == 0)
{
lean_object* v_snd_1744_; lean_object* v___x_1745_; lean_object* v___x_1747_; 
v_snd_1744_ = lean_ctor_get(v_a_1739_, 1);
lean_inc(v_snd_1744_);
lean_dec(v_a_1739_);
v___x_1745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1745_, 0, v_snd_1744_);
if (v_isShared_1742_ == 0)
{
lean_ctor_set(v___x_1741_, 0, v___x_1745_);
v___x_1747_ = v___x_1741_;
goto v_reusejp_1746_;
}
else
{
lean_object* v_reuseFailAlloc_1748_; 
v_reuseFailAlloc_1748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1748_, 0, v___x_1745_);
v___x_1747_ = v_reuseFailAlloc_1748_;
goto v_reusejp_1746_;
}
v_reusejp_1746_:
{
return v___x_1747_;
}
}
else
{
lean_object* v_val_1749_; lean_object* v___x_1751_; 
lean_inc_ref(v_fst_1743_);
lean_dec(v_a_1739_);
v_val_1749_ = lean_ctor_get(v_fst_1743_, 0);
lean_inc(v_val_1749_);
lean_dec_ref_known(v_fst_1743_, 1);
if (v_isShared_1742_ == 0)
{
lean_ctor_set(v___x_1741_, 0, v_val_1749_);
v___x_1751_ = v___x_1741_;
goto v_reusejp_1750_;
}
else
{
lean_object* v_reuseFailAlloc_1752_; 
v_reuseFailAlloc_1752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1752_, 0, v_val_1749_);
v___x_1751_ = v_reuseFailAlloc_1752_;
goto v_reusejp_1750_;
}
v_reusejp_1750_:
{
return v___x_1751_;
}
}
}
}
else
{
lean_object* v_a_1754_; lean_object* v___x_1756_; uint8_t v_isShared_1757_; uint8_t v_isSharedCheck_1761_; 
v_a_1754_ = lean_ctor_get(v___x_1738_, 0);
v_isSharedCheck_1761_ = !lean_is_exclusive(v___x_1738_);
if (v_isSharedCheck_1761_ == 0)
{
v___x_1756_ = v___x_1738_;
v_isShared_1757_ = v_isSharedCheck_1761_;
goto v_resetjp_1755_;
}
else
{
lean_inc(v_a_1754_);
lean_dec(v___x_1738_);
v___x_1756_ = lean_box(0);
v_isShared_1757_ = v_isSharedCheck_1761_;
goto v_resetjp_1755_;
}
v_resetjp_1755_:
{
lean_object* v___x_1759_; 
if (v_isShared_1757_ == 0)
{
v___x_1759_ = v___x_1756_;
goto v_reusejp_1758_;
}
else
{
lean_object* v_reuseFailAlloc_1760_; 
v_reuseFailAlloc_1760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1760_, 0, v_a_1754_);
v___x_1759_ = v_reuseFailAlloc_1760_;
goto v_reusejp_1758_;
}
v_reusejp_1758_:
{
return v___x_1759_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__1_spec__2_spec__3(lean_object* v_init_1762_, lean_object* v___x_1763_, lean_object* v___x_1764_, lean_object* v_as_1765_, size_t v_sz_1766_, size_t v_i_1767_, lean_object* v_b_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_){
_start:
{
uint8_t v___x_1776_; 
v___x_1776_ = lean_usize_dec_lt(v_i_1767_, v_sz_1766_);
if (v___x_1776_ == 0)
{
lean_object* v___x_1777_; 
v___x_1777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1777_, 0, v_b_1768_);
return v___x_1777_;
}
else
{
lean_object* v_snd_1778_; lean_object* v___x_1780_; uint8_t v_isShared_1781_; uint8_t v_isSharedCheck_1812_; 
v_snd_1778_ = lean_ctor_get(v_b_1768_, 1);
v_isSharedCheck_1812_ = !lean_is_exclusive(v_b_1768_);
if (v_isSharedCheck_1812_ == 0)
{
lean_object* v_unused_1813_; 
v_unused_1813_ = lean_ctor_get(v_b_1768_, 0);
lean_dec(v_unused_1813_);
v___x_1780_ = v_b_1768_;
v_isShared_1781_ = v_isSharedCheck_1812_;
goto v_resetjp_1779_;
}
else
{
lean_inc(v_snd_1778_);
lean_dec(v_b_1768_);
v___x_1780_ = lean_box(0);
v_isShared_1781_ = v_isSharedCheck_1812_;
goto v_resetjp_1779_;
}
v_resetjp_1779_:
{
lean_object* v_a_1782_; lean_object* v___x_1783_; 
v_a_1782_ = lean_array_uget_borrowed(v_as_1765_, v_i_1767_);
lean_inc(v_snd_1778_);
v___x_1783_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__1_spec__2(v_init_1762_, v___x_1763_, v___x_1764_, v_a_1782_, v_snd_1778_, v___y_1769_, v___y_1770_, v___y_1771_, v___y_1772_, v___y_1773_, v___y_1774_);
if (lean_obj_tag(v___x_1783_) == 0)
{
lean_object* v_a_1784_; lean_object* v___x_1786_; uint8_t v_isShared_1787_; uint8_t v_isSharedCheck_1803_; 
v_a_1784_ = lean_ctor_get(v___x_1783_, 0);
v_isSharedCheck_1803_ = !lean_is_exclusive(v___x_1783_);
if (v_isSharedCheck_1803_ == 0)
{
v___x_1786_ = v___x_1783_;
v_isShared_1787_ = v_isSharedCheck_1803_;
goto v_resetjp_1785_;
}
else
{
lean_inc(v_a_1784_);
lean_dec(v___x_1783_);
v___x_1786_ = lean_box(0);
v_isShared_1787_ = v_isSharedCheck_1803_;
goto v_resetjp_1785_;
}
v_resetjp_1785_:
{
if (lean_obj_tag(v_a_1784_) == 0)
{
lean_object* v___x_1788_; lean_object* v___x_1790_; 
v___x_1788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1788_, 0, v_a_1784_);
if (v_isShared_1781_ == 0)
{
lean_ctor_set(v___x_1780_, 0, v___x_1788_);
v___x_1790_ = v___x_1780_;
goto v_reusejp_1789_;
}
else
{
lean_object* v_reuseFailAlloc_1794_; 
v_reuseFailAlloc_1794_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1794_, 0, v___x_1788_);
lean_ctor_set(v_reuseFailAlloc_1794_, 1, v_snd_1778_);
v___x_1790_ = v_reuseFailAlloc_1794_;
goto v_reusejp_1789_;
}
v_reusejp_1789_:
{
lean_object* v___x_1792_; 
if (v_isShared_1787_ == 0)
{
lean_ctor_set(v___x_1786_, 0, v___x_1790_);
v___x_1792_ = v___x_1786_;
goto v_reusejp_1791_;
}
else
{
lean_object* v_reuseFailAlloc_1793_; 
v_reuseFailAlloc_1793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1793_, 0, v___x_1790_);
v___x_1792_ = v_reuseFailAlloc_1793_;
goto v_reusejp_1791_;
}
v_reusejp_1791_:
{
return v___x_1792_;
}
}
}
else
{
lean_object* v_a_1795_; lean_object* v___x_1796_; lean_object* v___x_1798_; 
lean_del_object(v___x_1786_);
lean_dec(v_snd_1778_);
v_a_1795_ = lean_ctor_get(v_a_1784_, 0);
lean_inc(v_a_1795_);
lean_dec_ref_known(v_a_1784_, 1);
v___x_1796_ = lean_box(0);
if (v_isShared_1781_ == 0)
{
lean_ctor_set(v___x_1780_, 1, v_a_1795_);
lean_ctor_set(v___x_1780_, 0, v___x_1796_);
v___x_1798_ = v___x_1780_;
goto v_reusejp_1797_;
}
else
{
lean_object* v_reuseFailAlloc_1802_; 
v_reuseFailAlloc_1802_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1802_, 0, v___x_1796_);
lean_ctor_set(v_reuseFailAlloc_1802_, 1, v_a_1795_);
v___x_1798_ = v_reuseFailAlloc_1802_;
goto v_reusejp_1797_;
}
v_reusejp_1797_:
{
size_t v___x_1799_; size_t v___x_1800_; 
v___x_1799_ = ((size_t)1ULL);
v___x_1800_ = lean_usize_add(v_i_1767_, v___x_1799_);
v_i_1767_ = v___x_1800_;
v_b_1768_ = v___x_1798_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1804_; lean_object* v___x_1806_; uint8_t v_isShared_1807_; uint8_t v_isSharedCheck_1811_; 
lean_del_object(v___x_1780_);
lean_dec(v_snd_1778_);
v_a_1804_ = lean_ctor_get(v___x_1783_, 0);
v_isSharedCheck_1811_ = !lean_is_exclusive(v___x_1783_);
if (v_isSharedCheck_1811_ == 0)
{
v___x_1806_ = v___x_1783_;
v_isShared_1807_ = v_isSharedCheck_1811_;
goto v_resetjp_1805_;
}
else
{
lean_inc(v_a_1804_);
lean_dec(v___x_1783_);
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
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__1_spec__2_spec__3___boxed(lean_object* v_init_1814_, lean_object* v___x_1815_, lean_object* v___x_1816_, lean_object* v_as_1817_, lean_object* v_sz_1818_, lean_object* v_i_1819_, lean_object* v_b_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_){
_start:
{
size_t v_sz_boxed_1828_; size_t v_i_boxed_1829_; lean_object* v_res_1830_; 
v_sz_boxed_1828_ = lean_unbox_usize(v_sz_1818_);
lean_dec(v_sz_1818_);
v_i_boxed_1829_ = lean_unbox_usize(v_i_1819_);
lean_dec(v_i_1819_);
v_res_1830_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__1_spec__2_spec__3(v_init_1814_, v___x_1815_, v___x_1816_, v_as_1817_, v_sz_boxed_1828_, v_i_boxed_1829_, v_b_1820_, v___y_1821_, v___y_1822_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_);
lean_dec(v___y_1826_);
lean_dec_ref(v___y_1825_);
lean_dec(v___y_1824_);
lean_dec_ref(v___y_1823_);
lean_dec(v___y_1822_);
lean_dec_ref(v___y_1821_);
lean_dec_ref(v_as_1817_);
lean_dec_ref(v___x_1816_);
lean_dec(v___x_1815_);
lean_dec_ref(v_init_1814_);
return v_res_1830_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__1_spec__2___boxed(lean_object* v_init_1831_, lean_object* v___x_1832_, lean_object* v___x_1833_, lean_object* v_n_1834_, lean_object* v_b_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_){
_start:
{
lean_object* v_res_1843_; 
v_res_1843_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__1_spec__2(v_init_1831_, v___x_1832_, v___x_1833_, v_n_1834_, v_b_1835_, v___y_1836_, v___y_1837_, v___y_1838_, v___y_1839_, v___y_1840_, v___y_1841_);
lean_dec(v___y_1841_);
lean_dec_ref(v___y_1840_);
lean_dec(v___y_1839_);
lean_dec_ref(v___y_1838_);
lean_dec(v___y_1837_);
lean_dec_ref(v___y_1836_);
lean_dec_ref(v_n_1834_);
lean_dec_ref(v___x_1833_);
lean_dec(v___x_1832_);
lean_dec_ref(v_init_1831_);
return v_res_1843_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__1(lean_object* v___x_1844_, lean_object* v___x_1845_, lean_object* v_t_1846_, lean_object* v_init_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_){
_start:
{
lean_object* v_root_1855_; lean_object* v_tail_1856_; lean_object* v___x_1857_; 
v_root_1855_ = lean_ctor_get(v_t_1846_, 0);
v_tail_1856_ = lean_ctor_get(v_t_1846_, 1);
lean_inc_ref(v_init_1847_);
v___x_1857_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__1_spec__2(v_init_1847_, v___x_1844_, v___x_1845_, v_root_1855_, v_init_1847_, v___y_1848_, v___y_1849_, v___y_1850_, v___y_1851_, v___y_1852_, v___y_1853_);
lean_dec_ref(v_init_1847_);
if (lean_obj_tag(v___x_1857_) == 0)
{
lean_object* v_a_1858_; lean_object* v___x_1860_; uint8_t v_isShared_1861_; uint8_t v_isSharedCheck_1894_; 
v_a_1858_ = lean_ctor_get(v___x_1857_, 0);
v_isSharedCheck_1894_ = !lean_is_exclusive(v___x_1857_);
if (v_isSharedCheck_1894_ == 0)
{
v___x_1860_ = v___x_1857_;
v_isShared_1861_ = v_isSharedCheck_1894_;
goto v_resetjp_1859_;
}
else
{
lean_inc(v_a_1858_);
lean_dec(v___x_1857_);
v___x_1860_ = lean_box(0);
v_isShared_1861_ = v_isSharedCheck_1894_;
goto v_resetjp_1859_;
}
v_resetjp_1859_:
{
if (lean_obj_tag(v_a_1858_) == 0)
{
lean_object* v_a_1862_; lean_object* v___x_1864_; 
v_a_1862_ = lean_ctor_get(v_a_1858_, 0);
lean_inc(v_a_1862_);
lean_dec_ref_known(v_a_1858_, 1);
if (v_isShared_1861_ == 0)
{
lean_ctor_set(v___x_1860_, 0, v_a_1862_);
v___x_1864_ = v___x_1860_;
goto v_reusejp_1863_;
}
else
{
lean_object* v_reuseFailAlloc_1865_; 
v_reuseFailAlloc_1865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1865_, 0, v_a_1862_);
v___x_1864_ = v_reuseFailAlloc_1865_;
goto v_reusejp_1863_;
}
v_reusejp_1863_:
{
return v___x_1864_;
}
}
else
{
lean_object* v_a_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; size_t v_sz_1869_; size_t v___x_1870_; lean_object* v___x_1871_; 
lean_del_object(v___x_1860_);
v_a_1866_ = lean_ctor_get(v_a_1858_, 0);
lean_inc(v_a_1866_);
lean_dec_ref_known(v_a_1858_, 1);
v___x_1867_ = lean_box(0);
v___x_1868_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1868_, 0, v___x_1867_);
lean_ctor_set(v___x_1868_, 1, v_a_1866_);
v_sz_1869_ = lean_array_size(v_tail_1856_);
v___x_1870_ = ((size_t)0ULL);
v___x_1871_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__1_spec__3(v___x_1844_, v___x_1845_, v_tail_1856_, v_sz_1869_, v___x_1870_, v___x_1868_, v___y_1848_, v___y_1849_, v___y_1850_, v___y_1851_, v___y_1852_, v___y_1853_);
if (lean_obj_tag(v___x_1871_) == 0)
{
lean_object* v_a_1872_; lean_object* v___x_1874_; uint8_t v_isShared_1875_; uint8_t v_isSharedCheck_1885_; 
v_a_1872_ = lean_ctor_get(v___x_1871_, 0);
v_isSharedCheck_1885_ = !lean_is_exclusive(v___x_1871_);
if (v_isSharedCheck_1885_ == 0)
{
v___x_1874_ = v___x_1871_;
v_isShared_1875_ = v_isSharedCheck_1885_;
goto v_resetjp_1873_;
}
else
{
lean_inc(v_a_1872_);
lean_dec(v___x_1871_);
v___x_1874_ = lean_box(0);
v_isShared_1875_ = v_isSharedCheck_1885_;
goto v_resetjp_1873_;
}
v_resetjp_1873_:
{
lean_object* v_fst_1876_; 
v_fst_1876_ = lean_ctor_get(v_a_1872_, 0);
if (lean_obj_tag(v_fst_1876_) == 0)
{
lean_object* v_snd_1877_; lean_object* v___x_1879_; 
v_snd_1877_ = lean_ctor_get(v_a_1872_, 1);
lean_inc(v_snd_1877_);
lean_dec(v_a_1872_);
if (v_isShared_1875_ == 0)
{
lean_ctor_set(v___x_1874_, 0, v_snd_1877_);
v___x_1879_ = v___x_1874_;
goto v_reusejp_1878_;
}
else
{
lean_object* v_reuseFailAlloc_1880_; 
v_reuseFailAlloc_1880_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1880_, 0, v_snd_1877_);
v___x_1879_ = v_reuseFailAlloc_1880_;
goto v_reusejp_1878_;
}
v_reusejp_1878_:
{
return v___x_1879_;
}
}
else
{
lean_object* v_val_1881_; lean_object* v___x_1883_; 
lean_inc_ref(v_fst_1876_);
lean_dec(v_a_1872_);
v_val_1881_ = lean_ctor_get(v_fst_1876_, 0);
lean_inc(v_val_1881_);
lean_dec_ref_known(v_fst_1876_, 1);
if (v_isShared_1875_ == 0)
{
lean_ctor_set(v___x_1874_, 0, v_val_1881_);
v___x_1883_ = v___x_1874_;
goto v_reusejp_1882_;
}
else
{
lean_object* v_reuseFailAlloc_1884_; 
v_reuseFailAlloc_1884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1884_, 0, v_val_1881_);
v___x_1883_ = v_reuseFailAlloc_1884_;
goto v_reusejp_1882_;
}
v_reusejp_1882_:
{
return v___x_1883_;
}
}
}
}
else
{
lean_object* v_a_1886_; lean_object* v___x_1888_; uint8_t v_isShared_1889_; uint8_t v_isSharedCheck_1893_; 
v_a_1886_ = lean_ctor_get(v___x_1871_, 0);
v_isSharedCheck_1893_ = !lean_is_exclusive(v___x_1871_);
if (v_isSharedCheck_1893_ == 0)
{
v___x_1888_ = v___x_1871_;
v_isShared_1889_ = v_isSharedCheck_1893_;
goto v_resetjp_1887_;
}
else
{
lean_inc(v_a_1886_);
lean_dec(v___x_1871_);
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
}
else
{
lean_object* v_a_1895_; lean_object* v___x_1897_; uint8_t v_isShared_1898_; uint8_t v_isSharedCheck_1902_; 
v_a_1895_ = lean_ctor_get(v___x_1857_, 0);
v_isSharedCheck_1902_ = !lean_is_exclusive(v___x_1857_);
if (v_isSharedCheck_1902_ == 0)
{
v___x_1897_ = v___x_1857_;
v_isShared_1898_ = v_isSharedCheck_1902_;
goto v_resetjp_1896_;
}
else
{
lean_inc(v_a_1895_);
lean_dec(v___x_1857_);
v___x_1897_ = lean_box(0);
v_isShared_1898_ = v_isSharedCheck_1902_;
goto v_resetjp_1896_;
}
v_resetjp_1896_:
{
lean_object* v___x_1900_; 
if (v_isShared_1898_ == 0)
{
v___x_1900_ = v___x_1897_;
goto v_reusejp_1899_;
}
else
{
lean_object* v_reuseFailAlloc_1901_; 
v_reuseFailAlloc_1901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1901_, 0, v_a_1895_);
v___x_1900_ = v_reuseFailAlloc_1901_;
goto v_reusejp_1899_;
}
v_reusejp_1899_:
{
return v___x_1900_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__1___boxed(lean_object* v___x_1903_, lean_object* v___x_1904_, lean_object* v_t_1905_, lean_object* v_init_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_){
_start:
{
lean_object* v_res_1914_; 
v_res_1914_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__1(v___x_1903_, v___x_1904_, v_t_1905_, v_init_1906_, v___y_1907_, v___y_1908_, v___y_1909_, v___y_1910_, v___y_1911_, v___y_1912_);
lean_dec(v___y_1912_);
lean_dec_ref(v___y_1911_);
lean_dec(v___y_1910_);
lean_dec_ref(v___y_1909_);
lean_dec(v___y_1908_);
lean_dec_ref(v___y_1907_);
lean_dec_ref(v_t_1905_);
lean_dec_ref(v___x_1904_);
lean_dec(v___x_1903_);
return v_res_1914_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_structuresPass___lam__0(lean_object* v_size_1915_, lean_object* v_interestingStructures_1916_, lean_object* v___x_1917_, lean_object* v___x_1918_, lean_object* v_goal_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_){
_start:
{
lean_object* v_lctx_1927_; lean_object* v_decls_1928_; lean_object* v___x_1929_; 
v_lctx_1927_ = lean_ctor_get(v___y_1922_, 2);
v_decls_1928_ = lean_ctor_get(v_lctx_1927_, 1);
v___x_1929_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__1(v_size_1915_, v_interestingStructures_1916_, v_decls_1928_, v___x_1917_, v___y_1920_, v___y_1921_, v___y_1922_, v___y_1923_, v___y_1924_, v___y_1925_);
if (lean_obj_tag(v___x_1929_) == 0)
{
lean_object* v_a_1930_; lean_object* v___x_1931_; lean_object* v_env_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; 
v_a_1930_ = lean_ctor_get(v___x_1929_, 0);
lean_inc(v_a_1930_);
lean_dec_ref_known(v___x_1929_, 1);
v___x_1931_ = lean_st_ref_get(v___y_1925_);
v_env_1932_ = lean_ctor_get(v___x_1931_, 0);
lean_inc_ref(v_env_1932_);
lean_dec(v___x_1931_);
v___x_1933_ = lean_mk_empty_array_with_capacity(v___x_1918_);
v___x_1934_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1934_, 0, v_a_1930_);
lean_ctor_set(v___x_1934_, 1, v___x_1933_);
v___x_1935_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__4___redArg(v_env_1932_, v_interestingStructures_1916_, v___x_1934_, v___y_1920_, v___y_1921_, v___y_1922_, v___y_1923_, v___y_1924_, v___y_1925_);
if (lean_obj_tag(v___x_1935_) == 0)
{
lean_object* v_a_1936_; lean_object* v_snd_1937_; lean_object* v___x_1938_; 
v_a_1936_ = lean_ctor_get(v___x_1935_, 0);
lean_inc(v_a_1936_);
lean_dec_ref_known(v___x_1935_, 1);
v_snd_1937_ = lean_ctor_get(v_a_1936_, 1);
lean_inc(v_snd_1937_);
lean_dec(v_a_1936_);
v___x_1938_ = l_Lean_MVarId_assertHypotheses(v_goal_1919_, v_snd_1937_, v___y_1922_, v___y_1923_, v___y_1924_, v___y_1925_);
if (lean_obj_tag(v___x_1938_) == 0)
{
lean_object* v_a_1939_; lean_object* v_snd_1940_; lean_object* v___x_1941_; 
v_a_1939_ = lean_ctor_get(v___x_1938_, 0);
lean_inc(v_a_1939_);
lean_dec_ref_known(v___x_1938_, 1);
v_snd_1940_ = lean_ctor_get(v_a_1939_, 1);
lean_inc(v_snd_1940_);
lean_dec(v_a_1939_);
v___x_1941_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess(v_snd_1940_, v___y_1920_, v___y_1921_, v___y_1922_, v___y_1923_, v___y_1924_, v___y_1925_);
return v___x_1941_;
}
else
{
lean_object* v_a_1942_; lean_object* v___x_1944_; uint8_t v_isShared_1945_; uint8_t v_isSharedCheck_1949_; 
v_a_1942_ = lean_ctor_get(v___x_1938_, 0);
v_isSharedCheck_1949_ = !lean_is_exclusive(v___x_1938_);
if (v_isSharedCheck_1949_ == 0)
{
v___x_1944_ = v___x_1938_;
v_isShared_1945_ = v_isSharedCheck_1949_;
goto v_resetjp_1943_;
}
else
{
lean_inc(v_a_1942_);
lean_dec(v___x_1938_);
v___x_1944_ = lean_box(0);
v_isShared_1945_ = v_isSharedCheck_1949_;
goto v_resetjp_1943_;
}
v_resetjp_1943_:
{
lean_object* v___x_1947_; 
if (v_isShared_1945_ == 0)
{
v___x_1947_ = v___x_1944_;
goto v_reusejp_1946_;
}
else
{
lean_object* v_reuseFailAlloc_1948_; 
v_reuseFailAlloc_1948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1948_, 0, v_a_1942_);
v___x_1947_ = v_reuseFailAlloc_1948_;
goto v_reusejp_1946_;
}
v_reusejp_1946_:
{
return v___x_1947_;
}
}
}
}
else
{
lean_object* v_a_1950_; lean_object* v___x_1952_; uint8_t v_isShared_1953_; uint8_t v_isSharedCheck_1957_; 
lean_dec(v_goal_1919_);
v_a_1950_ = lean_ctor_get(v___x_1935_, 0);
v_isSharedCheck_1957_ = !lean_is_exclusive(v___x_1935_);
if (v_isSharedCheck_1957_ == 0)
{
v___x_1952_ = v___x_1935_;
v_isShared_1953_ = v_isSharedCheck_1957_;
goto v_resetjp_1951_;
}
else
{
lean_inc(v_a_1950_);
lean_dec(v___x_1935_);
v___x_1952_ = lean_box(0);
v_isShared_1953_ = v_isSharedCheck_1957_;
goto v_resetjp_1951_;
}
v_resetjp_1951_:
{
lean_object* v___x_1955_; 
if (v_isShared_1953_ == 0)
{
v___x_1955_ = v___x_1952_;
goto v_reusejp_1954_;
}
else
{
lean_object* v_reuseFailAlloc_1956_; 
v_reuseFailAlloc_1956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1956_, 0, v_a_1950_);
v___x_1955_ = v_reuseFailAlloc_1956_;
goto v_reusejp_1954_;
}
v_reusejp_1954_:
{
return v___x_1955_;
}
}
}
}
else
{
lean_object* v_a_1958_; lean_object* v___x_1960_; uint8_t v_isShared_1961_; uint8_t v_isSharedCheck_1965_; 
lean_dec(v_goal_1919_);
v_a_1958_ = lean_ctor_get(v___x_1929_, 0);
v_isSharedCheck_1965_ = !lean_is_exclusive(v___x_1929_);
if (v_isSharedCheck_1965_ == 0)
{
v___x_1960_ = v___x_1929_;
v_isShared_1961_ = v_isSharedCheck_1965_;
goto v_resetjp_1959_;
}
else
{
lean_inc(v_a_1958_);
lean_dec(v___x_1929_);
v___x_1960_ = lean_box(0);
v_isShared_1961_ = v_isSharedCheck_1965_;
goto v_resetjp_1959_;
}
v_resetjp_1959_:
{
lean_object* v___x_1963_; 
if (v_isShared_1961_ == 0)
{
v___x_1963_ = v___x_1960_;
goto v_reusejp_1962_;
}
else
{
lean_object* v_reuseFailAlloc_1964_; 
v_reuseFailAlloc_1964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1964_, 0, v_a_1958_);
v___x_1963_ = v_reuseFailAlloc_1964_;
goto v_reusejp_1962_;
}
v_reusejp_1962_:
{
return v___x_1963_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_structuresPass___lam__0___boxed(lean_object* v_size_1966_, lean_object* v_interestingStructures_1967_, lean_object* v___x_1968_, lean_object* v___x_1969_, lean_object* v_goal_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_){
_start:
{
lean_object* v_res_1978_; 
v_res_1978_ = l_Lean_Meta_Tactic_BVDecide_Normalize_structuresPass___lam__0(v_size_1966_, v_interestingStructures_1967_, v___x_1968_, v___x_1969_, v_goal_1970_, v___y_1971_, v___y_1972_, v___y_1973_, v___y_1974_, v___y_1975_, v___y_1976_);
lean_dec(v___y_1976_);
lean_dec_ref(v___y_1975_);
lean_dec(v___y_1974_);
lean_dec_ref(v___y_1973_);
lean_dec(v___y_1972_);
lean_dec_ref(v___y_1971_);
lean_dec(v___x_1969_);
lean_dec_ref(v_interestingStructures_1967_);
lean_dec(v_size_1966_);
return v_res_1978_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_structuresPass___lam__1(lean_object* v_goal_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_){
_start:
{
lean_object* v___x_1989_; lean_object* v_typeAnalysis_1990_; lean_object* v_interestingStructures_1991_; lean_object* v_size_1992_; lean_object* v___x_1993_; uint8_t v___x_1994_; 
v___x_1989_ = lean_st_ref_get(v___y_1983_);
v_typeAnalysis_1990_ = lean_ctor_get(v___x_1989_, 2);
lean_inc_ref(v_typeAnalysis_1990_);
lean_dec(v___x_1989_);
v_interestingStructures_1991_ = lean_ctor_get(v_typeAnalysis_1990_, 0);
lean_inc_ref(v_interestingStructures_1991_);
lean_dec_ref(v_typeAnalysis_1990_);
v_size_1992_ = lean_ctor_get(v_interestingStructures_1991_, 0);
lean_inc(v_size_1992_);
v___x_1993_ = lean_unsigned_to_nat(0u);
v___x_1994_ = lean_nat_dec_eq(v_size_1992_, v___x_1993_);
if (v___x_1994_ == 0)
{
lean_object* v___x_1995_; lean_object* v___f_1996_; lean_object* v___x_1997_; 
v___x_1995_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_structuresPass___lam__1___closed__0));
lean_inc(v_goal_1981_);
v___f_1996_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_structuresPass___lam__0___boxed), 12, 5);
lean_closure_set(v___f_1996_, 0, v_size_1992_);
lean_closure_set(v___f_1996_, 1, v_interestingStructures_1991_);
lean_closure_set(v___f_1996_, 2, v___x_1995_);
lean_closure_set(v___f_1996_, 3, v___x_1993_);
lean_closure_set(v___f_1996_, 4, v_goal_1981_);
v___x_1997_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess_spec__1___redArg(v_goal_1981_, v___f_1996_, v___y_1982_, v___y_1983_, v___y_1984_, v___y_1985_, v___y_1986_, v___y_1987_);
return v___x_1997_;
}
else
{
lean_object* v___x_1998_; lean_object* v___x_1999_; 
lean_dec(v_size_1992_);
lean_dec_ref(v_interestingStructures_1991_);
v___x_1998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1998_, 0, v_goal_1981_);
v___x_1999_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1999_, 0, v___x_1998_);
return v___x_1999_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_structuresPass___lam__1___boxed(lean_object* v_goal_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_){
_start:
{
lean_object* v_res_2008_; 
v_res_2008_ = l_Lean_Meta_Tactic_BVDecide_Normalize_structuresPass___lam__1(v_goal_2000_, v___y_2001_, v___y_2002_, v___y_2003_, v___y_2004_, v___y_2005_, v___y_2006_);
lean_dec(v___y_2006_);
lean_dec_ref(v___y_2005_);
lean_dec(v___y_2004_);
lean_dec_ref(v___y_2003_);
lean_dec(v___y_2002_);
lean_dec_ref(v___y_2001_);
return v_res_2008_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__0(lean_object* v_00_u03b2_2017_, lean_object* v_m_2018_, lean_object* v_a_2019_){
_start:
{
uint8_t v___x_2020_; 
v___x_2020_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__0___redArg(v_m_2018_, v_a_2019_);
return v___x_2020_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__0___boxed(lean_object* v_00_u03b2_2021_, lean_object* v_m_2022_, lean_object* v_a_2023_){
_start:
{
uint8_t v_res_2024_; lean_object* v_r_2025_; 
v_res_2024_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__0(v_00_u03b2_2021_, v_m_2022_, v_a_2023_);
lean_dec(v_a_2023_);
lean_dec_ref(v_m_2022_);
v_r_2025_ = lean_box(v_res_2024_);
return v_r_2025_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__3(lean_object* v_upperBound_2026_, lean_object* v_a_2027_, lean_object* v_fst_2028_, lean_object* v_snd_2029_, lean_object* v_fst_2030_, lean_object* v___x_2031_, lean_object* v_inst_2032_, lean_object* v_R_2033_, lean_object* v_a_2034_, lean_object* v_b_2035_, lean_object* v_c_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_){
_start:
{
lean_object* v___x_2044_; 
v___x_2044_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__3___redArg(v_upperBound_2026_, v_a_2027_, v_fst_2028_, v_snd_2029_, v_fst_2030_, v___x_2031_, v_a_2034_, v_b_2035_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_);
return v___x_2044_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__3___boxed(lean_object** _args){
lean_object* v_upperBound_2045_ = _args[0];
lean_object* v_a_2046_ = _args[1];
lean_object* v_fst_2047_ = _args[2];
lean_object* v_snd_2048_ = _args[3];
lean_object* v_fst_2049_ = _args[4];
lean_object* v___x_2050_ = _args[5];
lean_object* v_inst_2051_ = _args[6];
lean_object* v_R_2052_ = _args[7];
lean_object* v_a_2053_ = _args[8];
lean_object* v_b_2054_ = _args[9];
lean_object* v_c_2055_ = _args[10];
lean_object* v___y_2056_ = _args[11];
lean_object* v___y_2057_ = _args[12];
lean_object* v___y_2058_ = _args[13];
lean_object* v___y_2059_ = _args[14];
lean_object* v___y_2060_ = _args[15];
lean_object* v___y_2061_ = _args[16];
lean_object* v___y_2062_ = _args[17];
_start:
{
lean_object* v_res_2063_; 
v_res_2063_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__3(v_upperBound_2045_, v_a_2046_, v_fst_2047_, v_snd_2048_, v_fst_2049_, v___x_2050_, v_inst_2051_, v_R_2052_, v_a_2053_, v_b_2054_, v_c_2055_, v___y_2056_, v___y_2057_, v___y_2058_, v___y_2059_, v___y_2060_, v___y_2061_);
lean_dec(v___y_2061_);
lean_dec_ref(v___y_2060_);
lean_dec(v___y_2059_);
lean_dec_ref(v___y_2058_);
lean_dec(v___y_2057_);
lean_dec_ref(v___y_2056_);
lean_dec_ref(v___x_2050_);
lean_dec_ref(v_snd_2048_);
lean_dec(v_upperBound_2045_);
return v_res_2063_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__4(lean_object* v___x_2064_, lean_object* v___x_2065_, lean_object* v_inst_2066_, lean_object* v_a_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_){
_start:
{
lean_object* v___x_2075_; 
v___x_2075_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__4___redArg(v___x_2064_, v___x_2065_, v_a_2067_, v___y_2068_, v___y_2069_, v___y_2070_, v___y_2071_, v___y_2072_, v___y_2073_);
return v___x_2075_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__4___boxed(lean_object* v___x_2076_, lean_object* v___x_2077_, lean_object* v_inst_2078_, lean_object* v_a_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_){
_start:
{
lean_object* v_res_2087_; 
v_res_2087_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__4(v___x_2076_, v___x_2077_, v_inst_2078_, v_a_2079_, v___y_2080_, v___y_2081_, v___y_2082_, v___y_2083_, v___y_2084_, v___y_2085_);
lean_dec(v___y_2085_);
lean_dec_ref(v___y_2084_);
lean_dec(v___y_2083_);
lean_dec_ref(v___y_2082_);
lean_dec(v___y_2081_);
lean_dec_ref(v___y_2080_);
lean_dec_ref(v___x_2077_);
return v_res_2087_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__0_spec__0(lean_object* v_00_u03b2_2088_, lean_object* v_a_2089_, lean_object* v_x_2090_){
_start:
{
uint8_t v___x_2091_; 
v___x_2091_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__0_spec__0___redArg(v_a_2089_, v_x_2090_);
return v___x_2091_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2092_, lean_object* v_a_2093_, lean_object* v_x_2094_){
_start:
{
uint8_t v_res_2095_; lean_object* v_r_2096_; 
v_res_2095_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__0_spec__0(v_00_u03b2_2092_, v_a_2093_, v_x_2094_);
lean_dec(v_x_2094_);
lean_dec(v_a_2093_);
v_r_2096_ = lean_box(v_res_2095_);
return v_r_2096_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__1_spec__3_spec__6(lean_object* v___x_2097_, lean_object* v___x_2098_, lean_object* v_as_2099_, size_t v_sz_2100_, size_t v_i_2101_, lean_object* v_b_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_){
_start:
{
lean_object* v___x_2110_; 
v___x_2110_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__1_spec__3_spec__6___redArg(v___x_2097_, v___x_2098_, v_as_2099_, v_sz_2100_, v_i_2101_, v_b_2102_);
return v___x_2110_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__1_spec__3_spec__6___boxed(lean_object* v___x_2111_, lean_object* v___x_2112_, lean_object* v_as_2113_, lean_object* v_sz_2114_, lean_object* v_i_2115_, lean_object* v_b_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_){
_start:
{
size_t v_sz_boxed_2124_; size_t v_i_boxed_2125_; lean_object* v_res_2126_; 
v_sz_boxed_2124_ = lean_unbox_usize(v_sz_2114_);
lean_dec(v_sz_2114_);
v_i_boxed_2125_ = lean_unbox_usize(v_i_2115_);
lean_dec(v_i_2115_);
v_res_2126_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__1_spec__3_spec__6(v___x_2111_, v___x_2112_, v_as_2113_, v_sz_boxed_2124_, v_i_boxed_2125_, v_b_2116_, v___y_2117_, v___y_2118_, v___y_2119_, v___y_2120_, v___y_2121_, v___y_2122_);
lean_dec(v___y_2122_);
lean_dec_ref(v___y_2121_);
lean_dec(v___y_2120_);
lean_dec_ref(v___y_2119_);
lean_dec(v___y_2118_);
lean_dec_ref(v___y_2117_);
lean_dec_ref(v_as_2113_);
lean_dec_ref(v___x_2112_);
lean_dec(v___x_2111_);
return v_res_2126_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__1_spec__2_spec__4_spec__9(lean_object* v___x_2127_, lean_object* v___x_2128_, lean_object* v_as_2129_, size_t v_sz_2130_, size_t v_i_2131_, lean_object* v_b_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_, lean_object* v___y_2138_){
_start:
{
lean_object* v___x_2140_; 
v___x_2140_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__1_spec__2_spec__4_spec__9___redArg(v___x_2127_, v___x_2128_, v_as_2129_, v_sz_2130_, v_i_2131_, v_b_2132_);
return v___x_2140_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__1_spec__2_spec__4_spec__9___boxed(lean_object* v___x_2141_, lean_object* v___x_2142_, lean_object* v_as_2143_, lean_object* v_sz_2144_, lean_object* v_i_2145_, lean_object* v_b_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_){
_start:
{
size_t v_sz_boxed_2154_; size_t v_i_boxed_2155_; lean_object* v_res_2156_; 
v_sz_boxed_2154_ = lean_unbox_usize(v_sz_2144_);
lean_dec(v_sz_2144_);
v_i_boxed_2155_ = lean_unbox_usize(v_i_2145_);
lean_dec(v_i_2145_);
v_res_2156_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__1_spec__2_spec__4_spec__9(v___x_2141_, v___x_2142_, v_as_2143_, v_sz_boxed_2154_, v_i_boxed_2155_, v_b_2146_, v___y_2147_, v___y_2148_, v___y_2149_, v___y_2150_, v___y_2151_, v___y_2152_);
lean_dec(v___y_2152_);
lean_dec_ref(v___y_2151_);
lean_dec(v___y_2150_);
lean_dec_ref(v___y_2149_);
lean_dec(v___y_2148_);
lean_dec_ref(v___y_2147_);
lean_dec_ref(v_as_2143_);
lean_dec_ref(v___x_2142_);
lean_dec(v___x_2141_);
return v_res_2156_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_TypeAnalysis(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_ApplyControlFlow(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Ext(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Structures(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_TypeAnalysis(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_ApplyControlFlow(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Ext(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Structures(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_BVDecide_Normalize_TypeAnalysis(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_BVDecide_Normalize_ApplyControlFlow(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Ext(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_BVDecide_Normalize_Structures(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_BVDecide_Normalize_TypeAnalysis(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_BVDecide_Normalize_ApplyControlFlow(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Ext(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Structures(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Structures(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_BVDecide_Normalize_Structures(builtin);
}
#ifdef __cplusplus
}
#endif
