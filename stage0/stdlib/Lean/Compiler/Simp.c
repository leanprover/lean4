// Lean compiler output
// Module: Lean.Compiler.Simp
// Imports: Init Lean.Compiler.CompilerM Lean.Compiler.Decl Lean.Compiler.Stage1 Lean.Compiler.InlineAttrs
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
LEAN_EXPORT lean_object* l_Std_HashMapImp_moveEntries___at_Lean_Compiler_Simp_OccInfo_add___spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_visitLet___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_Decl_simp_x3f___closed__3;
LEAN_EXPORT lean_object* l_Std_AssocList_foldlM___at_Lean_Compiler_Simp_OccInfo_format___spec__2___boxed(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Std_AssocList_foldlM___at_Lean_Compiler_Simp_OccInfo_format___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_expandTrivialExpr___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_inlineCandidate_x3f___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_Simp_visitLambda___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_visitLambda___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Compiler_InferType_inferType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_mkFlatLet___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_Compiler_Simp_visitLambda___closed__1;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_mkHashMap___at_Lean_Compiler_Simp_OccInfo_map___default___spec__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_markSimplified___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Std_Data_HashMap_0__Std_numBucketsForCapacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_inlineApp_x3f___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_Simp_visitCases___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_visitLambda___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_userName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_simpCasesOnCases_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_forIn_loop___at_Lean_Compiler_Simp_OccInfo_format___spec__4___closed__3;
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_Simp_internalize_visitCases___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_Simp_visitCases___closed__4;
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Compiler_mkLetUsingScope(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
static lean_object* l_Lean_Compiler_Decl_simp___closed__5;
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_internalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_Simp_instInhabitedState___closed__1;
static lean_object* l_Lean_Compiler_Decl_simp_x3f___lambda__3___closed__3;
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_visitLet___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_instInhabitedState;
static lean_object* l_Lean_Compiler_Simp_visitCases___closed__1;
static lean_object* l_List_forIn_loop___at_Lean_Compiler_Simp_OccInfo_format___spec__4___closed__5;
static lean_object* l_Lean_throwError___at_Lean_Compiler_Simp_visitLambda___spec__3___closed__6;
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_simpCasesOnCases_x3f_inlineJp(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_Simp_inlineProjInst_x3f_visitProj___closed__1;
lean_object* l_Lean_Compiler_getStage1Decl_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
static lean_object* l_panic___at_Lean_Compiler_Simp_inlineProjInst_x3f_visitProj___spec__1___closed__4;
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_findCtor___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_Simp_inlineApp_x3f___closed__5;
static lean_object* l_Lean_Compiler_Simp_instToFormatOccInfo___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_internalize_visitLambda(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_forIn_loop___at_Lean_Compiler_Simp_OccInfo_format___spec__4___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_visitLet___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_simpProj_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_Simp_simpProj_x3f___closed__1;
static lean_object* l_Lean_Compiler_Simp_visitCases___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_Occ_noConfusion___rarg___lambda__1(lean_object*);
static lean_object* l_Lean_Compiler_Simp_instReprOcc___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_simpAppApp_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_Simp_simpAppApp_x3f___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_OccInfo_map___default;
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_inlineCandidate_x3f___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_Decl_simp___closed__3;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Expr_constructorApp_x3f(lean_object*, lean_object*);
static lean_object* l_panic___at_Lean_Compiler_Simp_visitCases___spec__2___closed__1;
uint8_t l_Lean_Expr_isApp(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_simpAppApp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_insert___at_Lean_Compiler_Simp_OccInfo_add___spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_internalize_visitValue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_internalize_visitValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_Simp_0__Lean_Compiler_Simp_reprOcc____x40_Lean_Compiler_Simp___hyg_296____closed__12;
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_inlineCandidate_x3f___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_Simp_simpProj_x3f___closed__3;
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_expr_lift_loose_bvars(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_AssocList_find_x3f___at_Lean_Compiler_Simp_OccInfo_add___spec__2(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
static lean_object* l_Lean_throwError___at_Lean_Compiler_Simp_visitLambda___spec__3___closed__4;
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
static lean_object* l_Lean_Compiler_Decl_simp_x3f___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_inlineCandidate_x3f___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_Simp_inlineApp_x3f___lambda__1___closed__1;
static lean_object* l_Lean_throwError___at_Lean_Compiler_Simp_visitLambda___spec__3___closed__2;
static lean_object* l_Lean_Compiler_Decl_simp_x3f___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_mkLcUnreachable___at_Lean_Compiler_Simp_visitLambda___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_inlineApp_x3f___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_Simp_visitCases___closed__3;
static lean_object* l_Lean_Compiler_Simp_inlineApp_x3f___lambda__4___closed__4;
LEAN_EXPORT lean_object* l_Std_HashMapImp_expand___at_Lean_Compiler_Simp_OccInfo_add___spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_mkHashMap___at_Lean_Compiler_Simp_OccInfo_map___default___spec__1(lean_object*);
static lean_object* l_Lean_Compiler_Simp_simpProj_x3f___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_markSimplified(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_findExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_Simp_visitLambda___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_inlineApp_x3f___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_mkLcUnreachable___at_Lean_Compiler_Simp_visitLambda___spec__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_State_occInfo___default;
extern lean_object* l_Lean_levelZero;
static lean_object* l_Lean_throwError___at_Lean_Compiler_Simp_visitLambda___spec__3___closed__1;
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_Occ_noConfusion___rarg(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Compiler_Simp_inlineApp_x3f___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_OccInfo_add(lean_object*, lean_object*);
static lean_object* l_Lean_throwError___at_Lean_Compiler_Simp_visitLambda___spec__3___closed__3;
static lean_object* l___private_Lean_Compiler_Simp_0__Lean_Compiler_Simp_reprOcc____x40_Lean_Compiler_Simp___hyg_296____closed__14;
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
static lean_object* l_Lean_Compiler_Simp_inlineApp_x3f___closed__6;
LEAN_EXPORT lean_object* l_Lean_Compiler_Decl_simp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_Decl_simp___closed__6;
static lean_object* l_Lean_Compiler_Simp_inlineProjInst_x3f_visitProj___closed__3;
static lean_object* l_Lean_throwError___at_Lean_Compiler_Simp_visitLambda___spec__3___closed__5;
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_instReprOcc;
static lean_object* l___private_Lean_Compiler_Simp_0__Lean_Compiler_Simp_reprOcc____x40_Lean_Compiler_Simp___hyg_296____closed__5;
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Name_hash___override(lean_object*);
lean_object* l_Lean_LocalDecl_value(lean_object*);
static lean_object* l_panic___at_Lean_Compiler_Simp_inlineProjInst_x3f_visitProj___spec__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_expandTrivialExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_initFn____x40_Lean_Compiler_Simp___hyg_6456____closed__1;
extern lean_object* l_Lean_inheritedTraceOptions;
LEAN_EXPORT lean_object* l_Std_AssocList_contains___at_Lean_Compiler_Simp_OccInfo_add___spec__4___boxed(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_inlineCandidate_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_inlineApp_x3f___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_expandTrivialExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_isClass_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_Decl_simp___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_visitLambda(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_betaReduce(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_Simp_0__Lean_Compiler_Simp_reprOcc____x40_Lean_Compiler_Simp___hyg_296____closed__3;
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_mkLetDecl(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_OccInfo_format(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_inlineProjInst_x3f_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_Decl_simp___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_simpCasesOnCases_x3f_inlineJp___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_Decl_simp_x3f___lambda__3___closed__2;
static lean_object* l_List_forIn_loop___at_Lean_Compiler_Simp_OccInfo_format___spec__4___closed__1;
static lean_object* l___private_Lean_Compiler_Simp_0__Lean_Compiler_Simp_reprOcc____x40_Lean_Compiler_Simp___hyg_296____closed__10;
static lean_object* l___private_Lean_Compiler_Simp_0__Lean_Compiler_Simp_reprOcc____x40_Lean_Compiler_Simp___hyg_296____closed__7;
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
static lean_object* l_panic___at_Lean_Compiler_Simp_inlineProjInst_x3f_visitProj___spec__1___closed__1;
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
static lean_object* l_List_forIn_loop___at_Lean_Compiler_Simp_OccInfo_format___spec__4___closed__4;
lean_object* l_Std_mkHashMapImp___rarg(lean_object*);
static lean_object* l_Lean_Compiler_initFn____x40_Lean_Compiler_Simp___hyg_6456____closed__3;
LEAN_EXPORT uint8_t l_Lean_Compiler_Simp_instInhabitedOcc;
lean_object* l_instInhabited___rarg(lean_object*, lean_object*);
lean_object* l_panic___at_Lean_Expr_getRevArg_x21___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Compiler_Simp_inlineApp_x3f___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_Occ_noConfusion(lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_shouldInlineLocal___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_repr(lean_object*);
LEAN_EXPORT lean_object* l_Std_AssocList_foldlM___at_Lean_Compiler_Simp_OccInfo_add___spec__7(lean_object*, lean_object*);
static lean_object* l_List_forIn_loop___at_Lean_Compiler_Simp_OccInfo_format___spec__4___closed__6;
static lean_object* l_Lean_Compiler_Simp_inlineApp_x3f___closed__4;
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_Config_smallThreshold___default;
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_getLevel___at_Lean_Compiler_Simp_visitLambda___spec__2___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_Simp_visitLambda___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_mkLcUnreachable___at_Lean_Compiler_Simp_visitLambda___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
static lean_object* l_Lean_Compiler_Simp_inlineApp_x3f___closed__8;
static lean_object* l_Lean_Compiler_initFn____x40_Lean_Compiler_Simp___hyg_6456____closed__2;
static lean_object* l_Lean_Compiler_Simp_Occ_noConfusion___rarg___closed__1;
LEAN_EXPORT lean_object* l_Std_AssocList_replace___at_Lean_Compiler_Simp_OccInfo_add___spec__8(lean_object*, uint8_t, lean_object*);
static lean_object* l_Lean_Compiler_Decl_simp_x3f___closed__4;
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_inlineCandidate_x3f___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_Occ_noConfusion___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_mkFreshLetVarIdx(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_getLambdaArity(lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
static lean_object* l___private_Lean_Compiler_Simp_0__Lean_Compiler_Simp_reprOcc____x40_Lean_Compiler_Simp___hyg_296____closed__13;
static lean_object* l_Lean_Compiler_Decl_simp_x3f___lambda__2___closed__3;
size_t lean_usize_modn(size_t, lean_object*);
static lean_object* l_Lean_Compiler_Decl_simp___closed__4;
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_Decl_simp_x3f___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConst(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_getLevel___at_Lean_Compiler_Simp_visitLambda___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_Decl_simp_x3f___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_Compiler_Simp_visitCases___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_visitLetImp_go___at_Lean_Compiler_Simp_inlineProjInst_x3f_visit___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_Simp_inlineApp_x3f___closed__7;
LEAN_EXPORT lean_object* l_Lean_Compiler_visitLetImp_go___at_Lean_Compiler_Simp_inlineProjInst_x3f_visit___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bvar___override(lean_object*);
static lean_object* l_Lean_Compiler_Simp_inlineApp_x3f___closed__3;
static lean_object* l_Lean_Compiler_Simp_inlineApp_x3f___lambda__4___closed__3;
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Std_AssocList_replace___at_Lean_Compiler_Simp_OccInfo_add___spec__8___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isLambda(lean_object*);
LEAN_EXPORT uint8_t l_Std_AssocList_contains___at_Lean_Compiler_Simp_OccInfo_add___spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_simpCasesOnCases_x3f_isJpCtor_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_internalize_visitCases(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_attachJp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_getLevel___at_Lean_Compiler_Simp_visitLambda___spec__2___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_Decl_simp_x3f___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_visitLambdaCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_getLevel___at_Lean_Compiler_Simp_visitLambda___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_Decl_simp(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_Decl_simp_x3f___lambda__3___closed__1;
lean_object* l_Lean_Compiler_onlyOneExitPoint(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_Simp_inlineApp_x3f___lambda__4___closed__5;
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_visitLet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_getLevel___at_Lean_Compiler_Simp_visitLambda___spec__2___closed__1;
static lean_object* l_panic___at_Lean_Compiler_Simp_inlineProjInst_x3f_visitProj___spec__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_findLambda_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_Simp_State_simplified___default;
static lean_object* l_Lean_isTracingEnabledFor___at_Lean_Compiler_Simp_inlineApp_x3f___spec__1___closed__1;
lean_object* l_Lean_Compiler_findDecl_x3f___at_Lean_Compiler_JoinPoints_JoinPointFinder_declIsInScope___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_instInhabitedOccInfo;
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_simpProj_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_Lean_Compiler_Simp_inlineApp_x3f___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_push___rarg(lean_object*, lean_object*);
uint8_t l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_hasInlineAttrAux(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMapImp_find_x3f___at_Lean_Compiler_Simp_OccInfo_add___spec__1(lean_object*, lean_object*);
static lean_object* l_panic___at_Lean_Compiler_Simp_inlineProjInst_x3f_visitProj___spec__1___closed__5;
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_inlineApp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_inlineProjInst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_Simp_OccInfo_format___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_mkFlatLet(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_simpValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_Simp_0__Lean_Compiler_Simp_reprOcc____x40_Lean_Compiler_Simp___hyg_296____closed__6;
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_inlineApp_x3f___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_Simp_OccInfo_format___spec__3(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Compiler_Simp_OccInfo_format___spec__4(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_mkAuxLetDeclName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_beta(lean_object*, lean_object*);
lean_object* l_instInhabitedReaderT___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_mkLambda(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Core_instMonadCoreM;
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_simpCasesOnCases_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_Occ_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_insert___at_Lean_Compiler_Simp_OccInfo_add___spec__3(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_Decl_simp_x3f___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_Decl_simp_x3f___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_Decl_simp_x3f___lambda__2___closed__2;
uint8_t l_Lean_Expr_isConstructorApp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_Simp_simpCasesOnCases_x3f___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_isJp(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_findLambda_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_Lean_Compiler_Simp_inlineApp_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_simpCasesOnCases_x3f_isJpCtor_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_Simp_internalize_visitCases___closed__1;
static lean_object* l_Lean_Compiler_Simp_internalize_visitLambda___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_findDecl_x3f___at_Lean_Compiler_Simp_simpCasesOnCases_x3f_isJpCtor_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_ofSubarray___rarg(lean_object*);
static lean_object* l_Lean_Compiler_Simp_inlineApp_x3f___lambda__4___closed__7;
LEAN_EXPORT lean_object* l_Lean_Compiler_findDecl_x3f___at_Lean_Compiler_Simp_simpCasesOnCases_x3f_isJpCtor_x3f___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAnyType(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_internalize_visitLet___lambda__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_Compiler_Simp_inlineProjInst_x3f_visitProj___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_Simp_0__Lean_Compiler_Simp_reprOcc____x40_Lean_Compiler_Simp___hyg_296____closed__11;
uint8_t l_Lean_Expr_isFVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_inlineCandidate_x3f___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_Decl_simp_x3f___lambda__4___closed__1;
lean_object* l_Lean_Compiler_Decl_getArity(lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_Simp_simpCasesOnCases_x3f___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate_rev(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_Context_config___default;
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_visitCases(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_Simp_inlineApp_x3f___lambda__3___closed__1;
static lean_object* l_Lean_Compiler_Simp_inlineProjInst_x3f_visitProj___closed__2;
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isProj(lean_object*);
lean_object* l_Lean_Compiler_mkJpDeclIfNotSimple(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_findExpr(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_Simp_instInhabitedOccInfo___closed__1;
LEAN_EXPORT lean_object* l_Std_HashMap_toList___at_Lean_Compiler_Simp_OccInfo_format___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_inlineProjInst_x3f_visitProj(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_Simp_visitCases___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadReaderT___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_expandTrivialExpr___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_Occ_noConfusion___rarg___lambda__1___boxed(lean_object*);
static lean_object* l_Lean_Compiler_Simp_inlineApp_x3f___closed__2;
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_Simp_internalize_visitCases___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_mkLocalDecl(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_visitLambda___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_internalize_visitLet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_shouldInlineLocal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
static lean_object* l_Lean_Compiler_Simp_inlineApp_x3f___lambda__4___closed__2;
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_Simp_simpCasesOnCases_x3f___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_Simp_visitLambda___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_Simp_0__Lean_Compiler_Simp_reprOcc____x40_Lean_Compiler_Simp___hyg_296____closed__4;
static lean_object* l_Lean_Compiler_Simp_inlineApp_x3f___closed__1;
lean_object* l_Lean_Compiler_ensureUniqueLetVarNames(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_OptionT_instMonadOptionT___rarg(lean_object*);
static lean_object* l___private_Lean_Compiler_Simp_0__Lean_Compiler_Simp_reprOcc____x40_Lean_Compiler_Simp___hyg_296____closed__8;
lean_object* l_Lean_Compiler_isCasesApp_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_Simp_simpCasesOnCases_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_local_ctx_find(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_internalize_visitLet___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_mkFlatLet_go(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_getLCNFSize(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_mkAuxLetDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_Simp_0__Lean_Compiler_Simp_reprOcc____x40_Lean_Compiler_Simp___hyg_296____closed__9;
lean_object* l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParams___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_inlineCandidate_x3f___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_levelOne;
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_Occ_toCtorIdx(uint8_t);
static lean_object* l_Lean_Compiler_Simp_visitCases___closed__5;
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_instToFormatOccInfo;
static lean_object* l_Lean_Compiler_Simp_inlineProjInst_x3f_visitProj___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Simp_0__Lean_Compiler_Simp_reprOcc____x40_Lean_Compiler_Simp___hyg_296_(uint8_t, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Compiler_lcnfSizeLe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_Decl_simp_x3f___lambda__2___closed__1;
static lean_object* l_Lean_Compiler_mkLcUnreachable___at_Lean_Compiler_Simp_visitLambda___spec__1___closed__2;
static lean_object* l_Lean_Compiler_Simp_simpProj_x3f___closed__4;
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_findCtor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_markSimplified___boxed(lean_object*);
static lean_object* l_Lean_Compiler_Simp_inlineApp_x3f___lambda__3___closed__2;
LEAN_EXPORT lean_object* l_Std_AssocList_find_x3f___at_Lean_Compiler_Simp_OccInfo_add___spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_inlineCandidate_x3f___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_initFn____x40_Lean_Compiler_Simp___hyg_6456_(lean_object*);
static lean_object* l___private_Lean_Compiler_Simp_0__Lean_Compiler_Simp_reprOcc____x40_Lean_Compiler_Simp___hyg_296____closed__2;
lean_object* l_Lean_Compiler_isEmptyType(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Simp_0__Lean_Compiler_Simp_reprOcc____x40_Lean_Compiler_Simp___hyg_296____boxed(lean_object*, lean_object*);
static lean_object* l_panic___at_Lean_Compiler_Simp_visitCases___spec__2___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_markSimplified___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_mkFlatLet_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_Simp_inlineApp_x3f___lambda__4___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_inlineApp_x3f___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isLet(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_visitLet___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_Simp_0__Lean_Compiler_Simp_reprOcc____x40_Lean_Compiler_Simp___hyg_296____closed__1;
static lean_object* l_Lean_Compiler_Simp_inlineApp_x3f___lambda__4___closed__6;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_findLambda_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = l_Lean_Compiler_findDecl_x3f___at_Lean_Compiler_JoinPoints_JoinPointFinder_declIsInScope___spec__1(x_6, x_2, x_3, x_4, x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_7, 0);
lean_dec(x_10);
x_11 = lean_box(0);
lean_ctor_set(x_7, 0, x_11);
return x_7;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_7, 1);
lean_inc(x_12);
lean_dec(x_7);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_8);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_8, 0);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
lean_free_object(x_8);
lean_dec(x_16);
x_17 = !lean_is_exclusive(x_7);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_7, 0);
lean_dec(x_18);
x_19 = lean_box(0);
lean_ctor_set(x_7, 0, x_19);
return x_7;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_7, 1);
lean_inc(x_20);
lean_dec(x_7);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_7);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = lean_ctor_get(x_7, 1);
x_25 = lean_ctor_get(x_7, 0);
lean_dec(x_25);
x_26 = lean_ctor_get(x_16, 4);
lean_inc(x_26);
x_27 = l_Lean_Expr_isLambda(x_26);
if (x_27 == 0)
{
lean_free_object(x_7);
lean_free_object(x_8);
lean_dec(x_16);
x_1 = x_26;
x_5 = x_24;
goto _start;
}
else
{
lean_dec(x_26);
return x_7;
}
}
else
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_29 = lean_ctor_get(x_7, 1);
lean_inc(x_29);
lean_dec(x_7);
x_30 = lean_ctor_get(x_16, 4);
lean_inc(x_30);
x_31 = l_Lean_Expr_isLambda(x_30);
if (x_31 == 0)
{
lean_free_object(x_8);
lean_dec(x_16);
x_1 = x_30;
x_5 = x_29;
goto _start;
}
else
{
lean_object* x_33; 
lean_dec(x_30);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_8);
lean_ctor_set(x_33, 1, x_29);
return x_33;
}
}
}
}
else
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_8, 0);
lean_inc(x_34);
lean_dec(x_8);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_34);
x_35 = lean_ctor_get(x_7, 1);
lean_inc(x_35);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_36 = x_7;
} else {
 lean_dec_ref(x_7);
 x_36 = lean_box(0);
}
x_37 = lean_box(0);
if (lean_is_scalar(x_36)) {
 x_38 = lean_alloc_ctor(0, 2, 0);
} else {
 x_38 = x_36;
}
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_35);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_39 = lean_ctor_get(x_7, 1);
lean_inc(x_39);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_40 = x_7;
} else {
 lean_dec_ref(x_7);
 x_40 = lean_box(0);
}
x_41 = lean_ctor_get(x_34, 4);
lean_inc(x_41);
x_42 = l_Lean_Expr_isLambda(x_41);
if (x_42 == 0)
{
lean_dec(x_40);
lean_dec(x_34);
x_1 = x_41;
x_5 = x_39;
goto _start;
}
else
{
lean_object* x_44; lean_object* x_45; 
lean_dec(x_41);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_34);
if (lean_is_scalar(x_40)) {
 x_45 = lean_alloc_ctor(0, 2, 0);
} else {
 x_45 = x_40;
}
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_39);
return x_45;
}
}
}
}
}
case 10:
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_1, 1);
lean_inc(x_46);
lean_dec(x_1);
x_1 = x_46;
goto _start;
}
default: 
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_1);
x_48 = lean_box(0);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_5);
return x_49;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_findLambda_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Compiler_Simp_findLambda_x3f(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_findExpr(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = l_Lean_Compiler_findDecl_x3f___at_Lean_Compiler_JoinPoints_JoinPointFinder_declIsInScope___spec__1(x_7, x_3, x_4, x_5, x_6);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_8, 0);
lean_dec(x_11);
lean_ctor_set(x_8, 0, x_1);
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_8, 1);
lean_inc(x_12);
lean_dec(x_8);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
else
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_9, 0);
lean_inc(x_14);
lean_dec(x_9);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
lean_dec(x_14);
x_15 = !lean_is_exclusive(x_8);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_8, 0);
lean_dec(x_16);
lean_ctor_set(x_8, 0, x_1);
return x_8;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_8, 1);
lean_inc(x_17);
lean_dec(x_8);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_1);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
lean_dec(x_1);
x_19 = lean_ctor_get(x_8, 1);
lean_inc(x_19);
lean_dec(x_8);
x_20 = lean_ctor_get(x_14, 4);
lean_inc(x_20);
lean_dec(x_14);
x_21 = 1;
x_1 = x_20;
x_2 = x_21;
x_6 = x_19;
goto _start;
}
}
}
case 10:
{
if (x_2 == 0)
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_1);
lean_ctor_set(x_23, 1, x_6);
return x_23;
}
else
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_ctor_get(x_1, 1);
lean_inc(x_24);
lean_dec(x_1);
x_25 = 1;
x_1 = x_24;
x_2 = x_25;
goto _start;
}
}
default: 
{
lean_object* x_27; 
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_1);
lean_ctor_set(x_27, 1, x_6);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_findExpr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_2);
lean_dec(x_2);
x_8 = l_Lean_Compiler_Simp_findExpr(x_1, x_7, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_Occ_toCtorIdx(uint8_t x_1) {
_start:
{
if (x_1 == 0)
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
else
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_Occ_toCtorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Compiler_Simp_Occ_toCtorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_Occ_noConfusion___rarg___lambda__1(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_Simp_Occ_noConfusion___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_Simp_Occ_noConfusion___rarg___lambda__1___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_Occ_noConfusion___rarg(uint8_t x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Compiler_Simp_Occ_noConfusion___rarg___closed__1;
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_Occ_noConfusion(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Compiler_Simp_Occ_noConfusion___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_Occ_noConfusion___rarg___lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Compiler_Simp_Occ_noConfusion___rarg___lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_Occ_noConfusion___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_Lean_Compiler_Simp_Occ_noConfusion___rarg(x_4, x_5, x_3);
return x_6;
}
}
static lean_object* _init_l___private_Lean_Compiler_Simp_0__Lean_Compiler_Simp_reprOcc____x40_Lean_Compiler_Simp___hyg_296____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Compiler.Simp.Occ.once", 27);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Compiler_Simp_0__Lean_Compiler_Simp_reprOcc____x40_Lean_Compiler_Simp___hyg_296____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Compiler_Simp_0__Lean_Compiler_Simp_reprOcc____x40_Lean_Compiler_Simp___hyg_296____closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Compiler_Simp_0__Lean_Compiler_Simp_reprOcc____x40_Lean_Compiler_Simp___hyg_296____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Compiler_Simp_0__Lean_Compiler_Simp_reprOcc____x40_Lean_Compiler_Simp___hyg_296____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Compiler_Simp_0__Lean_Compiler_Simp_reprOcc____x40_Lean_Compiler_Simp___hyg_296____closed__3;
x_2 = l___private_Lean_Compiler_Simp_0__Lean_Compiler_Simp_reprOcc____x40_Lean_Compiler_Simp___hyg_296____closed__2;
x_3 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_Simp_0__Lean_Compiler_Simp_reprOcc____x40_Lean_Compiler_Simp___hyg_296____closed__5() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lean_Compiler_Simp_0__Lean_Compiler_Simp_reprOcc____x40_Lean_Compiler_Simp___hyg_296____closed__4;
x_2 = 0;
x_3 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_Simp_0__Lean_Compiler_Simp_reprOcc____x40_Lean_Compiler_Simp___hyg_296____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Compiler_Simp_0__Lean_Compiler_Simp_reprOcc____x40_Lean_Compiler_Simp___hyg_296____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Compiler_Simp_0__Lean_Compiler_Simp_reprOcc____x40_Lean_Compiler_Simp___hyg_296____closed__6;
x_2 = l___private_Lean_Compiler_Simp_0__Lean_Compiler_Simp_reprOcc____x40_Lean_Compiler_Simp___hyg_296____closed__2;
x_3 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_Simp_0__Lean_Compiler_Simp_reprOcc____x40_Lean_Compiler_Simp___hyg_296____closed__8() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lean_Compiler_Simp_0__Lean_Compiler_Simp_reprOcc____x40_Lean_Compiler_Simp___hyg_296____closed__7;
x_2 = 0;
x_3 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_Simp_0__Lean_Compiler_Simp_reprOcc____x40_Lean_Compiler_Simp___hyg_296____closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Compiler.Simp.Occ.many", 27);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Compiler_Simp_0__Lean_Compiler_Simp_reprOcc____x40_Lean_Compiler_Simp___hyg_296____closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Compiler_Simp_0__Lean_Compiler_Simp_reprOcc____x40_Lean_Compiler_Simp___hyg_296____closed__9;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Compiler_Simp_0__Lean_Compiler_Simp_reprOcc____x40_Lean_Compiler_Simp___hyg_296____closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Compiler_Simp_0__Lean_Compiler_Simp_reprOcc____x40_Lean_Compiler_Simp___hyg_296____closed__3;
x_2 = l___private_Lean_Compiler_Simp_0__Lean_Compiler_Simp_reprOcc____x40_Lean_Compiler_Simp___hyg_296____closed__10;
x_3 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_Simp_0__Lean_Compiler_Simp_reprOcc____x40_Lean_Compiler_Simp___hyg_296____closed__12() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lean_Compiler_Simp_0__Lean_Compiler_Simp_reprOcc____x40_Lean_Compiler_Simp___hyg_296____closed__11;
x_2 = 0;
x_3 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_Simp_0__Lean_Compiler_Simp_reprOcc____x40_Lean_Compiler_Simp___hyg_296____closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Compiler_Simp_0__Lean_Compiler_Simp_reprOcc____x40_Lean_Compiler_Simp___hyg_296____closed__6;
x_2 = l___private_Lean_Compiler_Simp_0__Lean_Compiler_Simp_reprOcc____x40_Lean_Compiler_Simp___hyg_296____closed__10;
x_3 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_Simp_0__Lean_Compiler_Simp_reprOcc____x40_Lean_Compiler_Simp___hyg_296____closed__14() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lean_Compiler_Simp_0__Lean_Compiler_Simp_reprOcc____x40_Lean_Compiler_Simp___hyg_296____closed__13;
x_2 = 0;
x_3 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Simp_0__Lean_Compiler_Simp_reprOcc____x40_Lean_Compiler_Simp___hyg_296_(uint8_t x_1, lean_object* x_2) {
_start:
{
if (x_1 == 0)
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(1024u);
x_4 = lean_nat_dec_le(x_3, x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = l___private_Lean_Compiler_Simp_0__Lean_Compiler_Simp_reprOcc____x40_Lean_Compiler_Simp___hyg_296____closed__5;
x_6 = l_Repr_addAppParen(x_5, x_2);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = l___private_Lean_Compiler_Simp_0__Lean_Compiler_Simp_reprOcc____x40_Lean_Compiler_Simp___hyg_296____closed__8;
x_8 = l_Repr_addAppParen(x_7, x_2);
return x_8;
}
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_unsigned_to_nat(1024u);
x_10 = lean_nat_dec_le(x_9, x_2);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = l___private_Lean_Compiler_Simp_0__Lean_Compiler_Simp_reprOcc____x40_Lean_Compiler_Simp___hyg_296____closed__12;
x_12 = l_Repr_addAppParen(x_11, x_2);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = l___private_Lean_Compiler_Simp_0__Lean_Compiler_Simp_reprOcc____x40_Lean_Compiler_Simp___hyg_296____closed__14;
x_14 = l_Repr_addAppParen(x_13, x_2);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Simp_0__Lean_Compiler_Simp_reprOcc____x40_Lean_Compiler_Simp___hyg_296____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l___private_Lean_Compiler_Simp_0__Lean_Compiler_Simp_reprOcc____x40_Lean_Compiler_Simp___hyg_296_(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Compiler_Simp_instReprOcc___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Compiler_Simp_0__Lean_Compiler_Simp_reprOcc____x40_Lean_Compiler_Simp___hyg_296____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_Simp_instReprOcc() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Compiler_Simp_instReprOcc___closed__1;
return x_1;
}
}
static uint8_t _init_l_Lean_Compiler_Simp_instInhabitedOcc() {
_start:
{
uint8_t x_1; 
x_1 = 0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_mkHashMap___at_Lean_Compiler_Simp_OccInfo_map___default___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_mkHashMapImp___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_Simp_OccInfo_map___default() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Std_mkHashMapImp___rarg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_mkHashMap___at_Lean_Compiler_Simp_OccInfo_map___default___spec__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_mkHashMap___at_Lean_Compiler_Simp_OccInfo_map___default___spec__1(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_Simp_instInhabitedOccInfo___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Std_mkHashMapImp___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_Simp_instInhabitedOccInfo() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Compiler_Simp_instInhabitedOccInfo___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_AssocList_foldlM___at_Lean_Compiler_Simp_OccInfo_format___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_4);
lean_inc(x_3);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_4);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_1);
x_1 = x_7;
x_2 = x_5;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_Simp_OccInfo_format___spec__3(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l_Std_AssocList_foldlM___at_Lean_Compiler_Simp_OccInfo_format___spec__2(x_4, x_6);
lean_dec(x_6);
x_8 = 1;
x_9 = lean_usize_add(x_2, x_8);
x_2 = x_9;
x_4 = x_7;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_toList___at_Lean_Compiler_Simp_OccInfo_format___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_2 = lean_box(0);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_array_get_size(x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_lt(x_5, x_4);
if (x_6 == 0)
{
lean_dec(x_4);
lean_dec(x_3);
return x_2;
}
else
{
uint8_t x_7; 
x_7 = lean_nat_dec_le(x_4, x_4);
if (x_7 == 0)
{
lean_dec(x_4);
lean_dec(x_3);
return x_2;
}
else
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = 0;
x_9 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_10 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_Simp_OccInfo_format___spec__3(x_3, x_8, x_9, x_2);
lean_dec(x_3);
return x_10;
}
}
}
}
static lean_object* _init_l_List_forIn_loop___at_Lean_Compiler_Simp_OccInfo_format___spec__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("\n", 1);
return x_1;
}
}
static lean_object* _init_l_List_forIn_loop___at_Lean_Compiler_Simp_OccInfo_format___spec__4___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_forIn_loop___at_Lean_Compiler_Simp_OccInfo_format___spec__4___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_List_forIn_loop___at_Lean_Compiler_Simp_OccInfo_format___spec__4___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("", 0);
return x_1;
}
}
static lean_object* _init_l_List_forIn_loop___at_Lean_Compiler_Simp_OccInfo_format___spec__4___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_forIn_loop___at_Lean_Compiler_Simp_OccInfo_format___spec__4___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_List_forIn_loop___at_Lean_Compiler_Simp_OccInfo_format___spec__4___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" ↦ ", 5);
return x_1;
}
}
static lean_object* _init_l_List_forIn_loop___at_Lean_Compiler_Simp_OccInfo_format___spec__4___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_forIn_loop___at_Lean_Compiler_Simp_OccInfo_format___spec__4___closed__5;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Compiler_Simp_OccInfo_format___spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec(x_3);
x_7 = l_List_forIn_loop___at_Lean_Compiler_Simp_OccInfo_format___spec__4___closed__2;
x_8 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_8, 0, x_2);
lean_ctor_set(x_8, 1, x_7);
x_9 = 1;
x_10 = l_Lean_Name_toString(x_5, x_9);
x_11 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = l_List_forIn_loop___at_Lean_Compiler_Simp_OccInfo_format___spec__4___closed__4;
x_13 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
x_14 = l_List_forIn_loop___at_Lean_Compiler_Simp_OccInfo_format___spec__4___closed__6;
x_15 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_unbox(x_6);
lean_dec(x_6);
x_18 = l___private_Lean_Compiler_Simp_0__Lean_Compiler_Simp_reprOcc____x40_Lean_Compiler_Simp___hyg_296_(x_17, x_16);
x_19 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_19, 0, x_15);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_12);
x_21 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_21, 0, x_8);
lean_ctor_set(x_21, 1, x_20);
x_1 = x_4;
x_2 = x_21;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_OccInfo_format(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Std_HashMap_toList___at_Lean_Compiler_Simp_OccInfo_format___spec__1(x_1);
x_3 = lean_box(0);
x_4 = l_List_forIn_loop___at_Lean_Compiler_Simp_OccInfo_format___spec__4(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_AssocList_foldlM___at_Lean_Compiler_Simp_OccInfo_format___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_AssocList_foldlM___at_Lean_Compiler_Simp_OccInfo_format___spec__2(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_Simp_OccInfo_format___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_Simp_OccInfo_format___spec__3(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
static lean_object* _init_l_Lean_Compiler_Simp_instToFormatOccInfo___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_Simp_OccInfo_format), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_Simp_instToFormatOccInfo() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Compiler_Simp_instToFormatOccInfo___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_AssocList_find_x3f___at_Lean_Compiler_Simp_OccInfo_add___spec__2(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Std_HashMapImp_find_x3f___at_Lean_Compiler_Simp_OccInfo_add___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint64_t x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_array_get_size(x_3);
x_5 = l_Lean_Name_hash___override(x_2);
x_6 = lean_uint64_to_usize(x_5);
x_7 = lean_usize_modn(x_6, x_4);
lean_dec(x_4);
x_8 = lean_array_uget(x_3, x_7);
lean_dec(x_3);
x_9 = l_Std_AssocList_find_x3f___at_Lean_Compiler_Simp_OccInfo_add___spec__2(x_2, x_8);
lean_dec(x_8);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT uint8_t l_Std_AssocList_contains___at_Lean_Compiler_Simp_OccInfo_add___spec__4(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Std_AssocList_foldlM___at_Lean_Compiler_Simp_OccInfo_add___spec__7(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; size_t x_8; size_t x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_array_get_size(x_1);
x_7 = l_Lean_Name_hash___override(x_4);
x_8 = lean_uint64_to_usize(x_7);
x_9 = lean_usize_modn(x_8, x_6);
lean_dec(x_6);
x_10 = lean_array_uget(x_1, x_9);
lean_ctor_set(x_2, 2, x_10);
x_11 = lean_array_uset(x_1, x_9, x_2);
x_1 = x_11;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint64_t x_17; size_t x_18; size_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_13 = lean_ctor_get(x_2, 0);
x_14 = lean_ctor_get(x_2, 1);
x_15 = lean_ctor_get(x_2, 2);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_2);
x_16 = lean_array_get_size(x_1);
x_17 = l_Lean_Name_hash___override(x_13);
x_18 = lean_uint64_to_usize(x_17);
x_19 = lean_usize_modn(x_18, x_16);
lean_dec(x_16);
x_20 = lean_array_uget(x_1, x_19);
x_21 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_21, 0, x_13);
lean_ctor_set(x_21, 1, x_14);
lean_ctor_set(x_21, 2, x_20);
x_22 = lean_array_uset(x_1, x_19, x_21);
x_1 = x_22;
x_2 = x_15;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMapImp_moveEntries___at_Lean_Compiler_Simp_OccInfo_add___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_Std_AssocList_foldlM___at_Lean_Compiler_Simp_OccInfo_add___spec__7(x_3, x_6);
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
LEAN_EXPORT lean_object* l_Std_HashMapImp_expand___at_Lean_Compiler_Simp_OccInfo_add___spec__5(lean_object* x_1, lean_object* x_2) {
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
x_9 = l_Std_HashMapImp_moveEntries___at_Lean_Compiler_Simp_OccInfo_add___spec__6(x_8, x_2, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_AssocList_replace___at_Lean_Compiler_Simp_OccInfo_add___spec__8(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
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
x_10 = l_Std_AssocList_replace___at_Lean_Compiler_Simp_OccInfo_add___spec__8(x_1, x_2, x_8);
lean_ctor_set(x_3, 2, x_10);
return x_3;
}
else
{
lean_object* x_11; 
lean_dec(x_7);
lean_dec(x_6);
x_11 = lean_box(x_2);
lean_ctor_set(x_3, 1, x_11);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_3, 0);
x_13 = lean_ctor_get(x_3, 1);
x_14 = lean_ctor_get(x_3, 2);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_3);
x_15 = lean_name_eq(x_12, x_1);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = l_Std_AssocList_replace___at_Lean_Compiler_Simp_OccInfo_add___spec__8(x_1, x_2, x_14);
x_17 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_17, 0, x_12);
lean_ctor_set(x_17, 1, x_13);
lean_ctor_set(x_17, 2, x_16);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_13);
lean_dec(x_12);
x_18 = lean_box(x_2);
x_19 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_19, 0, x_1);
lean_ctor_set(x_19, 1, x_18);
lean_ctor_set(x_19, 2, x_14);
return x_19;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_insert___at_Lean_Compiler_Simp_OccInfo_add___spec__3(lean_object* x_1, lean_object* x_2, uint8_t x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint64_t x_8; size_t x_9; size_t x_10; lean_object* x_11; uint8_t x_12; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_array_get_size(x_6);
x_8 = l_Lean_Name_hash___override(x_2);
x_9 = lean_uint64_to_usize(x_8);
x_10 = lean_usize_modn(x_9, x_7);
x_11 = lean_array_uget(x_6, x_10);
x_12 = l_Std_AssocList_contains___at_Lean_Compiler_Simp_OccInfo_add___spec__4(x_2, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_5, x_13);
lean_dec(x_5);
x_15 = lean_box(x_3);
x_16 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_16, 0, x_2);
lean_ctor_set(x_16, 1, x_15);
lean_ctor_set(x_16, 2, x_11);
x_17 = lean_array_uset(x_6, x_10, x_16);
x_18 = l___private_Std_Data_HashMap_0__Std_numBucketsForCapacity(x_14);
x_19 = lean_nat_dec_le(x_18, x_7);
lean_dec(x_7);
lean_dec(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
lean_free_object(x_1);
x_20 = l_Std_HashMapImp_expand___at_Lean_Compiler_Simp_OccInfo_add___spec__5(x_14, x_17);
return x_20;
}
else
{
lean_ctor_set(x_1, 1, x_17);
lean_ctor_set(x_1, 0, x_14);
return x_1;
}
}
else
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_7);
x_21 = l_Std_AssocList_replace___at_Lean_Compiler_Simp_OccInfo_add___spec__8(x_2, x_3, x_11);
x_22 = lean_array_uset(x_6, x_10, x_21);
lean_ctor_set(x_1, 1, x_22);
return x_1;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint64_t x_26; size_t x_27; size_t x_28; lean_object* x_29; uint8_t x_30; 
x_23 = lean_ctor_get(x_1, 0);
x_24 = lean_ctor_get(x_1, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_1);
x_25 = lean_array_get_size(x_24);
x_26 = l_Lean_Name_hash___override(x_2);
x_27 = lean_uint64_to_usize(x_26);
x_28 = lean_usize_modn(x_27, x_25);
x_29 = lean_array_uget(x_24, x_28);
x_30 = l_Std_AssocList_contains___at_Lean_Compiler_Simp_OccInfo_add___spec__4(x_2, x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_31 = lean_unsigned_to_nat(1u);
x_32 = lean_nat_add(x_23, x_31);
lean_dec(x_23);
x_33 = lean_box(x_3);
x_34 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_34, 0, x_2);
lean_ctor_set(x_34, 1, x_33);
lean_ctor_set(x_34, 2, x_29);
x_35 = lean_array_uset(x_24, x_28, x_34);
x_36 = l___private_Std_Data_HashMap_0__Std_numBucketsForCapacity(x_32);
x_37 = lean_nat_dec_le(x_36, x_25);
lean_dec(x_25);
lean_dec(x_36);
if (x_37 == 0)
{
lean_object* x_38; 
x_38 = l_Std_HashMapImp_expand___at_Lean_Compiler_Simp_OccInfo_add___spec__5(x_32, x_35);
return x_38;
}
else
{
lean_object* x_39; 
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_32);
lean_ctor_set(x_39, 1, x_35);
return x_39;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_25);
x_40 = l_Std_AssocList_replace___at_Lean_Compiler_Simp_OccInfo_add___spec__8(x_2, x_3, x_29);
x_41 = lean_array_uset(x_24, x_28, x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_23);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_OccInfo_add(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
lean_inc(x_2);
lean_inc(x_1);
x_3 = l_Std_HashMapImp_find_x3f___at_Lean_Compiler_Simp_OccInfo_add___spec__1(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; lean_object* x_5; 
x_4 = 0;
x_5 = l_Std_HashMap_insert___at_Lean_Compiler_Simp_OccInfo_add___spec__3(x_1, x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
lean_dec(x_3);
x_7 = lean_unbox(x_6);
lean_dec(x_6);
if (x_7 == 0)
{
uint8_t x_8; lean_object* x_9; 
x_8 = 1;
x_9 = l_Std_HashMap_insert___at_Lean_Compiler_Simp_OccInfo_add___spec__3(x_1, x_2, x_8);
return x_9;
}
else
{
lean_dec(x_2);
return x_1;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_AssocList_find_x3f___at_Lean_Compiler_Simp_OccInfo_add___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_AssocList_find_x3f___at_Lean_Compiler_Simp_OccInfo_add___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_AssocList_contains___at_Lean_Compiler_Simp_OccInfo_add___spec__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_AssocList_contains___at_Lean_Compiler_Simp_OccInfo_add___spec__4(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_AssocList_replace___at_Lean_Compiler_Simp_OccInfo_add___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_Std_AssocList_replace___at_Lean_Compiler_Simp_OccInfo_add___spec__8(x_1, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_insert___at_Lean_Compiler_Simp_OccInfo_add___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_3);
lean_dec(x_3);
x_5 = l_Std_HashMap_insert___at_Lean_Compiler_Simp_OccInfo_add___spec__3(x_1, x_2, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Compiler_Simp_Config_smallThreshold___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(1u);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_Simp_Context_config___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(1u);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_Simp_State_occInfo___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Compiler_Simp_instInhabitedOccInfo___closed__1;
return x_1;
}
}
static uint8_t _init_l_Lean_Compiler_Simp_State_simplified___default() {
_start:
{
uint8_t x_1; 
x_1 = 0;
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_Simp_instInhabitedState___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_Simp_instInhabitedOccInfo___closed__1;
x_2 = 0;
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_Simp_instInhabitedState() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Compiler_Simp_instInhabitedState___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_internalize_visitValue(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = l_Lean_Expr_isApp(x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = l_Lean_Expr_getAppFn(x_1);
x_12 = l_Lean_Compiler_Simp_findLambda_x3f(x_11, x_4, x_5, x_6, x_7);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_12, 0);
lean_dec(x_15);
x_16 = lean_box(0);
lean_ctor_set(x_12, 0, x_16);
return x_12;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_dec(x_12);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_12);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_21 = lean_ctor_get(x_12, 1);
x_22 = lean_ctor_get(x_12, 0);
lean_dec(x_22);
x_23 = lean_ctor_get(x_13, 0);
lean_inc(x_23);
lean_dec(x_13);
x_24 = l_Lean_LocalDecl_value(x_23);
x_25 = l_Lean_Expr_isLambda(x_24);
lean_dec(x_24);
if (x_25 == 0)
{
lean_object* x_26; 
lean_dec(x_23);
x_26 = lean_box(0);
lean_ctor_set(x_12, 0, x_26);
return x_12;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
lean_free_object(x_12);
x_27 = l_Lean_LocalDecl_userName(x_23);
lean_dec(x_23);
x_28 = lean_st_ref_get(x_6, x_21);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_30 = lean_st_ref_take(x_3, x_29);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = !lean_is_exclusive(x_31);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_34 = lean_ctor_get(x_31, 0);
x_35 = l_Lean_Compiler_Simp_OccInfo_add(x_34, x_27);
lean_ctor_set(x_31, 0, x_35);
x_36 = lean_st_ref_set(x_3, x_31, x_32);
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_36, 0);
lean_dec(x_38);
x_39 = lean_box(0);
lean_ctor_set(x_36, 0, x_39);
return x_36;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_36, 1);
lean_inc(x_40);
lean_dec(x_36);
x_41 = lean_box(0);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
return x_42;
}
}
else
{
lean_object* x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_43 = lean_ctor_get(x_31, 0);
x_44 = lean_ctor_get_uint8(x_31, sizeof(void*)*1);
lean_inc(x_43);
lean_dec(x_31);
x_45 = l_Lean_Compiler_Simp_OccInfo_add(x_43, x_27);
x_46 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set_uint8(x_46, sizeof(void*)*1, x_44);
x_47 = lean_st_ref_set(x_3, x_46, x_32);
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
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_52 = lean_ctor_get(x_12, 1);
lean_inc(x_52);
lean_dec(x_12);
x_53 = lean_ctor_get(x_13, 0);
lean_inc(x_53);
lean_dec(x_13);
x_54 = l_Lean_LocalDecl_value(x_53);
x_55 = l_Lean_Expr_isLambda(x_54);
lean_dec(x_54);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; 
lean_dec(x_53);
x_56 = lean_box(0);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_52);
return x_57;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_58 = l_Lean_LocalDecl_userName(x_53);
lean_dec(x_53);
x_59 = lean_st_ref_get(x_6, x_52);
x_60 = lean_ctor_get(x_59, 1);
lean_inc(x_60);
lean_dec(x_59);
x_61 = lean_st_ref_take(x_3, x_60);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_64 = lean_ctor_get(x_62, 0);
lean_inc(x_64);
x_65 = lean_ctor_get_uint8(x_62, sizeof(void*)*1);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 x_66 = x_62;
} else {
 lean_dec_ref(x_62);
 x_66 = lean_box(0);
}
x_67 = l_Lean_Compiler_Simp_OccInfo_add(x_64, x_58);
if (lean_is_scalar(x_66)) {
 x_68 = lean_alloc_ctor(0, 1, 1);
} else {
 x_68 = x_66;
}
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set_uint8(x_68, sizeof(void*)*1, x_65);
x_69 = lean_st_ref_set(x_3, x_68, x_63);
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
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_internalize_visitValue___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_Simp_internalize_visitValue(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
static lean_object* _init_l_Lean_Compiler_Simp_internalize_visitLambda___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_internalize_visitLambda(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_8 = lean_st_ref_get(x_6, x_7);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_st_ref_get(x_4, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_41 = lean_st_ref_get(x_6, x_12);
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
lean_dec(x_41);
x_43 = lean_st_ref_take(x_4, x_42);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = !lean_is_exclusive(x_44);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_47 = lean_ctor_get(x_44, 1);
lean_dec(x_47);
x_48 = l_Lean_Compiler_Simp_internalize_visitLambda___closed__1;
lean_ctor_set(x_44, 1, x_48);
x_49 = lean_st_ref_set(x_4, x_44, x_45);
x_50 = lean_ctor_get(x_49, 1);
lean_inc(x_50);
lean_dec(x_49);
x_51 = l_Lean_Compiler_visitLambdaCore(x_1, x_4, x_5, x_6, x_50);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = lean_ctor_get(x_52, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_52, 1);
lean_inc(x_55);
lean_dec(x_52);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_54);
x_56 = l_Lean_Compiler_Simp_internalize_visitLet(x_55, x_54, x_2, x_3, x_4, x_5, x_6, x_53);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_59 = l_Lean_Compiler_mkLetUsingScope(x_57, x_4, x_5, x_6, x_58);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_62 = l_Lean_Compiler_mkLambda(x_54, x_60, x_4, x_5, x_6, x_61);
lean_dec(x_5);
lean_dec(x_54);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
x_65 = lean_st_ref_get(x_6, x_64);
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
lean_dec(x_65);
x_67 = lean_st_ref_get(x_4, x_66);
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_70 = lean_ctor_get(x_11, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_11, 1);
lean_inc(x_71);
lean_dec(x_11);
x_72 = !lean_is_exclusive(x_68);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; 
x_73 = lean_ctor_get(x_68, 1);
lean_dec(x_73);
x_74 = lean_ctor_get(x_68, 0);
lean_dec(x_74);
lean_ctor_set(x_68, 1, x_71);
lean_ctor_set(x_68, 0, x_70);
x_75 = lean_st_ref_get(x_6, x_69);
lean_dec(x_6);
x_76 = lean_ctor_get(x_75, 1);
lean_inc(x_76);
lean_dec(x_75);
x_77 = lean_st_ref_set(x_4, x_68, x_76);
lean_dec(x_4);
x_78 = !lean_is_exclusive(x_77);
if (x_78 == 0)
{
lean_object* x_79; 
x_79 = lean_ctor_get(x_77, 0);
lean_dec(x_79);
lean_ctor_set(x_77, 0, x_63);
return x_77;
}
else
{
lean_object* x_80; lean_object* x_81; 
x_80 = lean_ctor_get(x_77, 1);
lean_inc(x_80);
lean_dec(x_77);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_63);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_82 = lean_ctor_get(x_68, 2);
lean_inc(x_82);
lean_dec(x_68);
x_83 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_83, 0, x_70);
lean_ctor_set(x_83, 1, x_71);
lean_ctor_set(x_83, 2, x_82);
x_84 = lean_st_ref_get(x_6, x_69);
lean_dec(x_6);
x_85 = lean_ctor_get(x_84, 1);
lean_inc(x_85);
lean_dec(x_84);
x_86 = lean_st_ref_set(x_4, x_83, x_85);
lean_dec(x_4);
x_87 = lean_ctor_get(x_86, 1);
lean_inc(x_87);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 lean_ctor_release(x_86, 1);
 x_88 = x_86;
} else {
 lean_dec_ref(x_86);
 x_88 = lean_box(0);
}
if (lean_is_scalar(x_88)) {
 x_89 = lean_alloc_ctor(0, 2, 0);
} else {
 x_89 = x_88;
}
lean_ctor_set(x_89, 0, x_63);
lean_ctor_set(x_89, 1, x_87);
return x_89;
}
}
else
{
lean_object* x_90; lean_object* x_91; 
lean_dec(x_54);
lean_dec(x_5);
x_90 = lean_ctor_get(x_59, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_59, 1);
lean_inc(x_91);
lean_dec(x_59);
x_13 = x_90;
x_14 = x_91;
goto block_40;
}
}
else
{
lean_object* x_92; lean_object* x_93; 
lean_dec(x_54);
lean_dec(x_5);
x_92 = lean_ctor_get(x_56, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_56, 1);
lean_inc(x_93);
lean_dec(x_56);
x_13 = x_92;
x_14 = x_93;
goto block_40;
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_94 = lean_ctor_get(x_44, 0);
x_95 = lean_ctor_get(x_44, 2);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_44);
x_96 = l_Lean_Compiler_Simp_internalize_visitLambda___closed__1;
x_97 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_97, 0, x_94);
lean_ctor_set(x_97, 1, x_96);
lean_ctor_set(x_97, 2, x_95);
x_98 = lean_st_ref_set(x_4, x_97, x_45);
x_99 = lean_ctor_get(x_98, 1);
lean_inc(x_99);
lean_dec(x_98);
x_100 = l_Lean_Compiler_visitLambdaCore(x_1, x_4, x_5, x_6, x_99);
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
lean_dec(x_100);
x_103 = lean_ctor_get(x_101, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_101, 1);
lean_inc(x_104);
lean_dec(x_101);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_103);
x_105 = l_Lean_Compiler_Simp_internalize_visitLet(x_104, x_103, x_2, x_3, x_4, x_5, x_6, x_102);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
lean_dec(x_105);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_108 = l_Lean_Compiler_mkLetUsingScope(x_106, x_4, x_5, x_6, x_107);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_108, 1);
lean_inc(x_110);
lean_dec(x_108);
x_111 = l_Lean_Compiler_mkLambda(x_103, x_109, x_4, x_5, x_6, x_110);
lean_dec(x_5);
lean_dec(x_103);
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_111, 1);
lean_inc(x_113);
lean_dec(x_111);
x_114 = lean_st_ref_get(x_6, x_113);
x_115 = lean_ctor_get(x_114, 1);
lean_inc(x_115);
lean_dec(x_114);
x_116 = lean_st_ref_get(x_4, x_115);
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_116, 1);
lean_inc(x_118);
lean_dec(x_116);
x_119 = lean_ctor_get(x_11, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_11, 1);
lean_inc(x_120);
lean_dec(x_11);
x_121 = lean_ctor_get(x_117, 2);
lean_inc(x_121);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 lean_ctor_release(x_117, 2);
 x_122 = x_117;
} else {
 lean_dec_ref(x_117);
 x_122 = lean_box(0);
}
if (lean_is_scalar(x_122)) {
 x_123 = lean_alloc_ctor(0, 3, 0);
} else {
 x_123 = x_122;
}
lean_ctor_set(x_123, 0, x_119);
lean_ctor_set(x_123, 1, x_120);
lean_ctor_set(x_123, 2, x_121);
x_124 = lean_st_ref_get(x_6, x_118);
lean_dec(x_6);
x_125 = lean_ctor_get(x_124, 1);
lean_inc(x_125);
lean_dec(x_124);
x_126 = lean_st_ref_set(x_4, x_123, x_125);
lean_dec(x_4);
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
if (lean_is_scalar(x_128)) {
 x_129 = lean_alloc_ctor(0, 2, 0);
} else {
 x_129 = x_128;
}
lean_ctor_set(x_129, 0, x_112);
lean_ctor_set(x_129, 1, x_127);
return x_129;
}
else
{
lean_object* x_130; lean_object* x_131; 
lean_dec(x_103);
lean_dec(x_5);
x_130 = lean_ctor_get(x_108, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_108, 1);
lean_inc(x_131);
lean_dec(x_108);
x_13 = x_130;
x_14 = x_131;
goto block_40;
}
}
else
{
lean_object* x_132; lean_object* x_133; 
lean_dec(x_103);
lean_dec(x_5);
x_132 = lean_ctor_get(x_105, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_105, 1);
lean_inc(x_133);
lean_dec(x_105);
x_13 = x_132;
x_14 = x_133;
goto block_40;
}
}
block_40:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_15 = lean_st_ref_get(x_6, x_14);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_st_ref_get(x_4, x_16);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_ctor_get(x_11, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_11, 1);
lean_inc(x_21);
lean_dec(x_11);
x_22 = !lean_is_exclusive(x_18);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_23 = lean_ctor_get(x_18, 1);
lean_dec(x_23);
x_24 = lean_ctor_get(x_18, 0);
lean_dec(x_24);
lean_ctor_set(x_18, 1, x_21);
lean_ctor_set(x_18, 0, x_20);
x_25 = lean_st_ref_get(x_6, x_19);
lean_dec(x_6);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_27 = lean_st_ref_set(x_4, x_18, x_26);
lean_dec(x_4);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_27, 0);
lean_dec(x_29);
lean_ctor_set_tag(x_27, 1);
lean_ctor_set(x_27, 0, x_13);
return x_27;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_dec(x_27);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_13);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_32 = lean_ctor_get(x_18, 2);
lean_inc(x_32);
lean_dec(x_18);
x_33 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_33, 0, x_20);
lean_ctor_set(x_33, 1, x_21);
lean_ctor_set(x_33, 2, x_32);
x_34 = lean_st_ref_get(x_6, x_19);
lean_dec(x_6);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
x_36 = lean_st_ref_set(x_4, x_33, x_35);
lean_dec(x_4);
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_38 = x_36;
} else {
 lean_dec_ref(x_36);
 x_38 = lean_box(0);
}
if (lean_is_scalar(x_38)) {
 x_39 = lean_alloc_ctor(1, 2, 0);
} else {
 x_39 = x_38;
 lean_ctor_set_tag(x_39, 1);
}
lean_ctor_set(x_39, 0, x_13);
lean_ctor_set(x_39, 1, x_37);
return x_39;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_internalize_visitLet___lambda__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_7);
x_14 = l_Lean_Compiler_mkLetDecl(x_1, x_2, x_6, x_3, x_10, x_11, x_12, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_array_push(x_4, x_15);
x_18 = l_Lean_Compiler_Simp_internalize_visitLet(x_5, x_17, x_8, x_9, x_10, x_11, x_12, x_16);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_internalize_visitLet(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_1) == 8)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 2);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 3);
lean_inc(x_12);
x_13 = lean_ctor_get_uint8(x_1, sizeof(void*)*4 + 8);
lean_dec(x_1);
x_14 = l_Lean_Compiler_mkFreshLetVarIdx(x_5, x_6, x_7, x_8);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_expr_instantiate_rev(x_10, x_2);
lean_dec(x_10);
x_18 = lean_expr_instantiate_rev(x_11, x_2);
lean_dec(x_11);
x_19 = l_Lean_Expr_isLambda(x_18);
if (lean_obj_tag(x_9) == 2)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_9, 0);
lean_inc(x_35);
lean_dec(x_9);
x_36 = l_Lean_Name_num___override(x_35, x_15);
x_20 = x_36;
goto block_34;
}
else
{
lean_object* x_37; 
x_37 = l_Lean_Name_num___override(x_9, x_15);
x_20 = x_37;
goto block_34;
}
block_34:
{
if (x_19 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = l_Lean_Compiler_Simp_internalize_visitValue(x_18, x_3, x_4, x_5, x_6, x_7, x_16);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l_Lean_Compiler_Simp_internalize_visitLet___lambda__1(x_20, x_17, x_13, x_2, x_12, x_18, x_22, x_3, x_4, x_5, x_6, x_7, x_23);
return x_24;
}
else
{
lean_object* x_25; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_25 = l_Lean_Compiler_Simp_internalize_visitLambda(x_18, x_3, x_4, x_5, x_6, x_7, x_16);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_box(0);
x_29 = l_Lean_Compiler_Simp_internalize_visitLet___lambda__1(x_20, x_17, x_13, x_2, x_12, x_26, x_28, x_3, x_4, x_5, x_6, x_7, x_27);
return x_29;
}
else
{
uint8_t x_30; 
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_30 = !lean_is_exclusive(x_25);
if (x_30 == 0)
{
return x_25;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_25, 0);
x_32 = lean_ctor_get(x_25, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_25);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_expr_instantiate_rev(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_38);
x_39 = l_Lean_Compiler_isCasesApp_x3f(x_38, x_6, x_7, x_8);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = l_Lean_Compiler_Simp_internalize_visitValue(x_38, x_3, x_4, x_5, x_6, x_7, x_41);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
lean_object* x_44; 
x_44 = lean_ctor_get(x_42, 0);
lean_dec(x_44);
lean_ctor_set(x_42, 0, x_38);
return x_42;
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_42, 1);
lean_inc(x_45);
lean_dec(x_42);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_38);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_39, 1);
lean_inc(x_47);
lean_dec(x_39);
x_48 = lean_ctor_get(x_40, 0);
lean_inc(x_48);
lean_dec(x_40);
x_49 = l_Lean_Compiler_Simp_internalize_visitCases(x_48, x_38, x_3, x_4, x_5, x_6, x_7, x_47);
return x_49;
}
}
else
{
uint8_t x_50; 
lean_dec(x_38);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_50 = !lean_is_exclusive(x_39);
if (x_50 == 0)
{
return x_39;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_39, 0);
x_52 = lean_ctor_get(x_39, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_39);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_Simp_internalize_visitCases___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_nat_dec_le(x_3, x_2);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_eq(x_1, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_sub(x_1, x_15);
lean_dec(x_1);
x_17 = lean_array_get_size(x_5);
x_18 = lean_nat_dec_lt(x_2, x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_nat_add(x_2, x_4);
lean_dec(x_2);
x_1 = x_16;
x_2 = x_19;
goto _start;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_array_fget(x_5, x_2);
x_22 = lean_box(0);
x_23 = lean_array_fset(x_5, x_2, x_22);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_24 = l_Lean_Compiler_Simp_internalize_visitLambda(x_21, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_array_fset(x_23, x_2, x_25);
x_28 = lean_nat_add(x_2, x_4);
lean_dec(x_2);
x_1 = x_16;
x_2 = x_28;
x_5 = x_27;
x_11 = x_26;
goto _start;
}
else
{
uint8_t x_30; 
lean_dec(x_23);
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_30 = !lean_is_exclusive(x_24);
if (x_30 == 0)
{
return x_24;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_24, 0);
x_32 = lean_ctor_get(x_24, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_24);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
else
{
lean_object* x_34; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_5);
lean_ctor_set(x_34, 1, x_11);
return x_34;
}
}
else
{
lean_object* x_35; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_5);
lean_ctor_set(x_35, 1, x_11);
return x_35;
}
}
}
static lean_object* _init_l_Lean_Compiler_Simp_internalize_visitCases___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_levelZero;
x_2 = l_Lean_Expr_sort___override(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_internalize_visitCases(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_2, x_9);
x_11 = l_Lean_Compiler_Simp_internalize_visitCases___closed__1;
lean_inc(x_10);
x_12 = lean_mk_array(x_10, x_11);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_sub(x_10, x_13);
lean_dec(x_10);
lean_inc(x_2);
x_15 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_2, x_12, x_14);
x_16 = lean_ctor_get(x_1, 3);
lean_inc(x_16);
lean_dec(x_1);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 2);
lean_inc(x_19);
lean_dec(x_16);
lean_inc(x_17);
x_20 = l_Std_Range_forIn_loop___at_Lean_Compiler_Simp_internalize_visitCases___spec__1(x_17, x_18, x_17, x_19, x_15, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_19);
lean_dec(x_17);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = l_Lean_Expr_getAppFn(x_2);
lean_dec(x_2);
x_24 = l_Lean_mkAppN(x_23, x_22);
lean_ctor_set(x_20, 0, x_24);
return x_20;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_20, 0);
x_26 = lean_ctor_get(x_20, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_20);
x_27 = l_Lean_Expr_getAppFn(x_2);
lean_dec(x_2);
x_28 = l_Lean_mkAppN(x_27, x_25);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_26);
return x_29;
}
}
else
{
uint8_t x_30; 
lean_dec(x_2);
x_30 = !lean_is_exclusive(x_20);
if (x_30 == 0)
{
return x_20;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_20, 0);
x_32 = lean_ctor_get(x_20, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_20);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_internalize_visitLet___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_3);
lean_dec(x_3);
x_15 = l_Lean_Compiler_Simp_internalize_visitLet___lambda__1(x_1, x_2, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_Simp_internalize_visitCases___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Std_Range_forIn_loop___at_Lean_Compiler_Simp_internalize_visitCases___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_internalize(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_Simp_internalize_visitLambda(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_markSimplified___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_6 = lean_st_ref_get(x_4, x_5);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_st_ref_take(x_1, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
uint8_t x_12; lean_object* x_13; uint8_t x_14; 
x_12 = 1;
lean_ctor_set_uint8(x_9, sizeof(void*)*1, x_12);
x_13 = lean_st_ref_set(x_1, x_9, x_10);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
lean_dec(x_15);
x_16 = lean_box(0);
lean_ctor_set(x_13, 0, x_16);
return x_13;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_13, 1);
lean_inc(x_17);
lean_dec(x_13);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
else
{
lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_20 = lean_ctor_get(x_9, 0);
lean_inc(x_20);
lean_dec(x_9);
x_21 = 1;
x_22 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set_uint8(x_22, sizeof(void*)*1, x_21);
x_23 = lean_st_ref_set(x_1, x_22, x_10);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 x_25 = x_23;
} else {
 lean_dec_ref(x_23);
 x_25 = lean_box(0);
}
x_26 = lean_box(0);
if (lean_is_scalar(x_25)) {
 x_27 = lean_alloc_ctor(0, 2, 0);
} else {
 x_27 = x_25;
}
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_24);
return x_27;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_markSimplified(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Compiler_Simp_markSimplified___rarg___boxed), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_markSimplified___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Compiler_Simp_markSimplified___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_markSimplified___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Compiler_Simp_markSimplified(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_findCtor(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = 1;
x_9 = l_Lean_Compiler_Simp_findExpr(x_1, x_8, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_findCtor___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_Simp_findCtor(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
static lean_object* _init_l_Lean_Compiler_Simp_simpProj_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Init.Util", 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_Simp_simpProj_x3f___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("getElem!", 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_Simp_simpProj_x3f___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("index out of bounds", 19);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_Simp_simpProj_x3f___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Compiler_Simp_simpProj_x3f___closed__1;
x_2 = l_Lean_Compiler_Simp_simpProj_x3f___closed__2;
x_3 = lean_unsigned_to_nat(73u);
x_4 = lean_unsigned_to_nat(36u);
x_5 = l_Lean_Compiler_Simp_simpProj_x3f___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_simpProj_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_1) == 11)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 2);
lean_inc(x_9);
lean_dec(x_1);
x_10 = 1;
x_11 = l_Lean_Compiler_Simp_findExpr(x_9, x_10, x_4, x_5, x_6, x_7);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_st_ref_get(x_6, x_13);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_Expr_constructorApp_x3f(x_18, x_12);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
lean_dec(x_8);
x_20 = lean_box(0);
lean_ctor_set(x_14, 0, x_20);
return x_14;
}
else
{
uint8_t x_21; 
lean_free_object(x_14);
x_21 = !lean_is_exclusive(x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_22 = lean_ctor_get(x_19, 0);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Lean_Compiler_Simp_markSimplified___rarg(x_3, x_4, x_5, x_6, x_17);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_27 = lean_ctor_get(x_25, 0);
lean_dec(x_27);
x_28 = lean_ctor_get(x_23, 3);
lean_inc(x_28);
lean_dec(x_23);
x_29 = lean_nat_add(x_28, x_8);
lean_dec(x_8);
lean_dec(x_28);
x_30 = lean_array_get_size(x_24);
x_31 = lean_nat_dec_lt(x_29, x_30);
lean_dec(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_29);
lean_dec(x_24);
x_32 = l_Lean_Compiler_Simp_simpProj_x3f___closed__4;
x_33 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_32);
lean_ctor_set(x_19, 0, x_33);
lean_ctor_set(x_25, 0, x_19);
return x_25;
}
else
{
lean_object* x_34; 
x_34 = lean_array_fget(x_24, x_29);
lean_dec(x_29);
lean_dec(x_24);
lean_ctor_set(x_19, 0, x_34);
lean_ctor_set(x_25, 0, x_19);
return x_25;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_35 = lean_ctor_get(x_25, 1);
lean_inc(x_35);
lean_dec(x_25);
x_36 = lean_ctor_get(x_23, 3);
lean_inc(x_36);
lean_dec(x_23);
x_37 = lean_nat_add(x_36, x_8);
lean_dec(x_8);
lean_dec(x_36);
x_38 = lean_array_get_size(x_24);
x_39 = lean_nat_dec_lt(x_37, x_38);
lean_dec(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_37);
lean_dec(x_24);
x_40 = l_Lean_Compiler_Simp_simpProj_x3f___closed__4;
x_41 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_40);
lean_ctor_set(x_19, 0, x_41);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_19);
lean_ctor_set(x_42, 1, x_35);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_array_fget(x_24, x_37);
lean_dec(x_37);
lean_dec(x_24);
lean_ctor_set(x_19, 0, x_43);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_19);
lean_ctor_set(x_44, 1, x_35);
return x_44;
}
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_45 = lean_ctor_get(x_19, 0);
lean_inc(x_45);
lean_dec(x_19);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = l_Lean_Compiler_Simp_markSimplified___rarg(x_3, x_4, x_5, x_6, x_17);
x_49 = lean_ctor_get(x_48, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_50 = x_48;
} else {
 lean_dec_ref(x_48);
 x_50 = lean_box(0);
}
x_51 = lean_ctor_get(x_46, 3);
lean_inc(x_51);
lean_dec(x_46);
x_52 = lean_nat_add(x_51, x_8);
lean_dec(x_8);
lean_dec(x_51);
x_53 = lean_array_get_size(x_47);
x_54 = lean_nat_dec_lt(x_52, x_53);
lean_dec(x_53);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_52);
lean_dec(x_47);
x_55 = l_Lean_Compiler_Simp_simpProj_x3f___closed__4;
x_56 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_55);
x_57 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_57, 0, x_56);
if (lean_is_scalar(x_50)) {
 x_58 = lean_alloc_ctor(0, 2, 0);
} else {
 x_58 = x_50;
}
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_49);
return x_58;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_array_fget(x_47, x_52);
lean_dec(x_52);
lean_dec(x_47);
x_60 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_60, 0, x_59);
if (lean_is_scalar(x_50)) {
 x_61 = lean_alloc_ctor(0, 2, 0);
} else {
 x_61 = x_50;
}
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_49);
return x_61;
}
}
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_62 = lean_ctor_get(x_14, 0);
x_63 = lean_ctor_get(x_14, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_14);
x_64 = lean_ctor_get(x_62, 0);
lean_inc(x_64);
lean_dec(x_62);
x_65 = l_Lean_Expr_constructorApp_x3f(x_64, x_12);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; 
lean_dec(x_8);
x_66 = lean_box(0);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_63);
return x_67;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; 
x_68 = lean_ctor_get(x_65, 0);
lean_inc(x_68);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 x_69 = x_65;
} else {
 lean_dec_ref(x_65);
 x_69 = lean_box(0);
}
x_70 = lean_ctor_get(x_68, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_68, 1);
lean_inc(x_71);
lean_dec(x_68);
x_72 = l_Lean_Compiler_Simp_markSimplified___rarg(x_3, x_4, x_5, x_6, x_63);
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
x_75 = lean_ctor_get(x_70, 3);
lean_inc(x_75);
lean_dec(x_70);
x_76 = lean_nat_add(x_75, x_8);
lean_dec(x_8);
lean_dec(x_75);
x_77 = lean_array_get_size(x_71);
x_78 = lean_nat_dec_lt(x_76, x_77);
lean_dec(x_77);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_76);
lean_dec(x_71);
x_79 = l_Lean_Compiler_Simp_simpProj_x3f___closed__4;
x_80 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_79);
if (lean_is_scalar(x_69)) {
 x_81 = lean_alloc_ctor(1, 1, 0);
} else {
 x_81 = x_69;
}
lean_ctor_set(x_81, 0, x_80);
if (lean_is_scalar(x_74)) {
 x_82 = lean_alloc_ctor(0, 2, 0);
} else {
 x_82 = x_74;
}
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_73);
return x_82;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_array_fget(x_71, x_76);
lean_dec(x_76);
lean_dec(x_71);
if (lean_is_scalar(x_69)) {
 x_84 = lean_alloc_ctor(1, 1, 0);
} else {
 x_84 = x_69;
}
lean_ctor_set(x_84, 0, x_83);
if (lean_is_scalar(x_74)) {
 x_85 = lean_alloc_ctor(0, 2, 0);
} else {
 x_85 = x_74;
}
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_73);
return x_85;
}
}
}
}
else
{
lean_object* x_86; lean_object* x_87; 
lean_dec(x_1);
x_86 = lean_box(0);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_7);
return x_87;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_simpProj_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_Simp_simpProj_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
static lean_object* _init_l_Lean_Compiler_Simp_simpAppApp_x3f___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_simpAppApp_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; lean_object* x_10; 
x_8 = l_Lean_Expr_isApp(x_1);
if (x_8 == 0)
{
lean_object* x_139; 
x_139 = lean_box(0);
x_9 = x_139;
x_10 = x_7;
goto block_138;
}
else
{
lean_object* x_140; 
x_140 = l_Lean_Compiler_Simp_simpAppApp_x3f___closed__1;
x_9 = x_140;
x_10 = x_7;
goto block_138;
}
block_138:
{
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_1);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_9);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_9, 0);
lean_dec(x_14);
x_15 = l_Lean_Expr_getAppFn(x_1);
x_16 = l_Lean_Expr_isFVar(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_15);
lean_free_object(x_9);
lean_dec(x_1);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_10);
return x_18;
}
else
{
uint8_t x_19; lean_object* x_20; uint8_t x_21; 
x_19 = 1;
x_20 = l_Lean_Compiler_Simp_findExpr(x_15, x_19, x_4, x_5, x_6, x_10);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_20, 1);
x_24 = l_Lean_Expr_isApp(x_22);
if (x_24 == 0)
{
uint8_t x_25; 
x_25 = l_Lean_Expr_isConst(x_22);
if (x_25 == 0)
{
lean_object* x_26; 
lean_dec(x_22);
lean_free_object(x_9);
lean_dec(x_1);
x_26 = lean_box(0);
lean_ctor_set(x_20, 0, x_26);
return x_20;
}
else
{
lean_object* x_27; uint8_t x_28; 
lean_free_object(x_20);
x_27 = l_Lean_Compiler_Simp_markSimplified___rarg(x_3, x_4, x_5, x_6, x_23);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_29 = lean_ctor_get(x_27, 0);
lean_dec(x_29);
x_30 = lean_unsigned_to_nat(0u);
x_31 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_30);
x_32 = l_Lean_Compiler_Simp_internalize_visitCases___closed__1;
lean_inc(x_31);
x_33 = lean_mk_array(x_31, x_32);
x_34 = lean_unsigned_to_nat(1u);
x_35 = lean_nat_sub(x_31, x_34);
lean_dec(x_31);
x_36 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_33, x_35);
x_37 = l_Lean_mkAppN(x_22, x_36);
lean_ctor_set(x_9, 0, x_37);
lean_ctor_set(x_27, 0, x_9);
return x_27;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_38 = lean_ctor_get(x_27, 1);
lean_inc(x_38);
lean_dec(x_27);
x_39 = lean_unsigned_to_nat(0u);
x_40 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_39);
x_41 = l_Lean_Compiler_Simp_internalize_visitCases___closed__1;
lean_inc(x_40);
x_42 = lean_mk_array(x_40, x_41);
x_43 = lean_unsigned_to_nat(1u);
x_44 = lean_nat_sub(x_40, x_43);
lean_dec(x_40);
x_45 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_42, x_44);
x_46 = l_Lean_mkAppN(x_22, x_45);
lean_ctor_set(x_9, 0, x_46);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_9);
lean_ctor_set(x_47, 1, x_38);
return x_47;
}
}
}
else
{
lean_object* x_48; uint8_t x_49; 
lean_free_object(x_20);
x_48 = l_Lean_Compiler_Simp_markSimplified___rarg(x_3, x_4, x_5, x_6, x_23);
x_49 = !lean_is_exclusive(x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_50 = lean_ctor_get(x_48, 0);
lean_dec(x_50);
x_51 = lean_unsigned_to_nat(0u);
x_52 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_51);
x_53 = l_Lean_Compiler_Simp_internalize_visitCases___closed__1;
lean_inc(x_52);
x_54 = lean_mk_array(x_52, x_53);
x_55 = lean_unsigned_to_nat(1u);
x_56 = lean_nat_sub(x_52, x_55);
lean_dec(x_52);
x_57 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_54, x_56);
x_58 = l_Lean_mkAppN(x_22, x_57);
lean_ctor_set(x_9, 0, x_58);
lean_ctor_set(x_48, 0, x_9);
return x_48;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_59 = lean_ctor_get(x_48, 1);
lean_inc(x_59);
lean_dec(x_48);
x_60 = lean_unsigned_to_nat(0u);
x_61 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_60);
x_62 = l_Lean_Compiler_Simp_internalize_visitCases___closed__1;
lean_inc(x_61);
x_63 = lean_mk_array(x_61, x_62);
x_64 = lean_unsigned_to_nat(1u);
x_65 = lean_nat_sub(x_61, x_64);
lean_dec(x_61);
x_66 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_63, x_65);
x_67 = l_Lean_mkAppN(x_22, x_66);
lean_ctor_set(x_9, 0, x_67);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_9);
lean_ctor_set(x_68, 1, x_59);
return x_68;
}
}
}
else
{
lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_69 = lean_ctor_get(x_20, 0);
x_70 = lean_ctor_get(x_20, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_20);
x_71 = l_Lean_Expr_isApp(x_69);
if (x_71 == 0)
{
uint8_t x_72; 
x_72 = l_Lean_Expr_isConst(x_69);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; 
lean_dec(x_69);
lean_free_object(x_9);
lean_dec(x_1);
x_73 = lean_box(0);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_70);
return x_74;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_75 = l_Lean_Compiler_Simp_markSimplified___rarg(x_3, x_4, x_5, x_6, x_70);
x_76 = lean_ctor_get(x_75, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 x_77 = x_75;
} else {
 lean_dec_ref(x_75);
 x_77 = lean_box(0);
}
x_78 = lean_unsigned_to_nat(0u);
x_79 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_78);
x_80 = l_Lean_Compiler_Simp_internalize_visitCases___closed__1;
lean_inc(x_79);
x_81 = lean_mk_array(x_79, x_80);
x_82 = lean_unsigned_to_nat(1u);
x_83 = lean_nat_sub(x_79, x_82);
lean_dec(x_79);
x_84 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_81, x_83);
x_85 = l_Lean_mkAppN(x_69, x_84);
lean_ctor_set(x_9, 0, x_85);
if (lean_is_scalar(x_77)) {
 x_86 = lean_alloc_ctor(0, 2, 0);
} else {
 x_86 = x_77;
}
lean_ctor_set(x_86, 0, x_9);
lean_ctor_set(x_86, 1, x_76);
return x_86;
}
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_87 = l_Lean_Compiler_Simp_markSimplified___rarg(x_3, x_4, x_5, x_6, x_70);
x_88 = lean_ctor_get(x_87, 1);
lean_inc(x_88);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 lean_ctor_release(x_87, 1);
 x_89 = x_87;
} else {
 lean_dec_ref(x_87);
 x_89 = lean_box(0);
}
x_90 = lean_unsigned_to_nat(0u);
x_91 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_90);
x_92 = l_Lean_Compiler_Simp_internalize_visitCases___closed__1;
lean_inc(x_91);
x_93 = lean_mk_array(x_91, x_92);
x_94 = lean_unsigned_to_nat(1u);
x_95 = lean_nat_sub(x_91, x_94);
lean_dec(x_91);
x_96 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_93, x_95);
x_97 = l_Lean_mkAppN(x_69, x_96);
lean_ctor_set(x_9, 0, x_97);
if (lean_is_scalar(x_89)) {
 x_98 = lean_alloc_ctor(0, 2, 0);
} else {
 x_98 = x_89;
}
lean_ctor_set(x_98, 0, x_9);
lean_ctor_set(x_98, 1, x_88);
return x_98;
}
}
}
}
else
{
lean_object* x_99; uint8_t x_100; 
lean_dec(x_9);
x_99 = l_Lean_Expr_getAppFn(x_1);
x_100 = l_Lean_Expr_isFVar(x_99);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; 
lean_dec(x_99);
lean_dec(x_1);
x_101 = lean_box(0);
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_10);
return x_102;
}
else
{
uint8_t x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; 
x_103 = 1;
x_104 = l_Lean_Compiler_Simp_findExpr(x_99, x_103, x_4, x_5, x_6, x_10);
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_104, 1);
lean_inc(x_106);
if (lean_is_exclusive(x_104)) {
 lean_ctor_release(x_104, 0);
 lean_ctor_release(x_104, 1);
 x_107 = x_104;
} else {
 lean_dec_ref(x_104);
 x_107 = lean_box(0);
}
x_108 = l_Lean_Expr_isApp(x_105);
if (x_108 == 0)
{
uint8_t x_109; 
x_109 = l_Lean_Expr_isConst(x_105);
if (x_109 == 0)
{
lean_object* x_110; lean_object* x_111; 
lean_dec(x_105);
lean_dec(x_1);
x_110 = lean_box(0);
if (lean_is_scalar(x_107)) {
 x_111 = lean_alloc_ctor(0, 2, 0);
} else {
 x_111 = x_107;
}
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_106);
return x_111;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
lean_dec(x_107);
x_112 = l_Lean_Compiler_Simp_markSimplified___rarg(x_3, x_4, x_5, x_6, x_106);
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
x_115 = lean_unsigned_to_nat(0u);
x_116 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_115);
x_117 = l_Lean_Compiler_Simp_internalize_visitCases___closed__1;
lean_inc(x_116);
x_118 = lean_mk_array(x_116, x_117);
x_119 = lean_unsigned_to_nat(1u);
x_120 = lean_nat_sub(x_116, x_119);
lean_dec(x_116);
x_121 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_118, x_120);
x_122 = l_Lean_mkAppN(x_105, x_121);
x_123 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_123, 0, x_122);
if (lean_is_scalar(x_114)) {
 x_124 = lean_alloc_ctor(0, 2, 0);
} else {
 x_124 = x_114;
}
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_113);
return x_124;
}
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
lean_dec(x_107);
x_125 = l_Lean_Compiler_Simp_markSimplified___rarg(x_3, x_4, x_5, x_6, x_106);
x_126 = lean_ctor_get(x_125, 1);
lean_inc(x_126);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 lean_ctor_release(x_125, 1);
 x_127 = x_125;
} else {
 lean_dec_ref(x_125);
 x_127 = lean_box(0);
}
x_128 = lean_unsigned_to_nat(0u);
x_129 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_128);
x_130 = l_Lean_Compiler_Simp_internalize_visitCases___closed__1;
lean_inc(x_129);
x_131 = lean_mk_array(x_129, x_130);
x_132 = lean_unsigned_to_nat(1u);
x_133 = lean_nat_sub(x_129, x_132);
lean_dec(x_129);
x_134 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_131, x_133);
x_135 = l_Lean_mkAppN(x_105, x_134);
x_136 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_136, 0, x_135);
if (lean_is_scalar(x_127)) {
 x_137 = lean_alloc_ctor(0, 2, 0);
} else {
 x_137 = x_127;
}
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_126);
return x_137;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_simpAppApp_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_Simp_simpAppApp_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_shouldInlineLocal(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_st_ref_get(x_6, x_7);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_st_ref_get(x_3, x_9);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_LocalDecl_userName(x_1);
x_16 = l_Std_HashMapImp_find_x3f___at_Lean_Compiler_Simp_OccInfo_add___spec__1(x_14, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_free_object(x_10);
x_17 = l_Lean_LocalDecl_value(x_1);
x_18 = l_Lean_Compiler_lcnfSizeLe(x_17, x_2, x_5, x_6, x_13);
return x_18;
}
else
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_16, 0);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_unbox(x_19);
lean_dec(x_19);
if (x_20 == 0)
{
uint8_t x_21; lean_object* x_22; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_21 = 1;
x_22 = lean_box(x_21);
lean_ctor_set(x_10, 0, x_22);
return x_10;
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_free_object(x_10);
x_23 = l_Lean_LocalDecl_value(x_1);
x_24 = l_Lean_Compiler_lcnfSizeLe(x_23, x_2, x_5, x_6, x_13);
return x_24;
}
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_10, 0);
x_26 = lean_ctor_get(x_10, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_10);
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
lean_dec(x_25);
x_28 = l_Lean_LocalDecl_userName(x_1);
x_29 = l_Std_HashMapImp_find_x3f___at_Lean_Compiler_Simp_OccInfo_add___spec__1(x_27, x_28);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = l_Lean_LocalDecl_value(x_1);
x_31 = l_Lean_Compiler_lcnfSizeLe(x_30, x_2, x_5, x_6, x_26);
return x_31;
}
else
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_ctor_get(x_29, 0);
lean_inc(x_32);
lean_dec(x_29);
x_33 = lean_unbox(x_32);
lean_dec(x_32);
if (x_33 == 0)
{
uint8_t x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_34 = 1;
x_35 = lean_box(x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_26);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = l_Lean_LocalDecl_value(x_1);
x_38 = l_Lean_Compiler_lcnfSizeLe(x_37, x_2, x_5, x_6, x_26);
return x_38;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_shouldInlineLocal___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_Simp_shouldInlineLocal(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_inlineCandidate_x3f___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_ensureUniqueLetVarNames(x_1, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = 1;
x_14 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_14, 0, x_2);
lean_ctor_set(x_14, 1, x_12);
lean_ctor_set_uint8(x_14, sizeof(void*)*2, x_13);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_10, 0, x_15);
return x_10;
}
else
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_10, 0);
x_17 = lean_ctor_get(x_10, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_10);
x_18 = 1;
x_19 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_19, 0, x_2);
lean_ctor_set(x_19, 1, x_16);
lean_ctor_set_uint8(x_19, sizeof(void*)*2, x_18);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_17);
return x_21;
}
}
else
{
uint8_t x_22; 
lean_dec(x_2);
x_22 = !lean_is_exclusive(x_10);
if (x_22 == 0)
{
return x_10;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_10, 0);
x_24 = lean_ctor_get(x_10, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_10);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_inlineCandidate_x3f___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
lean_dec(x_3);
x_10 = lean_unsigned_to_nat(0u);
x_11 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_10);
lean_dec(x_1);
x_12 = l_Lean_LocalDecl_value(x_2);
lean_dec(x_2);
x_13 = l_Lean_Compiler_getLambdaArity(x_12);
x_14 = lean_nat_dec_lt(x_11, x_13);
lean_dec(x_11);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_box(0);
x_16 = l_Lean_Compiler_Simp_inlineCandidate_x3f___lambda__1(x_12, x_13, x_15, x_4, x_5, x_6, x_7, x_8, x_9);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_9);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_inlineCandidate_x3f___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_1, 3);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_dec(x_1);
x_13 = l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParams___spec__1(x_12, x_2, x_11);
lean_dec(x_12);
x_14 = l_Lean_Compiler_ensureUniqueLetVarNames(x_13, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = 0;
x_18 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_18, 0, x_3);
lean_ctor_set(x_18, 1, x_16);
lean_ctor_set_uint8(x_18, sizeof(void*)*2, x_17);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_14, 0, x_19);
return x_14;
}
else
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_14, 0);
x_21 = lean_ctor_get(x_14, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_14);
x_22 = 0;
x_23 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_23, 0, x_3);
lean_ctor_set(x_23, 1, x_20);
lean_ctor_set_uint8(x_23, sizeof(void*)*2, x_22);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_21);
return x_25;
}
}
else
{
uint8_t x_26; 
lean_dec(x_3);
x_26 = !lean_is_exclusive(x_14);
if (x_26 == 0)
{
return x_14;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_14, 0);
x_28 = lean_ctor_get(x_14, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_14);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_inlineCandidate_x3f___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_dec(x_4);
lean_inc(x_9);
lean_inc(x_8);
x_11 = l_Lean_Compiler_getStage1Decl_x3f(x_1, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_11, 0);
lean_dec(x_14);
x_15 = lean_box(0);
lean_ctor_set(x_11, 0, x_15);
return x_11;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_dec(x_11);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_11);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_20 = lean_ctor_get(x_11, 1);
x_21 = lean_ctor_get(x_11, 0);
lean_dec(x_21);
x_22 = lean_ctor_get(x_12, 0);
lean_inc(x_22);
lean_dec(x_12);
x_23 = lean_unsigned_to_nat(0u);
x_24 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_2, x_23);
lean_dec(x_2);
x_25 = l_Lean_Compiler_Decl_getArity(x_22);
x_26 = lean_nat_dec_lt(x_24, x_25);
lean_dec(x_24);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
lean_free_object(x_11);
x_27 = lean_box(0);
x_28 = l_Lean_Compiler_Simp_inlineCandidate_x3f___lambda__3(x_22, x_3, x_25, x_27, x_5, x_6, x_7, x_8, x_9, x_20);
lean_dec(x_3);
return x_28;
}
else
{
lean_object* x_29; 
lean_dec(x_25);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
x_29 = lean_box(0);
lean_ctor_set(x_11, 0, x_29);
return x_11;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_30 = lean_ctor_get(x_11, 1);
lean_inc(x_30);
lean_dec(x_11);
x_31 = lean_ctor_get(x_12, 0);
lean_inc(x_31);
lean_dec(x_12);
x_32 = lean_unsigned_to_nat(0u);
x_33 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_2, x_32);
lean_dec(x_2);
x_34 = l_Lean_Compiler_Decl_getArity(x_31);
x_35 = lean_nat_dec_lt(x_33, x_34);
lean_dec(x_33);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_box(0);
x_37 = l_Lean_Compiler_Simp_inlineCandidate_x3f___lambda__3(x_31, x_3, x_34, x_36, x_5, x_6, x_7, x_8, x_9, x_30);
lean_dec(x_3);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; 
lean_dec(x_34);
lean_dec(x_31);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_30);
return x_39;
}
}
}
}
else
{
uint8_t x_40; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_40 = !lean_is_exclusive(x_11);
if (x_40 == 0)
{
return x_11;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_11, 0);
x_42 = lean_ctor_get(x_11, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_11);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_inlineCandidate_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; 
x_8 = l_Lean_Expr_getAppFn(x_1);
x_9 = 1;
lean_inc(x_8);
x_10 = l_Lean_Compiler_Simp_findExpr(x_8, x_9, x_4, x_5, x_6, x_7);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 4)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
lean_dec(x_8);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = lean_st_ref_get(x_6, x_12);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_21; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_15, 1);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec(x_17);
x_20 = 0;
lean_inc(x_13);
x_21 = l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_hasInlineAttrAux(x_19, x_20, x_13);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_22 = lean_box(0);
lean_ctor_set(x_15, 0, x_22);
return x_15;
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_free_object(x_15);
x_23 = lean_box(0);
x_24 = l_Lean_Compiler_Simp_inlineCandidate_x3f___lambda__4(x_13, x_1, x_14, x_23, x_2, x_3, x_4, x_5, x_6, x_18);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_29; 
x_25 = lean_ctor_get(x_15, 0);
x_26 = lean_ctor_get(x_15, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_15);
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
lean_dec(x_25);
x_28 = 0;
lean_inc(x_13);
x_29 = l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_hasInlineAttrAux(x_27, x_28, x_13);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_26);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_box(0);
x_33 = l_Lean_Compiler_Simp_inlineCandidate_x3f___lambda__4(x_13, x_1, x_14, x_32, x_2, x_3, x_4, x_5, x_6, x_26);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_33;
}
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_11);
x_34 = lean_ctor_get(x_10, 1);
lean_inc(x_34);
lean_dec(x_10);
x_35 = l_Lean_Compiler_Simp_findLambda_x3f(x_8, x_4, x_5, x_6, x_34);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
if (lean_obj_tag(x_36) == 0)
{
uint8_t x_37; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_37 = !lean_is_exclusive(x_35);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_35, 0);
lean_dec(x_38);
x_39 = lean_box(0);
lean_ctor_set(x_35, 0, x_39);
return x_35;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_35, 1);
lean_inc(x_40);
lean_dec(x_35);
x_41 = lean_box(0);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
return x_42;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_35, 1);
lean_inc(x_43);
lean_dec(x_35);
x_44 = lean_ctor_get(x_36, 0);
lean_inc(x_44);
lean_dec(x_36);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_2);
x_45 = l_Lean_Compiler_Simp_shouldInlineLocal(x_44, x_2, x_3, x_4, x_5, x_6, x_43);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; uint8_t x_47; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_unbox(x_46);
lean_dec(x_46);
if (x_47 == 0)
{
uint8_t x_48; 
lean_dec(x_44);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_48 = !lean_is_exclusive(x_45);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_45, 0);
lean_dec(x_49);
x_50 = lean_box(0);
lean_ctor_set(x_45, 0, x_50);
return x_45;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_45, 1);
lean_inc(x_51);
lean_dec(x_45);
x_52 = lean_box(0);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_51);
return x_53;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_45, 1);
lean_inc(x_54);
lean_dec(x_45);
x_55 = lean_box(0);
x_56 = l_Lean_Compiler_Simp_inlineCandidate_x3f___lambda__2(x_1, x_44, x_55, x_2, x_3, x_4, x_5, x_6, x_54);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_56;
}
}
else
{
uint8_t x_57; 
lean_dec(x_44);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_57 = !lean_is_exclusive(x_45);
if (x_57 == 0)
{
return x_45;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_45, 0);
x_59 = lean_ctor_get(x_45, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_45);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_inlineCandidate_x3f___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_Simp_inlineCandidate_x3f___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_inlineCandidate_x3f___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_Simp_inlineCandidate_x3f___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_inlineCandidate_x3f___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Compiler_Simp_inlineCandidate_x3f___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_inlineCandidate_x3f___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Compiler_Simp_inlineCandidate_x3f___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_expandTrivialExpr___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_expandTrivialExpr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = l_Lean_Expr_isFVar(x_1);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
uint8_t x_10; lean_object* x_11; uint8_t x_12; 
x_10 = 1;
lean_inc(x_1);
x_11 = l_Lean_Compiler_Simp_findExpr(x_1, x_10, x_4, x_5, x_6, x_7);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
x_15 = l_Lean_Expr_isLambda(x_13);
if (x_15 == 0)
{
uint8_t x_16; 
x_16 = lean_expr_eqv(x_1, x_13);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
lean_free_object(x_11);
lean_dec(x_1);
x_17 = l_Lean_Compiler_Simp_markSimplified___rarg(x_3, x_4, x_5, x_6, x_14);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
lean_ctor_set(x_17, 0, x_13);
return x_17;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_13);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
else
{
lean_dec(x_13);
lean_ctor_set(x_11, 0, x_1);
return x_11;
}
}
else
{
lean_dec(x_13);
lean_ctor_set(x_11, 0, x_1);
return x_11;
}
}
else
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_11, 0);
x_23 = lean_ctor_get(x_11, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_11);
x_24 = l_Lean_Expr_isLambda(x_22);
if (x_24 == 0)
{
uint8_t x_25; 
x_25 = lean_expr_eqv(x_1, x_22);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_1);
x_26 = l_Lean_Compiler_Simp_markSimplified___rarg(x_3, x_4, x_5, x_6, x_23);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_28 = x_26;
} else {
 lean_dec_ref(x_26);
 x_28 = lean_box(0);
}
if (lean_is_scalar(x_28)) {
 x_29 = lean_alloc_ctor(0, 2, 0);
} else {
 x_29 = x_28;
}
lean_ctor_set(x_29, 0, x_22);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
else
{
lean_object* x_30; 
lean_dec(x_22);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_1);
lean_ctor_set(x_30, 1, x_23);
return x_30;
}
}
else
{
lean_object* x_31; 
lean_dec(x_22);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_1);
lean_ctor_set(x_31, 1, x_23);
return x_31;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_expandTrivialExpr___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_Simp_expandTrivialExpr___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_expandTrivialExpr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_Simp_expandTrivialExpr(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_mkFlatLet_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_5) == 8)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_5, 2);
lean_inc(x_9);
x_10 = lean_ctor_get(x_5, 3);
lean_inc(x_10);
x_11 = lean_ctor_get_uint8(x_5, sizeof(void*)*4 + 8);
lean_dec(x_5);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_6, x_12);
x_14 = l_Lean_Compiler_Simp_mkFlatLet_go(x_1, x_2, x_3, x_4, x_10, x_13);
lean_dec(x_13);
x_15 = l_Lean_Expr_letE___override(x_7, x_8, x_9, x_14, x_11);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_expr_lift_loose_bvars(x_3, x_16, x_6);
x_18 = l_Lean_Expr_letE___override(x_1, x_2, x_5, x_17, x_4);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_mkFlatLet_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_4);
lean_dec(x_4);
x_8 = l_Lean_Compiler_Simp_mkFlatLet_go(x_1, x_2, x_3, x_7, x_5, x_6);
lean_dec(x_6);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_mkFlatLet(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Lean_Compiler_Simp_mkFlatLet_go(x_1, x_2, x_4, x_5, x_3, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_mkFlatLet___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_5);
lean_dec(x_5);
x_7 = l_Lean_Compiler_Simp_mkFlatLet(x_1, x_2, x_3, x_4, x_6);
lean_dec(x_4);
return x_7;
}
}
static lean_object* _init_l_panic___at_Lean_Compiler_Simp_inlineProjInst_x3f_visitProj___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Core_instMonadCoreM;
x_2 = l_ReaderT_instMonadReaderT___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_panic___at_Lean_Compiler_Simp_inlineProjInst_x3f_visitProj___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_panic___at_Lean_Compiler_Simp_inlineProjInst_x3f_visitProj___spec__1___closed__1;
x_2 = l_ReaderT_instMonadReaderT___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_panic___at_Lean_Compiler_Simp_inlineProjInst_x3f_visitProj___spec__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_panic___at_Lean_Compiler_Simp_inlineProjInst_x3f_visitProj___spec__1___closed__2;
x_2 = l_ReaderT_instMonadReaderT___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_panic___at_Lean_Compiler_Simp_inlineProjInst_x3f_visitProj___spec__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_panic___at_Lean_Compiler_Simp_inlineProjInst_x3f_visitProj___spec__1___closed__3;
x_2 = l_OptionT_instMonadOptionT___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_panic___at_Lean_Compiler_Simp_inlineProjInst_x3f_visitProj___spec__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_panic___at_Lean_Compiler_Simp_inlineProjInst_x3f_visitProj___spec__1___closed__4;
x_2 = l_Lean_instInhabitedExpr;
x_3 = l_instInhabited___rarg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_Compiler_Simp_inlineProjInst_x3f_visitProj___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = l_panic___at_Lean_Compiler_Simp_inlineProjInst_x3f_visitProj___spec__1___closed__5;
x_9 = lean_panic_fn(x_8, x_1);
x_10 = lean_apply_6(x_9, x_2, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
static lean_object* _init_l_Lean_Compiler_Simp_inlineProjInst_x3f_visitProj___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Compiler.Simp", 18);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_Simp_inlineProjInst_x3f_visitProj___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Compiler.Simp.inlineProjInst?.visitProj", 44);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_Simp_inlineProjInst_x3f_visitProj___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("unreachable code has been reached", 33);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_Simp_inlineProjInst_x3f_visitProj___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Compiler_Simp_inlineProjInst_x3f_visitProj___closed__1;
x_2 = l_Lean_Compiler_Simp_inlineProjInst_x3f_visitProj___closed__2;
x_3 = lean_unsigned_to_nat(272u);
x_4 = lean_unsigned_to_nat(27u);
x_5 = l_Lean_Compiler_Simp_inlineProjInst_x3f_visitProj___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_inlineProjInst_x3f_visitProj(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_1) == 11)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 2);
lean_inc(x_9);
lean_dec(x_1);
lean_inc(x_6);
x_10 = l_Lean_Compiler_Simp_inlineProjInst_x3f_visit(x_9, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
lean_dec(x_8);
lean_dec(x_6);
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_10, 0);
lean_dec(x_13);
x_14 = lean_box(0);
lean_ctor_set(x_10, 0, x_14);
return x_10;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_dec(x_10);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_ctor_get(x_10, 1);
lean_inc(x_18);
lean_dec(x_10);
x_19 = lean_ctor_get(x_11, 0);
lean_inc(x_19);
lean_dec(x_11);
x_20 = lean_st_ref_get(x_6, x_18);
lean_dec(x_6);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec(x_22);
x_24 = l_Lean_Expr_constructorApp_x3f(x_23, x_19);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; 
lean_dec(x_8);
x_25 = lean_box(0);
lean_ctor_set(x_20, 0, x_25);
return x_20;
}
else
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_24);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_27 = lean_ctor_get(x_24, 0);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_ctor_get(x_28, 3);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_nat_add(x_30, x_8);
lean_dec(x_8);
lean_dec(x_30);
x_32 = lean_array_get_size(x_29);
x_33 = lean_nat_dec_lt(x_31, x_32);
lean_dec(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_31);
lean_dec(x_29);
x_34 = l_Lean_Compiler_Simp_simpProj_x3f___closed__4;
x_35 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_34);
lean_ctor_set(x_24, 0, x_35);
lean_ctor_set(x_20, 0, x_24);
return x_20;
}
else
{
lean_object* x_36; 
x_36 = lean_array_fget(x_29, x_31);
lean_dec(x_31);
lean_dec(x_29);
lean_ctor_set(x_24, 0, x_36);
lean_ctor_set(x_20, 0, x_24);
return x_20;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_37 = lean_ctor_get(x_24, 0);
lean_inc(x_37);
lean_dec(x_24);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_ctor_get(x_38, 3);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_nat_add(x_40, x_8);
lean_dec(x_8);
lean_dec(x_40);
x_42 = lean_array_get_size(x_39);
x_43 = lean_nat_dec_lt(x_41, x_42);
lean_dec(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_41);
lean_dec(x_39);
x_44 = l_Lean_Compiler_Simp_simpProj_x3f___closed__4;
x_45 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_44);
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_20, 0, x_46);
return x_20;
}
else
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_array_fget(x_39, x_41);
lean_dec(x_41);
lean_dec(x_39);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_20, 0, x_48);
return x_20;
}
}
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_49 = lean_ctor_get(x_20, 0);
x_50 = lean_ctor_get(x_20, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_20);
x_51 = lean_ctor_get(x_49, 0);
lean_inc(x_51);
lean_dec(x_49);
x_52 = l_Lean_Expr_constructorApp_x3f(x_51, x_19);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; 
lean_dec(x_8);
x_53 = lean_box(0);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_50);
return x_54;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_55 = lean_ctor_get(x_52, 0);
lean_inc(x_55);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 x_56 = x_52;
} else {
 lean_dec_ref(x_52);
 x_56 = lean_box(0);
}
x_57 = lean_ctor_get(x_55, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_55, 1);
lean_inc(x_58);
lean_dec(x_55);
x_59 = lean_ctor_get(x_57, 3);
lean_inc(x_59);
lean_dec(x_57);
x_60 = lean_nat_add(x_59, x_8);
lean_dec(x_8);
lean_dec(x_59);
x_61 = lean_array_get_size(x_58);
x_62 = lean_nat_dec_lt(x_60, x_61);
lean_dec(x_61);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_60);
lean_dec(x_58);
x_63 = l_Lean_Compiler_Simp_simpProj_x3f___closed__4;
x_64 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_63);
if (lean_is_scalar(x_56)) {
 x_65 = lean_alloc_ctor(1, 1, 0);
} else {
 x_65 = x_56;
}
lean_ctor_set(x_65, 0, x_64);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_50);
return x_66;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_array_fget(x_58, x_60);
lean_dec(x_60);
lean_dec(x_58);
if (lean_is_scalar(x_56)) {
 x_68 = lean_alloc_ctor(1, 1, 0);
} else {
 x_68 = x_56;
}
lean_ctor_set(x_68, 0, x_67);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_50);
return x_69;
}
}
}
}
}
else
{
uint8_t x_70; 
lean_dec(x_8);
lean_dec(x_6);
x_70 = !lean_is_exclusive(x_10);
if (x_70 == 0)
{
return x_10;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_10, 0);
x_72 = lean_ctor_get(x_10, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_10);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
}
else
{
lean_object* x_74; lean_object* x_75; 
lean_dec(x_1);
x_74 = l_Lean_Compiler_Simp_inlineProjInst_x3f_visitProj___closed__4;
x_75 = l_panic___at_Lean_Compiler_Simp_inlineProjInst_x3f_visitProj___spec__1(x_74, x_2, x_3, x_4, x_5, x_6, x_7);
return x_75;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_visitLetImp_go___at_Lean_Compiler_Simp_inlineProjInst_x3f_visit___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_1) == 8)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 2);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 3);
lean_inc(x_10);
x_11 = lean_ctor_get_uint8(x_1, sizeof(void*)*4 + 8);
lean_dec(x_1);
x_12 = lean_expr_instantiate_rev(x_8, x_2);
lean_dec(x_8);
x_13 = lean_expr_instantiate_rev(x_9, x_2);
lean_dec(x_9);
x_14 = l_Lean_Compiler_mkLetDecl(x_7, x_12, x_13, x_11, x_3, x_4, x_5, x_6);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_array_push(x_2, x_15);
x_1 = x_10;
x_2 = x_17;
x_6 = x_16;
goto _start;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_expr_instantiate_rev(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_6);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_inlineProjInst_x3f_visit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_8 = 1;
x_9 = l_Lean_Compiler_Simp_findExpr(x_1, x_8, x_4, x_5, x_6, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_st_ref_get(x_6, x_11);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_Expr_isConstructorApp(x_16, x_10);
if (x_17 == 0)
{
uint8_t x_18; 
x_18 = l_Lean_Expr_isProj(x_10);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = l_Lean_Expr_getAppFn(x_10);
if (lean_obj_tag(x_19) == 4)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_free_object(x_12);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
lean_inc(x_6);
lean_inc(x_5);
x_22 = l_Lean_Compiler_getStage1Decl_x3f(x_20, x_5, x_6, x_15);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
lean_dec(x_21);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_24 = !lean_is_exclusive(x_22);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_22, 0);
lean_dec(x_25);
x_26 = lean_box(0);
lean_ctor_set(x_22, 0, x_26);
return x_22;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_22, 1);
lean_inc(x_27);
lean_dec(x_22);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
}
else
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_22);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_31 = lean_ctor_get(x_22, 1);
x_32 = lean_ctor_get(x_22, 0);
lean_dec(x_32);
x_33 = lean_ctor_get(x_23, 0);
lean_inc(x_33);
lean_dec(x_23);
x_34 = l_Lean_Compiler_Decl_getArity(x_33);
x_35 = lean_unsigned_to_nat(0u);
x_36 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_10, x_35);
x_37 = lean_nat_dec_eq(x_34, x_36);
lean_dec(x_34);
if (x_37 == 0)
{
lean_object* x_38; 
lean_dec(x_36);
lean_dec(x_33);
lean_dec(x_21);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_38 = lean_box(0);
lean_ctor_set(x_22, 0, x_38);
return x_22;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_free_object(x_22);
x_39 = lean_ctor_get(x_33, 3);
lean_inc(x_39);
x_40 = lean_ctor_get(x_33, 1);
lean_inc(x_40);
lean_dec(x_33);
x_41 = l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParams___spec__1(x_40, x_21, x_39);
lean_dec(x_21);
lean_dec(x_40);
x_42 = l_Lean_Compiler_Simp_internalize_visitCases___closed__1;
lean_inc(x_36);
x_43 = lean_mk_array(x_36, x_42);
x_44 = lean_unsigned_to_nat(1u);
x_45 = lean_nat_sub(x_36, x_44);
lean_dec(x_36);
x_46 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_10, x_43, x_45);
x_47 = l_Lean_Expr_beta(x_41, x_46);
x_48 = l_Lean_Compiler_Simp_internalize_visitLambda___closed__1;
x_49 = l_Lean_Compiler_visitLetImp_go___at_Lean_Compiler_Simp_inlineProjInst_x3f_visit___spec__1(x_47, x_48, x_4, x_5, x_6, x_31);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_1 = x_50;
x_7 = x_51;
goto _start;
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_53 = lean_ctor_get(x_22, 1);
lean_inc(x_53);
lean_dec(x_22);
x_54 = lean_ctor_get(x_23, 0);
lean_inc(x_54);
lean_dec(x_23);
x_55 = l_Lean_Compiler_Decl_getArity(x_54);
x_56 = lean_unsigned_to_nat(0u);
x_57 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_10, x_56);
x_58 = lean_nat_dec_eq(x_55, x_57);
lean_dec(x_55);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; 
lean_dec(x_57);
lean_dec(x_54);
lean_dec(x_21);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_59 = lean_box(0);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_53);
return x_60;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_61 = lean_ctor_get(x_54, 3);
lean_inc(x_61);
x_62 = lean_ctor_get(x_54, 1);
lean_inc(x_62);
lean_dec(x_54);
x_63 = l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParams___spec__1(x_62, x_21, x_61);
lean_dec(x_21);
lean_dec(x_62);
x_64 = l_Lean_Compiler_Simp_internalize_visitCases___closed__1;
lean_inc(x_57);
x_65 = lean_mk_array(x_57, x_64);
x_66 = lean_unsigned_to_nat(1u);
x_67 = lean_nat_sub(x_57, x_66);
lean_dec(x_57);
x_68 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_10, x_65, x_67);
x_69 = l_Lean_Expr_beta(x_63, x_68);
x_70 = l_Lean_Compiler_Simp_internalize_visitLambda___closed__1;
x_71 = l_Lean_Compiler_visitLetImp_go___at_Lean_Compiler_Simp_inlineProjInst_x3f_visit___spec__1(x_69, x_70, x_4, x_5, x_6, x_53);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec(x_71);
x_1 = x_72;
x_7 = x_73;
goto _start;
}
}
}
}
else
{
uint8_t x_75; 
lean_dec(x_21);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_75 = !lean_is_exclusive(x_22);
if (x_75 == 0)
{
return x_22;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_22, 0);
x_77 = lean_ctor_get(x_22, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_22);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
}
else
{
lean_object* x_79; 
lean_dec(x_19);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_79 = lean_box(0);
lean_ctor_set(x_12, 0, x_79);
return x_12;
}
}
else
{
lean_object* x_80; 
lean_free_object(x_12);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_80 = l_Lean_Compiler_Simp_inlineProjInst_x3f_visitProj(x_10, x_2, x_3, x_4, x_5, x_6, x_15);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; 
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
if (lean_obj_tag(x_81) == 0)
{
uint8_t x_82; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_82 = !lean_is_exclusive(x_80);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_80, 0);
lean_dec(x_83);
x_84 = lean_box(0);
lean_ctor_set(x_80, 0, x_84);
return x_80;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_80, 1);
lean_inc(x_85);
lean_dec(x_80);
x_86 = lean_box(0);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_85);
return x_87;
}
}
else
{
lean_object* x_88; lean_object* x_89; 
x_88 = lean_ctor_get(x_80, 1);
lean_inc(x_88);
lean_dec(x_80);
x_89 = lean_ctor_get(x_81, 0);
lean_inc(x_89);
lean_dec(x_81);
x_1 = x_89;
x_7 = x_88;
goto _start;
}
}
else
{
uint8_t x_91; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_91 = !lean_is_exclusive(x_80);
if (x_91 == 0)
{
return x_80;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_80, 0);
x_93 = lean_ctor_get(x_80, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_80);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
return x_94;
}
}
}
}
else
{
lean_object* x_95; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_95 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_95, 0, x_10);
lean_ctor_set(x_12, 0, x_95);
return x_12;
}
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; uint8_t x_99; 
x_96 = lean_ctor_get(x_12, 0);
x_97 = lean_ctor_get(x_12, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_12);
x_98 = lean_ctor_get(x_96, 0);
lean_inc(x_98);
lean_dec(x_96);
x_99 = l_Lean_Expr_isConstructorApp(x_98, x_10);
if (x_99 == 0)
{
uint8_t x_100; 
x_100 = l_Lean_Expr_isProj(x_10);
if (x_100 == 0)
{
lean_object* x_101; 
x_101 = l_Lean_Expr_getAppFn(x_10);
if (lean_obj_tag(x_101) == 4)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_101, 1);
lean_inc(x_103);
lean_dec(x_101);
lean_inc(x_6);
lean_inc(x_5);
x_104 = l_Lean_Compiler_getStage1Decl_x3f(x_102, x_5, x_6, x_97);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; 
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
lean_dec(x_103);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_106 = lean_ctor_get(x_104, 1);
lean_inc(x_106);
if (lean_is_exclusive(x_104)) {
 lean_ctor_release(x_104, 0);
 lean_ctor_release(x_104, 1);
 x_107 = x_104;
} else {
 lean_dec_ref(x_104);
 x_107 = lean_box(0);
}
x_108 = lean_box(0);
if (lean_is_scalar(x_107)) {
 x_109 = lean_alloc_ctor(0, 2, 0);
} else {
 x_109 = x_107;
}
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_106);
return x_109;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; 
x_110 = lean_ctor_get(x_104, 1);
lean_inc(x_110);
if (lean_is_exclusive(x_104)) {
 lean_ctor_release(x_104, 0);
 lean_ctor_release(x_104, 1);
 x_111 = x_104;
} else {
 lean_dec_ref(x_104);
 x_111 = lean_box(0);
}
x_112 = lean_ctor_get(x_105, 0);
lean_inc(x_112);
lean_dec(x_105);
x_113 = l_Lean_Compiler_Decl_getArity(x_112);
x_114 = lean_unsigned_to_nat(0u);
x_115 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_10, x_114);
x_116 = lean_nat_dec_eq(x_113, x_115);
lean_dec(x_113);
if (x_116 == 0)
{
lean_object* x_117; lean_object* x_118; 
lean_dec(x_115);
lean_dec(x_112);
lean_dec(x_103);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_117 = lean_box(0);
if (lean_is_scalar(x_111)) {
 x_118 = lean_alloc_ctor(0, 2, 0);
} else {
 x_118 = x_111;
}
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_110);
return x_118;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
lean_dec(x_111);
x_119 = lean_ctor_get(x_112, 3);
lean_inc(x_119);
x_120 = lean_ctor_get(x_112, 1);
lean_inc(x_120);
lean_dec(x_112);
x_121 = l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParams___spec__1(x_120, x_103, x_119);
lean_dec(x_103);
lean_dec(x_120);
x_122 = l_Lean_Compiler_Simp_internalize_visitCases___closed__1;
lean_inc(x_115);
x_123 = lean_mk_array(x_115, x_122);
x_124 = lean_unsigned_to_nat(1u);
x_125 = lean_nat_sub(x_115, x_124);
lean_dec(x_115);
x_126 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_10, x_123, x_125);
x_127 = l_Lean_Expr_beta(x_121, x_126);
x_128 = l_Lean_Compiler_Simp_internalize_visitLambda___closed__1;
x_129 = l_Lean_Compiler_visitLetImp_go___at_Lean_Compiler_Simp_inlineProjInst_x3f_visit___spec__1(x_127, x_128, x_4, x_5, x_6, x_110);
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_129, 1);
lean_inc(x_131);
lean_dec(x_129);
x_1 = x_130;
x_7 = x_131;
goto _start;
}
}
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
lean_dec(x_103);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_133 = lean_ctor_get(x_104, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_104, 1);
lean_inc(x_134);
if (lean_is_exclusive(x_104)) {
 lean_ctor_release(x_104, 0);
 lean_ctor_release(x_104, 1);
 x_135 = x_104;
} else {
 lean_dec_ref(x_104);
 x_135 = lean_box(0);
}
if (lean_is_scalar(x_135)) {
 x_136 = lean_alloc_ctor(1, 2, 0);
} else {
 x_136 = x_135;
}
lean_ctor_set(x_136, 0, x_133);
lean_ctor_set(x_136, 1, x_134);
return x_136;
}
}
else
{
lean_object* x_137; lean_object* x_138; 
lean_dec(x_101);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_137 = lean_box(0);
x_138 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_138, 0, x_137);
lean_ctor_set(x_138, 1, x_97);
return x_138;
}
}
else
{
lean_object* x_139; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_139 = l_Lean_Compiler_Simp_inlineProjInst_x3f_visitProj(x_10, x_2, x_3, x_4, x_5, x_6, x_97);
if (lean_obj_tag(x_139) == 0)
{
lean_object* x_140; 
x_140 = lean_ctor_get(x_139, 0);
lean_inc(x_140);
if (lean_obj_tag(x_140) == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_141 = lean_ctor_get(x_139, 1);
lean_inc(x_141);
if (lean_is_exclusive(x_139)) {
 lean_ctor_release(x_139, 0);
 lean_ctor_release(x_139, 1);
 x_142 = x_139;
} else {
 lean_dec_ref(x_139);
 x_142 = lean_box(0);
}
x_143 = lean_box(0);
if (lean_is_scalar(x_142)) {
 x_144 = lean_alloc_ctor(0, 2, 0);
} else {
 x_144 = x_142;
}
lean_ctor_set(x_144, 0, x_143);
lean_ctor_set(x_144, 1, x_141);
return x_144;
}
else
{
lean_object* x_145; lean_object* x_146; 
x_145 = lean_ctor_get(x_139, 1);
lean_inc(x_145);
lean_dec(x_139);
x_146 = lean_ctor_get(x_140, 0);
lean_inc(x_146);
lean_dec(x_140);
x_1 = x_146;
x_7 = x_145;
goto _start;
}
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_148 = lean_ctor_get(x_139, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_139, 1);
lean_inc(x_149);
if (lean_is_exclusive(x_139)) {
 lean_ctor_release(x_139, 0);
 lean_ctor_release(x_139, 1);
 x_150 = x_139;
} else {
 lean_dec_ref(x_139);
 x_150 = lean_box(0);
}
if (lean_is_scalar(x_150)) {
 x_151 = lean_alloc_ctor(1, 2, 0);
} else {
 x_151 = x_150;
}
lean_ctor_set(x_151, 0, x_148);
lean_ctor_set(x_151, 1, x_149);
return x_151;
}
}
}
else
{
lean_object* x_152; lean_object* x_153; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_152 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_152, 0, x_10);
x_153 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_153, 0, x_152);
lean_ctor_set(x_153, 1, x_97);
return x_153;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_visitLetImp_go___at_Lean_Compiler_Simp_inlineProjInst_x3f_visit___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_visitLetImp_go___at_Lean_Compiler_Simp_inlineProjInst_x3f_visit___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_inlineProjInst_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_1) == 11)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = lean_ctor_get(x_1, 2);
lean_inc(x_8);
x_9 = lean_st_ref_get(x_6, x_7);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_st_ref_get(x_4, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
lean_inc(x_6);
lean_inc(x_5);
x_15 = l_Lean_Compiler_InferType_inferType(x_8, x_14, x_5, x_6, x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_Compiler_isClass_x3f(x_16, x_5, x_6, x_17);
lean_dec(x_16);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_20 = !lean_is_exclusive(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_18, 0);
lean_dec(x_21);
x_22 = lean_box(0);
lean_ctor_set(x_18, 0, x_22);
return x_18;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_18, 1);
lean_inc(x_23);
lean_dec(x_18);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_19);
x_26 = lean_ctor_get(x_18, 1);
lean_inc(x_26);
lean_dec(x_18);
x_27 = lean_st_ref_get(x_6, x_26);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_st_ref_get(x_4, x_28);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_ctor_get(x_30, 0);
lean_inc(x_32);
lean_dec(x_30);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_33 = l_Lean_Compiler_InferType_inferType(x_1, x_32, x_5, x_6, x_31);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = l_Lean_Compiler_isClass_x3f(x_34, x_5, x_6, x_35);
lean_dec(x_34);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_104; lean_object* x_105; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_80 = lean_st_ref_get(x_6, x_38);
x_81 = lean_ctor_get(x_80, 1);
lean_inc(x_81);
lean_dec(x_80);
x_82 = lean_st_ref_get(x_4, x_81);
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec(x_82);
x_123 = lean_st_ref_get(x_6, x_84);
x_124 = lean_ctor_get(x_123, 1);
lean_inc(x_124);
lean_dec(x_123);
x_125 = lean_st_ref_take(x_4, x_124);
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_125, 1);
lean_inc(x_127);
lean_dec(x_125);
x_128 = lean_ctor_get(x_126, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_126, 2);
lean_inc(x_129);
lean_dec(x_126);
x_130 = l_Lean_Compiler_Simp_internalize_visitLambda___closed__1;
x_131 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_131, 0, x_128);
lean_ctor_set(x_131, 1, x_130);
lean_ctor_set(x_131, 2, x_129);
x_132 = lean_st_ref_set(x_4, x_131, x_127);
x_133 = lean_ctor_get(x_132, 1);
lean_inc(x_133);
lean_dec(x_132);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_134 = l_Lean_Compiler_Simp_inlineProjInst_x3f_visitProj(x_1, x_2, x_3, x_4, x_5, x_6, x_133);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_135; 
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
if (lean_obj_tag(x_135) == 0)
{
lean_object* x_136; lean_object* x_137; 
x_136 = lean_ctor_get(x_134, 1);
lean_inc(x_136);
lean_dec(x_134);
x_137 = lean_box(0);
x_85 = x_137;
x_86 = x_136;
goto block_103;
}
else
{
lean_object* x_138; uint8_t x_139; 
x_138 = lean_ctor_get(x_134, 1);
lean_inc(x_138);
lean_dec(x_134);
x_139 = !lean_is_exclusive(x_135);
if (x_139 == 0)
{
lean_object* x_140; lean_object* x_141; 
x_140 = lean_ctor_get(x_135, 0);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_141 = l_Lean_Compiler_mkLetUsingScope(x_140, x_4, x_5, x_6, x_138);
if (lean_obj_tag(x_141) == 0)
{
lean_object* x_142; lean_object* x_143; 
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_141, 1);
lean_inc(x_143);
lean_dec(x_141);
lean_ctor_set(x_135, 0, x_142);
x_85 = x_135;
x_86 = x_143;
goto block_103;
}
else
{
lean_object* x_144; lean_object* x_145; 
lean_free_object(x_135);
x_144 = lean_ctor_get(x_141, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_141, 1);
lean_inc(x_145);
lean_dec(x_141);
x_104 = x_144;
x_105 = x_145;
goto block_122;
}
}
else
{
lean_object* x_146; lean_object* x_147; 
x_146 = lean_ctor_get(x_135, 0);
lean_inc(x_146);
lean_dec(x_135);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_147 = l_Lean_Compiler_mkLetUsingScope(x_146, x_4, x_5, x_6, x_138);
if (lean_obj_tag(x_147) == 0)
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_148 = lean_ctor_get(x_147, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_147, 1);
lean_inc(x_149);
lean_dec(x_147);
x_150 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_150, 0, x_148);
x_85 = x_150;
x_86 = x_149;
goto block_103;
}
else
{
lean_object* x_151; lean_object* x_152; 
x_151 = lean_ctor_get(x_147, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_147, 1);
lean_inc(x_152);
lean_dec(x_147);
x_104 = x_151;
x_105 = x_152;
goto block_122;
}
}
}
}
else
{
lean_object* x_153; lean_object* x_154; 
x_153 = lean_ctor_get(x_134, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_134, 1);
lean_inc(x_154);
lean_dec(x_134);
x_104 = x_153;
x_105 = x_154;
goto block_122;
}
block_79:
{
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
if (lean_obj_tag(x_40) == 0)
{
uint8_t x_41; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_41 = !lean_is_exclusive(x_39);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_39, 0);
lean_dec(x_42);
x_43 = lean_box(0);
lean_ctor_set(x_39, 0, x_43);
return x_39;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_39, 1);
lean_inc(x_44);
lean_dec(x_39);
x_45 = lean_box(0);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_44);
return x_46;
}
}
else
{
lean_object* x_47; uint8_t x_48; 
x_47 = lean_ctor_get(x_39, 1);
lean_inc(x_47);
lean_dec(x_39);
x_48 = !lean_is_exclusive(x_40);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_49 = lean_ctor_get(x_40, 0);
x_50 = l_Lean_Compiler_Simp_markSimplified___rarg(x_3, x_4, x_5, x_6, x_47);
x_51 = lean_ctor_get(x_50, 1);
lean_inc(x_51);
lean_dec(x_50);
x_52 = l_Lean_Compiler_Simp_internalize_visitLambda(x_49, x_2, x_3, x_4, x_5, x_6, x_51);
if (lean_obj_tag(x_52) == 0)
{
uint8_t x_53; 
x_53 = !lean_is_exclusive(x_52);
if (x_53 == 0)
{
lean_object* x_54; 
x_54 = lean_ctor_get(x_52, 0);
lean_ctor_set(x_40, 0, x_54);
lean_ctor_set(x_52, 0, x_40);
return x_52;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_52, 0);
x_56 = lean_ctor_get(x_52, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_52);
lean_ctor_set(x_40, 0, x_55);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_40);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
else
{
uint8_t x_58; 
lean_free_object(x_40);
x_58 = !lean_is_exclusive(x_52);
if (x_58 == 0)
{
return x_52;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_52, 0);
x_60 = lean_ctor_get(x_52, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_52);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_62 = lean_ctor_get(x_40, 0);
lean_inc(x_62);
lean_dec(x_40);
x_63 = l_Lean_Compiler_Simp_markSimplified___rarg(x_3, x_4, x_5, x_6, x_47);
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
lean_dec(x_63);
x_65 = l_Lean_Compiler_Simp_internalize_visitLambda(x_62, x_2, x_3, x_4, x_5, x_6, x_64);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_68 = x_65;
} else {
 lean_dec_ref(x_65);
 x_68 = lean_box(0);
}
x_69 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_69, 0, x_66);
if (lean_is_scalar(x_68)) {
 x_70 = lean_alloc_ctor(0, 2, 0);
} else {
 x_70 = x_68;
}
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_67);
return x_70;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_71 = lean_ctor_get(x_65, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_65, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_73 = x_65;
} else {
 lean_dec_ref(x_65);
 x_73 = lean_box(0);
}
if (lean_is_scalar(x_73)) {
 x_74 = lean_alloc_ctor(1, 2, 0);
} else {
 x_74 = x_73;
}
lean_ctor_set(x_74, 0, x_71);
lean_ctor_set(x_74, 1, x_72);
return x_74;
}
}
}
}
else
{
uint8_t x_75; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_75 = !lean_is_exclusive(x_39);
if (x_75 == 0)
{
return x_39;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_39, 0);
x_77 = lean_ctor_get(x_39, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_39);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
}
block_103:
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; uint8_t x_99; 
x_87 = lean_st_ref_get(x_6, x_86);
x_88 = lean_ctor_get(x_87, 1);
lean_inc(x_88);
lean_dec(x_87);
x_89 = lean_st_ref_get(x_4, x_88);
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
lean_dec(x_89);
x_92 = lean_ctor_get(x_83, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_83, 1);
lean_inc(x_93);
lean_dec(x_83);
x_94 = lean_ctor_get(x_90, 2);
lean_inc(x_94);
lean_dec(x_90);
x_95 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_95, 0, x_92);
lean_ctor_set(x_95, 1, x_93);
lean_ctor_set(x_95, 2, x_94);
x_96 = lean_st_ref_get(x_6, x_91);
x_97 = lean_ctor_get(x_96, 1);
lean_inc(x_97);
lean_dec(x_96);
x_98 = lean_st_ref_set(x_4, x_95, x_97);
x_99 = !lean_is_exclusive(x_98);
if (x_99 == 0)
{
lean_object* x_100; 
x_100 = lean_ctor_get(x_98, 0);
lean_dec(x_100);
lean_ctor_set(x_98, 0, x_85);
x_39 = x_98;
goto block_79;
}
else
{
lean_object* x_101; lean_object* x_102; 
x_101 = lean_ctor_get(x_98, 1);
lean_inc(x_101);
lean_dec(x_98);
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_85);
lean_ctor_set(x_102, 1, x_101);
x_39 = x_102;
goto block_79;
}
}
block_122:
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; uint8_t x_118; 
x_106 = lean_st_ref_get(x_6, x_105);
x_107 = lean_ctor_get(x_106, 1);
lean_inc(x_107);
lean_dec(x_106);
x_108 = lean_st_ref_get(x_4, x_107);
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_108, 1);
lean_inc(x_110);
lean_dec(x_108);
x_111 = lean_ctor_get(x_83, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_83, 1);
lean_inc(x_112);
lean_dec(x_83);
x_113 = lean_ctor_get(x_109, 2);
lean_inc(x_113);
lean_dec(x_109);
x_114 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_114, 0, x_111);
lean_ctor_set(x_114, 1, x_112);
lean_ctor_set(x_114, 2, x_113);
x_115 = lean_st_ref_get(x_6, x_110);
x_116 = lean_ctor_get(x_115, 1);
lean_inc(x_116);
lean_dec(x_115);
x_117 = lean_st_ref_set(x_4, x_114, x_116);
x_118 = !lean_is_exclusive(x_117);
if (x_118 == 0)
{
lean_object* x_119; 
x_119 = lean_ctor_get(x_117, 0);
lean_dec(x_119);
lean_ctor_set_tag(x_117, 1);
lean_ctor_set(x_117, 0, x_104);
x_39 = x_117;
goto block_79;
}
else
{
lean_object* x_120; lean_object* x_121; 
x_120 = lean_ctor_get(x_117, 1);
lean_inc(x_120);
lean_dec(x_117);
x_121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_121, 0, x_104);
lean_ctor_set(x_121, 1, x_120);
x_39 = x_121;
goto block_79;
}
}
}
else
{
uint8_t x_155; 
lean_dec(x_37);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_155 = !lean_is_exclusive(x_36);
if (x_155 == 0)
{
lean_object* x_156; lean_object* x_157; 
x_156 = lean_ctor_get(x_36, 0);
lean_dec(x_156);
x_157 = lean_box(0);
lean_ctor_set(x_36, 0, x_157);
return x_36;
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_158 = lean_ctor_get(x_36, 1);
lean_inc(x_158);
lean_dec(x_36);
x_159 = lean_box(0);
x_160 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_160, 0, x_159);
lean_ctor_set(x_160, 1, x_158);
return x_160;
}
}
}
else
{
uint8_t x_161; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_161 = !lean_is_exclusive(x_33);
if (x_161 == 0)
{
return x_33;
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_162 = lean_ctor_get(x_33, 0);
x_163 = lean_ctor_get(x_33, 1);
lean_inc(x_163);
lean_inc(x_162);
lean_dec(x_33);
x_164 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_164, 0, x_162);
lean_ctor_set(x_164, 1, x_163);
return x_164;
}
}
}
}
else
{
uint8_t x_165; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_165 = !lean_is_exclusive(x_15);
if (x_165 == 0)
{
return x_15;
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_166 = lean_ctor_get(x_15, 0);
x_167 = lean_ctor_get(x_15, 1);
lean_inc(x_167);
lean_inc(x_166);
lean_dec(x_15);
x_168 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_168, 0, x_166);
lean_ctor_set(x_168, 1, x_167);
return x_168;
}
}
}
else
{
lean_object* x_169; lean_object* x_170; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_169 = lean_box(0);
x_170 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_170, 0, x_169);
lean_ctor_set(x_170, 1, x_7);
return x_170;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_betaReduce(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = l_Lean_Expr_beta(x_1, x_2);
x_10 = l_Lean_Compiler_Simp_internalize_visitLambda(x_9, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_findDecl_x3f___at_Lean_Compiler_Simp_simpCasesOnCases_x3f_isJpCtor_x3f___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_st_ref_get(x_6, x_7);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_st_ref_get(x_4, x_9);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_local_ctx_find(x_13, x_1);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_10, 0, x_15);
return x_10;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_10, 0);
x_17 = lean_ctor_get(x_10, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_10);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_local_ctx_find(x_18, x_1);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_17);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_simpCasesOnCases_x3f_isJpCtor_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 6:
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_1, 2);
lean_inc(x_8);
lean_dec(x_1);
x_1 = x_8;
goto _start;
}
case 8:
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_1, 3);
lean_inc(x_10);
switch (lean_obj_tag(x_10)) {
case 5:
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 1)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_13 = lean_ctor_get(x_1, 2);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_ctor_get(x_11, 0);
lean_inc(x_14);
lean_dec(x_11);
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_nat_dec_eq(x_15, x_16);
lean_dec(x_15);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_14);
lean_dec(x_13);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_7);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_inc(x_14);
x_20 = l_Lean_Compiler_findDecl_x3f___at_Lean_Compiler_Simp_simpCasesOnCases_x3f_isJpCtor_x3f___spec__1(x_14, x_2, x_3, x_4, x_5, x_6, x_7);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec(x_21);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
lean_dec(x_14);
lean_dec(x_13);
x_23 = !lean_is_exclusive(x_20);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_20, 0);
lean_dec(x_24);
x_25 = lean_box(0);
lean_ctor_set(x_20, 0, x_25);
return x_20;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_20, 1);
lean_inc(x_26);
lean_dec(x_20);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
else
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_20);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_30 = lean_ctor_get(x_20, 1);
x_31 = lean_ctor_get(x_20, 0);
lean_dec(x_31);
x_32 = !lean_is_exclusive(x_22);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_22, 0);
x_34 = l_Lean_LocalDecl_isJp(x_33);
lean_dec(x_33);
if (x_34 == 0)
{
lean_object* x_35; 
lean_free_object(x_22);
lean_dec(x_14);
lean_dec(x_13);
x_35 = lean_box(0);
lean_ctor_set(x_20, 0, x_35);
return x_20;
}
else
{
lean_object* x_36; uint8_t x_37; 
lean_free_object(x_20);
x_36 = lean_st_ref_get(x_6, x_30);
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_38 = lean_ctor_get(x_36, 0);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
lean_dec(x_38);
x_40 = l_Lean_Expr_isConstructorApp(x_39, x_13);
lean_dec(x_13);
if (x_40 == 0)
{
lean_object* x_41; 
lean_free_object(x_22);
lean_dec(x_14);
x_41 = lean_box(0);
lean_ctor_set(x_36, 0, x_41);
return x_36;
}
else
{
lean_ctor_set(x_22, 0, x_14);
lean_ctor_set(x_36, 0, x_22);
return x_36;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_42 = lean_ctor_get(x_36, 0);
x_43 = lean_ctor_get(x_36, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_36);
x_44 = lean_ctor_get(x_42, 0);
lean_inc(x_44);
lean_dec(x_42);
x_45 = l_Lean_Expr_isConstructorApp(x_44, x_13);
lean_dec(x_13);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
lean_free_object(x_22);
lean_dec(x_14);
x_46 = lean_box(0);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_43);
return x_47;
}
else
{
lean_object* x_48; 
lean_ctor_set(x_22, 0, x_14);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_22);
lean_ctor_set(x_48, 1, x_43);
return x_48;
}
}
}
}
else
{
lean_object* x_49; uint8_t x_50; 
x_49 = lean_ctor_get(x_22, 0);
lean_inc(x_49);
lean_dec(x_22);
x_50 = l_Lean_LocalDecl_isJp(x_49);
lean_dec(x_49);
if (x_50 == 0)
{
lean_object* x_51; 
lean_dec(x_14);
lean_dec(x_13);
x_51 = lean_box(0);
lean_ctor_set(x_20, 0, x_51);
return x_20;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
lean_free_object(x_20);
x_52 = lean_st_ref_get(x_6, x_30);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_55 = x_52;
} else {
 lean_dec_ref(x_52);
 x_55 = lean_box(0);
}
x_56 = lean_ctor_get(x_53, 0);
lean_inc(x_56);
lean_dec(x_53);
x_57 = l_Lean_Expr_isConstructorApp(x_56, x_13);
lean_dec(x_13);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; 
lean_dec(x_14);
x_58 = lean_box(0);
if (lean_is_scalar(x_55)) {
 x_59 = lean_alloc_ctor(0, 2, 0);
} else {
 x_59 = x_55;
}
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_54);
return x_59;
}
else
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_60, 0, x_14);
if (lean_is_scalar(x_55)) {
 x_61 = lean_alloc_ctor(0, 2, 0);
} else {
 x_61 = x_55;
}
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_54);
return x_61;
}
}
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_62 = lean_ctor_get(x_20, 1);
lean_inc(x_62);
lean_dec(x_20);
x_63 = lean_ctor_get(x_22, 0);
lean_inc(x_63);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 x_64 = x_22;
} else {
 lean_dec_ref(x_22);
 x_64 = lean_box(0);
}
x_65 = l_Lean_LocalDecl_isJp(x_63);
lean_dec(x_63);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; 
lean_dec(x_64);
lean_dec(x_14);
lean_dec(x_13);
x_66 = lean_box(0);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_62);
return x_67;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_68 = lean_st_ref_get(x_6, x_62);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 x_71 = x_68;
} else {
 lean_dec_ref(x_68);
 x_71 = lean_box(0);
}
x_72 = lean_ctor_get(x_69, 0);
lean_inc(x_72);
lean_dec(x_69);
x_73 = l_Lean_Expr_isConstructorApp(x_72, x_13);
lean_dec(x_13);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; 
lean_dec(x_64);
lean_dec(x_14);
x_74 = lean_box(0);
if (lean_is_scalar(x_71)) {
 x_75 = lean_alloc_ctor(0, 2, 0);
} else {
 x_75 = x_71;
}
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_70);
return x_75;
}
else
{
lean_object* x_76; lean_object* x_77; 
if (lean_is_scalar(x_64)) {
 x_76 = lean_alloc_ctor(1, 1, 0);
} else {
 x_76 = x_64;
}
lean_ctor_set(x_76, 0, x_14);
if (lean_is_scalar(x_71)) {
 x_77 = lean_alloc_ctor(0, 2, 0);
} else {
 x_77 = x_71;
}
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_70);
return x_77;
}
}
}
}
}
}
else
{
lean_object* x_78; lean_object* x_79; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_1);
x_78 = lean_box(0);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_7);
return x_79;
}
}
else
{
lean_object* x_80; lean_object* x_81; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_1);
x_80 = lean_box(0);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_7);
return x_81;
}
}
case 8:
{
lean_dec(x_1);
x_1 = x_10;
goto _start;
}
default: 
{
lean_object* x_83; lean_object* x_84; 
lean_dec(x_10);
lean_dec(x_1);
x_83 = lean_box(0);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_7);
return x_84;
}
}
}
default: 
{
lean_object* x_85; lean_object* x_86; 
lean_dec(x_1);
x_85 = lean_box(0);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_7);
return x_86;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_findDecl_x3f___at_Lean_Compiler_Simp_simpCasesOnCases_x3f_isJpCtor_x3f___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_findDecl_x3f___at_Lean_Compiler_Simp_simpCasesOnCases_x3f_isJpCtor_x3f___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_simpCasesOnCases_x3f_isJpCtor_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_Simp_simpCasesOnCases_x3f_isJpCtor_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_simpCasesOnCases_x3f_inlineJp(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 6:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
x_6 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
lean_dec(x_1);
x_7 = l_Lean_Compiler_Simp_simpCasesOnCases_x3f_inlineJp(x_5, x_2);
x_8 = l_Lean_Expr_lam___override(x_3, x_4, x_7, x_6);
return x_8;
}
case 8:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 2);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 3);
lean_inc(x_12);
x_13 = lean_ctor_get_uint8(x_1, sizeof(void*)*4 + 8);
lean_dec(x_1);
x_14 = l_Lean_Compiler_Simp_simpCasesOnCases_x3f_inlineJp(x_12, x_2);
x_15 = l_Lean_Expr_letE___override(x_9, x_10, x_11, x_14, x_13);
return x_15;
}
default: 
{
lean_dec(x_1);
lean_inc(x_2);
return x_2;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_simpCasesOnCases_x3f_inlineJp___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Compiler_Simp_simpCasesOnCases_x3f_inlineJp(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_Simp_simpCasesOnCases_x3f___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_nat_dec_le(x_4, x_3);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_dec_eq(x_2, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_27; lean_object* x_91; uint8_t x_92; 
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_sub(x_2, x_16);
lean_dec(x_2);
x_91 = lean_array_get_size(x_1);
x_92 = lean_nat_dec_lt(x_3, x_91);
lean_dec(x_91);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; 
x_93 = l_Lean_Compiler_Simp_simpProj_x3f___closed__4;
x_94 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_93);
x_27 = x_94;
goto block_90;
}
else
{
lean_object* x_95; 
x_95 = lean_array_fget(x_1, x_3);
x_27 = x_95;
goto block_90;
}
block_26:
{
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_3);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_18, 0);
lean_inc(x_22);
lean_dec(x_18);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_nat_add(x_3, x_5);
lean_dec(x_3);
x_2 = x_17;
x_3 = x_24;
x_6 = x_23;
x_12 = x_19;
goto _start;
}
}
block_90:
{
lean_object* x_28; lean_object* x_29; 
x_28 = l_Lean_Compiler_Simp_simpCasesOnCases_x3f_isJpCtor_x3f(x_27, x_7, x_8, x_9, x_10, x_11, x_12);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_6);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_box(0);
x_18 = x_31;
x_19 = x_30;
goto block_26;
}
else
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_32 = lean_ctor_get(x_28, 1);
lean_inc(x_32);
lean_dec(x_28);
x_33 = lean_ctor_get(x_29, 0);
lean_inc(x_33);
lean_dec(x_29);
lean_inc(x_33);
x_34 = l_Lean_Compiler_findDecl_x3f___at_Lean_Compiler_Simp_simpCasesOnCases_x3f_isJpCtor_x3f___spec__1(x_33, x_7, x_8, x_9, x_10, x_11, x_32);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
lean_dec(x_35);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_33);
x_37 = lean_ctor_get(x_34, 1);
lean_inc(x_37);
lean_dec(x_34);
x_38 = lean_box(0);
x_18 = x_38;
x_19 = x_37;
goto block_26;
}
else
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_ctor_get(x_34, 1);
lean_inc(x_39);
lean_dec(x_34);
x_40 = !lean_is_exclusive(x_36);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_36, 0);
x_42 = l_Lean_LocalDecl_value(x_41);
lean_dec(x_41);
if (lean_obj_tag(x_42) == 6)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_42, 2);
lean_inc(x_43);
lean_dec(x_42);
lean_inc(x_11);
lean_inc(x_10);
x_44 = l_Lean_Compiler_isCasesApp_x3f(x_43, x_10, x_11, x_39);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; 
lean_free_object(x_36);
lean_dec(x_33);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = lean_box(0);
x_18 = x_47;
x_19 = x_46;
goto block_26;
}
else
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_45);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_45, 0);
lean_dec(x_49);
x_50 = lean_ctor_get(x_44, 1);
lean_inc(x_50);
lean_dec(x_44);
lean_ctor_set(x_45, 0, x_33);
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_45);
lean_ctor_set(x_36, 0, x_51);
x_18 = x_36;
x_19 = x_50;
goto block_26;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_45);
x_52 = lean_ctor_get(x_44, 1);
lean_inc(x_52);
lean_dec(x_44);
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_33);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_36, 0, x_54);
x_18 = x_36;
x_19 = x_52;
goto block_26;
}
}
}
else
{
uint8_t x_55; 
lean_free_object(x_36);
lean_dec(x_33);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_3);
x_55 = !lean_is_exclusive(x_44);
if (x_55 == 0)
{
return x_44;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_44, 0);
x_57 = lean_ctor_get(x_44, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_44);
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
lean_dec(x_42);
lean_free_object(x_36);
lean_dec(x_33);
x_59 = lean_box(0);
x_18 = x_59;
x_19 = x_39;
goto block_26;
}
}
else
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_36, 0);
lean_inc(x_60);
lean_dec(x_36);
x_61 = l_Lean_LocalDecl_value(x_60);
lean_dec(x_60);
if (lean_obj_tag(x_61) == 6)
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_61, 2);
lean_inc(x_62);
lean_dec(x_61);
lean_inc(x_11);
lean_inc(x_10);
x_63 = l_Lean_Compiler_isCasesApp_x3f(x_62, x_10, x_11, x_39);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; 
lean_dec(x_33);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
x_66 = lean_box(0);
x_18 = x_66;
x_19 = x_65;
goto block_26;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 x_67 = x_64;
} else {
 lean_dec_ref(x_64);
 x_67 = lean_box(0);
}
x_68 = lean_ctor_get(x_63, 1);
lean_inc(x_68);
lean_dec(x_63);
if (lean_is_scalar(x_67)) {
 x_69 = lean_alloc_ctor(1, 1, 0);
} else {
 x_69 = x_67;
}
lean_ctor_set(x_69, 0, x_33);
x_70 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_70, 0, x_69);
x_71 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_71, 0, x_70);
x_18 = x_71;
x_19 = x_68;
goto block_26;
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_dec(x_33);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_3);
x_72 = lean_ctor_get(x_63, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_63, 1);
lean_inc(x_73);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_74 = x_63;
} else {
 lean_dec_ref(x_63);
 x_74 = lean_box(0);
}
if (lean_is_scalar(x_74)) {
 x_75 = lean_alloc_ctor(1, 2, 0);
} else {
 x_75 = x_74;
}
lean_ctor_set(x_75, 0, x_72);
lean_ctor_set(x_75, 1, x_73);
return x_75;
}
}
else
{
lean_object* x_76; 
lean_dec(x_61);
lean_dec(x_33);
x_76 = lean_box(0);
x_18 = x_76;
x_19 = x_39;
goto block_26;
}
}
}
}
else
{
lean_object* x_77; uint8_t x_78; 
x_77 = lean_ctor_get(x_28, 1);
lean_inc(x_77);
lean_dec(x_28);
x_78 = !lean_is_exclusive(x_29);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; uint8_t x_81; 
x_79 = lean_ctor_get(x_29, 0);
x_80 = lean_ctor_get(x_6, 0);
lean_inc(x_80);
x_81 = lean_name_eq(x_79, x_80);
lean_dec(x_80);
lean_dec(x_79);
if (x_81 == 0)
{
lean_object* x_82; 
lean_free_object(x_29);
lean_dec(x_6);
x_82 = lean_box(0);
x_18 = x_82;
x_19 = x_77;
goto block_26;
}
else
{
lean_object* x_83; 
x_83 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_83, 0, x_6);
lean_ctor_set(x_29, 0, x_83);
x_18 = x_29;
x_19 = x_77;
goto block_26;
}
}
else
{
lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_84 = lean_ctor_get(x_29, 0);
lean_inc(x_84);
lean_dec(x_29);
x_85 = lean_ctor_get(x_6, 0);
lean_inc(x_85);
x_86 = lean_name_eq(x_84, x_85);
lean_dec(x_85);
lean_dec(x_84);
if (x_86 == 0)
{
lean_object* x_87; 
lean_dec(x_6);
x_87 = lean_box(0);
x_18 = x_87;
x_19 = x_77;
goto block_26;
}
else
{
lean_object* x_88; lean_object* x_89; 
x_88 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_88, 0, x_6);
x_89 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_89, 0, x_88);
x_18 = x_89;
x_19 = x_77;
goto block_26;
}
}
}
}
}
}
else
{
lean_object* x_96; lean_object* x_97; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_3);
lean_dec(x_2);
x_96 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_96, 0, x_6);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_12);
return x_97;
}
}
else
{
lean_object* x_98; lean_object* x_99; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_3);
lean_dec(x_2);
x_98 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_98, 0, x_6);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_12);
return x_99;
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_Simp_simpCasesOnCases_x3f___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_nat_dec_le(x_4, x_3);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_dec_eq(x_2, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_sub(x_2, x_16);
lean_dec(x_2);
x_18 = lean_array_get_size(x_6);
x_19 = lean_nat_dec_lt(x_3, x_18);
lean_dec(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_nat_add(x_3, x_5);
lean_dec(x_3);
x_2 = x_17;
x_3 = x_20;
goto _start;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_array_fget(x_6, x_3);
x_23 = lean_box(0);
x_24 = lean_array_fset(x_6, x_3, x_23);
x_25 = l_Lean_Compiler_Simp_simpCasesOnCases_x3f_inlineJp(x_22, x_1);
x_26 = lean_array_fset(x_24, x_3, x_25);
x_27 = lean_nat_add(x_3, x_5);
lean_dec(x_3);
x_2 = x_17;
x_3 = x_27;
x_6 = x_26;
goto _start;
}
}
else
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_3);
lean_dec(x_2);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_6);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_12);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_3);
lean_dec(x_2);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_6);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_12);
return x_32;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_simpCasesOnCases_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_box(0);
x_11 = lean_ctor_get(x_1, 3);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_11, 2);
lean_inc(x_14);
lean_dec(x_11);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_13);
lean_inc(x_12);
x_15 = l_Std_Range_forIn_loop___at_Lean_Compiler_Simp_simpCasesOnCases_x3f___spec__1(x_3, x_12, x_13, x_12, x_14, x_10, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_17 = !lean_is_exclusive(x_15);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_15, 0);
lean_dec(x_18);
lean_ctor_set(x_15, 0, x_10);
return x_15;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_15, 1);
lean_inc(x_19);
lean_dec(x_15);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_10);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
else
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_16, 0);
lean_inc(x_21);
lean_dec(x_16);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_22 = !lean_is_exclusive(x_15);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_15, 0);
lean_dec(x_23);
lean_ctor_set(x_15, 0, x_10);
return x_15;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_15, 1);
lean_inc(x_24);
lean_dec(x_15);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_10);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = lean_ctor_get(x_15, 1);
lean_inc(x_26);
lean_dec(x_15);
x_27 = lean_ctor_get(x_21, 0);
lean_inc(x_27);
lean_dec(x_21);
x_28 = l_Lean_Compiler_findDecl_x3f___at_Lean_Compiler_Simp_simpCasesOnCases_x3f_isJpCtor_x3f___spec__1(x_27, x_4, x_5, x_6, x_7, x_8, x_26);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
lean_dec(x_29);
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_31; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_31 = !lean_is_exclusive(x_28);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_28, 0);
lean_dec(x_32);
lean_ctor_set(x_28, 0, x_10);
return x_28;
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_28, 1);
lean_inc(x_33);
lean_dec(x_28);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_10);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
else
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_28);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_28, 1);
x_37 = lean_ctor_get(x_28, 0);
lean_dec(x_37);
x_38 = lean_ctor_get(x_30, 0);
lean_inc(x_38);
lean_dec(x_30);
x_39 = l_Lean_LocalDecl_value(x_38);
lean_dec(x_38);
if (lean_obj_tag(x_39) == 6)
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; 
lean_free_object(x_28);
x_40 = lean_ctor_get(x_39, 2);
lean_inc(x_40);
lean_dec(x_39);
lean_inc(x_12);
x_41 = l_Std_Range_forIn_loop___at_Lean_Compiler_Simp_simpCasesOnCases_x3f___spec__2(x_40, x_12, x_13, x_12, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_36);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_40);
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_ctor_get(x_41, 0);
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_43, 0);
x_46 = l_Lean_mkAppN(x_2, x_45);
lean_ctor_set(x_43, 0, x_46);
return x_41;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_43, 0);
lean_inc(x_47);
lean_dec(x_43);
x_48 = l_Lean_mkAppN(x_2, x_47);
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_41, 0, x_49);
return x_41;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_50 = lean_ctor_get(x_41, 0);
x_51 = lean_ctor_get(x_41, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_41);
x_52 = lean_ctor_get(x_50, 0);
lean_inc(x_52);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 x_53 = x_50;
} else {
 lean_dec_ref(x_50);
 x_53 = lean_box(0);
}
x_54 = l_Lean_mkAppN(x_2, x_52);
if (lean_is_scalar(x_53)) {
 x_55 = lean_alloc_ctor(1, 1, 0);
} else {
 x_55 = x_53;
}
lean_ctor_set(x_55, 0, x_54);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_51);
return x_56;
}
}
else
{
lean_dec(x_39);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_ctor_set(x_28, 0, x_10);
return x_28;
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_28, 1);
lean_inc(x_57);
lean_dec(x_28);
x_58 = lean_ctor_get(x_30, 0);
lean_inc(x_58);
lean_dec(x_30);
x_59 = l_Lean_LocalDecl_value(x_58);
lean_dec(x_58);
if (lean_obj_tag(x_59) == 6)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_60 = lean_ctor_get(x_59, 2);
lean_inc(x_60);
lean_dec(x_59);
lean_inc(x_12);
x_61 = l_Std_Range_forIn_loop___at_Lean_Compiler_Simp_simpCasesOnCases_x3f___spec__2(x_60, x_12, x_13, x_12, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_57);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_60);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_64 = x_61;
} else {
 lean_dec_ref(x_61);
 x_64 = lean_box(0);
}
x_65 = lean_ctor_get(x_62, 0);
lean_inc(x_65);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 x_66 = x_62;
} else {
 lean_dec_ref(x_62);
 x_66 = lean_box(0);
}
x_67 = l_Lean_mkAppN(x_2, x_65);
if (lean_is_scalar(x_66)) {
 x_68 = lean_alloc_ctor(1, 1, 0);
} else {
 x_68 = x_66;
}
lean_ctor_set(x_68, 0, x_67);
if (lean_is_scalar(x_64)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_64;
}
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_63);
return x_69;
}
else
{
lean_object* x_70; 
lean_dec(x_59);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_10);
lean_ctor_set(x_70, 1, x_57);
return x_70;
}
}
}
}
}
}
else
{
uint8_t x_71; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_71 = !lean_is_exclusive(x_15);
if (x_71 == 0)
{
return x_15;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_15, 0);
x_73 = lean_ctor_get(x_15, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_15);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_Simp_simpCasesOnCases_x3f___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Std_Range_forIn_loop___at_Lean_Compiler_Simp_simpCasesOnCases_x3f___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_Simp_simpCasesOnCases_x3f___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Std_Range_forIn_loop___at_Lean_Compiler_Simp_simpCasesOnCases_x3f___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_simpCasesOnCases_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_Simp_simpCasesOnCases_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_simpValue_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
lean_inc(x_1);
x_8 = l_Lean_Compiler_Simp_simpProj_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
lean_inc(x_1);
x_11 = l_Lean_Compiler_Simp_simpAppApp_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Compiler_Simp_inlineProjInst_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_13);
return x_14;
}
else
{
uint8_t x_15; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_15 = !lean_is_exclusive(x_11);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_11, 0);
lean_dec(x_16);
x_17 = !lean_is_exclusive(x_12);
if (x_17 == 0)
{
return x_11;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_12, 0);
lean_inc(x_18);
lean_dec(x_12);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_11, 0, x_19);
return x_11;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_11, 1);
lean_inc(x_20);
lean_dec(x_11);
x_21 = lean_ctor_get(x_12, 0);
lean_inc(x_21);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 x_22 = x_12;
} else {
 lean_dec_ref(x_12);
 x_22 = lean_box(0);
}
if (lean_is_scalar(x_22)) {
 x_23 = lean_alloc_ctor(1, 1, 0);
} else {
 x_23 = x_22;
}
lean_ctor_set(x_23, 0, x_21);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_20);
return x_24;
}
}
}
else
{
uint8_t x_25; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_8);
if (x_25 == 0)
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_ctor_get(x_8, 0);
lean_dec(x_26);
x_27 = !lean_is_exclusive(x_9);
if (x_27 == 0)
{
return x_8;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_9, 0);
lean_inc(x_28);
lean_dec(x_9);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_8, 0, x_29);
return x_8;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_30 = lean_ctor_get(x_8, 1);
lean_inc(x_30);
lean_dec(x_8);
x_31 = lean_ctor_get(x_9, 0);
lean_inc(x_31);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 x_32 = x_9;
} else {
 lean_dec_ref(x_9);
 x_32 = lean_box(0);
}
if (lean_is_scalar(x_32)) {
 x_33 = lean_alloc_ctor(1, 1, 0);
} else {
 x_33 = x_32;
}
lean_ctor_set(x_33, 0, x_31);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_30);
return x_34;
}
}
}
}
static lean_object* _init_l_Lean_throwError___at_Lean_Compiler_Simp_visitLambda___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Std_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_throwError___at_Lean_Compiler_Simp_visitLambda___spec__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_throwError___at_Lean_Compiler_Simp_visitLambda___spec__3___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_throwError___at_Lean_Compiler_Simp_visitLambda___spec__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_throwError___at_Lean_Compiler_Simp_visitLambda___spec__3___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_throwError___at_Lean_Compiler_Simp_visitLambda___spec__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_throwError___at_Lean_Compiler_Simp_visitLambda___spec__3___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_throwError___at_Lean_Compiler_Simp_visitLambda___spec__3___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_throwError___at_Lean_Compiler_Simp_visitLambda___spec__3___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_throwError___at_Lean_Compiler_Simp_visitLambda___spec__3___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_throwError___at_Lean_Compiler_Simp_visitLambda___spec__3___closed__3;
x_3 = l_Lean_throwError___at_Lean_Compiler_Simp_visitLambda___spec__3___closed__4;
x_4 = l_Lean_throwError___at_Lean_Compiler_Simp_visitLambda___spec__3___closed__5;
x_5 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_1);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_3);
lean_ctor_set(x_5, 4, x_4);
lean_ctor_set(x_5, 5, x_2);
lean_ctor_set(x_5, 6, x_3);
lean_ctor_set(x_5, 7, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_Simp_visitLambda___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_8 = lean_ctor_get(x_5, 5);
x_9 = lean_st_ref_get(x_6, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_st_ref_get(x_6, x_11);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_st_ref_get(x_4, x_14);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_ctor_get(x_5, 2);
x_20 = l_Lean_throwError___at_Lean_Compiler_Simp_visitLambda___spec__3___closed__6;
lean_inc(x_19);
x_21 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_21, 0, x_12);
lean_ctor_set(x_21, 1, x_20);
lean_ctor_set(x_21, 2, x_18);
lean_ctor_set(x_21, 3, x_19);
x_22 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_1);
lean_inc(x_8);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_8);
lean_ctor_set(x_23, 1, x_22);
lean_ctor_set_tag(x_15, 1);
lean_ctor_set(x_15, 0, x_23);
return x_15;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_24 = lean_ctor_get(x_15, 0);
x_25 = lean_ctor_get(x_15, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_15);
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_ctor_get(x_5, 2);
x_28 = l_Lean_throwError___at_Lean_Compiler_Simp_visitLambda___spec__3___closed__6;
lean_inc(x_27);
x_29 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_29, 0, x_12);
lean_ctor_set(x_29, 1, x_28);
lean_ctor_set(x_29, 2, x_26);
lean_ctor_set(x_29, 3, x_27);
x_30 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_1);
lean_inc(x_8);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_8);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_25);
return x_32;
}
}
}
static lean_object* _init_l_Lean_Compiler_getLevel___at_Lean_Compiler_Simp_visitLambda___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("type expected", 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_getLevel___at_Lean_Compiler_Simp_visitLambda___spec__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_getLevel___at_Lean_Compiler_Simp_visitLambda___spec__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_getLevel___at_Lean_Compiler_Simp_visitLambda___spec__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_forIn_loop___at_Lean_Compiler_Simp_OccInfo_format___spec__4___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_getLevel___at_Lean_Compiler_Simp_visitLambda___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = lean_st_ref_get(x_6, x_7);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_st_ref_get(x_4, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_14 = l_Lean_Compiler_InferType_inferType(x_1, x_13, x_5, x_6, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 3)
{
uint8_t x_16; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_16 = !lean_is_exclusive(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_14, 0);
lean_dec(x_17);
x_18 = lean_ctor_get(x_15, 0);
lean_inc(x_18);
lean_dec(x_15);
lean_ctor_set(x_14, 0, x_18);
return x_14;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_14, 1);
lean_inc(x_19);
lean_dec(x_14);
x_20 = lean_ctor_get(x_15, 0);
lean_inc(x_20);
lean_dec(x_15);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_14);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_ctor_get(x_14, 1);
x_24 = lean_ctor_get(x_14, 0);
lean_dec(x_24);
x_25 = l_Lean_Expr_isAnyType(x_15);
lean_dec(x_15);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_free_object(x_14);
x_26 = l_Lean_indentExpr(x_1);
x_27 = l_Lean_Compiler_getLevel___at_Lean_Compiler_Simp_visitLambda___spec__2___closed__2;
x_28 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
x_29 = l_Lean_Compiler_getLevel___at_Lean_Compiler_Simp_visitLambda___spec__2___closed__3;
x_30 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = l_Lean_throwError___at_Lean_Compiler_Simp_visitLambda___spec__3(x_30, x_2, x_3, x_4, x_5, x_6, x_23);
lean_dec(x_6);
lean_dec(x_5);
return x_31;
}
else
{
lean_object* x_32; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_32 = l_Lean_levelOne;
lean_ctor_set(x_14, 0, x_32);
return x_14;
}
}
else
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_14, 1);
lean_inc(x_33);
lean_dec(x_14);
x_34 = l_Lean_Expr_isAnyType(x_15);
lean_dec(x_15);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_35 = l_Lean_indentExpr(x_1);
x_36 = l_Lean_Compiler_getLevel___at_Lean_Compiler_Simp_visitLambda___spec__2___closed__2;
x_37 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
x_38 = l_Lean_Compiler_getLevel___at_Lean_Compiler_Simp_visitLambda___spec__2___closed__3;
x_39 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
x_40 = l_Lean_throwError___at_Lean_Compiler_Simp_visitLambda___spec__3(x_39, x_2, x_3, x_4, x_5, x_6, x_33);
lean_dec(x_6);
lean_dec(x_5);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_41 = l_Lean_levelOne;
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_33);
return x_42;
}
}
}
}
else
{
uint8_t x_43; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_14);
if (x_43 == 0)
{
return x_14;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_14, 0);
x_45 = lean_ctor_get(x_14, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_14);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
}
static lean_object* _init_l_Lean_Compiler_mkLcUnreachable___at_Lean_Compiler_Simp_visitLambda___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("lcUnreachable", 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_mkLcUnreachable___at_Lean_Compiler_Simp_visitLambda___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_mkLcUnreachable___at_Lean_Compiler_Simp_visitLambda___spec__1___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_mkLcUnreachable___at_Lean_Compiler_Simp_visitLambda___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_1);
x_8 = l_Lean_Compiler_getLevel___at_Lean_Compiler_Simp_visitLambda___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = l_Lean_Compiler_mkLcUnreachable___at_Lean_Compiler_Simp_visitLambda___spec__1___closed__2;
x_14 = l_Lean_Expr_const___override(x_13, x_12);
x_15 = l_Lean_Expr_app___override(x_14, x_1);
lean_ctor_set(x_8, 0, x_15);
return x_8;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_16 = lean_ctor_get(x_8, 0);
x_17 = lean_ctor_get(x_8, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_8);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Lean_Compiler_mkLcUnreachable___at_Lean_Compiler_Simp_visitLambda___spec__1___closed__2;
x_21 = l_Lean_Expr_const___override(x_20, x_19);
x_22 = l_Lean_Expr_app___override(x_21, x_1);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_17);
return x_23;
}
}
else
{
uint8_t x_24; 
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_8);
if (x_24 == 0)
{
return x_8;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_8, 0);
x_26 = lean_ctor_get(x_8, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_8);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_Simp_visitLambda___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = lean_usize_dec_lt(x_6, x_5);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_3);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_7);
x_16 = lean_array_uget(x_4, x_6);
x_26 = lean_st_ref_get(x_12, x_13);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = lean_st_ref_get(x_10, x_27);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_ctor_get(x_29, 0);
lean_inc(x_31);
lean_dec(x_29);
lean_inc(x_12);
lean_inc(x_11);
x_32 = l_Lean_Compiler_InferType_inferType(x_16, x_31, x_11, x_12, x_30);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = l_Lean_Compiler_isEmptyType(x_33, x_11, x_12, x_34);
lean_dec(x_33);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_unbox(x_36);
lean_dec(x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
lean_dec(x_35);
lean_inc(x_3);
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_3);
x_17 = x_39;
x_18 = x_38;
goto block_25;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_40 = lean_ctor_get(x_35, 1);
lean_inc(x_40);
lean_dec(x_35);
x_41 = lean_expr_instantiate_rev(x_2, x_1);
x_42 = lean_st_ref_get(x_12, x_40);
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec(x_42);
x_44 = lean_st_ref_get(x_10, x_43);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = lean_ctor_get(x_45, 0);
lean_inc(x_47);
lean_dec(x_45);
lean_inc(x_12);
lean_inc(x_11);
x_48 = l_Lean_Compiler_InferType_inferType(x_41, x_47, x_11, x_12, x_46);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
lean_inc(x_12);
lean_inc(x_11);
x_51 = l_Lean_Compiler_mkLcUnreachable___at_Lean_Compiler_Simp_visitLambda___spec__1(x_49, x_8, x_9, x_10, x_11, x_12, x_50);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = l_Lean_Compiler_mkLambda(x_1, x_52, x_10, x_11, x_12, x_53);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
x_57 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_57, 0, x_55);
x_58 = lean_box(0);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
x_60 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_60, 0, x_59);
x_17 = x_60;
x_18 = x_56;
goto block_25;
}
else
{
uint8_t x_61; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_3);
x_61 = !lean_is_exclusive(x_51);
if (x_61 == 0)
{
return x_51;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_51, 0);
x_63 = lean_ctor_get(x_51, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_51);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
else
{
uint8_t x_65; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_3);
x_65 = !lean_is_exclusive(x_48);
if (x_65 == 0)
{
return x_48;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_48, 0);
x_67 = lean_ctor_get(x_48, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_48);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
}
else
{
uint8_t x_69; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_3);
x_69 = !lean_is_exclusive(x_32);
if (x_69 == 0)
{
return x_32;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_32, 0);
x_71 = lean_ctor_get(x_32, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_32);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
block_25:
{
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_3);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
else
{
lean_object* x_21; size_t x_22; size_t x_23; 
x_21 = lean_ctor_get(x_17, 0);
lean_inc(x_21);
lean_dec(x_17);
x_22 = 1;
x_23 = lean_usize_add(x_6, x_22);
x_6 = x_23;
x_7 = x_21;
x_13 = x_18;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_visitLambda___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_2);
x_10 = l_Lean_Compiler_Simp_visitLet(x_1, x_2, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_13 = l_Lean_Compiler_mkLetUsingScope(x_11, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_Compiler_mkLambda(x_2, x_14, x_6, x_7, x_8, x_15);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
return x_16;
}
else
{
uint8_t x_17; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_17 = !lean_is_exclusive(x_13);
if (x_17 == 0)
{
return x_13;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_13, 0);
x_19 = lean_ctor_get(x_13, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_13);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
else
{
uint8_t x_21; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_21 = !lean_is_exclusive(x_10);
if (x_21 == 0)
{
return x_10;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_10, 0);
x_23 = lean_ctor_get(x_10, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_10);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
static lean_object* _init_l_Lean_Compiler_Simp_visitLambda___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_visitLambda(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_42; lean_object* x_43; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_st_ref_get(x_5, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_70 = lean_st_ref_get(x_7, x_13);
x_71 = lean_ctor_get(x_70, 1);
lean_inc(x_71);
lean_dec(x_70);
x_72 = lean_st_ref_take(x_5, x_71);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
x_75 = !lean_is_exclusive(x_73);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_76 = lean_ctor_get(x_73, 1);
lean_dec(x_76);
x_77 = l_Lean_Compiler_Simp_internalize_visitLambda___closed__1;
lean_ctor_set(x_73, 1, x_77);
x_78 = lean_st_ref_set(x_5, x_73, x_74);
x_79 = lean_ctor_get(x_78, 1);
lean_inc(x_79);
lean_dec(x_78);
x_80 = l_Lean_Compiler_visitLambdaCore(x_1, x_5, x_6, x_7, x_79);
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
if (x_2 == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
lean_dec(x_80);
x_83 = lean_ctor_get(x_81, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_81, 1);
lean_inc(x_84);
lean_dec(x_81);
x_85 = lean_box(0);
lean_inc(x_7);
lean_inc(x_5);
x_86 = l_Lean_Compiler_Simp_visitLambda___lambda__1(x_84, x_83, x_85, x_3, x_4, x_5, x_6, x_7, x_82);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
lean_dec(x_86);
x_14 = x_87;
x_15 = x_88;
goto block_41;
}
else
{
lean_object* x_89; lean_object* x_90; 
x_89 = lean_ctor_get(x_86, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_86, 1);
lean_inc(x_90);
lean_dec(x_86);
x_42 = x_89;
x_43 = x_90;
goto block_69;
}
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; size_t x_95; size_t x_96; lean_object* x_97; lean_object* x_98; 
x_91 = lean_ctor_get(x_80, 1);
lean_inc(x_91);
lean_dec(x_80);
x_92 = lean_ctor_get(x_81, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_81, 1);
lean_inc(x_93);
lean_dec(x_81);
x_94 = lean_array_get_size(x_92);
x_95 = lean_usize_of_nat(x_94);
lean_dec(x_94);
x_96 = 0;
x_97 = l_Lean_Compiler_Simp_visitLambda___closed__1;
lean_inc(x_7);
lean_inc(x_6);
x_98 = l_Array_forInUnsafe_loop___at_Lean_Compiler_Simp_visitLambda___spec__4(x_92, x_93, x_97, x_92, x_95, x_96, x_97, x_3, x_4, x_5, x_6, x_7, x_91);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; lean_object* x_100; 
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
lean_dec(x_99);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_98, 1);
lean_inc(x_101);
lean_dec(x_98);
x_102 = lean_box(0);
lean_inc(x_7);
lean_inc(x_5);
x_103 = l_Lean_Compiler_Simp_visitLambda___lambda__1(x_93, x_92, x_102, x_3, x_4, x_5, x_6, x_7, x_101);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; 
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
lean_dec(x_103);
x_14 = x_104;
x_15 = x_105;
goto block_41;
}
else
{
lean_object* x_106; lean_object* x_107; 
x_106 = lean_ctor_get(x_103, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_103, 1);
lean_inc(x_107);
lean_dec(x_103);
x_42 = x_106;
x_43 = x_107;
goto block_69;
}
}
else
{
lean_object* x_108; lean_object* x_109; 
lean_dec(x_93);
lean_dec(x_92);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_108 = lean_ctor_get(x_98, 1);
lean_inc(x_108);
lean_dec(x_98);
x_109 = lean_ctor_get(x_100, 0);
lean_inc(x_109);
lean_dec(x_100);
x_14 = x_109;
x_15 = x_108;
goto block_41;
}
}
else
{
lean_object* x_110; lean_object* x_111; 
lean_dec(x_93);
lean_dec(x_92);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_110 = lean_ctor_get(x_98, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_98, 1);
lean_inc(x_111);
lean_dec(x_98);
x_42 = x_110;
x_43 = x_111;
goto block_69;
}
}
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_112 = lean_ctor_get(x_73, 0);
x_113 = lean_ctor_get(x_73, 2);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_73);
x_114 = l_Lean_Compiler_Simp_internalize_visitLambda___closed__1;
x_115 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_115, 0, x_112);
lean_ctor_set(x_115, 1, x_114);
lean_ctor_set(x_115, 2, x_113);
x_116 = lean_st_ref_set(x_5, x_115, x_74);
x_117 = lean_ctor_get(x_116, 1);
lean_inc(x_117);
lean_dec(x_116);
x_118 = l_Lean_Compiler_visitLambdaCore(x_1, x_5, x_6, x_7, x_117);
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
if (x_2 == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_120 = lean_ctor_get(x_118, 1);
lean_inc(x_120);
lean_dec(x_118);
x_121 = lean_ctor_get(x_119, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_119, 1);
lean_inc(x_122);
lean_dec(x_119);
x_123 = lean_box(0);
lean_inc(x_7);
lean_inc(x_5);
x_124 = l_Lean_Compiler_Simp_visitLambda___lambda__1(x_122, x_121, x_123, x_3, x_4, x_5, x_6, x_7, x_120);
if (lean_obj_tag(x_124) == 0)
{
lean_object* x_125; lean_object* x_126; 
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_124, 1);
lean_inc(x_126);
lean_dec(x_124);
x_14 = x_125;
x_15 = x_126;
goto block_41;
}
else
{
lean_object* x_127; lean_object* x_128; 
x_127 = lean_ctor_get(x_124, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_124, 1);
lean_inc(x_128);
lean_dec(x_124);
x_42 = x_127;
x_43 = x_128;
goto block_69;
}
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; size_t x_133; size_t x_134; lean_object* x_135; lean_object* x_136; 
x_129 = lean_ctor_get(x_118, 1);
lean_inc(x_129);
lean_dec(x_118);
x_130 = lean_ctor_get(x_119, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_119, 1);
lean_inc(x_131);
lean_dec(x_119);
x_132 = lean_array_get_size(x_130);
x_133 = lean_usize_of_nat(x_132);
lean_dec(x_132);
x_134 = 0;
x_135 = l_Lean_Compiler_Simp_visitLambda___closed__1;
lean_inc(x_7);
lean_inc(x_6);
x_136 = l_Array_forInUnsafe_loop___at_Lean_Compiler_Simp_visitLambda___spec__4(x_130, x_131, x_135, x_130, x_133, x_134, x_135, x_3, x_4, x_5, x_6, x_7, x_129);
if (lean_obj_tag(x_136) == 0)
{
lean_object* x_137; lean_object* x_138; 
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
lean_dec(x_137);
if (lean_obj_tag(x_138) == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_139 = lean_ctor_get(x_136, 1);
lean_inc(x_139);
lean_dec(x_136);
x_140 = lean_box(0);
lean_inc(x_7);
lean_inc(x_5);
x_141 = l_Lean_Compiler_Simp_visitLambda___lambda__1(x_131, x_130, x_140, x_3, x_4, x_5, x_6, x_7, x_139);
if (lean_obj_tag(x_141) == 0)
{
lean_object* x_142; lean_object* x_143; 
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_141, 1);
lean_inc(x_143);
lean_dec(x_141);
x_14 = x_142;
x_15 = x_143;
goto block_41;
}
else
{
lean_object* x_144; lean_object* x_145; 
x_144 = lean_ctor_get(x_141, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_141, 1);
lean_inc(x_145);
lean_dec(x_141);
x_42 = x_144;
x_43 = x_145;
goto block_69;
}
}
else
{
lean_object* x_146; lean_object* x_147; 
lean_dec(x_131);
lean_dec(x_130);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_146 = lean_ctor_get(x_136, 1);
lean_inc(x_146);
lean_dec(x_136);
x_147 = lean_ctor_get(x_138, 0);
lean_inc(x_147);
lean_dec(x_138);
x_14 = x_147;
x_15 = x_146;
goto block_41;
}
}
else
{
lean_object* x_148; lean_object* x_149; 
lean_dec(x_131);
lean_dec(x_130);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_148 = lean_ctor_get(x_136, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_136, 1);
lean_inc(x_149);
lean_dec(x_136);
x_42 = x_148;
x_43 = x_149;
goto block_69;
}
}
}
block_41:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_16 = lean_st_ref_get(x_7, x_15);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_st_ref_get(x_5, x_17);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_ctor_get(x_12, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_12, 1);
lean_inc(x_22);
lean_dec(x_12);
x_23 = !lean_is_exclusive(x_19);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_24 = lean_ctor_get(x_19, 1);
lean_dec(x_24);
x_25 = lean_ctor_get(x_19, 0);
lean_dec(x_25);
lean_ctor_set(x_19, 1, x_22);
lean_ctor_set(x_19, 0, x_21);
x_26 = lean_st_ref_get(x_7, x_20);
lean_dec(x_7);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = lean_st_ref_set(x_5, x_19, x_27);
lean_dec(x_5);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_28, 0);
lean_dec(x_30);
lean_ctor_set(x_28, 0, x_14);
return x_28;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_14);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_33 = lean_ctor_get(x_19, 2);
lean_inc(x_33);
lean_dec(x_19);
x_34 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_34, 0, x_21);
lean_ctor_set(x_34, 1, x_22);
lean_ctor_set(x_34, 2, x_33);
x_35 = lean_st_ref_get(x_7, x_20);
lean_dec(x_7);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec(x_35);
x_37 = lean_st_ref_set(x_5, x_34, x_36);
lean_dec(x_5);
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_39 = x_37;
} else {
 lean_dec_ref(x_37);
 x_39 = lean_box(0);
}
if (lean_is_scalar(x_39)) {
 x_40 = lean_alloc_ctor(0, 2, 0);
} else {
 x_40 = x_39;
}
lean_ctor_set(x_40, 0, x_14);
lean_ctor_set(x_40, 1, x_38);
return x_40;
}
}
block_69:
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_44 = lean_st_ref_get(x_7, x_43);
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec(x_44);
x_46 = lean_st_ref_get(x_5, x_45);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = lean_ctor_get(x_12, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_12, 1);
lean_inc(x_50);
lean_dec(x_12);
x_51 = !lean_is_exclusive(x_47);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_52 = lean_ctor_get(x_47, 1);
lean_dec(x_52);
x_53 = lean_ctor_get(x_47, 0);
lean_dec(x_53);
lean_ctor_set(x_47, 1, x_50);
lean_ctor_set(x_47, 0, x_49);
x_54 = lean_st_ref_get(x_7, x_48);
lean_dec(x_7);
x_55 = lean_ctor_get(x_54, 1);
lean_inc(x_55);
lean_dec(x_54);
x_56 = lean_st_ref_set(x_5, x_47, x_55);
lean_dec(x_5);
x_57 = !lean_is_exclusive(x_56);
if (x_57 == 0)
{
lean_object* x_58; 
x_58 = lean_ctor_get(x_56, 0);
lean_dec(x_58);
lean_ctor_set_tag(x_56, 1);
lean_ctor_set(x_56, 0, x_42);
return x_56;
}
else
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_56, 1);
lean_inc(x_59);
lean_dec(x_56);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_42);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_61 = lean_ctor_get(x_47, 2);
lean_inc(x_61);
lean_dec(x_47);
x_62 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_62, 0, x_49);
lean_ctor_set(x_62, 1, x_50);
lean_ctor_set(x_62, 2, x_61);
x_63 = lean_st_ref_get(x_7, x_48);
lean_dec(x_7);
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
lean_dec(x_63);
x_65 = lean_st_ref_set(x_5, x_62, x_64);
lean_dec(x_5);
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_67 = x_65;
} else {
 lean_dec_ref(x_65);
 x_67 = lean_box(0);
}
if (lean_is_scalar(x_67)) {
 x_68 = lean_alloc_ctor(1, 2, 0);
} else {
 x_68 = x_67;
 lean_ctor_set_tag(x_68, 1);
}
lean_ctor_set(x_68, 0, x_42);
lean_ctor_set(x_68, 1, x_66);
return x_68;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_visitLet___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
lean_dec(x_7);
x_14 = l_Lean_Expr_isFVar(x_6);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_inc(x_1);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_1);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_2);
lean_inc(x_6);
x_16 = l_Lean_Compiler_Simp_inlineApp_x3f(x_6, x_2, x_15, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_expr_instantiate_rev(x_3, x_2);
lean_dec(x_3);
x_20 = l_Lean_Compiler_mkLetDecl(x_4, x_19, x_6, x_5, x_10, x_11, x_12, x_18);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_array_push(x_2, x_21);
x_24 = l_Lean_Compiler_Simp_visitLet(x_1, x_23, x_8, x_9, x_10, x_11, x_12, x_22);
return x_24;
}
else
{
uint8_t x_25; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_16);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_16, 0);
lean_dec(x_26);
x_27 = lean_ctor_get(x_17, 0);
lean_inc(x_27);
lean_dec(x_17);
lean_ctor_set(x_16, 0, x_27);
return x_16;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_16, 1);
lean_inc(x_28);
lean_dec(x_16);
x_29 = lean_ctor_get(x_17, 0);
lean_inc(x_29);
lean_dec(x_17);
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
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_4);
lean_dec(x_3);
x_35 = l_Lean_Compiler_Simp_markSimplified___rarg(x_9, x_10, x_11, x_12, x_13);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec(x_35);
x_37 = lean_array_push(x_2, x_6);
x_38 = l_Lean_Compiler_Simp_visitLet(x_1, x_37, x_8, x_9, x_10, x_11, x_12, x_36);
return x_38;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_visitLet___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_box(0);
x_12 = lean_apply_8(x_1, x_2, x_11, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_visitLet(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_1) == 8)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; uint8_t x_15; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 2);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 3);
lean_inc(x_12);
x_13 = lean_ctor_get_uint8(x_1, sizeof(void*)*4 + 8);
lean_dec(x_1);
x_14 = lean_expr_instantiate_rev(x_11, x_2);
lean_dec(x_11);
x_15 = l_Lean_Expr_isLambda(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_14);
x_16 = l_Lean_Compiler_Simp_simpValue_x3f(x_14, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_box(0);
x_20 = l_Lean_Compiler_Simp_visitLet___lambda__1(x_12, x_2, x_10, x_9, x_13, x_14, x_19, x_3, x_4, x_5, x_6, x_7, x_18);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
lean_dec(x_14);
x_21 = lean_ctor_get(x_16, 1);
lean_inc(x_21);
lean_dec(x_16);
x_22 = lean_ctor_get(x_17, 0);
lean_inc(x_22);
lean_dec(x_17);
x_23 = l_Lean_Expr_isLet(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_box(0);
x_25 = l_Lean_Compiler_Simp_visitLet___lambda__1(x_12, x_2, x_10, x_9, x_13, x_22, x_24, x_3, x_4, x_5, x_6, x_7, x_21);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_unsigned_to_nat(0u);
x_27 = l_Lean_Compiler_Simp_mkFlatLet_go(x_9, x_10, x_12, x_13, x_22, x_26);
lean_dec(x_12);
x_28 = l_Lean_Compiler_Simp_visitLet(x_27, x_2, x_3, x_4, x_5, x_6, x_7, x_21);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
return x_28;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_28, 0);
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_28);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
else
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_28);
if (x_33 == 0)
{
return x_28;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_28, 0);
x_35 = lean_ctor_get(x_28, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_28);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
}
else
{
uint8_t x_37; 
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_37 = !lean_is_exclusive(x_16);
if (x_37 == 0)
{
return x_16;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_16, 0);
x_39 = lean_ctor_get(x_16, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_16);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
else
{
uint8_t x_41; lean_object* x_42; 
x_41 = 0;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_42 = l_Lean_Compiler_Simp_visitLambda(x_14, x_41, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = lean_box(0);
x_46 = l_Lean_Compiler_Simp_visitLet___lambda__1(x_12, x_2, x_10, x_9, x_13, x_43, x_45, x_3, x_4, x_5, x_6, x_7, x_44);
return x_46;
}
else
{
uint8_t x_47; 
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_47 = !lean_is_exclusive(x_42);
if (x_47 == 0)
{
return x_42;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_42, 0);
x_49 = lean_ctor_get(x_42, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_42);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
}
else
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_expr_instantiate_rev(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_51);
x_52 = l_Lean_Compiler_Simp_simpValue_x3f(x_51, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_51);
x_55 = l_Lean_Compiler_isCasesApp_x3f(x_51, x_6, x_7, x_54);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_58 = lean_box(0);
x_59 = l_Lean_Compiler_Simp_internalize_visitLambda___closed__1;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_51);
x_60 = l_Lean_Compiler_Simp_inlineApp_x3f(x_51, x_59, x_58, x_3, x_4, x_5, x_6, x_7, x_57);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_63 = l_Lean_Compiler_Simp_expandTrivialExpr(x_51, x_3, x_4, x_5, x_6, x_7, x_62);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_63;
}
else
{
uint8_t x_64; 
lean_dec(x_51);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_64 = !lean_is_exclusive(x_60);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_60, 0);
lean_dec(x_65);
x_66 = lean_ctor_get(x_61, 0);
lean_inc(x_66);
lean_dec(x_61);
lean_ctor_set(x_60, 0, x_66);
return x_60;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_60, 1);
lean_inc(x_67);
lean_dec(x_60);
x_68 = lean_ctor_get(x_61, 0);
lean_inc(x_68);
lean_dec(x_61);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_67);
return x_69;
}
}
}
else
{
uint8_t x_70; 
lean_dec(x_51);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_70 = !lean_is_exclusive(x_60);
if (x_70 == 0)
{
return x_60;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_60, 0);
x_72 = lean_ctor_get(x_60, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_60);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_55, 1);
lean_inc(x_74);
lean_dec(x_55);
x_75 = lean_ctor_get(x_56, 0);
lean_inc(x_75);
lean_dec(x_56);
x_76 = l_Lean_Compiler_Simp_visitCases(x_75, x_51, x_3, x_4, x_5, x_6, x_7, x_74);
return x_76;
}
}
else
{
uint8_t x_77; 
lean_dec(x_51);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_77 = !lean_is_exclusive(x_55);
if (x_77 == 0)
{
return x_55;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_55, 0);
x_79 = lean_ctor_get(x_55, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_55);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
lean_dec(x_51);
x_81 = lean_ctor_get(x_52, 1);
lean_inc(x_81);
lean_dec(x_52);
x_82 = lean_ctor_get(x_53, 0);
lean_inc(x_82);
lean_dec(x_53);
x_83 = l_Lean_Compiler_Simp_internalize_visitLambda___closed__1;
x_1 = x_82;
x_2 = x_83;
x_8 = x_81;
goto _start;
}
}
else
{
uint8_t x_85; 
lean_dec(x_51);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_85 = !lean_is_exclusive(x_52);
if (x_85 == 0)
{
return x_52;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_52, 0);
x_87 = lean_ctor_get(x_52, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_52);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_Simp_visitCases___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_nat_dec_le(x_3, x_2);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_eq(x_1, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_sub(x_1, x_15);
lean_dec(x_1);
x_17 = lean_array_get_size(x_5);
x_18 = lean_nat_dec_lt(x_2, x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_nat_add(x_2, x_4);
lean_dec(x_2);
x_1 = x_16;
x_2 = x_19;
goto _start;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; 
x_21 = lean_array_fget(x_5, x_2);
x_22 = lean_box(0);
x_23 = lean_array_fset(x_5, x_2, x_22);
x_24 = 1;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_25 = l_Lean_Compiler_Simp_visitLambda(x_21, x_24, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_array_fset(x_23, x_2, x_26);
x_29 = lean_nat_add(x_2, x_4);
lean_dec(x_2);
x_1 = x_16;
x_2 = x_29;
x_5 = x_28;
x_11 = x_27;
goto _start;
}
else
{
uint8_t x_31; 
lean_dec(x_23);
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_31 = !lean_is_exclusive(x_25);
if (x_31 == 0)
{
return x_25;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_25, 0);
x_33 = lean_ctor_get(x_25, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_25);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
else
{
lean_object* x_35; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_5);
lean_ctor_set(x_35, 1, x_11);
return x_35;
}
}
else
{
lean_object* x_36; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_5);
lean_ctor_set(x_36, 1, x_11);
return x_36;
}
}
}
static lean_object* _init_l_panic___at_Lean_Compiler_Simp_visitCases___spec__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_panic___at_Lean_Compiler_Simp_inlineProjInst_x3f_visitProj___spec__1___closed__2;
x_2 = l_Lean_instInhabitedExpr;
x_3 = l_instInhabited___rarg(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_panic___at_Lean_Compiler_Simp_visitCases___spec__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_panic___at_Lean_Compiler_Simp_visitCases___spec__2___closed__1;
x_2 = lean_alloc_closure((void*)(l_instInhabitedReaderT___rarg___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_Compiler_Simp_visitCases___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = l_panic___at_Lean_Compiler_Simp_visitCases___spec__2___closed__2;
x_9 = lean_panic_fn(x_8, x_1);
x_10 = lean_apply_6(x_9, x_2, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
static lean_object* _init_l_Lean_Compiler_Simp_visitCases___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("assertion violation: ", 21);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_Simp_visitCases___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("!alt.isLambda\n    ", 18);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_Simp_visitCases___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_Simp_visitCases___closed__1;
x_2 = l_Lean_Compiler_Simp_visitCases___closed__2;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_Simp_visitCases___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Compiler.Simp.visitCases", 29);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_Simp_visitCases___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Compiler_Simp_inlineProjInst_x3f_visitProj___closed__1;
x_2 = l_Lean_Compiler_Simp_visitCases___closed__4;
x_3 = lean_unsigned_to_nat(414u);
x_4 = lean_unsigned_to_nat(4u);
x_5 = l_Lean_Compiler_Simp_visitCases___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_visitCases(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; 
x_9 = l_Lean_Expr_getAppFn(x_2);
x_10 = lean_unsigned_to_nat(0u);
x_11 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_2, x_10);
x_12 = l_Lean_Compiler_Simp_internalize_visitCases___closed__1;
lean_inc(x_11);
x_13 = lean_mk_array(x_11, x_12);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_sub(x_11, x_14);
lean_dec(x_11);
x_16 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_2, x_13, x_15);
x_17 = lean_ctor_get(x_1, 2);
lean_inc(x_17);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_nat_sub(x_18, x_14);
lean_dec(x_18);
x_20 = lean_array_get_size(x_16);
x_21 = lean_nat_dec_lt(x_19, x_20);
if (x_21 == 0)
{
lean_object* x_90; lean_object* x_91; 
lean_dec(x_19);
x_90 = l_Lean_Compiler_Simp_simpProj_x3f___closed__4;
x_91 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_90);
x_22 = x_91;
goto block_89;
}
else
{
lean_object* x_92; 
x_92 = lean_array_fget(x_16, x_19);
lean_dec(x_19);
x_22 = x_92;
goto block_89;
}
block_89:
{
uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_23 = 1;
x_24 = l_Lean_Compiler_Simp_findExpr(x_22, x_23, x_5, x_6, x_7, x_8);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_st_ref_get(x_7, x_26);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_ctor_get(x_28, 0);
lean_inc(x_30);
lean_dec(x_28);
x_31 = l_Lean_Expr_constructorApp_x3f(x_30, x_25);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; 
lean_dec(x_20);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_16);
lean_inc(x_9);
lean_inc(x_1);
x_32 = l_Lean_Compiler_Simp_simpCasesOnCases_x3f(x_1, x_9, x_16, x_3, x_4, x_5, x_6, x_7, x_29);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_ctor_get(x_1, 3);
lean_inc(x_35);
lean_dec(x_1);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_35, 2);
lean_inc(x_38);
lean_dec(x_35);
lean_inc(x_36);
x_39 = l_Std_Range_forIn_loop___at_Lean_Compiler_Simp_visitCases___spec__1(x_36, x_37, x_36, x_38, x_16, x_3, x_4, x_5, x_6, x_7, x_34);
lean_dec(x_38);
lean_dec(x_36);
if (lean_obj_tag(x_39) == 0)
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_39, 0);
x_42 = l_Lean_mkAppN(x_9, x_41);
lean_ctor_set(x_39, 0, x_42);
return x_39;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_43 = lean_ctor_get(x_39, 0);
x_44 = lean_ctor_get(x_39, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_39);
x_45 = l_Lean_mkAppN(x_9, x_43);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_44);
return x_46;
}
}
else
{
uint8_t x_47; 
lean_dec(x_9);
x_47 = !lean_is_exclusive(x_39);
if (x_47 == 0)
{
return x_39;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_39, 0);
x_49 = lean_ctor_get(x_39, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_39);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
else
{
lean_object* x_51; lean_object* x_52; 
lean_dec(x_16);
lean_dec(x_9);
x_51 = lean_ctor_get(x_32, 1);
lean_inc(x_51);
lean_dec(x_32);
x_52 = lean_ctor_get(x_33, 0);
lean_inc(x_52);
lean_dec(x_33);
x_2 = x_52;
x_8 = x_51;
goto _start;
}
}
else
{
uint8_t x_54; 
lean_dec(x_16);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_54 = !lean_is_exclusive(x_32);
if (x_54 == 0)
{
return x_32;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_32, 0);
x_56 = lean_ctor_get(x_32, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_32);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_dec(x_9);
x_58 = lean_ctor_get(x_31, 0);
lean_inc(x_58);
lean_dec(x_31);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_61 = lean_ctor_get(x_59, 2);
lean_inc(x_61);
x_62 = lean_ctor_get(x_1, 3);
lean_inc(x_62);
lean_dec(x_1);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
lean_dec(x_62);
x_64 = lean_nat_add(x_63, x_61);
lean_dec(x_61);
lean_dec(x_63);
x_65 = lean_nat_dec_lt(x_64, x_20);
lean_dec(x_20);
x_66 = lean_ctor_get(x_59, 3);
lean_inc(x_66);
lean_dec(x_59);
x_67 = lean_array_get_size(x_60);
x_68 = l_Array_toSubarray___rarg(x_60, x_66, x_67);
x_69 = l_Array_ofSubarray___rarg(x_68);
if (x_65 == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; 
lean_dec(x_64);
lean_dec(x_16);
x_70 = l_Lean_Compiler_Simp_simpProj_x3f___closed__4;
x_71 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_70);
x_72 = l_Lean_Expr_beta(x_71, x_69);
x_73 = l_Lean_Expr_isLambda(x_72);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_74 = l_Lean_Compiler_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_29);
x_75 = lean_ctor_get(x_74, 1);
lean_inc(x_75);
lean_dec(x_74);
x_76 = l_Lean_Compiler_Simp_internalize_visitLambda___closed__1;
x_77 = l_Lean_Compiler_Simp_visitLet(x_72, x_76, x_3, x_4, x_5, x_6, x_7, x_75);
return x_77;
}
else
{
lean_object* x_78; lean_object* x_79; 
lean_dec(x_72);
x_78 = l_Lean_Compiler_Simp_visitCases___closed__5;
x_79 = l_panic___at_Lean_Compiler_Simp_visitCases___spec__2(x_78, x_3, x_4, x_5, x_6, x_7, x_29);
return x_79;
}
}
else
{
lean_object* x_80; lean_object* x_81; uint8_t x_82; 
x_80 = lean_array_fget(x_16, x_64);
lean_dec(x_64);
lean_dec(x_16);
x_81 = l_Lean_Expr_beta(x_80, x_69);
x_82 = l_Lean_Expr_isLambda(x_81);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_83 = l_Lean_Compiler_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_29);
x_84 = lean_ctor_get(x_83, 1);
lean_inc(x_84);
lean_dec(x_83);
x_85 = l_Lean_Compiler_Simp_internalize_visitLambda___closed__1;
x_86 = l_Lean_Compiler_Simp_visitLet(x_81, x_85, x_3, x_4, x_5, x_6, x_7, x_84);
return x_86;
}
else
{
lean_object* x_87; lean_object* x_88; 
lean_dec(x_81);
x_87 = l_Lean_Compiler_Simp_visitCases___closed__5;
x_88 = l_panic___at_Lean_Compiler_Simp_visitCases___spec__2(x_87, x_3, x_4, x_5, x_6, x_7, x_29);
return x_88;
}
}
}
}
}
}
static lean_object* _init_l_Lean_isTracingEnabledFor___at_Lean_Compiler_Simp_inlineApp_x3f___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_inheritedTraceOptions;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_Lean_Compiler_Simp_inlineApp_x3f___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = lean_st_ref_get(x_6, x_7);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = l_Lean_isTracingEnabledFor___at_Lean_Compiler_Simp_inlineApp_x3f___spec__1___closed__1;
x_11 = lean_st_ref_get(x_10, x_9);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_5, 2);
x_15 = l___private_Lean_Util_Trace_0__Lean_checkTraceOption(x_13, x_14, x_1);
lean_dec(x_13);
x_16 = lean_box(x_15);
lean_ctor_set(x_11, 0, x_16);
return x_11;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; 
x_17 = lean_ctor_get(x_11, 0);
x_18 = lean_ctor_get(x_11, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_11);
x_19 = lean_ctor_get(x_5, 2);
x_20 = l___private_Lean_Util_Trace_0__Lean_checkTraceOption(x_17, x_19, x_1);
lean_dec(x_17);
x_21 = lean_box(x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_18);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Compiler_Simp_inlineApp_x3f___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
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
x_14 = lean_st_ref_get(x_7, x_12);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_st_ref_get(x_5, x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_ctor_get(x_6, 2);
x_21 = l_Lean_throwError___at_Lean_Compiler_Simp_visitLambda___spec__3___closed__6;
lean_inc(x_20);
x_22 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_22, 0, x_13);
lean_ctor_set(x_22, 1, x_21);
lean_ctor_set(x_22, 2, x_19);
lean_ctor_set(x_22, 3, x_20);
x_23 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_2);
x_24 = lean_st_ref_take(x_7, x_18);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = !lean_is_exclusive(x_25);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_28 = lean_ctor_get(x_25, 3);
x_29 = l_Lean_Compiler_Simp_internalize_visitLambda___closed__1;
x_30 = 0;
x_31 = lean_alloc_ctor(12, 3, 1);
lean_ctor_set(x_31, 0, x_1);
lean_ctor_set(x_31, 1, x_23);
lean_ctor_set(x_31, 2, x_29);
lean_ctor_set_uint8(x_31, sizeof(void*)*3, x_30);
lean_inc(x_9);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_9);
lean_ctor_set(x_32, 1, x_31);
x_33 = l_Std_PersistentArray_push___rarg(x_28, x_32);
lean_ctor_set(x_25, 3, x_33);
x_34 = lean_st_ref_set(x_7, x_25, x_26);
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
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_41 = lean_ctor_get(x_25, 0);
x_42 = lean_ctor_get(x_25, 1);
x_43 = lean_ctor_get(x_25, 2);
x_44 = lean_ctor_get(x_25, 3);
x_45 = lean_ctor_get(x_25, 4);
x_46 = lean_ctor_get(x_25, 5);
x_47 = lean_ctor_get(x_25, 6);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_25);
x_48 = l_Lean_Compiler_Simp_internalize_visitLambda___closed__1;
x_49 = 0;
x_50 = lean_alloc_ctor(12, 3, 1);
lean_ctor_set(x_50, 0, x_1);
lean_ctor_set(x_50, 1, x_23);
lean_ctor_set(x_50, 2, x_48);
lean_ctor_set_uint8(x_50, sizeof(void*)*3, x_49);
lean_inc(x_9);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_9);
lean_ctor_set(x_51, 1, x_50);
x_52 = l_Std_PersistentArray_push___rarg(x_44, x_51);
x_53 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_53, 0, x_41);
lean_ctor_set(x_53, 1, x_42);
lean_ctor_set(x_53, 2, x_43);
lean_ctor_set(x_53, 3, x_52);
lean_ctor_set(x_53, 4, x_45);
lean_ctor_set(x_53, 5, x_46);
lean_ctor_set(x_53, 6, x_47);
x_54 = lean_st_ref_set(x_7, x_53, x_26);
x_55 = lean_ctor_get(x_54, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_56 = x_54;
} else {
 lean_dec_ref(x_54);
 x_56 = lean_box(0);
}
x_57 = lean_box(0);
if (lean_is_scalar(x_56)) {
 x_58 = lean_alloc_ctor(0, 2, 0);
} else {
 x_58 = x_56;
}
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_55);
return x_58;
}
}
}
static lean_object* _init_l_Lean_Compiler_Simp_inlineApp_x3f___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_inlineApp_x3f___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_9 = l_Lean_Compiler_mkLetUsingScope(x_2, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Compiler_Simp_inlineApp_x3f___lambda__1___closed__1;
x_13 = lean_array_push(x_12, x_1);
x_14 = l_Lean_Compiler_mkLambda(x_13, x_10, x_5, x_6, x_7, x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_13);
return x_14;
}
else
{
uint8_t x_15; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_15 = !lean_is_exclusive(x_9);
if (x_15 == 0)
{
return x_9;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_9, 0);
x_17 = lean_ctor_get(x_9, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_9);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_inlineApp_x3f___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_Simp_visitLet(x_2, x_1, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_10, 0, x_13);
return x_10;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_10, 0);
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_10);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_14);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_10);
if (x_18 == 0)
{
return x_10;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_10, 0);
x_20 = lean_ctor_get(x_10, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_10);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
static lean_object* _init_l_Lean_Compiler_Simp_inlineApp_x3f___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_x", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_Simp_inlineApp_x3f___lambda__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_Simp_inlineApp_x3f___lambda__3___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_inlineApp_x3f___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_dec(x_5);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_3);
x_12 = lean_box(0);
x_13 = l_Lean_Compiler_Simp_inlineApp_x3f___lambda__2(x_1, x_4, x_12, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_14 = lean_ctor_get(x_2, 0);
lean_inc(x_14);
lean_dec(x_2);
x_15 = lean_st_ref_get(x_10, x_11);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_st_ref_get(x_8, x_16);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
lean_dec(x_18);
lean_inc(x_10);
lean_inc(x_9);
x_21 = l_Lean_Compiler_InferType_inferType(x_3, x_20, x_9, x_10, x_19);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l_Lean_Compiler_Simp_inlineApp_x3f___lambda__3___closed__2;
x_25 = l_Lean_Compiler_mkAuxLetDeclName(x_24, x_8, x_9, x_10, x_23);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = 0;
x_29 = lean_unsigned_to_nat(0u);
x_30 = l_Lean_Compiler_Simp_mkFlatLet_go(x_26, x_22, x_14, x_28, x_4, x_29);
lean_dec(x_14);
x_31 = lean_box(0);
x_32 = l_Lean_Compiler_Simp_inlineApp_x3f___lambda__2(x_1, x_30, x_31, x_6, x_7, x_8, x_9, x_10, x_27);
return x_32;
}
else
{
uint8_t x_33; 
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_21);
if (x_33 == 0)
{
return x_21;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_21, 0);
x_35 = lean_ctor_get(x_21, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_21);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_Simp_inlineApp_x3f___lambda__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_y", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_Simp_inlineApp_x3f___lambda__4___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_Simp_inlineApp_x3f___lambda__4___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_Simp_inlineApp_x3f___lambda__4___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Init.Data.Option.BasicAux", 25);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_Simp_inlineApp_x3f___lambda__4___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Option.get!", 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_Simp_inlineApp_x3f___lambda__4___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("value is none", 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_Simp_inlineApp_x3f___lambda__4___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Compiler_Simp_inlineApp_x3f___lambda__4___closed__3;
x_2 = l_Lean_Compiler_Simp_inlineApp_x3f___lambda__4___closed__4;
x_3 = lean_unsigned_to_nat(16u);
x_4 = lean_unsigned_to_nat(14u);
x_5 = l_Lean_Compiler_Simp_inlineApp_x3f___lambda__4___closed__5;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Compiler_Simp_inlineApp_x3f___lambda__4___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Expr_bvar___override(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_inlineApp_x3f___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_7);
x_14 = l_Lean_Compiler_Simp_markSimplified___rarg(x_9, x_10, x_11, x_12, x_13);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_340; uint8_t x_341; 
x_340 = lean_ctor_get(x_1, 0);
lean_inc(x_340);
x_341 = lean_nat_dec_eq(x_4, x_340);
lean_dec(x_340);
if (x_341 == 0)
{
lean_object* x_342; 
x_342 = lean_box(0);
x_16 = x_342;
goto block_339;
}
else
{
lean_object* x_343; lean_object* x_344; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_343 = lean_ctor_get(x_1, 1);
lean_inc(x_343);
lean_dec(x_1);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_344 = l_Lean_Compiler_Simp_betaReduce(x_343, x_3, x_8, x_9, x_10, x_11, x_12, x_15);
if (lean_obj_tag(x_344) == 0)
{
lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; 
x_345 = lean_ctor_get(x_344, 0);
lean_inc(x_345);
x_346 = lean_ctor_get(x_344, 1);
lean_inc(x_346);
lean_dec(x_344);
x_347 = l_Lean_Compiler_Simp_internalize_visitLambda___closed__1;
x_348 = l_Lean_Compiler_Simp_visitLet(x_345, x_347, x_8, x_9, x_10, x_11, x_12, x_346);
if (lean_obj_tag(x_348) == 0)
{
uint8_t x_349; 
x_349 = !lean_is_exclusive(x_348);
if (x_349 == 0)
{
lean_object* x_350; lean_object* x_351; 
x_350 = lean_ctor_get(x_348, 0);
x_351 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_351, 0, x_350);
lean_ctor_set(x_348, 0, x_351);
return x_348;
}
else
{
lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; 
x_352 = lean_ctor_get(x_348, 0);
x_353 = lean_ctor_get(x_348, 1);
lean_inc(x_353);
lean_inc(x_352);
lean_dec(x_348);
x_354 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_354, 0, x_352);
x_355 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_355, 0, x_354);
lean_ctor_set(x_355, 1, x_353);
return x_355;
}
}
else
{
uint8_t x_356; 
x_356 = !lean_is_exclusive(x_348);
if (x_356 == 0)
{
return x_348;
}
else
{
lean_object* x_357; lean_object* x_358; lean_object* x_359; 
x_357 = lean_ctor_get(x_348, 0);
x_358 = lean_ctor_get(x_348, 1);
lean_inc(x_358);
lean_inc(x_357);
lean_dec(x_348);
x_359 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_359, 0, x_357);
lean_ctor_set(x_359, 1, x_358);
return x_359;
}
}
}
else
{
uint8_t x_360; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_360 = !lean_is_exclusive(x_344);
if (x_360 == 0)
{
return x_344;
}
else
{
lean_object* x_361; lean_object* x_362; lean_object* x_363; 
x_361 = lean_ctor_get(x_344, 0);
x_362 = lean_ctor_get(x_344, 1);
lean_inc(x_362);
lean_inc(x_361);
lean_dec(x_344);
x_363 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_363, 0, x_361);
lean_ctor_set(x_363, 1, x_362);
return x_363;
}
}
}
}
else
{
lean_object* x_364; 
x_364 = lean_box(0);
x_16 = x_364;
goto block_339;
}
block_339:
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_16);
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_17);
x_18 = l_Lean_Compiler_onlyOneExitPoint(x_17, x_11, x_12, x_15);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_unbox(x_19);
lean_dec(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = l_Lean_Expr_getAppFn(x_2);
lean_dec(x_2);
x_23 = lean_ctor_get(x_1, 0);
lean_inc(x_23);
lean_dec(x_1);
x_24 = lean_unsigned_to_nat(0u);
lean_inc(x_23);
lean_inc(x_3);
x_25 = l_Array_toSubarray___rarg(x_3, x_24, x_23);
x_26 = l_Array_ofSubarray___rarg(x_25);
lean_inc(x_26);
x_27 = l_Lean_mkAppN(x_22, x_26);
x_28 = lean_st_ref_get(x_12, x_21);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_30 = lean_st_ref_get(x_10, x_29);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_ctor_get(x_31, 0);
lean_inc(x_33);
lean_dec(x_31);
lean_inc(x_12);
lean_inc(x_11);
x_34 = l_Lean_Compiler_InferType_inferType(x_27, x_33, x_11, x_12, x_32);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_116; lean_object* x_117; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; uint8_t x_149; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = l_Lean_Compiler_Simp_inlineApp_x3f___lambda__4___closed__2;
x_38 = l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(x_37, x_11, x_12, x_36);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_83 = lean_st_ref_get(x_12, x_40);
x_84 = lean_ctor_get(x_83, 1);
lean_inc(x_84);
lean_dec(x_83);
x_85 = lean_st_ref_get(x_10, x_84);
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
lean_dec(x_85);
x_144 = lean_st_ref_get(x_12, x_87);
x_145 = lean_ctor_get(x_144, 1);
lean_inc(x_145);
lean_dec(x_144);
x_146 = lean_st_ref_take(x_10, x_145);
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_146, 1);
lean_inc(x_148);
lean_dec(x_146);
x_149 = !lean_is_exclusive(x_147);
if (x_149 == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; uint8_t x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; uint8_t x_158; 
x_150 = lean_ctor_get(x_147, 1);
lean_dec(x_150);
x_151 = l_Lean_Compiler_Simp_internalize_visitLambda___closed__1;
lean_ctor_set(x_147, 1, x_151);
x_152 = lean_st_ref_set(x_10, x_147, x_148);
x_153 = lean_ctor_get(x_152, 1);
lean_inc(x_153);
lean_dec(x_152);
x_154 = 0;
x_155 = l_Lean_Compiler_mkLocalDecl(x_39, x_35, x_154, x_10, x_11, x_12, x_153);
x_156 = lean_ctor_get(x_155, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_155, 1);
lean_inc(x_157);
lean_dec(x_155);
x_158 = lean_nat_dec_eq(x_4, x_23);
lean_dec(x_4);
if (x_158 == 0)
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_159 = lean_array_get_size(x_3);
x_160 = l_Array_toSubarray___rarg(x_3, x_23, x_159);
x_161 = l_Array_ofSubarray___rarg(x_160);
lean_inc(x_156);
x_162 = l_Lean_mkAppN(x_156, x_161);
x_163 = l_Lean_Compiler_Simp_inlineApp_x3f___lambda__3___closed__2;
lean_inc(x_12);
lean_inc(x_11);
x_164 = l_Lean_Compiler_mkAuxLetDecl(x_162, x_163, x_10, x_11, x_12, x_157);
if (lean_obj_tag(x_164) == 0)
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_165 = lean_ctor_get(x_164, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_164, 1);
lean_inc(x_166);
lean_dec(x_164);
lean_inc(x_165);
x_167 = lean_array_push(x_6, x_165);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_168 = l_Lean_Compiler_Simp_visitLet(x_165, x_167, x_8, x_9, x_10, x_11, x_12, x_166);
if (lean_obj_tag(x_168) == 0)
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_169 = lean_ctor_get(x_168, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_168, 1);
lean_inc(x_170);
lean_dec(x_168);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_171 = l_Lean_Compiler_Simp_inlineApp_x3f___lambda__1(x_156, x_169, x_8, x_9, x_10, x_11, x_12, x_170);
if (lean_obj_tag(x_171) == 0)
{
lean_object* x_172; lean_object* x_173; 
x_172 = lean_ctor_get(x_171, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_171, 1);
lean_inc(x_173);
lean_dec(x_171);
x_88 = x_172;
x_89 = x_173;
goto block_115;
}
else
{
lean_object* x_174; lean_object* x_175; 
x_174 = lean_ctor_get(x_171, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_171, 1);
lean_inc(x_175);
lean_dec(x_171);
x_116 = x_174;
x_117 = x_175;
goto block_143;
}
}
else
{
lean_object* x_176; lean_object* x_177; 
lean_dec(x_156);
x_176 = lean_ctor_get(x_168, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_168, 1);
lean_inc(x_177);
lean_dec(x_168);
x_116 = x_176;
x_117 = x_177;
goto block_143;
}
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_178 = lean_ctor_get(x_164, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_164, 1);
lean_inc(x_179);
lean_dec(x_164);
x_180 = lean_ctor_get(x_5, 0);
lean_inc(x_180);
lean_dec(x_5);
x_181 = lean_array_push(x_6, x_178);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_182 = l_Lean_Compiler_Simp_visitLet(x_180, x_181, x_8, x_9, x_10, x_11, x_12, x_179);
if (lean_obj_tag(x_182) == 0)
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_183 = lean_ctor_get(x_182, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_182, 1);
lean_inc(x_184);
lean_dec(x_182);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_185 = l_Lean_Compiler_Simp_inlineApp_x3f___lambda__1(x_156, x_183, x_8, x_9, x_10, x_11, x_12, x_184);
if (lean_obj_tag(x_185) == 0)
{
lean_object* x_186; lean_object* x_187; 
x_186 = lean_ctor_get(x_185, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_185, 1);
lean_inc(x_187);
lean_dec(x_185);
x_88 = x_186;
x_89 = x_187;
goto block_115;
}
else
{
lean_object* x_188; lean_object* x_189; 
x_188 = lean_ctor_get(x_185, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_185, 1);
lean_inc(x_189);
lean_dec(x_185);
x_116 = x_188;
x_117 = x_189;
goto block_143;
}
}
else
{
lean_object* x_190; lean_object* x_191; 
lean_dec(x_156);
x_190 = lean_ctor_get(x_182, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_182, 1);
lean_inc(x_191);
lean_dec(x_182);
x_116 = x_190;
x_117 = x_191;
goto block_143;
}
}
}
else
{
lean_object* x_192; lean_object* x_193; 
lean_dec(x_156);
lean_dec(x_6);
lean_dec(x_5);
x_192 = lean_ctor_get(x_164, 0);
lean_inc(x_192);
x_193 = lean_ctor_get(x_164, 1);
lean_inc(x_193);
lean_dec(x_164);
x_116 = x_192;
x_117 = x_193;
goto block_143;
}
}
else
{
lean_object* x_194; 
lean_dec(x_23);
lean_dec(x_3);
lean_inc(x_156);
x_194 = lean_array_push(x_6, x_156);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; 
x_195 = l_Lean_Compiler_Simp_inlineApp_x3f___lambda__4___closed__6;
x_196 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_195);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_197 = l_Lean_Compiler_Simp_visitLet(x_196, x_194, x_8, x_9, x_10, x_11, x_12, x_157);
if (lean_obj_tag(x_197) == 0)
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_198 = lean_ctor_get(x_197, 0);
lean_inc(x_198);
x_199 = lean_ctor_get(x_197, 1);
lean_inc(x_199);
lean_dec(x_197);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_200 = l_Lean_Compiler_Simp_inlineApp_x3f___lambda__1(x_156, x_198, x_8, x_9, x_10, x_11, x_12, x_199);
if (lean_obj_tag(x_200) == 0)
{
lean_object* x_201; lean_object* x_202; 
x_201 = lean_ctor_get(x_200, 0);
lean_inc(x_201);
x_202 = lean_ctor_get(x_200, 1);
lean_inc(x_202);
lean_dec(x_200);
x_88 = x_201;
x_89 = x_202;
goto block_115;
}
else
{
lean_object* x_203; lean_object* x_204; 
x_203 = lean_ctor_get(x_200, 0);
lean_inc(x_203);
x_204 = lean_ctor_get(x_200, 1);
lean_inc(x_204);
lean_dec(x_200);
x_116 = x_203;
x_117 = x_204;
goto block_143;
}
}
else
{
lean_object* x_205; lean_object* x_206; 
lean_dec(x_156);
x_205 = lean_ctor_get(x_197, 0);
lean_inc(x_205);
x_206 = lean_ctor_get(x_197, 1);
lean_inc(x_206);
lean_dec(x_197);
x_116 = x_205;
x_117 = x_206;
goto block_143;
}
}
else
{
lean_object* x_207; lean_object* x_208; 
x_207 = lean_ctor_get(x_5, 0);
lean_inc(x_207);
lean_dec(x_5);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_208 = l_Lean_Compiler_Simp_visitLet(x_207, x_194, x_8, x_9, x_10, x_11, x_12, x_157);
if (lean_obj_tag(x_208) == 0)
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; 
x_209 = lean_ctor_get(x_208, 0);
lean_inc(x_209);
x_210 = lean_ctor_get(x_208, 1);
lean_inc(x_210);
lean_dec(x_208);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_211 = l_Lean_Compiler_Simp_inlineApp_x3f___lambda__1(x_156, x_209, x_8, x_9, x_10, x_11, x_12, x_210);
if (lean_obj_tag(x_211) == 0)
{
lean_object* x_212; lean_object* x_213; 
x_212 = lean_ctor_get(x_211, 0);
lean_inc(x_212);
x_213 = lean_ctor_get(x_211, 1);
lean_inc(x_213);
lean_dec(x_211);
x_88 = x_212;
x_89 = x_213;
goto block_115;
}
else
{
lean_object* x_214; lean_object* x_215; 
x_214 = lean_ctor_get(x_211, 0);
lean_inc(x_214);
x_215 = lean_ctor_get(x_211, 1);
lean_inc(x_215);
lean_dec(x_211);
x_116 = x_214;
x_117 = x_215;
goto block_143;
}
}
else
{
lean_object* x_216; lean_object* x_217; 
lean_dec(x_156);
x_216 = lean_ctor_get(x_208, 0);
lean_inc(x_216);
x_217 = lean_ctor_get(x_208, 1);
lean_inc(x_217);
lean_dec(x_208);
x_116 = x_216;
x_117 = x_217;
goto block_143;
}
}
}
}
else
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; uint8_t x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; uint8_t x_228; 
x_218 = lean_ctor_get(x_147, 0);
x_219 = lean_ctor_get(x_147, 2);
lean_inc(x_219);
lean_inc(x_218);
lean_dec(x_147);
x_220 = l_Lean_Compiler_Simp_internalize_visitLambda___closed__1;
x_221 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_221, 0, x_218);
lean_ctor_set(x_221, 1, x_220);
lean_ctor_set(x_221, 2, x_219);
x_222 = lean_st_ref_set(x_10, x_221, x_148);
x_223 = lean_ctor_get(x_222, 1);
lean_inc(x_223);
lean_dec(x_222);
x_224 = 0;
x_225 = l_Lean_Compiler_mkLocalDecl(x_39, x_35, x_224, x_10, x_11, x_12, x_223);
x_226 = lean_ctor_get(x_225, 0);
lean_inc(x_226);
x_227 = lean_ctor_get(x_225, 1);
lean_inc(x_227);
lean_dec(x_225);
x_228 = lean_nat_dec_eq(x_4, x_23);
lean_dec(x_4);
if (x_228 == 0)
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; 
x_229 = lean_array_get_size(x_3);
x_230 = l_Array_toSubarray___rarg(x_3, x_23, x_229);
x_231 = l_Array_ofSubarray___rarg(x_230);
lean_inc(x_226);
x_232 = l_Lean_mkAppN(x_226, x_231);
x_233 = l_Lean_Compiler_Simp_inlineApp_x3f___lambda__3___closed__2;
lean_inc(x_12);
lean_inc(x_11);
x_234 = l_Lean_Compiler_mkAuxLetDecl(x_232, x_233, x_10, x_11, x_12, x_227);
if (lean_obj_tag(x_234) == 0)
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; 
x_235 = lean_ctor_get(x_234, 0);
lean_inc(x_235);
x_236 = lean_ctor_get(x_234, 1);
lean_inc(x_236);
lean_dec(x_234);
lean_inc(x_235);
x_237 = lean_array_push(x_6, x_235);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_238 = l_Lean_Compiler_Simp_visitLet(x_235, x_237, x_8, x_9, x_10, x_11, x_12, x_236);
if (lean_obj_tag(x_238) == 0)
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; 
x_239 = lean_ctor_get(x_238, 0);
lean_inc(x_239);
x_240 = lean_ctor_get(x_238, 1);
lean_inc(x_240);
lean_dec(x_238);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_241 = l_Lean_Compiler_Simp_inlineApp_x3f___lambda__1(x_226, x_239, x_8, x_9, x_10, x_11, x_12, x_240);
if (lean_obj_tag(x_241) == 0)
{
lean_object* x_242; lean_object* x_243; 
x_242 = lean_ctor_get(x_241, 0);
lean_inc(x_242);
x_243 = lean_ctor_get(x_241, 1);
lean_inc(x_243);
lean_dec(x_241);
x_88 = x_242;
x_89 = x_243;
goto block_115;
}
else
{
lean_object* x_244; lean_object* x_245; 
x_244 = lean_ctor_get(x_241, 0);
lean_inc(x_244);
x_245 = lean_ctor_get(x_241, 1);
lean_inc(x_245);
lean_dec(x_241);
x_116 = x_244;
x_117 = x_245;
goto block_143;
}
}
else
{
lean_object* x_246; lean_object* x_247; 
lean_dec(x_226);
x_246 = lean_ctor_get(x_238, 0);
lean_inc(x_246);
x_247 = lean_ctor_get(x_238, 1);
lean_inc(x_247);
lean_dec(x_238);
x_116 = x_246;
x_117 = x_247;
goto block_143;
}
}
else
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; 
x_248 = lean_ctor_get(x_234, 0);
lean_inc(x_248);
x_249 = lean_ctor_get(x_234, 1);
lean_inc(x_249);
lean_dec(x_234);
x_250 = lean_ctor_get(x_5, 0);
lean_inc(x_250);
lean_dec(x_5);
x_251 = lean_array_push(x_6, x_248);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_252 = l_Lean_Compiler_Simp_visitLet(x_250, x_251, x_8, x_9, x_10, x_11, x_12, x_249);
if (lean_obj_tag(x_252) == 0)
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; 
x_253 = lean_ctor_get(x_252, 0);
lean_inc(x_253);
x_254 = lean_ctor_get(x_252, 1);
lean_inc(x_254);
lean_dec(x_252);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_255 = l_Lean_Compiler_Simp_inlineApp_x3f___lambda__1(x_226, x_253, x_8, x_9, x_10, x_11, x_12, x_254);
if (lean_obj_tag(x_255) == 0)
{
lean_object* x_256; lean_object* x_257; 
x_256 = lean_ctor_get(x_255, 0);
lean_inc(x_256);
x_257 = lean_ctor_get(x_255, 1);
lean_inc(x_257);
lean_dec(x_255);
x_88 = x_256;
x_89 = x_257;
goto block_115;
}
else
{
lean_object* x_258; lean_object* x_259; 
x_258 = lean_ctor_get(x_255, 0);
lean_inc(x_258);
x_259 = lean_ctor_get(x_255, 1);
lean_inc(x_259);
lean_dec(x_255);
x_116 = x_258;
x_117 = x_259;
goto block_143;
}
}
else
{
lean_object* x_260; lean_object* x_261; 
lean_dec(x_226);
x_260 = lean_ctor_get(x_252, 0);
lean_inc(x_260);
x_261 = lean_ctor_get(x_252, 1);
lean_inc(x_261);
lean_dec(x_252);
x_116 = x_260;
x_117 = x_261;
goto block_143;
}
}
}
else
{
lean_object* x_262; lean_object* x_263; 
lean_dec(x_226);
lean_dec(x_6);
lean_dec(x_5);
x_262 = lean_ctor_get(x_234, 0);
lean_inc(x_262);
x_263 = lean_ctor_get(x_234, 1);
lean_inc(x_263);
lean_dec(x_234);
x_116 = x_262;
x_117 = x_263;
goto block_143;
}
}
else
{
lean_object* x_264; 
lean_dec(x_23);
lean_dec(x_3);
lean_inc(x_226);
x_264 = lean_array_push(x_6, x_226);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; 
x_265 = l_Lean_Compiler_Simp_inlineApp_x3f___lambda__4___closed__6;
x_266 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_265);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_267 = l_Lean_Compiler_Simp_visitLet(x_266, x_264, x_8, x_9, x_10, x_11, x_12, x_227);
if (lean_obj_tag(x_267) == 0)
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; 
x_268 = lean_ctor_get(x_267, 0);
lean_inc(x_268);
x_269 = lean_ctor_get(x_267, 1);
lean_inc(x_269);
lean_dec(x_267);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_270 = l_Lean_Compiler_Simp_inlineApp_x3f___lambda__1(x_226, x_268, x_8, x_9, x_10, x_11, x_12, x_269);
if (lean_obj_tag(x_270) == 0)
{
lean_object* x_271; lean_object* x_272; 
x_271 = lean_ctor_get(x_270, 0);
lean_inc(x_271);
x_272 = lean_ctor_get(x_270, 1);
lean_inc(x_272);
lean_dec(x_270);
x_88 = x_271;
x_89 = x_272;
goto block_115;
}
else
{
lean_object* x_273; lean_object* x_274; 
x_273 = lean_ctor_get(x_270, 0);
lean_inc(x_273);
x_274 = lean_ctor_get(x_270, 1);
lean_inc(x_274);
lean_dec(x_270);
x_116 = x_273;
x_117 = x_274;
goto block_143;
}
}
else
{
lean_object* x_275; lean_object* x_276; 
lean_dec(x_226);
x_275 = lean_ctor_get(x_267, 0);
lean_inc(x_275);
x_276 = lean_ctor_get(x_267, 1);
lean_inc(x_276);
lean_dec(x_267);
x_116 = x_275;
x_117 = x_276;
goto block_143;
}
}
else
{
lean_object* x_277; lean_object* x_278; 
x_277 = lean_ctor_get(x_5, 0);
lean_inc(x_277);
lean_dec(x_5);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_278 = l_Lean_Compiler_Simp_visitLet(x_277, x_264, x_8, x_9, x_10, x_11, x_12, x_227);
if (lean_obj_tag(x_278) == 0)
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; 
x_279 = lean_ctor_get(x_278, 0);
lean_inc(x_279);
x_280 = lean_ctor_get(x_278, 1);
lean_inc(x_280);
lean_dec(x_278);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_281 = l_Lean_Compiler_Simp_inlineApp_x3f___lambda__1(x_226, x_279, x_8, x_9, x_10, x_11, x_12, x_280);
if (lean_obj_tag(x_281) == 0)
{
lean_object* x_282; lean_object* x_283; 
x_282 = lean_ctor_get(x_281, 0);
lean_inc(x_282);
x_283 = lean_ctor_get(x_281, 1);
lean_inc(x_283);
lean_dec(x_281);
x_88 = x_282;
x_89 = x_283;
goto block_115;
}
else
{
lean_object* x_284; lean_object* x_285; 
x_284 = lean_ctor_get(x_281, 0);
lean_inc(x_284);
x_285 = lean_ctor_get(x_281, 1);
lean_inc(x_285);
lean_dec(x_281);
x_116 = x_284;
x_117 = x_285;
goto block_143;
}
}
else
{
lean_object* x_286; lean_object* x_287; 
lean_dec(x_226);
x_286 = lean_ctor_get(x_278, 0);
lean_inc(x_286);
x_287 = lean_ctor_get(x_278, 1);
lean_inc(x_287);
lean_dec(x_278);
x_116 = x_286;
x_117 = x_287;
goto block_143;
}
}
}
}
block_82:
{
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
lean_inc(x_12);
lean_inc(x_11);
x_44 = l_Lean_Compiler_mkJpDeclIfNotSimple(x_42, x_10, x_11, x_12, x_43);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_47 = l_Lean_Compiler_Simp_betaReduce(x_17, x_26, x_8, x_9, x_10, x_11, x_12, x_46);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_50 = l_Lean_Compiler_attachJp(x_48, x_45, x_10, x_11, x_12, x_49);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = l_Lean_Compiler_Simp_internalize_visitLambda___closed__1;
x_54 = l_Lean_Compiler_Simp_visitLet(x_51, x_53, x_8, x_9, x_10, x_11, x_12, x_52);
if (lean_obj_tag(x_54) == 0)
{
uint8_t x_55; 
x_55 = !lean_is_exclusive(x_54);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_54, 0);
x_57 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_54, 0, x_57);
return x_54;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_58 = lean_ctor_get(x_54, 0);
x_59 = lean_ctor_get(x_54, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_54);
x_60 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_60, 0, x_58);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_59);
return x_61;
}
}
else
{
uint8_t x_62; 
x_62 = !lean_is_exclusive(x_54);
if (x_62 == 0)
{
return x_54;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_54, 0);
x_64 = lean_ctor_get(x_54, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_54);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
else
{
uint8_t x_66; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_66 = !lean_is_exclusive(x_50);
if (x_66 == 0)
{
return x_50;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_50, 0);
x_68 = lean_ctor_get(x_50, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_50);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
}
else
{
uint8_t x_70; 
lean_dec(x_45);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_70 = !lean_is_exclusive(x_47);
if (x_70 == 0)
{
return x_47;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_47, 0);
x_72 = lean_ctor_get(x_47, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_47);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
}
else
{
uint8_t x_74; 
lean_dec(x_26);
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_74 = !lean_is_exclusive(x_44);
if (x_74 == 0)
{
return x_44;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_44, 0);
x_76 = lean_ctor_get(x_44, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_44);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
}
else
{
uint8_t x_78; 
lean_dec(x_26);
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_78 = !lean_is_exclusive(x_41);
if (x_78 == 0)
{
return x_41;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_41, 0);
x_80 = lean_ctor_get(x_41, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_41);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
block_115:
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; 
x_90 = lean_st_ref_get(x_12, x_89);
x_91 = lean_ctor_get(x_90, 1);
lean_inc(x_91);
lean_dec(x_90);
x_92 = lean_st_ref_get(x_10, x_91);
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
lean_dec(x_92);
x_95 = lean_ctor_get(x_86, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_86, 1);
lean_inc(x_96);
lean_dec(x_86);
x_97 = !lean_is_exclusive(x_93);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_98 = lean_ctor_get(x_93, 1);
lean_dec(x_98);
x_99 = lean_ctor_get(x_93, 0);
lean_dec(x_99);
lean_ctor_set(x_93, 1, x_96);
lean_ctor_set(x_93, 0, x_95);
x_100 = lean_st_ref_get(x_12, x_94);
x_101 = lean_ctor_get(x_100, 1);
lean_inc(x_101);
lean_dec(x_100);
x_102 = lean_st_ref_set(x_10, x_93, x_101);
x_103 = !lean_is_exclusive(x_102);
if (x_103 == 0)
{
lean_object* x_104; 
x_104 = lean_ctor_get(x_102, 0);
lean_dec(x_104);
lean_ctor_set(x_102, 0, x_88);
x_41 = x_102;
goto block_82;
}
else
{
lean_object* x_105; lean_object* x_106; 
x_105 = lean_ctor_get(x_102, 1);
lean_inc(x_105);
lean_dec(x_102);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_88);
lean_ctor_set(x_106, 1, x_105);
x_41 = x_106;
goto block_82;
}
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_107 = lean_ctor_get(x_93, 2);
lean_inc(x_107);
lean_dec(x_93);
x_108 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_108, 0, x_95);
lean_ctor_set(x_108, 1, x_96);
lean_ctor_set(x_108, 2, x_107);
x_109 = lean_st_ref_get(x_12, x_94);
x_110 = lean_ctor_get(x_109, 1);
lean_inc(x_110);
lean_dec(x_109);
x_111 = lean_st_ref_set(x_10, x_108, x_110);
x_112 = lean_ctor_get(x_111, 1);
lean_inc(x_112);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 x_113 = x_111;
} else {
 lean_dec_ref(x_111);
 x_113 = lean_box(0);
}
if (lean_is_scalar(x_113)) {
 x_114 = lean_alloc_ctor(0, 2, 0);
} else {
 x_114 = x_113;
}
lean_ctor_set(x_114, 0, x_88);
lean_ctor_set(x_114, 1, x_112);
x_41 = x_114;
goto block_82;
}
}
block_143:
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; uint8_t x_125; 
x_118 = lean_st_ref_get(x_12, x_117);
x_119 = lean_ctor_get(x_118, 1);
lean_inc(x_119);
lean_dec(x_118);
x_120 = lean_st_ref_get(x_10, x_119);
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_120, 1);
lean_inc(x_122);
lean_dec(x_120);
x_123 = lean_ctor_get(x_86, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_86, 1);
lean_inc(x_124);
lean_dec(x_86);
x_125 = !lean_is_exclusive(x_121);
if (x_125 == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; uint8_t x_131; 
x_126 = lean_ctor_get(x_121, 1);
lean_dec(x_126);
x_127 = lean_ctor_get(x_121, 0);
lean_dec(x_127);
lean_ctor_set(x_121, 1, x_124);
lean_ctor_set(x_121, 0, x_123);
x_128 = lean_st_ref_get(x_12, x_122);
x_129 = lean_ctor_get(x_128, 1);
lean_inc(x_129);
lean_dec(x_128);
x_130 = lean_st_ref_set(x_10, x_121, x_129);
x_131 = !lean_is_exclusive(x_130);
if (x_131 == 0)
{
lean_object* x_132; 
x_132 = lean_ctor_get(x_130, 0);
lean_dec(x_132);
lean_ctor_set_tag(x_130, 1);
lean_ctor_set(x_130, 0, x_116);
x_41 = x_130;
goto block_82;
}
else
{
lean_object* x_133; lean_object* x_134; 
x_133 = lean_ctor_get(x_130, 1);
lean_inc(x_133);
lean_dec(x_130);
x_134 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_134, 0, x_116);
lean_ctor_set(x_134, 1, x_133);
x_41 = x_134;
goto block_82;
}
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_135 = lean_ctor_get(x_121, 2);
lean_inc(x_135);
lean_dec(x_121);
x_136 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_136, 0, x_123);
lean_ctor_set(x_136, 1, x_124);
lean_ctor_set(x_136, 2, x_135);
x_137 = lean_st_ref_get(x_12, x_122);
x_138 = lean_ctor_get(x_137, 1);
lean_inc(x_138);
lean_dec(x_137);
x_139 = lean_st_ref_set(x_10, x_136, x_138);
x_140 = lean_ctor_get(x_139, 1);
lean_inc(x_140);
if (lean_is_exclusive(x_139)) {
 lean_ctor_release(x_139, 0);
 lean_ctor_release(x_139, 1);
 x_141 = x_139;
} else {
 lean_dec_ref(x_139);
 x_141 = lean_box(0);
}
if (lean_is_scalar(x_141)) {
 x_142 = lean_alloc_ctor(1, 2, 0);
} else {
 x_142 = x_141;
 lean_ctor_set_tag(x_142, 1);
}
lean_ctor_set(x_142, 0, x_116);
lean_ctor_set(x_142, 1, x_140);
x_41 = x_142;
goto block_82;
}
}
}
else
{
uint8_t x_288; 
lean_dec(x_26);
lean_dec(x_23);
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_288 = !lean_is_exclusive(x_34);
if (x_288 == 0)
{
return x_34;
}
else
{
lean_object* x_289; lean_object* x_290; lean_object* x_291; 
x_289 = lean_ctor_get(x_34, 0);
x_290 = lean_ctor_get(x_34, 1);
lean_inc(x_290);
lean_inc(x_289);
lean_dec(x_34);
x_291 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_291, 0, x_289);
lean_ctor_set(x_291, 1, x_290);
return x_291;
}
}
}
else
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; 
x_292 = lean_ctor_get(x_18, 1);
lean_inc(x_292);
lean_dec(x_18);
x_293 = lean_ctor_get(x_1, 0);
lean_inc(x_293);
lean_dec(x_1);
x_294 = lean_unsigned_to_nat(0u);
lean_inc(x_293);
lean_inc(x_3);
x_295 = l_Array_toSubarray___rarg(x_3, x_294, x_293);
x_296 = l_Array_ofSubarray___rarg(x_295);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_296);
x_297 = l_Lean_Compiler_Simp_betaReduce(x_17, x_296, x_8, x_9, x_10, x_11, x_12, x_292);
if (lean_obj_tag(x_297) == 0)
{
lean_object* x_298; lean_object* x_299; uint8_t x_300; 
x_298 = lean_ctor_get(x_297, 0);
lean_inc(x_298);
x_299 = lean_ctor_get(x_297, 1);
lean_inc(x_299);
lean_dec(x_297);
x_300 = lean_nat_dec_lt(x_293, x_4);
lean_dec(x_4);
if (x_300 == 0)
{
lean_object* x_301; lean_object* x_302; 
lean_dec(x_296);
lean_dec(x_293);
lean_dec(x_3);
x_301 = lean_box(0);
x_302 = l_Lean_Compiler_Simp_inlineApp_x3f___lambda__3(x_6, x_5, x_2, x_298, x_301, x_8, x_9, x_10, x_11, x_12, x_299);
return x_302;
}
else
{
lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; 
x_303 = l_Lean_Expr_getAppFn(x_2);
x_304 = l_Lean_mkAppN(x_303, x_296);
x_305 = lean_st_ref_get(x_12, x_299);
x_306 = lean_ctor_get(x_305, 1);
lean_inc(x_306);
lean_dec(x_305);
x_307 = lean_st_ref_get(x_10, x_306);
x_308 = lean_ctor_get(x_307, 0);
lean_inc(x_308);
x_309 = lean_ctor_get(x_307, 1);
lean_inc(x_309);
lean_dec(x_307);
x_310 = lean_ctor_get(x_308, 0);
lean_inc(x_310);
lean_dec(x_308);
lean_inc(x_12);
lean_inc(x_11);
x_311 = l_Lean_Compiler_InferType_inferType(x_304, x_310, x_11, x_12, x_309);
if (lean_obj_tag(x_311) == 0)
{
lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; uint8_t x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; 
x_312 = lean_ctor_get(x_311, 0);
lean_inc(x_312);
x_313 = lean_ctor_get(x_311, 1);
lean_inc(x_313);
lean_dec(x_311);
x_314 = l_Lean_Compiler_Simp_inlineApp_x3f___lambda__3___closed__2;
x_315 = l_Lean_Compiler_mkAuxLetDeclName(x_314, x_10, x_11, x_12, x_313);
x_316 = lean_ctor_get(x_315, 0);
lean_inc(x_316);
x_317 = lean_ctor_get(x_315, 1);
lean_inc(x_317);
lean_dec(x_315);
x_318 = lean_array_get_size(x_3);
x_319 = l_Array_toSubarray___rarg(x_3, x_293, x_318);
x_320 = l_Array_ofSubarray___rarg(x_319);
x_321 = l_Lean_Compiler_Simp_inlineApp_x3f___lambda__4___closed__7;
x_322 = l_Lean_mkAppN(x_321, x_320);
x_323 = 0;
x_324 = l_Lean_Compiler_Simp_mkFlatLet_go(x_316, x_312, x_322, x_323, x_298, x_294);
lean_dec(x_322);
x_325 = lean_box(0);
x_326 = l_Lean_Compiler_Simp_inlineApp_x3f___lambda__3(x_6, x_5, x_2, x_324, x_325, x_8, x_9, x_10, x_11, x_12, x_317);
return x_326;
}
else
{
uint8_t x_327; 
lean_dec(x_298);
lean_dec(x_293);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_327 = !lean_is_exclusive(x_311);
if (x_327 == 0)
{
return x_311;
}
else
{
lean_object* x_328; lean_object* x_329; lean_object* x_330; 
x_328 = lean_ctor_get(x_311, 0);
x_329 = lean_ctor_get(x_311, 1);
lean_inc(x_329);
lean_inc(x_328);
lean_dec(x_311);
x_330 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_330, 0, x_328);
lean_ctor_set(x_330, 1, x_329);
return x_330;
}
}
}
}
else
{
uint8_t x_331; 
lean_dec(x_296);
lean_dec(x_293);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_331 = !lean_is_exclusive(x_297);
if (x_331 == 0)
{
return x_297;
}
else
{
lean_object* x_332; lean_object* x_333; lean_object* x_334; 
x_332 = lean_ctor_get(x_297, 0);
x_333 = lean_ctor_get(x_297, 1);
lean_inc(x_333);
lean_inc(x_332);
lean_dec(x_297);
x_334 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_334, 0, x_332);
lean_ctor_set(x_334, 1, x_333);
return x_334;
}
}
}
}
else
{
uint8_t x_335; 
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_335 = !lean_is_exclusive(x_18);
if (x_335 == 0)
{
return x_18;
}
else
{
lean_object* x_336; lean_object* x_337; lean_object* x_338; 
x_336 = lean_ctor_get(x_18, 0);
x_337 = lean_ctor_get(x_18, 1);
lean_inc(x_337);
lean_inc(x_336);
lean_dec(x_18);
x_338 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_338, 0, x_336);
lean_ctor_set(x_338, 1, x_337);
return x_338;
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_Simp_inlineApp_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Compiler", 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_Simp_inlineApp_x3f___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_Simp_inlineApp_x3f___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_Simp_inlineApp_x3f___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("simp", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_Simp_inlineApp_x3f___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_Simp_inlineApp_x3f___closed__2;
x_2 = l_Lean_Compiler_Simp_inlineApp_x3f___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_Simp_inlineApp_x3f___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("inline", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_Simp_inlineApp_x3f___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_Simp_inlineApp_x3f___closed__4;
x_2 = l_Lean_Compiler_Simp_inlineApp_x3f___closed__5;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_Simp_inlineApp_x3f___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("inlining ", 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_Simp_inlineApp_x3f___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_Simp_inlineApp_x3f___closed__7;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_inlineApp_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_10 = l_Lean_Compiler_Simp_inlineCandidate_x3f(x_1, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_10, 0);
lean_dec(x_13);
x_14 = lean_box(0);
lean_ctor_set(x_10, 0, x_14);
return x_10;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_dec(x_10);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_18 = lean_ctor_get(x_10, 1);
lean_inc(x_18);
lean_dec(x_10);
x_19 = lean_ctor_get(x_11, 0);
lean_inc(x_19);
lean_dec(x_11);
x_20 = lean_unsigned_to_nat(0u);
x_21 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_20);
x_22 = l_Lean_Compiler_Simp_internalize_visitCases___closed__1;
lean_inc(x_21);
x_23 = lean_mk_array(x_21, x_22);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_sub(x_21, x_24);
lean_dec(x_21);
lean_inc(x_1);
x_26 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_23, x_25);
x_27 = lean_array_get_size(x_26);
x_28 = l_Lean_Compiler_Simp_inlineApp_x3f___closed__6;
x_29 = l_Lean_isTracingEnabledFor___at_Lean_Compiler_Simp_inlineApp_x3f___spec__1(x_28, x_4, x_5, x_6, x_7, x_8, x_18);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_unbox(x_30);
lean_dec(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
lean_dec(x_29);
x_33 = lean_box(0);
x_34 = l_Lean_Compiler_Simp_inlineApp_x3f___lambda__4(x_19, x_1, x_26, x_27, x_3, x_2, x_33, x_4, x_5, x_6, x_7, x_8, x_32);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_35 = lean_ctor_get(x_29, 1);
lean_inc(x_35);
lean_dec(x_29);
lean_inc(x_1);
x_36 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_36, 0, x_1);
x_37 = l_Lean_Compiler_Simp_inlineApp_x3f___closed__8;
x_38 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
x_39 = l_Lean_Compiler_getLevel___at_Lean_Compiler_Simp_visitLambda___spec__2___closed__3;
x_40 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_41 = l_Lean_addTrace___at_Lean_Compiler_Simp_inlineApp_x3f___spec__2(x_28, x_40, x_4, x_5, x_6, x_7, x_8, x_35);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = l_Lean_Compiler_Simp_inlineApp_x3f___lambda__4(x_19, x_1, x_26, x_27, x_3, x_2, x_42, x_4, x_5, x_6, x_7, x_8, x_43);
return x_44;
}
}
}
else
{
uint8_t x_45; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_45 = !lean_is_exclusive(x_10);
if (x_45 == 0)
{
return x_10;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_10, 0);
x_47 = lean_ctor_get(x_10, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_10);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_Simp_visitLambda___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_throwError___at_Lean_Compiler_Simp_visitLambda___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_getLevel___at_Lean_Compiler_Simp_visitLambda___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_getLevel___at_Lean_Compiler_Simp_visitLambda___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_mkLcUnreachable___at_Lean_Compiler_Simp_visitLambda___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_mkLcUnreachable___at_Lean_Compiler_Simp_visitLambda___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_Simp_visitLambda___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_15 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_16 = l_Array_forInUnsafe_loop___at_Lean_Compiler_Simp_visitLambda___spec__4(x_1, x_2, x_3, x_4, x_14, x_15, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_visitLambda___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_Simp_visitLambda___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_visitLambda___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = l_Lean_Compiler_Simp_visitLambda(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_visitLet___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_5);
lean_dec(x_5);
x_15 = l_Lean_Compiler_Simp_visitLet___lambda__1(x_1, x_2, x_3, x_4, x_14, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_visitLet___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Compiler_Simp_visitLet___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_4);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_Simp_visitCases___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Std_Range_forIn_loop___at_Lean_Compiler_Simp_visitCases___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_Lean_Compiler_Simp_inlineApp_x3f___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_isTracingEnabledFor___at_Lean_Compiler_Simp_inlineApp_x3f___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Compiler_Simp_inlineApp_x3f___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_addTrace___at_Lean_Compiler_Simp_inlineApp_x3f___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_inlineApp_x3f___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_Simp_inlineApp_x3f___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Simp_inlineApp_x3f___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_Simp_inlineApp_x3f___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Decl_simp_x3f___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_st_ref_get(x_10, x_11);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_st_ref_get(x_7, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get_uint8(x_15, sizeof(void*)*1);
lean_dec(x_15);
if (x_16 == 0)
{
uint8_t x_17; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_17 = !lean_is_exclusive(x_14);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_14, 0);
lean_dec(x_18);
x_19 = lean_box(0);
lean_ctor_set(x_14, 0, x_19);
return x_14;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_14, 1);
lean_inc(x_20);
lean_dec(x_14);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_14);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_14, 0);
lean_dec(x_24);
x_25 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_25, 0, x_1);
lean_ctor_set(x_25, 1, x_2);
lean_ctor_set(x_25, 2, x_3);
lean_ctor_set(x_25, 3, x_4);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_14, 0, x_26);
return x_14;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_14, 1);
lean_inc(x_27);
lean_dec(x_14);
x_28 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_28, 0, x_1);
lean_ctor_set(x_28, 1, x_2);
lean_ctor_set(x_28, 2, x_3);
lean_ctor_set(x_28, 3, x_4);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_27);
return x_30;
}
}
}
}
static lean_object* _init_l_Lean_Compiler_Decl_simp_x3f___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("stat", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_Decl_simp_x3f___lambda__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(": ", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_Decl_simp_x3f___lambda__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_Decl_simp_x3f___lambda__2___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Decl_simp_x3f___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
lean_dec(x_7);
x_14 = l_Lean_Compiler_Decl_simp_x3f___lambda__2___closed__1;
x_15 = l_Lean_Name_str___override(x_1, x_14);
lean_inc(x_15);
x_16 = l_Lean_isTracingEnabledFor___at_Lean_Compiler_Simp_inlineApp_x3f___spec__1(x_15, x_8, x_9, x_10, x_11, x_12, x_13);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_unbox(x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_15);
lean_dec(x_6);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_box(0);
x_21 = l_Lean_Compiler_Decl_simp_x3f___lambda__1(x_2, x_3, x_4, x_5, x_20, x_8, x_9, x_10, x_11, x_12, x_19);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_16, 1);
lean_inc(x_22);
lean_dec(x_16);
lean_inc(x_12);
lean_inc(x_11);
x_23 = l_Lean_Compiler_getLCNFSize(x_6, x_11, x_12, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
lean_inc(x_2);
x_26 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_26, 0, x_2);
x_27 = l_Lean_Compiler_getLevel___at_Lean_Compiler_Simp_visitLambda___spec__2___closed__3;
x_28 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
x_29 = l_Lean_Compiler_Decl_simp_x3f___lambda__2___closed__3;
x_30 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = l_Nat_repr(x_24);
x_32 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_33 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_34 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_34, 0, x_30);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_27);
x_36 = l_Lean_addTrace___at_Lean_Compiler_Simp_inlineApp_x3f___spec__2(x_15, x_35, x_8, x_9, x_10, x_11, x_12, x_25);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = l_Lean_Compiler_Decl_simp_x3f___lambda__1(x_2, x_3, x_4, x_5, x_37, x_8, x_9, x_10, x_11, x_12, x_38);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_37);
return x_39;
}
else
{
uint8_t x_40; 
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_40 = !lean_is_exclusive(x_23);
if (x_40 == 0)
{
return x_23;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_23, 0);
x_42 = lean_ctor_get(x_23, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_23);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_Decl_simp_x3f___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("new", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_Decl_simp_x3f___lambda__3___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" :=\n", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_Decl_simp_x3f___lambda__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_Decl_simp_x3f___lambda__3___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Decl_simp_x3f___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; 
lean_dec(x_8);
x_15 = 0;
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_16 = l_Lean_Compiler_Simp_visitLambda(x_1, x_15, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_Compiler_Decl_simp_x3f___lambda__3___closed__1;
x_20 = l_Lean_Name_str___override(x_2, x_19);
lean_inc(x_20);
x_21 = l_Lean_isTracingEnabledFor___at_Lean_Compiler_Simp_inlineApp_x3f___spec__1(x_20, x_9, x_10, x_11, x_12, x_13, x_18);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_unbox(x_22);
lean_dec(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_20);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_box(0);
x_26 = l_Lean_Compiler_Decl_simp_x3f___lambda__2(x_3, x_4, x_5, x_6, x_17, x_7, x_25, x_9, x_10, x_11, x_12, x_13, x_24);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_27 = lean_ctor_get(x_21, 1);
lean_inc(x_27);
lean_dec(x_21);
lean_inc(x_4);
x_28 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_28, 0, x_4);
x_29 = l_Lean_Compiler_getLevel___at_Lean_Compiler_Simp_visitLambda___spec__2___closed__3;
x_30 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
x_31 = l_Lean_Compiler_Decl_simp_x3f___lambda__3___closed__3;
x_32 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
lean_inc(x_17);
x_33 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_33, 0, x_17);
x_34 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_29);
x_36 = l_Lean_addTrace___at_Lean_Compiler_Simp_inlineApp_x3f___spec__2(x_20, x_35, x_9, x_10, x_11, x_12, x_13, x_27);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = l_Lean_Compiler_Decl_simp_x3f___lambda__2(x_3, x_4, x_5, x_6, x_17, x_7, x_37, x_9, x_10, x_11, x_12, x_13, x_38);
return x_39;
}
}
else
{
uint8_t x_40; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_40 = !lean_is_exclusive(x_16);
if (x_40 == 0)
{
return x_16;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_16, 0);
x_42 = lean_ctor_get(x_16, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_16);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
}
static lean_object* _init_l_Lean_Compiler_Decl_simp_x3f___lambda__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("step", 4);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Decl_simp_x3f___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
lean_dec(x_7);
x_14 = l_Lean_Compiler_Decl_simp_x3f___lambda__4___closed__1;
lean_inc(x_1);
x_15 = l_Lean_Name_str___override(x_1, x_14);
lean_inc(x_15);
x_16 = l_Lean_isTracingEnabledFor___at_Lean_Compiler_Simp_inlineApp_x3f___spec__1(x_15, x_8, x_9, x_10, x_11, x_12, x_13);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_unbox(x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_box(0);
x_21 = l_Lean_Compiler_Decl_simp_x3f___lambda__3(x_2, x_15, x_1, x_3, x_4, x_5, x_6, x_20, x_8, x_9, x_10, x_11, x_12, x_19);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_22 = lean_ctor_get(x_16, 1);
lean_inc(x_22);
lean_dec(x_16);
lean_inc(x_3);
x_23 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_23, 0, x_3);
x_24 = l_Lean_Compiler_getLevel___at_Lean_Compiler_Simp_visitLambda___spec__2___closed__3;
x_25 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
x_26 = l_Lean_Compiler_Decl_simp_x3f___lambda__3___closed__3;
x_27 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
lean_inc(x_6);
x_28 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_28, 0, x_6);
x_29 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_24);
lean_inc(x_15);
x_31 = l_Lean_addTrace___at_Lean_Compiler_Simp_inlineApp_x3f___spec__2(x_15, x_30, x_8, x_9, x_10, x_11, x_12, x_22);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = l_Lean_Compiler_Decl_simp_x3f___lambda__3(x_2, x_15, x_1, x_3, x_4, x_5, x_6, x_32, x_8, x_9, x_10, x_11, x_12, x_33);
return x_34;
}
}
}
static lean_object* _init_l_Lean_Compiler_Decl_simp_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("occs", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_Decl_simp_x3f___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_Simp_inlineApp_x3f___closed__6;
x_2 = l_Lean_Compiler_Decl_simp_x3f___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_Decl_simp_x3f___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(":", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_Decl_simp_x3f___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_Decl_simp_x3f___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Decl_simp_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 2);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 3);
lean_inc(x_11);
lean_dec(x_1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_11);
x_12 = l_Lean_Compiler_Simp_internalize_visitLambda(x_11, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Compiler_Decl_simp_x3f___closed__2;
x_16 = l_Lean_isTracingEnabledFor___at_Lean_Compiler_Simp_inlineApp_x3f___spec__1(x_15, x_2, x_3, x_4, x_5, x_6, x_14);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_unbox(x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = l_Lean_Compiler_Simp_inlineApp_x3f___closed__4;
x_21 = lean_box(0);
x_22 = l_Lean_Compiler_Decl_simp_x3f___lambda__4(x_20, x_13, x_8, x_9, x_10, x_11, x_21, x_2, x_3, x_4, x_5, x_6, x_19);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_23 = lean_ctor_get(x_16, 1);
lean_inc(x_23);
lean_dec(x_16);
x_24 = lean_st_ref_get(x_6, x_23);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_26 = lean_st_ref_get(x_3, x_25);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
lean_inc(x_8);
x_29 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_29, 0, x_8);
x_30 = l_Lean_Compiler_getLevel___at_Lean_Compiler_Simp_visitLambda___spec__2___closed__3;
x_31 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
x_32 = l_Lean_Compiler_Decl_simp_x3f___closed__4;
x_33 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_ctor_get(x_27, 0);
lean_inc(x_34);
lean_dec(x_27);
x_35 = l_Lean_Compiler_Simp_OccInfo_format(x_34);
x_36 = l___private_Lean_Compiler_Simp_0__Lean_Compiler_Simp_reprOcc____x40_Lean_Compiler_Simp___hyg_296____closed__3;
x_37 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
x_38 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_38, 0, x_37);
x_39 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_39, 0, x_33);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_30);
x_41 = l_Lean_addTrace___at_Lean_Compiler_Simp_inlineApp_x3f___spec__2(x_15, x_40, x_2, x_3, x_4, x_5, x_6, x_28);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = l_Lean_Compiler_Simp_inlineApp_x3f___closed__4;
x_45 = l_Lean_Compiler_Decl_simp_x3f___lambda__4(x_44, x_13, x_8, x_9, x_10, x_11, x_42, x_2, x_3, x_4, x_5, x_6, x_43);
return x_45;
}
}
else
{
uint8_t x_46; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_46 = !lean_is_exclusive(x_12);
if (x_46 == 0)
{
return x_12;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_12, 0);
x_48 = lean_ctor_get(x_12, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_12);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Decl_simp_x3f___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Compiler_Decl_simp_x3f___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_12;
}
}
static lean_object* _init_l_Lean_Compiler_Decl_simp___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_throwError___at_Lean_Compiler_Simp_visitLambda___spec__3___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_Decl_simp___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_Decl_simp___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_Decl_simp___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_Decl_simp___closed__4() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = l_Lean_Compiler_Decl_simp___closed__3;
x_3 = l_Lean_Compiler_Decl_simp___closed__2;
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
lean_ctor_set(x_5, 3, x_4);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Compiler_Decl_simp___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_Decl_simp___closed__1;
x_2 = l_Lean_Compiler_Decl_simp___closed__4;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_Decl_simp___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Compiler_Decl_simp___closed__5;
x_2 = l_Lean_Compiler_Simp_internalize_visitLambda___closed__1;
x_3 = lean_unsigned_to_nat(1u);
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Decl_simp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_Lean_Compiler_Decl_simp___closed__6;
x_8 = lean_st_mk_ref(x_7, x_6);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_st_ref_get(x_3, x_10);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = l_Lean_Compiler_Simp_instInhabitedState___closed__1;
x_14 = lean_st_mk_ref(x_13, x_12);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_unsigned_to_nat(1u);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_9);
lean_inc(x_15);
lean_inc(x_1);
x_18 = l_Lean_Compiler_Decl_simp_x3f(x_1, x_17, x_15, x_9, x_2, x_3, x_16);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_st_ref_get(x_3, x_20);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_st_ref_get(x_15, x_22);
lean_dec(x_15);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_st_ref_get(x_3, x_24);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_27 = lean_st_ref_get(x_9, x_26);
lean_dec(x_9);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_28; 
lean_dec(x_3);
lean_dec(x_2);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_27, 0);
lean_dec(x_29);
lean_ctor_set(x_27, 0, x_1);
return x_27;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_dec(x_27);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_1);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_1);
x_32 = lean_ctor_get(x_27, 1);
lean_inc(x_32);
lean_dec(x_27);
x_33 = lean_ctor_get(x_19, 0);
lean_inc(x_33);
lean_dec(x_19);
x_1 = x_33;
x_4 = x_32;
goto _start;
}
}
else
{
uint8_t x_35; 
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_18);
if (x_35 == 0)
{
return x_18;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_18, 0);
x_37 = lean_ctor_get(x_18, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_18);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
static lean_object* _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Simp___hyg_6456____closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_Simp_inlineApp_x3f___closed__4;
x_2 = l_Lean_Compiler_Decl_simp_x3f___lambda__2___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Simp___hyg_6456____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_Simp_inlineApp_x3f___closed__4;
x_2 = l_Lean_Compiler_Decl_simp_x3f___lambda__4___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Simp___hyg_6456____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_initFn____x40_Lean_Compiler_Simp___hyg_6456____closed__2;
x_2 = l_Lean_Compiler_Decl_simp_x3f___lambda__3___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_initFn____x40_Lean_Compiler_Simp___hyg_6456_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; 
x_2 = l_Lean_Compiler_Simp_inlineApp_x3f___closed__6;
x_3 = 0;
x_4 = l_Lean_registerTraceClass(x_2, x_3, x_1);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_6 = l_Lean_Compiler_initFn____x40_Lean_Compiler_Simp___hyg_6456____closed__1;
x_7 = l_Lean_registerTraceClass(x_6, x_3, x_5);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = l_Lean_Compiler_initFn____x40_Lean_Compiler_Simp___hyg_6456____closed__2;
x_10 = l_Lean_registerTraceClass(x_9, x_3, x_8);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = l_Lean_Compiler_initFn____x40_Lean_Compiler_Simp___hyg_6456____closed__3;
x_13 = l_Lean_registerTraceClass(x_12, x_3, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = l_Lean_Compiler_Decl_simp_x3f___closed__2;
x_16 = l_Lean_registerTraceClass(x_15, x_3, x_14);
return x_16;
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_13);
if (x_17 == 0)
{
return x_13;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_13, 0);
x_19 = lean_ctor_get(x_13, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_13);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_10);
if (x_21 == 0)
{
return x_10;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_10, 0);
x_23 = lean_ctor_get(x_10, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_10);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
else
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_7);
if (x_25 == 0)
{
return x_7;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_7, 0);
x_27 = lean_ctor_get(x_7, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_7);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
else
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_4);
if (x_29 == 0)
{
return x_4;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_4, 0);
x_31 = lean_ctor_get(x_4, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_4);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_CompilerM(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_Decl(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_Stage1(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_InlineAttrs(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_Simp(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_CompilerM(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_Decl(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_Stage1(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_InlineAttrs(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Compiler_Simp_Occ_noConfusion___rarg___closed__1 = _init_l_Lean_Compiler_Simp_Occ_noConfusion___rarg___closed__1();
lean_mark_persistent(l_Lean_Compiler_Simp_Occ_noConfusion___rarg___closed__1);
l___private_Lean_Compiler_Simp_0__Lean_Compiler_Simp_reprOcc____x40_Lean_Compiler_Simp___hyg_296____closed__1 = _init_l___private_Lean_Compiler_Simp_0__Lean_Compiler_Simp_reprOcc____x40_Lean_Compiler_Simp___hyg_296____closed__1();
lean_mark_persistent(l___private_Lean_Compiler_Simp_0__Lean_Compiler_Simp_reprOcc____x40_Lean_Compiler_Simp___hyg_296____closed__1);
l___private_Lean_Compiler_Simp_0__Lean_Compiler_Simp_reprOcc____x40_Lean_Compiler_Simp___hyg_296____closed__2 = _init_l___private_Lean_Compiler_Simp_0__Lean_Compiler_Simp_reprOcc____x40_Lean_Compiler_Simp___hyg_296____closed__2();
lean_mark_persistent(l___private_Lean_Compiler_Simp_0__Lean_Compiler_Simp_reprOcc____x40_Lean_Compiler_Simp___hyg_296____closed__2);
l___private_Lean_Compiler_Simp_0__Lean_Compiler_Simp_reprOcc____x40_Lean_Compiler_Simp___hyg_296____closed__3 = _init_l___private_Lean_Compiler_Simp_0__Lean_Compiler_Simp_reprOcc____x40_Lean_Compiler_Simp___hyg_296____closed__3();
lean_mark_persistent(l___private_Lean_Compiler_Simp_0__Lean_Compiler_Simp_reprOcc____x40_Lean_Compiler_Simp___hyg_296____closed__3);
l___private_Lean_Compiler_Simp_0__Lean_Compiler_Simp_reprOcc____x40_Lean_Compiler_Simp___hyg_296____closed__4 = _init_l___private_Lean_Compiler_Simp_0__Lean_Compiler_Simp_reprOcc____x40_Lean_Compiler_Simp___hyg_296____closed__4();
lean_mark_persistent(l___private_Lean_Compiler_Simp_0__Lean_Compiler_Simp_reprOcc____x40_Lean_Compiler_Simp___hyg_296____closed__4);
l___private_Lean_Compiler_Simp_0__Lean_Compiler_Simp_reprOcc____x40_Lean_Compiler_Simp___hyg_296____closed__5 = _init_l___private_Lean_Compiler_Simp_0__Lean_Compiler_Simp_reprOcc____x40_Lean_Compiler_Simp___hyg_296____closed__5();
lean_mark_persistent(l___private_Lean_Compiler_Simp_0__Lean_Compiler_Simp_reprOcc____x40_Lean_Compiler_Simp___hyg_296____closed__5);
l___private_Lean_Compiler_Simp_0__Lean_Compiler_Simp_reprOcc____x40_Lean_Compiler_Simp___hyg_296____closed__6 = _init_l___private_Lean_Compiler_Simp_0__Lean_Compiler_Simp_reprOcc____x40_Lean_Compiler_Simp___hyg_296____closed__6();
lean_mark_persistent(l___private_Lean_Compiler_Simp_0__Lean_Compiler_Simp_reprOcc____x40_Lean_Compiler_Simp___hyg_296____closed__6);
l___private_Lean_Compiler_Simp_0__Lean_Compiler_Simp_reprOcc____x40_Lean_Compiler_Simp___hyg_296____closed__7 = _init_l___private_Lean_Compiler_Simp_0__Lean_Compiler_Simp_reprOcc____x40_Lean_Compiler_Simp___hyg_296____closed__7();
lean_mark_persistent(l___private_Lean_Compiler_Simp_0__Lean_Compiler_Simp_reprOcc____x40_Lean_Compiler_Simp___hyg_296____closed__7);
l___private_Lean_Compiler_Simp_0__Lean_Compiler_Simp_reprOcc____x40_Lean_Compiler_Simp___hyg_296____closed__8 = _init_l___private_Lean_Compiler_Simp_0__Lean_Compiler_Simp_reprOcc____x40_Lean_Compiler_Simp___hyg_296____closed__8();
lean_mark_persistent(l___private_Lean_Compiler_Simp_0__Lean_Compiler_Simp_reprOcc____x40_Lean_Compiler_Simp___hyg_296____closed__8);
l___private_Lean_Compiler_Simp_0__Lean_Compiler_Simp_reprOcc____x40_Lean_Compiler_Simp___hyg_296____closed__9 = _init_l___private_Lean_Compiler_Simp_0__Lean_Compiler_Simp_reprOcc____x40_Lean_Compiler_Simp___hyg_296____closed__9();
lean_mark_persistent(l___private_Lean_Compiler_Simp_0__Lean_Compiler_Simp_reprOcc____x40_Lean_Compiler_Simp___hyg_296____closed__9);
l___private_Lean_Compiler_Simp_0__Lean_Compiler_Simp_reprOcc____x40_Lean_Compiler_Simp___hyg_296____closed__10 = _init_l___private_Lean_Compiler_Simp_0__Lean_Compiler_Simp_reprOcc____x40_Lean_Compiler_Simp___hyg_296____closed__10();
lean_mark_persistent(l___private_Lean_Compiler_Simp_0__Lean_Compiler_Simp_reprOcc____x40_Lean_Compiler_Simp___hyg_296____closed__10);
l___private_Lean_Compiler_Simp_0__Lean_Compiler_Simp_reprOcc____x40_Lean_Compiler_Simp___hyg_296____closed__11 = _init_l___private_Lean_Compiler_Simp_0__Lean_Compiler_Simp_reprOcc____x40_Lean_Compiler_Simp___hyg_296____closed__11();
lean_mark_persistent(l___private_Lean_Compiler_Simp_0__Lean_Compiler_Simp_reprOcc____x40_Lean_Compiler_Simp___hyg_296____closed__11);
l___private_Lean_Compiler_Simp_0__Lean_Compiler_Simp_reprOcc____x40_Lean_Compiler_Simp___hyg_296____closed__12 = _init_l___private_Lean_Compiler_Simp_0__Lean_Compiler_Simp_reprOcc____x40_Lean_Compiler_Simp___hyg_296____closed__12();
lean_mark_persistent(l___private_Lean_Compiler_Simp_0__Lean_Compiler_Simp_reprOcc____x40_Lean_Compiler_Simp___hyg_296____closed__12);
l___private_Lean_Compiler_Simp_0__Lean_Compiler_Simp_reprOcc____x40_Lean_Compiler_Simp___hyg_296____closed__13 = _init_l___private_Lean_Compiler_Simp_0__Lean_Compiler_Simp_reprOcc____x40_Lean_Compiler_Simp___hyg_296____closed__13();
lean_mark_persistent(l___private_Lean_Compiler_Simp_0__Lean_Compiler_Simp_reprOcc____x40_Lean_Compiler_Simp___hyg_296____closed__13);
l___private_Lean_Compiler_Simp_0__Lean_Compiler_Simp_reprOcc____x40_Lean_Compiler_Simp___hyg_296____closed__14 = _init_l___private_Lean_Compiler_Simp_0__Lean_Compiler_Simp_reprOcc____x40_Lean_Compiler_Simp___hyg_296____closed__14();
lean_mark_persistent(l___private_Lean_Compiler_Simp_0__Lean_Compiler_Simp_reprOcc____x40_Lean_Compiler_Simp___hyg_296____closed__14);
l_Lean_Compiler_Simp_instReprOcc___closed__1 = _init_l_Lean_Compiler_Simp_instReprOcc___closed__1();
lean_mark_persistent(l_Lean_Compiler_Simp_instReprOcc___closed__1);
l_Lean_Compiler_Simp_instReprOcc = _init_l_Lean_Compiler_Simp_instReprOcc();
lean_mark_persistent(l_Lean_Compiler_Simp_instReprOcc);
l_Lean_Compiler_Simp_instInhabitedOcc = _init_l_Lean_Compiler_Simp_instInhabitedOcc();
l_Lean_Compiler_Simp_OccInfo_map___default = _init_l_Lean_Compiler_Simp_OccInfo_map___default();
lean_mark_persistent(l_Lean_Compiler_Simp_OccInfo_map___default);
l_Lean_Compiler_Simp_instInhabitedOccInfo___closed__1 = _init_l_Lean_Compiler_Simp_instInhabitedOccInfo___closed__1();
lean_mark_persistent(l_Lean_Compiler_Simp_instInhabitedOccInfo___closed__1);
l_Lean_Compiler_Simp_instInhabitedOccInfo = _init_l_Lean_Compiler_Simp_instInhabitedOccInfo();
lean_mark_persistent(l_Lean_Compiler_Simp_instInhabitedOccInfo);
l_List_forIn_loop___at_Lean_Compiler_Simp_OccInfo_format___spec__4___closed__1 = _init_l_List_forIn_loop___at_Lean_Compiler_Simp_OccInfo_format___spec__4___closed__1();
lean_mark_persistent(l_List_forIn_loop___at_Lean_Compiler_Simp_OccInfo_format___spec__4___closed__1);
l_List_forIn_loop___at_Lean_Compiler_Simp_OccInfo_format___spec__4___closed__2 = _init_l_List_forIn_loop___at_Lean_Compiler_Simp_OccInfo_format___spec__4___closed__2();
lean_mark_persistent(l_List_forIn_loop___at_Lean_Compiler_Simp_OccInfo_format___spec__4___closed__2);
l_List_forIn_loop___at_Lean_Compiler_Simp_OccInfo_format___spec__4___closed__3 = _init_l_List_forIn_loop___at_Lean_Compiler_Simp_OccInfo_format___spec__4___closed__3();
lean_mark_persistent(l_List_forIn_loop___at_Lean_Compiler_Simp_OccInfo_format___spec__4___closed__3);
l_List_forIn_loop___at_Lean_Compiler_Simp_OccInfo_format___spec__4___closed__4 = _init_l_List_forIn_loop___at_Lean_Compiler_Simp_OccInfo_format___spec__4___closed__4();
lean_mark_persistent(l_List_forIn_loop___at_Lean_Compiler_Simp_OccInfo_format___spec__4___closed__4);
l_List_forIn_loop___at_Lean_Compiler_Simp_OccInfo_format___spec__4___closed__5 = _init_l_List_forIn_loop___at_Lean_Compiler_Simp_OccInfo_format___spec__4___closed__5();
lean_mark_persistent(l_List_forIn_loop___at_Lean_Compiler_Simp_OccInfo_format___spec__4___closed__5);
l_List_forIn_loop___at_Lean_Compiler_Simp_OccInfo_format___spec__4___closed__6 = _init_l_List_forIn_loop___at_Lean_Compiler_Simp_OccInfo_format___spec__4___closed__6();
lean_mark_persistent(l_List_forIn_loop___at_Lean_Compiler_Simp_OccInfo_format___spec__4___closed__6);
l_Lean_Compiler_Simp_instToFormatOccInfo___closed__1 = _init_l_Lean_Compiler_Simp_instToFormatOccInfo___closed__1();
lean_mark_persistent(l_Lean_Compiler_Simp_instToFormatOccInfo___closed__1);
l_Lean_Compiler_Simp_instToFormatOccInfo = _init_l_Lean_Compiler_Simp_instToFormatOccInfo();
lean_mark_persistent(l_Lean_Compiler_Simp_instToFormatOccInfo);
l_Lean_Compiler_Simp_Config_smallThreshold___default = _init_l_Lean_Compiler_Simp_Config_smallThreshold___default();
lean_mark_persistent(l_Lean_Compiler_Simp_Config_smallThreshold___default);
l_Lean_Compiler_Simp_Context_config___default = _init_l_Lean_Compiler_Simp_Context_config___default();
lean_mark_persistent(l_Lean_Compiler_Simp_Context_config___default);
l_Lean_Compiler_Simp_State_occInfo___default = _init_l_Lean_Compiler_Simp_State_occInfo___default();
lean_mark_persistent(l_Lean_Compiler_Simp_State_occInfo___default);
l_Lean_Compiler_Simp_State_simplified___default = _init_l_Lean_Compiler_Simp_State_simplified___default();
l_Lean_Compiler_Simp_instInhabitedState___closed__1 = _init_l_Lean_Compiler_Simp_instInhabitedState___closed__1();
lean_mark_persistent(l_Lean_Compiler_Simp_instInhabitedState___closed__1);
l_Lean_Compiler_Simp_instInhabitedState = _init_l_Lean_Compiler_Simp_instInhabitedState();
lean_mark_persistent(l_Lean_Compiler_Simp_instInhabitedState);
l_Lean_Compiler_Simp_internalize_visitLambda___closed__1 = _init_l_Lean_Compiler_Simp_internalize_visitLambda___closed__1();
lean_mark_persistent(l_Lean_Compiler_Simp_internalize_visitLambda___closed__1);
l_Lean_Compiler_Simp_internalize_visitCases___closed__1 = _init_l_Lean_Compiler_Simp_internalize_visitCases___closed__1();
lean_mark_persistent(l_Lean_Compiler_Simp_internalize_visitCases___closed__1);
l_Lean_Compiler_Simp_simpProj_x3f___closed__1 = _init_l_Lean_Compiler_Simp_simpProj_x3f___closed__1();
lean_mark_persistent(l_Lean_Compiler_Simp_simpProj_x3f___closed__1);
l_Lean_Compiler_Simp_simpProj_x3f___closed__2 = _init_l_Lean_Compiler_Simp_simpProj_x3f___closed__2();
lean_mark_persistent(l_Lean_Compiler_Simp_simpProj_x3f___closed__2);
l_Lean_Compiler_Simp_simpProj_x3f___closed__3 = _init_l_Lean_Compiler_Simp_simpProj_x3f___closed__3();
lean_mark_persistent(l_Lean_Compiler_Simp_simpProj_x3f___closed__3);
l_Lean_Compiler_Simp_simpProj_x3f___closed__4 = _init_l_Lean_Compiler_Simp_simpProj_x3f___closed__4();
lean_mark_persistent(l_Lean_Compiler_Simp_simpProj_x3f___closed__4);
l_Lean_Compiler_Simp_simpAppApp_x3f___closed__1 = _init_l_Lean_Compiler_Simp_simpAppApp_x3f___closed__1();
lean_mark_persistent(l_Lean_Compiler_Simp_simpAppApp_x3f___closed__1);
l_panic___at_Lean_Compiler_Simp_inlineProjInst_x3f_visitProj___spec__1___closed__1 = _init_l_panic___at_Lean_Compiler_Simp_inlineProjInst_x3f_visitProj___spec__1___closed__1();
lean_mark_persistent(l_panic___at_Lean_Compiler_Simp_inlineProjInst_x3f_visitProj___spec__1___closed__1);
l_panic___at_Lean_Compiler_Simp_inlineProjInst_x3f_visitProj___spec__1___closed__2 = _init_l_panic___at_Lean_Compiler_Simp_inlineProjInst_x3f_visitProj___spec__1___closed__2();
lean_mark_persistent(l_panic___at_Lean_Compiler_Simp_inlineProjInst_x3f_visitProj___spec__1___closed__2);
l_panic___at_Lean_Compiler_Simp_inlineProjInst_x3f_visitProj___spec__1___closed__3 = _init_l_panic___at_Lean_Compiler_Simp_inlineProjInst_x3f_visitProj___spec__1___closed__3();
lean_mark_persistent(l_panic___at_Lean_Compiler_Simp_inlineProjInst_x3f_visitProj___spec__1___closed__3);
l_panic___at_Lean_Compiler_Simp_inlineProjInst_x3f_visitProj___spec__1___closed__4 = _init_l_panic___at_Lean_Compiler_Simp_inlineProjInst_x3f_visitProj___spec__1___closed__4();
lean_mark_persistent(l_panic___at_Lean_Compiler_Simp_inlineProjInst_x3f_visitProj___spec__1___closed__4);
l_panic___at_Lean_Compiler_Simp_inlineProjInst_x3f_visitProj___spec__1___closed__5 = _init_l_panic___at_Lean_Compiler_Simp_inlineProjInst_x3f_visitProj___spec__1___closed__5();
lean_mark_persistent(l_panic___at_Lean_Compiler_Simp_inlineProjInst_x3f_visitProj___spec__1___closed__5);
l_Lean_Compiler_Simp_inlineProjInst_x3f_visitProj___closed__1 = _init_l_Lean_Compiler_Simp_inlineProjInst_x3f_visitProj___closed__1();
lean_mark_persistent(l_Lean_Compiler_Simp_inlineProjInst_x3f_visitProj___closed__1);
l_Lean_Compiler_Simp_inlineProjInst_x3f_visitProj___closed__2 = _init_l_Lean_Compiler_Simp_inlineProjInst_x3f_visitProj___closed__2();
lean_mark_persistent(l_Lean_Compiler_Simp_inlineProjInst_x3f_visitProj___closed__2);
l_Lean_Compiler_Simp_inlineProjInst_x3f_visitProj___closed__3 = _init_l_Lean_Compiler_Simp_inlineProjInst_x3f_visitProj___closed__3();
lean_mark_persistent(l_Lean_Compiler_Simp_inlineProjInst_x3f_visitProj___closed__3);
l_Lean_Compiler_Simp_inlineProjInst_x3f_visitProj___closed__4 = _init_l_Lean_Compiler_Simp_inlineProjInst_x3f_visitProj___closed__4();
lean_mark_persistent(l_Lean_Compiler_Simp_inlineProjInst_x3f_visitProj___closed__4);
l_Lean_throwError___at_Lean_Compiler_Simp_visitLambda___spec__3___closed__1 = _init_l_Lean_throwError___at_Lean_Compiler_Simp_visitLambda___spec__3___closed__1();
lean_mark_persistent(l_Lean_throwError___at_Lean_Compiler_Simp_visitLambda___spec__3___closed__1);
l_Lean_throwError___at_Lean_Compiler_Simp_visitLambda___spec__3___closed__2 = _init_l_Lean_throwError___at_Lean_Compiler_Simp_visitLambda___spec__3___closed__2();
lean_mark_persistent(l_Lean_throwError___at_Lean_Compiler_Simp_visitLambda___spec__3___closed__2);
l_Lean_throwError___at_Lean_Compiler_Simp_visitLambda___spec__3___closed__3 = _init_l_Lean_throwError___at_Lean_Compiler_Simp_visitLambda___spec__3___closed__3();
lean_mark_persistent(l_Lean_throwError___at_Lean_Compiler_Simp_visitLambda___spec__3___closed__3);
l_Lean_throwError___at_Lean_Compiler_Simp_visitLambda___spec__3___closed__4 = _init_l_Lean_throwError___at_Lean_Compiler_Simp_visitLambda___spec__3___closed__4();
lean_mark_persistent(l_Lean_throwError___at_Lean_Compiler_Simp_visitLambda___spec__3___closed__4);
l_Lean_throwError___at_Lean_Compiler_Simp_visitLambda___spec__3___closed__5 = _init_l_Lean_throwError___at_Lean_Compiler_Simp_visitLambda___spec__3___closed__5();
lean_mark_persistent(l_Lean_throwError___at_Lean_Compiler_Simp_visitLambda___spec__3___closed__5);
l_Lean_throwError___at_Lean_Compiler_Simp_visitLambda___spec__3___closed__6 = _init_l_Lean_throwError___at_Lean_Compiler_Simp_visitLambda___spec__3___closed__6();
lean_mark_persistent(l_Lean_throwError___at_Lean_Compiler_Simp_visitLambda___spec__3___closed__6);
l_Lean_Compiler_getLevel___at_Lean_Compiler_Simp_visitLambda___spec__2___closed__1 = _init_l_Lean_Compiler_getLevel___at_Lean_Compiler_Simp_visitLambda___spec__2___closed__1();
lean_mark_persistent(l_Lean_Compiler_getLevel___at_Lean_Compiler_Simp_visitLambda___spec__2___closed__1);
l_Lean_Compiler_getLevel___at_Lean_Compiler_Simp_visitLambda___spec__2___closed__2 = _init_l_Lean_Compiler_getLevel___at_Lean_Compiler_Simp_visitLambda___spec__2___closed__2();
lean_mark_persistent(l_Lean_Compiler_getLevel___at_Lean_Compiler_Simp_visitLambda___spec__2___closed__2);
l_Lean_Compiler_getLevel___at_Lean_Compiler_Simp_visitLambda___spec__2___closed__3 = _init_l_Lean_Compiler_getLevel___at_Lean_Compiler_Simp_visitLambda___spec__2___closed__3();
lean_mark_persistent(l_Lean_Compiler_getLevel___at_Lean_Compiler_Simp_visitLambda___spec__2___closed__3);
l_Lean_Compiler_mkLcUnreachable___at_Lean_Compiler_Simp_visitLambda___spec__1___closed__1 = _init_l_Lean_Compiler_mkLcUnreachable___at_Lean_Compiler_Simp_visitLambda___spec__1___closed__1();
lean_mark_persistent(l_Lean_Compiler_mkLcUnreachable___at_Lean_Compiler_Simp_visitLambda___spec__1___closed__1);
l_Lean_Compiler_mkLcUnreachable___at_Lean_Compiler_Simp_visitLambda___spec__1___closed__2 = _init_l_Lean_Compiler_mkLcUnreachable___at_Lean_Compiler_Simp_visitLambda___spec__1___closed__2();
lean_mark_persistent(l_Lean_Compiler_mkLcUnreachable___at_Lean_Compiler_Simp_visitLambda___spec__1___closed__2);
l_Lean_Compiler_Simp_visitLambda___closed__1 = _init_l_Lean_Compiler_Simp_visitLambda___closed__1();
lean_mark_persistent(l_Lean_Compiler_Simp_visitLambda___closed__1);
l_panic___at_Lean_Compiler_Simp_visitCases___spec__2___closed__1 = _init_l_panic___at_Lean_Compiler_Simp_visitCases___spec__2___closed__1();
lean_mark_persistent(l_panic___at_Lean_Compiler_Simp_visitCases___spec__2___closed__1);
l_panic___at_Lean_Compiler_Simp_visitCases___spec__2___closed__2 = _init_l_panic___at_Lean_Compiler_Simp_visitCases___spec__2___closed__2();
lean_mark_persistent(l_panic___at_Lean_Compiler_Simp_visitCases___spec__2___closed__2);
l_Lean_Compiler_Simp_visitCases___closed__1 = _init_l_Lean_Compiler_Simp_visitCases___closed__1();
lean_mark_persistent(l_Lean_Compiler_Simp_visitCases___closed__1);
l_Lean_Compiler_Simp_visitCases___closed__2 = _init_l_Lean_Compiler_Simp_visitCases___closed__2();
lean_mark_persistent(l_Lean_Compiler_Simp_visitCases___closed__2);
l_Lean_Compiler_Simp_visitCases___closed__3 = _init_l_Lean_Compiler_Simp_visitCases___closed__3();
lean_mark_persistent(l_Lean_Compiler_Simp_visitCases___closed__3);
l_Lean_Compiler_Simp_visitCases___closed__4 = _init_l_Lean_Compiler_Simp_visitCases___closed__4();
lean_mark_persistent(l_Lean_Compiler_Simp_visitCases___closed__4);
l_Lean_Compiler_Simp_visitCases___closed__5 = _init_l_Lean_Compiler_Simp_visitCases___closed__5();
lean_mark_persistent(l_Lean_Compiler_Simp_visitCases___closed__5);
l_Lean_isTracingEnabledFor___at_Lean_Compiler_Simp_inlineApp_x3f___spec__1___closed__1 = _init_l_Lean_isTracingEnabledFor___at_Lean_Compiler_Simp_inlineApp_x3f___spec__1___closed__1();
lean_mark_persistent(l_Lean_isTracingEnabledFor___at_Lean_Compiler_Simp_inlineApp_x3f___spec__1___closed__1);
l_Lean_Compiler_Simp_inlineApp_x3f___lambda__1___closed__1 = _init_l_Lean_Compiler_Simp_inlineApp_x3f___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Compiler_Simp_inlineApp_x3f___lambda__1___closed__1);
l_Lean_Compiler_Simp_inlineApp_x3f___lambda__3___closed__1 = _init_l_Lean_Compiler_Simp_inlineApp_x3f___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Compiler_Simp_inlineApp_x3f___lambda__3___closed__1);
l_Lean_Compiler_Simp_inlineApp_x3f___lambda__3___closed__2 = _init_l_Lean_Compiler_Simp_inlineApp_x3f___lambda__3___closed__2();
lean_mark_persistent(l_Lean_Compiler_Simp_inlineApp_x3f___lambda__3___closed__2);
l_Lean_Compiler_Simp_inlineApp_x3f___lambda__4___closed__1 = _init_l_Lean_Compiler_Simp_inlineApp_x3f___lambda__4___closed__1();
lean_mark_persistent(l_Lean_Compiler_Simp_inlineApp_x3f___lambda__4___closed__1);
l_Lean_Compiler_Simp_inlineApp_x3f___lambda__4___closed__2 = _init_l_Lean_Compiler_Simp_inlineApp_x3f___lambda__4___closed__2();
lean_mark_persistent(l_Lean_Compiler_Simp_inlineApp_x3f___lambda__4___closed__2);
l_Lean_Compiler_Simp_inlineApp_x3f___lambda__4___closed__3 = _init_l_Lean_Compiler_Simp_inlineApp_x3f___lambda__4___closed__3();
lean_mark_persistent(l_Lean_Compiler_Simp_inlineApp_x3f___lambda__4___closed__3);
l_Lean_Compiler_Simp_inlineApp_x3f___lambda__4___closed__4 = _init_l_Lean_Compiler_Simp_inlineApp_x3f___lambda__4___closed__4();
lean_mark_persistent(l_Lean_Compiler_Simp_inlineApp_x3f___lambda__4___closed__4);
l_Lean_Compiler_Simp_inlineApp_x3f___lambda__4___closed__5 = _init_l_Lean_Compiler_Simp_inlineApp_x3f___lambda__4___closed__5();
lean_mark_persistent(l_Lean_Compiler_Simp_inlineApp_x3f___lambda__4___closed__5);
l_Lean_Compiler_Simp_inlineApp_x3f___lambda__4___closed__6 = _init_l_Lean_Compiler_Simp_inlineApp_x3f___lambda__4___closed__6();
lean_mark_persistent(l_Lean_Compiler_Simp_inlineApp_x3f___lambda__4___closed__6);
l_Lean_Compiler_Simp_inlineApp_x3f___lambda__4___closed__7 = _init_l_Lean_Compiler_Simp_inlineApp_x3f___lambda__4___closed__7();
lean_mark_persistent(l_Lean_Compiler_Simp_inlineApp_x3f___lambda__4___closed__7);
l_Lean_Compiler_Simp_inlineApp_x3f___closed__1 = _init_l_Lean_Compiler_Simp_inlineApp_x3f___closed__1();
lean_mark_persistent(l_Lean_Compiler_Simp_inlineApp_x3f___closed__1);
l_Lean_Compiler_Simp_inlineApp_x3f___closed__2 = _init_l_Lean_Compiler_Simp_inlineApp_x3f___closed__2();
lean_mark_persistent(l_Lean_Compiler_Simp_inlineApp_x3f___closed__2);
l_Lean_Compiler_Simp_inlineApp_x3f___closed__3 = _init_l_Lean_Compiler_Simp_inlineApp_x3f___closed__3();
lean_mark_persistent(l_Lean_Compiler_Simp_inlineApp_x3f___closed__3);
l_Lean_Compiler_Simp_inlineApp_x3f___closed__4 = _init_l_Lean_Compiler_Simp_inlineApp_x3f___closed__4();
lean_mark_persistent(l_Lean_Compiler_Simp_inlineApp_x3f___closed__4);
l_Lean_Compiler_Simp_inlineApp_x3f___closed__5 = _init_l_Lean_Compiler_Simp_inlineApp_x3f___closed__5();
lean_mark_persistent(l_Lean_Compiler_Simp_inlineApp_x3f___closed__5);
l_Lean_Compiler_Simp_inlineApp_x3f___closed__6 = _init_l_Lean_Compiler_Simp_inlineApp_x3f___closed__6();
lean_mark_persistent(l_Lean_Compiler_Simp_inlineApp_x3f___closed__6);
l_Lean_Compiler_Simp_inlineApp_x3f___closed__7 = _init_l_Lean_Compiler_Simp_inlineApp_x3f___closed__7();
lean_mark_persistent(l_Lean_Compiler_Simp_inlineApp_x3f___closed__7);
l_Lean_Compiler_Simp_inlineApp_x3f___closed__8 = _init_l_Lean_Compiler_Simp_inlineApp_x3f___closed__8();
lean_mark_persistent(l_Lean_Compiler_Simp_inlineApp_x3f___closed__8);
l_Lean_Compiler_Decl_simp_x3f___lambda__2___closed__1 = _init_l_Lean_Compiler_Decl_simp_x3f___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Compiler_Decl_simp_x3f___lambda__2___closed__1);
l_Lean_Compiler_Decl_simp_x3f___lambda__2___closed__2 = _init_l_Lean_Compiler_Decl_simp_x3f___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Compiler_Decl_simp_x3f___lambda__2___closed__2);
l_Lean_Compiler_Decl_simp_x3f___lambda__2___closed__3 = _init_l_Lean_Compiler_Decl_simp_x3f___lambda__2___closed__3();
lean_mark_persistent(l_Lean_Compiler_Decl_simp_x3f___lambda__2___closed__3);
l_Lean_Compiler_Decl_simp_x3f___lambda__3___closed__1 = _init_l_Lean_Compiler_Decl_simp_x3f___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Compiler_Decl_simp_x3f___lambda__3___closed__1);
l_Lean_Compiler_Decl_simp_x3f___lambda__3___closed__2 = _init_l_Lean_Compiler_Decl_simp_x3f___lambda__3___closed__2();
lean_mark_persistent(l_Lean_Compiler_Decl_simp_x3f___lambda__3___closed__2);
l_Lean_Compiler_Decl_simp_x3f___lambda__3___closed__3 = _init_l_Lean_Compiler_Decl_simp_x3f___lambda__3___closed__3();
lean_mark_persistent(l_Lean_Compiler_Decl_simp_x3f___lambda__3___closed__3);
l_Lean_Compiler_Decl_simp_x3f___lambda__4___closed__1 = _init_l_Lean_Compiler_Decl_simp_x3f___lambda__4___closed__1();
lean_mark_persistent(l_Lean_Compiler_Decl_simp_x3f___lambda__4___closed__1);
l_Lean_Compiler_Decl_simp_x3f___closed__1 = _init_l_Lean_Compiler_Decl_simp_x3f___closed__1();
lean_mark_persistent(l_Lean_Compiler_Decl_simp_x3f___closed__1);
l_Lean_Compiler_Decl_simp_x3f___closed__2 = _init_l_Lean_Compiler_Decl_simp_x3f___closed__2();
lean_mark_persistent(l_Lean_Compiler_Decl_simp_x3f___closed__2);
l_Lean_Compiler_Decl_simp_x3f___closed__3 = _init_l_Lean_Compiler_Decl_simp_x3f___closed__3();
lean_mark_persistent(l_Lean_Compiler_Decl_simp_x3f___closed__3);
l_Lean_Compiler_Decl_simp_x3f___closed__4 = _init_l_Lean_Compiler_Decl_simp_x3f___closed__4();
lean_mark_persistent(l_Lean_Compiler_Decl_simp_x3f___closed__4);
l_Lean_Compiler_Decl_simp___closed__1 = _init_l_Lean_Compiler_Decl_simp___closed__1();
lean_mark_persistent(l_Lean_Compiler_Decl_simp___closed__1);
l_Lean_Compiler_Decl_simp___closed__2 = _init_l_Lean_Compiler_Decl_simp___closed__2();
lean_mark_persistent(l_Lean_Compiler_Decl_simp___closed__2);
l_Lean_Compiler_Decl_simp___closed__3 = _init_l_Lean_Compiler_Decl_simp___closed__3();
lean_mark_persistent(l_Lean_Compiler_Decl_simp___closed__3);
l_Lean_Compiler_Decl_simp___closed__4 = _init_l_Lean_Compiler_Decl_simp___closed__4();
lean_mark_persistent(l_Lean_Compiler_Decl_simp___closed__4);
l_Lean_Compiler_Decl_simp___closed__5 = _init_l_Lean_Compiler_Decl_simp___closed__5();
lean_mark_persistent(l_Lean_Compiler_Decl_simp___closed__5);
l_Lean_Compiler_Decl_simp___closed__6 = _init_l_Lean_Compiler_Decl_simp___closed__6();
lean_mark_persistent(l_Lean_Compiler_Decl_simp___closed__6);
l_Lean_Compiler_initFn____x40_Lean_Compiler_Simp___hyg_6456____closed__1 = _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Simp___hyg_6456____closed__1();
lean_mark_persistent(l_Lean_Compiler_initFn____x40_Lean_Compiler_Simp___hyg_6456____closed__1);
l_Lean_Compiler_initFn____x40_Lean_Compiler_Simp___hyg_6456____closed__2 = _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Simp___hyg_6456____closed__2();
lean_mark_persistent(l_Lean_Compiler_initFn____x40_Lean_Compiler_Simp___hyg_6456____closed__2);
l_Lean_Compiler_initFn____x40_Lean_Compiler_Simp___hyg_6456____closed__3 = _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Simp___hyg_6456____closed__3();
lean_mark_persistent(l_Lean_Compiler_initFn____x40_Lean_Compiler_Simp___hyg_6456____closed__3);
res = l_Lean_Compiler_initFn____x40_Lean_Compiler_Simp___hyg_6456_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
