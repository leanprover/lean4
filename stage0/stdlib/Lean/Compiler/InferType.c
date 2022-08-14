// Lean compiler output
// Module: Lean.Compiler.InferType
// Imports: Init Lean.Compiler.LCNFTypes Lean.Compiler.Util
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
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_InferType_inferForallType_go___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
static lean_object* l_Lean_Compiler_InferType_instAddMessageContextInferTypeM___closed__4;
LEAN_EXPORT lean_object* l_Lean_Compiler_InferType_withLocalDecl___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_InferType_inferProjType___spec__4___closed__4;
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_InferType_inferType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_InferType_inferFVarType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_InferType_inferForallType_go___spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at_Lean_Compiler_InferType_inferProjType___spec__3___closed__2;
lean_object* lean_array_uget(lean_object*, size_t);
static lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_InferType_inferAppType___spec__2___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_InferType_inferAppType___spec__2___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_InferType_inferProjType___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_succ___override(lean_object*);
static lean_object* l_Lean_Compiler_InferType_getCasesResultingType_go___closed__4;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_InferType_inferForallType_go___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_InferType_inferProjType___spec__4___closed__3;
static lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_InferType_inferAppType___spec__2___lambda__1___closed__1;
lean_object* lean_environment_find(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_read___at_Lean_Compiler_InferType_instMonadLCtxInferTypeM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at_Lean_Compiler_InferType_inferProjType___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_InferType_inferType___closed__2;
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_InferType_inferProjType___spec__4___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_mkLcCast___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_InferType_inferType___closed__1;
static lean_object* l_Lean_Compiler_InferType_getCasesResultingType_go___closed__1;
lean_object* l_Lean_FVarId_throwUnknown___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_InferType_inferForallType_go___spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_InferType_getCasesResultingType_go___closed__2;
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_InferType_inferForallType_go___spec__5(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_mkLcUnreachable___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_mkLcCast___rarg___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instInhabitedCoreM___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at_Lean_Compiler_InferType_withLocalDecl___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_getLevel___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getRevArg_x21(lean_object*, lean_object*);
static lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_InferType_inferProjType___spec__4___closed__1;
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_InferType_inferProjType___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
static lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_InferType_inferProjType___spec__4___closed__2;
extern lean_object* l_Lean_levelZero;
static lean_object* l_Lean_getConstInfo___at_Lean_Compiler_InferType_inferProjType___spec__1___closed__4;
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_InferType_inferForallType_go___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_InferType_inferForallType_go___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_instMonadInferTypeInferTypeM;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_InferType_getCasesResultingType_go___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_getLevel(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_mkLcUnreachable___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_InferType_inferConstType___closed__2;
static lean_object* l_Lean_Compiler_InferType_inferConstType___closed__1;
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at_Lean_Compiler_InferType_withLocalDecl___spec__2___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_InferType_instMonadLCtxInferTypeM___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Literal_type(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_InferType_inferAppType___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_InferType_withLocalDecl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_InferType_inferForallType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate_rev_range(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Level_imax___override(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_InferType_inferProjType___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_InferType_inferType___closed__4;
static lean_object* l_Lean_Compiler_InferType_instAddMessageContextInferTypeM___closed__5;
lean_object* l_Lean_Expr_headBeta(lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_InferType_inferAppType___spec__2___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_InferType_inferForallType_go___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_InferType_instAddMessageContextInferTypeM___closed__3;
static lean_object* l_Lean_getConstInfo___at_Lean_Compiler_InferType_inferProjType___spec__1___closed__2;
lean_object* l_Lean_Compiler_instantiateLCNFTypeLevelParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_InferType_inferProjType___spec__4___closed__5;
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_mkLcCast___rarg___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_InferType_inferAppType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at_Lean_Compiler_InferType_withLocalDecl___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_InferType_inferAppType___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_InferType_getCasesResultingType_go___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_InferType_getLevel_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_InferType_getCasesResultingType_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_InferType_getCasesResultingType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_InferType_inferConstType___closed__4;
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_InferType_inferAppType___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_InferType_inferProjType___spec__4___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_InferType_inferForallType_go___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at_Lean_Compiler_InferType_inferProjType___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
static lean_object* l_Lean_getConstInfo___at_Lean_Compiler_InferType_inferProjType___spec__1___closed__1;
static lean_object* l_Lean_Compiler_mkLcCast___rarg___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_InferType_inferProjType___spec__4___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_InferType_inferProjType___spec__4___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_InferType_inferForallType_go___spec__7(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_InferType_instMonadLCtxInferTypeM___closed__1;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_InferType_inferForallType_go___spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_InferType_instMonadLCtxInferTypeM;
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_CasesInfo_geNumDiscrs(lean_object*);
size_t lean_usize_of_nat(lean_object*);
static lean_object* l_Lean_Compiler_InferType_instMonadLCtxInferTypeM___closed__2;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_InferType_inferForallType_go___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_InferType_inferForallType_go___spec__1___closed__1;
static lean_object* l_Lean_Compiler_InferType_inferLambdaType___closed__1;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_InferType_inferForallType_go___spec__8(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_InferType_inferForallType_go___spec__9(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_InferType_inferProjType___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_local_ctx_mk_local_decl(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
static lean_object* l_Lean_Compiler_InferType_getCasesResultingType_go___closed__3;
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Compiler_InferType_instMonadLCtxInferTypeM___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_mkLcUnreachable(lean_object*);
static lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_InferType_inferProjType___spec__4___closed__6;
lean_object* l_Lean_Expr_fvar___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_InferType_inferProjType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_InferType_inferForallType_go___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_read___at_Lean_Compiler_InferType_instMonadLCtxInferTypeM___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_mkLcCast___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_InferType_inferForallType_go___spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_getConstInfo___at_Lean_Compiler_InferType_inferProjType___spec__1___closed__3;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_mkLcUnreachable___rarg___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_InferType_inferProjType___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_mkLcUnreachable___rarg___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_InferType_inferForallType_go___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedReaderT___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_Compiler_InferType_inferProjType___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_InferType_inferConstType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_getLevel___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Compiler_InferType_instMonadLCtxInferTypeM___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_normalize(lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_InferType_inferForallType_go___spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_InferType_inferAppType___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_InferType_inferProjType___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_InferType_inferLambdaType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAnyType(lean_object*);
lean_object* l_Lean_throwError___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_InferType_inferForallType_go___spec__11(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_InferType_instMonadLCtxInferTypeM___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at_Lean_Compiler_InferType_withLocalDecl___spec__2___rarg(lean_object*, lean_object*);
lean_object* lean_expr_instantiate_rev(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at_Lean_Compiler_InferType_withLocalDecl___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_InferType_getCasesResultingType_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
static lean_object* l_Lean_Compiler_InferType_getLevel_x3f___closed__2;
static lean_object* l_Lean_Compiler_InferType_instAddMessageContextInferTypeM___closed__6;
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_InferType_inferForallType_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_InferType_inferAppType___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_instMonadInferTypeInferTypeM___closed__1;
static lean_object* l_Lean_Compiler_InferType_inferConstType___closed__3;
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_InferType_inferForallType_go___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_InferType_inferAppType___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_instMonadInferType___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at_Lean_Compiler_InferType_withLocalDecl___spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_InferType_inferForallType_go___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_instMonadInferType(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_isCasesApp_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_local_ctx_find(lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_mkForall(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_InferType_withLocalDecl___rarg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_levelOne;
static lean_object* l_Lean_Compiler_InferType_instAddMessageContextInferTypeM___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_InferType_inferLambdaType_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_mkLcCast___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_InferType_inferProjType___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
static lean_object* l_panic___at_Lean_Compiler_InferType_inferProjType___spec__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_InferType_inferFVarType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_InferType_getLevel_x3f___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_InferType_getCasesResultingType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Compiler_anyTypeExpr;
LEAN_EXPORT lean_object* l_Lean_Compiler_mkLcCast(lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_InferType_inferForallType_go___spec__6(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_InferType_getLevel_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_InferType_getLevel_x3f___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_InferType_instAddMessageContextInferTypeM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_InferType_inferForallType_go___spec__10(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_InferType_inferType___closed__3;
LEAN_EXPORT lean_object* l_Lean_Compiler_InferType_inferAppType___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_InferType_instAddMessageContextInferTypeM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_InferType_instAddMessageContextInferTypeM___closed__1;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_InferType_inferForallType_go___spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_read___at_Lean_Compiler_InferType_instMonadLCtxInferTypeM___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Compiler_InferType_instMonadLCtxInferTypeM___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_7 = lean_apply_4(x_1, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_apply_5(x_2, x_8, x_3, x_4, x_5, x_9);
return x_10;
}
else
{
uint8_t x_11; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_11 = !lean_is_exclusive(x_7);
if (x_11 == 0)
{
return x_7;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_7, 0);
x_13 = lean_ctor_get(x_7, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_7);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Compiler_InferType_instMonadLCtxInferTypeM___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Compiler_InferType_instMonadLCtxInferTypeM___spec__2___rarg), 6, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_InferType_instMonadLCtxInferTypeM___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Compiler_InferType_instMonadLCtxInferTypeM___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_ReaderT_read___at_Lean_Compiler_InferType_instMonadLCtxInferTypeM___spec__1___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_InferType_instMonadLCtxInferTypeM___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_InferType_instMonadLCtxInferTypeM___lambda__1___boxed), 5, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_InferType_instMonadLCtxInferTypeM() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_InferType_instMonadLCtxInferTypeM___closed__1;
x_2 = l_Lean_Compiler_InferType_instMonadLCtxInferTypeM___closed__2;
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Compiler_InferType_instMonadLCtxInferTypeM___spec__2___rarg), 6, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_ReaderT_read___at_Lean_Compiler_InferType_instMonadLCtxInferTypeM___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_ReaderT_read___at_Lean_Compiler_InferType_instMonadLCtxInferTypeM___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_InferType_instMonadLCtxInferTypeM___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Compiler_InferType_instMonadLCtxInferTypeM___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
static lean_object* _init_l_Lean_Compiler_InferType_instAddMessageContextInferTypeM___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Std_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_InferType_instAddMessageContextInferTypeM___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_InferType_instAddMessageContextInferTypeM___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_InferType_instAddMessageContextInferTypeM___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_InferType_instAddMessageContextInferTypeM___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_InferType_instAddMessageContextInferTypeM___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_InferType_instAddMessageContextInferTypeM___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_InferType_instAddMessageContextInferTypeM___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_InferType_instAddMessageContextInferTypeM___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_InferType_instAddMessageContextInferTypeM___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Compiler_InferType_instAddMessageContextInferTypeM___closed__3;
x_3 = l_Lean_Compiler_InferType_instAddMessageContextInferTypeM___closed__4;
x_4 = l_Lean_Compiler_InferType_instAddMessageContextInferTypeM___closed__5;
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
LEAN_EXPORT lean_object* l_Lean_Compiler_InferType_instAddMessageContextInferTypeM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_st_ref_get(x_4, x_5);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_ctor_get(x_3, 2);
x_11 = l_Lean_Compiler_InferType_instAddMessageContextInferTypeM___closed__6;
lean_inc(x_10);
x_12 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_12, 0, x_9);
lean_ctor_set(x_12, 1, x_11);
lean_ctor_set(x_12, 2, x_2);
lean_ctor_set(x_12, 3, x_10);
x_13 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_1);
lean_ctor_set(x_6, 0, x_13);
return x_6;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_14 = lean_ctor_get(x_6, 0);
x_15 = lean_ctor_get(x_6, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_6);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_3, 2);
x_18 = l_Lean_Compiler_InferType_instAddMessageContextInferTypeM___closed__6;
lean_inc(x_17);
x_19 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_18);
lean_ctor_set(x_19, 2, x_2);
lean_ctor_set(x_19, 3, x_17);
x_20 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_1);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_15);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_InferType_instAddMessageContextInferTypeM___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Compiler_InferType_instAddMessageContextInferTypeM(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at_Lean_Compiler_InferType_withLocalDecl___spec__2___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_st_ref_get(x_1, x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_4, 2);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec(x_3);
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_8 = lean_ctor_get(x_5, 0);
x_9 = lean_ctor_get(x_5, 1);
lean_inc(x_9);
lean_inc(x_8);
x_10 = l_Lean_Name_num___override(x_8, x_9);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_9, x_11);
lean_dec(x_9);
lean_ctor_set(x_5, 1, x_12);
x_13 = lean_st_ref_take(x_1, x_6);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = !lean_is_exclusive(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_14, 2);
lean_dec(x_17);
lean_ctor_set(x_14, 2, x_5);
x_18 = lean_st_ref_set(x_1, x_14, x_15);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_18, 0);
lean_dec(x_20);
lean_ctor_set(x_18, 0, x_10);
return x_18;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_10);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_23 = lean_ctor_get(x_14, 0);
x_24 = lean_ctor_get(x_14, 1);
x_25 = lean_ctor_get(x_14, 3);
x_26 = lean_ctor_get(x_14, 4);
x_27 = lean_ctor_get(x_14, 5);
x_28 = lean_ctor_get(x_14, 6);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_14);
x_29 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_29, 0, x_23);
lean_ctor_set(x_29, 1, x_24);
lean_ctor_set(x_29, 2, x_5);
lean_ctor_set(x_29, 3, x_25);
lean_ctor_set(x_29, 4, x_26);
lean_ctor_set(x_29, 5, x_27);
lean_ctor_set(x_29, 6, x_28);
x_30 = lean_st_ref_set(x_1, x_29, x_15);
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_32 = x_30;
} else {
 lean_dec_ref(x_30);
 x_32 = lean_box(0);
}
if (lean_is_scalar(x_32)) {
 x_33 = lean_alloc_ctor(0, 2, 0);
} else {
 x_33 = x_32;
}
lean_ctor_set(x_33, 0, x_10);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_34 = lean_ctor_get(x_5, 0);
x_35 = lean_ctor_get(x_5, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_5);
lean_inc(x_35);
lean_inc(x_34);
x_36 = l_Lean_Name_num___override(x_34, x_35);
x_37 = lean_unsigned_to_nat(1u);
x_38 = lean_nat_add(x_35, x_37);
lean_dec(x_35);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_34);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_st_ref_take(x_1, x_6);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = lean_ctor_get(x_41, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_41, 1);
lean_inc(x_44);
x_45 = lean_ctor_get(x_41, 3);
lean_inc(x_45);
x_46 = lean_ctor_get(x_41, 4);
lean_inc(x_46);
x_47 = lean_ctor_get(x_41, 5);
lean_inc(x_47);
x_48 = lean_ctor_get(x_41, 6);
lean_inc(x_48);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 lean_ctor_release(x_41, 2);
 lean_ctor_release(x_41, 3);
 lean_ctor_release(x_41, 4);
 lean_ctor_release(x_41, 5);
 lean_ctor_release(x_41, 6);
 x_49 = x_41;
} else {
 lean_dec_ref(x_41);
 x_49 = lean_box(0);
}
if (lean_is_scalar(x_49)) {
 x_50 = lean_alloc_ctor(0, 7, 0);
} else {
 x_50 = x_49;
}
lean_ctor_set(x_50, 0, x_43);
lean_ctor_set(x_50, 1, x_44);
lean_ctor_set(x_50, 2, x_39);
lean_ctor_set(x_50, 3, x_45);
lean_ctor_set(x_50, 4, x_46);
lean_ctor_set(x_50, 5, x_47);
lean_ctor_set(x_50, 6, x_48);
x_51 = lean_st_ref_set(x_1, x_50, x_42);
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 lean_ctor_release(x_51, 1);
 x_53 = x_51;
} else {
 lean_dec_ref(x_51);
 x_53 = lean_box(0);
}
if (lean_is_scalar(x_53)) {
 x_54 = lean_alloc_ctor(0, 2, 0);
} else {
 x_54 = x_53;
}
lean_ctor_set(x_54, 0, x_36);
lean_ctor_set(x_54, 1, x_52);
return x_54;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at_Lean_Compiler_InferType_withLocalDecl___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_mkFreshId___at_Lean_Compiler_InferType_withLocalDecl___spec__2___rarg___boxed), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at_Lean_Compiler_InferType_withLocalDecl___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_mkFreshId___at_Lean_Compiler_InferType_withLocalDecl___spec__2___rarg(x_3, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
return x_5;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_5);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_InferType_withLocalDecl___rarg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = l_Lean_mkFreshFVarId___at_Lean_Compiler_InferType_withLocalDecl___spec__1(x_5, x_6, x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_10);
x_12 = l_Lean_Expr_fvar___override(x_10);
x_13 = lean_local_ctx_mk_local_decl(x_5, x_10, x_1, x_2, x_3);
x_14 = lean_apply_5(x_4, x_12, x_13, x_6, x_7, x_11);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_InferType_withLocalDecl(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Compiler_InferType_withLocalDecl___rarg___boxed), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at_Lean_Compiler_InferType_withLocalDecl___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_mkFreshId___at_Lean_Compiler_InferType_withLocalDecl___spec__2___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at_Lean_Compiler_InferType_withLocalDecl___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_mkFreshId___at_Lean_Compiler_InferType_withLocalDecl___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at_Lean_Compiler_InferType_withLocalDecl___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_mkFreshFVarId___at_Lean_Compiler_InferType_withLocalDecl___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_InferType_withLocalDecl___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
lean_dec(x_3);
x_10 = l_Lean_Compiler_InferType_withLocalDecl___rarg(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
static lean_object* _init_l_Lean_Compiler_InferType_inferConstType___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("lcAny", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_InferType_inferConstType___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_InferType_inferConstType___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_InferType_inferConstType___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("lcErased", 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_InferType_inferConstType___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_InferType_inferConstType___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_InferType_inferConstType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = l_Lean_Compiler_InferType_inferConstType___closed__2;
x_7 = lean_name_eq(x_1, x_6);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = l_Lean_Compiler_InferType_inferConstType___closed__4;
x_9 = lean_name_eq(x_1, x_8);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_instantiateLCNFTypeLevelParams(x_1, x_2, x_3, x_4, x_5);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = l_Lean_Compiler_anyTypeExpr;
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_5);
return x_12;
}
}
else
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_13 = l_Lean_Compiler_anyTypeExpr;
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_5);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_InferType_inferFVarType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
lean_inc(x_1);
x_6 = lean_local_ctx_find(x_2, x_1);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
x_7 = l_Lean_FVarId_throwUnknown___rarg(x_1, x_3, x_4, x_5);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_1);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_LocalDecl_type(x_8);
lean_dec(x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_5);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_InferType_inferFVarType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Compiler_InferType_inferFVarType(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_InferType_getCasesResultingType_go___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_3, 5);
x_7 = lean_st_ref_get(x_4, x_5);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_ctor_get(x_3, 2);
x_12 = l_Lean_Compiler_InferType_instAddMessageContextInferTypeM___closed__6;
lean_inc(x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_12);
lean_ctor_set(x_13, 2, x_2);
lean_ctor_set(x_13, 3, x_11);
x_14 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_1);
lean_inc(x_6);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_6);
lean_ctor_set(x_15, 1, x_14);
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 0, x_15);
return x_7;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_16 = lean_ctor_get(x_7, 0);
x_17 = lean_ctor_get(x_7, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_7);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_3, 2);
x_20 = l_Lean_Compiler_InferType_instAddMessageContextInferTypeM___closed__6;
lean_inc(x_19);
x_21 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_20);
lean_ctor_set(x_21, 2, x_2);
lean_ctor_set(x_21, 3, x_19);
x_22 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_1);
lean_inc(x_6);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_6);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_17);
return x_24;
}
}
}
static lean_object* _init_l_Lean_Compiler_InferType_getCasesResultingType_go___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("invalid LCNF cases-experession", 30);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_InferType_getCasesResultingType_go___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_InferType_getCasesResultingType_go___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_InferType_getCasesResultingType_go___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("", 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_InferType_getCasesResultingType_go___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_InferType_getCasesResultingType_go___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_InferType_getCasesResultingType_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_3, x_8);
if (x_9 == 0)
{
if (lean_obj_tag(x_2) == 6)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_2, 2);
lean_inc(x_10);
lean_dec(x_2);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_sub(x_3, x_11);
lean_dec(x_3);
x_2 = x_10;
x_3 = x_12;
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_3);
lean_dec(x_2);
x_14 = l_Lean_indentExpr(x_1);
x_15 = l_Lean_Compiler_InferType_getCasesResultingType_go___closed__2;
x_16 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
x_17 = l_Lean_Compiler_InferType_getCasesResultingType_go___closed__4;
x_18 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Lean_throwError___at_Lean_Compiler_InferType_getCasesResultingType_go___spec__1(x_18, x_4, x_5, x_6, x_7);
lean_dec(x_5);
return x_19;
}
}
else
{
lean_object* x_20; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_2);
lean_ctor_set(x_20, 1, x_7);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_InferType_getCasesResultingType_go___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_throwError___at_Lean_Compiler_InferType_getCasesResultingType_go___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_InferType_getCasesResultingType_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_InferType_getCasesResultingType_go(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_InferType_getCasesResultingType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_ctor_get(x_1, 5);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_2, x_8);
x_10 = lean_nat_sub(x_9, x_7);
lean_dec(x_9);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_sub(x_10, x_11);
lean_dec(x_10);
lean_inc(x_2);
x_13 = l_Lean_Expr_getRevArg_x21(x_2, x_12);
x_14 = l_Lean_Compiler_CasesInfo_geNumDiscrs(x_1);
x_15 = l_Lean_Compiler_InferType_getCasesResultingType_go(x_2, x_13, x_14, x_3, x_4, x_5, x_6);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_InferType_getCasesResultingType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_InferType_getCasesResultingType(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_InferType_inferLambdaType_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 6:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 2);
lean_inc(x_10);
x_11 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
lean_dec(x_1);
x_12 = lean_expr_instantiate_rev(x_9, x_3);
lean_dec(x_9);
x_13 = l_Lean_mkFreshFVarId___at_Lean_Compiler_InferType_withLocalDecl___spec__1(x_4, x_5, x_6, x_7);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_14);
x_16 = l_Lean_Expr_fvar___override(x_14);
x_17 = lean_local_ctx_mk_local_decl(x_4, x_14, x_8, x_12, x_11);
lean_inc(x_16);
x_18 = lean_array_push(x_2, x_16);
x_19 = lean_array_push(x_3, x_16);
x_1 = x_10;
x_2 = x_18;
x_3 = x_19;
x_4 = x_17;
x_7 = x_15;
goto _start;
}
case 8:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; 
x_21 = lean_ctor_get(x_1, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_1, 1);
lean_inc(x_22);
x_23 = lean_ctor_get(x_1, 3);
lean_inc(x_23);
lean_dec(x_1);
x_24 = lean_expr_instantiate_rev(x_22, x_3);
lean_dec(x_22);
x_25 = l_Lean_mkFreshFVarId___at_Lean_Compiler_InferType_withLocalDecl___spec__1(x_4, x_5, x_6, x_7);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
lean_inc(x_26);
x_28 = l_Lean_Expr_fvar___override(x_26);
x_29 = 0;
x_30 = lean_local_ctx_mk_local_decl(x_4, x_26, x_21, x_24, x_29);
x_31 = lean_array_push(x_3, x_28);
x_1 = x_23;
x_3 = x_31;
x_4 = x_30;
x_7 = x_27;
goto _start;
}
default: 
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_expr_instantiate_rev(x_1, x_3);
lean_dec(x_3);
lean_dec(x_1);
lean_inc(x_4);
x_34 = l_Lean_Compiler_InferType_inferType(x_33, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_34) == 0)
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_34, 0);
x_37 = l_Lean_LocalContext_mkForall(x_4, x_2, x_36);
lean_dec(x_2);
lean_ctor_set(x_34, 0, x_37);
return x_34;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_ctor_get(x_34, 0);
x_39 = lean_ctor_get(x_34, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_34);
x_40 = l_Lean_LocalContext_mkForall(x_4, x_2, x_38);
lean_dec(x_2);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
return x_41;
}
}
else
{
uint8_t x_42; 
lean_dec(x_4);
lean_dec(x_2);
x_42 = !lean_is_exclusive(x_34);
if (x_42 == 0)
{
return x_34;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_34, 0);
x_44 = lean_ctor_get(x_34, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_34);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_InferType_inferType___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("unexpected bound variable ", 26);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_InferType_inferType___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_InferType_inferType___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_InferType_inferType___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("unexpected metavariable ", 24);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_InferType_inferType___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_InferType_inferType___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_InferType_inferType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_6, 0, x_1);
x_7 = l_Lean_Compiler_InferType_inferType___closed__2;
x_8 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
x_9 = l_Lean_Compiler_InferType_getCasesResultingType_go___closed__4;
x_10 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = l_Lean_throwError___at_Lean_Compiler_InferType_getCasesResultingType_go___spec__1(x_10, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_11;
}
case 1:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
lean_dec(x_1);
x_13 = l_Lean_Compiler_InferType_inferFVarType(x_12, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_13;
}
case 2:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_14, 0, x_1);
x_15 = l_Lean_Compiler_InferType_inferType___closed__4;
x_16 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
x_17 = l_Lean_Compiler_InferType_getCasesResultingType_go___closed__4;
x_18 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Lean_throwError___at_Lean_Compiler_InferType_getCasesResultingType_go___spec__1(x_18, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_19;
}
case 3:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
lean_dec(x_1);
x_21 = l_Lean_Level_succ___override(x_20);
x_22 = l_Lean_Expr_sort___override(x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_5);
return x_23;
}
case 4:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_2);
x_24 = lean_ctor_get(x_1, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_1, 1);
lean_inc(x_25);
lean_dec(x_1);
x_26 = l_Lean_Compiler_InferType_inferConstType(x_24, x_25, x_3, x_4, x_5);
return x_26;
}
case 5:
{
lean_object* x_27; 
x_27 = l_Lean_Compiler_InferType_inferAppType(x_1, x_2, x_3, x_4, x_5);
return x_27;
}
case 7:
{
lean_object* x_28; 
x_28 = l_Lean_Compiler_InferType_inferForallType(x_1, x_2, x_3, x_4, x_5);
return x_28;
}
case 9:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_29 = lean_ctor_get(x_1, 0);
lean_inc(x_29);
lean_dec(x_1);
x_30 = l_Lean_Literal_type(x_29);
lean_dec(x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_5);
return x_31;
}
case 10:
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_1, 1);
lean_inc(x_32);
lean_dec(x_1);
x_1 = x_32;
goto _start;
}
case 11:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_1, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_1, 1);
lean_inc(x_35);
x_36 = lean_ctor_get(x_1, 2);
lean_inc(x_36);
lean_dec(x_1);
x_37 = l_Lean_Compiler_InferType_inferProjType(x_34, x_35, x_36, x_2, x_3, x_4, x_5);
return x_37;
}
default: 
{
lean_object* x_38; 
x_38 = l_Lean_Compiler_InferType_inferLambdaType(x_1, x_2, x_3, x_4, x_5);
return x_38;
}
}
}
}
static lean_object* _init_l_Lean_Compiler_InferType_inferLambdaType___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_InferType_inferLambdaType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lean_Compiler_InferType_inferLambdaType___closed__1;
x_7 = l_Lean_Compiler_InferType_inferLambdaType_go(x_1, x_6, x_6, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_InferType_inferForallType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lean_Compiler_InferType_inferLambdaType___closed__1;
x_7 = l_Lean_Compiler_InferType_inferForallType_go(x_1, x_6, x_2, x_3, x_4, x_5);
return x_7;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Compiler_InferType_inferForallType_go___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_anyTypeExpr;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_InferType_inferForallType_go___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_4, x_3);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_5);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_uget(x_2, x_4);
x_13 = !lean_is_exclusive(x_5);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_5, 1);
x_15 = lean_ctor_get(x_5, 0);
lean_dec(x_15);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_16 = l_Lean_Compiler_InferType_inferType(x_12, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_19 = l_Lean_Compiler_InferType_getLevel_x3f(x_17, x_6, x_7, x_8, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_19, 0);
lean_dec(x_22);
x_23 = l_Array_forInUnsafe_loop___at_Lean_Compiler_InferType_inferForallType_go___spec__1___closed__1;
lean_ctor_set(x_5, 0, x_23);
lean_ctor_set(x_19, 0, x_5);
return x_19;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_19, 1);
lean_inc(x_24);
lean_dec(x_19);
x_25 = l_Array_forInUnsafe_loop___at_Lean_Compiler_InferType_inferForallType_go___spec__1___closed__1;
lean_ctor_set(x_5, 0, x_25);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_5);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; size_t x_30; size_t x_31; 
x_27 = lean_ctor_get(x_19, 1);
lean_inc(x_27);
lean_dec(x_19);
x_28 = lean_ctor_get(x_20, 0);
lean_inc(x_28);
lean_dec(x_20);
x_29 = l_Lean_Level_imax___override(x_28, x_14);
lean_inc(x_1);
lean_ctor_set(x_5, 1, x_29);
lean_ctor_set(x_5, 0, x_1);
x_30 = 1;
x_31 = lean_usize_add(x_4, x_30);
x_4 = x_31;
x_9 = x_27;
goto _start;
}
}
else
{
uint8_t x_33; 
lean_free_object(x_5);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_19);
if (x_33 == 0)
{
return x_19;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_19, 0);
x_35 = lean_ctor_get(x_19, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_19);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
uint8_t x_37; 
lean_free_object(x_5);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
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
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_5, 1);
lean_inc(x_41);
lean_dec(x_5);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_42 = l_Lean_Compiler_InferType_inferType(x_12, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_45 = l_Lean_Compiler_InferType_getLevel_x3f(x_43, x_6, x_7, x_8, x_44);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_48 = x_45;
} else {
 lean_dec_ref(x_45);
 x_48 = lean_box(0);
}
x_49 = l_Array_forInUnsafe_loop___at_Lean_Compiler_InferType_inferForallType_go___spec__1___closed__1;
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_41);
if (lean_is_scalar(x_48)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_48;
}
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_47);
return x_51;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; size_t x_56; size_t x_57; 
x_52 = lean_ctor_get(x_45, 1);
lean_inc(x_52);
lean_dec(x_45);
x_53 = lean_ctor_get(x_46, 0);
lean_inc(x_53);
lean_dec(x_46);
x_54 = l_Lean_Level_imax___override(x_53, x_41);
lean_inc(x_1);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_1);
lean_ctor_set(x_55, 1, x_54);
x_56 = 1;
x_57 = lean_usize_add(x_4, x_56);
x_4 = x_57;
x_5 = x_55;
x_9 = x_52;
goto _start;
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_41);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_59 = lean_ctor_get(x_45, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_45, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_61 = x_45;
} else {
 lean_dec_ref(x_45);
 x_61 = lean_box(0);
}
if (lean_is_scalar(x_61)) {
 x_62 = lean_alloc_ctor(1, 2, 0);
} else {
 x_62 = x_61;
}
lean_ctor_set(x_62, 0, x_59);
lean_ctor_set(x_62, 1, x_60);
return x_62;
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_41);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_63 = lean_ctor_get(x_42, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_42, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_65 = x_42;
} else {
 lean_dec_ref(x_42);
 x_65 = lean_box(0);
}
if (lean_is_scalar(x_65)) {
 x_66 = lean_alloc_ctor(1, 2, 0);
} else {
 x_66 = x_65;
}
lean_ctor_set(x_66, 0, x_63);
lean_ctor_set(x_66, 1, x_64);
return x_66;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_InferType_inferForallType_go___spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_4, x_3);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_5);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_uget(x_2, x_4);
x_13 = !lean_is_exclusive(x_5);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_5, 1);
x_15 = lean_ctor_get(x_5, 0);
lean_dec(x_15);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_16 = l_Lean_Compiler_InferType_inferType(x_12, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_19 = l_Lean_Compiler_InferType_getLevel_x3f(x_17, x_6, x_7, x_8, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_19, 0);
lean_dec(x_22);
x_23 = l_Array_forInUnsafe_loop___at_Lean_Compiler_InferType_inferForallType_go___spec__1___closed__1;
lean_ctor_set(x_5, 0, x_23);
lean_ctor_set(x_19, 0, x_5);
return x_19;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_19, 1);
lean_inc(x_24);
lean_dec(x_19);
x_25 = l_Array_forInUnsafe_loop___at_Lean_Compiler_InferType_inferForallType_go___spec__1___closed__1;
lean_ctor_set(x_5, 0, x_25);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_5);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; size_t x_30; size_t x_31; 
x_27 = lean_ctor_get(x_19, 1);
lean_inc(x_27);
lean_dec(x_19);
x_28 = lean_ctor_get(x_20, 0);
lean_inc(x_28);
lean_dec(x_20);
x_29 = l_Lean_Level_imax___override(x_28, x_14);
lean_inc(x_1);
lean_ctor_set(x_5, 1, x_29);
lean_ctor_set(x_5, 0, x_1);
x_30 = 1;
x_31 = lean_usize_add(x_4, x_30);
x_4 = x_31;
x_9 = x_27;
goto _start;
}
}
else
{
uint8_t x_33; 
lean_free_object(x_5);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_19);
if (x_33 == 0)
{
return x_19;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_19, 0);
x_35 = lean_ctor_get(x_19, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_19);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
uint8_t x_37; 
lean_free_object(x_5);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
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
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_5, 1);
lean_inc(x_41);
lean_dec(x_5);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_42 = l_Lean_Compiler_InferType_inferType(x_12, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_45 = l_Lean_Compiler_InferType_getLevel_x3f(x_43, x_6, x_7, x_8, x_44);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_48 = x_45;
} else {
 lean_dec_ref(x_45);
 x_48 = lean_box(0);
}
x_49 = l_Array_forInUnsafe_loop___at_Lean_Compiler_InferType_inferForallType_go___spec__1___closed__1;
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_41);
if (lean_is_scalar(x_48)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_48;
}
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_47);
return x_51;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; size_t x_56; size_t x_57; 
x_52 = lean_ctor_get(x_45, 1);
lean_inc(x_52);
lean_dec(x_45);
x_53 = lean_ctor_get(x_46, 0);
lean_inc(x_53);
lean_dec(x_46);
x_54 = l_Lean_Level_imax___override(x_53, x_41);
lean_inc(x_1);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_1);
lean_ctor_set(x_55, 1, x_54);
x_56 = 1;
x_57 = lean_usize_add(x_4, x_56);
x_4 = x_57;
x_5 = x_55;
x_9 = x_52;
goto _start;
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_41);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_59 = lean_ctor_get(x_45, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_45, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_61 = x_45;
} else {
 lean_dec_ref(x_45);
 x_61 = lean_box(0);
}
if (lean_is_scalar(x_61)) {
 x_62 = lean_alloc_ctor(1, 2, 0);
} else {
 x_62 = x_61;
}
lean_ctor_set(x_62, 0, x_59);
lean_ctor_set(x_62, 1, x_60);
return x_62;
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_41);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_63 = lean_ctor_get(x_42, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_42, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_65 = x_42;
} else {
 lean_dec_ref(x_42);
 x_65 = lean_box(0);
}
if (lean_is_scalar(x_65)) {
 x_66 = lean_alloc_ctor(1, 2, 0);
} else {
 x_66 = x_65;
}
lean_ctor_set(x_66, 0, x_63);
lean_ctor_set(x_66, 1, x_64);
return x_66;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_InferType_inferForallType_go___spec__3(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_4, x_3);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_5);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_uget(x_2, x_4);
x_13 = !lean_is_exclusive(x_5);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_5, 1);
x_15 = lean_ctor_get(x_5, 0);
lean_dec(x_15);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_16 = l_Lean_Compiler_InferType_inferType(x_12, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_19 = l_Lean_Compiler_InferType_getLevel_x3f(x_17, x_6, x_7, x_8, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_19, 0);
lean_dec(x_22);
x_23 = l_Array_forInUnsafe_loop___at_Lean_Compiler_InferType_inferForallType_go___spec__1___closed__1;
lean_ctor_set(x_5, 0, x_23);
lean_ctor_set(x_19, 0, x_5);
return x_19;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_19, 1);
lean_inc(x_24);
lean_dec(x_19);
x_25 = l_Array_forInUnsafe_loop___at_Lean_Compiler_InferType_inferForallType_go___spec__1___closed__1;
lean_ctor_set(x_5, 0, x_25);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_5);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; size_t x_30; size_t x_31; 
x_27 = lean_ctor_get(x_19, 1);
lean_inc(x_27);
lean_dec(x_19);
x_28 = lean_ctor_get(x_20, 0);
lean_inc(x_28);
lean_dec(x_20);
x_29 = l_Lean_Level_imax___override(x_28, x_14);
lean_inc(x_1);
lean_ctor_set(x_5, 1, x_29);
lean_ctor_set(x_5, 0, x_1);
x_30 = 1;
x_31 = lean_usize_add(x_4, x_30);
x_4 = x_31;
x_9 = x_27;
goto _start;
}
}
else
{
uint8_t x_33; 
lean_free_object(x_5);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_19);
if (x_33 == 0)
{
return x_19;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_19, 0);
x_35 = lean_ctor_get(x_19, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_19);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
uint8_t x_37; 
lean_free_object(x_5);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
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
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_5, 1);
lean_inc(x_41);
lean_dec(x_5);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_42 = l_Lean_Compiler_InferType_inferType(x_12, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_45 = l_Lean_Compiler_InferType_getLevel_x3f(x_43, x_6, x_7, x_8, x_44);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_48 = x_45;
} else {
 lean_dec_ref(x_45);
 x_48 = lean_box(0);
}
x_49 = l_Array_forInUnsafe_loop___at_Lean_Compiler_InferType_inferForallType_go___spec__1___closed__1;
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_41);
if (lean_is_scalar(x_48)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_48;
}
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_47);
return x_51;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; size_t x_56; size_t x_57; 
x_52 = lean_ctor_get(x_45, 1);
lean_inc(x_52);
lean_dec(x_45);
x_53 = lean_ctor_get(x_46, 0);
lean_inc(x_53);
lean_dec(x_46);
x_54 = l_Lean_Level_imax___override(x_53, x_41);
lean_inc(x_1);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_1);
lean_ctor_set(x_55, 1, x_54);
x_56 = 1;
x_57 = lean_usize_add(x_4, x_56);
x_4 = x_57;
x_5 = x_55;
x_9 = x_52;
goto _start;
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_41);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_59 = lean_ctor_get(x_45, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_45, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_61 = x_45;
} else {
 lean_dec_ref(x_45);
 x_61 = lean_box(0);
}
if (lean_is_scalar(x_61)) {
 x_62 = lean_alloc_ctor(1, 2, 0);
} else {
 x_62 = x_61;
}
lean_ctor_set(x_62, 0, x_59);
lean_ctor_set(x_62, 1, x_60);
return x_62;
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_41);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_63 = lean_ctor_get(x_42, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_42, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_65 = x_42;
} else {
 lean_dec_ref(x_42);
 x_65 = lean_box(0);
}
if (lean_is_scalar(x_65)) {
 x_66 = lean_alloc_ctor(1, 2, 0);
} else {
 x_66 = x_65;
}
lean_ctor_set(x_66, 0, x_63);
lean_ctor_set(x_66, 1, x_64);
return x_66;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_InferType_inferForallType_go___spec__4(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_4, x_3);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_5);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_uget(x_2, x_4);
x_13 = !lean_is_exclusive(x_5);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_5, 1);
x_15 = lean_ctor_get(x_5, 0);
lean_dec(x_15);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_16 = l_Lean_Compiler_InferType_inferType(x_12, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_19 = l_Lean_Compiler_InferType_getLevel_x3f(x_17, x_6, x_7, x_8, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_19, 0);
lean_dec(x_22);
x_23 = l_Array_forInUnsafe_loop___at_Lean_Compiler_InferType_inferForallType_go___spec__1___closed__1;
lean_ctor_set(x_5, 0, x_23);
lean_ctor_set(x_19, 0, x_5);
return x_19;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_19, 1);
lean_inc(x_24);
lean_dec(x_19);
x_25 = l_Array_forInUnsafe_loop___at_Lean_Compiler_InferType_inferForallType_go___spec__1___closed__1;
lean_ctor_set(x_5, 0, x_25);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_5);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; size_t x_30; size_t x_31; 
x_27 = lean_ctor_get(x_19, 1);
lean_inc(x_27);
lean_dec(x_19);
x_28 = lean_ctor_get(x_20, 0);
lean_inc(x_28);
lean_dec(x_20);
x_29 = l_Lean_Level_imax___override(x_28, x_14);
lean_inc(x_1);
lean_ctor_set(x_5, 1, x_29);
lean_ctor_set(x_5, 0, x_1);
x_30 = 1;
x_31 = lean_usize_add(x_4, x_30);
x_4 = x_31;
x_9 = x_27;
goto _start;
}
}
else
{
uint8_t x_33; 
lean_free_object(x_5);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_19);
if (x_33 == 0)
{
return x_19;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_19, 0);
x_35 = lean_ctor_get(x_19, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_19);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
uint8_t x_37; 
lean_free_object(x_5);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
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
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_5, 1);
lean_inc(x_41);
lean_dec(x_5);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_42 = l_Lean_Compiler_InferType_inferType(x_12, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_45 = l_Lean_Compiler_InferType_getLevel_x3f(x_43, x_6, x_7, x_8, x_44);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_48 = x_45;
} else {
 lean_dec_ref(x_45);
 x_48 = lean_box(0);
}
x_49 = l_Array_forInUnsafe_loop___at_Lean_Compiler_InferType_inferForallType_go___spec__1___closed__1;
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_41);
if (lean_is_scalar(x_48)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_48;
}
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_47);
return x_51;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; size_t x_56; size_t x_57; 
x_52 = lean_ctor_get(x_45, 1);
lean_inc(x_52);
lean_dec(x_45);
x_53 = lean_ctor_get(x_46, 0);
lean_inc(x_53);
lean_dec(x_46);
x_54 = l_Lean_Level_imax___override(x_53, x_41);
lean_inc(x_1);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_1);
lean_ctor_set(x_55, 1, x_54);
x_56 = 1;
x_57 = lean_usize_add(x_4, x_56);
x_4 = x_57;
x_5 = x_55;
x_9 = x_52;
goto _start;
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_41);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_59 = lean_ctor_get(x_45, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_45, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_61 = x_45;
} else {
 lean_dec_ref(x_45);
 x_61 = lean_box(0);
}
if (lean_is_scalar(x_61)) {
 x_62 = lean_alloc_ctor(1, 2, 0);
} else {
 x_62 = x_61;
}
lean_ctor_set(x_62, 0, x_59);
lean_ctor_set(x_62, 1, x_60);
return x_62;
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_41);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_63 = lean_ctor_get(x_42, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_42, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_65 = x_42;
} else {
 lean_dec_ref(x_42);
 x_65 = lean_box(0);
}
if (lean_is_scalar(x_65)) {
 x_66 = lean_alloc_ctor(1, 2, 0);
} else {
 x_66 = x_65;
}
lean_ctor_set(x_66, 0, x_63);
lean_ctor_set(x_66, 1, x_64);
return x_66;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_InferType_inferForallType_go___spec__5(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_4, x_3);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_5);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_uget(x_2, x_4);
x_13 = !lean_is_exclusive(x_5);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_5, 1);
x_15 = lean_ctor_get(x_5, 0);
lean_dec(x_15);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_16 = l_Lean_Compiler_InferType_inferType(x_12, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_19 = l_Lean_Compiler_InferType_getLevel_x3f(x_17, x_6, x_7, x_8, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_19, 0);
lean_dec(x_22);
x_23 = l_Array_forInUnsafe_loop___at_Lean_Compiler_InferType_inferForallType_go___spec__1___closed__1;
lean_ctor_set(x_5, 0, x_23);
lean_ctor_set(x_19, 0, x_5);
return x_19;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_19, 1);
lean_inc(x_24);
lean_dec(x_19);
x_25 = l_Array_forInUnsafe_loop___at_Lean_Compiler_InferType_inferForallType_go___spec__1___closed__1;
lean_ctor_set(x_5, 0, x_25);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_5);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; size_t x_30; size_t x_31; 
x_27 = lean_ctor_get(x_19, 1);
lean_inc(x_27);
lean_dec(x_19);
x_28 = lean_ctor_get(x_20, 0);
lean_inc(x_28);
lean_dec(x_20);
x_29 = l_Lean_Level_imax___override(x_28, x_14);
lean_inc(x_1);
lean_ctor_set(x_5, 1, x_29);
lean_ctor_set(x_5, 0, x_1);
x_30 = 1;
x_31 = lean_usize_add(x_4, x_30);
x_4 = x_31;
x_9 = x_27;
goto _start;
}
}
else
{
uint8_t x_33; 
lean_free_object(x_5);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_19);
if (x_33 == 0)
{
return x_19;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_19, 0);
x_35 = lean_ctor_get(x_19, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_19);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
uint8_t x_37; 
lean_free_object(x_5);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
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
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_5, 1);
lean_inc(x_41);
lean_dec(x_5);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_42 = l_Lean_Compiler_InferType_inferType(x_12, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_45 = l_Lean_Compiler_InferType_getLevel_x3f(x_43, x_6, x_7, x_8, x_44);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_48 = x_45;
} else {
 lean_dec_ref(x_45);
 x_48 = lean_box(0);
}
x_49 = l_Array_forInUnsafe_loop___at_Lean_Compiler_InferType_inferForallType_go___spec__1___closed__1;
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_41);
if (lean_is_scalar(x_48)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_48;
}
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_47);
return x_51;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; size_t x_56; size_t x_57; 
x_52 = lean_ctor_get(x_45, 1);
lean_inc(x_52);
lean_dec(x_45);
x_53 = lean_ctor_get(x_46, 0);
lean_inc(x_53);
lean_dec(x_46);
x_54 = l_Lean_Level_imax___override(x_53, x_41);
lean_inc(x_1);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_1);
lean_ctor_set(x_55, 1, x_54);
x_56 = 1;
x_57 = lean_usize_add(x_4, x_56);
x_4 = x_57;
x_5 = x_55;
x_9 = x_52;
goto _start;
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_41);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_59 = lean_ctor_get(x_45, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_45, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_61 = x_45;
} else {
 lean_dec_ref(x_45);
 x_61 = lean_box(0);
}
if (lean_is_scalar(x_61)) {
 x_62 = lean_alloc_ctor(1, 2, 0);
} else {
 x_62 = x_61;
}
lean_ctor_set(x_62, 0, x_59);
lean_ctor_set(x_62, 1, x_60);
return x_62;
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_41);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_63 = lean_ctor_get(x_42, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_42, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_65 = x_42;
} else {
 lean_dec_ref(x_42);
 x_65 = lean_box(0);
}
if (lean_is_scalar(x_65)) {
 x_66 = lean_alloc_ctor(1, 2, 0);
} else {
 x_66 = x_65;
}
lean_ctor_set(x_66, 0, x_63);
lean_ctor_set(x_66, 1, x_64);
return x_66;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_InferType_inferForallType_go___spec__6(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_4, x_3);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_5);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_uget(x_2, x_4);
x_13 = !lean_is_exclusive(x_5);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_5, 1);
x_15 = lean_ctor_get(x_5, 0);
lean_dec(x_15);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_16 = l_Lean_Compiler_InferType_inferType(x_12, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_19 = l_Lean_Compiler_InferType_getLevel_x3f(x_17, x_6, x_7, x_8, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_19, 0);
lean_dec(x_22);
x_23 = l_Array_forInUnsafe_loop___at_Lean_Compiler_InferType_inferForallType_go___spec__1___closed__1;
lean_ctor_set(x_5, 0, x_23);
lean_ctor_set(x_19, 0, x_5);
return x_19;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_19, 1);
lean_inc(x_24);
lean_dec(x_19);
x_25 = l_Array_forInUnsafe_loop___at_Lean_Compiler_InferType_inferForallType_go___spec__1___closed__1;
lean_ctor_set(x_5, 0, x_25);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_5);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; size_t x_30; size_t x_31; 
x_27 = lean_ctor_get(x_19, 1);
lean_inc(x_27);
lean_dec(x_19);
x_28 = lean_ctor_get(x_20, 0);
lean_inc(x_28);
lean_dec(x_20);
x_29 = l_Lean_Level_imax___override(x_28, x_14);
lean_inc(x_1);
lean_ctor_set(x_5, 1, x_29);
lean_ctor_set(x_5, 0, x_1);
x_30 = 1;
x_31 = lean_usize_add(x_4, x_30);
x_4 = x_31;
x_9 = x_27;
goto _start;
}
}
else
{
uint8_t x_33; 
lean_free_object(x_5);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_19);
if (x_33 == 0)
{
return x_19;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_19, 0);
x_35 = lean_ctor_get(x_19, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_19);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
uint8_t x_37; 
lean_free_object(x_5);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
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
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_5, 1);
lean_inc(x_41);
lean_dec(x_5);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_42 = l_Lean_Compiler_InferType_inferType(x_12, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_45 = l_Lean_Compiler_InferType_getLevel_x3f(x_43, x_6, x_7, x_8, x_44);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_48 = x_45;
} else {
 lean_dec_ref(x_45);
 x_48 = lean_box(0);
}
x_49 = l_Array_forInUnsafe_loop___at_Lean_Compiler_InferType_inferForallType_go___spec__1___closed__1;
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_41);
if (lean_is_scalar(x_48)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_48;
}
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_47);
return x_51;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; size_t x_56; size_t x_57; 
x_52 = lean_ctor_get(x_45, 1);
lean_inc(x_52);
lean_dec(x_45);
x_53 = lean_ctor_get(x_46, 0);
lean_inc(x_53);
lean_dec(x_46);
x_54 = l_Lean_Level_imax___override(x_53, x_41);
lean_inc(x_1);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_1);
lean_ctor_set(x_55, 1, x_54);
x_56 = 1;
x_57 = lean_usize_add(x_4, x_56);
x_4 = x_57;
x_5 = x_55;
x_9 = x_52;
goto _start;
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_41);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_59 = lean_ctor_get(x_45, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_45, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_61 = x_45;
} else {
 lean_dec_ref(x_45);
 x_61 = lean_box(0);
}
if (lean_is_scalar(x_61)) {
 x_62 = lean_alloc_ctor(1, 2, 0);
} else {
 x_62 = x_61;
}
lean_ctor_set(x_62, 0, x_59);
lean_ctor_set(x_62, 1, x_60);
return x_62;
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_41);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_63 = lean_ctor_get(x_42, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_42, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_65 = x_42;
} else {
 lean_dec_ref(x_42);
 x_65 = lean_box(0);
}
if (lean_is_scalar(x_65)) {
 x_66 = lean_alloc_ctor(1, 2, 0);
} else {
 x_66 = x_65;
}
lean_ctor_set(x_66, 0, x_63);
lean_ctor_set(x_66, 1, x_64);
return x_66;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_InferType_inferForallType_go___spec__7(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_4, x_3);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_5);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_uget(x_2, x_4);
x_13 = !lean_is_exclusive(x_5);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_5, 1);
x_15 = lean_ctor_get(x_5, 0);
lean_dec(x_15);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_16 = l_Lean_Compiler_InferType_inferType(x_12, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_19 = l_Lean_Compiler_InferType_getLevel_x3f(x_17, x_6, x_7, x_8, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_19, 0);
lean_dec(x_22);
x_23 = l_Array_forInUnsafe_loop___at_Lean_Compiler_InferType_inferForallType_go___spec__1___closed__1;
lean_ctor_set(x_5, 0, x_23);
lean_ctor_set(x_19, 0, x_5);
return x_19;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_19, 1);
lean_inc(x_24);
lean_dec(x_19);
x_25 = l_Array_forInUnsafe_loop___at_Lean_Compiler_InferType_inferForallType_go___spec__1___closed__1;
lean_ctor_set(x_5, 0, x_25);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_5);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; size_t x_30; size_t x_31; 
x_27 = lean_ctor_get(x_19, 1);
lean_inc(x_27);
lean_dec(x_19);
x_28 = lean_ctor_get(x_20, 0);
lean_inc(x_28);
lean_dec(x_20);
x_29 = l_Lean_Level_imax___override(x_28, x_14);
lean_inc(x_1);
lean_ctor_set(x_5, 1, x_29);
lean_ctor_set(x_5, 0, x_1);
x_30 = 1;
x_31 = lean_usize_add(x_4, x_30);
x_4 = x_31;
x_9 = x_27;
goto _start;
}
}
else
{
uint8_t x_33; 
lean_free_object(x_5);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_19);
if (x_33 == 0)
{
return x_19;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_19, 0);
x_35 = lean_ctor_get(x_19, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_19);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
uint8_t x_37; 
lean_free_object(x_5);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
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
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_5, 1);
lean_inc(x_41);
lean_dec(x_5);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_42 = l_Lean_Compiler_InferType_inferType(x_12, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_45 = l_Lean_Compiler_InferType_getLevel_x3f(x_43, x_6, x_7, x_8, x_44);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_48 = x_45;
} else {
 lean_dec_ref(x_45);
 x_48 = lean_box(0);
}
x_49 = l_Array_forInUnsafe_loop___at_Lean_Compiler_InferType_inferForallType_go___spec__1___closed__1;
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_41);
if (lean_is_scalar(x_48)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_48;
}
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_47);
return x_51;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; size_t x_56; size_t x_57; 
x_52 = lean_ctor_get(x_45, 1);
lean_inc(x_52);
lean_dec(x_45);
x_53 = lean_ctor_get(x_46, 0);
lean_inc(x_53);
lean_dec(x_46);
x_54 = l_Lean_Level_imax___override(x_53, x_41);
lean_inc(x_1);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_1);
lean_ctor_set(x_55, 1, x_54);
x_56 = 1;
x_57 = lean_usize_add(x_4, x_56);
x_4 = x_57;
x_5 = x_55;
x_9 = x_52;
goto _start;
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_41);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_59 = lean_ctor_get(x_45, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_45, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_61 = x_45;
} else {
 lean_dec_ref(x_45);
 x_61 = lean_box(0);
}
if (lean_is_scalar(x_61)) {
 x_62 = lean_alloc_ctor(1, 2, 0);
} else {
 x_62 = x_61;
}
lean_ctor_set(x_62, 0, x_59);
lean_ctor_set(x_62, 1, x_60);
return x_62;
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_41);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_63 = lean_ctor_get(x_42, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_42, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_65 = x_42;
} else {
 lean_dec_ref(x_42);
 x_65 = lean_box(0);
}
if (lean_is_scalar(x_65)) {
 x_66 = lean_alloc_ctor(1, 2, 0);
} else {
 x_66 = x_65;
}
lean_ctor_set(x_66, 0, x_63);
lean_ctor_set(x_66, 1, x_64);
return x_66;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_InferType_inferForallType_go___spec__8(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_4, x_3);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_5);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_uget(x_2, x_4);
x_13 = !lean_is_exclusive(x_5);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_5, 1);
x_15 = lean_ctor_get(x_5, 0);
lean_dec(x_15);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_16 = l_Lean_Compiler_InferType_inferType(x_12, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_19 = l_Lean_Compiler_InferType_getLevel_x3f(x_17, x_6, x_7, x_8, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_19, 0);
lean_dec(x_22);
x_23 = l_Array_forInUnsafe_loop___at_Lean_Compiler_InferType_inferForallType_go___spec__1___closed__1;
lean_ctor_set(x_5, 0, x_23);
lean_ctor_set(x_19, 0, x_5);
return x_19;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_19, 1);
lean_inc(x_24);
lean_dec(x_19);
x_25 = l_Array_forInUnsafe_loop___at_Lean_Compiler_InferType_inferForallType_go___spec__1___closed__1;
lean_ctor_set(x_5, 0, x_25);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_5);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; size_t x_30; size_t x_31; 
x_27 = lean_ctor_get(x_19, 1);
lean_inc(x_27);
lean_dec(x_19);
x_28 = lean_ctor_get(x_20, 0);
lean_inc(x_28);
lean_dec(x_20);
x_29 = l_Lean_Level_imax___override(x_28, x_14);
lean_inc(x_1);
lean_ctor_set(x_5, 1, x_29);
lean_ctor_set(x_5, 0, x_1);
x_30 = 1;
x_31 = lean_usize_add(x_4, x_30);
x_4 = x_31;
x_9 = x_27;
goto _start;
}
}
else
{
uint8_t x_33; 
lean_free_object(x_5);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_19);
if (x_33 == 0)
{
return x_19;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_19, 0);
x_35 = lean_ctor_get(x_19, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_19);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
uint8_t x_37; 
lean_free_object(x_5);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
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
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_5, 1);
lean_inc(x_41);
lean_dec(x_5);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_42 = l_Lean_Compiler_InferType_inferType(x_12, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_45 = l_Lean_Compiler_InferType_getLevel_x3f(x_43, x_6, x_7, x_8, x_44);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_48 = x_45;
} else {
 lean_dec_ref(x_45);
 x_48 = lean_box(0);
}
x_49 = l_Array_forInUnsafe_loop___at_Lean_Compiler_InferType_inferForallType_go___spec__1___closed__1;
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_41);
if (lean_is_scalar(x_48)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_48;
}
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_47);
return x_51;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; size_t x_56; size_t x_57; 
x_52 = lean_ctor_get(x_45, 1);
lean_inc(x_52);
lean_dec(x_45);
x_53 = lean_ctor_get(x_46, 0);
lean_inc(x_53);
lean_dec(x_46);
x_54 = l_Lean_Level_imax___override(x_53, x_41);
lean_inc(x_1);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_1);
lean_ctor_set(x_55, 1, x_54);
x_56 = 1;
x_57 = lean_usize_add(x_4, x_56);
x_4 = x_57;
x_5 = x_55;
x_9 = x_52;
goto _start;
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_41);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_59 = lean_ctor_get(x_45, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_45, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_61 = x_45;
} else {
 lean_dec_ref(x_45);
 x_61 = lean_box(0);
}
if (lean_is_scalar(x_61)) {
 x_62 = lean_alloc_ctor(1, 2, 0);
} else {
 x_62 = x_61;
}
lean_ctor_set(x_62, 0, x_59);
lean_ctor_set(x_62, 1, x_60);
return x_62;
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_41);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_63 = lean_ctor_get(x_42, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_42, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_65 = x_42;
} else {
 lean_dec_ref(x_42);
 x_65 = lean_box(0);
}
if (lean_is_scalar(x_65)) {
 x_66 = lean_alloc_ctor(1, 2, 0);
} else {
 x_66 = x_65;
}
lean_ctor_set(x_66, 0, x_63);
lean_ctor_set(x_66, 1, x_64);
return x_66;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_InferType_inferForallType_go___spec__9(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_4, x_3);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_5);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_uget(x_2, x_4);
x_13 = !lean_is_exclusive(x_5);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_5, 1);
x_15 = lean_ctor_get(x_5, 0);
lean_dec(x_15);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_16 = l_Lean_Compiler_InferType_inferType(x_12, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_19 = l_Lean_Compiler_InferType_getLevel_x3f(x_17, x_6, x_7, x_8, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_19, 0);
lean_dec(x_22);
x_23 = l_Array_forInUnsafe_loop___at_Lean_Compiler_InferType_inferForallType_go___spec__1___closed__1;
lean_ctor_set(x_5, 0, x_23);
lean_ctor_set(x_19, 0, x_5);
return x_19;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_19, 1);
lean_inc(x_24);
lean_dec(x_19);
x_25 = l_Array_forInUnsafe_loop___at_Lean_Compiler_InferType_inferForallType_go___spec__1___closed__1;
lean_ctor_set(x_5, 0, x_25);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_5);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; size_t x_30; size_t x_31; 
x_27 = lean_ctor_get(x_19, 1);
lean_inc(x_27);
lean_dec(x_19);
x_28 = lean_ctor_get(x_20, 0);
lean_inc(x_28);
lean_dec(x_20);
x_29 = l_Lean_Level_imax___override(x_28, x_14);
lean_inc(x_1);
lean_ctor_set(x_5, 1, x_29);
lean_ctor_set(x_5, 0, x_1);
x_30 = 1;
x_31 = lean_usize_add(x_4, x_30);
x_4 = x_31;
x_9 = x_27;
goto _start;
}
}
else
{
uint8_t x_33; 
lean_free_object(x_5);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_19);
if (x_33 == 0)
{
return x_19;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_19, 0);
x_35 = lean_ctor_get(x_19, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_19);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
uint8_t x_37; 
lean_free_object(x_5);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
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
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_5, 1);
lean_inc(x_41);
lean_dec(x_5);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_42 = l_Lean_Compiler_InferType_inferType(x_12, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_45 = l_Lean_Compiler_InferType_getLevel_x3f(x_43, x_6, x_7, x_8, x_44);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_48 = x_45;
} else {
 lean_dec_ref(x_45);
 x_48 = lean_box(0);
}
x_49 = l_Array_forInUnsafe_loop___at_Lean_Compiler_InferType_inferForallType_go___spec__1___closed__1;
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_41);
if (lean_is_scalar(x_48)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_48;
}
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_47);
return x_51;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; size_t x_56; size_t x_57; 
x_52 = lean_ctor_get(x_45, 1);
lean_inc(x_52);
lean_dec(x_45);
x_53 = lean_ctor_get(x_46, 0);
lean_inc(x_53);
lean_dec(x_46);
x_54 = l_Lean_Level_imax___override(x_53, x_41);
lean_inc(x_1);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_1);
lean_ctor_set(x_55, 1, x_54);
x_56 = 1;
x_57 = lean_usize_add(x_4, x_56);
x_4 = x_57;
x_5 = x_55;
x_9 = x_52;
goto _start;
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_41);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_59 = lean_ctor_get(x_45, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_45, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_61 = x_45;
} else {
 lean_dec_ref(x_45);
 x_61 = lean_box(0);
}
if (lean_is_scalar(x_61)) {
 x_62 = lean_alloc_ctor(1, 2, 0);
} else {
 x_62 = x_61;
}
lean_ctor_set(x_62, 0, x_59);
lean_ctor_set(x_62, 1, x_60);
return x_62;
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_41);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_63 = lean_ctor_get(x_42, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_42, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_65 = x_42;
} else {
 lean_dec_ref(x_42);
 x_65 = lean_box(0);
}
if (lean_is_scalar(x_65)) {
 x_66 = lean_alloc_ctor(1, 2, 0);
} else {
 x_66 = x_65;
}
lean_ctor_set(x_66, 0, x_63);
lean_ctor_set(x_66, 1, x_64);
return x_66;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_InferType_inferForallType_go___spec__10(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_4, x_3);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_5);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_uget(x_2, x_4);
x_13 = !lean_is_exclusive(x_5);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_5, 1);
x_15 = lean_ctor_get(x_5, 0);
lean_dec(x_15);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_16 = l_Lean_Compiler_InferType_inferType(x_12, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_19 = l_Lean_Compiler_InferType_getLevel_x3f(x_17, x_6, x_7, x_8, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_19, 0);
lean_dec(x_22);
x_23 = l_Array_forInUnsafe_loop___at_Lean_Compiler_InferType_inferForallType_go___spec__1___closed__1;
lean_ctor_set(x_5, 0, x_23);
lean_ctor_set(x_19, 0, x_5);
return x_19;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_19, 1);
lean_inc(x_24);
lean_dec(x_19);
x_25 = l_Array_forInUnsafe_loop___at_Lean_Compiler_InferType_inferForallType_go___spec__1___closed__1;
lean_ctor_set(x_5, 0, x_25);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_5);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; size_t x_30; size_t x_31; 
x_27 = lean_ctor_get(x_19, 1);
lean_inc(x_27);
lean_dec(x_19);
x_28 = lean_ctor_get(x_20, 0);
lean_inc(x_28);
lean_dec(x_20);
x_29 = l_Lean_Level_imax___override(x_28, x_14);
lean_inc(x_1);
lean_ctor_set(x_5, 1, x_29);
lean_ctor_set(x_5, 0, x_1);
x_30 = 1;
x_31 = lean_usize_add(x_4, x_30);
x_4 = x_31;
x_9 = x_27;
goto _start;
}
}
else
{
uint8_t x_33; 
lean_free_object(x_5);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_19);
if (x_33 == 0)
{
return x_19;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_19, 0);
x_35 = lean_ctor_get(x_19, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_19);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
uint8_t x_37; 
lean_free_object(x_5);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
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
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_5, 1);
lean_inc(x_41);
lean_dec(x_5);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_42 = l_Lean_Compiler_InferType_inferType(x_12, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_45 = l_Lean_Compiler_InferType_getLevel_x3f(x_43, x_6, x_7, x_8, x_44);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_48 = x_45;
} else {
 lean_dec_ref(x_45);
 x_48 = lean_box(0);
}
x_49 = l_Array_forInUnsafe_loop___at_Lean_Compiler_InferType_inferForallType_go___spec__1___closed__1;
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_41);
if (lean_is_scalar(x_48)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_48;
}
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_47);
return x_51;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; size_t x_56; size_t x_57; 
x_52 = lean_ctor_get(x_45, 1);
lean_inc(x_52);
lean_dec(x_45);
x_53 = lean_ctor_get(x_46, 0);
lean_inc(x_53);
lean_dec(x_46);
x_54 = l_Lean_Level_imax___override(x_53, x_41);
lean_inc(x_1);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_1);
lean_ctor_set(x_55, 1, x_54);
x_56 = 1;
x_57 = lean_usize_add(x_4, x_56);
x_4 = x_57;
x_5 = x_55;
x_9 = x_52;
goto _start;
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_41);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_59 = lean_ctor_get(x_45, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_45, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_61 = x_45;
} else {
 lean_dec_ref(x_45);
 x_61 = lean_box(0);
}
if (lean_is_scalar(x_61)) {
 x_62 = lean_alloc_ctor(1, 2, 0);
} else {
 x_62 = x_61;
}
lean_ctor_set(x_62, 0, x_59);
lean_ctor_set(x_62, 1, x_60);
return x_62;
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_41);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_63 = lean_ctor_get(x_42, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_42, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_65 = x_42;
} else {
 lean_dec_ref(x_42);
 x_65 = lean_box(0);
}
if (lean_is_scalar(x_65)) {
 x_66 = lean_alloc_ctor(1, 2, 0);
} else {
 x_66 = x_65;
}
lean_ctor_set(x_66, 0, x_63);
lean_ctor_set(x_66, 1, x_64);
return x_66;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_InferType_inferForallType_go___spec__11(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_4, x_3);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_5);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_uget(x_2, x_4);
x_13 = !lean_is_exclusive(x_5);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_5, 1);
x_15 = lean_ctor_get(x_5, 0);
lean_dec(x_15);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_16 = l_Lean_Compiler_InferType_inferType(x_12, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_19 = l_Lean_Compiler_InferType_getLevel_x3f(x_17, x_6, x_7, x_8, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_19, 0);
lean_dec(x_22);
x_23 = l_Array_forInUnsafe_loop___at_Lean_Compiler_InferType_inferForallType_go___spec__1___closed__1;
lean_ctor_set(x_5, 0, x_23);
lean_ctor_set(x_19, 0, x_5);
return x_19;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_19, 1);
lean_inc(x_24);
lean_dec(x_19);
x_25 = l_Array_forInUnsafe_loop___at_Lean_Compiler_InferType_inferForallType_go___spec__1___closed__1;
lean_ctor_set(x_5, 0, x_25);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_5);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; size_t x_30; size_t x_31; 
x_27 = lean_ctor_get(x_19, 1);
lean_inc(x_27);
lean_dec(x_19);
x_28 = lean_ctor_get(x_20, 0);
lean_inc(x_28);
lean_dec(x_20);
x_29 = l_Lean_Level_imax___override(x_28, x_14);
lean_inc(x_1);
lean_ctor_set(x_5, 1, x_29);
lean_ctor_set(x_5, 0, x_1);
x_30 = 1;
x_31 = lean_usize_add(x_4, x_30);
x_4 = x_31;
x_9 = x_27;
goto _start;
}
}
else
{
uint8_t x_33; 
lean_free_object(x_5);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_19);
if (x_33 == 0)
{
return x_19;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_19, 0);
x_35 = lean_ctor_get(x_19, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_19);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
uint8_t x_37; 
lean_free_object(x_5);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
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
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_5, 1);
lean_inc(x_41);
lean_dec(x_5);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_42 = l_Lean_Compiler_InferType_inferType(x_12, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_45 = l_Lean_Compiler_InferType_getLevel_x3f(x_43, x_6, x_7, x_8, x_44);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_48 = x_45;
} else {
 lean_dec_ref(x_45);
 x_48 = lean_box(0);
}
x_49 = l_Array_forInUnsafe_loop___at_Lean_Compiler_InferType_inferForallType_go___spec__1___closed__1;
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_41);
if (lean_is_scalar(x_48)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_48;
}
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_47);
return x_51;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; size_t x_56; size_t x_57; 
x_52 = lean_ctor_get(x_45, 1);
lean_inc(x_52);
lean_dec(x_45);
x_53 = lean_ctor_get(x_46, 0);
lean_inc(x_53);
lean_dec(x_46);
x_54 = l_Lean_Level_imax___override(x_53, x_41);
lean_inc(x_1);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_1);
lean_ctor_set(x_55, 1, x_54);
x_56 = 1;
x_57 = lean_usize_add(x_4, x_56);
x_4 = x_57;
x_5 = x_55;
x_9 = x_52;
goto _start;
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_41);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_59 = lean_ctor_get(x_45, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_45, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_61 = x_45;
} else {
 lean_dec_ref(x_45);
 x_61 = lean_box(0);
}
if (lean_is_scalar(x_61)) {
 x_62 = lean_alloc_ctor(1, 2, 0);
} else {
 x_62 = x_61;
}
lean_ctor_set(x_62, 0, x_59);
lean_ctor_set(x_62, 1, x_60);
return x_62;
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_41);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_63 = lean_ctor_get(x_42, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_42, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_65 = x_42;
} else {
 lean_dec_ref(x_42);
 x_65 = lean_box(0);
}
if (lean_is_scalar(x_65)) {
 x_66 = lean_alloc_ctor(1, 2, 0);
} else {
 x_66 = x_65;
}
lean_ctor_set(x_66, 0, x_63);
lean_ctor_set(x_66, 1, x_64);
return x_66;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_InferType_inferForallType_go___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = l_Lean_Level_normalize(x_1);
x_8 = l_Lean_Expr_sort___override(x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_InferType_inferForallType_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_expr_instantiate_rev(x_1, x_2);
lean_dec(x_1);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_8 = l_Lean_Compiler_InferType_getLevel_x3f(x_7, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_8, 0);
lean_dec(x_11);
x_12 = l_Lean_Compiler_anyTypeExpr;
lean_ctor_set(x_8, 0, x_12);
return x_8;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_dec(x_8);
x_14 = l_Lean_Compiler_anyTypeExpr;
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; size_t x_21; size_t x_22; lean_object* x_23; 
x_16 = lean_ctor_get(x_8, 1);
lean_inc(x_16);
lean_dec(x_8);
x_17 = lean_ctor_get(x_9, 0);
lean_inc(x_17);
lean_dec(x_9);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
x_20 = lean_array_get_size(x_2);
x_21 = lean_usize_of_nat(x_20);
lean_dec(x_20);
x_22 = 0;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_23 = l_Array_forInUnsafe_loop___at_Lean_Compiler_InferType_inferForallType_go___spec__1(x_18, x_2, x_21, x_22, x_19, x_3, x_4, x_5, x_16);
lean_dec(x_2);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
x_28 = lean_box(0);
x_29 = l_Lean_Compiler_InferType_inferForallType_go___lambda__1(x_27, x_28, x_3, x_4, x_5, x_26);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_29;
}
else
{
uint8_t x_30; 
lean_dec(x_24);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_30 = !lean_is_exclusive(x_23);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_23, 0);
lean_dec(x_31);
x_32 = lean_ctor_get(x_25, 0);
lean_inc(x_32);
lean_dec(x_25);
lean_ctor_set(x_23, 0, x_32);
return x_23;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_23, 1);
lean_inc(x_33);
lean_dec(x_23);
x_34 = lean_ctor_get(x_25, 0);
lean_inc(x_34);
lean_dec(x_25);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
return x_35;
}
}
}
else
{
uint8_t x_36; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_36 = !lean_is_exclusive(x_23);
if (x_36 == 0)
{
return x_23;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_23, 0);
x_38 = lean_ctor_get(x_23, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_23);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
else
{
uint8_t x_40; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_40 = !lean_is_exclusive(x_8);
if (x_40 == 0)
{
return x_8;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_8, 0);
x_42 = lean_ctor_get(x_8, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_8);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
case 1:
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_expr_instantiate_rev(x_1, x_2);
lean_dec(x_1);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_45 = l_Lean_Compiler_InferType_getLevel_x3f(x_44, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
if (lean_obj_tag(x_46) == 0)
{
uint8_t x_47; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_47 = !lean_is_exclusive(x_45);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_45, 0);
lean_dec(x_48);
x_49 = l_Lean_Compiler_anyTypeExpr;
lean_ctor_set(x_45, 0, x_49);
return x_45;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_45, 1);
lean_inc(x_50);
lean_dec(x_45);
x_51 = l_Lean_Compiler_anyTypeExpr;
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_50);
return x_52;
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; size_t x_58; size_t x_59; lean_object* x_60; 
x_53 = lean_ctor_get(x_45, 1);
lean_inc(x_53);
lean_dec(x_45);
x_54 = lean_ctor_get(x_46, 0);
lean_inc(x_54);
lean_dec(x_46);
x_55 = lean_box(0);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_54);
x_57 = lean_array_get_size(x_2);
x_58 = lean_usize_of_nat(x_57);
lean_dec(x_57);
x_59 = 0;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_60 = l_Array_forInUnsafe_loop___at_Lean_Compiler_InferType_inferForallType_go___spec__2(x_55, x_2, x_58, x_59, x_56, x_3, x_4, x_5, x_53);
lean_dec(x_2);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_63 = lean_ctor_get(x_60, 1);
lean_inc(x_63);
lean_dec(x_60);
x_64 = lean_ctor_get(x_61, 1);
lean_inc(x_64);
lean_dec(x_61);
x_65 = lean_box(0);
x_66 = l_Lean_Compiler_InferType_inferForallType_go___lambda__1(x_64, x_65, x_3, x_4, x_5, x_63);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_66;
}
else
{
uint8_t x_67; 
lean_dec(x_61);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_67 = !lean_is_exclusive(x_60);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_60, 0);
lean_dec(x_68);
x_69 = lean_ctor_get(x_62, 0);
lean_inc(x_69);
lean_dec(x_62);
lean_ctor_set(x_60, 0, x_69);
return x_60;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_60, 1);
lean_inc(x_70);
lean_dec(x_60);
x_71 = lean_ctor_get(x_62, 0);
lean_inc(x_71);
lean_dec(x_62);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_70);
return x_72;
}
}
}
else
{
uint8_t x_73; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_73 = !lean_is_exclusive(x_60);
if (x_73 == 0)
{
return x_60;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_60, 0);
x_75 = lean_ctor_get(x_60, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_60);
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
uint8_t x_77; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_77 = !lean_is_exclusive(x_45);
if (x_77 == 0)
{
return x_45;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_45, 0);
x_79 = lean_ctor_get(x_45, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_45);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
case 2:
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_expr_instantiate_rev(x_1, x_2);
lean_dec(x_1);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_82 = l_Lean_Compiler_InferType_getLevel_x3f(x_81, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
if (lean_obj_tag(x_83) == 0)
{
uint8_t x_84; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_84 = !lean_is_exclusive(x_82);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; 
x_85 = lean_ctor_get(x_82, 0);
lean_dec(x_85);
x_86 = l_Lean_Compiler_anyTypeExpr;
lean_ctor_set(x_82, 0, x_86);
return x_82;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_82, 1);
lean_inc(x_87);
lean_dec(x_82);
x_88 = l_Lean_Compiler_anyTypeExpr;
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_87);
return x_89;
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; size_t x_95; size_t x_96; lean_object* x_97; 
x_90 = lean_ctor_get(x_82, 1);
lean_inc(x_90);
lean_dec(x_82);
x_91 = lean_ctor_get(x_83, 0);
lean_inc(x_91);
lean_dec(x_83);
x_92 = lean_box(0);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_91);
x_94 = lean_array_get_size(x_2);
x_95 = lean_usize_of_nat(x_94);
lean_dec(x_94);
x_96 = 0;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_97 = l_Array_forInUnsafe_loop___at_Lean_Compiler_InferType_inferForallType_go___spec__3(x_92, x_2, x_95, x_96, x_93, x_3, x_4, x_5, x_90);
lean_dec(x_2);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; lean_object* x_99; 
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_100 = lean_ctor_get(x_97, 1);
lean_inc(x_100);
lean_dec(x_97);
x_101 = lean_ctor_get(x_98, 1);
lean_inc(x_101);
lean_dec(x_98);
x_102 = lean_box(0);
x_103 = l_Lean_Compiler_InferType_inferForallType_go___lambda__1(x_101, x_102, x_3, x_4, x_5, x_100);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_103;
}
else
{
uint8_t x_104; 
lean_dec(x_98);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_104 = !lean_is_exclusive(x_97);
if (x_104 == 0)
{
lean_object* x_105; lean_object* x_106; 
x_105 = lean_ctor_get(x_97, 0);
lean_dec(x_105);
x_106 = lean_ctor_get(x_99, 0);
lean_inc(x_106);
lean_dec(x_99);
lean_ctor_set(x_97, 0, x_106);
return x_97;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_97, 1);
lean_inc(x_107);
lean_dec(x_97);
x_108 = lean_ctor_get(x_99, 0);
lean_inc(x_108);
lean_dec(x_99);
x_109 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_107);
return x_109;
}
}
}
else
{
uint8_t x_110; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_110 = !lean_is_exclusive(x_97);
if (x_110 == 0)
{
return x_97;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_97, 0);
x_112 = lean_ctor_get(x_97, 1);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_97);
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_112);
return x_113;
}
}
}
}
else
{
uint8_t x_114; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_114 = !lean_is_exclusive(x_82);
if (x_114 == 0)
{
return x_82;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_82, 0);
x_116 = lean_ctor_get(x_82, 1);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_82);
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
return x_117;
}
}
}
case 3:
{
lean_object* x_118; lean_object* x_119; 
x_118 = lean_expr_instantiate_rev(x_1, x_2);
lean_dec(x_1);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_119 = l_Lean_Compiler_InferType_getLevel_x3f(x_118, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; 
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
if (lean_obj_tag(x_120) == 0)
{
uint8_t x_121; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_121 = !lean_is_exclusive(x_119);
if (x_121 == 0)
{
lean_object* x_122; lean_object* x_123; 
x_122 = lean_ctor_get(x_119, 0);
lean_dec(x_122);
x_123 = l_Lean_Compiler_anyTypeExpr;
lean_ctor_set(x_119, 0, x_123);
return x_119;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_124 = lean_ctor_get(x_119, 1);
lean_inc(x_124);
lean_dec(x_119);
x_125 = l_Lean_Compiler_anyTypeExpr;
x_126 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_126, 0, x_125);
lean_ctor_set(x_126, 1, x_124);
return x_126;
}
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; size_t x_132; size_t x_133; lean_object* x_134; 
x_127 = lean_ctor_get(x_119, 1);
lean_inc(x_127);
lean_dec(x_119);
x_128 = lean_ctor_get(x_120, 0);
lean_inc(x_128);
lean_dec(x_120);
x_129 = lean_box(0);
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_128);
x_131 = lean_array_get_size(x_2);
x_132 = lean_usize_of_nat(x_131);
lean_dec(x_131);
x_133 = 0;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_134 = l_Array_forInUnsafe_loop___at_Lean_Compiler_InferType_inferForallType_go___spec__4(x_129, x_2, x_132, x_133, x_130, x_3, x_4, x_5, x_127);
lean_dec(x_2);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_135; lean_object* x_136; 
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
if (lean_obj_tag(x_136) == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_137 = lean_ctor_get(x_134, 1);
lean_inc(x_137);
lean_dec(x_134);
x_138 = lean_ctor_get(x_135, 1);
lean_inc(x_138);
lean_dec(x_135);
x_139 = lean_box(0);
x_140 = l_Lean_Compiler_InferType_inferForallType_go___lambda__1(x_138, x_139, x_3, x_4, x_5, x_137);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_140;
}
else
{
uint8_t x_141; 
lean_dec(x_135);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_141 = !lean_is_exclusive(x_134);
if (x_141 == 0)
{
lean_object* x_142; lean_object* x_143; 
x_142 = lean_ctor_get(x_134, 0);
lean_dec(x_142);
x_143 = lean_ctor_get(x_136, 0);
lean_inc(x_143);
lean_dec(x_136);
lean_ctor_set(x_134, 0, x_143);
return x_134;
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_144 = lean_ctor_get(x_134, 1);
lean_inc(x_144);
lean_dec(x_134);
x_145 = lean_ctor_get(x_136, 0);
lean_inc(x_145);
lean_dec(x_136);
x_146 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_146, 0, x_145);
lean_ctor_set(x_146, 1, x_144);
return x_146;
}
}
}
else
{
uint8_t x_147; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_147 = !lean_is_exclusive(x_134);
if (x_147 == 0)
{
return x_134;
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_148 = lean_ctor_get(x_134, 0);
x_149 = lean_ctor_get(x_134, 1);
lean_inc(x_149);
lean_inc(x_148);
lean_dec(x_134);
x_150 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_150, 0, x_148);
lean_ctor_set(x_150, 1, x_149);
return x_150;
}
}
}
}
else
{
uint8_t x_151; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_151 = !lean_is_exclusive(x_119);
if (x_151 == 0)
{
return x_119;
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_152 = lean_ctor_get(x_119, 0);
x_153 = lean_ctor_get(x_119, 1);
lean_inc(x_153);
lean_inc(x_152);
lean_dec(x_119);
x_154 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_154, 0, x_152);
lean_ctor_set(x_154, 1, x_153);
return x_154;
}
}
}
case 4:
{
lean_object* x_155; lean_object* x_156; 
x_155 = lean_expr_instantiate_rev(x_1, x_2);
lean_dec(x_1);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_156 = l_Lean_Compiler_InferType_getLevel_x3f(x_155, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_156) == 0)
{
lean_object* x_157; 
x_157 = lean_ctor_get(x_156, 0);
lean_inc(x_157);
if (lean_obj_tag(x_157) == 0)
{
uint8_t x_158; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_158 = !lean_is_exclusive(x_156);
if (x_158 == 0)
{
lean_object* x_159; lean_object* x_160; 
x_159 = lean_ctor_get(x_156, 0);
lean_dec(x_159);
x_160 = l_Lean_Compiler_anyTypeExpr;
lean_ctor_set(x_156, 0, x_160);
return x_156;
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_161 = lean_ctor_get(x_156, 1);
lean_inc(x_161);
lean_dec(x_156);
x_162 = l_Lean_Compiler_anyTypeExpr;
x_163 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_163, 0, x_162);
lean_ctor_set(x_163, 1, x_161);
return x_163;
}
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; size_t x_169; size_t x_170; lean_object* x_171; 
x_164 = lean_ctor_get(x_156, 1);
lean_inc(x_164);
lean_dec(x_156);
x_165 = lean_ctor_get(x_157, 0);
lean_inc(x_165);
lean_dec(x_157);
x_166 = lean_box(0);
x_167 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_167, 0, x_166);
lean_ctor_set(x_167, 1, x_165);
x_168 = lean_array_get_size(x_2);
x_169 = lean_usize_of_nat(x_168);
lean_dec(x_168);
x_170 = 0;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_171 = l_Array_forInUnsafe_loop___at_Lean_Compiler_InferType_inferForallType_go___spec__5(x_166, x_2, x_169, x_170, x_167, x_3, x_4, x_5, x_164);
lean_dec(x_2);
if (lean_obj_tag(x_171) == 0)
{
lean_object* x_172; lean_object* x_173; 
x_172 = lean_ctor_get(x_171, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_172, 0);
lean_inc(x_173);
if (lean_obj_tag(x_173) == 0)
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_174 = lean_ctor_get(x_171, 1);
lean_inc(x_174);
lean_dec(x_171);
x_175 = lean_ctor_get(x_172, 1);
lean_inc(x_175);
lean_dec(x_172);
x_176 = lean_box(0);
x_177 = l_Lean_Compiler_InferType_inferForallType_go___lambda__1(x_175, x_176, x_3, x_4, x_5, x_174);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_177;
}
else
{
uint8_t x_178; 
lean_dec(x_172);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_178 = !lean_is_exclusive(x_171);
if (x_178 == 0)
{
lean_object* x_179; lean_object* x_180; 
x_179 = lean_ctor_get(x_171, 0);
lean_dec(x_179);
x_180 = lean_ctor_get(x_173, 0);
lean_inc(x_180);
lean_dec(x_173);
lean_ctor_set(x_171, 0, x_180);
return x_171;
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_181 = lean_ctor_get(x_171, 1);
lean_inc(x_181);
lean_dec(x_171);
x_182 = lean_ctor_get(x_173, 0);
lean_inc(x_182);
lean_dec(x_173);
x_183 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_183, 0, x_182);
lean_ctor_set(x_183, 1, x_181);
return x_183;
}
}
}
else
{
uint8_t x_184; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_184 = !lean_is_exclusive(x_171);
if (x_184 == 0)
{
return x_171;
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_185 = lean_ctor_get(x_171, 0);
x_186 = lean_ctor_get(x_171, 1);
lean_inc(x_186);
lean_inc(x_185);
lean_dec(x_171);
x_187 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_187, 0, x_185);
lean_ctor_set(x_187, 1, x_186);
return x_187;
}
}
}
}
else
{
uint8_t x_188; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_188 = !lean_is_exclusive(x_156);
if (x_188 == 0)
{
return x_156;
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_189 = lean_ctor_get(x_156, 0);
x_190 = lean_ctor_get(x_156, 1);
lean_inc(x_190);
lean_inc(x_189);
lean_dec(x_156);
x_191 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_191, 0, x_189);
lean_ctor_set(x_191, 1, x_190);
return x_191;
}
}
}
case 5:
{
lean_object* x_192; lean_object* x_193; 
x_192 = lean_expr_instantiate_rev(x_1, x_2);
lean_dec(x_1);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_193 = l_Lean_Compiler_InferType_getLevel_x3f(x_192, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_193) == 0)
{
lean_object* x_194; 
x_194 = lean_ctor_get(x_193, 0);
lean_inc(x_194);
if (lean_obj_tag(x_194) == 0)
{
uint8_t x_195; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_195 = !lean_is_exclusive(x_193);
if (x_195 == 0)
{
lean_object* x_196; lean_object* x_197; 
x_196 = lean_ctor_get(x_193, 0);
lean_dec(x_196);
x_197 = l_Lean_Compiler_anyTypeExpr;
lean_ctor_set(x_193, 0, x_197);
return x_193;
}
else
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_198 = lean_ctor_get(x_193, 1);
lean_inc(x_198);
lean_dec(x_193);
x_199 = l_Lean_Compiler_anyTypeExpr;
x_200 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_200, 0, x_199);
lean_ctor_set(x_200, 1, x_198);
return x_200;
}
}
else
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; size_t x_206; size_t x_207; lean_object* x_208; 
x_201 = lean_ctor_get(x_193, 1);
lean_inc(x_201);
lean_dec(x_193);
x_202 = lean_ctor_get(x_194, 0);
lean_inc(x_202);
lean_dec(x_194);
x_203 = lean_box(0);
x_204 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_204, 0, x_203);
lean_ctor_set(x_204, 1, x_202);
x_205 = lean_array_get_size(x_2);
x_206 = lean_usize_of_nat(x_205);
lean_dec(x_205);
x_207 = 0;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_208 = l_Array_forInUnsafe_loop___at_Lean_Compiler_InferType_inferForallType_go___spec__6(x_203, x_2, x_206, x_207, x_204, x_3, x_4, x_5, x_201);
lean_dec(x_2);
if (lean_obj_tag(x_208) == 0)
{
lean_object* x_209; lean_object* x_210; 
x_209 = lean_ctor_get(x_208, 0);
lean_inc(x_209);
x_210 = lean_ctor_get(x_209, 0);
lean_inc(x_210);
if (lean_obj_tag(x_210) == 0)
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; 
x_211 = lean_ctor_get(x_208, 1);
lean_inc(x_211);
lean_dec(x_208);
x_212 = lean_ctor_get(x_209, 1);
lean_inc(x_212);
lean_dec(x_209);
x_213 = lean_box(0);
x_214 = l_Lean_Compiler_InferType_inferForallType_go___lambda__1(x_212, x_213, x_3, x_4, x_5, x_211);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_214;
}
else
{
uint8_t x_215; 
lean_dec(x_209);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_215 = !lean_is_exclusive(x_208);
if (x_215 == 0)
{
lean_object* x_216; lean_object* x_217; 
x_216 = lean_ctor_get(x_208, 0);
lean_dec(x_216);
x_217 = lean_ctor_get(x_210, 0);
lean_inc(x_217);
lean_dec(x_210);
lean_ctor_set(x_208, 0, x_217);
return x_208;
}
else
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; 
x_218 = lean_ctor_get(x_208, 1);
lean_inc(x_218);
lean_dec(x_208);
x_219 = lean_ctor_get(x_210, 0);
lean_inc(x_219);
lean_dec(x_210);
x_220 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_220, 0, x_219);
lean_ctor_set(x_220, 1, x_218);
return x_220;
}
}
}
else
{
uint8_t x_221; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_221 = !lean_is_exclusive(x_208);
if (x_221 == 0)
{
return x_208;
}
else
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; 
x_222 = lean_ctor_get(x_208, 0);
x_223 = lean_ctor_get(x_208, 1);
lean_inc(x_223);
lean_inc(x_222);
lean_dec(x_208);
x_224 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_224, 0, x_222);
lean_ctor_set(x_224, 1, x_223);
return x_224;
}
}
}
}
else
{
uint8_t x_225; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_225 = !lean_is_exclusive(x_193);
if (x_225 == 0)
{
return x_193;
}
else
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; 
x_226 = lean_ctor_get(x_193, 0);
x_227 = lean_ctor_get(x_193, 1);
lean_inc(x_227);
lean_inc(x_226);
lean_dec(x_193);
x_228 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_228, 0, x_226);
lean_ctor_set(x_228, 1, x_227);
return x_228;
}
}
}
case 6:
{
lean_object* x_229; lean_object* x_230; 
x_229 = lean_expr_instantiate_rev(x_1, x_2);
lean_dec(x_1);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_230 = l_Lean_Compiler_InferType_getLevel_x3f(x_229, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_230) == 0)
{
lean_object* x_231; 
x_231 = lean_ctor_get(x_230, 0);
lean_inc(x_231);
if (lean_obj_tag(x_231) == 0)
{
uint8_t x_232; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_232 = !lean_is_exclusive(x_230);
if (x_232 == 0)
{
lean_object* x_233; lean_object* x_234; 
x_233 = lean_ctor_get(x_230, 0);
lean_dec(x_233);
x_234 = l_Lean_Compiler_anyTypeExpr;
lean_ctor_set(x_230, 0, x_234);
return x_230;
}
else
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; 
x_235 = lean_ctor_get(x_230, 1);
lean_inc(x_235);
lean_dec(x_230);
x_236 = l_Lean_Compiler_anyTypeExpr;
x_237 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_237, 0, x_236);
lean_ctor_set(x_237, 1, x_235);
return x_237;
}
}
else
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; size_t x_243; size_t x_244; lean_object* x_245; 
x_238 = lean_ctor_get(x_230, 1);
lean_inc(x_238);
lean_dec(x_230);
x_239 = lean_ctor_get(x_231, 0);
lean_inc(x_239);
lean_dec(x_231);
x_240 = lean_box(0);
x_241 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_241, 0, x_240);
lean_ctor_set(x_241, 1, x_239);
x_242 = lean_array_get_size(x_2);
x_243 = lean_usize_of_nat(x_242);
lean_dec(x_242);
x_244 = 0;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_245 = l_Array_forInUnsafe_loop___at_Lean_Compiler_InferType_inferForallType_go___spec__7(x_240, x_2, x_243, x_244, x_241, x_3, x_4, x_5, x_238);
lean_dec(x_2);
if (lean_obj_tag(x_245) == 0)
{
lean_object* x_246; lean_object* x_247; 
x_246 = lean_ctor_get(x_245, 0);
lean_inc(x_246);
x_247 = lean_ctor_get(x_246, 0);
lean_inc(x_247);
if (lean_obj_tag(x_247) == 0)
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; 
x_248 = lean_ctor_get(x_245, 1);
lean_inc(x_248);
lean_dec(x_245);
x_249 = lean_ctor_get(x_246, 1);
lean_inc(x_249);
lean_dec(x_246);
x_250 = lean_box(0);
x_251 = l_Lean_Compiler_InferType_inferForallType_go___lambda__1(x_249, x_250, x_3, x_4, x_5, x_248);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_251;
}
else
{
uint8_t x_252; 
lean_dec(x_246);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_252 = !lean_is_exclusive(x_245);
if (x_252 == 0)
{
lean_object* x_253; lean_object* x_254; 
x_253 = lean_ctor_get(x_245, 0);
lean_dec(x_253);
x_254 = lean_ctor_get(x_247, 0);
lean_inc(x_254);
lean_dec(x_247);
lean_ctor_set(x_245, 0, x_254);
return x_245;
}
else
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; 
x_255 = lean_ctor_get(x_245, 1);
lean_inc(x_255);
lean_dec(x_245);
x_256 = lean_ctor_get(x_247, 0);
lean_inc(x_256);
lean_dec(x_247);
x_257 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_257, 0, x_256);
lean_ctor_set(x_257, 1, x_255);
return x_257;
}
}
}
else
{
uint8_t x_258; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_258 = !lean_is_exclusive(x_245);
if (x_258 == 0)
{
return x_245;
}
else
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; 
x_259 = lean_ctor_get(x_245, 0);
x_260 = lean_ctor_get(x_245, 1);
lean_inc(x_260);
lean_inc(x_259);
lean_dec(x_245);
x_261 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_261, 0, x_259);
lean_ctor_set(x_261, 1, x_260);
return x_261;
}
}
}
}
else
{
uint8_t x_262; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_262 = !lean_is_exclusive(x_230);
if (x_262 == 0)
{
return x_230;
}
else
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; 
x_263 = lean_ctor_get(x_230, 0);
x_264 = lean_ctor_get(x_230, 1);
lean_inc(x_264);
lean_inc(x_263);
lean_dec(x_230);
x_265 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_265, 0, x_263);
lean_ctor_set(x_265, 1, x_264);
return x_265;
}
}
}
case 7:
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; uint8_t x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; 
x_266 = lean_ctor_get(x_1, 0);
lean_inc(x_266);
x_267 = lean_ctor_get(x_1, 1);
lean_inc(x_267);
x_268 = lean_ctor_get(x_1, 2);
lean_inc(x_268);
x_269 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
lean_dec(x_1);
x_270 = lean_expr_instantiate_rev(x_267, x_2);
lean_dec(x_267);
x_271 = l_Lean_mkFreshFVarId___at_Lean_Compiler_InferType_withLocalDecl___spec__1(x_3, x_4, x_5, x_6);
x_272 = lean_ctor_get(x_271, 0);
lean_inc(x_272);
x_273 = lean_ctor_get(x_271, 1);
lean_inc(x_273);
lean_dec(x_271);
lean_inc(x_272);
x_274 = l_Lean_Expr_fvar___override(x_272);
x_275 = lean_local_ctx_mk_local_decl(x_3, x_272, x_266, x_270, x_269);
x_276 = lean_array_push(x_2, x_274);
x_1 = x_268;
x_2 = x_276;
x_3 = x_275;
x_6 = x_273;
goto _start;
}
case 8:
{
lean_object* x_278; lean_object* x_279; 
x_278 = lean_expr_instantiate_rev(x_1, x_2);
lean_dec(x_1);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_279 = l_Lean_Compiler_InferType_getLevel_x3f(x_278, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_279) == 0)
{
lean_object* x_280; 
x_280 = lean_ctor_get(x_279, 0);
lean_inc(x_280);
if (lean_obj_tag(x_280) == 0)
{
uint8_t x_281; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_281 = !lean_is_exclusive(x_279);
if (x_281 == 0)
{
lean_object* x_282; lean_object* x_283; 
x_282 = lean_ctor_get(x_279, 0);
lean_dec(x_282);
x_283 = l_Lean_Compiler_anyTypeExpr;
lean_ctor_set(x_279, 0, x_283);
return x_279;
}
else
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; 
x_284 = lean_ctor_get(x_279, 1);
lean_inc(x_284);
lean_dec(x_279);
x_285 = l_Lean_Compiler_anyTypeExpr;
x_286 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_286, 0, x_285);
lean_ctor_set(x_286, 1, x_284);
return x_286;
}
}
else
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; size_t x_292; size_t x_293; lean_object* x_294; 
x_287 = lean_ctor_get(x_279, 1);
lean_inc(x_287);
lean_dec(x_279);
x_288 = lean_ctor_get(x_280, 0);
lean_inc(x_288);
lean_dec(x_280);
x_289 = lean_box(0);
x_290 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_290, 0, x_289);
lean_ctor_set(x_290, 1, x_288);
x_291 = lean_array_get_size(x_2);
x_292 = lean_usize_of_nat(x_291);
lean_dec(x_291);
x_293 = 0;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_294 = l_Array_forInUnsafe_loop___at_Lean_Compiler_InferType_inferForallType_go___spec__8(x_289, x_2, x_292, x_293, x_290, x_3, x_4, x_5, x_287);
lean_dec(x_2);
if (lean_obj_tag(x_294) == 0)
{
lean_object* x_295; lean_object* x_296; 
x_295 = lean_ctor_get(x_294, 0);
lean_inc(x_295);
x_296 = lean_ctor_get(x_295, 0);
lean_inc(x_296);
if (lean_obj_tag(x_296) == 0)
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; 
x_297 = lean_ctor_get(x_294, 1);
lean_inc(x_297);
lean_dec(x_294);
x_298 = lean_ctor_get(x_295, 1);
lean_inc(x_298);
lean_dec(x_295);
x_299 = lean_box(0);
x_300 = l_Lean_Compiler_InferType_inferForallType_go___lambda__1(x_298, x_299, x_3, x_4, x_5, x_297);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_300;
}
else
{
uint8_t x_301; 
lean_dec(x_295);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_301 = !lean_is_exclusive(x_294);
if (x_301 == 0)
{
lean_object* x_302; lean_object* x_303; 
x_302 = lean_ctor_get(x_294, 0);
lean_dec(x_302);
x_303 = lean_ctor_get(x_296, 0);
lean_inc(x_303);
lean_dec(x_296);
lean_ctor_set(x_294, 0, x_303);
return x_294;
}
else
{
lean_object* x_304; lean_object* x_305; lean_object* x_306; 
x_304 = lean_ctor_get(x_294, 1);
lean_inc(x_304);
lean_dec(x_294);
x_305 = lean_ctor_get(x_296, 0);
lean_inc(x_305);
lean_dec(x_296);
x_306 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_306, 0, x_305);
lean_ctor_set(x_306, 1, x_304);
return x_306;
}
}
}
else
{
uint8_t x_307; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_307 = !lean_is_exclusive(x_294);
if (x_307 == 0)
{
return x_294;
}
else
{
lean_object* x_308; lean_object* x_309; lean_object* x_310; 
x_308 = lean_ctor_get(x_294, 0);
x_309 = lean_ctor_get(x_294, 1);
lean_inc(x_309);
lean_inc(x_308);
lean_dec(x_294);
x_310 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_310, 0, x_308);
lean_ctor_set(x_310, 1, x_309);
return x_310;
}
}
}
}
else
{
uint8_t x_311; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_311 = !lean_is_exclusive(x_279);
if (x_311 == 0)
{
return x_279;
}
else
{
lean_object* x_312; lean_object* x_313; lean_object* x_314; 
x_312 = lean_ctor_get(x_279, 0);
x_313 = lean_ctor_get(x_279, 1);
lean_inc(x_313);
lean_inc(x_312);
lean_dec(x_279);
x_314 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_314, 0, x_312);
lean_ctor_set(x_314, 1, x_313);
return x_314;
}
}
}
case 9:
{
lean_object* x_315; lean_object* x_316; 
x_315 = lean_expr_instantiate_rev(x_1, x_2);
lean_dec(x_1);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_316 = l_Lean_Compiler_InferType_getLevel_x3f(x_315, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_316) == 0)
{
lean_object* x_317; 
x_317 = lean_ctor_get(x_316, 0);
lean_inc(x_317);
if (lean_obj_tag(x_317) == 0)
{
uint8_t x_318; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_318 = !lean_is_exclusive(x_316);
if (x_318 == 0)
{
lean_object* x_319; lean_object* x_320; 
x_319 = lean_ctor_get(x_316, 0);
lean_dec(x_319);
x_320 = l_Lean_Compiler_anyTypeExpr;
lean_ctor_set(x_316, 0, x_320);
return x_316;
}
else
{
lean_object* x_321; lean_object* x_322; lean_object* x_323; 
x_321 = lean_ctor_get(x_316, 1);
lean_inc(x_321);
lean_dec(x_316);
x_322 = l_Lean_Compiler_anyTypeExpr;
x_323 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_323, 0, x_322);
lean_ctor_set(x_323, 1, x_321);
return x_323;
}
}
else
{
lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; size_t x_329; size_t x_330; lean_object* x_331; 
x_324 = lean_ctor_get(x_316, 1);
lean_inc(x_324);
lean_dec(x_316);
x_325 = lean_ctor_get(x_317, 0);
lean_inc(x_325);
lean_dec(x_317);
x_326 = lean_box(0);
x_327 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_327, 0, x_326);
lean_ctor_set(x_327, 1, x_325);
x_328 = lean_array_get_size(x_2);
x_329 = lean_usize_of_nat(x_328);
lean_dec(x_328);
x_330 = 0;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_331 = l_Array_forInUnsafe_loop___at_Lean_Compiler_InferType_inferForallType_go___spec__9(x_326, x_2, x_329, x_330, x_327, x_3, x_4, x_5, x_324);
lean_dec(x_2);
if (lean_obj_tag(x_331) == 0)
{
lean_object* x_332; lean_object* x_333; 
x_332 = lean_ctor_get(x_331, 0);
lean_inc(x_332);
x_333 = lean_ctor_get(x_332, 0);
lean_inc(x_333);
if (lean_obj_tag(x_333) == 0)
{
lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; 
x_334 = lean_ctor_get(x_331, 1);
lean_inc(x_334);
lean_dec(x_331);
x_335 = lean_ctor_get(x_332, 1);
lean_inc(x_335);
lean_dec(x_332);
x_336 = lean_box(0);
x_337 = l_Lean_Compiler_InferType_inferForallType_go___lambda__1(x_335, x_336, x_3, x_4, x_5, x_334);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_337;
}
else
{
uint8_t x_338; 
lean_dec(x_332);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_338 = !lean_is_exclusive(x_331);
if (x_338 == 0)
{
lean_object* x_339; lean_object* x_340; 
x_339 = lean_ctor_get(x_331, 0);
lean_dec(x_339);
x_340 = lean_ctor_get(x_333, 0);
lean_inc(x_340);
lean_dec(x_333);
lean_ctor_set(x_331, 0, x_340);
return x_331;
}
else
{
lean_object* x_341; lean_object* x_342; lean_object* x_343; 
x_341 = lean_ctor_get(x_331, 1);
lean_inc(x_341);
lean_dec(x_331);
x_342 = lean_ctor_get(x_333, 0);
lean_inc(x_342);
lean_dec(x_333);
x_343 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_343, 0, x_342);
lean_ctor_set(x_343, 1, x_341);
return x_343;
}
}
}
else
{
uint8_t x_344; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_344 = !lean_is_exclusive(x_331);
if (x_344 == 0)
{
return x_331;
}
else
{
lean_object* x_345; lean_object* x_346; lean_object* x_347; 
x_345 = lean_ctor_get(x_331, 0);
x_346 = lean_ctor_get(x_331, 1);
lean_inc(x_346);
lean_inc(x_345);
lean_dec(x_331);
x_347 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_347, 0, x_345);
lean_ctor_set(x_347, 1, x_346);
return x_347;
}
}
}
}
else
{
uint8_t x_348; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_348 = !lean_is_exclusive(x_316);
if (x_348 == 0)
{
return x_316;
}
else
{
lean_object* x_349; lean_object* x_350; lean_object* x_351; 
x_349 = lean_ctor_get(x_316, 0);
x_350 = lean_ctor_get(x_316, 1);
lean_inc(x_350);
lean_inc(x_349);
lean_dec(x_316);
x_351 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_351, 0, x_349);
lean_ctor_set(x_351, 1, x_350);
return x_351;
}
}
}
case 10:
{
lean_object* x_352; lean_object* x_353; 
x_352 = lean_expr_instantiate_rev(x_1, x_2);
lean_dec(x_1);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_353 = l_Lean_Compiler_InferType_getLevel_x3f(x_352, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_353) == 0)
{
lean_object* x_354; 
x_354 = lean_ctor_get(x_353, 0);
lean_inc(x_354);
if (lean_obj_tag(x_354) == 0)
{
uint8_t x_355; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_355 = !lean_is_exclusive(x_353);
if (x_355 == 0)
{
lean_object* x_356; lean_object* x_357; 
x_356 = lean_ctor_get(x_353, 0);
lean_dec(x_356);
x_357 = l_Lean_Compiler_anyTypeExpr;
lean_ctor_set(x_353, 0, x_357);
return x_353;
}
else
{
lean_object* x_358; lean_object* x_359; lean_object* x_360; 
x_358 = lean_ctor_get(x_353, 1);
lean_inc(x_358);
lean_dec(x_353);
x_359 = l_Lean_Compiler_anyTypeExpr;
x_360 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_360, 0, x_359);
lean_ctor_set(x_360, 1, x_358);
return x_360;
}
}
else
{
lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; size_t x_366; size_t x_367; lean_object* x_368; 
x_361 = lean_ctor_get(x_353, 1);
lean_inc(x_361);
lean_dec(x_353);
x_362 = lean_ctor_get(x_354, 0);
lean_inc(x_362);
lean_dec(x_354);
x_363 = lean_box(0);
x_364 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_364, 0, x_363);
lean_ctor_set(x_364, 1, x_362);
x_365 = lean_array_get_size(x_2);
x_366 = lean_usize_of_nat(x_365);
lean_dec(x_365);
x_367 = 0;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_368 = l_Array_forInUnsafe_loop___at_Lean_Compiler_InferType_inferForallType_go___spec__10(x_363, x_2, x_366, x_367, x_364, x_3, x_4, x_5, x_361);
lean_dec(x_2);
if (lean_obj_tag(x_368) == 0)
{
lean_object* x_369; lean_object* x_370; 
x_369 = lean_ctor_get(x_368, 0);
lean_inc(x_369);
x_370 = lean_ctor_get(x_369, 0);
lean_inc(x_370);
if (lean_obj_tag(x_370) == 0)
{
lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; 
x_371 = lean_ctor_get(x_368, 1);
lean_inc(x_371);
lean_dec(x_368);
x_372 = lean_ctor_get(x_369, 1);
lean_inc(x_372);
lean_dec(x_369);
x_373 = lean_box(0);
x_374 = l_Lean_Compiler_InferType_inferForallType_go___lambda__1(x_372, x_373, x_3, x_4, x_5, x_371);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_374;
}
else
{
uint8_t x_375; 
lean_dec(x_369);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_375 = !lean_is_exclusive(x_368);
if (x_375 == 0)
{
lean_object* x_376; lean_object* x_377; 
x_376 = lean_ctor_get(x_368, 0);
lean_dec(x_376);
x_377 = lean_ctor_get(x_370, 0);
lean_inc(x_377);
lean_dec(x_370);
lean_ctor_set(x_368, 0, x_377);
return x_368;
}
else
{
lean_object* x_378; lean_object* x_379; lean_object* x_380; 
x_378 = lean_ctor_get(x_368, 1);
lean_inc(x_378);
lean_dec(x_368);
x_379 = lean_ctor_get(x_370, 0);
lean_inc(x_379);
lean_dec(x_370);
x_380 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_380, 0, x_379);
lean_ctor_set(x_380, 1, x_378);
return x_380;
}
}
}
else
{
uint8_t x_381; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_381 = !lean_is_exclusive(x_368);
if (x_381 == 0)
{
return x_368;
}
else
{
lean_object* x_382; lean_object* x_383; lean_object* x_384; 
x_382 = lean_ctor_get(x_368, 0);
x_383 = lean_ctor_get(x_368, 1);
lean_inc(x_383);
lean_inc(x_382);
lean_dec(x_368);
x_384 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_384, 0, x_382);
lean_ctor_set(x_384, 1, x_383);
return x_384;
}
}
}
}
else
{
uint8_t x_385; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_385 = !lean_is_exclusive(x_353);
if (x_385 == 0)
{
return x_353;
}
else
{
lean_object* x_386; lean_object* x_387; lean_object* x_388; 
x_386 = lean_ctor_get(x_353, 0);
x_387 = lean_ctor_get(x_353, 1);
lean_inc(x_387);
lean_inc(x_386);
lean_dec(x_353);
x_388 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_388, 0, x_386);
lean_ctor_set(x_388, 1, x_387);
return x_388;
}
}
}
default: 
{
lean_object* x_389; lean_object* x_390; 
x_389 = lean_expr_instantiate_rev(x_1, x_2);
lean_dec(x_1);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_390 = l_Lean_Compiler_InferType_getLevel_x3f(x_389, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_390) == 0)
{
lean_object* x_391; 
x_391 = lean_ctor_get(x_390, 0);
lean_inc(x_391);
if (lean_obj_tag(x_391) == 0)
{
uint8_t x_392; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_392 = !lean_is_exclusive(x_390);
if (x_392 == 0)
{
lean_object* x_393; lean_object* x_394; 
x_393 = lean_ctor_get(x_390, 0);
lean_dec(x_393);
x_394 = l_Lean_Compiler_anyTypeExpr;
lean_ctor_set(x_390, 0, x_394);
return x_390;
}
else
{
lean_object* x_395; lean_object* x_396; lean_object* x_397; 
x_395 = lean_ctor_get(x_390, 1);
lean_inc(x_395);
lean_dec(x_390);
x_396 = l_Lean_Compiler_anyTypeExpr;
x_397 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_397, 0, x_396);
lean_ctor_set(x_397, 1, x_395);
return x_397;
}
}
else
{
lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; size_t x_403; size_t x_404; lean_object* x_405; 
x_398 = lean_ctor_get(x_390, 1);
lean_inc(x_398);
lean_dec(x_390);
x_399 = lean_ctor_get(x_391, 0);
lean_inc(x_399);
lean_dec(x_391);
x_400 = lean_box(0);
x_401 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_401, 0, x_400);
lean_ctor_set(x_401, 1, x_399);
x_402 = lean_array_get_size(x_2);
x_403 = lean_usize_of_nat(x_402);
lean_dec(x_402);
x_404 = 0;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_405 = l_Array_forInUnsafe_loop___at_Lean_Compiler_InferType_inferForallType_go___spec__11(x_400, x_2, x_403, x_404, x_401, x_3, x_4, x_5, x_398);
lean_dec(x_2);
if (lean_obj_tag(x_405) == 0)
{
lean_object* x_406; lean_object* x_407; 
x_406 = lean_ctor_get(x_405, 0);
lean_inc(x_406);
x_407 = lean_ctor_get(x_406, 0);
lean_inc(x_407);
if (lean_obj_tag(x_407) == 0)
{
lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; 
x_408 = lean_ctor_get(x_405, 1);
lean_inc(x_408);
lean_dec(x_405);
x_409 = lean_ctor_get(x_406, 1);
lean_inc(x_409);
lean_dec(x_406);
x_410 = lean_box(0);
x_411 = l_Lean_Compiler_InferType_inferForallType_go___lambda__1(x_409, x_410, x_3, x_4, x_5, x_408);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_411;
}
else
{
uint8_t x_412; 
lean_dec(x_406);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_412 = !lean_is_exclusive(x_405);
if (x_412 == 0)
{
lean_object* x_413; lean_object* x_414; 
x_413 = lean_ctor_get(x_405, 0);
lean_dec(x_413);
x_414 = lean_ctor_get(x_407, 0);
lean_inc(x_414);
lean_dec(x_407);
lean_ctor_set(x_405, 0, x_414);
return x_405;
}
else
{
lean_object* x_415; lean_object* x_416; lean_object* x_417; 
x_415 = lean_ctor_get(x_405, 1);
lean_inc(x_415);
lean_dec(x_405);
x_416 = lean_ctor_get(x_407, 0);
lean_inc(x_416);
lean_dec(x_407);
x_417 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_417, 0, x_416);
lean_ctor_set(x_417, 1, x_415);
return x_417;
}
}
}
else
{
uint8_t x_418; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_418 = !lean_is_exclusive(x_405);
if (x_418 == 0)
{
return x_405;
}
else
{
lean_object* x_419; lean_object* x_420; lean_object* x_421; 
x_419 = lean_ctor_get(x_405, 0);
x_420 = lean_ctor_get(x_405, 1);
lean_inc(x_420);
lean_inc(x_419);
lean_dec(x_405);
x_421 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_421, 0, x_419);
lean_ctor_set(x_421, 1, x_420);
return x_421;
}
}
}
}
else
{
uint8_t x_422; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_422 = !lean_is_exclusive(x_390);
if (x_422 == 0)
{
return x_390;
}
else
{
lean_object* x_423; lean_object* x_424; lean_object* x_425; 
x_423 = lean_ctor_get(x_390, 0);
x_424 = lean_ctor_get(x_390, 1);
lean_inc(x_424);
lean_inc(x_423);
lean_dec(x_390);
x_425 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_425, 0, x_423);
lean_ctor_set(x_425, 1, x_424);
return x_425;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_InferType_getLevel_x3f___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_3, 5);
x_7 = lean_st_ref_get(x_4, x_5);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_ctor_get(x_3, 2);
x_12 = l_Lean_Compiler_InferType_instAddMessageContextInferTypeM___closed__6;
lean_inc(x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_12);
lean_ctor_set(x_13, 2, x_2);
lean_ctor_set(x_13, 3, x_11);
x_14 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_1);
lean_inc(x_6);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_6);
lean_ctor_set(x_15, 1, x_14);
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 0, x_15);
return x_7;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_16 = lean_ctor_get(x_7, 0);
x_17 = lean_ctor_get(x_7, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_7);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_3, 2);
x_20 = l_Lean_Compiler_InferType_instAddMessageContextInferTypeM___closed__6;
lean_inc(x_19);
x_21 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_20);
lean_ctor_set(x_21, 2, x_2);
lean_ctor_set(x_21, 3, x_19);
x_22 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_1);
lean_inc(x_6);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_6);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_17);
return x_24;
}
}
}
static lean_object* _init_l_Lean_Compiler_InferType_getLevel_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("type expected", 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_InferType_getLevel_x3f___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_InferType_getLevel_x3f___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_InferType_getLevel_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_6 = l_Lean_Compiler_InferType_inferType(x_1, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 3)
{
uint8_t x_8; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_6, 0);
lean_dec(x_9);
x_10 = lean_ctor_get(x_7, 0);
lean_inc(x_10);
lean_dec(x_7);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_6, 0, x_11);
return x_6;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_6, 1);
lean_inc(x_12);
lean_dec(x_6);
x_13 = lean_ctor_get(x_7, 0);
lean_inc(x_13);
lean_dec(x_7);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_12);
return x_15;
}
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_6);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_6, 1);
x_18 = lean_ctor_get(x_6, 0);
lean_dec(x_18);
x_19 = l_Lean_Expr_isAnyType(x_7);
lean_dec(x_7);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_free_object(x_6);
x_20 = l_Lean_indentExpr(x_1);
x_21 = l_Lean_Compiler_InferType_getLevel_x3f___closed__2;
x_22 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
x_23 = l_Lean_Compiler_InferType_getCasesResultingType_go___closed__4;
x_24 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Lean_throwError___at_Lean_Compiler_InferType_getLevel_x3f___spec__1(x_24, x_2, x_3, x_4, x_17);
lean_dec(x_4);
lean_dec(x_3);
return x_25;
}
else
{
lean_object* x_26; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_26 = lean_box(0);
lean_ctor_set(x_6, 0, x_26);
return x_6;
}
}
else
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_ctor_get(x_6, 1);
lean_inc(x_27);
lean_dec(x_6);
x_28 = l_Lean_Expr_isAnyType(x_7);
lean_dec(x_7);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_29 = l_Lean_indentExpr(x_1);
x_30 = l_Lean_Compiler_InferType_getLevel_x3f___closed__2;
x_31 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
x_32 = l_Lean_Compiler_InferType_getCasesResultingType_go___closed__4;
x_33 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
x_34 = l_Lean_throwError___at_Lean_Compiler_InferType_getLevel_x3f___spec__1(x_33, x_2, x_3, x_4, x_27);
lean_dec(x_4);
lean_dec(x_3);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_27);
return x_36;
}
}
}
}
else
{
uint8_t x_37; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_37 = !lean_is_exclusive(x_6);
if (x_37 == 0)
{
return x_6;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_6, 0);
x_39 = lean_ctor_get(x_6, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_6);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_InferType_inferAppType___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_3, 5);
x_7 = lean_st_ref_get(x_4, x_5);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_ctor_get(x_3, 2);
x_12 = l_Lean_Compiler_InferType_instAddMessageContextInferTypeM___closed__6;
lean_inc(x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_12);
lean_ctor_set(x_13, 2, x_2);
lean_ctor_set(x_13, 3, x_11);
x_14 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_1);
lean_inc(x_6);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_6);
lean_ctor_set(x_15, 1, x_14);
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 0, x_15);
return x_7;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_16 = lean_ctor_get(x_7, 0);
x_17 = lean_ctor_get(x_7, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_7);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_3, 2);
x_20 = l_Lean_Compiler_InferType_instAddMessageContextInferTypeM___closed__6;
lean_inc(x_19);
x_21 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_20);
lean_ctor_set(x_21, 2, x_2);
lean_ctor_set(x_21, 3, x_19);
x_22 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_1);
lean_inc(x_6);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_6);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_17);
return x_24;
}
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Compiler_InferType_inferAppType___spec__2___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("function expected", 17);
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Compiler_InferType_inferAppType___spec__2___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Range_forIn_loop___at_Lean_Compiler_InferType_inferAppType___spec__2___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_InferType_inferAppType___spec__2___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_10 = l_Lean_indentExpr(x_1);
x_11 = l_Std_Range_forIn_loop___at_Lean_Compiler_InferType_inferAppType___spec__2___lambda__1___closed__2;
x_12 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
x_13 = l_Lean_Compiler_InferType_getCasesResultingType_go___closed__4;
x_14 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = l_Lean_throwError___at_Lean_Compiler_InferType_inferAppType___spec__1(x_14, x_6, x_7, x_8, x_9);
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
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_InferType_inferAppType___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_nat_dec_le(x_6, x_5);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_dec_eq(x_4, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_sub(x_4, x_16);
lean_dec(x_4);
x_35 = lean_ctor_get(x_8, 1);
lean_inc(x_35);
lean_dec(x_8);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = l_Lean_Expr_headBeta(x_36);
if (lean_obj_tag(x_38) == 7)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_39 = lean_ctor_get(x_38, 2);
lean_inc(x_39);
lean_dec(x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_37);
lean_inc(x_3);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_3);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_41);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_12);
x_18 = x_43;
goto block_34;
}
else
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_expr_instantiate_rev_range(x_38, x_37, x_5, x_2);
x_45 = l_Lean_Expr_headBeta(x_44);
if (lean_obj_tag(x_45) == 7)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_38);
lean_dec(x_37);
x_46 = lean_ctor_get(x_45, 2);
lean_inc(x_46);
lean_dec(x_45);
lean_inc(x_5);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_5);
lean_inc(x_3);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_3);
lean_ctor_set(x_48, 1, x_47);
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_48);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_12);
x_18 = x_50;
goto block_34;
}
else
{
uint8_t x_51; 
lean_dec(x_45);
x_51 = l_Lean_Expr_isAnyType(x_38);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_box(0);
lean_inc(x_9);
lean_inc(x_1);
x_53 = l_Std_Range_forIn_loop___at_Lean_Compiler_InferType_inferAppType___spec__2___lambda__1(x_1, x_38, x_37, x_3, x_52, x_9, x_10, x_11, x_12);
lean_dec(x_37);
lean_dec(x_38);
x_18 = x_53;
goto block_34;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_38);
lean_ctor_set(x_54, 1, x_37);
x_55 = l_Array_forInUnsafe_loop___at_Lean_Compiler_InferType_inferForallType_go___spec__1___closed__1;
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_54);
x_57 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_57, 0, x_56);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_12);
x_18 = x_58;
goto block_34;
}
}
}
block_34:
{
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
lean_dec(x_17);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_20 = !lean_is_exclusive(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_18, 0);
lean_dec(x_21);
x_22 = lean_ctor_get(x_19, 0);
lean_inc(x_22);
lean_dec(x_19);
lean_ctor_set(x_18, 0, x_22);
return x_18;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_18, 1);
lean_inc(x_23);
lean_dec(x_18);
x_24 = lean_ctor_get(x_19, 0);
lean_inc(x_24);
lean_dec(x_19);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_18, 1);
lean_inc(x_26);
lean_dec(x_18);
x_27 = lean_ctor_get(x_19, 0);
lean_inc(x_27);
lean_dec(x_19);
x_28 = lean_nat_add(x_5, x_7);
lean_dec(x_5);
x_4 = x_17;
x_5 = x_28;
x_8 = x_27;
x_12 = x_26;
goto _start;
}
}
else
{
uint8_t x_30; 
lean_dec(x_17);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_18);
if (x_30 == 0)
{
return x_18;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_18, 0);
x_32 = lean_ctor_get(x_18, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_18);
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
lean_object* x_59; 
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_8);
lean_ctor_set(x_59, 1, x_12);
return x_59;
}
}
else
{
lean_object* x_60; 
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_8);
lean_ctor_set(x_60, 1, x_12);
return x_60;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_InferType_inferAppType___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_expr_instantiate_rev_range(x_1, x_2, x_3, x_4);
x_11 = l_Lean_Expr_headBeta(x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
}
static lean_object* _init_l_Lean_Compiler_InferType_inferAppType___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_levelZero;
x_2 = l_Lean_Expr_sort___override(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_InferType_inferAppType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_6 = l_Lean_Compiler_isCasesApp_x3f(x_1, x_3, x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_Expr_getAppFn(x_1);
x_10 = lean_unsigned_to_nat(0u);
x_11 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_10);
x_12 = l_Lean_Compiler_InferType_inferAppType___closed__1;
lean_inc(x_11);
x_13 = lean_mk_array(x_11, x_12);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_sub(x_11, x_14);
lean_dec(x_11);
x_16 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_13, x_15);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_9);
x_17 = l_Lean_Compiler_InferType_inferType(x_9, x_2, x_3, x_4, x_8);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_array_get_size(x_16);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_18);
lean_ctor_set(x_22, 1, x_10);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
lean_inc(x_2);
lean_inc(x_20);
x_24 = l_Std_Range_forIn_loop___at_Lean_Compiler_InferType_inferAppType___spec__2(x_9, x_16, x_21, x_20, x_10, x_20, x_14, x_23, x_2, x_3, x_4, x_19);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
lean_dec(x_25);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_24, 1);
lean_inc(x_28);
lean_dec(x_24);
x_29 = lean_ctor_get(x_26, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_26, 1);
lean_inc(x_30);
lean_dec(x_26);
x_31 = lean_box(0);
x_32 = l_Lean_Compiler_InferType_inferAppType___lambda__1(x_29, x_30, x_20, x_16, x_31, x_2, x_3, x_4, x_28);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_16);
lean_dec(x_20);
lean_dec(x_30);
lean_dec(x_29);
return x_32;
}
else
{
uint8_t x_33; 
lean_dec(x_26);
lean_dec(x_20);
lean_dec(x_16);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_33 = !lean_is_exclusive(x_24);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_24, 0);
lean_dec(x_34);
x_35 = lean_ctor_get(x_27, 0);
lean_inc(x_35);
lean_dec(x_27);
lean_ctor_set(x_24, 0, x_35);
return x_24;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_24, 1);
lean_inc(x_36);
lean_dec(x_24);
x_37 = lean_ctor_get(x_27, 0);
lean_inc(x_37);
lean_dec(x_27);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
}
else
{
uint8_t x_39; 
lean_dec(x_20);
lean_dec(x_16);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_39 = !lean_is_exclusive(x_24);
if (x_39 == 0)
{
return x_24;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_24, 0);
x_41 = lean_ctor_get(x_24, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_24);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
uint8_t x_43; 
lean_dec(x_16);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_43 = !lean_is_exclusive(x_17);
if (x_43 == 0)
{
return x_17;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_17, 0);
x_45 = lean_ctor_get(x_17, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_17);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_6, 1);
lean_inc(x_47);
lean_dec(x_6);
x_48 = lean_ctor_get(x_7, 0);
lean_inc(x_48);
lean_dec(x_7);
x_49 = l_Lean_Compiler_InferType_getCasesResultingType(x_48, x_1, x_2, x_3, x_4, x_47);
lean_dec(x_4);
lean_dec(x_48);
return x_49;
}
}
else
{
uint8_t x_50; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_50 = !lean_is_exclusive(x_6);
if (x_50 == 0)
{
return x_6;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_6, 0);
x_52 = lean_ctor_get(x_6, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_6);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_InferType_inferProjType___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_3, 5);
x_7 = lean_st_ref_get(x_4, x_5);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_ctor_get(x_3, 2);
x_12 = l_Lean_Compiler_InferType_instAddMessageContextInferTypeM___closed__6;
lean_inc(x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_12);
lean_ctor_set(x_13, 2, x_2);
lean_ctor_set(x_13, 3, x_11);
x_14 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_1);
lean_inc(x_6);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_6);
lean_ctor_set(x_15, 1, x_14);
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 0, x_15);
return x_7;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_16 = lean_ctor_get(x_7, 0);
x_17 = lean_ctor_get(x_7, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_7);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_3, 2);
x_20 = l_Lean_Compiler_InferType_instAddMessageContextInferTypeM___closed__6;
lean_inc(x_19);
x_21 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_20);
lean_ctor_set(x_21, 2, x_2);
lean_ctor_set(x_21, 3, x_19);
x_22 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_1);
lean_inc(x_6);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_6);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_17);
return x_24;
}
}
}
static lean_object* _init_l_Lean_getConstInfo___at_Lean_Compiler_InferType_inferProjType___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("unknown constant '", 18);
return x_1;
}
}
static lean_object* _init_l_Lean_getConstInfo___at_Lean_Compiler_InferType_inferProjType___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_getConstInfo___at_Lean_Compiler_InferType_inferProjType___spec__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_getConstInfo___at_Lean_Compiler_InferType_inferProjType___spec__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("'", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_getConstInfo___at_Lean_Compiler_InferType_inferProjType___spec__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_getConstInfo___at_Lean_Compiler_InferType_inferProjType___spec__1___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at_Lean_Compiler_InferType_inferProjType___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_st_ref_get(x_4, x_5);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_6, 1);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
lean_inc(x_1);
x_11 = lean_environment_find(x_10, x_1);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_free_object(x_6);
x_12 = lean_box(0);
x_13 = l_Lean_Expr_const___override(x_1, x_12);
x_14 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = l_Lean_getConstInfo___at_Lean_Compiler_InferType_inferProjType___spec__1___closed__2;
x_16 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
x_17 = l_Lean_getConstInfo___at_Lean_Compiler_InferType_inferProjType___spec__1___closed__4;
x_18 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Lean_throwError___at_Lean_Compiler_InferType_inferProjType___spec__2(x_18, x_2, x_3, x_4, x_9);
return x_19;
}
else
{
lean_object* x_20; 
lean_dec(x_2);
lean_dec(x_1);
x_20 = lean_ctor_get(x_11, 0);
lean_inc(x_20);
lean_dec(x_11);
lean_ctor_set(x_6, 0, x_20);
return x_6;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_6, 0);
x_22 = lean_ctor_get(x_6, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_6);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
lean_dec(x_21);
lean_inc(x_1);
x_24 = lean_environment_find(x_23, x_1);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_25 = lean_box(0);
x_26 = l_Lean_Expr_const___override(x_1, x_25);
x_27 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_28 = l_Lean_getConstInfo___at_Lean_Compiler_InferType_inferProjType___spec__1___closed__2;
x_29 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
x_30 = l_Lean_getConstInfo___at_Lean_Compiler_InferType_inferProjType___spec__1___closed__4;
x_31 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = l_Lean_throwError___at_Lean_Compiler_InferType_inferProjType___spec__2(x_31, x_2, x_3, x_4, x_22);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_2);
lean_dec(x_1);
x_33 = lean_ctor_get(x_24, 0);
lean_inc(x_33);
lean_dec(x_24);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_22);
return x_34;
}
}
}
}
static lean_object* _init_l_panic___at_Lean_Compiler_InferType_inferProjType___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_instInhabitedCoreM___boxed), 3, 1);
lean_closure_set(x_1, 0, lean_box(0));
return x_1;
}
}
static lean_object* _init_l_panic___at_Lean_Compiler_InferType_inferProjType___spec__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_panic___at_Lean_Compiler_InferType_inferProjType___spec__3___closed__1;
x_2 = lean_alloc_closure((void*)(l_instInhabitedReaderT___rarg___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_Compiler_InferType_inferProjType___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_panic___at_Lean_Compiler_InferType_inferProjType___spec__3___closed__2;
x_7 = lean_panic_fn(x_6, x_1);
x_8 = lean_apply_4(x_7, x_2, x_3, x_4, x_5);
return x_8;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Compiler_InferType_inferProjType___spec__4___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("invalid projection", 18);
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Compiler_InferType_inferProjType___spec__4___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Range_forIn_loop___at_Lean_Compiler_InferType_inferProjType___spec__4___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_InferType_inferProjType___spec__4___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_11 = l_Lean_Expr_proj___override(x_1, x_2, x_3);
x_12 = l_Lean_indentExpr(x_11);
x_13 = l_Std_Range_forIn_loop___at_Lean_Compiler_InferType_inferProjType___spec__4___lambda__1___closed__2;
x_14 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
x_15 = l_Lean_Compiler_InferType_getCasesResultingType_go___closed__4;
x_16 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = l_Lean_throwError___at_Lean_Compiler_InferType_inferAppType___spec__1(x_16, x_7, x_8, x_9, x_10);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
return x_17;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_17);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Compiler_InferType_inferProjType___spec__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("assertion violation: ", 21);
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Compiler_InferType_inferProjType___spec__4___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("!body.hasLooseBVars\n            ", 32);
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Compiler_InferType_inferProjType___spec__4___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_Range_forIn_loop___at_Lean_Compiler_InferType_inferProjType___spec__4___closed__1;
x_2 = l_Std_Range_forIn_loop___at_Lean_Compiler_InferType_inferProjType___spec__4___closed__2;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Compiler_InferType_inferProjType___spec__4___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Compiler.InferType", 23);
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Compiler_InferType_inferProjType___spec__4___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Compiler.InferType.inferProjType", 37);
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Compiler_InferType_inferProjType___spec__4___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Std_Range_forIn_loop___at_Lean_Compiler_InferType_inferProjType___spec__4___closed__4;
x_2 = l_Std_Range_forIn_loop___at_Lean_Compiler_InferType_inferProjType___spec__4___closed__5;
x_3 = lean_unsigned_to_nat(90u);
x_4 = lean_unsigned_to_nat(12u);
x_5 = l_Std_Range_forIn_loop___at_Lean_Compiler_InferType_inferProjType___spec__4___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_InferType_inferProjType___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = lean_nat_dec_le(x_7, x_6);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_nat_dec_eq(x_5, x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_36; 
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_sub(x_5, x_17);
lean_dec(x_5);
x_36 = lean_ctor_get(x_9, 1);
lean_inc(x_36);
lean_dec(x_9);
if (lean_obj_tag(x_36) == 7)
{
lean_object* x_37; uint8_t x_38; 
x_37 = lean_ctor_get(x_36, 2);
lean_inc(x_37);
lean_dec(x_36);
x_38 = l_Lean_Expr_hasLooseBVars(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_inc(x_4);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_4);
lean_ctor_set(x_39, 1, x_37);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_39);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_13);
x_19 = x_41;
goto block_35;
}
else
{
lean_object* x_42; lean_object* x_43; 
lean_dec(x_37);
x_42 = l_Std_Range_forIn_loop___at_Lean_Compiler_InferType_inferProjType___spec__4___closed__6;
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_43 = l_panic___at_Lean_Compiler_InferType_inferProjType___spec__3(x_42, x_10, x_11, x_12, x_13);
x_19 = x_43;
goto block_35;
}
}
else
{
uint8_t x_44; 
x_44 = l_Lean_Expr_isAnyType(x_36);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_box(0);
lean_inc(x_10);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_46 = l_Std_Range_forIn_loop___at_Lean_Compiler_InferType_inferProjType___spec__4___lambda__1(x_1, x_2, x_3, x_4, x_36, x_45, x_10, x_11, x_12, x_13);
lean_dec(x_36);
x_19 = x_46;
goto block_35;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_47 = l_Array_forInUnsafe_loop___at_Lean_Compiler_InferType_inferForallType_go___spec__1___closed__1;
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_36);
x_49 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_49, 0, x_48);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_13);
x_19 = x_50;
goto block_35;
}
}
block_35:
{
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_19, 0);
lean_dec(x_22);
x_23 = lean_ctor_get(x_20, 0);
lean_inc(x_23);
lean_dec(x_20);
lean_ctor_set(x_19, 0, x_23);
return x_19;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_19, 1);
lean_inc(x_24);
lean_dec(x_19);
x_25 = lean_ctor_get(x_20, 0);
lean_inc(x_25);
lean_dec(x_20);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_19, 1);
lean_inc(x_27);
lean_dec(x_19);
x_28 = lean_ctor_get(x_20, 0);
lean_inc(x_28);
lean_dec(x_20);
x_29 = lean_nat_add(x_6, x_8);
lean_dec(x_6);
x_5 = x_18;
x_6 = x_29;
x_9 = x_28;
x_13 = x_27;
goto _start;
}
}
else
{
uint8_t x_31; 
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_31 = !lean_is_exclusive(x_19);
if (x_31 == 0)
{
return x_19;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_19, 0);
x_33 = lean_ctor_get(x_19, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_19);
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
lean_object* x_51; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_9);
lean_ctor_set(x_51, 1, x_13);
return x_51;
}
}
else
{
lean_object* x_52; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_9);
lean_ctor_set(x_52, 1, x_13);
return x_52;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_InferType_inferProjType___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = l_Lean_Expr_proj___override(x_1, x_2, x_3);
x_10 = l_Lean_indentExpr(x_9);
x_11 = l_Std_Range_forIn_loop___at_Lean_Compiler_InferType_inferProjType___spec__4___lambda__1___closed__2;
x_12 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
x_13 = l_Lean_Compiler_InferType_getCasesResultingType_go___closed__4;
x_14 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = l_Lean_throwError___at_Lean_Compiler_InferType_getCasesResultingType_go___spec__1(x_14, x_5, x_6, x_7, x_8);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_InferType_inferProjType___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_dec(x_5);
if (lean_obj_tag(x_1) == 7)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
uint8_t x_12; 
x_12 = l_Lean_Expr_isAnyType(x_1);
lean_dec(x_1);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_box(0);
x_14 = l_Lean_Compiler_InferType_inferProjType___lambda__1(x_2, x_3, x_4, x_13, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_15 = l_Lean_Compiler_anyTypeExpr;
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_9);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_InferType_inferProjType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_8 = l_Lean_Compiler_InferType_inferType(x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_Expr_getAppFn(x_9);
if (lean_obj_tag(x_11) == 4)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_st_ref_get(x_6, x_10);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_environment_find(x_17, x_12);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_13);
lean_dec(x_9);
x_19 = l_Lean_Expr_proj___override(x_1, x_2, x_3);
x_20 = l_Lean_indentExpr(x_19);
x_21 = l_Std_Range_forIn_loop___at_Lean_Compiler_InferType_inferProjType___spec__4___lambda__1___closed__2;
x_22 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
x_23 = l_Lean_Compiler_InferType_getCasesResultingType_go___closed__4;
x_24 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Lean_throwError___at_Lean_Compiler_InferType_getCasesResultingType_go___spec__1(x_24, x_4, x_5, x_6, x_16);
lean_dec(x_6);
lean_dec(x_5);
return x_25;
}
else
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_18, 0);
lean_inc(x_26);
lean_dec(x_18);
if (lean_obj_tag(x_26) == 5)
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec(x_26);
x_28 = lean_ctor_get_uint8(x_27, sizeof(void*)*5);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_29 = lean_ctor_get(x_27, 2);
lean_inc(x_29);
x_30 = lean_unsigned_to_nat(0u);
x_31 = lean_nat_dec_eq(x_29, x_30);
lean_dec(x_29);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_27);
lean_dec(x_13);
lean_dec(x_9);
x_32 = l_Lean_Expr_proj___override(x_1, x_2, x_3);
x_33 = l_Lean_indentExpr(x_32);
x_34 = l_Std_Range_forIn_loop___at_Lean_Compiler_InferType_inferProjType___spec__4___lambda__1___closed__2;
x_35 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
x_36 = l_Lean_Compiler_InferType_getCasesResultingType_go___closed__4;
x_37 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
x_38 = l_Lean_throwError___at_Lean_Compiler_InferType_getCasesResultingType_go___spec__1(x_37, x_4, x_5, x_6, x_16);
lean_dec(x_6);
lean_dec(x_5);
return x_38;
}
else
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_27, 4);
lean_inc(x_39);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_27);
lean_dec(x_13);
lean_dec(x_9);
x_40 = l_Lean_Expr_proj___override(x_1, x_2, x_3);
x_41 = l_Lean_indentExpr(x_40);
x_42 = l_Std_Range_forIn_loop___at_Lean_Compiler_InferType_inferProjType___spec__4___lambda__1___closed__2;
x_43 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_41);
x_44 = l_Lean_Compiler_InferType_getCasesResultingType_go___closed__4;
x_45 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
x_46 = l_Lean_throwError___at_Lean_Compiler_InferType_getCasesResultingType_go___spec__1(x_45, x_4, x_5, x_6, x_16);
lean_dec(x_6);
lean_dec(x_5);
return x_46;
}
else
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_39, 1);
lean_inc(x_47);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_39, 0);
lean_inc(x_48);
lean_dec(x_39);
lean_inc(x_4);
x_49 = l_Lean_getConstInfo___at_Lean_Compiler_InferType_inferProjType___spec__1(x_48, x_4, x_5, x_6, x_16);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
if (lean_obj_tag(x_50) == 6)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = lean_ctor_get(x_50, 0);
lean_inc(x_52);
lean_dec(x_50);
x_53 = lean_ctor_get(x_27, 1);
lean_inc(x_53);
lean_dec(x_27);
x_54 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_9, x_30);
x_55 = l_Lean_Compiler_InferType_inferAppType___closed__1;
lean_inc(x_54);
x_56 = lean_mk_array(x_54, x_55);
x_57 = lean_unsigned_to_nat(1u);
x_58 = lean_nat_sub(x_54, x_57);
lean_dec(x_54);
x_59 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_9, x_56, x_58);
x_60 = lean_array_get_size(x_59);
x_61 = lean_nat_dec_eq(x_53, x_60);
lean_dec(x_60);
lean_dec(x_53);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_59);
lean_dec(x_52);
lean_dec(x_13);
x_62 = l_Lean_Expr_proj___override(x_1, x_2, x_3);
x_63 = l_Lean_indentExpr(x_62);
x_64 = l_Std_Range_forIn_loop___at_Lean_Compiler_InferType_inferProjType___spec__4___lambda__1___closed__2;
x_65 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_63);
x_66 = l_Lean_Compiler_InferType_getCasesResultingType_go___closed__4;
x_67 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
x_68 = l_Lean_throwError___at_Lean_Compiler_InferType_getCasesResultingType_go___spec__1(x_67, x_4, x_5, x_6, x_51);
lean_dec(x_6);
lean_dec(x_5);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_69 = lean_ctor_get(x_52, 0);
lean_inc(x_69);
lean_dec(x_52);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
lean_dec(x_69);
x_71 = l_Lean_Expr_const___override(x_70, x_13);
x_72 = l_Lean_mkAppN(x_71, x_59);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_73 = l_Lean_Compiler_InferType_inferAppType(x_72, x_4, x_5, x_6, x_51);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec(x_73);
x_76 = lean_box(0);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_74);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc_n(x_2, 2);
lean_inc(x_1);
x_78 = l_Std_Range_forIn_loop___at_Lean_Compiler_InferType_inferProjType___spec__4(x_1, x_2, x_3, x_76, x_2, x_30, x_2, x_57, x_77, x_4, x_5, x_6, x_75);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_81 = lean_ctor_get(x_78, 1);
lean_inc(x_81);
lean_dec(x_78);
x_82 = lean_ctor_get(x_79, 1);
lean_inc(x_82);
lean_dec(x_79);
x_83 = lean_box(0);
x_84 = l_Lean_Compiler_InferType_inferProjType___lambda__2(x_82, x_1, x_2, x_3, x_83, x_4, x_5, x_6, x_81);
return x_84;
}
else
{
uint8_t x_85; 
lean_dec(x_79);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_85 = !lean_is_exclusive(x_78);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_ctor_get(x_78, 0);
lean_dec(x_86);
x_87 = lean_ctor_get(x_80, 0);
lean_inc(x_87);
lean_dec(x_80);
lean_ctor_set(x_78, 0, x_87);
return x_78;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_78, 1);
lean_inc(x_88);
lean_dec(x_78);
x_89 = lean_ctor_get(x_80, 0);
lean_inc(x_89);
lean_dec(x_80);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_88);
return x_90;
}
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
lean_dec(x_1);
x_91 = !lean_is_exclusive(x_78);
if (x_91 == 0)
{
return x_78;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_78, 0);
x_93 = lean_ctor_get(x_78, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_78);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
return x_94;
}
}
}
else
{
uint8_t x_95; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_95 = !lean_is_exclusive(x_73);
if (x_95 == 0)
{
return x_73;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_73, 0);
x_97 = lean_ctor_get(x_73, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_73);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
return x_98;
}
}
}
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
lean_dec(x_50);
lean_dec(x_27);
lean_dec(x_13);
lean_dec(x_9);
x_99 = lean_ctor_get(x_49, 1);
lean_inc(x_99);
lean_dec(x_49);
x_100 = l_Lean_Expr_proj___override(x_1, x_2, x_3);
x_101 = l_Lean_indentExpr(x_100);
x_102 = l_Std_Range_forIn_loop___at_Lean_Compiler_InferType_inferProjType___spec__4___lambda__1___closed__2;
x_103 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_101);
x_104 = l_Lean_Compiler_InferType_getCasesResultingType_go___closed__4;
x_105 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
x_106 = l_Lean_throwError___at_Lean_Compiler_InferType_getCasesResultingType_go___spec__1(x_105, x_4, x_5, x_6, x_99);
lean_dec(x_6);
lean_dec(x_5);
return x_106;
}
}
else
{
uint8_t x_107; 
lean_dec(x_27);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_107 = !lean_is_exclusive(x_49);
if (x_107 == 0)
{
return x_49;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_108 = lean_ctor_get(x_49, 0);
x_109 = lean_ctor_get(x_49, 1);
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_49);
x_110 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_109);
return x_110;
}
}
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
lean_dec(x_47);
lean_dec(x_39);
lean_dec(x_27);
lean_dec(x_13);
lean_dec(x_9);
x_111 = l_Lean_Expr_proj___override(x_1, x_2, x_3);
x_112 = l_Lean_indentExpr(x_111);
x_113 = l_Std_Range_forIn_loop___at_Lean_Compiler_InferType_inferProjType___spec__4___lambda__1___closed__2;
x_114 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_112);
x_115 = l_Lean_Compiler_InferType_getCasesResultingType_go___closed__4;
x_116 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
x_117 = l_Lean_throwError___at_Lean_Compiler_InferType_getCasesResultingType_go___spec__1(x_116, x_4, x_5, x_6, x_16);
lean_dec(x_6);
lean_dec(x_5);
return x_117;
}
}
}
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
lean_dec(x_27);
lean_dec(x_13);
lean_dec(x_9);
x_118 = l_Lean_Expr_proj___override(x_1, x_2, x_3);
x_119 = l_Lean_indentExpr(x_118);
x_120 = l_Std_Range_forIn_loop___at_Lean_Compiler_InferType_inferProjType___spec__4___lambda__1___closed__2;
x_121 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_119);
x_122 = l_Lean_Compiler_InferType_getCasesResultingType_go___closed__4;
x_123 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set(x_123, 1, x_122);
x_124 = l_Lean_throwError___at_Lean_Compiler_InferType_getCasesResultingType_go___spec__1(x_123, x_4, x_5, x_6, x_16);
lean_dec(x_6);
lean_dec(x_5);
return x_124;
}
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
lean_dec(x_26);
lean_dec(x_13);
lean_dec(x_9);
x_125 = l_Lean_Expr_proj___override(x_1, x_2, x_3);
x_126 = l_Lean_indentExpr(x_125);
x_127 = l_Std_Range_forIn_loop___at_Lean_Compiler_InferType_inferProjType___spec__4___lambda__1___closed__2;
x_128 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_128, 0, x_127);
lean_ctor_set(x_128, 1, x_126);
x_129 = l_Lean_Compiler_InferType_getCasesResultingType_go___closed__4;
x_130 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_130, 0, x_128);
lean_ctor_set(x_130, 1, x_129);
x_131 = l_Lean_throwError___at_Lean_Compiler_InferType_getCasesResultingType_go___spec__1(x_130, x_4, x_5, x_6, x_16);
lean_dec(x_6);
lean_dec(x_5);
return x_131;
}
}
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
lean_dec(x_11);
lean_dec(x_9);
x_132 = l_Lean_Expr_proj___override(x_1, x_2, x_3);
x_133 = l_Lean_indentExpr(x_132);
x_134 = l_Std_Range_forIn_loop___at_Lean_Compiler_InferType_inferProjType___spec__4___lambda__1___closed__2;
x_135 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_133);
x_136 = l_Lean_Compiler_InferType_getCasesResultingType_go___closed__4;
x_137 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_137, 0, x_135);
lean_ctor_set(x_137, 1, x_136);
x_138 = l_Lean_throwError___at_Lean_Compiler_InferType_getCasesResultingType_go___spec__1(x_137, x_4, x_5, x_6, x_10);
lean_dec(x_6);
lean_dec(x_5);
return x_138;
}
}
else
{
uint8_t x_139; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_139 = !lean_is_exclusive(x_8);
if (x_139 == 0)
{
return x_8;
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_140 = lean_ctor_get(x_8, 0);
x_141 = lean_ctor_get(x_8, 1);
lean_inc(x_141);
lean_inc(x_140);
lean_dec(x_8);
x_142 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_142, 0, x_140);
lean_ctor_set(x_142, 1, x_141);
return x_142;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_InferType_inferForallType_go___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_11 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_12 = l_Array_forInUnsafe_loop___at_Lean_Compiler_InferType_inferForallType_go___spec__1(x_1, x_2, x_10, x_11, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_InferType_inferForallType_go___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_11 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_12 = l_Array_forInUnsafe_loop___at_Lean_Compiler_InferType_inferForallType_go___spec__2(x_1, x_2, x_10, x_11, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_InferType_inferForallType_go___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_11 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_12 = l_Array_forInUnsafe_loop___at_Lean_Compiler_InferType_inferForallType_go___spec__3(x_1, x_2, x_10, x_11, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_InferType_inferForallType_go___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_11 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_12 = l_Array_forInUnsafe_loop___at_Lean_Compiler_InferType_inferForallType_go___spec__4(x_1, x_2, x_10, x_11, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_InferType_inferForallType_go___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_11 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_12 = l_Array_forInUnsafe_loop___at_Lean_Compiler_InferType_inferForallType_go___spec__5(x_1, x_2, x_10, x_11, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_InferType_inferForallType_go___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_11 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_12 = l_Array_forInUnsafe_loop___at_Lean_Compiler_InferType_inferForallType_go___spec__6(x_1, x_2, x_10, x_11, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_InferType_inferForallType_go___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_11 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_12 = l_Array_forInUnsafe_loop___at_Lean_Compiler_InferType_inferForallType_go___spec__7(x_1, x_2, x_10, x_11, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_InferType_inferForallType_go___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_11 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_12 = l_Array_forInUnsafe_loop___at_Lean_Compiler_InferType_inferForallType_go___spec__8(x_1, x_2, x_10, x_11, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_InferType_inferForallType_go___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_11 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_12 = l_Array_forInUnsafe_loop___at_Lean_Compiler_InferType_inferForallType_go___spec__9(x_1, x_2, x_10, x_11, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_InferType_inferForallType_go___spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_11 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_12 = l_Array_forInUnsafe_loop___at_Lean_Compiler_InferType_inferForallType_go___spec__10(x_1, x_2, x_10, x_11, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_InferType_inferForallType_go___spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_11 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_12 = l_Array_forInUnsafe_loop___at_Lean_Compiler_InferType_inferForallType_go___spec__11(x_1, x_2, x_10, x_11, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_InferType_inferForallType_go___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_InferType_inferForallType_go___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_InferType_getLevel_x3f___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_throwError___at_Lean_Compiler_InferType_getLevel_x3f___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_InferType_inferAppType___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_throwError___at_Lean_Compiler_InferType_inferAppType___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_InferType_inferAppType___spec__2___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Std_Range_forIn_loop___at_Lean_Compiler_InferType_inferAppType___spec__2___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_InferType_inferAppType___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Std_Range_forIn_loop___at_Lean_Compiler_InferType_inferAppType___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_InferType_inferAppType___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_InferType_inferAppType___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_InferType_inferProjType___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_throwError___at_Lean_Compiler_InferType_inferProjType___spec__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at_Lean_Compiler_InferType_inferProjType___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_getConstInfo___at_Lean_Compiler_InferType_inferProjType___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_InferType_inferProjType___spec__4___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Std_Range_forIn_loop___at_Lean_Compiler_InferType_inferProjType___spec__4___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_InferType_inferProjType___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Std_Range_forIn_loop___at_Lean_Compiler_InferType_inferProjType___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_8);
lean_dec(x_7);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_InferType_inferProjType___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_InferType_inferProjType___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
return x_9;
}
}
static lean_object* _init_l_Lean_Compiler_instMonadInferTypeInferTypeM___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_InferType_inferType), 5, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_instMonadInferTypeInferTypeM() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Compiler_instMonadInferTypeInferTypeM___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_instMonadInferType___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_apply_1(x_2, x_3);
x_5 = lean_apply_2(x_1, lean_box(0), x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_instMonadInferType(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Compiler_instMonadInferType___rarg), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_getLevel___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 3)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
lean_dec(x_1);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_apply_2(x_7, lean_box(0), x_5);
return x_8;
}
else
{
uint8_t x_9; 
x_9 = l_Lean_Expr_isAnyType(x_4);
lean_dec(x_4);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = l_Lean_indentExpr(x_1);
x_11 = l_Lean_Compiler_InferType_getLevel_x3f___closed__2;
x_12 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
x_13 = l_Lean_Compiler_InferType_getCasesResultingType_go___closed__4;
x_14 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = l_Lean_throwError___rarg(x_2, x_3, x_14);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_3);
lean_dec(x_1);
x_16 = lean_ctor_get(x_2, 0);
lean_inc(x_16);
lean_dec(x_2);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = l_Lean_levelOne;
x_19 = lean_apply_2(x_17, lean_box(0), x_18);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_getLevel___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_inc(x_4);
x_6 = lean_apply_1(x_2, x_4);
x_7 = lean_alloc_closure((void*)(l_Lean_Compiler_getLevel___rarg___lambda__1), 4, 3);
lean_closure_set(x_7, 0, x_4);
lean_closure_set(x_7, 1, x_1);
lean_closure_set(x_7, 2, x_3);
x_8 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_getLevel(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Compiler_getLevel___rarg), 4, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_mkLcUnreachable___rarg___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("lcUnreachable", 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_mkLcUnreachable___rarg___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_mkLcUnreachable___rarg___lambda__1___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_mkLcUnreachable___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_7, 1, x_6);
x_8 = l_Lean_Compiler_mkLcUnreachable___rarg___lambda__1___closed__2;
x_9 = l_Lean_Expr_const___override(x_8, x_7);
x_10 = l_Lean_Expr_app___override(x_9, x_2);
x_11 = lean_apply_2(x_5, lean_box(0), x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_mkLcUnreachable___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_6 = l_Lean_Compiler_getLevel___rarg(x_1, x_2, x_3, x_4);
x_7 = lean_alloc_closure((void*)(l_Lean_Compiler_mkLcUnreachable___rarg___lambda__1), 3, 2);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_4);
x_8 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_mkLcUnreachable(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Compiler_mkLcUnreachable___rarg), 4, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_mkLcCast___rarg___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("lcCast", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_mkLcCast___rarg___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_mkLcCast___rarg___lambda__1___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_mkLcCast___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_6);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_2);
lean_ctor_set(x_11, 1, x_10);
x_12 = l_Lean_Compiler_mkLcCast___rarg___lambda__1___closed__2;
x_13 = l_Lean_Expr_const___override(x_12, x_11);
x_14 = l_Lean_mkApp3(x_13, x_3, x_4, x_5);
x_15 = lean_apply_2(x_8, lean_box(0), x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_mkLcCast___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_inc(x_4);
lean_inc(x_1);
x_9 = l_Lean_Compiler_getLevel___rarg(x_1, x_2, x_3, x_4);
x_10 = lean_alloc_closure((void*)(l_Lean_Compiler_mkLcCast___rarg___lambda__1), 6, 5);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_8);
lean_closure_set(x_10, 2, x_5);
lean_closure_set(x_10, 3, x_4);
lean_closure_set(x_10, 4, x_6);
x_11 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_mkLcCast___rarg___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_inc(x_7);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_8 = l_Lean_Compiler_getLevel___rarg(x_1, x_2, x_3, x_7);
lean_inc(x_6);
x_9 = lean_alloc_closure((void*)(l_Lean_Compiler_mkLcCast___rarg___lambda__2), 8, 7);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_2);
lean_closure_set(x_9, 2, x_3);
lean_closure_set(x_9, 3, x_4);
lean_closure_set(x_9, 4, x_7);
lean_closure_set(x_9, 5, x_5);
lean_closure_set(x_9, 6, x_6);
x_10 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_mkLcCast___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_inc(x_2);
lean_inc(x_4);
x_7 = lean_apply_1(x_2, x_4);
lean_inc(x_6);
x_8 = lean_alloc_closure((void*)(l_Lean_Compiler_mkLcCast___rarg___lambda__3), 7, 6);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_2);
lean_closure_set(x_8, 2, x_3);
lean_closure_set(x_8, 3, x_5);
lean_closure_set(x_8, 4, x_4);
lean_closure_set(x_8, 5, x_6);
x_9 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_mkLcCast(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Compiler_mkLcCast___rarg), 5, 0);
return x_2;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNFTypes(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_Util(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_InferType(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNFTypes(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_Util(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Compiler_InferType_instMonadLCtxInferTypeM___closed__1 = _init_l_Lean_Compiler_InferType_instMonadLCtxInferTypeM___closed__1();
lean_mark_persistent(l_Lean_Compiler_InferType_instMonadLCtxInferTypeM___closed__1);
l_Lean_Compiler_InferType_instMonadLCtxInferTypeM___closed__2 = _init_l_Lean_Compiler_InferType_instMonadLCtxInferTypeM___closed__2();
lean_mark_persistent(l_Lean_Compiler_InferType_instMonadLCtxInferTypeM___closed__2);
l_Lean_Compiler_InferType_instMonadLCtxInferTypeM = _init_l_Lean_Compiler_InferType_instMonadLCtxInferTypeM();
lean_mark_persistent(l_Lean_Compiler_InferType_instMonadLCtxInferTypeM);
l_Lean_Compiler_InferType_instAddMessageContextInferTypeM___closed__1 = _init_l_Lean_Compiler_InferType_instAddMessageContextInferTypeM___closed__1();
lean_mark_persistent(l_Lean_Compiler_InferType_instAddMessageContextInferTypeM___closed__1);
l_Lean_Compiler_InferType_instAddMessageContextInferTypeM___closed__2 = _init_l_Lean_Compiler_InferType_instAddMessageContextInferTypeM___closed__2();
lean_mark_persistent(l_Lean_Compiler_InferType_instAddMessageContextInferTypeM___closed__2);
l_Lean_Compiler_InferType_instAddMessageContextInferTypeM___closed__3 = _init_l_Lean_Compiler_InferType_instAddMessageContextInferTypeM___closed__3();
lean_mark_persistent(l_Lean_Compiler_InferType_instAddMessageContextInferTypeM___closed__3);
l_Lean_Compiler_InferType_instAddMessageContextInferTypeM___closed__4 = _init_l_Lean_Compiler_InferType_instAddMessageContextInferTypeM___closed__4();
lean_mark_persistent(l_Lean_Compiler_InferType_instAddMessageContextInferTypeM___closed__4);
l_Lean_Compiler_InferType_instAddMessageContextInferTypeM___closed__5 = _init_l_Lean_Compiler_InferType_instAddMessageContextInferTypeM___closed__5();
lean_mark_persistent(l_Lean_Compiler_InferType_instAddMessageContextInferTypeM___closed__5);
l_Lean_Compiler_InferType_instAddMessageContextInferTypeM___closed__6 = _init_l_Lean_Compiler_InferType_instAddMessageContextInferTypeM___closed__6();
lean_mark_persistent(l_Lean_Compiler_InferType_instAddMessageContextInferTypeM___closed__6);
l_Lean_Compiler_InferType_inferConstType___closed__1 = _init_l_Lean_Compiler_InferType_inferConstType___closed__1();
lean_mark_persistent(l_Lean_Compiler_InferType_inferConstType___closed__1);
l_Lean_Compiler_InferType_inferConstType___closed__2 = _init_l_Lean_Compiler_InferType_inferConstType___closed__2();
lean_mark_persistent(l_Lean_Compiler_InferType_inferConstType___closed__2);
l_Lean_Compiler_InferType_inferConstType___closed__3 = _init_l_Lean_Compiler_InferType_inferConstType___closed__3();
lean_mark_persistent(l_Lean_Compiler_InferType_inferConstType___closed__3);
l_Lean_Compiler_InferType_inferConstType___closed__4 = _init_l_Lean_Compiler_InferType_inferConstType___closed__4();
lean_mark_persistent(l_Lean_Compiler_InferType_inferConstType___closed__4);
l_Lean_Compiler_InferType_getCasesResultingType_go___closed__1 = _init_l_Lean_Compiler_InferType_getCasesResultingType_go___closed__1();
lean_mark_persistent(l_Lean_Compiler_InferType_getCasesResultingType_go___closed__1);
l_Lean_Compiler_InferType_getCasesResultingType_go___closed__2 = _init_l_Lean_Compiler_InferType_getCasesResultingType_go___closed__2();
lean_mark_persistent(l_Lean_Compiler_InferType_getCasesResultingType_go___closed__2);
l_Lean_Compiler_InferType_getCasesResultingType_go___closed__3 = _init_l_Lean_Compiler_InferType_getCasesResultingType_go___closed__3();
lean_mark_persistent(l_Lean_Compiler_InferType_getCasesResultingType_go___closed__3);
l_Lean_Compiler_InferType_getCasesResultingType_go___closed__4 = _init_l_Lean_Compiler_InferType_getCasesResultingType_go___closed__4();
lean_mark_persistent(l_Lean_Compiler_InferType_getCasesResultingType_go___closed__4);
l_Lean_Compiler_InferType_inferType___closed__1 = _init_l_Lean_Compiler_InferType_inferType___closed__1();
lean_mark_persistent(l_Lean_Compiler_InferType_inferType___closed__1);
l_Lean_Compiler_InferType_inferType___closed__2 = _init_l_Lean_Compiler_InferType_inferType___closed__2();
lean_mark_persistent(l_Lean_Compiler_InferType_inferType___closed__2);
l_Lean_Compiler_InferType_inferType___closed__3 = _init_l_Lean_Compiler_InferType_inferType___closed__3();
lean_mark_persistent(l_Lean_Compiler_InferType_inferType___closed__3);
l_Lean_Compiler_InferType_inferType___closed__4 = _init_l_Lean_Compiler_InferType_inferType___closed__4();
lean_mark_persistent(l_Lean_Compiler_InferType_inferType___closed__4);
l_Lean_Compiler_InferType_inferLambdaType___closed__1 = _init_l_Lean_Compiler_InferType_inferLambdaType___closed__1();
lean_mark_persistent(l_Lean_Compiler_InferType_inferLambdaType___closed__1);
l_Array_forInUnsafe_loop___at_Lean_Compiler_InferType_inferForallType_go___spec__1___closed__1 = _init_l_Array_forInUnsafe_loop___at_Lean_Compiler_InferType_inferForallType_go___spec__1___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Compiler_InferType_inferForallType_go___spec__1___closed__1);
l_Lean_Compiler_InferType_getLevel_x3f___closed__1 = _init_l_Lean_Compiler_InferType_getLevel_x3f___closed__1();
lean_mark_persistent(l_Lean_Compiler_InferType_getLevel_x3f___closed__1);
l_Lean_Compiler_InferType_getLevel_x3f___closed__2 = _init_l_Lean_Compiler_InferType_getLevel_x3f___closed__2();
lean_mark_persistent(l_Lean_Compiler_InferType_getLevel_x3f___closed__2);
l_Std_Range_forIn_loop___at_Lean_Compiler_InferType_inferAppType___spec__2___lambda__1___closed__1 = _init_l_Std_Range_forIn_loop___at_Lean_Compiler_InferType_inferAppType___spec__2___lambda__1___closed__1();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_Compiler_InferType_inferAppType___spec__2___lambda__1___closed__1);
l_Std_Range_forIn_loop___at_Lean_Compiler_InferType_inferAppType___spec__2___lambda__1___closed__2 = _init_l_Std_Range_forIn_loop___at_Lean_Compiler_InferType_inferAppType___spec__2___lambda__1___closed__2();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_Compiler_InferType_inferAppType___spec__2___lambda__1___closed__2);
l_Lean_Compiler_InferType_inferAppType___closed__1 = _init_l_Lean_Compiler_InferType_inferAppType___closed__1();
lean_mark_persistent(l_Lean_Compiler_InferType_inferAppType___closed__1);
l_Lean_getConstInfo___at_Lean_Compiler_InferType_inferProjType___spec__1___closed__1 = _init_l_Lean_getConstInfo___at_Lean_Compiler_InferType_inferProjType___spec__1___closed__1();
lean_mark_persistent(l_Lean_getConstInfo___at_Lean_Compiler_InferType_inferProjType___spec__1___closed__1);
l_Lean_getConstInfo___at_Lean_Compiler_InferType_inferProjType___spec__1___closed__2 = _init_l_Lean_getConstInfo___at_Lean_Compiler_InferType_inferProjType___spec__1___closed__2();
lean_mark_persistent(l_Lean_getConstInfo___at_Lean_Compiler_InferType_inferProjType___spec__1___closed__2);
l_Lean_getConstInfo___at_Lean_Compiler_InferType_inferProjType___spec__1___closed__3 = _init_l_Lean_getConstInfo___at_Lean_Compiler_InferType_inferProjType___spec__1___closed__3();
lean_mark_persistent(l_Lean_getConstInfo___at_Lean_Compiler_InferType_inferProjType___spec__1___closed__3);
l_Lean_getConstInfo___at_Lean_Compiler_InferType_inferProjType___spec__1___closed__4 = _init_l_Lean_getConstInfo___at_Lean_Compiler_InferType_inferProjType___spec__1___closed__4();
lean_mark_persistent(l_Lean_getConstInfo___at_Lean_Compiler_InferType_inferProjType___spec__1___closed__4);
l_panic___at_Lean_Compiler_InferType_inferProjType___spec__3___closed__1 = _init_l_panic___at_Lean_Compiler_InferType_inferProjType___spec__3___closed__1();
lean_mark_persistent(l_panic___at_Lean_Compiler_InferType_inferProjType___spec__3___closed__1);
l_panic___at_Lean_Compiler_InferType_inferProjType___spec__3___closed__2 = _init_l_panic___at_Lean_Compiler_InferType_inferProjType___spec__3___closed__2();
lean_mark_persistent(l_panic___at_Lean_Compiler_InferType_inferProjType___spec__3___closed__2);
l_Std_Range_forIn_loop___at_Lean_Compiler_InferType_inferProjType___spec__4___lambda__1___closed__1 = _init_l_Std_Range_forIn_loop___at_Lean_Compiler_InferType_inferProjType___spec__4___lambda__1___closed__1();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_Compiler_InferType_inferProjType___spec__4___lambda__1___closed__1);
l_Std_Range_forIn_loop___at_Lean_Compiler_InferType_inferProjType___spec__4___lambda__1___closed__2 = _init_l_Std_Range_forIn_loop___at_Lean_Compiler_InferType_inferProjType___spec__4___lambda__1___closed__2();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_Compiler_InferType_inferProjType___spec__4___lambda__1___closed__2);
l_Std_Range_forIn_loop___at_Lean_Compiler_InferType_inferProjType___spec__4___closed__1 = _init_l_Std_Range_forIn_loop___at_Lean_Compiler_InferType_inferProjType___spec__4___closed__1();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_Compiler_InferType_inferProjType___spec__4___closed__1);
l_Std_Range_forIn_loop___at_Lean_Compiler_InferType_inferProjType___spec__4___closed__2 = _init_l_Std_Range_forIn_loop___at_Lean_Compiler_InferType_inferProjType___spec__4___closed__2();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_Compiler_InferType_inferProjType___spec__4___closed__2);
l_Std_Range_forIn_loop___at_Lean_Compiler_InferType_inferProjType___spec__4___closed__3 = _init_l_Std_Range_forIn_loop___at_Lean_Compiler_InferType_inferProjType___spec__4___closed__3();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_Compiler_InferType_inferProjType___spec__4___closed__3);
l_Std_Range_forIn_loop___at_Lean_Compiler_InferType_inferProjType___spec__4___closed__4 = _init_l_Std_Range_forIn_loop___at_Lean_Compiler_InferType_inferProjType___spec__4___closed__4();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_Compiler_InferType_inferProjType___spec__4___closed__4);
l_Std_Range_forIn_loop___at_Lean_Compiler_InferType_inferProjType___spec__4___closed__5 = _init_l_Std_Range_forIn_loop___at_Lean_Compiler_InferType_inferProjType___spec__4___closed__5();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_Compiler_InferType_inferProjType___spec__4___closed__5);
l_Std_Range_forIn_loop___at_Lean_Compiler_InferType_inferProjType___spec__4___closed__6 = _init_l_Std_Range_forIn_loop___at_Lean_Compiler_InferType_inferProjType___spec__4___closed__6();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_Compiler_InferType_inferProjType___spec__4___closed__6);
l_Lean_Compiler_instMonadInferTypeInferTypeM___closed__1 = _init_l_Lean_Compiler_instMonadInferTypeInferTypeM___closed__1();
lean_mark_persistent(l_Lean_Compiler_instMonadInferTypeInferTypeM___closed__1);
l_Lean_Compiler_instMonadInferTypeInferTypeM = _init_l_Lean_Compiler_instMonadInferTypeInferTypeM();
lean_mark_persistent(l_Lean_Compiler_instMonadInferTypeInferTypeM);
l_Lean_Compiler_mkLcUnreachable___rarg___lambda__1___closed__1 = _init_l_Lean_Compiler_mkLcUnreachable___rarg___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Compiler_mkLcUnreachable___rarg___lambda__1___closed__1);
l_Lean_Compiler_mkLcUnreachable___rarg___lambda__1___closed__2 = _init_l_Lean_Compiler_mkLcUnreachable___rarg___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Compiler_mkLcUnreachable___rarg___lambda__1___closed__2);
l_Lean_Compiler_mkLcCast___rarg___lambda__1___closed__1 = _init_l_Lean_Compiler_mkLcCast___rarg___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Compiler_mkLcCast___rarg___lambda__1___closed__1);
l_Lean_Compiler_mkLcCast___rarg___lambda__1___closed__2 = _init_l_Lean_Compiler_mkLcCast___rarg___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Compiler_mkLcCast___rarg___lambda__1___closed__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
