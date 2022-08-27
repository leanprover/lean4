// Lean compiler output
// Module: Lean.Compiler.LCNF.InferType
// Imports: Init Lean.Compiler.LCNF.CompilerM Lean.Compiler.LCNF.Types
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_mkForallParams___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Nat_foldRevM_loop___at_Lean_Compiler_LCNF_InferType_mkForallFVars___spec__2___closed__2;
static lean_object* l_Lean_Compiler_LCNF_mkAuxJpDecl_x27___closed__2;
lean_object* l_Lean_addMessageContextPartial___at_Lean_Core_instAddMessageContextCoreM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
static lean_object* l_Lean_Compiler_LCNF_InferType_mkForallParams___closed__1;
LEAN_EXPORT lean_object* l_panic___at_Lean_Compiler_LCNF_InferType_mkForallFVars___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
extern lean_object* l_Lean_Compiler_LCNF_anyTypeExpr;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Compiler_LCNF_instantiateLCNFTypeLevelParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__4___closed__3;
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Nat_foldRevM_loop___at_Lean_Compiler_LCNF_InferType_mkForallFVars___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferAppTypeCore___spec__2___lambda__1___closed__5;
static lean_object* l_Lean_Compiler_LCNF_InferType_inferConstType___closed__3;
static lean_object* l_Nat_foldRevM_loop___at_Lean_Compiler_LCNF_InferType_mkForallFVars___spec__2___closed__8;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_inferLambdaType_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkLcCast(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_InferType_inferType___closed__5;
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at_Lean_Compiler_LCNF_InferType_withLocalDecl___spec__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_succ___override(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_InferType_getLevel_x3f___closed__2;
static lean_object* l_Lean_Compiler_LCNF_InferType_inferAppType___closed__1;
static lean_object* l_Nat_foldRevM_loop___at_Lean_Compiler_LCNF_InferType_mkForallFVars___spec__2___closed__1;
static lean_object* l_panic___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_inferAppTypeCore___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instantiateForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at_Lean_Compiler_LCNF_InferType_withLocalDecl___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_getConstInfo___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_inferFVarType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_environment_find(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* l_Array_toSubarray___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__9(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_instantiateForall_go___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__4___closed__5;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__8(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_InferType_getLevel_x3f___closed__1;
static lean_object* l_Lean_Compiler_LCNF_InferType_mkForallParams___closed__2;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
static lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferAppTypeCore___spec__2___lambda__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_inferType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_levelZero;
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldRevM_loop___at_Lean_Compiler_LCNF_InferType_mkForallFVars___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Nat_foldRevM_loop___at_Lean_Compiler_LCNF_InferType_mkForallFVars___spec__2___closed__6;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__7(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_getLevel___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_InferType_mkForallParams___closed__4;
static lean_object* l_panic___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__3___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_InferType_inferAppTypeCore___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_inferParamType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Literal_type(lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Nat_foldRevM_loop___at_Lean_Compiler_LCNF_InferType_mkForallFVars___spec__2___closed__3;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__6(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_InferType_inferAppTypeCore___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate_rev_range(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_getLevel___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_imax___override(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_InferType_mkForallParams___closed__6;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__1___closed__1;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_mkForallFVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_headBeta(lean_object*);
static lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__4___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_inferFVarType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instantiateForall_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferAppTypeCore___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inferType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_InferType_inferConstType___closed__4;
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__4___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_inferForallType_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__4___lambda__1___closed__1;
lean_object* l_instInhabited___rarg(lean_object*, lean_object*);
lean_object* l_panic___at_Lean_Expr_getRevArg_x21___spec__1(lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instantiateForall___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at_Lean_Compiler_LCNF_InferType_mkForallFVars___spec__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_withLocalDecl___rarg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instantiateForall_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at_Lean_Compiler_LCNF_InferType_mkForallFVars___spec__1___closed__1;
static lean_object* l_Lean_Compiler_LCNF_instantiateForall_go___closed__1;
static lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__4___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__11(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_abstract_range(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_InferType_inferConstType___closed__1;
lean_object* l_Std_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_mkForallParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_InferType_mkForallParams___closed__5;
lean_object* l_Lean_Compiler_LCNF_mkLetDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_InferType_inferConstType___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_getLevel_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Nat_foldRevM_loop___at_Lean_Compiler_LCNF_InferType_mkForallFVars___spec__2___closed__4;
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__4___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__4___closed__2;
extern lean_object* l_Lean_instInhabitedExpr;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_inferAppTypeCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_AltCore_inferType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Nat_foldRevM_loop___at_Lean_Compiler_LCNF_InferType_mkForallFVars___spec__2___closed__7;
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_inferType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at_Lean_Compiler_LCNF_InferType_mkForallFVars___spec__1___closed__3;
static lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_InferType_inferType___spec__1___closed__4;
static lean_object* l_Lean_Compiler_LCNF_instantiateForall_go___closed__2;
static lean_object* l_panic___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__3___closed__4;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_inferAppType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_inferLambdaType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
static lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__4___closed__4;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__5(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_InferType_mkForallParams___closed__7;
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkAuxLetDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_mkLcCast___closed__1;
static lean_object* l_Nat_foldRevM_loop___at_Lean_Compiler_LCNF_InferType_mkForallFVars___spec__2___closed__5;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_inferForallType_go___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* lean_local_ctx_mk_local_decl(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkForallParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_mkLcCast___closed__2;
lean_object* l_Lean_Expr_fvar___override(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_InferType_mkForallParams___spec__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferAppTypeCore___spec__2___lambda__1___closed__4;
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at_Lean_Compiler_LCNF_InferType_withLocalDecl___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkFunDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkAuxJpDecl_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_inferProjType___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferAppTypeCore___spec__2___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_InferType_mkForallParams___closed__3;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_inferConstType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_AltCore_getCode(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at_Lean_Compiler_LCNF_InferType_withLocalDecl___spec__2___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at_Lean_Compiler_LCNF_InferType_withLocalDecl___spec__2___rarg(lean_object*, lean_object*);
lean_object* l_instInhabitedReaderT___rarg___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_mkAuxJpDecl_x27___closed__3;
extern lean_object* l_Lean_Core_instMonadCoreM;
static lean_object* l_Lean_Compiler_LCNF_InferType_inferLambdaType___closed__1;
static lean_object* l_Lean_Compiler_LCNF_InferType_inferType___closed__6;
lean_object* l_Lean_Compiler_LCNF_mkFreshBinderName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_toLocalContext(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_InferType_inferType___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_inferProjType___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_normalize(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_mkForallFVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_ofSubarray___rarg(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_InferType_inferType___closed__2;
uint8_t l_Lean_Expr_isAnyType(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_inferProjType___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_InferType_inferType___closed__1;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferAppTypeCore___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate_rev(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_AltCore_inferType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_inferForallType_go___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_inferProjType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_withLocalDecl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_inferForallType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_abstract(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkAuxFunDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferAppTypeCore___spec__2___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at_Lean_Compiler_LCNF_InferType_withLocalDecl___spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_InferType_mkForallParams___spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferAppTypeCore___spec__2___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_InferType_inferType___spec__1___closed__3;
static lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferAppTypeCore___spec__2___lambda__1___closed__2;
static lean_object* l_Lean_getConstInfo___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__1___closed__2;
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadReaderT___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_InferType_inferType___closed__4;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_instantiateForall_go___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_InferType_getLevel_x3f___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkAuxJpDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_getLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_withLocalDecl___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_local_ctx_find(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_inferAppTypeCore___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_levelOne;
static lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferAppTypeCore___spec__2___lambda__1___closed__6;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_getLocalDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_getConstInfo___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__1___closed__4;
static lean_object* l_Lean_Compiler_LCNF_mkAuxJpDecl_x27___closed__1;
static lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_InferType_inferType___spec__1___closed__2;
static lean_object* l_Lean_getConstInfo___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__1___closed__1;
static lean_object* l_Lean_Compiler_LCNF_InferType_inferType___closed__3;
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_InferType_inferType___spec__1___closed__1;
lean_object* l_Lean_Compiler_LCNF_getLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_InferType_getLevel_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_InferType_inferType___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_panic___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__3___closed__2;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__10(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_getLocalDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_1);
x_7 = lean_local_ctx_find(x_2, x_1);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_getLocalDecl(x_1, x_3, x_4, x_5, x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_1);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_6);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_getLocalDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_InferType_getLocalDecl(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
static lean_object* _init_l_panic___at_Lean_Compiler_LCNF_InferType_mkForallFVars___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Core_instMonadCoreM;
x_2 = l_ReaderT_instMonadReaderT___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_panic___at_Lean_Compiler_LCNF_InferType_mkForallFVars___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_panic___at_Lean_Compiler_LCNF_InferType_mkForallFVars___spec__1___closed__1;
x_2 = l_Lean_instInhabitedExpr;
x_3 = l_instInhabited___rarg(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_panic___at_Lean_Compiler_LCNF_InferType_mkForallFVars___spec__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_panic___at_Lean_Compiler_LCNF_InferType_mkForallFVars___spec__1___closed__2;
x_2 = lean_alloc_closure((void*)(l_instInhabitedReaderT___rarg___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_Compiler_LCNF_InferType_mkForallFVars___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = l_panic___at_Lean_Compiler_LCNF_InferType_mkForallFVars___spec__1___closed__3;
x_8 = lean_panic_fn(x_7, x_1);
x_9 = lean_apply_5(x_8, x_2, x_3, x_4, x_5, x_6);
return x_9;
}
}
static lean_object* _init_l_Nat_foldRevM_loop___at_Lean_Compiler_LCNF_InferType_mkForallFVars___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Init.Util", 9);
return x_1;
}
}
static lean_object* _init_l_Nat_foldRevM_loop___at_Lean_Compiler_LCNF_InferType_mkForallFVars___spec__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("getElem!", 8);
return x_1;
}
}
static lean_object* _init_l_Nat_foldRevM_loop___at_Lean_Compiler_LCNF_InferType_mkForallFVars___spec__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("index out of bounds", 19);
return x_1;
}
}
static lean_object* _init_l_Nat_foldRevM_loop___at_Lean_Compiler_LCNF_InferType_mkForallFVars___spec__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Nat_foldRevM_loop___at_Lean_Compiler_LCNF_InferType_mkForallFVars___spec__2___closed__1;
x_2 = l_Nat_foldRevM_loop___at_Lean_Compiler_LCNF_InferType_mkForallFVars___spec__2___closed__2;
x_3 = lean_unsigned_to_nat(77u);
x_4 = lean_unsigned_to_nat(36u);
x_5 = l_Nat_foldRevM_loop___at_Lean_Compiler_LCNF_InferType_mkForallFVars___spec__2___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Nat_foldRevM_loop___at_Lean_Compiler_LCNF_InferType_mkForallFVars___spec__2___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Compiler.LCNF.InferType", 28);
return x_1;
}
}
static lean_object* _init_l_Nat_foldRevM_loop___at_Lean_Compiler_LCNF_InferType_mkForallFVars___spec__2___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Compiler.LCNF.InferType.mkForallFVars", 42);
return x_1;
}
}
static lean_object* _init_l_Nat_foldRevM_loop___at_Lean_Compiler_LCNF_InferType_mkForallFVars___spec__2___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("unreachable code has been reached", 33);
return x_1;
}
}
static lean_object* _init_l_Nat_foldRevM_loop___at_Lean_Compiler_LCNF_InferType_mkForallFVars___spec__2___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Nat_foldRevM_loop___at_Lean_Compiler_LCNF_InferType_mkForallFVars___spec__2___closed__5;
x_2 = l_Nat_foldRevM_loop___at_Lean_Compiler_LCNF_InferType_mkForallFVars___spec__2___closed__6;
x_3 = lean_unsigned_to_nat(28u);
x_4 = lean_unsigned_to_nat(53u);
x_5 = l_Nat_foldRevM_loop___at_Lean_Compiler_LCNF_InferType_mkForallFVars___spec__2___closed__7;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRevM_loop___at_Lean_Compiler_LCNF_InferType_mkForallFVars___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_nat_dec_eq(x_2, x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_sub(x_2, x_11);
lean_dec(x_2);
x_13 = lean_array_get_size(x_1);
x_14 = lean_nat_dec_lt(x_12, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = l_Nat_foldRevM_loop___at_Lean_Compiler_LCNF_InferType_mkForallFVars___spec__2___closed__4;
x_16 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_15);
x_17 = l_Lean_Expr_fvarId_x21(x_16);
lean_inc(x_4);
x_18 = l_Lean_Compiler_LCNF_InferType_getLocalDecl(x_17, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_ctor_get(x_19, 2);
lean_inc(x_21);
x_22 = lean_ctor_get(x_19, 3);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_expr_abstract_range(x_22, x_12, x_1);
lean_dec(x_22);
x_24 = 0;
x_25 = l_Lean_Expr_forallE___override(x_21, x_23, x_3, x_24);
x_2 = x_12;
x_3 = x_25;
x_8 = x_20;
goto _start;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_19);
lean_dec(x_3);
x_27 = lean_ctor_get(x_18, 1);
lean_inc(x_27);
lean_dec(x_18);
x_28 = l_Nat_foldRevM_loop___at_Lean_Compiler_LCNF_InferType_mkForallFVars___spec__2___closed__8;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_29 = l_panic___at_Lean_Compiler_LCNF_InferType_mkForallFVars___spec__1(x_28, x_4, x_5, x_6, x_7, x_27);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_2 = x_12;
x_3 = x_30;
x_8 = x_31;
goto _start;
}
else
{
uint8_t x_33; 
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_33 = !lean_is_exclusive(x_29);
if (x_33 == 0)
{
return x_29;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_29, 0);
x_35 = lean_ctor_get(x_29, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_29);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
else
{
uint8_t x_37; 
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_37 = !lean_is_exclusive(x_18);
if (x_37 == 0)
{
return x_18;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_18, 0);
x_39 = lean_ctor_get(x_18, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_18);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_array_fget(x_1, x_12);
x_42 = l_Lean_Expr_fvarId_x21(x_41);
lean_inc(x_4);
x_43 = l_Lean_Compiler_LCNF_InferType_getLocalDecl(x_42, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; 
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = lean_ctor_get(x_44, 2);
lean_inc(x_46);
x_47 = lean_ctor_get(x_44, 3);
lean_inc(x_47);
lean_dec(x_44);
x_48 = lean_expr_abstract_range(x_47, x_12, x_1);
lean_dec(x_47);
x_49 = 0;
x_50 = l_Lean_Expr_forallE___override(x_46, x_48, x_3, x_49);
x_2 = x_12;
x_3 = x_50;
x_8 = x_45;
goto _start;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_44);
lean_dec(x_3);
x_52 = lean_ctor_get(x_43, 1);
lean_inc(x_52);
lean_dec(x_43);
x_53 = l_Nat_foldRevM_loop___at_Lean_Compiler_LCNF_InferType_mkForallFVars___spec__2___closed__8;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_54 = l_panic___at_Lean_Compiler_LCNF_InferType_mkForallFVars___spec__1(x_53, x_4, x_5, x_6, x_7, x_52);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
x_2 = x_12;
x_3 = x_55;
x_8 = x_56;
goto _start;
}
else
{
uint8_t x_58; 
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_58 = !lean_is_exclusive(x_54);
if (x_58 == 0)
{
return x_54;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_54, 0);
x_60 = lean_ctor_get(x_54, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_54);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
}
else
{
uint8_t x_62; 
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_62 = !lean_is_exclusive(x_43);
if (x_62 == 0)
{
return x_43;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_43, 0);
x_64 = lean_ctor_get(x_43, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_43);
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
lean_object* x_66; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_3);
lean_ctor_set(x_66, 1, x_8);
return x_66;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_mkForallFVars(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_expr_abstract(x_2, x_1);
lean_dec(x_2);
x_9 = lean_array_get_size(x_1);
x_10 = l_Nat_foldRevM_loop___at_Lean_Compiler_LCNF_InferType_mkForallFVars___spec__2(x_1, x_9, x_8, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRevM_loop___at_Lean_Compiler_LCNF_InferType_mkForallFVars___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Nat_foldRevM_loop___at_Lean_Compiler_LCNF_InferType_mkForallFVars___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_mkForallFVars___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_InferType_mkForallFVars(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_InferType_mkForallParams___spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
lean_dec(x_5);
x_9 = l_Lean_Expr_fvar___override(x_8);
x_10 = 1;
x_11 = lean_usize_add(x_2, x_10);
x_12 = lean_array_uset(x_7, x_2, x_9);
x_2 = x_11;
x_3 = x_12;
goto _start;
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_mkForallParams___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Std_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_mkForallParams___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_InferType_mkForallParams___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_mkForallParams___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_InferType_mkForallParams___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_mkForallParams___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_mkForallParams___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_InferType_mkForallParams___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_mkForallParams___closed__6() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = l_Lean_Compiler_LCNF_InferType_mkForallParams___closed__5;
x_3 = l_Lean_Compiler_LCNF_InferType_mkForallParams___closed__4;
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
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_mkForallParams___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_InferType_mkForallParams___closed__3;
x_2 = l_Lean_Compiler_LCNF_InferType_mkForallParams___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_mkForallParams(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_array_get_size(x_1);
x_9 = lean_usize_of_nat(x_8);
lean_dec(x_8);
x_10 = 0;
x_11 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_InferType_mkForallParams___spec__1(x_9, x_10, x_1);
x_12 = l_Lean_Compiler_LCNF_InferType_mkForallParams___closed__7;
x_13 = l_Lean_Compiler_LCNF_InferType_mkForallFVars(x_11, x_2, x_12, x_4, x_5, x_6, x_7);
lean_dec(x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_InferType_mkForallParams___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_InferType_mkForallParams___spec__1(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_mkForallParams___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_InferType_mkForallParams(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at_Lean_Compiler_LCNF_InferType_withLocalDecl___spec__2___rarg(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at_Lean_Compiler_LCNF_InferType_withLocalDecl___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lean_mkFreshId___at_Lean_Compiler_LCNF_InferType_withLocalDecl___spec__2___rarg___boxed), 2, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at_Lean_Compiler_LCNF_InferType_withLocalDecl___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = l_Lean_mkFreshId___at_Lean_Compiler_LCNF_InferType_withLocalDecl___spec__2___rarg(x_4, x_5);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
return x_6;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_6);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_withLocalDecl___rarg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = l_Lean_mkFreshFVarId___at_Lean_Compiler_LCNF_InferType_withLocalDecl___spec__1(x_5, x_6, x_7, x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_11);
x_13 = l_Lean_Expr_fvar___override(x_11);
x_14 = lean_local_ctx_mk_local_decl(x_5, x_11, x_1, x_2, x_3);
x_15 = lean_apply_6(x_4, x_13, x_14, x_6, x_7, x_8, x_12);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_withLocalDecl(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_InferType_withLocalDecl___rarg___boxed), 9, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at_Lean_Compiler_LCNF_InferType_withLocalDecl___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_mkFreshId___at_Lean_Compiler_LCNF_InferType_withLocalDecl___spec__2___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at_Lean_Compiler_LCNF_InferType_withLocalDecl___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_mkFreshId___at_Lean_Compiler_LCNF_InferType_withLocalDecl___spec__2(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at_Lean_Compiler_LCNF_InferType_withLocalDecl___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_mkFreshFVarId___at_Lean_Compiler_LCNF_InferType_withLocalDecl___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_withLocalDecl___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_3);
lean_dec(x_3);
x_11 = l_Lean_Compiler_LCNF_InferType_withLocalDecl___rarg(x_1, x_2, x_10, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_inferFVarType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_InferType_getLocalDecl(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = l_Lean_LocalDecl_type(x_9);
lean_dec(x_9);
lean_ctor_set(x_7, 0, x_10);
return x_7;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_7, 0);
x_12 = lean_ctor_get(x_7, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_7);
x_13 = l_Lean_LocalDecl_type(x_11);
lean_dec(x_11);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_7);
if (x_15 == 0)
{
return x_7;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_7, 0);
x_17 = lean_ctor_get(x_7, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_7);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_inferFVarType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_InferType_inferFVarType(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_inferConstType___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("lcAny", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_inferConstType___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_InferType_inferConstType___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_inferConstType___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("lcErased", 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_inferConstType___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_InferType_inferConstType___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_inferConstType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = l_Lean_Compiler_LCNF_InferType_inferConstType___closed__2;
x_7 = lean_name_eq(x_1, x_6);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = l_Lean_Compiler_LCNF_InferType_inferConstType___closed__4;
x_9 = lean_name_eq(x_1, x_8);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_instantiateLCNFTypeLevelParams(x_1, x_2, x_3, x_4, x_5);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = l_Lean_Compiler_LCNF_anyTypeExpr;
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
x_13 = l_Lean_Compiler_LCNF_anyTypeExpr;
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_5);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_inferLambdaType_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 6:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 2);
lean_inc(x_11);
x_12 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
lean_dec(x_1);
x_13 = lean_expr_instantiate_rev(x_10, x_3);
lean_dec(x_10);
x_14 = l_Lean_mkFreshFVarId___at_Lean_Compiler_LCNF_InferType_withLocalDecl___spec__1(x_4, x_5, x_6, x_7, x_8);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_15);
x_17 = l_Lean_Expr_fvar___override(x_15);
x_18 = lean_local_ctx_mk_local_decl(x_4, x_15, x_9, x_13, x_12);
lean_inc(x_17);
x_19 = lean_array_push(x_2, x_17);
x_20 = lean_array_push(x_3, x_17);
x_1 = x_11;
x_2 = x_19;
x_3 = x_20;
x_4 = x_18;
x_8 = x_16;
goto _start;
}
case 8:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; 
x_22 = lean_ctor_get(x_1, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_1, 1);
lean_inc(x_23);
x_24 = lean_ctor_get(x_1, 3);
lean_inc(x_24);
lean_dec(x_1);
x_25 = lean_expr_instantiate_rev(x_23, x_3);
lean_dec(x_23);
x_26 = l_Lean_mkFreshFVarId___at_Lean_Compiler_LCNF_InferType_withLocalDecl___spec__1(x_4, x_5, x_6, x_7, x_8);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
lean_inc(x_27);
x_29 = l_Lean_Expr_fvar___override(x_27);
x_30 = 0;
x_31 = lean_local_ctx_mk_local_decl(x_4, x_27, x_22, x_25, x_30);
x_32 = lean_array_push(x_3, x_29);
x_1 = x_24;
x_3 = x_32;
x_4 = x_31;
x_8 = x_28;
goto _start;
}
default: 
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_expr_instantiate_rev(x_1, x_3);
lean_dec(x_3);
lean_dec(x_1);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_35 = l_Lean_Compiler_LCNF_InferType_inferType(x_34, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = l_Lean_Compiler_LCNF_InferType_mkForallFVars(x_2, x_36, x_4, x_5, x_6, x_7, x_37);
lean_dec(x_2);
return x_38;
}
else
{
uint8_t x_39; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_39 = !lean_is_exclusive(x_35);
if (x_39 == 0)
{
return x_35;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_35, 0);
x_41 = lean_ctor_get(x_35, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_35);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
}
}
}
static lean_object* _init_l_Lean_throwError___at_Lean_Compiler_LCNF_InferType_inferType___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_InferType_mkForallParams___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_throwError___at_Lean_Compiler_LCNF_InferType_inferType___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_InferType_mkForallParams___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_throwError___at_Lean_Compiler_LCNF_InferType_inferType___spec__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_InferType_mkForallParams___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_throwError___at_Lean_Compiler_LCNF_InferType_inferType___spec__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_throwError___at_Lean_Compiler_LCNF_InferType_inferType___spec__1___closed__1;
x_3 = l_Lean_throwError___at_Lean_Compiler_LCNF_InferType_inferType___spec__1___closed__2;
x_4 = l_Lean_throwError___at_Lean_Compiler_LCNF_InferType_inferType___spec__1___closed__3;
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
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_InferType_inferType___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_7 = lean_ctor_get(x_4, 5);
x_8 = lean_st_ref_get(x_5, x_6);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_st_ref_get(x_3, x_10);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
x_16 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_15);
x_17 = lean_ctor_get(x_4, 2);
x_18 = l_Lean_throwError___at_Lean_Compiler_LCNF_InferType_inferType___spec__1___closed__4;
lean_inc(x_17);
x_19 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_19, 0, x_11);
lean_ctor_set(x_19, 1, x_18);
lean_ctor_set(x_19, 2, x_16);
lean_ctor_set(x_19, 3, x_17);
x_20 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_1);
lean_inc(x_7);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_7);
lean_ctor_set(x_21, 1, x_20);
lean_ctor_set_tag(x_12, 1);
lean_ctor_set(x_12, 0, x_21);
return x_12;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_22 = lean_ctor_get(x_12, 0);
x_23 = lean_ctor_get(x_12, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_12);
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_24);
x_26 = lean_ctor_get(x_4, 2);
x_27 = l_Lean_throwError___at_Lean_Compiler_LCNF_InferType_inferType___spec__1___closed__4;
lean_inc(x_26);
x_28 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_28, 0, x_11);
lean_ctor_set(x_28, 1, x_27);
lean_ctor_set(x_28, 2, x_25);
lean_ctor_set(x_28, 3, x_26);
x_29 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_1);
lean_inc(x_7);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_7);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_23);
return x_31;
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_inferType___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("unexpected bound variable ", 26);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_inferType___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_InferType_inferType___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_inferType___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("", 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_inferType___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_InferType_inferType___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_inferType___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("unexpected metavariable ", 24);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_inferType___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_InferType_inferType___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_inferType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_7, 0, x_1);
x_8 = l_Lean_Compiler_LCNF_InferType_inferType___closed__2;
x_9 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
x_10 = l_Lean_Compiler_LCNF_InferType_inferType___closed__4;
x_11 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = l_Lean_throwError___at_Lean_Compiler_LCNF_InferType_inferType___spec__1(x_11, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
case 1:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
lean_dec(x_1);
x_14 = l_Lean_Compiler_LCNF_InferType_inferFVarType(x_13, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_14;
}
case 2:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_15, 0, x_1);
x_16 = l_Lean_Compiler_LCNF_InferType_inferType___closed__6;
x_17 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
x_18 = l_Lean_Compiler_LCNF_InferType_inferType___closed__4;
x_19 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Lean_throwError___at_Lean_Compiler_LCNF_InferType_inferType___spec__1(x_19, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_20;
}
case 3:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_21 = lean_ctor_get(x_1, 0);
lean_inc(x_21);
lean_dec(x_1);
x_22 = l_Lean_Level_succ___override(x_21);
x_23 = l_Lean_Expr_sort___override(x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_6);
return x_24;
}
case 4:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_3);
lean_dec(x_2);
x_25 = lean_ctor_get(x_1, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_1, 1);
lean_inc(x_26);
lean_dec(x_1);
x_27 = l_Lean_Compiler_LCNF_InferType_inferConstType(x_25, x_26, x_4, x_5, x_6);
return x_27;
}
case 5:
{
lean_object* x_28; 
x_28 = l_Lean_Compiler_LCNF_InferType_inferAppType(x_1, x_2, x_3, x_4, x_5, x_6);
return x_28;
}
case 7:
{
lean_object* x_29; 
x_29 = l_Lean_Compiler_LCNF_InferType_inferForallType(x_1, x_2, x_3, x_4, x_5, x_6);
return x_29;
}
case 9:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_30 = lean_ctor_get(x_1, 0);
lean_inc(x_30);
lean_dec(x_1);
x_31 = l_Lean_Literal_type(x_30);
lean_dec(x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_6);
return x_32;
}
case 10:
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_1, 1);
lean_inc(x_33);
lean_dec(x_1);
x_1 = x_33;
goto _start;
}
case 11:
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_1, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_1, 1);
lean_inc(x_36);
x_37 = lean_ctor_get(x_1, 2);
lean_inc(x_37);
lean_dec(x_1);
x_38 = l_Lean_Compiler_LCNF_InferType_inferProjType(x_35, x_36, x_37, x_2, x_3, x_4, x_5, x_6);
return x_38;
}
default: 
{
lean_object* x_39; 
x_39 = l_Lean_Compiler_LCNF_InferType_inferLambdaType(x_1, x_2, x_3, x_4, x_5, x_6);
return x_39;
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_inferLambdaType___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_inferLambdaType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_Compiler_LCNF_InferType_inferLambdaType___closed__1;
x_8 = l_Lean_Compiler_LCNF_InferType_inferLambdaType_go(x_1, x_7, x_7, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_inferForallType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_Compiler_LCNF_InferType_inferLambdaType___closed__1;
x_8 = l_Lean_Compiler_LCNF_InferType_inferForallType_go(x_1, x_7, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_anyTypeExpr;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_4, x_3);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_5);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_array_uget(x_2, x_4);
x_14 = !lean_is_exclusive(x_5);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_5, 1);
x_16 = lean_ctor_get(x_5, 0);
lean_dec(x_16);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_17 = l_Lean_Compiler_LCNF_InferType_inferType(x_13, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_20 = l_Lean_Compiler_LCNF_InferType_getLevel_x3f(x_18, x_6, x_7, x_8, x_9, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_22 = !lean_is_exclusive(x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_20, 0);
lean_dec(x_23);
x_24 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__1___closed__1;
lean_ctor_set(x_5, 0, x_24);
lean_ctor_set(x_20, 0, x_5);
return x_20;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_20, 1);
lean_inc(x_25);
lean_dec(x_20);
x_26 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__1___closed__1;
lean_ctor_set(x_5, 0, x_26);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_5);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; size_t x_31; size_t x_32; 
x_28 = lean_ctor_get(x_20, 1);
lean_inc(x_28);
lean_dec(x_20);
x_29 = lean_ctor_get(x_21, 0);
lean_inc(x_29);
lean_dec(x_21);
x_30 = l_Lean_Level_imax___override(x_29, x_15);
lean_inc(x_1);
lean_ctor_set(x_5, 1, x_30);
lean_ctor_set(x_5, 0, x_1);
x_31 = 1;
x_32 = lean_usize_add(x_4, x_31);
x_4 = x_32;
x_10 = x_28;
goto _start;
}
}
else
{
uint8_t x_34; 
lean_free_object(x_5);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_34 = !lean_is_exclusive(x_20);
if (x_34 == 0)
{
return x_20;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_20, 0);
x_36 = lean_ctor_get(x_20, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_20);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
else
{
uint8_t x_38; 
lean_free_object(x_5);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_17);
if (x_38 == 0)
{
return x_17;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_17, 0);
x_40 = lean_ctor_get(x_17, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_17);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
else
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_5, 1);
lean_inc(x_42);
lean_dec(x_5);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_43 = l_Lean_Compiler_LCNF_InferType_inferType(x_13, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_46 = l_Lean_Compiler_LCNF_InferType_getLevel_x3f(x_44, x_6, x_7, x_8, x_9, x_45);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_49 = x_46;
} else {
 lean_dec_ref(x_46);
 x_49 = lean_box(0);
}
x_50 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__1___closed__1;
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_42);
if (lean_is_scalar(x_49)) {
 x_52 = lean_alloc_ctor(0, 2, 0);
} else {
 x_52 = x_49;
}
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_48);
return x_52;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; size_t x_57; size_t x_58; 
x_53 = lean_ctor_get(x_46, 1);
lean_inc(x_53);
lean_dec(x_46);
x_54 = lean_ctor_get(x_47, 0);
lean_inc(x_54);
lean_dec(x_47);
x_55 = l_Lean_Level_imax___override(x_54, x_42);
lean_inc(x_1);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_1);
lean_ctor_set(x_56, 1, x_55);
x_57 = 1;
x_58 = lean_usize_add(x_4, x_57);
x_4 = x_58;
x_5 = x_56;
x_10 = x_53;
goto _start;
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_42);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_60 = lean_ctor_get(x_46, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_46, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_62 = x_46;
} else {
 lean_dec_ref(x_46);
 x_62 = lean_box(0);
}
if (lean_is_scalar(x_62)) {
 x_63 = lean_alloc_ctor(1, 2, 0);
} else {
 x_63 = x_62;
}
lean_ctor_set(x_63, 0, x_60);
lean_ctor_set(x_63, 1, x_61);
return x_63;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_42);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_64 = lean_ctor_get(x_43, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_43, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_66 = x_43;
} else {
 lean_dec_ref(x_43);
 x_66 = lean_box(0);
}
if (lean_is_scalar(x_66)) {
 x_67 = lean_alloc_ctor(1, 2, 0);
} else {
 x_67 = x_66;
}
lean_ctor_set(x_67, 0, x_64);
lean_ctor_set(x_67, 1, x_65);
return x_67;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_4, x_3);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_5);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_array_uget(x_2, x_4);
x_14 = !lean_is_exclusive(x_5);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_5, 1);
x_16 = lean_ctor_get(x_5, 0);
lean_dec(x_16);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_17 = l_Lean_Compiler_LCNF_InferType_inferType(x_13, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_20 = l_Lean_Compiler_LCNF_InferType_getLevel_x3f(x_18, x_6, x_7, x_8, x_9, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_22 = !lean_is_exclusive(x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_20, 0);
lean_dec(x_23);
x_24 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__1___closed__1;
lean_ctor_set(x_5, 0, x_24);
lean_ctor_set(x_20, 0, x_5);
return x_20;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_20, 1);
lean_inc(x_25);
lean_dec(x_20);
x_26 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__1___closed__1;
lean_ctor_set(x_5, 0, x_26);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_5);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; size_t x_31; size_t x_32; 
x_28 = lean_ctor_get(x_20, 1);
lean_inc(x_28);
lean_dec(x_20);
x_29 = lean_ctor_get(x_21, 0);
lean_inc(x_29);
lean_dec(x_21);
x_30 = l_Lean_Level_imax___override(x_29, x_15);
lean_inc(x_1);
lean_ctor_set(x_5, 1, x_30);
lean_ctor_set(x_5, 0, x_1);
x_31 = 1;
x_32 = lean_usize_add(x_4, x_31);
x_4 = x_32;
x_10 = x_28;
goto _start;
}
}
else
{
uint8_t x_34; 
lean_free_object(x_5);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_34 = !lean_is_exclusive(x_20);
if (x_34 == 0)
{
return x_20;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_20, 0);
x_36 = lean_ctor_get(x_20, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_20);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
else
{
uint8_t x_38; 
lean_free_object(x_5);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_17);
if (x_38 == 0)
{
return x_17;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_17, 0);
x_40 = lean_ctor_get(x_17, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_17);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
else
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_5, 1);
lean_inc(x_42);
lean_dec(x_5);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_43 = l_Lean_Compiler_LCNF_InferType_inferType(x_13, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_46 = l_Lean_Compiler_LCNF_InferType_getLevel_x3f(x_44, x_6, x_7, x_8, x_9, x_45);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_49 = x_46;
} else {
 lean_dec_ref(x_46);
 x_49 = lean_box(0);
}
x_50 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__1___closed__1;
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_42);
if (lean_is_scalar(x_49)) {
 x_52 = lean_alloc_ctor(0, 2, 0);
} else {
 x_52 = x_49;
}
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_48);
return x_52;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; size_t x_57; size_t x_58; 
x_53 = lean_ctor_get(x_46, 1);
lean_inc(x_53);
lean_dec(x_46);
x_54 = lean_ctor_get(x_47, 0);
lean_inc(x_54);
lean_dec(x_47);
x_55 = l_Lean_Level_imax___override(x_54, x_42);
lean_inc(x_1);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_1);
lean_ctor_set(x_56, 1, x_55);
x_57 = 1;
x_58 = lean_usize_add(x_4, x_57);
x_4 = x_58;
x_5 = x_56;
x_10 = x_53;
goto _start;
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_42);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_60 = lean_ctor_get(x_46, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_46, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_62 = x_46;
} else {
 lean_dec_ref(x_46);
 x_62 = lean_box(0);
}
if (lean_is_scalar(x_62)) {
 x_63 = lean_alloc_ctor(1, 2, 0);
} else {
 x_63 = x_62;
}
lean_ctor_set(x_63, 0, x_60);
lean_ctor_set(x_63, 1, x_61);
return x_63;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_42);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_64 = lean_ctor_get(x_43, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_43, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_66 = x_43;
} else {
 lean_dec_ref(x_43);
 x_66 = lean_box(0);
}
if (lean_is_scalar(x_66)) {
 x_67 = lean_alloc_ctor(1, 2, 0);
} else {
 x_67 = x_66;
}
lean_ctor_set(x_67, 0, x_64);
lean_ctor_set(x_67, 1, x_65);
return x_67;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__3(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_4, x_3);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_5);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_array_uget(x_2, x_4);
x_14 = !lean_is_exclusive(x_5);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_5, 1);
x_16 = lean_ctor_get(x_5, 0);
lean_dec(x_16);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_17 = l_Lean_Compiler_LCNF_InferType_inferType(x_13, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_20 = l_Lean_Compiler_LCNF_InferType_getLevel_x3f(x_18, x_6, x_7, x_8, x_9, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_22 = !lean_is_exclusive(x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_20, 0);
lean_dec(x_23);
x_24 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__1___closed__1;
lean_ctor_set(x_5, 0, x_24);
lean_ctor_set(x_20, 0, x_5);
return x_20;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_20, 1);
lean_inc(x_25);
lean_dec(x_20);
x_26 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__1___closed__1;
lean_ctor_set(x_5, 0, x_26);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_5);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; size_t x_31; size_t x_32; 
x_28 = lean_ctor_get(x_20, 1);
lean_inc(x_28);
lean_dec(x_20);
x_29 = lean_ctor_get(x_21, 0);
lean_inc(x_29);
lean_dec(x_21);
x_30 = l_Lean_Level_imax___override(x_29, x_15);
lean_inc(x_1);
lean_ctor_set(x_5, 1, x_30);
lean_ctor_set(x_5, 0, x_1);
x_31 = 1;
x_32 = lean_usize_add(x_4, x_31);
x_4 = x_32;
x_10 = x_28;
goto _start;
}
}
else
{
uint8_t x_34; 
lean_free_object(x_5);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_34 = !lean_is_exclusive(x_20);
if (x_34 == 0)
{
return x_20;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_20, 0);
x_36 = lean_ctor_get(x_20, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_20);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
else
{
uint8_t x_38; 
lean_free_object(x_5);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_17);
if (x_38 == 0)
{
return x_17;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_17, 0);
x_40 = lean_ctor_get(x_17, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_17);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
else
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_5, 1);
lean_inc(x_42);
lean_dec(x_5);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_43 = l_Lean_Compiler_LCNF_InferType_inferType(x_13, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_46 = l_Lean_Compiler_LCNF_InferType_getLevel_x3f(x_44, x_6, x_7, x_8, x_9, x_45);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_49 = x_46;
} else {
 lean_dec_ref(x_46);
 x_49 = lean_box(0);
}
x_50 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__1___closed__1;
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_42);
if (lean_is_scalar(x_49)) {
 x_52 = lean_alloc_ctor(0, 2, 0);
} else {
 x_52 = x_49;
}
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_48);
return x_52;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; size_t x_57; size_t x_58; 
x_53 = lean_ctor_get(x_46, 1);
lean_inc(x_53);
lean_dec(x_46);
x_54 = lean_ctor_get(x_47, 0);
lean_inc(x_54);
lean_dec(x_47);
x_55 = l_Lean_Level_imax___override(x_54, x_42);
lean_inc(x_1);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_1);
lean_ctor_set(x_56, 1, x_55);
x_57 = 1;
x_58 = lean_usize_add(x_4, x_57);
x_4 = x_58;
x_5 = x_56;
x_10 = x_53;
goto _start;
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_42);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_60 = lean_ctor_get(x_46, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_46, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_62 = x_46;
} else {
 lean_dec_ref(x_46);
 x_62 = lean_box(0);
}
if (lean_is_scalar(x_62)) {
 x_63 = lean_alloc_ctor(1, 2, 0);
} else {
 x_63 = x_62;
}
lean_ctor_set(x_63, 0, x_60);
lean_ctor_set(x_63, 1, x_61);
return x_63;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_42);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_64 = lean_ctor_get(x_43, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_43, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_66 = x_43;
} else {
 lean_dec_ref(x_43);
 x_66 = lean_box(0);
}
if (lean_is_scalar(x_66)) {
 x_67 = lean_alloc_ctor(1, 2, 0);
} else {
 x_67 = x_66;
}
lean_ctor_set(x_67, 0, x_64);
lean_ctor_set(x_67, 1, x_65);
return x_67;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__4(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_4, x_3);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_5);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_array_uget(x_2, x_4);
x_14 = !lean_is_exclusive(x_5);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_5, 1);
x_16 = lean_ctor_get(x_5, 0);
lean_dec(x_16);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_17 = l_Lean_Compiler_LCNF_InferType_inferType(x_13, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_20 = l_Lean_Compiler_LCNF_InferType_getLevel_x3f(x_18, x_6, x_7, x_8, x_9, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_22 = !lean_is_exclusive(x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_20, 0);
lean_dec(x_23);
x_24 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__1___closed__1;
lean_ctor_set(x_5, 0, x_24);
lean_ctor_set(x_20, 0, x_5);
return x_20;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_20, 1);
lean_inc(x_25);
lean_dec(x_20);
x_26 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__1___closed__1;
lean_ctor_set(x_5, 0, x_26);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_5);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; size_t x_31; size_t x_32; 
x_28 = lean_ctor_get(x_20, 1);
lean_inc(x_28);
lean_dec(x_20);
x_29 = lean_ctor_get(x_21, 0);
lean_inc(x_29);
lean_dec(x_21);
x_30 = l_Lean_Level_imax___override(x_29, x_15);
lean_inc(x_1);
lean_ctor_set(x_5, 1, x_30);
lean_ctor_set(x_5, 0, x_1);
x_31 = 1;
x_32 = lean_usize_add(x_4, x_31);
x_4 = x_32;
x_10 = x_28;
goto _start;
}
}
else
{
uint8_t x_34; 
lean_free_object(x_5);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_34 = !lean_is_exclusive(x_20);
if (x_34 == 0)
{
return x_20;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_20, 0);
x_36 = lean_ctor_get(x_20, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_20);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
else
{
uint8_t x_38; 
lean_free_object(x_5);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_17);
if (x_38 == 0)
{
return x_17;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_17, 0);
x_40 = lean_ctor_get(x_17, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_17);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
else
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_5, 1);
lean_inc(x_42);
lean_dec(x_5);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_43 = l_Lean_Compiler_LCNF_InferType_inferType(x_13, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_46 = l_Lean_Compiler_LCNF_InferType_getLevel_x3f(x_44, x_6, x_7, x_8, x_9, x_45);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_49 = x_46;
} else {
 lean_dec_ref(x_46);
 x_49 = lean_box(0);
}
x_50 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__1___closed__1;
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_42);
if (lean_is_scalar(x_49)) {
 x_52 = lean_alloc_ctor(0, 2, 0);
} else {
 x_52 = x_49;
}
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_48);
return x_52;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; size_t x_57; size_t x_58; 
x_53 = lean_ctor_get(x_46, 1);
lean_inc(x_53);
lean_dec(x_46);
x_54 = lean_ctor_get(x_47, 0);
lean_inc(x_54);
lean_dec(x_47);
x_55 = l_Lean_Level_imax___override(x_54, x_42);
lean_inc(x_1);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_1);
lean_ctor_set(x_56, 1, x_55);
x_57 = 1;
x_58 = lean_usize_add(x_4, x_57);
x_4 = x_58;
x_5 = x_56;
x_10 = x_53;
goto _start;
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_42);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_60 = lean_ctor_get(x_46, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_46, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_62 = x_46;
} else {
 lean_dec_ref(x_46);
 x_62 = lean_box(0);
}
if (lean_is_scalar(x_62)) {
 x_63 = lean_alloc_ctor(1, 2, 0);
} else {
 x_63 = x_62;
}
lean_ctor_set(x_63, 0, x_60);
lean_ctor_set(x_63, 1, x_61);
return x_63;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_42);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_64 = lean_ctor_get(x_43, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_43, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_66 = x_43;
} else {
 lean_dec_ref(x_43);
 x_66 = lean_box(0);
}
if (lean_is_scalar(x_66)) {
 x_67 = lean_alloc_ctor(1, 2, 0);
} else {
 x_67 = x_66;
}
lean_ctor_set(x_67, 0, x_64);
lean_ctor_set(x_67, 1, x_65);
return x_67;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__5(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_4, x_3);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_5);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_array_uget(x_2, x_4);
x_14 = !lean_is_exclusive(x_5);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_5, 1);
x_16 = lean_ctor_get(x_5, 0);
lean_dec(x_16);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_17 = l_Lean_Compiler_LCNF_InferType_inferType(x_13, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_20 = l_Lean_Compiler_LCNF_InferType_getLevel_x3f(x_18, x_6, x_7, x_8, x_9, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_22 = !lean_is_exclusive(x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_20, 0);
lean_dec(x_23);
x_24 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__1___closed__1;
lean_ctor_set(x_5, 0, x_24);
lean_ctor_set(x_20, 0, x_5);
return x_20;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_20, 1);
lean_inc(x_25);
lean_dec(x_20);
x_26 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__1___closed__1;
lean_ctor_set(x_5, 0, x_26);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_5);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; size_t x_31; size_t x_32; 
x_28 = lean_ctor_get(x_20, 1);
lean_inc(x_28);
lean_dec(x_20);
x_29 = lean_ctor_get(x_21, 0);
lean_inc(x_29);
lean_dec(x_21);
x_30 = l_Lean_Level_imax___override(x_29, x_15);
lean_inc(x_1);
lean_ctor_set(x_5, 1, x_30);
lean_ctor_set(x_5, 0, x_1);
x_31 = 1;
x_32 = lean_usize_add(x_4, x_31);
x_4 = x_32;
x_10 = x_28;
goto _start;
}
}
else
{
uint8_t x_34; 
lean_free_object(x_5);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_34 = !lean_is_exclusive(x_20);
if (x_34 == 0)
{
return x_20;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_20, 0);
x_36 = lean_ctor_get(x_20, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_20);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
else
{
uint8_t x_38; 
lean_free_object(x_5);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_17);
if (x_38 == 0)
{
return x_17;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_17, 0);
x_40 = lean_ctor_get(x_17, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_17);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
else
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_5, 1);
lean_inc(x_42);
lean_dec(x_5);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_43 = l_Lean_Compiler_LCNF_InferType_inferType(x_13, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_46 = l_Lean_Compiler_LCNF_InferType_getLevel_x3f(x_44, x_6, x_7, x_8, x_9, x_45);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_49 = x_46;
} else {
 lean_dec_ref(x_46);
 x_49 = lean_box(0);
}
x_50 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__1___closed__1;
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_42);
if (lean_is_scalar(x_49)) {
 x_52 = lean_alloc_ctor(0, 2, 0);
} else {
 x_52 = x_49;
}
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_48);
return x_52;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; size_t x_57; size_t x_58; 
x_53 = lean_ctor_get(x_46, 1);
lean_inc(x_53);
lean_dec(x_46);
x_54 = lean_ctor_get(x_47, 0);
lean_inc(x_54);
lean_dec(x_47);
x_55 = l_Lean_Level_imax___override(x_54, x_42);
lean_inc(x_1);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_1);
lean_ctor_set(x_56, 1, x_55);
x_57 = 1;
x_58 = lean_usize_add(x_4, x_57);
x_4 = x_58;
x_5 = x_56;
x_10 = x_53;
goto _start;
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_42);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_60 = lean_ctor_get(x_46, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_46, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_62 = x_46;
} else {
 lean_dec_ref(x_46);
 x_62 = lean_box(0);
}
if (lean_is_scalar(x_62)) {
 x_63 = lean_alloc_ctor(1, 2, 0);
} else {
 x_63 = x_62;
}
lean_ctor_set(x_63, 0, x_60);
lean_ctor_set(x_63, 1, x_61);
return x_63;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_42);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_64 = lean_ctor_get(x_43, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_43, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_66 = x_43;
} else {
 lean_dec_ref(x_43);
 x_66 = lean_box(0);
}
if (lean_is_scalar(x_66)) {
 x_67 = lean_alloc_ctor(1, 2, 0);
} else {
 x_67 = x_66;
}
lean_ctor_set(x_67, 0, x_64);
lean_ctor_set(x_67, 1, x_65);
return x_67;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__6(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_4, x_3);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_5);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_array_uget(x_2, x_4);
x_14 = !lean_is_exclusive(x_5);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_5, 1);
x_16 = lean_ctor_get(x_5, 0);
lean_dec(x_16);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_17 = l_Lean_Compiler_LCNF_InferType_inferType(x_13, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_20 = l_Lean_Compiler_LCNF_InferType_getLevel_x3f(x_18, x_6, x_7, x_8, x_9, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_22 = !lean_is_exclusive(x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_20, 0);
lean_dec(x_23);
x_24 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__1___closed__1;
lean_ctor_set(x_5, 0, x_24);
lean_ctor_set(x_20, 0, x_5);
return x_20;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_20, 1);
lean_inc(x_25);
lean_dec(x_20);
x_26 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__1___closed__1;
lean_ctor_set(x_5, 0, x_26);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_5);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; size_t x_31; size_t x_32; 
x_28 = lean_ctor_get(x_20, 1);
lean_inc(x_28);
lean_dec(x_20);
x_29 = lean_ctor_get(x_21, 0);
lean_inc(x_29);
lean_dec(x_21);
x_30 = l_Lean_Level_imax___override(x_29, x_15);
lean_inc(x_1);
lean_ctor_set(x_5, 1, x_30);
lean_ctor_set(x_5, 0, x_1);
x_31 = 1;
x_32 = lean_usize_add(x_4, x_31);
x_4 = x_32;
x_10 = x_28;
goto _start;
}
}
else
{
uint8_t x_34; 
lean_free_object(x_5);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_34 = !lean_is_exclusive(x_20);
if (x_34 == 0)
{
return x_20;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_20, 0);
x_36 = lean_ctor_get(x_20, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_20);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
else
{
uint8_t x_38; 
lean_free_object(x_5);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_17);
if (x_38 == 0)
{
return x_17;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_17, 0);
x_40 = lean_ctor_get(x_17, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_17);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
else
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_5, 1);
lean_inc(x_42);
lean_dec(x_5);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_43 = l_Lean_Compiler_LCNF_InferType_inferType(x_13, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_46 = l_Lean_Compiler_LCNF_InferType_getLevel_x3f(x_44, x_6, x_7, x_8, x_9, x_45);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_49 = x_46;
} else {
 lean_dec_ref(x_46);
 x_49 = lean_box(0);
}
x_50 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__1___closed__1;
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_42);
if (lean_is_scalar(x_49)) {
 x_52 = lean_alloc_ctor(0, 2, 0);
} else {
 x_52 = x_49;
}
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_48);
return x_52;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; size_t x_57; size_t x_58; 
x_53 = lean_ctor_get(x_46, 1);
lean_inc(x_53);
lean_dec(x_46);
x_54 = lean_ctor_get(x_47, 0);
lean_inc(x_54);
lean_dec(x_47);
x_55 = l_Lean_Level_imax___override(x_54, x_42);
lean_inc(x_1);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_1);
lean_ctor_set(x_56, 1, x_55);
x_57 = 1;
x_58 = lean_usize_add(x_4, x_57);
x_4 = x_58;
x_5 = x_56;
x_10 = x_53;
goto _start;
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_42);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_60 = lean_ctor_get(x_46, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_46, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_62 = x_46;
} else {
 lean_dec_ref(x_46);
 x_62 = lean_box(0);
}
if (lean_is_scalar(x_62)) {
 x_63 = lean_alloc_ctor(1, 2, 0);
} else {
 x_63 = x_62;
}
lean_ctor_set(x_63, 0, x_60);
lean_ctor_set(x_63, 1, x_61);
return x_63;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_42);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_64 = lean_ctor_get(x_43, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_43, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_66 = x_43;
} else {
 lean_dec_ref(x_43);
 x_66 = lean_box(0);
}
if (lean_is_scalar(x_66)) {
 x_67 = lean_alloc_ctor(1, 2, 0);
} else {
 x_67 = x_66;
}
lean_ctor_set(x_67, 0, x_64);
lean_ctor_set(x_67, 1, x_65);
return x_67;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__7(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_4, x_3);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_5);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_array_uget(x_2, x_4);
x_14 = !lean_is_exclusive(x_5);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_5, 1);
x_16 = lean_ctor_get(x_5, 0);
lean_dec(x_16);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_17 = l_Lean_Compiler_LCNF_InferType_inferType(x_13, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_20 = l_Lean_Compiler_LCNF_InferType_getLevel_x3f(x_18, x_6, x_7, x_8, x_9, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_22 = !lean_is_exclusive(x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_20, 0);
lean_dec(x_23);
x_24 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__1___closed__1;
lean_ctor_set(x_5, 0, x_24);
lean_ctor_set(x_20, 0, x_5);
return x_20;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_20, 1);
lean_inc(x_25);
lean_dec(x_20);
x_26 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__1___closed__1;
lean_ctor_set(x_5, 0, x_26);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_5);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; size_t x_31; size_t x_32; 
x_28 = lean_ctor_get(x_20, 1);
lean_inc(x_28);
lean_dec(x_20);
x_29 = lean_ctor_get(x_21, 0);
lean_inc(x_29);
lean_dec(x_21);
x_30 = l_Lean_Level_imax___override(x_29, x_15);
lean_inc(x_1);
lean_ctor_set(x_5, 1, x_30);
lean_ctor_set(x_5, 0, x_1);
x_31 = 1;
x_32 = lean_usize_add(x_4, x_31);
x_4 = x_32;
x_10 = x_28;
goto _start;
}
}
else
{
uint8_t x_34; 
lean_free_object(x_5);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_34 = !lean_is_exclusive(x_20);
if (x_34 == 0)
{
return x_20;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_20, 0);
x_36 = lean_ctor_get(x_20, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_20);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
else
{
uint8_t x_38; 
lean_free_object(x_5);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_17);
if (x_38 == 0)
{
return x_17;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_17, 0);
x_40 = lean_ctor_get(x_17, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_17);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
else
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_5, 1);
lean_inc(x_42);
lean_dec(x_5);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_43 = l_Lean_Compiler_LCNF_InferType_inferType(x_13, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_46 = l_Lean_Compiler_LCNF_InferType_getLevel_x3f(x_44, x_6, x_7, x_8, x_9, x_45);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_49 = x_46;
} else {
 lean_dec_ref(x_46);
 x_49 = lean_box(0);
}
x_50 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__1___closed__1;
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_42);
if (lean_is_scalar(x_49)) {
 x_52 = lean_alloc_ctor(0, 2, 0);
} else {
 x_52 = x_49;
}
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_48);
return x_52;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; size_t x_57; size_t x_58; 
x_53 = lean_ctor_get(x_46, 1);
lean_inc(x_53);
lean_dec(x_46);
x_54 = lean_ctor_get(x_47, 0);
lean_inc(x_54);
lean_dec(x_47);
x_55 = l_Lean_Level_imax___override(x_54, x_42);
lean_inc(x_1);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_1);
lean_ctor_set(x_56, 1, x_55);
x_57 = 1;
x_58 = lean_usize_add(x_4, x_57);
x_4 = x_58;
x_5 = x_56;
x_10 = x_53;
goto _start;
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_42);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_60 = lean_ctor_get(x_46, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_46, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_62 = x_46;
} else {
 lean_dec_ref(x_46);
 x_62 = lean_box(0);
}
if (lean_is_scalar(x_62)) {
 x_63 = lean_alloc_ctor(1, 2, 0);
} else {
 x_63 = x_62;
}
lean_ctor_set(x_63, 0, x_60);
lean_ctor_set(x_63, 1, x_61);
return x_63;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_42);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_64 = lean_ctor_get(x_43, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_43, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_66 = x_43;
} else {
 lean_dec_ref(x_43);
 x_66 = lean_box(0);
}
if (lean_is_scalar(x_66)) {
 x_67 = lean_alloc_ctor(1, 2, 0);
} else {
 x_67 = x_66;
}
lean_ctor_set(x_67, 0, x_64);
lean_ctor_set(x_67, 1, x_65);
return x_67;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__8(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_4, x_3);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_5);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_array_uget(x_2, x_4);
x_14 = !lean_is_exclusive(x_5);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_5, 1);
x_16 = lean_ctor_get(x_5, 0);
lean_dec(x_16);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_17 = l_Lean_Compiler_LCNF_InferType_inferType(x_13, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_20 = l_Lean_Compiler_LCNF_InferType_getLevel_x3f(x_18, x_6, x_7, x_8, x_9, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_22 = !lean_is_exclusive(x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_20, 0);
lean_dec(x_23);
x_24 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__1___closed__1;
lean_ctor_set(x_5, 0, x_24);
lean_ctor_set(x_20, 0, x_5);
return x_20;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_20, 1);
lean_inc(x_25);
lean_dec(x_20);
x_26 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__1___closed__1;
lean_ctor_set(x_5, 0, x_26);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_5);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; size_t x_31; size_t x_32; 
x_28 = lean_ctor_get(x_20, 1);
lean_inc(x_28);
lean_dec(x_20);
x_29 = lean_ctor_get(x_21, 0);
lean_inc(x_29);
lean_dec(x_21);
x_30 = l_Lean_Level_imax___override(x_29, x_15);
lean_inc(x_1);
lean_ctor_set(x_5, 1, x_30);
lean_ctor_set(x_5, 0, x_1);
x_31 = 1;
x_32 = lean_usize_add(x_4, x_31);
x_4 = x_32;
x_10 = x_28;
goto _start;
}
}
else
{
uint8_t x_34; 
lean_free_object(x_5);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_34 = !lean_is_exclusive(x_20);
if (x_34 == 0)
{
return x_20;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_20, 0);
x_36 = lean_ctor_get(x_20, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_20);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
else
{
uint8_t x_38; 
lean_free_object(x_5);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_17);
if (x_38 == 0)
{
return x_17;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_17, 0);
x_40 = lean_ctor_get(x_17, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_17);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
else
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_5, 1);
lean_inc(x_42);
lean_dec(x_5);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_43 = l_Lean_Compiler_LCNF_InferType_inferType(x_13, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_46 = l_Lean_Compiler_LCNF_InferType_getLevel_x3f(x_44, x_6, x_7, x_8, x_9, x_45);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_49 = x_46;
} else {
 lean_dec_ref(x_46);
 x_49 = lean_box(0);
}
x_50 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__1___closed__1;
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_42);
if (lean_is_scalar(x_49)) {
 x_52 = lean_alloc_ctor(0, 2, 0);
} else {
 x_52 = x_49;
}
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_48);
return x_52;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; size_t x_57; size_t x_58; 
x_53 = lean_ctor_get(x_46, 1);
lean_inc(x_53);
lean_dec(x_46);
x_54 = lean_ctor_get(x_47, 0);
lean_inc(x_54);
lean_dec(x_47);
x_55 = l_Lean_Level_imax___override(x_54, x_42);
lean_inc(x_1);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_1);
lean_ctor_set(x_56, 1, x_55);
x_57 = 1;
x_58 = lean_usize_add(x_4, x_57);
x_4 = x_58;
x_5 = x_56;
x_10 = x_53;
goto _start;
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_42);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_60 = lean_ctor_get(x_46, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_46, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_62 = x_46;
} else {
 lean_dec_ref(x_46);
 x_62 = lean_box(0);
}
if (lean_is_scalar(x_62)) {
 x_63 = lean_alloc_ctor(1, 2, 0);
} else {
 x_63 = x_62;
}
lean_ctor_set(x_63, 0, x_60);
lean_ctor_set(x_63, 1, x_61);
return x_63;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_42);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_64 = lean_ctor_get(x_43, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_43, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_66 = x_43;
} else {
 lean_dec_ref(x_43);
 x_66 = lean_box(0);
}
if (lean_is_scalar(x_66)) {
 x_67 = lean_alloc_ctor(1, 2, 0);
} else {
 x_67 = x_66;
}
lean_ctor_set(x_67, 0, x_64);
lean_ctor_set(x_67, 1, x_65);
return x_67;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__9(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_4, x_3);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_5);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_array_uget(x_2, x_4);
x_14 = !lean_is_exclusive(x_5);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_5, 1);
x_16 = lean_ctor_get(x_5, 0);
lean_dec(x_16);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_17 = l_Lean_Compiler_LCNF_InferType_inferType(x_13, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_20 = l_Lean_Compiler_LCNF_InferType_getLevel_x3f(x_18, x_6, x_7, x_8, x_9, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_22 = !lean_is_exclusive(x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_20, 0);
lean_dec(x_23);
x_24 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__1___closed__1;
lean_ctor_set(x_5, 0, x_24);
lean_ctor_set(x_20, 0, x_5);
return x_20;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_20, 1);
lean_inc(x_25);
lean_dec(x_20);
x_26 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__1___closed__1;
lean_ctor_set(x_5, 0, x_26);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_5);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; size_t x_31; size_t x_32; 
x_28 = lean_ctor_get(x_20, 1);
lean_inc(x_28);
lean_dec(x_20);
x_29 = lean_ctor_get(x_21, 0);
lean_inc(x_29);
lean_dec(x_21);
x_30 = l_Lean_Level_imax___override(x_29, x_15);
lean_inc(x_1);
lean_ctor_set(x_5, 1, x_30);
lean_ctor_set(x_5, 0, x_1);
x_31 = 1;
x_32 = lean_usize_add(x_4, x_31);
x_4 = x_32;
x_10 = x_28;
goto _start;
}
}
else
{
uint8_t x_34; 
lean_free_object(x_5);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_34 = !lean_is_exclusive(x_20);
if (x_34 == 0)
{
return x_20;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_20, 0);
x_36 = lean_ctor_get(x_20, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_20);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
else
{
uint8_t x_38; 
lean_free_object(x_5);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_17);
if (x_38 == 0)
{
return x_17;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_17, 0);
x_40 = lean_ctor_get(x_17, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_17);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
else
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_5, 1);
lean_inc(x_42);
lean_dec(x_5);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_43 = l_Lean_Compiler_LCNF_InferType_inferType(x_13, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_46 = l_Lean_Compiler_LCNF_InferType_getLevel_x3f(x_44, x_6, x_7, x_8, x_9, x_45);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_49 = x_46;
} else {
 lean_dec_ref(x_46);
 x_49 = lean_box(0);
}
x_50 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__1___closed__1;
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_42);
if (lean_is_scalar(x_49)) {
 x_52 = lean_alloc_ctor(0, 2, 0);
} else {
 x_52 = x_49;
}
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_48);
return x_52;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; size_t x_57; size_t x_58; 
x_53 = lean_ctor_get(x_46, 1);
lean_inc(x_53);
lean_dec(x_46);
x_54 = lean_ctor_get(x_47, 0);
lean_inc(x_54);
lean_dec(x_47);
x_55 = l_Lean_Level_imax___override(x_54, x_42);
lean_inc(x_1);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_1);
lean_ctor_set(x_56, 1, x_55);
x_57 = 1;
x_58 = lean_usize_add(x_4, x_57);
x_4 = x_58;
x_5 = x_56;
x_10 = x_53;
goto _start;
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_42);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_60 = lean_ctor_get(x_46, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_46, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_62 = x_46;
} else {
 lean_dec_ref(x_46);
 x_62 = lean_box(0);
}
if (lean_is_scalar(x_62)) {
 x_63 = lean_alloc_ctor(1, 2, 0);
} else {
 x_63 = x_62;
}
lean_ctor_set(x_63, 0, x_60);
lean_ctor_set(x_63, 1, x_61);
return x_63;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_42);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_64 = lean_ctor_get(x_43, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_43, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_66 = x_43;
} else {
 lean_dec_ref(x_43);
 x_66 = lean_box(0);
}
if (lean_is_scalar(x_66)) {
 x_67 = lean_alloc_ctor(1, 2, 0);
} else {
 x_67 = x_66;
}
lean_ctor_set(x_67, 0, x_64);
lean_ctor_set(x_67, 1, x_65);
return x_67;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__10(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_4, x_3);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_5);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_array_uget(x_2, x_4);
x_14 = !lean_is_exclusive(x_5);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_5, 1);
x_16 = lean_ctor_get(x_5, 0);
lean_dec(x_16);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_17 = l_Lean_Compiler_LCNF_InferType_inferType(x_13, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_20 = l_Lean_Compiler_LCNF_InferType_getLevel_x3f(x_18, x_6, x_7, x_8, x_9, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_22 = !lean_is_exclusive(x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_20, 0);
lean_dec(x_23);
x_24 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__1___closed__1;
lean_ctor_set(x_5, 0, x_24);
lean_ctor_set(x_20, 0, x_5);
return x_20;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_20, 1);
lean_inc(x_25);
lean_dec(x_20);
x_26 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__1___closed__1;
lean_ctor_set(x_5, 0, x_26);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_5);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; size_t x_31; size_t x_32; 
x_28 = lean_ctor_get(x_20, 1);
lean_inc(x_28);
lean_dec(x_20);
x_29 = lean_ctor_get(x_21, 0);
lean_inc(x_29);
lean_dec(x_21);
x_30 = l_Lean_Level_imax___override(x_29, x_15);
lean_inc(x_1);
lean_ctor_set(x_5, 1, x_30);
lean_ctor_set(x_5, 0, x_1);
x_31 = 1;
x_32 = lean_usize_add(x_4, x_31);
x_4 = x_32;
x_10 = x_28;
goto _start;
}
}
else
{
uint8_t x_34; 
lean_free_object(x_5);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_34 = !lean_is_exclusive(x_20);
if (x_34 == 0)
{
return x_20;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_20, 0);
x_36 = lean_ctor_get(x_20, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_20);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
else
{
uint8_t x_38; 
lean_free_object(x_5);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_17);
if (x_38 == 0)
{
return x_17;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_17, 0);
x_40 = lean_ctor_get(x_17, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_17);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
else
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_5, 1);
lean_inc(x_42);
lean_dec(x_5);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_43 = l_Lean_Compiler_LCNF_InferType_inferType(x_13, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_46 = l_Lean_Compiler_LCNF_InferType_getLevel_x3f(x_44, x_6, x_7, x_8, x_9, x_45);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_49 = x_46;
} else {
 lean_dec_ref(x_46);
 x_49 = lean_box(0);
}
x_50 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__1___closed__1;
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_42);
if (lean_is_scalar(x_49)) {
 x_52 = lean_alloc_ctor(0, 2, 0);
} else {
 x_52 = x_49;
}
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_48);
return x_52;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; size_t x_57; size_t x_58; 
x_53 = lean_ctor_get(x_46, 1);
lean_inc(x_53);
lean_dec(x_46);
x_54 = lean_ctor_get(x_47, 0);
lean_inc(x_54);
lean_dec(x_47);
x_55 = l_Lean_Level_imax___override(x_54, x_42);
lean_inc(x_1);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_1);
lean_ctor_set(x_56, 1, x_55);
x_57 = 1;
x_58 = lean_usize_add(x_4, x_57);
x_4 = x_58;
x_5 = x_56;
x_10 = x_53;
goto _start;
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_42);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_60 = lean_ctor_get(x_46, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_46, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_62 = x_46;
} else {
 lean_dec_ref(x_46);
 x_62 = lean_box(0);
}
if (lean_is_scalar(x_62)) {
 x_63 = lean_alloc_ctor(1, 2, 0);
} else {
 x_63 = x_62;
}
lean_ctor_set(x_63, 0, x_60);
lean_ctor_set(x_63, 1, x_61);
return x_63;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_42);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_64 = lean_ctor_get(x_43, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_43, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_66 = x_43;
} else {
 lean_dec_ref(x_43);
 x_66 = lean_box(0);
}
if (lean_is_scalar(x_66)) {
 x_67 = lean_alloc_ctor(1, 2, 0);
} else {
 x_67 = x_66;
}
lean_ctor_set(x_67, 0, x_64);
lean_ctor_set(x_67, 1, x_65);
return x_67;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__11(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_4, x_3);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_5);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_array_uget(x_2, x_4);
x_14 = !lean_is_exclusive(x_5);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_5, 1);
x_16 = lean_ctor_get(x_5, 0);
lean_dec(x_16);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_17 = l_Lean_Compiler_LCNF_InferType_inferType(x_13, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_20 = l_Lean_Compiler_LCNF_InferType_getLevel_x3f(x_18, x_6, x_7, x_8, x_9, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_22 = !lean_is_exclusive(x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_20, 0);
lean_dec(x_23);
x_24 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__1___closed__1;
lean_ctor_set(x_5, 0, x_24);
lean_ctor_set(x_20, 0, x_5);
return x_20;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_20, 1);
lean_inc(x_25);
lean_dec(x_20);
x_26 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__1___closed__1;
lean_ctor_set(x_5, 0, x_26);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_5);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; size_t x_31; size_t x_32; 
x_28 = lean_ctor_get(x_20, 1);
lean_inc(x_28);
lean_dec(x_20);
x_29 = lean_ctor_get(x_21, 0);
lean_inc(x_29);
lean_dec(x_21);
x_30 = l_Lean_Level_imax___override(x_29, x_15);
lean_inc(x_1);
lean_ctor_set(x_5, 1, x_30);
lean_ctor_set(x_5, 0, x_1);
x_31 = 1;
x_32 = lean_usize_add(x_4, x_31);
x_4 = x_32;
x_10 = x_28;
goto _start;
}
}
else
{
uint8_t x_34; 
lean_free_object(x_5);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_34 = !lean_is_exclusive(x_20);
if (x_34 == 0)
{
return x_20;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_20, 0);
x_36 = lean_ctor_get(x_20, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_20);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
else
{
uint8_t x_38; 
lean_free_object(x_5);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_17);
if (x_38 == 0)
{
return x_17;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_17, 0);
x_40 = lean_ctor_get(x_17, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_17);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
else
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_5, 1);
lean_inc(x_42);
lean_dec(x_5);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_43 = l_Lean_Compiler_LCNF_InferType_inferType(x_13, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_46 = l_Lean_Compiler_LCNF_InferType_getLevel_x3f(x_44, x_6, x_7, x_8, x_9, x_45);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_49 = x_46;
} else {
 lean_dec_ref(x_46);
 x_49 = lean_box(0);
}
x_50 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__1___closed__1;
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_42);
if (lean_is_scalar(x_49)) {
 x_52 = lean_alloc_ctor(0, 2, 0);
} else {
 x_52 = x_49;
}
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_48);
return x_52;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; size_t x_57; size_t x_58; 
x_53 = lean_ctor_get(x_46, 1);
lean_inc(x_53);
lean_dec(x_46);
x_54 = lean_ctor_get(x_47, 0);
lean_inc(x_54);
lean_dec(x_47);
x_55 = l_Lean_Level_imax___override(x_54, x_42);
lean_inc(x_1);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_1);
lean_ctor_set(x_56, 1, x_55);
x_57 = 1;
x_58 = lean_usize_add(x_4, x_57);
x_4 = x_58;
x_5 = x_56;
x_10 = x_53;
goto _start;
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_42);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_60 = lean_ctor_get(x_46, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_46, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_62 = x_46;
} else {
 lean_dec_ref(x_46);
 x_62 = lean_box(0);
}
if (lean_is_scalar(x_62)) {
 x_63 = lean_alloc_ctor(1, 2, 0);
} else {
 x_63 = x_62;
}
lean_ctor_set(x_63, 0, x_60);
lean_ctor_set(x_63, 1, x_61);
return x_63;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_42);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_64 = lean_ctor_get(x_43, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_43, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_66 = x_43;
} else {
 lean_dec_ref(x_43);
 x_66 = lean_box(0);
}
if (lean_is_scalar(x_66)) {
 x_67 = lean_alloc_ctor(1, 2, 0);
} else {
 x_67 = x_66;
}
lean_ctor_set(x_67, 0, x_64);
lean_ctor_set(x_67, 1, x_65);
return x_67;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_inferForallType_go___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = l_Lean_Level_normalize(x_1);
x_9 = l_Lean_Expr_sort___override(x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_inferForallType_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_expr_instantiate_rev(x_1, x_2);
lean_dec(x_1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_9 = l_Lean_Compiler_LCNF_InferType_getLevel_x3f(x_8, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_9, 0);
lean_dec(x_12);
x_13 = l_Lean_Compiler_LCNF_anyTypeExpr;
lean_ctor_set(x_9, 0, x_13);
return x_9;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
lean_dec(x_9);
x_15 = l_Lean_Compiler_LCNF_anyTypeExpr;
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; size_t x_22; size_t x_23; lean_object* x_24; 
x_17 = lean_ctor_get(x_9, 1);
lean_inc(x_17);
lean_dec(x_9);
x_18 = lean_ctor_get(x_10, 0);
lean_inc(x_18);
lean_dec(x_10);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
x_21 = lean_array_get_size(x_2);
x_22 = lean_usize_of_nat(x_21);
lean_dec(x_21);
x_23 = 0;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_24 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__1(x_19, x_2, x_22, x_23, x_20, x_3, x_4, x_5, x_6, x_17);
lean_dec(x_2);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_dec(x_25);
x_29 = lean_box(0);
x_30 = l_Lean_Compiler_LCNF_InferType_inferForallType_go___lambda__1(x_28, x_29, x_3, x_4, x_5, x_6, x_27);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_30;
}
else
{
uint8_t x_31; 
lean_dec(x_25);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_31 = !lean_is_exclusive(x_24);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_24, 0);
lean_dec(x_32);
x_33 = lean_ctor_get(x_26, 0);
lean_inc(x_33);
lean_dec(x_26);
lean_ctor_set(x_24, 0, x_33);
return x_24;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_24, 1);
lean_inc(x_34);
lean_dec(x_24);
x_35 = lean_ctor_get(x_26, 0);
lean_inc(x_35);
lean_dec(x_26);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
return x_36;
}
}
}
else
{
uint8_t x_37; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_37 = !lean_is_exclusive(x_24);
if (x_37 == 0)
{
return x_24;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_24, 0);
x_39 = lean_ctor_get(x_24, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_24);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
else
{
uint8_t x_41; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_41 = !lean_is_exclusive(x_9);
if (x_41 == 0)
{
return x_9;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_9, 0);
x_43 = lean_ctor_get(x_9, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_9);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
case 1:
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_expr_instantiate_rev(x_1, x_2);
lean_dec(x_1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_46 = l_Lean_Compiler_LCNF_InferType_getLevel_x3f(x_45, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
if (lean_obj_tag(x_47) == 0)
{
uint8_t x_48; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_48 = !lean_is_exclusive(x_46);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_46, 0);
lean_dec(x_49);
x_50 = l_Lean_Compiler_LCNF_anyTypeExpr;
lean_ctor_set(x_46, 0, x_50);
return x_46;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_46, 1);
lean_inc(x_51);
lean_dec(x_46);
x_52 = l_Lean_Compiler_LCNF_anyTypeExpr;
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_51);
return x_53;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; size_t x_59; size_t x_60; lean_object* x_61; 
x_54 = lean_ctor_get(x_46, 1);
lean_inc(x_54);
lean_dec(x_46);
x_55 = lean_ctor_get(x_47, 0);
lean_inc(x_55);
lean_dec(x_47);
x_56 = lean_box(0);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_55);
x_58 = lean_array_get_size(x_2);
x_59 = lean_usize_of_nat(x_58);
lean_dec(x_58);
x_60 = 0;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_61 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__2(x_56, x_2, x_59, x_60, x_57, x_3, x_4, x_5, x_6, x_54);
lean_dec(x_2);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_64 = lean_ctor_get(x_61, 1);
lean_inc(x_64);
lean_dec(x_61);
x_65 = lean_ctor_get(x_62, 1);
lean_inc(x_65);
lean_dec(x_62);
x_66 = lean_box(0);
x_67 = l_Lean_Compiler_LCNF_InferType_inferForallType_go___lambda__1(x_65, x_66, x_3, x_4, x_5, x_6, x_64);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_67;
}
else
{
uint8_t x_68; 
lean_dec(x_62);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_68 = !lean_is_exclusive(x_61);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_61, 0);
lean_dec(x_69);
x_70 = lean_ctor_get(x_63, 0);
lean_inc(x_70);
lean_dec(x_63);
lean_ctor_set(x_61, 0, x_70);
return x_61;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_61, 1);
lean_inc(x_71);
lean_dec(x_61);
x_72 = lean_ctor_get(x_63, 0);
lean_inc(x_72);
lean_dec(x_63);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_71);
return x_73;
}
}
}
else
{
uint8_t x_74; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_74 = !lean_is_exclusive(x_61);
if (x_74 == 0)
{
return x_61;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_61, 0);
x_76 = lean_ctor_get(x_61, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_61);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
}
}
else
{
uint8_t x_78; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_78 = !lean_is_exclusive(x_46);
if (x_78 == 0)
{
return x_46;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_46, 0);
x_80 = lean_ctor_get(x_46, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_46);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
case 2:
{
lean_object* x_82; lean_object* x_83; 
x_82 = lean_expr_instantiate_rev(x_1, x_2);
lean_dec(x_1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_83 = l_Lean_Compiler_LCNF_InferType_getLevel_x3f(x_82, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
if (lean_obj_tag(x_84) == 0)
{
uint8_t x_85; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_85 = !lean_is_exclusive(x_83);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_ctor_get(x_83, 0);
lean_dec(x_86);
x_87 = l_Lean_Compiler_LCNF_anyTypeExpr;
lean_ctor_set(x_83, 0, x_87);
return x_83;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_83, 1);
lean_inc(x_88);
lean_dec(x_83);
x_89 = l_Lean_Compiler_LCNF_anyTypeExpr;
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_88);
return x_90;
}
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; size_t x_96; size_t x_97; lean_object* x_98; 
x_91 = lean_ctor_get(x_83, 1);
lean_inc(x_91);
lean_dec(x_83);
x_92 = lean_ctor_get(x_84, 0);
lean_inc(x_92);
lean_dec(x_84);
x_93 = lean_box(0);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_92);
x_95 = lean_array_get_size(x_2);
x_96 = lean_usize_of_nat(x_95);
lean_dec(x_95);
x_97 = 0;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_98 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__3(x_93, x_2, x_96, x_97, x_94, x_3, x_4, x_5, x_6, x_91);
lean_dec(x_2);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; lean_object* x_100; 
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_101 = lean_ctor_get(x_98, 1);
lean_inc(x_101);
lean_dec(x_98);
x_102 = lean_ctor_get(x_99, 1);
lean_inc(x_102);
lean_dec(x_99);
x_103 = lean_box(0);
x_104 = l_Lean_Compiler_LCNF_InferType_inferForallType_go___lambda__1(x_102, x_103, x_3, x_4, x_5, x_6, x_101);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_104;
}
else
{
uint8_t x_105; 
lean_dec(x_99);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_105 = !lean_is_exclusive(x_98);
if (x_105 == 0)
{
lean_object* x_106; lean_object* x_107; 
x_106 = lean_ctor_get(x_98, 0);
lean_dec(x_106);
x_107 = lean_ctor_get(x_100, 0);
lean_inc(x_107);
lean_dec(x_100);
lean_ctor_set(x_98, 0, x_107);
return x_98;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_108 = lean_ctor_get(x_98, 1);
lean_inc(x_108);
lean_dec(x_98);
x_109 = lean_ctor_get(x_100, 0);
lean_inc(x_109);
lean_dec(x_100);
x_110 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_108);
return x_110;
}
}
}
else
{
uint8_t x_111; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_111 = !lean_is_exclusive(x_98);
if (x_111 == 0)
{
return x_98;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_98, 0);
x_113 = lean_ctor_get(x_98, 1);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_98);
x_114 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set(x_114, 1, x_113);
return x_114;
}
}
}
}
else
{
uint8_t x_115; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_115 = !lean_is_exclusive(x_83);
if (x_115 == 0)
{
return x_83;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_116 = lean_ctor_get(x_83, 0);
x_117 = lean_ctor_get(x_83, 1);
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_83);
x_118 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set(x_118, 1, x_117);
return x_118;
}
}
}
case 3:
{
lean_object* x_119; lean_object* x_120; 
x_119 = lean_expr_instantiate_rev(x_1, x_2);
lean_dec(x_1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_120 = l_Lean_Compiler_LCNF_InferType_getLevel_x3f(x_119, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_121; 
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
if (lean_obj_tag(x_121) == 0)
{
uint8_t x_122; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_122 = !lean_is_exclusive(x_120);
if (x_122 == 0)
{
lean_object* x_123; lean_object* x_124; 
x_123 = lean_ctor_get(x_120, 0);
lean_dec(x_123);
x_124 = l_Lean_Compiler_LCNF_anyTypeExpr;
lean_ctor_set(x_120, 0, x_124);
return x_120;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_ctor_get(x_120, 1);
lean_inc(x_125);
lean_dec(x_120);
x_126 = l_Lean_Compiler_LCNF_anyTypeExpr;
x_127 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_127, 0, x_126);
lean_ctor_set(x_127, 1, x_125);
return x_127;
}
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; size_t x_133; size_t x_134; lean_object* x_135; 
x_128 = lean_ctor_get(x_120, 1);
lean_inc(x_128);
lean_dec(x_120);
x_129 = lean_ctor_get(x_121, 0);
lean_inc(x_129);
lean_dec(x_121);
x_130 = lean_box(0);
x_131 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_129);
x_132 = lean_array_get_size(x_2);
x_133 = lean_usize_of_nat(x_132);
lean_dec(x_132);
x_134 = 0;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_135 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__4(x_130, x_2, x_133, x_134, x_131, x_3, x_4, x_5, x_6, x_128);
lean_dec(x_2);
if (lean_obj_tag(x_135) == 0)
{
lean_object* x_136; lean_object* x_137; 
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
if (lean_obj_tag(x_137) == 0)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_138 = lean_ctor_get(x_135, 1);
lean_inc(x_138);
lean_dec(x_135);
x_139 = lean_ctor_get(x_136, 1);
lean_inc(x_139);
lean_dec(x_136);
x_140 = lean_box(0);
x_141 = l_Lean_Compiler_LCNF_InferType_inferForallType_go___lambda__1(x_139, x_140, x_3, x_4, x_5, x_6, x_138);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_141;
}
else
{
uint8_t x_142; 
lean_dec(x_136);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_142 = !lean_is_exclusive(x_135);
if (x_142 == 0)
{
lean_object* x_143; lean_object* x_144; 
x_143 = lean_ctor_get(x_135, 0);
lean_dec(x_143);
x_144 = lean_ctor_get(x_137, 0);
lean_inc(x_144);
lean_dec(x_137);
lean_ctor_set(x_135, 0, x_144);
return x_135;
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_145 = lean_ctor_get(x_135, 1);
lean_inc(x_145);
lean_dec(x_135);
x_146 = lean_ctor_get(x_137, 0);
lean_inc(x_146);
lean_dec(x_137);
x_147 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_147, 1, x_145);
return x_147;
}
}
}
else
{
uint8_t x_148; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_148 = !lean_is_exclusive(x_135);
if (x_148 == 0)
{
return x_135;
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_149 = lean_ctor_get(x_135, 0);
x_150 = lean_ctor_get(x_135, 1);
lean_inc(x_150);
lean_inc(x_149);
lean_dec(x_135);
x_151 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_151, 0, x_149);
lean_ctor_set(x_151, 1, x_150);
return x_151;
}
}
}
}
else
{
uint8_t x_152; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_152 = !lean_is_exclusive(x_120);
if (x_152 == 0)
{
return x_120;
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_153 = lean_ctor_get(x_120, 0);
x_154 = lean_ctor_get(x_120, 1);
lean_inc(x_154);
lean_inc(x_153);
lean_dec(x_120);
x_155 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_155, 0, x_153);
lean_ctor_set(x_155, 1, x_154);
return x_155;
}
}
}
case 4:
{
lean_object* x_156; lean_object* x_157; 
x_156 = lean_expr_instantiate_rev(x_1, x_2);
lean_dec(x_1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_157 = l_Lean_Compiler_LCNF_InferType_getLevel_x3f(x_156, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_157) == 0)
{
lean_object* x_158; 
x_158 = lean_ctor_get(x_157, 0);
lean_inc(x_158);
if (lean_obj_tag(x_158) == 0)
{
uint8_t x_159; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_159 = !lean_is_exclusive(x_157);
if (x_159 == 0)
{
lean_object* x_160; lean_object* x_161; 
x_160 = lean_ctor_get(x_157, 0);
lean_dec(x_160);
x_161 = l_Lean_Compiler_LCNF_anyTypeExpr;
lean_ctor_set(x_157, 0, x_161);
return x_157;
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_162 = lean_ctor_get(x_157, 1);
lean_inc(x_162);
lean_dec(x_157);
x_163 = l_Lean_Compiler_LCNF_anyTypeExpr;
x_164 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_164, 0, x_163);
lean_ctor_set(x_164, 1, x_162);
return x_164;
}
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; size_t x_170; size_t x_171; lean_object* x_172; 
x_165 = lean_ctor_get(x_157, 1);
lean_inc(x_165);
lean_dec(x_157);
x_166 = lean_ctor_get(x_158, 0);
lean_inc(x_166);
lean_dec(x_158);
x_167 = lean_box(0);
x_168 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_168, 0, x_167);
lean_ctor_set(x_168, 1, x_166);
x_169 = lean_array_get_size(x_2);
x_170 = lean_usize_of_nat(x_169);
lean_dec(x_169);
x_171 = 0;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_172 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__5(x_167, x_2, x_170, x_171, x_168, x_3, x_4, x_5, x_6, x_165);
lean_dec(x_2);
if (lean_obj_tag(x_172) == 0)
{
lean_object* x_173; lean_object* x_174; 
x_173 = lean_ctor_get(x_172, 0);
lean_inc(x_173);
x_174 = lean_ctor_get(x_173, 0);
lean_inc(x_174);
if (lean_obj_tag(x_174) == 0)
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_175 = lean_ctor_get(x_172, 1);
lean_inc(x_175);
lean_dec(x_172);
x_176 = lean_ctor_get(x_173, 1);
lean_inc(x_176);
lean_dec(x_173);
x_177 = lean_box(0);
x_178 = l_Lean_Compiler_LCNF_InferType_inferForallType_go___lambda__1(x_176, x_177, x_3, x_4, x_5, x_6, x_175);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_178;
}
else
{
uint8_t x_179; 
lean_dec(x_173);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_179 = !lean_is_exclusive(x_172);
if (x_179 == 0)
{
lean_object* x_180; lean_object* x_181; 
x_180 = lean_ctor_get(x_172, 0);
lean_dec(x_180);
x_181 = lean_ctor_get(x_174, 0);
lean_inc(x_181);
lean_dec(x_174);
lean_ctor_set(x_172, 0, x_181);
return x_172;
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_182 = lean_ctor_get(x_172, 1);
lean_inc(x_182);
lean_dec(x_172);
x_183 = lean_ctor_get(x_174, 0);
lean_inc(x_183);
lean_dec(x_174);
x_184 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_184, 0, x_183);
lean_ctor_set(x_184, 1, x_182);
return x_184;
}
}
}
else
{
uint8_t x_185; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_185 = !lean_is_exclusive(x_172);
if (x_185 == 0)
{
return x_172;
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_186 = lean_ctor_get(x_172, 0);
x_187 = lean_ctor_get(x_172, 1);
lean_inc(x_187);
lean_inc(x_186);
lean_dec(x_172);
x_188 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_188, 0, x_186);
lean_ctor_set(x_188, 1, x_187);
return x_188;
}
}
}
}
else
{
uint8_t x_189; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_189 = !lean_is_exclusive(x_157);
if (x_189 == 0)
{
return x_157;
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_190 = lean_ctor_get(x_157, 0);
x_191 = lean_ctor_get(x_157, 1);
lean_inc(x_191);
lean_inc(x_190);
lean_dec(x_157);
x_192 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_192, 0, x_190);
lean_ctor_set(x_192, 1, x_191);
return x_192;
}
}
}
case 5:
{
lean_object* x_193; lean_object* x_194; 
x_193 = lean_expr_instantiate_rev(x_1, x_2);
lean_dec(x_1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_194 = l_Lean_Compiler_LCNF_InferType_getLevel_x3f(x_193, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_194) == 0)
{
lean_object* x_195; 
x_195 = lean_ctor_get(x_194, 0);
lean_inc(x_195);
if (lean_obj_tag(x_195) == 0)
{
uint8_t x_196; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_196 = !lean_is_exclusive(x_194);
if (x_196 == 0)
{
lean_object* x_197; lean_object* x_198; 
x_197 = lean_ctor_get(x_194, 0);
lean_dec(x_197);
x_198 = l_Lean_Compiler_LCNF_anyTypeExpr;
lean_ctor_set(x_194, 0, x_198);
return x_194;
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_199 = lean_ctor_get(x_194, 1);
lean_inc(x_199);
lean_dec(x_194);
x_200 = l_Lean_Compiler_LCNF_anyTypeExpr;
x_201 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_201, 0, x_200);
lean_ctor_set(x_201, 1, x_199);
return x_201;
}
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; size_t x_207; size_t x_208; lean_object* x_209; 
x_202 = lean_ctor_get(x_194, 1);
lean_inc(x_202);
lean_dec(x_194);
x_203 = lean_ctor_get(x_195, 0);
lean_inc(x_203);
lean_dec(x_195);
x_204 = lean_box(0);
x_205 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_205, 0, x_204);
lean_ctor_set(x_205, 1, x_203);
x_206 = lean_array_get_size(x_2);
x_207 = lean_usize_of_nat(x_206);
lean_dec(x_206);
x_208 = 0;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_209 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__6(x_204, x_2, x_207, x_208, x_205, x_3, x_4, x_5, x_6, x_202);
lean_dec(x_2);
if (lean_obj_tag(x_209) == 0)
{
lean_object* x_210; lean_object* x_211; 
x_210 = lean_ctor_get(x_209, 0);
lean_inc(x_210);
x_211 = lean_ctor_get(x_210, 0);
lean_inc(x_211);
if (lean_obj_tag(x_211) == 0)
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; 
x_212 = lean_ctor_get(x_209, 1);
lean_inc(x_212);
lean_dec(x_209);
x_213 = lean_ctor_get(x_210, 1);
lean_inc(x_213);
lean_dec(x_210);
x_214 = lean_box(0);
x_215 = l_Lean_Compiler_LCNF_InferType_inferForallType_go___lambda__1(x_213, x_214, x_3, x_4, x_5, x_6, x_212);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_215;
}
else
{
uint8_t x_216; 
lean_dec(x_210);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_216 = !lean_is_exclusive(x_209);
if (x_216 == 0)
{
lean_object* x_217; lean_object* x_218; 
x_217 = lean_ctor_get(x_209, 0);
lean_dec(x_217);
x_218 = lean_ctor_get(x_211, 0);
lean_inc(x_218);
lean_dec(x_211);
lean_ctor_set(x_209, 0, x_218);
return x_209;
}
else
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; 
x_219 = lean_ctor_get(x_209, 1);
lean_inc(x_219);
lean_dec(x_209);
x_220 = lean_ctor_get(x_211, 0);
lean_inc(x_220);
lean_dec(x_211);
x_221 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_221, 0, x_220);
lean_ctor_set(x_221, 1, x_219);
return x_221;
}
}
}
else
{
uint8_t x_222; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_222 = !lean_is_exclusive(x_209);
if (x_222 == 0)
{
return x_209;
}
else
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; 
x_223 = lean_ctor_get(x_209, 0);
x_224 = lean_ctor_get(x_209, 1);
lean_inc(x_224);
lean_inc(x_223);
lean_dec(x_209);
x_225 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_225, 0, x_223);
lean_ctor_set(x_225, 1, x_224);
return x_225;
}
}
}
}
else
{
uint8_t x_226; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_226 = !lean_is_exclusive(x_194);
if (x_226 == 0)
{
return x_194;
}
else
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; 
x_227 = lean_ctor_get(x_194, 0);
x_228 = lean_ctor_get(x_194, 1);
lean_inc(x_228);
lean_inc(x_227);
lean_dec(x_194);
x_229 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_229, 0, x_227);
lean_ctor_set(x_229, 1, x_228);
return x_229;
}
}
}
case 6:
{
lean_object* x_230; lean_object* x_231; 
x_230 = lean_expr_instantiate_rev(x_1, x_2);
lean_dec(x_1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_231 = l_Lean_Compiler_LCNF_InferType_getLevel_x3f(x_230, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_231) == 0)
{
lean_object* x_232; 
x_232 = lean_ctor_get(x_231, 0);
lean_inc(x_232);
if (lean_obj_tag(x_232) == 0)
{
uint8_t x_233; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_233 = !lean_is_exclusive(x_231);
if (x_233 == 0)
{
lean_object* x_234; lean_object* x_235; 
x_234 = lean_ctor_get(x_231, 0);
lean_dec(x_234);
x_235 = l_Lean_Compiler_LCNF_anyTypeExpr;
lean_ctor_set(x_231, 0, x_235);
return x_231;
}
else
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; 
x_236 = lean_ctor_get(x_231, 1);
lean_inc(x_236);
lean_dec(x_231);
x_237 = l_Lean_Compiler_LCNF_anyTypeExpr;
x_238 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_238, 0, x_237);
lean_ctor_set(x_238, 1, x_236);
return x_238;
}
}
else
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; size_t x_244; size_t x_245; lean_object* x_246; 
x_239 = lean_ctor_get(x_231, 1);
lean_inc(x_239);
lean_dec(x_231);
x_240 = lean_ctor_get(x_232, 0);
lean_inc(x_240);
lean_dec(x_232);
x_241 = lean_box(0);
x_242 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_242, 0, x_241);
lean_ctor_set(x_242, 1, x_240);
x_243 = lean_array_get_size(x_2);
x_244 = lean_usize_of_nat(x_243);
lean_dec(x_243);
x_245 = 0;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_246 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__7(x_241, x_2, x_244, x_245, x_242, x_3, x_4, x_5, x_6, x_239);
lean_dec(x_2);
if (lean_obj_tag(x_246) == 0)
{
lean_object* x_247; lean_object* x_248; 
x_247 = lean_ctor_get(x_246, 0);
lean_inc(x_247);
x_248 = lean_ctor_get(x_247, 0);
lean_inc(x_248);
if (lean_obj_tag(x_248) == 0)
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; 
x_249 = lean_ctor_get(x_246, 1);
lean_inc(x_249);
lean_dec(x_246);
x_250 = lean_ctor_get(x_247, 1);
lean_inc(x_250);
lean_dec(x_247);
x_251 = lean_box(0);
x_252 = l_Lean_Compiler_LCNF_InferType_inferForallType_go___lambda__1(x_250, x_251, x_3, x_4, x_5, x_6, x_249);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_252;
}
else
{
uint8_t x_253; 
lean_dec(x_247);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_253 = !lean_is_exclusive(x_246);
if (x_253 == 0)
{
lean_object* x_254; lean_object* x_255; 
x_254 = lean_ctor_get(x_246, 0);
lean_dec(x_254);
x_255 = lean_ctor_get(x_248, 0);
lean_inc(x_255);
lean_dec(x_248);
lean_ctor_set(x_246, 0, x_255);
return x_246;
}
else
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; 
x_256 = lean_ctor_get(x_246, 1);
lean_inc(x_256);
lean_dec(x_246);
x_257 = lean_ctor_get(x_248, 0);
lean_inc(x_257);
lean_dec(x_248);
x_258 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_258, 0, x_257);
lean_ctor_set(x_258, 1, x_256);
return x_258;
}
}
}
else
{
uint8_t x_259; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_259 = !lean_is_exclusive(x_246);
if (x_259 == 0)
{
return x_246;
}
else
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; 
x_260 = lean_ctor_get(x_246, 0);
x_261 = lean_ctor_get(x_246, 1);
lean_inc(x_261);
lean_inc(x_260);
lean_dec(x_246);
x_262 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_262, 0, x_260);
lean_ctor_set(x_262, 1, x_261);
return x_262;
}
}
}
}
else
{
uint8_t x_263; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_263 = !lean_is_exclusive(x_231);
if (x_263 == 0)
{
return x_231;
}
else
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; 
x_264 = lean_ctor_get(x_231, 0);
x_265 = lean_ctor_get(x_231, 1);
lean_inc(x_265);
lean_inc(x_264);
lean_dec(x_231);
x_266 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_266, 0, x_264);
lean_ctor_set(x_266, 1, x_265);
return x_266;
}
}
}
case 7:
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; uint8_t x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; 
x_267 = lean_ctor_get(x_1, 0);
lean_inc(x_267);
x_268 = lean_ctor_get(x_1, 1);
lean_inc(x_268);
x_269 = lean_ctor_get(x_1, 2);
lean_inc(x_269);
x_270 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
lean_dec(x_1);
x_271 = lean_expr_instantiate_rev(x_268, x_2);
lean_dec(x_268);
x_272 = l_Lean_mkFreshFVarId___at_Lean_Compiler_LCNF_InferType_withLocalDecl___spec__1(x_3, x_4, x_5, x_6, x_7);
x_273 = lean_ctor_get(x_272, 0);
lean_inc(x_273);
x_274 = lean_ctor_get(x_272, 1);
lean_inc(x_274);
lean_dec(x_272);
lean_inc(x_273);
x_275 = l_Lean_Expr_fvar___override(x_273);
x_276 = lean_local_ctx_mk_local_decl(x_3, x_273, x_267, x_271, x_270);
x_277 = lean_array_push(x_2, x_275);
x_1 = x_269;
x_2 = x_277;
x_3 = x_276;
x_7 = x_274;
goto _start;
}
case 8:
{
lean_object* x_279; lean_object* x_280; 
x_279 = lean_expr_instantiate_rev(x_1, x_2);
lean_dec(x_1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_280 = l_Lean_Compiler_LCNF_InferType_getLevel_x3f(x_279, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_280) == 0)
{
lean_object* x_281; 
x_281 = lean_ctor_get(x_280, 0);
lean_inc(x_281);
if (lean_obj_tag(x_281) == 0)
{
uint8_t x_282; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_282 = !lean_is_exclusive(x_280);
if (x_282 == 0)
{
lean_object* x_283; lean_object* x_284; 
x_283 = lean_ctor_get(x_280, 0);
lean_dec(x_283);
x_284 = l_Lean_Compiler_LCNF_anyTypeExpr;
lean_ctor_set(x_280, 0, x_284);
return x_280;
}
else
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; 
x_285 = lean_ctor_get(x_280, 1);
lean_inc(x_285);
lean_dec(x_280);
x_286 = l_Lean_Compiler_LCNF_anyTypeExpr;
x_287 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_287, 0, x_286);
lean_ctor_set(x_287, 1, x_285);
return x_287;
}
}
else
{
lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; size_t x_293; size_t x_294; lean_object* x_295; 
x_288 = lean_ctor_get(x_280, 1);
lean_inc(x_288);
lean_dec(x_280);
x_289 = lean_ctor_get(x_281, 0);
lean_inc(x_289);
lean_dec(x_281);
x_290 = lean_box(0);
x_291 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_291, 0, x_290);
lean_ctor_set(x_291, 1, x_289);
x_292 = lean_array_get_size(x_2);
x_293 = lean_usize_of_nat(x_292);
lean_dec(x_292);
x_294 = 0;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_295 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__8(x_290, x_2, x_293, x_294, x_291, x_3, x_4, x_5, x_6, x_288);
lean_dec(x_2);
if (lean_obj_tag(x_295) == 0)
{
lean_object* x_296; lean_object* x_297; 
x_296 = lean_ctor_get(x_295, 0);
lean_inc(x_296);
x_297 = lean_ctor_get(x_296, 0);
lean_inc(x_297);
if (lean_obj_tag(x_297) == 0)
{
lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; 
x_298 = lean_ctor_get(x_295, 1);
lean_inc(x_298);
lean_dec(x_295);
x_299 = lean_ctor_get(x_296, 1);
lean_inc(x_299);
lean_dec(x_296);
x_300 = lean_box(0);
x_301 = l_Lean_Compiler_LCNF_InferType_inferForallType_go___lambda__1(x_299, x_300, x_3, x_4, x_5, x_6, x_298);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_301;
}
else
{
uint8_t x_302; 
lean_dec(x_296);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_302 = !lean_is_exclusive(x_295);
if (x_302 == 0)
{
lean_object* x_303; lean_object* x_304; 
x_303 = lean_ctor_get(x_295, 0);
lean_dec(x_303);
x_304 = lean_ctor_get(x_297, 0);
lean_inc(x_304);
lean_dec(x_297);
lean_ctor_set(x_295, 0, x_304);
return x_295;
}
else
{
lean_object* x_305; lean_object* x_306; lean_object* x_307; 
x_305 = lean_ctor_get(x_295, 1);
lean_inc(x_305);
lean_dec(x_295);
x_306 = lean_ctor_get(x_297, 0);
lean_inc(x_306);
lean_dec(x_297);
x_307 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_307, 0, x_306);
lean_ctor_set(x_307, 1, x_305);
return x_307;
}
}
}
else
{
uint8_t x_308; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_308 = !lean_is_exclusive(x_295);
if (x_308 == 0)
{
return x_295;
}
else
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; 
x_309 = lean_ctor_get(x_295, 0);
x_310 = lean_ctor_get(x_295, 1);
lean_inc(x_310);
lean_inc(x_309);
lean_dec(x_295);
x_311 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_311, 0, x_309);
lean_ctor_set(x_311, 1, x_310);
return x_311;
}
}
}
}
else
{
uint8_t x_312; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_312 = !lean_is_exclusive(x_280);
if (x_312 == 0)
{
return x_280;
}
else
{
lean_object* x_313; lean_object* x_314; lean_object* x_315; 
x_313 = lean_ctor_get(x_280, 0);
x_314 = lean_ctor_get(x_280, 1);
lean_inc(x_314);
lean_inc(x_313);
lean_dec(x_280);
x_315 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_315, 0, x_313);
lean_ctor_set(x_315, 1, x_314);
return x_315;
}
}
}
case 9:
{
lean_object* x_316; lean_object* x_317; 
x_316 = lean_expr_instantiate_rev(x_1, x_2);
lean_dec(x_1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_317 = l_Lean_Compiler_LCNF_InferType_getLevel_x3f(x_316, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_317) == 0)
{
lean_object* x_318; 
x_318 = lean_ctor_get(x_317, 0);
lean_inc(x_318);
if (lean_obj_tag(x_318) == 0)
{
uint8_t x_319; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_319 = !lean_is_exclusive(x_317);
if (x_319 == 0)
{
lean_object* x_320; lean_object* x_321; 
x_320 = lean_ctor_get(x_317, 0);
lean_dec(x_320);
x_321 = l_Lean_Compiler_LCNF_anyTypeExpr;
lean_ctor_set(x_317, 0, x_321);
return x_317;
}
else
{
lean_object* x_322; lean_object* x_323; lean_object* x_324; 
x_322 = lean_ctor_get(x_317, 1);
lean_inc(x_322);
lean_dec(x_317);
x_323 = l_Lean_Compiler_LCNF_anyTypeExpr;
x_324 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_324, 0, x_323);
lean_ctor_set(x_324, 1, x_322);
return x_324;
}
}
else
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; size_t x_330; size_t x_331; lean_object* x_332; 
x_325 = lean_ctor_get(x_317, 1);
lean_inc(x_325);
lean_dec(x_317);
x_326 = lean_ctor_get(x_318, 0);
lean_inc(x_326);
lean_dec(x_318);
x_327 = lean_box(0);
x_328 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_328, 0, x_327);
lean_ctor_set(x_328, 1, x_326);
x_329 = lean_array_get_size(x_2);
x_330 = lean_usize_of_nat(x_329);
lean_dec(x_329);
x_331 = 0;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_332 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__9(x_327, x_2, x_330, x_331, x_328, x_3, x_4, x_5, x_6, x_325);
lean_dec(x_2);
if (lean_obj_tag(x_332) == 0)
{
lean_object* x_333; lean_object* x_334; 
x_333 = lean_ctor_get(x_332, 0);
lean_inc(x_333);
x_334 = lean_ctor_get(x_333, 0);
lean_inc(x_334);
if (lean_obj_tag(x_334) == 0)
{
lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; 
x_335 = lean_ctor_get(x_332, 1);
lean_inc(x_335);
lean_dec(x_332);
x_336 = lean_ctor_get(x_333, 1);
lean_inc(x_336);
lean_dec(x_333);
x_337 = lean_box(0);
x_338 = l_Lean_Compiler_LCNF_InferType_inferForallType_go___lambda__1(x_336, x_337, x_3, x_4, x_5, x_6, x_335);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_338;
}
else
{
uint8_t x_339; 
lean_dec(x_333);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_339 = !lean_is_exclusive(x_332);
if (x_339 == 0)
{
lean_object* x_340; lean_object* x_341; 
x_340 = lean_ctor_get(x_332, 0);
lean_dec(x_340);
x_341 = lean_ctor_get(x_334, 0);
lean_inc(x_341);
lean_dec(x_334);
lean_ctor_set(x_332, 0, x_341);
return x_332;
}
else
{
lean_object* x_342; lean_object* x_343; lean_object* x_344; 
x_342 = lean_ctor_get(x_332, 1);
lean_inc(x_342);
lean_dec(x_332);
x_343 = lean_ctor_get(x_334, 0);
lean_inc(x_343);
lean_dec(x_334);
x_344 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_344, 0, x_343);
lean_ctor_set(x_344, 1, x_342);
return x_344;
}
}
}
else
{
uint8_t x_345; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_345 = !lean_is_exclusive(x_332);
if (x_345 == 0)
{
return x_332;
}
else
{
lean_object* x_346; lean_object* x_347; lean_object* x_348; 
x_346 = lean_ctor_get(x_332, 0);
x_347 = lean_ctor_get(x_332, 1);
lean_inc(x_347);
lean_inc(x_346);
lean_dec(x_332);
x_348 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_348, 0, x_346);
lean_ctor_set(x_348, 1, x_347);
return x_348;
}
}
}
}
else
{
uint8_t x_349; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_349 = !lean_is_exclusive(x_317);
if (x_349 == 0)
{
return x_317;
}
else
{
lean_object* x_350; lean_object* x_351; lean_object* x_352; 
x_350 = lean_ctor_get(x_317, 0);
x_351 = lean_ctor_get(x_317, 1);
lean_inc(x_351);
lean_inc(x_350);
lean_dec(x_317);
x_352 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_352, 0, x_350);
lean_ctor_set(x_352, 1, x_351);
return x_352;
}
}
}
case 10:
{
lean_object* x_353; lean_object* x_354; 
x_353 = lean_expr_instantiate_rev(x_1, x_2);
lean_dec(x_1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_354 = l_Lean_Compiler_LCNF_InferType_getLevel_x3f(x_353, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_354) == 0)
{
lean_object* x_355; 
x_355 = lean_ctor_get(x_354, 0);
lean_inc(x_355);
if (lean_obj_tag(x_355) == 0)
{
uint8_t x_356; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_356 = !lean_is_exclusive(x_354);
if (x_356 == 0)
{
lean_object* x_357; lean_object* x_358; 
x_357 = lean_ctor_get(x_354, 0);
lean_dec(x_357);
x_358 = l_Lean_Compiler_LCNF_anyTypeExpr;
lean_ctor_set(x_354, 0, x_358);
return x_354;
}
else
{
lean_object* x_359; lean_object* x_360; lean_object* x_361; 
x_359 = lean_ctor_get(x_354, 1);
lean_inc(x_359);
lean_dec(x_354);
x_360 = l_Lean_Compiler_LCNF_anyTypeExpr;
x_361 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_361, 0, x_360);
lean_ctor_set(x_361, 1, x_359);
return x_361;
}
}
else
{
lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; size_t x_367; size_t x_368; lean_object* x_369; 
x_362 = lean_ctor_get(x_354, 1);
lean_inc(x_362);
lean_dec(x_354);
x_363 = lean_ctor_get(x_355, 0);
lean_inc(x_363);
lean_dec(x_355);
x_364 = lean_box(0);
x_365 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_365, 0, x_364);
lean_ctor_set(x_365, 1, x_363);
x_366 = lean_array_get_size(x_2);
x_367 = lean_usize_of_nat(x_366);
lean_dec(x_366);
x_368 = 0;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_369 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__10(x_364, x_2, x_367, x_368, x_365, x_3, x_4, x_5, x_6, x_362);
lean_dec(x_2);
if (lean_obj_tag(x_369) == 0)
{
lean_object* x_370; lean_object* x_371; 
x_370 = lean_ctor_get(x_369, 0);
lean_inc(x_370);
x_371 = lean_ctor_get(x_370, 0);
lean_inc(x_371);
if (lean_obj_tag(x_371) == 0)
{
lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; 
x_372 = lean_ctor_get(x_369, 1);
lean_inc(x_372);
lean_dec(x_369);
x_373 = lean_ctor_get(x_370, 1);
lean_inc(x_373);
lean_dec(x_370);
x_374 = lean_box(0);
x_375 = l_Lean_Compiler_LCNF_InferType_inferForallType_go___lambda__1(x_373, x_374, x_3, x_4, x_5, x_6, x_372);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_375;
}
else
{
uint8_t x_376; 
lean_dec(x_370);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_376 = !lean_is_exclusive(x_369);
if (x_376 == 0)
{
lean_object* x_377; lean_object* x_378; 
x_377 = lean_ctor_get(x_369, 0);
lean_dec(x_377);
x_378 = lean_ctor_get(x_371, 0);
lean_inc(x_378);
lean_dec(x_371);
lean_ctor_set(x_369, 0, x_378);
return x_369;
}
else
{
lean_object* x_379; lean_object* x_380; lean_object* x_381; 
x_379 = lean_ctor_get(x_369, 1);
lean_inc(x_379);
lean_dec(x_369);
x_380 = lean_ctor_get(x_371, 0);
lean_inc(x_380);
lean_dec(x_371);
x_381 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_381, 0, x_380);
lean_ctor_set(x_381, 1, x_379);
return x_381;
}
}
}
else
{
uint8_t x_382; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_382 = !lean_is_exclusive(x_369);
if (x_382 == 0)
{
return x_369;
}
else
{
lean_object* x_383; lean_object* x_384; lean_object* x_385; 
x_383 = lean_ctor_get(x_369, 0);
x_384 = lean_ctor_get(x_369, 1);
lean_inc(x_384);
lean_inc(x_383);
lean_dec(x_369);
x_385 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_385, 0, x_383);
lean_ctor_set(x_385, 1, x_384);
return x_385;
}
}
}
}
else
{
uint8_t x_386; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_386 = !lean_is_exclusive(x_354);
if (x_386 == 0)
{
return x_354;
}
else
{
lean_object* x_387; lean_object* x_388; lean_object* x_389; 
x_387 = lean_ctor_get(x_354, 0);
x_388 = lean_ctor_get(x_354, 1);
lean_inc(x_388);
lean_inc(x_387);
lean_dec(x_354);
x_389 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_389, 0, x_387);
lean_ctor_set(x_389, 1, x_388);
return x_389;
}
}
}
default: 
{
lean_object* x_390; lean_object* x_391; 
x_390 = lean_expr_instantiate_rev(x_1, x_2);
lean_dec(x_1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_391 = l_Lean_Compiler_LCNF_InferType_getLevel_x3f(x_390, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_391) == 0)
{
lean_object* x_392; 
x_392 = lean_ctor_get(x_391, 0);
lean_inc(x_392);
if (lean_obj_tag(x_392) == 0)
{
uint8_t x_393; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_393 = !lean_is_exclusive(x_391);
if (x_393 == 0)
{
lean_object* x_394; lean_object* x_395; 
x_394 = lean_ctor_get(x_391, 0);
lean_dec(x_394);
x_395 = l_Lean_Compiler_LCNF_anyTypeExpr;
lean_ctor_set(x_391, 0, x_395);
return x_391;
}
else
{
lean_object* x_396; lean_object* x_397; lean_object* x_398; 
x_396 = lean_ctor_get(x_391, 1);
lean_inc(x_396);
lean_dec(x_391);
x_397 = l_Lean_Compiler_LCNF_anyTypeExpr;
x_398 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_398, 0, x_397);
lean_ctor_set(x_398, 1, x_396);
return x_398;
}
}
else
{
lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; size_t x_404; size_t x_405; lean_object* x_406; 
x_399 = lean_ctor_get(x_391, 1);
lean_inc(x_399);
lean_dec(x_391);
x_400 = lean_ctor_get(x_392, 0);
lean_inc(x_400);
lean_dec(x_392);
x_401 = lean_box(0);
x_402 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_402, 0, x_401);
lean_ctor_set(x_402, 1, x_400);
x_403 = lean_array_get_size(x_2);
x_404 = lean_usize_of_nat(x_403);
lean_dec(x_403);
x_405 = 0;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_406 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__11(x_401, x_2, x_404, x_405, x_402, x_3, x_4, x_5, x_6, x_399);
lean_dec(x_2);
if (lean_obj_tag(x_406) == 0)
{
lean_object* x_407; lean_object* x_408; 
x_407 = lean_ctor_get(x_406, 0);
lean_inc(x_407);
x_408 = lean_ctor_get(x_407, 0);
lean_inc(x_408);
if (lean_obj_tag(x_408) == 0)
{
lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; 
x_409 = lean_ctor_get(x_406, 1);
lean_inc(x_409);
lean_dec(x_406);
x_410 = lean_ctor_get(x_407, 1);
lean_inc(x_410);
lean_dec(x_407);
x_411 = lean_box(0);
x_412 = l_Lean_Compiler_LCNF_InferType_inferForallType_go___lambda__1(x_410, x_411, x_3, x_4, x_5, x_6, x_409);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_412;
}
else
{
uint8_t x_413; 
lean_dec(x_407);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_413 = !lean_is_exclusive(x_406);
if (x_413 == 0)
{
lean_object* x_414; lean_object* x_415; 
x_414 = lean_ctor_get(x_406, 0);
lean_dec(x_414);
x_415 = lean_ctor_get(x_408, 0);
lean_inc(x_415);
lean_dec(x_408);
lean_ctor_set(x_406, 0, x_415);
return x_406;
}
else
{
lean_object* x_416; lean_object* x_417; lean_object* x_418; 
x_416 = lean_ctor_get(x_406, 1);
lean_inc(x_416);
lean_dec(x_406);
x_417 = lean_ctor_get(x_408, 0);
lean_inc(x_417);
lean_dec(x_408);
x_418 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_418, 0, x_417);
lean_ctor_set(x_418, 1, x_416);
return x_418;
}
}
}
else
{
uint8_t x_419; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_419 = !lean_is_exclusive(x_406);
if (x_419 == 0)
{
return x_406;
}
else
{
lean_object* x_420; lean_object* x_421; lean_object* x_422; 
x_420 = lean_ctor_get(x_406, 0);
x_421 = lean_ctor_get(x_406, 1);
lean_inc(x_421);
lean_inc(x_420);
lean_dec(x_406);
x_422 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_422, 0, x_420);
lean_ctor_set(x_422, 1, x_421);
return x_422;
}
}
}
}
else
{
uint8_t x_423; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_423 = !lean_is_exclusive(x_391);
if (x_423 == 0)
{
return x_391;
}
else
{
lean_object* x_424; lean_object* x_425; lean_object* x_426; 
x_424 = lean_ctor_get(x_391, 0);
x_425 = lean_ctor_get(x_391, 1);
lean_inc(x_425);
lean_inc(x_424);
lean_dec(x_391);
x_426 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_426, 0, x_424);
lean_ctor_set(x_426, 1, x_425);
return x_426;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_InferType_getLevel_x3f___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_7 = lean_ctor_get(x_4, 5);
x_8 = lean_st_ref_get(x_5, x_6);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_st_ref_get(x_3, x_10);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
x_16 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_15);
x_17 = lean_ctor_get(x_4, 2);
x_18 = l_Lean_throwError___at_Lean_Compiler_LCNF_InferType_inferType___spec__1___closed__4;
lean_inc(x_17);
x_19 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_19, 0, x_11);
lean_ctor_set(x_19, 1, x_18);
lean_ctor_set(x_19, 2, x_16);
lean_ctor_set(x_19, 3, x_17);
x_20 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_1);
lean_inc(x_7);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_7);
lean_ctor_set(x_21, 1, x_20);
lean_ctor_set_tag(x_12, 1);
lean_ctor_set(x_12, 0, x_21);
return x_12;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_22 = lean_ctor_get(x_12, 0);
x_23 = lean_ctor_get(x_12, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_12);
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_24);
x_26 = lean_ctor_get(x_4, 2);
x_27 = l_Lean_throwError___at_Lean_Compiler_LCNF_InferType_inferType___spec__1___closed__4;
lean_inc(x_26);
x_28 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_28, 0, x_11);
lean_ctor_set(x_28, 1, x_27);
lean_ctor_set(x_28, 2, x_25);
lean_ctor_set(x_28, 3, x_26);
x_29 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_1);
lean_inc(x_7);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_7);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_23);
return x_31;
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_getLevel_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("type expected", 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_getLevel_x3f___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_InferType_getLevel_x3f___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_getLevel_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_7 = l_Lean_Compiler_LCNF_InferType_inferType(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 3)
{
uint8_t x_9; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_7, 0);
lean_dec(x_10);
x_11 = lean_ctor_get(x_8, 0);
lean_inc(x_11);
lean_dec(x_8);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_7, 0, x_12);
return x_7;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_7, 1);
lean_inc(x_13);
lean_dec(x_7);
x_14 = lean_ctor_get(x_8, 0);
lean_inc(x_14);
lean_dec(x_8);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_13);
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_7);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_ctor_get(x_7, 1);
x_19 = lean_ctor_get(x_7, 0);
lean_dec(x_19);
x_20 = l_Lean_Expr_isAnyType(x_8);
lean_dec(x_8);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_free_object(x_7);
x_21 = l_Lean_indentExpr(x_1);
x_22 = l_Lean_Compiler_LCNF_InferType_getLevel_x3f___closed__2;
x_23 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
x_24 = l_Lean_Compiler_LCNF_InferType_inferType___closed__4;
x_25 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Lean_throwError___at_Lean_Compiler_LCNF_InferType_getLevel_x3f___spec__1(x_25, x_2, x_3, x_4, x_5, x_18);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_26;
}
else
{
lean_object* x_27; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_27 = lean_box(0);
lean_ctor_set(x_7, 0, x_27);
return x_7;
}
}
else
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_ctor_get(x_7, 1);
lean_inc(x_28);
lean_dec(x_7);
x_29 = l_Lean_Expr_isAnyType(x_8);
lean_dec(x_8);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_30 = l_Lean_indentExpr(x_1);
x_31 = l_Lean_Compiler_LCNF_InferType_getLevel_x3f___closed__2;
x_32 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
x_33 = l_Lean_Compiler_LCNF_InferType_inferType___closed__4;
x_34 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
x_35 = l_Lean_throwError___at_Lean_Compiler_LCNF_InferType_getLevel_x3f___spec__1(x_34, x_2, x_3, x_4, x_5, x_28);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_36 = lean_box(0);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_28);
return x_37;
}
}
}
}
else
{
uint8_t x_38; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_7);
if (x_38 == 0)
{
return x_7;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_7, 0);
x_40 = lean_ctor_get(x_7, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_7);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_inferAppType___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_levelZero;
x_2 = l_Lean_Expr_sort___override(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_inferAppType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = l_Lean_Expr_getAppFn(x_1);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_8);
x_10 = l_Lean_Compiler_LCNF_InferType_inferAppType___closed__1;
lean_inc(x_9);
x_11 = lean_mk_array(x_9, x_10);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_sub(x_9, x_12);
lean_dec(x_9);
x_14 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_11, x_13);
x_15 = l_Lean_Compiler_LCNF_InferType_inferAppTypeCore(x_7, x_14, x_2, x_3, x_4, x_5, x_6);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_InferType_inferAppTypeCore___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_7 = lean_ctor_get(x_4, 5);
x_8 = lean_st_ref_get(x_5, x_6);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_st_ref_get(x_3, x_10);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
x_16 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_15);
x_17 = lean_ctor_get(x_4, 2);
x_18 = l_Lean_throwError___at_Lean_Compiler_LCNF_InferType_inferType___spec__1___closed__4;
lean_inc(x_17);
x_19 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_19, 0, x_11);
lean_ctor_set(x_19, 1, x_18);
lean_ctor_set(x_19, 2, x_16);
lean_ctor_set(x_19, 3, x_17);
x_20 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_1);
lean_inc(x_7);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_7);
lean_ctor_set(x_21, 1, x_20);
lean_ctor_set_tag(x_12, 1);
lean_ctor_set(x_12, 0, x_21);
return x_12;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_22 = lean_ctor_get(x_12, 0);
x_23 = lean_ctor_get(x_12, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_12);
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_24);
x_26 = lean_ctor_get(x_4, 2);
x_27 = l_Lean_throwError___at_Lean_Compiler_LCNF_InferType_inferType___spec__1___closed__4;
lean_inc(x_26);
x_28 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_28, 0, x_11);
lean_ctor_set(x_28, 1, x_27);
lean_ctor_set(x_28, 2, x_25);
lean_ctor_set(x_28, 3, x_26);
x_29 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_1);
lean_inc(x_7);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_7);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_23);
return x_31;
}
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferAppTypeCore___spec__2___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("function expected", 17);
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferAppTypeCore___spec__2___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferAppTypeCore___spec__2___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferAppTypeCore___spec__2___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" : ", 3);
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferAppTypeCore___spec__2___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferAppTypeCore___spec__2___lambda__1___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferAppTypeCore___spec__2___lambda__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("\nfunction type", 14);
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferAppTypeCore___spec__2___lambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferAppTypeCore___spec__2___lambda__1___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferAppTypeCore___spec__2___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_1);
x_13 = l_Lean_Compiler_LCNF_InferType_inferType(x_1, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_unsigned_to_nat(0u);
x_17 = l_Array_toSubarray___rarg(x_2, x_16, x_3);
x_18 = l_Array_ofSubarray___rarg(x_17);
x_19 = l_Lean_mkAppN(x_1, x_18);
x_20 = l_Lean_indentExpr(x_19);
x_21 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferAppTypeCore___spec__2___lambda__1___closed__2;
x_22 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
x_23 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferAppTypeCore___spec__2___lambda__1___closed__4;
x_24 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_25, 0, x_4);
x_26 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferAppTypeCore___spec__2___lambda__1___closed__6;
x_28 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = l_Lean_indentExpr(x_14);
x_30 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = l_Lean_Compiler_LCNF_InferType_inferType___closed__4;
x_32 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = l_Lean_throwError___at_Lean_Compiler_LCNF_InferType_inferAppTypeCore___spec__1(x_32, x_8, x_9, x_10, x_11, x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
return x_33;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_33, 0);
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_33);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
else
{
uint8_t x_38; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_13);
if (x_38 == 0)
{
return x_13;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_13, 0);
x_40 = lean_ctor_get(x_13, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_13);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferAppTypeCore___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = lean_nat_dec_le(x_6, x_5);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_nat_dec_eq(x_4, x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_sub(x_4, x_17);
lean_dec(x_4);
x_36 = lean_ctor_get(x_8, 1);
lean_inc(x_36);
lean_dec(x_8);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = l_Lean_Expr_headBeta(x_37);
if (lean_obj_tag(x_39) == 7)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_40 = lean_ctor_get(x_39, 2);
lean_inc(x_40);
lean_dec(x_39);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_38);
lean_inc(x_3);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_3);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_42);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_13);
x_19 = x_44;
goto block_35;
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_expr_instantiate_rev_range(x_39, x_38, x_5, x_2);
lean_dec(x_39);
x_46 = l_Lean_Expr_headBeta(x_45);
if (lean_obj_tag(x_46) == 7)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_38);
x_47 = lean_ctor_get(x_46, 2);
lean_inc(x_47);
lean_dec(x_46);
lean_inc(x_5);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_5);
lean_inc(x_3);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_3);
lean_ctor_set(x_49, 1, x_48);
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_49);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_13);
x_19 = x_51;
goto block_35;
}
else
{
uint8_t x_52; 
x_52 = l_Lean_Expr_isAnyType(x_46);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_box(0);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_5);
lean_inc(x_2);
lean_inc(x_1);
x_54 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferAppTypeCore___spec__2___lambda__1(x_1, x_2, x_5, x_46, x_38, x_3, x_53, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_38);
x_19 = x_54;
goto block_35;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_46);
lean_ctor_set(x_55, 1, x_38);
x_56 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__1___closed__1;
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_55);
x_58 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_58, 0, x_57);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_13);
x_19 = x_59;
goto block_35;
}
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
lean_dec(x_9);
lean_dec(x_5);
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
x_29 = lean_nat_add(x_5, x_7);
lean_dec(x_5);
x_4 = x_18;
x_5 = x_29;
x_8 = x_28;
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
lean_dec(x_9);
lean_dec(x_5);
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
lean_object* x_60; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_8);
lean_ctor_set(x_60, 1, x_13);
return x_60;
}
}
else
{
lean_object* x_61; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_8);
lean_ctor_set(x_61, 1, x_13);
return x_61;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_inferAppTypeCore___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_expr_instantiate_rev_range(x_1, x_2, x_3, x_4);
x_12 = l_Lean_Expr_headBeta(x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_inferAppTypeCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_8 = l_Lean_Compiler_LCNF_InferType_inferType(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_array_get_size(x_2);
x_12 = lean_box(0);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_9);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_12);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_unsigned_to_nat(1u);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_11);
lean_inc(x_2);
x_17 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferAppTypeCore___spec__2(x_1, x_2, x_12, x_11, x_13, x_11, x_16, x_15, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
lean_dec(x_18);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_17, 1);
lean_inc(x_21);
lean_dec(x_17);
x_22 = lean_ctor_get(x_19, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_19, 1);
lean_inc(x_23);
lean_dec(x_19);
x_24 = lean_box(0);
x_25 = l_Lean_Compiler_LCNF_InferType_inferAppTypeCore___lambda__1(x_22, x_23, x_11, x_2, x_24, x_3, x_4, x_5, x_6, x_21);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_11);
lean_dec(x_23);
lean_dec(x_22);
return x_25;
}
else
{
uint8_t x_26; 
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_26 = !lean_is_exclusive(x_17);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_17, 0);
lean_dec(x_27);
x_28 = lean_ctor_get(x_20, 0);
lean_inc(x_28);
lean_dec(x_20);
lean_ctor_set(x_17, 0, x_28);
return x_17;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_17, 1);
lean_inc(x_29);
lean_dec(x_17);
x_30 = lean_ctor_get(x_20, 0);
lean_inc(x_30);
lean_dec(x_20);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
}
else
{
uint8_t x_32; 
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_32 = !lean_is_exclusive(x_17);
if (x_32 == 0)
{
return x_17;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_17, 0);
x_34 = lean_ctor_get(x_17, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_17);
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
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_36 = !lean_is_exclusive(x_8);
if (x_36 == 0)
{
return x_8;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_8, 0);
x_38 = lean_ctor_get(x_8, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_8);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_7 = lean_ctor_get(x_4, 5);
x_8 = lean_st_ref_get(x_5, x_6);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_st_ref_get(x_3, x_10);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
x_16 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_15);
x_17 = lean_ctor_get(x_4, 2);
x_18 = l_Lean_throwError___at_Lean_Compiler_LCNF_InferType_inferType___spec__1___closed__4;
lean_inc(x_17);
x_19 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_19, 0, x_11);
lean_ctor_set(x_19, 1, x_18);
lean_ctor_set(x_19, 2, x_16);
lean_ctor_set(x_19, 3, x_17);
x_20 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_1);
lean_inc(x_7);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_7);
lean_ctor_set(x_21, 1, x_20);
lean_ctor_set_tag(x_12, 1);
lean_ctor_set(x_12, 0, x_21);
return x_12;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_22 = lean_ctor_get(x_12, 0);
x_23 = lean_ctor_get(x_12, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_12);
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_24);
x_26 = lean_ctor_get(x_4, 2);
x_27 = l_Lean_throwError___at_Lean_Compiler_LCNF_InferType_inferType___spec__1___closed__4;
lean_inc(x_26);
x_28 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_28, 0, x_11);
lean_ctor_set(x_28, 1, x_27);
lean_ctor_set(x_28, 2, x_25);
lean_ctor_set(x_28, 3, x_26);
x_29 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_1);
lean_inc(x_7);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_7);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_23);
return x_31;
}
}
}
static lean_object* _init_l_Lean_getConstInfo___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("unknown constant '", 18);
return x_1;
}
}
static lean_object* _init_l_Lean_getConstInfo___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_getConstInfo___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_getConstInfo___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("'", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_getConstInfo___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_getConstInfo___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__1___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_1);
x_12 = lean_environment_find(x_11, x_1);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_free_object(x_7);
x_13 = lean_box(0);
x_14 = l_Lean_Expr_const___override(x_1, x_13);
x_15 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = l_Lean_getConstInfo___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__1___closed__2;
x_17 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
x_18 = l_Lean_getConstInfo___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__1___closed__4;
x_19 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Lean_throwError___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__2(x_19, x_2, x_3, x_4, x_5, x_10);
return x_20;
}
else
{
lean_object* x_21; 
lean_dec(x_1);
x_21 = lean_ctor_get(x_12, 0);
lean_inc(x_21);
lean_dec(x_12);
lean_ctor_set(x_7, 0, x_21);
return x_7;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_7, 0);
x_23 = lean_ctor_get(x_7, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_7);
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
lean_dec(x_22);
lean_inc(x_1);
x_25 = lean_environment_find(x_24, x_1);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_26 = lean_box(0);
x_27 = l_Lean_Expr_const___override(x_1, x_26);
x_28 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = l_Lean_getConstInfo___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__1___closed__2;
x_30 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
x_31 = l_Lean_getConstInfo___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__1___closed__4;
x_32 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = l_Lean_throwError___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__2(x_32, x_2, x_3, x_4, x_5, x_23);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_1);
x_34 = lean_ctor_get(x_25, 0);
lean_inc(x_34);
lean_dec(x_25);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_23);
return x_35;
}
}
}
}
static lean_object* _init_l_panic___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__3___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_instInhabitedExpr;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_panic___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_panic___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__3___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_panic___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_panic___at_Lean_Compiler_LCNF_InferType_mkForallFVars___spec__1___closed__1;
x_2 = l_panic___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__3___closed__2;
x_3 = l_instInhabited___rarg(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_panic___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_panic___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__3___closed__3;
x_2 = lean_alloc_closure((void*)(l_instInhabitedReaderT___rarg___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = l_panic___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__3___closed__4;
x_8 = lean_panic_fn(x_7, x_1);
x_9 = lean_apply_5(x_8, x_2, x_3, x_4, x_5, x_6);
return x_9;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__4___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("invalid projection", 18);
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__4___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__4___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__4___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_12 = l_Lean_Expr_proj___override(x_1, x_2, x_3);
x_13 = l_Lean_indentExpr(x_12);
x_14 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__4___lambda__1___closed__2;
x_15 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
x_16 = l_Lean_Compiler_LCNF_InferType_inferType___closed__4;
x_17 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Lean_throwError___at_Lean_Compiler_LCNF_InferType_inferAppTypeCore___spec__1(x_17, x_7, x_8, x_9, x_10, x_11);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
return x_18;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_18);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("assertion violation: ", 21);
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__4___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("!body.hasLooseBVars\n            ", 32);
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__4___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__4___closed__1;
x_2 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__4___closed__2;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__4___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Compiler.LCNF.InferType.inferProjType", 42);
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__4___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Nat_foldRevM_loop___at_Lean_Compiler_LCNF_InferType_mkForallFVars___spec__2___closed__5;
x_2 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__4___closed__4;
x_3 = lean_unsigned_to_nat(100u);
x_4 = lean_unsigned_to_nat(12u);
x_5 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__4___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; 
x_15 = lean_nat_dec_le(x_7, x_6);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_nat_dec_eq(x_5, x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_37; 
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_sub(x_5, x_18);
lean_dec(x_5);
x_37 = lean_ctor_get(x_9, 1);
lean_inc(x_37);
lean_dec(x_9);
if (lean_obj_tag(x_37) == 7)
{
lean_object* x_38; uint8_t x_39; 
x_38 = lean_ctor_get(x_37, 2);
lean_inc(x_38);
lean_dec(x_37);
x_39 = l_Lean_Expr_hasLooseBVars(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_inc(x_4);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_4);
lean_ctor_set(x_40, 1, x_38);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_14);
x_20 = x_42;
goto block_36;
}
else
{
lean_object* x_43; lean_object* x_44; 
lean_dec(x_38);
x_43 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__4___closed__5;
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_44 = l_panic___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__3(x_43, x_10, x_11, x_12, x_13, x_14);
x_20 = x_44;
goto block_36;
}
}
else
{
uint8_t x_45; 
x_45 = l_Lean_Expr_isAnyType(x_37);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_box(0);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_47 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__4___lambda__1(x_1, x_2, x_3, x_4, x_37, x_46, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_37);
x_20 = x_47;
goto block_36;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_48 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__1___closed__1;
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_37);
x_50 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_50, 0, x_49);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_14);
x_20 = x_51;
goto block_36;
}
}
block_36:
{
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
lean_dec(x_19);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_22 = !lean_is_exclusive(x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_20, 0);
lean_dec(x_23);
x_24 = lean_ctor_get(x_21, 0);
lean_inc(x_24);
lean_dec(x_21);
lean_ctor_set(x_20, 0, x_24);
return x_20;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_20, 1);
lean_inc(x_25);
lean_dec(x_20);
x_26 = lean_ctor_get(x_21, 0);
lean_inc(x_26);
lean_dec(x_21);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_20, 1);
lean_inc(x_28);
lean_dec(x_20);
x_29 = lean_ctor_get(x_21, 0);
lean_inc(x_29);
lean_dec(x_21);
x_30 = lean_nat_add(x_6, x_8);
lean_dec(x_6);
x_5 = x_19;
x_6 = x_30;
x_9 = x_29;
x_14 = x_28;
goto _start;
}
}
else
{
uint8_t x_32; 
lean_dec(x_19);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_20);
if (x_32 == 0)
{
return x_20;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_20, 0);
x_34 = lean_ctor_get(x_20, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_20);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
}
else
{
lean_object* x_52; 
lean_dec(x_13);
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
lean_ctor_set(x_52, 1, x_14);
return x_52;
}
}
else
{
lean_object* x_53; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_9);
lean_ctor_set(x_53, 1, x_14);
return x_53;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_inferProjType___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = l_Lean_Expr_proj___override(x_1, x_2, x_3);
x_11 = l_Lean_indentExpr(x_10);
x_12 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__4___lambda__1___closed__2;
x_13 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
x_14 = l_Lean_Compiler_LCNF_InferType_inferType___closed__4;
x_15 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Lean_throwError___at_Lean_Compiler_LCNF_InferType_inferType___spec__1(x_15, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_6);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_inferProjType___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_dec(x_5);
if (lean_obj_tag(x_1) == 7)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
uint8_t x_13; 
x_13 = l_Lean_Expr_isAnyType(x_1);
lean_dec(x_1);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_box(0);
x_15 = l_Lean_Compiler_LCNF_InferType_inferProjType___lambda__1(x_2, x_3, x_4, x_14, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_16 = l_Lean_Compiler_LCNF_anyTypeExpr;
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_10);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_inferProjType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_9 = l_Lean_Compiler_LCNF_InferType_inferType(x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Expr_getAppFn(x_10);
if (lean_obj_tag(x_12) == 4)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_st_ref_get(x_7, x_11);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_environment_find(x_18, x_13);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_14);
lean_dec(x_10);
x_20 = l_Lean_Expr_proj___override(x_1, x_2, x_3);
x_21 = l_Lean_indentExpr(x_20);
x_22 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__4___lambda__1___closed__2;
x_23 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
x_24 = l_Lean_Compiler_LCNF_InferType_inferType___closed__4;
x_25 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Lean_throwError___at_Lean_Compiler_LCNF_InferType_inferType___spec__1(x_25, x_4, x_5, x_6, x_7, x_17);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_26;
}
else
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_19, 0);
lean_inc(x_27);
lean_dec(x_19);
if (lean_obj_tag(x_27) == 5)
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_ctor_get_uint8(x_28, sizeof(void*)*5);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_30 = lean_ctor_get(x_28, 2);
lean_inc(x_30);
x_31 = lean_unsigned_to_nat(0u);
x_32 = lean_nat_dec_eq(x_30, x_31);
lean_dec(x_30);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_28);
lean_dec(x_14);
lean_dec(x_10);
x_33 = l_Lean_Expr_proj___override(x_1, x_2, x_3);
x_34 = l_Lean_indentExpr(x_33);
x_35 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__4___lambda__1___closed__2;
x_36 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
x_37 = l_Lean_Compiler_LCNF_InferType_inferType___closed__4;
x_38 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_39 = l_Lean_throwError___at_Lean_Compiler_LCNF_InferType_inferType___spec__1(x_38, x_4, x_5, x_6, x_7, x_17);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_39;
}
else
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_28, 4);
lean_inc(x_40);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_28);
lean_dec(x_14);
lean_dec(x_10);
x_41 = l_Lean_Expr_proj___override(x_1, x_2, x_3);
x_42 = l_Lean_indentExpr(x_41);
x_43 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__4___lambda__1___closed__2;
x_44 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_42);
x_45 = l_Lean_Compiler_LCNF_InferType_inferType___closed__4;
x_46 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
x_47 = l_Lean_throwError___at_Lean_Compiler_LCNF_InferType_inferType___spec__1(x_46, x_4, x_5, x_6, x_7, x_17);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_47;
}
else
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_40, 1);
lean_inc(x_48);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_40, 0);
lean_inc(x_49);
lean_dec(x_40);
x_50 = l_Lean_getConstInfo___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__1(x_49, x_4, x_5, x_6, x_7, x_17);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
if (lean_obj_tag(x_51) == 6)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = lean_ctor_get(x_51, 0);
lean_inc(x_53);
lean_dec(x_51);
x_54 = lean_ctor_get(x_28, 1);
lean_inc(x_54);
lean_dec(x_28);
x_55 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_10, x_31);
x_56 = l_Lean_Compiler_LCNF_InferType_inferAppType___closed__1;
lean_inc(x_55);
x_57 = lean_mk_array(x_55, x_56);
x_58 = lean_unsigned_to_nat(1u);
x_59 = lean_nat_sub(x_55, x_58);
lean_dec(x_55);
x_60 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_10, x_57, x_59);
x_61 = lean_array_get_size(x_60);
x_62 = lean_nat_dec_eq(x_54, x_61);
lean_dec(x_61);
lean_dec(x_54);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_dec(x_60);
lean_dec(x_53);
lean_dec(x_14);
x_63 = l_Lean_Expr_proj___override(x_1, x_2, x_3);
x_64 = l_Lean_indentExpr(x_63);
x_65 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__4___lambda__1___closed__2;
x_66 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_64);
x_67 = l_Lean_Compiler_LCNF_InferType_inferType___closed__4;
x_68 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
x_69 = l_Lean_throwError___at_Lean_Compiler_LCNF_InferType_inferType___spec__1(x_68, x_4, x_5, x_6, x_7, x_52);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_69;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_70 = lean_ctor_get(x_53, 0);
lean_inc(x_70);
lean_dec(x_53);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
lean_dec(x_70);
x_72 = l_Lean_Expr_const___override(x_71, x_14);
x_73 = l_Lean_mkAppN(x_72, x_60);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_74 = l_Lean_Compiler_LCNF_InferType_inferAppType(x_73, x_4, x_5, x_6, x_7, x_52);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec(x_74);
x_77 = lean_box(0);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_75);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc_n(x_2, 2);
lean_inc(x_1);
x_79 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__4(x_1, x_2, x_3, x_77, x_2, x_31, x_2, x_58, x_78, x_4, x_5, x_6, x_7, x_76);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; 
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_82 = lean_ctor_get(x_79, 1);
lean_inc(x_82);
lean_dec(x_79);
x_83 = lean_ctor_get(x_80, 1);
lean_inc(x_83);
lean_dec(x_80);
x_84 = lean_box(0);
x_85 = l_Lean_Compiler_LCNF_InferType_inferProjType___lambda__2(x_83, x_1, x_2, x_3, x_84, x_4, x_5, x_6, x_7, x_82);
return x_85;
}
else
{
uint8_t x_86; 
lean_dec(x_80);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_86 = !lean_is_exclusive(x_79);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_ctor_get(x_79, 0);
lean_dec(x_87);
x_88 = lean_ctor_get(x_81, 0);
lean_inc(x_88);
lean_dec(x_81);
lean_ctor_set(x_79, 0, x_88);
return x_79;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_79, 1);
lean_inc(x_89);
lean_dec(x_79);
x_90 = lean_ctor_get(x_81, 0);
lean_inc(x_90);
lean_dec(x_81);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_89);
return x_91;
}
}
}
else
{
uint8_t x_92; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_92 = !lean_is_exclusive(x_79);
if (x_92 == 0)
{
return x_79;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_79, 0);
x_94 = lean_ctor_get(x_79, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_79);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
}
else
{
uint8_t x_96; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_96 = !lean_is_exclusive(x_74);
if (x_96 == 0)
{
return x_74;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_74, 0);
x_98 = lean_ctor_get(x_74, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_74);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
return x_99;
}
}
}
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
lean_dec(x_51);
lean_dec(x_28);
lean_dec(x_14);
lean_dec(x_10);
x_100 = lean_ctor_get(x_50, 1);
lean_inc(x_100);
lean_dec(x_50);
x_101 = l_Lean_Expr_proj___override(x_1, x_2, x_3);
x_102 = l_Lean_indentExpr(x_101);
x_103 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__4___lambda__1___closed__2;
x_104 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_102);
x_105 = l_Lean_Compiler_LCNF_InferType_inferType___closed__4;
x_106 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_105);
x_107 = l_Lean_throwError___at_Lean_Compiler_LCNF_InferType_inferType___spec__1(x_106, x_4, x_5, x_6, x_7, x_100);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_107;
}
}
else
{
uint8_t x_108; 
lean_dec(x_28);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_108 = !lean_is_exclusive(x_50);
if (x_108 == 0)
{
return x_50;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_50, 0);
x_110 = lean_ctor_get(x_50, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_50);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
return x_111;
}
}
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
lean_dec(x_48);
lean_dec(x_40);
lean_dec(x_28);
lean_dec(x_14);
lean_dec(x_10);
x_112 = l_Lean_Expr_proj___override(x_1, x_2, x_3);
x_113 = l_Lean_indentExpr(x_112);
x_114 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__4___lambda__1___closed__2;
x_115 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_113);
x_116 = l_Lean_Compiler_LCNF_InferType_inferType___closed__4;
x_117 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
x_118 = l_Lean_throwError___at_Lean_Compiler_LCNF_InferType_inferType___spec__1(x_117, x_4, x_5, x_6, x_7, x_17);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_118;
}
}
}
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
lean_dec(x_28);
lean_dec(x_14);
lean_dec(x_10);
x_119 = l_Lean_Expr_proj___override(x_1, x_2, x_3);
x_120 = l_Lean_indentExpr(x_119);
x_121 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__4___lambda__1___closed__2;
x_122 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_122, 0, x_121);
lean_ctor_set(x_122, 1, x_120);
x_123 = l_Lean_Compiler_LCNF_InferType_inferType___closed__4;
x_124 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_124, 0, x_122);
lean_ctor_set(x_124, 1, x_123);
x_125 = l_Lean_throwError___at_Lean_Compiler_LCNF_InferType_inferType___spec__1(x_124, x_4, x_5, x_6, x_7, x_17);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_125;
}
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
lean_dec(x_27);
lean_dec(x_14);
lean_dec(x_10);
x_126 = l_Lean_Expr_proj___override(x_1, x_2, x_3);
x_127 = l_Lean_indentExpr(x_126);
x_128 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__4___lambda__1___closed__2;
x_129 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_129, 1, x_127);
x_130 = l_Lean_Compiler_LCNF_InferType_inferType___closed__4;
x_131 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_131, 0, x_129);
lean_ctor_set(x_131, 1, x_130);
x_132 = l_Lean_throwError___at_Lean_Compiler_LCNF_InferType_inferType___spec__1(x_131, x_4, x_5, x_6, x_7, x_17);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_132;
}
}
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
lean_dec(x_12);
lean_dec(x_10);
x_133 = l_Lean_Expr_proj___override(x_1, x_2, x_3);
x_134 = l_Lean_indentExpr(x_133);
x_135 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__4___lambda__1___closed__2;
x_136 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_136, 1, x_134);
x_137 = l_Lean_Compiler_LCNF_InferType_inferType___closed__4;
x_138 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_138, 0, x_136);
lean_ctor_set(x_138, 1, x_137);
x_139 = l_Lean_throwError___at_Lean_Compiler_LCNF_InferType_inferType___spec__1(x_138, x_4, x_5, x_6, x_7, x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_139;
}
}
else
{
uint8_t x_140; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_140 = !lean_is_exclusive(x_9);
if (x_140 == 0)
{
return x_9;
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_141 = lean_ctor_get(x_9, 0);
x_142 = lean_ctor_get(x_9, 1);
lean_inc(x_142);
lean_inc(x_141);
lean_dec(x_9);
x_143 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_143, 0, x_141);
lean_ctor_set(x_143, 1, x_142);
return x_143;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_InferType_inferType___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at_Lean_Compiler_LCNF_InferType_inferType___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__1(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__2(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__3(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__4(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__5(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__6(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__7(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__8(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__9(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__10(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__11(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_inferForallType_go___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_InferType_inferForallType_go___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_InferType_getLevel_x3f___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at_Lean_Compiler_LCNF_InferType_getLevel_x3f___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_InferType_inferAppTypeCore___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at_Lean_Compiler_LCNF_InferType_inferAppTypeCore___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferAppTypeCore___spec__2___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferAppTypeCore___spec__2___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferAppTypeCore___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferAppTypeCore___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_7);
lean_dec(x_6);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_inferAppTypeCore___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Compiler_LCNF_InferType_inferAppTypeCore___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_getConstInfo___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__4___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__4___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_8);
lean_dec(x_7);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_inferProjType___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_InferType_inferProjType___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inferType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lean_Compiler_LCNF_InferType_mkForallParams___closed__7;
x_7 = l_Lean_Compiler_LCNF_InferType_inferType(x_1, x_6, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_getLevel___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_6 = lean_ctor_get(x_3, 5);
x_7 = lean_st_ref_get(x_4, x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_st_ref_get(x_2, x_9);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
x_15 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_14);
x_16 = lean_ctor_get(x_3, 2);
x_17 = l_Lean_throwError___at_Lean_Compiler_LCNF_InferType_inferType___spec__1___closed__4;
lean_inc(x_16);
x_18 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_18, 0, x_10);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set(x_18, 2, x_15);
lean_ctor_set(x_18, 3, x_16);
x_19 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_1);
lean_inc(x_6);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_6);
lean_ctor_set(x_20, 1, x_19);
lean_ctor_set_tag(x_11, 1);
lean_ctor_set(x_11, 0, x_20);
return x_11;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_21 = lean_ctor_get(x_11, 0);
x_22 = lean_ctor_get(x_11, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_11);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_23);
x_25 = lean_ctor_get(x_3, 2);
x_26 = l_Lean_throwError___at_Lean_Compiler_LCNF_InferType_inferType___spec__1___closed__4;
lean_inc(x_25);
x_27 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_27, 0, x_10);
lean_ctor_set(x_27, 1, x_26);
lean_ctor_set(x_27, 2, x_24);
lean_ctor_set(x_27, 3, x_25);
x_28 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_1);
lean_inc(x_6);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_6);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_22);
return x_30;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getLevel(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_6 = l_Lean_Compiler_LCNF_inferType(x_1, x_2, x_3, x_4, x_5);
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
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_6, 0);
lean_dec(x_9);
x_10 = lean_ctor_get(x_7, 0);
lean_inc(x_10);
lean_dec(x_7);
lean_ctor_set(x_6, 0, x_10);
return x_6;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_6, 1);
lean_inc(x_11);
lean_dec(x_6);
x_12 = lean_ctor_get(x_7, 0);
lean_inc(x_12);
lean_dec(x_7);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_6);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_6, 1);
x_16 = lean_ctor_get(x_6, 0);
lean_dec(x_16);
x_17 = l_Lean_Expr_isAnyType(x_7);
lean_dec(x_7);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_free_object(x_6);
x_18 = l_Lean_indentExpr(x_1);
x_19 = l_Lean_Compiler_LCNF_InferType_getLevel_x3f___closed__2;
x_20 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
x_21 = l_Lean_Compiler_LCNF_InferType_inferType___closed__4;
x_22 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Lean_throwError___at_Lean_Compiler_LCNF_getLevel___spec__1(x_22, x_2, x_3, x_4, x_15);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_23;
}
else
{
lean_object* x_24; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_24 = l_Lean_levelOne;
lean_ctor_set(x_6, 0, x_24);
return x_6;
}
}
else
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_ctor_get(x_6, 1);
lean_inc(x_25);
lean_dec(x_6);
x_26 = l_Lean_Expr_isAnyType(x_7);
lean_dec(x_7);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_27 = l_Lean_indentExpr(x_1);
x_28 = l_Lean_Compiler_LCNF_InferType_getLevel_x3f___closed__2;
x_29 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
x_30 = l_Lean_Compiler_LCNF_InferType_inferType___closed__4;
x_31 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = l_Lean_throwError___at_Lean_Compiler_LCNF_getLevel___spec__1(x_31, x_2, x_3, x_4, x_25);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_33 = l_Lean_levelOne;
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_25);
return x_34;
}
}
}
}
else
{
uint8_t x_35; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_6);
if (x_35 == 0)
{
return x_6;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_6, 0);
x_37 = lean_ctor_get(x_6, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_6);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_getLevel___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_throwError___at_Lean_Compiler_LCNF_getLevel___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_mkLcCast___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("lcCast", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_mkLcCast___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_mkLcCast___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkLcCast(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_7 = l_Lean_Compiler_LCNF_inferType(x_1, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_8);
x_10 = l_Lean_Compiler_LCNF_getLevel(x_8, x_3, x_4, x_5, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_2);
x_13 = l_Lean_Compiler_LCNF_getLevel(x_2, x_3, x_4, x_5, x_12);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Lean_Compiler_LCNF_mkLcCast___closed__2;
x_20 = l_Lean_Expr_const___override(x_19, x_18);
x_21 = l_Lean_mkApp3(x_20, x_8, x_2, x_1);
lean_ctor_set(x_13, 0, x_21);
return x_13;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_22 = lean_ctor_get(x_13, 0);
x_23 = lean_ctor_get(x_13, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_13);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_11);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_Lean_Compiler_LCNF_mkLcCast___closed__2;
x_28 = l_Lean_Expr_const___override(x_27, x_26);
x_29 = l_Lean_mkApp3(x_28, x_8, x_2, x_1);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_23);
return x_30;
}
}
else
{
uint8_t x_31; 
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_31 = !lean_is_exclusive(x_13);
if (x_31 == 0)
{
return x_13;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_13, 0);
x_33 = lean_ctor_get(x_13, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_13);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
uint8_t x_35; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_10);
if (x_35 == 0)
{
return x_10;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_10, 0);
x_37 = lean_ctor_get(x_10, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_10);
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
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_7);
if (x_39 == 0)
{
return x_7;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_7, 0);
x_41 = lean_ctor_get(x_7, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_7);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_inferType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 3:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
x_8 = l_Lean_Expr_fvar___override(x_6);
x_9 = l_Lean_Compiler_LCNF_InferType_mkForallParams___closed__7;
x_10 = l_Lean_Compiler_LCNF_InferType_inferAppTypeCore(x_8, x_7, x_9, x_2, x_3, x_4, x_5);
return x_10;
}
case 4:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_5);
return x_13;
}
case 5:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
lean_dec(x_1);
x_15 = l_Lean_Compiler_LCNF_getLocalDecl(x_14, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = l_Lean_LocalDecl_type(x_17);
lean_dec(x_17);
lean_ctor_set(x_15, 0, x_18);
return x_15;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_ctor_get(x_15, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_15);
x_21 = l_Lean_LocalDecl_type(x_19);
lean_dec(x_19);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_15);
if (x_23 == 0)
{
return x_15;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_15, 0);
x_25 = lean_ctor_get(x_15, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_15);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
case 6:
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_27 = lean_ctor_get(x_1, 0);
lean_inc(x_27);
lean_dec(x_1);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_5);
return x_28;
}
default: 
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_1, 1);
lean_inc(x_29);
lean_dec(x_1);
x_1 = x_29;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_inferParamType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_7 = l_Lean_Compiler_LCNF_Code_inferType(x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_array_get_size(x_1);
x_11 = lean_usize_of_nat(x_10);
lean_dec(x_10);
x_12 = 0;
x_13 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_InferType_mkForallParams___spec__1(x_11, x_12, x_1);
x_14 = l_Lean_Compiler_LCNF_InferType_mkForallParams___closed__7;
x_15 = l_Lean_Compiler_LCNF_InferType_mkForallFVars(x_13, x_8, x_14, x_3, x_4, x_5, x_9);
lean_dec(x_13);
return x_15;
}
else
{
uint8_t x_16; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_16 = !lean_is_exclusive(x_7);
if (x_16 == 0)
{
return x_7;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_7, 0);
x_18 = lean_ctor_get(x_7, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_7);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_AltCore_inferType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lean_Compiler_LCNF_AltCore_getCode(x_1);
x_7 = l_Lean_Compiler_LCNF_Code_inferType(x_6, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_AltCore_inferType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Compiler_LCNF_AltCore_inferType(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkAuxLetDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = l_Lean_Compiler_LCNF_mkFreshBinderName(x_2, x_3, x_4, x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_10 = l_Lean_Compiler_LCNF_inferType(x_1, x_3, x_4, x_5, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Compiler_LCNF_mkLetDecl(x_8, x_11, x_1, x_3, x_4, x_5, x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_13;
}
else
{
uint8_t x_14; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_14 = !lean_is_exclusive(x_10);
if (x_14 == 0)
{
return x_10;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_10, 0);
x_16 = lean_ctor_get(x_10, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_10);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkForallParams(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_Compiler_LCNF_InferType_mkForallParams___closed__7;
x_8 = l_Lean_Compiler_LCNF_InferType_mkForallParams(x_1, x_2, x_7, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkAuxFunDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_8 = l_Lean_Compiler_LCNF_Code_inferType(x_2, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_11 = l_Lean_Compiler_LCNF_mkForallParams(x_1, x_9, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Compiler_LCNF_mkFreshBinderName(x_3, x_4, x_5, x_6, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_Compiler_LCNF_mkFunDecl(x_15, x_12, x_1, x_2, x_4, x_5, x_6, x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_17;
}
else
{
uint8_t x_18; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_11);
if (x_18 == 0)
{
return x_11;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_11, 0);
x_20 = lean_ctor_get(x_11, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_11);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
else
{
uint8_t x_22; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_22 = !lean_is_exclusive(x_8);
if (x_22 == 0)
{
return x_8;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_8, 0);
x_24 = lean_ctor_get(x_8, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_8);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkAuxJpDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_mkAuxJpDecl_x27___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_y", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_mkAuxJpDecl_x27___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_mkAuxJpDecl_x27___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_mkAuxJpDecl_x27___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkAuxJpDecl_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = l_Lean_Compiler_LCNF_mkAuxJpDecl_x27___closed__2;
x_9 = l_Lean_Compiler_LCNF_mkFreshBinderName(x_8, x_4, x_5, x_6, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_1);
x_12 = l_Lean_Expr_fvar___override(x_1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_13 = l_Lean_Compiler_LCNF_inferType(x_12, x_4, x_5, x_6, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_10);
lean_ctor_set(x_16, 2, x_14);
x_17 = l_Lean_Compiler_LCNF_mkAuxJpDecl_x27___closed__3;
x_18 = lean_array_push(x_17, x_16);
x_19 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_18, x_2, x_3, x_4, x_5, x_6, x_15);
return x_19;
}
else
{
uint8_t x_20; 
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_instantiateForall_go___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_2, 5);
x_6 = l_Lean_addMessageContextPartial___at_Lean_Core_instAddMessageContextCoreM___spec__1(x_1, x_2, x_3, x_4);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_5);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_8);
lean_ctor_set_tag(x_6, 1);
lean_ctor_set(x_6, 0, x_9);
return x_6;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_6, 0);
x_11 = lean_ctor_get(x_6, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_6);
lean_inc(x_5);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_5);
lean_ctor_set(x_12, 1, x_10);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instantiateForall_go___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("invalid instantiateForall, too many parameters", 46);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instantiateForall_go___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_instantiateForall_go___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instantiateForall_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_1);
x_8 = lean_nat_dec_lt(x_3, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_2);
lean_ctor_set(x_9, 1, x_6);
return x_9;
}
else
{
if (lean_obj_tag(x_2) == 7)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_ctor_get(x_2, 2);
lean_inc(x_10);
lean_dec(x_2);
x_11 = lean_array_fget(x_1, x_3);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
x_13 = l_Lean_Expr_fvar___override(x_12);
x_14 = lean_expr_instantiate1(x_10, x_13);
lean_dec(x_13);
lean_dec(x_10);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_3, x_15);
lean_dec(x_3);
x_2 = x_14;
x_3 = x_16;
goto _start;
}
else
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_18 = l_Lean_Compiler_LCNF_instantiateForall_go___closed__2;
x_19 = l_Lean_throwError___at_Lean_Compiler_LCNF_instantiateForall_go___spec__1(x_18, x_4, x_5, x_6);
lean_dec(x_4);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_instantiateForall_go___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_throwError___at_Lean_Compiler_LCNF_instantiateForall_go___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instantiateForall_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_instantiateForall_go(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instantiateForall(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Lean_Compiler_LCNF_instantiateForall_go(x_2, x_1, x_6, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instantiateForall___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Compiler_LCNF_instantiateForall(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_CompilerM(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_Types(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_InferType(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_CompilerM(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Types(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_panic___at_Lean_Compiler_LCNF_InferType_mkForallFVars___spec__1___closed__1 = _init_l_panic___at_Lean_Compiler_LCNF_InferType_mkForallFVars___spec__1___closed__1();
lean_mark_persistent(l_panic___at_Lean_Compiler_LCNF_InferType_mkForallFVars___spec__1___closed__1);
l_panic___at_Lean_Compiler_LCNF_InferType_mkForallFVars___spec__1___closed__2 = _init_l_panic___at_Lean_Compiler_LCNF_InferType_mkForallFVars___spec__1___closed__2();
lean_mark_persistent(l_panic___at_Lean_Compiler_LCNF_InferType_mkForallFVars___spec__1___closed__2);
l_panic___at_Lean_Compiler_LCNF_InferType_mkForallFVars___spec__1___closed__3 = _init_l_panic___at_Lean_Compiler_LCNF_InferType_mkForallFVars___spec__1___closed__3();
lean_mark_persistent(l_panic___at_Lean_Compiler_LCNF_InferType_mkForallFVars___spec__1___closed__3);
l_Nat_foldRevM_loop___at_Lean_Compiler_LCNF_InferType_mkForallFVars___spec__2___closed__1 = _init_l_Nat_foldRevM_loop___at_Lean_Compiler_LCNF_InferType_mkForallFVars___spec__2___closed__1();
lean_mark_persistent(l_Nat_foldRevM_loop___at_Lean_Compiler_LCNF_InferType_mkForallFVars___spec__2___closed__1);
l_Nat_foldRevM_loop___at_Lean_Compiler_LCNF_InferType_mkForallFVars___spec__2___closed__2 = _init_l_Nat_foldRevM_loop___at_Lean_Compiler_LCNF_InferType_mkForallFVars___spec__2___closed__2();
lean_mark_persistent(l_Nat_foldRevM_loop___at_Lean_Compiler_LCNF_InferType_mkForallFVars___spec__2___closed__2);
l_Nat_foldRevM_loop___at_Lean_Compiler_LCNF_InferType_mkForallFVars___spec__2___closed__3 = _init_l_Nat_foldRevM_loop___at_Lean_Compiler_LCNF_InferType_mkForallFVars___spec__2___closed__3();
lean_mark_persistent(l_Nat_foldRevM_loop___at_Lean_Compiler_LCNF_InferType_mkForallFVars___spec__2___closed__3);
l_Nat_foldRevM_loop___at_Lean_Compiler_LCNF_InferType_mkForallFVars___spec__2___closed__4 = _init_l_Nat_foldRevM_loop___at_Lean_Compiler_LCNF_InferType_mkForallFVars___spec__2___closed__4();
lean_mark_persistent(l_Nat_foldRevM_loop___at_Lean_Compiler_LCNF_InferType_mkForallFVars___spec__2___closed__4);
l_Nat_foldRevM_loop___at_Lean_Compiler_LCNF_InferType_mkForallFVars___spec__2___closed__5 = _init_l_Nat_foldRevM_loop___at_Lean_Compiler_LCNF_InferType_mkForallFVars___spec__2___closed__5();
lean_mark_persistent(l_Nat_foldRevM_loop___at_Lean_Compiler_LCNF_InferType_mkForallFVars___spec__2___closed__5);
l_Nat_foldRevM_loop___at_Lean_Compiler_LCNF_InferType_mkForallFVars___spec__2___closed__6 = _init_l_Nat_foldRevM_loop___at_Lean_Compiler_LCNF_InferType_mkForallFVars___spec__2___closed__6();
lean_mark_persistent(l_Nat_foldRevM_loop___at_Lean_Compiler_LCNF_InferType_mkForallFVars___spec__2___closed__6);
l_Nat_foldRevM_loop___at_Lean_Compiler_LCNF_InferType_mkForallFVars___spec__2___closed__7 = _init_l_Nat_foldRevM_loop___at_Lean_Compiler_LCNF_InferType_mkForallFVars___spec__2___closed__7();
lean_mark_persistent(l_Nat_foldRevM_loop___at_Lean_Compiler_LCNF_InferType_mkForallFVars___spec__2___closed__7);
l_Nat_foldRevM_loop___at_Lean_Compiler_LCNF_InferType_mkForallFVars___spec__2___closed__8 = _init_l_Nat_foldRevM_loop___at_Lean_Compiler_LCNF_InferType_mkForallFVars___spec__2___closed__8();
lean_mark_persistent(l_Nat_foldRevM_loop___at_Lean_Compiler_LCNF_InferType_mkForallFVars___spec__2___closed__8);
l_Lean_Compiler_LCNF_InferType_mkForallParams___closed__1 = _init_l_Lean_Compiler_LCNF_InferType_mkForallParams___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_InferType_mkForallParams___closed__1);
l_Lean_Compiler_LCNF_InferType_mkForallParams___closed__2 = _init_l_Lean_Compiler_LCNF_InferType_mkForallParams___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_InferType_mkForallParams___closed__2);
l_Lean_Compiler_LCNF_InferType_mkForallParams___closed__3 = _init_l_Lean_Compiler_LCNF_InferType_mkForallParams___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_InferType_mkForallParams___closed__3);
l_Lean_Compiler_LCNF_InferType_mkForallParams___closed__4 = _init_l_Lean_Compiler_LCNF_InferType_mkForallParams___closed__4();
lean_mark_persistent(l_Lean_Compiler_LCNF_InferType_mkForallParams___closed__4);
l_Lean_Compiler_LCNF_InferType_mkForallParams___closed__5 = _init_l_Lean_Compiler_LCNF_InferType_mkForallParams___closed__5();
lean_mark_persistent(l_Lean_Compiler_LCNF_InferType_mkForallParams___closed__5);
l_Lean_Compiler_LCNF_InferType_mkForallParams___closed__6 = _init_l_Lean_Compiler_LCNF_InferType_mkForallParams___closed__6();
lean_mark_persistent(l_Lean_Compiler_LCNF_InferType_mkForallParams___closed__6);
l_Lean_Compiler_LCNF_InferType_mkForallParams___closed__7 = _init_l_Lean_Compiler_LCNF_InferType_mkForallParams___closed__7();
lean_mark_persistent(l_Lean_Compiler_LCNF_InferType_mkForallParams___closed__7);
l_Lean_Compiler_LCNF_InferType_inferConstType___closed__1 = _init_l_Lean_Compiler_LCNF_InferType_inferConstType___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_InferType_inferConstType___closed__1);
l_Lean_Compiler_LCNF_InferType_inferConstType___closed__2 = _init_l_Lean_Compiler_LCNF_InferType_inferConstType___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_InferType_inferConstType___closed__2);
l_Lean_Compiler_LCNF_InferType_inferConstType___closed__3 = _init_l_Lean_Compiler_LCNF_InferType_inferConstType___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_InferType_inferConstType___closed__3);
l_Lean_Compiler_LCNF_InferType_inferConstType___closed__4 = _init_l_Lean_Compiler_LCNF_InferType_inferConstType___closed__4();
lean_mark_persistent(l_Lean_Compiler_LCNF_InferType_inferConstType___closed__4);
l_Lean_throwError___at_Lean_Compiler_LCNF_InferType_inferType___spec__1___closed__1 = _init_l_Lean_throwError___at_Lean_Compiler_LCNF_InferType_inferType___spec__1___closed__1();
lean_mark_persistent(l_Lean_throwError___at_Lean_Compiler_LCNF_InferType_inferType___spec__1___closed__1);
l_Lean_throwError___at_Lean_Compiler_LCNF_InferType_inferType___spec__1___closed__2 = _init_l_Lean_throwError___at_Lean_Compiler_LCNF_InferType_inferType___spec__1___closed__2();
lean_mark_persistent(l_Lean_throwError___at_Lean_Compiler_LCNF_InferType_inferType___spec__1___closed__2);
l_Lean_throwError___at_Lean_Compiler_LCNF_InferType_inferType___spec__1___closed__3 = _init_l_Lean_throwError___at_Lean_Compiler_LCNF_InferType_inferType___spec__1___closed__3();
lean_mark_persistent(l_Lean_throwError___at_Lean_Compiler_LCNF_InferType_inferType___spec__1___closed__3);
l_Lean_throwError___at_Lean_Compiler_LCNF_InferType_inferType___spec__1___closed__4 = _init_l_Lean_throwError___at_Lean_Compiler_LCNF_InferType_inferType___spec__1___closed__4();
lean_mark_persistent(l_Lean_throwError___at_Lean_Compiler_LCNF_InferType_inferType___spec__1___closed__4);
l_Lean_Compiler_LCNF_InferType_inferType___closed__1 = _init_l_Lean_Compiler_LCNF_InferType_inferType___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_InferType_inferType___closed__1);
l_Lean_Compiler_LCNF_InferType_inferType___closed__2 = _init_l_Lean_Compiler_LCNF_InferType_inferType___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_InferType_inferType___closed__2);
l_Lean_Compiler_LCNF_InferType_inferType___closed__3 = _init_l_Lean_Compiler_LCNF_InferType_inferType___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_InferType_inferType___closed__3);
l_Lean_Compiler_LCNF_InferType_inferType___closed__4 = _init_l_Lean_Compiler_LCNF_InferType_inferType___closed__4();
lean_mark_persistent(l_Lean_Compiler_LCNF_InferType_inferType___closed__4);
l_Lean_Compiler_LCNF_InferType_inferType___closed__5 = _init_l_Lean_Compiler_LCNF_InferType_inferType___closed__5();
lean_mark_persistent(l_Lean_Compiler_LCNF_InferType_inferType___closed__5);
l_Lean_Compiler_LCNF_InferType_inferType___closed__6 = _init_l_Lean_Compiler_LCNF_InferType_inferType___closed__6();
lean_mark_persistent(l_Lean_Compiler_LCNF_InferType_inferType___closed__6);
l_Lean_Compiler_LCNF_InferType_inferLambdaType___closed__1 = _init_l_Lean_Compiler_LCNF_InferType_inferLambdaType___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_InferType_inferLambdaType___closed__1);
l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__1___closed__1 = _init_l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__1___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__1___closed__1);
l_Lean_Compiler_LCNF_InferType_getLevel_x3f___closed__1 = _init_l_Lean_Compiler_LCNF_InferType_getLevel_x3f___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_InferType_getLevel_x3f___closed__1);
l_Lean_Compiler_LCNF_InferType_getLevel_x3f___closed__2 = _init_l_Lean_Compiler_LCNF_InferType_getLevel_x3f___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_InferType_getLevel_x3f___closed__2);
l_Lean_Compiler_LCNF_InferType_inferAppType___closed__1 = _init_l_Lean_Compiler_LCNF_InferType_inferAppType___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_InferType_inferAppType___closed__1);
l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferAppTypeCore___spec__2___lambda__1___closed__1 = _init_l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferAppTypeCore___spec__2___lambda__1___closed__1();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferAppTypeCore___spec__2___lambda__1___closed__1);
l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferAppTypeCore___spec__2___lambda__1___closed__2 = _init_l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferAppTypeCore___spec__2___lambda__1___closed__2();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferAppTypeCore___spec__2___lambda__1___closed__2);
l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferAppTypeCore___spec__2___lambda__1___closed__3 = _init_l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferAppTypeCore___spec__2___lambda__1___closed__3();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferAppTypeCore___spec__2___lambda__1___closed__3);
l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferAppTypeCore___spec__2___lambda__1___closed__4 = _init_l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferAppTypeCore___spec__2___lambda__1___closed__4();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferAppTypeCore___spec__2___lambda__1___closed__4);
l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferAppTypeCore___spec__2___lambda__1___closed__5 = _init_l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferAppTypeCore___spec__2___lambda__1___closed__5();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferAppTypeCore___spec__2___lambda__1___closed__5);
l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferAppTypeCore___spec__2___lambda__1___closed__6 = _init_l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferAppTypeCore___spec__2___lambda__1___closed__6();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferAppTypeCore___spec__2___lambda__1___closed__6);
l_Lean_getConstInfo___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__1___closed__1 = _init_l_Lean_getConstInfo___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__1___closed__1();
lean_mark_persistent(l_Lean_getConstInfo___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__1___closed__1);
l_Lean_getConstInfo___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__1___closed__2 = _init_l_Lean_getConstInfo___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__1___closed__2();
lean_mark_persistent(l_Lean_getConstInfo___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__1___closed__2);
l_Lean_getConstInfo___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__1___closed__3 = _init_l_Lean_getConstInfo___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__1___closed__3();
lean_mark_persistent(l_Lean_getConstInfo___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__1___closed__3);
l_Lean_getConstInfo___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__1___closed__4 = _init_l_Lean_getConstInfo___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__1___closed__4();
lean_mark_persistent(l_Lean_getConstInfo___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__1___closed__4);
l_panic___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__3___closed__1 = _init_l_panic___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__3___closed__1();
lean_mark_persistent(l_panic___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__3___closed__1);
l_panic___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__3___closed__2 = _init_l_panic___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__3___closed__2();
lean_mark_persistent(l_panic___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__3___closed__2);
l_panic___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__3___closed__3 = _init_l_panic___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__3___closed__3();
lean_mark_persistent(l_panic___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__3___closed__3);
l_panic___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__3___closed__4 = _init_l_panic___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__3___closed__4();
lean_mark_persistent(l_panic___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__3___closed__4);
l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__4___lambda__1___closed__1 = _init_l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__4___lambda__1___closed__1();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__4___lambda__1___closed__1);
l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__4___lambda__1___closed__2 = _init_l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__4___lambda__1___closed__2();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__4___lambda__1___closed__2);
l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__4___closed__1 = _init_l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__4___closed__1();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__4___closed__1);
l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__4___closed__2 = _init_l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__4___closed__2();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__4___closed__2);
l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__4___closed__3 = _init_l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__4___closed__3();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__4___closed__3);
l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__4___closed__4 = _init_l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__4___closed__4();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__4___closed__4);
l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__4___closed__5 = _init_l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__4___closed__5();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__4___closed__5);
l_Lean_Compiler_LCNF_mkLcCast___closed__1 = _init_l_Lean_Compiler_LCNF_mkLcCast___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_mkLcCast___closed__1);
l_Lean_Compiler_LCNF_mkLcCast___closed__2 = _init_l_Lean_Compiler_LCNF_mkLcCast___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_mkLcCast___closed__2);
l_Lean_Compiler_LCNF_mkAuxJpDecl_x27___closed__1 = _init_l_Lean_Compiler_LCNF_mkAuxJpDecl_x27___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_mkAuxJpDecl_x27___closed__1);
l_Lean_Compiler_LCNF_mkAuxJpDecl_x27___closed__2 = _init_l_Lean_Compiler_LCNF_mkAuxJpDecl_x27___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_mkAuxJpDecl_x27___closed__2);
l_Lean_Compiler_LCNF_mkAuxJpDecl_x27___closed__3 = _init_l_Lean_Compiler_LCNF_mkAuxJpDecl_x27___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_mkAuxJpDecl_x27___closed__3);
l_Lean_Compiler_LCNF_instantiateForall_go___closed__1 = _init_l_Lean_Compiler_LCNF_instantiateForall_go___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_instantiateForall_go___closed__1);
l_Lean_Compiler_LCNF_instantiateForall_go___closed__2 = _init_l_Lean_Compiler_LCNF_instantiateForall_go___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_instantiateForall_go___closed__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
