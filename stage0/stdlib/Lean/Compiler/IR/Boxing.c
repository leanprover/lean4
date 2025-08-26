// Lean compiler output
// Module: Lean.Compiler.IR.Boxing
// Imports: Lean.Runtime Lean.Compiler.ClosedTermCache Lean.Compiler.ExternAttr Lean.Compiler.IR.Basic Lean.Compiler.IR.CompilerM Lean.Compiler.IR.FreeVars Lean.Compiler.IR.ElimDeadVars Lean.Compiler.IR.ToIRType Lean.Data.AssocList
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
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_visitFnBody___lam__5(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_LocalContext_addParams(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_IR_ExplicitBoxing_mkBoxedVersionAux_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___Lean_IR_ExplicitBoxing_requiresBoxedVersion_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_mkBoxedVersion(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__14____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_castArgsIfNeeded___lam__0(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__8____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_getEnv(lean_object*, lean_object*);
lean_object* l_Lean_IR_Decl_elimDead(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_IR_ExplicitBoxing_visitFnBody_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_requiresBoxedVersion___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_IR_ExplicitBoxing_requiresBoxedVersion___closed__0;
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_withParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Decl_maxIndex(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_getJPParams___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_castArgsIfNeeded___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__27____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_castResultIfNeeded(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ExplicitBoxing_mkBoxedVersionAux___closed__1;
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_visitFnBody___lam__3___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__11____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_getResultType(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_boxArgsIfNeeded___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_unboxResultIfNeeded___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___closed__1;
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_getVarType(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_visitFnBody___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_unboxResultIfNeeded___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__10____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_ExplicitBoxing_M_mkFresh___boxed(lean_object*, lean_object*);
uint8_t l_Lean_IR_CtorInfo_isScalar(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_IR_ExplicitBoxing_visitFnBody_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_withVDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_eqvTypes___boxed(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_withVDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_getVarType___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__22____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_visitFnBody___lam__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_getLocalContext___boxed(lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__4____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_boxArgsIfNeeded___lam__0(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_mkBoxedVersionAux___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_IR_ExplicitBoxing_addBoxedVersions_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lean_IR_ExplicitBoxing_mkCast___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_ExplicitBoxing_M_mkFresh(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_castArgsIfNeeded(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_IR_instInhabitedParam;
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_castArgIfNeeded___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Decl_resultType(lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_find_x3f___at___Lean_IR_ExplicitBoxing_mkCast_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___Lean_IR_ExplicitBoxing_mkBoxedVersionAux_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
static lean_object* l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__1____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_;
static lean_object* l_Lean_IR_ExplicitBoxing_visitVDeclExpr___closed__0;
static lean_object* l_Lean_IR_ExplicitBoxing_addBoxedVersions___closed__0;
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_visitFnBody___lam__4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_LocalContext_getType(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_withJDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Decl_params(lean_object*);
lean_object* l_Array_empty(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_boxArgsIfNeeded(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_visitVDeclExpr___lam__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_closureMaxArgs;
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_mkBoxedVersion___boxed(lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__18____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_;
lean_object* l_Lean_IR_LocalContext_getJPParams(lean_object*, lean_object*);
static lean_object* l_Lean_IR_ExplicitBoxing_mkCast___closed__3;
static lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___Lean_IR_ExplicitBoxing_mkBoxedVersionAux_spec__1___redArg___closed__1;
static lean_object* l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__2____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_visitFnBody___lam__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_ExplicitBoxing_isExpensiveConstantValueBoxing(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___Lean_IR_ExplicitBoxing_mkBoxedVersionAux_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__28____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_;
static lean_object* l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__15____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_;
lean_object* l_Lean_IR_Decl_name(lean_object*);
static lean_object* l_Lean_IR_ExplicitBoxing_getDecl___closed__1;
static lean_object* l_Lean_IR_ExplicitBoxing_mkBoxedName___closed__0;
static lean_object* l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__30____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_;
static lean_object* l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__13____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_explicitBoxing___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__29____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_visitVDeclExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_castResultIfNeeded___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_visitFnBody___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_(lean_object*);
static lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___Lean_IR_ExplicitBoxing_mkBoxedVersionAux_spec__1___redArg___closed__0;
lean_object* l_Lean_IR_findEnvDecl_x27(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_visitFnBody___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_visitFnBody___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__7____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_ExplicitBoxing_isExpensiveConstantValueBoxing___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_visitFnBody___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_mkCast(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_LocalContext_addLocal(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isExtern(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_explicitBoxing___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_mkBoxedName(lean_object*);
uint8_t l_Lean_IR_beqIRType____x40_Lean_Compiler_IR_Basic_840659257____hygCtx___hyg_63_(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_ExplicitBoxing_requiresBoxedVersion(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_castVarIfNeeded(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_isBoxedName___boxed(lean_object*);
static lean_object* l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__3____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_;
lean_object* l_Lean_IR_IRType_boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_visitFnBody(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ExplicitBoxing_mkCast___closed__0;
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_unboxResultIfNeeded(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___Lean_IR_ExplicitBoxing_mkBoxedVersionAux_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_IR_ExplicitBoxing_castArgsIfNeededAux_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__5____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_IR_ExplicitBoxing_run_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_append_index_after(lean_object*, lean_object*);
uint8_t l_Lean_IR_FnBody_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_mkBoxedVersionAux(lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__26____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_ExplicitBoxing_M_mkFresh___redArg(lean_object*);
lean_object* l_Lean_IR_Decl_updateBody_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_explicitBoxing___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ExplicitBoxing_mkCast___closed__4;
static lean_object* l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__6____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_ExplicitBoxing_N_mkFresh(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_IR_ExplicitBoxing_run_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_getJPParams(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__21____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_;
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___Lean_IR_ExplicitBoxing_requiresBoxedVersion_spec__0(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_IR_ExplicitBoxing_addBoxedVersions_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_castArgsIfNeeded___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___Lean_IR_ExplicitBoxing_mkBoxedVersionAux_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_ExplicitBoxing_isBoxedName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_getLocalContext(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_withParams___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_getResultType___boxed(lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__24____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_boxArgsIfNeeded___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_LocalContext_getValue(lean_object*, lean_object*);
static lean_object* l_Lean_IR_ExplicitBoxing_mkCast___closed__2;
static lean_object* l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__19____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_;
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_getEnv___boxed(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_getDecl(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ExplicitBoxing_getDecl___closed__0;
lean_object* l_Lean_IR_Decl_getInfo(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_withParams___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_addBoxedVersions(lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__20____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_withJDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__25____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_castArgIfNeeded(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
static lean_object* l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__12____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_;
static lean_object* l_Lean_IR_ExplicitBoxing_getJPParams___closed__0;
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
static lean_object* l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__17____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_IR_ExplicitBoxing_mkBoxedVersionAux_spec__0(size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_ExplicitBoxing_eqvTypes(lean_object*, lean_object*);
lean_object* l_Lean_IR_LocalContext_addJP(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__23____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_;
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_visitVDeclExpr___lam__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_reshape(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_IR_ExplicitBoxing_castArgsIfNeededAux_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l_Lean_IR_ExplicitBoxing_mkBoxedVersionAux___closed__0;
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_withParams___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_run(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_find_x3f___at___Lean_IR_ExplicitBoxing_mkCast_spec__0(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
static lean_object* l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__16____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l_Lean_IR_explicitBoxing(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_IR_IRType_isScalar(lean_object*);
static lean_object* l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__9____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_visitFnBody___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__0____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_;
static lean_object* _init_l_Lean_IR_ExplicitBoxing_mkBoxedName___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_boxed", 6, 6);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_mkBoxedName(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_IR_ExplicitBoxing_mkBoxedName___closed__0;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_ExplicitBoxing_isBoxedName(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = l_Lean_IR_ExplicitBoxing_mkBoxedName___closed__0;
x_4 = lean_string_dec_eq(x_2, x_3);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_isBoxedName___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_IR_ExplicitBoxing_isBoxedName(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_ExplicitBoxing_N_mkFresh(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_nat_add(x_1, x_2);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___Lean_IR_ExplicitBoxing_requiresBoxedVersion_spec__0(lean_object* x_1, size_t x_2, size_t x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; uint8_t x_14; 
x_5 = lean_array_uget(x_1, x_2);
x_6 = lean_ctor_get_uint8(x_5, sizeof(void*)*2);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec_ref(x_5);
x_8 = 1;
x_14 = l_Lean_IR_IRType_isScalar(x_7);
lean_dec(x_7);
if (x_14 == 0)
{
x_9 = x_6;
goto block_13;
}
else
{
x_9 = x_14;
goto block_13;
}
block_13:
{
if (x_9 == 0)
{
size_t x_10; size_t x_11; 
x_10 = 1;
x_11 = lean_usize_add(x_2, x_10);
x_2 = x_11;
goto _start;
}
else
{
return x_8;
}
}
}
else
{
uint8_t x_15; 
x_15 = 0;
return x_15;
}
}
}
static lean_object* _init_l_Lean_IR_ExplicitBoxing_requiresBoxedVersion___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_closureMaxArgs;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_ExplicitBoxing_requiresBoxedVersion(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; uint8_t x_9; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_3 = l_Lean_IR_Decl_params(x_2);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_array_get_size(x_3);
x_15 = lean_nat_dec_lt(x_13, x_14);
if (x_15 == 0)
{
lean_dec(x_14);
lean_dec_ref(x_1);
x_4 = x_15;
goto block_8;
}
else
{
lean_object* x_16; uint8_t x_17; 
x_16 = l_Lean_IR_Decl_resultType(x_2);
x_17 = l_Lean_IR_IRType_isScalar(x_16);
lean_dec(x_16);
if (x_17 == 0)
{
if (x_15 == 0)
{
lean_dec(x_14);
x_9 = x_17;
goto block_12;
}
else
{
if (x_15 == 0)
{
lean_dec(x_14);
x_9 = x_17;
goto block_12;
}
else
{
size_t x_18; size_t x_19; uint8_t x_20; 
x_18 = 0;
x_19 = lean_usize_of_nat(x_14);
lean_dec(x_14);
x_20 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___Lean_IR_ExplicitBoxing_requiresBoxedVersion_spec__0(x_3, x_18, x_19);
x_9 = x_20;
goto block_12;
}
}
}
else
{
lean_dec(x_14);
x_9 = x_17;
goto block_12;
}
}
block_8:
{
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = l_Lean_IR_ExplicitBoxing_requiresBoxedVersion___closed__0;
x_6 = lean_array_get_size(x_3);
lean_dec_ref(x_3);
x_7 = lean_nat_dec_lt(x_5, x_6);
lean_dec(x_6);
return x_7;
}
else
{
lean_dec_ref(x_3);
return x_4;
}
}
block_12:
{
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = l_Lean_IR_Decl_name(x_2);
x_11 = l_Lean_isExtern(x_1, x_10);
x_4 = x_11;
goto block_8;
}
else
{
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___Lean_IR_ExplicitBoxing_requiresBoxedVersion_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___Lean_IR_ExplicitBoxing_requiresBoxedVersion_spec__0(x_1, x_4, x_5);
lean_dec_ref(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_requiresBoxedVersion___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_IR_ExplicitBoxing_requiresBoxedVersion(x_1, x_2);
lean_dec_ref(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_IR_ExplicitBoxing_mkBoxedVersionAux_spec__0(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_lt(x_2, x_1);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_ExplicitBoxing_N_mkFresh(x_4);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec_ref(x_7);
x_10 = lean_array_uget(x_3, x_2);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; size_t x_18; size_t x_19; lean_object* x_20; 
x_12 = lean_ctor_get(x_10, 1);
x_13 = lean_ctor_get(x_10, 0);
lean_dec(x_13);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_array_uset(x_3, x_2, x_14);
x_16 = 0;
x_17 = l_Lean_IR_IRType_boxed(x_12);
lean_dec(x_12);
lean_ctor_set(x_10, 1, x_17);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set_uint8(x_10, sizeof(void*)*2, x_16);
x_18 = 1;
x_19 = lean_usize_add(x_2, x_18);
x_20 = lean_array_uset(x_15, x_2, x_10);
x_2 = x_19;
x_3 = x_20;
x_4 = x_9;
goto _start;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; size_t x_28; size_t x_29; lean_object* x_30; 
x_22 = lean_ctor_get(x_10, 1);
lean_inc(x_22);
lean_dec(x_10);
x_23 = lean_unsigned_to_nat(0u);
x_24 = lean_array_uset(x_3, x_2, x_23);
x_25 = 0;
x_26 = l_Lean_IR_IRType_boxed(x_22);
lean_dec(x_22);
x_27 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_27, 0, x_8);
lean_ctor_set(x_27, 1, x_26);
lean_ctor_set_uint8(x_27, sizeof(void*)*2, x_25);
x_28 = 1;
x_29 = lean_usize_add(x_2, x_28);
x_30 = lean_array_uset(x_24, x_2, x_27);
x_2 = x_29;
x_3 = x_30;
x_4 = x_9;
goto _start;
}
}
}
}
static lean_object* _init_l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___Lean_IR_ExplicitBoxing_mkBoxedVersionAux_spec__1___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_empty(lean_box(0));
return x_1;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___Lean_IR_ExplicitBoxing_mkBoxedVersionAux_spec__1___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___Lean_IR_ExplicitBoxing_mkBoxedVersionAux_spec__1___redArg___closed__0;
x_2 = lean_box(0);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(9, 4, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___Lean_IR_ExplicitBoxing_mkBoxedVersionAux_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_5, x_8);
if (x_9 == 1)
{
lean_object* x_10; 
lean_dec(x_5);
lean_dec_ref(x_1);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_6);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_6);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_12 = lean_ctor_get(x_6, 0);
x_13 = lean_ctor_get(x_6, 1);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_sub(x_5, x_14);
lean_dec(x_5);
x_16 = lean_nat_sub(x_4, x_15);
x_17 = lean_nat_sub(x_16, x_14);
lean_dec(x_16);
lean_inc_ref(x_1);
x_18 = lean_array_get_borrowed(x_1, x_2, x_17);
x_19 = lean_ctor_get(x_18, 1);
x_20 = lean_array_fget_borrowed(x_3, x_17);
lean_dec(x_17);
x_21 = l_Lean_IR_IRType_isScalar(x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_array_push(x_13, x_23);
lean_ctor_set(x_6, 1, x_24);
x_5 = x_15;
goto _start;
}
else
{
lean_object* x_26; uint8_t x_27; 
lean_free_object(x_6);
x_26 = l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_ExplicitBoxing_N_mkFresh(x_7);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_28 = lean_ctor_get(x_26, 0);
x_29 = lean_ctor_get(x_26, 1);
x_30 = lean_ctor_get(x_20, 0);
lean_inc(x_30);
x_31 = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_32 = l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___Lean_IR_ExplicitBoxing_mkBoxedVersionAux_spec__1___redArg___closed__1;
lean_inc(x_19);
lean_inc(x_28);
x_33 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_33, 0, x_28);
lean_ctor_set(x_33, 1, x_19);
lean_ctor_set(x_33, 2, x_31);
lean_ctor_set(x_33, 3, x_32);
x_34 = lean_array_push(x_12, x_33);
x_35 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_35, 0, x_28);
x_36 = lean_array_push(x_13, x_35);
lean_ctor_set(x_26, 1, x_36);
lean_ctor_set(x_26, 0, x_34);
x_5 = x_15;
x_6 = x_26;
x_7 = x_29;
goto _start;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_38 = lean_ctor_get(x_26, 0);
x_39 = lean_ctor_get(x_26, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_26);
x_40 = lean_ctor_get(x_20, 0);
lean_inc(x_40);
x_41 = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(x_41, 0, x_40);
x_42 = l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___Lean_IR_ExplicitBoxing_mkBoxedVersionAux_spec__1___redArg___closed__1;
lean_inc(x_19);
lean_inc(x_38);
x_43 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_43, 0, x_38);
lean_ctor_set(x_43, 1, x_19);
lean_ctor_set(x_43, 2, x_41);
lean_ctor_set(x_43, 3, x_42);
x_44 = lean_array_push(x_12, x_43);
x_45 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_45, 0, x_38);
x_46 = lean_array_push(x_13, x_45);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_44);
lean_ctor_set(x_47, 1, x_46);
x_5 = x_15;
x_6 = x_47;
x_7 = x_39;
goto _start;
}
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_49 = lean_ctor_get(x_6, 0);
x_50 = lean_ctor_get(x_6, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_6);
x_51 = lean_unsigned_to_nat(1u);
x_52 = lean_nat_sub(x_5, x_51);
lean_dec(x_5);
x_53 = lean_nat_sub(x_4, x_52);
x_54 = lean_nat_sub(x_53, x_51);
lean_dec(x_53);
lean_inc_ref(x_1);
x_55 = lean_array_get_borrowed(x_1, x_2, x_54);
x_56 = lean_ctor_get(x_55, 1);
x_57 = lean_array_fget_borrowed(x_3, x_54);
lean_dec(x_54);
x_58 = l_Lean_IR_IRType_isScalar(x_56);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_59 = lean_ctor_get(x_57, 0);
lean_inc(x_59);
x_60 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_60, 0, x_59);
x_61 = lean_array_push(x_50, x_60);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_49);
lean_ctor_set(x_62, 1, x_61);
x_5 = x_52;
x_6 = x_62;
goto _start;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_64 = l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_ExplicitBoxing_N_mkFresh(x_7);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_67 = x_64;
} else {
 lean_dec_ref(x_64);
 x_67 = lean_box(0);
}
x_68 = lean_ctor_get(x_57, 0);
lean_inc(x_68);
x_69 = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(x_69, 0, x_68);
x_70 = l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___Lean_IR_ExplicitBoxing_mkBoxedVersionAux_spec__1___redArg___closed__1;
lean_inc(x_56);
lean_inc(x_65);
x_71 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_71, 0, x_65);
lean_ctor_set(x_71, 1, x_56);
lean_ctor_set(x_71, 2, x_69);
lean_ctor_set(x_71, 3, x_70);
x_72 = lean_array_push(x_49, x_71);
x_73 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_73, 0, x_65);
x_74 = lean_array_push(x_50, x_73);
if (lean_is_scalar(x_67)) {
 x_75 = lean_alloc_ctor(0, 2, 0);
} else {
 x_75 = x_67;
}
lean_ctor_set(x_75, 0, x_72);
lean_ctor_set(x_75, 1, x_74);
x_5 = x_52;
x_6 = x_75;
x_7 = x_66;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___Lean_IR_ExplicitBoxing_mkBoxedVersionAux_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___Lean_IR_ExplicitBoxing_mkBoxedVersionAux_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_7, x_8);
return x_9;
}
}
static lean_object* _init_l_Lean_IR_ExplicitBoxing_mkBoxedVersionAux___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_ExplicitBoxing_mkBoxedVersionAux___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_ExplicitBoxing_mkBoxedVersionAux___closed__0;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_mkBoxedVersionAux(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; size_t x_4; size_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_3 = l_Lean_IR_Decl_params(x_1);
x_4 = lean_array_size(x_3);
x_5 = 0;
lean_inc_ref(x_3);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_IR_ExplicitBoxing_mkBoxedVersionAux_spec__0(x_4, x_5, x_3, x_2);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec_ref(x_6);
x_9 = l_Lean_IR_instInhabitedParam;
x_10 = lean_array_get_size(x_7);
x_11 = l_Lean_IR_ExplicitBoxing_mkBoxedVersionAux___closed__1;
lean_inc(x_10);
x_12 = l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___Lean_IR_ExplicitBoxing_mkBoxedVersionAux_spec__1___redArg(x_9, x_3, x_7, x_10, x_10, x_11, x_8);
lean_dec(x_10);
lean_dec_ref(x_3);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec_ref(x_12);
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_16 = lean_ctor_get(x_13, 0);
x_17 = l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_ExplicitBoxing_N_mkFresh(x_14);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 lean_ctor_release(x_17, 1);
 x_20 = x_17;
} else {
 lean_dec_ref(x_17);
 x_20 = lean_box(0);
}
x_21 = l_Lean_IR_Decl_resultType(x_1);
x_22 = l_Lean_IR_Decl_name(x_1);
lean_inc(x_22);
lean_ctor_set_tag(x_13, 6);
lean_ctor_set(x_13, 0, x_22);
x_31 = l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___Lean_IR_ExplicitBoxing_mkBoxedVersionAux_spec__1___redArg___closed__1;
lean_inc(x_21);
lean_inc(x_18);
x_32 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_32, 0, x_18);
lean_ctor_set(x_32, 1, x_21);
lean_ctor_set(x_32, 2, x_13);
lean_ctor_set(x_32, 3, x_31);
x_33 = lean_array_push(x_16, x_32);
x_34 = l_Lean_IR_IRType_isScalar(x_21);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_35, 0, x_18);
x_36 = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(x_36, 0, x_35);
x_37 = l_Lean_IR_reshape(x_33, x_36);
x_23 = x_37;
x_24 = x_19;
goto block_30;
}
else
{
lean_object* x_38; uint8_t x_39; 
x_38 = l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_ExplicitBoxing_N_mkFresh(x_19);
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_40 = lean_ctor_get(x_38, 0);
x_41 = lean_ctor_get(x_38, 1);
x_42 = lean_box(8);
lean_inc(x_21);
lean_ctor_set_tag(x_38, 9);
lean_ctor_set(x_38, 1, x_18);
lean_ctor_set(x_38, 0, x_21);
lean_inc(x_40);
x_43 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_43, 0, x_40);
lean_ctor_set(x_43, 1, x_42);
lean_ctor_set(x_43, 2, x_38);
lean_ctor_set(x_43, 3, x_31);
x_44 = lean_array_push(x_33, x_43);
x_45 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_45, 0, x_40);
x_46 = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(x_46, 0, x_45);
x_47 = l_Lean_IR_reshape(x_44, x_46);
x_23 = x_47;
x_24 = x_41;
goto block_30;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_48 = lean_ctor_get(x_38, 0);
x_49 = lean_ctor_get(x_38, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_38);
x_50 = lean_box(8);
lean_inc(x_21);
x_51 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_51, 0, x_21);
lean_ctor_set(x_51, 1, x_18);
lean_inc(x_48);
x_52 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_52, 0, x_48);
lean_ctor_set(x_52, 1, x_50);
lean_ctor_set(x_52, 2, x_51);
lean_ctor_set(x_52, 3, x_31);
x_53 = lean_array_push(x_33, x_52);
x_54 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_54, 0, x_48);
x_55 = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(x_55, 0, x_54);
x_56 = l_Lean_IR_reshape(x_53, x_55);
x_23 = x_56;
x_24 = x_49;
goto block_30;
}
}
block_30:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = l_Lean_IR_ExplicitBoxing_mkBoxedName(x_22);
x_26 = l_Lean_IR_IRType_boxed(x_21);
lean_dec(x_21);
x_27 = l_Lean_IR_Decl_getInfo(x_1);
x_28 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_28, 0, x_25);
lean_ctor_set(x_28, 1, x_7);
lean_ctor_set(x_28, 2, x_26);
lean_ctor_set(x_28, 3, x_23);
lean_ctor_set(x_28, 4, x_27);
if (lean_is_scalar(x_20)) {
 x_29 = lean_alloc_ctor(0, 2, 0);
} else {
 x_29 = x_20;
}
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_24);
return x_29;
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_57 = lean_ctor_get(x_13, 0);
x_58 = lean_ctor_get(x_13, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_13);
x_59 = l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_ExplicitBoxing_N_mkFresh(x_14);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_62 = x_59;
} else {
 lean_dec_ref(x_59);
 x_62 = lean_box(0);
}
x_63 = l_Lean_IR_Decl_resultType(x_1);
x_64 = l_Lean_IR_Decl_name(x_1);
lean_inc(x_64);
x_73 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_73, 0, x_64);
lean_ctor_set(x_73, 1, x_58);
x_74 = l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___Lean_IR_ExplicitBoxing_mkBoxedVersionAux_spec__1___redArg___closed__1;
lean_inc(x_63);
lean_inc(x_60);
x_75 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_75, 0, x_60);
lean_ctor_set(x_75, 1, x_63);
lean_ctor_set(x_75, 2, x_73);
lean_ctor_set(x_75, 3, x_74);
x_76 = lean_array_push(x_57, x_75);
x_77 = l_Lean_IR_IRType_isScalar(x_63);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_78, 0, x_60);
x_79 = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(x_79, 0, x_78);
x_80 = l_Lean_IR_reshape(x_76, x_79);
x_65 = x_80;
x_66 = x_61;
goto block_72;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_81 = l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_ExplicitBoxing_N_mkFresh(x_61);
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_84 = x_81;
} else {
 lean_dec_ref(x_81);
 x_84 = lean_box(0);
}
x_85 = lean_box(8);
lean_inc(x_63);
if (lean_is_scalar(x_84)) {
 x_86 = lean_alloc_ctor(9, 2, 0);
} else {
 x_86 = x_84;
 lean_ctor_set_tag(x_86, 9);
}
lean_ctor_set(x_86, 0, x_63);
lean_ctor_set(x_86, 1, x_60);
lean_inc(x_82);
x_87 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_87, 0, x_82);
lean_ctor_set(x_87, 1, x_85);
lean_ctor_set(x_87, 2, x_86);
lean_ctor_set(x_87, 3, x_74);
x_88 = lean_array_push(x_76, x_87);
x_89 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_89, 0, x_82);
x_90 = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(x_90, 0, x_89);
x_91 = l_Lean_IR_reshape(x_88, x_90);
x_65 = x_91;
x_66 = x_83;
goto block_72;
}
block_72:
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_67 = l_Lean_IR_ExplicitBoxing_mkBoxedName(x_64);
x_68 = l_Lean_IR_IRType_boxed(x_63);
lean_dec(x_63);
x_69 = l_Lean_IR_Decl_getInfo(x_1);
x_70 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_70, 0, x_67);
lean_ctor_set(x_70, 1, x_7);
lean_ctor_set(x_70, 2, x_68);
lean_ctor_set(x_70, 3, x_65);
lean_ctor_set(x_70, 4, x_69);
if (lean_is_scalar(x_62)) {
 x_71 = lean_alloc_ctor(0, 2, 0);
} else {
 x_71 = x_62;
}
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_66);
return x_71;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_IR_ExplicitBoxing_mkBoxedVersionAux_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_IR_ExplicitBoxing_mkBoxedVersionAux_spec__0(x_5, x_6, x_3, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___Lean_IR_ExplicitBoxing_mkBoxedVersionAux_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___Lean_IR_ExplicitBoxing_mkBoxedVersionAux_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___Lean_IR_ExplicitBoxing_mkBoxedVersionAux_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___Lean_IR_ExplicitBoxing_mkBoxedVersionAux_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_mkBoxedVersionAux___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_ExplicitBoxing_mkBoxedVersionAux(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_mkBoxedVersion(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_unsigned_to_nat(1u);
x_3 = l_Lean_IR_ExplicitBoxing_mkBoxedVersionAux(x_1, x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec_ref(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_mkBoxedVersion___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_IR_ExplicitBoxing_mkBoxedVersion(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_IR_ExplicitBoxing_addBoxedVersions_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_3, x_4);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_uget(x_2, x_3);
lean_inc_ref(x_1);
x_13 = l_Lean_IR_ExplicitBoxing_requiresBoxedVersion(x_1, x_12);
if (x_13 == 0)
{
lean_dec_ref(x_12);
x_6 = x_5;
goto block_10;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_Lean_IR_ExplicitBoxing_mkBoxedVersion(x_12);
lean_dec_ref(x_12);
x_15 = lean_array_push(x_5, x_14);
x_6 = x_15;
goto block_10;
}
}
else
{
lean_dec_ref(x_1);
return x_5;
}
block_10:
{
size_t x_7; size_t x_8; 
x_7 = 1;
x_8 = lean_usize_add(x_3, x_7);
x_3 = x_8;
x_5 = x_6;
goto _start;
}
}
}
static lean_object* _init_l_Lean_IR_ExplicitBoxing_addBoxedVersions___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_addBoxedVersions(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Lean_IR_ExplicitBoxing_addBoxedVersions___closed__0;
x_5 = lean_array_get_size(x_2);
x_6 = lean_nat_dec_lt(x_3, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_5);
lean_dec_ref(x_1);
x_7 = l_Array_append___redArg(x_2, x_4);
return x_7;
}
else
{
uint8_t x_8; 
x_8 = lean_nat_dec_le(x_5, x_5);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_5);
lean_dec_ref(x_1);
x_9 = l_Array_append___redArg(x_2, x_4);
return x_9;
}
else
{
size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; 
x_10 = 0;
x_11 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_12 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_IR_ExplicitBoxing_addBoxedVersions_spec__0(x_1, x_2, x_10, x_11, x_4);
x_13 = l_Array_append___redArg(x_2, x_12);
lean_dec_ref(x_12);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_IR_ExplicitBoxing_addBoxedVersions_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_IR_ExplicitBoxing_addBoxedVersions_spec__0(x_1, x_2, x_6, x_7, x_5);
lean_dec_ref(x_2);
return x_8;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_ExplicitBoxing_eqvTypes(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_7; uint8_t x_9; uint8_t x_10; 
x_9 = l_Lean_IR_IRType_isScalar(x_1);
x_10 = l_Lean_IR_IRType_isScalar(x_2);
if (x_9 == 0)
{
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = 1;
x_3 = x_11;
goto block_6;
}
else
{
x_7 = x_9;
goto block_8;
}
}
else
{
x_7 = x_10;
goto block_8;
}
block_6:
{
uint8_t x_4; 
x_4 = l_Lean_IR_IRType_isScalar(x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
uint8_t x_5; 
x_5 = l_Lean_IR_beqIRType____x40_Lean_Compiler_IR_Basic_840659257____hygCtx___hyg_63_(x_1, x_2);
return x_5;
}
}
block_8:
{
if (x_7 == 0)
{
return x_7;
}
else
{
x_3 = x_7;
goto block_6;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_eqvTypes___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_ExplicitBoxing_M_mkFresh___redArg(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_add(x_3, x_4);
lean_ctor_set(x_1, 0, x_5);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_1);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
x_9 = lean_ctor_get(x_1, 2);
x_10 = lean_ctor_get(x_1, 3);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_1);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_7, x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_8);
lean_ctor_set(x_13, 2, x_9);
lean_ctor_set(x_13, 3, x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_ExplicitBoxing_M_mkFresh(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_ExplicitBoxing_M_mkFresh___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_ExplicitBoxing_M_mkFresh___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_ExplicitBoxing_M_mkFresh(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_getEnv(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 4);
lean_inc_ref(x_3);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_getEnv___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_ExplicitBoxing_getEnv(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_getLocalContext(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_getLocalContext___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_ExplicitBoxing_getLocalContext(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_getResultType(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 2);
lean_inc(x_3);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_getResultType___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_ExplicitBoxing_getResultType(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_getVarType(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_IR_ExplicitBoxing_getLocalContext(x_2, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = l_Lean_IR_LocalContext_getType(x_6, x_1);
lean_dec(x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
x_8 = lean_box(8);
lean_ctor_set(x_4, 0, x_8);
return x_4;
}
else
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec_ref(x_7);
lean_ctor_set(x_4, 0, x_9);
return x_4;
}
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_4, 0);
x_11 = lean_ctor_get(x_4, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_4);
x_12 = l_Lean_IR_LocalContext_getType(x_10, x_1);
lean_dec(x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_box(8);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_11);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_15);
lean_dec_ref(x_12);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_11);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_getVarType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_ExplicitBoxing_getVarType(x_1, x_2, x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_IR_ExplicitBoxing_getJPParams___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_getJPParams(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_IR_ExplicitBoxing_getLocalContext(x_2, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = l_Lean_IR_LocalContext_getJPParams(x_6, x_1);
lean_dec(x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
x_8 = l_Lean_IR_ExplicitBoxing_getJPParams___closed__0;
lean_ctor_set(x_4, 0, x_8);
return x_4;
}
else
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec_ref(x_7);
lean_ctor_set(x_4, 0, x_9);
return x_4;
}
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_4, 0);
x_11 = lean_ctor_get(x_4, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_4);
x_12 = l_Lean_IR_LocalContext_getJPParams(x_10, x_1);
lean_dec(x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = l_Lean_IR_ExplicitBoxing_getJPParams___closed__0;
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_11);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_15);
lean_dec_ref(x_12);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_11);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_getJPParams___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_ExplicitBoxing_getJPParams(x_1, x_2, x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_IR_ExplicitBoxing_getDecl___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_empty(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ExplicitBoxing_getDecl___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = l_Lean_IR_ExplicitBoxing_getDecl___closed__0;
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_getDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 3);
lean_inc_ref(x_4);
x_5 = lean_ctor_get(x_2, 4);
lean_inc_ref(x_5);
lean_dec_ref(x_2);
x_6 = l_Lean_IR_findEnvDecl_x27(x_5, x_1, x_4);
lean_dec_ref(x_4);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_IR_ExplicitBoxing_getDecl___closed__1;
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_3);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
lean_dec_ref(x_6);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_3);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_withParams___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_3, 1);
x_7 = l_Lean_IR_LocalContext_addParams(x_6, x_1);
lean_ctor_set(x_3, 1, x_7);
x_8 = lean_apply_2(x_2, x_3, x_4);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_9 = lean_ctor_get(x_3, 0);
x_10 = lean_ctor_get(x_3, 1);
x_11 = lean_ctor_get(x_3, 2);
x_12 = lean_ctor_get(x_3, 3);
x_13 = lean_ctor_get(x_3, 4);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_3);
x_14 = l_Lean_IR_LocalContext_addParams(x_10, x_1);
x_15 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_15, 0, x_9);
lean_ctor_set(x_15, 1, x_14);
lean_ctor_set(x_15, 2, x_11);
lean_ctor_set(x_15, 3, x_12);
lean_ctor_set(x_15, 4, x_13);
x_16 = lean_apply_2(x_2, x_15, x_4);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_withParams(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_4, 1);
x_8 = l_Lean_IR_LocalContext_addParams(x_7, x_2);
lean_ctor_set(x_4, 1, x_8);
x_9 = lean_apply_2(x_3, x_4, x_5);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_10 = lean_ctor_get(x_4, 0);
x_11 = lean_ctor_get(x_4, 1);
x_12 = lean_ctor_get(x_4, 2);
x_13 = lean_ctor_get(x_4, 3);
x_14 = lean_ctor_get(x_4, 4);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_4);
x_15 = l_Lean_IR_LocalContext_addParams(x_11, x_2);
x_16 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_16, 0, x_10);
lean_ctor_set(x_16, 1, x_15);
lean_ctor_set(x_16, 2, x_12);
lean_ctor_set(x_16, 3, x_13);
lean_ctor_set(x_16, 4, x_14);
x_17 = lean_apply_2(x_3, x_16, x_5);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_withParams___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_ExplicitBoxing_withParams___redArg(x_1, x_2, x_3, x_4);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_withParams___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_ExplicitBoxing_withParams(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_withVDecl___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_5, 1);
x_9 = l_Lean_IR_LocalContext_addLocal(x_8, x_1, x_2, x_3);
lean_ctor_set(x_5, 1, x_9);
x_10 = lean_apply_2(x_4, x_5, x_6);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_11 = lean_ctor_get(x_5, 0);
x_12 = lean_ctor_get(x_5, 1);
x_13 = lean_ctor_get(x_5, 2);
x_14 = lean_ctor_get(x_5, 3);
x_15 = lean_ctor_get(x_5, 4);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_5);
x_16 = l_Lean_IR_LocalContext_addLocal(x_12, x_1, x_2, x_3);
x_17 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_17, 0, x_11);
lean_ctor_set(x_17, 1, x_16);
lean_ctor_set(x_17, 2, x_13);
lean_ctor_set(x_17, 3, x_14);
lean_ctor_set(x_17, 4, x_15);
x_18 = lean_apply_2(x_4, x_17, x_6);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_withVDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_6, 1);
x_10 = l_Lean_IR_LocalContext_addLocal(x_9, x_2, x_3, x_4);
lean_ctor_set(x_6, 1, x_10);
x_11 = lean_apply_2(x_5, x_6, x_7);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_12 = lean_ctor_get(x_6, 0);
x_13 = lean_ctor_get(x_6, 1);
x_14 = lean_ctor_get(x_6, 2);
x_15 = lean_ctor_get(x_6, 3);
x_16 = lean_ctor_get(x_6, 4);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_6);
x_17 = l_Lean_IR_LocalContext_addLocal(x_13, x_2, x_3, x_4);
x_18 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_18, 0, x_12);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set(x_18, 2, x_14);
lean_ctor_set(x_18, 3, x_15);
lean_ctor_set(x_18, 4, x_16);
x_19 = lean_apply_2(x_5, x_18, x_7);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_withJDecl___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_5, 1);
x_9 = l_Lean_IR_LocalContext_addJP(x_8, x_1, x_2, x_3);
lean_ctor_set(x_5, 1, x_9);
x_10 = lean_apply_2(x_4, x_5, x_6);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_11 = lean_ctor_get(x_5, 0);
x_12 = lean_ctor_get(x_5, 1);
x_13 = lean_ctor_get(x_5, 2);
x_14 = lean_ctor_get(x_5, 3);
x_15 = lean_ctor_get(x_5, 4);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_5);
x_16 = l_Lean_IR_LocalContext_addJP(x_12, x_1, x_2, x_3);
x_17 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_17, 0, x_11);
lean_ctor_set(x_17, 1, x_16);
lean_ctor_set(x_17, 2, x_13);
lean_ctor_set(x_17, 3, x_14);
lean_ctor_set(x_17, 4, x_15);
x_18 = lean_apply_2(x_4, x_17, x_6);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_withJDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_6, 1);
x_10 = l_Lean_IR_LocalContext_addJP(x_9, x_2, x_3, x_4);
lean_ctor_set(x_6, 1, x_10);
x_11 = lean_apply_2(x_5, x_6, x_7);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_12 = lean_ctor_get(x_6, 0);
x_13 = lean_ctor_get(x_6, 1);
x_14 = lean_ctor_get(x_6, 2);
x_15 = lean_ctor_get(x_6, 3);
x_16 = lean_ctor_get(x_6, 4);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_6);
x_17 = l_Lean_IR_LocalContext_addJP(x_13, x_2, x_3, x_4);
x_18 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_18, 0, x_12);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set(x_18, 2, x_14);
lean_ctor_set(x_18, 3, x_15);
lean_ctor_set(x_18, 4, x_16);
x_19 = lean_apply_2(x_5, x_18, x_7);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_ExplicitBoxing_isExpensiveConstantValueBoxing(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
switch (lean_obj_tag(x_2)) {
case 1:
{
x_5 = x_4;
goto block_8;
}
case 2:
{
x_5 = x_4;
goto block_8;
}
default: 
{
lean_object* x_9; uint8_t x_10; 
x_9 = l_Lean_IR_ExplicitBoxing_getLocalContext(x_3, x_4);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = l_Lean_IR_LocalContext_getValue(x_11, x_1);
lean_dec(x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_ctor_set(x_9, 0, x_12);
return x_9;
}
else
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
switch (lean_obj_tag(x_13)) {
case 6:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_13, 1);
lean_inc_ref(x_14);
lean_dec_ref(x_13);
x_15 = lean_array_get_size(x_14);
lean_dec_ref(x_14);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_nat_dec_eq(x_15, x_16);
lean_dec(x_15);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec_ref(x_12);
x_18 = lean_box(0);
lean_ctor_set(x_9, 0, x_18);
return x_9;
}
else
{
lean_ctor_set(x_9, 0, x_12);
return x_9;
}
}
case 11:
{
lean_dec_ref(x_13);
lean_ctor_set(x_9, 0, x_12);
return x_9;
}
default: 
{
lean_object* x_19; 
lean_dec(x_13);
lean_dec_ref(x_12);
x_19 = lean_box(0);
lean_ctor_set(x_9, 0, x_19);
return x_9;
}
}
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_9, 0);
x_21 = lean_ctor_get(x_9, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_9);
x_22 = l_Lean_IR_LocalContext_getValue(x_20, x_1);
lean_dec(x_20);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
else
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
switch (lean_obj_tag(x_24)) {
case 6:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_25 = lean_ctor_get(x_24, 1);
lean_inc_ref(x_25);
lean_dec_ref(x_24);
x_26 = lean_array_get_size(x_25);
lean_dec_ref(x_25);
x_27 = lean_unsigned_to_nat(0u);
x_28 = lean_nat_dec_eq(x_26, x_27);
lean_dec(x_26);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
lean_dec_ref(x_22);
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_21);
return x_30;
}
else
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_22);
lean_ctor_set(x_31, 1, x_21);
return x_31;
}
}
case 11:
{
lean_object* x_32; 
lean_dec_ref(x_24);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_22);
lean_ctor_set(x_32, 1, x_21);
return x_32;
}
default: 
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_24);
lean_dec_ref(x_22);
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_21);
return x_34;
}
}
}
}
}
}
block_8:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_ExplicitBoxing_isExpensiveConstantValueBoxing___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_ExplicitBoxing_isExpensiveConstantValueBoxing(x_1, x_2, x_3, x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_find_x3f___at___Lean_IR_ExplicitBoxing_mkCast_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
lean_dec(x_1);
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 2);
lean_inc(x_6);
lean_dec_ref(x_2);
lean_inc(x_1);
x_7 = l_Lean_IR_FnBody_beq(x_4, x_1);
if (x_7 == 0)
{
lean_dec(x_5);
x_2 = x_6;
goto _start;
}
else
{
lean_object* x_9; 
lean_dec(x_6);
lean_dec(x_1);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_5);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_find_x3f___at___Lean_IR_ExplicitBoxing_mkCast_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_AssocList_find_x3f___at___Lean_IR_ExplicitBoxing_mkCast_spec__0___redArg(x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_IR_ExplicitBoxing_mkCast___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_ExplicitBoxing_mkCast___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_ExplicitBoxing_mkCast___closed__0;
x_2 = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_ExplicitBoxing_mkCast___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_boxed_const", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ExplicitBoxing_mkCast___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_ExplicitBoxing_mkCast___closed__2;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_ExplicitBoxing_mkCast___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_mkCast(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = l_Lean_IR_IRType_isScalar(x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_ExplicitBoxing_isExpensiveConstantValueBoxing(x_1, x_2, x_4, x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
lean_dec_ref(x_4);
lean_dec(x_3);
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_7, 0);
lean_dec(x_10);
x_11 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_11, 0, x_2);
lean_ctor_set(x_11, 1, x_1);
lean_ctor_set(x_7, 0, x_11);
return x_7;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_7, 1);
lean_inc(x_12);
lean_dec(x_7);
x_13 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_13, 0, x_2);
lean_ctor_set(x_13, 1, x_1);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
}
else
{
uint8_t x_15; 
lean_dec(x_1);
x_15 = !lean_is_exclusive(x_7);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_16 = lean_ctor_get(x_7, 1);
x_17 = lean_ctor_get(x_7, 0);
lean_dec(x_17);
x_18 = lean_ctor_get(x_8, 0);
lean_inc(x_18);
lean_dec_ref(x_8);
x_19 = lean_ctor_get(x_16, 0);
x_20 = lean_ctor_get(x_16, 1);
x_21 = lean_ctor_get(x_16, 2);
x_22 = lean_ctor_get(x_16, 3);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_unsigned_to_nat(2u);
lean_inc(x_2);
x_25 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_25, 0, x_2);
lean_ctor_set(x_25, 1, x_23);
x_26 = l_Lean_IR_ExplicitBoxing_mkCast___closed__1;
lean_inc(x_3);
x_27 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_27, 0, x_24);
lean_ctor_set(x_27, 1, x_3);
lean_ctor_set(x_27, 2, x_25);
lean_ctor_set(x_27, 3, x_26);
x_28 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_28, 0, x_23);
lean_ctor_set(x_28, 1, x_2);
lean_ctor_set(x_28, 2, x_18);
lean_ctor_set(x_28, 3, x_27);
lean_inc(x_21);
lean_inc_ref(x_28);
x_29 = l_Lean_AssocList_find_x3f___at___Lean_IR_ExplicitBoxing_mkCast_spec__0___redArg(x_28, x_21);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
lean_inc(x_22);
lean_inc(x_21);
lean_inc_ref(x_20);
lean_inc(x_19);
x_30 = !lean_is_exclusive(x_16);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_31 = lean_ctor_get(x_16, 3);
lean_dec(x_31);
x_32 = lean_ctor_get(x_16, 2);
lean_dec(x_32);
x_33 = lean_ctor_get(x_16, 1);
lean_dec(x_33);
x_34 = lean_ctor_get(x_16, 0);
lean_dec(x_34);
x_35 = !lean_is_exclusive(x_4);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_36 = lean_ctor_get(x_4, 0);
x_37 = lean_ctor_get(x_4, 4);
lean_dec(x_37);
x_38 = lean_ctor_get(x_4, 3);
lean_dec(x_38);
x_39 = lean_ctor_get(x_4, 2);
lean_dec(x_39);
x_40 = lean_ctor_get(x_4, 1);
lean_dec(x_40);
x_41 = l_Lean_IR_ExplicitBoxing_mkCast___closed__3;
lean_inc(x_22);
x_42 = lean_name_append_index_after(x_41, x_22);
x_43 = l_Lean_Name_append(x_36, x_42);
x_44 = l_Lean_IR_ExplicitBoxing_mkCast___closed__4;
lean_inc(x_43);
x_45 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
x_46 = lean_box(0);
lean_inc_ref(x_28);
lean_ctor_set(x_4, 4, x_46);
lean_ctor_set(x_4, 3, x_28);
lean_ctor_set(x_4, 2, x_3);
lean_ctor_set(x_4, 1, x_44);
lean_ctor_set(x_4, 0, x_43);
x_47 = lean_array_push(x_20, x_4);
lean_inc_ref(x_45);
x_48 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_48, 0, x_28);
lean_ctor_set(x_48, 1, x_45);
lean_ctor_set(x_48, 2, x_21);
x_49 = lean_nat_add(x_22, x_23);
lean_dec(x_22);
lean_ctor_set(x_16, 3, x_49);
lean_ctor_set(x_16, 2, x_48);
lean_ctor_set(x_16, 1, x_47);
lean_ctor_set(x_7, 0, x_45);
return x_7;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_50 = lean_ctor_get(x_4, 0);
lean_inc(x_50);
lean_dec(x_4);
x_51 = l_Lean_IR_ExplicitBoxing_mkCast___closed__3;
lean_inc(x_22);
x_52 = lean_name_append_index_after(x_51, x_22);
x_53 = l_Lean_Name_append(x_50, x_52);
x_54 = l_Lean_IR_ExplicitBoxing_mkCast___closed__4;
lean_inc(x_53);
x_55 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
x_56 = lean_box(0);
lean_inc_ref(x_28);
x_57 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_57, 0, x_53);
lean_ctor_set(x_57, 1, x_54);
lean_ctor_set(x_57, 2, x_3);
lean_ctor_set(x_57, 3, x_28);
lean_ctor_set(x_57, 4, x_56);
x_58 = lean_array_push(x_20, x_57);
lean_inc_ref(x_55);
x_59 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_59, 0, x_28);
lean_ctor_set(x_59, 1, x_55);
lean_ctor_set(x_59, 2, x_21);
x_60 = lean_nat_add(x_22, x_23);
lean_dec(x_22);
lean_ctor_set(x_16, 3, x_60);
lean_ctor_set(x_16, 2, x_59);
lean_ctor_set(x_16, 1, x_58);
lean_ctor_set(x_7, 0, x_55);
return x_7;
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_16);
x_61 = lean_ctor_get(x_4, 0);
lean_inc(x_61);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 lean_ctor_release(x_4, 4);
 x_62 = x_4;
} else {
 lean_dec_ref(x_4);
 x_62 = lean_box(0);
}
x_63 = l_Lean_IR_ExplicitBoxing_mkCast___closed__3;
lean_inc(x_22);
x_64 = lean_name_append_index_after(x_63, x_22);
x_65 = l_Lean_Name_append(x_61, x_64);
x_66 = l_Lean_IR_ExplicitBoxing_mkCast___closed__4;
lean_inc(x_65);
x_67 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
x_68 = lean_box(0);
lean_inc_ref(x_28);
if (lean_is_scalar(x_62)) {
 x_69 = lean_alloc_ctor(0, 5, 0);
} else {
 x_69 = x_62;
}
lean_ctor_set(x_69, 0, x_65);
lean_ctor_set(x_69, 1, x_66);
lean_ctor_set(x_69, 2, x_3);
lean_ctor_set(x_69, 3, x_28);
lean_ctor_set(x_69, 4, x_68);
x_70 = lean_array_push(x_20, x_69);
lean_inc_ref(x_67);
x_71 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_71, 0, x_28);
lean_ctor_set(x_71, 1, x_67);
lean_ctor_set(x_71, 2, x_21);
x_72 = lean_nat_add(x_22, x_23);
lean_dec(x_22);
x_73 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_73, 0, x_19);
lean_ctor_set(x_73, 1, x_70);
lean_ctor_set(x_73, 2, x_71);
lean_ctor_set(x_73, 3, x_72);
lean_ctor_set(x_7, 1, x_73);
lean_ctor_set(x_7, 0, x_67);
return x_7;
}
}
else
{
lean_object* x_74; 
lean_dec_ref(x_28);
lean_dec_ref(x_4);
lean_dec(x_3);
x_74 = lean_ctor_get(x_29, 0);
lean_inc(x_74);
lean_dec_ref(x_29);
lean_ctor_set(x_7, 0, x_74);
return x_7;
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_75 = lean_ctor_get(x_7, 1);
lean_inc(x_75);
lean_dec(x_7);
x_76 = lean_ctor_get(x_8, 0);
lean_inc(x_76);
lean_dec_ref(x_8);
x_77 = lean_ctor_get(x_75, 0);
x_78 = lean_ctor_get(x_75, 1);
x_79 = lean_ctor_get(x_75, 2);
x_80 = lean_ctor_get(x_75, 3);
x_81 = lean_unsigned_to_nat(1u);
x_82 = lean_unsigned_to_nat(2u);
lean_inc(x_2);
x_83 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_83, 0, x_2);
lean_ctor_set(x_83, 1, x_81);
x_84 = l_Lean_IR_ExplicitBoxing_mkCast___closed__1;
lean_inc(x_3);
x_85 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_85, 0, x_82);
lean_ctor_set(x_85, 1, x_3);
lean_ctor_set(x_85, 2, x_83);
lean_ctor_set(x_85, 3, x_84);
x_86 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_86, 0, x_81);
lean_ctor_set(x_86, 1, x_2);
lean_ctor_set(x_86, 2, x_76);
lean_ctor_set(x_86, 3, x_85);
lean_inc(x_79);
lean_inc_ref(x_86);
x_87 = l_Lean_AssocList_find_x3f___at___Lean_IR_ExplicitBoxing_mkCast_spec__0___redArg(x_86, x_79);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
lean_inc(x_80);
lean_inc(x_79);
lean_inc_ref(x_78);
lean_inc(x_77);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 lean_ctor_release(x_75, 2);
 lean_ctor_release(x_75, 3);
 x_88 = x_75;
} else {
 lean_dec_ref(x_75);
 x_88 = lean_box(0);
}
x_89 = lean_ctor_get(x_4, 0);
lean_inc(x_89);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 lean_ctor_release(x_4, 4);
 x_90 = x_4;
} else {
 lean_dec_ref(x_4);
 x_90 = lean_box(0);
}
x_91 = l_Lean_IR_ExplicitBoxing_mkCast___closed__3;
lean_inc(x_80);
x_92 = lean_name_append_index_after(x_91, x_80);
x_93 = l_Lean_Name_append(x_89, x_92);
x_94 = l_Lean_IR_ExplicitBoxing_mkCast___closed__4;
lean_inc(x_93);
x_95 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
x_96 = lean_box(0);
lean_inc_ref(x_86);
if (lean_is_scalar(x_90)) {
 x_97 = lean_alloc_ctor(0, 5, 0);
} else {
 x_97 = x_90;
}
lean_ctor_set(x_97, 0, x_93);
lean_ctor_set(x_97, 1, x_94);
lean_ctor_set(x_97, 2, x_3);
lean_ctor_set(x_97, 3, x_86);
lean_ctor_set(x_97, 4, x_96);
x_98 = lean_array_push(x_78, x_97);
lean_inc_ref(x_95);
x_99 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_99, 0, x_86);
lean_ctor_set(x_99, 1, x_95);
lean_ctor_set(x_99, 2, x_79);
x_100 = lean_nat_add(x_80, x_81);
lean_dec(x_80);
if (lean_is_scalar(x_88)) {
 x_101 = lean_alloc_ctor(0, 4, 0);
} else {
 x_101 = x_88;
}
lean_ctor_set(x_101, 0, x_77);
lean_ctor_set(x_101, 1, x_98);
lean_ctor_set(x_101, 2, x_99);
lean_ctor_set(x_101, 3, x_100);
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_95);
lean_ctor_set(x_102, 1, x_101);
return x_102;
}
else
{
lean_object* x_103; lean_object* x_104; 
lean_dec_ref(x_86);
lean_dec_ref(x_4);
lean_dec(x_3);
x_103 = lean_ctor_get(x_87, 0);
lean_inc(x_103);
lean_dec_ref(x_87);
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_75);
return x_104;
}
}
}
}
else
{
lean_object* x_105; lean_object* x_106; 
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_105 = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(x_105, 0, x_1);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_5);
return x_106;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_castVarIfNeeded(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = l_Lean_IR_ExplicitBoxing_getVarType(x_1, x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec_ref(x_6);
x_9 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_7, x_2);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_10 = l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_ExplicitBoxing_M_mkFresh___redArg(x_8);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec_ref(x_10);
lean_inc_ref(x_4);
lean_inc(x_2);
x_13 = l_Lean_IR_ExplicitBoxing_mkCast(x_1, x_7, x_2, x_4, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec_ref(x_13);
lean_inc(x_11);
x_16 = lean_apply_3(x_3, x_11, x_4, x_15);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_19, 0, x_11);
lean_ctor_set(x_19, 1, x_2);
lean_ctor_set(x_19, 2, x_14);
lean_ctor_set(x_19, 3, x_18);
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
x_22 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_22, 0, x_11);
lean_ctor_set(x_22, 1, x_2);
lean_ctor_set(x_22, 2, x_14);
lean_ctor_set(x_22, 3, x_20);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
else
{
lean_object* x_24; 
lean_dec(x_7);
lean_dec(x_2);
x_24 = lean_apply_3(x_3, x_1, x_4, x_8);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_castArgIfNeeded___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_2);
x_6 = lean_apply_3(x_1, x_5, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_castArgIfNeeded(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec_ref(x_1);
x_7 = l_Lean_IR_ExplicitBoxing_getVarType(x_6, x_4, x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec_ref(x_7);
x_10 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_8, x_2);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_11 = l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_ExplicitBoxing_M_mkFresh___redArg(x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec_ref(x_11);
lean_inc_ref(x_4);
lean_inc(x_2);
x_14 = l_Lean_IR_ExplicitBoxing_mkCast(x_6, x_8, x_2, x_4, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec_ref(x_14);
lean_inc(x_12);
x_17 = l_Lean_IR_ExplicitBoxing_castArgIfNeeded___lam__0(x_3, x_12, x_4, x_16);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_20, 0, x_12);
lean_ctor_set(x_20, 1, x_2);
lean_ctor_set(x_20, 2, x_15);
lean_ctor_set(x_20, 3, x_19);
lean_ctor_set(x_17, 0, x_20);
return x_17;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_17, 0);
x_22 = lean_ctor_get(x_17, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_17);
x_23 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_23, 0, x_12);
lean_ctor_set(x_23, 1, x_2);
lean_ctor_set(x_23, 2, x_15);
lean_ctor_set(x_23, 3, x_21);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
else
{
lean_object* x_25; 
lean_dec(x_8);
lean_dec(x_2);
x_25 = l_Lean_IR_ExplicitBoxing_castArgIfNeeded___lam__0(x_3, x_6, x_4, x_9);
return x_25;
}
}
else
{
lean_object* x_26; 
lean_dec(x_2);
x_26 = lean_apply_3(x_3, x_1, x_4, x_5);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_IR_ExplicitBoxing_castArgsIfNeededAux_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_lt(x_4, x_3);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec_ref(x_6);
lean_dec_ref(x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_27; 
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_5, 0);
lean_inc(x_11);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_12 = x_5;
} else {
 lean_dec_ref(x_5);
 x_12 = lean_box(0);
}
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_10, 1);
lean_inc(x_14);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_15 = x_10;
} else {
 lean_dec_ref(x_10);
 x_15 = lean_box(0);
}
x_27 = lean_array_uget(x_2, x_4);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = l_Lean_IR_ExplicitBoxing_getVarType(x_28, x_6, x_7);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec_ref(x_29);
lean_inc_ref(x_1);
lean_inc(x_13);
x_32 = lean_apply_1(x_1, x_13);
x_33 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_30, x_32);
if (x_33 == 0)
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_27);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_35 = lean_ctor_get(x_27, 0);
lean_dec(x_35);
x_36 = l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_ExplicitBoxing_M_mkFresh___redArg(x_31);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec_ref(x_36);
lean_inc_ref(x_6);
lean_inc(x_32);
x_39 = l_Lean_IR_ExplicitBoxing_mkCast(x_28, x_30, x_32, x_6, x_38);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec_ref(x_39);
x_42 = lean_box(12);
lean_inc(x_37);
x_43 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_43, 0, x_37);
lean_ctor_set(x_43, 1, x_32);
lean_ctor_set(x_43, 2, x_40);
lean_ctor_set(x_43, 3, x_42);
lean_ctor_set(x_27, 0, x_37);
x_44 = lean_array_push(x_14, x_27);
x_45 = lean_array_push(x_11, x_43);
x_16 = x_45;
x_17 = x_44;
x_18 = x_41;
goto block_26;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_27);
x_46 = l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_ExplicitBoxing_M_mkFresh___redArg(x_31);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec_ref(x_46);
lean_inc_ref(x_6);
lean_inc(x_32);
x_49 = l_Lean_IR_ExplicitBoxing_mkCast(x_28, x_30, x_32, x_6, x_48);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec_ref(x_49);
x_52 = lean_box(12);
lean_inc(x_47);
x_53 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_53, 0, x_47);
lean_ctor_set(x_53, 1, x_32);
lean_ctor_set(x_53, 2, x_50);
lean_ctor_set(x_53, 3, x_52);
x_54 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_54, 0, x_47);
x_55 = lean_array_push(x_14, x_54);
x_56 = lean_array_push(x_11, x_53);
x_16 = x_56;
x_17 = x_55;
x_18 = x_51;
goto block_26;
}
}
else
{
lean_object* x_57; 
lean_dec(x_32);
lean_dec(x_30);
lean_dec(x_28);
x_57 = lean_array_push(x_14, x_27);
x_16 = x_11;
x_17 = x_57;
x_18 = x_31;
goto block_26;
}
}
else
{
lean_object* x_58; 
x_58 = lean_array_push(x_14, x_27);
x_16 = x_11;
x_17 = x_58;
x_18 = x_7;
goto block_26;
}
block_26:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_13, x_19);
lean_dec(x_13);
if (lean_is_scalar(x_15)) {
 x_21 = lean_alloc_ctor(0, 2, 0);
} else {
 x_21 = x_15;
}
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_17);
if (lean_is_scalar(x_12)) {
 x_22 = lean_alloc_ctor(0, 2, 0);
} else {
 x_22 = x_12;
}
lean_ctor_set(x_22, 0, x_16);
lean_ctor_set(x_22, 1, x_21);
x_23 = 1;
x_24 = lean_usize_add(x_4, x_23);
x_4 = x_24;
x_5 = x_22;
x_7 = x_18;
goto _start;
}
}
}
}
static lean_object* _init_l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_ExplicitBoxing_mkCast___closed__4;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___closed__0;
x_2 = l_Lean_IR_ExplicitBoxing_mkCast___closed__4;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_5 = l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___closed__1;
x_6 = lean_array_size(x_1);
x_7 = 0;
x_8 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_IR_ExplicitBoxing_castArgsIfNeededAux_spec__0(x_2, x_1, x_6, x_7, x_5, x_3, x_4);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
x_11 = !lean_is_exclusive(x_8);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_8, 1);
x_13 = lean_ctor_get(x_8, 0);
lean_dec(x_13);
x_14 = lean_ctor_get(x_9, 0);
lean_inc(x_14);
lean_dec(x_9);
x_15 = !lean_is_exclusive(x_10);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_10, 1);
x_17 = lean_ctor_get(x_10, 0);
lean_dec(x_17);
lean_ctor_set(x_8, 1, x_14);
lean_ctor_set(x_8, 0, x_16);
lean_ctor_set(x_10, 1, x_12);
lean_ctor_set(x_10, 0, x_8);
return x_10;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_10, 1);
lean_inc(x_18);
lean_dec(x_10);
lean_ctor_set(x_8, 1, x_14);
lean_ctor_set(x_8, 0, x_18);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_8);
lean_ctor_set(x_19, 1, x_12);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_8, 1);
lean_inc(x_20);
lean_dec(x_8);
x_21 = lean_ctor_get(x_9, 0);
lean_inc(x_21);
lean_dec(x_9);
x_22 = lean_ctor_get(x_10, 1);
lean_inc(x_22);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_23 = x_10;
} else {
 lean_dec_ref(x_10);
 x_23 = lean_box(0);
}
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_21);
if (lean_is_scalar(x_23)) {
 x_25 = lean_alloc_ctor(0, 2, 0);
} else {
 x_25 = x_23;
}
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_20);
return x_25;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_IR_ExplicitBoxing_castArgsIfNeededAux_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_IR_ExplicitBoxing_castArgsIfNeededAux_spec__0(x_1, x_2, x_8, x_9, x_5, x_6, x_7);
lean_dec_ref(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux(x_1, x_2, x_3, x_4);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_castArgsIfNeeded___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_array_get_borrowed(x_1, x_2, x_3);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_castArgsIfNeeded(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_6 = l_Lean_IR_instInhabitedParam;
x_7 = lean_alloc_closure((void*)(l_Lean_IR_ExplicitBoxing_castArgsIfNeeded___lam__0___boxed), 3, 2);
lean_closure_set(x_7, 0, x_6);
lean_closure_set(x_7, 1, x_2);
lean_inc_ref(x_4);
x_8 = l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux(x_1, x_7, x_4, x_5);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_dec(x_9);
x_13 = lean_apply_3(x_3, x_11, x_4, x_10);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = l_Lean_IR_reshape(x_12, x_15);
lean_ctor_set(x_13, 0, x_16);
return x_13;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_13, 0);
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_13);
x_19 = l_Lean_IR_reshape(x_12, x_17);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_castArgsIfNeeded___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_ExplicitBoxing_castArgsIfNeeded___lam__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_castArgsIfNeeded___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_ExplicitBoxing_castArgsIfNeeded(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_boxArgsIfNeeded___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(8);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_boxArgsIfNeeded(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_5 = lean_alloc_closure((void*)(l_Lean_IR_ExplicitBoxing_boxArgsIfNeeded___lam__0___boxed), 1, 0);
lean_inc_ref(x_3);
x_6 = l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux(x_1, x_5, x_3, x_4);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec_ref(x_6);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_dec(x_7);
x_11 = lean_apply_3(x_2, x_9, x_3, x_8);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = l_Lean_IR_reshape(x_10, x_13);
lean_ctor_set(x_11, 0, x_14);
return x_11;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_11, 0);
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_11);
x_17 = l_Lean_IR_reshape(x_10, x_15);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_boxArgsIfNeeded___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_IR_ExplicitBoxing_boxArgsIfNeeded___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_boxArgsIfNeeded___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_ExplicitBoxing_boxArgsIfNeeded(x_1, x_2, x_3, x_4);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_unboxResultIfNeeded___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = l_Lean_IR_IRType_isScalar(x_2);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_2);
lean_ctor_set(x_7, 2, x_3);
lean_ctor_set(x_7, 3, x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_5);
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_ExplicitBoxing_M_mkFresh___redArg(x_5);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_box(8);
lean_inc(x_11);
x_13 = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(x_13, 0, x_11);
x_14 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_14, 1, x_2);
lean_ctor_set(x_14, 2, x_13);
lean_ctor_set(x_14, 3, x_4);
x_15 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_15, 0, x_11);
lean_ctor_set(x_15, 1, x_12);
lean_ctor_set(x_15, 2, x_3);
lean_ctor_set(x_15, 3, x_14);
lean_ctor_set(x_9, 0, x_15);
return x_9;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_ctor_get(x_9, 0);
x_17 = lean_ctor_get(x_9, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_9);
x_18 = lean_box(8);
lean_inc(x_16);
x_19 = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(x_19, 0, x_16);
x_20 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_20, 0, x_1);
lean_ctor_set(x_20, 1, x_2);
lean_ctor_set(x_20, 2, x_19);
lean_ctor_set(x_20, 3, x_4);
x_21 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_21, 0, x_16);
lean_ctor_set(x_21, 1, x_18);
lean_ctor_set(x_21, 2, x_3);
lean_ctor_set(x_21, 3, x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_17);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_unboxResultIfNeeded(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_IR_ExplicitBoxing_unboxResultIfNeeded___redArg(x_1, x_2, x_3, x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_unboxResultIfNeeded___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_IR_ExplicitBoxing_unboxResultIfNeeded(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_castResultIfNeeded(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_2, x_4);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_9 = l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_ExplicitBoxing_M_mkFresh___redArg(x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec_ref(x_9);
x_12 = l_Lean_IR_IRType_boxed(x_2);
lean_inc(x_2);
lean_inc(x_12);
lean_inc(x_10);
x_13 = l_Lean_IR_ExplicitBoxing_mkCast(x_10, x_12, x_2, x_6, x_11);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_2);
lean_ctor_set(x_16, 2, x_15);
lean_ctor_set(x_16, 3, x_5);
x_17 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_17, 0, x_10);
lean_ctor_set(x_17, 1, x_12);
lean_ctor_set(x_17, 2, x_3);
lean_ctor_set(x_17, 3, x_16);
lean_ctor_set(x_13, 0, x_17);
return x_13;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_13, 0);
x_19 = lean_ctor_get(x_13, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_13);
x_20 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_20, 0, x_1);
lean_ctor_set(x_20, 1, x_2);
lean_ctor_set(x_20, 2, x_18);
lean_ctor_set(x_20, 3, x_5);
x_21 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_21, 0, x_10);
lean_ctor_set(x_21, 1, x_12);
lean_ctor_set(x_21, 2, x_3);
lean_ctor_set(x_21, 3, x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_19);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec_ref(x_6);
x_23 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_23, 0, x_1);
lean_ctor_set(x_23, 1, x_2);
lean_ctor_set(x_23, 2, x_3);
lean_ctor_set(x_23, 3, x_5);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_7);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_castResultIfNeeded___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_IR_ExplicitBoxing_castResultIfNeeded(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_visitVDeclExpr___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_array_get_borrowed(x_1, x_2, x_3);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
return x_5;
}
}
static lean_object* _init_l_Lean_IR_ExplicitBoxing_visitVDeclExpr___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_IR_ExplicitBoxing_boxArgsIfNeeded___lam__0___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_visitVDeclExpr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (lean_obj_tag(x_3)) {
case 0:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_33; 
x_7 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_7);
x_8 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_8);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_9 = x_3;
} else {
 lean_dec_ref(x_3);
 x_9 = lean_box(0);
}
x_10 = l_Lean_IR_ExplicitBoxing_visitVDeclExpr___closed__0;
x_33 = l_Lean_IR_CtorInfo_isScalar(x_7);
if (x_33 == 0)
{
x_11 = x_33;
goto block_32;
}
else
{
uint8_t x_34; 
x_34 = l_Lean_IR_IRType_isScalar(x_2);
x_11 = x_34;
goto block_32;
}
block_32:
{
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux(x_8, x_10, x_5, x_6);
lean_dec_ref(x_8);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec_ref(x_12);
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_13, 0);
x_17 = lean_ctor_get(x_13, 1);
if (lean_is_scalar(x_9)) {
 x_18 = lean_alloc_ctor(0, 2, 0);
} else {
 x_18 = x_9;
}
lean_ctor_set(x_18, 0, x_7);
lean_ctor_set(x_18, 1, x_16);
x_19 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_19, 0, x_1);
lean_ctor_set(x_19, 1, x_2);
lean_ctor_set(x_19, 2, x_18);
lean_ctor_set(x_19, 3, x_4);
x_20 = l_Lean_IR_reshape(x_17, x_19);
lean_ctor_set(x_13, 1, x_14);
lean_ctor_set(x_13, 0, x_20);
return x_13;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_21 = lean_ctor_get(x_13, 0);
x_22 = lean_ctor_get(x_13, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_13);
if (lean_is_scalar(x_9)) {
 x_23 = lean_alloc_ctor(0, 2, 0);
} else {
 x_23 = x_9;
}
lean_ctor_set(x_23, 0, x_7);
lean_ctor_set(x_23, 1, x_21);
x_24 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_24, 0, x_1);
lean_ctor_set(x_24, 1, x_2);
lean_ctor_set(x_24, 2, x_23);
lean_ctor_set(x_24, 3, x_4);
x_25 = l_Lean_IR_reshape(x_22, x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_14);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_5);
x_27 = lean_ctor_get(x_7, 1);
lean_inc(x_27);
lean_dec_ref(x_7);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_30 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_30, 0, x_1);
lean_ctor_set(x_30, 1, x_2);
lean_ctor_set(x_30, 2, x_29);
lean_ctor_set(x_30, 3, x_4);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_6);
return x_31;
}
}
}
case 2:
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_3);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_36 = lean_ctor_get(x_3, 2);
x_37 = l_Lean_IR_ExplicitBoxing_visitVDeclExpr___closed__0;
x_38 = l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux(x_36, x_37, x_5, x_6);
lean_dec_ref(x_36);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec_ref(x_38);
x_41 = !lean_is_exclusive(x_39);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_42 = lean_ctor_get(x_39, 0);
x_43 = lean_ctor_get(x_39, 1);
lean_ctor_set(x_3, 2, x_42);
x_44 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_44, 0, x_1);
lean_ctor_set(x_44, 1, x_2);
lean_ctor_set(x_44, 2, x_3);
lean_ctor_set(x_44, 3, x_4);
x_45 = l_Lean_IR_reshape(x_43, x_44);
lean_ctor_set(x_39, 1, x_40);
lean_ctor_set(x_39, 0, x_45);
return x_39;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_46 = lean_ctor_get(x_39, 0);
x_47 = lean_ctor_get(x_39, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_39);
lean_ctor_set(x_3, 2, x_46);
x_48 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_48, 0, x_1);
lean_ctor_set(x_48, 1, x_2);
lean_ctor_set(x_48, 2, x_3);
lean_ctor_set(x_48, 3, x_4);
x_49 = l_Lean_IR_reshape(x_47, x_48);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_40);
return x_50;
}
}
else
{
lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_51 = lean_ctor_get(x_3, 0);
x_52 = lean_ctor_get(x_3, 1);
x_53 = lean_ctor_get_uint8(x_3, sizeof(void*)*3);
x_54 = lean_ctor_get(x_3, 2);
lean_inc(x_54);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_3);
x_55 = l_Lean_IR_ExplicitBoxing_visitVDeclExpr___closed__0;
x_56 = l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux(x_54, x_55, x_5, x_6);
lean_dec_ref(x_54);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec_ref(x_56);
x_59 = lean_ctor_get(x_57, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_57, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_61 = x_57;
} else {
 lean_dec_ref(x_57);
 x_61 = lean_box(0);
}
x_62 = lean_alloc_ctor(2, 3, 1);
lean_ctor_set(x_62, 0, x_51);
lean_ctor_set(x_62, 1, x_52);
lean_ctor_set(x_62, 2, x_59);
lean_ctor_set_uint8(x_62, sizeof(void*)*3, x_53);
x_63 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_63, 0, x_1);
lean_ctor_set(x_63, 1, x_2);
lean_ctor_set(x_63, 2, x_62);
lean_ctor_set(x_63, 3, x_4);
x_64 = l_Lean_IR_reshape(x_60, x_63);
if (lean_is_scalar(x_61)) {
 x_65 = lean_alloc_ctor(0, 2, 0);
} else {
 x_65 = x_61;
}
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_58);
return x_65;
}
}
case 6:
{
uint8_t x_66; 
x_66 = !lean_is_exclusive(x_3);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; 
x_67 = lean_ctor_get(x_3, 0);
x_68 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_5);
lean_inc(x_67);
x_69 = l_Lean_IR_ExplicitBoxing_getDecl(x_67, x_5, x_6);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec_ref(x_69);
x_72 = l_Lean_IR_Decl_params(x_70);
x_73 = l_Lean_IR_instInhabitedParam;
x_74 = lean_alloc_closure((void*)(l_Lean_IR_ExplicitBoxing_visitVDeclExpr___lam__2___boxed), 3, 2);
lean_closure_set(x_74, 0, x_73);
lean_closure_set(x_74, 1, x_72);
lean_inc_ref(x_5);
x_75 = l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux(x_68, x_74, x_5, x_71);
lean_dec_ref(x_68);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec_ref(x_75);
x_78 = lean_ctor_get(x_76, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_76, 1);
lean_inc(x_79);
lean_dec(x_76);
lean_ctor_set(x_3, 1, x_78);
x_80 = l_Lean_IR_Decl_resultType(x_70);
lean_dec(x_70);
x_81 = l_Lean_IR_ExplicitBoxing_castResultIfNeeded(x_1, x_2, x_3, x_80, x_4, x_5, x_77);
lean_dec(x_80);
x_82 = !lean_is_exclusive(x_81);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_81, 0);
x_84 = l_Lean_IR_reshape(x_79, x_83);
lean_ctor_set(x_81, 0, x_84);
return x_81;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_85 = lean_ctor_get(x_81, 0);
x_86 = lean_ctor_get(x_81, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_81);
x_87 = l_Lean_IR_reshape(x_79, x_85);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_86);
return x_88;
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_89 = lean_ctor_get(x_3, 0);
x_90 = lean_ctor_get(x_3, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_3);
lean_inc_ref(x_5);
lean_inc(x_89);
x_91 = l_Lean_IR_ExplicitBoxing_getDecl(x_89, x_5, x_6);
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
lean_dec_ref(x_91);
x_94 = l_Lean_IR_Decl_params(x_92);
x_95 = l_Lean_IR_instInhabitedParam;
x_96 = lean_alloc_closure((void*)(l_Lean_IR_ExplicitBoxing_visitVDeclExpr___lam__2___boxed), 3, 2);
lean_closure_set(x_96, 0, x_95);
lean_closure_set(x_96, 1, x_94);
lean_inc_ref(x_5);
x_97 = l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux(x_90, x_96, x_5, x_93);
lean_dec_ref(x_90);
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_97, 1);
lean_inc(x_99);
lean_dec_ref(x_97);
x_100 = lean_ctor_get(x_98, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_98, 1);
lean_inc(x_101);
lean_dec(x_98);
x_102 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_102, 0, x_89);
lean_ctor_set(x_102, 1, x_100);
x_103 = l_Lean_IR_Decl_resultType(x_92);
lean_dec(x_92);
x_104 = l_Lean_IR_ExplicitBoxing_castResultIfNeeded(x_1, x_2, x_102, x_103, x_4, x_5, x_99);
lean_dec(x_103);
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
x_108 = l_Lean_IR_reshape(x_101, x_105);
if (lean_is_scalar(x_107)) {
 x_109 = lean_alloc_ctor(0, 2, 0);
} else {
 x_109 = x_107;
}
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_106);
return x_109;
}
}
case 7:
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; uint8_t x_137; 
x_110 = lean_ctor_get(x_3, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_111);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_112 = x_3;
} else {
 lean_dec_ref(x_3);
 x_112 = lean_box(0);
}
x_113 = l_Lean_IR_ExplicitBoxing_getEnv(x_5, x_6);
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_113, 1);
lean_inc(x_115);
lean_dec_ref(x_113);
lean_inc_ref(x_5);
lean_inc(x_110);
x_116 = l_Lean_IR_ExplicitBoxing_getDecl(x_110, x_5, x_115);
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_116, 1);
lean_inc(x_118);
lean_dec_ref(x_116);
x_119 = l_Lean_IR_ExplicitBoxing_visitVDeclExpr___closed__0;
x_137 = l_Lean_IR_ExplicitBoxing_requiresBoxedVersion(x_114, x_117);
lean_dec(x_117);
if (x_137 == 0)
{
x_120 = x_110;
goto block_136;
}
else
{
lean_object* x_138; 
x_138 = l_Lean_IR_ExplicitBoxing_mkBoxedName(x_110);
x_120 = x_138;
goto block_136;
}
block_136:
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; uint8_t x_124; 
x_121 = l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux(x_111, x_119, x_5, x_118);
lean_dec_ref(x_111);
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_121, 1);
lean_inc(x_123);
lean_dec_ref(x_121);
x_124 = !lean_is_exclusive(x_122);
if (x_124 == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_125 = lean_ctor_get(x_122, 0);
x_126 = lean_ctor_get(x_122, 1);
if (lean_is_scalar(x_112)) {
 x_127 = lean_alloc_ctor(7, 2, 0);
} else {
 x_127 = x_112;
}
lean_ctor_set(x_127, 0, x_120);
lean_ctor_set(x_127, 1, x_125);
x_128 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_128, 0, x_1);
lean_ctor_set(x_128, 1, x_2);
lean_ctor_set(x_128, 2, x_127);
lean_ctor_set(x_128, 3, x_4);
x_129 = l_Lean_IR_reshape(x_126, x_128);
lean_ctor_set(x_122, 1, x_123);
lean_ctor_set(x_122, 0, x_129);
return x_122;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_130 = lean_ctor_get(x_122, 0);
x_131 = lean_ctor_get(x_122, 1);
lean_inc(x_131);
lean_inc(x_130);
lean_dec(x_122);
if (lean_is_scalar(x_112)) {
 x_132 = lean_alloc_ctor(7, 2, 0);
} else {
 x_132 = x_112;
}
lean_ctor_set(x_132, 0, x_120);
lean_ctor_set(x_132, 1, x_130);
x_133 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_133, 0, x_1);
lean_ctor_set(x_133, 1, x_2);
lean_ctor_set(x_133, 2, x_132);
lean_ctor_set(x_133, 3, x_4);
x_134 = l_Lean_IR_reshape(x_131, x_133);
x_135 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_123);
return x_135;
}
}
}
case 8:
{
uint8_t x_139; 
x_139 = !lean_is_exclusive(x_3);
if (x_139 == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; uint8_t x_148; 
x_140 = lean_ctor_get(x_3, 1);
x_141 = l_Lean_IR_ExplicitBoxing_visitVDeclExpr___closed__0;
x_142 = l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux(x_140, x_141, x_5, x_6);
lean_dec_ref(x_140);
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_142, 1);
lean_inc(x_144);
lean_dec_ref(x_142);
x_145 = lean_ctor_get(x_143, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_143, 1);
lean_inc(x_146);
lean_dec(x_143);
lean_ctor_set(x_3, 1, x_145);
x_147 = l_Lean_IR_ExplicitBoxing_unboxResultIfNeeded___redArg(x_1, x_2, x_3, x_4, x_144);
x_148 = !lean_is_exclusive(x_147);
if (x_148 == 0)
{
lean_object* x_149; lean_object* x_150; 
x_149 = lean_ctor_get(x_147, 0);
x_150 = l_Lean_IR_reshape(x_146, x_149);
lean_ctor_set(x_147, 0, x_150);
return x_147;
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_151 = lean_ctor_get(x_147, 0);
x_152 = lean_ctor_get(x_147, 1);
lean_inc(x_152);
lean_inc(x_151);
lean_dec(x_147);
x_153 = l_Lean_IR_reshape(x_146, x_151);
x_154 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_154, 0, x_153);
lean_ctor_set(x_154, 1, x_152);
return x_154;
}
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_155 = lean_ctor_get(x_3, 0);
x_156 = lean_ctor_get(x_3, 1);
lean_inc(x_156);
lean_inc(x_155);
lean_dec(x_3);
x_157 = l_Lean_IR_ExplicitBoxing_visitVDeclExpr___closed__0;
x_158 = l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux(x_156, x_157, x_5, x_6);
lean_dec_ref(x_156);
x_159 = lean_ctor_get(x_158, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_158, 1);
lean_inc(x_160);
lean_dec_ref(x_158);
x_161 = lean_ctor_get(x_159, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_159, 1);
lean_inc(x_162);
lean_dec(x_159);
x_163 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_163, 0, x_155);
lean_ctor_set(x_163, 1, x_161);
x_164 = l_Lean_IR_ExplicitBoxing_unboxResultIfNeeded___redArg(x_1, x_2, x_163, x_4, x_160);
x_165 = lean_ctor_get(x_164, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_164, 1);
lean_inc(x_166);
if (lean_is_exclusive(x_164)) {
 lean_ctor_release(x_164, 0);
 lean_ctor_release(x_164, 1);
 x_167 = x_164;
} else {
 lean_dec_ref(x_164);
 x_167 = lean_box(0);
}
x_168 = l_Lean_IR_reshape(x_162, x_165);
if (lean_is_scalar(x_167)) {
 x_169 = lean_alloc_ctor(0, 2, 0);
} else {
 x_169 = x_167;
}
lean_ctor_set(x_169, 0, x_168);
lean_ctor_set(x_169, 1, x_166);
return x_169;
}
}
default: 
{
lean_object* x_170; lean_object* x_171; 
lean_dec_ref(x_5);
x_170 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_170, 0, x_1);
lean_ctor_set(x_170, 1, x_2);
lean_ctor_set(x_170, 2, x_3);
lean_ctor_set(x_170, 3, x_4);
x_171 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_171, 0, x_170);
lean_ctor_set(x_171, 1, x_6);
return x_171;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_visitVDeclExpr___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_ExplicitBoxing_visitVDeclExpr___lam__2(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_IR_ExplicitBoxing_visitFnBody_spec__0(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_lt(x_2, x_1);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec_ref(x_4);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_array_uget(x_3, x_2);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_array_uset(x_3, x_2, x_9);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_8);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_8, 1);
lean_inc_ref(x_4);
x_20 = l_Lean_IR_ExplicitBoxing_visitFnBody(x_19, x_4, x_5);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec_ref(x_20);
lean_ctor_set(x_8, 1, x_21);
x_11 = x_8;
x_12 = x_22;
goto block_17;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_23 = lean_ctor_get(x_8, 0);
x_24 = lean_ctor_get(x_8, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_8);
lean_inc_ref(x_4);
x_25 = l_Lean_IR_ExplicitBoxing_visitFnBody(x_24, x_4, x_5);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec_ref(x_25);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_23);
lean_ctor_set(x_28, 1, x_26);
x_11 = x_28;
x_12 = x_27;
goto block_17;
}
}
else
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_8);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_8, 0);
lean_inc_ref(x_4);
x_31 = l_Lean_IR_ExplicitBoxing_visitFnBody(x_30, x_4, x_5);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec_ref(x_31);
lean_ctor_set(x_8, 0, x_32);
x_11 = x_8;
x_12 = x_33;
goto block_17;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_34 = lean_ctor_get(x_8, 0);
lean_inc(x_34);
lean_dec(x_8);
lean_inc_ref(x_4);
x_35 = l_Lean_IR_ExplicitBoxing_visitFnBody(x_34, x_4, x_5);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec_ref(x_35);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_36);
x_11 = x_38;
x_12 = x_37;
goto block_17;
}
}
block_17:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = 1;
x_14 = lean_usize_add(x_2, x_13);
x_15 = lean_array_uset(x_10, x_2, x_11);
x_2 = x_14;
x_3 = x_15;
x_5 = x_12;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_visitFnBody___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_alloc_ctor(4, 4, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_2);
lean_ctor_set(x_7, 2, x_4);
lean_ctor_set(x_7, 3, x_3);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_visitFnBody___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_alloc_ctor(5, 6, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_2);
lean_ctor_set(x_9, 2, x_3);
lean_ctor_set(x_9, 3, x_6);
lean_ctor_set(x_9, 4, x_4);
lean_ctor_set(x_9, 5, x_5);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_visitFnBody___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_alloc_ctor(9, 4, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_4);
lean_ctor_set(x_7, 2, x_2);
lean_ctor_set(x_7, 3, x_3);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_visitFnBody___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(x_4, 0, x_1);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_visitFnBody___lam__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_2);
x_6 = lean_apply_3(x_1, x_5, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_visitFnBody___lam__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_array_get_borrowed(x_1, x_2, x_3);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_visitFnBody(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_6);
x_7 = lean_ctor_get(x_1, 3);
lean_inc(x_7);
lean_dec_ref(x_1);
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 1);
x_10 = lean_ctor_get(x_2, 2);
x_11 = lean_ctor_get(x_2, 3);
x_12 = lean_ctor_get(x_2, 4);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_9);
x_13 = l_Lean_IR_LocalContext_addLocal(x_9, x_4, x_5, x_6);
lean_inc_ref(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc(x_8);
x_14 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_14, 0, x_8);
lean_ctor_set(x_14, 1, x_13);
lean_ctor_set(x_14, 2, x_10);
lean_ctor_set(x_14, 3, x_11);
lean_ctor_set(x_14, 4, x_12);
x_15 = l_Lean_IR_ExplicitBoxing_visitFnBody(x_7, x_14, x_3);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec_ref(x_15);
x_18 = l_Lean_IR_ExplicitBoxing_visitVDeclExpr(x_4, x_5, x_6, x_16, x_2, x_17);
return x_18;
}
case 1:
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_1);
if (x_19 == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_2);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_21 = lean_ctor_get(x_1, 0);
x_22 = lean_ctor_get(x_1, 1);
x_23 = lean_ctor_get(x_1, 2);
x_24 = lean_ctor_get(x_1, 3);
x_25 = lean_ctor_get(x_2, 0);
x_26 = lean_ctor_get(x_2, 1);
x_27 = lean_ctor_get(x_2, 2);
x_28 = lean_ctor_get(x_2, 3);
x_29 = lean_ctor_get(x_2, 4);
lean_inc(x_26);
x_30 = l_Lean_IR_LocalContext_addParams(x_26, x_22);
lean_inc_ref(x_29);
lean_inc_ref(x_28);
lean_inc(x_27);
lean_inc(x_25);
lean_ctor_set(x_2, 1, x_30);
x_31 = l_Lean_IR_ExplicitBoxing_visitFnBody(x_23, x_2, x_3);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec_ref(x_31);
lean_inc(x_32);
lean_inc_ref(x_22);
lean_inc(x_21);
x_34 = l_Lean_IR_LocalContext_addJP(x_26, x_21, x_22, x_32);
x_35 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_35, 0, x_25);
lean_ctor_set(x_35, 1, x_34);
lean_ctor_set(x_35, 2, x_27);
lean_ctor_set(x_35, 3, x_28);
lean_ctor_set(x_35, 4, x_29);
x_36 = l_Lean_IR_ExplicitBoxing_visitFnBody(x_24, x_35, x_33);
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_36, 0);
lean_ctor_set(x_1, 3, x_38);
lean_ctor_set(x_1, 2, x_32);
lean_ctor_set(x_36, 0, x_1);
return x_36;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_36, 0);
x_40 = lean_ctor_get(x_36, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_36);
lean_ctor_set(x_1, 3, x_39);
lean_ctor_set(x_1, 2, x_32);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_1);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_42 = lean_ctor_get(x_1, 0);
x_43 = lean_ctor_get(x_1, 1);
x_44 = lean_ctor_get(x_1, 2);
x_45 = lean_ctor_get(x_1, 3);
x_46 = lean_ctor_get(x_2, 0);
x_47 = lean_ctor_get(x_2, 1);
x_48 = lean_ctor_get(x_2, 2);
x_49 = lean_ctor_get(x_2, 3);
x_50 = lean_ctor_get(x_2, 4);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_2);
lean_inc(x_47);
x_51 = l_Lean_IR_LocalContext_addParams(x_47, x_43);
lean_inc_ref(x_50);
lean_inc_ref(x_49);
lean_inc(x_48);
lean_inc(x_46);
x_52 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_52, 0, x_46);
lean_ctor_set(x_52, 1, x_51);
lean_ctor_set(x_52, 2, x_48);
lean_ctor_set(x_52, 3, x_49);
lean_ctor_set(x_52, 4, x_50);
x_53 = l_Lean_IR_ExplicitBoxing_visitFnBody(x_44, x_52, x_3);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec_ref(x_53);
lean_inc(x_54);
lean_inc_ref(x_43);
lean_inc(x_42);
x_56 = l_Lean_IR_LocalContext_addJP(x_47, x_42, x_43, x_54);
x_57 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_57, 0, x_46);
lean_ctor_set(x_57, 1, x_56);
lean_ctor_set(x_57, 2, x_48);
lean_ctor_set(x_57, 3, x_49);
lean_ctor_set(x_57, 4, x_50);
x_58 = l_Lean_IR_ExplicitBoxing_visitFnBody(x_45, x_57, x_55);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_61 = x_58;
} else {
 lean_dec_ref(x_58);
 x_61 = lean_box(0);
}
lean_ctor_set(x_1, 3, x_59);
lean_ctor_set(x_1, 2, x_54);
if (lean_is_scalar(x_61)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_61;
}
lean_ctor_set(x_62, 0, x_1);
lean_ctor_set(x_62, 1, x_60);
return x_62;
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_63 = lean_ctor_get(x_1, 0);
x_64 = lean_ctor_get(x_1, 1);
x_65 = lean_ctor_get(x_1, 2);
x_66 = lean_ctor_get(x_1, 3);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_1);
x_67 = lean_ctor_get(x_2, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_2, 1);
lean_inc(x_68);
x_69 = lean_ctor_get(x_2, 2);
lean_inc(x_69);
x_70 = lean_ctor_get(x_2, 3);
lean_inc_ref(x_70);
x_71 = lean_ctor_get(x_2, 4);
lean_inc_ref(x_71);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 lean_ctor_release(x_2, 2);
 lean_ctor_release(x_2, 3);
 lean_ctor_release(x_2, 4);
 x_72 = x_2;
} else {
 lean_dec_ref(x_2);
 x_72 = lean_box(0);
}
lean_inc(x_68);
x_73 = l_Lean_IR_LocalContext_addParams(x_68, x_64);
lean_inc_ref(x_71);
lean_inc_ref(x_70);
lean_inc(x_69);
lean_inc(x_67);
if (lean_is_scalar(x_72)) {
 x_74 = lean_alloc_ctor(0, 5, 0);
} else {
 x_74 = x_72;
}
lean_ctor_set(x_74, 0, x_67);
lean_ctor_set(x_74, 1, x_73);
lean_ctor_set(x_74, 2, x_69);
lean_ctor_set(x_74, 3, x_70);
lean_ctor_set(x_74, 4, x_71);
x_75 = l_Lean_IR_ExplicitBoxing_visitFnBody(x_65, x_74, x_3);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec_ref(x_75);
lean_inc(x_76);
lean_inc_ref(x_64);
lean_inc(x_63);
x_78 = l_Lean_IR_LocalContext_addJP(x_68, x_63, x_64, x_76);
x_79 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_79, 0, x_67);
lean_ctor_set(x_79, 1, x_78);
lean_ctor_set(x_79, 2, x_69);
lean_ctor_set(x_79, 3, x_70);
lean_ctor_set(x_79, 4, x_71);
x_80 = l_Lean_IR_ExplicitBoxing_visitFnBody(x_66, x_79, x_77);
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 lean_ctor_release(x_80, 1);
 x_83 = x_80;
} else {
 lean_dec_ref(x_80);
 x_83 = lean_box(0);
}
x_84 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_84, 0, x_63);
lean_ctor_set(x_84, 1, x_64);
lean_ctor_set(x_84, 2, x_76);
lean_ctor_set(x_84, 3, x_81);
if (lean_is_scalar(x_83)) {
 x_85 = lean_alloc_ctor(0, 2, 0);
} else {
 x_85 = x_83;
}
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_82);
return x_85;
}
}
case 4:
{
uint8_t x_86; 
x_86 = !lean_is_exclusive(x_1);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; 
x_87 = lean_ctor_get(x_1, 0);
x_88 = lean_ctor_get(x_1, 1);
x_89 = lean_ctor_get(x_1, 2);
x_90 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_2);
x_91 = l_Lean_IR_ExplicitBoxing_visitFnBody(x_90, x_2, x_3);
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
lean_dec_ref(x_91);
x_94 = l_Lean_IR_ExplicitBoxing_getVarType(x_89, x_2, x_93);
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
lean_dec_ref(x_94);
x_97 = lean_box(5);
x_98 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_95, x_97);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; uint8_t x_106; 
x_99 = l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_ExplicitBoxing_M_mkFresh___redArg(x_96);
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_99, 1);
lean_inc(x_101);
lean_dec_ref(x_99);
lean_inc_ref(x_2);
x_102 = l_Lean_IR_ExplicitBoxing_mkCast(x_89, x_95, x_97, x_2, x_101);
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_102, 1);
lean_inc(x_104);
lean_dec_ref(x_102);
lean_inc(x_100);
x_105 = l_Lean_IR_ExplicitBoxing_visitFnBody___lam__0(x_87, x_88, x_92, x_100, x_2, x_104);
lean_dec_ref(x_2);
x_106 = !lean_is_exclusive(x_105);
if (x_106 == 0)
{
lean_object* x_107; 
x_107 = lean_ctor_get(x_105, 0);
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 3, x_107);
lean_ctor_set(x_1, 2, x_103);
lean_ctor_set(x_1, 1, x_97);
lean_ctor_set(x_1, 0, x_100);
lean_ctor_set(x_105, 0, x_1);
return x_105;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_108 = lean_ctor_get(x_105, 0);
x_109 = lean_ctor_get(x_105, 1);
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_105);
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 3, x_108);
lean_ctor_set(x_1, 2, x_103);
lean_ctor_set(x_1, 1, x_97);
lean_ctor_set(x_1, 0, x_100);
x_110 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_110, 0, x_1);
lean_ctor_set(x_110, 1, x_109);
return x_110;
}
}
else
{
lean_object* x_111; 
lean_dec(x_95);
lean_free_object(x_1);
x_111 = l_Lean_IR_ExplicitBoxing_visitFnBody___lam__0(x_87, x_88, x_92, x_89, x_2, x_96);
lean_dec_ref(x_2);
return x_111;
}
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; uint8_t x_123; 
x_112 = lean_ctor_get(x_1, 0);
x_113 = lean_ctor_get(x_1, 1);
x_114 = lean_ctor_get(x_1, 2);
x_115 = lean_ctor_get(x_1, 3);
lean_inc(x_115);
lean_inc(x_114);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_1);
lean_inc_ref(x_2);
x_116 = l_Lean_IR_ExplicitBoxing_visitFnBody(x_115, x_2, x_3);
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_116, 1);
lean_inc(x_118);
lean_dec_ref(x_116);
x_119 = l_Lean_IR_ExplicitBoxing_getVarType(x_114, x_2, x_118);
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_119, 1);
lean_inc(x_121);
lean_dec_ref(x_119);
x_122 = lean_box(5);
x_123 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_120, x_122);
if (x_123 == 0)
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_124 = l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_ExplicitBoxing_M_mkFresh___redArg(x_121);
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_124, 1);
lean_inc(x_126);
lean_dec_ref(x_124);
lean_inc_ref(x_2);
x_127 = l_Lean_IR_ExplicitBoxing_mkCast(x_114, x_120, x_122, x_2, x_126);
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_127, 1);
lean_inc(x_129);
lean_dec_ref(x_127);
lean_inc(x_125);
x_130 = l_Lean_IR_ExplicitBoxing_visitFnBody___lam__0(x_112, x_113, x_117, x_125, x_2, x_129);
lean_dec_ref(x_2);
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_130, 1);
lean_inc(x_132);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 x_133 = x_130;
} else {
 lean_dec_ref(x_130);
 x_133 = lean_box(0);
}
x_134 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_134, 0, x_125);
lean_ctor_set(x_134, 1, x_122);
lean_ctor_set(x_134, 2, x_128);
lean_ctor_set(x_134, 3, x_131);
if (lean_is_scalar(x_133)) {
 x_135 = lean_alloc_ctor(0, 2, 0);
} else {
 x_135 = x_133;
}
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_132);
return x_135;
}
else
{
lean_object* x_136; 
lean_dec(x_120);
x_136 = l_Lean_IR_ExplicitBoxing_visitFnBody___lam__0(x_112, x_113, x_117, x_114, x_2, x_121);
lean_dec_ref(x_2);
return x_136;
}
}
}
case 5:
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; uint8_t x_149; 
x_137 = lean_ctor_get(x_1, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_1, 1);
lean_inc(x_138);
x_139 = lean_ctor_get(x_1, 2);
lean_inc(x_139);
x_140 = lean_ctor_get(x_1, 3);
lean_inc(x_140);
x_141 = lean_ctor_get(x_1, 4);
lean_inc(x_141);
x_142 = lean_ctor_get(x_1, 5);
lean_inc(x_142);
lean_dec_ref(x_1);
lean_inc_ref(x_2);
x_143 = l_Lean_IR_ExplicitBoxing_visitFnBody(x_142, x_2, x_3);
x_144 = lean_ctor_get(x_143, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_143, 1);
lean_inc(x_145);
lean_dec_ref(x_143);
x_146 = l_Lean_IR_ExplicitBoxing_getVarType(x_140, x_2, x_145);
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_146, 1);
lean_inc(x_148);
lean_dec_ref(x_146);
x_149 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_147, x_141);
if (x_149 == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; uint8_t x_157; 
x_150 = l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_ExplicitBoxing_M_mkFresh___redArg(x_148);
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_150, 1);
lean_inc(x_152);
lean_dec_ref(x_150);
lean_inc_ref(x_2);
lean_inc(x_141);
x_153 = l_Lean_IR_ExplicitBoxing_mkCast(x_140, x_147, x_141, x_2, x_152);
x_154 = lean_ctor_get(x_153, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_153, 1);
lean_inc(x_155);
lean_dec_ref(x_153);
lean_inc(x_151);
lean_inc(x_141);
x_156 = l_Lean_IR_ExplicitBoxing_visitFnBody___lam__1(x_137, x_138, x_139, x_141, x_144, x_151, x_2, x_155);
lean_dec_ref(x_2);
x_157 = !lean_is_exclusive(x_156);
if (x_157 == 0)
{
lean_object* x_158; lean_object* x_159; 
x_158 = lean_ctor_get(x_156, 0);
x_159 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_159, 0, x_151);
lean_ctor_set(x_159, 1, x_141);
lean_ctor_set(x_159, 2, x_154);
lean_ctor_set(x_159, 3, x_158);
lean_ctor_set(x_156, 0, x_159);
return x_156;
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_160 = lean_ctor_get(x_156, 0);
x_161 = lean_ctor_get(x_156, 1);
lean_inc(x_161);
lean_inc(x_160);
lean_dec(x_156);
x_162 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_162, 0, x_151);
lean_ctor_set(x_162, 1, x_141);
lean_ctor_set(x_162, 2, x_154);
lean_ctor_set(x_162, 3, x_160);
x_163 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_163, 0, x_162);
lean_ctor_set(x_163, 1, x_161);
return x_163;
}
}
else
{
lean_object* x_164; 
lean_dec(x_147);
x_164 = l_Lean_IR_ExplicitBoxing_visitFnBody___lam__1(x_137, x_138, x_139, x_141, x_144, x_140, x_2, x_148);
lean_dec_ref(x_2);
return x_164;
}
}
case 9:
{
uint8_t x_165; 
x_165 = !lean_is_exclusive(x_1);
if (x_165 == 0)
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; size_t x_170; size_t x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; uint8_t x_178; 
x_166 = lean_ctor_get(x_1, 0);
x_167 = lean_ctor_get(x_1, 1);
x_168 = lean_ctor_get(x_1, 2);
x_169 = lean_ctor_get(x_1, 3);
x_170 = lean_array_size(x_169);
x_171 = 0;
lean_inc_ref(x_2);
x_172 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_IR_ExplicitBoxing_visitFnBody_spec__0(x_170, x_171, x_169, x_2, x_3);
x_173 = lean_ctor_get(x_172, 0);
lean_inc(x_173);
x_174 = lean_ctor_get(x_172, 1);
lean_inc(x_174);
lean_dec_ref(x_172);
x_175 = l_Lean_IR_ExplicitBoxing_getVarType(x_167, x_2, x_174);
x_176 = lean_ctor_get(x_175, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_175, 1);
lean_inc(x_177);
lean_dec_ref(x_175);
x_178 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_176, x_168);
if (x_178 == 0)
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; uint8_t x_186; 
x_179 = l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_ExplicitBoxing_M_mkFresh___redArg(x_177);
x_180 = lean_ctor_get(x_179, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_179, 1);
lean_inc(x_181);
lean_dec_ref(x_179);
lean_inc_ref(x_2);
lean_inc(x_168);
x_182 = l_Lean_IR_ExplicitBoxing_mkCast(x_167, x_176, x_168, x_2, x_181);
x_183 = lean_ctor_get(x_182, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_182, 1);
lean_inc(x_184);
lean_dec_ref(x_182);
lean_inc(x_180);
lean_inc(x_168);
x_185 = l_Lean_IR_ExplicitBoxing_visitFnBody___lam__2(x_166, x_168, x_173, x_180, x_2, x_184);
lean_dec_ref(x_2);
x_186 = !lean_is_exclusive(x_185);
if (x_186 == 0)
{
lean_object* x_187; 
x_187 = lean_ctor_get(x_185, 0);
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 3, x_187);
lean_ctor_set(x_1, 2, x_183);
lean_ctor_set(x_1, 1, x_168);
lean_ctor_set(x_1, 0, x_180);
lean_ctor_set(x_185, 0, x_1);
return x_185;
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_188 = lean_ctor_get(x_185, 0);
x_189 = lean_ctor_get(x_185, 1);
lean_inc(x_189);
lean_inc(x_188);
lean_dec(x_185);
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 3, x_188);
lean_ctor_set(x_1, 2, x_183);
lean_ctor_set(x_1, 1, x_168);
lean_ctor_set(x_1, 0, x_180);
x_190 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_190, 0, x_1);
lean_ctor_set(x_190, 1, x_189);
return x_190;
}
}
else
{
lean_object* x_191; 
lean_dec(x_176);
lean_free_object(x_1);
x_191 = l_Lean_IR_ExplicitBoxing_visitFnBody___lam__2(x_166, x_168, x_173, x_167, x_2, x_177);
lean_dec_ref(x_2);
return x_191;
}
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; size_t x_196; size_t x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; uint8_t x_204; 
x_192 = lean_ctor_get(x_1, 0);
x_193 = lean_ctor_get(x_1, 1);
x_194 = lean_ctor_get(x_1, 2);
x_195 = lean_ctor_get(x_1, 3);
lean_inc(x_195);
lean_inc(x_194);
lean_inc(x_193);
lean_inc(x_192);
lean_dec(x_1);
x_196 = lean_array_size(x_195);
x_197 = 0;
lean_inc_ref(x_2);
x_198 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_IR_ExplicitBoxing_visitFnBody_spec__0(x_196, x_197, x_195, x_2, x_3);
x_199 = lean_ctor_get(x_198, 0);
lean_inc(x_199);
x_200 = lean_ctor_get(x_198, 1);
lean_inc(x_200);
lean_dec_ref(x_198);
x_201 = l_Lean_IR_ExplicitBoxing_getVarType(x_193, x_2, x_200);
x_202 = lean_ctor_get(x_201, 0);
lean_inc(x_202);
x_203 = lean_ctor_get(x_201, 1);
lean_inc(x_203);
lean_dec_ref(x_201);
x_204 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_202, x_194);
if (x_204 == 0)
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
x_205 = l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_ExplicitBoxing_M_mkFresh___redArg(x_203);
x_206 = lean_ctor_get(x_205, 0);
lean_inc(x_206);
x_207 = lean_ctor_get(x_205, 1);
lean_inc(x_207);
lean_dec_ref(x_205);
lean_inc_ref(x_2);
lean_inc(x_194);
x_208 = l_Lean_IR_ExplicitBoxing_mkCast(x_193, x_202, x_194, x_2, x_207);
x_209 = lean_ctor_get(x_208, 0);
lean_inc(x_209);
x_210 = lean_ctor_get(x_208, 1);
lean_inc(x_210);
lean_dec_ref(x_208);
lean_inc(x_206);
lean_inc(x_194);
x_211 = l_Lean_IR_ExplicitBoxing_visitFnBody___lam__2(x_192, x_194, x_199, x_206, x_2, x_210);
lean_dec_ref(x_2);
x_212 = lean_ctor_get(x_211, 0);
lean_inc(x_212);
x_213 = lean_ctor_get(x_211, 1);
lean_inc(x_213);
if (lean_is_exclusive(x_211)) {
 lean_ctor_release(x_211, 0);
 lean_ctor_release(x_211, 1);
 x_214 = x_211;
} else {
 lean_dec_ref(x_211);
 x_214 = lean_box(0);
}
x_215 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_215, 0, x_206);
lean_ctor_set(x_215, 1, x_194);
lean_ctor_set(x_215, 2, x_209);
lean_ctor_set(x_215, 3, x_212);
if (lean_is_scalar(x_214)) {
 x_216 = lean_alloc_ctor(0, 2, 0);
} else {
 x_216 = x_214;
}
lean_ctor_set(x_216, 0, x_215);
lean_ctor_set(x_216, 1, x_213);
return x_216;
}
else
{
lean_object* x_217; 
lean_dec(x_202);
x_217 = l_Lean_IR_ExplicitBoxing_visitFnBody___lam__2(x_192, x_194, x_199, x_193, x_2, x_203);
lean_dec_ref(x_2);
return x_217;
}
}
}
case 10:
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; 
x_218 = lean_ctor_get(x_1, 0);
lean_inc(x_218);
lean_dec_ref(x_1);
x_219 = l_Lean_IR_ExplicitBoxing_getResultType(x_2, x_3);
x_220 = lean_ctor_get(x_219, 0);
lean_inc(x_220);
x_221 = lean_ctor_get(x_219, 1);
lean_inc(x_221);
lean_dec_ref(x_219);
x_222 = lean_alloc_closure((void*)(l_Lean_IR_ExplicitBoxing_visitFnBody___lam__3___boxed), 3, 0);
if (lean_obj_tag(x_218) == 0)
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; uint8_t x_227; 
x_223 = lean_ctor_get(x_218, 0);
lean_inc(x_223);
lean_dec_ref(x_218);
x_224 = l_Lean_IR_ExplicitBoxing_getVarType(x_223, x_2, x_221);
x_225 = lean_ctor_get(x_224, 0);
lean_inc(x_225);
x_226 = lean_ctor_get(x_224, 1);
lean_inc(x_226);
lean_dec_ref(x_224);
x_227 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_225, x_220);
if (x_227 == 0)
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; uint8_t x_235; 
x_228 = l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_ExplicitBoxing_M_mkFresh___redArg(x_226);
x_229 = lean_ctor_get(x_228, 0);
lean_inc(x_229);
x_230 = lean_ctor_get(x_228, 1);
lean_inc(x_230);
lean_dec_ref(x_228);
lean_inc_ref(x_2);
lean_inc(x_220);
x_231 = l_Lean_IR_ExplicitBoxing_mkCast(x_223, x_225, x_220, x_2, x_230);
x_232 = lean_ctor_get(x_231, 0);
lean_inc(x_232);
x_233 = lean_ctor_get(x_231, 1);
lean_inc(x_233);
lean_dec_ref(x_231);
lean_inc(x_229);
x_234 = l_Lean_IR_ExplicitBoxing_visitFnBody___lam__4(x_222, x_229, x_2, x_233);
x_235 = !lean_is_exclusive(x_234);
if (x_235 == 0)
{
lean_object* x_236; lean_object* x_237; 
x_236 = lean_ctor_get(x_234, 0);
x_237 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_237, 0, x_229);
lean_ctor_set(x_237, 1, x_220);
lean_ctor_set(x_237, 2, x_232);
lean_ctor_set(x_237, 3, x_236);
lean_ctor_set(x_234, 0, x_237);
return x_234;
}
else
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; 
x_238 = lean_ctor_get(x_234, 0);
x_239 = lean_ctor_get(x_234, 1);
lean_inc(x_239);
lean_inc(x_238);
lean_dec(x_234);
x_240 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_240, 0, x_229);
lean_ctor_set(x_240, 1, x_220);
lean_ctor_set(x_240, 2, x_232);
lean_ctor_set(x_240, 3, x_238);
x_241 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_241, 0, x_240);
lean_ctor_set(x_241, 1, x_239);
return x_241;
}
}
else
{
lean_object* x_242; 
lean_dec(x_225);
lean_dec(x_220);
x_242 = l_Lean_IR_ExplicitBoxing_visitFnBody___lam__4(x_222, x_223, x_2, x_226);
return x_242;
}
}
else
{
lean_object* x_243; 
lean_dec_ref(x_222);
lean_dec(x_220);
x_243 = l_Lean_IR_ExplicitBoxing_visitFnBody___lam__3(x_218, x_2, x_221);
lean_dec_ref(x_2);
return x_243;
}
}
case 11:
{
uint8_t x_244; 
x_244 = !lean_is_exclusive(x_1);
if (x_244 == 0)
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; uint8_t x_255; 
x_245 = lean_ctor_get(x_1, 0);
x_246 = lean_ctor_get(x_1, 1);
x_247 = l_Lean_IR_ExplicitBoxing_getJPParams(x_245, x_2, x_3);
x_248 = lean_ctor_get(x_247, 0);
lean_inc(x_248);
x_249 = lean_ctor_get(x_247, 1);
lean_inc(x_249);
lean_dec_ref(x_247);
x_250 = l_Lean_IR_instInhabitedParam;
x_251 = lean_alloc_closure((void*)(l_Lean_IR_ExplicitBoxing_visitFnBody___lam__5___boxed), 3, 2);
lean_closure_set(x_251, 0, x_250);
lean_closure_set(x_251, 1, x_248);
x_252 = l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux(x_246, x_251, x_2, x_249);
lean_dec_ref(x_246);
x_253 = lean_ctor_get(x_252, 0);
lean_inc(x_253);
x_254 = lean_ctor_get(x_252, 1);
lean_inc(x_254);
lean_dec_ref(x_252);
x_255 = !lean_is_exclusive(x_253);
if (x_255 == 0)
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; 
x_256 = lean_ctor_get(x_253, 0);
x_257 = lean_ctor_get(x_253, 1);
lean_ctor_set(x_1, 1, x_256);
x_258 = l_Lean_IR_reshape(x_257, x_1);
lean_ctor_set(x_253, 1, x_254);
lean_ctor_set(x_253, 0, x_258);
return x_253;
}
else
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; 
x_259 = lean_ctor_get(x_253, 0);
x_260 = lean_ctor_get(x_253, 1);
lean_inc(x_260);
lean_inc(x_259);
lean_dec(x_253);
lean_ctor_set(x_1, 1, x_259);
x_261 = l_Lean_IR_reshape(x_260, x_1);
x_262 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_262, 0, x_261);
lean_ctor_set(x_262, 1, x_254);
return x_262;
}
}
else
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; 
x_263 = lean_ctor_get(x_1, 0);
x_264 = lean_ctor_get(x_1, 1);
lean_inc(x_264);
lean_inc(x_263);
lean_dec(x_1);
x_265 = l_Lean_IR_ExplicitBoxing_getJPParams(x_263, x_2, x_3);
x_266 = lean_ctor_get(x_265, 0);
lean_inc(x_266);
x_267 = lean_ctor_get(x_265, 1);
lean_inc(x_267);
lean_dec_ref(x_265);
x_268 = l_Lean_IR_instInhabitedParam;
x_269 = lean_alloc_closure((void*)(l_Lean_IR_ExplicitBoxing_visitFnBody___lam__5___boxed), 3, 2);
lean_closure_set(x_269, 0, x_268);
lean_closure_set(x_269, 1, x_266);
x_270 = l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux(x_264, x_269, x_2, x_267);
lean_dec_ref(x_264);
x_271 = lean_ctor_get(x_270, 0);
lean_inc(x_271);
x_272 = lean_ctor_get(x_270, 1);
lean_inc(x_272);
lean_dec_ref(x_270);
x_273 = lean_ctor_get(x_271, 0);
lean_inc(x_273);
x_274 = lean_ctor_get(x_271, 1);
lean_inc(x_274);
if (lean_is_exclusive(x_271)) {
 lean_ctor_release(x_271, 0);
 lean_ctor_release(x_271, 1);
 x_275 = x_271;
} else {
 lean_dec_ref(x_271);
 x_275 = lean_box(0);
}
x_276 = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(x_276, 0, x_263);
lean_ctor_set(x_276, 1, x_273);
x_277 = l_Lean_IR_reshape(x_274, x_276);
if (lean_is_scalar(x_275)) {
 x_278 = lean_alloc_ctor(0, 2, 0);
} else {
 x_278 = x_275;
}
lean_ctor_set(x_278, 0, x_277);
lean_ctor_set(x_278, 1, x_272);
return x_278;
}
}
default: 
{
lean_object* x_279; 
lean_dec_ref(x_2);
x_279 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_279, 0, x_1);
lean_ctor_set(x_279, 1, x_3);
return x_279;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_IR_ExplicitBoxing_visitFnBody_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_IR_ExplicitBoxing_visitFnBody_spec__0(x_6, x_7, x_3, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_visitFnBody___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_IR_ExplicitBoxing_visitFnBody___lam__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_visitFnBody___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_IR_ExplicitBoxing_visitFnBody___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_visitFnBody___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_IR_ExplicitBoxing_visitFnBody___lam__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_visitFnBody___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_ExplicitBoxing_visitFnBody___lam__3(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_visitFnBody___lam__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_ExplicitBoxing_visitFnBody___lam__5(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_IR_ExplicitBoxing_run_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_12; 
x_12 = lean_usize_dec_eq(x_4, x_5);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_array_uget(x_3, x_4);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc_ref(x_15);
x_16 = lean_ctor_get(x_13, 2);
lean_inc(x_16);
x_17 = lean_ctor_get(x_13, 3);
lean_inc(x_17);
lean_inc_ref(x_13);
x_18 = l_Lean_IR_Decl_maxIndex(x_13);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_18, x_19);
lean_dec(x_18);
x_21 = lean_box(1);
x_22 = l_Lean_IR_ExplicitBoxing_addBoxedVersions___closed__0;
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_24, 0, x_20);
lean_ctor_set(x_24, 1, x_22);
lean_ctor_set(x_24, 2, x_23);
lean_ctor_set(x_24, 3, x_19);
x_25 = l_Lean_IR_LocalContext_addParams(x_21, x_15);
lean_dec_ref(x_15);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_26 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_26, 0, x_14);
lean_ctor_set(x_26, 1, x_25);
lean_ctor_set(x_26, 2, x_16);
lean_ctor_set(x_26, 3, x_1);
lean_ctor_set(x_26, 4, x_2);
x_27 = l_Lean_IR_ExplicitBoxing_visitFnBody(x_17, x_26, x_24);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 0);
lean_inc(x_29);
lean_dec_ref(x_27);
x_30 = lean_ctor_get(x_28, 1);
lean_inc_ref(x_30);
lean_dec(x_28);
x_31 = l_Array_append___redArg(x_6, x_30);
lean_dec_ref(x_30);
x_32 = l_Lean_IR_Decl_updateBody_x21(x_13, x_29);
x_33 = l_Lean_IR_Decl_elimDead(x_32);
x_34 = lean_array_push(x_31, x_33);
x_7 = x_34;
goto block_11;
}
else
{
lean_object* x_35; 
x_35 = lean_array_push(x_6, x_13);
x_7 = x_35;
goto block_11;
}
}
else
{
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_6;
}
block_11:
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = lean_usize_add(x_4, x_8);
x_4 = x_9;
x_6 = x_7;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_run(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Lean_IR_ExplicitBoxing_addBoxedVersions___closed__0;
x_5 = lean_array_get_size(x_2);
x_6 = lean_nat_dec_lt(x_3, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_5);
lean_dec_ref(x_2);
x_7 = l_Lean_IR_ExplicitBoxing_addBoxedVersions(x_1, x_4);
return x_7;
}
else
{
uint8_t x_8; 
x_8 = lean_nat_dec_le(x_5, x_5);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_5);
lean_dec_ref(x_2);
x_9 = l_Lean_IR_ExplicitBoxing_addBoxedVersions(x_1, x_4);
return x_9;
}
else
{
size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; 
x_10 = 0;
x_11 = lean_usize_of_nat(x_5);
lean_dec(x_5);
lean_inc_ref(x_1);
lean_inc_ref(x_2);
x_12 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_IR_ExplicitBoxing_run_spec__0(x_2, x_1, x_2, x_10, x_11, x_4);
lean_dec_ref(x_2);
x_13 = l_Lean_IR_ExplicitBoxing_addBoxedVersions(x_1, x_12);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_IR_ExplicitBoxing_run_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_IR_ExplicitBoxing_run_spec__0(x_1, x_2, x_3, x_7, x_8, x_6);
lean_dec_ref(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_explicitBoxing___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_st_ref_get(x_2, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_7);
lean_dec(x_6);
x_8 = l_Lean_IR_ExplicitBoxing_run(x_7, x_1);
lean_ctor_set(x_4, 0, x_8);
return x_4;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_4, 0);
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_4);
x_11 = lean_ctor_get(x_9, 0);
lean_inc_ref(x_11);
lean_dec(x_9);
x_12 = l_Lean_IR_ExplicitBoxing_run(x_11, x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_explicitBoxing(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_explicitBoxing___redArg(x_1, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_explicitBoxing___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_explicitBoxing___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_explicitBoxing___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_explicitBoxing(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__0____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("compiler", 8, 8);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__1____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ir", 2, 2);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__2____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("boxing", 6, 6);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__3____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__2____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_;
x_2 = l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__1____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_;
x_3 = l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__0____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__4____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_private", 8, 8);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__5____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__4____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_;
x_2 = lean_box(0);
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__6____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__7____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__6____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_;
x_2 = l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__5____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__8____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Compiler", 8, 8);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__9____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__8____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_;
x_2 = l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__7____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__10____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("IR", 2, 2);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__11____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__10____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_;
x_2 = l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__9____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__12____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Boxing", 6, 6);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__13____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__12____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_;
x_2 = l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__11____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__14____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__13____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__15____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__6____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_;
x_2 = l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__14____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__16____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__10____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_;
x_2 = l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__15____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__17____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("initFn", 6, 6);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__18____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__17____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_;
x_2 = l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__16____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__19____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_@", 2, 2);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__20____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__19____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_;
x_2 = l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__18____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__21____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__6____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_;
x_2 = l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__20____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__22____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__8____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_;
x_2 = l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__21____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__23____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__10____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_;
x_2 = l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__22____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__24____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__12____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_;
x_2 = l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__23____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__25____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(3293845429u);
x_2 = l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__24____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__26____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_hygCtx", 7, 7);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__27____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__26____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_;
x_2 = l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__25____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__28____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_hyg", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__29____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__28____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_;
x_2 = l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__27____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__30____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__29____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__3____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_;
x_3 = 1;
x_4 = l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__30____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* initialize_Lean_Runtime(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_ClosedTermCache(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_ExternAttr(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_IR_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_IR_CompilerM(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_IR_FreeVars(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_IR_ElimDeadVars(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_IR_ToIRType(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_AssocList(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_IR_Boxing(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Runtime(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_ClosedTermCache(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_ExternAttr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_CompilerM(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_FreeVars(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_ElimDeadVars(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_ToIRType(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_AssocList(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_IR_ExplicitBoxing_mkBoxedName___closed__0 = _init_l_Lean_IR_ExplicitBoxing_mkBoxedName___closed__0();
lean_mark_persistent(l_Lean_IR_ExplicitBoxing_mkBoxedName___closed__0);
l_Lean_IR_ExplicitBoxing_requiresBoxedVersion___closed__0 = _init_l_Lean_IR_ExplicitBoxing_requiresBoxedVersion___closed__0();
lean_mark_persistent(l_Lean_IR_ExplicitBoxing_requiresBoxedVersion___closed__0);
l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___Lean_IR_ExplicitBoxing_mkBoxedVersionAux_spec__1___redArg___closed__0 = _init_l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___Lean_IR_ExplicitBoxing_mkBoxedVersionAux_spec__1___redArg___closed__0();
lean_mark_persistent(l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___Lean_IR_ExplicitBoxing_mkBoxedVersionAux_spec__1___redArg___closed__0);
l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___Lean_IR_ExplicitBoxing_mkBoxedVersionAux_spec__1___redArg___closed__1 = _init_l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___Lean_IR_ExplicitBoxing_mkBoxedVersionAux_spec__1___redArg___closed__1();
lean_mark_persistent(l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___Lean_IR_ExplicitBoxing_mkBoxedVersionAux_spec__1___redArg___closed__1);
l_Lean_IR_ExplicitBoxing_mkBoxedVersionAux___closed__0 = _init_l_Lean_IR_ExplicitBoxing_mkBoxedVersionAux___closed__0();
lean_mark_persistent(l_Lean_IR_ExplicitBoxing_mkBoxedVersionAux___closed__0);
l_Lean_IR_ExplicitBoxing_mkBoxedVersionAux___closed__1 = _init_l_Lean_IR_ExplicitBoxing_mkBoxedVersionAux___closed__1();
lean_mark_persistent(l_Lean_IR_ExplicitBoxing_mkBoxedVersionAux___closed__1);
l_Lean_IR_ExplicitBoxing_addBoxedVersions___closed__0 = _init_l_Lean_IR_ExplicitBoxing_addBoxedVersions___closed__0();
lean_mark_persistent(l_Lean_IR_ExplicitBoxing_addBoxedVersions___closed__0);
l_Lean_IR_ExplicitBoxing_getJPParams___closed__0 = _init_l_Lean_IR_ExplicitBoxing_getJPParams___closed__0();
lean_mark_persistent(l_Lean_IR_ExplicitBoxing_getJPParams___closed__0);
l_Lean_IR_ExplicitBoxing_getDecl___closed__0 = _init_l_Lean_IR_ExplicitBoxing_getDecl___closed__0();
lean_mark_persistent(l_Lean_IR_ExplicitBoxing_getDecl___closed__0);
l_Lean_IR_ExplicitBoxing_getDecl___closed__1 = _init_l_Lean_IR_ExplicitBoxing_getDecl___closed__1();
lean_mark_persistent(l_Lean_IR_ExplicitBoxing_getDecl___closed__1);
l_Lean_IR_ExplicitBoxing_mkCast___closed__0 = _init_l_Lean_IR_ExplicitBoxing_mkCast___closed__0();
lean_mark_persistent(l_Lean_IR_ExplicitBoxing_mkCast___closed__0);
l_Lean_IR_ExplicitBoxing_mkCast___closed__1 = _init_l_Lean_IR_ExplicitBoxing_mkCast___closed__1();
lean_mark_persistent(l_Lean_IR_ExplicitBoxing_mkCast___closed__1);
l_Lean_IR_ExplicitBoxing_mkCast___closed__2 = _init_l_Lean_IR_ExplicitBoxing_mkCast___closed__2();
lean_mark_persistent(l_Lean_IR_ExplicitBoxing_mkCast___closed__2);
l_Lean_IR_ExplicitBoxing_mkCast___closed__3 = _init_l_Lean_IR_ExplicitBoxing_mkCast___closed__3();
lean_mark_persistent(l_Lean_IR_ExplicitBoxing_mkCast___closed__3);
l_Lean_IR_ExplicitBoxing_mkCast___closed__4 = _init_l_Lean_IR_ExplicitBoxing_mkCast___closed__4();
lean_mark_persistent(l_Lean_IR_ExplicitBoxing_mkCast___closed__4);
l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___closed__0 = _init_l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___closed__0();
lean_mark_persistent(l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___closed__0);
l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___closed__1 = _init_l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___closed__1();
lean_mark_persistent(l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___closed__1);
l_Lean_IR_ExplicitBoxing_visitVDeclExpr___closed__0 = _init_l_Lean_IR_ExplicitBoxing_visitVDeclExpr___closed__0();
lean_mark_persistent(l_Lean_IR_ExplicitBoxing_visitVDeclExpr___closed__0);
l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__0____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_ = _init_l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__0____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__0____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_);
l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__1____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_ = _init_l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__1____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__1____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_);
l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__2____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_ = _init_l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__2____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__2____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_);
l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__3____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_ = _init_l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__3____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__3____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_);
l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__4____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_ = _init_l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__4____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__4____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_);
l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__5____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_ = _init_l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__5____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__5____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_);
l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__6____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_ = _init_l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__6____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__6____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_);
l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__7____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_ = _init_l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__7____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__7____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_);
l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__8____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_ = _init_l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__8____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__8____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_);
l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__9____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_ = _init_l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__9____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__9____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_);
l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__10____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_ = _init_l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__10____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__10____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_);
l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__11____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_ = _init_l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__11____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__11____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_);
l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__12____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_ = _init_l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__12____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__12____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_);
l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__13____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_ = _init_l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__13____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__13____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_);
l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__14____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_ = _init_l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__14____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__14____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_);
l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__15____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_ = _init_l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__15____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__15____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_);
l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__16____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_ = _init_l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__16____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__16____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_);
l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__17____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_ = _init_l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__17____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__17____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_);
l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__18____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_ = _init_l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__18____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__18____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_);
l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__19____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_ = _init_l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__19____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__19____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_);
l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__20____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_ = _init_l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__20____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__20____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_);
l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__21____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_ = _init_l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__21____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__21____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_);
l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__22____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_ = _init_l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__22____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__22____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_);
l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__23____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_ = _init_l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__23____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__23____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_);
l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__24____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_ = _init_l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__24____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__24____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_);
l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__25____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_ = _init_l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__25____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__25____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_);
l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__26____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_ = _init_l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__26____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__26____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_);
l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__27____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_ = _init_l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__27____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__27____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_);
l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__28____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_ = _init_l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__28____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__28____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_);
l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__29____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_ = _init_l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__29____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__29____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_);
l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__30____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_ = _init_l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__30____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn___closed__30____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_);
if (builtin) {res = l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_initFn____x40_Lean_Compiler_IR_Boxing_3293845429____hygCtx___hyg_2_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
