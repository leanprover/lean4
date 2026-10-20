// Lean compiler output
// Module: Lean.Compiler.LCNF.InferType
// Imports: public import Lean.Compiler.LCNF.PhaseExt public import Lean.Compiler.LCNF.OtherDecl import Init.Omega
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
lean_object* lean_local_ctx_find(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getBinderName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_userName(lean_object*);
lean_object* lean_expr_instantiate_rev(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
lean_object* l_Lean_LocalContext_mkLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Lean_Level_succ___override(lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getPhase___redArg(lean_object*);
lean_object* l_Lean_Compiler_LCNF_getDeclAt_x3f(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_instantiateTypeLevelParams___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getOtherDeclType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Compiler_LCNF_erasedExpr;
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Expr_headBeta(lean_object*);
lean_object* lean_expr_instantiate_rev_range(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Compiler_LCNF_anyExpr;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Array_reverse___redArg(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_mkLevelIMax_x27(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Level_normalize(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO___redArg();
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_instInhabitedForall___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* lean_expr_abstract(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* lean_expr_abstract_range(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* l_Lean_mkProj(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Compiler_LCNF_getPurity___redArg(lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_toLocalContext(lean_object*, uint8_t);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
uint8_t l_Lean_Expr_isErased(lean_object*);
uint8_t l_Lean_Expr_isAny(lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Subarray_copy___redArg(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instantiateRevRangeArgs___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkLetDecl(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
uint8_t l_Lean_Level_isEquiv(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
extern lean_object* l_Lean_Core_instMonadNameGeneratorCoreM;
lean_object* l_StateRefT_x27_lift___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_monadNameGeneratorLift___redArg(lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadLift___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFreshFVarId___redArg(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkFunDecl(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instInhabitedAlt_default__1___redArg();
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_joinTypes(lean_object*, lean_object*);
uint8_t l_Lean_Compiler_LCNF_isPredicateType(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_getBinderName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_getBinderName___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_getType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Compiler_LCNF_InferType_Pure_mkForallFVars_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Compiler_LCNF_InferType_Pure_mkForallFVars_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_mkForallFVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_mkForallFVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Compiler_LCNF_InferType_Pure_mkForallFVars_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Compiler_LCNF_InferType_Pure_mkForallFVars_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_InferType_Pure_mkForallParams_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_InferType_Pure_mkForallParams_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__0;
static lean_once_cell_t l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__1;
static lean_once_cell_t l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__2;
static lean_once_cell_t l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__3;
static lean_once_cell_t l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__0;
static lean_once_cell_t l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__1;
static const lean_closure_object l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__2_value;
static const lean_closure_object l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__3 = (const lean_object*)&l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__3_value;
static const lean_closure_object l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__4 = (const lean_object*)&l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__4_value;
static const lean_closure_object l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__5 = (const lean_object*)&l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__5_value;
static const lean_closure_object l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instMonadLift___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__6 = (const lean_object*)&l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__6_value;
static const lean_closure_object l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateRefT_x27_lift___boxed, .m_arity = 6, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__7 = (const lean_object*)&l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__7_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__8;
static lean_once_cell_t l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__9;
static lean_once_cell_t l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__10;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_InferType_Pure_inferConstType___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "lcErased"};
static const lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferConstType___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_InferType_Pure_inferConstType___closed__0_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_InferType_Pure_inferConstType___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_InferType_Pure_inferConstType___closed__0_value),LEAN_SCALAR_PTR_LITERAL(171, 218, 234, 194, 194, 57, 75, 5)}};
static const lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferConstType___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_InferType_Pure_inferConstType___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferConstType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferConstType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Nat"};
static const lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__0_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__1_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__2;
static const lean_string_object l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "String"};
static const lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__3 = (const lean_object*)&l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__3_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__3_value),LEAN_SCALAR_PTR_LITERAL(6, 130, 56, 8, 41, 104, 134, 43)}};
static const lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__4 = (const lean_object*)&l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__4_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__5;
static const lean_string_object l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "UInt8"};
static const lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__6 = (const lean_object*)&l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__6_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__6_value),LEAN_SCALAR_PTR_LITERAL(144, 254, 64, 72, 7, 99, 197, 218)}};
static const lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__7 = (const lean_object*)&l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__7_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__8;
static const lean_string_object l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UInt16"};
static const lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__9 = (const lean_object*)&l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__9_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__9_value),LEAN_SCALAR_PTR_LITERAL(6, 214, 154, 233, 192, 74, 99, 135)}};
static const lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__10 = (const lean_object*)&l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__10_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__11;
static const lean_string_object l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UInt32"};
static const lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__12 = (const lean_object*)&l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__12_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__12_value),LEAN_SCALAR_PTR_LITERAL(98, 192, 58, 241, 186, 14, 255, 186)}};
static const lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__13 = (const lean_object*)&l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__13_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__14;
static const lean_string_object l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UInt64"};
static const lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__15 = (const lean_object*)&l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__15_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__15_value),LEAN_SCALAR_PTR_LITERAL(58, 113, 45, 150, 103, 228, 0, 41)}};
static const lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__16 = (const lean_object*)&l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__16_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__17;
static const lean_string_object l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "USize"};
static const lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__18 = (const lean_object*)&l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__18_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__18_value),LEAN_SCALAR_PTR_LITERAL(109, 217, 26, 131, 232, 198, 207, 245)}};
static const lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__19 = (const lean_object*)&l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__19_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__20;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferLambdaType_go_spec__0_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferLambdaType_go_spec__0_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferLambdaType_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferLambdaType_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_InferType_Pure_inferType_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_InferType_Pure_inferType_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppType_spec__9___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppType_spec__9___redArg___closed__0;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppType_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppType_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Compiler_LCNF_InferType_Pure_inferForallType___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferForallType___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_InferType_Pure_inferForallType___closed__0_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_InferType_Pure_inferAppType___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferAppType___closed__0;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferAppType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferLambdaType_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferLambdaType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_InferType_Pure_inferType___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferType___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_InferType_Pure_inferType___closed__2_value;
static const lean_string_object l_Lean_Compiler_LCNF_InferType_Pure_inferType___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "Lean.Compiler.LCNF.InferType.Pure.inferType"};
static const lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferType___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_InferType_Pure_inferType___closed__1_value;
static const lean_string_object l_Lean_Compiler_LCNF_InferType_Pure_inferType___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Lean.Compiler.LCNF.InferType"};
static const lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferType___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_InferType_Pure_inferType___closed__0_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_InferType_Pure_inferType___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferType___closed__3;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_getLevel_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferForallType_go_spec__6___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferForallType_go_spec__6___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferForallType_go_spec__6(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferForallType_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferForallType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferForallType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferLambdaType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_getLevel_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferForallType_go_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferAppType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferLambdaType_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferForallType_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferLambdaType_go_spec__0_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferLambdaType_go_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppType_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppType_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferArgType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferArgType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppTypeCore_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppTypeCore_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferAppTypeCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferAppTypeCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppTypeCore_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppTypeCore_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___closed__0;
static lean_once_cell_t l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "invalid projection"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3___redArg___closed__0_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3___redArg___closed__1;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__0;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__1 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__1_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__2;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__3 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__3_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__4;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__5 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__5_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__6;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__7 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__7_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__8;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__9 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__9_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__10;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__11 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__11_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__12;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__13 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__13_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__14;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg___closed__1;
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg___closed__2 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferProjType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferProjType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferLetValueType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferLetValueType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inferType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inferType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_inferAppType_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_inferAppType_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_inferAppType___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "Lean.Compiler.LCNF.inferAppType"};
static const lean_object* l_Lean_Compiler_LCNF_inferAppType___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_inferAppType___closed__0_value;
static const lean_string_object l_Lean_Compiler_LCNF_inferAppType___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "Infer type for impure unimplemented"};
static const lean_object* l_Lean_Compiler_LCNF_inferAppType___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_inferAppType___closed__1_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_inferAppType___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_inferAppType___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inferAppType(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inferAppType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_Arg_inferType___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "Lean.Compiler.LCNF.Arg.inferType"};
static const lean_object* l_Lean_Compiler_LCNF_Arg_inferType___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_Arg_inferType___closed__0_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_Arg_inferType___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Arg_inferType___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_inferType(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_inferType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_LetValue_inferType___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "Lean.Compiler.LCNF.LetValue.inferType"};
static const lean_object* l_Lean_Compiler_LCNF_LetValue_inferType___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_LetValue_inferType___closed__0_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_LetValue_inferType___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_LetValue_inferType___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_inferType(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_inferType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_Code_inferType___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "Lean.Compiler.LCNF.Code.inferType"};
static const lean_object* l_Lean_Compiler_LCNF_Code_inferType___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_Code_inferType___closed__0_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_Code_inferType___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Code_inferType___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_inferType(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_inferType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_Code_inferType_match__3_splitter___redArg(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_Code_inferType_match__3_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_Code_inferType_match__3_splitter(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_Code_inferType_match__3_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_Code_inferType_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_Code_inferType_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_inferParamType(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_inferParamType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_inferType(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_inferType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkAuxLetDecl(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkAuxLetDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_mkForallParams___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "Lean.Compiler.LCNF.mkForallParams"};
static const lean_object* l_Lean_Compiler_LCNF_mkForallParams___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_mkForallParams___closed__0_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_mkForallParams___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_mkForallParams___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkForallParams(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkForallParams___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_mkAuxFunDeclAux(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_mkAuxFunDeclAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkAuxFunDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkAuxFunDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkAuxJpDecl(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkAuxJpDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkAuxJpDecl_x27(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkAuxJpDecl_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__0___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Compiler_LCNF_mkCasesResultType___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_mkCasesResultType___closed__0;
static const lean_string_object l_Lean_Compiler_LCNF_mkCasesResultType___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "`Code.bind` failed, empty `cases` found"};
static const lean_object* l_Lean_Compiler_LCNF_mkCasesResultType___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_mkCasesResultType___closed__1_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_mkCasesResultType___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_mkCasesResultType___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkCasesResultType(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkCasesResultType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_isErasedCompatible_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_isErasedCompatible_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_isErasedCompatible_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 81, .m_capacity = 81, .m_length = 80, .m_data = "_private.Lean.Compiler.LCNF.InferType.0.Lean.Compiler.LCNF.isErasedCompatible.go"};
static const lean_object* l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_isErasedCompatible_go___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_isErasedCompatible_go___closed__0_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_isErasedCompatible_go___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_isErasedCompatible_go___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_isErasedCompatible_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_isErasedCompatible_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isErasedCompatible(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isErasedCompatible___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_isEqv___at___00Lean_Compiler_LCNF_eqvTypes_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_isEqv___at___00Lean_Compiler_LCNF_eqvTypes_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_eqvTypes(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eqvTypes___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_getBinderName(lean_object* v_fvarId_1_, lean_object* v_a_2_, lean_object* v_a_3_, lean_object* v_a_4_, lean_object* v_a_5_, lean_object* v_a_6_){
_start:
{
lean_object* v___x_8_; 
lean_inc(v_fvarId_1_);
lean_inc_ref(v_a_2_);
v___x_8_ = lean_local_ctx_find(v_a_2_, v_fvarId_1_);
if (lean_obj_tag(v___x_8_) == 0)
{
lean_object* v___x_9_; 
v___x_9_ = l_Lean_Compiler_LCNF_getBinderName(v_fvarId_1_, v_a_3_, v_a_4_, v_a_5_, v_a_6_);
return v___x_9_;
}
else
{
lean_object* v_val_10_; lean_object* v___x_12_; uint8_t v_isShared_13_; uint8_t v_isSharedCheck_18_; 
lean_dec(v_fvarId_1_);
v_val_10_ = lean_ctor_get(v___x_8_, 0);
v_isSharedCheck_18_ = !lean_is_exclusive(v___x_8_);
if (v_isSharedCheck_18_ == 0)
{
v___x_12_ = v___x_8_;
v_isShared_13_ = v_isSharedCheck_18_;
goto v_resetjp_11_;
}
else
{
lean_inc(v_val_10_);
lean_dec(v___x_8_);
v___x_12_ = lean_box(0);
v_isShared_13_ = v_isSharedCheck_18_;
goto v_resetjp_11_;
}
v_resetjp_11_:
{
lean_object* v___x_14_; lean_object* v___x_16_; 
v___x_14_ = l_Lean_LocalDecl_userName(v_val_10_);
lean_dec(v_val_10_);
if (v_isShared_13_ == 0)
{
lean_ctor_set_tag(v___x_12_, 0);
lean_ctor_set(v___x_12_, 0, v___x_14_);
v___x_16_ = v___x_12_;
goto v_reusejp_15_;
}
else
{
lean_object* v_reuseFailAlloc_17_; 
v_reuseFailAlloc_17_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_17_, 0, v___x_14_);
v___x_16_ = v_reuseFailAlloc_17_;
goto v_reusejp_15_;
}
v_reusejp_15_:
{
return v___x_16_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_getBinderName___boxed(lean_object* v_fvarId_19_, lean_object* v_a_20_, lean_object* v_a_21_, lean_object* v_a_22_, lean_object* v_a_23_, lean_object* v_a_24_, lean_object* v_a_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l_Lean_Compiler_LCNF_InferType_Pure_getBinderName(v_fvarId_19_, v_a_20_, v_a_21_, v_a_22_, v_a_23_, v_a_24_);
lean_dec(v_a_24_);
lean_dec_ref(v_a_23_);
lean_dec(v_a_22_);
lean_dec_ref(v_a_21_);
lean_dec_ref(v_a_20_);
return v_res_26_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_getType(lean_object* v_fvarId_27_, lean_object* v_a_28_, lean_object* v_a_29_, lean_object* v_a_30_, lean_object* v_a_31_, lean_object* v_a_32_){
_start:
{
lean_object* v___x_34_; 
lean_inc(v_fvarId_27_);
lean_inc_ref(v_a_28_);
v___x_34_ = lean_local_ctx_find(v_a_28_, v_fvarId_27_);
if (lean_obj_tag(v___x_34_) == 0)
{
lean_object* v___x_35_; 
v___x_35_ = l_Lean_Compiler_LCNF_getType(v_fvarId_27_, v_a_29_, v_a_30_, v_a_31_, v_a_32_);
return v___x_35_;
}
else
{
lean_object* v_val_36_; lean_object* v___x_38_; uint8_t v_isShared_39_; uint8_t v_isSharedCheck_44_; 
lean_dec(v_fvarId_27_);
v_val_36_ = lean_ctor_get(v___x_34_, 0);
v_isSharedCheck_44_ = !lean_is_exclusive(v___x_34_);
if (v_isSharedCheck_44_ == 0)
{
v___x_38_ = v___x_34_;
v_isShared_39_ = v_isSharedCheck_44_;
goto v_resetjp_37_;
}
else
{
lean_inc(v_val_36_);
lean_dec(v___x_34_);
v___x_38_ = lean_box(0);
v_isShared_39_ = v_isSharedCheck_44_;
goto v_resetjp_37_;
}
v_resetjp_37_:
{
lean_object* v___x_40_; lean_object* v___x_42_; 
v___x_40_ = l_Lean_LocalDecl_type(v_val_36_);
lean_dec(v_val_36_);
if (v_isShared_39_ == 0)
{
lean_ctor_set_tag(v___x_38_, 0);
lean_ctor_set(v___x_38_, 0, v___x_40_);
v___x_42_ = v___x_38_;
goto v_reusejp_41_;
}
else
{
lean_object* v_reuseFailAlloc_43_; 
v_reuseFailAlloc_43_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_43_, 0, v___x_40_);
v___x_42_ = v_reuseFailAlloc_43_;
goto v_reusejp_41_;
}
v_reusejp_41_:
{
return v___x_42_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_getType___boxed(lean_object* v_fvarId_45_, lean_object* v_a_46_, lean_object* v_a_47_, lean_object* v_a_48_, lean_object* v_a_49_, lean_object* v_a_50_, lean_object* v_a_51_){
_start:
{
lean_object* v_res_52_; 
v_res_52_ = l_Lean_Compiler_LCNF_InferType_Pure_getType(v_fvarId_45_, v_a_46_, v_a_47_, v_a_48_, v_a_49_, v_a_50_);
lean_dec(v_a_50_);
lean_dec_ref(v_a_49_);
lean_dec(v_a_48_);
lean_dec_ref(v_a_47_);
lean_dec_ref(v_a_46_);
return v_res_52_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Compiler_LCNF_InferType_Pure_mkForallFVars_spec__0___redArg(lean_object* v_xs_53_, lean_object* v_i_54_, lean_object* v_a_55_, lean_object* v___y_56_, lean_object* v___y_57_, lean_object* v___y_58_, lean_object* v___y_59_, lean_object* v___y_60_){
_start:
{
lean_object* v_zero_62_; uint8_t v_isZero_63_; 
v_zero_62_ = lean_unsigned_to_nat(0u);
v_isZero_63_ = lean_nat_dec_eq(v_i_54_, v_zero_62_);
if (v_isZero_63_ == 1)
{
lean_object* v___x_64_; 
lean_dec(v_i_54_);
v___x_64_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_64_, 0, v_a_55_);
return v___x_64_;
}
else
{
lean_object* v_one_65_; lean_object* v_n_66_; lean_object* v_x_67_; lean_object* v___x_68_; lean_object* v___x_69_; 
v_one_65_ = lean_unsigned_to_nat(1u);
v_n_66_ = lean_nat_sub(v_i_54_, v_one_65_);
lean_dec(v_i_54_);
v_x_67_ = lean_array_fget_borrowed(v_xs_53_, v_n_66_);
v___x_68_ = l_Lean_Expr_fvarId_x21(v_x_67_);
lean_inc(v___x_68_);
v___x_69_ = l_Lean_Compiler_LCNF_InferType_Pure_getBinderName(v___x_68_, v___y_56_, v___y_57_, v___y_58_, v___y_59_, v___y_60_);
if (lean_obj_tag(v___x_69_) == 0)
{
lean_object* v_a_70_; lean_object* v___x_71_; 
v_a_70_ = lean_ctor_get(v___x_69_, 0);
lean_inc(v_a_70_);
lean_dec_ref_known(v___x_69_, 1);
v___x_71_ = l_Lean_Compiler_LCNF_InferType_Pure_getType(v___x_68_, v___y_56_, v___y_57_, v___y_58_, v___y_59_, v___y_60_);
if (lean_obj_tag(v___x_71_) == 0)
{
lean_object* v_a_72_; lean_object* v___x_73_; uint8_t v___x_74_; lean_object* v___x_75_; 
v_a_72_ = lean_ctor_get(v___x_71_, 0);
lean_inc(v_a_72_);
lean_dec_ref_known(v___x_71_, 1);
v___x_73_ = lean_expr_abstract_range(v_a_72_, v_n_66_, v_xs_53_);
lean_dec(v_a_72_);
v___x_74_ = 0;
v___x_75_ = l_Lean_Expr_forallE___override(v_a_70_, v___x_73_, v_a_55_, v___x_74_);
v_i_54_ = v_n_66_;
v_a_55_ = v___x_75_;
goto _start;
}
else
{
lean_dec(v_a_70_);
lean_dec(v_n_66_);
lean_dec_ref(v_a_55_);
return v___x_71_;
}
}
else
{
lean_object* v_a_77_; lean_object* v___x_79_; uint8_t v_isShared_80_; uint8_t v_isSharedCheck_84_; 
lean_dec(v___x_68_);
lean_dec(v_n_66_);
lean_dec_ref(v_a_55_);
v_a_77_ = lean_ctor_get(v___x_69_, 0);
v_isSharedCheck_84_ = !lean_is_exclusive(v___x_69_);
if (v_isSharedCheck_84_ == 0)
{
v___x_79_ = v___x_69_;
v_isShared_80_ = v_isSharedCheck_84_;
goto v_resetjp_78_;
}
else
{
lean_inc(v_a_77_);
lean_dec(v___x_69_);
v___x_79_ = lean_box(0);
v_isShared_80_ = v_isSharedCheck_84_;
goto v_resetjp_78_;
}
v_resetjp_78_:
{
lean_object* v___x_82_; 
if (v_isShared_80_ == 0)
{
v___x_82_ = v___x_79_;
goto v_reusejp_81_;
}
else
{
lean_object* v_reuseFailAlloc_83_; 
v_reuseFailAlloc_83_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_83_, 0, v_a_77_);
v___x_82_ = v_reuseFailAlloc_83_;
goto v_reusejp_81_;
}
v_reusejp_81_:
{
return v___x_82_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Compiler_LCNF_InferType_Pure_mkForallFVars_spec__0___redArg___boxed(lean_object* v_xs_85_, lean_object* v_i_86_, lean_object* v_a_87_, lean_object* v___y_88_, lean_object* v___y_89_, lean_object* v___y_90_, lean_object* v___y_91_, lean_object* v___y_92_, lean_object* v___y_93_){
_start:
{
lean_object* v_res_94_; 
v_res_94_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Compiler_LCNF_InferType_Pure_mkForallFVars_spec__0___redArg(v_xs_85_, v_i_86_, v_a_87_, v___y_88_, v___y_89_, v___y_90_, v___y_91_, v___y_92_);
lean_dec(v___y_92_);
lean_dec_ref(v___y_91_);
lean_dec(v___y_90_);
lean_dec_ref(v___y_89_);
lean_dec_ref(v___y_88_);
lean_dec_ref(v_xs_85_);
return v_res_94_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_mkForallFVars(lean_object* v_xs_95_, lean_object* v_type_96_, lean_object* v_a_97_, lean_object* v_a_98_, lean_object* v_a_99_, lean_object* v_a_100_, lean_object* v_a_101_){
_start:
{
lean_object* v_b_103_; lean_object* v___x_104_; lean_object* v___x_105_; 
v_b_103_ = lean_expr_abstract(v_type_96_, v_xs_95_);
v___x_104_ = lean_array_get_size(v_xs_95_);
v___x_105_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Compiler_LCNF_InferType_Pure_mkForallFVars_spec__0___redArg(v_xs_95_, v___x_104_, v_b_103_, v_a_97_, v_a_98_, v_a_99_, v_a_100_, v_a_101_);
return v___x_105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_mkForallFVars___boxed(lean_object* v_xs_106_, lean_object* v_type_107_, lean_object* v_a_108_, lean_object* v_a_109_, lean_object* v_a_110_, lean_object* v_a_111_, lean_object* v_a_112_, lean_object* v_a_113_){
_start:
{
lean_object* v_res_114_; 
v_res_114_ = l_Lean_Compiler_LCNF_InferType_Pure_mkForallFVars(v_xs_106_, v_type_107_, v_a_108_, v_a_109_, v_a_110_, v_a_111_, v_a_112_);
lean_dec(v_a_112_);
lean_dec_ref(v_a_111_);
lean_dec(v_a_110_);
lean_dec_ref(v_a_109_);
lean_dec_ref(v_a_108_);
lean_dec_ref(v_type_107_);
lean_dec_ref(v_xs_106_);
return v_res_114_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Compiler_LCNF_InferType_Pure_mkForallFVars_spec__0(lean_object* v_xs_115_, lean_object* v_n_116_, lean_object* v_i_117_, lean_object* v_a_118_, lean_object* v_a_119_, lean_object* v___y_120_, lean_object* v___y_121_, lean_object* v___y_122_, lean_object* v___y_123_, lean_object* v___y_124_){
_start:
{
lean_object* v___x_126_; 
v___x_126_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Compiler_LCNF_InferType_Pure_mkForallFVars_spec__0___redArg(v_xs_115_, v_i_117_, v_a_119_, v___y_120_, v___y_121_, v___y_122_, v___y_123_, v___y_124_);
return v___x_126_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Compiler_LCNF_InferType_Pure_mkForallFVars_spec__0___boxed(lean_object* v_xs_127_, lean_object* v_n_128_, lean_object* v_i_129_, lean_object* v_a_130_, lean_object* v_a_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_, lean_object* v___y_137_){
_start:
{
lean_object* v_res_138_; 
v_res_138_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Compiler_LCNF_InferType_Pure_mkForallFVars_spec__0(v_xs_127_, v_n_128_, v_i_129_, v_a_130_, v_a_131_, v___y_132_, v___y_133_, v___y_134_, v___y_135_, v___y_136_);
lean_dec(v___y_136_);
lean_dec_ref(v___y_135_);
lean_dec(v___y_134_);
lean_dec_ref(v___y_133_);
lean_dec_ref(v___y_132_);
lean_dec(v_n_128_);
lean_dec_ref(v_xs_127_);
return v_res_138_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_InferType_Pure_mkForallParams_spec__0(size_t v_sz_139_, size_t v_i_140_, lean_object* v_bs_141_){
_start:
{
uint8_t v___x_142_; 
v___x_142_ = lean_usize_dec_lt(v_i_140_, v_sz_139_);
if (v___x_142_ == 0)
{
return v_bs_141_;
}
else
{
lean_object* v_v_143_; lean_object* v_fvarId_144_; lean_object* v___x_145_; lean_object* v_bs_x27_146_; lean_object* v___x_147_; size_t v___x_148_; size_t v___x_149_; lean_object* v___x_150_; 
v_v_143_ = lean_array_uget_borrowed(v_bs_141_, v_i_140_);
v_fvarId_144_ = lean_ctor_get(v_v_143_, 0);
lean_inc(v_fvarId_144_);
v___x_145_ = lean_unsigned_to_nat(0u);
v_bs_x27_146_ = lean_array_uset(v_bs_141_, v_i_140_, v___x_145_);
v___x_147_ = l_Lean_Expr_fvar___override(v_fvarId_144_);
v___x_148_ = ((size_t)1ULL);
v___x_149_ = lean_usize_add(v_i_140_, v___x_148_);
v___x_150_ = lean_array_uset(v_bs_x27_146_, v_i_140_, v___x_147_);
v_i_140_ = v___x_149_;
v_bs_141_ = v___x_150_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_InferType_Pure_mkForallParams_spec__0___boxed(lean_object* v_sz_152_, lean_object* v_i_153_, lean_object* v_bs_154_){
_start:
{
size_t v_sz_boxed_155_; size_t v_i_boxed_156_; lean_object* v_res_157_; 
v_sz_boxed_155_ = lean_unbox_usize(v_sz_152_);
lean_dec(v_sz_152_);
v_i_boxed_156_ = lean_unbox_usize(v_i_153_);
lean_dec(v_i_153_);
v_res_157_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_InferType_Pure_mkForallParams_spec__0(v_sz_boxed_155_, v_i_boxed_156_, v_bs_154_);
return v_res_157_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__0(void){
_start:
{
lean_object* v___x_158_; 
v___x_158_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_158_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__1(void){
_start:
{
lean_object* v___x_159_; lean_object* v___x_160_; 
v___x_159_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__0, &l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__0_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__0);
v___x_160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_160_, 0, v___x_159_);
return v___x_160_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__2(void){
_start:
{
lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; 
v___x_161_ = lean_unsigned_to_nat(32u);
v___x_162_ = lean_mk_empty_array_with_capacity(v___x_161_);
v___x_163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_163_, 0, v___x_162_);
return v___x_163_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__3(void){
_start:
{
size_t v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; 
v___x_164_ = ((size_t)5ULL);
v___x_165_ = lean_unsigned_to_nat(0u);
v___x_166_ = lean_unsigned_to_nat(32u);
v___x_167_ = lean_mk_empty_array_with_capacity(v___x_166_);
v___x_168_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__2, &l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__2_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__2);
v___x_169_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_169_, 0, v___x_168_);
lean_ctor_set(v___x_169_, 1, v___x_167_);
lean_ctor_set(v___x_169_, 2, v___x_165_);
lean_ctor_set(v___x_169_, 3, v___x_165_);
lean_ctor_set_usize(v___x_169_, 4, v___x_164_);
return v___x_169_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4(void){
_start:
{
lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; 
v___x_170_ = lean_box(1);
v___x_171_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__3, &l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__3_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__3);
v___x_172_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__1, &l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__1);
v___x_173_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_173_, 0, v___x_172_);
lean_ctor_set(v___x_173_, 1, v___x_171_);
lean_ctor_set(v___x_173_, 2, v___x_170_);
return v___x_173_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg(lean_object* v_params_174_, lean_object* v_type_175_, lean_object* v_a_176_, lean_object* v_a_177_, lean_object* v_a_178_, lean_object* v_a_179_){
_start:
{
size_t v_sz_181_; size_t v___x_182_; lean_object* v_xs_183_; lean_object* v___x_184_; lean_object* v___x_185_; 
v_sz_181_ = lean_array_size(v_params_174_);
v___x_182_ = ((size_t)0ULL);
v_xs_183_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_InferType_Pure_mkForallParams_spec__0(v_sz_181_, v___x_182_, v_params_174_);
v___x_184_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4, &l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4);
v___x_185_ = l_Lean_Compiler_LCNF_InferType_Pure_mkForallFVars(v_xs_183_, v_type_175_, v___x_184_, v_a_176_, v_a_177_, v_a_178_, v_a_179_);
lean_dec_ref(v_xs_183_);
return v___x_185_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___boxed(lean_object* v_params_186_, lean_object* v_type_187_, lean_object* v_a_188_, lean_object* v_a_189_, lean_object* v_a_190_, lean_object* v_a_191_, lean_object* v_a_192_){
_start:
{
lean_object* v_res_193_; 
v_res_193_ = l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg(v_params_186_, v_type_187_, v_a_188_, v_a_189_, v_a_190_, v_a_191_);
lean_dec(v_a_191_);
lean_dec_ref(v_a_190_);
lean_dec(v_a_189_);
lean_dec_ref(v_a_188_);
lean_dec_ref(v_type_187_);
return v_res_193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams(lean_object* v_params_194_, lean_object* v_type_195_, lean_object* v_a_196_, lean_object* v_a_197_, lean_object* v_a_198_, lean_object* v_a_199_, lean_object* v_a_200_){
_start:
{
lean_object* v___x_202_; 
v___x_202_ = l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg(v_params_194_, v_type_195_, v_a_197_, v_a_198_, v_a_199_, v_a_200_);
return v___x_202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___boxed(lean_object* v_params_203_, lean_object* v_type_204_, lean_object* v_a_205_, lean_object* v_a_206_, lean_object* v_a_207_, lean_object* v_a_208_, lean_object* v_a_209_, lean_object* v_a_210_){
_start:
{
lean_object* v_res_211_; 
v_res_211_ = l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams(v_params_203_, v_type_204_, v_a_205_, v_a_206_, v_a_207_, v_a_208_, v_a_209_);
lean_dec(v_a_209_);
lean_dec_ref(v_a_208_);
lean_dec(v_a_207_);
lean_dec_ref(v_a_206_);
lean_dec_ref(v_a_205_);
lean_dec_ref(v_type_204_);
return v_res_211_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__0(void){
_start:
{
lean_object* v___x_212_; 
v___x_212_ = l_instMonadEIO___redArg();
return v___x_212_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__1(void){
_start:
{
lean_object* v___x_213_; lean_object* v___x_214_; 
v___x_213_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__0, &l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__0_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__0);
v___x_214_ = l_StateRefT_x27_instMonad___redArg(v___x_213_);
return v___x_214_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__8(void){
_start:
{
lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; 
v___x_221_ = l_Lean_Core_instMonadNameGeneratorCoreM;
v___x_222_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__7));
v___x_223_ = l_Lean_monadNameGeneratorLift___redArg(v___x_222_, v___x_221_);
return v___x_223_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__9(void){
_start:
{
lean_object* v___x_224_; lean_object* v___f_225_; lean_object* v___x_226_; 
v___x_224_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__8, &l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__8_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__8);
v___f_225_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__6));
v___x_226_ = l_Lean_monadNameGeneratorLift___redArg(v___f_225_, v___x_224_);
return v___x_226_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__10(void){
_start:
{
lean_object* v___x_227_; lean_object* v___f_228_; lean_object* v___x_229_; 
v___x_227_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__9, &l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__9_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__9);
v___f_228_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__6));
v___x_229_ = l_Lean_monadNameGeneratorLift___redArg(v___f_228_, v___x_227_);
return v___x_229_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg(lean_object* v_binderName_230_, lean_object* v_type_231_, uint8_t v_binderInfo_232_, lean_object* v_k_233_, lean_object* v_a_234_, lean_object* v_a_235_, lean_object* v_a_236_, lean_object* v_a_237_, lean_object* v_a_238_){
_start:
{
lean_object* v___x_240_; lean_object* v_toApplicative_241_; lean_object* v_toFunctor_242_; lean_object* v_toSeq_243_; lean_object* v_toSeqLeft_244_; lean_object* v_toSeqRight_245_; lean_object* v___f_246_; lean_object* v___f_247_; lean_object* v___f_248_; lean_object* v___f_249_; lean_object* v___x_250_; lean_object* v___f_251_; lean_object* v___f_252_; lean_object* v___f_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v_toApplicative_257_; lean_object* v___x_259_; uint8_t v_isShared_260_; uint8_t v_isSharedCheck_301_; 
v___x_240_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__1, &l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__1);
v_toApplicative_241_ = lean_ctor_get(v___x_240_, 0);
v_toFunctor_242_ = lean_ctor_get(v_toApplicative_241_, 0);
v_toSeq_243_ = lean_ctor_get(v_toApplicative_241_, 2);
v_toSeqLeft_244_ = lean_ctor_get(v_toApplicative_241_, 3);
v_toSeqRight_245_ = lean_ctor_get(v_toApplicative_241_, 4);
v___f_246_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__2));
v___f_247_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_242_, 2);
v___f_248_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_248_, 0, v_toFunctor_242_);
v___f_249_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_249_, 0, v_toFunctor_242_);
v___x_250_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_250_, 0, v___f_248_);
lean_ctor_set(v___x_250_, 1, v___f_249_);
lean_inc(v_toSeqRight_245_);
v___f_251_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_251_, 0, v_toSeqRight_245_);
lean_inc(v_toSeqLeft_244_);
v___f_252_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_252_, 0, v_toSeqLeft_244_);
lean_inc(v_toSeq_243_);
v___f_253_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_253_, 0, v_toSeq_243_);
v___x_254_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_254_, 0, v___x_250_);
lean_ctor_set(v___x_254_, 1, v___f_246_);
lean_ctor_set(v___x_254_, 2, v___f_253_);
lean_ctor_set(v___x_254_, 3, v___f_252_);
lean_ctor_set(v___x_254_, 4, v___f_251_);
v___x_255_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_255_, 0, v___x_254_);
lean_ctor_set(v___x_255_, 1, v___f_247_);
v___x_256_ = l_StateRefT_x27_instMonad___redArg(v___x_255_);
v_toApplicative_257_ = lean_ctor_get(v___x_256_, 0);
v_isSharedCheck_301_ = !lean_is_exclusive(v___x_256_);
if (v_isSharedCheck_301_ == 0)
{
lean_object* v_unused_302_; 
v_unused_302_ = lean_ctor_get(v___x_256_, 1);
lean_dec(v_unused_302_);
v___x_259_ = v___x_256_;
v_isShared_260_ = v_isSharedCheck_301_;
goto v_resetjp_258_;
}
else
{
lean_inc(v_toApplicative_257_);
lean_dec(v___x_256_);
v___x_259_ = lean_box(0);
v_isShared_260_ = v_isSharedCheck_301_;
goto v_resetjp_258_;
}
v_resetjp_258_:
{
lean_object* v_toFunctor_261_; lean_object* v_toSeq_262_; lean_object* v_toSeqLeft_263_; lean_object* v_toSeqRight_264_; lean_object* v___x_266_; uint8_t v_isShared_267_; uint8_t v_isSharedCheck_299_; 
v_toFunctor_261_ = lean_ctor_get(v_toApplicative_257_, 0);
v_toSeq_262_ = lean_ctor_get(v_toApplicative_257_, 2);
v_toSeqLeft_263_ = lean_ctor_get(v_toApplicative_257_, 3);
v_toSeqRight_264_ = lean_ctor_get(v_toApplicative_257_, 4);
v_isSharedCheck_299_ = !lean_is_exclusive(v_toApplicative_257_);
if (v_isSharedCheck_299_ == 0)
{
lean_object* v_unused_300_; 
v_unused_300_ = lean_ctor_get(v_toApplicative_257_, 1);
lean_dec(v_unused_300_);
v___x_266_ = v_toApplicative_257_;
v_isShared_267_ = v_isSharedCheck_299_;
goto v_resetjp_265_;
}
else
{
lean_inc(v_toSeqRight_264_);
lean_inc(v_toSeqLeft_263_);
lean_inc(v_toSeq_262_);
lean_inc(v_toFunctor_261_);
lean_dec(v_toApplicative_257_);
v___x_266_ = lean_box(0);
v_isShared_267_ = v_isSharedCheck_299_;
goto v_resetjp_265_;
}
v_resetjp_265_:
{
lean_object* v___f_268_; lean_object* v___f_269_; lean_object* v___f_270_; lean_object* v___f_271_; lean_object* v___x_272_; lean_object* v___f_273_; lean_object* v___f_274_; lean_object* v___f_275_; lean_object* v___x_277_; 
v___f_268_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__4));
v___f_269_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__5));
lean_inc_ref(v_toFunctor_261_);
v___f_270_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_270_, 0, v_toFunctor_261_);
v___f_271_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_271_, 0, v_toFunctor_261_);
v___x_272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_272_, 0, v___f_270_);
lean_ctor_set(v___x_272_, 1, v___f_271_);
v___f_273_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_273_, 0, v_toSeqRight_264_);
v___f_274_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_274_, 0, v_toSeqLeft_263_);
v___f_275_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_275_, 0, v_toSeq_262_);
if (v_isShared_267_ == 0)
{
lean_ctor_set(v___x_266_, 4, v___f_273_);
lean_ctor_set(v___x_266_, 3, v___f_274_);
lean_ctor_set(v___x_266_, 2, v___f_275_);
lean_ctor_set(v___x_266_, 1, v___f_268_);
lean_ctor_set(v___x_266_, 0, v___x_272_);
v___x_277_ = v___x_266_;
goto v_reusejp_276_;
}
else
{
lean_object* v_reuseFailAlloc_298_; 
v_reuseFailAlloc_298_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_298_, 0, v___x_272_);
lean_ctor_set(v_reuseFailAlloc_298_, 1, v___f_268_);
lean_ctor_set(v_reuseFailAlloc_298_, 2, v___f_275_);
lean_ctor_set(v_reuseFailAlloc_298_, 3, v___f_274_);
lean_ctor_set(v_reuseFailAlloc_298_, 4, v___f_273_);
v___x_277_ = v_reuseFailAlloc_298_;
goto v_reusejp_276_;
}
v_reusejp_276_:
{
lean_object* v___x_279_; 
if (v_isShared_260_ == 0)
{
lean_ctor_set(v___x_259_, 1, v___f_269_);
lean_ctor_set(v___x_259_, 0, v___x_277_);
v___x_279_ = v___x_259_;
goto v_reusejp_278_;
}
else
{
lean_object* v_reuseFailAlloc_297_; 
v_reuseFailAlloc_297_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_297_, 0, v___x_277_);
lean_ctor_set(v_reuseFailAlloc_297_, 1, v___f_269_);
v___x_279_ = v_reuseFailAlloc_297_;
goto v_reusejp_278_;
}
v_reusejp_278_:
{
lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_198__overap_282_; lean_object* v___x_283_; 
v___x_280_ = l_ReaderT_instMonad___redArg(v___x_279_);
v___x_281_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__10, &l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__10_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__10);
v___x_198__overap_282_ = l_Lean_mkFreshFVarId___redArg(v___x_280_, v___x_281_);
lean_inc(v_a_238_);
lean_inc_ref(v_a_237_);
lean_inc(v_a_236_);
lean_inc_ref(v_a_235_);
lean_inc_ref(v_a_234_);
v___x_283_ = lean_apply_6(v___x_198__overap_282_, v_a_234_, v_a_235_, v_a_236_, v_a_237_, v_a_238_, lean_box(0));
if (lean_obj_tag(v___x_283_) == 0)
{
lean_object* v_a_284_; lean_object* v___x_285_; uint8_t v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; 
v_a_284_ = lean_ctor_get(v___x_283_, 0);
lean_inc_n(v_a_284_, 2);
lean_dec_ref_known(v___x_283_, 1);
v___x_285_ = l_Lean_Expr_fvar___override(v_a_284_);
v___x_286_ = 0;
lean_inc_ref(v_a_234_);
v___x_287_ = l_Lean_LocalContext_mkLocalDecl(v_a_234_, v_a_284_, v_binderName_230_, v_type_231_, v_binderInfo_232_, v___x_286_);
lean_inc(v_a_238_);
lean_inc_ref(v_a_237_);
lean_inc(v_a_236_);
lean_inc_ref(v_a_235_);
v___x_288_ = lean_apply_7(v_k_233_, v___x_285_, v___x_287_, v_a_235_, v_a_236_, v_a_237_, v_a_238_, lean_box(0));
return v___x_288_;
}
else
{
lean_object* v_a_289_; lean_object* v___x_291_; uint8_t v_isShared_292_; uint8_t v_isSharedCheck_296_; 
lean_dec_ref(v_k_233_);
lean_dec_ref(v_type_231_);
lean_dec(v_binderName_230_);
v_a_289_ = lean_ctor_get(v___x_283_, 0);
v_isSharedCheck_296_ = !lean_is_exclusive(v___x_283_);
if (v_isSharedCheck_296_ == 0)
{
v___x_291_ = v___x_283_;
v_isShared_292_ = v_isSharedCheck_296_;
goto v_resetjp_290_;
}
else
{
lean_inc(v_a_289_);
lean_dec(v___x_283_);
v___x_291_ = lean_box(0);
v_isShared_292_ = v_isSharedCheck_296_;
goto v_resetjp_290_;
}
v_resetjp_290_:
{
lean_object* v___x_294_; 
if (v_isShared_292_ == 0)
{
v___x_294_ = v___x_291_;
goto v_reusejp_293_;
}
else
{
lean_object* v_reuseFailAlloc_295_; 
v_reuseFailAlloc_295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_295_, 0, v_a_289_);
v___x_294_ = v_reuseFailAlloc_295_;
goto v_reusejp_293_;
}
v_reusejp_293_:
{
return v___x_294_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___boxed(lean_object* v_binderName_303_, lean_object* v_type_304_, lean_object* v_binderInfo_305_, lean_object* v_k_306_, lean_object* v_a_307_, lean_object* v_a_308_, lean_object* v_a_309_, lean_object* v_a_310_, lean_object* v_a_311_, lean_object* v_a_312_){
_start:
{
uint8_t v_binderInfo_boxed_313_; lean_object* v_res_314_; 
v_binderInfo_boxed_313_ = lean_unbox(v_binderInfo_305_);
v_res_314_ = l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg(v_binderName_303_, v_type_304_, v_binderInfo_boxed_313_, v_k_306_, v_a_307_, v_a_308_, v_a_309_, v_a_310_, v_a_311_);
lean_dec(v_a_311_);
lean_dec_ref(v_a_310_);
lean_dec(v_a_309_);
lean_dec_ref(v_a_308_);
lean_dec_ref(v_a_307_);
return v_res_314_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl(lean_object* v_00_u03b1_315_, lean_object* v_binderName_316_, lean_object* v_type_317_, uint8_t v_binderInfo_318_, lean_object* v_k_319_, lean_object* v_a_320_, lean_object* v_a_321_, lean_object* v_a_322_, lean_object* v_a_323_, lean_object* v_a_324_){
_start:
{
lean_object* v___x_326_; lean_object* v_toApplicative_327_; lean_object* v_toFunctor_328_; lean_object* v_toSeq_329_; lean_object* v_toSeqLeft_330_; lean_object* v_toSeqRight_331_; lean_object* v___f_332_; lean_object* v___f_333_; lean_object* v___f_334_; lean_object* v___f_335_; lean_object* v___x_336_; lean_object* v___f_337_; lean_object* v___f_338_; lean_object* v___f_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v_toApplicative_343_; lean_object* v___x_345_; uint8_t v_isShared_346_; uint8_t v_isSharedCheck_387_; 
v___x_326_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__1, &l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__1);
v_toApplicative_327_ = lean_ctor_get(v___x_326_, 0);
v_toFunctor_328_ = lean_ctor_get(v_toApplicative_327_, 0);
v_toSeq_329_ = lean_ctor_get(v_toApplicative_327_, 2);
v_toSeqLeft_330_ = lean_ctor_get(v_toApplicative_327_, 3);
v_toSeqRight_331_ = lean_ctor_get(v_toApplicative_327_, 4);
v___f_332_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__2));
v___f_333_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_328_, 2);
v___f_334_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_334_, 0, v_toFunctor_328_);
v___f_335_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_335_, 0, v_toFunctor_328_);
v___x_336_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_336_, 0, v___f_334_);
lean_ctor_set(v___x_336_, 1, v___f_335_);
lean_inc(v_toSeqRight_331_);
v___f_337_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_337_, 0, v_toSeqRight_331_);
lean_inc(v_toSeqLeft_330_);
v___f_338_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_338_, 0, v_toSeqLeft_330_);
lean_inc(v_toSeq_329_);
v___f_339_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_339_, 0, v_toSeq_329_);
v___x_340_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_340_, 0, v___x_336_);
lean_ctor_set(v___x_340_, 1, v___f_332_);
lean_ctor_set(v___x_340_, 2, v___f_339_);
lean_ctor_set(v___x_340_, 3, v___f_338_);
lean_ctor_set(v___x_340_, 4, v___f_337_);
v___x_341_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_341_, 0, v___x_340_);
lean_ctor_set(v___x_341_, 1, v___f_333_);
v___x_342_ = l_StateRefT_x27_instMonad___redArg(v___x_341_);
v_toApplicative_343_ = lean_ctor_get(v___x_342_, 0);
v_isSharedCheck_387_ = !lean_is_exclusive(v___x_342_);
if (v_isSharedCheck_387_ == 0)
{
lean_object* v_unused_388_; 
v_unused_388_ = lean_ctor_get(v___x_342_, 1);
lean_dec(v_unused_388_);
v___x_345_ = v___x_342_;
v_isShared_346_ = v_isSharedCheck_387_;
goto v_resetjp_344_;
}
else
{
lean_inc(v_toApplicative_343_);
lean_dec(v___x_342_);
v___x_345_ = lean_box(0);
v_isShared_346_ = v_isSharedCheck_387_;
goto v_resetjp_344_;
}
v_resetjp_344_:
{
lean_object* v_toFunctor_347_; lean_object* v_toSeq_348_; lean_object* v_toSeqLeft_349_; lean_object* v_toSeqRight_350_; lean_object* v___x_352_; uint8_t v_isShared_353_; uint8_t v_isSharedCheck_385_; 
v_toFunctor_347_ = lean_ctor_get(v_toApplicative_343_, 0);
v_toSeq_348_ = lean_ctor_get(v_toApplicative_343_, 2);
v_toSeqLeft_349_ = lean_ctor_get(v_toApplicative_343_, 3);
v_toSeqRight_350_ = lean_ctor_get(v_toApplicative_343_, 4);
v_isSharedCheck_385_ = !lean_is_exclusive(v_toApplicative_343_);
if (v_isSharedCheck_385_ == 0)
{
lean_object* v_unused_386_; 
v_unused_386_ = lean_ctor_get(v_toApplicative_343_, 1);
lean_dec(v_unused_386_);
v___x_352_ = v_toApplicative_343_;
v_isShared_353_ = v_isSharedCheck_385_;
goto v_resetjp_351_;
}
else
{
lean_inc(v_toSeqRight_350_);
lean_inc(v_toSeqLeft_349_);
lean_inc(v_toSeq_348_);
lean_inc(v_toFunctor_347_);
lean_dec(v_toApplicative_343_);
v___x_352_ = lean_box(0);
v_isShared_353_ = v_isSharedCheck_385_;
goto v_resetjp_351_;
}
v_resetjp_351_:
{
lean_object* v___f_354_; lean_object* v___f_355_; lean_object* v___f_356_; lean_object* v___f_357_; lean_object* v___x_358_; lean_object* v___f_359_; lean_object* v___f_360_; lean_object* v___f_361_; lean_object* v___x_363_; 
v___f_354_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__4));
v___f_355_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__5));
lean_inc_ref(v_toFunctor_347_);
v___f_356_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_356_, 0, v_toFunctor_347_);
v___f_357_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_357_, 0, v_toFunctor_347_);
v___x_358_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_358_, 0, v___f_356_);
lean_ctor_set(v___x_358_, 1, v___f_357_);
v___f_359_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_359_, 0, v_toSeqRight_350_);
v___f_360_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_360_, 0, v_toSeqLeft_349_);
v___f_361_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_361_, 0, v_toSeq_348_);
if (v_isShared_353_ == 0)
{
lean_ctor_set(v___x_352_, 4, v___f_359_);
lean_ctor_set(v___x_352_, 3, v___f_360_);
lean_ctor_set(v___x_352_, 2, v___f_361_);
lean_ctor_set(v___x_352_, 1, v___f_354_);
lean_ctor_set(v___x_352_, 0, v___x_358_);
v___x_363_ = v___x_352_;
goto v_reusejp_362_;
}
else
{
lean_object* v_reuseFailAlloc_384_; 
v_reuseFailAlloc_384_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_384_, 0, v___x_358_);
lean_ctor_set(v_reuseFailAlloc_384_, 1, v___f_354_);
lean_ctor_set(v_reuseFailAlloc_384_, 2, v___f_361_);
lean_ctor_set(v_reuseFailAlloc_384_, 3, v___f_360_);
lean_ctor_set(v_reuseFailAlloc_384_, 4, v___f_359_);
v___x_363_ = v_reuseFailAlloc_384_;
goto v_reusejp_362_;
}
v_reusejp_362_:
{
lean_object* v___x_365_; 
if (v_isShared_346_ == 0)
{
lean_ctor_set(v___x_345_, 1, v___f_355_);
lean_ctor_set(v___x_345_, 0, v___x_363_);
v___x_365_ = v___x_345_;
goto v_reusejp_364_;
}
else
{
lean_object* v_reuseFailAlloc_383_; 
v_reuseFailAlloc_383_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_383_, 0, v___x_363_);
lean_ctor_set(v_reuseFailAlloc_383_, 1, v___f_355_);
v___x_365_ = v_reuseFailAlloc_383_;
goto v_reusejp_364_;
}
v_reusejp_364_:
{
lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_232__overap_368_; lean_object* v___x_369_; 
v___x_366_ = l_ReaderT_instMonad___redArg(v___x_365_);
v___x_367_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__10, &l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__10_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__10);
v___x_232__overap_368_ = l_Lean_mkFreshFVarId___redArg(v___x_366_, v___x_367_);
lean_inc(v_a_324_);
lean_inc_ref(v_a_323_);
lean_inc(v_a_322_);
lean_inc_ref(v_a_321_);
lean_inc_ref(v_a_320_);
v___x_369_ = lean_apply_6(v___x_232__overap_368_, v_a_320_, v_a_321_, v_a_322_, v_a_323_, v_a_324_, lean_box(0));
if (lean_obj_tag(v___x_369_) == 0)
{
lean_object* v_a_370_; lean_object* v___x_371_; uint8_t v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; 
v_a_370_ = lean_ctor_get(v___x_369_, 0);
lean_inc_n(v_a_370_, 2);
lean_dec_ref_known(v___x_369_, 1);
v___x_371_ = l_Lean_Expr_fvar___override(v_a_370_);
v___x_372_ = 0;
lean_inc_ref(v_a_320_);
v___x_373_ = l_Lean_LocalContext_mkLocalDecl(v_a_320_, v_a_370_, v_binderName_316_, v_type_317_, v_binderInfo_318_, v___x_372_);
lean_inc(v_a_324_);
lean_inc_ref(v_a_323_);
lean_inc(v_a_322_);
lean_inc_ref(v_a_321_);
v___x_374_ = lean_apply_7(v_k_319_, v___x_371_, v___x_373_, v_a_321_, v_a_322_, v_a_323_, v_a_324_, lean_box(0));
return v___x_374_;
}
else
{
lean_object* v_a_375_; lean_object* v___x_377_; uint8_t v_isShared_378_; uint8_t v_isSharedCheck_382_; 
lean_dec_ref(v_k_319_);
lean_dec_ref(v_type_317_);
lean_dec(v_binderName_316_);
v_a_375_ = lean_ctor_get(v___x_369_, 0);
v_isSharedCheck_382_ = !lean_is_exclusive(v___x_369_);
if (v_isSharedCheck_382_ == 0)
{
v___x_377_ = v___x_369_;
v_isShared_378_ = v_isSharedCheck_382_;
goto v_resetjp_376_;
}
else
{
lean_inc(v_a_375_);
lean_dec(v___x_369_);
v___x_377_ = lean_box(0);
v_isShared_378_ = v_isSharedCheck_382_;
goto v_resetjp_376_;
}
v_resetjp_376_:
{
lean_object* v___x_380_; 
if (v_isShared_378_ == 0)
{
v___x_380_ = v___x_377_;
goto v_reusejp_379_;
}
else
{
lean_object* v_reuseFailAlloc_381_; 
v_reuseFailAlloc_381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_381_, 0, v_a_375_);
v___x_380_ = v_reuseFailAlloc_381_;
goto v_reusejp_379_;
}
v_reusejp_379_:
{
return v___x_380_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___boxed(lean_object* v_00_u03b1_389_, lean_object* v_binderName_390_, lean_object* v_type_391_, lean_object* v_binderInfo_392_, lean_object* v_k_393_, lean_object* v_a_394_, lean_object* v_a_395_, lean_object* v_a_396_, lean_object* v_a_397_, lean_object* v_a_398_, lean_object* v_a_399_){
_start:
{
uint8_t v_binderInfo_boxed_400_; lean_object* v_res_401_; 
v_binderInfo_boxed_400_ = lean_unbox(v_binderInfo_392_);
v_res_401_ = l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl(v_00_u03b1_389_, v_binderName_390_, v_type_391_, v_binderInfo_boxed_400_, v_k_393_, v_a_394_, v_a_395_, v_a_396_, v_a_397_, v_a_398_);
lean_dec(v_a_398_);
lean_dec_ref(v_a_397_);
lean_dec(v_a_396_);
lean_dec_ref(v_a_395_);
lean_dec_ref(v_a_394_);
return v_res_401_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferConstType(lean_object* v_declName_405_, lean_object* v_us_406_, lean_object* v_a_407_, lean_object* v_a_408_, lean_object* v_a_409_, lean_object* v_a_410_){
_start:
{
lean_object* v___x_412_; uint8_t v___x_413_; 
v___x_412_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_inferConstType___closed__1));
v___x_413_ = lean_name_eq(v_declName_405_, v___x_412_);
if (v___x_413_ == 0)
{
lean_object* v___x_414_; 
v___x_414_ = l_Lean_Compiler_LCNF_getPhase___redArg(v_a_407_);
if (lean_obj_tag(v___x_414_) == 0)
{
lean_object* v_a_415_; uint8_t v___x_416_; lean_object* v___x_417_; 
v_a_415_ = lean_ctor_get(v___x_414_, 0);
lean_inc(v_a_415_);
lean_dec_ref_known(v___x_414_, 1);
v___x_416_ = lean_unbox(v_a_415_);
lean_dec(v_a_415_);
lean_inc(v_declName_405_);
v___x_417_ = l_Lean_Compiler_LCNF_getDeclAt_x3f(v_declName_405_, v___x_416_, v_a_409_, v_a_410_);
if (lean_obj_tag(v___x_417_) == 0)
{
lean_object* v_a_418_; lean_object* v___x_420_; uint8_t v_isShared_421_; uint8_t v_isSharedCheck_428_; 
v_a_418_ = lean_ctor_get(v___x_417_, 0);
v_isSharedCheck_428_ = !lean_is_exclusive(v___x_417_);
if (v_isSharedCheck_428_ == 0)
{
v___x_420_ = v___x_417_;
v_isShared_421_ = v_isSharedCheck_428_;
goto v_resetjp_419_;
}
else
{
lean_inc(v_a_418_);
lean_dec(v___x_417_);
v___x_420_ = lean_box(0);
v_isShared_421_ = v_isSharedCheck_428_;
goto v_resetjp_419_;
}
v_resetjp_419_:
{
if (lean_obj_tag(v_a_418_) == 1)
{
lean_object* v_val_422_; lean_object* v___x_423_; lean_object* v___x_425_; 
lean_dec(v_declName_405_);
v_val_422_ = lean_ctor_get(v_a_418_, 0);
lean_inc(v_val_422_);
lean_dec_ref_known(v_a_418_, 1);
v___x_423_ = l_Lean_Compiler_LCNF_Decl_instantiateTypeLevelParams___redArg(v_val_422_, v_us_406_);
if (v_isShared_421_ == 0)
{
lean_ctor_set(v___x_420_, 0, v___x_423_);
v___x_425_ = v___x_420_;
goto v_reusejp_424_;
}
else
{
lean_object* v_reuseFailAlloc_426_; 
v_reuseFailAlloc_426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_426_, 0, v___x_423_);
v___x_425_ = v_reuseFailAlloc_426_;
goto v_reusejp_424_;
}
v_reusejp_424_:
{
return v___x_425_;
}
}
else
{
lean_object* v___x_427_; 
lean_del_object(v___x_420_);
lean_dec(v_a_418_);
v___x_427_ = l_Lean_Compiler_LCNF_getOtherDeclType(v_declName_405_, v_us_406_, v_a_407_, v_a_408_, v_a_409_, v_a_410_);
return v___x_427_;
}
}
}
else
{
lean_object* v_a_429_; lean_object* v___x_431_; uint8_t v_isShared_432_; uint8_t v_isSharedCheck_436_; 
lean_dec(v_us_406_);
lean_dec(v_declName_405_);
v_a_429_ = lean_ctor_get(v___x_417_, 0);
v_isSharedCheck_436_ = !lean_is_exclusive(v___x_417_);
if (v_isSharedCheck_436_ == 0)
{
v___x_431_ = v___x_417_;
v_isShared_432_ = v_isSharedCheck_436_;
goto v_resetjp_430_;
}
else
{
lean_inc(v_a_429_);
lean_dec(v___x_417_);
v___x_431_ = lean_box(0);
v_isShared_432_ = v_isSharedCheck_436_;
goto v_resetjp_430_;
}
v_resetjp_430_:
{
lean_object* v___x_434_; 
if (v_isShared_432_ == 0)
{
v___x_434_ = v___x_431_;
goto v_reusejp_433_;
}
else
{
lean_object* v_reuseFailAlloc_435_; 
v_reuseFailAlloc_435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_435_, 0, v_a_429_);
v___x_434_ = v_reuseFailAlloc_435_;
goto v_reusejp_433_;
}
v_reusejp_433_:
{
return v___x_434_;
}
}
}
}
else
{
lean_object* v_a_437_; lean_object* v___x_439_; uint8_t v_isShared_440_; uint8_t v_isSharedCheck_444_; 
lean_dec(v_us_406_);
lean_dec(v_declName_405_);
v_a_437_ = lean_ctor_get(v___x_414_, 0);
v_isSharedCheck_444_ = !lean_is_exclusive(v___x_414_);
if (v_isSharedCheck_444_ == 0)
{
v___x_439_ = v___x_414_;
v_isShared_440_ = v_isSharedCheck_444_;
goto v_resetjp_438_;
}
else
{
lean_inc(v_a_437_);
lean_dec(v___x_414_);
v___x_439_ = lean_box(0);
v_isShared_440_ = v_isSharedCheck_444_;
goto v_resetjp_438_;
}
v_resetjp_438_:
{
lean_object* v___x_442_; 
if (v_isShared_440_ == 0)
{
v___x_442_ = v___x_439_;
goto v_reusejp_441_;
}
else
{
lean_object* v_reuseFailAlloc_443_; 
v_reuseFailAlloc_443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_443_, 0, v_a_437_);
v___x_442_ = v_reuseFailAlloc_443_;
goto v_reusejp_441_;
}
v_reusejp_441_:
{
return v___x_442_;
}
}
}
}
else
{
lean_object* v___x_445_; lean_object* v___x_446_; 
lean_dec(v_us_406_);
lean_dec(v_declName_405_);
v___x_445_ = l_Lean_Compiler_LCNF_erasedExpr;
v___x_446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_446_, 0, v___x_445_);
return v___x_446_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferConstType___boxed(lean_object* v_declName_447_, lean_object* v_us_448_, lean_object* v_a_449_, lean_object* v_a_450_, lean_object* v_a_451_, lean_object* v_a_452_, lean_object* v_a_453_){
_start:
{
lean_object* v_res_454_; 
v_res_454_ = l_Lean_Compiler_LCNF_InferType_Pure_inferConstType(v_declName_447_, v_us_448_, v_a_449_, v_a_450_, v_a_451_, v_a_452_);
lean_dec(v_a_452_);
lean_dec_ref(v_a_451_);
lean_dec(v_a_450_);
lean_dec_ref(v_a_449_);
return v_res_454_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__2(void){
_start:
{
lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; 
v___x_458_ = lean_box(0);
v___x_459_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__1));
v___x_460_ = l_Lean_mkConst(v___x_459_, v___x_458_);
return v___x_460_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__5(void){
_start:
{
lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; 
v___x_464_ = lean_box(0);
v___x_465_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__4));
v___x_466_ = l_Lean_mkConst(v___x_465_, v___x_464_);
return v___x_466_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__8(void){
_start:
{
lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; 
v___x_470_ = lean_box(0);
v___x_471_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__7));
v___x_472_ = l_Lean_mkConst(v___x_471_, v___x_470_);
return v___x_472_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__11(void){
_start:
{
lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; 
v___x_476_ = lean_box(0);
v___x_477_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__10));
v___x_478_ = l_Lean_mkConst(v___x_477_, v___x_476_);
return v___x_478_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__14(void){
_start:
{
lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; 
v___x_482_ = lean_box(0);
v___x_483_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__13));
v___x_484_ = l_Lean_mkConst(v___x_483_, v___x_482_);
return v___x_484_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__17(void){
_start:
{
lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; 
v___x_488_ = lean_box(0);
v___x_489_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__16));
v___x_490_ = l_Lean_mkConst(v___x_489_, v___x_488_);
return v___x_490_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__20(void){
_start:
{
lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; 
v___x_494_ = lean_box(0);
v___x_495_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__19));
v___x_496_ = l_Lean_mkConst(v___x_495_, v___x_494_);
return v___x_496_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType(lean_object* v_value_497_){
_start:
{
switch(lean_obj_tag(v_value_497_))
{
case 0:
{
lean_object* v___x_498_; 
v___x_498_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__2, &l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__2_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__2);
return v___x_498_;
}
case 1:
{
lean_object* v___x_499_; 
v___x_499_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__5, &l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__5_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__5);
return v___x_499_;
}
case 2:
{
lean_object* v___x_500_; 
v___x_500_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__8, &l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__8_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__8);
return v___x_500_;
}
case 3:
{
lean_object* v___x_501_; 
v___x_501_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__11, &l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__11_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__11);
return v___x_501_;
}
case 4:
{
lean_object* v___x_502_; 
v___x_502_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__14, &l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__14_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__14);
return v___x_502_;
}
case 5:
{
lean_object* v___x_503_; 
v___x_503_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__17, &l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__17_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__17);
return v___x_503_;
}
default: 
{
lean_object* v___x_504_; 
v___x_504_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__20, &l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__20_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__20);
return v___x_504_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___boxed(lean_object* v_value_505_){
_start:
{
lean_object* v_res_506_; 
v_res_506_ = l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType(v_value_505_);
lean_dec_ref(v_value_505_);
return v_res_506_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferLambdaType_go_spec__0_spec__3___redArg(lean_object* v___y_507_){
_start:
{
lean_object* v___x_509_; lean_object* v_ngen_510_; lean_object* v_namePrefix_511_; lean_object* v_idx_512_; lean_object* v___x_514_; uint8_t v_isShared_515_; uint8_t v_isSharedCheck_542_; 
v___x_509_ = lean_st_ref_get(v___y_507_);
v_ngen_510_ = lean_ctor_get(v___x_509_, 2);
lean_inc_ref(v_ngen_510_);
lean_dec(v___x_509_);
v_namePrefix_511_ = lean_ctor_get(v_ngen_510_, 0);
v_idx_512_ = lean_ctor_get(v_ngen_510_, 1);
v_isSharedCheck_542_ = !lean_is_exclusive(v_ngen_510_);
if (v_isSharedCheck_542_ == 0)
{
v___x_514_ = v_ngen_510_;
v_isShared_515_ = v_isSharedCheck_542_;
goto v_resetjp_513_;
}
else
{
lean_inc(v_idx_512_);
lean_inc(v_namePrefix_511_);
lean_dec(v_ngen_510_);
v___x_514_ = lean_box(0);
v_isShared_515_ = v_isSharedCheck_542_;
goto v_resetjp_513_;
}
v_resetjp_513_:
{
lean_object* v_r_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_520_; 
lean_inc(v_idx_512_);
lean_inc(v_namePrefix_511_);
v_r_516_ = l_Lean_Name_num___override(v_namePrefix_511_, v_idx_512_);
v___x_517_ = lean_unsigned_to_nat(1u);
v___x_518_ = lean_nat_add(v_idx_512_, v___x_517_);
lean_dec(v_idx_512_);
if (v_isShared_515_ == 0)
{
lean_ctor_set(v___x_514_, 1, v___x_518_);
v___x_520_ = v___x_514_;
goto v_reusejp_519_;
}
else
{
lean_object* v_reuseFailAlloc_541_; 
v_reuseFailAlloc_541_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_541_, 0, v_namePrefix_511_);
lean_ctor_set(v_reuseFailAlloc_541_, 1, v___x_518_);
v___x_520_ = v_reuseFailAlloc_541_;
goto v_reusejp_519_;
}
v_reusejp_519_:
{
lean_object* v___x_521_; lean_object* v_env_522_; lean_object* v_nextMacroScope_523_; lean_object* v_auxDeclNGen_524_; lean_object* v_traceState_525_; lean_object* v_cache_526_; lean_object* v_recordedDeps_527_; lean_object* v_messages_528_; lean_object* v_infoState_529_; lean_object* v_snapshotTasks_530_; lean_object* v___x_532_; uint8_t v_isShared_533_; uint8_t v_isSharedCheck_539_; 
v___x_521_ = lean_st_ref_take(v___y_507_);
v_env_522_ = lean_ctor_get(v___x_521_, 0);
v_nextMacroScope_523_ = lean_ctor_get(v___x_521_, 1);
v_auxDeclNGen_524_ = lean_ctor_get(v___x_521_, 3);
v_traceState_525_ = lean_ctor_get(v___x_521_, 4);
v_cache_526_ = lean_ctor_get(v___x_521_, 5);
v_recordedDeps_527_ = lean_ctor_get(v___x_521_, 6);
v_messages_528_ = lean_ctor_get(v___x_521_, 7);
v_infoState_529_ = lean_ctor_get(v___x_521_, 8);
v_snapshotTasks_530_ = lean_ctor_get(v___x_521_, 9);
v_isSharedCheck_539_ = !lean_is_exclusive(v___x_521_);
if (v_isSharedCheck_539_ == 0)
{
lean_object* v_unused_540_; 
v_unused_540_ = lean_ctor_get(v___x_521_, 2);
lean_dec(v_unused_540_);
v___x_532_ = v___x_521_;
v_isShared_533_ = v_isSharedCheck_539_;
goto v_resetjp_531_;
}
else
{
lean_inc(v_snapshotTasks_530_);
lean_inc(v_infoState_529_);
lean_inc(v_messages_528_);
lean_inc(v_recordedDeps_527_);
lean_inc(v_cache_526_);
lean_inc(v_traceState_525_);
lean_inc(v_auxDeclNGen_524_);
lean_inc(v_nextMacroScope_523_);
lean_inc(v_env_522_);
lean_dec(v___x_521_);
v___x_532_ = lean_box(0);
v_isShared_533_ = v_isSharedCheck_539_;
goto v_resetjp_531_;
}
v_resetjp_531_:
{
lean_object* v___x_535_; 
if (v_isShared_533_ == 0)
{
lean_ctor_set(v___x_532_, 2, v___x_520_);
v___x_535_ = v___x_532_;
goto v_reusejp_534_;
}
else
{
lean_object* v_reuseFailAlloc_538_; 
v_reuseFailAlloc_538_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_538_, 0, v_env_522_);
lean_ctor_set(v_reuseFailAlloc_538_, 1, v_nextMacroScope_523_);
lean_ctor_set(v_reuseFailAlloc_538_, 2, v___x_520_);
lean_ctor_set(v_reuseFailAlloc_538_, 3, v_auxDeclNGen_524_);
lean_ctor_set(v_reuseFailAlloc_538_, 4, v_traceState_525_);
lean_ctor_set(v_reuseFailAlloc_538_, 5, v_cache_526_);
lean_ctor_set(v_reuseFailAlloc_538_, 6, v_recordedDeps_527_);
lean_ctor_set(v_reuseFailAlloc_538_, 7, v_messages_528_);
lean_ctor_set(v_reuseFailAlloc_538_, 8, v_infoState_529_);
lean_ctor_set(v_reuseFailAlloc_538_, 9, v_snapshotTasks_530_);
v___x_535_ = v_reuseFailAlloc_538_;
goto v_reusejp_534_;
}
v_reusejp_534_:
{
lean_object* v___x_536_; lean_object* v___x_537_; 
v___x_536_ = lean_st_ref_put(v___y_507_, v___x_535_);
v___x_537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_537_, 0, v_r_516_);
return v___x_537_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferLambdaType_go_spec__0_spec__3___redArg___boxed(lean_object* v___y_543_, lean_object* v___y_544_){
_start:
{
lean_object* v_res_545_; 
v_res_545_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferLambdaType_go_spec__0_spec__3___redArg(v___y_543_);
lean_dec(v___y_543_);
return v_res_545_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferLambdaType_go_spec__0(lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_){
_start:
{
lean_object* v___x_552_; lean_object* v_a_553_; lean_object* v___x_555_; uint8_t v_isShared_556_; uint8_t v_isSharedCheck_560_; 
v___x_552_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferLambdaType_go_spec__0_spec__3___redArg(v___y_550_);
v_a_553_ = lean_ctor_get(v___x_552_, 0);
v_isSharedCheck_560_ = !lean_is_exclusive(v___x_552_);
if (v_isSharedCheck_560_ == 0)
{
v___x_555_ = v___x_552_;
v_isShared_556_ = v_isSharedCheck_560_;
goto v_resetjp_554_;
}
else
{
lean_inc(v_a_553_);
lean_dec(v___x_552_);
v___x_555_ = lean_box(0);
v_isShared_556_ = v_isSharedCheck_560_;
goto v_resetjp_554_;
}
v_resetjp_554_:
{
lean_object* v___x_558_; 
if (v_isShared_556_ == 0)
{
v___x_558_ = v___x_555_;
goto v_reusejp_557_;
}
else
{
lean_object* v_reuseFailAlloc_559_; 
v_reuseFailAlloc_559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_559_, 0, v_a_553_);
v___x_558_ = v_reuseFailAlloc_559_;
goto v_reusejp_557_;
}
v_reusejp_557_:
{
return v___x_558_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferLambdaType_go_spec__0___boxed(lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_){
_start:
{
lean_object* v_res_567_; 
v_res_567_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferLambdaType_go_spec__0(v___y_561_, v___y_562_, v___y_563_, v___y_564_, v___y_565_);
lean_dec(v___y_565_);
lean_dec_ref(v___y_564_);
lean_dec(v___y_563_);
lean_dec_ref(v___y_562_);
lean_dec_ref(v___y_561_);
return v_res_567_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_InferType_Pure_inferType_spec__2(lean_object* v_msg_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_){
_start:
{
lean_object* v___x_575_; lean_object* v_toApplicative_576_; lean_object* v_toFunctor_577_; lean_object* v_toSeq_578_; lean_object* v_toSeqLeft_579_; lean_object* v_toSeqRight_580_; lean_object* v___f_581_; lean_object* v___f_582_; lean_object* v___f_583_; lean_object* v___f_584_; lean_object* v___x_585_; lean_object* v___f_586_; lean_object* v___f_587_; lean_object* v___f_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___f_594_; lean_object* v___f_595_; lean_object* v___x_6179__overap_596_; lean_object* v___x_597_; 
v___x_575_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__1, &l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__1);
v_toApplicative_576_ = lean_ctor_get(v___x_575_, 0);
v_toFunctor_577_ = lean_ctor_get(v_toApplicative_576_, 0);
v_toSeq_578_ = lean_ctor_get(v_toApplicative_576_, 2);
v_toSeqLeft_579_ = lean_ctor_get(v_toApplicative_576_, 3);
v_toSeqRight_580_ = lean_ctor_get(v_toApplicative_576_, 4);
v___f_581_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__2));
v___f_582_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_577_, 2);
v___f_583_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_583_, 0, v_toFunctor_577_);
v___f_584_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_584_, 0, v_toFunctor_577_);
v___x_585_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_585_, 0, v___f_583_);
lean_ctor_set(v___x_585_, 1, v___f_584_);
lean_inc(v_toSeqRight_580_);
v___f_586_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_586_, 0, v_toSeqRight_580_);
lean_inc(v_toSeqLeft_579_);
v___f_587_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_587_, 0, v_toSeqLeft_579_);
lean_inc(v_toSeq_578_);
v___f_588_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_588_, 0, v_toSeq_578_);
v___x_589_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_589_, 0, v___x_585_);
lean_ctor_set(v___x_589_, 1, v___f_581_);
lean_ctor_set(v___x_589_, 2, v___f_588_);
lean_ctor_set(v___x_589_, 3, v___f_587_);
lean_ctor_set(v___x_589_, 4, v___f_586_);
v___x_590_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_590_, 0, v___x_589_);
lean_ctor_set(v___x_590_, 1, v___f_582_);
v___x_591_ = l_StateRefT_x27_instMonad___redArg(v___x_590_);
v___x_592_ = l_Lean_instInhabitedExpr;
v___x_593_ = l_instInhabitedOfMonad___redArg(v___x_591_, v___x_592_);
v___f_594_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_594_, 0, v___x_593_);
v___f_595_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_595_, 0, v___f_594_);
v___x_6179__overap_596_ = lean_panic_fn_borrowed(v___f_595_, v_msg_568_);
lean_dec_ref(v___f_595_);
lean_inc(v___y_573_);
lean_inc_ref(v___y_572_);
lean_inc(v___y_571_);
lean_inc_ref(v___y_570_);
lean_inc_ref(v___y_569_);
v___x_597_ = lean_apply_6(v___x_6179__overap_596_, v___y_569_, v___y_570_, v___y_571_, v___y_572_, v___y_573_, lean_box(0));
return v___x_597_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_InferType_Pure_inferType_spec__2___boxed(lean_object* v_msg_598_, lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_, lean_object* v___y_603_, lean_object* v___y_604_){
_start:
{
lean_object* v_res_605_; 
v_res_605_ = l_panic___at___00Lean_Compiler_LCNF_InferType_Pure_inferType_spec__2(v_msg_598_, v___y_599_, v___y_600_, v___y_601_, v___y_602_, v___y_603_);
lean_dec(v___y_603_);
lean_dec_ref(v___y_602_);
lean_dec(v___y_601_);
lean_dec_ref(v___y_600_);
lean_dec_ref(v___y_599_);
return v_res_605_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppType_spec__9___redArg___closed__0(void){
_start:
{
lean_object* v___x_606_; lean_object* v___x_607_; 
v___x_606_ = l_Lean_Compiler_LCNF_anyExpr;
v___x_607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_607_, 0, v___x_606_);
return v___x_607_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppType_spec__9___redArg(lean_object* v_upperBound_608_, lean_object* v___x_609_, lean_object* v_a_610_, lean_object* v_b_611_){
_start:
{
lean_object* v_a_614_; uint8_t v___x_618_; 
v___x_618_ = lean_nat_dec_lt(v_a_610_, v_upperBound_608_);
if (v___x_618_ == 0)
{
lean_object* v___x_619_; 
lean_dec(v_a_610_);
v___x_619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_619_, 0, v_b_611_);
return v___x_619_;
}
else
{
lean_object* v_snd_620_; lean_object* v___x_622_; uint8_t v_isShared_623_; uint8_t v_isSharedCheck_656_; 
v_snd_620_ = lean_ctor_get(v_b_611_, 1);
v_isSharedCheck_656_ = !lean_is_exclusive(v_b_611_);
if (v_isSharedCheck_656_ == 0)
{
lean_object* v_unused_657_; 
v_unused_657_ = lean_ctor_get(v_b_611_, 0);
lean_dec(v_unused_657_);
v___x_622_ = v_b_611_;
v_isShared_623_ = v_isSharedCheck_656_;
goto v_resetjp_621_;
}
else
{
lean_inc(v_snd_620_);
lean_dec(v_b_611_);
v___x_622_ = lean_box(0);
v_isShared_623_ = v_isSharedCheck_656_;
goto v_resetjp_621_;
}
v_resetjp_621_:
{
lean_object* v_fst_624_; lean_object* v_snd_625_; lean_object* v___x_627_; uint8_t v_isShared_628_; uint8_t v_isSharedCheck_655_; 
v_fst_624_ = lean_ctor_get(v_snd_620_, 0);
v_snd_625_ = lean_ctor_get(v_snd_620_, 1);
v_isSharedCheck_655_ = !lean_is_exclusive(v_snd_620_);
if (v_isSharedCheck_655_ == 0)
{
v___x_627_ = v_snd_620_;
v_isShared_628_ = v_isSharedCheck_655_;
goto v_resetjp_626_;
}
else
{
lean_inc(v_snd_625_);
lean_inc(v_fst_624_);
lean_dec(v_snd_620_);
v___x_627_ = lean_box(0);
v_isShared_628_ = v_isSharedCheck_655_;
goto v_resetjp_626_;
}
v_resetjp_626_:
{
lean_object* v___x_629_; lean_object* v___x_630_; 
v___x_629_ = lean_box(0);
v___x_630_ = l_Lean_Expr_headBeta(v_snd_625_);
if (lean_obj_tag(v___x_630_) == 7)
{
lean_object* v_body_631_; lean_object* v___x_633_; 
v_body_631_ = lean_ctor_get(v___x_630_, 2);
lean_inc_ref(v_body_631_);
lean_dec_ref_known(v___x_630_, 3);
if (v_isShared_628_ == 0)
{
lean_ctor_set(v___x_627_, 1, v_body_631_);
v___x_633_ = v___x_627_;
goto v_reusejp_632_;
}
else
{
lean_object* v_reuseFailAlloc_637_; 
v_reuseFailAlloc_637_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_637_, 0, v_fst_624_);
lean_ctor_set(v_reuseFailAlloc_637_, 1, v_body_631_);
v___x_633_ = v_reuseFailAlloc_637_;
goto v_reusejp_632_;
}
v_reusejp_632_:
{
lean_object* v___x_635_; 
if (v_isShared_623_ == 0)
{
lean_ctor_set(v___x_622_, 1, v___x_633_);
lean_ctor_set(v___x_622_, 0, v___x_629_);
v___x_635_ = v___x_622_;
goto v_reusejp_634_;
}
else
{
lean_object* v_reuseFailAlloc_636_; 
v_reuseFailAlloc_636_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_636_, 0, v___x_629_);
lean_ctor_set(v_reuseFailAlloc_636_, 1, v___x_633_);
v___x_635_ = v_reuseFailAlloc_636_;
goto v_reusejp_634_;
}
v_reusejp_634_:
{
v_a_614_ = v___x_635_;
goto v___jp_613_;
}
}
}
else
{
lean_object* v___x_638_; lean_object* v___x_639_; 
v___x_638_ = lean_expr_instantiate_rev_range(v___x_630_, v_fst_624_, v_a_610_, v___x_609_);
lean_dec_ref(v___x_630_);
v___x_639_ = l_Lean_Expr_headBeta(v___x_638_);
if (lean_obj_tag(v___x_639_) == 7)
{
lean_object* v_body_640_; lean_object* v___x_642_; 
lean_dec(v_fst_624_);
v_body_640_ = lean_ctor_get(v___x_639_, 2);
lean_inc_ref(v_body_640_);
lean_dec_ref_known(v___x_639_, 3);
lean_inc(v_a_610_);
if (v_isShared_628_ == 0)
{
lean_ctor_set(v___x_627_, 1, v_body_640_);
lean_ctor_set(v___x_627_, 0, v_a_610_);
v___x_642_ = v___x_627_;
goto v_reusejp_641_;
}
else
{
lean_object* v_reuseFailAlloc_646_; 
v_reuseFailAlloc_646_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_646_, 0, v_a_610_);
lean_ctor_set(v_reuseFailAlloc_646_, 1, v_body_640_);
v___x_642_ = v_reuseFailAlloc_646_;
goto v_reusejp_641_;
}
v_reusejp_641_:
{
lean_object* v___x_644_; 
if (v_isShared_623_ == 0)
{
lean_ctor_set(v___x_622_, 1, v___x_642_);
lean_ctor_set(v___x_622_, 0, v___x_629_);
v___x_644_ = v___x_622_;
goto v_reusejp_643_;
}
else
{
lean_object* v_reuseFailAlloc_645_; 
v_reuseFailAlloc_645_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_645_, 0, v___x_629_);
lean_ctor_set(v_reuseFailAlloc_645_, 1, v___x_642_);
v___x_644_ = v_reuseFailAlloc_645_;
goto v_reusejp_643_;
}
v_reusejp_643_:
{
v_a_614_ = v___x_644_;
goto v___jp_613_;
}
}
}
else
{
lean_object* v___x_647_; lean_object* v___x_649_; 
lean_dec(v_a_610_);
v___x_647_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppType_spec__9___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppType_spec__9___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppType_spec__9___redArg___closed__0);
if (v_isShared_628_ == 0)
{
lean_ctor_set(v___x_627_, 1, v___x_639_);
v___x_649_ = v___x_627_;
goto v_reusejp_648_;
}
else
{
lean_object* v_reuseFailAlloc_654_; 
v_reuseFailAlloc_654_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_654_, 0, v_fst_624_);
lean_ctor_set(v_reuseFailAlloc_654_, 1, v___x_639_);
v___x_649_ = v_reuseFailAlloc_654_;
goto v_reusejp_648_;
}
v_reusejp_648_:
{
lean_object* v___x_651_; 
if (v_isShared_623_ == 0)
{
lean_ctor_set(v___x_622_, 1, v___x_649_);
lean_ctor_set(v___x_622_, 0, v___x_647_);
v___x_651_ = v___x_622_;
goto v_reusejp_650_;
}
else
{
lean_object* v_reuseFailAlloc_653_; 
v_reuseFailAlloc_653_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_653_, 0, v___x_647_);
lean_ctor_set(v_reuseFailAlloc_653_, 1, v___x_649_);
v___x_651_ = v_reuseFailAlloc_653_;
goto v_reusejp_650_;
}
v_reusejp_650_:
{
lean_object* v___x_652_; 
v___x_652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_652_, 0, v___x_651_);
return v___x_652_;
}
}
}
}
}
}
}
v___jp_613_:
{
lean_object* v___x_615_; lean_object* v___x_616_; 
v___x_615_ = lean_unsigned_to_nat(1u);
v___x_616_ = lean_nat_add(v_a_610_, v___x_615_);
lean_dec(v_a_610_);
v_a_610_ = v___x_616_;
v_b_611_ = v_a_614_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppType_spec__9___redArg___boxed(lean_object* v_upperBound_658_, lean_object* v___x_659_, lean_object* v_a_660_, lean_object* v_b_661_, lean_object* v___y_662_){
_start:
{
lean_object* v_res_663_; 
v_res_663_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppType_spec__9___redArg(v_upperBound_658_, v___x_659_, v_a_660_, v_b_661_);
lean_dec_ref(v___x_659_);
lean_dec(v_upperBound_658_);
return v_res_663_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_Pure_inferAppType___closed__0(void){
_start:
{
lean_object* v___x_666_; lean_object* v_dummy_667_; 
v___x_666_ = lean_box(0);
v_dummy_667_ = l_Lean_Expr_sort___override(v___x_666_);
return v_dummy_667_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferAppType(lean_object* v_e_668_, lean_object* v_a_669_, lean_object* v_a_670_, lean_object* v_a_671_, lean_object* v_a_672_, lean_object* v_a_673_){
_start:
{
lean_object* v_j_675_; lean_object* v___x_676_; lean_object* v___x_677_; 
v_j_675_ = lean_unsigned_to_nat(0u);
v___x_676_ = l_Lean_Expr_getAppFn(v_e_668_);
v___x_677_ = l_Lean_Compiler_LCNF_InferType_Pure_inferType(v___x_676_, v_a_669_, v_a_670_, v_a_671_, v_a_672_, v_a_673_);
if (lean_obj_tag(v___x_677_) == 0)
{
lean_object* v_a_678_; lean_object* v_dummy_679_; lean_object* v_nargs_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; 
v_a_678_ = lean_ctor_get(v___x_677_, 0);
lean_inc(v_a_678_);
lean_dec_ref_known(v___x_677_, 1);
v_dummy_679_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_inferAppType___closed__0, &l_Lean_Compiler_LCNF_InferType_Pure_inferAppType___closed__0_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_inferAppType___closed__0);
v_nargs_680_ = l_Lean_Expr_getAppNumArgs(v_e_668_);
lean_inc(v_nargs_680_);
v___x_681_ = lean_mk_array(v_nargs_680_, v_dummy_679_);
v___x_682_ = lean_unsigned_to_nat(1u);
v___x_683_ = lean_nat_sub(v_nargs_680_, v___x_682_);
lean_dec(v_nargs_680_);
v___x_684_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_668_, v___x_681_, v___x_683_);
v___x_685_ = lean_array_get_size(v___x_684_);
v___x_686_ = lean_box(0);
v___x_687_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_687_, 0, v_j_675_);
lean_ctor_set(v___x_687_, 1, v_a_678_);
v___x_688_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_688_, 0, v___x_686_);
lean_ctor_set(v___x_688_, 1, v___x_687_);
v___x_689_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppType_spec__9___redArg(v___x_685_, v___x_684_, v_j_675_, v___x_688_);
if (lean_obj_tag(v___x_689_) == 0)
{
lean_object* v_a_690_; lean_object* v___x_692_; uint8_t v_isShared_693_; uint8_t v_isSharedCheck_707_; 
v_a_690_ = lean_ctor_get(v___x_689_, 0);
v_isSharedCheck_707_ = !lean_is_exclusive(v___x_689_);
if (v_isSharedCheck_707_ == 0)
{
v___x_692_ = v___x_689_;
v_isShared_693_ = v_isSharedCheck_707_;
goto v_resetjp_691_;
}
else
{
lean_inc(v_a_690_);
lean_dec(v___x_689_);
v___x_692_ = lean_box(0);
v_isShared_693_ = v_isSharedCheck_707_;
goto v_resetjp_691_;
}
v_resetjp_691_:
{
lean_object* v_fst_694_; 
v_fst_694_ = lean_ctor_get(v_a_690_, 0);
if (lean_obj_tag(v_fst_694_) == 0)
{
lean_object* v_snd_695_; lean_object* v_fst_696_; lean_object* v_snd_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_701_; 
v_snd_695_ = lean_ctor_get(v_a_690_, 1);
lean_inc(v_snd_695_);
lean_dec(v_a_690_);
v_fst_696_ = lean_ctor_get(v_snd_695_, 0);
lean_inc(v_fst_696_);
v_snd_697_ = lean_ctor_get(v_snd_695_, 1);
lean_inc(v_snd_697_);
lean_dec(v_snd_695_);
v___x_698_ = lean_expr_instantiate_rev_range(v_snd_697_, v_fst_696_, v___x_685_, v___x_684_);
lean_dec_ref(v___x_684_);
lean_dec(v_fst_696_);
lean_dec(v_snd_697_);
v___x_699_ = l_Lean_Expr_headBeta(v___x_698_);
if (v_isShared_693_ == 0)
{
lean_ctor_set(v___x_692_, 0, v___x_699_);
v___x_701_ = v___x_692_;
goto v_reusejp_700_;
}
else
{
lean_object* v_reuseFailAlloc_702_; 
v_reuseFailAlloc_702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_702_, 0, v___x_699_);
v___x_701_ = v_reuseFailAlloc_702_;
goto v_reusejp_700_;
}
v_reusejp_700_:
{
return v___x_701_;
}
}
else
{
lean_object* v_val_703_; lean_object* v___x_705_; 
lean_inc_ref(v_fst_694_);
lean_dec(v_a_690_);
lean_dec_ref(v___x_684_);
v_val_703_ = lean_ctor_get(v_fst_694_, 0);
lean_inc(v_val_703_);
lean_dec_ref_known(v_fst_694_, 1);
if (v_isShared_693_ == 0)
{
lean_ctor_set(v___x_692_, 0, v_val_703_);
v___x_705_ = v___x_692_;
goto v_reusejp_704_;
}
else
{
lean_object* v_reuseFailAlloc_706_; 
v_reuseFailAlloc_706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_706_, 0, v_val_703_);
v___x_705_ = v_reuseFailAlloc_706_;
goto v_reusejp_704_;
}
v_reusejp_704_:
{
return v___x_705_;
}
}
}
}
else
{
lean_object* v_a_708_; lean_object* v___x_710_; uint8_t v_isShared_711_; uint8_t v_isSharedCheck_715_; 
lean_dec_ref(v___x_684_);
v_a_708_ = lean_ctor_get(v___x_689_, 0);
v_isSharedCheck_715_ = !lean_is_exclusive(v___x_689_);
if (v_isSharedCheck_715_ == 0)
{
v___x_710_ = v___x_689_;
v_isShared_711_ = v_isSharedCheck_715_;
goto v_resetjp_709_;
}
else
{
lean_inc(v_a_708_);
lean_dec(v___x_689_);
v___x_710_ = lean_box(0);
v_isShared_711_ = v_isSharedCheck_715_;
goto v_resetjp_709_;
}
v_resetjp_709_:
{
lean_object* v___x_713_; 
if (v_isShared_711_ == 0)
{
v___x_713_ = v___x_710_;
goto v_reusejp_712_;
}
else
{
lean_object* v_reuseFailAlloc_714_; 
v_reuseFailAlloc_714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_714_, 0, v_a_708_);
v___x_713_ = v_reuseFailAlloc_714_;
goto v_reusejp_712_;
}
v_reusejp_712_:
{
return v___x_713_;
}
}
}
}
else
{
lean_dec_ref(v_e_668_);
return v___x_677_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferLambdaType_go(lean_object* v_e_716_, lean_object* v_fvars_717_, lean_object* v_all_718_, lean_object* v_a_719_, lean_object* v_a_720_, lean_object* v_a_721_, lean_object* v_a_722_, lean_object* v_a_723_){
_start:
{
switch(lean_obj_tag(v_e_716_))
{
case 6:
{
lean_object* v_binderName_725_; lean_object* v_binderType_726_; lean_object* v_body_727_; uint8_t v_binderInfo_728_; lean_object* v___x_729_; lean_object* v___x_730_; 
v_binderName_725_ = lean_ctor_get(v_e_716_, 0);
lean_inc(v_binderName_725_);
v_binderType_726_ = lean_ctor_get(v_e_716_, 1);
lean_inc_ref(v_binderType_726_);
v_body_727_ = lean_ctor_get(v_e_716_, 2);
lean_inc_ref(v_body_727_);
v_binderInfo_728_ = lean_ctor_get_uint8(v_e_716_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_716_, 3);
v___x_729_ = lean_expr_instantiate_rev(v_binderType_726_, v_all_718_);
lean_dec_ref(v_binderType_726_);
v___x_730_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferLambdaType_go_spec__0(v_a_719_, v_a_720_, v_a_721_, v_a_722_, v_a_723_);
if (lean_obj_tag(v___x_730_) == 0)
{
lean_object* v_a_731_; lean_object* v___x_732_; uint8_t v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; 
v_a_731_ = lean_ctor_get(v___x_730_, 0);
lean_inc_n(v_a_731_, 2);
lean_dec_ref_known(v___x_730_, 1);
v___x_732_ = l_Lean_Expr_fvar___override(v_a_731_);
v___x_733_ = 0;
v___x_734_ = l_Lean_LocalContext_mkLocalDecl(v_a_719_, v_a_731_, v_binderName_725_, v___x_729_, v_binderInfo_728_, v___x_733_);
lean_inc_ref(v___x_732_);
v___x_735_ = lean_array_push(v_fvars_717_, v___x_732_);
v___x_736_ = lean_array_push(v_all_718_, v___x_732_);
v_e_716_ = v_body_727_;
v_fvars_717_ = v___x_735_;
v_all_718_ = v___x_736_;
v_a_719_ = v___x_734_;
goto _start;
}
else
{
lean_object* v_a_738_; lean_object* v___x_740_; uint8_t v_isShared_741_; uint8_t v_isSharedCheck_745_; 
lean_dec_ref(v___x_729_);
lean_dec_ref(v_body_727_);
lean_dec(v_binderName_725_);
lean_dec_ref(v_a_719_);
lean_dec_ref(v_all_718_);
lean_dec_ref(v_fvars_717_);
v_a_738_ = lean_ctor_get(v___x_730_, 0);
v_isSharedCheck_745_ = !lean_is_exclusive(v___x_730_);
if (v_isSharedCheck_745_ == 0)
{
v___x_740_ = v___x_730_;
v_isShared_741_ = v_isSharedCheck_745_;
goto v_resetjp_739_;
}
else
{
lean_inc(v_a_738_);
lean_dec(v___x_730_);
v___x_740_ = lean_box(0);
v_isShared_741_ = v_isSharedCheck_745_;
goto v_resetjp_739_;
}
v_resetjp_739_:
{
lean_object* v___x_743_; 
if (v_isShared_741_ == 0)
{
v___x_743_ = v___x_740_;
goto v_reusejp_742_;
}
else
{
lean_object* v_reuseFailAlloc_744_; 
v_reuseFailAlloc_744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_744_, 0, v_a_738_);
v___x_743_ = v_reuseFailAlloc_744_;
goto v_reusejp_742_;
}
v_reusejp_742_:
{
return v___x_743_;
}
}
}
}
case 8:
{
lean_object* v_declName_746_; lean_object* v_type_747_; lean_object* v_body_748_; lean_object* v___x_749_; uint8_t v___x_750_; lean_object* v___x_751_; 
v_declName_746_ = lean_ctor_get(v_e_716_, 0);
lean_inc(v_declName_746_);
v_type_747_ = lean_ctor_get(v_e_716_, 1);
lean_inc_ref(v_type_747_);
v_body_748_ = lean_ctor_get(v_e_716_, 3);
lean_inc_ref(v_body_748_);
lean_dec_ref_known(v_e_716_, 4);
v___x_749_ = lean_expr_instantiate_rev(v_type_747_, v_all_718_);
lean_dec_ref(v_type_747_);
v___x_750_ = 0;
v___x_751_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferLambdaType_go_spec__0(v_a_719_, v_a_720_, v_a_721_, v_a_722_, v_a_723_);
if (lean_obj_tag(v___x_751_) == 0)
{
lean_object* v_a_752_; lean_object* v___x_753_; uint8_t v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; 
v_a_752_ = lean_ctor_get(v___x_751_, 0);
lean_inc_n(v_a_752_, 2);
lean_dec_ref_known(v___x_751_, 1);
v___x_753_ = l_Lean_Expr_fvar___override(v_a_752_);
v___x_754_ = 0;
v___x_755_ = l_Lean_LocalContext_mkLocalDecl(v_a_719_, v_a_752_, v_declName_746_, v___x_749_, v___x_750_, v___x_754_);
v___x_756_ = lean_array_push(v_all_718_, v___x_753_);
v_e_716_ = v_body_748_;
v_all_718_ = v___x_756_;
v_a_719_ = v___x_755_;
goto _start;
}
else
{
lean_object* v_a_758_; lean_object* v___x_760_; uint8_t v_isShared_761_; uint8_t v_isSharedCheck_765_; 
lean_dec_ref(v___x_749_);
lean_dec_ref(v_body_748_);
lean_dec(v_declName_746_);
lean_dec_ref(v_a_719_);
lean_dec_ref(v_all_718_);
lean_dec_ref(v_fvars_717_);
v_a_758_ = lean_ctor_get(v___x_751_, 0);
v_isSharedCheck_765_ = !lean_is_exclusive(v___x_751_);
if (v_isSharedCheck_765_ == 0)
{
v___x_760_ = v___x_751_;
v_isShared_761_ = v_isSharedCheck_765_;
goto v_resetjp_759_;
}
else
{
lean_inc(v_a_758_);
lean_dec(v___x_751_);
v___x_760_ = lean_box(0);
v_isShared_761_ = v_isSharedCheck_765_;
goto v_resetjp_759_;
}
v_resetjp_759_:
{
lean_object* v___x_763_; 
if (v_isShared_761_ == 0)
{
v___x_763_ = v___x_760_;
goto v_reusejp_762_;
}
else
{
lean_object* v_reuseFailAlloc_764_; 
v_reuseFailAlloc_764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_764_, 0, v_a_758_);
v___x_763_ = v_reuseFailAlloc_764_;
goto v_reusejp_762_;
}
v_reusejp_762_:
{
return v___x_763_;
}
}
}
}
default: 
{
lean_object* v___x_766_; lean_object* v___x_767_; 
v___x_766_ = lean_expr_instantiate_rev(v_e_716_, v_all_718_);
lean_dec_ref(v_all_718_);
lean_dec_ref(v_e_716_);
v___x_767_ = l_Lean_Compiler_LCNF_InferType_Pure_inferType(v___x_766_, v_a_719_, v_a_720_, v_a_721_, v_a_722_, v_a_723_);
if (lean_obj_tag(v___x_767_) == 0)
{
lean_object* v_a_768_; lean_object* v___x_769_; 
v_a_768_ = lean_ctor_get(v___x_767_, 0);
lean_inc(v_a_768_);
lean_dec_ref_known(v___x_767_, 1);
v___x_769_ = l_Lean_Compiler_LCNF_InferType_Pure_mkForallFVars(v_fvars_717_, v_a_768_, v_a_719_, v_a_720_, v_a_721_, v_a_722_, v_a_723_);
lean_dec_ref(v_a_719_);
lean_dec(v_a_768_);
lean_dec_ref(v_fvars_717_);
return v___x_769_;
}
else
{
lean_dec_ref(v_a_719_);
lean_dec_ref(v_fvars_717_);
return v___x_767_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferLambdaType(lean_object* v_e_770_, lean_object* v_a_771_, lean_object* v_a_772_, lean_object* v_a_773_, lean_object* v_a_774_, lean_object* v_a_775_){
_start:
{
lean_object* v___x_777_; lean_object* v___x_778_; 
v___x_777_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_inferForallType___closed__0));
lean_inc_ref(v_a_771_);
v___x_778_ = l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferLambdaType_go(v_e_770_, v___x_777_, v___x_777_, v_a_771_, v_a_772_, v_a_773_, v_a_774_, v_a_775_);
return v___x_778_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_Pure_inferType___closed__3(void){
_start:
{
lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; 
v___x_782_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_inferType___closed__2));
v___x_783_ = lean_unsigned_to_nat(73u);
v___x_784_ = lean_unsigned_to_nat(135u);
v___x_785_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_inferType___closed__1));
v___x_786_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_inferType___closed__0));
v___x_787_ = l_mkPanicMessageWithDecl(v___x_786_, v___x_785_, v___x_784_, v___x_783_, v___x_782_);
return v___x_787_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferType(lean_object* v_e_788_, lean_object* v_a_789_, lean_object* v_a_790_, lean_object* v_a_791_, lean_object* v_a_792_, lean_object* v_a_793_){
_start:
{
switch(lean_obj_tag(v_e_788_))
{
case 1:
{
lean_object* v_fvarId_795_; lean_object* v___x_796_; 
v_fvarId_795_ = lean_ctor_get(v_e_788_, 0);
lean_inc(v_fvarId_795_);
lean_dec_ref_known(v_e_788_, 1);
v___x_796_ = l_Lean_Compiler_LCNF_InferType_Pure_getType(v_fvarId_795_, v_a_789_, v_a_790_, v_a_791_, v_a_792_, v_a_793_);
return v___x_796_;
}
case 3:
{
lean_object* v_u_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; 
v_u_797_ = lean_ctor_get(v_e_788_, 0);
lean_inc(v_u_797_);
lean_dec_ref_known(v_e_788_, 1);
v___x_798_ = l_Lean_Level_succ___override(v_u_797_);
v___x_799_ = l_Lean_Expr_sort___override(v___x_798_);
v___x_800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_800_, 0, v___x_799_);
return v___x_800_;
}
case 4:
{
lean_object* v_declName_801_; lean_object* v_us_802_; lean_object* v___x_803_; 
v_declName_801_ = lean_ctor_get(v_e_788_, 0);
lean_inc(v_declName_801_);
v_us_802_ = lean_ctor_get(v_e_788_, 1);
lean_inc(v_us_802_);
lean_dec_ref_known(v_e_788_, 2);
v___x_803_ = l_Lean_Compiler_LCNF_InferType_Pure_inferConstType(v_declName_801_, v_us_802_, v_a_790_, v_a_791_, v_a_792_, v_a_793_);
return v___x_803_;
}
case 5:
{
lean_object* v___x_804_; 
v___x_804_ = l_Lean_Compiler_LCNF_InferType_Pure_inferAppType(v_e_788_, v_a_789_, v_a_790_, v_a_791_, v_a_792_, v_a_793_);
return v___x_804_;
}
case 6:
{
lean_object* v___x_805_; 
v___x_805_ = l_Lean_Compiler_LCNF_InferType_Pure_inferLambdaType(v_e_788_, v_a_789_, v_a_790_, v_a_791_, v_a_792_, v_a_793_);
return v___x_805_;
}
case 7:
{
lean_object* v___x_806_; 
v___x_806_ = l_Lean_Compiler_LCNF_InferType_Pure_inferForallType(v_e_788_, v_a_789_, v_a_790_, v_a_791_, v_a_792_, v_a_793_);
return v___x_806_;
}
default: 
{
lean_object* v___x_807_; lean_object* v___x_808_; 
lean_dec_ref(v_e_788_);
v___x_807_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_inferType___closed__3, &l_Lean_Compiler_LCNF_InferType_Pure_inferType___closed__3_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_inferType___closed__3);
v___x_808_ = l_panic___at___00Lean_Compiler_LCNF_InferType_Pure_inferType_spec__2(v___x_807_, v_a_789_, v_a_790_, v_a_791_, v_a_792_, v_a_793_);
return v___x_808_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_getLevel_x3f(lean_object* v_type_809_, lean_object* v_a_810_, lean_object* v_a_811_, lean_object* v_a_812_, lean_object* v_a_813_, lean_object* v_a_814_){
_start:
{
lean_object* v___x_816_; 
v___x_816_ = l_Lean_Compiler_LCNF_InferType_Pure_inferType(v_type_809_, v_a_810_, v_a_811_, v_a_812_, v_a_813_, v_a_814_);
if (lean_obj_tag(v___x_816_) == 0)
{
lean_object* v_a_817_; lean_object* v___x_819_; uint8_t v_isShared_820_; uint8_t v_isSharedCheck_830_; 
v_a_817_ = lean_ctor_get(v___x_816_, 0);
v_isSharedCheck_830_ = !lean_is_exclusive(v___x_816_);
if (v_isSharedCheck_830_ == 0)
{
v___x_819_ = v___x_816_;
v_isShared_820_ = v_isSharedCheck_830_;
goto v_resetjp_818_;
}
else
{
lean_inc(v_a_817_);
lean_dec(v___x_816_);
v___x_819_ = lean_box(0);
v_isShared_820_ = v_isSharedCheck_830_;
goto v_resetjp_818_;
}
v_resetjp_818_:
{
if (lean_obj_tag(v_a_817_) == 3)
{
lean_object* v_u_821_; lean_object* v___x_822_; lean_object* v___x_824_; 
v_u_821_ = lean_ctor_get(v_a_817_, 0);
lean_inc(v_u_821_);
lean_dec_ref_known(v_a_817_, 1);
v___x_822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_822_, 0, v_u_821_);
if (v_isShared_820_ == 0)
{
lean_ctor_set(v___x_819_, 0, v___x_822_);
v___x_824_ = v___x_819_;
goto v_reusejp_823_;
}
else
{
lean_object* v_reuseFailAlloc_825_; 
v_reuseFailAlloc_825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_825_, 0, v___x_822_);
v___x_824_ = v_reuseFailAlloc_825_;
goto v_reusejp_823_;
}
v_reusejp_823_:
{
return v___x_824_;
}
}
else
{
lean_object* v___x_826_; lean_object* v___x_828_; 
lean_dec(v_a_817_);
v___x_826_ = lean_box(0);
if (v_isShared_820_ == 0)
{
lean_ctor_set(v___x_819_, 0, v___x_826_);
v___x_828_ = v___x_819_;
goto v_reusejp_827_;
}
else
{
lean_object* v_reuseFailAlloc_829_; 
v_reuseFailAlloc_829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_829_, 0, v___x_826_);
v___x_828_ = v_reuseFailAlloc_829_;
goto v_reusejp_827_;
}
v_reusejp_827_:
{
return v___x_828_;
}
}
}
}
else
{
lean_object* v_a_831_; lean_object* v___x_833_; uint8_t v_isShared_834_; uint8_t v_isSharedCheck_838_; 
v_a_831_ = lean_ctor_get(v___x_816_, 0);
v_isSharedCheck_838_ = !lean_is_exclusive(v___x_816_);
if (v_isSharedCheck_838_ == 0)
{
v___x_833_ = v___x_816_;
v_isShared_834_ = v_isSharedCheck_838_;
goto v_resetjp_832_;
}
else
{
lean_inc(v_a_831_);
lean_dec(v___x_816_);
v___x_833_ = lean_box(0);
v_isShared_834_ = v_isSharedCheck_838_;
goto v_resetjp_832_;
}
v_resetjp_832_:
{
lean_object* v___x_836_; 
if (v_isShared_834_ == 0)
{
v___x_836_ = v___x_833_;
goto v_reusejp_835_;
}
else
{
lean_object* v_reuseFailAlloc_837_; 
v_reuseFailAlloc_837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_837_, 0, v_a_831_);
v___x_836_ = v_reuseFailAlloc_837_;
goto v_reusejp_835_;
}
v_reusejp_835_:
{
return v___x_836_;
}
}
}
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferForallType_go_spec__6___closed__0(void){
_start:
{
lean_object* v___x_839_; lean_object* v___x_840_; 
v___x_839_ = l_Lean_Compiler_LCNF_erasedExpr;
v___x_840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_840_, 0, v___x_839_);
return v___x_840_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferForallType_go_spec__6(lean_object* v_as_841_, size_t v_sz_842_, size_t v_i_843_, lean_object* v_b_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_){
_start:
{
uint8_t v___x_851_; 
v___x_851_ = lean_usize_dec_lt(v_i_843_, v_sz_842_);
if (v___x_851_ == 0)
{
lean_object* v___x_852_; 
v___x_852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_852_, 0, v_b_844_);
return v___x_852_;
}
else
{
lean_object* v_snd_853_; lean_object* v___x_855_; uint8_t v_isShared_856_; uint8_t v_isSharedCheck_898_; 
v_snd_853_ = lean_ctor_get(v_b_844_, 1);
v_isSharedCheck_898_ = !lean_is_exclusive(v_b_844_);
if (v_isSharedCheck_898_ == 0)
{
lean_object* v_unused_899_; 
v_unused_899_ = lean_ctor_get(v_b_844_, 0);
lean_dec(v_unused_899_);
v___x_855_ = v_b_844_;
v_isShared_856_ = v_isSharedCheck_898_;
goto v_resetjp_854_;
}
else
{
lean_inc(v_snd_853_);
lean_dec(v_b_844_);
v___x_855_ = lean_box(0);
v_isShared_856_ = v_isSharedCheck_898_;
goto v_resetjp_854_;
}
v_resetjp_854_:
{
lean_object* v___x_857_; lean_object* v_a_858_; lean_object* v___x_859_; 
v___x_857_ = lean_box(0);
v_a_858_ = lean_array_uget_borrowed(v_as_841_, v_i_843_);
lean_inc(v_a_858_);
v___x_859_ = l_Lean_Compiler_LCNF_InferType_Pure_inferType(v_a_858_, v___y_845_, v___y_846_, v___y_847_, v___y_848_, v___y_849_);
if (lean_obj_tag(v___x_859_) == 0)
{
lean_object* v_a_860_; lean_object* v___x_861_; 
v_a_860_ = lean_ctor_get(v___x_859_, 0);
lean_inc(v_a_860_);
lean_dec_ref_known(v___x_859_, 1);
v___x_861_ = l_Lean_Compiler_LCNF_InferType_Pure_getLevel_x3f(v_a_860_, v___y_845_, v___y_846_, v___y_847_, v___y_848_, v___y_849_);
if (lean_obj_tag(v___x_861_) == 0)
{
lean_object* v_a_862_; lean_object* v___x_864_; uint8_t v_isShared_865_; uint8_t v_isSharedCheck_881_; 
v_a_862_ = lean_ctor_get(v___x_861_, 0);
v_isSharedCheck_881_ = !lean_is_exclusive(v___x_861_);
if (v_isSharedCheck_881_ == 0)
{
v___x_864_ = v___x_861_;
v_isShared_865_ = v_isSharedCheck_881_;
goto v_resetjp_863_;
}
else
{
lean_inc(v_a_862_);
lean_dec(v___x_861_);
v___x_864_ = lean_box(0);
v_isShared_865_ = v_isSharedCheck_881_;
goto v_resetjp_863_;
}
v_resetjp_863_:
{
if (lean_obj_tag(v_a_862_) == 1)
{
lean_object* v_val_866_; lean_object* v___x_867_; lean_object* v___x_869_; 
lean_del_object(v___x_864_);
v_val_866_ = lean_ctor_get(v_a_862_, 0);
lean_inc(v_val_866_);
lean_dec_ref_known(v_a_862_, 1);
v___x_867_ = l_Lean_mkLevelIMax_x27(v_val_866_, v_snd_853_);
if (v_isShared_856_ == 0)
{
lean_ctor_set(v___x_855_, 1, v___x_867_);
lean_ctor_set(v___x_855_, 0, v___x_857_);
v___x_869_ = v___x_855_;
goto v_reusejp_868_;
}
else
{
lean_object* v_reuseFailAlloc_873_; 
v_reuseFailAlloc_873_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_873_, 0, v___x_857_);
lean_ctor_set(v_reuseFailAlloc_873_, 1, v___x_867_);
v___x_869_ = v_reuseFailAlloc_873_;
goto v_reusejp_868_;
}
v_reusejp_868_:
{
size_t v___x_870_; size_t v___x_871_; 
v___x_870_ = ((size_t)1ULL);
v___x_871_ = lean_usize_add(v_i_843_, v___x_870_);
v_i_843_ = v___x_871_;
v_b_844_ = v___x_869_;
goto _start;
}
}
else
{
lean_object* v___x_874_; lean_object* v___x_876_; 
lean_dec(v_a_862_);
v___x_874_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferForallType_go_spec__6___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferForallType_go_spec__6___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferForallType_go_spec__6___closed__0);
if (v_isShared_856_ == 0)
{
lean_ctor_set(v___x_855_, 0, v___x_874_);
v___x_876_ = v___x_855_;
goto v_reusejp_875_;
}
else
{
lean_object* v_reuseFailAlloc_880_; 
v_reuseFailAlloc_880_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_880_, 0, v___x_874_);
lean_ctor_set(v_reuseFailAlloc_880_, 1, v_snd_853_);
v___x_876_ = v_reuseFailAlloc_880_;
goto v_reusejp_875_;
}
v_reusejp_875_:
{
lean_object* v___x_878_; 
if (v_isShared_865_ == 0)
{
lean_ctor_set(v___x_864_, 0, v___x_876_);
v___x_878_ = v___x_864_;
goto v_reusejp_877_;
}
else
{
lean_object* v_reuseFailAlloc_879_; 
v_reuseFailAlloc_879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_879_, 0, v___x_876_);
v___x_878_ = v_reuseFailAlloc_879_;
goto v_reusejp_877_;
}
v_reusejp_877_:
{
return v___x_878_;
}
}
}
}
}
else
{
lean_object* v_a_882_; lean_object* v___x_884_; uint8_t v_isShared_885_; uint8_t v_isSharedCheck_889_; 
lean_del_object(v___x_855_);
lean_dec(v_snd_853_);
v_a_882_ = lean_ctor_get(v___x_861_, 0);
v_isSharedCheck_889_ = !lean_is_exclusive(v___x_861_);
if (v_isSharedCheck_889_ == 0)
{
v___x_884_ = v___x_861_;
v_isShared_885_ = v_isSharedCheck_889_;
goto v_resetjp_883_;
}
else
{
lean_inc(v_a_882_);
lean_dec(v___x_861_);
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
lean_del_object(v___x_855_);
lean_dec(v_snd_853_);
v_a_890_ = lean_ctor_get(v___x_859_, 0);
v_isSharedCheck_897_ = !lean_is_exclusive(v___x_859_);
if (v_isSharedCheck_897_ == 0)
{
v___x_892_ = v___x_859_;
v_isShared_893_ = v_isSharedCheck_897_;
goto v_resetjp_891_;
}
else
{
lean_inc(v_a_890_);
lean_dec(v___x_859_);
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
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferForallType_go(lean_object* v_e_900_, lean_object* v_fvars_901_, lean_object* v_a_902_, lean_object* v_a_903_, lean_object* v_a_904_, lean_object* v_a_905_, lean_object* v_a_906_){
_start:
{
if (lean_obj_tag(v_e_900_) == 7)
{
lean_object* v_binderName_908_; lean_object* v_binderType_909_; lean_object* v_body_910_; uint8_t v_binderInfo_911_; lean_object* v___x_912_; lean_object* v___x_913_; 
v_binderName_908_ = lean_ctor_get(v_e_900_, 0);
lean_inc(v_binderName_908_);
v_binderType_909_ = lean_ctor_get(v_e_900_, 1);
lean_inc_ref(v_binderType_909_);
v_body_910_ = lean_ctor_get(v_e_900_, 2);
lean_inc_ref(v_body_910_);
v_binderInfo_911_ = lean_ctor_get_uint8(v_e_900_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_900_, 3);
v___x_912_ = lean_expr_instantiate_rev(v_binderType_909_, v_fvars_901_);
lean_dec_ref(v_binderType_909_);
v___x_913_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferLambdaType_go_spec__0(v_a_902_, v_a_903_, v_a_904_, v_a_905_, v_a_906_);
if (lean_obj_tag(v___x_913_) == 0)
{
lean_object* v_a_914_; lean_object* v___x_915_; uint8_t v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; 
v_a_914_ = lean_ctor_get(v___x_913_, 0);
lean_inc_n(v_a_914_, 2);
lean_dec_ref_known(v___x_913_, 1);
v___x_915_ = l_Lean_Expr_fvar___override(v_a_914_);
v___x_916_ = 0;
v___x_917_ = l_Lean_LocalContext_mkLocalDecl(v_a_902_, v_a_914_, v_binderName_908_, v___x_912_, v_binderInfo_911_, v___x_916_);
v___x_918_ = lean_array_push(v_fvars_901_, v___x_915_);
v_e_900_ = v_body_910_;
v_fvars_901_ = v___x_918_;
v_a_902_ = v___x_917_;
goto _start;
}
else
{
lean_object* v_a_920_; lean_object* v___x_922_; uint8_t v_isShared_923_; uint8_t v_isSharedCheck_927_; 
lean_dec_ref(v___x_912_);
lean_dec_ref(v_body_910_);
lean_dec(v_binderName_908_);
lean_dec_ref(v_a_902_);
lean_dec_ref(v_fvars_901_);
v_a_920_ = lean_ctor_get(v___x_913_, 0);
v_isSharedCheck_927_ = !lean_is_exclusive(v___x_913_);
if (v_isSharedCheck_927_ == 0)
{
v___x_922_ = v___x_913_;
v_isShared_923_ = v_isSharedCheck_927_;
goto v_resetjp_921_;
}
else
{
lean_inc(v_a_920_);
lean_dec(v___x_913_);
v___x_922_ = lean_box(0);
v_isShared_923_ = v_isSharedCheck_927_;
goto v_resetjp_921_;
}
v_resetjp_921_:
{
lean_object* v___x_925_; 
if (v_isShared_923_ == 0)
{
v___x_925_ = v___x_922_;
goto v_reusejp_924_;
}
else
{
lean_object* v_reuseFailAlloc_926_; 
v_reuseFailAlloc_926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_926_, 0, v_a_920_);
v___x_925_ = v_reuseFailAlloc_926_;
goto v_reusejp_924_;
}
v_reusejp_924_:
{
return v___x_925_;
}
}
}
}
else
{
lean_object* v_e_928_; lean_object* v___x_929_; 
v_e_928_ = lean_expr_instantiate_rev(v_e_900_, v_fvars_901_);
lean_dec_ref(v_e_900_);
v___x_929_ = l_Lean_Compiler_LCNF_InferType_Pure_getLevel_x3f(v_e_928_, v_a_902_, v_a_903_, v_a_904_, v_a_905_, v_a_906_);
if (lean_obj_tag(v___x_929_) == 0)
{
lean_object* v_a_930_; lean_object* v___x_932_; uint8_t v_isShared_933_; uint8_t v_isSharedCheck_969_; 
v_a_930_ = lean_ctor_get(v___x_929_, 0);
v_isSharedCheck_969_ = !lean_is_exclusive(v___x_929_);
if (v_isSharedCheck_969_ == 0)
{
v___x_932_ = v___x_929_;
v_isShared_933_ = v_isSharedCheck_969_;
goto v_resetjp_931_;
}
else
{
lean_inc(v_a_930_);
lean_dec(v___x_929_);
v___x_932_ = lean_box(0);
v_isShared_933_ = v_isSharedCheck_969_;
goto v_resetjp_931_;
}
v_resetjp_931_:
{
if (lean_obj_tag(v_a_930_) == 1)
{
lean_object* v_val_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; size_t v_sz_938_; size_t v___x_939_; lean_object* v___x_940_; 
lean_del_object(v___x_932_);
v_val_934_ = lean_ctor_get(v_a_930_, 0);
lean_inc(v_val_934_);
lean_dec_ref_known(v_a_930_, 1);
v___x_935_ = l_Array_reverse___redArg(v_fvars_901_);
v___x_936_ = lean_box(0);
v___x_937_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_937_, 0, v___x_936_);
lean_ctor_set(v___x_937_, 1, v_val_934_);
v_sz_938_ = lean_array_size(v___x_935_);
v___x_939_ = ((size_t)0ULL);
v___x_940_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferForallType_go_spec__6(v___x_935_, v_sz_938_, v___x_939_, v___x_937_, v_a_902_, v_a_903_, v_a_904_, v_a_905_, v_a_906_);
lean_dec_ref(v_a_902_);
lean_dec_ref(v___x_935_);
if (lean_obj_tag(v___x_940_) == 0)
{
lean_object* v_a_941_; lean_object* v___x_943_; uint8_t v_isShared_944_; uint8_t v_isSharedCheck_956_; 
v_a_941_ = lean_ctor_get(v___x_940_, 0);
v_isSharedCheck_956_ = !lean_is_exclusive(v___x_940_);
if (v_isSharedCheck_956_ == 0)
{
v___x_943_ = v___x_940_;
v_isShared_944_ = v_isSharedCheck_956_;
goto v_resetjp_942_;
}
else
{
lean_inc(v_a_941_);
lean_dec(v___x_940_);
v___x_943_ = lean_box(0);
v_isShared_944_ = v_isSharedCheck_956_;
goto v_resetjp_942_;
}
v_resetjp_942_:
{
lean_object* v_fst_945_; 
v_fst_945_ = lean_ctor_get(v_a_941_, 0);
if (lean_obj_tag(v_fst_945_) == 0)
{
lean_object* v_snd_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_950_; 
v_snd_946_ = lean_ctor_get(v_a_941_, 1);
lean_inc(v_snd_946_);
lean_dec(v_a_941_);
v___x_947_ = l_Lean_Level_normalize(v_snd_946_);
lean_dec(v_snd_946_);
v___x_948_ = l_Lean_Expr_sort___override(v___x_947_);
if (v_isShared_944_ == 0)
{
lean_ctor_set(v___x_943_, 0, v___x_948_);
v___x_950_ = v___x_943_;
goto v_reusejp_949_;
}
else
{
lean_object* v_reuseFailAlloc_951_; 
v_reuseFailAlloc_951_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_951_, 0, v___x_948_);
v___x_950_ = v_reuseFailAlloc_951_;
goto v_reusejp_949_;
}
v_reusejp_949_:
{
return v___x_950_;
}
}
else
{
lean_object* v_val_952_; lean_object* v___x_954_; 
lean_inc_ref(v_fst_945_);
lean_dec(v_a_941_);
v_val_952_ = lean_ctor_get(v_fst_945_, 0);
lean_inc(v_val_952_);
lean_dec_ref_known(v_fst_945_, 1);
if (v_isShared_944_ == 0)
{
lean_ctor_set(v___x_943_, 0, v_val_952_);
v___x_954_ = v___x_943_;
goto v_reusejp_953_;
}
else
{
lean_object* v_reuseFailAlloc_955_; 
v_reuseFailAlloc_955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_955_, 0, v_val_952_);
v___x_954_ = v_reuseFailAlloc_955_;
goto v_reusejp_953_;
}
v_reusejp_953_:
{
return v___x_954_;
}
}
}
}
else
{
lean_object* v_a_957_; lean_object* v___x_959_; uint8_t v_isShared_960_; uint8_t v_isSharedCheck_964_; 
v_a_957_ = lean_ctor_get(v___x_940_, 0);
v_isSharedCheck_964_ = !lean_is_exclusive(v___x_940_);
if (v_isSharedCheck_964_ == 0)
{
v___x_959_ = v___x_940_;
v_isShared_960_ = v_isSharedCheck_964_;
goto v_resetjp_958_;
}
else
{
lean_inc(v_a_957_);
lean_dec(v___x_940_);
v___x_959_ = lean_box(0);
v_isShared_960_ = v_isSharedCheck_964_;
goto v_resetjp_958_;
}
v_resetjp_958_:
{
lean_object* v___x_962_; 
if (v_isShared_960_ == 0)
{
v___x_962_ = v___x_959_;
goto v_reusejp_961_;
}
else
{
lean_object* v_reuseFailAlloc_963_; 
v_reuseFailAlloc_963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_963_, 0, v_a_957_);
v___x_962_ = v_reuseFailAlloc_963_;
goto v_reusejp_961_;
}
v_reusejp_961_:
{
return v___x_962_;
}
}
}
}
else
{
lean_object* v___x_965_; lean_object* v___x_967_; 
lean_dec(v_a_930_);
lean_dec_ref(v_a_902_);
lean_dec_ref(v_fvars_901_);
v___x_965_ = l_Lean_Compiler_LCNF_erasedExpr;
if (v_isShared_933_ == 0)
{
lean_ctor_set(v___x_932_, 0, v___x_965_);
v___x_967_ = v___x_932_;
goto v_reusejp_966_;
}
else
{
lean_object* v_reuseFailAlloc_968_; 
v_reuseFailAlloc_968_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_968_, 0, v___x_965_);
v___x_967_ = v_reuseFailAlloc_968_;
goto v_reusejp_966_;
}
v_reusejp_966_:
{
return v___x_967_;
}
}
}
}
else
{
lean_object* v_a_970_; lean_object* v___x_972_; uint8_t v_isShared_973_; uint8_t v_isSharedCheck_977_; 
lean_dec_ref(v_a_902_);
lean_dec_ref(v_fvars_901_);
v_a_970_ = lean_ctor_get(v___x_929_, 0);
v_isSharedCheck_977_ = !lean_is_exclusive(v___x_929_);
if (v_isSharedCheck_977_ == 0)
{
v___x_972_ = v___x_929_;
v_isShared_973_ = v_isSharedCheck_977_;
goto v_resetjp_971_;
}
else
{
lean_inc(v_a_970_);
lean_dec(v___x_929_);
v___x_972_ = lean_box(0);
v_isShared_973_ = v_isSharedCheck_977_;
goto v_resetjp_971_;
}
v_resetjp_971_:
{
lean_object* v___x_975_; 
if (v_isShared_973_ == 0)
{
v___x_975_ = v___x_972_;
goto v_reusejp_974_;
}
else
{
lean_object* v_reuseFailAlloc_976_; 
v_reuseFailAlloc_976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_976_, 0, v_a_970_);
v___x_975_ = v_reuseFailAlloc_976_;
goto v_reusejp_974_;
}
v_reusejp_974_:
{
return v___x_975_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferForallType(lean_object* v_e_978_, lean_object* v_a_979_, lean_object* v_a_980_, lean_object* v_a_981_, lean_object* v_a_982_, lean_object* v_a_983_){
_start:
{
lean_object* v___x_985_; lean_object* v___x_986_; 
v___x_985_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_inferForallType___closed__0));
lean_inc_ref(v_a_979_);
v___x_986_ = l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferForallType_go(v_e_978_, v___x_985_, v_a_979_, v_a_980_, v_a_981_, v_a_982_, v_a_983_);
return v___x_986_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferForallType___boxed(lean_object* v_e_987_, lean_object* v_a_988_, lean_object* v_a_989_, lean_object* v_a_990_, lean_object* v_a_991_, lean_object* v_a_992_, lean_object* v_a_993_){
_start:
{
lean_object* v_res_994_; 
v_res_994_ = l_Lean_Compiler_LCNF_InferType_Pure_inferForallType(v_e_987_, v_a_988_, v_a_989_, v_a_990_, v_a_991_, v_a_992_);
lean_dec(v_a_992_);
lean_dec_ref(v_a_991_);
lean_dec(v_a_990_);
lean_dec_ref(v_a_989_);
lean_dec_ref(v_a_988_);
return v_res_994_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferLambdaType___boxed(lean_object* v_e_995_, lean_object* v_a_996_, lean_object* v_a_997_, lean_object* v_a_998_, lean_object* v_a_999_, lean_object* v_a_1000_, lean_object* v_a_1001_){
_start:
{
lean_object* v_res_1002_; 
v_res_1002_ = l_Lean_Compiler_LCNF_InferType_Pure_inferLambdaType(v_e_995_, v_a_996_, v_a_997_, v_a_998_, v_a_999_, v_a_1000_);
lean_dec(v_a_1000_);
lean_dec_ref(v_a_999_);
lean_dec(v_a_998_);
lean_dec_ref(v_a_997_);
lean_dec_ref(v_a_996_);
return v_res_1002_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_getLevel_x3f___boxed(lean_object* v_type_1003_, lean_object* v_a_1004_, lean_object* v_a_1005_, lean_object* v_a_1006_, lean_object* v_a_1007_, lean_object* v_a_1008_, lean_object* v_a_1009_){
_start:
{
lean_object* v_res_1010_; 
v_res_1010_ = l_Lean_Compiler_LCNF_InferType_Pure_getLevel_x3f(v_type_1003_, v_a_1004_, v_a_1005_, v_a_1006_, v_a_1007_, v_a_1008_);
lean_dec(v_a_1008_);
lean_dec_ref(v_a_1007_);
lean_dec(v_a_1006_);
lean_dec_ref(v_a_1005_);
lean_dec_ref(v_a_1004_);
return v_res_1010_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferType___boxed(lean_object* v_e_1011_, lean_object* v_a_1012_, lean_object* v_a_1013_, lean_object* v_a_1014_, lean_object* v_a_1015_, lean_object* v_a_1016_, lean_object* v_a_1017_){
_start:
{
lean_object* v_res_1018_; 
v_res_1018_ = l_Lean_Compiler_LCNF_InferType_Pure_inferType(v_e_1011_, v_a_1012_, v_a_1013_, v_a_1014_, v_a_1015_, v_a_1016_);
lean_dec(v_a_1016_);
lean_dec_ref(v_a_1015_);
lean_dec(v_a_1014_);
lean_dec_ref(v_a_1013_);
lean_dec_ref(v_a_1012_);
return v_res_1018_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferForallType_go_spec__6___boxed(lean_object* v_as_1019_, lean_object* v_sz_1020_, lean_object* v_i_1021_, lean_object* v_b_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_){
_start:
{
size_t v_sz_boxed_1029_; size_t v_i_boxed_1030_; lean_object* v_res_1031_; 
v_sz_boxed_1029_ = lean_unbox_usize(v_sz_1020_);
lean_dec(v_sz_1020_);
v_i_boxed_1030_ = lean_unbox_usize(v_i_1021_);
lean_dec(v_i_1021_);
v_res_1031_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferForallType_go_spec__6(v_as_1019_, v_sz_boxed_1029_, v_i_boxed_1030_, v_b_1022_, v___y_1023_, v___y_1024_, v___y_1025_, v___y_1026_, v___y_1027_);
lean_dec(v___y_1027_);
lean_dec_ref(v___y_1026_);
lean_dec(v___y_1025_);
lean_dec_ref(v___y_1024_);
lean_dec_ref(v___y_1023_);
lean_dec_ref(v_as_1019_);
return v_res_1031_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferAppType___boxed(lean_object* v_e_1032_, lean_object* v_a_1033_, lean_object* v_a_1034_, lean_object* v_a_1035_, lean_object* v_a_1036_, lean_object* v_a_1037_, lean_object* v_a_1038_){
_start:
{
lean_object* v_res_1039_; 
v_res_1039_ = l_Lean_Compiler_LCNF_InferType_Pure_inferAppType(v_e_1032_, v_a_1033_, v_a_1034_, v_a_1035_, v_a_1036_, v_a_1037_);
lean_dec(v_a_1037_);
lean_dec_ref(v_a_1036_);
lean_dec(v_a_1035_);
lean_dec_ref(v_a_1034_);
lean_dec_ref(v_a_1033_);
return v_res_1039_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferLambdaType_go___boxed(lean_object* v_e_1040_, lean_object* v_fvars_1041_, lean_object* v_all_1042_, lean_object* v_a_1043_, lean_object* v_a_1044_, lean_object* v_a_1045_, lean_object* v_a_1046_, lean_object* v_a_1047_, lean_object* v_a_1048_){
_start:
{
lean_object* v_res_1049_; 
v_res_1049_ = l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferLambdaType_go(v_e_1040_, v_fvars_1041_, v_all_1042_, v_a_1043_, v_a_1044_, v_a_1045_, v_a_1046_, v_a_1047_);
lean_dec(v_a_1047_);
lean_dec_ref(v_a_1046_);
lean_dec(v_a_1045_);
lean_dec_ref(v_a_1044_);
return v_res_1049_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferForallType_go___boxed(lean_object* v_e_1050_, lean_object* v_fvars_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_, lean_object* v_a_1054_, lean_object* v_a_1055_, lean_object* v_a_1056_, lean_object* v_a_1057_){
_start:
{
lean_object* v_res_1058_; 
v_res_1058_ = l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferForallType_go(v_e_1050_, v_fvars_1051_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_, v_a_1056_);
lean_dec(v_a_1056_);
lean_dec_ref(v_a_1055_);
lean_dec(v_a_1054_);
lean_dec_ref(v_a_1053_);
return v_res_1058_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferLambdaType_go_spec__0_spec__3(lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_){
_start:
{
lean_object* v___x_1065_; 
v___x_1065_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferLambdaType_go_spec__0_spec__3___redArg(v___y_1063_);
return v___x_1065_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferLambdaType_go_spec__0_spec__3___boxed(lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_){
_start:
{
lean_object* v_res_1072_; 
v_res_1072_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferLambdaType_go_spec__0_spec__3(v___y_1066_, v___y_1067_, v___y_1068_, v___y_1069_, v___y_1070_);
lean_dec(v___y_1070_);
lean_dec_ref(v___y_1069_);
lean_dec(v___y_1068_);
lean_dec_ref(v___y_1067_);
lean_dec_ref(v___y_1066_);
return v_res_1072_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppType_spec__9(lean_object* v_upperBound_1073_, lean_object* v___x_1074_, lean_object* v_inst_1075_, lean_object* v_R_1076_, lean_object* v_a_1077_, lean_object* v_b_1078_, lean_object* v_c_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_){
_start:
{
lean_object* v___x_1086_; 
v___x_1086_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppType_spec__9___redArg(v_upperBound_1073_, v___x_1074_, v_a_1077_, v_b_1078_);
return v___x_1086_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppType_spec__9___boxed(lean_object* v_upperBound_1087_, lean_object* v___x_1088_, lean_object* v_inst_1089_, lean_object* v_R_1090_, lean_object* v_a_1091_, lean_object* v_b_1092_, lean_object* v_c_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_){
_start:
{
lean_object* v_res_1100_; 
v_res_1100_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppType_spec__9(v_upperBound_1087_, v___x_1088_, v_inst_1089_, v_R_1090_, v_a_1091_, v_b_1092_, v_c_1093_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_, v___y_1098_);
lean_dec(v___y_1098_);
lean_dec_ref(v___y_1097_);
lean_dec(v___y_1096_);
lean_dec_ref(v___y_1095_);
lean_dec_ref(v___y_1094_);
lean_dec_ref(v___x_1088_);
lean_dec(v_upperBound_1087_);
return v_res_1100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferArgType(lean_object* v_arg_1101_, lean_object* v_a_1102_, lean_object* v_a_1103_, lean_object* v_a_1104_, lean_object* v_a_1105_, lean_object* v_a_1106_){
_start:
{
switch(lean_obj_tag(v_arg_1101_))
{
case 0:
{
lean_object* v___x_1108_; lean_object* v___x_1109_; 
v___x_1108_ = l_Lean_Compiler_LCNF_erasedExpr;
v___x_1109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1109_, 0, v___x_1108_);
return v___x_1109_;
}
case 1:
{
lean_object* v_fvarId_1110_; lean_object* v___x_1111_; 
v_fvarId_1110_ = lean_ctor_get(v_arg_1101_, 0);
lean_inc(v_fvarId_1110_);
lean_dec_ref_known(v_arg_1101_, 1);
v___x_1111_ = l_Lean_Compiler_LCNF_getType(v_fvarId_1110_, v_a_1103_, v_a_1104_, v_a_1105_, v_a_1106_);
return v___x_1111_;
}
default: 
{
lean_object* v_expr_1112_; lean_object* v___x_1113_; 
v_expr_1112_ = lean_ctor_get(v_arg_1101_, 0);
lean_inc_ref(v_expr_1112_);
lean_dec_ref_known(v_arg_1101_, 1);
v___x_1113_ = l_Lean_Compiler_LCNF_InferType_Pure_inferType(v_expr_1112_, v_a_1102_, v_a_1103_, v_a_1104_, v_a_1105_, v_a_1106_);
return v___x_1113_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferArgType___boxed(lean_object* v_arg_1114_, lean_object* v_a_1115_, lean_object* v_a_1116_, lean_object* v_a_1117_, lean_object* v_a_1118_, lean_object* v_a_1119_, lean_object* v_a_1120_){
_start:
{
lean_object* v_res_1121_; 
v_res_1121_ = l_Lean_Compiler_LCNF_InferType_Pure_inferArgType(v_arg_1114_, v_a_1115_, v_a_1116_, v_a_1117_, v_a_1118_, v_a_1119_);
lean_dec(v_a_1119_);
lean_dec_ref(v_a_1118_);
lean_dec(v_a_1117_);
lean_dec_ref(v_a_1116_);
lean_dec_ref(v_a_1115_);
return v_res_1121_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppTypeCore_spec__0___redArg(lean_object* v_upperBound_1122_, lean_object* v_args_1123_, lean_object* v_a_1124_, lean_object* v_b_1125_){
_start:
{
lean_object* v_a_1128_; uint8_t v___x_1132_; 
v___x_1132_ = lean_nat_dec_lt(v_a_1124_, v_upperBound_1122_);
if (v___x_1132_ == 0)
{
lean_object* v___x_1133_; 
lean_dec(v_a_1124_);
lean_dec_ref(v_args_1123_);
v___x_1133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1133_, 0, v_b_1125_);
return v___x_1133_;
}
else
{
lean_object* v_snd_1134_; lean_object* v___x_1136_; uint8_t v_isShared_1137_; uint8_t v_isSharedCheck_1170_; 
v_snd_1134_ = lean_ctor_get(v_b_1125_, 1);
v_isSharedCheck_1170_ = !lean_is_exclusive(v_b_1125_);
if (v_isSharedCheck_1170_ == 0)
{
lean_object* v_unused_1171_; 
v_unused_1171_ = lean_ctor_get(v_b_1125_, 0);
lean_dec(v_unused_1171_);
v___x_1136_ = v_b_1125_;
v_isShared_1137_ = v_isSharedCheck_1170_;
goto v_resetjp_1135_;
}
else
{
lean_inc(v_snd_1134_);
lean_dec(v_b_1125_);
v___x_1136_ = lean_box(0);
v_isShared_1137_ = v_isSharedCheck_1170_;
goto v_resetjp_1135_;
}
v_resetjp_1135_:
{
lean_object* v_fst_1138_; lean_object* v_snd_1139_; lean_object* v___x_1141_; uint8_t v_isShared_1142_; uint8_t v_isSharedCheck_1169_; 
v_fst_1138_ = lean_ctor_get(v_snd_1134_, 0);
v_snd_1139_ = lean_ctor_get(v_snd_1134_, 1);
v_isSharedCheck_1169_ = !lean_is_exclusive(v_snd_1134_);
if (v_isSharedCheck_1169_ == 0)
{
v___x_1141_ = v_snd_1134_;
v_isShared_1142_ = v_isSharedCheck_1169_;
goto v_resetjp_1140_;
}
else
{
lean_inc(v_snd_1139_);
lean_inc(v_fst_1138_);
lean_dec(v_snd_1134_);
v___x_1141_ = lean_box(0);
v_isShared_1142_ = v_isSharedCheck_1169_;
goto v_resetjp_1140_;
}
v_resetjp_1140_:
{
lean_object* v___x_1143_; lean_object* v___x_1144_; 
v___x_1143_ = lean_box(0);
v___x_1144_ = l_Lean_Expr_headBeta(v_snd_1139_);
if (lean_obj_tag(v___x_1144_) == 7)
{
lean_object* v_body_1145_; lean_object* v___x_1147_; 
v_body_1145_ = lean_ctor_get(v___x_1144_, 2);
lean_inc_ref(v_body_1145_);
lean_dec_ref_known(v___x_1144_, 3);
if (v_isShared_1142_ == 0)
{
lean_ctor_set(v___x_1141_, 1, v_body_1145_);
v___x_1147_ = v___x_1141_;
goto v_reusejp_1146_;
}
else
{
lean_object* v_reuseFailAlloc_1151_; 
v_reuseFailAlloc_1151_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1151_, 0, v_fst_1138_);
lean_ctor_set(v_reuseFailAlloc_1151_, 1, v_body_1145_);
v___x_1147_ = v_reuseFailAlloc_1151_;
goto v_reusejp_1146_;
}
v_reusejp_1146_:
{
lean_object* v___x_1149_; 
if (v_isShared_1137_ == 0)
{
lean_ctor_set(v___x_1136_, 1, v___x_1147_);
lean_ctor_set(v___x_1136_, 0, v___x_1143_);
v___x_1149_ = v___x_1136_;
goto v_reusejp_1148_;
}
else
{
lean_object* v_reuseFailAlloc_1150_; 
v_reuseFailAlloc_1150_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1150_, 0, v___x_1143_);
lean_ctor_set(v_reuseFailAlloc_1150_, 1, v___x_1147_);
v___x_1149_ = v_reuseFailAlloc_1150_;
goto v_reusejp_1148_;
}
v_reusejp_1148_:
{
v_a_1128_ = v___x_1149_;
goto v___jp_1127_;
}
}
}
else
{
lean_object* v___x_1152_; lean_object* v___x_1153_; 
lean_inc_ref(v_args_1123_);
v___x_1152_ = l_Lean_Compiler_LCNF_instantiateRevRangeArgs___redArg(v___x_1144_, v_fst_1138_, v_a_1124_, v_args_1123_);
lean_dec_ref(v___x_1144_);
v___x_1153_ = l_Lean_Expr_headBeta(v___x_1152_);
if (lean_obj_tag(v___x_1153_) == 7)
{
lean_object* v_body_1154_; lean_object* v___x_1156_; 
lean_dec(v_fst_1138_);
v_body_1154_ = lean_ctor_get(v___x_1153_, 2);
lean_inc_ref(v_body_1154_);
lean_dec_ref_known(v___x_1153_, 3);
lean_inc(v_a_1124_);
if (v_isShared_1142_ == 0)
{
lean_ctor_set(v___x_1141_, 1, v_body_1154_);
lean_ctor_set(v___x_1141_, 0, v_a_1124_);
v___x_1156_ = v___x_1141_;
goto v_reusejp_1155_;
}
else
{
lean_object* v_reuseFailAlloc_1160_; 
v_reuseFailAlloc_1160_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1160_, 0, v_a_1124_);
lean_ctor_set(v_reuseFailAlloc_1160_, 1, v_body_1154_);
v___x_1156_ = v_reuseFailAlloc_1160_;
goto v_reusejp_1155_;
}
v_reusejp_1155_:
{
lean_object* v___x_1158_; 
if (v_isShared_1137_ == 0)
{
lean_ctor_set(v___x_1136_, 1, v___x_1156_);
lean_ctor_set(v___x_1136_, 0, v___x_1143_);
v___x_1158_ = v___x_1136_;
goto v_reusejp_1157_;
}
else
{
lean_object* v_reuseFailAlloc_1159_; 
v_reuseFailAlloc_1159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1159_, 0, v___x_1143_);
lean_ctor_set(v_reuseFailAlloc_1159_, 1, v___x_1156_);
v___x_1158_ = v_reuseFailAlloc_1159_;
goto v_reusejp_1157_;
}
v_reusejp_1157_:
{
v_a_1128_ = v___x_1158_;
goto v___jp_1127_;
}
}
}
else
{
lean_object* v___x_1161_; lean_object* v___x_1163_; 
lean_dec(v_a_1124_);
lean_dec_ref(v_args_1123_);
v___x_1161_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppType_spec__9___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppType_spec__9___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppType_spec__9___redArg___closed__0);
if (v_isShared_1142_ == 0)
{
lean_ctor_set(v___x_1141_, 1, v___x_1153_);
v___x_1163_ = v___x_1141_;
goto v_reusejp_1162_;
}
else
{
lean_object* v_reuseFailAlloc_1168_; 
v_reuseFailAlloc_1168_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1168_, 0, v_fst_1138_);
lean_ctor_set(v_reuseFailAlloc_1168_, 1, v___x_1153_);
v___x_1163_ = v_reuseFailAlloc_1168_;
goto v_reusejp_1162_;
}
v_reusejp_1162_:
{
lean_object* v___x_1165_; 
if (v_isShared_1137_ == 0)
{
lean_ctor_set(v___x_1136_, 1, v___x_1163_);
lean_ctor_set(v___x_1136_, 0, v___x_1161_);
v___x_1165_ = v___x_1136_;
goto v_reusejp_1164_;
}
else
{
lean_object* v_reuseFailAlloc_1167_; 
v_reuseFailAlloc_1167_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1167_, 0, v___x_1161_);
lean_ctor_set(v_reuseFailAlloc_1167_, 1, v___x_1163_);
v___x_1165_ = v_reuseFailAlloc_1167_;
goto v_reusejp_1164_;
}
v_reusejp_1164_:
{
lean_object* v___x_1166_; 
v___x_1166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1166_, 0, v___x_1165_);
return v___x_1166_;
}
}
}
}
}
}
}
v___jp_1127_:
{
lean_object* v___x_1129_; lean_object* v___x_1130_; 
v___x_1129_ = lean_unsigned_to_nat(1u);
v___x_1130_ = lean_nat_add(v_a_1124_, v___x_1129_);
lean_dec(v_a_1124_);
v_a_1124_ = v___x_1130_;
v_b_1125_ = v_a_1128_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppTypeCore_spec__0___redArg___boxed(lean_object* v_upperBound_1172_, lean_object* v_args_1173_, lean_object* v_a_1174_, lean_object* v_b_1175_, lean_object* v___y_1176_){
_start:
{
lean_object* v_res_1177_; 
v_res_1177_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppTypeCore_spec__0___redArg(v_upperBound_1172_, v_args_1173_, v_a_1174_, v_b_1175_);
lean_dec(v_upperBound_1172_);
return v_res_1177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferAppTypeCore(lean_object* v_fType_1178_, lean_object* v_args_1179_, lean_object* v_a_1180_, lean_object* v_a_1181_, lean_object* v_a_1182_, lean_object* v_a_1183_, lean_object* v_a_1184_){
_start:
{
lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; 
v___x_1186_ = lean_array_get_size(v_args_1179_);
v___x_1187_ = lean_unsigned_to_nat(0u);
v___x_1188_ = lean_box(0);
v___x_1189_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1189_, 0, v___x_1187_);
lean_ctor_set(v___x_1189_, 1, v_fType_1178_);
v___x_1190_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1190_, 0, v___x_1188_);
lean_ctor_set(v___x_1190_, 1, v___x_1189_);
lean_inc_ref(v_args_1179_);
v___x_1191_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppTypeCore_spec__0___redArg(v___x_1186_, v_args_1179_, v___x_1187_, v___x_1190_);
if (lean_obj_tag(v___x_1191_) == 0)
{
lean_object* v_a_1192_; lean_object* v___x_1194_; uint8_t v_isShared_1195_; uint8_t v_isSharedCheck_1209_; 
v_a_1192_ = lean_ctor_get(v___x_1191_, 0);
v_isSharedCheck_1209_ = !lean_is_exclusive(v___x_1191_);
if (v_isSharedCheck_1209_ == 0)
{
v___x_1194_ = v___x_1191_;
v_isShared_1195_ = v_isSharedCheck_1209_;
goto v_resetjp_1193_;
}
else
{
lean_inc(v_a_1192_);
lean_dec(v___x_1191_);
v___x_1194_ = lean_box(0);
v_isShared_1195_ = v_isSharedCheck_1209_;
goto v_resetjp_1193_;
}
v_resetjp_1193_:
{
lean_object* v_fst_1196_; 
v_fst_1196_ = lean_ctor_get(v_a_1192_, 0);
if (lean_obj_tag(v_fst_1196_) == 0)
{
lean_object* v_snd_1197_; lean_object* v_fst_1198_; lean_object* v_snd_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1203_; 
v_snd_1197_ = lean_ctor_get(v_a_1192_, 1);
lean_inc(v_snd_1197_);
lean_dec(v_a_1192_);
v_fst_1198_ = lean_ctor_get(v_snd_1197_, 0);
lean_inc(v_fst_1198_);
v_snd_1199_ = lean_ctor_get(v_snd_1197_, 1);
lean_inc(v_snd_1199_);
lean_dec(v_snd_1197_);
v___x_1200_ = l_Lean_Compiler_LCNF_instantiateRevRangeArgs___redArg(v_snd_1199_, v_fst_1198_, v___x_1186_, v_args_1179_);
lean_dec(v_fst_1198_);
lean_dec(v_snd_1199_);
v___x_1201_ = l_Lean_Expr_headBeta(v___x_1200_);
if (v_isShared_1195_ == 0)
{
lean_ctor_set(v___x_1194_, 0, v___x_1201_);
v___x_1203_ = v___x_1194_;
goto v_reusejp_1202_;
}
else
{
lean_object* v_reuseFailAlloc_1204_; 
v_reuseFailAlloc_1204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1204_, 0, v___x_1201_);
v___x_1203_ = v_reuseFailAlloc_1204_;
goto v_reusejp_1202_;
}
v_reusejp_1202_:
{
return v___x_1203_;
}
}
else
{
lean_object* v_val_1205_; lean_object* v___x_1207_; 
lean_inc_ref(v_fst_1196_);
lean_dec(v_a_1192_);
lean_dec_ref(v_args_1179_);
v_val_1205_ = lean_ctor_get(v_fst_1196_, 0);
lean_inc(v_val_1205_);
lean_dec_ref_known(v_fst_1196_, 1);
if (v_isShared_1195_ == 0)
{
lean_ctor_set(v___x_1194_, 0, v_val_1205_);
v___x_1207_ = v___x_1194_;
goto v_reusejp_1206_;
}
else
{
lean_object* v_reuseFailAlloc_1208_; 
v_reuseFailAlloc_1208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1208_, 0, v_val_1205_);
v___x_1207_ = v_reuseFailAlloc_1208_;
goto v_reusejp_1206_;
}
v_reusejp_1206_:
{
return v___x_1207_;
}
}
}
}
else
{
lean_object* v_a_1210_; lean_object* v___x_1212_; uint8_t v_isShared_1213_; uint8_t v_isSharedCheck_1217_; 
lean_dec_ref(v_args_1179_);
v_a_1210_ = lean_ctor_get(v___x_1191_, 0);
v_isSharedCheck_1217_ = !lean_is_exclusive(v___x_1191_);
if (v_isSharedCheck_1217_ == 0)
{
v___x_1212_ = v___x_1191_;
v_isShared_1213_ = v_isSharedCheck_1217_;
goto v_resetjp_1211_;
}
else
{
lean_inc(v_a_1210_);
lean_dec(v___x_1191_);
v___x_1212_ = lean_box(0);
v_isShared_1213_ = v_isSharedCheck_1217_;
goto v_resetjp_1211_;
}
v_resetjp_1211_:
{
lean_object* v___x_1215_; 
if (v_isShared_1213_ == 0)
{
v___x_1215_ = v___x_1212_;
goto v_reusejp_1214_;
}
else
{
lean_object* v_reuseFailAlloc_1216_; 
v_reuseFailAlloc_1216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1216_, 0, v_a_1210_);
v___x_1215_ = v_reuseFailAlloc_1216_;
goto v_reusejp_1214_;
}
v_reusejp_1214_:
{
return v___x_1215_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferAppTypeCore___boxed(lean_object* v_fType_1218_, lean_object* v_args_1219_, lean_object* v_a_1220_, lean_object* v_a_1221_, lean_object* v_a_1222_, lean_object* v_a_1223_, lean_object* v_a_1224_, lean_object* v_a_1225_){
_start:
{
lean_object* v_res_1226_; 
v_res_1226_ = l_Lean_Compiler_LCNF_InferType_Pure_inferAppTypeCore(v_fType_1218_, v_args_1219_, v_a_1220_, v_a_1221_, v_a_1222_, v_a_1223_, v_a_1224_);
lean_dec(v_a_1224_);
lean_dec_ref(v_a_1223_);
lean_dec(v_a_1222_);
lean_dec_ref(v_a_1221_);
lean_dec_ref(v_a_1220_);
return v_res_1226_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppTypeCore_spec__0(lean_object* v_upperBound_1227_, lean_object* v_args_1228_, lean_object* v_inst_1229_, lean_object* v_R_1230_, lean_object* v_a_1231_, lean_object* v_b_1232_, lean_object* v_c_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_){
_start:
{
lean_object* v___x_1240_; 
v___x_1240_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppTypeCore_spec__0___redArg(v_upperBound_1227_, v_args_1228_, v_a_1231_, v_b_1232_);
return v___x_1240_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppTypeCore_spec__0___boxed(lean_object* v_upperBound_1241_, lean_object* v_args_1242_, lean_object* v_inst_1243_, lean_object* v_R_1244_, lean_object* v_a_1245_, lean_object* v_b_1246_, lean_object* v_c_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_){
_start:
{
lean_object* v_res_1254_; 
v_res_1254_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppTypeCore_spec__0(v_upperBound_1241_, v_args_1242_, v_inst_1243_, v_R_1244_, v_a_1245_, v_b_1246_, v_c_1247_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_, v___y_1252_);
lean_dec(v___y_1252_);
lean_dec_ref(v___y_1251_);
lean_dec(v___y_1250_);
lean_dec_ref(v___y_1249_);
lean_dec_ref(v___y_1248_);
lean_dec(v_upperBound_1241_);
return v_res_1254_;
}
}
static lean_object* _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1255_; lean_object* v___x_1256_; 
v___x_1255_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__0, &l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__0_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__0);
v___x_1256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1256_, 0, v___x_1255_);
return v___x_1256_;
}
}
static lean_object* _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; 
v___x_1257_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_1258_ = lean_obj_once(&l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___closed__0, &l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___closed__0_once, _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___closed__0);
v___x_1259_ = lean_unsigned_to_nat(0u);
v___x_1260_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_1260_, 0, v___x_1259_);
lean_ctor_set(v___x_1260_, 1, v___x_1259_);
lean_ctor_set(v___x_1260_, 2, v___x_1259_);
lean_ctor_set(v___x_1260_, 3, v___x_1259_);
lean_ctor_set(v___x_1260_, 4, v___x_1258_);
lean_ctor_set(v___x_1260_, 5, v___x_1258_);
lean_ctor_set(v___x_1260_, 6, v___x_1258_);
lean_ctor_set(v___x_1260_, 7, v___x_1258_);
lean_ctor_set(v___x_1260_, 8, v___x_1258_);
lean_ctor_set(v___x_1260_, 9, v___x_1258_);
lean_ctor_set(v___x_1260_, 10, v___x_1258_);
lean_ctor_set(v___x_1260_, 11, v___x_1257_);
return v___x_1260_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg(lean_object* v_msg_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_){
_start:
{
lean_object* v_ref_1267_; lean_object* v___x_1268_; lean_object* v_env_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; 
v_ref_1267_ = lean_ctor_get(v___y_1264_, 2);
v___x_1268_ = lean_st_ref_get(v___y_1265_);
v_env_1269_ = lean_ctor_get(v___x_1268_, 0);
lean_inc_ref(v_env_1269_);
lean_dec(v___x_1268_);
v___x_1270_ = lean_st_ref_get(v___y_1263_);
v___x_1271_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_1262_);
if (lean_obj_tag(v___x_1271_) == 0)
{
lean_object* v_a_1272_; lean_object* v___x_1274_; uint8_t v_isShared_1275_; uint8_t v_isSharedCheck_1294_; 
v_a_1272_ = lean_ctor_get(v___x_1271_, 0);
v_isSharedCheck_1294_ = !lean_is_exclusive(v___x_1271_);
if (v_isSharedCheck_1294_ == 0)
{
v___x_1274_ = v___x_1271_;
v_isShared_1275_ = v_isSharedCheck_1294_;
goto v_resetjp_1273_;
}
else
{
lean_inc(v_a_1272_);
lean_dec(v___x_1271_);
v___x_1274_ = lean_box(0);
v_isShared_1275_ = v_isSharedCheck_1294_;
goto v_resetjp_1273_;
}
v_resetjp_1273_:
{
lean_object* v_lctx_1276_; lean_object* v___x_1278_; uint8_t v_isShared_1279_; uint8_t v_isSharedCheck_1292_; 
v_lctx_1276_ = lean_ctor_get(v___x_1270_, 0);
v_isSharedCheck_1292_ = !lean_is_exclusive(v___x_1270_);
if (v_isSharedCheck_1292_ == 0)
{
lean_object* v_unused_1293_; 
v_unused_1293_ = lean_ctor_get(v___x_1270_, 1);
lean_dec(v_unused_1293_);
v___x_1278_ = v___x_1270_;
v_isShared_1279_ = v_isSharedCheck_1292_;
goto v_resetjp_1277_;
}
else
{
lean_inc(v_lctx_1276_);
lean_dec(v___x_1270_);
v___x_1278_ = lean_box(0);
v_isShared_1279_ = v_isSharedCheck_1292_;
goto v_resetjp_1277_;
}
v_resetjp_1277_:
{
uint8_t v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1286_; 
v___x_1280_ = lean_unbox(v_a_1272_);
lean_dec(v_a_1272_);
v___x_1281_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_1276_, v___x_1280_);
lean_dec_ref(v_lctx_1276_);
v___x_1282_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1264_);
v___x_1283_ = lean_obj_once(&l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___closed__1, &l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___closed__1_once, _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___closed__1);
v___x_1284_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1284_, 0, v_env_1269_);
lean_ctor_set(v___x_1284_, 1, v___x_1283_);
lean_ctor_set(v___x_1284_, 2, v___x_1281_);
lean_ctor_set(v___x_1284_, 3, v___x_1282_);
if (v_isShared_1279_ == 0)
{
lean_ctor_set_tag(v___x_1278_, 3);
lean_ctor_set(v___x_1278_, 1, v_msg_1261_);
lean_ctor_set(v___x_1278_, 0, v___x_1284_);
v___x_1286_ = v___x_1278_;
goto v_reusejp_1285_;
}
else
{
lean_object* v_reuseFailAlloc_1291_; 
v_reuseFailAlloc_1291_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1291_, 0, v___x_1284_);
lean_ctor_set(v_reuseFailAlloc_1291_, 1, v_msg_1261_);
v___x_1286_ = v_reuseFailAlloc_1291_;
goto v_reusejp_1285_;
}
v_reusejp_1285_:
{
lean_object* v___x_1287_; lean_object* v___x_1289_; 
lean_inc(v_ref_1267_);
v___x_1287_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1287_, 0, v_ref_1267_);
lean_ctor_set(v___x_1287_, 1, v___x_1286_);
if (v_isShared_1275_ == 0)
{
lean_ctor_set_tag(v___x_1274_, 1);
lean_ctor_set(v___x_1274_, 0, v___x_1287_);
v___x_1289_ = v___x_1274_;
goto v_reusejp_1288_;
}
else
{
lean_object* v_reuseFailAlloc_1290_; 
v_reuseFailAlloc_1290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1290_, 0, v___x_1287_);
v___x_1289_ = v_reuseFailAlloc_1290_;
goto v_reusejp_1288_;
}
v_reusejp_1288_:
{
return v___x_1289_;
}
}
}
}
}
else
{
lean_object* v_a_1295_; lean_object* v___x_1297_; uint8_t v_isShared_1298_; uint8_t v_isSharedCheck_1302_; 
lean_dec(v___x_1270_);
lean_dec_ref(v_env_1269_);
lean_dec_ref(v_msg_1261_);
v_a_1295_ = lean_ctor_get(v___x_1271_, 0);
v_isSharedCheck_1302_ = !lean_is_exclusive(v___x_1271_);
if (v_isSharedCheck_1302_ == 0)
{
v___x_1297_ = v___x_1271_;
v_isShared_1298_ = v_isSharedCheck_1302_;
goto v_resetjp_1296_;
}
else
{
lean_inc(v_a_1295_);
lean_dec(v___x_1271_);
v___x_1297_ = lean_box(0);
v_isShared_1298_ = v_isSharedCheck_1302_;
goto v_resetjp_1296_;
}
v_resetjp_1296_:
{
lean_object* v___x_1300_; 
if (v_isShared_1298_ == 0)
{
v___x_1300_ = v___x_1297_;
goto v_reusejp_1299_;
}
else
{
lean_object* v_reuseFailAlloc_1301_; 
v_reuseFailAlloc_1301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1301_, 0, v_a_1295_);
v___x_1300_ = v_reuseFailAlloc_1301_;
goto v_reusejp_1299_;
}
v_reusejp_1299_:
{
return v___x_1300_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___boxed(lean_object* v_msg_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_){
_start:
{
lean_object* v_res_1309_; 
v_res_1309_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg(v_msg_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_);
lean_dec(v___y_1307_);
lean_dec_ref(v___y_1306_);
lean_dec(v___y_1305_);
lean_dec_ref(v___y_1304_);
return v_res_1309_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0(lean_object* v_00_u03b1_1310_, lean_object* v_msg_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_){
_start:
{
lean_object* v___x_1318_; 
v___x_1318_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg(v_msg_1311_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_);
return v___x_1318_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___boxed(lean_object* v_00_u03b1_1319_, lean_object* v_msg_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_){
_start:
{
lean_object* v_res_1327_; 
v_res_1327_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0(v_00_u03b1_1319_, v_msg_1320_, v___y_1321_, v___y_1322_, v___y_1323_, v___y_1324_, v___y_1325_);
lean_dec(v___y_1325_);
lean_dec_ref(v___y_1324_);
lean_dec(v___y_1323_);
lean_dec_ref(v___y_1322_);
lean_dec_ref(v___y_1321_);
return v_res_1327_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_1329_; lean_object* v___x_1330_; 
v___x_1329_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3___redArg___closed__0));
v___x_1330_ = l_Lean_stringToMessageData(v___x_1329_);
return v___x_1330_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3___redArg(lean_object* v_upperBound_1331_, lean_object* v_s_1332_, lean_object* v_structName_1333_, lean_object* v_idx_1334_, lean_object* v_a_1335_, lean_object* v_b_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_){
_start:
{
lean_object* v_a_1344_; uint8_t v___x_1348_; 
v___x_1348_ = lean_nat_dec_lt(v_a_1335_, v_upperBound_1331_);
if (v___x_1348_ == 0)
{
lean_object* v___x_1349_; 
lean_dec(v_a_1335_);
lean_dec(v_idx_1334_);
lean_dec(v_structName_1333_);
lean_dec(v_s_1332_);
v___x_1349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1349_, 0, v_b_1336_);
return v___x_1349_;
}
else
{
lean_object* v_snd_1350_; lean_object* v___x_1352_; uint8_t v_isShared_1353_; uint8_t v_isSharedCheck_1388_; 
v_snd_1350_ = lean_ctor_get(v_b_1336_, 1);
v_isSharedCheck_1388_ = !lean_is_exclusive(v_b_1336_);
if (v_isSharedCheck_1388_ == 0)
{
lean_object* v_unused_1389_; 
v_unused_1389_ = lean_ctor_get(v_b_1336_, 0);
lean_dec(v_unused_1389_);
v___x_1352_ = v_b_1336_;
v_isShared_1353_ = v_isSharedCheck_1388_;
goto v_resetjp_1351_;
}
else
{
lean_inc(v_snd_1350_);
lean_dec(v_b_1336_);
v___x_1352_ = lean_box(0);
v_isShared_1353_ = v_isSharedCheck_1388_;
goto v_resetjp_1351_;
}
v_resetjp_1351_:
{
lean_object* v___x_1354_; 
v___x_1354_ = lean_box(0);
if (lean_obj_tag(v_snd_1350_) == 7)
{
lean_object* v_body_1355_; uint8_t v___x_1356_; 
v_body_1355_ = lean_ctor_get(v_snd_1350_, 2);
lean_inc_ref(v_body_1355_);
lean_dec_ref_known(v_snd_1350_, 3);
v___x_1356_ = l_Lean_Expr_hasLooseBVars(v_body_1355_);
if (v___x_1356_ == 0)
{
lean_object* v___x_1358_; 
if (v_isShared_1353_ == 0)
{
lean_ctor_set(v___x_1352_, 1, v_body_1355_);
lean_ctor_set(v___x_1352_, 0, v___x_1354_);
v___x_1358_ = v___x_1352_;
goto v_reusejp_1357_;
}
else
{
lean_object* v_reuseFailAlloc_1359_; 
v_reuseFailAlloc_1359_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1359_, 0, v___x_1354_);
lean_ctor_set(v_reuseFailAlloc_1359_, 1, v_body_1355_);
v___x_1358_ = v_reuseFailAlloc_1359_;
goto v_reusejp_1357_;
}
v_reusejp_1357_:
{
v_a_1344_ = v___x_1358_;
goto v___jp_1343_;
}
}
else
{
lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1363_; 
v___x_1360_ = l_Lean_Compiler_LCNF_anyExpr;
v___x_1361_ = lean_expr_instantiate1(v_body_1355_, v___x_1360_);
lean_dec_ref(v_body_1355_);
if (v_isShared_1353_ == 0)
{
lean_ctor_set(v___x_1352_, 1, v___x_1361_);
lean_ctor_set(v___x_1352_, 0, v___x_1354_);
v___x_1363_ = v___x_1352_;
goto v_reusejp_1362_;
}
else
{
lean_object* v_reuseFailAlloc_1364_; 
v_reuseFailAlloc_1364_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1364_, 0, v___x_1354_);
lean_ctor_set(v_reuseFailAlloc_1364_, 1, v___x_1361_);
v___x_1363_ = v_reuseFailAlloc_1364_;
goto v_reusejp_1362_;
}
v_reusejp_1362_:
{
v_a_1344_ = v___x_1363_;
goto v___jp_1343_;
}
}
}
else
{
uint8_t v___x_1365_; 
v___x_1365_ = l_Lean_Expr_isErased(v_snd_1350_);
if (v___x_1365_ == 0)
{
lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; 
v___x_1366_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3___redArg___closed__1);
lean_inc(v_s_1332_);
v___x_1367_ = l_Lean_mkFVar(v_s_1332_);
lean_inc(v_idx_1334_);
lean_inc(v_structName_1333_);
v___x_1368_ = l_Lean_mkProj(v_structName_1333_, v_idx_1334_, v___x_1367_);
v___x_1369_ = l_Lean_indentExpr(v___x_1368_);
v___x_1370_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1370_, 0, v___x_1366_);
lean_ctor_set(v___x_1370_, 1, v___x_1369_);
v___x_1371_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg(v___x_1370_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_);
if (lean_obj_tag(v___x_1371_) == 0)
{
lean_object* v___x_1373_; 
lean_dec_ref_known(v___x_1371_, 1);
if (v_isShared_1353_ == 0)
{
lean_ctor_set(v___x_1352_, 0, v___x_1354_);
v___x_1373_ = v___x_1352_;
goto v_reusejp_1372_;
}
else
{
lean_object* v_reuseFailAlloc_1374_; 
v_reuseFailAlloc_1374_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1374_, 0, v___x_1354_);
lean_ctor_set(v_reuseFailAlloc_1374_, 1, v_snd_1350_);
v___x_1373_ = v_reuseFailAlloc_1374_;
goto v_reusejp_1372_;
}
v_reusejp_1372_:
{
v_a_1344_ = v___x_1373_;
goto v___jp_1343_;
}
}
else
{
lean_object* v_a_1375_; lean_object* v___x_1377_; uint8_t v_isShared_1378_; uint8_t v_isSharedCheck_1382_; 
lean_del_object(v___x_1352_);
lean_dec(v_snd_1350_);
lean_dec(v_a_1335_);
lean_dec(v_idx_1334_);
lean_dec(v_structName_1333_);
lean_dec(v_s_1332_);
v_a_1375_ = lean_ctor_get(v___x_1371_, 0);
v_isSharedCheck_1382_ = !lean_is_exclusive(v___x_1371_);
if (v_isSharedCheck_1382_ == 0)
{
v___x_1377_ = v___x_1371_;
v_isShared_1378_ = v_isSharedCheck_1382_;
goto v_resetjp_1376_;
}
else
{
lean_inc(v_a_1375_);
lean_dec(v___x_1371_);
v___x_1377_ = lean_box(0);
v_isShared_1378_ = v_isSharedCheck_1382_;
goto v_resetjp_1376_;
}
v_resetjp_1376_:
{
lean_object* v___x_1380_; 
if (v_isShared_1378_ == 0)
{
v___x_1380_ = v___x_1377_;
goto v_reusejp_1379_;
}
else
{
lean_object* v_reuseFailAlloc_1381_; 
v_reuseFailAlloc_1381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1381_, 0, v_a_1375_);
v___x_1380_ = v_reuseFailAlloc_1381_;
goto v_reusejp_1379_;
}
v_reusejp_1379_:
{
return v___x_1380_;
}
}
}
}
else
{
lean_object* v___x_1383_; lean_object* v___x_1385_; 
lean_dec(v_a_1335_);
lean_dec(v_idx_1334_);
lean_dec(v_structName_1333_);
lean_dec(v_s_1332_);
v___x_1383_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferForallType_go_spec__6___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferForallType_go_spec__6___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferForallType_go_spec__6___closed__0);
if (v_isShared_1353_ == 0)
{
lean_ctor_set(v___x_1352_, 0, v___x_1383_);
v___x_1385_ = v___x_1352_;
goto v_reusejp_1384_;
}
else
{
lean_object* v_reuseFailAlloc_1387_; 
v_reuseFailAlloc_1387_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1387_, 0, v___x_1383_);
lean_ctor_set(v_reuseFailAlloc_1387_, 1, v_snd_1350_);
v___x_1385_ = v_reuseFailAlloc_1387_;
goto v_reusejp_1384_;
}
v_reusejp_1384_:
{
lean_object* v___x_1386_; 
v___x_1386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1386_, 0, v___x_1385_);
return v___x_1386_;
}
}
}
}
}
v___jp_1343_:
{
lean_object* v___x_1345_; lean_object* v___x_1346_; 
v___x_1345_ = lean_unsigned_to_nat(1u);
v___x_1346_ = lean_nat_add(v_a_1335_, v___x_1345_);
lean_dec(v_a_1335_);
v_a_1335_ = v___x_1346_;
v_b_1336_ = v_a_1344_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3___redArg___boxed(lean_object* v_upperBound_1390_, lean_object* v_s_1391_, lean_object* v_structName_1392_, lean_object* v_idx_1393_, lean_object* v_a_1394_, lean_object* v_b_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_){
_start:
{
lean_object* v_res_1402_; 
v_res_1402_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3___redArg(v_upperBound_1390_, v_s_1391_, v_structName_1392_, v_idx_1393_, v_a_1394_, v_b_1395_, v___y_1396_, v___y_1397_, v___y_1398_, v___y_1399_, v___y_1400_);
lean_dec(v___y_1400_);
lean_dec_ref(v___y_1399_);
lean_dec(v___y_1398_);
lean_dec_ref(v___y_1397_);
lean_dec_ref(v___y_1396_);
lean_dec(v_upperBound_1390_);
return v_res_1402_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2___redArg(lean_object* v_upperBound_1403_, lean_object* v_s_1404_, lean_object* v_structName_1405_, lean_object* v_idx_1406_, lean_object* v_a_1407_, lean_object* v_b_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_){
_start:
{
lean_object* v_a_1416_; uint8_t v___x_1420_; 
v___x_1420_ = lean_nat_dec_lt(v_a_1407_, v_upperBound_1403_);
if (v___x_1420_ == 0)
{
lean_object* v___x_1421_; 
lean_dec(v_idx_1406_);
lean_dec(v_structName_1405_);
lean_dec(v_s_1404_);
v___x_1421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1421_, 0, v_b_1408_);
return v___x_1421_;
}
else
{
lean_object* v_snd_1422_; lean_object* v___x_1424_; uint8_t v_isShared_1425_; uint8_t v_isSharedCheck_1460_; 
v_snd_1422_ = lean_ctor_get(v_b_1408_, 1);
v_isSharedCheck_1460_ = !lean_is_exclusive(v_b_1408_);
if (v_isSharedCheck_1460_ == 0)
{
lean_object* v_unused_1461_; 
v_unused_1461_ = lean_ctor_get(v_b_1408_, 0);
lean_dec(v_unused_1461_);
v___x_1424_ = v_b_1408_;
v_isShared_1425_ = v_isSharedCheck_1460_;
goto v_resetjp_1423_;
}
else
{
lean_inc(v_snd_1422_);
lean_dec(v_b_1408_);
v___x_1424_ = lean_box(0);
v_isShared_1425_ = v_isSharedCheck_1460_;
goto v_resetjp_1423_;
}
v_resetjp_1423_:
{
lean_object* v___x_1426_; 
v___x_1426_ = lean_box(0);
if (lean_obj_tag(v_snd_1422_) == 7)
{
lean_object* v_body_1427_; uint8_t v___x_1428_; 
v_body_1427_ = lean_ctor_get(v_snd_1422_, 2);
lean_inc_ref(v_body_1427_);
lean_dec_ref_known(v_snd_1422_, 3);
v___x_1428_ = l_Lean_Expr_hasLooseBVars(v_body_1427_);
if (v___x_1428_ == 0)
{
lean_object* v___x_1430_; 
if (v_isShared_1425_ == 0)
{
lean_ctor_set(v___x_1424_, 1, v_body_1427_);
lean_ctor_set(v___x_1424_, 0, v___x_1426_);
v___x_1430_ = v___x_1424_;
goto v_reusejp_1429_;
}
else
{
lean_object* v_reuseFailAlloc_1431_; 
v_reuseFailAlloc_1431_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1431_, 0, v___x_1426_);
lean_ctor_set(v_reuseFailAlloc_1431_, 1, v_body_1427_);
v___x_1430_ = v_reuseFailAlloc_1431_;
goto v_reusejp_1429_;
}
v_reusejp_1429_:
{
v_a_1416_ = v___x_1430_;
goto v___jp_1415_;
}
}
else
{
lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1435_; 
v___x_1432_ = l_Lean_Compiler_LCNF_anyExpr;
v___x_1433_ = lean_expr_instantiate1(v_body_1427_, v___x_1432_);
lean_dec_ref(v_body_1427_);
if (v_isShared_1425_ == 0)
{
lean_ctor_set(v___x_1424_, 1, v___x_1433_);
lean_ctor_set(v___x_1424_, 0, v___x_1426_);
v___x_1435_ = v___x_1424_;
goto v_reusejp_1434_;
}
else
{
lean_object* v_reuseFailAlloc_1436_; 
v_reuseFailAlloc_1436_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1436_, 0, v___x_1426_);
lean_ctor_set(v_reuseFailAlloc_1436_, 1, v___x_1433_);
v___x_1435_ = v_reuseFailAlloc_1436_;
goto v_reusejp_1434_;
}
v_reusejp_1434_:
{
v_a_1416_ = v___x_1435_;
goto v___jp_1415_;
}
}
}
else
{
uint8_t v___x_1437_; 
v___x_1437_ = l_Lean_Expr_isErased(v_snd_1422_);
if (v___x_1437_ == 0)
{
lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; 
v___x_1438_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3___redArg___closed__1);
lean_inc(v_s_1404_);
v___x_1439_ = l_Lean_mkFVar(v_s_1404_);
lean_inc(v_idx_1406_);
lean_inc(v_structName_1405_);
v___x_1440_ = l_Lean_mkProj(v_structName_1405_, v_idx_1406_, v___x_1439_);
v___x_1441_ = l_Lean_indentExpr(v___x_1440_);
v___x_1442_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1442_, 0, v___x_1438_);
lean_ctor_set(v___x_1442_, 1, v___x_1441_);
v___x_1443_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg(v___x_1442_, v___y_1410_, v___y_1411_, v___y_1412_, v___y_1413_);
if (lean_obj_tag(v___x_1443_) == 0)
{
lean_object* v___x_1445_; 
lean_dec_ref_known(v___x_1443_, 1);
if (v_isShared_1425_ == 0)
{
lean_ctor_set(v___x_1424_, 0, v___x_1426_);
v___x_1445_ = v___x_1424_;
goto v_reusejp_1444_;
}
else
{
lean_object* v_reuseFailAlloc_1446_; 
v_reuseFailAlloc_1446_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1446_, 0, v___x_1426_);
lean_ctor_set(v_reuseFailAlloc_1446_, 1, v_snd_1422_);
v___x_1445_ = v_reuseFailAlloc_1446_;
goto v_reusejp_1444_;
}
v_reusejp_1444_:
{
v_a_1416_ = v___x_1445_;
goto v___jp_1415_;
}
}
else
{
lean_object* v_a_1447_; lean_object* v___x_1449_; uint8_t v_isShared_1450_; uint8_t v_isSharedCheck_1454_; 
lean_del_object(v___x_1424_);
lean_dec(v_snd_1422_);
lean_dec(v_idx_1406_);
lean_dec(v_structName_1405_);
lean_dec(v_s_1404_);
v_a_1447_ = lean_ctor_get(v___x_1443_, 0);
v_isSharedCheck_1454_ = !lean_is_exclusive(v___x_1443_);
if (v_isSharedCheck_1454_ == 0)
{
v___x_1449_ = v___x_1443_;
v_isShared_1450_ = v_isSharedCheck_1454_;
goto v_resetjp_1448_;
}
else
{
lean_inc(v_a_1447_);
lean_dec(v___x_1443_);
v___x_1449_ = lean_box(0);
v_isShared_1450_ = v_isSharedCheck_1454_;
goto v_resetjp_1448_;
}
v_resetjp_1448_:
{
lean_object* v___x_1452_; 
if (v_isShared_1450_ == 0)
{
v___x_1452_ = v___x_1449_;
goto v_reusejp_1451_;
}
else
{
lean_object* v_reuseFailAlloc_1453_; 
v_reuseFailAlloc_1453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1453_, 0, v_a_1447_);
v___x_1452_ = v_reuseFailAlloc_1453_;
goto v_reusejp_1451_;
}
v_reusejp_1451_:
{
return v___x_1452_;
}
}
}
}
else
{
lean_object* v___x_1455_; lean_object* v___x_1457_; 
lean_dec(v_idx_1406_);
lean_dec(v_structName_1405_);
lean_dec(v_s_1404_);
v___x_1455_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferForallType_go_spec__6___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferForallType_go_spec__6___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferForallType_go_spec__6___closed__0);
if (v_isShared_1425_ == 0)
{
lean_ctor_set(v___x_1424_, 0, v___x_1455_);
v___x_1457_ = v___x_1424_;
goto v_reusejp_1456_;
}
else
{
lean_object* v_reuseFailAlloc_1459_; 
v_reuseFailAlloc_1459_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1459_, 0, v___x_1455_);
lean_ctor_set(v_reuseFailAlloc_1459_, 1, v_snd_1422_);
v___x_1457_ = v_reuseFailAlloc_1459_;
goto v_reusejp_1456_;
}
v_reusejp_1456_:
{
lean_object* v___x_1458_; 
v___x_1458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1458_, 0, v___x_1457_);
return v___x_1458_;
}
}
}
}
}
v___jp_1415_:
{
lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; 
v___x_1417_ = lean_unsigned_to_nat(1u);
v___x_1418_ = lean_nat_add(v_a_1407_, v___x_1417_);
v___x_1419_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3___redArg(v_upperBound_1403_, v_s_1404_, v_structName_1405_, v_idx_1406_, v___x_1418_, v_a_1416_, v___y_1409_, v___y_1410_, v___y_1411_, v___y_1412_, v___y_1413_);
return v___x_1419_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2___redArg___boxed(lean_object* v_upperBound_1462_, lean_object* v_s_1463_, lean_object* v_structName_1464_, lean_object* v_idx_1465_, lean_object* v_a_1466_, lean_object* v_b_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_){
_start:
{
lean_object* v_res_1474_; 
v_res_1474_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2___redArg(v_upperBound_1462_, v_s_1463_, v_structName_1464_, v_idx_1465_, v_a_1466_, v_b_1467_, v___y_1468_, v___y_1469_, v___y_1470_, v___y_1471_, v___y_1472_);
lean_dec(v___y_1472_);
lean_dec_ref(v___y_1471_);
lean_dec(v___y_1470_);
lean_dec_ref(v___y_1469_);
lean_dec_ref(v___y_1468_);
lean_dec(v_a_1466_);
lean_dec(v_upperBound_1462_);
return v_res_1474_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__7___redArg(lean_object* v_ref_1475_, lean_object* v_msg_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_){
_start:
{
lean_object* v_toCold_1483_; lean_object* v_currRecDepth_1484_; lean_object* v_ref_1485_; uint16_t v_optionFlags_1486_; uint8_t v_suppressElabErrors_1487_; uint8_t v_isRecordingDeps_1488_; lean_object* v_ref_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; 
v_toCold_1483_ = lean_ctor_get(v___y_1480_, 0);
v_currRecDepth_1484_ = lean_ctor_get(v___y_1480_, 1);
v_ref_1485_ = lean_ctor_get(v___y_1480_, 2);
v_optionFlags_1486_ = lean_ctor_get_uint16(v___y_1480_, sizeof(void*)*3);
v_suppressElabErrors_1487_ = lean_ctor_get_uint8(v___y_1480_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1488_ = lean_ctor_get_uint8(v___y_1480_, sizeof(void*)*3 + 3);
v_ref_1489_ = l_Lean_replaceRef(v_ref_1475_, v_ref_1485_);
lean_inc(v_currRecDepth_1484_);
lean_inc_ref(v_toCold_1483_);
v___x_1490_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1490_, 0, v_toCold_1483_);
lean_ctor_set(v___x_1490_, 1, v_currRecDepth_1484_);
lean_ctor_set(v___x_1490_, 2, v_ref_1489_);
lean_ctor_set_uint16(v___x_1490_, sizeof(void*)*3, v_optionFlags_1486_);
lean_ctor_set_uint8(v___x_1490_, sizeof(void*)*3 + 2, v_suppressElabErrors_1487_);
lean_ctor_set_uint8(v___x_1490_, sizeof(void*)*3 + 3, v_isRecordingDeps_1488_);
v___x_1491_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg(v_msg_1476_, v___y_1478_, v___y_1479_, v___x_1490_, v___y_1481_);
lean_dec_ref_known(v___x_1490_, 3);
return v___x_1491_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__7___redArg___boxed(lean_object* v_ref_1492_, lean_object* v_msg_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_){
_start:
{
lean_object* v_res_1500_; 
v_res_1500_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__7___redArg(v_ref_1492_, v_msg_1493_, v___y_1494_, v___y_1495_, v___y_1496_, v___y_1497_, v___y_1498_);
lean_dec(v___y_1498_);
lean_dec_ref(v___y_1497_);
lean_dec(v___y_1496_);
lean_dec_ref(v___y_1495_);
lean_dec_ref(v___y_1494_);
lean_dec(v_ref_1492_);
return v_res_1500_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__0(void){
_start:
{
lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; 
v___x_1501_ = lean_box(1);
v___x_1502_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__3, &l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__3_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__3);
v___x_1503_ = lean_obj_once(&l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___closed__0, &l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___closed__0_once, _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___closed__0);
v___x_1504_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1504_, 0, v___x_1503_);
lean_ctor_set(v___x_1504_, 1, v___x_1502_);
lean_ctor_set(v___x_1504_, 2, v___x_1501_);
return v___x_1504_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__2(void){
_start:
{
lean_object* v___x_1506_; lean_object* v___x_1507_; 
v___x_1506_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__1));
v___x_1507_ = l_Lean_stringToMessageData(v___x_1506_);
return v___x_1507_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__4(void){
_start:
{
lean_object* v___x_1509_; lean_object* v___x_1510_; 
v___x_1509_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__3));
v___x_1510_ = l_Lean_stringToMessageData(v___x_1509_);
return v___x_1510_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__6(void){
_start:
{
lean_object* v___x_1512_; lean_object* v___x_1513_; 
v___x_1512_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__5));
v___x_1513_ = l_Lean_stringToMessageData(v___x_1512_);
return v___x_1513_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__8(void){
_start:
{
lean_object* v___x_1515_; lean_object* v___x_1516_; 
v___x_1515_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__7));
v___x_1516_ = l_Lean_stringToMessageData(v___x_1515_);
return v___x_1516_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__10(void){
_start:
{
lean_object* v___x_1518_; lean_object* v___x_1519_; 
v___x_1518_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__9));
v___x_1519_ = l_Lean_stringToMessageData(v___x_1518_);
return v___x_1519_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__12(void){
_start:
{
lean_object* v___x_1521_; lean_object* v___x_1522_; 
v___x_1521_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__11));
v___x_1522_ = l_Lean_stringToMessageData(v___x_1521_);
return v___x_1522_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__14(void){
_start:
{
lean_object* v___x_1524_; lean_object* v___x_1525_; 
v___x_1524_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__13));
v___x_1525_ = l_Lean_stringToMessageData(v___x_1524_);
return v___x_1525_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg(lean_object* v_msg_1526_, lean_object* v_declHint_1527_, lean_object* v___y_1528_){
_start:
{
lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v_env_1532_; uint8_t v___x_1533_; 
v___x_1530_ = lean_box(0);
v___x_1531_ = lean_st_ref_get(v___y_1528_);
v_env_1532_ = lean_ctor_get(v___x_1531_, 0);
lean_inc_ref(v_env_1532_);
lean_dec(v___x_1531_);
v___x_1533_ = l_Lean_Name_isAnonymous(v_declHint_1527_);
if (v___x_1533_ == 0)
{
uint8_t v_isExporting_1534_; 
v_isExporting_1534_ = lean_ctor_get_uint8(v_env_1532_, sizeof(void*)*13);
if (v_isExporting_1534_ == 0)
{
lean_object* v___x_1535_; 
lean_dec_ref(v_env_1532_);
lean_dec(v_declHint_1527_);
v___x_1535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1535_, 0, v_msg_1526_);
return v___x_1535_;
}
else
{
lean_object* v___x_1536_; uint8_t v___x_1537_; 
lean_inc_ref(v_env_1532_);
v___x_1536_ = l_Lean_Environment_setExporting(v_env_1532_, v___x_1533_);
lean_inc(v_declHint_1527_);
lean_inc_ref(v___x_1536_);
v___x_1537_ = l_Lean_Environment_contains(v___x_1536_, v_declHint_1527_, v_isExporting_1534_);
if (v___x_1537_ == 0)
{
lean_object* v___x_1538_; 
lean_dec_ref(v___x_1536_);
lean_dec_ref(v_env_1532_);
lean_dec(v_declHint_1527_);
v___x_1538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1538_, 0, v_msg_1526_);
return v___x_1538_;
}
else
{
lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v_c_1544_; lean_object* v___x_1545_; 
v___x_1539_ = lean_obj_once(&l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___closed__1, &l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___closed__1_once, _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___closed__1);
v___x_1540_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__0);
v___x_1541_ = l_Lean_Options_empty;
v___x_1542_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1542_, 0, v___x_1536_);
lean_ctor_set(v___x_1542_, 1, v___x_1539_);
lean_ctor_set(v___x_1542_, 2, v___x_1540_);
lean_ctor_set(v___x_1542_, 3, v___x_1541_);
lean_inc(v_declHint_1527_);
v___x_1543_ = l_Lean_MessageData_ofConstName(v_declHint_1527_, v___x_1533_);
v_c_1544_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1544_, 0, v___x_1542_);
lean_ctor_set(v_c_1544_, 1, v___x_1543_);
v___x_1545_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1532_, v_declHint_1527_);
if (lean_obj_tag(v___x_1545_) == 0)
{
lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; 
lean_dec_ref(v_env_1532_);
lean_dec(v_declHint_1527_);
v___x_1546_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__2);
v___x_1547_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1547_, 0, v___x_1546_);
lean_ctor_set(v___x_1547_, 1, v_c_1544_);
v___x_1548_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__4);
v___x_1549_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1549_, 0, v___x_1547_);
lean_ctor_set(v___x_1549_, 1, v___x_1548_);
v___x_1550_ = l_Lean_MessageData_note(v___x_1549_);
v___x_1551_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1551_, 0, v_msg_1526_);
lean_ctor_set(v___x_1551_, 1, v___x_1550_);
v___x_1552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1552_, 0, v___x_1551_);
return v___x_1552_;
}
else
{
lean_object* v_val_1553_; lean_object* v___x_1555_; uint8_t v_isShared_1556_; uint8_t v_isSharedCheck_1587_; 
v_val_1553_ = lean_ctor_get(v___x_1545_, 0);
v_isSharedCheck_1587_ = !lean_is_exclusive(v___x_1545_);
if (v_isSharedCheck_1587_ == 0)
{
v___x_1555_ = v___x_1545_;
v_isShared_1556_ = v_isSharedCheck_1587_;
goto v_resetjp_1554_;
}
else
{
lean_inc(v_val_1553_);
lean_dec(v___x_1545_);
v___x_1555_ = lean_box(0);
v_isShared_1556_ = v_isSharedCheck_1587_;
goto v_resetjp_1554_;
}
v_resetjp_1554_:
{
lean_object* v___x_1557_; lean_object* v_moduleNames_1558_; lean_object* v_mod_1559_; uint8_t v___x_1560_; 
v___x_1557_ = l_Lean_Environment_header(v_env_1532_);
lean_dec_ref(v_env_1532_);
v_moduleNames_1558_ = lean_ctor_get(v___x_1557_, 4);
lean_inc_ref(v_moduleNames_1558_);
lean_dec_ref(v___x_1557_);
v_mod_1559_ = lean_array_get(v___x_1530_, v_moduleNames_1558_, v_val_1553_);
lean_dec(v_val_1553_);
lean_dec_ref(v_moduleNames_1558_);
v___x_1560_ = l_Lean_isPrivateName(v_declHint_1527_);
lean_dec(v_declHint_1527_);
if (v___x_1560_ == 0)
{
lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1572_; 
v___x_1561_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__6, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__6_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__6);
v___x_1562_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1562_, 0, v___x_1561_);
lean_ctor_set(v___x_1562_, 1, v_c_1544_);
v___x_1563_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__8, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__8_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__8);
v___x_1564_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1564_, 0, v___x_1562_);
lean_ctor_set(v___x_1564_, 1, v___x_1563_);
v___x_1565_ = l_Lean_MessageData_ofName(v_mod_1559_);
v___x_1566_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1566_, 0, v___x_1564_);
lean_ctor_set(v___x_1566_, 1, v___x_1565_);
v___x_1567_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__10, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__10_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__10);
v___x_1568_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1568_, 0, v___x_1566_);
lean_ctor_set(v___x_1568_, 1, v___x_1567_);
v___x_1569_ = l_Lean_MessageData_note(v___x_1568_);
v___x_1570_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1570_, 0, v_msg_1526_);
lean_ctor_set(v___x_1570_, 1, v___x_1569_);
if (v_isShared_1556_ == 0)
{
lean_ctor_set_tag(v___x_1555_, 0);
lean_ctor_set(v___x_1555_, 0, v___x_1570_);
v___x_1572_ = v___x_1555_;
goto v_reusejp_1571_;
}
else
{
lean_object* v_reuseFailAlloc_1573_; 
v_reuseFailAlloc_1573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1573_, 0, v___x_1570_);
v___x_1572_ = v_reuseFailAlloc_1573_;
goto v_reusejp_1571_;
}
v_reusejp_1571_:
{
return v___x_1572_;
}
}
else
{
lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1585_; 
v___x_1574_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__2);
v___x_1575_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1575_, 0, v___x_1574_);
lean_ctor_set(v___x_1575_, 1, v_c_1544_);
v___x_1576_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__12, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__12_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__12);
v___x_1577_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1577_, 0, v___x_1575_);
lean_ctor_set(v___x_1577_, 1, v___x_1576_);
v___x_1578_ = l_Lean_MessageData_ofName(v_mod_1559_);
v___x_1579_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1579_, 0, v___x_1577_);
lean_ctor_set(v___x_1579_, 1, v___x_1578_);
v___x_1580_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__14, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__14_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__14);
v___x_1581_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1581_, 0, v___x_1579_);
lean_ctor_set(v___x_1581_, 1, v___x_1580_);
v___x_1582_ = l_Lean_MessageData_note(v___x_1581_);
v___x_1583_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1583_, 0, v_msg_1526_);
lean_ctor_set(v___x_1583_, 1, v___x_1582_);
if (v_isShared_1556_ == 0)
{
lean_ctor_set_tag(v___x_1555_, 0);
lean_ctor_set(v___x_1555_, 0, v___x_1583_);
v___x_1585_ = v___x_1555_;
goto v_reusejp_1584_;
}
else
{
lean_object* v_reuseFailAlloc_1586_; 
v_reuseFailAlloc_1586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1586_, 0, v___x_1583_);
v___x_1585_ = v_reuseFailAlloc_1586_;
goto v_reusejp_1584_;
}
v_reusejp_1584_:
{
return v___x_1585_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1588_; 
lean_dec_ref(v_env_1532_);
lean_dec(v_declHint_1527_);
v___x_1588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1588_, 0, v_msg_1526_);
return v___x_1588_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___boxed(lean_object* v_msg_1589_, lean_object* v_declHint_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_){
_start:
{
lean_object* v_res_1593_; 
v_res_1593_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg(v_msg_1589_, v_declHint_1590_, v___y_1591_);
lean_dec(v___y_1591_);
return v_res_1593_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6(lean_object* v_msg_1594_, lean_object* v_declHint_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_){
_start:
{
lean_object* v___x_1602_; lean_object* v_a_1603_; lean_object* v___x_1605_; uint8_t v_isShared_1606_; uint8_t v_isSharedCheck_1612_; 
v___x_1602_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg(v_msg_1594_, v_declHint_1595_, v___y_1600_);
v_a_1603_ = lean_ctor_get(v___x_1602_, 0);
v_isSharedCheck_1612_ = !lean_is_exclusive(v___x_1602_);
if (v_isSharedCheck_1612_ == 0)
{
v___x_1605_ = v___x_1602_;
v_isShared_1606_ = v_isSharedCheck_1612_;
goto v_resetjp_1604_;
}
else
{
lean_inc(v_a_1603_);
lean_dec(v___x_1602_);
v___x_1605_ = lean_box(0);
v_isShared_1606_ = v_isSharedCheck_1612_;
goto v_resetjp_1604_;
}
v_resetjp_1604_:
{
lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1610_; 
v___x_1607_ = l_Lean_unknownIdentifierMessageTag;
v___x_1608_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1608_, 0, v___x_1607_);
lean_ctor_set(v___x_1608_, 1, v_a_1603_);
if (v_isShared_1606_ == 0)
{
lean_ctor_set(v___x_1605_, 0, v___x_1608_);
v___x_1610_ = v___x_1605_;
goto v_reusejp_1609_;
}
else
{
lean_object* v_reuseFailAlloc_1611_; 
v_reuseFailAlloc_1611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1611_, 0, v___x_1608_);
v___x_1610_ = v_reuseFailAlloc_1611_;
goto v_reusejp_1609_;
}
v_reusejp_1609_:
{
return v___x_1610_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6___boxed(lean_object* v_msg_1613_, lean_object* v_declHint_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_){
_start:
{
lean_object* v_res_1621_; 
v_res_1621_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6(v_msg_1613_, v_declHint_1614_, v___y_1615_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_);
lean_dec(v___y_1619_);
lean_dec_ref(v___y_1618_);
lean_dec(v___y_1617_);
lean_dec_ref(v___y_1616_);
lean_dec_ref(v___y_1615_);
return v_res_1621_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4___redArg(lean_object* v_ref_1622_, lean_object* v_msg_1623_, lean_object* v_declHint_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_){
_start:
{
lean_object* v___x_1631_; lean_object* v_a_1632_; lean_object* v___x_1633_; 
v___x_1631_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6(v_msg_1623_, v_declHint_1624_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_);
v_a_1632_ = lean_ctor_get(v___x_1631_, 0);
lean_inc(v_a_1632_);
lean_dec_ref(v___x_1631_);
v___x_1633_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__7___redArg(v_ref_1622_, v_a_1632_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_);
return v___x_1633_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_ref_1634_, lean_object* v_msg_1635_, lean_object* v_declHint_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_){
_start:
{
lean_object* v_res_1643_; 
v_res_1643_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4___redArg(v_ref_1634_, v_msg_1635_, v_declHint_1636_, v___y_1637_, v___y_1638_, v___y_1639_, v___y_1640_, v___y_1641_);
lean_dec(v___y_1641_);
lean_dec_ref(v___y_1640_);
lean_dec(v___y_1639_);
lean_dec_ref(v___y_1638_);
lean_dec_ref(v___y_1637_);
lean_dec(v_ref_1634_);
return v_res_1643_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_1645_; lean_object* v___x_1646_; 
v___x_1645_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg___closed__0));
v___x_1646_ = l_Lean_stringToMessageData(v___x_1645_);
return v___x_1646_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_1648_; lean_object* v___x_1649_; 
v___x_1648_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg___closed__2));
v___x_1649_ = l_Lean_stringToMessageData(v___x_1648_);
return v___x_1649_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg(lean_object* v_ref_1650_, lean_object* v_constName_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_){
_start:
{
lean_object* v___x_1658_; uint8_t v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; 
v___x_1658_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg___closed__1);
v___x_1659_ = 0;
lean_inc(v_constName_1651_);
v___x_1660_ = l_Lean_MessageData_ofConstName(v_constName_1651_, v___x_1659_);
v___x_1661_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1661_, 0, v___x_1658_);
lean_ctor_set(v___x_1661_, 1, v___x_1660_);
v___x_1662_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg___closed__3);
v___x_1663_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1663_, 0, v___x_1661_);
lean_ctor_set(v___x_1663_, 1, v___x_1662_);
v___x_1664_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4___redArg(v_ref_1650_, v___x_1663_, v_constName_1651_, v___y_1652_, v___y_1653_, v___y_1654_, v___y_1655_, v___y_1656_);
return v___x_1664_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_ref_1665_, lean_object* v_constName_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_){
_start:
{
lean_object* v_res_1673_; 
v_res_1673_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg(v_ref_1665_, v_constName_1666_, v___y_1667_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_);
lean_dec(v___y_1671_);
lean_dec_ref(v___y_1670_);
lean_dec(v___y_1669_);
lean_dec_ref(v___y_1668_);
lean_dec_ref(v___y_1667_);
lean_dec(v_ref_1665_);
return v_res_1673_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1___redArg(lean_object* v_constName_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_){
_start:
{
lean_object* v_ref_1681_; lean_object* v___x_1682_; 
v_ref_1681_ = lean_ctor_get(v___y_1678_, 2);
v___x_1682_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg(v_ref_1681_, v_constName_1674_, v___y_1675_, v___y_1676_, v___y_1677_, v___y_1678_, v___y_1679_);
return v___x_1682_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1___redArg___boxed(lean_object* v_constName_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_){
_start:
{
lean_object* v_res_1690_; 
v_res_1690_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1___redArg(v_constName_1683_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_, v___y_1688_);
lean_dec(v___y_1688_);
lean_dec_ref(v___y_1687_);
lean_dec(v___y_1686_);
lean_dec_ref(v___y_1685_);
lean_dec_ref(v___y_1684_);
return v_res_1690_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1(lean_object* v_constName_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_){
_start:
{
lean_object* v___x_1698_; lean_object* v_env_1699_; uint8_t v___x_1700_; lean_object* v___x_1701_; 
v___x_1698_ = lean_st_ref_get(v___y_1696_);
v_env_1699_ = lean_ctor_get(v___x_1698_, 0);
lean_inc_ref(v_env_1699_);
lean_dec(v___x_1698_);
v___x_1700_ = 0;
lean_inc(v_constName_1691_);
v___x_1701_ = l_Lean_Environment_find_x3f(v_env_1699_, v_constName_1691_, v___x_1700_);
if (lean_obj_tag(v___x_1701_) == 0)
{
lean_object* v___x_1702_; 
v___x_1702_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1___redArg(v_constName_1691_, v___y_1692_, v___y_1693_, v___y_1694_, v___y_1695_, v___y_1696_);
return v___x_1702_;
}
else
{
lean_object* v_val_1703_; lean_object* v___x_1705_; uint8_t v_isShared_1706_; uint8_t v_isSharedCheck_1710_; 
lean_dec(v_constName_1691_);
v_val_1703_ = lean_ctor_get(v___x_1701_, 0);
v_isSharedCheck_1710_ = !lean_is_exclusive(v___x_1701_);
if (v_isSharedCheck_1710_ == 0)
{
v___x_1705_ = v___x_1701_;
v_isShared_1706_ = v_isSharedCheck_1710_;
goto v_resetjp_1704_;
}
else
{
lean_inc(v_val_1703_);
lean_dec(v___x_1701_);
v___x_1705_ = lean_box(0);
v_isShared_1706_ = v_isSharedCheck_1710_;
goto v_resetjp_1704_;
}
v_resetjp_1704_:
{
lean_object* v___x_1708_; 
if (v_isShared_1706_ == 0)
{
lean_ctor_set_tag(v___x_1705_, 0);
v___x_1708_ = v___x_1705_;
goto v_reusejp_1707_;
}
else
{
lean_object* v_reuseFailAlloc_1709_; 
v_reuseFailAlloc_1709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1709_, 0, v_val_1703_);
v___x_1708_ = v_reuseFailAlloc_1709_;
goto v_reusejp_1707_;
}
v_reusejp_1707_:
{
return v___x_1708_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1___boxed(lean_object* v_constName_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_){
_start:
{
lean_object* v_res_1718_; 
v_res_1718_ = l_Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1(v_constName_1711_, v___y_1712_, v___y_1713_, v___y_1714_, v___y_1715_, v___y_1716_);
lean_dec(v___y_1716_);
lean_dec_ref(v___y_1715_);
lean_dec(v___y_1714_);
lean_dec_ref(v___y_1713_);
lean_dec_ref(v___y_1712_);
return v_res_1718_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferProjType(lean_object* v_structName_1719_, lean_object* v_idx_1720_, lean_object* v_s_1721_, lean_object* v_a_1722_, lean_object* v_a_1723_, lean_object* v_a_1724_, lean_object* v_a_1725_, lean_object* v_a_1726_){
_start:
{
lean_object* v___y_1729_; lean_object* v___y_1730_; lean_object* v___y_1731_; lean_object* v___y_1732_; lean_object* v___y_1733_; lean_object* v___x_1740_; 
lean_inc(v_s_1721_);
v___x_1740_ = l_Lean_Compiler_LCNF_InferType_Pure_getType(v_s_1721_, v_a_1722_, v_a_1723_, v_a_1724_, v_a_1725_, v_a_1726_);
if (lean_obj_tag(v___x_1740_) == 0)
{
lean_object* v_a_1741_; lean_object* v___x_1743_; uint8_t v_isShared_1744_; uint8_t v_isSharedCheck_1836_; 
v_a_1741_ = lean_ctor_get(v___x_1740_, 0);
v_isSharedCheck_1836_ = !lean_is_exclusive(v___x_1740_);
if (v_isSharedCheck_1836_ == 0)
{
v___x_1743_ = v___x_1740_;
v_isShared_1744_ = v_isSharedCheck_1836_;
goto v_resetjp_1742_;
}
else
{
lean_inc(v_a_1741_);
lean_dec(v___x_1740_);
v___x_1743_ = lean_box(0);
v_isShared_1744_ = v_isSharedCheck_1836_;
goto v_resetjp_1742_;
}
v_resetjp_1742_:
{
lean_object* v___x_1745_; uint8_t v___x_1746_; 
v___x_1745_ = l_Lean_Expr_headBeta(v_a_1741_);
v___x_1746_ = l_Lean_Expr_isErased(v___x_1745_);
if (v___x_1746_ == 0)
{
uint8_t v___x_1747_; 
v___x_1747_ = l_Lean_Expr_isAny(v___x_1745_);
if (v___x_1747_ == 0)
{
lean_object* v___x_1748_; 
lean_del_object(v___x_1743_);
v___x_1748_ = l_Lean_Expr_getAppFn(v___x_1745_);
if (lean_obj_tag(v___x_1748_) == 4)
{
lean_object* v_declName_1749_; lean_object* v_us_1750_; lean_object* v___x_1751_; lean_object* v_env_1752_; lean_object* v___x_1753_; 
v_declName_1749_ = lean_ctor_get(v___x_1748_, 0);
lean_inc(v_declName_1749_);
v_us_1750_ = lean_ctor_get(v___x_1748_, 1);
lean_inc(v_us_1750_);
lean_dec_ref_known(v___x_1748_, 2);
v___x_1751_ = lean_st_ref_get(v_a_1726_);
v_env_1752_ = lean_ctor_get(v___x_1751_, 0);
lean_inc_ref(v_env_1752_);
lean_dec(v___x_1751_);
v___x_1753_ = l_Lean_Environment_find_x3f(v_env_1752_, v_declName_1749_, v___x_1747_);
if (lean_obj_tag(v___x_1753_) == 0)
{
lean_dec(v_us_1750_);
lean_dec_ref(v___x_1745_);
v___y_1729_ = v_a_1722_;
v___y_1730_ = v_a_1723_;
v___y_1731_ = v_a_1724_;
v___y_1732_ = v_a_1725_;
v___y_1733_ = v_a_1726_;
goto v___jp_1728_;
}
else
{
lean_object* v_val_1754_; 
v_val_1754_ = lean_ctor_get(v___x_1753_, 0);
lean_inc(v_val_1754_);
lean_dec_ref_known(v___x_1753_, 1);
if (lean_obj_tag(v_val_1754_) == 5)
{
lean_object* v_val_1755_; lean_object* v_ctors_1756_; 
v_val_1755_ = lean_ctor_get(v_val_1754_, 0);
lean_inc_ref(v_val_1755_);
lean_dec_ref_known(v_val_1754_, 1);
v_ctors_1756_ = lean_ctor_get(v_val_1755_, 4);
lean_inc(v_ctors_1756_);
if (lean_obj_tag(v_ctors_1756_) == 1)
{
lean_object* v_tail_1757_; 
v_tail_1757_ = lean_ctor_get(v_ctors_1756_, 1);
if (lean_obj_tag(v_tail_1757_) == 0)
{
lean_object* v_numParams_1758_; lean_object* v_numIndices_1759_; lean_object* v_head_1760_; lean_object* v___x_1762_; uint8_t v_isShared_1763_; uint8_t v_isSharedCheck_1826_; 
v_numParams_1758_ = lean_ctor_get(v_val_1755_, 1);
lean_inc(v_numParams_1758_);
v_numIndices_1759_ = lean_ctor_get(v_val_1755_, 2);
lean_inc(v_numIndices_1759_);
lean_dec_ref(v_val_1755_);
v_head_1760_ = lean_ctor_get(v_ctors_1756_, 0);
v_isSharedCheck_1826_ = !lean_is_exclusive(v_ctors_1756_);
if (v_isSharedCheck_1826_ == 0)
{
lean_object* v_unused_1827_; 
v_unused_1827_ = lean_ctor_get(v_ctors_1756_, 1);
lean_dec(v_unused_1827_);
v___x_1762_ = v_ctors_1756_;
v_isShared_1763_ = v_isSharedCheck_1826_;
goto v_resetjp_1761_;
}
else
{
lean_inc(v_head_1760_);
lean_dec(v_ctors_1756_);
v___x_1762_ = lean_box(0);
v_isShared_1763_ = v_isSharedCheck_1826_;
goto v_resetjp_1761_;
}
v_resetjp_1761_:
{
lean_object* v___x_1764_; 
v___x_1764_ = l_Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1(v_head_1760_, v_a_1722_, v_a_1723_, v_a_1724_, v_a_1725_, v_a_1726_);
if (lean_obj_tag(v___x_1764_) == 0)
{
lean_object* v_a_1765_; 
v_a_1765_ = lean_ctor_get(v___x_1764_, 0);
lean_inc(v_a_1765_);
lean_dec_ref_known(v___x_1764_, 1);
if (lean_obj_tag(v_a_1765_) == 6)
{
lean_object* v_val_1766_; lean_object* v_dummy_1767_; lean_object* v_nargs_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; uint8_t v___x_1775_; 
v_val_1766_ = lean_ctor_get(v_a_1765_, 0);
lean_inc_ref(v_val_1766_);
lean_dec_ref_known(v_a_1765_, 1);
v_dummy_1767_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_inferAppType___closed__0, &l_Lean_Compiler_LCNF_InferType_Pure_inferAppType___closed__0_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_inferAppType___closed__0);
v_nargs_1768_ = l_Lean_Expr_getAppNumArgs(v___x_1745_);
lean_inc(v_nargs_1768_);
v___x_1769_ = lean_mk_array(v_nargs_1768_, v_dummy_1767_);
v___x_1770_ = lean_unsigned_to_nat(1u);
v___x_1771_ = lean_nat_sub(v_nargs_1768_, v___x_1770_);
lean_dec(v_nargs_1768_);
v___x_1772_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v___x_1745_, v___x_1769_, v___x_1771_);
v___x_1773_ = lean_nat_add(v_numParams_1758_, v_numIndices_1759_);
lean_dec(v_numIndices_1759_);
v___x_1774_ = lean_array_get_size(v___x_1772_);
v___x_1775_ = lean_nat_dec_eq(v___x_1773_, v___x_1774_);
lean_dec(v___x_1773_);
if (v___x_1775_ == 0)
{
lean_dec_ref(v___x_1772_);
lean_dec_ref(v_val_1766_);
lean_del_object(v___x_1762_);
lean_dec(v_numParams_1758_);
lean_dec(v_us_1750_);
v___y_1729_ = v_a_1722_;
v___y_1730_ = v_a_1723_;
v___y_1731_ = v_a_1724_;
v___y_1732_ = v_a_1725_;
v___y_1733_ = v_a_1726_;
goto v___jp_1728_;
}
else
{
lean_object* v_toConstantVal_1776_; lean_object* v_name_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; 
v_toConstantVal_1776_ = lean_ctor_get(v_val_1766_, 0);
lean_inc_ref(v_toConstantVal_1776_);
lean_dec_ref(v_val_1766_);
v_name_1777_ = lean_ctor_get(v_toConstantVal_1776_, 0);
lean_inc(v_name_1777_);
lean_dec_ref(v_toConstantVal_1776_);
v___x_1778_ = l_Lean_mkConst(v_name_1777_, v_us_1750_);
v___x_1779_ = lean_unsigned_to_nat(0u);
v___x_1780_ = l_Array_toSubarray___redArg(v___x_1772_, v___x_1779_, v_numParams_1758_);
v___x_1781_ = l_Subarray_copy___redArg(v___x_1780_);
v___x_1782_ = l_Lean_mkAppN(v___x_1778_, v___x_1781_);
lean_dec_ref(v___x_1781_);
v___x_1783_ = l_Lean_Compiler_LCNF_InferType_Pure_inferAppType(v___x_1782_, v_a_1722_, v_a_1723_, v_a_1724_, v_a_1725_, v_a_1726_);
if (lean_obj_tag(v___x_1783_) == 0)
{
lean_object* v_a_1784_; lean_object* v___x_1785_; lean_object* v___x_1787_; 
v_a_1784_ = lean_ctor_get(v___x_1783_, 0);
lean_inc(v_a_1784_);
lean_dec_ref_known(v___x_1783_, 1);
v___x_1785_ = lean_box(0);
if (v_isShared_1763_ == 0)
{
lean_ctor_set_tag(v___x_1762_, 0);
lean_ctor_set(v___x_1762_, 1, v_a_1784_);
lean_ctor_set(v___x_1762_, 0, v___x_1785_);
v___x_1787_ = v___x_1762_;
goto v_reusejp_1786_;
}
else
{
lean_object* v_reuseFailAlloc_1817_; 
v_reuseFailAlloc_1817_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1817_, 0, v___x_1785_);
lean_ctor_set(v_reuseFailAlloc_1817_, 1, v_a_1784_);
v___x_1787_ = v_reuseFailAlloc_1817_;
goto v_reusejp_1786_;
}
v_reusejp_1786_:
{
lean_object* v___x_1788_; 
lean_inc(v_structName_1719_);
lean_inc(v_s_1721_);
lean_inc(v_idx_1720_);
v___x_1788_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2___redArg(v_idx_1720_, v_s_1721_, v_structName_1719_, v_idx_1720_, v___x_1779_, v___x_1787_, v_a_1722_, v_a_1723_, v_a_1724_, v_a_1725_, v_a_1726_);
if (lean_obj_tag(v___x_1788_) == 0)
{
lean_object* v_a_1789_; lean_object* v___x_1791_; uint8_t v_isShared_1792_; uint8_t v_isSharedCheck_1808_; 
v_a_1789_ = lean_ctor_get(v___x_1788_, 0);
v_isSharedCheck_1808_ = !lean_is_exclusive(v___x_1788_);
if (v_isSharedCheck_1808_ == 0)
{
v___x_1791_ = v___x_1788_;
v_isShared_1792_ = v_isSharedCheck_1808_;
goto v_resetjp_1790_;
}
else
{
lean_inc(v_a_1789_);
lean_dec(v___x_1788_);
v___x_1791_ = lean_box(0);
v_isShared_1792_ = v_isSharedCheck_1808_;
goto v_resetjp_1790_;
}
v_resetjp_1790_:
{
lean_object* v_fst_1793_; 
v_fst_1793_ = lean_ctor_get(v_a_1789_, 0);
if (lean_obj_tag(v_fst_1793_) == 0)
{
lean_object* v_snd_1794_; 
v_snd_1794_ = lean_ctor_get(v_a_1789_, 1);
lean_inc(v_snd_1794_);
lean_dec(v_a_1789_);
if (lean_obj_tag(v_snd_1794_) == 7)
{
lean_object* v_binderType_1795_; lean_object* v___x_1797_; 
lean_dec(v_s_1721_);
lean_dec(v_idx_1720_);
lean_dec(v_structName_1719_);
v_binderType_1795_ = lean_ctor_get(v_snd_1794_, 1);
lean_inc_ref(v_binderType_1795_);
lean_dec_ref_known(v_snd_1794_, 3);
if (v_isShared_1792_ == 0)
{
lean_ctor_set(v___x_1791_, 0, v_binderType_1795_);
v___x_1797_ = v___x_1791_;
goto v_reusejp_1796_;
}
else
{
lean_object* v_reuseFailAlloc_1798_; 
v_reuseFailAlloc_1798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1798_, 0, v_binderType_1795_);
v___x_1797_ = v_reuseFailAlloc_1798_;
goto v_reusejp_1796_;
}
v_reusejp_1796_:
{
return v___x_1797_;
}
}
else
{
uint8_t v___x_1799_; 
v___x_1799_ = l_Lean_Expr_isErased(v_snd_1794_);
lean_dec(v_snd_1794_);
if (v___x_1799_ == 0)
{
lean_del_object(v___x_1791_);
v___y_1729_ = v_a_1722_;
v___y_1730_ = v_a_1723_;
v___y_1731_ = v_a_1724_;
v___y_1732_ = v_a_1725_;
v___y_1733_ = v_a_1726_;
goto v___jp_1728_;
}
else
{
lean_object* v___x_1800_; lean_object* v___x_1802_; 
lean_dec(v_s_1721_);
lean_dec(v_idx_1720_);
lean_dec(v_structName_1719_);
v___x_1800_ = l_Lean_Compiler_LCNF_erasedExpr;
if (v_isShared_1792_ == 0)
{
lean_ctor_set(v___x_1791_, 0, v___x_1800_);
v___x_1802_ = v___x_1791_;
goto v_reusejp_1801_;
}
else
{
lean_object* v_reuseFailAlloc_1803_; 
v_reuseFailAlloc_1803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1803_, 0, v___x_1800_);
v___x_1802_ = v_reuseFailAlloc_1803_;
goto v_reusejp_1801_;
}
v_reusejp_1801_:
{
return v___x_1802_;
}
}
}
}
else
{
lean_object* v_val_1804_; lean_object* v___x_1806_; 
lean_inc_ref(v_fst_1793_);
lean_dec(v_a_1789_);
lean_dec(v_s_1721_);
lean_dec(v_idx_1720_);
lean_dec(v_structName_1719_);
v_val_1804_ = lean_ctor_get(v_fst_1793_, 0);
lean_inc(v_val_1804_);
lean_dec_ref_known(v_fst_1793_, 1);
if (v_isShared_1792_ == 0)
{
lean_ctor_set(v___x_1791_, 0, v_val_1804_);
v___x_1806_ = v___x_1791_;
goto v_reusejp_1805_;
}
else
{
lean_object* v_reuseFailAlloc_1807_; 
v_reuseFailAlloc_1807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1807_, 0, v_val_1804_);
v___x_1806_ = v_reuseFailAlloc_1807_;
goto v_reusejp_1805_;
}
v_reusejp_1805_:
{
return v___x_1806_;
}
}
}
}
else
{
lean_object* v_a_1809_; lean_object* v___x_1811_; uint8_t v_isShared_1812_; uint8_t v_isSharedCheck_1816_; 
lean_dec(v_s_1721_);
lean_dec(v_idx_1720_);
lean_dec(v_structName_1719_);
v_a_1809_ = lean_ctor_get(v___x_1788_, 0);
v_isSharedCheck_1816_ = !lean_is_exclusive(v___x_1788_);
if (v_isSharedCheck_1816_ == 0)
{
v___x_1811_ = v___x_1788_;
v_isShared_1812_ = v_isSharedCheck_1816_;
goto v_resetjp_1810_;
}
else
{
lean_inc(v_a_1809_);
lean_dec(v___x_1788_);
v___x_1811_ = lean_box(0);
v_isShared_1812_ = v_isSharedCheck_1816_;
goto v_resetjp_1810_;
}
v_resetjp_1810_:
{
lean_object* v___x_1814_; 
if (v_isShared_1812_ == 0)
{
v___x_1814_ = v___x_1811_;
goto v_reusejp_1813_;
}
else
{
lean_object* v_reuseFailAlloc_1815_; 
v_reuseFailAlloc_1815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1815_, 0, v_a_1809_);
v___x_1814_ = v_reuseFailAlloc_1815_;
goto v_reusejp_1813_;
}
v_reusejp_1813_:
{
return v___x_1814_;
}
}
}
}
}
else
{
lean_del_object(v___x_1762_);
lean_dec(v_s_1721_);
lean_dec(v_idx_1720_);
lean_dec(v_structName_1719_);
return v___x_1783_;
}
}
}
else
{
lean_dec(v_a_1765_);
lean_del_object(v___x_1762_);
lean_dec(v_numIndices_1759_);
lean_dec(v_numParams_1758_);
lean_dec(v_us_1750_);
lean_dec_ref(v___x_1745_);
v___y_1729_ = v_a_1722_;
v___y_1730_ = v_a_1723_;
v___y_1731_ = v_a_1724_;
v___y_1732_ = v_a_1725_;
v___y_1733_ = v_a_1726_;
goto v___jp_1728_;
}
}
else
{
lean_object* v_a_1818_; lean_object* v___x_1820_; uint8_t v_isShared_1821_; uint8_t v_isSharedCheck_1825_; 
lean_del_object(v___x_1762_);
lean_dec(v_numIndices_1759_);
lean_dec(v_numParams_1758_);
lean_dec(v_us_1750_);
lean_dec_ref(v___x_1745_);
lean_dec(v_s_1721_);
lean_dec(v_idx_1720_);
lean_dec(v_structName_1719_);
v_a_1818_ = lean_ctor_get(v___x_1764_, 0);
v_isSharedCheck_1825_ = !lean_is_exclusive(v___x_1764_);
if (v_isSharedCheck_1825_ == 0)
{
v___x_1820_ = v___x_1764_;
v_isShared_1821_ = v_isSharedCheck_1825_;
goto v_resetjp_1819_;
}
else
{
lean_inc(v_a_1818_);
lean_dec(v___x_1764_);
v___x_1820_ = lean_box(0);
v_isShared_1821_ = v_isSharedCheck_1825_;
goto v_resetjp_1819_;
}
v_resetjp_1819_:
{
lean_object* v___x_1823_; 
if (v_isShared_1821_ == 0)
{
v___x_1823_ = v___x_1820_;
goto v_reusejp_1822_;
}
else
{
lean_object* v_reuseFailAlloc_1824_; 
v_reuseFailAlloc_1824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1824_, 0, v_a_1818_);
v___x_1823_ = v_reuseFailAlloc_1824_;
goto v_reusejp_1822_;
}
v_reusejp_1822_:
{
return v___x_1823_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_ctors_1756_, 2);
lean_dec_ref(v_val_1755_);
lean_dec(v_us_1750_);
lean_dec_ref(v___x_1745_);
v___y_1729_ = v_a_1722_;
v___y_1730_ = v_a_1723_;
v___y_1731_ = v_a_1724_;
v___y_1732_ = v_a_1725_;
v___y_1733_ = v_a_1726_;
goto v___jp_1728_;
}
}
else
{
lean_dec(v_ctors_1756_);
lean_dec_ref(v_val_1755_);
lean_dec(v_us_1750_);
lean_dec_ref(v___x_1745_);
v___y_1729_ = v_a_1722_;
v___y_1730_ = v_a_1723_;
v___y_1731_ = v_a_1724_;
v___y_1732_ = v_a_1725_;
v___y_1733_ = v_a_1726_;
goto v___jp_1728_;
}
}
else
{
lean_dec(v_val_1754_);
lean_dec(v_us_1750_);
lean_dec_ref(v___x_1745_);
v___y_1729_ = v_a_1722_;
v___y_1730_ = v_a_1723_;
v___y_1731_ = v_a_1724_;
v___y_1732_ = v_a_1725_;
v___y_1733_ = v_a_1726_;
goto v___jp_1728_;
}
}
}
else
{
lean_dec_ref(v___x_1748_);
lean_dec_ref(v___x_1745_);
v___y_1729_ = v_a_1722_;
v___y_1730_ = v_a_1723_;
v___y_1731_ = v_a_1724_;
v___y_1732_ = v_a_1725_;
v___y_1733_ = v_a_1726_;
goto v___jp_1728_;
}
}
else
{
lean_object* v___x_1828_; lean_object* v___x_1830_; 
lean_dec_ref(v___x_1745_);
lean_dec(v_s_1721_);
lean_dec(v_idx_1720_);
lean_dec(v_structName_1719_);
v___x_1828_ = l_Lean_Compiler_LCNF_anyExpr;
if (v_isShared_1744_ == 0)
{
lean_ctor_set(v___x_1743_, 0, v___x_1828_);
v___x_1830_ = v___x_1743_;
goto v_reusejp_1829_;
}
else
{
lean_object* v_reuseFailAlloc_1831_; 
v_reuseFailAlloc_1831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1831_, 0, v___x_1828_);
v___x_1830_ = v_reuseFailAlloc_1831_;
goto v_reusejp_1829_;
}
v_reusejp_1829_:
{
return v___x_1830_;
}
}
}
else
{
lean_object* v___x_1832_; lean_object* v___x_1834_; 
lean_dec_ref(v___x_1745_);
lean_dec(v_s_1721_);
lean_dec(v_idx_1720_);
lean_dec(v_structName_1719_);
v___x_1832_ = l_Lean_Compiler_LCNF_erasedExpr;
if (v_isShared_1744_ == 0)
{
lean_ctor_set(v___x_1743_, 0, v___x_1832_);
v___x_1834_ = v___x_1743_;
goto v_reusejp_1833_;
}
else
{
lean_object* v_reuseFailAlloc_1835_; 
v_reuseFailAlloc_1835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1835_, 0, v___x_1832_);
v___x_1834_ = v_reuseFailAlloc_1835_;
goto v_reusejp_1833_;
}
v_reusejp_1833_:
{
return v___x_1834_;
}
}
}
}
else
{
lean_dec(v_s_1721_);
lean_dec(v_idx_1720_);
lean_dec(v_structName_1719_);
return v___x_1740_;
}
v___jp_1728_:
{
lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; 
v___x_1734_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3___redArg___closed__1);
v___x_1735_ = l_Lean_mkFVar(v_s_1721_);
v___x_1736_ = l_Lean_mkProj(v_structName_1719_, v_idx_1720_, v___x_1735_);
v___x_1737_ = l_Lean_indentExpr(v___x_1736_);
v___x_1738_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1738_, 0, v___x_1734_);
lean_ctor_set(v___x_1738_, 1, v___x_1737_);
v___x_1739_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg(v___x_1738_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_);
return v___x_1739_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferProjType___boxed(lean_object* v_structName_1837_, lean_object* v_idx_1838_, lean_object* v_s_1839_, lean_object* v_a_1840_, lean_object* v_a_1841_, lean_object* v_a_1842_, lean_object* v_a_1843_, lean_object* v_a_1844_, lean_object* v_a_1845_){
_start:
{
lean_object* v_res_1846_; 
v_res_1846_ = l_Lean_Compiler_LCNF_InferType_Pure_inferProjType(v_structName_1837_, v_idx_1838_, v_s_1839_, v_a_1840_, v_a_1841_, v_a_1842_, v_a_1843_, v_a_1844_);
lean_dec(v_a_1844_);
lean_dec_ref(v_a_1843_);
lean_dec(v_a_1842_);
lean_dec_ref(v_a_1841_);
lean_dec_ref(v_a_1840_);
return v_res_1846_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2(lean_object* v_upperBound_1847_, lean_object* v_s_1848_, lean_object* v_structName_1849_, lean_object* v_idx_1850_, lean_object* v_inst_1851_, lean_object* v_R_1852_, lean_object* v_a_1853_, lean_object* v_b_1854_, lean_object* v_c_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_){
_start:
{
lean_object* v___x_1862_; 
v___x_1862_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2___redArg(v_upperBound_1847_, v_s_1848_, v_structName_1849_, v_idx_1850_, v_a_1853_, v_b_1854_, v___y_1856_, v___y_1857_, v___y_1858_, v___y_1859_, v___y_1860_);
return v___x_1862_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2___boxed(lean_object* v_upperBound_1863_, lean_object* v_s_1864_, lean_object* v_structName_1865_, lean_object* v_idx_1866_, lean_object* v_inst_1867_, lean_object* v_R_1868_, lean_object* v_a_1869_, lean_object* v_b_1870_, lean_object* v_c_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_){
_start:
{
lean_object* v_res_1878_; 
v_res_1878_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2(v_upperBound_1863_, v_s_1864_, v_structName_1865_, v_idx_1866_, v_inst_1867_, v_R_1868_, v_a_1869_, v_b_1870_, v_c_1871_, v___y_1872_, v___y_1873_, v___y_1874_, v___y_1875_, v___y_1876_);
lean_dec(v___y_1876_);
lean_dec_ref(v___y_1875_);
lean_dec(v___y_1874_);
lean_dec_ref(v___y_1873_);
lean_dec_ref(v___y_1872_);
lean_dec(v_a_1869_);
lean_dec(v_upperBound_1863_);
return v_res_1878_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1(lean_object* v_00_u03b1_1879_, lean_object* v_constName_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_){
_start:
{
lean_object* v___x_1887_; 
v___x_1887_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1___redArg(v_constName_1880_, v___y_1881_, v___y_1882_, v___y_1883_, v___y_1884_, v___y_1885_);
return v___x_1887_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1___boxed(lean_object* v_00_u03b1_1888_, lean_object* v_constName_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_){
_start:
{
lean_object* v_res_1896_; 
v_res_1896_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1(v_00_u03b1_1888_, v_constName_1889_, v___y_1890_, v___y_1891_, v___y_1892_, v___y_1893_, v___y_1894_);
lean_dec(v___y_1894_);
lean_dec_ref(v___y_1893_);
lean_dec(v___y_1892_);
lean_dec_ref(v___y_1891_);
lean_dec_ref(v___y_1890_);
return v_res_1896_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3(lean_object* v_upperBound_1897_, lean_object* v_s_1898_, lean_object* v_structName_1899_, lean_object* v_idx_1900_, lean_object* v_inst_1901_, lean_object* v_R_1902_, lean_object* v_a_1903_, lean_object* v_b_1904_, lean_object* v_c_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_){
_start:
{
lean_object* v___x_1912_; 
v___x_1912_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3___redArg(v_upperBound_1897_, v_s_1898_, v_structName_1899_, v_idx_1900_, v_a_1903_, v_b_1904_, v___y_1906_, v___y_1907_, v___y_1908_, v___y_1909_, v___y_1910_);
return v___x_1912_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3___boxed(lean_object* v_upperBound_1913_, lean_object* v_s_1914_, lean_object* v_structName_1915_, lean_object* v_idx_1916_, lean_object* v_inst_1917_, lean_object* v_R_1918_, lean_object* v_a_1919_, lean_object* v_b_1920_, lean_object* v_c_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_){
_start:
{
lean_object* v_res_1928_; 
v_res_1928_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3(v_upperBound_1913_, v_s_1914_, v_structName_1915_, v_idx_1916_, v_inst_1917_, v_R_1918_, v_a_1919_, v_b_1920_, v_c_1921_, v___y_1922_, v___y_1923_, v___y_1924_, v___y_1925_, v___y_1926_);
lean_dec(v___y_1926_);
lean_dec_ref(v___y_1925_);
lean_dec(v___y_1924_);
lean_dec_ref(v___y_1923_);
lean_dec_ref(v___y_1922_);
lean_dec(v_upperBound_1913_);
return v_res_1928_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2(lean_object* v_00_u03b1_1929_, lean_object* v_ref_1930_, lean_object* v_constName_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_){
_start:
{
lean_object* v___x_1938_; 
v___x_1938_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg(v_ref_1930_, v_constName_1931_, v___y_1932_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_);
return v___x_1938_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___boxed(lean_object* v_00_u03b1_1939_, lean_object* v_ref_1940_, lean_object* v_constName_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_){
_start:
{
lean_object* v_res_1948_; 
v_res_1948_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2(v_00_u03b1_1939_, v_ref_1940_, v_constName_1941_, v___y_1942_, v___y_1943_, v___y_1944_, v___y_1945_, v___y_1946_);
lean_dec(v___y_1946_);
lean_dec_ref(v___y_1945_);
lean_dec(v___y_1944_);
lean_dec_ref(v___y_1943_);
lean_dec_ref(v___y_1942_);
lean_dec(v_ref_1940_);
return v_res_1948_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4(lean_object* v_00_u03b1_1949_, lean_object* v_ref_1950_, lean_object* v_msg_1951_, lean_object* v_declHint_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_){
_start:
{
lean_object* v___x_1959_; 
v___x_1959_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4___redArg(v_ref_1950_, v_msg_1951_, v_declHint_1952_, v___y_1953_, v___y_1954_, v___y_1955_, v___y_1956_, v___y_1957_);
return v___x_1959_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b1_1960_, lean_object* v_ref_1961_, lean_object* v_msg_1962_, lean_object* v_declHint_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_){
_start:
{
lean_object* v_res_1970_; 
v_res_1970_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4(v_00_u03b1_1960_, v_ref_1961_, v_msg_1962_, v_declHint_1963_, v___y_1964_, v___y_1965_, v___y_1966_, v___y_1967_, v___y_1968_);
lean_dec(v___y_1968_);
lean_dec_ref(v___y_1967_);
lean_dec(v___y_1966_);
lean_dec_ref(v___y_1965_);
lean_dec_ref(v___y_1964_);
lean_dec(v_ref_1961_);
return v_res_1970_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7(lean_object* v_msg_1971_, lean_object* v_declHint_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_){
_start:
{
lean_object* v___x_1979_; 
v___x_1979_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg(v_msg_1971_, v_declHint_1972_, v___y_1977_);
return v___x_1979_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___boxed(lean_object* v_msg_1980_, lean_object* v_declHint_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_){
_start:
{
lean_object* v_res_1988_; 
v_res_1988_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7(v_msg_1980_, v_declHint_1981_, v___y_1982_, v___y_1983_, v___y_1984_, v___y_1985_, v___y_1986_);
lean_dec(v___y_1986_);
lean_dec_ref(v___y_1985_);
lean_dec(v___y_1984_);
lean_dec_ref(v___y_1983_);
lean_dec_ref(v___y_1982_);
return v_res_1988_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__7(lean_object* v_00_u03b1_1989_, lean_object* v_ref_1990_, lean_object* v_msg_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_){
_start:
{
lean_object* v___x_1998_; 
v___x_1998_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__7___redArg(v_ref_1990_, v_msg_1991_, v___y_1992_, v___y_1993_, v___y_1994_, v___y_1995_, v___y_1996_);
return v___x_1998_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__7___boxed(lean_object* v_00_u03b1_1999_, lean_object* v_ref_2000_, lean_object* v_msg_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_){
_start:
{
lean_object* v_res_2008_; 
v_res_2008_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__7(v_00_u03b1_1999_, v_ref_2000_, v_msg_2001_, v___y_2002_, v___y_2003_, v___y_2004_, v___y_2005_, v___y_2006_);
lean_dec(v___y_2006_);
lean_dec_ref(v___y_2005_);
lean_dec(v___y_2004_);
lean_dec_ref(v___y_2003_);
lean_dec_ref(v___y_2002_);
lean_dec(v_ref_2000_);
return v_res_2008_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferLetValueType(lean_object* v_e_2009_, lean_object* v_a_2010_, lean_object* v_a_2011_, lean_object* v_a_2012_, lean_object* v_a_2013_, lean_object* v_a_2014_){
_start:
{
switch(lean_obj_tag(v_e_2009_))
{
case 0:
{
lean_object* v_value_2016_; lean_object* v___x_2018_; uint8_t v_isShared_2019_; uint8_t v_isSharedCheck_2024_; 
v_value_2016_ = lean_ctor_get(v_e_2009_, 0);
v_isSharedCheck_2024_ = !lean_is_exclusive(v_e_2009_);
if (v_isSharedCheck_2024_ == 0)
{
v___x_2018_ = v_e_2009_;
v_isShared_2019_ = v_isSharedCheck_2024_;
goto v_resetjp_2017_;
}
else
{
lean_inc(v_value_2016_);
lean_dec(v_e_2009_);
v___x_2018_ = lean_box(0);
v_isShared_2019_ = v_isSharedCheck_2024_;
goto v_resetjp_2017_;
}
v_resetjp_2017_:
{
lean_object* v___x_2020_; lean_object* v___x_2022_; 
v___x_2020_ = l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType(v_value_2016_);
lean_dec_ref(v_value_2016_);
if (v_isShared_2019_ == 0)
{
lean_ctor_set(v___x_2018_, 0, v___x_2020_);
v___x_2022_ = v___x_2018_;
goto v_reusejp_2021_;
}
else
{
lean_object* v_reuseFailAlloc_2023_; 
v_reuseFailAlloc_2023_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2023_, 0, v___x_2020_);
v___x_2022_ = v_reuseFailAlloc_2023_;
goto v_reusejp_2021_;
}
v_reusejp_2021_:
{
return v___x_2022_;
}
}
}
case 1:
{
lean_object* v___x_2025_; lean_object* v___x_2026_; 
v___x_2025_ = l_Lean_Compiler_LCNF_erasedExpr;
v___x_2026_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2026_, 0, v___x_2025_);
return v___x_2026_;
}
case 2:
{
lean_object* v_typeName_2027_; lean_object* v_idx_2028_; lean_object* v_struct_2029_; lean_object* v___x_2030_; 
v_typeName_2027_ = lean_ctor_get(v_e_2009_, 0);
lean_inc(v_typeName_2027_);
v_idx_2028_ = lean_ctor_get(v_e_2009_, 1);
lean_inc(v_idx_2028_);
v_struct_2029_ = lean_ctor_get(v_e_2009_, 2);
lean_inc(v_struct_2029_);
lean_dec_ref_known(v_e_2009_, 3);
v___x_2030_ = l_Lean_Compiler_LCNF_InferType_Pure_inferProjType(v_typeName_2027_, v_idx_2028_, v_struct_2029_, v_a_2010_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_);
return v___x_2030_;
}
case 3:
{
lean_object* v_declName_2031_; lean_object* v_us_2032_; lean_object* v_args_2033_; lean_object* v___x_2034_; 
v_declName_2031_ = lean_ctor_get(v_e_2009_, 0);
lean_inc(v_declName_2031_);
v_us_2032_ = lean_ctor_get(v_e_2009_, 1);
lean_inc(v_us_2032_);
v_args_2033_ = lean_ctor_get(v_e_2009_, 2);
lean_inc_ref(v_args_2033_);
lean_dec_ref_known(v_e_2009_, 3);
v___x_2034_ = l_Lean_Compiler_LCNF_InferType_Pure_inferConstType(v_declName_2031_, v_us_2032_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_);
if (lean_obj_tag(v___x_2034_) == 0)
{
lean_object* v_a_2035_; lean_object* v___x_2036_; 
v_a_2035_ = lean_ctor_get(v___x_2034_, 0);
lean_inc(v_a_2035_);
lean_dec_ref_known(v___x_2034_, 1);
v___x_2036_ = l_Lean_Compiler_LCNF_InferType_Pure_inferAppTypeCore(v_a_2035_, v_args_2033_, v_a_2010_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_);
return v___x_2036_;
}
else
{
lean_dec_ref(v_args_2033_);
return v___x_2034_;
}
}
default: 
{
lean_object* v_fvarId_2037_; lean_object* v_args_2038_; lean_object* v___x_2039_; 
v_fvarId_2037_ = lean_ctor_get(v_e_2009_, 0);
lean_inc(v_fvarId_2037_);
v_args_2038_ = lean_ctor_get(v_e_2009_, 1);
lean_inc_ref(v_args_2038_);
lean_dec_ref_known(v_e_2009_, 2);
v___x_2039_ = l_Lean_Compiler_LCNF_InferType_Pure_getType(v_fvarId_2037_, v_a_2010_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_);
if (lean_obj_tag(v___x_2039_) == 0)
{
lean_object* v_a_2040_; lean_object* v___x_2041_; 
v_a_2040_ = lean_ctor_get(v___x_2039_, 0);
lean_inc(v_a_2040_);
lean_dec_ref_known(v___x_2039_, 1);
v___x_2041_ = l_Lean_Compiler_LCNF_InferType_Pure_inferAppTypeCore(v_a_2040_, v_args_2038_, v_a_2010_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_);
return v___x_2041_;
}
else
{
lean_dec_ref(v_args_2038_);
return v___x_2039_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferLetValueType___boxed(lean_object* v_e_2042_, lean_object* v_a_2043_, lean_object* v_a_2044_, lean_object* v_a_2045_, lean_object* v_a_2046_, lean_object* v_a_2047_, lean_object* v_a_2048_){
_start:
{
lean_object* v_res_2049_; 
v_res_2049_ = l_Lean_Compiler_LCNF_InferType_Pure_inferLetValueType(v_e_2042_, v_a_2043_, v_a_2044_, v_a_2045_, v_a_2046_, v_a_2047_);
lean_dec(v_a_2047_);
lean_dec_ref(v_a_2046_);
lean_dec(v_a_2045_);
lean_dec_ref(v_a_2044_);
lean_dec_ref(v_a_2043_);
return v_res_2049_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inferType(lean_object* v_e_2050_, lean_object* v_a_2051_, lean_object* v_a_2052_, lean_object* v_a_2053_, lean_object* v_a_2054_){
_start:
{
lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; 
v___x_2056_ = lean_unsigned_to_nat(32u);
v___x_2057_ = lean_mk_empty_array_with_capacity(v___x_2056_);
lean_dec_ref(v___x_2057_);
v___x_2058_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4, &l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4);
v___x_2059_ = l_Lean_Compiler_LCNF_InferType_Pure_inferType(v_e_2050_, v___x_2058_, v_a_2051_, v_a_2052_, v_a_2053_, v_a_2054_);
return v___x_2059_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inferType___boxed(lean_object* v_e_2060_, lean_object* v_a_2061_, lean_object* v_a_2062_, lean_object* v_a_2063_, lean_object* v_a_2064_, lean_object* v_a_2065_){
_start:
{
lean_object* v_res_2066_; 
v_res_2066_ = l_Lean_Compiler_LCNF_inferType(v_e_2060_, v_a_2061_, v_a_2062_, v_a_2063_, v_a_2064_);
lean_dec(v_a_2064_);
lean_dec_ref(v_a_2063_);
lean_dec(v_a_2062_);
lean_dec_ref(v_a_2061_);
return v_res_2066_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_inferAppType_spec__0(lean_object* v_msg_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_){
_start:
{
lean_object* v___x_2073_; lean_object* v_toApplicative_2074_; lean_object* v_toFunctor_2075_; lean_object* v_toSeq_2076_; lean_object* v_toSeqLeft_2077_; lean_object* v_toSeqRight_2078_; lean_object* v___f_2079_; lean_object* v___f_2080_; lean_object* v___f_2081_; lean_object* v___f_2082_; lean_object* v___x_2083_; lean_object* v___f_2084_; lean_object* v___f_2085_; lean_object* v___f_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___f_2092_; lean_object* v___x_148__overap_2093_; lean_object* v___x_2094_; 
v___x_2073_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__1, &l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__1);
v_toApplicative_2074_ = lean_ctor_get(v___x_2073_, 0);
v_toFunctor_2075_ = lean_ctor_get(v_toApplicative_2074_, 0);
v_toSeq_2076_ = lean_ctor_get(v_toApplicative_2074_, 2);
v_toSeqLeft_2077_ = lean_ctor_get(v_toApplicative_2074_, 3);
v_toSeqRight_2078_ = lean_ctor_get(v_toApplicative_2074_, 4);
v___f_2079_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__2));
v___f_2080_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_2075_, 2);
v___f_2081_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2081_, 0, v_toFunctor_2075_);
v___f_2082_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2082_, 0, v_toFunctor_2075_);
v___x_2083_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2083_, 0, v___f_2081_);
lean_ctor_set(v___x_2083_, 1, v___f_2082_);
lean_inc(v_toSeqRight_2078_);
v___f_2084_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2084_, 0, v_toSeqRight_2078_);
lean_inc(v_toSeqLeft_2077_);
v___f_2085_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2085_, 0, v_toSeqLeft_2077_);
lean_inc(v_toSeq_2076_);
v___f_2086_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2086_, 0, v_toSeq_2076_);
v___x_2087_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2087_, 0, v___x_2083_);
lean_ctor_set(v___x_2087_, 1, v___f_2079_);
lean_ctor_set(v___x_2087_, 2, v___f_2086_);
lean_ctor_set(v___x_2087_, 3, v___f_2085_);
lean_ctor_set(v___x_2087_, 4, v___f_2084_);
v___x_2088_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2088_, 0, v___x_2087_);
lean_ctor_set(v___x_2088_, 1, v___f_2080_);
v___x_2089_ = l_StateRefT_x27_instMonad___redArg(v___x_2088_);
v___x_2090_ = l_Lean_instInhabitedExpr;
v___x_2091_ = l_instInhabitedOfMonad___redArg(v___x_2089_, v___x_2090_);
v___f_2092_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2092_, 0, v___x_2091_);
v___x_148__overap_2093_ = lean_panic_fn_borrowed(v___f_2092_, v_msg_2067_);
lean_dec_ref(v___f_2092_);
lean_inc(v___y_2071_);
lean_inc_ref(v___y_2070_);
lean_inc(v___y_2069_);
lean_inc_ref(v___y_2068_);
v___x_2094_ = lean_apply_5(v___x_148__overap_2093_, v___y_2068_, v___y_2069_, v___y_2070_, v___y_2071_, lean_box(0));
return v___x_2094_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_inferAppType_spec__0___boxed(lean_object* v_msg_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_){
_start:
{
lean_object* v_res_2101_; 
v_res_2101_ = l_panic___at___00Lean_Compiler_LCNF_inferAppType_spec__0(v_msg_2095_, v___y_2096_, v___y_2097_, v___y_2098_, v___y_2099_);
lean_dec(v___y_2099_);
lean_dec_ref(v___y_2098_);
lean_dec(v___y_2097_);
lean_dec_ref(v___y_2096_);
return v_res_2101_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_inferAppType___closed__2(void){
_start:
{
lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; 
v___x_2104_ = ((lean_object*)(l_Lean_Compiler_LCNF_inferAppType___closed__1));
v___x_2105_ = lean_unsigned_to_nat(15u);
v___x_2106_ = lean_unsigned_to_nat(258u);
v___x_2107_ = ((lean_object*)(l_Lean_Compiler_LCNF_inferAppType___closed__0));
v___x_2108_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_inferType___closed__0));
v___x_2109_ = l_mkPanicMessageWithDecl(v___x_2108_, v___x_2107_, v___x_2106_, v___x_2105_, v___x_2104_);
return v___x_2109_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inferAppType(uint8_t v_pu_2110_, lean_object* v_fnType_2111_, lean_object* v_args_2112_, lean_object* v_a_2113_, lean_object* v_a_2114_, lean_object* v_a_2115_, lean_object* v_a_2116_){
_start:
{
if (v_pu_2110_ == 0)
{
lean_object* v___x_2118_; lean_object* v___x_2119_; 
v___x_2118_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4, &l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4);
v___x_2119_ = l_Lean_Compiler_LCNF_InferType_Pure_inferAppTypeCore(v_fnType_2111_, v_args_2112_, v___x_2118_, v_a_2113_, v_a_2114_, v_a_2115_, v_a_2116_);
return v___x_2119_;
}
else
{
lean_object* v___x_2120_; lean_object* v___x_2121_; 
lean_dec_ref(v_args_2112_);
lean_dec_ref(v_fnType_2111_);
v___x_2120_ = lean_obj_once(&l_Lean_Compiler_LCNF_inferAppType___closed__2, &l_Lean_Compiler_LCNF_inferAppType___closed__2_once, _init_l_Lean_Compiler_LCNF_inferAppType___closed__2);
v___x_2121_ = l_panic___at___00Lean_Compiler_LCNF_inferAppType_spec__0(v___x_2120_, v_a_2113_, v_a_2114_, v_a_2115_, v_a_2116_);
return v___x_2121_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inferAppType___boxed(lean_object* v_pu_2122_, lean_object* v_fnType_2123_, lean_object* v_args_2124_, lean_object* v_a_2125_, lean_object* v_a_2126_, lean_object* v_a_2127_, lean_object* v_a_2128_, lean_object* v_a_2129_){
_start:
{
uint8_t v_pu_boxed_2130_; lean_object* v_res_2131_; 
v_pu_boxed_2130_ = lean_unbox(v_pu_2122_);
v_res_2131_ = l_Lean_Compiler_LCNF_inferAppType(v_pu_boxed_2130_, v_fnType_2123_, v_args_2124_, v_a_2125_, v_a_2126_, v_a_2127_, v_a_2128_);
lean_dec(v_a_2128_);
lean_dec_ref(v_a_2127_);
lean_dec(v_a_2126_);
lean_dec_ref(v_a_2125_);
return v_res_2131_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Arg_inferType___closed__1(void){
_start:
{
lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; 
v___x_2133_ = ((lean_object*)(l_Lean_Compiler_LCNF_inferAppType___closed__1));
v___x_2134_ = lean_unsigned_to_nat(15u);
v___x_2135_ = lean_unsigned_to_nat(263u);
v___x_2136_ = ((lean_object*)(l_Lean_Compiler_LCNF_Arg_inferType___closed__0));
v___x_2137_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_inferType___closed__0));
v___x_2138_ = l_mkPanicMessageWithDecl(v___x_2137_, v___x_2136_, v___x_2135_, v___x_2134_, v___x_2133_);
return v___x_2138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_inferType(uint8_t v_pu_2139_, lean_object* v_arg_2140_, lean_object* v_a_2141_, lean_object* v_a_2142_, lean_object* v_a_2143_, lean_object* v_a_2144_){
_start:
{
if (v_pu_2139_ == 0)
{
lean_object* v___x_2146_; lean_object* v___x_2147_; 
v___x_2146_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4, &l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4);
v___x_2147_ = l_Lean_Compiler_LCNF_InferType_Pure_inferArgType(v_arg_2140_, v___x_2146_, v_a_2141_, v_a_2142_, v_a_2143_, v_a_2144_);
return v___x_2147_;
}
else
{
lean_object* v___x_2148_; lean_object* v___x_2149_; 
lean_dec(v_arg_2140_);
v___x_2148_ = lean_obj_once(&l_Lean_Compiler_LCNF_Arg_inferType___closed__1, &l_Lean_Compiler_LCNF_Arg_inferType___closed__1_once, _init_l_Lean_Compiler_LCNF_Arg_inferType___closed__1);
v___x_2149_ = l_panic___at___00Lean_Compiler_LCNF_inferAppType_spec__0(v___x_2148_, v_a_2141_, v_a_2142_, v_a_2143_, v_a_2144_);
return v___x_2149_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_inferType___boxed(lean_object* v_pu_2150_, lean_object* v_arg_2151_, lean_object* v_a_2152_, lean_object* v_a_2153_, lean_object* v_a_2154_, lean_object* v_a_2155_, lean_object* v_a_2156_){
_start:
{
uint8_t v_pu_boxed_2157_; lean_object* v_res_2158_; 
v_pu_boxed_2157_ = lean_unbox(v_pu_2150_);
v_res_2158_ = l_Lean_Compiler_LCNF_Arg_inferType(v_pu_boxed_2157_, v_arg_2151_, v_a_2152_, v_a_2153_, v_a_2154_, v_a_2155_);
lean_dec(v_a_2155_);
lean_dec_ref(v_a_2154_);
lean_dec(v_a_2153_);
lean_dec_ref(v_a_2152_);
return v_res_2158_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_LetValue_inferType___closed__1(void){
_start:
{
lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; 
v___x_2160_ = ((lean_object*)(l_Lean_Compiler_LCNF_inferAppType___closed__1));
v___x_2161_ = lean_unsigned_to_nat(15u);
v___x_2162_ = lean_unsigned_to_nat(268u);
v___x_2163_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_inferType___closed__0));
v___x_2164_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_inferType___closed__0));
v___x_2165_ = l_mkPanicMessageWithDecl(v___x_2164_, v___x_2163_, v___x_2162_, v___x_2161_, v___x_2160_);
return v___x_2165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_inferType(uint8_t v_pu_2166_, lean_object* v_e_2167_, lean_object* v_a_2168_, lean_object* v_a_2169_, lean_object* v_a_2170_, lean_object* v_a_2171_){
_start:
{
if (v_pu_2166_ == 0)
{
lean_object* v___x_2173_; lean_object* v___x_2174_; 
v___x_2173_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4, &l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4);
v___x_2174_ = l_Lean_Compiler_LCNF_InferType_Pure_inferLetValueType(v_e_2167_, v___x_2173_, v_a_2168_, v_a_2169_, v_a_2170_, v_a_2171_);
return v___x_2174_;
}
else
{
lean_object* v___x_2175_; lean_object* v___x_2176_; 
lean_dec(v_e_2167_);
v___x_2175_ = lean_obj_once(&l_Lean_Compiler_LCNF_LetValue_inferType___closed__1, &l_Lean_Compiler_LCNF_LetValue_inferType___closed__1_once, _init_l_Lean_Compiler_LCNF_LetValue_inferType___closed__1);
v___x_2176_ = l_panic___at___00Lean_Compiler_LCNF_inferAppType_spec__0(v___x_2175_, v_a_2168_, v_a_2169_, v_a_2170_, v_a_2171_);
return v___x_2176_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_inferType___boxed(lean_object* v_pu_2177_, lean_object* v_e_2178_, lean_object* v_a_2179_, lean_object* v_a_2180_, lean_object* v_a_2181_, lean_object* v_a_2182_, lean_object* v_a_2183_){
_start:
{
uint8_t v_pu_boxed_2184_; lean_object* v_res_2185_; 
v_pu_boxed_2184_ = lean_unbox(v_pu_2177_);
v_res_2185_ = l_Lean_Compiler_LCNF_LetValue_inferType(v_pu_boxed_2184_, v_e_2178_, v_a_2179_, v_a_2180_, v_a_2181_, v_a_2182_);
lean_dec(v_a_2182_);
lean_dec_ref(v_a_2181_);
lean_dec(v_a_2180_);
lean_dec_ref(v_a_2179_);
return v_res_2185_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Code_inferType___closed__1(void){
_start:
{
lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; 
v___x_2187_ = ((lean_object*)(l_Lean_Compiler_LCNF_inferAppType___closed__1));
v___x_2188_ = lean_unsigned_to_nat(15u);
v___x_2189_ = lean_unsigned_to_nat(279u);
v___x_2190_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_inferType___closed__0));
v___x_2191_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_inferType___closed__0));
v___x_2192_ = l_mkPanicMessageWithDecl(v___x_2191_, v___x_2190_, v___x_2189_, v___x_2188_, v___x_2187_);
return v___x_2192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_inferType(uint8_t v_pu_2193_, lean_object* v_code_2194_, lean_object* v_a_2195_, lean_object* v_a_2196_, lean_object* v_a_2197_, lean_object* v_a_2198_){
_start:
{
if (v_pu_2193_ == 0)
{
switch(lean_obj_tag(v_code_2194_))
{
case 3:
{
lean_object* v_fvarId_2200_; lean_object* v_args_2201_; lean_object* v___x_2202_; 
v_fvarId_2200_ = lean_ctor_get(v_code_2194_, 0);
lean_inc(v_fvarId_2200_);
v_args_2201_ = lean_ctor_get(v_code_2194_, 1);
lean_inc_ref(v_args_2201_);
lean_dec_ref_known(v_code_2194_, 2);
v___x_2202_ = l_Lean_Compiler_LCNF_getType(v_fvarId_2200_, v_a_2195_, v_a_2196_, v_a_2197_, v_a_2198_);
if (lean_obj_tag(v___x_2202_) == 0)
{
lean_object* v_a_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; 
v_a_2203_ = lean_ctor_get(v___x_2202_, 0);
lean_inc(v_a_2203_);
lean_dec_ref_known(v___x_2202_, 1);
v___x_2204_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4, &l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4);
v___x_2205_ = l_Lean_Compiler_LCNF_InferType_Pure_inferAppTypeCore(v_a_2203_, v_args_2201_, v___x_2204_, v_a_2195_, v_a_2196_, v_a_2197_, v_a_2198_);
return v___x_2205_;
}
else
{
lean_dec_ref(v_args_2201_);
return v___x_2202_;
}
}
case 4:
{
lean_object* v_cases_2206_; lean_object* v___x_2208_; uint8_t v_isShared_2209_; uint8_t v_isSharedCheck_2214_; 
v_cases_2206_ = lean_ctor_get(v_code_2194_, 0);
v_isSharedCheck_2214_ = !lean_is_exclusive(v_code_2194_);
if (v_isSharedCheck_2214_ == 0)
{
v___x_2208_ = v_code_2194_;
v_isShared_2209_ = v_isSharedCheck_2214_;
goto v_resetjp_2207_;
}
else
{
lean_inc(v_cases_2206_);
lean_dec(v_code_2194_);
v___x_2208_ = lean_box(0);
v_isShared_2209_ = v_isSharedCheck_2214_;
goto v_resetjp_2207_;
}
v_resetjp_2207_:
{
lean_object* v_resultType_2210_; lean_object* v___x_2212_; 
v_resultType_2210_ = lean_ctor_get(v_cases_2206_, 1);
lean_inc_ref(v_resultType_2210_);
lean_dec_ref(v_cases_2206_);
if (v_isShared_2209_ == 0)
{
lean_ctor_set_tag(v___x_2208_, 0);
lean_ctor_set(v___x_2208_, 0, v_resultType_2210_);
v___x_2212_ = v___x_2208_;
goto v_reusejp_2211_;
}
else
{
lean_object* v_reuseFailAlloc_2213_; 
v_reuseFailAlloc_2213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2213_, 0, v_resultType_2210_);
v___x_2212_ = v_reuseFailAlloc_2213_;
goto v_reusejp_2211_;
}
v_reusejp_2211_:
{
return v___x_2212_;
}
}
}
case 5:
{
lean_object* v_fvarId_2215_; lean_object* v___x_2216_; 
v_fvarId_2215_ = lean_ctor_get(v_code_2194_, 0);
lean_inc(v_fvarId_2215_);
lean_dec_ref_known(v_code_2194_, 1);
v___x_2216_ = l_Lean_Compiler_LCNF_getType(v_fvarId_2215_, v_a_2195_, v_a_2196_, v_a_2197_, v_a_2198_);
return v___x_2216_;
}
case 6:
{
lean_object* v_type_2217_; lean_object* v___x_2219_; uint8_t v_isShared_2220_; uint8_t v_isSharedCheck_2224_; 
v_type_2217_ = lean_ctor_get(v_code_2194_, 0);
v_isSharedCheck_2224_ = !lean_is_exclusive(v_code_2194_);
if (v_isSharedCheck_2224_ == 0)
{
v___x_2219_ = v_code_2194_;
v_isShared_2220_ = v_isSharedCheck_2224_;
goto v_resetjp_2218_;
}
else
{
lean_inc(v_type_2217_);
lean_dec(v_code_2194_);
v___x_2219_ = lean_box(0);
v_isShared_2220_ = v_isSharedCheck_2224_;
goto v_resetjp_2218_;
}
v_resetjp_2218_:
{
lean_object* v___x_2222_; 
if (v_isShared_2220_ == 0)
{
lean_ctor_set_tag(v___x_2219_, 0);
v___x_2222_ = v___x_2219_;
goto v_reusejp_2221_;
}
else
{
lean_object* v_reuseFailAlloc_2223_; 
v_reuseFailAlloc_2223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2223_, 0, v_type_2217_);
v___x_2222_ = v_reuseFailAlloc_2223_;
goto v_reusejp_2221_;
}
v_reusejp_2221_:
{
return v___x_2222_;
}
}
}
default: 
{
lean_object* v_k_2225_; 
v_k_2225_ = lean_ctor_get(v_code_2194_, 1);
lean_inc_ref(v_k_2225_);
lean_dec_ref(v_code_2194_);
v_code_2194_ = v_k_2225_;
goto _start;
}
}
}
else
{
lean_object* v___x_2227_; lean_object* v___x_2228_; 
lean_dec_ref(v_code_2194_);
v___x_2227_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_inferType___closed__1, &l_Lean_Compiler_LCNF_Code_inferType___closed__1_once, _init_l_Lean_Compiler_LCNF_Code_inferType___closed__1);
v___x_2228_ = l_panic___at___00Lean_Compiler_LCNF_inferAppType_spec__0(v___x_2227_, v_a_2195_, v_a_2196_, v_a_2197_, v_a_2198_);
return v___x_2228_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_inferType___boxed(lean_object* v_pu_2229_, lean_object* v_code_2230_, lean_object* v_a_2231_, lean_object* v_a_2232_, lean_object* v_a_2233_, lean_object* v_a_2234_, lean_object* v_a_2235_){
_start:
{
uint8_t v_pu_boxed_2236_; lean_object* v_res_2237_; 
v_pu_boxed_2236_ = lean_unbox(v_pu_2229_);
v_res_2237_ = l_Lean_Compiler_LCNF_Code_inferType(v_pu_boxed_2236_, v_code_2230_, v_a_2231_, v_a_2232_, v_a_2233_, v_a_2234_);
lean_dec(v_a_2234_);
lean_dec_ref(v_a_2233_);
lean_dec(v_a_2232_);
lean_dec_ref(v_a_2231_);
return v_res_2237_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_Code_inferType_match__3_splitter___redArg(uint8_t v_pu_2238_, lean_object* v_code_2239_, lean_object* v_h__1_2240_, lean_object* v_h__2_2241_){
_start:
{
if (v_pu_2238_ == 0)
{
lean_object* v___x_2242_; 
lean_dec(v_h__2_2241_);
v___x_2242_ = lean_apply_1(v_h__1_2240_, v_code_2239_);
return v___x_2242_;
}
else
{
lean_object* v___x_2243_; 
lean_dec(v_h__1_2240_);
v___x_2243_ = lean_apply_1(v_h__2_2241_, v_code_2239_);
return v___x_2243_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_Code_inferType_match__3_splitter___redArg___boxed(lean_object* v_pu_2244_, lean_object* v_code_2245_, lean_object* v_h__1_2246_, lean_object* v_h__2_2247_){
_start:
{
uint8_t v_pu_32__boxed_2248_; lean_object* v_res_2249_; 
v_pu_32__boxed_2248_ = lean_unbox(v_pu_2244_);
v_res_2249_ = l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_Code_inferType_match__3_splitter___redArg(v_pu_32__boxed_2248_, v_code_2245_, v_h__1_2246_, v_h__2_2247_);
return v_res_2249_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_Code_inferType_match__3_splitter(lean_object* v_motive_2250_, uint8_t v_pu_2251_, lean_object* v_code_2252_, lean_object* v_h__1_2253_, lean_object* v_h__2_2254_){
_start:
{
if (v_pu_2251_ == 0)
{
lean_object* v___x_2255_; 
lean_dec(v_h__2_2254_);
v___x_2255_ = lean_apply_1(v_h__1_2253_, v_code_2252_);
return v___x_2255_;
}
else
{
lean_object* v___x_2256_; 
lean_dec(v_h__1_2253_);
v___x_2256_ = lean_apply_1(v_h__2_2254_, v_code_2252_);
return v___x_2256_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_Code_inferType_match__3_splitter___boxed(lean_object* v_motive_2257_, lean_object* v_pu_2258_, lean_object* v_code_2259_, lean_object* v_h__1_2260_, lean_object* v_h__2_2261_){
_start:
{
uint8_t v_pu_39__boxed_2262_; lean_object* v_res_2263_; 
v_pu_39__boxed_2262_ = lean_unbox(v_pu_2258_);
v_res_2263_ = l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_Code_inferType_match__3_splitter(v_motive_2257_, v_pu_39__boxed_2262_, v_code_2259_, v_h__1_2260_, v_h__2_2261_);
return v_res_2263_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_Code_inferType_match__1_splitter___redArg(lean_object* v_code_2264_, lean_object* v_h__1_2265_, lean_object* v_h__2_2266_, lean_object* v_h__3_2267_, lean_object* v_h__4_2268_, lean_object* v_h__5_2269_, lean_object* v_h__6_2270_, lean_object* v_h__7_2271_){
_start:
{
switch(lean_obj_tag(v_code_2264_))
{
case 0:
{
lean_object* v_decl_2272_; lean_object* v_k_2273_; lean_object* v___x_2274_; 
lean_dec(v_h__7_2271_);
lean_dec(v_h__6_2270_);
lean_dec(v_h__5_2269_);
lean_dec(v_h__4_2268_);
lean_dec(v_h__3_2267_);
lean_dec(v_h__2_2266_);
v_decl_2272_ = lean_ctor_get(v_code_2264_, 0);
lean_inc_ref(v_decl_2272_);
v_k_2273_ = lean_ctor_get(v_code_2264_, 1);
lean_inc_ref(v_k_2273_);
lean_dec_ref_known(v_code_2264_, 2);
v___x_2274_ = lean_apply_2(v_h__1_2265_, v_decl_2272_, v_k_2273_);
return v___x_2274_;
}
case 1:
{
lean_object* v_decl_2275_; lean_object* v_k_2276_; lean_object* v___x_2277_; 
lean_dec(v_h__7_2271_);
lean_dec(v_h__6_2270_);
lean_dec(v_h__5_2269_);
lean_dec(v_h__4_2268_);
lean_dec(v_h__3_2267_);
lean_dec(v_h__1_2265_);
v_decl_2275_ = lean_ctor_get(v_code_2264_, 0);
lean_inc_ref(v_decl_2275_);
v_k_2276_ = lean_ctor_get(v_code_2264_, 1);
lean_inc_ref(v_k_2276_);
lean_dec_ref_known(v_code_2264_, 2);
v___x_2277_ = lean_apply_3(v_h__2_2266_, v_decl_2275_, v_k_2276_, lean_box(0));
return v___x_2277_;
}
case 2:
{
lean_object* v_decl_2278_; lean_object* v_k_2279_; lean_object* v___x_2280_; 
lean_dec(v_h__7_2271_);
lean_dec(v_h__6_2270_);
lean_dec(v_h__5_2269_);
lean_dec(v_h__4_2268_);
lean_dec(v_h__2_2266_);
lean_dec(v_h__1_2265_);
v_decl_2278_ = lean_ctor_get(v_code_2264_, 0);
lean_inc_ref(v_decl_2278_);
v_k_2279_ = lean_ctor_get(v_code_2264_, 1);
lean_inc_ref(v_k_2279_);
lean_dec_ref_known(v_code_2264_, 2);
v___x_2280_ = lean_apply_2(v_h__3_2267_, v_decl_2278_, v_k_2279_);
return v___x_2280_;
}
case 3:
{
lean_object* v_fvarId_2281_; lean_object* v_args_2282_; lean_object* v___x_2283_; 
lean_dec(v_h__7_2271_);
lean_dec(v_h__6_2270_);
lean_dec(v_h__4_2268_);
lean_dec(v_h__3_2267_);
lean_dec(v_h__2_2266_);
lean_dec(v_h__1_2265_);
v_fvarId_2281_ = lean_ctor_get(v_code_2264_, 0);
lean_inc(v_fvarId_2281_);
v_args_2282_ = lean_ctor_get(v_code_2264_, 1);
lean_inc_ref(v_args_2282_);
lean_dec_ref_known(v_code_2264_, 2);
v___x_2283_ = lean_apply_2(v_h__5_2269_, v_fvarId_2281_, v_args_2282_);
return v___x_2283_;
}
case 4:
{
lean_object* v_cases_2284_; lean_object* v___x_2285_; 
lean_dec(v_h__6_2270_);
lean_dec(v_h__5_2269_);
lean_dec(v_h__4_2268_);
lean_dec(v_h__3_2267_);
lean_dec(v_h__2_2266_);
lean_dec(v_h__1_2265_);
v_cases_2284_ = lean_ctor_get(v_code_2264_, 0);
lean_inc_ref(v_cases_2284_);
lean_dec_ref_known(v_code_2264_, 1);
v___x_2285_ = lean_apply_1(v_h__7_2271_, v_cases_2284_);
return v___x_2285_;
}
case 5:
{
lean_object* v_fvarId_2286_; lean_object* v___x_2287_; 
lean_dec(v_h__7_2271_);
lean_dec(v_h__6_2270_);
lean_dec(v_h__5_2269_);
lean_dec(v_h__3_2267_);
lean_dec(v_h__2_2266_);
lean_dec(v_h__1_2265_);
v_fvarId_2286_ = lean_ctor_get(v_code_2264_, 0);
lean_inc(v_fvarId_2286_);
lean_dec_ref_known(v_code_2264_, 1);
v___x_2287_ = lean_apply_1(v_h__4_2268_, v_fvarId_2286_);
return v___x_2287_;
}
default: 
{
lean_object* v_type_2288_; lean_object* v___x_2289_; 
lean_dec(v_h__7_2271_);
lean_dec(v_h__5_2269_);
lean_dec(v_h__4_2268_);
lean_dec(v_h__3_2267_);
lean_dec(v_h__2_2266_);
lean_dec(v_h__1_2265_);
v_type_2288_ = lean_ctor_get(v_code_2264_, 0);
lean_inc_ref(v_type_2288_);
lean_dec_ref_known(v_code_2264_, 1);
v___x_2289_ = lean_apply_1(v_h__6_2270_, v_type_2288_);
return v___x_2289_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_Code_inferType_match__1_splitter(lean_object* v_motive_2290_, lean_object* v_code_2291_, lean_object* v_h__1_2292_, lean_object* v_h__2_2293_, lean_object* v_h__3_2294_, lean_object* v_h__4_2295_, lean_object* v_h__5_2296_, lean_object* v_h__6_2297_, lean_object* v_h__7_2298_){
_start:
{
switch(lean_obj_tag(v_code_2291_))
{
case 0:
{
lean_object* v_decl_2299_; lean_object* v_k_2300_; lean_object* v___x_2301_; 
lean_dec(v_h__7_2298_);
lean_dec(v_h__6_2297_);
lean_dec(v_h__5_2296_);
lean_dec(v_h__4_2295_);
lean_dec(v_h__3_2294_);
lean_dec(v_h__2_2293_);
v_decl_2299_ = lean_ctor_get(v_code_2291_, 0);
lean_inc_ref(v_decl_2299_);
v_k_2300_ = lean_ctor_get(v_code_2291_, 1);
lean_inc_ref(v_k_2300_);
lean_dec_ref_known(v_code_2291_, 2);
v___x_2301_ = lean_apply_2(v_h__1_2292_, v_decl_2299_, v_k_2300_);
return v___x_2301_;
}
case 1:
{
lean_object* v_decl_2302_; lean_object* v_k_2303_; lean_object* v___x_2304_; 
lean_dec(v_h__7_2298_);
lean_dec(v_h__6_2297_);
lean_dec(v_h__5_2296_);
lean_dec(v_h__4_2295_);
lean_dec(v_h__3_2294_);
lean_dec(v_h__1_2292_);
v_decl_2302_ = lean_ctor_get(v_code_2291_, 0);
lean_inc_ref(v_decl_2302_);
v_k_2303_ = lean_ctor_get(v_code_2291_, 1);
lean_inc_ref(v_k_2303_);
lean_dec_ref_known(v_code_2291_, 2);
v___x_2304_ = lean_apply_3(v_h__2_2293_, v_decl_2302_, v_k_2303_, lean_box(0));
return v___x_2304_;
}
case 2:
{
lean_object* v_decl_2305_; lean_object* v_k_2306_; lean_object* v___x_2307_; 
lean_dec(v_h__7_2298_);
lean_dec(v_h__6_2297_);
lean_dec(v_h__5_2296_);
lean_dec(v_h__4_2295_);
lean_dec(v_h__2_2293_);
lean_dec(v_h__1_2292_);
v_decl_2305_ = lean_ctor_get(v_code_2291_, 0);
lean_inc_ref(v_decl_2305_);
v_k_2306_ = lean_ctor_get(v_code_2291_, 1);
lean_inc_ref(v_k_2306_);
lean_dec_ref_known(v_code_2291_, 2);
v___x_2307_ = lean_apply_2(v_h__3_2294_, v_decl_2305_, v_k_2306_);
return v___x_2307_;
}
case 3:
{
lean_object* v_fvarId_2308_; lean_object* v_args_2309_; lean_object* v___x_2310_; 
lean_dec(v_h__7_2298_);
lean_dec(v_h__6_2297_);
lean_dec(v_h__4_2295_);
lean_dec(v_h__3_2294_);
lean_dec(v_h__2_2293_);
lean_dec(v_h__1_2292_);
v_fvarId_2308_ = lean_ctor_get(v_code_2291_, 0);
lean_inc(v_fvarId_2308_);
v_args_2309_ = lean_ctor_get(v_code_2291_, 1);
lean_inc_ref(v_args_2309_);
lean_dec_ref_known(v_code_2291_, 2);
v___x_2310_ = lean_apply_2(v_h__5_2296_, v_fvarId_2308_, v_args_2309_);
return v___x_2310_;
}
case 4:
{
lean_object* v_cases_2311_; lean_object* v___x_2312_; 
lean_dec(v_h__6_2297_);
lean_dec(v_h__5_2296_);
lean_dec(v_h__4_2295_);
lean_dec(v_h__3_2294_);
lean_dec(v_h__2_2293_);
lean_dec(v_h__1_2292_);
v_cases_2311_ = lean_ctor_get(v_code_2291_, 0);
lean_inc_ref(v_cases_2311_);
lean_dec_ref_known(v_code_2291_, 1);
v___x_2312_ = lean_apply_1(v_h__7_2298_, v_cases_2311_);
return v___x_2312_;
}
case 5:
{
lean_object* v_fvarId_2313_; lean_object* v___x_2314_; 
lean_dec(v_h__7_2298_);
lean_dec(v_h__6_2297_);
lean_dec(v_h__5_2296_);
lean_dec(v_h__3_2294_);
lean_dec(v_h__2_2293_);
lean_dec(v_h__1_2292_);
v_fvarId_2313_ = lean_ctor_get(v_code_2291_, 0);
lean_inc(v_fvarId_2313_);
lean_dec_ref_known(v_code_2291_, 1);
v___x_2314_ = lean_apply_1(v_h__4_2295_, v_fvarId_2313_);
return v___x_2314_;
}
default: 
{
lean_object* v_type_2315_; lean_object* v___x_2316_; 
lean_dec(v_h__7_2298_);
lean_dec(v_h__5_2296_);
lean_dec(v_h__4_2295_);
lean_dec(v_h__3_2294_);
lean_dec(v_h__2_2293_);
lean_dec(v_h__1_2292_);
v_type_2315_ = lean_ctor_get(v_code_2291_, 0);
lean_inc_ref(v_type_2315_);
lean_dec_ref_known(v_code_2291_, 1);
v___x_2316_ = lean_apply_1(v_h__6_2297_, v_type_2315_);
return v___x_2316_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_inferParamType(uint8_t v_pu_2317_, lean_object* v_params_2318_, lean_object* v_code_2319_, lean_object* v_a_2320_, lean_object* v_a_2321_, lean_object* v_a_2322_, lean_object* v_a_2323_){
_start:
{
lean_object* v___x_2325_; 
v___x_2325_ = l_Lean_Compiler_LCNF_Code_inferType(v_pu_2317_, v_code_2319_, v_a_2320_, v_a_2321_, v_a_2322_, v_a_2323_);
if (lean_obj_tag(v___x_2325_) == 0)
{
lean_object* v_a_2326_; size_t v_sz_2327_; size_t v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; 
v_a_2326_ = lean_ctor_get(v___x_2325_, 0);
lean_inc(v_a_2326_);
lean_dec_ref_known(v___x_2325_, 1);
v_sz_2327_ = lean_array_size(v_params_2318_);
v___x_2328_ = ((size_t)0ULL);
v___x_2329_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_InferType_Pure_mkForallParams_spec__0(v_sz_2327_, v___x_2328_, v_params_2318_);
v___x_2330_ = lean_unsigned_to_nat(32u);
v___x_2331_ = lean_mk_empty_array_with_capacity(v___x_2330_);
lean_dec_ref(v___x_2331_);
v___x_2332_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4, &l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4);
v___x_2333_ = l_Lean_Compiler_LCNF_InferType_Pure_mkForallFVars(v___x_2329_, v_a_2326_, v___x_2332_, v_a_2320_, v_a_2321_, v_a_2322_, v_a_2323_);
lean_dec(v_a_2326_);
lean_dec_ref(v___x_2329_);
return v___x_2333_;
}
else
{
lean_dec_ref(v_params_2318_);
return v___x_2325_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_inferParamType___boxed(lean_object* v_pu_2334_, lean_object* v_params_2335_, lean_object* v_code_2336_, lean_object* v_a_2337_, lean_object* v_a_2338_, lean_object* v_a_2339_, lean_object* v_a_2340_, lean_object* v_a_2341_){
_start:
{
uint8_t v_pu_boxed_2342_; lean_object* v_res_2343_; 
v_pu_boxed_2342_ = lean_unbox(v_pu_2334_);
v_res_2343_ = l_Lean_Compiler_LCNF_Code_inferParamType(v_pu_boxed_2342_, v_params_2335_, v_code_2336_, v_a_2337_, v_a_2338_, v_a_2339_, v_a_2340_);
lean_dec(v_a_2340_);
lean_dec_ref(v_a_2339_);
lean_dec(v_a_2338_);
lean_dec_ref(v_a_2337_);
return v_res_2343_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_inferType(uint8_t v_pu_2344_, lean_object* v_alt_2345_, lean_object* v_a_2346_, lean_object* v_a_2347_, lean_object* v_a_2348_, lean_object* v_a_2349_){
_start:
{
switch(lean_obj_tag(v_alt_2345_))
{
case 0:
{
lean_object* v_code_2351_; lean_object* v___x_2352_; 
v_code_2351_ = lean_ctor_get(v_alt_2345_, 2);
lean_inc_ref(v_code_2351_);
lean_dec_ref_known(v_alt_2345_, 3);
v___x_2352_ = l_Lean_Compiler_LCNF_Code_inferType(v_pu_2344_, v_code_2351_, v_a_2346_, v_a_2347_, v_a_2348_, v_a_2349_);
return v___x_2352_;
}
case 1:
{
lean_object* v_code_2353_; lean_object* v___x_2354_; 
v_code_2353_ = lean_ctor_get(v_alt_2345_, 1);
lean_inc_ref(v_code_2353_);
lean_dec_ref_known(v_alt_2345_, 2);
v___x_2354_ = l_Lean_Compiler_LCNF_Code_inferType(v_pu_2344_, v_code_2353_, v_a_2346_, v_a_2347_, v_a_2348_, v_a_2349_);
return v___x_2354_;
}
default: 
{
lean_object* v_code_2355_; lean_object* v___x_2356_; 
v_code_2355_ = lean_ctor_get(v_alt_2345_, 0);
lean_inc_ref(v_code_2355_);
lean_dec_ref_known(v_alt_2345_, 1);
v___x_2356_ = l_Lean_Compiler_LCNF_Code_inferType(v_pu_2344_, v_code_2355_, v_a_2346_, v_a_2347_, v_a_2348_, v_a_2349_);
return v___x_2356_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_inferType___boxed(lean_object* v_pu_2357_, lean_object* v_alt_2358_, lean_object* v_a_2359_, lean_object* v_a_2360_, lean_object* v_a_2361_, lean_object* v_a_2362_, lean_object* v_a_2363_){
_start:
{
uint8_t v_pu_boxed_2364_; lean_object* v_res_2365_; 
v_pu_boxed_2364_ = lean_unbox(v_pu_2357_);
v_res_2365_ = l_Lean_Compiler_LCNF_Alt_inferType(v_pu_boxed_2364_, v_alt_2358_, v_a_2359_, v_a_2360_, v_a_2361_, v_a_2362_);
lean_dec(v_a_2362_);
lean_dec_ref(v_a_2361_);
lean_dec(v_a_2360_);
lean_dec_ref(v_a_2359_);
return v_res_2365_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkAuxLetDecl(uint8_t v_pu_2366_, lean_object* v_e_2367_, lean_object* v_prefixName_2368_, lean_object* v_a_2369_, lean_object* v_a_2370_, lean_object* v_a_2371_, lean_object* v_a_2372_){
_start:
{
lean_object* v___x_2374_; 
v___x_2374_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v_prefixName_2368_, v_a_2370_);
if (lean_obj_tag(v___x_2374_) == 0)
{
lean_object* v_a_2375_; lean_object* v___x_2376_; 
v_a_2375_ = lean_ctor_get(v___x_2374_, 0);
lean_inc(v_a_2375_);
lean_dec_ref_known(v___x_2374_, 1);
lean_inc(v_e_2367_);
v___x_2376_ = l_Lean_Compiler_LCNF_LetValue_inferType(v_pu_2366_, v_e_2367_, v_a_2369_, v_a_2370_, v_a_2371_, v_a_2372_);
if (lean_obj_tag(v___x_2376_) == 0)
{
lean_object* v_a_2377_; lean_object* v___x_2378_; 
v_a_2377_ = lean_ctor_get(v___x_2376_, 0);
lean_inc(v_a_2377_);
lean_dec_ref_known(v___x_2376_, 1);
v___x_2378_ = l_Lean_Compiler_LCNF_mkLetDecl(v_pu_2366_, v_a_2375_, v_a_2377_, v_e_2367_, v_a_2369_, v_a_2370_, v_a_2371_, v_a_2372_);
return v___x_2378_;
}
else
{
lean_object* v_a_2379_; lean_object* v___x_2381_; uint8_t v_isShared_2382_; uint8_t v_isSharedCheck_2386_; 
lean_dec(v_a_2375_);
lean_dec(v_e_2367_);
v_a_2379_ = lean_ctor_get(v___x_2376_, 0);
v_isSharedCheck_2386_ = !lean_is_exclusive(v___x_2376_);
if (v_isSharedCheck_2386_ == 0)
{
v___x_2381_ = v___x_2376_;
v_isShared_2382_ = v_isSharedCheck_2386_;
goto v_resetjp_2380_;
}
else
{
lean_inc(v_a_2379_);
lean_dec(v___x_2376_);
v___x_2381_ = lean_box(0);
v_isShared_2382_ = v_isSharedCheck_2386_;
goto v_resetjp_2380_;
}
v_resetjp_2380_:
{
lean_object* v___x_2384_; 
if (v_isShared_2382_ == 0)
{
v___x_2384_ = v___x_2381_;
goto v_reusejp_2383_;
}
else
{
lean_object* v_reuseFailAlloc_2385_; 
v_reuseFailAlloc_2385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2385_, 0, v_a_2379_);
v___x_2384_ = v_reuseFailAlloc_2385_;
goto v_reusejp_2383_;
}
v_reusejp_2383_:
{
return v___x_2384_;
}
}
}
}
else
{
lean_object* v_a_2387_; lean_object* v___x_2389_; uint8_t v_isShared_2390_; uint8_t v_isSharedCheck_2394_; 
lean_dec(v_e_2367_);
v_a_2387_ = lean_ctor_get(v___x_2374_, 0);
v_isSharedCheck_2394_ = !lean_is_exclusive(v___x_2374_);
if (v_isSharedCheck_2394_ == 0)
{
v___x_2389_ = v___x_2374_;
v_isShared_2390_ = v_isSharedCheck_2394_;
goto v_resetjp_2388_;
}
else
{
lean_inc(v_a_2387_);
lean_dec(v___x_2374_);
v___x_2389_ = lean_box(0);
v_isShared_2390_ = v_isSharedCheck_2394_;
goto v_resetjp_2388_;
}
v_resetjp_2388_:
{
lean_object* v___x_2392_; 
if (v_isShared_2390_ == 0)
{
v___x_2392_ = v___x_2389_;
goto v_reusejp_2391_;
}
else
{
lean_object* v_reuseFailAlloc_2393_; 
v_reuseFailAlloc_2393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2393_, 0, v_a_2387_);
v___x_2392_ = v_reuseFailAlloc_2393_;
goto v_reusejp_2391_;
}
v_reusejp_2391_:
{
return v___x_2392_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkAuxLetDecl___boxed(lean_object* v_pu_2395_, lean_object* v_e_2396_, lean_object* v_prefixName_2397_, lean_object* v_a_2398_, lean_object* v_a_2399_, lean_object* v_a_2400_, lean_object* v_a_2401_, lean_object* v_a_2402_){
_start:
{
uint8_t v_pu_boxed_2403_; lean_object* v_res_2404_; 
v_pu_boxed_2403_ = lean_unbox(v_pu_2395_);
v_res_2404_ = l_Lean_Compiler_LCNF_mkAuxLetDecl(v_pu_boxed_2403_, v_e_2396_, v_prefixName_2397_, v_a_2398_, v_a_2399_, v_a_2400_, v_a_2401_);
lean_dec(v_a_2401_);
lean_dec_ref(v_a_2400_);
lean_dec(v_a_2399_);
lean_dec_ref(v_a_2398_);
return v_res_2404_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_mkForallParams___closed__1(void){
_start:
{
lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; 
v___x_2406_ = ((lean_object*)(l_Lean_Compiler_LCNF_inferAppType___closed__1));
v___x_2407_ = lean_unsigned_to_nat(15u);
v___x_2408_ = lean_unsigned_to_nat(295u);
v___x_2409_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkForallParams___closed__0));
v___x_2410_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_inferType___closed__0));
v___x_2411_ = l_mkPanicMessageWithDecl(v___x_2410_, v___x_2409_, v___x_2408_, v___x_2407_, v___x_2406_);
return v___x_2411_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkForallParams(uint8_t v_pu_2412_, lean_object* v_params_2413_, lean_object* v_type_2414_, lean_object* v_a_2415_, lean_object* v_a_2416_, lean_object* v_a_2417_, lean_object* v_a_2418_){
_start:
{
if (v_pu_2412_ == 0)
{
lean_object* v___x_2420_; 
v___x_2420_ = l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg(v_params_2413_, v_type_2414_, v_a_2415_, v_a_2416_, v_a_2417_, v_a_2418_);
return v___x_2420_;
}
else
{
lean_object* v___x_2421_; lean_object* v___x_2422_; 
lean_dec_ref(v_params_2413_);
v___x_2421_ = lean_obj_once(&l_Lean_Compiler_LCNF_mkForallParams___closed__1, &l_Lean_Compiler_LCNF_mkForallParams___closed__1_once, _init_l_Lean_Compiler_LCNF_mkForallParams___closed__1);
v___x_2422_ = l_panic___at___00Lean_Compiler_LCNF_inferAppType_spec__0(v___x_2421_, v_a_2415_, v_a_2416_, v_a_2417_, v_a_2418_);
return v___x_2422_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkForallParams___boxed(lean_object* v_pu_2423_, lean_object* v_params_2424_, lean_object* v_type_2425_, lean_object* v_a_2426_, lean_object* v_a_2427_, lean_object* v_a_2428_, lean_object* v_a_2429_, lean_object* v_a_2430_){
_start:
{
uint8_t v_pu_boxed_2431_; lean_object* v_res_2432_; 
v_pu_boxed_2431_ = lean_unbox(v_pu_2423_);
v_res_2432_ = l_Lean_Compiler_LCNF_mkForallParams(v_pu_boxed_2431_, v_params_2424_, v_type_2425_, v_a_2426_, v_a_2427_, v_a_2428_, v_a_2429_);
lean_dec(v_a_2429_);
lean_dec_ref(v_a_2428_);
lean_dec(v_a_2427_);
lean_dec_ref(v_a_2426_);
lean_dec_ref(v_type_2425_);
return v_res_2432_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_mkAuxFunDeclAux(uint8_t v_pu_2433_, lean_object* v_params_2434_, lean_object* v_code_2435_, lean_object* v_prefixName_2436_, lean_object* v_a_2437_, lean_object* v_a_2438_, lean_object* v_a_2439_, lean_object* v_a_2440_){
_start:
{
lean_object* v___x_2442_; 
lean_inc_ref(v_code_2435_);
v___x_2442_ = l_Lean_Compiler_LCNF_Code_inferType(v_pu_2433_, v_code_2435_, v_a_2437_, v_a_2438_, v_a_2439_, v_a_2440_);
if (lean_obj_tag(v___x_2442_) == 0)
{
lean_object* v_a_2443_; lean_object* v___x_2444_; 
v_a_2443_ = lean_ctor_get(v___x_2442_, 0);
lean_inc(v_a_2443_);
lean_dec_ref_known(v___x_2442_, 1);
lean_inc_ref(v_params_2434_);
v___x_2444_ = l_Lean_Compiler_LCNF_mkForallParams(v_pu_2433_, v_params_2434_, v_a_2443_, v_a_2437_, v_a_2438_, v_a_2439_, v_a_2440_);
lean_dec(v_a_2443_);
if (lean_obj_tag(v___x_2444_) == 0)
{
lean_object* v_a_2445_; lean_object* v___x_2446_; 
v_a_2445_ = lean_ctor_get(v___x_2444_, 0);
lean_inc(v_a_2445_);
lean_dec_ref_known(v___x_2444_, 1);
v___x_2446_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v_prefixName_2436_, v_a_2438_);
if (lean_obj_tag(v___x_2446_) == 0)
{
lean_object* v_a_2447_; lean_object* v___x_2448_; 
v_a_2447_ = lean_ctor_get(v___x_2446_, 0);
lean_inc(v_a_2447_);
lean_dec_ref_known(v___x_2446_, 1);
v___x_2448_ = l_Lean_Compiler_LCNF_mkFunDecl(v_pu_2433_, v_a_2447_, v_a_2445_, v_params_2434_, v_code_2435_, v_a_2437_, v_a_2438_, v_a_2439_, v_a_2440_);
return v___x_2448_;
}
else
{
lean_object* v_a_2449_; lean_object* v___x_2451_; uint8_t v_isShared_2452_; uint8_t v_isSharedCheck_2456_; 
lean_dec(v_a_2445_);
lean_dec_ref(v_code_2435_);
lean_dec_ref(v_params_2434_);
v_a_2449_ = lean_ctor_get(v___x_2446_, 0);
v_isSharedCheck_2456_ = !lean_is_exclusive(v___x_2446_);
if (v_isSharedCheck_2456_ == 0)
{
v___x_2451_ = v___x_2446_;
v_isShared_2452_ = v_isSharedCheck_2456_;
goto v_resetjp_2450_;
}
else
{
lean_inc(v_a_2449_);
lean_dec(v___x_2446_);
v___x_2451_ = lean_box(0);
v_isShared_2452_ = v_isSharedCheck_2456_;
goto v_resetjp_2450_;
}
v_resetjp_2450_:
{
lean_object* v___x_2454_; 
if (v_isShared_2452_ == 0)
{
v___x_2454_ = v___x_2451_;
goto v_reusejp_2453_;
}
else
{
lean_object* v_reuseFailAlloc_2455_; 
v_reuseFailAlloc_2455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2455_, 0, v_a_2449_);
v___x_2454_ = v_reuseFailAlloc_2455_;
goto v_reusejp_2453_;
}
v_reusejp_2453_:
{
return v___x_2454_;
}
}
}
}
else
{
lean_object* v_a_2457_; lean_object* v___x_2459_; uint8_t v_isShared_2460_; uint8_t v_isSharedCheck_2464_; 
lean_dec(v_prefixName_2436_);
lean_dec_ref(v_code_2435_);
lean_dec_ref(v_params_2434_);
v_a_2457_ = lean_ctor_get(v___x_2444_, 0);
v_isSharedCheck_2464_ = !lean_is_exclusive(v___x_2444_);
if (v_isSharedCheck_2464_ == 0)
{
v___x_2459_ = v___x_2444_;
v_isShared_2460_ = v_isSharedCheck_2464_;
goto v_resetjp_2458_;
}
else
{
lean_inc(v_a_2457_);
lean_dec(v___x_2444_);
v___x_2459_ = lean_box(0);
v_isShared_2460_ = v_isSharedCheck_2464_;
goto v_resetjp_2458_;
}
v_resetjp_2458_:
{
lean_object* v___x_2462_; 
if (v_isShared_2460_ == 0)
{
v___x_2462_ = v___x_2459_;
goto v_reusejp_2461_;
}
else
{
lean_object* v_reuseFailAlloc_2463_; 
v_reuseFailAlloc_2463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2463_, 0, v_a_2457_);
v___x_2462_ = v_reuseFailAlloc_2463_;
goto v_reusejp_2461_;
}
v_reusejp_2461_:
{
return v___x_2462_;
}
}
}
}
else
{
lean_object* v_a_2465_; lean_object* v___x_2467_; uint8_t v_isShared_2468_; uint8_t v_isSharedCheck_2472_; 
lean_dec(v_prefixName_2436_);
lean_dec_ref(v_code_2435_);
lean_dec_ref(v_params_2434_);
v_a_2465_ = lean_ctor_get(v___x_2442_, 0);
v_isSharedCheck_2472_ = !lean_is_exclusive(v___x_2442_);
if (v_isSharedCheck_2472_ == 0)
{
v___x_2467_ = v___x_2442_;
v_isShared_2468_ = v_isSharedCheck_2472_;
goto v_resetjp_2466_;
}
else
{
lean_inc(v_a_2465_);
lean_dec(v___x_2442_);
v___x_2467_ = lean_box(0);
v_isShared_2468_ = v_isSharedCheck_2472_;
goto v_resetjp_2466_;
}
v_resetjp_2466_:
{
lean_object* v___x_2470_; 
if (v_isShared_2468_ == 0)
{
v___x_2470_ = v___x_2467_;
goto v_reusejp_2469_;
}
else
{
lean_object* v_reuseFailAlloc_2471_; 
v_reuseFailAlloc_2471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2471_, 0, v_a_2465_);
v___x_2470_ = v_reuseFailAlloc_2471_;
goto v_reusejp_2469_;
}
v_reusejp_2469_:
{
return v___x_2470_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_mkAuxFunDeclAux___boxed(lean_object* v_pu_2473_, lean_object* v_params_2474_, lean_object* v_code_2475_, lean_object* v_prefixName_2476_, lean_object* v_a_2477_, lean_object* v_a_2478_, lean_object* v_a_2479_, lean_object* v_a_2480_, lean_object* v_a_2481_){
_start:
{
uint8_t v_pu_boxed_2482_; lean_object* v_res_2483_; 
v_pu_boxed_2482_ = lean_unbox(v_pu_2473_);
v_res_2483_ = l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_mkAuxFunDeclAux(v_pu_boxed_2482_, v_params_2474_, v_code_2475_, v_prefixName_2476_, v_a_2477_, v_a_2478_, v_a_2479_, v_a_2480_);
lean_dec(v_a_2480_);
lean_dec_ref(v_a_2479_);
lean_dec(v_a_2478_);
lean_dec_ref(v_a_2477_);
return v_res_2483_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkAuxFunDecl(lean_object* v_params_2484_, lean_object* v_code_2485_, lean_object* v_prefixName_2486_, lean_object* v_a_2487_, lean_object* v_a_2488_, lean_object* v_a_2489_, lean_object* v_a_2490_){
_start:
{
uint8_t v___x_2492_; lean_object* v___x_2493_; 
v___x_2492_ = 0;
v___x_2493_ = l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_mkAuxFunDeclAux(v___x_2492_, v_params_2484_, v_code_2485_, v_prefixName_2486_, v_a_2487_, v_a_2488_, v_a_2489_, v_a_2490_);
return v___x_2493_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkAuxFunDecl___boxed(lean_object* v_params_2494_, lean_object* v_code_2495_, lean_object* v_prefixName_2496_, lean_object* v_a_2497_, lean_object* v_a_2498_, lean_object* v_a_2499_, lean_object* v_a_2500_, lean_object* v_a_2501_){
_start:
{
lean_object* v_res_2502_; 
v_res_2502_ = l_Lean_Compiler_LCNF_mkAuxFunDecl(v_params_2494_, v_code_2495_, v_prefixName_2496_, v_a_2497_, v_a_2498_, v_a_2499_, v_a_2500_);
lean_dec(v_a_2500_);
lean_dec_ref(v_a_2499_);
lean_dec(v_a_2498_);
lean_dec_ref(v_a_2497_);
return v_res_2502_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkAuxJpDecl(uint8_t v_pu_2503_, lean_object* v_params_2504_, lean_object* v_code_2505_, lean_object* v_prefixName_2506_, lean_object* v_a_2507_, lean_object* v_a_2508_, lean_object* v_a_2509_, lean_object* v_a_2510_){
_start:
{
lean_object* v___x_2512_; 
v___x_2512_ = l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_mkAuxFunDeclAux(v_pu_2503_, v_params_2504_, v_code_2505_, v_prefixName_2506_, v_a_2507_, v_a_2508_, v_a_2509_, v_a_2510_);
return v___x_2512_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkAuxJpDecl___boxed(lean_object* v_pu_2513_, lean_object* v_params_2514_, lean_object* v_code_2515_, lean_object* v_prefixName_2516_, lean_object* v_a_2517_, lean_object* v_a_2518_, lean_object* v_a_2519_, lean_object* v_a_2520_, lean_object* v_a_2521_){
_start:
{
uint8_t v_pu_boxed_2522_; lean_object* v_res_2523_; 
v_pu_boxed_2522_ = lean_unbox(v_pu_2513_);
v_res_2523_ = l_Lean_Compiler_LCNF_mkAuxJpDecl(v_pu_boxed_2522_, v_params_2514_, v_code_2515_, v_prefixName_2516_, v_a_2517_, v_a_2518_, v_a_2519_, v_a_2520_);
lean_dec(v_a_2520_);
lean_dec_ref(v_a_2519_);
lean_dec(v_a_2518_);
lean_dec_ref(v_a_2517_);
return v_res_2523_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkAuxJpDecl_x27(uint8_t v_pu_2524_, lean_object* v_param_2525_, lean_object* v_code_2526_, lean_object* v_prefixName_2527_, lean_object* v_a_2528_, lean_object* v_a_2529_, lean_object* v_a_2530_, lean_object* v_a_2531_){
_start:
{
lean_object* v___x_2533_; lean_object* v___x_2534_; lean_object* v_params_2535_; lean_object* v___x_2536_; 
v___x_2533_ = lean_unsigned_to_nat(1u);
v___x_2534_ = lean_mk_empty_array_with_capacity(v___x_2533_);
v_params_2535_ = lean_array_push(v___x_2534_, v_param_2525_);
v___x_2536_ = l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_mkAuxFunDeclAux(v_pu_2524_, v_params_2535_, v_code_2526_, v_prefixName_2527_, v_a_2528_, v_a_2529_, v_a_2530_, v_a_2531_);
return v___x_2536_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkAuxJpDecl_x27___boxed(lean_object* v_pu_2537_, lean_object* v_param_2538_, lean_object* v_code_2539_, lean_object* v_prefixName_2540_, lean_object* v_a_2541_, lean_object* v_a_2542_, lean_object* v_a_2543_, lean_object* v_a_2544_, lean_object* v_a_2545_){
_start:
{
uint8_t v_pu_boxed_2546_; lean_object* v_res_2547_; 
v_pu_boxed_2546_ = lean_unbox(v_pu_2537_);
v_res_2547_ = l_Lean_Compiler_LCNF_mkAuxJpDecl_x27(v_pu_boxed_2546_, v_param_2538_, v_code_2539_, v_prefixName_2540_, v_a_2541_, v_a_2542_, v_a_2543_, v_a_2544_);
lean_dec(v_a_2544_);
lean_dec_ref(v_a_2543_);
lean_dec(v_a_2542_);
lean_dec_ref(v_a_2541_);
return v_res_2547_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__1___redArg(lean_object* v_msg_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_, lean_object* v___y_2552_){
_start:
{
lean_object* v_ref_2554_; lean_object* v___x_2555_; lean_object* v_env_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; 
v_ref_2554_ = lean_ctor_get(v___y_2551_, 2);
v___x_2555_ = lean_st_ref_get(v___y_2552_);
v_env_2556_ = lean_ctor_get(v___x_2555_, 0);
lean_inc_ref(v_env_2556_);
lean_dec(v___x_2555_);
v___x_2557_ = lean_st_ref_get(v___y_2550_);
v___x_2558_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_2549_);
if (lean_obj_tag(v___x_2558_) == 0)
{
lean_object* v_a_2559_; lean_object* v___x_2561_; uint8_t v_isShared_2562_; uint8_t v_isSharedCheck_2581_; 
v_a_2559_ = lean_ctor_get(v___x_2558_, 0);
v_isSharedCheck_2581_ = !lean_is_exclusive(v___x_2558_);
if (v_isSharedCheck_2581_ == 0)
{
v___x_2561_ = v___x_2558_;
v_isShared_2562_ = v_isSharedCheck_2581_;
goto v_resetjp_2560_;
}
else
{
lean_inc(v_a_2559_);
lean_dec(v___x_2558_);
v___x_2561_ = lean_box(0);
v_isShared_2562_ = v_isSharedCheck_2581_;
goto v_resetjp_2560_;
}
v_resetjp_2560_:
{
lean_object* v_lctx_2563_; lean_object* v___x_2565_; uint8_t v_isShared_2566_; uint8_t v_isSharedCheck_2579_; 
v_lctx_2563_ = lean_ctor_get(v___x_2557_, 0);
v_isSharedCheck_2579_ = !lean_is_exclusive(v___x_2557_);
if (v_isSharedCheck_2579_ == 0)
{
lean_object* v_unused_2580_; 
v_unused_2580_ = lean_ctor_get(v___x_2557_, 1);
lean_dec(v_unused_2580_);
v___x_2565_ = v___x_2557_;
v_isShared_2566_ = v_isSharedCheck_2579_;
goto v_resetjp_2564_;
}
else
{
lean_inc(v_lctx_2563_);
lean_dec(v___x_2557_);
v___x_2565_ = lean_box(0);
v_isShared_2566_ = v_isSharedCheck_2579_;
goto v_resetjp_2564_;
}
v_resetjp_2564_:
{
uint8_t v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2573_; 
v___x_2567_ = lean_unbox(v_a_2559_);
lean_dec(v_a_2559_);
v___x_2568_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_2563_, v___x_2567_);
lean_dec_ref(v_lctx_2563_);
v___x_2569_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2551_);
v___x_2570_ = lean_obj_once(&l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___closed__1, &l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___closed__1_once, _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___closed__1);
v___x_2571_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2571_, 0, v_env_2556_);
lean_ctor_set(v___x_2571_, 1, v___x_2570_);
lean_ctor_set(v___x_2571_, 2, v___x_2568_);
lean_ctor_set(v___x_2571_, 3, v___x_2569_);
if (v_isShared_2566_ == 0)
{
lean_ctor_set_tag(v___x_2565_, 3);
lean_ctor_set(v___x_2565_, 1, v_msg_2548_);
lean_ctor_set(v___x_2565_, 0, v___x_2571_);
v___x_2573_ = v___x_2565_;
goto v_reusejp_2572_;
}
else
{
lean_object* v_reuseFailAlloc_2578_; 
v_reuseFailAlloc_2578_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2578_, 0, v___x_2571_);
lean_ctor_set(v_reuseFailAlloc_2578_, 1, v_msg_2548_);
v___x_2573_ = v_reuseFailAlloc_2578_;
goto v_reusejp_2572_;
}
v_reusejp_2572_:
{
lean_object* v___x_2574_; lean_object* v___x_2576_; 
lean_inc(v_ref_2554_);
v___x_2574_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2574_, 0, v_ref_2554_);
lean_ctor_set(v___x_2574_, 1, v___x_2573_);
if (v_isShared_2562_ == 0)
{
lean_ctor_set_tag(v___x_2561_, 1);
lean_ctor_set(v___x_2561_, 0, v___x_2574_);
v___x_2576_ = v___x_2561_;
goto v_reusejp_2575_;
}
else
{
lean_object* v_reuseFailAlloc_2577_; 
v_reuseFailAlloc_2577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2577_, 0, v___x_2574_);
v___x_2576_ = v_reuseFailAlloc_2577_;
goto v_reusejp_2575_;
}
v_reusejp_2575_:
{
return v___x_2576_;
}
}
}
}
}
else
{
lean_object* v_a_2582_; lean_object* v___x_2584_; uint8_t v_isShared_2585_; uint8_t v_isSharedCheck_2589_; 
lean_dec(v___x_2557_);
lean_dec_ref(v_env_2556_);
lean_dec_ref(v_msg_2548_);
v_a_2582_ = lean_ctor_get(v___x_2558_, 0);
v_isSharedCheck_2589_ = !lean_is_exclusive(v___x_2558_);
if (v_isSharedCheck_2589_ == 0)
{
v___x_2584_ = v___x_2558_;
v_isShared_2585_ = v_isSharedCheck_2589_;
goto v_resetjp_2583_;
}
else
{
lean_inc(v_a_2582_);
lean_dec(v___x_2558_);
v___x_2584_ = lean_box(0);
v_isShared_2585_ = v_isSharedCheck_2589_;
goto v_resetjp_2583_;
}
v_resetjp_2583_:
{
lean_object* v___x_2587_; 
if (v_isShared_2585_ == 0)
{
v___x_2587_ = v___x_2584_;
goto v_reusejp_2586_;
}
else
{
lean_object* v_reuseFailAlloc_2588_; 
v_reuseFailAlloc_2588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2588_, 0, v_a_2582_);
v___x_2587_ = v_reuseFailAlloc_2588_;
goto v_reusejp_2586_;
}
v_reusejp_2586_:
{
return v___x_2587_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__1___redArg___boxed(lean_object* v_msg_2590_, lean_object* v___y_2591_, lean_object* v___y_2592_, lean_object* v___y_2593_, lean_object* v___y_2594_, lean_object* v___y_2595_){
_start:
{
lean_object* v_res_2596_; 
v_res_2596_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__1___redArg(v_msg_2590_, v___y_2591_, v___y_2592_, v___y_2593_, v___y_2594_);
lean_dec(v___y_2594_);
lean_dec_ref(v___y_2593_);
lean_dec(v___y_2592_);
lean_dec_ref(v___y_2591_);
return v_res_2596_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__1(lean_object* v_00_u03b1_2597_, lean_object* v_msg_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_){
_start:
{
lean_object* v___x_2604_; 
v___x_2604_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__1___redArg(v_msg_2598_, v___y_2599_, v___y_2600_, v___y_2601_, v___y_2602_);
return v___x_2604_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__1___boxed(lean_object* v_00_u03b1_2605_, lean_object* v_msg_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_, lean_object* v___y_2611_){
_start:
{
lean_object* v_res_2612_; 
v_res_2612_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__1(v_00_u03b1_2605_, v_msg_2606_, v___y_2607_, v___y_2608_, v___y_2609_, v___y_2610_);
lean_dec(v___y_2610_);
lean_dec_ref(v___y_2609_);
lean_dec(v___y_2608_);
lean_dec_ref(v___y_2607_);
return v_res_2612_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__0___redArg(uint8_t v_pu_2613_, lean_object* v_a_2614_, lean_object* v_b_2615_, lean_object* v___y_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_){
_start:
{
lean_object* v_array_2621_; lean_object* v_start_2622_; lean_object* v_stop_2623_; lean_object* v___x_2625_; uint8_t v_isShared_2626_; uint8_t v_isSharedCheck_2639_; 
v_array_2621_ = lean_ctor_get(v_a_2614_, 0);
v_start_2622_ = lean_ctor_get(v_a_2614_, 1);
v_stop_2623_ = lean_ctor_get(v_a_2614_, 2);
v_isSharedCheck_2639_ = !lean_is_exclusive(v_a_2614_);
if (v_isSharedCheck_2639_ == 0)
{
v___x_2625_ = v_a_2614_;
v_isShared_2626_ = v_isSharedCheck_2639_;
goto v_resetjp_2624_;
}
else
{
lean_inc(v_stop_2623_);
lean_inc(v_start_2622_);
lean_inc(v_array_2621_);
lean_dec(v_a_2614_);
v___x_2625_ = lean_box(0);
v_isShared_2626_ = v_isSharedCheck_2639_;
goto v_resetjp_2624_;
}
v_resetjp_2624_:
{
uint8_t v___x_2627_; 
v___x_2627_ = lean_nat_dec_lt(v_start_2622_, v_stop_2623_);
if (v___x_2627_ == 0)
{
lean_object* v___x_2628_; 
lean_del_object(v___x_2625_);
lean_dec(v_stop_2623_);
lean_dec(v_start_2622_);
lean_dec_ref(v_array_2621_);
v___x_2628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2628_, 0, v_b_2615_);
return v___x_2628_;
}
else
{
lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2632_; 
v___x_2629_ = lean_unsigned_to_nat(1u);
v___x_2630_ = lean_nat_add(v_start_2622_, v___x_2629_);
lean_inc_ref(v_array_2621_);
if (v_isShared_2626_ == 0)
{
lean_ctor_set(v___x_2625_, 1, v___x_2630_);
v___x_2632_ = v___x_2625_;
goto v_reusejp_2631_;
}
else
{
lean_object* v_reuseFailAlloc_2638_; 
v_reuseFailAlloc_2638_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2638_, 0, v_array_2621_);
lean_ctor_set(v_reuseFailAlloc_2638_, 1, v___x_2630_);
lean_ctor_set(v_reuseFailAlloc_2638_, 2, v_stop_2623_);
v___x_2632_ = v_reuseFailAlloc_2638_;
goto v_reusejp_2631_;
}
v_reusejp_2631_:
{
lean_object* v___x_2633_; lean_object* v___x_2634_; 
v___x_2633_ = lean_array_fget(v_array_2621_, v_start_2622_);
lean_dec(v_start_2622_);
lean_dec_ref(v_array_2621_);
v___x_2634_ = l_Lean_Compiler_LCNF_Alt_inferType(v_pu_2613_, v___x_2633_, v___y_2616_, v___y_2617_, v___y_2618_, v___y_2619_);
if (lean_obj_tag(v___x_2634_) == 0)
{
lean_object* v_a_2635_; lean_object* v___x_2636_; 
v_a_2635_ = lean_ctor_get(v___x_2634_, 0);
lean_inc(v_a_2635_);
lean_dec_ref_known(v___x_2634_, 1);
v___x_2636_ = l_Lean_Compiler_LCNF_joinTypes(v_b_2615_, v_a_2635_);
v_a_2614_ = v___x_2632_;
v_b_2615_ = v___x_2636_;
goto _start;
}
else
{
lean_dec_ref(v___x_2632_);
lean_dec_ref(v_b_2615_);
return v___x_2634_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__0___redArg___boxed(lean_object* v_pu_2640_, lean_object* v_a_2641_, lean_object* v_b_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_){
_start:
{
uint8_t v_pu_boxed_2648_; lean_object* v_res_2649_; 
v_pu_boxed_2648_ = lean_unbox(v_pu_2640_);
v_res_2649_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__0___redArg(v_pu_boxed_2648_, v_a_2641_, v_b_2642_, v___y_2643_, v___y_2644_, v___y_2645_, v___y_2646_);
lean_dec(v___y_2646_);
lean_dec_ref(v___y_2645_);
lean_dec(v___y_2644_);
lean_dec_ref(v___y_2643_);
return v_res_2649_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_mkCasesResultType___closed__0(void){
_start:
{
lean_object* v___x_2650_; 
v___x_2650_ = l_Lean_Compiler_LCNF_instInhabitedAlt_default__1___redArg();
return v___x_2650_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_mkCasesResultType___closed__2(void){
_start:
{
lean_object* v___x_2652_; lean_object* v___x_2653_; 
v___x_2652_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkCasesResultType___closed__1));
v___x_2653_ = l_Lean_stringToMessageData(v___x_2652_);
return v___x_2653_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkCasesResultType(uint8_t v_pu_2654_, lean_object* v_alts_2655_, lean_object* v_a_2656_, lean_object* v_a_2657_, lean_object* v_a_2658_, lean_object* v_a_2659_){
_start:
{
lean_object* v___x_2661_; lean_object* v___y_2663_; lean_object* v___y_2664_; lean_object* v___y_2665_; lean_object* v___y_2666_; lean_object* v___x_2675_; lean_object* v___x_2676_; uint8_t v___x_2677_; 
v___x_2661_ = lean_obj_once(&l_Lean_Compiler_LCNF_mkCasesResultType___closed__0, &l_Lean_Compiler_LCNF_mkCasesResultType___closed__0_once, _init_l_Lean_Compiler_LCNF_mkCasesResultType___closed__0);
v___x_2675_ = lean_array_get_size(v_alts_2655_);
v___x_2676_ = lean_unsigned_to_nat(0u);
v___x_2677_ = lean_nat_dec_eq(v___x_2675_, v___x_2676_);
if (v___x_2677_ == 0)
{
v___y_2663_ = v_a_2656_;
v___y_2664_ = v_a_2657_;
v___y_2665_ = v_a_2658_;
v___y_2666_ = v_a_2659_;
goto v___jp_2662_;
}
else
{
lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v_a_2680_; lean_object* v___x_2682_; uint8_t v_isShared_2683_; uint8_t v_isSharedCheck_2687_; 
lean_dec_ref(v_alts_2655_);
v___x_2678_ = lean_obj_once(&l_Lean_Compiler_LCNF_mkCasesResultType___closed__2, &l_Lean_Compiler_LCNF_mkCasesResultType___closed__2_once, _init_l_Lean_Compiler_LCNF_mkCasesResultType___closed__2);
v___x_2679_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__1___redArg(v___x_2678_, v_a_2656_, v_a_2657_, v_a_2658_, v_a_2659_);
v_a_2680_ = lean_ctor_get(v___x_2679_, 0);
v_isSharedCheck_2687_ = !lean_is_exclusive(v___x_2679_);
if (v_isSharedCheck_2687_ == 0)
{
v___x_2682_ = v___x_2679_;
v_isShared_2683_ = v_isSharedCheck_2687_;
goto v_resetjp_2681_;
}
else
{
lean_inc(v_a_2680_);
lean_dec(v___x_2679_);
v___x_2682_ = lean_box(0);
v_isShared_2683_ = v_isSharedCheck_2687_;
goto v_resetjp_2681_;
}
v_resetjp_2681_:
{
lean_object* v___x_2685_; 
if (v_isShared_2683_ == 0)
{
v___x_2685_ = v___x_2682_;
goto v_reusejp_2684_;
}
else
{
lean_object* v_reuseFailAlloc_2686_; 
v_reuseFailAlloc_2686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2686_, 0, v_a_2680_);
v___x_2685_ = v_reuseFailAlloc_2686_;
goto v_reusejp_2684_;
}
v_reusejp_2684_:
{
return v___x_2685_;
}
}
}
v___jp_2662_:
{
lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; 
v___x_2667_ = lean_unsigned_to_nat(0u);
v___x_2668_ = lean_array_get_borrowed(v___x_2661_, v_alts_2655_, v___x_2667_);
lean_inc(v___x_2668_);
v___x_2669_ = l_Lean_Compiler_LCNF_Alt_inferType(v_pu_2654_, v___x_2668_, v___y_2663_, v___y_2664_, v___y_2665_, v___y_2666_);
if (lean_obj_tag(v___x_2669_) == 0)
{
lean_object* v_a_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; 
v_a_2670_ = lean_ctor_get(v___x_2669_, 0);
lean_inc(v_a_2670_);
lean_dec_ref_known(v___x_2669_, 1);
v___x_2671_ = lean_unsigned_to_nat(1u);
v___x_2672_ = lean_array_get_size(v_alts_2655_);
v___x_2673_ = l_Array_toSubarray___redArg(v_alts_2655_, v___x_2671_, v___x_2672_);
v___x_2674_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__0___redArg(v_pu_2654_, v___x_2673_, v_a_2670_, v___y_2663_, v___y_2664_, v___y_2665_, v___y_2666_);
return v___x_2674_;
}
else
{
lean_dec_ref(v_alts_2655_);
return v___x_2669_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkCasesResultType___boxed(lean_object* v_pu_2688_, lean_object* v_alts_2689_, lean_object* v_a_2690_, lean_object* v_a_2691_, lean_object* v_a_2692_, lean_object* v_a_2693_, lean_object* v_a_2694_){
_start:
{
uint8_t v_pu_boxed_2695_; lean_object* v_res_2696_; 
v_pu_boxed_2695_ = lean_unbox(v_pu_2688_);
v_res_2696_ = l_Lean_Compiler_LCNF_mkCasesResultType(v_pu_boxed_2695_, v_alts_2689_, v_a_2690_, v_a_2691_, v_a_2692_, v_a_2693_);
lean_dec(v_a_2693_);
lean_dec_ref(v_a_2692_);
lean_dec(v_a_2691_);
lean_dec_ref(v_a_2690_);
return v_res_2696_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__0(uint8_t v_pu_2697_, lean_object* v_inst_2698_, lean_object* v_R_2699_, lean_object* v_a_2700_, lean_object* v_b_2701_, lean_object* v_c_2702_, lean_object* v___y_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_){
_start:
{
lean_object* v___x_2708_; 
v___x_2708_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__0___redArg(v_pu_2697_, v_a_2700_, v_b_2701_, v___y_2703_, v___y_2704_, v___y_2705_, v___y_2706_);
return v___x_2708_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__0___boxed(lean_object* v_pu_2709_, lean_object* v_inst_2710_, lean_object* v_R_2711_, lean_object* v_a_2712_, lean_object* v_b_2713_, lean_object* v_c_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_, lean_object* v___y_2719_){
_start:
{
uint8_t v_pu_boxed_2720_; lean_object* v_res_2721_; 
v_pu_boxed_2720_ = lean_unbox(v_pu_2709_);
v_res_2721_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__0(v_pu_boxed_2720_, v_inst_2710_, v_R_2711_, v_a_2712_, v_b_2713_, v_c_2714_, v___y_2715_, v___y_2716_, v___y_2717_, v___y_2718_);
lean_dec(v___y_2718_);
lean_dec_ref(v___y_2717_);
lean_dec(v___y_2716_);
lean_dec_ref(v___y_2715_);
return v_res_2721_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_isErasedCompatible_go_spec__0(lean_object* v_msg_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_){
_start:
{
lean_object* v___x_2728_; lean_object* v_toApplicative_2729_; lean_object* v_toFunctor_2730_; lean_object* v_toSeq_2731_; lean_object* v_toSeqLeft_2732_; lean_object* v_toSeqRight_2733_; lean_object* v___f_2734_; lean_object* v___f_2735_; lean_object* v___f_2736_; lean_object* v___f_2737_; lean_object* v___x_2738_; lean_object* v___f_2739_; lean_object* v___f_2740_; lean_object* v___f_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; uint8_t v___x_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; lean_object* v___f_2748_; lean_object* v___x_970__overap_2749_; lean_object* v___x_2750_; 
v___x_2728_ = lean_obj_once(&l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__1, &l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__1);
v_toApplicative_2729_ = lean_ctor_get(v___x_2728_, 0);
v_toFunctor_2730_ = lean_ctor_get(v_toApplicative_2729_, 0);
v_toSeq_2731_ = lean_ctor_get(v_toApplicative_2729_, 2);
v_toSeqLeft_2732_ = lean_ctor_get(v_toApplicative_2729_, 3);
v_toSeqRight_2733_ = lean_ctor_get(v_toApplicative_2729_, 4);
v___f_2734_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__2));
v___f_2735_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_2730_, 2);
v___f_2736_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2736_, 0, v_toFunctor_2730_);
v___f_2737_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2737_, 0, v_toFunctor_2730_);
v___x_2738_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2738_, 0, v___f_2736_);
lean_ctor_set(v___x_2738_, 1, v___f_2737_);
lean_inc(v_toSeqRight_2733_);
v___f_2739_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2739_, 0, v_toSeqRight_2733_);
lean_inc(v_toSeqLeft_2732_);
v___f_2740_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2740_, 0, v_toSeqLeft_2732_);
lean_inc(v_toSeq_2731_);
v___f_2741_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2741_, 0, v_toSeq_2731_);
v___x_2742_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2742_, 0, v___x_2738_);
lean_ctor_set(v___x_2742_, 1, v___f_2734_);
lean_ctor_set(v___x_2742_, 2, v___f_2741_);
lean_ctor_set(v___x_2742_, 3, v___f_2740_);
lean_ctor_set(v___x_2742_, 4, v___f_2739_);
v___x_2743_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2743_, 0, v___x_2742_);
lean_ctor_set(v___x_2743_, 1, v___f_2735_);
v___x_2744_ = l_StateRefT_x27_instMonad___redArg(v___x_2743_);
v___x_2745_ = 0;
v___x_2746_ = lean_box(v___x_2745_);
v___x_2747_ = l_instInhabitedOfMonad___redArg(v___x_2744_, v___x_2746_);
v___f_2748_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2748_, 0, v___x_2747_);
v___x_970__overap_2749_ = lean_panic_fn_borrowed(v___f_2748_, v_msg_2722_);
lean_dec_ref(v___f_2748_);
lean_inc(v___y_2726_);
lean_inc_ref(v___y_2725_);
lean_inc(v___y_2724_);
lean_inc_ref(v___y_2723_);
v___x_2750_ = lean_apply_5(v___x_970__overap_2749_, v___y_2723_, v___y_2724_, v___y_2725_, v___y_2726_, lean_box(0));
return v___x_2750_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_isErasedCompatible_go_spec__0___boxed(lean_object* v_msg_2751_, lean_object* v___y_2752_, lean_object* v___y_2753_, lean_object* v___y_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_){
_start:
{
lean_object* v_res_2757_; 
v_res_2757_ = l_panic___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_isErasedCompatible_go_spec__0(v_msg_2751_, v___y_2752_, v___y_2753_, v___y_2754_, v___y_2755_);
lean_dec(v___y_2755_);
lean_dec_ref(v___y_2754_);
lean_dec(v___y_2753_);
lean_dec_ref(v___y_2752_);
return v_res_2757_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_isErasedCompatible_go___closed__1(void){
_start:
{
lean_object* v___x_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; 
v___x_2759_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_inferType___closed__2));
v___x_2760_ = lean_unsigned_to_nat(50u);
v___x_2761_ = lean_unsigned_to_nat(345u);
v___x_2762_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_isErasedCompatible_go___closed__0));
v___x_2763_ = ((lean_object*)(l_Lean_Compiler_LCNF_InferType_Pure_inferType___closed__0));
v___x_2764_ = l_mkPanicMessageWithDecl(v___x_2763_, v___x_2762_, v___x_2761_, v___x_2760_, v___x_2759_);
return v___x_2764_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_isErasedCompatible_go(lean_object* v_type_2765_, lean_object* v_predVars_2766_, lean_object* v_a_2767_, lean_object* v_a_2768_, lean_object* v_a_2769_, lean_object* v_a_2770_){
_start:
{
lean_object* v_t_2773_; lean_object* v_b_2774_; lean_object* v___y_2775_; lean_object* v___y_2776_; lean_object* v___y_2777_; lean_object* v___y_2778_; lean_object* v_type_2783_; 
v_type_2783_ = l_Lean_Expr_headBeta(v_type_2765_);
switch(lean_obj_tag(v_type_2783_))
{
case 0:
{
lean_object* v_deBruijnIndex_2784_; uint8_t v___x_2785_; lean_object* v___x_2786_; lean_object* v___x_2787_; lean_object* v___x_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; 
v_deBruijnIndex_2784_ = lean_ctor_get(v_type_2783_, 0);
lean_inc(v_deBruijnIndex_2784_);
lean_dec_ref_known(v_type_2783_, 1);
v___x_2785_ = 0;
v___x_2786_ = lean_array_get_size(v_predVars_2766_);
v___x_2787_ = lean_nat_sub(v___x_2786_, v_deBruijnIndex_2784_);
lean_dec(v_deBruijnIndex_2784_);
v___x_2788_ = lean_unsigned_to_nat(1u);
v___x_2789_ = lean_nat_sub(v___x_2787_, v___x_2788_);
lean_dec(v___x_2787_);
v___x_2790_ = lean_box(v___x_2785_);
v___x_2791_ = lean_array_get(v___x_2790_, v_predVars_2766_, v___x_2789_);
lean_dec(v___x_2789_);
lean_dec_ref(v_predVars_2766_);
lean_dec(v___x_2790_);
v___x_2792_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2792_, 0, v___x_2791_);
return v___x_2792_;
}
case 1:
{
lean_object* v_fvarId_2793_; lean_object* v___x_2794_; 
lean_dec_ref(v_predVars_2766_);
v_fvarId_2793_ = lean_ctor_get(v_type_2783_, 0);
lean_inc(v_fvarId_2793_);
lean_dec_ref_known(v_type_2783_, 1);
v___x_2794_ = l_Lean_Compiler_LCNF_getType(v_fvarId_2793_, v_a_2767_, v_a_2768_, v_a_2769_, v_a_2770_);
if (lean_obj_tag(v___x_2794_) == 0)
{
lean_object* v_a_2795_; lean_object* v___x_2797_; uint8_t v_isShared_2798_; uint8_t v_isSharedCheck_2804_; 
v_a_2795_ = lean_ctor_get(v___x_2794_, 0);
v_isSharedCheck_2804_ = !lean_is_exclusive(v___x_2794_);
if (v_isSharedCheck_2804_ == 0)
{
v___x_2797_ = v___x_2794_;
v_isShared_2798_ = v_isSharedCheck_2804_;
goto v_resetjp_2796_;
}
else
{
lean_inc(v_a_2795_);
lean_dec(v___x_2794_);
v___x_2797_ = lean_box(0);
v_isShared_2798_ = v_isSharedCheck_2804_;
goto v_resetjp_2796_;
}
v_resetjp_2796_:
{
uint8_t v___x_2799_; lean_object* v___x_2800_; lean_object* v___x_2802_; 
v___x_2799_ = l_Lean_Compiler_LCNF_isPredicateType(v_a_2795_);
v___x_2800_ = lean_box(v___x_2799_);
if (v_isShared_2798_ == 0)
{
lean_ctor_set(v___x_2797_, 0, v___x_2800_);
v___x_2802_ = v___x_2797_;
goto v_reusejp_2801_;
}
else
{
lean_object* v_reuseFailAlloc_2803_; 
v_reuseFailAlloc_2803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2803_, 0, v___x_2800_);
v___x_2802_ = v_reuseFailAlloc_2803_;
goto v_reusejp_2801_;
}
v_reusejp_2801_:
{
return v___x_2802_;
}
}
}
else
{
lean_object* v_a_2805_; lean_object* v___x_2807_; uint8_t v_isShared_2808_; uint8_t v_isSharedCheck_2812_; 
v_a_2805_ = lean_ctor_get(v___x_2794_, 0);
v_isSharedCheck_2812_ = !lean_is_exclusive(v___x_2794_);
if (v_isSharedCheck_2812_ == 0)
{
v___x_2807_ = v___x_2794_;
v_isShared_2808_ = v_isSharedCheck_2812_;
goto v_resetjp_2806_;
}
else
{
lean_inc(v_a_2805_);
lean_dec(v___x_2794_);
v___x_2807_ = lean_box(0);
v_isShared_2808_ = v_isSharedCheck_2812_;
goto v_resetjp_2806_;
}
v_resetjp_2806_:
{
lean_object* v___x_2810_; 
if (v_isShared_2808_ == 0)
{
v___x_2810_ = v___x_2807_;
goto v_reusejp_2809_;
}
else
{
lean_object* v_reuseFailAlloc_2811_; 
v_reuseFailAlloc_2811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2811_, 0, v_a_2805_);
v___x_2810_ = v_reuseFailAlloc_2811_;
goto v_reusejp_2809_;
}
v_reusejp_2809_:
{
return v___x_2810_;
}
}
}
}
case 3:
{
uint8_t v___x_2813_; lean_object* v___x_2814_; lean_object* v___x_2815_; 
lean_dec_ref_known(v_type_2783_, 1);
lean_dec_ref(v_predVars_2766_);
v___x_2813_ = 0;
v___x_2814_ = lean_box(v___x_2813_);
v___x_2815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2815_, 0, v___x_2814_);
return v___x_2815_;
}
case 4:
{
uint8_t v___x_2816_; lean_object* v___x_2817_; lean_object* v___x_2818_; 
lean_dec_ref(v_predVars_2766_);
v___x_2816_ = l_Lean_Expr_isErased(v_type_2783_);
lean_dec_ref_known(v_type_2783_, 2);
v___x_2817_ = lean_box(v___x_2816_);
v___x_2818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2818_, 0, v___x_2817_);
return v___x_2818_;
}
case 5:
{
lean_object* v_fn_2819_; 
v_fn_2819_ = lean_ctor_get(v_type_2783_, 0);
lean_inc_ref(v_fn_2819_);
lean_dec_ref_known(v_type_2783_, 2);
v_type_2765_ = v_fn_2819_;
goto _start;
}
case 6:
{
lean_object* v_binderType_2821_; lean_object* v_body_2822_; 
v_binderType_2821_ = lean_ctor_get(v_type_2783_, 1);
lean_inc_ref(v_binderType_2821_);
v_body_2822_ = lean_ctor_get(v_type_2783_, 2);
lean_inc_ref(v_body_2822_);
lean_dec_ref_known(v_type_2783_, 3);
v_t_2773_ = v_binderType_2821_;
v_b_2774_ = v_body_2822_;
v___y_2775_ = v_a_2767_;
v___y_2776_ = v_a_2768_;
v___y_2777_ = v_a_2769_;
v___y_2778_ = v_a_2770_;
goto v___jp_2772_;
}
case 7:
{
lean_object* v_binderType_2823_; lean_object* v_body_2824_; 
v_binderType_2823_ = lean_ctor_get(v_type_2783_, 1);
lean_inc_ref(v_binderType_2823_);
v_body_2824_ = lean_ctor_get(v_type_2783_, 2);
lean_inc_ref(v_body_2824_);
lean_dec_ref_known(v_type_2783_, 3);
v_t_2773_ = v_binderType_2823_;
v_b_2774_ = v_body_2824_;
v___y_2775_ = v_a_2767_;
v___y_2776_ = v_a_2768_;
v___y_2777_ = v_a_2769_;
v___y_2778_ = v_a_2770_;
goto v___jp_2772_;
}
case 10:
{
lean_object* v_expr_2825_; 
v_expr_2825_ = lean_ctor_get(v_type_2783_, 1);
lean_inc_ref(v_expr_2825_);
lean_dec_ref_known(v_type_2783_, 2);
v_type_2765_ = v_expr_2825_;
goto _start;
}
default: 
{
lean_object* v___x_2827_; lean_object* v___x_2828_; 
lean_dec_ref(v_type_2783_);
lean_dec_ref(v_predVars_2766_);
v___x_2827_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_isErasedCompatible_go___closed__1, &l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_isErasedCompatible_go___closed__1_once, _init_l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_isErasedCompatible_go___closed__1);
v___x_2828_ = l_panic___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_isErasedCompatible_go_spec__0(v___x_2827_, v_a_2767_, v_a_2768_, v_a_2769_, v_a_2770_);
return v___x_2828_;
}
}
v___jp_2772_:
{
uint8_t v___x_2779_; lean_object* v___x_2780_; lean_object* v___x_2781_; 
v___x_2779_ = l_Lean_Compiler_LCNF_isPredicateType(v_t_2773_);
v___x_2780_ = lean_box(v___x_2779_);
v___x_2781_ = lean_array_push(v_predVars_2766_, v___x_2780_);
v_type_2765_ = v_b_2774_;
v_predVars_2766_ = v___x_2781_;
v_a_2767_ = v___y_2775_;
v_a_2768_ = v___y_2776_;
v_a_2769_ = v___y_2777_;
v_a_2770_ = v___y_2778_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_isErasedCompatible_go___boxed(lean_object* v_type_2829_, lean_object* v_predVars_2830_, lean_object* v_a_2831_, lean_object* v_a_2832_, lean_object* v_a_2833_, lean_object* v_a_2834_, lean_object* v_a_2835_){
_start:
{
lean_object* v_res_2836_; 
v_res_2836_ = l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_isErasedCompatible_go(v_type_2829_, v_predVars_2830_, v_a_2831_, v_a_2832_, v_a_2833_, v_a_2834_);
lean_dec(v_a_2834_);
lean_dec_ref(v_a_2833_);
lean_dec(v_a_2832_);
lean_dec_ref(v_a_2831_);
return v_res_2836_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isErasedCompatible(lean_object* v_type_2837_, lean_object* v_predVars_2838_, lean_object* v_a_2839_, lean_object* v_a_2840_, lean_object* v_a_2841_, lean_object* v_a_2842_){
_start:
{
lean_object* v___x_2844_; 
v___x_2844_ = l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_isErasedCompatible_go(v_type_2837_, v_predVars_2838_, v_a_2839_, v_a_2840_, v_a_2841_, v_a_2842_);
return v___x_2844_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isErasedCompatible___boxed(lean_object* v_type_2845_, lean_object* v_predVars_2846_, lean_object* v_a_2847_, lean_object* v_a_2848_, lean_object* v_a_2849_, lean_object* v_a_2850_, lean_object* v_a_2851_){
_start:
{
lean_object* v_res_2852_; 
v_res_2852_ = l_Lean_Compiler_LCNF_isErasedCompatible(v_type_2845_, v_predVars_2846_, v_a_2847_, v_a_2848_, v_a_2849_, v_a_2850_);
lean_dec(v_a_2850_);
lean_dec_ref(v_a_2849_);
lean_dec(v_a_2848_);
lean_dec_ref(v_a_2847_);
return v_res_2852_;
}
}
LEAN_EXPORT uint8_t l_List_isEqv___at___00Lean_Compiler_LCNF_eqvTypes_spec__0(lean_object* v_x_2853_, lean_object* v_x_2854_){
_start:
{
if (lean_obj_tag(v_x_2853_) == 0)
{
if (lean_obj_tag(v_x_2854_) == 0)
{
uint8_t v___x_2855_; 
v___x_2855_ = 1;
return v___x_2855_;
}
else
{
uint8_t v___x_2856_; 
v___x_2856_ = 0;
return v___x_2856_;
}
}
else
{
if (lean_obj_tag(v_x_2854_) == 0)
{
uint8_t v___x_2857_; 
v___x_2857_ = 0;
return v___x_2857_;
}
else
{
lean_object* v_head_2858_; lean_object* v_tail_2859_; lean_object* v_head_2860_; lean_object* v_tail_2861_; uint8_t v___x_2862_; 
v_head_2858_ = lean_ctor_get(v_x_2853_, 0);
v_tail_2859_ = lean_ctor_get(v_x_2853_, 1);
v_head_2860_ = lean_ctor_get(v_x_2854_, 0);
v_tail_2861_ = lean_ctor_get(v_x_2854_, 1);
v___x_2862_ = l_Lean_Level_isEquiv(v_head_2858_, v_head_2860_);
if (v___x_2862_ == 0)
{
return v___x_2862_;
}
else
{
v_x_2853_ = v_tail_2859_;
v_x_2854_ = v_tail_2861_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_isEqv___at___00Lean_Compiler_LCNF_eqvTypes_spec__0___boxed(lean_object* v_x_2864_, lean_object* v_x_2865_){
_start:
{
uint8_t v_res_2866_; lean_object* v_r_2867_; 
v_res_2866_ = l_List_isEqv___at___00Lean_Compiler_LCNF_eqvTypes_spec__0(v_x_2864_, v_x_2865_);
lean_dec(v_x_2865_);
lean_dec(v_x_2864_);
v_r_2867_ = lean_box(v_res_2866_);
return v_r_2867_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_eqvTypes(lean_object* v_a_2868_, lean_object* v_b_2869_){
_start:
{
uint8_t v___x_2870_; lean_object* v_d_u2081_2872_; lean_object* v_b_u2081_2873_; lean_object* v_d_u2082_2874_; lean_object* v_b_u2082_2875_; uint8_t v___y_2879_; uint8_t v___x_2924_; 
v___x_2870_ = lean_expr_eqv(v_a_2868_, v_b_2869_);
v___x_2924_ = 1;
if (v___x_2870_ == 0)
{
uint8_t v___x_2925_; 
v___x_2925_ = l_Lean_Expr_isErased(v_a_2868_);
if (v___x_2925_ == 0)
{
v___y_2879_ = v___x_2870_;
goto v___jp_2878_;
}
else
{
uint8_t v___x_2926_; 
v___x_2926_ = l_Lean_Expr_isErased(v_b_2869_);
if (v___x_2926_ == 0)
{
v___y_2879_ = v___x_2926_;
goto v___jp_2878_;
}
else
{
lean_dec_ref(v_b_2869_);
lean_dec_ref(v_a_2868_);
return v___x_2924_;
}
}
}
else
{
lean_dec_ref(v_b_2869_);
lean_dec_ref(v_a_2868_);
return v___x_2924_;
}
v___jp_2871_:
{
uint8_t v___x_2876_; 
v___x_2876_ = l_Lean_Compiler_LCNF_eqvTypes(v_d_u2081_2872_, v_d_u2082_2874_);
if (v___x_2876_ == 0)
{
lean_dec_ref(v_b_u2082_2875_);
lean_dec_ref(v_b_u2081_2873_);
return v___x_2870_;
}
else
{
v_a_2868_ = v_b_u2081_2873_;
v_b_2869_ = v_b_u2082_2875_;
goto _start;
}
}
v___jp_2878_:
{
lean_object* v_a_x27_2880_; lean_object* v_b_x27_2881_; uint8_t v___x_2882_; 
lean_inc_ref(v_a_2868_);
v_a_x27_2880_ = l_Lean_Expr_headBeta(v_a_2868_);
lean_inc_ref(v_b_2869_);
v_b_x27_2881_ = l_Lean_Expr_headBeta(v_b_2869_);
v___x_2882_ = lean_expr_eqv(v_a_2868_, v_a_x27_2880_);
if (v___x_2882_ == 0)
{
lean_dec_ref(v_b_2869_);
lean_dec_ref(v_a_2868_);
v_a_2868_ = v_a_x27_2880_;
v_b_2869_ = v_b_x27_2881_;
goto _start;
}
else
{
if (v___y_2879_ == 0)
{
uint8_t v___x_2884_; 
v___x_2884_ = lean_expr_eqv(v_b_2869_, v_b_x27_2881_);
if (v___x_2884_ == 0)
{
lean_dec_ref(v_b_2869_);
lean_dec_ref(v_a_2868_);
v_a_2868_ = v_a_x27_2880_;
v_b_2869_ = v_b_x27_2881_;
goto _start;
}
else
{
lean_dec_ref(v_b_x27_2881_);
lean_dec_ref(v_a_x27_2880_);
switch(lean_obj_tag(v_a_2868_))
{
case 10:
{
lean_object* v_expr_2886_; 
v_expr_2886_ = lean_ctor_get(v_a_2868_, 1);
lean_inc_ref(v_expr_2886_);
lean_dec_ref_known(v_a_2868_, 2);
v_a_2868_ = v_expr_2886_;
goto _start;
}
case 5:
{
switch(lean_obj_tag(v_b_2869_))
{
case 10:
{
lean_object* v_expr_2888_; 
v_expr_2888_ = lean_ctor_get(v_b_2869_, 1);
lean_inc_ref(v_expr_2888_);
lean_dec_ref_known(v_b_2869_, 2);
v_b_2869_ = v_expr_2888_;
goto _start;
}
case 5:
{
lean_object* v_fn_2890_; lean_object* v_arg_2891_; lean_object* v_fn_2892_; lean_object* v_arg_2893_; uint8_t v___x_2894_; 
v_fn_2890_ = lean_ctor_get(v_a_2868_, 0);
lean_inc_ref(v_fn_2890_);
v_arg_2891_ = lean_ctor_get(v_a_2868_, 1);
lean_inc_ref(v_arg_2891_);
lean_dec_ref_known(v_a_2868_, 2);
v_fn_2892_ = lean_ctor_get(v_b_2869_, 0);
lean_inc_ref(v_fn_2892_);
v_arg_2893_ = lean_ctor_get(v_b_2869_, 1);
lean_inc_ref(v_arg_2893_);
lean_dec_ref_known(v_b_2869_, 2);
v___x_2894_ = l_Lean_Compiler_LCNF_eqvTypes(v_fn_2890_, v_fn_2892_);
if (v___x_2894_ == 0)
{
lean_dec_ref(v_arg_2893_);
lean_dec_ref(v_arg_2891_);
return v___x_2870_;
}
else
{
v_a_2868_ = v_arg_2891_;
v_b_2869_ = v_arg_2893_;
goto _start;
}
}
default: 
{
lean_dec_ref_known(v_a_2868_, 2);
lean_dec_ref(v_b_2869_);
return v___y_2879_;
}
}
}
case 7:
{
switch(lean_obj_tag(v_b_2869_))
{
case 10:
{
lean_object* v_expr_2896_; 
v_expr_2896_ = lean_ctor_get(v_b_2869_, 1);
lean_inc_ref(v_expr_2896_);
lean_dec_ref_known(v_b_2869_, 2);
v_b_2869_ = v_expr_2896_;
goto _start;
}
case 7:
{
lean_object* v_binderType_2898_; lean_object* v_body_2899_; lean_object* v_binderType_2900_; lean_object* v_body_2901_; 
v_binderType_2898_ = lean_ctor_get(v_a_2868_, 1);
lean_inc_ref(v_binderType_2898_);
v_body_2899_ = lean_ctor_get(v_a_2868_, 2);
lean_inc_ref(v_body_2899_);
lean_dec_ref_known(v_a_2868_, 3);
v_binderType_2900_ = lean_ctor_get(v_b_2869_, 1);
lean_inc_ref(v_binderType_2900_);
v_body_2901_ = lean_ctor_get(v_b_2869_, 2);
lean_inc_ref(v_body_2901_);
lean_dec_ref_known(v_b_2869_, 3);
v_d_u2081_2872_ = v_binderType_2898_;
v_b_u2081_2873_ = v_body_2899_;
v_d_u2082_2874_ = v_binderType_2900_;
v_b_u2082_2875_ = v_body_2901_;
goto v___jp_2871_;
}
default: 
{
lean_dec_ref_known(v_a_2868_, 3);
lean_dec_ref(v_b_2869_);
return v___y_2879_;
}
}
}
case 6:
{
switch(lean_obj_tag(v_b_2869_))
{
case 10:
{
lean_object* v_expr_2902_; 
v_expr_2902_ = lean_ctor_get(v_b_2869_, 1);
lean_inc_ref(v_expr_2902_);
lean_dec_ref_known(v_b_2869_, 2);
v_b_2869_ = v_expr_2902_;
goto _start;
}
case 6:
{
lean_object* v_binderType_2904_; lean_object* v_body_2905_; lean_object* v_binderType_2906_; lean_object* v_body_2907_; 
v_binderType_2904_ = lean_ctor_get(v_a_2868_, 1);
lean_inc_ref(v_binderType_2904_);
v_body_2905_ = lean_ctor_get(v_a_2868_, 2);
lean_inc_ref(v_body_2905_);
lean_dec_ref_known(v_a_2868_, 3);
v_binderType_2906_ = lean_ctor_get(v_b_2869_, 1);
lean_inc_ref(v_binderType_2906_);
v_body_2907_ = lean_ctor_get(v_b_2869_, 2);
lean_inc_ref(v_body_2907_);
lean_dec_ref_known(v_b_2869_, 3);
v_d_u2081_2872_ = v_binderType_2904_;
v_b_u2081_2873_ = v_body_2905_;
v_d_u2082_2874_ = v_binderType_2906_;
v_b_u2082_2875_ = v_body_2907_;
goto v___jp_2871_;
}
default: 
{
lean_dec_ref_known(v_a_2868_, 3);
lean_dec_ref(v_b_2869_);
return v___y_2879_;
}
}
}
case 3:
{
switch(lean_obj_tag(v_b_2869_))
{
case 10:
{
lean_object* v_expr_2908_; 
v_expr_2908_ = lean_ctor_get(v_b_2869_, 1);
lean_inc_ref(v_expr_2908_);
lean_dec_ref_known(v_b_2869_, 2);
v_b_2869_ = v_expr_2908_;
goto _start;
}
case 3:
{
lean_object* v_u_2910_; lean_object* v_u_2911_; uint8_t v___x_2912_; 
v_u_2910_ = lean_ctor_get(v_a_2868_, 0);
lean_inc(v_u_2910_);
lean_dec_ref_known(v_a_2868_, 1);
v_u_2911_ = lean_ctor_get(v_b_2869_, 0);
lean_inc(v_u_2911_);
lean_dec_ref_known(v_b_2869_, 1);
v___x_2912_ = l_Lean_Level_isEquiv(v_u_2910_, v_u_2911_);
lean_dec(v_u_2911_);
lean_dec(v_u_2910_);
return v___x_2912_;
}
default: 
{
lean_dec_ref_known(v_a_2868_, 1);
lean_dec_ref(v_b_2869_);
return v___y_2879_;
}
}
}
case 4:
{
switch(lean_obj_tag(v_b_2869_))
{
case 10:
{
lean_object* v_expr_2913_; 
v_expr_2913_ = lean_ctor_get(v_b_2869_, 1);
lean_inc_ref(v_expr_2913_);
lean_dec_ref_known(v_b_2869_, 2);
v_b_2869_ = v_expr_2913_;
goto _start;
}
case 4:
{
lean_object* v_declName_2915_; lean_object* v_us_2916_; lean_object* v_declName_2917_; lean_object* v_us_2918_; uint8_t v___x_2919_; 
v_declName_2915_ = lean_ctor_get(v_a_2868_, 0);
lean_inc(v_declName_2915_);
v_us_2916_ = lean_ctor_get(v_a_2868_, 1);
lean_inc(v_us_2916_);
lean_dec_ref_known(v_a_2868_, 2);
v_declName_2917_ = lean_ctor_get(v_b_2869_, 0);
lean_inc(v_declName_2917_);
v_us_2918_ = lean_ctor_get(v_b_2869_, 1);
lean_inc(v_us_2918_);
lean_dec_ref_known(v_b_2869_, 2);
v___x_2919_ = lean_name_eq(v_declName_2915_, v_declName_2917_);
lean_dec(v_declName_2917_);
lean_dec(v_declName_2915_);
if (v___x_2919_ == 0)
{
lean_dec(v_us_2918_);
lean_dec(v_us_2916_);
return v___x_2870_;
}
else
{
uint8_t v___x_2920_; 
v___x_2920_ = l_List_isEqv___at___00Lean_Compiler_LCNF_eqvTypes_spec__0(v_us_2916_, v_us_2918_);
lean_dec(v_us_2918_);
lean_dec(v_us_2916_);
return v___x_2920_;
}
}
default: 
{
lean_dec_ref_known(v_a_2868_, 2);
lean_dec_ref(v_b_2869_);
return v___y_2879_;
}
}
}
default: 
{
if (lean_obj_tag(v_b_2869_) == 10)
{
lean_object* v_expr_2921_; 
v_expr_2921_ = lean_ctor_get(v_b_2869_, 1);
lean_inc_ref(v_expr_2921_);
lean_dec_ref_known(v_b_2869_, 2);
v_b_2869_ = v_expr_2921_;
goto _start;
}
else
{
lean_dec_ref(v_b_2869_);
lean_dec_ref(v_a_2868_);
return v___y_2879_;
}
}
}
}
}
else
{
lean_dec_ref(v_b_2869_);
lean_dec_ref(v_a_2868_);
v_a_2868_ = v_a_x27_2880_;
v_b_2869_ = v_b_x27_2881_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eqvTypes___boxed(lean_object* v_a_2927_, lean_object* v_b_2928_){
_start:
{
uint8_t v_res_2929_; lean_object* v_r_2930_; 
v_res_2929_ = l_Lean_Compiler_LCNF_eqvTypes(v_a_2927_, v_b_2928_);
v_r_2930_ = lean_box(v_res_2929_);
return v_r_2930_;
}
}
lean_object* runtime_initialize_Lean_Compiler_LCNF_PhaseExt(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_OtherDecl(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_LCNF_InferType(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Compiler_LCNF_PhaseExt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_OtherDecl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Compiler_LCNF_InferType(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Compiler_LCNF_PhaseExt(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_OtherDecl(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_InferType(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_LCNF_PhaseExt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_OtherDecl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_InferType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Compiler_LCNF_InferType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Compiler_LCNF_InferType(builtin);
}
#ifdef __cplusplus
}
#endif
